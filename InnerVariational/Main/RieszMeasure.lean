/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Defs.LaplacianMeasure
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.Algebra.Order.Ring.Star
public import InnerVariational.Defs.Calculus

/-!
# Positive distributions are measures (Riesz measure of a subharmonic function)

A linear functional `T` on `C^∞_c(Ω)` which is nonnegative on nonnegative test functions is
given by integration against a unique measure `ρ` on `Ω`, finite on compact subsets of `Ω`
(L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, 2nd ed., Springer,
1990, Theorem 2.1.7; E. H. Lieb and M. Loss, *Analysis*, 2nd ed., Amer. Math. Soc., 2001,
Theorem 6.22). Applied to `T φ = ∫ u Δφ` for a continuous weakly subharmonic `u`, this gives the
Riesz measure `Δu` (`exists_hasDistribLaplacianOn`), which the proof of Theorem 8.7 of
D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
DOI 10.1002/cpa.22226; arXiv:2306.10131 (numbering of arXiv v2), uses.

## Proof

* `T` is bounded on test functions supported in a fixed compact `K`: `|T φ| ≤ sup|φ| · T η` for a
  smooth cutoff `0 ≤ η ≤ 1` with `η = 1` on `K` (`abs_le_mul_of_tsupport_subset`), by positivity.
* Every `F ∈ C_c(Ω)` is a uniform limit of test functions supported in a fixed compact subset of
  `Ω` (`exists_isTestFunction_approx`: smooth approximation of the uniformly continuous `F`,
  multiplied by a cutoff). So `T` extends to `C_c(Ω)`, as `L F = lim T φ_k`
  (`tendsto_extendPositive`), and the extension is linear and positive.
* Mathlib's Riesz–Markov–Kakutani theorem (`RealRMK.rieszMeasure`) on the locally compact
  space `Ω` gives a measure on `Ω`; push it forward to `ℝⁿ`.
* Uniqueness (`eq_of_integral_eq`): two measures on `Ω`, finite on compacts, that agree on test
  functions agree on `C_c(Ω)` (same approximation) and are regular, so they are equal
  (`Measure.ext_of_integral_eq_on_compactlySupported`).
-/

open MeasureTheory Metric Set Filter Topology Laplacian
open scoped ContDiff Manifold CompactlySupported

@[expose] public noncomputable section

namespace InnerVariational.Main

variable {n : ℕ}

/-! ### Smooth cutoffs and the Laplacian of a test function -/

/-- **Smooth Urysohn lemma.** For a compact `K` inside an open `U` there is a test function
`0 ≤ η ≤ 1` on `U` with `η = 1` on `K`. -/
theorem exists_isTestFunction_eq_one {K U : Set (Rn n)} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ η : Rn n → ℝ, IsTestFunction U η ∧ (∀ x, 0 ≤ η x ∧ η x ≤ 1) ∧ ∀ x ∈ K, η x = 1 := by
  obtain ⟨V, hVo, hKV, hVU, hVc⟩ := exists_open_between_and_isCompact_closure hK hU hKU
  obtain ⟨η, hη, hrange, hsupp, h1⟩ :=
    exists_contMDiff_support_eq_eq_one_iff 𝓘(ℝ, Rn n) (n := (⊤ : ℕ∞)) hVo hK.isClosed hKV
  have hts : tsupport η = closure V := by rw [tsupport, hsupp]
  refine ⟨η, ⟨contMDiff_iff_contDiff.1 hη, ?_, ?_⟩, fun x => hrange (mem_range_self x),
    fun x hx => (h1 x).1 hx⟩
  · rw [HasCompactSupport, hts]
    exact hVc
  · rw [hts]
    exact hVU

/-- The Laplacian of a function vanishes outside its topological support. -/
theorem laplacian_eq_zero_of_notMem_tsupport {φ : Rn n → ℝ} {x : Rn n} (hx : x ∉ tsupport φ) :
    Δ φ x = 0 := by
  rw [(InnerProductSpace.laplacian_congr_nhds (notMem_tsupport_iff_eventuallyEq.1 hx)).eq_of_nhds]
  exact congrFun InnerProductSpace.laplacian_const x

theorem tsupport_laplacian_subset (φ : Rn n → ℝ) : tsupport (Δ φ) ⊆ tsupport φ :=
  closure_minimal (fun _ hx => by_contra fun h => hx (laplacian_eq_zero_of_notMem_tsupport h))
    (isClosed_tsupport φ)

/-- The Laplacian of a smooth function is continuous. -/
theorem continuous_laplacian {φ : Rn n → ℝ} (hφ : ContDiff ℝ ∞ φ) : Continuous (Δ φ) := by
  have e : Δ φ = fun x => ∑ i, iteratedFDeriv ℝ 2 φ x
      ![(EuclideanSpace.basisFun (Fin n) ℝ).toBasis i,
        (EuclideanSpace.basisFun (Fin n) ℝ).toBasis i] := by
    funext x
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis φ
      (EuclideanSpace.basisFun (Fin n) ℝ)]
    rfl
  rw [e]
  refine continuous_finsetSum _ fun i _ => ?_
  exact (continuous_eval_const _).comp
    (hφ.continuous_iteratedFDeriv (m := 2) (by norm_cast))

/-- `u Δφ` is continuous with compact support (hence integrable) when `u` is continuous on the
open set `Ω` and `φ ∈ C^∞_c(Ω)`. -/
theorem continuous_mul_laplacian {Ω : Set (Rn n)} (hΩ : IsOpen Ω) {u : Rn n → ℝ}
    (hu : ContinuousOn u Ω) {φ : Rn n → ℝ} (hφ : IsTestFunction Ω φ) :
    Continuous fun x => u x * Δ φ x := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  by_cases hx : x ∈ Ω
  · exact (hu.continuousAt (hΩ.mem_nhds hx)).mul (continuous_laplacian hφ.1).continuousAt
  · have hx' : x ∉ tsupport φ := fun h => hx (hφ.2.2 h)
    have hev : (fun y => u y * Δ φ y) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hx'] with y hy
      rw [laplacian_eq_zero_of_notMem_tsupport hy, mul_zero]
    exact (continuousAt_congr hev).2 continuousAt_const

theorem integrable_mul_laplacian {Ω : Set (Rn n)} (hΩ : IsOpen Ω) {u : Rn n → ℝ}
    (hu : ContinuousOn u Ω) {φ : Rn n → ℝ} (hφ : IsTestFunction Ω φ) :
    Integrable fun x => u x * Δ φ x := by
  refine (continuous_mul_laplacian hΩ hu hφ).integrable_of_hasCompactSupport ?_
  exact (hφ.2.1.mono' ((subset_tsupport _).trans (tsupport_laplacian_subset φ))).mul_left

/-! ### Test functions form a vector space -/

theorem isTestFunction_add {Ω : Set (Rn n)} {φ ψ : Rn n → ℝ} (hφ : IsTestFunction Ω φ)
    (hψ : IsTestFunction Ω ψ) : IsTestFunction Ω (φ + ψ) :=
  ⟨hφ.1.add hψ.1, hφ.2.1.add hψ.2.1,
    (tsupport_add φ ψ).trans (union_subset hφ.2.2 hψ.2.2)⟩

theorem isTestFunction_smul {Ω : Set (Rn n)} {φ : Rn n → ℝ} (hφ : IsTestFunction Ω φ) (c : ℝ) :
    IsTestFunction Ω (c • φ) :=
  ⟨hφ.1.const_smul c, hφ.2.1.mono (Function.support_const_smul_subset c φ),
    (closure_mono (Function.support_const_smul_subset c φ)).trans hφ.2.2⟩

theorem isTestFunction_sub {Ω : Set (Rn n)} {φ ψ : Rn n → ℝ} (hφ : IsTestFunction Ω φ)
    (hψ : IsTestFunction Ω ψ) : IsTestFunction Ω (φ - ψ) := by
  rw [sub_eq_add_neg, ← neg_one_smul ℝ ψ]
  exact isTestFunction_add hφ (isTestFunction_smul hψ (-1))

/-! ### Positive distributions -/

/-- `T` is a positive linear functional on `C^∞_c(Ω)`: additive and homogeneous on test
functions, and nonnegative on nonnegative test functions. -/
structure IsPositiveDistrib (Ω : Set (Rn n)) (T : (Rn n → ℝ) → ℝ) : Prop where
  map_add : ∀ φ ψ, IsTestFunction Ω φ → IsTestFunction Ω ψ → T (φ + ψ) = T φ + T ψ
  map_smul : ∀ (c : ℝ) φ, IsTestFunction Ω φ → T (c • φ) = c * T φ
  nonneg : ∀ φ, IsTestFunction Ω φ → (∀ x, 0 ≤ φ x) → 0 ≤ T φ

namespace IsPositiveDistrib

variable {Ω : Set (Rn n)} {T : (Rn n → ℝ) → ℝ}

theorem map_sub (hT : IsPositiveDistrib Ω T) {φ ψ : Rn n → ℝ} (hφ : IsTestFunction Ω φ)
    (hψ : IsTestFunction Ω ψ) : T (φ - ψ) = T φ - T ψ := by
  rw [sub_eq_add_neg, ← neg_one_smul ℝ ψ, hT.map_add _ _ hφ (isTestFunction_smul hψ _),
    hT.map_smul _ _ hψ]
  ring

/-- **`T` is bounded on test functions supported in a fixed compact set.** If `0 ≤ η` is a test
function with `η = 1` on `K`, then `|T φ| ≤ s T η` whenever `tsupport φ ⊆ K` and `|φ| ≤ s`. -/
theorem abs_le_mul (hT : IsPositiveDistrib Ω T) {K : Set (Rn n)} {η : Rn n → ℝ}
    (hη : IsTestFunction Ω η) (hη0 : ∀ x, 0 ≤ η x) (hη1 : ∀ x ∈ K, η x = 1) {φ : Rn n → ℝ}
    (hφ : IsTestFunction Ω φ) (hφK : tsupport φ ⊆ K) {s : ℝ} (hs : ∀ x, |φ x| ≤ s) :
    |T φ| ≤ s * T η := by
  have hs0 : 0 ≤ s := (abs_nonneg _).trans (hs 0)
  have key : ∀ ε : ℝ, ε = 1 ∨ ε = -1 → 0 ≤ T (s • η + ε • φ) := by
    intro ε hε
    refine hT.nonneg _ (isTestFunction_add (isTestFunction_smul hη s)
      (isTestFunction_smul hφ ε)) fun x => ?_
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hx : x ∈ K
    · rw [hη1 x hx, mul_one]
      have h1 := hs x
      rcases hε with rfl | rfl
      · linarith [neg_abs_le (φ x)]
      · linarith [le_abs_self (φ x)]
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hφK h)), mul_zero, add_zero]
      exact mul_nonneg hs0 (hη0 x)
  have h1 := key 1 (Or.inl rfl)
  have h2 := key (-1) (Or.inr rfl)
  rw [hT.map_add _ _ (isTestFunction_smul hη s) (isTestFunction_smul hφ _), hT.map_smul _ _ hη,
    hT.map_smul _ _ hφ] at h1 h2
  rw [abs_le]
  constructor <;> linarith

/-- Two sequences of test functions with supports in a fixed compact subset of `Ω` which are
uniformly close have asymptotically equal `T`-values. -/
theorem tendsto_sub (hT : IsPositiveDistrib Ω T) (hΩ : IsOpen Ω) {K : Set (Rn n)}
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) {φ ψ : ℕ → Rn n → ℝ} (hφ : ∀ k, IsTestFunction Ω (φ k))
    (hψ : ∀ k, IsTestFunction Ω (ψ k)) (hφK : ∀ k, tsupport (φ k) ⊆ K)
    (hψK : ∀ k, tsupport (ψ k) ⊆ K) {e : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0))
    (hφψ : ∀ k x, |φ k x - ψ k x| ≤ e k) :
    Tendsto (fun k => T (φ k) - T (ψ k)) atTop (𝓝 0) := by
  obtain ⟨η, hη, hη01, hη1⟩ := exists_isTestFunction_eq_one hK hΩ hKΩ
  have hb : ∀ k, ‖T (φ k) - T (ψ k)‖ ≤ e k * T η := fun k => by
    rw [Real.norm_eq_abs, ← hT.map_sub (hφ k) (hψ k)]
    exact hT.abs_le_mul hη (fun x => (hη01 x).1) hη1 (isTestFunction_sub (hφ k) (hψ k))
      ((tsupport_sub _ _).trans (union_subset (hφK k) (hψK k))) (hφψ k)
  refine squeeze_zero_norm hb ?_
  simpa using he.mul_const (T η)

/-- A sequence of test functions with supports in a fixed compact subset of `Ω` converging
uniformly has Cauchy `T`-values. -/
theorem cauchySeq (hT : IsPositiveDistrib Ω T) (hΩ : IsOpen Ω) {K : Set (Rn n)}
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) {φ : ℕ → Rn n → ℝ} (hφ : ∀ k, IsTestFunction Ω (φ k))
    (hφK : ∀ k, tsupport (φ k) ⊆ K) {F : Rn n → ℝ} {e : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0))
    (hφF : ∀ k x, |φ k x - F x| ≤ e k) :
    CauchySeq fun k => T (φ k) := by
  obtain ⟨η, hη, hη01, hη1⟩ := exists_isTestFunction_eq_one hK hΩ hKΩ
  rw [cauchySeq_iff_tendsto_dist_atTop_0]
  have hb : ∀ p : ℕ × ℕ, ‖dist (T (φ p.1)) (T (φ p.2))‖ ≤ (e p.1 + e p.2) * T η := fun p => by
    rw [Real.norm_eq_abs, abs_dist, Real.dist_eq, ← hT.map_sub (hφ p.1) (hφ p.2)]
    refine hT.abs_le_mul hη (fun x => (hη01 x).1) hη1 (isTestFunction_sub (hφ p.1) (hφ p.2))
      ((tsupport_sub _ _).trans (union_subset (hφK p.1) (hφK p.2))) fun x => ?_
    calc |φ p.1 x - φ p.2 x| = |(φ p.1 x - F x) - (φ p.2 x - F x)| := by ring_nf
      _ ≤ |φ p.1 x - F x| + |φ p.2 x - F x| := abs_sub _ _
      _ ≤ e p.1 + e p.2 := add_le_add (hφF _ x) (hφF _ x)
  refine squeeze_zero_norm hb ?_
  have h1 : Tendsto (fun p : ℕ × ℕ => e p.1 + e p.2) atTop (𝓝 0) := by
    rw [← prod_atTop_atTop_eq]
    simpa using (he.comp tendsto_fst).add (he.comp tendsto_snd)
  simpa using h1.mul_const (T η)

end IsPositiveDistrib

/-! ### Uniform approximation of `C_c(Ω)` by test functions -/

/-- Every continuous `F` with compact support in the open set `Ω` is a uniform limit of test
functions supported in a fixed compact subset of `Ω`: approximate `F` uniformly by a smooth `g`
(`F` is uniformly continuous) and multiply by a cutoff which is `1` on `tsupport F`. -/
theorem exists_isTestFunction_approx {Ω : Set (Rn n)} (hΩ : IsOpen Ω) {F : Rn n → ℝ}
    (hF : Continuous F) (hFc : HasCompactSupport F) (hFΩ : tsupport F ⊆ Ω) :
    ∃ K, IsCompact K ∧ K ⊆ Ω ∧ ∃ φ : ℕ → Rn n → ℝ, ∀ k, IsTestFunction Ω (φ k) ∧
      tsupport (φ k) ⊆ K ∧ ∀ x, |φ k x - F x| ≤ 1 / ((k : ℝ) + 1) := by
  obtain ⟨η, hη, hη01, hη1⟩ := exists_isTestFunction_eq_one hFc hΩ hFΩ
  have hU := hFc.uniformContinuous_of_continuous hF
  have hg : ∀ k : ℕ, ∃ g : Rn n → ℝ, ContDiff ℝ ∞ g ∧
      ∀ a, dist (g a) (F a) < 1 / ((k : ℝ) + 1) :=
    fun k => hU.exists_contDiff_dist_le (by positivity)
  choose g hgs hgF using hg
  refine ⟨tsupport η, hη.2.1, hη.2.2, fun k => η * g k, fun k =>
    ⟨⟨hη.1.mul (hgs k), hη.2.1.mul_right, tsupport_mul_subset_left.trans hη.2.2⟩,
      tsupport_mul_subset_left, fun x => ?_⟩⟩
  have hηF : η x * F x = F x := by
    by_cases hx : x ∈ tsupport F
    · rw [hη1 x hx, one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
  have hgx := hgF k x
  rw [Real.dist_eq] at hgx
  calc |(η * g k) x - F x| = |η x| * |g k x - F x| := by
        rw [Pi.mul_apply, ← abs_mul, mul_sub, hηF]
    _ ≤ 1 * (1 / ((k : ℝ) + 1)) := by
        refine mul_le_mul ?_ hgx.le (abs_nonneg _) zero_le_one
        rw [abs_of_nonneg (hη01 x).1]
        exact (hη01 x).2
    _ = 1 / ((k : ℝ) + 1) := one_mul _

open Classical in
/-- The extension of a positive distribution `T` on `C^∞_c(Ω)` to `F ∈ C_c(Ω)`: the limit of
`T φ_k` along a chosen sequence of test functions `φ_k → F` (`exists_isTestFunction_approx`).
By `IsPositiveDistrib.tendsto_extendPositive` any other such sequence gives the same limit. Junk
(`0`) unless `Ω` is open and `F` is continuous with compact support in `Ω`. -/
def extendPositive (Ω : Set (Rn n)) (T : (Rn n → ℝ) → ℝ) (F : Rn n → ℝ) : ℝ :=
  if h : IsOpen Ω ∧ Continuous F ∧ HasCompactSupport F ∧ tsupport F ⊆ Ω then
    limUnder atTop fun k =>
      T ((exists_isTestFunction_approx h.1 h.2.1 h.2.2.1 h.2.2.2).choose_spec.2.2.choose k)
  else 0

namespace IsPositiveDistrib

variable {Ω : Set (Rn n)} {T : (Rn n → ℝ) → ℝ}

/-- `T φ_k → extendPositive Ω T F` along any sequence of test functions with supports in a fixed
compact subset of `Ω` converging uniformly to `F`. -/
theorem tendsto_extendPositive (hT : IsPositiveDistrib Ω T) (hΩ : IsOpen Ω) {F : Rn n → ℝ}
    (hF : Continuous F) (hFc : HasCompactSupport F) (hFΩ : tsupport F ⊆ Ω) {K : Set (Rn n)}
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) {φ : ℕ → Rn n → ℝ} (hφ : ∀ k, IsTestFunction Ω (φ k))
    (hφK : ∀ k, tsupport (φ k) ⊆ K) {e : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0))
    (hφF : ∀ k x, |φ k x - F x| ≤ e k) :
    Tendsto (fun k => T (φ k)) atTop (𝓝 (extendPositive Ω T F)) := by
  have h : IsOpen Ω ∧ Continuous F ∧ HasCompactSupport F ∧ tsupport F ⊆ Ω := ⟨hΩ, hF, hFc, hFΩ⟩
  have hex := (exists_isTestFunction_approx h.1 h.2.1 h.2.2.1 h.2.2.2).choose_spec
  set K₀ := (exists_isTestFunction_approx h.1 h.2.1 h.2.2.1 h.2.2.2).choose
  set ψ := hex.2.2.choose with hψdef
  have hψ := hex.2.2.choose_spec
  have he₀ : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete (hT.cauchySeq hΩ hex.1 hex.2.1
    (fun k => (hψ k).1) (fun k => (hψ k).2.1) he₀ fun k x => (hψ k).2.2 x)
  have hdef : extendPositive Ω T F = L := by
    rw [extendPositive, dite_eq_left h]
    exact hL.limUnder_eq
  rw [hdef]
  have hsub := hT.tendsto_sub hΩ (hK.union hex.1) (union_subset hKΩ hex.2.1) hφ
    (fun k => (hψ k).1) (fun k => (hφK k).trans subset_union_left)
    (fun k => (hψ k).2.1.trans subset_union_right)
    (e := fun k => e k + 1 / ((k : ℝ) + 1)) (by simpa using he.add he₀) fun k x => by
      calc |φ k x - ψ k x| = |(φ k x - F x) - (ψ k x - F x)| := by ring_nf
        _ ≤ |φ k x - F x| + |ψ k x - F x| := abs_sub _ _
        _ ≤ e k + 1 / ((k : ℝ) + 1) := add_le_add (hφF k x) ((hψ k).2.2 x)
  simpa using hsub.add hL

theorem extendPositive_eq (hT : IsPositiveDistrib Ω T) (hΩ : IsOpen Ω) {φ : Rn n → ℝ}
    (hφ : IsTestFunction Ω φ) : extendPositive Ω T φ = T φ :=
  tendsto_nhds_unique (hT.tendsto_extendPositive hΩ hφ.1.continuous hφ.2.1 hφ.2.2 hφ.2.1 hφ.2.2
    (fun _ => hφ) (fun _ => subset_rfl) tendsto_const_nhds fun k x => by simp)
    tendsto_const_nhds

theorem extendPositive_add (hT : IsPositiveDistrib Ω T) (hΩ : IsOpen Ω) {F G : Rn n → ℝ}
    (hF : Continuous F) (hFc : HasCompactSupport F) (hFΩ : tsupport F ⊆ Ω)
    (hG : Continuous G) (hGc : HasCompactSupport G) (hGΩ : tsupport G ⊆ Ω) :
    extendPositive Ω T (F + G) = extendPositive Ω T F + extendPositive Ω T G := by
  obtain ⟨K₁, hK₁, hK₁Ω, φ, hφ⟩ := exists_isTestFunction_approx hΩ hF hFc hFΩ
  obtain ⟨K₂, hK₂, hK₂Ω, ψ, hψ⟩ := exists_isTestFunction_approx hΩ hG hGc hGΩ
  have he₀ : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h1 := hT.tendsto_extendPositive hΩ hF hFc hFΩ hK₁ hK₁Ω (fun k => (hφ k).1)
    (fun k => (hφ k).2.1) he₀ fun k => (hφ k).2.2
  have h2 := hT.tendsto_extendPositive hΩ hG hGc hGΩ hK₂ hK₂Ω (fun k => (hψ k).1)
    (fun k => (hψ k).2.1) he₀ fun k => (hψ k).2.2
  have h3 := hT.tendsto_extendPositive hΩ (hF.add hG) (hFc.add hGc)
    ((tsupport_add F G).trans (union_subset hFΩ hGΩ)) (hK₁.union hK₂) (union_subset hK₁Ω hK₂Ω)
    (fun k => isTestFunction_add (hφ k).1 (hψ k).1)
    (fun k => (tsupport_add _ _).trans (union_subset_union (hφ k).2.1 (hψ k).2.1))
    (e := fun k => 1 / ((k : ℝ) + 1) + 1 / ((k : ℝ) + 1)) (by simpa using he₀.add he₀)
    fun k x => by
      calc |(φ k + ψ k) x - (F + G) x| = |(φ k x - F x) + (ψ k x - G x)| := by
            simp only [Pi.add_apply]; ring_nf
        _ ≤ |φ k x - F x| + |ψ k x - G x| := abs_add_le _ _
        _ ≤ 1 / ((k : ℝ) + 1) + 1 / ((k : ℝ) + 1) := add_le_add ((hφ k).2.2 x) ((hψ k).2.2 x)
  refine tendsto_nhds_unique h3 ?_
  exact (h1.add h2).congr fun k => (hT.map_add _ _ (hφ k).1 (hψ k).1).symm

theorem extendPositive_smul (hT : IsPositiveDistrib Ω T) (hΩ : IsOpen Ω) (c : ℝ)
    {F : Rn n → ℝ} (hF : Continuous F) (hFc : HasCompactSupport F) (hFΩ : tsupport F ⊆ Ω) :
    extendPositive Ω T (c • F) = c * extendPositive Ω T F := by
  obtain ⟨K₁, hK₁, hK₁Ω, φ, hφ⟩ := exists_isTestFunction_approx hΩ hF hFc hFΩ
  have he₀ : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h1 := hT.tendsto_extendPositive hΩ hF hFc hFΩ hK₁ hK₁Ω (fun k => (hφ k).1)
    (fun k => (hφ k).2.1) he₀ fun k => (hφ k).2.2
  have hsupp : tsupport (c • F) ⊆ tsupport F :=
    closure_mono (Function.support_const_smul_subset c F)
  have h3 := hT.tendsto_extendPositive hΩ (hF.const_smul c)
    (hFc.mono (Function.support_const_smul_subset c F)) (hsupp.trans hFΩ) hK₁ hK₁Ω
    (fun k => isTestFunction_smul (hφ k).1 c)
    (fun k => (closure_mono (Function.support_const_smul_subset c _)).trans (hφ k).2.1)
    (e := fun k => |c| * (1 / ((k : ℝ) + 1))) (by simpa using he₀.const_mul |c|) fun k x => by
      calc |(c • φ k) x - (c • F) x| = |c| * |φ k x - F x| := by
            simp only [Pi.smul_apply, smul_eq_mul]; rw [← abs_mul, mul_sub]
        _ ≤ |c| * (1 / ((k : ℝ) + 1)) := mul_le_mul_of_nonneg_left ((hφ k).2.2 x) (abs_nonneg c)
  refine tendsto_nhds_unique h3 ?_
  exact (h1.const_mul c).congr fun k => (hT.map_smul _ _ (hφ k).1).symm

theorem extendPositive_nonneg (hT : IsPositiveDistrib Ω T) (hΩ : IsOpen Ω) {F : Rn n → ℝ}
    (hF : Continuous F) (hFc : HasCompactSupport F) (hFΩ : tsupport F ⊆ Ω)
    (hF0 : ∀ x, 0 ≤ F x) : 0 ≤ extendPositive Ω T F := by
  obtain ⟨K₁, hK₁, hK₁Ω, φ, hφ⟩ := exists_isTestFunction_approx hΩ hF hFc hFΩ
  obtain ⟨η, hη, hη01, hη1⟩ := exists_isTestFunction_eq_one hK₁ hΩ hK₁Ω
  have he₀ : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  set ψ : ℕ → Rn n → ℝ := fun k => φ k + (1 / ((k : ℝ) + 1)) • η with hψdef
  have hψ : ∀ k, IsTestFunction Ω (ψ k) := fun k =>
    isTestFunction_add (hφ k).1 (isTestFunction_smul hη _)
  have hψ0 : ∀ k x, 0 ≤ ψ k x := fun k x => by
    simp only [hψdef, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hx : x ∈ K₁
    · rw [hη1 x hx, mul_one]
      have := (abs_le.1 ((hφ k).2.2 x)).1
      linarith [hF0 x]
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hx ((hφ k).2.1 h)), zero_add]
      exact mul_nonneg (by positivity) (hη01 x).1
  have h := hT.tendsto_extendPositive hΩ hF hFc hFΩ (hK₁.union hη.2.1)
    (union_subset hK₁Ω hη.2.2) hψ
    (fun k => (tsupport_add _ _).trans (union_subset_union (hφ k).2.1
      (closure_mono (Function.support_const_smul_subset _ _))))
    (e := fun k => 1 / ((k : ℝ) + 1) + 1 / ((k : ℝ) + 1)) (by simpa using he₀.add he₀)
    fun k x => by
      simp only [hψdef, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      calc |φ k x + 1 / ((k : ℝ) + 1) * η x - F x|
          = |(φ k x - F x) + 1 / ((k : ℝ) + 1) * η x| := by ring_nf
        _ ≤ |φ k x - F x| + |1 / ((k : ℝ) + 1) * η x| := abs_add_le _ _
        _ ≤ 1 / ((k : ℝ) + 1) + 1 / ((k : ℝ) + 1) := by
            refine add_le_add ((hφ k).2.2 x) ?_
            rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / ((k : ℝ) + 1)),
              abs_of_nonneg (hη01 x).1]
            exact mul_le_of_le_one_right (by positivity) (hη01 x).2
  exact ge_of_tendsto' h fun k => hT.nonneg _ (hψ k) (hψ0 k)

theorem extendPositive_congr {Ω : Set (Rn n)} {T T' : (Rn n → ℝ) → ℝ}
    (h : ∀ φ, IsTestFunction Ω φ → T φ = T' φ) (F : Rn n → ℝ) :
    extendPositive Ω T F = extendPositive Ω T' F := by
  unfold extendPositive
  split_ifs with hF
  · congr 1
    funext k
    exact h _ ((exists_isTestFunction_approx hF.1 hF.2.1 hF.2.2.1
      hF.2.2.2).choose_spec.2.2.choose_spec k).1
  · rfl

end IsPositiveDistrib

/-! ### Integrals of continuous functions with compact support in `Ω` -/

/-- A continuous function supported in a compact set of finite `ρ`-measure is `ρ`-integrable. -/
theorem integrable_of_tsupport_subset {ρ : Measure (Rn n)} {K : Set (Rn n)} (hK : IsCompact K)
    (hρK : ρ K < ⊤) {f : Rn n → ℝ} (hf : Continuous f) (hfK : tsupport f ⊆ K) :
    Integrable f ρ := by
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  have hon : IntegrableOn f K ρ :=
    IntegrableOn.of_bound hρK hf.aestronglyMeasurable M
      ((ae_restrict_iff' hK.measurableSet).2 (.of_forall hM))
  exact (integrableOn_iff_integrable_of_support_subset ((subset_tsupport f).trans hfK)).1 hon

/-- `∫ φ_k dρ → ∫ F dρ` for test functions `φ_k → F` uniformly with supports in a fixed compact
set of finite `ρ`-measure. -/
theorem tendsto_integral_of_approx {ρ : Measure (Rn n)} {K : Set (Rn n)} (hK : IsCompact K)
    (hρK : ρ K < ⊤) {F : Rn n → ℝ} (hF : Continuous F) (hFK : tsupport F ⊆ K)
    {φ : ℕ → Rn n → ℝ} (hφ : ∀ k, Continuous (φ k)) (hφK : ∀ k, tsupport (φ k) ⊆ K)
    {e : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0)) (hφF : ∀ k x, |φ k x - F x| ≤ e k) :
    Tendsto (fun k => ∫ x, φ k x ∂ρ) atTop (𝓝 (∫ x, F x ∂ρ)) := by
  have hFi := integrable_of_tsupport_subset hK hρK hF hFK
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero_norm (a := fun k => e k * ρ.real K) (fun k => ?_) ?_
  · rw [norm_norm, ← integral_sub (integrable_of_tsupport_subset hK hρK (hφ k) (hφK k)) hFi,
      ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := K) fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hφK k h)),
          image_eq_zero_of_notMem_tsupport (fun h => hx (hFK h)), sub_zero]]
    exact norm_setIntegral_le_of_norm_le_const hρK fun x _ => hφF k x
  · simpa using he.mul_const (ρ.real K)

/-! ### The Riesz–Markov–Kakutani step -/

section RMK

variable {Ω : Set (Rn n)}

/-- Extension by zero of `f ∈ C_c(Ω)` to `ℝⁿ`. -/
def extendByZero (f : C_c(Ω, ℝ)) : Rn n → ℝ :=
  Function.extend Subtype.val f 0

theorem extendByZero_of_mem (f : C_c(Ω, ℝ)) {x : Rn n} (hx : x ∈ Ω) :
    extendByZero f x = f ⟨x, hx⟩ :=
  Subtype.val_injective.extend_apply f 0 ⟨x, hx⟩

theorem extendByZero_of_notMem (f : C_c(Ω, ℝ)) {x : Rn n} (hx : x ∉ Ω) :
    extendByZero f x = 0 :=
  Function.extend_apply' _ _ _ fun ⟨y, hy⟩ => hx (hy ▸ y.2)

theorem extendByZero_coe (f : C_c(Ω, ℝ)) (y : Ω) : extendByZero f y = f y :=
  extendByZero_of_mem f y.2

theorem continuous_extendByZero (hΩ : IsOpen Ω) (f : C_c(Ω, ℝ)) :
    Continuous (extendByZero f) :=
  f.hasCompactSupport.continuous_extend_zero hΩ f.continuous

theorem hasCompactSupport_extendByZero (f : C_c(Ω, ℝ)) : HasCompactSupport (extendByZero f) :=
  f.hasCompactSupport.extend_zero continuous_subtype_val

theorem tsupport_extendByZero_subset (f : C_c(Ω, ℝ)) : tsupport (extendByZero f) ⊆ Ω :=
  (f.hasCompactSupport.tsupport_extend_zero_subset continuous_subtype_val).trans
    (by rintro _ ⟨y, -, rfl⟩; exact y.2)

theorem extendByZero_add (f g : C_c(Ω, ℝ)) :
    extendByZero (f + g) = extendByZero f + extendByZero g := by
  funext x
  by_cases hx : x ∈ Ω
  · simp [extendByZero_of_mem _ hx]
  · simp [extendByZero_of_notMem _ hx]

theorem extendByZero_smul (c : ℝ) (f : C_c(Ω, ℝ)) :
    extendByZero (c • f) = c • extendByZero f := by
  funext x
  by_cases hx : x ∈ Ω
  · simp [extendByZero_of_mem _ hx]
  · simp [extendByZero_of_notMem _ hx]

/-- The positive linear functional on `C_c(Ω)` extending a positive distribution. -/
def rieszFunctional {T : (Rn n → ℝ) → ℝ} (hT : IsPositiveDistrib Ω T) (hΩ : IsOpen Ω) :
    C_c(Ω, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    { toFun := fun f => extendPositive Ω T (extendByZero f)
      map_add' := fun f g => by
        rw [extendByZero_add]
        exact hT.extendPositive_add hΩ (continuous_extendByZero hΩ f)
          (hasCompactSupport_extendByZero f) (tsupport_extendByZero_subset f)
          (continuous_extendByZero hΩ g) (hasCompactSupport_extendByZero g)
          (tsupport_extendByZero_subset g)
      map_smul' := fun c f => by
        rw [extendByZero_smul]
        exact hT.extendPositive_smul hΩ c (continuous_extendByZero hΩ f)
          (hasCompactSupport_extendByZero f) (tsupport_extendByZero_subset f) }
    fun f hf => hT.extendPositive_nonneg hΩ (continuous_extendByZero hΩ f)
      (hasCompactSupport_extendByZero f) (tsupport_extendByZero_subset f) fun x => by
        by_cases hx : x ∈ Ω
        · rw [extendByZero_of_mem _ hx]
          exact hf ⟨x, hx⟩
        · rw [extendByZero_of_notMem _ hx]

/-- The restriction to `Ω` of a test function on `Ω`, as an element of `C_c(Ω)`. -/
def testFunctionRestrict {φ : Rn n → ℝ} (hφ : IsTestFunction Ω φ) : C_c(Ω, ℝ) where
  toFun y := φ y
  continuous_toFun := hφ.1.continuous.comp continuous_subtype_val
  hasCompactSupport' := by
    have hc : IsCompact (Subtype.val ⁻¹' tsupport φ : Set Ω) := by
      rw [Subtype.isCompact_iff, Subtype.image_preimage_coe, inter_eq_right.2 hφ.2.2]
      exact hφ.2.1
    exact hc.of_isClosed_subset (isClosed_tsupport _)
      (tsupport_comp_subset_preimage φ continuous_subtype_val)

theorem extendByZero_testFunctionRestrict {φ : Rn n → ℝ} (hφ : IsTestFunction Ω φ) :
    extendByZero (testFunctionRestrict hφ) = φ := by
  funext x
  by_cases hx : x ∈ Ω
  · rw [extendByZero_of_mem _ hx]
    rfl
  · rw [extendByZero_of_notMem _ hx, image_eq_zero_of_notMem_tsupport fun h => hx (hφ.2.2 h)]

/-- **Positive distributions are measures** (Hörmander, Theorem 2.1.7). A positive linear
functional on `C^∞_c(Ω)` is integration against a measure concentrated on `Ω` and finite on
compact subsets of `Ω`. -/
theorem IsPositiveDistrib.exists_measure {T : (Rn n → ℝ) → ℝ} (hT : IsPositiveDistrib Ω T)
    (hΩ : IsOpen Ω) :
    ∃ ρ : Measure (Rn n), ρ Ωᶜ = 0 ∧ (∀ K, IsCompact K → K ⊆ Ω → ρ K < ⊤) ∧
      ∀ φ, IsTestFunction Ω φ → ∫ x, φ x ∂ρ = T φ := by
  have : LocallyCompactSpace Ω := hΩ.locallyCompactSpace
  set Λ := rieszFunctional hT hΩ
  set ρ₀ := RealRMK.rieszMeasure Λ
  refine ⟨ρ₀.map Subtype.val, ?_, fun K hK hKΩ => ?_, fun φ hφ => ?_⟩
  · rw [Measure.map_apply measurable_subtype_coe hΩ.measurableSet.compl]
    convert measure_empty (μ := ρ₀)
    ext y
    simp
  · rw [Measure.map_apply measurable_subtype_coe hK.measurableSet]
    have hc : IsCompact (Subtype.val ⁻¹' K : Set Ω) := by
      rw [Subtype.isCompact_iff, Subtype.image_preimage_coe, inter_eq_right.2 hKΩ]
      exact hK
    exact hc.measure_lt_top
  · rw [integral_map measurable_subtype_coe.aemeasurable hφ.1.continuous.aestronglyMeasurable]
    have h := RealRMK.integral_rieszMeasure Λ (testFunctionRestrict hφ)
    change ∫ y, φ y ∂ρ₀ = _ at h
    rw [h]
    change extendPositive Ω T (extendByZero (testFunctionRestrict hφ)) = T φ
    rw [extendByZero_testFunctionRestrict]
    exact hT.extendPositive_eq hΩ hφ

/-- **Uniqueness.** Two measures concentrated on the open set `Ω`, finite on compact subsets of
`Ω`, with the same integrals of test functions, are equal. -/
theorem eq_of_integral_eq (hΩ : IsOpen Ω) {ρ₁ ρ₂ : Measure (Rn n)} (h₁ : ρ₁ Ωᶜ = 0)
    (h₂ : ρ₂ Ωᶜ = 0) (hf₁ : ∀ K, IsCompact K → K ⊆ Ω → ρ₁ K < ⊤)
    (hf₂ : ∀ K, IsCompact K → K ⊆ Ω → ρ₂ K < ⊤)
    (h : ∀ φ, IsTestFunction Ω φ → ∫ x, φ x ∂ρ₁ = ∫ x, φ x ∂ρ₂) : ρ₁ = ρ₂ := by
  have : LocallyCompactSpace Ω := hΩ.locallyCompactSpace
  have hΩm := hΩ.measurableSet
  -- integrals of `F ∈ C_c(Ω)` agree
  have hC : ∀ F : Rn n → ℝ, Continuous F → HasCompactSupport F → tsupport F ⊆ Ω →
      ∫ x, F x ∂ρ₁ = ∫ x, F x ∂ρ₂ := by
    intro F hF hFc hFΩ
    obtain ⟨K, hK, hKΩ, φ, hφ⟩ := exists_isTestFunction_approx hΩ hF hFc hFΩ
    have he₀ : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hK' := hK.union hFc
    have hK'Ω : K ∪ tsupport F ⊆ Ω := union_subset hKΩ hFΩ
    have t₁ := tendsto_integral_of_approx hK' (hf₁ _ hK' hK'Ω) hF subset_union_right
      (fun k => (hφ k).1.1.continuous) (fun k => (hφ k).2.1.trans subset_union_left) he₀
      fun k => (hφ k).2.2
    have t₂ := tendsto_integral_of_approx hK' (hf₂ _ hK' hK'Ω) hF subset_union_right
      (fun k => (hφ k).1.1.continuous) (fun k => (hφ k).2.1.trans subset_union_left) he₀
      fun k => (hφ k).2.2
    exact tendsto_nhds_unique t₁ (t₂.congr fun k => (h _ (hφ k).1).symm)
  -- pass to the subtype `Ω`
  have hmap : ∀ ρ : Measure (Rn n), ρ Ωᶜ = 0 → (ρ.comap Subtype.val).map Subtype.val = ρ :=
    fun ρ hρ => by
      rw [map_comap_subtype_coe hΩm]
      exact Measure.restrict_eq_self_of_ae_mem (ae_iff.2 hρ)
  have hfin : ∀ ρ : Measure (Rn n), (∀ K, IsCompact K → K ⊆ Ω → ρ K < ⊤) →
      IsFiniteMeasureOnCompacts (ρ.comap (Subtype.val : Ω → Rn n)) := fun ρ hρ =>
    ⟨fun C hC => by
      rw [comap_subtype_coe_apply hΩm]
      exact hρ _ (hC.image continuous_subtype_val) (by rintro _ ⟨y, -, rfl⟩; exact y.2)⟩
  have := hfin ρ₁ hf₁
  have := hfin ρ₂ hf₂
  have hint : ∀ ρ : Measure (Rn n), ρ Ωᶜ = 0 → ∀ f : C_c(Ω, ℝ),
      ∫ y, f y ∂(ρ.comap Subtype.val) = ∫ x, extendByZero f x ∂ρ := fun ρ hρ f => by
    conv_rhs => rw [← hmap ρ hρ]
    rw [integral_map measurable_subtype_coe.aemeasurable
      (continuous_extendByZero hΩ f).aestronglyMeasurable]
    simp only [extendByZero_coe]
  have hsub : ρ₁.comap (Subtype.val : Ω → Rn n) = ρ₂.comap Subtype.val :=
    Measure.ext_of_integral_eq_on_compactlySupported fun f => by
      rw [hint ρ₁ h₁, hint ρ₂ h₂]
      exact hC _ (continuous_extendByZero hΩ f) (hasCompactSupport_extendByZero f)
        (tsupport_extendByZero_subset f)
  rw [← hmap ρ₁ h₁, ← hmap ρ₂ h₂, hsub]

end RMK

/-! ### The Riesz measure of a subharmonic function -/

/-- `φ ↦ ∫ u Δφ` is a positive distribution on `Ω` when `u` is continuous on `Ω` and weakly
subharmonic there. -/
theorem isPositiveDistrib_laplacian {Ω : Set (Rn n)} (hΩ : IsOpen Ω) {u : Rn n → ℝ}
    (hu : ContinuousOn u Ω) (hsub : IsWeaklySubharmonicOn Ω u) :
    IsPositiveDistrib Ω fun φ => ∫ x, u x * Δ φ x where
  map_add φ ψ hφ hψ := by
    rw [← integral_add (integrable_mul_laplacian hΩ hu hφ) (integrable_mul_laplacian hΩ hu hψ)]
    congr 1
    funext x
    rw [(hφ.1.contDiffAt.of_le (by norm_cast)).laplacian_add
      (hψ.1.contDiffAt.of_le (by norm_cast)), mul_add]
  map_smul c φ hφ := by
    rw [← integral_const_mul]
    congr 1
    funext x
    rw [InnerProductSpace.laplacian_smul c (hφ.1.contDiffAt.of_le (by norm_cast)), smul_eq_mul]
    ring
  nonneg φ hφ h0 := hsub φ hφ h0

/-- **Riesz measure of a subharmonic function** (Hörmander, Theorem 2.1.7; Lieb–Loss,
Theorem 6.22). A continuous weakly subharmonic function on an open
set `Ω` has a distributional Laplacian which is a measure concentrated on `Ω`, finite on compact
subsets of `Ω`. -/
theorem exists_hasDistribLaplacianOn {Ω : Set (Rn n)} (hΩ : IsOpen Ω) {u : Rn n → ℝ}
    (hu : ContinuousOn u Ω) (hsub : IsWeaklySubharmonicOn Ω u) :
    ∃ ρ : Measure (Rn n), ρ Ωᶜ = 0 ∧ HasDistribLaplacianOn Ω u ρ := by
  obtain ⟨ρ, hρΩ, hρK, hρ⟩ := (isPositiveDistrib_laplacian hΩ hu hsub).exists_measure hΩ
  exact ⟨ρ, hρΩ, hρK, fun φ hφ => (hρ φ hφ).symm⟩

/-- **Uniqueness of the distributional Laplacian as a measure.** -/
theorem HasDistribLaplacianOn.eq {Ω : Set (Rn n)} (hΩ : IsOpen Ω) {u : Rn n → ℝ}
    {ρ₁ ρ₂ : Measure (Rn n)} (h₁ : HasDistribLaplacianOn Ω u ρ₁) (h₂ : HasDistribLaplacianOn Ω u ρ₂)
    (hρ₁ : ρ₁ Ωᶜ = 0) (hρ₂ : ρ₂ Ωᶜ = 0) : ρ₁ = ρ₂ :=
  eq_of_integral_eq hΩ hρ₁ hρ₂ h₁.1 h₂.1 fun φ hφ => (h₁.2 φ hφ).symm.trans (h₂.2 φ hφ)

end InnerVariational.Main
