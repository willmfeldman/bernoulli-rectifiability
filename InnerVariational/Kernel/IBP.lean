/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Registry.Sobolev
public import InnerVariational.Basic.SphereIntegral
import Mathlib.Order.CompletePartialOrder
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import GMTFoundations.Defs.Calculus

/-!
# Integration by parts: consequences of the Gauss–Green formula

Kriventsov–Weiss (full reference below) integrate by parts freely against Lipschitz functions.
The basic statement, `∫ f ∂_v g = −∫ g ∂_v f` for `f` locally Lipschitz and `g` Lipschitz with
compact support, is `Registry.integral_mul_fderiv_eq_neg`, proved in `Sobolev/Lipschitz.lean` by
way of Rademacher's theorem. This file derives the forms used in `Kernel/*`.

## Main results

* `Kernel.integral_inner_gradient_eq_neg_laplacian`: for `u ∈ C²(V)` and `g` Lipschitz with
  compact support in `V`, `∫ ⟪∇u, ∇g⟫ = −∫ g Δu`.
* `Kernel.integral_mul_laplacian_eq_neg`: for `f` locally Lipschitz on `Ω` and `φ ∈ C^∞_c(Ω)`,
  `∫ f Δφ = −∫ ⟪∇f, ∇φ⟫`.
* Helpers: coordinates in the standard basis, integrability of bounded functions with compact
  support, bounds on `fderiv` of locally Lipschitz functions, and a product rule for Lipschitz
  constants (`Kernel.lipschitzWith_smul_of_support`).

## References

* D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
  DOI 10.1002/cpa.22226; arXiv:2306.10131. Result and equation numbers refer to arXiv v2.
-/

open MeasureTheory Metric Set Filter Topology Laplacian
open scoped NNReal ENNReal ContDiff RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational.Kernel

variable {n : ℕ}

/-! ### Coordinates -/

/-- The standard orthonormal basis of `ℝⁿ`. -/
abbrev stdBasis (n : ℕ) : OrthonormalBasis (Fin n) ℝ (Rn n) := EuclideanSpace.basisFun (Fin n) ℝ

theorem inner_gradient_left (f : Rn n → ℝ) (y w : Rn n) :
    ⟪gradient f y, w⟫ = fderiv ℝ f y w := by
  simp [gradient, InnerProductSpace.toDual_symm_apply]

theorem inner_gradient_right (f : Rn n → ℝ) (y w : Rn n) :
    ⟪w, gradient f y⟫ = fderiv ℝ f y w := by
  rw [real_inner_comm, inner_gradient_left]

theorem inner_eq_sum (a c : Rn n) : ⟪a, c⟫ = ∑ i, ⟪a, stdBasis n i⟫ * ⟪stdBasis n i, c⟫ :=
  ((stdBasis n).sum_inner_mul_inner a c).symm

/-- `⟪∇f, ∇g⟫ = Σᵢ ∂ᵢf ∂ᵢg`. -/
theorem inner_gradient_gradient_eq_sum (f g : Rn n → ℝ) (y : Rn n) :
    ⟪gradient f y, gradient g y⟫ =
      ∑ i, fderiv ℝ f y (stdBasis n i) * fderiv ℝ g y (stdBasis n i) := by
  rw [inner_eq_sum]
  simp only [inner_gradient_left, inner_gradient_right]

/-- `‖∇f‖² = Σᵢ (∂ᵢf)²`. -/
theorem norm_gradient_sq_eq_sum (f : Rn n → ℝ) (y : Rn n) :
    ‖gradient f y‖ ^ 2 = ∑ i, fderiv ℝ f y (stdBasis n i) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_gradient_gradient_eq_sum]
  simp only [sq]

/-- `∇f = Σᵢ (∂ᵢf) eᵢ`. -/
theorem gradient_eq_sum (f : Rn n → ℝ) (y : Rn n) :
    gradient f y = ∑ i, fderiv ℝ f y (stdBasis n i) • stdBasis n i := by
  conv_lhs => rw [← (stdBasis n).sum_repr' (gradient f y)]
  simp only [inner_gradient_right]

/-- `Δf = Σᵢ ∂ᵢ∂ᵢ f`, with no regularity assumption (both sides use `fderiv`). -/
theorem laplacian_apply_eq_sum (f : Rn n → ℝ) (y : Rn n) :
    Δ f y = ∑ i, fderiv ℝ (fderiv ℝ f) y (stdBasis n i) (stdBasis n i) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f (stdBasis n)]
  simp [iteratedFDeriv_two_apply]

/-- `∂_v (∂_w f) = D²f(v, w)` where `fderiv f` is differentiable. -/
theorem fderiv_fderiv_apply {f : Rn n → ℝ} {y : Rn n} (hf : DifferentiableAt ℝ (fderiv ℝ f) y)
    (v w : Rn n) : fderiv ℝ (fun z => fderiv ℝ f z w) y v = fderiv ℝ (fderiv ℝ f) y v w := by
  rw [fderiv_clm_apply hf (differentiableAt_const w)]
  simp

theorem differentiableAt_fderiv_of_contDiffOn {V : Set (Rn n)} (hV : IsOpen V) {f : Rn n → ℝ}
    (hf : ContDiffOn ℝ 2 f V) {y : Rn n} (hy : y ∈ V) : DifferentiableAt ℝ (fderiv ℝ f) y :=
  ((hf.fderiv_of_isOpen hV (m := 1) (by norm_num)).contDiffAt
    (hV.mem_nhds hy)).differentiableAt (by norm_num)

/-- `y ↦ ∂_w f(y)` is `C¹` on `V` when `f` is `C²` on the open set `V`. -/
theorem contDiffOn_fderiv_apply {V : Set (Rn n)} (hV : IsOpen V) {f : Rn n → ℝ}
    (hf : ContDiffOn ℝ 2 f V) (w : Rn n) : ContDiffOn ℝ 1 (fun z => fderiv ℝ f z w) V :=
  (hf.fderiv_of_isOpen hV (m := 1) (by norm_num)).clm_apply contDiffOn_const

/-! ### Lipschitz bounds and integrability -/

theorem locallyLipschitzOn_of_contDiffOn {V : Set (Rn n)} (hV : IsOpen V) {f : Rn n → ℝ}
    (hf : ContDiffOn ℝ 1 f V) : LocallyLipschitzOn V f := by
  intro y hy
  obtain ⟨K, t, ht, hK⟩ := (hf.contDiffAt (hV.mem_nhds hy)).exists_lipschitzOnWith
  exact ⟨K, t, mem_nhdsWithin_of_mem_nhds ht, hK⟩

/-- A locally Lipschitz function on an open set has bounded `fderiv` on compact subsets. -/
theorem exists_bound_fderiv {Ω : Set (Rn n)} (hΩ : IsOpen Ω) {f : Rn n → ℝ}
    (hf : LocallyLipschitzOn Ω f) {K : Set (Rn n)} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ L : ℝ≥0, ∀ y ∈ K, ‖fderiv ℝ f y‖ ≤ L := by
  obtain ⟨δ, hδ, hδΩ⟩ := hK.exists_cthickening_subset_open hΩ hKΩ
  obtain ⟨L, hL⟩ := (hf.mono hδΩ).exists_lipschitzOnWith_of_compact (hK.cthickening (r := δ))
  refine ⟨L, fun y hy => norm_fderiv_le_of_lipschitzOn ℝ ?_ hL⟩
  exact mem_of_superset ((isOpen_thickening).mem_nhds (self_subset_thickening hδ K hy))
    (thickening_subset_cthickening δ K)

/-- A function bounded on a compact set `K` and vanishing off `K` is integrable. -/
theorem integrable_of_bound_of_isCompact {f : Rn n → ℝ} {K : Set (Rn n)} (hK : IsCompact K)
    (hf : AEStronglyMeasurable f (volume.restrict K)) {M : ℝ} (hM : ∀ y ∈ K, ‖f y‖ ≤ M)
    (h0 : ∀ y ∉ K, f y = 0) : Integrable f := by
  have hI : IntegrableOn f K :=
    IntegrableOn.of_bound hK.measure_lt_top hf M
      ((ae_restrict_iff' hK.measurableSet).2 (.of_forall hM))
  exact hI.integrable_of_forall_notMem_eq_zero h0

/-- A product `f h` with `f`, `h` bounded on a compact `K` and `h = 0` off `K` is integrable. -/
theorem integrable_mul_of_isCompact {f h : Rn n → ℝ} {K : Set (Rn n)} (hK : IsCompact K)
    (hm : AEStronglyMeasurable (fun y => f y * h y) (volume.restrict K)) {A B : ℝ}
    (hf : ∀ y ∈ K, ‖f y‖ ≤ A) (hh : ∀ y ∈ K, ‖h y‖ ≤ B) (h0 : ∀ y ∉ K, h y = 0) :
    Integrable fun y => f y * h y := by
  refine integrable_of_bound_of_isCompact hK hm (M := A * B) (fun y hy => ?_)
    (fun y hy => by simp [h0 y hy])
  rw [norm_mul]
  exact mul_le_mul (hf y hy) (hh y hy) (norm_nonneg _) ((norm_nonneg _).trans (hf y hy))

/-- `|∂_v g| ≤ C ‖v‖` for `g` `C`-Lipschitz. -/
theorem norm_fderiv_apply_le {g : Rn n → ℝ} {C : ℝ≥0} (hg : LipschitzWith C g) (y v : Rn n) :
    ‖fderiv ℝ g y v‖ ≤ C * ‖v‖ :=
  ((fderiv ℝ g y).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hg) (norm_nonneg _))

theorem fderiv_eq_zero_of_notMem_tsupport {g : Rn n → ℝ} {y : Rn n} (hy : y ∉ tsupport g) :
    fderiv ℝ g y = 0 :=
  fderiv_of_notMem_tsupport (𝕜 := ℝ) hy

theorem norm_gradient_eq (f : Rn n → ℝ) (y : Rn n) : ‖gradient f y‖ = ‖fderiv ℝ f y‖ := by
  rw [gradient, LinearIsometryEquiv.norm_map]

theorem norm_stdBasis (i : Fin n) : ‖stdBasis n i‖ = 1 := (stdBasis n).orthonormal.1 i

theorem norm_apply_stdBasis_le (L : Rn n →L[ℝ] ℝ) (i : Fin n) : ‖L (stdBasis n i)‖ ≤ ‖L‖ :=
  (L.le_opNorm _).trans_eq (by rw [norm_stdBasis, mul_one])

theorem norm_gradient_le_of_lipschitz {g : Rn n → ℝ} {C : ℝ≥0} (hg : LipschitzWith C g)
    (y : Rn n) : ‖gradient g y‖ ≤ C := by
  rw [norm_gradient_eq]
  exact norm_fderiv_le_of_lipschitz ℝ hg

theorem gradient_eq_zero_of_notMem_tsupport {g : Rn n → ℝ} {y : Rn n} (hy : y ∉ tsupport g) :
    gradient g y = 0 := by
  simp [gradient, fderiv_eq_zero_of_notMem_tsupport hy]

/-- Measurability of `Φ ∘ u · m` on a set where `u` is continuous. -/
theorem aestronglyMeasurable_comp_mul {K : Set (Rn n)} (hK : MeasurableSet K) {u : Rn n → ℝ}
    (hu : ContinuousOn u K) {Φ : ℝ → ℝ} (hΦ : Continuous Φ) {m : Rn n → ℝ} (hm : Measurable m) :
    AEStronglyMeasurable (fun y => Φ (u y) * m y) (volume.restrict K) :=
  ((hΦ.comp_continuousOn hu).aestronglyMeasurable hK).mul hm.aestronglyMeasurable

/-- Dominated convergence for functions supported in a compact set, with a constant bound. -/
theorem tendsto_integral_of_isCompact {K : Set (Rn n)} (hK : IsCompact K) {G : ℕ → Rn n → ℝ}
    {g : Rn n → ℝ} (hG0 : ∀ k, ∀ y ∉ K, G k y = 0) (hg0 : ∀ y ∉ K, g y = 0)
    (hGm : ∀ k, AEStronglyMeasurable (G k) (volume.restrict K)) {B : ℝ}
    (hB : ∀ k, ∀ y ∈ K, ‖G k y‖ ≤ B)
    (hlim : ∀ y ∈ K, Tendsto (fun k => G k y) atTop (𝓝 (g y))) :
    Tendsto (fun k => ∫ y, G k y) atTop (𝓝 (∫ y, g y)) := by
  have e1 : (fun k => ∫ y, G k y) = fun k => ∫ y in K, G k y :=
    funext fun k => (setIntegral_eq_integral_of_forall_compl_eq_zero (hG0 k)).symm
  rw [e1, ← setIntegral_eq_integral_of_forall_compl_eq_zero hg0]
  refine tendsto_integral_of_dominated_convergence (fun _ => B) hGm
    (integrableOn_const hK.measure_lt_top.ne) (fun k => ?_) ?_
  · exact (ae_restrict_iff' hK.measurableSet).2 (.of_forall (hB k))
  · exact (ae_restrict_iff' hK.measurableSet).2 (.of_forall hlim)

/-! ### Products of Lipschitz functions -/

/-- If `f` is `Lf`-Lipschitz, `|f| ≤ A`, and `f = 0` off `K`, and `g` is `Lg`-Lipschitz with
`‖g‖ ≤ M` on `K`, then `f • g` is `(A Lg + M Lf)`-Lipschitz. `g` is only controlled on `K`. -/
theorem lipschitzWith_smul_of_support {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Rn n → ℝ} {g : Rn n → F} {K : Set (Rn n)} {Lf Lg : ℝ≥0} {A M : ℝ}
    (hf : LipschitzWith Lf f) (hfA : ∀ y, |f y| ≤ A) (hf0 : ∀ y ∉ K, f y = 0)
    (hg : LipschitzOnWith Lg g K) (hgM : ∀ y ∈ K, ‖g y‖ ≤ M) :
    LipschitzWith (Real.toNNReal (A * Lg + M * Lf)) (fun y => f y • g y) := by
  have hA : 0 ≤ A := (abs_nonneg _).trans (hfA 0)
  -- the estimate when `a ∈ K`
  have key : ∀ a ∈ K, ∀ b, ‖f a • g a - f b • g b‖ ≤ (A * Lg + M * Lf) * dist a b := by
    intro a ha b
    have hM : 0 ≤ M := (norm_nonneg _).trans (hgM a ha)
    have e : f a • g a - f b • g b = (f a - f b) • g a + f b • (g a - g b) := by
      rw [sub_smul, smul_sub]; abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul]
    have h1 : ‖f a - f b‖ * ‖g a‖ ≤ Lf * dist a b * M := by
      rw [← dist_eq_norm]
      exact mul_le_mul (hf.dist_le_mul a b) (hgM a ha) (norm_nonneg _)
        (mul_nonneg Lf.2 dist_nonneg)
    have h2 : ‖f b‖ * ‖g a - g b‖ ≤ A * (Lg * dist a b) := by
      by_cases hb : b ∈ K
      · rw [← dist_eq_norm, Real.norm_eq_abs]
        exact mul_le_mul (hfA b) (hg.dist_le_mul a ha b hb) dist_nonneg hA
      · rw [hf0 b hb, norm_zero, zero_mul]
        exact mul_nonneg hA (mul_nonneg Lg.2 dist_nonneg)
    nlinarith
  refine LipschitzWith.of_dist_le_mul fun a b => ?_
  rw [dist_eq_norm]
  have hK : (A * Lg + M * Lf) ≤ (Real.toNNReal (A * Lg + M * Lf) : ℝ) := Real.le_coe_toNNReal _
  by_cases ha : a ∈ K
  · exact (key a ha b).trans (mul_le_mul_of_nonneg_right hK dist_nonneg)
  · by_cases hb : b ∈ K
    · rw [norm_sub_rev, dist_comm]
      exact (key b hb a).trans (mul_le_mul_of_nonneg_right hK dist_nonneg)
    · simp only [hf0 a ha, hf0 b hb, zero_smul, sub_zero, norm_zero]
      exact mul_nonneg (NNReal.coe_nonneg _) dist_nonneg

/-! ### Integration by parts -/

/-- **IBP against a `C²` function.** For `u ∈ C²(V)` and `g` Lipschitz with compact support in `V`,
`∫ ⟪∇u, ∇g⟫ = −∫ g Δu`. From Lipschitz integration by parts (`Registry.integral_mul_fderiv_eq_neg`)
applied to `∂ᵢu`, coordinate by coordinate. -/
theorem integral_inner_gradient_eq_neg_laplacian {V : Set (Rn n)} (hV : IsOpen V)
    {u g : Rn n → ℝ} (hu : ContDiffOn ℝ 2 u V) (hg : ∃ C, LipschitzWith C g)
    (hgc : HasCompactSupport g) (hgV : tsupport g ⊆ V) :
    ∫ y, ⟪gradient u y, gradient g y⟫ = -∫ y, g y * Δ u y := by
  set b := stdBasis n
  obtain ⟨C, hC⟩ := hg
  set p : Fin n → Rn n → ℝ := fun i z => fderiv ℝ u z (b i) with hp
  have hp1 : ∀ i, ContDiffOn ℝ 1 (p i) V := fun i => contDiffOn_fderiv_apply hV hu (b i)
  set q : Fin n → Rn n → ℝ := fun i z => fderiv ℝ (p i) z (b i) with hq
  have hqc : ∀ i, ContinuousOn (q i) V := fun i =>
    ((hp1 i).continuousOn_fderiv_of_isOpen hV le_rfl).clm_apply continuousOn_const
  set K := tsupport g
  have hK : IsCompact K := hgc
  have hg0 : ∀ y ∉ K, g y = 0 := fun y hy => image_eq_zero_of_notMem_tsupport hy
  obtain ⟨Mg, hMg⟩ := hK.exists_bound_of_continuousOn hC.continuous.continuousOn
  -- pointwise identities
  have hlhs : ∀ y, ⟪gradient u y, gradient g y⟫ = ∑ i, p i y * fderiv ℝ g y (b i) := fun y =>
    inner_gradient_gradient_eq_sum u g y
  have hrhs : ∀ y, g y * Δ u y = ∑ i, g y * q i y := by
    intro y
    rw [← Finset.mul_sum]
    by_cases hy : y ∈ V
    · rw [laplacian_apply_eq_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hq, hp]
      exact (fderiv_fderiv_apply (differentiableAt_fderiv_of_contDiffOn hV hu hy) _ _).symm
    · rw [hg0 y (fun h => hy (hgV h)), zero_mul, zero_mul]
  -- integrability
  have hint1 : ∀ i, Integrable fun y => p i y * fderiv ℝ g y (b i) := by
    intro i
    obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn ((hp1 i).continuousOn.mono hgV)
    refine integrable_mul_of_isCompact hK
      ((measurable_fderiv_apply_const ℝ u (b i)).mul
        (measurable_fderiv_apply_const ℝ g (b i))).aestronglyMeasurable hA
      (B := C) (fun y _ => (norm_apply_stdBasis_le _ i).trans (norm_fderiv_le_of_lipschitz ℝ hC)) ?_
    intro y hy
    rw [fderiv_eq_zero_of_notMem_tsupport hy, zero_apply]
  have hint2 : ∀ i, Integrable fun y => g y * q i y := by
    intro i
    obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn ((hqc i).mono hgV)
    have := integrable_mul_of_isCompact hK
      ((measurable_fderiv_apply_const ℝ (p i) (b i)).mul
        hC.continuous.measurable).aestronglyMeasurable hA hMg hg0
    simpa only [mul_comm] using this
  -- Lipschitz integration by parts, coordinate by coordinate
  have hibp : ∀ i, ∫ y, p i y * fderiv ℝ g y (b i) = -∫ y, g y * q i y := fun i =>
    Registry.integral_mul_fderiv_eq_neg hV
      (locallyLipschitzOn_of_contDiffOn hV (hp1 i)) ⟨C, hC⟩ hgc hgV (b i)
  simp_rw [hlhs, hrhs]
  rw [integral_finsetSum _ (fun i _ => hint1 i), integral_finsetSum _ (fun i _ => hint2 i),
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => hibp i

/-- **IBP against a test function.** For `f` locally Lipschitz on `Ω` and `φ ∈ C^∞_c(Ω)`,
`∫ f Δφ = −∫ ⟪∇f, ∇φ⟫`. -/
theorem integral_mul_laplacian_eq_neg {Ω : Set (Rn n)} (hΩ : IsOpen Ω) {f φ : Rn n → ℝ}
    (hf : LocallyLipschitzOn Ω f) (hφ : IsTestFunction Ω φ) :
    ∫ y, f y * Δ φ y = -∫ y, ⟪gradient f y, gradient φ y⟫ := by
  set b := stdBasis n
  obtain ⟨hφs, hφc, hφΩ⟩ := hφ
  set K := tsupport φ
  have hK : IsCompact K := hφc
  set g : Fin n → Rn n → ℝ := fun i z => fderiv ℝ φ z (b i) with hg
  have hgs : ∀ i, ContDiff ℝ ∞ (g i) := fun i =>
    (hφs.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hgK : ∀ i, tsupport (g i) ⊆ K := fun i =>
    (tsupport_fderiv_apply_subset ℝ (b i)).trans subset_rfl
  have hgc : ∀ i, HasCompactSupport (g i) := fun i => hK.of_isClosed_subset
    (isClosed_tsupport _) (hgK i)
  have hgL : ∀ i, ∃ C, LipschitzWith C (g i) := fun i =>
    (hgs i).lipschitzWith_of_hasCompactSupport (hgc i) (by simp)
  -- pointwise identities
  have hl : ∀ y, f y * Δ φ y = ∑ i, f y * fderiv ℝ (g i) y (b i) := by
    intro y
    rw [laplacian_apply_eq_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hg, fderiv_fderiv_apply ((hφs.fderiv_right (m := ∞) (by simp)).differentiable
      (by simp) y)]
  have hr : ∀ y, ⟪gradient f y, gradient φ y⟫ = ∑ i, g i y * fderiv ℝ f y (b i) := by
    intro y
    rw [inner_gradient_gradient_eq_sum]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  -- integrability
  obtain ⟨L, hL⟩ := exists_bound_fderiv hΩ hf hK hφΩ
  obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn (hf.continuousOn.mono hφΩ)
  have hint1 : ∀ i, Integrable fun y => f y * fderiv ℝ (g i) y (b i) := by
    intro i
    have hc : Continuous fun y => fderiv ℝ (g i) y (b i) :=
      ((hgs i).continuous_fderiv (by simp)).clm_apply continuous_const
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
    refine integrable_mul_of_isCompact hK ?_ hA hB ?_
    · exact ((hf.continuousOn.mono hφΩ).aestronglyMeasurable hK.measurableSet).mul
        hc.aestronglyMeasurable
    · intro y hy
      rw [fderiv_eq_zero_of_notMem_tsupport (fun h => hy (hgK i h)),
        zero_apply]
  have hint2 : ∀ i, Integrable fun y => g i y * fderiv ℝ f y (b i) := by
    intro i
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (hgs i).continuous.continuousOn
    have := integrable_mul_of_isCompact hK
      ((measurable_fderiv_apply_const ℝ f (b i)).mul
        (hgs i).continuous.measurable).aestronglyMeasurable
      (A := L) (fun y hy => (norm_apply_stdBasis_le _ i).trans (hL y hy)) hB
      (fun y hy => image_eq_zero_of_notMem_tsupport (fun h => hy (hgK i h)))
    simpa only [mul_comm] using this
  have hibp : ∀ i, ∫ y, f y * fderiv ℝ (g i) y (b i) = -∫ y, g i y * fderiv ℝ f y (b i) :=
    fun i => Registry.integral_mul_fderiv_eq_neg hΩ hf (hgL i) (hgc i) ((hgK i).trans hφΩ) (b i)
  simp_rw [hl, hr]
  rw [integral_finsetSum _ (fun i _ => hint1 i), integral_finsetSum _ (fun i _ => hint2 i),
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => hibp i

end InnerVariational.Kernel
