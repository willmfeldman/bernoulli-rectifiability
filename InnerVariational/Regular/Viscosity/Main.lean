/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Regular.Perimeter
public import InnerVariational.Regular.HarmonicCone
public import InnerVariational.Blowup.ExplicitForm
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Real.StarOrdered
import InnerVariational.Regular.Density
import InnerVariational.Registry.BV
import InnerVariational.Regular.ChiInterior
import InnerVariational.Regular.ZeroGradient
import InnerVariational.Monotonicity.HighestDensity
public import InnerVariational.Defs.HighestDensity
import InnerVariational.Monotonicity.Density
import InnerVariational.Monotonicity.Blowup
import InnerVariational.Registry.Harmonic
public import InnerVariational.Kernel.BV
import InnerVariational.Kernel.Subharmonic
public import InnerVariational.Defs.Solutions
import InnerVariational.Kernel.IBP
import InnerVariational.Basic.SphereIntegral
public import InnerVariational.Regular.Viscosity.Classification

/-!
# Lemma 8.3: variational solutions are viscosity solutions off `Σ^H`

Lemma 8.3 of D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and
compactness for non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025),
no. 3, DOI 10.1002/cpa.22226; arXiv:2306.10131 (numbering of arXiv v2). Let `(u, χ)` be a
variational solution on `Ω`, `2 ≤ n`, with `Σ^H = ∅`. Then `u` is a viscosity solution on `Ω`
(`IsViscositySolution`). The paper's Definition 8.1 of viscosity solution concludes `|∇u| ≤ 1`
(resp. `|∇u| ≥ 1`) at the touching point; since `u` is not differentiable at free boundary
points, the conclusion used here is `|∇φ(x)| ≤ 1` (resp. `|∇φ(x)| ≥ 1`) for the touching
function `φ`.

## Main results

* `IsVariationalSolution.isViscositySolution`: the lemma as stated in the paper.
* `IsVariationalSolution.isViscositySolution_diff_sigmaH`: `u` is a viscosity solution on the open
  set `Ω \ Σ^H`, for any variational solution.
* `IsVariationalSolution.norm_gradient_le_one_of_le`,
  `IsVariationalSolution.one_le_norm_gradient_of_le_max`: the pointwise statements at a free
  boundary point `x ∉ Σ^H`.

## Proof

Let `φ` touch `u` from below (resp. `φ₊` from above) at `x ∈ Ω ∩ ∂{u > 0}`, `x ∉ Σ^H`, and let
`p = ∇φ(x)`, `β = |p|`, `e = p / β`.

1. `M_x(u; 0+) = m ∈ [|B_1|/2, |B_1|)` (Lemma 8.1 and `x ∉ Σ^H`). Along `r_k → 0+` the blow-ups
   `u_{x,r_k} → u₀` locally uniformly (Proposition 3.5); `u₀` is Lipschitz, one-homogeneous,
   harmonic on
   `{u₀ > 0}`, and `|{u₀ > 0} ∩ B_1| ≤ m`. By Lemma 8.1's last claim, `u₀ ≢ 0`.
2. `χ_{x,r_k} → χ₀` in `L¹_loc` along a subsequence (Lemma 3.3 and BV compactness, L. C. Evans
   and R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, rev. ed., CRC Press,
   2015, Theorem 5.5), and the
   inner variation passes to the limit (`exists_chi_blowup`): `∫ Q_ξ(∇u₀) + ∫ χ₀ div ξ = 0`,
   `χ₀ ∈ {0, 1}`, `χ₀ ≥ χ_{u₀ > 0}`, `∫_{B_1} χ₀ = m`.
3. `φ(x + r y)/r → ⟪p, y⟫`, so `⟪p, y⟫ ≤ u₀(y)` (resp. `u₀(y) ≤ ⟪p, y⟫₊`).
4. Classification (the proof of Lemma 8.3, classification of `u₀`): `u₀ = a ⟪y, e⟫₊`, `a > 0`
   (`eq_mul_max_of_le_max`, `eq_mul_max_of_le`). From above, `{u₀ > 0}` lies in the half-space
   `{⟪y, e⟫ > 0}`, so each component has volume `≤ |B_1|/2` and the equality case of Sperner's
   inequality (E. Sperner, Jr., *Zur Symmetrisierung von Funktionen auf Sphären*, Math. Z. 134
   (1973), 317–327) applies. From below, the component through `e` contains the half-space; it
   *is* the half-space (`connectedComponentIn_eq_halfSpace`, `Regular/HarmonicCone.lean`; the
   paper uses domain monotonicity of the first Dirichlet eigenvalue), and any further
   component would add `|B_1|/2` by Sperner's inequality, contradicting
   `|{u₀ > 0} ∩ B_1| ≤ m < |B_1|`.
5. The half-space computation (end of the proof of Lemma 8.3, `eq_one_of_halfSpace`): `a = 1`.
6. Hence `β = ⟪p, e⟫ ≤ u₀(e) = 1` (resp. `1 = u₀(e) ≤ β`).

Steps 4 and 5 and the deviations from the paper's argument there are in
`Regular/Viscosity/Classification.lean`.
-/

open MeasureTheory Metric Set Filter Topology InnerProductSpace
open scoped NNReal ENNReal RealInnerProductSpace ContDiff

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

namespace IsVariationalSolution

variable {Ω : Set (Rn n)} {C : ℝ≥0} {u χ : Rn n → ℝ} {x : Rn n}

/-- **Blow-up pairs** (proof of Lemma 8.3). Along a blow-up sequence `u_{x,r_k} → u₀` with
`M_x(r) → m`, a subsequence of `χ_{x,r_k}` converges a.e. on `B_{3/2}` to some `χ₀` with

* `χ₀ ∈ {0, 1}` a.e. on `B_1`, and `χ₀ = 1` a.e. on `B_1 ∩ {u₀ > 0}`;
* `∫_{B_1} χ₀ = m`;
* the limit domain variation identity `∫ (|∇u₀|² div ξ − 2 ∇u₀·Dξ ∇u₀) + ∫ χ₀ div ξ = 0` for all
  `ξ ∈ C^∞_c(B_1; ℝⁿ)`.

Uses Lemma 3.3, BV compactness and the strong `L²_loc` convergence of gradients (proof of
Proposition 3.5). -/
theorem exists_chi_blowup [NeZero n] (h : IsVariationalSolution Ω C u χ) (hx : x ∈ Ω) {m : ℝ}
    (hm : Tendsto (monotonicityM u χ x) (𝓝[>] 0) (𝓝 m))
    (hd : Tendsto (fun r => (r ^ n)⁻¹ * ∫ y in ball x r, χ y) (𝓝[>] 0) (𝓝 m))
    {r : ℕ → ℝ} (hr : ∀ k, 0 < r k) (hr0 : Tendsto r atTop (𝓝 0)) {u₀ : Rn n → ℝ}
    (hconv : TendstoLocallyUniformly (fun k => oneHomRescale u x (r k)) u₀ atTop) :
    ∃ f₀ : Rn n → ℝ, Measurable f₀ ∧
      (∀ᵐ y ∂(volume.restrict (ball (0 : Rn n) 1)), f₀ y = 0 ∨ f₀ y = 1) ∧
      (∀ᵐ y ∂(volume.restrict (ball (0 : Rn n) 1)), 0 < u₀ y → f₀ y = 1) ∧
      ∫ y in ball (0 : Rn n) 1, f₀ y = m ∧
      ∀ ξ, IsSmoothTestField (ball (0 : Rn n) 1) ξ →
        (∫ y, Kernel.gradVariation u₀ ξ y) + ∫ y, f₀ y * divergence ξ y = 0 := by
  obtain ⟨R, hR0, hR⟩ := h.exists_ball_subset hx
  obtain ⟨k₀, hw, hconv', -⟩ := h.blowup_window hR0 hR hm hr hr0 hconv (ρ := 4) (by norm_num)
  set w : ℕ → Rn n → ℝ := fun j => oneHomRescale u x (r (j + k₀)) with hwdef
  set χw : ℕ → Rn n → ℝ := fun j => chiRescale χ x (r (j + k₀)) with hχwdef
  set V : Set (Rn n) := ball 0 (3 * 1 / 2) with hVdef
  have hV4 : V ⊆ ball 0 4 := ball_subset_ball (by norm_num)
  have hB1V : ball (0 : Rn n) 1 ⊆ V := ball_subset_ball (by norm_num)
  set f : ℕ → Rn n → ℝ := fun j => (ball (0 : Rn n) 4).indicator (χw j) with hfdef
  have hfm : ∀ j, Measurable (f j) := fun j => (hw j).measurable_chi
  have hf01 : ∀ j, ∀ y ∈ ball (0 : Rn n) 4, f j y = 0 ∨ f j y = 1 := fun j y hy => by
    simp only [hfdef, indicator_of_mem hy]
    exact (hw j).chi_mem y hy
  have hfb : ∀ j, ∀ y ∈ V, |f j y| ≤ 1 := fun j y hy => by
    rcases hf01 j y (hV4 hy) with h0 | h0 <;> simp [h0]
  have hfχ : ∀ j (ξ : Rn n → Rn n), tsupport ξ ⊆ ball (0 : Rn n) 4 →
      ∫ y, f j y * divergence ξ y = ∫ y, χw j y * divergence ξ y := by
    intro j ξ hξ
    congr 1
    funext y
    by_cases hy : y ∈ ball (0 : Rn n) 4
    · simp only [hfdef, indicator_of_mem hy]
    · simp only [hfdef, indicator_of_notMem hy,
        divergence_eq_zero_of_notMem_tsupport fun h' => hy (hξ h'), mul_zero]
  -- Lemma 3.3 on `B_{3/2}` for the rescaled solutions
  have hcl : closedBall (0 : Rn n) (2 * 1) ⊆ ball 0 4 := closedBall_subset_ball (by norm_num)
  have hTV : ∀ K, IsCompact K → K ⊆ V → ∃ W, IsOpen W ∧ K ⊆ W ∧ W ⊆ V ∧ ∃ P : ℝ, ∀ j,
      ∀ ψ : Rn n → Rn n, ContDiff ℝ 1 ψ → HasCompactSupport ψ → tsupport ψ ⊆ W →
        (∀ y, ‖ψ y‖ ≤ 1) → ∫ y, f j y * divergence ψ y ≤ P := by
    intro K _ hKV
    refine ⟨V, isOpen_ball, hKV, subset_rfl,
      2 ^ (n + 1) * volume.real (ball (0 : Rn n) 1) * C ^ 2 * 1 * 1 ^ (n - 1),
      fun j ψ hψ hψc hψV hψ1 => ?_⟩
    have hψL : IsLipTestField (ball (0 : Rn n) (3 * 1 / 2)) ψ :=
      ⟨ContDiff.lipschitzWith_of_hasCompactSupport hψc hψ one_ne_zero, hψc, hψV⟩
    rw [hfχ j ψ (hψV.trans hV4)]
    exact (le_abs_self _).trans ((hw j).chi_divergence_bound one_pos hcl hψL hψ1)
  obtain ⟨φ, hφ, f₀, hf₀m, -, hf₀ae⟩ :=
    Registry.exists_subseq_tendsto_of_integral_mul_divergence_le isOpen_ball f hfm hfb hTV
  have hf₀ae1 : ∀ᵐ y ∂(volume.restrict (ball (0 : Rn n) 1)),
      Tendsto (fun j => f (φ j) y) atTop (𝓝 (f₀ y)) :=
    ae_restrict_of_ae_restrict_of_subset hB1V hf₀ae
  -- `f₀ ∈ {0, 1}` a.e. on `B_1`
  have h01 : ∀ᵐ y ∂(volume.restrict (ball (0 : Rn n) 1)), f₀ y = 0 ∨ f₀ y = 1 := by
    filter_upwards [hf₀ae1, ae_restrict_mem measurableSet_ball] with y hy hyB
    have hcl01 : IsClosed ({0, 1} : Set ℝ) := (Set.toFinite _).isClosed
    exact hcl01.mem_of_tendsto hy (.of_forall fun j => hf01 (φ j) y (hV4 (hB1V hyB)))
  -- `f₀ = 1` a.e. on `{u₀ > 0}`
  have hposae : ∀ᵐ y ∂(volume.restrict (ball (0 : Rn n) 4)),
      ∀ j, posIndicator (w j) y ≤ χw j y :=
    ae_all_iff.2 fun j => (hw j).posIndicator_le_chi
  have hpos : ∀ᵐ y ∂(volume.restrict (ball (0 : Rn n) 1)), 0 < u₀ y → f₀ y = 1 := by
    filter_upwards [hf₀ae1, ae_restrict_of_ae_restrict_of_subset (hB1V.trans hV4) hposae,
      ae_restrict_mem measurableSet_ball] with y hy hyp hyB hu₀
    have hy4 : y ∈ ball (0 : Rn n) 4 := hV4 (hB1V hyB)
    have hev : ∀ᶠ j in atTop, f (φ j) y = 1 := by
      have hc := (hconv'.tendsto_at hy4).comp hφ.tendsto_atTop
      filter_upwards [hc.eventually (lt_mem_nhds hu₀)] with j hj
      have h1 := hyp (φ j)
      rw [posIndicator_of_pos hj] at h1
      simp only [hfdef, indicator_of_mem hy4, hχwdef] at h1 ⊢
      rcases (hw (φ j)).chi_mem y hy4 with h0 | h0
      · rw [h0] at h1
        norm_num at h1
      · exact h0
    exact tendsto_nhds_unique hy (tendsto_const_nhds.congr' (hev.mono fun j hj => hj.symm))
  -- `∫_{B_1} f₀ = m`
  have hm1 : Tendsto (fun j => ∫ y in ball (0 : Rn n) 1, f (φ j) y) atTop
      (𝓝 (∫ y in ball (0 : Rn n) 1, f₀ y)) :=
    tendsto_integral_of_dominated_convergence (μ := volume.restrict (ball (0 : Rn n) 1))
      (F := fun j y => f (φ j) y) (f := f₀) (fun _ => (1 : ℝ))
      (fun j => (hfm _).aestronglyMeasurable) (integrableOn_const measure_ball_lt_top.ne)
      (fun j => (ae_restrict_iff' measurableSet_ball).2 (.of_forall fun y hy => by
        rw [Real.norm_eq_abs]; exact hfb _ y (hB1V hy)))
      hf₀ae1
  have hm2 : Tendsto (fun j => ∫ y in ball (0 : Rn n) 1, f (φ j) y) atTop (𝓝 m) := by
    have := ((tendsto_add_atTop_iff_nat k₀).2
      (Regular.tendsto_setIntegral_chiRescale hd hr hr0)).comp hφ.tendsto_atTop
    refine this.congr fun j => ?_
    simp only [Function.comp_apply]
    refine setIntegral_congr_fun measurableSet_ball fun y hy => ?_
    simp only [hfdef, indicator_of_mem (hB1V.trans hV4 hy), hχwdef]
  refine ⟨f₀, hf₀m, h01, hpos, tendsto_nhds_unique hm1 hm2, fun ξ hξ => ?_⟩
  -- the limit identity
  obtain ⟨⟨D, hD⟩, hξc, hξB⟩ := hξ.isLipTestField
  have hξ4 : IsLipTestField (ball (0 : Rn n) 4) ξ := hξ.isLipTestField.mono (hB1V.trans hV4)
  have hK4 : tsupport ξ ⊆ ball (0 : Rn n) 4 := hξB.trans (hB1V.trans hV4)
  have h1 : Tendsto (fun j => ∫ y, f (φ j) y * divergence ξ y) atTop
      (𝓝 (∫ y, f₀ y * divergence ξ y)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun y => (tsupport ξ).indicator (fun _ => (n : ℝ) * D) y)
      (fun j => ((hfm _).mul (Kernel.measurable_divergence ξ)).aestronglyMeasurable)
      ((integrableOn_const hξc.isCompact.measure_lt_top.ne).integrable_indicator
        (isClosed_tsupport ξ).measurableSet) (fun j => .of_forall fun y => ?_) ?_
    · dsimp only
      by_cases hy : y ∈ tsupport ξ
      · rw [indicator_of_mem hy, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        calc |f (φ j) y| * |divergence ξ y| ≤ 1 * ((n : ℝ) * D) :=
              mul_le_mul (hfb _ y (hB1V (hξB hy))) (Kernel.abs_divergence_le hD y)
                (abs_nonneg _) zero_le_one
          _ = (n : ℝ) * D := one_mul _
      · rw [indicator_of_notMem hy, divergence_eq_zero_of_notMem_tsupport hy, mul_zero,
          norm_zero]
    · filter_upwards [(ae_restrict_iff' measurableSet_ball).1 hf₀ae] with y hy
      by_cases hyV : y ∈ V
      · exact (hy hyV).mul_const _
      · have : y ∉ tsupport ξ := fun h' => hyV (hB1V (hξB h'))
        simp [divergence_eq_zero_of_notMem_tsupport this]
  have hg := tendsto_setIntegral_norm_gradient_sub_sq (fun j => (hw j).isLipHarmonicPos)
    (fun j => (hw j).lipschitzOnWith) hconv' hξc.isCompact hK4
  have h2 : Tendsto (fun j => ∫ y, Kernel.gradVariation (w (φ j)) ξ y) atTop
      (𝓝 (∫ y, Kernel.gradVariation u₀ ξ y)) :=
    Regular.tendsto_integral_gradVariation hD hξc (L := C)
      (fun j y hy => (hw (φ j)).norm_gradient_le (hK4 hy))
      (fun y _ => Kernel.norm_gradient_le_of_lipschitz (blowup_lipschitzWith h hx hr hr0 hconv) y)
      (hg.comp hφ.tendsto_atTop)
  have h3 : ∀ j, ∫ y, f (φ j) y * divergence ξ y = -∫ y, Kernel.gradVariation (w (φ j)) ξ y :=
    fun j => by rw [hfχ _ ξ hK4, (hw (φ j)).integral_chi_mul_divergence_eq hξ4]
  have h4 := tendsto_nhds_unique h1 (h2.neg.congr fun j => (h3 j).symm)
  rw [h4]
  ring

/-! ### Lemma 8.3 -/

/-- The difference quotients of a smooth `φ` with `φ(x) = 0` along `r_k → 0+`:
`φ(x + r_k y)/r_k → ⟪∇φ(x), y⟫`. -/
theorem _root_.InnerVariational.Regular.tendsto_div_of_contDiff {φ : Rn n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) {x : Rn n} (hφx : φ x = 0) {r : ℕ → ℝ} (hr : ∀ k, 0 < r k)
    (hr0 : Tendsto r atTop (𝓝 0)) (y : Rn n) :
    Tendsto (fun k => φ (x + r k • y) / r k) atTop (𝓝 ⟪gradient φ x, y⟫) := by
  have hd : HasFDerivAt φ (fderiv ℝ φ x) x := (hφ.differentiable (by simp) x).hasFDerivAt
  have hc : Tendsto (fun k => ‖(r k)⁻¹‖) atTop atTop := by
    have h1 : Tendsto r atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.2 ⟨hr0, .of_forall hr⟩
    refine (tendsto_inv_nhdsGT_zero.comp h1).congr fun k => ?_
    rw [Function.comp_apply, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (hr k))]
  have := hd.lim y hc
  rw [gradient, InnerProductSpace.toDual_symm_apply]
  refine this.congr fun k => ?_
  rw [inv_inv, hφx, sub_zero, smul_eq_mul, div_eq_inv_mul]

/-- The blow-up data at a free boundary point `x ∉ Σ^H` (proof of Lemma 8.3): a blow-up
`u_{x,r_k} → u₀` that is Lipschitz, nonnegative, one-homogeneous, harmonic on `{u₀ > 0}`, not
identically zero (Lemma 8.1, last claim), with `|{u₀ > 0} ∩ B_1| ≤ M_x(0+) < |B_1|`, and a limit
`χ₀` of `χ_{x,r_k}` satisfying the limit domain variation identity (`exists_chi_blowup`). -/
theorem exists_blowup_of_notMem_sigmaH (hn : 2 ≤ n) (h : IsVariationalSolution Ω C u χ)
    (hx : x ∈ Ω) (hfr : x ∈ frontier {y | 0 < u y}) (hS : x ∉ sigmaH Ω u χ) :
    ∃ r : ℕ → ℝ, (∀ k, 0 < r k) ∧ Tendsto r atTop (𝓝 0) ∧ ∃ u₀ : Rn n → ℝ,
      TendstoLocallyUniformly (fun k => oneHomRescale u x (r k)) u₀ atTop ∧
      LipschitzWith C u₀ ∧ (∀ y, 0 ≤ u₀ y) ∧ (∀ t, 0 < t → ∀ y, u₀ (t • y) = t * u₀ y) ∧
      (∀ y, 0 < u₀ y → HarmonicAt u₀ y) ∧ (∃ y, 0 < u₀ y) ∧
      volume.real ({y | 0 < u₀ y} ∩ ball (0 : Rn n) 1) < unitBallVolume n ∧
      ∃ f₀ : Rn n → ℝ, Measurable f₀ ∧
        (∀ᵐ y ∂(volume.restrict (ball (0 : Rn n) 1)), f₀ y = 0 ∨ f₀ y = 1) ∧
        (∀ᵐ y ∂(volume.restrict (ball (0 : Rn n) 1)), 0 < u₀ y → f₀ y = 1) ∧
        ∀ ξ, IsSmoothTestField (ball (0 : Rn n) 1) ξ →
          (∫ y, Kernel.gradVariation u₀ ξ y) + ∫ y, f₀ y * divergence ξ y = 0 := by
  haveI : NeZero n := ⟨by omega⟩
  obtain ⟨hcl, hux⟩ := (h.mem_frontier_pos_iff hx).1 hfr
  obtain ⟨m, hmM, hm, hd⟩ := h.tendsto_monotonicityM_zero hx hux
  have hmlt : m < unitBallVolume n := by
    by_contra hge
    push Not at hge
    exact hS (h.mem_sigmaH_iff_le_Mzero.2 ⟨hx, hcl, by rw [hmM]; exact_mod_cast hge⟩)
  have hr : ∀ k : ℕ, 0 < 1 / ((k : ℝ) + 1) := fun k => by positivity
  have hr0 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨φ, hφ, u₀, hconv⟩ := h.exists_tendsto_rescale hx hux hr hr0
  have hr' : ∀ k, 0 < 1 / ((φ k : ℝ) + 1) := fun k => hr (φ k)
  have hr0' : Tendsto (fun k => 1 / ((φ k : ℝ) + 1)) atTop (𝓝 0) := hr0.comp hφ.tendsto_atTop
  have hH := blowup_isLipHarmonicPos h hx hr' hr0' hconv
  obtain ⟨f₀, hf₀m, h01, hpos, -, hid⟩ := h.exists_chi_blowup hx hm hd hr' hr0' hconv
  refine ⟨_, hr', hr0', u₀, hconv, blowup_lipschitzWith h hx hr' hr0' hconv,
    fun y => hH.nonneg y trivial, blowup_homogeneous h hx hr' hr0' hconv,
    fun y hy => hH.harmonicAt y trivial hy, ?_,
    (measureReal_pos_inter_ball_le h hx hm hd hr' hr0' hconv).trans_lt hmlt,
    f₀, hf₀m, h01, hpos, hid⟩
  by_contra hall
  push Not at hall
  have hu₀ : u₀ = fun _ => 0 := funext fun y => le_antisymm (hall y) (hH.nonneg y trivial)
  rw [hu₀] at hconv
  have hM := Mzero_eq_of_tendsto_rescale_zero hn h hx hfr hr' hr0' hconv
  rw [hmM, EReal.coe_eq_coe_iff] at hM
  exact hmlt.ne hM

/-- **Lemma 8.3**, touching from below. If `x ∈ Ω ∩ ∂{u > 0}`, `x ∉ Σ^H`,
`φ` is smooth, `φ(x) = 0` and `φ ≤ u` on `B_ρ(x)`, then `|∇φ(x)| ≤ 1`. -/
theorem norm_gradient_le_one_of_le (hn : 2 ≤ n) (h : IsVariationalSolution Ω C u χ)
    (hx : x ∈ Ω) (hfr : x ∈ frontier {y | 0 < u y}) (hS : x ∉ sigmaH Ω u χ) {ρ : ℝ} (hρ : 0 < ρ)
    {φ : Rn n → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφx : φ x = 0) (hle : ∀ y ∈ ball x ρ, φ y ≤ u y) :
    ‖gradient φ x‖ ≤ 1 := by
  obtain ⟨r, hr, hr0, u₀, hconv, hLip, hnn, hhom, hharm, -, hvol, f₀, hf₀m, h01, hpos, hid⟩ :=
    exists_blowup_of_notMem_sigmaH hn h hx hfr hS
  set p := gradient φ x with hpdef
  have hball : ∀ y, ∀ᶠ k in atTop, x + r k • y ∈ ball x ρ := fun y => by
    have : Tendsto (fun k => x + r k • y) atTop (𝓝 x) := by
      simpa using tendsto_const_nhds.add (hr0.smul_const y)
    exact this.eventually (ball_mem_nhds x hρ)
  have htouch : ∀ y, ⟪p, y⟫ ≤ u₀ y := fun y => by
    refine le_of_tendsto_of_tendsto (Regular.tendsto_div_of_contDiff hφ hφx hr hr0 y)
      ((tendstoLocallyUniformlyOn_univ.2 hconv).tendsto_at (mem_univ y)) ?_
    filter_upwards [hball y] with k hk
    rw [oneHomRescale_apply]
    exact div_le_div_of_nonneg_right (hle _ hk) (hr k).le
  by_cases hp : p = 0
  · rw [hp, norm_zero]; exact zero_le_one
  set β := ‖p‖ with hβdef
  have hβ : 0 < β := norm_pos_iff.2 hp
  set e := β⁻¹ • p with hedef
  have he : ‖e‖ = 1 := by rw [hedef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hβ.ne']
  have hpe : ∀ y, ⟪p, y⟫ = β * ⟪y, e⟫ := fun y => by
    rw [hedef, real_inner_smul_right, real_inner_comm, ← mul_assoc, mul_inv_cancel₀ hβ.ne',
      one_mul]
  have hee : ⟪e, e⟫ = 1 := by rw [real_inner_self_eq_norm_sq, he, one_pow]
  obtain ⟨a, ha, hu₀⟩ := Regular.eq_mul_max_of_le hn hLip hnn hhom hharm hvol he hβ
    (fun y => (hpe y) ▸ htouch y)
  have hu₀' : u₀ = fun z => a * max ⟪z, e⟫ 0 := funext hu₀
  have ha1 : a = 1 := by
    refine Regular.eq_one_of_halfSpace he ha hf₀m h01 ?_ fun ξ hξ => ?_
    · filter_upwards [hpos] with y hy hye
      exact hy (by rw [hu₀ y, max_eq_left hye.le]; exact mul_pos ha hye)
    · have := hid ξ hξ
      rwa [hu₀'] at this
  have := htouch e
  rw [hpe e, hee, mul_one, hu₀ e, hee, max_eq_left zero_le_one, ha1, mul_one] at this
  exact this

/-- **Lemma 8.3**, touching from above. If `x ∈ Ω ∩ ∂{u > 0}`, `x ∉ Σ^H`,
`φ` is smooth, `φ(x) = 0` and `u ≤ φ₊` on `B_ρ(x)`, then `|∇φ(x)| ≥ 1`. -/
theorem one_le_norm_gradient_of_le_max (hn : 2 ≤ n) (h : IsVariationalSolution Ω C u χ)
    (hx : x ∈ Ω) (hfr : x ∈ frontier {y | 0 < u y}) (hS : x ∉ sigmaH Ω u χ) {ρ : ℝ} (hρ : 0 < ρ)
    {φ : Rn n → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφx : φ x = 0)
    (hle : ∀ y ∈ ball x ρ, u y ≤ max (φ y) 0) : 1 ≤ ‖gradient φ x‖ := by
  obtain ⟨r, hr, hr0, u₀, hconv, hLip, hnn, hhom, hharm, ⟨y₀, hy₀⟩, -, f₀, hf₀m, h01, hpos,
    hid⟩ := exists_blowup_of_notMem_sigmaH hn h hx hfr hS
  set p := gradient φ x with hpdef
  have hball : ∀ y, ∀ᶠ k in atTop, x + r k • y ∈ ball x ρ := fun y => by
    have : Tendsto (fun k => x + r k • y) atTop (𝓝 x) := by
      simpa using tendsto_const_nhds.add (hr0.smul_const y)
    exact this.eventually (ball_mem_nhds x hρ)
  have htouch : ∀ y, u₀ y ≤ max ⟪p, y⟫ 0 := fun y => by
    refine le_of_tendsto_of_tendsto
      ((tendstoLocallyUniformlyOn_univ.2 hconv).tendsto_at (mem_univ y))
      ((Regular.tendsto_div_of_contDiff hφ hφx hr hr0 y).max tendsto_const_nhds) ?_
    filter_upwards [hball y] with k hk
    rw [oneHomRescale_apply, ← zero_div (r k), max_div_div_right (hr k).le]
    exact div_le_div_of_nonneg_right (hle _ hk) (hr k).le
  by_cases hp : p = 0
  · exfalso
    have := htouch y₀
    rw [hp, inner_zero_left, max_self] at this
    linarith
  set β := ‖p‖ with hβdef
  have hβ : 0 < β := norm_pos_iff.2 hp
  set e := β⁻¹ • p with hedef
  have he : ‖e‖ = 1 := by rw [hedef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hβ.ne']
  have hpe : ∀ y, ⟪p, y⟫ = β * ⟪y, e⟫ := fun y => by
    rw [hedef, real_inner_smul_right, real_inner_comm, ← mul_assoc, mul_inv_cancel₀ hβ.ne',
      one_mul]
  have hee : ⟪e, e⟫ = 1 := by rw [real_inner_self_eq_norm_sq, he, one_pow]
  obtain ⟨a, ha, hu₀⟩ := Regular.eq_mul_max_of_le_max hn hLip hnn hhom hharm hy₀ he hβ
    (fun y => (hpe y) ▸ htouch y)
  have hu₀' : u₀ = fun z => a * max ⟪z, e⟫ 0 := funext hu₀
  have ha1 : a = 1 := by
    refine Regular.eq_one_of_halfSpace he ha hf₀m h01 ?_ fun ξ hξ => ?_
    · filter_upwards [hpos] with y hy hye
      exact hy (by rw [hu₀ y, max_eq_left hye.le]; exact mul_pos ha hye)
    · have := hid ξ hξ
      rwa [hu₀'] at this
  have := htouch e
  rw [hpe e, hee, mul_one, hu₀ e, hee, max_eq_left zero_le_one, ha1, mul_one,
    max_eq_left hβ.le] at this
  exact this

/-- **Lemma 8.3**. Let `(u, χ)` be a variational solution on
`Ω`, `2 ≤ n`, with `Σ^H = ∅`. Then `u` is a viscosity solution on `Ω`, with the conclusions
`|∇φ(x)| ≤ 1` (resp. `≥ 1`) for the touching function `φ`; the paper's Definition 8.1 writes
`|∇u|`, which is not defined at free boundary points. -/
theorem isViscositySolution (hn : 2 ≤ n) (h : IsVariationalSolution Ω C u χ)
    (hS : sigmaH Ω u χ = ∅) : IsViscositySolution Ω u where
  continuousOn := h.continuousOn
  nonneg := h.nonneg
  harmonicAt _ hx hpos := h.harmonicOn_pos hx hpos
  norm_gradient_le x hx _ hr _ _ hφ hφx hle :=
    h.norm_gradient_le_one_of_le hn hx.1 hx.2 (by rw [hS]; exact notMem_empty x) hr hφ hφx hle
  one_le_norm_gradient x hx _ hr _ _ hφ hφx hle :=
    h.one_le_norm_gradient_of_le_max hn hx.1 hx.2 (by rw [hS]; exact notMem_empty x) hr hφ hφx
      hle

/-- **Lemma 8.3 on `Ω \ Σ^H`**. For every variational solution
`(u, χ)` on `Ω`, `2 ≤ n`, `u` is a viscosity solution on the open set `Ω \ Σ^H`. -/
theorem isViscositySolution_diff_sigmaH (hn : 2 ≤ n) (h : IsVariationalSolution Ω C u χ) :
    IsViscositySolution (Ω \ sigmaH Ω u χ) u := by
  haveI : NeZero n := ⟨by omega⟩
  exact h.diff_sigmaH.isViscositySolution hn h.sigmaH_diff_sigmaH_eq_empty

end IsVariationalSolution

end InnerVariational
