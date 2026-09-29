/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Defs.Quantities
public import InnerVariational.Defs.VariationalSolution
public import InnerVariational.Kernel.VariationalQ
import Mathlib.Data.Real.StarOrdered
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Group.Integral

/-!
# Similarity invariance of variational solutions

Kriventsov–Weiss (Section 3.2, equation (3.6); full reference below): if `(u, χ)` is a variational
solution on `B_r(x)`, then the one-homogeneous rescaling `u_{x,r}(y) = u(x + r y) / r`,
`χ_{x,r}(y) = χ(x + r y)` is a variational solution on `B_1` with the same constant. The paper also
uses rotations ("perform an isometry", in the proof of Theorem 6.3). We prove one statement for
every similarity `A y = x + r T y` with `r > 0` and `T` a linear isometry, and derive the special
cases.

## Main results

* `IsVariationalSolutionQ.comp_similarity`: `(u(A ·) / r, χ(A ·))` is a variational solution on
  `A⁻¹(Ω)` for the coefficient `Q ∘ A`, with the same constant; `QBounds.comp_similarity`:
  `Q ∘ A` is `r L`-Lipschitz with the same bounds.
* `IsVariationalSolutionQ.rescale`, `QBounds.rescale`: the one-homogeneous rescaling, on
  `(Ω − x) / r`.
* `IsVariationalSolutionQ.rescale_ball`, `QBounds.rescale_ball`: the paper's statement, from
  `B_r(x)` to `B_1`.
* `IsVariationalSolutionQ.comp_linearIsometryEquiv`, `IsVariationalSolutionQ.comp_add_left`,
  `QBounds.comp_add_left`: rotations and translations.
* The `IsVariationalSolution` versions (the coefficient `Q ≡ 1`) are specializations.

## Proof

Given a test field `ξ` on `A⁻¹(Ω)`, the field `ξ̃ = L ∘ ξ ∘ A⁻¹` (with `L = r T`) is a test
field on `Ω`. Pointwise, `∇(u ∘ A / r) = T⁻¹ (∇u ∘ A)`, `Dξ̃ ∘ A = L Dξ L⁻¹`,
`div ξ̃ ∘ A = div ξ` and `∇(Q² ∘ A) · ξ = (∇(Q²) · ξ̃) ∘ A`. So the integrand of the inner
variation of `(u ∘ A / r, χ ∘ A)` along `ξ` is the integrand of the inner variation of `(u, χ)`
along `ξ̃`, evaluated at `A y`. These identities hold at every point, including the points where
`ξ` is not differentiable, because `fderiv` commutes with composition by continuous linear
equivalences. The change of variables
`∫ F(A y) dy = r^{-n} ∫ F` finishes the proof.

## References

* D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
  DOI 10.1002/cpa.22226; arXiv:2306.10131. Result and equation numbers refer to arXiv v2.
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

namespace Kernel

/-- The linear part `y ↦ r • Q y` of a similarity, as a continuous linear equivalence. -/
def simLinear (r : ℝ) (hr : r ≠ 0) (Q : Rn n ≃ₗᵢ[ℝ] Rn n) : Rn n ≃L[ℝ] Rn n :=
  Q.toContinuousLinearEquiv.trans (LinearEquiv.smulOfNeZero ℝ (Rn n) r hr).toContinuousLinearEquiv

@[simp] theorem simLinear_apply (r : ℝ) (hr : r ≠ 0) (Q : Rn n ≃ₗᵢ[ℝ] Rn n) (y : Rn n) :
    simLinear r hr Q y = r • Q y := rfl

theorem simLinear_symm_apply (r : ℝ) (hr : r ≠ 0) (Q : Rn n ≃ₗᵢ[ℝ] Rn n) (w : Rn n) :
    (simLinear r hr Q).symm w = r⁻¹ • Q.symm w := by
  rw [ContinuousLinearEquiv.symm_apply_eq, simLinear_apply, map_smul,
    LinearIsometryEquiv.apply_symm_apply, smul_smul, mul_inv_cancel₀ hr, one_smul]

theorem dist_similarity {r : ℝ} (hr : 0 < r) (Q : Rn n ≃ₗᵢ[ℝ] Rn n) (x a b : Rn n) :
    dist (x + r • Q a) (x + r • Q b) = r * dist a b := by
  rw [dist_eq_norm, dist_eq_norm, add_sub_add_left_eq_sub, ← smul_sub, ← map_sub, norm_smul,
    LinearIsometryEquiv.norm_map, Real.norm_of_nonneg hr.le]

/-- Change of variables along a similarity: `∫ F(x + r Q y) dy = r^{-n} ∫ F`. -/
theorem integral_comp_similarity (F : Rn n → ℝ) (x : Rn n) {r : ℝ} (hr : 0 < r)
    (Q : Rn n ≃ₗᵢ[ℝ] Rn n) :
    ∫ y, F (x + r • Q y) = (r ^ n)⁻¹ * ∫ z, F z := by
  have h1 : ∫ y, F (x + r • Q y) = ∫ w, F (x + r • w) :=
    (Q.measurePreserving).integral_comp Q.toHomeomorph.measurableEmbedding
      (fun w => F (x + r • w))
  have h2 := Measure.integral_comp_smul (volume : Measure (Rn n)) (fun w => F (x + w)) r
  simp only at h2
  rw [h1, h2, integral_add_left_eq_self, finrank_euclideanSpace_fin, smul_eq_mul,
    abs_of_pos (inv_pos.2 (pow_pos hr n))]

/-- An a.e. property transfers along a similarity. -/
theorem ae_comp_similarity {p : Rn n → Prop} (h : ∀ᵐ z, p z) (x : Rn n) {r : ℝ} (hr : 0 < r)
    (Q : Rn n ≃ₗᵢ[ℝ] Rn n) : ∀ᵐ y, p (x + r • Q y) := by
  have hA : Measure.QuasiMeasurePreserving (fun y : Rn n => x + r • Q y) volume volume :=
    (measurePreserving_add_left volume x).quasiMeasurePreserving.comp
      ((Measure.quasiMeasurePreserving_smul volume hr.ne').comp
        Q.measurePreserving.quasiMeasurePreserving)
  exact hA.ae h

/-- The gradient of `u(x + r Q ·) / r` is `Q⁻¹ ∇u(x + r Q ·)`. -/
theorem gradient_comp_similarity (u : Rn n → ℝ) (x : Rn n) {r : ℝ} (hr : 0 < r)
    (Q : Rn n ≃ₗᵢ[ℝ] Rn n) (y : Rn n) :
    gradient (fun z => u (x + r • Q z) / r) y = Q.symm (gradient u (x + r • Q y)) := by
  set L := simLinear r hr.ne' Q
  have hφ : (fun z => u (x + r • Q z) / r) = r⁻¹ • ((fun w => u (x + w)) ∘ L) := by
    ext z
    simp [L, div_eq_inv_mul]
  have hD : fderiv ℝ (fun z => u (x + r • Q z) / r) y =
      r⁻¹ • (fderiv ℝ u (x + r • Q y)).comp (L : Rn n →L[ℝ] Rn n) := by
    rw [hφ, fderiv_const_smul_field, Pi.smul_apply, L.comp_right_fderiv, fderiv_comp_add_left]
    rfl
  refine ext_inner_right ℝ fun v => ?_
  rw [LinearIsometryEquiv.inner_map_eq_flip, LinearIsometryEquiv.symm_symm]
  simp only [gradient, InnerProductSpace.toDual_symm_apply, hD]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearEquiv.coe_coe, L, simLinear_apply, map_smul, smul_eq_mul]
  field_simp

end Kernel

namespace IsVariationalSolution

theorem preimage_add_smul_ball (x : Rn n) {r : ℝ} (hr : 0 < r) :
    (fun y => x + r • y) ⁻¹' ball x r = ball (0 : Rn n) 1 := by
  ext y
  simp only [mem_preimage, mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero, norm_smul,
    Real.norm_of_nonneg hr.le]
  exact ⟨fun h => by nlinarith [norm_nonneg y], fun h => by nlinarith [norm_nonneg y]⟩

end IsVariationalSolution

namespace IsVariationalSolutionQ

open Kernel

variable {Ω : Set (Rn n)} {C : ℝ≥0} {Q u χ : Rn n → ℝ}

/-- **Similarity invariance** (generalizing Section 3.2 of the paper). If `(u, χ)` is a
variational solution on `Ω` for the coefficient `Q`, and `A y = x + r T y` with `r > 0` and `T` a
linear isometry, then `(u ∘ A / r, χ ∘ A)` is a variational solution on `A⁻¹(Ω)` for the
coefficient `Q ∘ A`, with the same gradient constant. -/
theorem comp_similarity (h : IsVariationalSolutionQ Ω C Q u χ) (x : Rn n) {r : ℝ} (hr : 0 < r)
    (T : Rn n ≃ₗᵢ[ℝ] Rn n) :
    IsVariationalSolutionQ ((fun y => x + r • T y) ⁻¹' Ω) C (fun y => Q (x + r • T y))
      (fun y => u (x + r • T y) / r) (fun y => χ (x + r • T y)) := by
  set L := simLinear r hr.ne' T with hLdef
  set A : Rn n → Rn n := fun y => x + r • T y with hAdef
  have hAc : Continuous A := continuous_const.add (continuous_const.smul T.continuous)
  have hAL : ∀ y, A y = x + L y := fun y => rfl
  -- the inverse of `A`
  set B : Rn n ≃ₜ Rn n := (Homeomorph.subRight x).trans L.symm.toHomeomorph with hBdef
  have hB : ∀ z, B z = L.symm (z - x) := fun z => rfl
  have hBA : ∀ y, B (A y) = y := fun y => by rw [hB, hAL, add_sub_cancel_left, L.symm_apply_apply]
  have hAB : ∀ z, A (B z) = z := fun z => by rw [hB, hAL, L.apply_symm_apply, add_sub_cancel]
  have hpos : ∀ y, (0 < u (A y) / r ↔ 0 < u (A y)) := fun y => div_pos_iff_of_pos_right hr
  refine
    { isOpen := h.isOpen.preimage hAc
      nonneg := fun y hy => div_nonneg (h.nonneg _ hy) hr.le
      continuousOn := (h.continuousOn.comp hAc.continuousOn fun y hy => hy).div_const r
      contDiffOn := ?_
      lipschitzOnWith := ?_
      measurable_chi := ?_
      chi_mem := fun y hy => h.chi_mem _ hy
      posIndicator_le_chi := ?_
      innerVariationQ_eq_zero := ?_ }
  · -- `C²` on the positivity set
    have hAd : ContDiff ℝ 2 A := contDiff_const.add (T.contDiff.const_smul r)
    refine (h.contDiffOn.comp hAd.contDiffOn fun y hy => ⟨hy.1, (hpos y).1 hy.2⟩).div_const r
  · -- Lipschitz bound
    intro y ρ hρ
    have hball : ball (A y) (r * ρ) ⊆ Ω := by
      intro z hz
      have hBz : B z ∈ ball y ρ := by
        rw [mem_ball, ← mul_lt_mul_iff_right₀ hr, ← dist_similarity hr T x]
        change dist (A (B z)) (A y) < r * ρ
        rw [hAB]; exact hz
      have := hρ hBz
      rwa [mem_preimage, hAB] at this
    have hL := h.lipschitzOnWith (A y) (r * ρ) hball
    refine LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_
    have hmem : ∀ c ∈ ball y ρ, A c ∈ ball (A y) (r * ρ) := fun c hc => by
      rw [mem_ball, hAdef, dist_similarity hr T]
      exact mul_lt_mul_of_pos_left (mem_ball.1 hc) hr
    have := hL.dist_le_mul (A a) (hmem a ha) (A b) (hmem b hb)
    rw [hAdef, dist_similarity hr T] at this
    rw [Real.dist_eq, ← sub_div, abs_div, abs_of_pos hr, div_le_iff₀ hr]
    rw [Real.dist_eq] at this
    linarith
  · -- measurability of `χ ∘ A`
    have : ((fun y => x + r • T y) ⁻¹' Ω).indicator (fun y => χ (x + r • T y)) =
        Ω.indicator χ ∘ A := by
      ext y
      exact indicator_comp_right (s := Ω) (g := χ) A (x := y)
    rw [this]
    exact h.measurable_chi.comp hAc.measurable
  · -- `χ_{u>0} ≤ χ` a.e.
    have h0 := (ae_restrict_iff' h.isOpen.measurableSet).1 h.posIndicator_le_chi
    refine (ae_restrict_iff' (h.isOpen.preimage hAc).measurableSet).2 ?_
    filter_upwards [ae_comp_similarity h0 x hr T] with y hy hyΩ
    have e : posIndicator (fun y => u (x + r • T y) / r) y = posIndicator u (A y) := by
      simp only [posIndicator_apply, indicator, mem_setOf_eq]
      exact if_congr (hpos y) rfl rfl
    rw [e]
    exact hy hyΩ
  · -- the inner variation
    intro ξ hξ
    obtain ⟨⟨K, hK⟩, hξc, hξΩ⟩ := hξ
    set ξ' : Rn n → Rn n := fun z => L (ξ (B z)) with hξ'def
    have hξ'c : HasCompactSupport ξ' :=
      (hξc.comp_homeomorph B).comp_left (g := fun v => L v) (map_zero L)
    have hξ't : tsupport ξ' = B ⁻¹' tsupport ξ := by
      rw [show ξ' = (fun v => L v) ∘ (ξ ∘ B) from rfl,
        tsupport_comp_eq (fun {v} => L.map_eq_zero_iff), tsupport_comp_eq_preimage]
    have hξ'L : LipschitzWith K ξ' := by
      refine LipschitzWith.of_dist_le_mul fun a b => ?_
      have hdL : ∀ v w, dist (L v) (L w) = r * dist v w := fun v w => by
        simpa using dist_similarity hr T 0 v w
      have hdB : dist (B a) (B b) = r⁻¹ * dist a b := by
        have := hdL (B a) (B b)
        rw [show L (B a) = a - x by rw [hB, L.apply_symm_apply],
          show L (B b) = b - x by rw [hB, L.apply_symm_apply], dist_sub_right] at this
        field_simp
        linarith
      rw [hξ'def]
      simp only
      rw [hdL, ← le_div_iff₀' hr]
      calc dist (ξ (B a)) (ξ (B b)) ≤ K * dist (B a) (B b) := hK.dist_le_mul _ _
        _ = K * dist a b / r := by rw [hdB]; ring
    have hξ' : IsLipTestField Ω ξ' := by
      refine ⟨⟨K, hξ'L⟩, hξ'c, ?_⟩
      rw [hξ't]
      intro z hz
      have := hξΩ hz
      rwa [mem_preimage, hAB] at this
    have hIV := h.innerVariationQ_eq_zero ξ' hξ'
    -- pointwise identities
    have hDξ' : ∀ y, fderiv ℝ ξ' (A y) =
        (L : Rn n →L[ℝ] Rn n).comp ((fderiv ℝ ξ y).comp (L.symm : Rn n →L[ℝ] Rn n)) := by
      intro y
      have e1 : ξ' = (L ∘ (ξ ∘ L.symm)) ∘ fun z => z - x := rfl
      rw [e1, show ((L ∘ (ξ ∘ L.symm)) ∘ fun z => z - x) = fun z => (L ∘ (ξ ∘ L.symm)) (z - x)
        from rfl, fderiv_comp_sub, L.comp_fderiv, L.symm.comp_right_fderiv]
      congr 3
      rw [hAL, add_sub_cancel_left, L.symm_apply_apply]
    have hdiv : ∀ y, divergence ξ' (A y) = divergence ξ y := by
      intro y
      rw [divergence, divergence, hDξ']
      have : ((L : Rn n →L[ℝ] Rn n).comp ((fderiv ℝ ξ y).comp (L.symm : Rn n →L[ℝ] Rn n)) :
          Rn n →ₗ[ℝ] Rn n) = L.toLinearEquiv.conj (fderiv ℝ ξ y : Rn n →ₗ[ℝ] Rn n) := by
        ext v
        simp [LinearEquiv.conj_apply]
      rw [this, LinearMap.trace_conj']
    have hgrad : ∀ y, gradient (fun z => u (x + r • T z) / r) y = T.symm (gradient u (A y)) :=
      gradient_comp_similarity u x hr T
    have hquad : ∀ y, ⟪gradient u (A y), fderiv ℝ ξ' (A y) (gradient u (A y))⟫ =
        ⟪T.symm (gradient u (A y)), fderiv ℝ ξ y (T.symm (gradient u (A y)))⟫ := by
      intro y
      rw [hDξ']
      simp only [ContinuousLinearMap.coe_comp', ContinuousLinearEquiv.coe_coe,
        Function.comp_apply, simLinear_symm_apply, map_smul, hLdef, simLinear_apply,
        smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
      rw [LinearIsometryEquiv.inner_map_eq_flip, LinearIsometryEquiv.symm_symm]
    have hQd : ∀ y, fderiv ℝ (fun z => Q (x + r • T z) ^ 2) y (ξ y) =
        fderiv ℝ (fun z => Q z ^ 2) (A y) (ξ' (A y)) := by
      intro y
      have e1 : (fun z => Q (x + r • T z) ^ 2) = (fun w => (fun z => Q z ^ 2) (x + w)) ∘ L := rfl
      rw [e1, L.comp_right_fderiv, fderiv_comp_add_left (f := fun z : Rn n => Q z ^ 2)]
      simp only [ContinuousLinearMap.coe_comp', ContinuousLinearEquiv.coe_coe,
        Function.comp_apply, hξ'def, hBA]
      rfl
    have hpt : ∀ y, ((‖gradient (fun z => u (x + r • T z) / r) y‖ ^ 2 +
        Q (x + r • T y) ^ 2 * χ (x + r • T y)) * divergence ξ y -
        2 * ⟪gradient (fun z => u (x + r • T z) / r) y,
          fderiv ℝ ξ y (gradient (fun z => u (x + r • T z) / r) y)⟫ +
        fderiv ℝ (fun z => Q (x + r • T z) ^ 2) y (ξ y) * χ (x + r • T y)) =
        (fun z => (‖gradient u z‖ ^ 2 + Q z ^ 2 * χ z) * divergence ξ' z -
          2 * ⟪gradient u z, fderiv ℝ ξ' z (gradient u z)⟫ +
          fderiv ℝ (fun w => Q w ^ 2) z (ξ' z) * χ z) (x + r • T y) := by
      intro y
      change _ = (‖gradient u (A y)‖ ^ 2 + Q (A y) ^ 2 * χ (A y)) * divergence ξ' (A y) -
        2 * ⟪gradient u (A y), fderiv ℝ ξ' (A y) (gradient u (A y))⟫ +
        fderiv ℝ (fun w => Q w ^ 2) (A y) (ξ' (A y)) * χ (A y)
      rw [hgrad, hdiv, hquad, hQd, LinearIsometryEquiv.norm_map]
    rw [innerVariationQ]
    refine (integral_congr_ae (.of_forall hpt)).trans ((integral_comp_similarity
      (fun z => (‖gradient u z‖ ^ 2 + Q z ^ 2 * χ z) * divergence ξ' z -
        2 * ⟪gradient u z, fderiv ℝ ξ' z (gradient u z)⟫ +
        fderiv ℝ (fun w => Q w ^ 2) z (ξ' z) * χ z) x hr T).trans ?_)
    change (r ^ n)⁻¹ * innerVariationQ Q u χ ξ' = 0
    rw [hIV, mul_zero]

/-- **One-homogeneous rescaling** (equation (3.6)) with a Lipschitz coefficient. If `(u, χ)` is a
variational solution on `Ω` for the coefficient `Q`, then `(u_{x,r}, χ_{x,r})` is one on
`(Ω − x) / r` for the coefficient `Q(x + r ·)`, with the same gradient constant. -/
theorem rescale (h : IsVariationalSolutionQ Ω C Q u χ) (x : Rn n) {r : ℝ} (hr : 0 < r) :
    IsVariationalSolutionQ ((fun y => x + r • y) ⁻¹' Ω) C (fun y => Q (x + r • y))
      (oneHomRescale u x r) (chiRescale χ x r) :=
  h.comp_similarity x hr (LinearIsometryEquiv.refl ℝ (Rn n))

/-- **One-homogeneous rescaling** with a Lipschitz coefficient, from `B_r(x)` to `B_1`. -/
theorem rescale_ball {x : Rn n} {r : ℝ} (hr : 0 < r)
    (h : IsVariationalSolutionQ (ball x r) C Q u χ) :
    IsVariationalSolutionQ (ball 0 1) C (fun y => Q (x + r • y)) (oneHomRescale u x r)
      (chiRescale χ x r) := by
  simpa only [IsVariationalSolution.preimage_add_smul_ball x hr] using h.rescale x hr

/-- **Rotation invariance** with a Lipschitz coefficient. -/
theorem comp_linearIsometryEquiv (h : IsVariationalSolutionQ Ω C Q u χ)
    (T : Rn n ≃ₗᵢ[ℝ] Rn n) : IsVariationalSolutionQ (T ⁻¹' Ω) C (Q ∘ T) (u ∘ T) (χ ∘ T) := by
  simpa using h.comp_similarity 0 one_pos T

/-- **Translation invariance** with a Lipschitz coefficient. -/
theorem comp_add_left (h : IsVariationalSolutionQ Ω C Q u χ) (x : Rn n) :
    IsVariationalSolutionQ ((x + ·) ⁻¹' Ω) C (fun y => Q (x + y)) (fun y => u (x + y))
      (fun y => χ (x + y)) := by
  simpa using h.comp_similarity x one_pos (LinearIsometryEquiv.refl ℝ (Rn n))

end IsVariationalSolutionQ

namespace QBounds

variable {Ω : Set (Rn n)} {Q : Rn n → ℝ} {L : ℝ≥0} {c C' : ℝ}

/-- The bounds on the coefficient under a similarity `A y = x + r T y`: `Q ∘ A` is
`r L`-Lipschitz on `A⁻¹(Ω)`, with the same bounds `c ≤ Q ∘ A ≤ C'`. -/
theorem comp_similarity (hQ : QBounds Ω Q L c C') (x : Rn n) {r : ℝ} (hr : 0 < r)
    (T : Rn n ≃ₗᵢ[ℝ] Rn n) :
    QBounds ((fun y => x + r • T y) ⁻¹' Ω) (fun y => Q (x + r • T y)) (Real.toNNReal r * L)
      c C' where
  lipschitzOnWith := by
    refine LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_
    have := hQ.lipschitzOnWith.dist_le_mul _ ha _ hb
    rw [Kernel.dist_similarity hr T] at this
    rw [NNReal.coe_mul, Real.coe_toNNReal _ hr.le]
    linarith
  pos := hQ.pos
  le y hy := hQ.le _ hy
  le' y hy := hQ.le' _ hy

/-- The bounds on the coefficient under the one-homogeneous rescaling: `Q(x + r ·)` is
`r L`-Lipschitz on `(Ω − x) / r`, with the same bounds. -/
theorem rescale (hQ : QBounds Ω Q L c C') (x : Rn n) {r : ℝ} (hr : 0 < r) :
    QBounds ((fun y => x + r • y) ⁻¹' Ω) (fun y => Q (x + r • y)) (Real.toNNReal r * L) c C' :=
  hQ.comp_similarity x hr (LinearIsometryEquiv.refl ℝ (Rn n))

/-- The bounds on the coefficient under the rescaling from `B_r(x)` to `B_1`. -/
theorem rescale_ball {x : Rn n} {r : ℝ} (hr : 0 < r) (hQ : QBounds (ball x r) Q L c C') :
    QBounds (ball 0 1) (fun y => Q (x + r • y)) (Real.toNNReal r * L) c C' := by
  simpa only [IsVariationalSolution.preimage_add_smul_ball x hr] using hQ.rescale x hr

/-- The bounds on the coefficient under a translation. -/
theorem comp_add_left (hQ : QBounds Ω Q L c C') (x : Rn n) :
    QBounds ((x + ·) ⁻¹' Ω) (fun y => Q (x + y)) L c C' := by
  simpa using hQ.comp_similarity x one_pos (LinearIsometryEquiv.refl ℝ (Rn n))

end QBounds

namespace IsVariationalSolution

open Kernel

variable {Ω : Set (Rn n)} {C : ℝ≥0} {u χ : Rn n → ℝ}

/-- **Similarity invariance** (generalizing Section 3.2 of the paper). If `(u, χ)` is a
variational solution on `Ω`, and `A y = x + r Q y` with `r > 0` and `Q` a linear isometry, then
`(u ∘ A / r, χ ∘ A)` is a variational solution on `A⁻¹(Ω)` with the same constant. -/
theorem comp_similarity (h : IsVariationalSolution Ω C u χ) (x : Rn n) {r : ℝ} (hr : 0 < r)
    (Q : Rn n ≃ₗᵢ[ℝ] Rn n) :
    IsVariationalSolution ((fun y => x + r • Q y) ⁻¹' Ω) C (fun y => u (x + r • Q y) / r)
      (fun y => χ (x + r • Q y)) :=
  isVariationalSolutionQ_one_iff.1 (h.toQ.comp_similarity x hr Q)

/-- **One-homogeneous rescaling** (equation (3.6)). If `(u, χ)` is a variational solution on `Ω`,
then `(u_{x,r}, χ_{x,r})` is one on `(Ω − x) / r`, with the same constant. -/
theorem rescale (h : IsVariationalSolution Ω C u χ) (x : Rn n) {r : ℝ} (hr : 0 < r) :
    IsVariationalSolution ((fun y => x + r • y) ⁻¹' Ω) C (oneHomRescale u x r)
      (chiRescale χ x r) :=
  h.comp_similarity x hr (LinearIsometryEquiv.refl ℝ (Rn n))

/-- **One-homogeneous rescaling**, as stated in the paper (Section 3.2): a variational solution
on `B_r(x)` rescales to one on `B_1`. -/
theorem rescale_ball {x : Rn n} {r : ℝ} (hr : 0 < r)
    (h : IsVariationalSolution (ball x r) C u χ) :
    IsVariationalSolution (ball 0 1) C (oneHomRescale u x r) (chiRescale χ x r) := by
  simpa only [preimage_add_smul_ball x hr] using h.rescale x hr

/-- **Rotation invariance** (used in the proof of Theorem 6.3). -/
theorem comp_linearIsometryEquiv (h : IsVariationalSolution Ω C u χ) (Q : Rn n ≃ₗᵢ[ℝ] Rn n) :
    IsVariationalSolution (Q ⁻¹' Ω) C (u ∘ Q) (χ ∘ Q) := by
  simpa using h.comp_similarity 0 one_pos Q

/-- **Translation invariance.** -/
theorem comp_add_left (h : IsVariationalSolution Ω C u χ) (x : Rn n) :
    IsVariationalSolution ((x + ·) ⁻¹' Ω) C (fun y => u (x + y)) (fun y => χ (x + y)) := by
  simpa using h.comp_similarity x one_pos (LinearIsometryEquiv.refl ℝ (Rn n))

end IsVariationalSolution

end InnerVariational
