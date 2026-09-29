/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Sperner.GaussIBP
public import Sperner.Radial
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Picone's identity and the Gaussian Poincaré inequality on cones

Let `w ≥ 0` be Lipschitz and one-homogeneous, and let `φ(x) = ⟪x, e⟫ - c |x|` with `c ≥ 0`.
If `φ > 0` on `{w > 0}` and `w ≤ M φ` there, then with the Picone quotient `h = w²/φ`
(Lipschitz, one-homogeneous) one has pointwise `|Dw|² ≥ ⟨Dh, ∇φ⟩ = ∂ₑh - c h/|x|`
(at zeros of `w`, `h ≥ 0` has a local minimum), and Gaussian integration by parts in the
direction `e` together with the radial identity `∫ F |x|² dγ = n ∫ F dγ` gives
`∫ w² dγ + c (n - 1) ∫ h/|x| dγ ≤ ∫ |Dw|² dγ`.

Consequences:
* if `{w > 0} ⊆ {⟪x, e⟫ ≥ s |x|}` with `s > 0`, `w ≢ 0` and `n ≥ 2`, then `∫ w² dγ < ∫ |Dw|² dγ`
  (a spherical cap strictly smaller than a hemisphere has first eigenvalue `> n - 1`);
* if `{w > 0} ⊆ {⟪x, e⟫ > 0}`, then `∫ w² dγ ≤ ∫ |Dw|² dγ` (hemisphere: eigenvalue `n - 1`).
-/

open MeasureTheory Set Filter Topology
open scoped NNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace Sperner

variable {n : ℕ}

/-- The Picone quotient `w²/φ` on `{w > 0}`, extended by `0`. -/
def piconeQuot (w φ : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  if 0 < w x then w x ^ 2 / φ x else 0

lemma abs_sq_div_sub_sq_div_le {a b p q M L K d : ℝ} (hq : 0 < q) (hqp : q ≤ p) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (haM : a ≤ M * p) (hbM : b ≤ M * q) (hab : |a - b| ≤ L * d)
    (hpq : |p - q| ≤ K * d) :
    |a ^ 2 / p - b ^ 2 / q| ≤ (2 * L * M + K * M ^ 2) * d := by
  have hp : 0 < p := lt_of_lt_of_le hq hqp
  have hM : 0 ≤ M := by
    by_contra h; push Not at h; nlinarith
  have e : a ^ 2 / p - b ^ 2 / q = (a - b) * ((a + b) / p) + b ^ 2 / (p * q) * (q - p) := by
    field_simp; ring
  have h1 : (a + b) / p ≤ 2 * M := by
    rw [div_le_iff₀ hp]; nlinarith [mul_le_mul_of_nonneg_left hqp hM]
  have h2 : b ^ 2 / (p * q) ≤ M ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have : b ^ 2 ≤ (M * q) ^ 2 := pow_le_pow_left₀ hb hbM 2
    nlinarith [mul_le_mul_of_nonneg_left hqp (by positivity : 0 ≤ M ^ 2 * q)]
  have h1' : 0 ≤ (a + b) / p := by positivity
  have h2' : 0 ≤ b ^ 2 / (p * q) := by positivity
  rw [e]
  calc |(a - b) * ((a + b) / p) + b ^ 2 / (p * q) * (q - p)|
      ≤ |a - b| * ((a + b) / p) + b ^ 2 / (p * q) * |p - q| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_nonneg h1', abs_of_nonneg h2', abs_sub_comm q p]
    _ ≤ (L * d) * (2 * M) + M ^ 2 * (K * d) := by
        gcongr
        · exact (abs_nonneg _).trans hab
    _ = (2 * L * M + K * M ^ 2) * d := by ring

section Quot

variable {w φ : EuclideanSpace ℝ (Fin n) → ℝ} {M : ℝ}

lemma piconeQuot_of_pos {x : EuclideanSpace ℝ (Fin n)} (hx : 0 < w x) :
    piconeQuot w φ x = w x ^ 2 / φ x := if_pos hx

lemma piconeQuot_of_not_pos {x : EuclideanSpace ℝ (Fin n)} (hx : ¬ 0 < w x) :
    piconeQuot w φ x = 0 := if_neg hx

variable (hM : ∀ x, 0 < w x → 0 < φ x ∧ w x ≤ M * φ x)
include hM

lemma piconeQuot_nonneg (x : EuclideanSpace ℝ (Fin n)) : 0 ≤ piconeQuot w φ x := by
  by_cases hx : 0 < w x
  · rw [piconeQuot_of_pos hx]; exact div_nonneg (sq_nonneg _) (hM x hx).1.le
  · rw [piconeQuot_of_not_pos hx]

lemma piconeQuot_le (hnn : ∀ x, 0 ≤ w x) (x : EuclideanSpace ℝ (Fin n)) :
    piconeQuot w φ x ≤ M * w x := by
  by_cases hx : 0 < w x
  · rw [piconeQuot_of_pos hx, div_le_iff₀ (hM x hx).1]
    have := (hM x hx).2
    nlinarith
  · rw [piconeQuot_of_not_pos hx]
    have hM0 : 0 ≤ M * w x := by
      have : w x = 0 := le_antisymm (not_lt.1 hx) (hnn x)
      rw [this, mul_zero]
    exact hM0

lemma sq_eq_piconeQuot_mul (hnn : ∀ x, 0 ≤ w x) (x : EuclideanSpace ℝ (Fin n)) :
    w x ^ 2 = piconeQuot w φ x * φ x := by
  by_cases hx : 0 < w x
  · rw [piconeQuot_of_pos hx, div_mul_cancel₀ _ (hM x hx).1.ne']
  · rw [piconeQuot_of_not_pos hx, le_antisymm (not_lt.1 hx) (hnn x)]; ring

lemma lipschitzWith_piconeQuot {L K : ℝ≥0} (hw : LipschitzWith L w) (hnn : ∀ x, 0 ≤ w x)
    (hφ : LipschitzWith K φ) (hM0 : 0 ≤ M) :
    LipschitzWith (Real.toNNReal (2 * L * M + K * M ^ 2)) (piconeQuot w φ) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.coe_toNNReal _ (by positivity), Real.dist_eq]
  have hwd := hw.dist_le_mul x y
  have hφd := hφ.dist_le_mul x y
  rw [Real.dist_eq] at hwd hφd
  have hd : 0 ≤ dist x y := dist_nonneg
  have hC : (L : ℝ) * M * dist x y ≤ (2 * L * M + K * M ^ 2) * dist x y := by
    have : (0 : ℝ) ≤ L := L.2
    have : (0 : ℝ) ≤ K := K.2
    gcongr; nlinarith [mul_nonneg this (sq_nonneg M), mul_nonneg ‹(0 : ℝ) ≤ L› hM0]
  by_cases hx : 0 < w x <;> by_cases hy : 0 < w y
  · rw [piconeQuot_of_pos hx, piconeQuot_of_pos hy]
    obtain ⟨hpx, hMx⟩ := hM x hx
    obtain ⟨hpy, hMy⟩ := hM y hy
    rcases le_total (φ y) (φ x) with h | h
    · exact abs_sq_div_sub_sq_div_le hpy h hx.le hy.le hMx hMy hwd hφd
    · rw [abs_sub_comm]
      rw [abs_sub_comm] at hwd hφd
      exact abs_sq_div_sub_sq_div_le hpx h hy.le hx.le hMy hMx hwd hφd
  · rw [piconeQuot_of_pos hx, piconeQuot_of_not_pos hy, sub_zero]
    have hy0 : w y = 0 := le_antisymm (not_lt.1 hy) (hnn y)
    rw [hy0, sub_zero, abs_of_pos hx] at hwd
    obtain ⟨hpx, hMx⟩ := hM x hx
    rw [abs_of_nonneg (by positivity)]
    calc w x ^ 2 / φ x ≤ M * w x := by rw [div_le_iff₀ hpx]; nlinarith
      _ ≤ M * (L * dist x y) := by gcongr
      _ = L * M * dist x y := by ring
      _ ≤ _ := hC
  · rw [piconeQuot_of_not_pos hx, piconeQuot_of_pos hy, zero_sub, abs_neg]
    have hx0 : w x = 0 := le_antisymm (not_lt.1 hx) (hnn x)
    rw [hx0, zero_sub, abs_neg, abs_of_pos hy] at hwd
    obtain ⟨hpy, hMy⟩ := hM y hy
    rw [abs_of_nonneg (by positivity)]
    calc w y ^ 2 / φ y ≤ M * w y := by rw [div_le_iff₀ hpy]; nlinarith
      _ ≤ M * (L * dist x y) := by gcongr
      _ = L * M * dist x y := by ring
      _ ≤ _ := hC
  · rw [piconeQuot_of_not_pos hx, piconeQuot_of_not_pos hy, sub_zero, abs_zero]
    positivity

lemma isOneHomogeneous_piconeQuot (hw : IsOneHomogeneous w) (hφ : IsOneHomogeneous φ) :
    IsOneHomogeneous (piconeQuot w φ) := by
  intro x t ht
  have hiff : 0 < w (t • x) ↔ 0 < w x := by rw [hw x t ht]; exact mul_pos_iff_of_pos_left ht
  by_cases hx : 0 < w x
  · rw [piconeQuot_of_pos hx, piconeQuot_of_pos (hiff.2 hx), hw x t ht, hφ x t ht]
    have := (hM x hx).1.ne'
    field_simp
  · rw [piconeQuot_of_not_pos hx, piconeQuot_of_not_pos (fun h => hx (hiff.1 h)), mul_zero]

end Quot

/-- The derivative of the norm away from the origin. -/
lemma hasFDerivAt_norm_of_ne_zero {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖) (‖x‖⁻¹ • innerSL ℝ x) x := by
  have hx' : ‖x‖ ^ 2 ≠ 0 := by positivity
  have h := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt).sqrt hx'
  have hf : (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖) = fun y => √(‖y‖ ^ 2) := by
    funext y; rw [Real.sqrt_sq (norm_nonneg y)]
  rw [hf]
  convert h using 1
  rw [Real.sqrt_sq (norm_nonneg x)]
  ext v
  have : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul]
  field_simp
  norm_num

/-- The comparison function `φ(x) = ⟪x, e⟫ - c |x|`. -/
def coneWeight (e : EuclideanSpace ℝ (Fin n)) (c : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ⟪x, e⟫ - c * ‖x‖

lemma isOneHomogeneous_coneWeight (e : EuclideanSpace ℝ (Fin n)) {c : ℝ} :
    IsOneHomogeneous (coneWeight e c) := by
  intro x t ht
  simp only [coneWeight, inner_smul_left, norm_smul, Real.norm_of_nonneg ht.le,
    RCLike.conj_to_real]
  ring

lemma lipschitzWith_coneWeight (e : EuclideanSpace ℝ (Fin n)) {c : ℝ} (hc : 0 ≤ c) :
    LipschitzWith (‖e‖₊ + c.toNNReal) (coneWeight e c) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq, dist_eq_norm, NNReal.coe_add, coe_nnnorm, Real.coe_toNNReal _ hc]
  have h1 : |⟪x, e⟫ - ⟪y, e⟫| ≤ ‖e‖ * ‖x - y‖ := by
    rw [← inner_sub_left]
    exact (abs_real_inner_le_norm _ _).trans (by rw [mul_comm])
  have h2 : |‖x‖ - ‖y‖| ≤ ‖x - y‖ := abs_norm_sub_norm_le x y
  calc |coneWeight e c x - coneWeight e c y|
      = |(⟪x, e⟫ - ⟪y, e⟫) - c * (‖x‖ - ‖y‖)| := by unfold coneWeight; ring_nf
    _ ≤ |⟪x, e⟫ - ⟪y, e⟫| + c * |‖x‖ - ‖y‖| := by
        refine (abs_sub _ _).trans ?_
        rw [abs_mul, abs_of_nonneg hc]
    _ ≤ ‖e‖ * ‖x - y‖ + c * ‖x - y‖ := by gcongr
    _ = (‖e‖ + c) * ‖x - y‖ := by ring

/-- **Pointwise Picone inequality** `∂ₑh - c h/|x| ≤ |Dw|²`, `h = w²/φ`, `φ = ⟪x, e⟫ - c|x|`. -/
lemma picone_pointwise {w : EuclideanSpace ℝ (Fin n) → ℝ} (hwc : Continuous w)
    (hnn : ∀ x, 0 ≤ w x) {e : EuclideanSpace ℝ (Fin n)} {c M : ℝ}
    (hM : ∀ x, 0 < w x → 0 < coneWeight e c x ∧ w x ≤ M * coneWeight e c x)
    (hhom : IsOneHomogeneous (piconeQuot w (coneWeight e c)))
    {x : EuclideanSpace ℝ (Fin n)} (hwd : DifferentiableAt ℝ w x)
    (hhd : DifferentiableAt ℝ (piconeQuot w (coneWeight e c)) x) :
    fderiv ℝ (piconeQuot w (coneWeight e c)) x e -
        c * piconeQuot w (coneWeight e c) x / ‖x‖ ≤ ‖fderiv ℝ w x‖ ^ 2 := by
  set φ := coneWeight e c
  set h := piconeQuot w φ
  by_cases hpos : 0 < w x
  · have hx0 : x ≠ 0 := by
      rintro rfl
      have := (hM 0 hpos).1
      simp [φ, coneWeight] at this
    have hnx : 0 < ‖x‖ := norm_pos_iff.2 hx0
    obtain ⟨hφx, -⟩ := hM x hpos
    set p : EuclideanSpace ℝ (Fin n) := e - (c / ‖x‖) • x with hp
    -- Euler's identity for `h` converts `∂ₚh` into `∂ₑh - c h/|x|`
    have hDp : fderiv ℝ h x p = fderiv ℝ h x e - c * h x / ‖x‖ := by
      rw [hp, map_sub, map_smul, hhom.fderiv_apply_self hhd, smul_eq_mul]; ring
    -- the directional derivative of `h` along `p` by the quotient rule
    have hline : Tendsto (fun t : ℝ => x + t • p) (𝓝 0) (𝓝 x) := by
      have : Continuous fun t : ℝ => x + t • p := by fun_prop
      simpa using this.tendsto 0
    have hnear : ∀ᶠ y in 𝓝 x, 0 < w y :=
      (isOpen_lt continuous_const hwc).mem_nhds hpos
    have heq : (fun t : ℝ => h (x + t • p)) =ᶠ[𝓝 0]
        fun t => w (x + t • p) ^ 2 / φ (x + t • p) :=
      (hline.eventually hnear).mono fun t ht => piconeQuot_of_pos ht
    have hW : HasDerivAt (fun t : ℝ => w (x + t • p)) (fderiv ℝ w x p) 0 :=
      hwd.hasFDerivAt.hasLineDerivAt p
    have hN : HasDerivAt (fun t : ℝ => ‖x + t • p‖) (‖x‖⁻¹ * ⟪x, p⟫) 0 := by
      have h1 : HasDerivAt (fun t : ℝ => x + t • p) p 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const p).const_add x
      have := (hasFDerivAt_norm_of_ne_zero hx0).comp_hasDerivAt_of_eq 0 h1 (by simp)
      simpa [Function.comp_def] using this
    have hI : HasDerivAt (fun t : ℝ => ⟪x + t • p, e⟫) ⟪p, e⟫ 0 := by
      have : (fun t : ℝ => ⟪x + t • p, e⟫) = fun t => ⟪x, e⟫ + t * ⟪p, e⟫ := by
        funext t; rw [inner_add_left, real_inner_smul_left]
      rw [this]
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const ⟪p, e⟫).const_add ⟪x, e⟫
    have hpp : ⟪p, p⟫ = ⟪p, e⟫ - c * (‖x‖⁻¹ * ⟪x, p⟫) := by
      nth_rw 1 [hp]
      rw [inner_sub_left, real_inner_smul_left, real_inner_comm e p]
      ring
    have hΦ : HasDerivAt (fun t : ℝ => φ (x + t • p)) ⟪p, p⟫ 0 := by
      rw [hpp]
      exact hI.sub (hN.const_mul c)
    have hG := (hW.fun_pow 2).fun_div hΦ (by simpa using hφx.ne')
    have h1 : HasDerivAt (fun t : ℝ => h (x + t • p)) (fderiv ℝ h x p) 0 :=
      hhd.hasFDerivAt.hasLineDerivAt p
    have hval := h1.unique (hG.congr_of_eventuallyEq heq)
    simp only [zero_smul, add_zero, Nat.cast_ofNat, Nat.reduceSub, pow_one] at hval
    rw [← hDp, hval]
    -- Picone: `2 r ∂ₚw - r² |p|² ≤ |Dw|²` with `r = w/φ`
    have hDw : fderiv ℝ w x p ≤ ‖fderiv ℝ w x‖ * ‖p‖ :=
      (le_abs_self _).trans ((fderiv ℝ w x).le_opNorm p |>.trans_eq' (Real.norm_eq_abs _).symm)
    rw [real_inner_self_eq_norm_sq, div_le_iff₀ (by positivity)]
    have hA := norm_nonneg (fderiv ℝ w x)
    have hP := norm_nonneg p
    nlinarith [sq_nonneg (‖fderiv ℝ w x‖ * φ x - w x * ‖p‖),
      mul_le_mul_of_nonneg_left hDw (by positivity : 0 ≤ 2 * w x * φ x)]
  · have hx0 : w x = 0 := le_antisymm (not_lt.1 hpos) (hnn x)
    have hh0 : h x = 0 := piconeQuot_of_not_pos hpos
    have hmin : IsLocalMin h x :=
      Filter.Eventually.of_forall fun y => by
        rw [hh0]; exact piconeQuot_nonneg hM y
    rw [hmin.fderiv_eq_zero, hh0]
    simp only [ContinuousLinearMap.zero_apply, mul_zero, zero_div, sub_zero]
    positivity

/-- **Picone's inequality, integrated.** With `φ = ⟪x, e⟫ - c|x|` positive on `{w > 0}` and
`w ≤ M φ` there, `∫ w² dγ + c (n - 1) I ≤ ∫ |Dw|² dγ` where `I = ∫ (w²/φ)/|x| dγ ≥ 0`, and `I > 0`
unless `w ≡ 0`. -/
theorem exists_gaussL2_add_le_dirichletEnergy {w : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ≥0}
    (hw : LipschitzWith L w) (hnn : ∀ x, 0 ≤ w x) (hhom : IsOneHomogeneous w)
    (e : EuclideanSpace ℝ (Fin n)) {c M : ℝ} (hc : 0 ≤ c) (hM0 : 0 ≤ M)
    (hM : ∀ x, 0 < w x → 0 < coneWeight e c x ∧ w x ≤ M * coneWeight e c x) :
    ∃ I : ℝ, 0 ≤ I ∧ ((∃ x, 0 < w x) → 0 < I) ∧
      gaussL2 w + c * (n - 1) * I ≤ dirichletEnergy w := by
  set φ := coneWeight e c with hφdef
  set h := piconeQuot w φ with hhdef
  have hhL := lipschitzWith_piconeQuot hM hw hnn (lipschitzWith_coneWeight e hc) hM0
  set K' := Real.toNNReal (2 * L * M + (‖e‖₊ + c.toNNReal) * M ^ 2)
  have hhhom : IsOneHomogeneous h :=
    isOneHomogeneous_piconeQuot hM hhom (isOneHomogeneous_coneWeight e)
  have hw0 : w 0 = 0 := hhom.map_zero
  have hwle : ∀ x, w x ≤ L * ‖x‖ := fun x => by
    have := hw.dist_le_mul x 0
    rw [Real.dist_eq, hw0, sub_zero, dist_zero_right] at this
    exact (le_abs_self _).trans this
  have hh0 : ∀ x, 0 ≤ h x := piconeQuot_nonneg hM
  have hhle : ∀ x, h x ≤ M * L * ‖x‖ := fun x =>
    (piconeQuot_le hM hnn x).trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hwle x) hM0)
  set F : EuclideanSpace ℝ (Fin n) → ℝ := fun x => h x / ‖x‖ with hFdef
  have hF0 : ∀ x, 0 ≤ F x := fun x => div_nonneg (hh0 x) (norm_nonneg x)
  have hFle : ∀ x, F x ≤ M * L := by
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · simp only [F, norm_zero, div_zero]; positivity
    · rw [hFdef, div_le_iff₀ (norm_pos_iff.2 hx)]; exact hhle x
  have hhc : Continuous h := hhL.continuous
  have hFm : Measurable F := hhc.measurable.div continuous_norm.measurable
  have hFhom : ∀ x (t : ℝ), 0 < t → F (t • x) = F x := by
    intro x t ht
    simp only [F, hhhom x t ht, norm_smul, Real.norm_of_nonneg ht.le]
    rcases eq_or_ne ‖x‖ 0 with hx | hx
    · simp [hx]
    · field_simp
  -- integrability
  have iF : Integrable F (gaussMeasure n) :=
    (integrable_const (M * L)).mono' hFm.aestronglyMeasurable
      (ae_of_all _ fun x => by rw [Real.norm_of_nonneg (hF0 x)]; exact hFle x)
  have iDw : Integrable (fun x => ‖fderiv ℝ w x‖ ^ 2) (gaussMeasure n) :=
    (integrable_const ((L : ℝ) ^ 2)).mono'
      ((measurable_fderiv ℝ w).norm.pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun x => by
        rw [Real.norm_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_le_of_lipschitz ℝ hw) 2)
  have iDh : Integrable (fun x => fderiv ℝ h x e) (gaussMeasure n) :=
    (integrable_const ((K' : ℝ) * ‖e‖)).mono'
      (measurable_fderiv_apply_const ℝ h e).aestronglyMeasurable
      (ae_of_all _ fun x => ((fderiv ℝ h x).le_opNorm e).trans
        (by gcongr; exact norm_fderiv_le_of_lipschitz ℝ hhL))
  have i2 := integrable_norm_pow_gaussMeasure (n := n) 2
  have ihe : Integrable (fun x => h x * ⟪x, e⟫) (gaussMeasure n) :=
    (i2.const_mul (M * L * ‖e‖)).mono' (by fun_prop) (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hh0 x)]
      calc h x * |⟪x, e⟫| ≤ (M * L * ‖x‖) * (‖x‖ * ‖e‖) :=
            mul_le_mul (hhle x) (abs_real_inner_le_norm x e) (abs_nonneg _) (by positivity)
        _ = M * L * ‖e‖ * ‖x‖ ^ 2 := by ring)
  have ihn : Integrable (fun x => h x * ‖x‖) (gaussMeasure n) :=
    (i2.const_mul (M * L)).mono' (by fun_prop) (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hh0 x), abs_norm]
      calc h x * ‖x‖ ≤ (M * L * ‖x‖) * ‖x‖ := by gcongr; exact hhle x
        _ = M * L * ‖x‖ ^ 2 := by ring)
  -- Step 1: pointwise Picone
  have step1 : ∫ x, (fderiv ℝ h x e - c * F x) ∂gaussMeasure n ≤ dirichletEnergy w := by
    unfold dirichletEnergy
    refine integral_mono_ae (iDh.sub (iF.const_mul c)) iDw ?_
    have hac : gaussMeasure n ≪ volume := withDensity_absolutelyContinuous _ _
    filter_upwards [hac.ae_le hw.ae_differentiableAt, hac.ae_le hhL.ae_differentiableAt]
      with x hx1 hx2
    have := picone_pointwise hw.continuous hnn hM hhhom hx1 hx2
    simpa only [F, mul_div_assoc] using this
  -- Step 2: Gaussian integration by parts in the direction `e`
  have step2 : ∫ x, fderiv ℝ h x e ∂gaussMeasure n = ∫ x, h x * ⟪x, e⟫ ∂gaussMeasure n :=
    integral_fderiv_gaussMeasure hhL e
  -- Step 3: `w² = h φ`
  have step3 : gaussL2 w =
      ∫ x, h x * ⟪x, e⟫ ∂gaussMeasure n - c * ∫ x, h x * ‖x‖ ∂gaussMeasure n := by
    unfold gaussL2
    rw [← integral_const_mul, ← integral_sub ihe (ihn.const_mul c)]
    congr 1; funext x
    rw [sq_eq_piconeQuot_mul hM hnn x]
    simp only [φ, coneWeight]; ring
  -- Step 4: radial identity
  have step4 : ∫ x, h x * ‖x‖ ∂gaussMeasure n = n * ∫ x, F x ∂gaussMeasure n := by
    rw [← integral_mul_norm_sq_gaussMeasure hFm
      ⟨M * L, fun x => by rw [abs_of_nonneg (hF0 x)]; exact hFle x⟩ hFhom]
    congr 1; funext x
    rcases eq_or_ne x 0 with rfl | hx
    · simp [F]
    · have : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
      simp only [F]; field_simp
  refine ⟨∫ x, F x ∂gaussMeasure n, integral_nonneg hF0, fun ⟨x₀, hx₀⟩ => ?_, ?_⟩
  · rw [integral_pos_iff_support_of_nonneg hF0 iF]
    refine lt_of_lt_of_le (gaussMeasure_pos_of_isOpen (isOpen_lt continuous_const hw.continuous)
      ⟨x₀, hx₀⟩) (measure_mono fun x (hx : 0 < w x) => ?_)
    have hx0 : x ≠ 0 := by rintro rfl; rw [hw0] at hx; exact lt_irrefl _ hx
    have hhx : 0 < h x := by
      rw [hhdef, piconeQuot_of_pos hx]; exact div_pos (by positivity) (hM x hx).1
    exact (div_pos hhx (norm_pos_iff.2 hx0)).ne'
  · rw [integral_sub iDh (iF.const_mul c), integral_const_mul, step2] at step1
    rw [step3, step4]
    calc ∫ x, h x * ⟪x, e⟫ ∂gaussMeasure n - c * (n * ∫ x, F x ∂gaussMeasure n) +
          c * (n - 1) * ∫ x, F x ∂gaussMeasure n
        = ∫ x, h x * ⟪x, e⟫ ∂gaussMeasure n - c * ∫ x, F x ∂gaussMeasure n := by ring
      _ ≤ _ := step1

/-- **Strict Gaussian Poincaré inequality on a cone strictly inside a half-space** (a spherical
cap smaller than a hemisphere has first Dirichlet eigenvalue `> n - 1`). -/
theorem gaussL2_lt_dirichletEnergy_of_subset_cone (hn : 2 ≤ n)
    {w : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ≥0}
    (hw : LipschitzWith L w) (hnn : ∀ x, 0 ≤ w x) (hhom : IsOneHomogeneous w)
    {e : EuclideanSpace ℝ (Fin n)} {s : ℝ} (hs : 0 < s)
    (hsupp : ∀ x, 0 < w x → s * ‖x‖ ≤ ⟪x, e⟫) (hpos : ∃ x, 0 < w x) :
    gaussL2 w < dirichletEnergy w := by
  have hw0 : w 0 = 0 := hhom.map_zero
  have hM : ∀ x, 0 < w x →
      0 < coneWeight e (s / 2) x ∧ w x ≤ 2 * L / s * coneWeight e (s / 2) x := by
    intro x hx
    have hx0 : x ≠ 0 := by rintro rfl; rw [hw0] at hx; exact lt_irrefl _ hx
    have hnx : 0 < ‖x‖ := norm_pos_iff.2 hx0
    have h1 := hsupp x hx
    have hφ : s / 2 * ‖x‖ ≤ coneWeight e (s / 2) x := by unfold coneWeight; linarith
    refine ⟨lt_of_lt_of_le (by positivity) hφ, ?_⟩
    have hwx : w x ≤ L * ‖x‖ := by
      have := hw.dist_le_mul x 0
      rw [Real.dist_eq, hw0, sub_zero, dist_zero_right] at this
      exact (le_abs_self _).trans this
    calc w x ≤ L * ‖x‖ := hwx
      _ = 2 * L / s * (s / 2 * ‖x‖) := by field_simp
      _ ≤ 2 * L / s * coneWeight e (s / 2) x := by gcongr
  obtain ⟨I, -, hI, hle⟩ := exists_gaussL2_add_le_dirichletEnergy hw hnn hhom e
    (by positivity : (0 : ℝ) ≤ s / 2) (by positivity) hM
  have hI := hI hpos
  have hn' : (0 : ℝ) < n - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have : 0 < s / 2 * (n - 1) * I := by positivity
  linarith

/-- **Gaussian Poincaré inequality on a half-space** (hemisphere: first eigenvalue `n - 1`). -/
theorem gaussL2_le_dirichletEnergy_of_subset_halfSpace
    {w : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ≥0}
    (hw : LipschitzWith L w) (hnn : ∀ x, 0 ≤ w x) (hhom : IsOneHomogeneous w)
    {e : EuclideanSpace ℝ (Fin n)} (he : ‖e‖ = 1) (hsupp : ∀ x, 0 < w x → 0 < ⟪x, e⟫) :
    gaussL2 w ≤ dirichletEnergy w := by
  have hM : ∀ x, 0 < w x → 0 < coneWeight e 0 x ∧ w x ≤ L * coneWeight e 0 x := by
    intro x hx
    have hxe := hsupp x hx
    simp only [coneWeight, zero_mul, sub_zero]
    refine ⟨hxe, ?_⟩
    set y := x - ⟪x, e⟫ • e
    have hye : ⟪y, e⟫ = 0 := by
      simp only [y, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, he]; ring
    have hy : w y = 0 := le_antisymm (not_lt.1 fun h => by
      have := hsupp y h; rw [hye] at this; exact lt_irrefl _ this) (hnn y)
    have := hw.dist_le_mul x y
    rw [Real.dist_eq, hy, sub_zero, dist_eq_norm, show x - y = ⟪x, e⟫ • e by simp [y],
      norm_smul, he, mul_one, Real.norm_of_nonneg hxe.le] at this
    exact (le_abs_self _).trans this
  obtain ⟨I, -, -, hle⟩ := exists_gaussL2_add_le_dirichletEnergy hw hnn hhom e le_rfl L.2 hM
  simpa using hle

end Sperner
