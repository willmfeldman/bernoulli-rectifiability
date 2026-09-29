/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Sperner.Polarization

/-!
# Functions fixed by all polarizations favouring `e` are cap-symmetric

If `w (σ_a x) ≤ w x` whenever `⟪a, e⟫ > 0` and `⟪x, a⟫ > 0`, then on every sphere `w` is a
nondecreasing function of `⟪x, e⟫` (reflect `x` to `y` through the bisecting hyperplane).
Consequently, for a nonnegative, continuous, one-homogeneous such `w`:
* if `2 γ{w > 0} < γ(ℝⁿ)`, then `{w > 0} ⊆ {⟪x, e⟫ ≥ s |x|}` for some `s > 0`;
* if `2 γ{w > 0} ≤ γ(ℝⁿ)`, then `{w > 0} ⊆ {⟪x, e⟫ > 0}`.
-/

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace Sperner

variable {n : ℕ}

/-- The reflection through the hyperplane bisecting `x` and `y` (with `|x| = |y|`) swaps them. -/
lemma reflect_bisector {x y : EuclideanSpace ℝ (Fin n)} (hxy : ‖x‖ = ‖y‖) (hne : x ≠ y) :
    reflect (‖x - y‖⁻¹ • (x - y)) x = y := by
  have hd : ‖x - y‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 hne)
  have ha : ‖‖x - y‖⁻¹ • (x - y)‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hd]
  rw [reflect_apply ha, real_inner_smul_right, smul_smul]
  have hin : ⟪x, x - y⟫ = ‖x - y‖ ^ 2 / 2 := by
    rw [@norm_sub_sq_real, inner_sub_right, real_inner_self_eq_norm_sq, hxy]; ring
  rw [hin]
  have : 2 * (‖x - y‖⁻¹ * (‖x - y‖ ^ 2 / 2)) * ‖x - y‖⁻¹ = 1 := by field_simp
  rw [this, one_smul]; abel

/-- **Monotonicity on spheres.** -/
lemma le_of_norm_eq_of_inner_lt {w : EuclideanSpace ℝ (Fin n) → ℝ}
    {e : EuclideanSpace ℝ (Fin n)}
    (hsym : ∀ a : EuclideanSpace ℝ (Fin n), ‖a‖ = 1 → 0 < ⟪a, e⟫ →
      ∀ x, 0 < ⟪x, a⟫ → w (reflect a x) ≤ w x)
    {x y : EuclideanSpace ℝ (Fin n)} (hxy : ‖x‖ = ‖y‖) (hlt : ⟪y, e⟫ < ⟪x, e⟫) :
    w y ≤ w x := by
  have hne : x ≠ y := by rintro rfl; exact lt_irrefl _ hlt
  have hd : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  set a := ‖x - y‖⁻¹ • (x - y)
  have ha : ‖a‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hd.ne']
  have hae : 0 < ⟪a, e⟫ := by
    rw [real_inner_smul_left, inner_sub_left]
    exact mul_pos (inv_pos.2 hd) (by linarith)
  have hxa : 0 < ⟪x, a⟫ := by
    rw [real_inner_smul_right]
    have : ⟪x, x - y⟫ = ‖x - y‖ ^ 2 / 2 := by
      rw [@norm_sub_sq_real, inner_sub_right, real_inner_self_eq_norm_sq, hxy]; ring
    rw [this]; positivity
  have := hsym a ha hae x hxa
  rwa [reflect_bisector hxy hne] at this

lemma two_mul_gaussMeasure_halfSpace {e : EuclideanSpace ℝ (Fin n)} (he : ‖e‖ = 1) :
    2 * gaussMeasure n {x | 0 < ⟪x, e⟫} = gaussMeasure n univ := by
  have hm1 : MeasurableSet {x : EuclideanSpace ℝ (Fin n) | 0 < ⟪x, e⟫} :=
    measurableSet_lt measurable_const (continuous_id.inner continuous_const).measurable
  have hm2 : MeasurableSet {x : EuclideanSpace ℝ (Fin n) | ⟪x, e⟫ < 0} :=
    measurableSet_lt (continuous_id.inner continuous_const).measurable measurable_const
  -- the reflection in `e^⊥` swaps the two open half-spaces
  have hswap : gaussMeasure n {x | ⟪x, e⟫ < 0} = gaussMeasure n {x | 0 < ⟪x, e⟫} := by
    rw [← measurePreserving_reflect (a := e).measure_preimage hm1.nullMeasurableSet]
    congr 1; ext x
    simp [inner_reflect_left he]
  have hnull : gaussMeasure n {x | ⟪x, e⟫ = 0} = 0 := by
    have := ae_inner_ne_zero (n := n) he
    rw [ae_iff] at this
    simpa using this
  have hunion : univ = {x : EuclideanSpace ℝ (Fin n) | 0 < ⟪x, e⟫} ∪
      {x | ⟪x, e⟫ < 0} ∪ {x | ⟪x, e⟫ = 0} := by
    ext x; simp only [mem_univ, mem_union, mem_setOf_eq, true_iff]
    rcases lt_trichotomy ⟪x, e⟫ 0 with h | h | h <;> simp [h]
  have hle : gaussMeasure n univ ≤ 2 * gaussMeasure n {x | 0 < ⟪x, e⟫} := by
    rw [hunion]
    refine (measure_union_le _ _).trans ?_
    rw [hnull, add_zero]
    refine (measure_union_le _ _).trans ?_
    rw [hswap, two_mul]
  have hge : 2 * gaussMeasure n {x | 0 < ⟪x, e⟫} ≤ gaussMeasure n univ := by
    rw [two_mul]
    nth_rw 2 [← hswap]
    rw [← measure_union _ hm2]
    · exact measure_mono (subset_univ _)
    · exact Set.disjoint_left.2 fun x h1 h2 => by
        simp only [mem_setOf_eq] at h1 h2; linarith
  exact le_antisymm hge hle

variable {w : EuclideanSpace ℝ (Fin n) → ℝ} {e : EuclideanSpace ℝ (Fin n)}

/-- If `w` is positive at some point `θ₁` of the unit sphere, it is positive on the whole cone
`{⟪x, e⟫ > ⟪θ₁, e⟫ |x|}`. -/
lemma pos_of_inner_gt (hhom : IsOneHomogeneous w)
    (hsym : ∀ a : EuclideanSpace ℝ (Fin n), ‖a‖ = 1 → 0 < ⟪a, e⟫ →
      ∀ x, 0 < ⟪x, a⟫ → w (reflect a x) ≤ w x)
    {θ₁ : EuclideanSpace ℝ (Fin n)} (hθ₁ : ‖θ₁‖ = 1) (hw₁ : 0 < w θ₁)
    {x : EuclideanSpace ℝ (Fin n)} (hx : ⟪θ₁, e⟫ * ‖x‖ < ⟪x, e⟫) : 0 < w x := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  have hnx : 0 < ‖x‖ := norm_pos_iff.2 hx0
  set θ := ‖x‖⁻¹ • x
  have hθ : ‖θ‖ = 1 := by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnx.ne']
  have hlt : ⟪θ₁, e⟫ < ⟪θ, e⟫ := by
    rw [real_inner_smul_left, lt_inv_mul_iff₀ hnx, mul_comm]; exact hx
  have h1 := le_of_norm_eq_of_inner_lt hsym (hθ.trans hθ₁.symm) hlt
  have hxθ : x = ‖x‖ • θ := by rw [smul_smul, mul_inv_cancel₀ hnx.ne', one_smul]
  rw [hxθ, hhom θ ‖x‖ hnx]
  exact mul_pos hnx (hw₁.trans_le h1)

lemma normalize_pos {x : EuclideanSpace ℝ (Fin n)} (hhom : IsOneHomogeneous w)
    (hx : 0 < w x) : x ≠ 0 ∧ ‖‖x‖⁻¹ • x‖ = 1 ∧ 0 < w (‖x‖⁻¹ • x) := by
  have hx0 : x ≠ 0 := by rintro rfl; rw [hhom.map_zero] at hx; exact lt_irrefl _ hx
  have hnx : 0 < ‖x‖ := norm_pos_iff.2 hx0
  refine ⟨hx0, by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnx.ne'], ?_⟩
  rw [hhom x _ (inv_pos.2 hnx)]; exact mul_pos (inv_pos.2 hnx) hx

/-- **Half-space support.** -/
theorem inner_pos_of_two_mul_le (he : ‖e‖ = 1) (hwc : Continuous w)
    (hhom : IsOneHomogeneous w)
    (hsym : ∀ a : EuclideanSpace ℝ (Fin n), ‖a‖ = 1 → 0 < ⟪a, e⟫ →
      ∀ x, 0 < ⟪x, a⟫ → w (reflect a x) ≤ w x)
    (hhalf : 2 * gaussMeasure n {x | 0 < w x} ≤ gaussMeasure n univ) :
    ∀ x, 0 < w x → 0 < ⟪x, e⟫ := by
  intro x₁ hx₁
  by_contra hle
  push Not at hle
  obtain ⟨hx0, hθ₁, hwθ₁⟩ := normalize_pos hhom hx₁
  set θ₁ := ‖x₁‖⁻¹ • x₁
  have hθe : ⟪θ₁, e⟫ ≤ 0 := by
    rw [real_inner_smul_left]; exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hle
  -- the open half-space is contained in `{w > 0}`
  have hH : {x | 0 < ⟪x, e⟫} ⊆ {x | 0 < w x} := fun x (hx : 0 < ⟪x, e⟫) =>
    pos_of_inner_gt hhom hsym hθ₁ hwθ₁
      (lt_of_le_of_lt (mul_nonpos_of_nonpos_of_nonneg hθe (norm_nonneg x)) hx)
  -- and `{w > 0}` also meets the opposite open half-space
  have hV : ({x | 0 < w x} ∩ {x | ⟪x, e⟫ < 0}).Nonempty := by
    have hc : Continuous fun t : ℝ => x₁ - t • e := by fun_prop
    have hev : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < w (x₁ - t • e) :=
      (hwc.comp hc).continuousAt.eventually (lt_mem_nhds (by simpa using hx₁))
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
    have hmem : 0 < w (x₁ - (ε / 2) • e) :=
      hball (by rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]; linarith)
    refine ⟨x₁ - (ε / 2) • e, hmem, ?_⟩
    simp only [mem_setOf_eq, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
      he]
    nlinarith
  have hopen : IsOpen ({x | 0 < w x} ∩ {x | ⟪x, e⟫ < 0}) :=
    (isOpen_lt continuous_const hwc).inter
      (isOpen_lt (continuous_id.inner continuous_const) continuous_const)
  have hVpos := gaussMeasure_pos_of_isOpen hopen hV
  have hdisj : Disjoint {x : EuclideanSpace ℝ (Fin n) | 0 < ⟪x, e⟫}
      ({x | 0 < w x} ∩ {x | ⟪x, e⟫ < 0}) :=
    Set.disjoint_left.2 fun x h1 h2 => by
      simp only [mem_setOf_eq, mem_inter_iff] at h1 h2; linarith [h2.2]
  have hsum : gaussMeasure n {x | 0 < ⟪x, e⟫} +
      gaussMeasure n ({x | 0 < w x} ∩ {x | ⟪x, e⟫ < 0}) ≤ gaussMeasure n {x | 0 < w x} := by
    rw [← measure_union hdisj hopen.measurableSet]
    exact measure_mono (union_subset hH inter_subset_left)
  have hfin : gaussMeasure n {x | 0 < ⟪x, e⟫} ≠ ⊤ := measure_ne_top _ _
  have := two_mul_gaussMeasure_halfSpace (n := n) he
  have h2 : 2 * gaussMeasure n {x | 0 < ⟪x, e⟫} < 2 * gaussMeasure n {x | 0 < w x} := by
    rw [mul_comm 2, mul_comm 2]
    exact ENNReal.mul_lt_mul_left two_ne_zero ENNReal.ofNat_ne_top
      (lt_of_lt_of_le (ENNReal.lt_add_right hfin hVpos.ne') hsum)
  rw [this] at h2
  exact absurd hhalf (not_le.2 h2)

/-- **Cone support** when the positivity set has less than half of the Gaussian measure. -/
theorem exists_cone_of_two_mul_lt (he : ‖e‖ = 1) (hnn : ∀ x, 0 ≤ w x)
    (hhom : IsOneHomogeneous w)
    (hsym : ∀ a : EuclideanSpace ℝ (Fin n), ‖a‖ = 1 → 0 < ⟪a, e⟫ →
      ∀ x, 0 < ⟪x, a⟫ → w (reflect a x) ≤ w x)
    (hsmall : 2 * gaussMeasure n {x | 0 < w x} < gaussMeasure n univ) :
    ∃ s : ℝ, 0 < s ∧ ∀ x, 0 < w x → s * ‖x‖ ≤ ⟪x, e⟫ := by
  -- some point of the open upper hemisphere is a zero of `w`
  have hθ₀ : ∃ θ₀ : EuclideanSpace ℝ (Fin n), ‖θ₀‖ = 1 ∧ 0 < ⟪θ₀, e⟫ ∧ w θ₀ = 0 := by
    by_contra hno
    push Not at hno
    have hH : {x | 0 < ⟪x, e⟫} ⊆ {x | 0 < w x} := by
      intro x (hx : 0 < ⟪x, e⟫)
      have hx0 : x ≠ 0 := by rintro rfl; simp at hx
      have hnx : 0 < ‖x‖ := norm_pos_iff.2 hx0
      have hθ : ‖‖x‖⁻¹ • x‖ = 1 := by
        rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnx.ne']
      have hθe : 0 < ⟪‖x‖⁻¹ • x, e⟫ := by rw [real_inner_smul_left]; positivity
      have h1 := lt_of_le_of_ne (hnn _) (hno _ hθ hθe).symm
      have : x = ‖x‖ • (‖x‖⁻¹ • x) := by rw [smul_smul, mul_inv_cancel₀ hnx.ne', one_smul]
      change 0 < w x
      rw [this, hhom _ _ hnx]; exact mul_pos hnx h1
    have := (two_mul_gaussMeasure_halfSpace (n := n) he).symm.le.trans
      (mul_le_mul_right (measure_mono hH) 2)
    exact absurd hsmall (not_lt.2 this)
  obtain ⟨θ₀, hθ₀, hpos, hzero⟩ := hθ₀
  refine ⟨⟪θ₀, e⟫, hpos, fun x hx => ?_⟩
  obtain ⟨hx0, hθ, hwθ⟩ := normalize_pos hhom hx
  have hnx : 0 < ‖x‖ := norm_pos_iff.2 hx0
  by_contra hlt
  push Not at hlt
  have : ⟪‖x‖⁻¹ • x, e⟫ < ⟪θ₀, e⟫ := by
    rw [real_inner_smul_left, inv_mul_lt_iff₀ hnx]; linarith
  have := le_of_norm_eq_of_inner_lt hsym (hθ₀.trans hθ.symm) this
  rw [hzero] at this
  exact absurd hwθ (not_lt.2 this)

end Sperner
