/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Basic.Setup
public import InnerVariational.Basic.LipschitzFTC
public import InnerVariational.Basic.Polar
public import InnerVariational.Basic.SphereIntegral
public import Mathlib.Order.CompletePartialOrder
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Data.Real.StarOrdered
public import GMTFoundations.Defs.Setup

/-!
# Calculus along lines and rays for Lipschitz functions

This file collects the one-variable calculus used in the proof of the two-point homogeneity
lemma, Lemma 6.2 of D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure,
and compactness for non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025),
no. 3, DOI 10.1002/cpa.22226; arXiv:2306.10131 (numbering of arXiv v2), in reusable form.

## Main results

* `annulus a b = B_b ∖ B_a` and its API: splitting (`setIntegral_annulus_eq_add`), monotonicity,
  and the changes of variables `y ↦ T • y` (`setIntegral_annulus_comp_smul`) and
  `z ↦ p + ρ • z` (`setIntegral_annulus_comp_add_smul`).
* `sq_setIntegral_le_measureReal_mul`, `sq_intervalIntegral_le`: Cauchy–Schwarz
  `(∫_s f)² ≤ |s| ∫_s f²`.
* `setIntegral_le_of_ae_le_intervalIntegral`: integrating a pointwise bound by a line integral
  (Tonelli).
* `gradient_comp_add_left`, `gradient_comp_add_smul`: gradients of translates and rescalings.
* `LipschitzWith.ae_ae_hasDerivAt_add_smul`, `LipschitzWith.ae_ae_hasDerivAt_smul`: for `u`
  Lipschitz and a.e. `y`, the functions `t ↦ u (y + t • v)` and `t ↦ u (t • y)` have derivatives
  `⟪∇u(y + t v), v⟫` and `⟪∇u(t y), y⟫` for a.e. `t` (Rademacher + Fubini).
* `LipschitzWith.setIntegral_sq_exp_mul_comp_add_sub_le` (*almost invariance along segments*,
  the estimate (6.18) in the proof of Lemma 6.2): if `∇u · x + a u` is small in `L²(S)` and the
  segments `y + [0,1] x`, `y ∈ E`,
  lie in `S`, then `e^a u(y + x) - u(y)` is small in `L²(E)`.
* `LipschitzWith.setIntegral_sq_rpow_mul_comp_smul_sub_le` (*almost homogeneity along rays*,
  the estimate (6.19) in the proof of Lemma 6.2): if `∇u(z) · z - N u(z)` is small in `L²(S)`
  and the segments `[1, T] y`, `y ∈ E`,
  lie in `S`, then `T^{-N} u(T y) - u(y)` is small in `L²(E)`.

## Implementation notes

The paper integrates the ray identity over spheres `∂B_s`. We integrate over arbitrary measurable
sets `E` (in practice annuli), which only needs the change of variables `y ↦ t • y` on `ℝⁿ`
(`MeasureTheory.Measure.integral_comp_smul`) and no polar coordinates.

The a.e. differentiability along lines and rays uses `ae_ae_add_smul_notMem` and
`ae_ae_smul_notMem` (`Basic/Polar.lean`, Tonelli on `ℝⁿ × ℝ`) together with Rademacher's theorem.
-/

open MeasureTheory Metric Set Filter Bornology
open scoped NNReal RealInnerProductSpace Pointwise

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

/-! ### Annuli -/

/-- The annulus `B_b ∖ B_a = {y : a ≤ ‖y‖ < b}` centred at the origin of `ℝⁿ`. -/
def annulus (a b : ℝ) : Set (Rn n) := ball 0 b \ ball 0 a

theorem annulus_def (a b : ℝ) : (annulus a b : Set (Rn n)) = ball 0 b \ ball 0 a := rfl

@[simp]
theorem mem_annulus {a b : ℝ} {y : Rn n} : y ∈ annulus a b ↔ a ≤ ‖y‖ ∧ ‖y‖ < b := by
  simp [annulus, and_comm]

theorem measurableSet_annulus (a b : ℝ) : MeasurableSet (annulus a b : Set (Rn n)) :=
  measurableSet_ball.diff measurableSet_ball

theorem isBounded_annulus (a b : ℝ) : IsBounded (annulus a b : Set (Rn n)) :=
  isBounded_ball.subset diff_subset

theorem annulus_subset_annulus {a b a' b' : ℝ} (ha : a ≤ a') (hb : b' ≤ b) :
    (annulus a' b' : Set (Rn n)) ⊆ annulus a b := fun y hy => by
  rw [mem_annulus] at hy ⊢
  exact ⟨ha.trans hy.1, hy.2.trans_le hb⟩

theorem annulus_union_annulus {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    (annulus a b ∪ annulus b c : Set (Rn n)) = annulus a c := by
  ext y
  simp only [mem_union, mem_annulus]
  constructor
  · rintro (h | h)
    · exact ⟨h.1, h.2.trans_le hbc⟩
    · exact ⟨hab.trans h.1, h.2⟩
  · rintro ⟨h1, h2⟩
    rcases lt_or_ge ‖y‖ b with h | h
    · exact Or.inl ⟨h1, h⟩
    · exact Or.inr ⟨h, h2⟩

theorem disjoint_annulus_annulus (a b c : ℝ) :
    Disjoint (annulus a b : Set (Rn n)) (annulus b c) := by
  rw [Set.disjoint_left]
  intro y h1 h2
  rw [mem_annulus] at h1 h2
  exact absurd h2.1 (not_le.2 h1.2)

theorem smul_annulus {T : ℝ} (hT : 0 < T) (a b : ℝ) :
    T • (annulus a b : Set (Rn n)) = annulus (T * a) (T * b) := by
  ext z
  rw [mem_smul_set_iff_inv_smul_mem₀ hT.ne', mem_annulus, mem_annulus, norm_smul,
    Real.norm_eq_abs, abs_inv, abs_of_pos hT, ← div_eq_inv_mul, le_div_iff₀ hT, div_lt_iff₀ hT,
    mul_comm a, mul_comm b]

/-- Splitting the integral over an annulus into two concentric annuli. -/
theorem setIntegral_annulus_eq_add {f : Rn n → ℝ} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hf : IntegrableOn f (annulus a c)) :
    ∫ y in annulus a c, f y = (∫ y in annulus a b, f y) + ∫ y in annulus b c, f y := by
  rw [← annulus_union_annulus hab hbc] at hf ⊢
  exact setIntegral_union (disjoint_annulus_annulus a b c) (measurableSet_annulus b c)
    hf.left_of_union hf.right_of_union

/-- Change of variables `y ↦ T • y` on an annulus. -/
theorem setIntegral_annulus_comp_smul (f : Rn n → ℝ) {T : ℝ} (hT : 0 < T) (a b : ℝ) :
    ∫ y in annulus a b, f (T • y) = (T ^ n)⁻¹ * ∫ z in annulus (T * a) (T * b), f z := by
  rw [Measure.setIntegral_comp_smul volume f _ hT.ne', smul_annulus hT, finrank_euclideanSpace_fin,
    abs_of_pos (by positivity), smul_eq_mul]

/-! ### Elementary integral inequalities -/

/-- *Cauchy–Schwarz* (or Jensen) on a set of finite measure: `(∫_s f)² ≤ μ(s) ∫_s f²`. -/
theorem sq_setIntegral_le_measureReal_mul {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : Set α} {f : α → ℝ} (hs : μ s ≠ ⊤) (hf : IntegrableOn f s μ)
    (hf2 : IntegrableOn (fun x => f x ^ 2) s μ) :
    (∫ x in s, f x ∂μ) ^ 2 ≤ μ.real s * ∫ x in s, f x ^ 2 ∂μ := by
  set c := ∫ x in s, f x ∂μ
  set m := μ.real s
  have hI : ∫ x in s, (m * f x - c) ^ 2 ∂μ = m * (m * ∫ x in s, f x ^ 2 ∂μ - c ^ 2) := by
    haveI : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.2 hs
    have h1 : Integrable (fun x => m ^ 2 * f x ^ 2 - (2 * m * c) * f x) (μ.restrict s) :=
      (hf2.const_mul _).sub (hf.const_mul _)
    have e1 : ∫ x in s, (m * f x - c) ^ 2 ∂μ =
        ∫ x in s, (m ^ 2 * f x ^ 2 - (2 * m * c) * f x + c ^ 2) ∂μ :=
      integral_congr_ae (Eventually.of_forall fun x => by ring)
    have e2 : ∫ x in s, (m ^ 2 * f x ^ 2 - (2 * m * c) * f x + c ^ 2) ∂μ =
        (∫ x in s, (m ^ 2 * f x ^ 2 - (2 * m * c) * f x) ∂μ) + ∫ _ in s, c ^ 2 ∂μ :=
      integral_add h1 (integrable_const _)
    have e3 : ∫ x in s, (m ^ 2 * f x ^ 2 - (2 * m * c) * f x) ∂μ =
        (∫ x in s, m ^ 2 * f x ^ 2 ∂μ) - ∫ x in s, (2 * m * c) * f x ∂μ :=
      integral_sub (hf2.const_mul _) (hf.const_mul _)
    rw [e1, e2, e3, integral_const_mul, integral_const_mul, setIntegral_const, smul_eq_mul]
    ring
  have h0 : 0 ≤ ∫ x in s, (m * f x - c) ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  rw [hI] at h0
  rcases (measureReal_nonneg : 0 ≤ m).eq_or_lt with hm | hm
  · have hs0 : μ s = 0 := (measureReal_eq_zero_iff hs).1 hm.symm
    have hc : c = 0 := by simp [c, Measure.restrict_eq_zero.2 hs0]
    have hm0 : m = 0 := hm.symm
    rw [hc, hm0]
    simp
  · nlinarith

/-- *Cauchy–Schwarz* on an interval: `(∫_a^b f)² ≤ (b - a) ∫_a^b f²`. -/
theorem sq_intervalIntegral_le {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b)
    (hf2 : IntervalIntegrable (fun x => f x ^ 2) volume a b) :
    (∫ x in a..b, f x) ^ 2 ≤ (b - a) * ∫ x in a..b, f x ^ 2 := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
    ← Real.volume_real_Ioc_of_le hab]
  exact sq_setIntegral_le_measureReal_mul measure_Ioc_lt_top.ne hf.1 hf2.1

/-- A measurable function bounded on a bounded measurable set is integrable there. -/
theorem integrableOn_of_isBounded_of_abs_le {f : Rn n → ℝ} {S : Set (Rn n)}
    (hf : AEStronglyMeasurable f volume) (hS : MeasurableSet S) (hSb : IsBounded S)
    {M : ℝ} (hM : ∀ z ∈ S, |f z| ≤ M) : IntegrableOn f S :=
  Measure.integrableOn_of_bounded (hSb.measure_lt_top).ne hf (M := M)
    ((ae_restrict_iff' hS).2 (Eventually.of_forall fun z hz => by
      simpa [Real.norm_eq_abs] using hM z hz))

/-- If `t • y ∈ S` for all `y ∈ E` and `t ≥ 1`, then `∫_E f(t y) dy ≤ ∫_S f` for `f ≥ 0`. -/
theorem setIntegral_comp_smul_le {f : Rn n → ℝ} (hf0 : ∀ z, 0 ≤ f z) {E S : Set (Rn n)}
    (hE : MeasurableSet E) (hS : MeasurableSet S) (hfS : IntegrableOn f S) {t : ℝ} (ht : 1 ≤ t)
    (hES : ∀ y ∈ E, t • y ∈ S) : ∫ y in E, f (t • y) ≤ ∫ z in S, f z := by
  have ht0 : t ≠ 0 := by positivity
  calc ∫ y in E, f (t • y) = ∫ y, E.indicator (fun y => f (t • y)) y :=
        (integral_indicator hE).symm
    _ ≤ ∫ y, S.indicator f (t • y) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun y => indicator_nonneg
          (fun y _ => hf0 _) y) ((hfS.integrable_indicator hS).comp_smul ht0)
          (Eventually.of_forall fun y => ?_)
        by_cases hy : y ∈ E
        · simp [hy, hES y hy]
        · simp only [indicator_of_notMem hy]
          exact indicator_nonneg (fun z _ => hf0 z) _
    _ = |(t ^ n)⁻¹| * ∫ z, S.indicator f z := by
        rw [Measure.integral_comp_smul volume (S.indicator f) t, finrank_euclideanSpace_fin,
          smul_eq_mul]
    _ ≤ ∫ z in S, f z := by
        rw [integral_indicator hS]
        have h1 : |(t ^ n)⁻¹| ≤ 1 := by
          rw [abs_of_pos (by positivity)]
          exact inv_le_one_of_one_le₀ (one_le_pow₀ ht)
        exact mul_le_of_le_one_left (setIntegral_nonneg hS fun z _ => hf0 z) h1

/-- If `y + w ∈ S` for all `y ∈ E`, then `∫_E f(y + w) dy ≤ ∫_S f` for `f ≥ 0`. -/
theorem setIntegral_comp_add_le {f : Rn n → ℝ} (hf0 : ∀ z, 0 ≤ f z) {E S : Set (Rn n)}
    (hE : MeasurableSet E) (hS : MeasurableSet S) (hfS : IntegrableOn f S) (w : Rn n)
    (hES : ∀ y ∈ E, y + w ∈ S) : ∫ y in E, f (y + w) ≤ ∫ z in S, f z := by
  calc ∫ y in E, f (y + w) = ∫ y, E.indicator (fun y => f (y + w)) y :=
        (integral_indicator hE).symm
    _ ≤ ∫ y, S.indicator f (y + w) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun y => indicator_nonneg
          (fun y _ => hf0 _) y) ((hfS.integrable_indicator hS).comp_add_right w)
          (Eventually.of_forall fun y => ?_)
        by_cases hy : y ∈ E
        · simp [hy, hES y hy]
        · simp only [indicator_of_notMem hy]
          exact indicator_nonneg (fun z _ => hf0 z) _
    _ = ∫ z in S, f z := by
        rw [integral_add_right_eq_self (fun z => S.indicator f z) w, integral_indicator hS]

/-- Integrating a pointwise bound by a line integral: if `0 ≤ G y ≤ c ∫_α^β F(y, t) dt` for a.e.
`y ∈ E`, with `F ≥ 0` measurable and bounded on `E × [α, β]`, and `∫_E F(·, t) ≤ K` for every
`t ∈ [α, β]`, then `∫_E G ≤ c (β - α) K`. This is Tonelli plus the trivial bound in `t`. -/
theorem setIntegral_le_of_ae_le_intervalIntegral {E : Set (Rn n)} (hE : MeasurableSet E)
    (hEfin : volume E ≠ ⊤) {α β : ℝ} (hαβ : α ≤ β) {F : Rn n → ℝ → ℝ}
    (hF : Measurable (Function.uncurry F)) (hF0 : ∀ y t, 0 ≤ F y t) {M : ℝ}
    (hFM : ∀ y ∈ E, ∀ t ∈ Icc α β, F y t ≤ M) {K : ℝ}
    (hK : ∀ t ∈ Icc α β, ∫ y in E, F y t ≤ K) {G : Rn n → ℝ} (hG0 : ∀ y, 0 ≤ G y) {c : ℝ}
    (hc : 0 ≤ c) (hG : ∀ᵐ y, y ∈ E → G y ≤ c * ∫ t in α..β, F y t) :
    ∫ y in E, G y ≤ c * ((β - α) * K) := by
  haveI : IsFiniteMeasure (volume.restrict E) := isFiniteMeasure_restrict.2 hEfin
  have hprod : Integrable (Function.uncurry F)
      ((volume.restrict E).prod (volume.restrict (Ioc α β))) := by
    refine Integrable.of_bound hF.aestronglyMeasurable M ?_
    rw [Measure.prod_restrict, ae_restrict_iff' (hE.prod measurableSet_Ioc)]
    refine Eventually.of_forall fun p hp => ?_
    change |F p.1 p.2| ≤ M
    rw [abs_of_nonneg (hF0 _ _)]
    exact hFM p.1 hp.1 p.2 (Ioc_subset_Icc_self hp.2)
  calc ∫ y in E, G y ≤ ∫ y in E, c * ∫ t in Ioc α β, F y t := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun y => hG0 y)
          (hprod.integral_prod_left.const_mul c) ?_
        rw [EventuallyLE, ae_restrict_iff' hE]
        filter_upwards [hG] with y hy hyE
        simpa [intervalIntegral.integral_of_le hαβ] using hy hyE
    _ = c * ∫ t in Ioc α β, ∫ y in E, F y t := by
        rw [integral_const_mul, integral_integral_swap hprod]
    _ ≤ c * ∫ _ in Ioc α β, K :=
        mul_le_mul_of_nonneg_left (setIntegral_mono_on hprod.integral_prod_right
          (integrableOn_const measure_Ioc_lt_top.ne) measurableSet_Ioc
          fun t ht => hK t (Ioc_subset_Icc_self ht)) hc
    _ = c * ((β - α) * K) := by
        rw [setIntegral_const, Real.volume_real_Ioc_of_le hαβ, smul_eq_mul]

/-- A function bounded and a.e.-strongly measurable on `[α, β]` is interval integrable. -/
theorem intervalIntegrable_of_abs_le {f : ℝ → ℝ} {α β : ℝ} (hαβ : α ≤ β)
    (hf : AEStronglyMeasurable f volume) {M : ℝ} (hM : ∀ t ∈ Icc α β, |f t| ≤ M) :
    IntervalIntegrable f volume α β :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hαβ).2
    (Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne hf (M := M)
      ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun t ht => by
        simpa [Real.norm_eq_abs] using hM t (Ioc_subset_Icc_self ht))))

/-- A continuous function is integrable on every bounded set. -/
theorem integrableOn_of_continuous {f : Rn n → ℝ} (hf : Continuous f) {S : Set (Rn n)}
    (hSb : IsBounded S) : IntegrableOn f S := by
  obtain ⟨r, hr⟩ := hSb.subset_closedBall 0
  exact (hf.continuousOn.integrableOn_compact (isCompact_closedBall 0 r)).mono_set hr

/-- Monotonicity of `∫_{B_b ∖ B_a} f` in the annulus, for `f ≥ 0` continuous. -/
theorem setIntegral_annulus_mono {f : Rn n → ℝ} (hf : Continuous f) (hf0 : ∀ z, 0 ≤ f z)
    {a b a' b' : ℝ} (ha : a ≤ a') (hb : b' ≤ b) :
    ∫ y in annulus a' b', f y ≤ ∫ y in annulus a b, f y :=
  setIntegral_mono_set (integrableOn_of_continuous hf (isBounded_annulus a b))
    (Eventually.of_forall hf0) (annulus_subset_annulus ha hb).eventuallyLE

/-! ### Lipschitz functions: gradient bounds and derivatives along lines and rays -/

/-- `⟪∇u(z), w⟫ = Du(z) w`, with no differentiability assumption (both sides vanish when `u` is
not differentiable at `z`). -/
theorem inner_gradient_eq_fderiv (u : Rn n → ℝ) (z w : Rn n) :
    ⟪gradient u z, w⟫ = fderiv ℝ u z w :=
  InnerProductSpace.toDual_symm_apply

/-- The gradient of a translate is the translate of the gradient. -/
theorem gradient_comp_add_left (u : Rn n → ℝ) (x z : Rn n) :
    gradient (fun y => u (x + y)) z = gradient u (x + z) := by
  simp only [gradient, fderiv_comp_add_left]

/-- The gradient of `y ↦ u (p + ρ • y)` is `ρ • ∇u (p + ρ • y)`. -/
theorem gradient_comp_add_smul (u : Rn n → ℝ) (p : Rn n) (ρ : ℝ) (z : Rn n) :
    gradient (fun y => u (p + ρ • y)) z = ρ • gradient u (p + ρ • z) := by
  have h := fderiv_comp_smul (𝕜 := ℝ) (f := fun w => u (p + w)) (x := z) ρ
  simp only at h
  simp [gradient, h, fderiv_comp_add_left]

/-- Change of variables `y = p + ρ • z` from the annulus `B_b ∖ B_a` to `B_{ρb}(p) ∖ B_{ρa}(p)`. -/
theorem setIntegral_annulus_comp_add_smul (f : Rn n → ℝ) (p : Rn n) {ρ : ℝ} (hρ : 0 < ρ)
    (a b : ℝ) : ∫ z in annulus a b, f (p + ρ • z) =
      (ρ ^ n)⁻¹ * ∫ y in ball p (ρ * b) \ ball p (ρ * a), f y := by
  rw [setIntegral_annulus_comp_smul (fun w => f (p + w)) hρ]
  congr 1
  have hpre : (fun w : Rn n => p + w) ⁻¹' (ball p (ρ * b) \ ball p (ρ * a)) =
      annulus (ρ * a) (ρ * b) := by
    ext w
    simp [annulus, mem_ball, dist_eq_norm]
  rw [← hpre]
  exact (measurePreserving_add_left volume p).setIntegral_preimage_emb
    (measurableEmbedding_addLeft p) f _

namespace LipschitzWith

variable {u : Rn n → ℝ} {L : ℝ≥0}

theorem norm_gradient_le (hu : LipschitzWith L u) (z : Rn n) : ‖gradient u z‖ ≤ L := by
  rw [gradient, LinearIsometryEquiv.norm_map]
  exact norm_fderiv_le_of_lipschitz ℝ hu

theorem abs_inner_gradient_le_mul_norm (hu : LipschitzWith L u) (z w : Rn n) :
    |⟪gradient u z, w⟫| ≤ L * ‖w‖ :=
  (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (LipschitzWith.norm_gradient_le hu z) (norm_nonneg _))

theorem abs_le_add_mul_norm (hu : LipschitzWith L u) (z : Rn n) :
    |u z| ≤ |u 0| + L * ‖z‖ := by
  have := hu.dist_le_mul z 0
  rw [Real.dist_eq, dist_zero_right] at this
  have := abs_sub_abs_le_abs_sub (u z) (u 0)
  linarith

/-- The pointwise bound `|⟪∇u(z), w⟫ + a u(z)| ≤ L ‖w‖ + |a| (|u 0| + L ‖z‖)`. -/
theorem abs_inner_gradient_add_mul_le (hu : LipschitzWith L u) (a : ℝ) (z w : Rn n) :
    |⟪gradient u z, w⟫ + a * u z| ≤ L * ‖w‖ + |a| * (|u 0| + L * ‖z‖) := by
  calc |⟪gradient u z, w⟫ + a * u z| ≤ |⟪gradient u z, w⟫| + |a| * |u z| := by
        rw [← abs_mul]; exact abs_add_le _ _
    _ ≤ L * ‖w‖ + |a| * (|u 0| + L * ‖z‖) := by
        gcongr
        · exact LipschitzWith.abs_inner_gradient_le_mul_norm hu z w
        · exact LipschitzWith.abs_le_add_mul_norm hu z

/-- A translate of a Lipschitz function is Lipschitz. -/
theorem comp_const_add (hu : LipschitzWith L u) (x : Rn n) :
    LipschitzWith L (fun z => u (x + z)) :=
  LipschitzWith.of_dist_le_mul fun a b => by
    simpa [dist_add_left] using hu.dist_le_mul (x + a) (x + b)

/-- For `u` Lipschitz and `p` continuous, `(⟪∇u, p⟫ + a u)²` is integrable on bounded sets. -/
theorem integrableOn_sq_inner_gradient_add_mul (hu : LipschitzWith L u) {S : Set (Rn n)}
    (hS : MeasurableSet S) (hSb : IsBounded S) {p : Rn n → Rn n} (hp : Continuous p) (a : ℝ) :
    IntegrableOn (fun z => (⟪gradient u z, p z⟫ + a * u z) ^ 2) S := by
  obtain ⟨R, hR⟩ := hSb.exists_norm_le
  obtain ⟨P, hP⟩ :=
    (isCompact_closedBall (0 : Rn n) R).exists_bound_of_continuousOn hp.continuousOn
  refine integrableOn_of_isBounded_of_abs_le ((((measurable_gradient u).inner hp.measurable).add
    (measurable_const.mul hu.continuous.measurable)).pow_const 2).aestronglyMeasurable hS hSb
    (M := (L * P + |a| * (|u 0| + L * R)) ^ 2) fun z hz => ?_
  have hzR : ‖z‖ ≤ R := hR z hz
  have hpz : ‖p z‖ ≤ P := hP z (mem_closedBall_zero_iff.2 hzR)
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _)
    ((abs_inner_gradient_add_mul_le hu a z (p z)).trans (by gcongr)) 2

/-- For `u` Lipschitz and `p` continuous, `(⟪∇u, p⟫ - a u)²` is integrable on bounded sets. -/
theorem integrableOn_sq_inner_gradient_sub_mul (hu : LipschitzWith L u) {S : Set (Rn n)}
    (hS : MeasurableSet S) (hSb : IsBounded S) {p : Rn n → Rn n} (hp : Continuous p) (a : ℝ) :
    IntegrableOn (fun z => (⟪gradient u z, p z⟫ - a * u z) ^ 2) S :=
  (integrableOn_sq_inner_gradient_add_mul hu hS hSb hp (-a)).congr_fun
    (fun z _ => by ring) hS

/-- For `u` Lipschitz and a.e. `y`, `t ↦ u (y + t • v)` has derivative `⟪∇u(y + t v), v⟫` at
a.e. `t`. -/
theorem ae_ae_hasDerivAt_add_smul (hu : LipschitzWith L u) (v : Rn n) :
    ∀ᵐ y, ∀ᵐ t : ℝ, HasDerivAt (fun s => u (y + s • v)) ⟪gradient u (y + t • v), v⟫ t := by
  have hZ : volume {z : Rn n | ¬DifferentiableAt ℝ u z} = 0 := by
    simpa [ae_iff] using hu.ae_differentiableAt
  filter_upwards [ae_ae_add_smul_notMem hZ v] with y hy
  filter_upwards [hy] with t ht
  have hd : DifferentiableAt ℝ u (y + t • v) := by simpa using ht
  rw [inner_gradient_eq_fderiv]
  have hγ : HasDerivAt (fun s : ℝ => y + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add y
  exact hd.hasFDerivAt.comp_hasDerivAt t hγ

/-- For `u` Lipschitz and a.e. `y`, `t ↦ u (t • y)` has derivative `⟪∇u(t y), y⟫` at a.e.
`t ≠ 0`. -/
theorem ae_ae_hasDerivAt_smul (hu : LipschitzWith L u) :
    ∀ᵐ y, ∀ᵐ t : ℝ, t ≠ 0 → HasDerivAt (fun s => u (s • y)) ⟪gradient u (t • y), y⟫ t := by
  have hZ : volume {z : Rn n | ¬DifferentiableAt ℝ u z} = 0 := by
    simpa [ae_iff] using hu.ae_differentiableAt
  filter_upwards [ae_ae_smul_notMem hZ] with y hy
  filter_upwards [hy] with t ht _
  have hd : DifferentiableAt ℝ u (t • y) := by simpa using ht
  rw [inner_gradient_eq_fderiv]
  have hγ : HasDerivAt (fun s : ℝ => s • y) y t := by
    simpa using (hasDerivAt_id t).smul_const y
  exact hd.hasFDerivAt.comp_hasDerivAt t hγ

/-- *Almost invariance along segments* (the estimate (6.18) in the proof of Lemma 6.2 of the
paper). Let `w = ⟪∇u, x⟫ + a u`. If the segments
`y + [0, 1] • x`, `y ∈ E`, lie in `S`, then
`∫_E (e^a u(y + x) - u(y))² ≤ e^{2|a|} ∫_S w²`.

Proof: for a.e. `y`, `t ↦ e^{at} u(y + t x)` is absolutely continuous with a.e. derivative
`e^{at} w(y + t x)`; apply the FTC, Cauchy–Schwarz in `t`, Tonelli and translation invariance. -/
theorem setIntegral_sq_exp_mul_comp_add_sub_le (hu : LipschitzWith L u) (a : ℝ) (x : Rn n)
    {E S : Set (Rn n)} (hE : MeasurableSet E) (hEb : IsBounded E) (hS : MeasurableSet S)
    (hSb : IsBounded S) (hES : ∀ y ∈ E, ∀ t ∈ Icc (0 : ℝ) 1, y + t • x ∈ S) :
    ∫ y in E, (Real.exp a * u (y + x) - u y) ^ 2 ≤
      Real.exp (2 * |a|) * ∫ z in S, (⟪gradient u z, x⟫ + a * u z) ^ 2 := by
  set w : Rn n → ℝ := fun z => ⟪gradient u z, x⟫ + a * u z with hw
  have hwm : Measurable w :=
    ((measurable_gradient u).inner measurable_const).add
      (measurable_const.mul hu.continuous.measurable)
  obtain ⟨R, hR⟩ := hEb.exists_norm_le
  obtain ⟨RS, hRS⟩ := hSb.exists_norm_le
  have hwb : ∀ z : Rn n, ∀ r, ‖z‖ ≤ r → |w z| ≤ L * ‖x‖ + |a| * (|u 0| + L * r) :=
    fun z r hz => (LipschitzWith.abs_inner_gradient_add_mul_le hu a z x).trans (by gcongr)
  have hwS : IntegrableOn (fun z => w z ^ 2) S :=
    integrableOn_of_isBounded_of_abs_le (hwm.pow_const 2).aestronglyMeasurable hS hSb
      (M := (L * ‖x‖ + |a| * (|u 0| + L * RS)) ^ 2) fun z hz => by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hwb z RS (hRS z hz)) 2
  have hexp : ∀ t ∈ Icc (0 : ℝ) 1, Real.exp (a * t) ^ 2 ≤ Real.exp (2 * |a|) := fun t ht => by
    rw [← Real.exp_nat_mul, Real.exp_le_exp]
    push_cast
    nlinarith [mul_nonneg (sub_nonneg.2 (le_abs_self a)) ht.1,
      mul_nonneg (abs_nonneg a) (sub_nonneg.2 ht.2)]
  have hnorm : ∀ y ∈ E, ∀ t ∈ Icc (0 : ℝ) 1, ‖y + t • x‖ ≤ R + ‖x‖ := fun y hy t ht => by
    calc ‖y + t • x‖ ≤ ‖y‖ + ‖t • x‖ := norm_add_le _ _
      _ ≤ R + ‖x‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
        gcongr
        · exact hR y hy
        · exact mul_le_of_le_one_left (norm_nonneg _) ht.2
  set Mw := L * ‖x‖ + |a| * (|u 0| + L * (R + ‖x‖))
  have hFb : ∀ y ∈ E, ∀ t ∈ Icc (0 : ℝ) 1,
      (Real.exp (a * t) * w (y + t • x)) ^ 2 ≤ Real.exp (2 * |a|) * Mw ^ 2 :=
    fun y hy t ht => by
      rw [mul_pow]
      refine mul_le_mul (hexp t ht) ?_ (sq_nonneg _) (Real.exp_pos _).le
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hwb _ _ (hnorm y hy t ht)) 2
  have hFm : Measurable (Function.uncurry fun (y : Rn n) (t : ℝ) =>
      (Real.exp (a * t) * w (y + t • x)) ^ 2) := by
    change Measurable fun p : Rn n × ℝ => (Real.exp (a * p.2) * w (p.1 + p.2 • x)) ^ 2
    exact ((by fun_prop : Measurable fun p : Rn n × ℝ => Real.exp (a * p.2)).mul
      (hwm.comp (by fun_prop))).pow_const 2
  refine (setIntegral_le_of_ae_le_intervalIntegral hE hEb.measure_lt_top.ne zero_le_one hFm
    (fun _ _ => sq_nonneg _) hFb (K := Real.exp (2 * |a|) * ∫ z in S, w z ^ 2) ?_
    (fun _ => sq_nonneg _) zero_le_one ?_).trans_eq (by ring)
  · intro t ht
    simp_rw [mul_pow]
    rw [integral_const_mul]
    exact mul_le_mul (hexp t ht) (setIntegral_comp_add_le (f := fun z => w z ^ 2)
      (fun _ => sq_nonneg _) hE hS hwS (t • x) fun y hy => hES y hy t ht)
      (setIntegral_nonneg hE fun _ _ => sq_nonneg _) (Real.exp_pos _).le
  · filter_upwards [LipschitzWith.ae_ae_hasDerivAt_add_smul hu x] with y hy hyE
    have hl : LipschitzWith ‖x‖₊ (fun s : ℝ => y + s • x) :=
      LipschitzWith.of_dist_le_mul fun s t => by
        rw [dist_eq_norm, dist_eq_norm, add_sub_add_left_eq_sub, ← sub_smul, norm_smul,
          mul_comm, coe_nnnorm]
    have hAC : AbsolutelyContinuousOnInterval
        (fun s => Real.exp (a * s) * u (y + s • x)) 0 1 :=
      ((by fun_prop : ContDiff ℝ 1 fun s : ℝ => Real.exp (a * s)).contDiffOn
        |>.absolutelyContinuousOnInterval).fun_mul
        (hu.comp hl).lipschitzOnWith.absolutelyContinuousOnInterval
    have hd : ∀ᵐ t, t ∈ uIcc (0 : ℝ) 1 → HasDerivAt
        (fun s => Real.exp (a * s) * u (y + s • x)) (Real.exp (a * t) * w (y + t • x)) t := by
      filter_upwards [hy] with t ht _
      have h := (((hasDerivAt_id t).const_mul a).exp).mul ht
      convert h using 1
      simp only [hw, id, mul_one]
      ring
    have hint := hAC.intervalIntegrable_of_ae_hasDerivAt hd
    have hint2 : IntervalIntegrable (fun t => (Real.exp (a * t) * w (y + t • x)) ^ 2)
        volume 0 1 :=
      intervalIntegrable_of_abs_le zero_le_one
        (((by fun_prop : Measurable fun t : ℝ => Real.exp (a * t)).mul
          (hwm.comp (by fun_prop))).pow_const 2).aestronglyMeasurable
        (M := Real.exp (2 * |a|) * Mw ^ 2) fun t ht => by
          rw [abs_of_nonneg (sq_nonneg _)]; exact hFb y hyE t ht
    have h1 : Real.exp a * u (y + x) - u y =
        ∫ t in (0 : ℝ)..1, Real.exp (a * t) * w (y + t • x) := by
      rw [hAC.integral_eq_sub_of_ae_hasDerivAt hd]
      simp
    rw [h1]
    simpa using sq_intervalIntegral_le zero_le_one hint hint2

/-- *Almost homogeneity along rays* (the estimate (6.19) in the proof of Lemma 6.2 of the
paper). Let `v(z) = ⟪∇u(z), z⟫ - N u(z)`, with
`N ≥ -1`, and `T ≥ 1`. If the segments `[1, T] • y`, `y ∈ E`, lie in `S`, then
`∫_E (T^{-N} u(T y) - u(y))² ≤ (T - 1)² ∫_S v²`.

Proof: for a.e. `y`, `t ↦ t^{-N} u(t y)` is absolutely continuous on `[1, T]` with a.e.
derivative `t^{-N-1} v(t y)`; apply the FTC, Cauchy–Schwarz in `t`, Tonelli and the change of
variables `z = t y` (whose Jacobian `t^{-n}` is at most `1`). -/
theorem setIntegral_sq_rpow_mul_comp_smul_sub_le (hu : LipschitzWith L u) {N T : ℝ}
    (hN : -1 ≤ N) (hT : 1 ≤ T) {E S : Set (Rn n)} (hE : MeasurableSet E) (hEb : IsBounded E)
    (hS : MeasurableSet S) (hSb : IsBounded S) (hES : ∀ y ∈ E, ∀ t ∈ Icc 1 T, t • y ∈ S) :
    ∫ y in E, (T ^ (-N) * u (T • y) - u y) ^ 2 ≤
      (T - 1) ^ 2 * ∫ z in S, (⟪gradient u z, z⟫ - N * u z) ^ 2 := by
  set v : Rn n → ℝ := fun z => ⟪gradient u z, z⟫ - N * u z with hv
  have hvm : Measurable v :=
    ((measurable_gradient u).inner measurable_id).sub
      (measurable_const.mul hu.continuous.measurable)
  obtain ⟨R, hR⟩ := hEb.exists_norm_le
  obtain ⟨RS, hRS⟩ := hSb.exists_norm_le
  have hvb : ∀ z : Rn n, ∀ r, ‖z‖ ≤ r → |v z| ≤ L * r + |N| * (|u 0| + L * r) :=
    fun z r hz => by
      have := LipschitzWith.abs_inner_gradient_add_mul_le hu (-N) z z
      rw [abs_neg, neg_mul, ← sub_eq_add_neg] at this
      exact this.trans (by gcongr)
  have hvS : IntegrableOn (fun z => v z ^ 2) S :=
    integrableOn_of_isBounded_of_abs_le (hvm.pow_const 2).aestronglyMeasurable hS hSb
      (M := (L * RS + |N| * (|u 0| + L * RS)) ^ 2) fun z hz => by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hvb z RS (hRS z hz)) 2
  have hw1 : ∀ t ∈ Icc (1 : ℝ) T, (t ^ (-N - 1)) ^ 2 ≤ 1 := fun t ht =>
    pow_le_one₀ (Real.rpow_nonneg (by linarith [ht.1]) _)
      (Real.rpow_le_one_of_one_le_of_nonpos ht.1 (by linarith))
  have hnorm : ∀ y ∈ E, ∀ t ∈ Icc (1 : ℝ) T, ‖t • y‖ ≤ T * R := fun y hy t ht => by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith [ht.1])]
    exact mul_le_mul ht.2 (hR y hy) (norm_nonneg _) (by linarith)
  set Mv := L * (T * R) + |N| * (|u 0| + L * (T * R))
  have hFb : ∀ y ∈ E, ∀ t ∈ Icc (1 : ℝ) T, (t ^ (-N - 1) * v (t • y)) ^ 2 ≤ 1 * Mv ^ 2 :=
    fun y hy t ht => by
      rw [mul_pow]
      refine mul_le_mul (hw1 t ht) ?_ (sq_nonneg _) zero_le_one
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hvb _ _ (hnorm y hy t ht)) 2
  have hFm : Measurable (Function.uncurry fun (y : Rn n) (t : ℝ) =>
      (t ^ (-N - 1) * v (t • y)) ^ 2) := by
    change Measurable fun p : Rn n × ℝ => (p.2 ^ (-N - 1) * v (p.2 • p.1)) ^ 2
    exact ((measurable_snd.pow_const _).mul (hvm.comp (by fun_prop))).pow_const 2
  refine (setIntegral_le_of_ae_le_intervalIntegral hE hEb.measure_lt_top.ne hT hFm
    (fun _ _ => sq_nonneg _) hFb (K := ∫ z in S, v z ^ 2) ?_ (fun _ => sq_nonneg _)
    (sub_nonneg.2 hT) ?_).trans_eq (by ring)
  · intro t ht
    simp_rw [mul_pow]
    rw [integral_const_mul]
    calc (t ^ (-N - 1)) ^ 2 * ∫ y in E, v (t • y) ^ 2 ≤ 1 * ∫ z in S, v z ^ 2 :=
          mul_le_mul (hw1 t ht) (setIntegral_comp_smul_le (f := fun z => v z ^ 2)
            (fun _ => sq_nonneg _) hE hS hvS ht.1 fun y hy => hES y hy t ht)
            (setIntegral_nonneg hE fun _ _ => sq_nonneg _) zero_le_one
      _ = ∫ z in S, v z ^ 2 := one_mul _
  · filter_upwards [LipschitzWith.ae_ae_hasDerivAt_smul hu] with y hy hyE
    have hl : LipschitzWith ‖y‖₊ (fun s : ℝ => s • y) :=
      LipschitzWith.of_dist_le_mul fun s t => by
        rw [dist_eq_norm, dist_eq_norm, ← sub_smul, norm_smul, mul_comm, coe_nnnorm]
    have hpow : ContDiffOn ℝ 1 (fun s : ℝ => s ^ (-N)) (uIcc 1 T) := fun s hs => by
      rw [uIcc_of_le hT] at hs
      exact (Real.contDiffAt_rpow_const_of_ne (by linarith [hs.1] : s ≠ 0)).contDiffWithinAt
    have hAC : AbsolutelyContinuousOnInterval (fun s => s ^ (-N) * u (s • y)) 1 T :=
      hpow.absolutelyContinuousOnInterval.fun_mul
        (hu.comp hl).lipschitzOnWith.absolutelyContinuousOnInterval
    have hd : ∀ᵐ t, t ∈ uIcc (1 : ℝ) T →
        HasDerivAt (fun s => s ^ (-N) * u (s • y)) (t ^ (-N - 1) * v (t • y)) t := by
      filter_upwards [hy] with t ht htI
      rw [uIcc_of_le hT] at htI
      have ht0 : t ≠ 0 := by linarith [htI.1]
      have h := (Real.hasDerivAt_rpow_const (p := -N) (Or.inl ht0)).mul (ht ht0)
      convert h using 1
      simp only [hv, real_inner_smul_right, Real.rpow_sub_one ht0]
      field_simp
      ring
    have hint := hAC.intervalIntegrable_of_ae_hasDerivAt hd
    have hint2 : IntervalIntegrable (fun t => (t ^ (-N - 1) * v (t • y)) ^ 2) volume 1 T :=
      intervalIntegrable_of_abs_le hT (((measurable_id.pow_const _).mul
          (hvm.comp (measurable_id.smul_const y))).pow_const 2).aestronglyMeasurable
        (M := 1 * Mv ^ 2) fun t ht => by
          rw [abs_of_nonneg (sq_nonneg _)]; exact hFb y hyE t ht
    have h1 : T ^ (-N) * u (T • y) - u y = ∫ t in (1 : ℝ)..T, t ^ (-N - 1) * v (t • y) := by
      rw [hAC.integral_eq_sub_of_ae_hasDerivAt hd]
      simp
    rw [h1]
    exact sq_intervalIntegral_le hT hint hint2

end LipschitzWith

end InnerVariational
