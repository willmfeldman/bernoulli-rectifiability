/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Sperner.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Polarization (two-point rearrangement) with respect to hyperplanes through the origin

For a unit vector `a`, let `σ_a` be the reflection in the hyperplane `a^⊥`. The polarization of
`f : ℝⁿ → ℝ` is
`P_a f(x) = max (f x) (f (σ_a x))` if `⟪x, a⟫ ≥ 0`, and `min (f x) (f (σ_a x))` otherwise.

On each pair `{x, σ_a x}` the two values of `P_a f` are those of `f`, possibly swapped. Hence
`P_a` preserves every Gaussian integral of the form `∫ Φ ∘ f dγ`, the Gaussian measure of
`{f > 0}`, the Lipschitz constant, homogeneity and sign, and (by the *local-minimum trick*)
the Dirichlet energy. It increases `J_e(f) = ∫ f ⟪x, e⟫ dγ` when `⟪a, e⟫ ≥ 0`.
-/

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace Sperner

variable {n : ℕ}

/-- The reflection in the hyperplane `a^⊥`. -/
def reflect (a : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
  (ℝ ∙ a)ᗮ.reflection

section Reflect

variable {a : EuclideanSpace ℝ (Fin n)}

lemma reflect_apply (ha : ‖a‖ = 1) (x : EuclideanSpace ℝ (Fin n)) :
    reflect a x = x - (2 * ⟪x, a⟫) • a := by
  rw [reflect, Submodule.reflection_orthogonal_apply, Submodule.reflection_singleton_apply]
  simp only [ha, RCLike.ofReal_real_eq_id, id, one_pow, div_one, real_inner_comm a x]
  module

@[simp] lemma reflect_reflect (x : EuclideanSpace ℝ (Fin n)) : reflect a (reflect a x) = x :=
  Submodule.reflection_reflection _ x

lemma inner_reflect_left (ha : ‖a‖ = 1) (x : EuclideanSpace ℝ (Fin n)) :
    ⟪reflect a x, a⟫ = -⟪x, a⟫ := by
  rw [reflect_apply ha, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, ha]
  ring

lemma reflect_eq_self_of_inner_eq_zero (ha : ‖a‖ = 1) {x : EuclideanSpace ℝ (Fin n)}
    (hx : ⟪x, a⟫ = 0) : reflect a x = x := by
  rw [reflect_apply ha, hx]; simp

lemma inner_reflect_sub (ha : ‖a‖ = 1) (x e : EuclideanSpace ℝ (Fin n)) :
    ⟪x, e⟫ - ⟪reflect a x, e⟫ = 2 * ⟪x, a⟫ * ⟪a, e⟫ := by
  rw [reflect_apply ha, inner_sub_left, real_inner_smul_left]; ring

@[simp] lemma norm_reflect (x : EuclideanSpace ℝ (Fin n)) : ‖reflect a x‖ = ‖x‖ :=
  (reflect a).norm_map x

@[simp] lemma gaussWeight_reflect (x : EuclideanSpace ℝ (Fin n)) :
    gaussWeight (reflect a x) = gaussWeight x := by
  simp [gaussWeight]

lemma measurePreserving_reflect :
    MeasurePreserving (reflect a) (gaussMeasure n) (gaussMeasure n) := by
  refine ⟨(reflect a).continuous.measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply (reflect a).continuous.measurable hs, gaussMeasure,
    withDensity_apply _ (hs.preimage (reflect a).continuous.measurable), withDensity_apply _ hs]
  have := ((reflect a).measurePreserving).setLIntegral_comp_preimage hs
    (f := fun y => ENNReal.ofReal (gaussWeight y))
    (continuous_gaussWeight.measurable.ennreal_ofReal)
  simpa using this

lemma integral_comp_reflect (F : EuclideanSpace ℝ (Fin n) → ℝ) :
    ∫ x, F (reflect a x) ∂gaussMeasure n = ∫ x, F x ∂gaussMeasure n :=
  measurePreserving_reflect.integral_comp (reflect a).toHomeomorph.measurableEmbedding F

lemma lintegral_comp_reflect (F : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) :
    ∫⁻ x, F (reflect a x) ∂gaussMeasure n = ∫⁻ x, F x ∂gaussMeasure n :=
  measurePreserving_reflect.lintegral_comp_emb (reflect a).toHomeomorph.measurableEmbedding F

lemma ae_comp_reflect {p : EuclideanSpace ℝ (Fin n) → Prop} (h : ∀ᵐ x ∂gaussMeasure n, p x) :
    ∀ᵐ x ∂gaussMeasure n, p (reflect a x) :=
  measurePreserving_reflect.quasiMeasurePreserving.ae h

end Reflect

lemma dist_reflect_le {a : EuclideanSpace ℝ (Fin n)} (ha : ‖a‖ = 1)
    {x y : EuclideanSpace ℝ (Fin n)} (h : ⟪x, a⟫ * ⟪y, a⟫ ≤ 0) :
    dist x (reflect a y) ≤ dist x y := by
  rw [dist_eq_norm, dist_eq_norm, ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _),
    reflect_apply ha, show x - (y - (2 * ⟪y, a⟫) • a) = (x - y) + (2 * ⟪y, a⟫) • a by abel,
    norm_add_sq_real, norm_smul, real_inner_smul_right, inner_sub_left, ha, Real.norm_eq_abs]
  nlinarith [sq_abs (2 * ⟪y, a⟫), real_inner_self_eq_norm_sq a]

/-- Polarization of `f` with respect to the hyperplane `a^⊥`, favouring `{⟪x, a⟫ ≥ 0}`. -/
def polarize (a : EuclideanSpace ℝ (Fin n)) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  if 0 ≤ ⟪x, a⟫ then max (f x) (f (reflect a x)) else min (f x) (f (reflect a x))

section Polarize

variable {a : EuclideanSpace ℝ (Fin n)} {f : EuclideanSpace ℝ (Fin n) → ℝ}

lemma polarize_of_nonneg {x : EuclideanSpace ℝ (Fin n)} (hx : 0 ≤ ⟪x, a⟫) :
    polarize a f x = max (f x) (f (reflect a x)) := if_pos hx

lemma polarize_of_neg {x : EuclideanSpace ℝ (Fin n)} (hx : ⟪x, a⟫ < 0) :
    polarize a f x = min (f x) (f (reflect a x)) := if_neg (not_le.2 hx)

variable (ha : ‖a‖ = 1)
include ha

/-- On each pair `{x, σx}`, `P_a f` takes the values of `f`, possibly swapped. -/
lemma polarize_pair (x : EuclideanSpace ℝ (Fin n)) :
    (polarize a f x = f x ∧ polarize a f (reflect a x) = f (reflect a x)) ∨
      (polarize a f x = f (reflect a x) ∧ polarize a f (reflect a x) = f x) := by
  rcases lt_trichotomy ⟪x, a⟫ 0 with h | h | h
  · have h' : 0 ≤ ⟪reflect a x, a⟫ := by rw [inner_reflect_left ha]; linarith
    rw [polarize_of_neg h, polarize_of_nonneg h', reflect_reflect]
    rcases le_total (f x) (f (reflect a x)) with hle | hle
    · exact Or.inl ⟨min_eq_left hle, max_eq_left hle⟩
    · exact Or.inr ⟨min_eq_right hle, max_eq_right hle⟩
  · have hσ := reflect_eq_self_of_inner_eq_zero ha h
    have hP : polarize a f x = f x := by rw [polarize_of_nonneg h.ge, hσ, max_self]
    left; rw [hσ]; exact ⟨hP, hP⟩
  · have h' : ⟪reflect a x, a⟫ < 0 := by rw [inner_reflect_left ha]; linarith
    rw [polarize_of_nonneg h.le, polarize_of_neg h', reflect_reflect]
    rcases le_total (f x) (f (reflect a x)) with hle | hle
    · exact Or.inr ⟨max_eq_right hle, min_eq_right hle⟩
    · exact Or.inl ⟨max_eq_left hle, min_eq_left hle⟩

lemma comp_polarize_add {β : Type*} [AddCommMagma β] (Φ : ℝ → β) (x : EuclideanSpace ℝ (Fin n)) :
    Φ (polarize a f x) + Φ (polarize a f (reflect a x)) = Φ (f x) + Φ (f (reflect a x)) := by
  rcases polarize_pair ha (f := f) x with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, add_comm]

lemma continuous_polarize (hf : Continuous f) : Continuous (polarize a f) := by
  have hσ : Continuous (reflect a) := (reflect a).continuous
  refine Continuous.if_le (hf.max (hf.comp hσ)) (hf.min (hf.comp hσ)) continuous_const
    (continuous_id.inner continuous_const) fun x hx => ?_
  rw [reflect_eq_self_of_inner_eq_zero ha hx.symm, max_self, min_self]

lemma lintegral_comp_polarize (hf : Continuous f) {Φ : ℝ → ℝ≥0∞} (hΦ : Measurable Φ) :
    ∫⁻ x, Φ (polarize a f x) ∂gaussMeasure n = ∫⁻ x, Φ (f x) ∂gaussMeasure n := by
  have hPm : Measurable fun x => Φ (polarize a f x) :=
    hΦ.comp (continuous_polarize ha hf).measurable
  have hfm : Measurable fun x => Φ (f x) := hΦ.comp hf.measurable
  have key : ∫⁻ x, Φ (polarize a f x) ∂gaussMeasure n +
      ∫⁻ x, Φ (polarize a f (reflect a x)) ∂gaussMeasure n =
      ∫⁻ x, Φ (f x) ∂gaussMeasure n + ∫⁻ x, Φ (f (reflect a x)) ∂gaussMeasure n := by
    rw [← lintegral_add_left hPm, ← lintegral_add_left hfm]
    congr 1; funext x; exact comp_polarize_add ha Φ x
  rw [lintegral_comp_reflect (fun x => Φ (polarize a f x)),
    lintegral_comp_reflect (fun x => Φ (f x)), ← two_mul, ← two_mul] at key
  exact (ENNReal.mul_right_inj two_ne_zero ENNReal.ofNat_ne_top).1 key

lemma gaussMeasure_polarize_pos (hf : Continuous f) :
    gaussMeasure n {x | 0 < polarize a f x} = gaussMeasure n {x | 0 < f x} := by
  have h : ∀ g : EuclideanSpace ℝ (Fin n) → ℝ, Continuous g →
      gaussMeasure n {x | 0 < g x} = ∫⁻ x, (Ioi (0 : ℝ)).indicator 1 (g x) ∂gaussMeasure n := by
    intro g hg
    rw [← lintegral_indicator_one (measurableSet_lt continuous_const.measurable hg.measurable)]
    refine lintegral_congr fun x => ?_
    by_cases hx : 0 < g x <;> simp [indicator, hx]
  rw [h _ (continuous_polarize ha hf), h _ hf]
  exact lintegral_comp_polarize ha hf (measurable_const.indicator measurableSet_Ioi)

lemma gaussL2_polarize (hf : Continuous f) : gaussL2 (polarize a f) = gaussL2 f := by
  unfold gaussL2
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => sq_nonneg _)
      ((continuous_polarize ha hf).pow 2).aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => sq_nonneg _)
      (hf.pow 2).aestronglyMeasurable]
  congr 1
  exact lintegral_comp_polarize ha hf (Φ := fun t => ENNReal.ofReal (t ^ 2))
    (by fun_prop)

lemma lipschitzWith_polarize {L : ℝ≥0} (hf : LipschitzWith L f) :
    LipschitzWith L (polarize a f) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have hσ : dist (reflect a x) (reflect a y) = dist x y := (reflect a).dist_map x y
  have h1 := hf.dist_le_mul x y
  have h2 := hf.dist_le_mul (reflect a x) (reflect a y)
  rw [hσ] at h2
  rw [Real.dist_eq] at h1 h2 ⊢
  -- cross terms, used when `x` and `y` lie on opposite sides
  have cross : ⟪x, a⟫ * ⟪y, a⟫ ≤ 0 →
      |f x - f (reflect a y)| ≤ L * dist x y ∧ |f (reflect a x) - f y| ≤ L * dist x y := by
    intro h
    have h3 := hf.dist_le_mul x (reflect a y)
    have h4 := hf.dist_le_mul (reflect a x) y
    rw [Real.dist_eq] at h3 h4
    have d3 := dist_reflect_le ha h
    have d4 : dist (reflect a x) y ≤ dist x y := by
      rw [dist_comm, dist_comm x y]; exact dist_reflect_le ha (by linarith [mul_comm ⟪x, a⟫ ⟪y, a⟫])
    exact ⟨h3.trans (by gcongr), h4.trans (by gcongr)⟩
  by_cases hx : 0 ≤ ⟪x, a⟫ <;> by_cases hy : 0 ≤ ⟪y, a⟫
  · rw [polarize_of_nonneg hx, polarize_of_nonneg hy]
    exact (abs_max_sub_max_le_max _ _ _ _).trans (max_le h1 h2)
  · push Not at hy
    rw [polarize_of_nonneg hx, polarize_of_neg hy]
    obtain ⟨h3, h4⟩ := cross (mul_nonpos_of_nonneg_of_nonpos hx hy.le)
    rw [abs_sub_le_iff] at h1 h2 h3 h4 ⊢
    constructor
    · rcases le_total (f x) (f (reflect a x)) with h | h <;>
        rcases le_total (f y) (f (reflect a y)) with h' | h' <;>
        simp only [max_eq_left, max_eq_right, min_eq_left, min_eq_right, h, h'] <;> linarith
    · rcases le_total (f x) (f (reflect a x)) with h | h <;>
        rcases le_total (f y) (f (reflect a y)) with h' | h' <;>
        simp only [max_eq_left, max_eq_right, min_eq_left, min_eq_right, h, h'] <;> linarith
  · push Not at hx
    rw [polarize_of_neg hx, polarize_of_nonneg hy]
    obtain ⟨h3, h4⟩ := cross (mul_nonpos_of_nonpos_of_nonneg hx.le hy)
    rw [abs_sub_le_iff] at h1 h2 h3 h4 ⊢
    constructor
    · rcases le_total (f x) (f (reflect a x)) with h | h <;>
        rcases le_total (f y) (f (reflect a y)) with h' | h' <;>
        simp only [max_eq_left, max_eq_right, min_eq_left, min_eq_right, h, h'] <;> linarith
    · rcases le_total (f x) (f (reflect a x)) with h | h <;>
        rcases le_total (f y) (f (reflect a y)) with h' | h' <;>
        simp only [max_eq_left, max_eq_right, min_eq_left, min_eq_right, h, h'] <;> linarith
  · push Not at hx hy
    rw [polarize_of_neg hx, polarize_of_neg hy]
    exact (abs_min_sub_min_le_max _ _ _ _).trans (max_le h1 h2)

omit ha in
lemma isOneHomogeneous_polarize (hf : IsOneHomogeneous f) :
    IsOneHomogeneous (polarize a f) := by
  intro x t ht
  have hσ : reflect a (t • x) = t • reflect a x := map_smul _ t x
  have hin : ⟪t • x, a⟫ = t * ⟪x, a⟫ := real_inner_smul_left _ _ _
  by_cases hx : 0 ≤ ⟪x, a⟫
  · have htx : 0 ≤ ⟪t • x, a⟫ := by rw [hin]; positivity
    rw [polarize_of_nonneg hx, polarize_of_nonneg htx, hσ, hf x t ht, hf _ t ht,
      mul_max_of_nonneg _ _ ht.le]
  · push Not at hx
    have htx : ⟪t • x, a⟫ < 0 := by rw [hin]; exact mul_neg_of_pos_of_neg ht hx
    rw [polarize_of_neg hx, polarize_of_neg htx, hσ, hf x t ht, hf _ t ht,
      mul_min_of_nonneg _ _ ht.le]

omit ha in
lemma polarize_nonneg (hnn : ∀ x, 0 ≤ f x) (x : EuclideanSpace ℝ (Fin n)) :
    0 ≤ polarize a f x := by
  unfold polarize
  split_ifs
  · exact le_max_of_le_left (hnn x)
  · exact le_min (hnn x) (hnn _)

end Polarize

/-! ### The Dirichlet energy is preserved: the local-minimum trick -/

/-- If `u ≤ v` near `x`, `u x = v x`, and both are differentiable at `x`, then their derivatives
at `x` agree (`v - u` has a local minimum at `x`). -/
lemma fderiv_eq_of_eventually_le {u v : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x)
    (hle : ∀ᶠ y in 𝓝 x, u y ≤ v y) (heq : u x = v x) : fderiv ℝ u x = fderiv ℝ v x := by
  have hmin : IsLocalMin (fun y => v y - u y) x :=
    hle.mono fun y hy => by simp only [heq, sub_self]; linarith
  have := hmin.fderiv_eq_zero
  rw [fderiv_fun_sub hv hu, sub_eq_zero] at this
  exact this.symm

section Reflect'

variable {a : EuclideanSpace ℝ (Fin n)}

lemma hasFDerivAt_comp_reflect {h : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (hd : DifferentiableAt ℝ h (reflect a x)) :
    HasFDerivAt (h ∘ reflect a)
      ((fderiv ℝ h (reflect a x)).comp (reflect a).toLinearIsometry.toContinuousLinearMap) x :=
  hd.hasFDerivAt.comp x (reflect a).toContinuousLinearEquiv.hasFDerivAt

lemma differentiableAt_comp_reflect {h : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (hd : DifferentiableAt ℝ h (reflect a x)) :
    DifferentiableAt ℝ (h ∘ reflect a) x :=
  (hasFDerivAt_comp_reflect hd).differentiableAt

lemma norm_fderiv_comp_reflect {h : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (hd : DifferentiableAt ℝ h (reflect a x)) :
    ‖fderiv ℝ (h ∘ reflect a) x‖ = ‖fderiv ℝ h (reflect a x)‖ := by
  rw [(hasFDerivAt_comp_reflect hd).fderiv,
    ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]

lemma ae_inner_ne_zero (ha : ‖a‖ = 1) : ∀ᵐ x ∂gaussMeasure n, ⟪x, a⟫ ≠ 0 := by
  have hac : gaussMeasure n ≪ volume := withDensity_absolutelyContinuous _ _
  have hne : (ℝ ∙ a)ᗮ ≠ ⊤ := by
    intro h
    have : a ∈ (ℝ ∙ a)ᗮ := h ▸ Submodule.mem_top
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_self_eq_norm_sq, ha] at this
    norm_num at this
  have h0 := Measure.addHaar_submodule volume _ hne
  have hv : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ⟪x, a⟫ ≠ 0 := by
    rw [ae_iff]
    refine measure_mono_null (fun x hx => ?_) h0
    simp only [ne_eq, not_not, mem_setOf_eq] at hx
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_comm]
    exact hx
  exact hac.ae_le hv

end Reflect'

section PolarizeEnergy

variable {a : EuclideanSpace ℝ (Fin n)} {f : EuclideanSpace ℝ (Fin n) → ℝ}

/-- The pointwise gradient identity on a pair `{x, σx}` with `⟪x, a⟫ > 0`. -/
lemma norm_fderiv_polarize_add_of_pos (ha : ‖a‖ = 1) (hfc : Continuous f)
    {x : EuclideanSpace ℝ (Fin n)} (hx : 0 < ⟪x, a⟫)
    (hf1 : DifferentiableAt ℝ f x) (hf2 : DifferentiableAt ℝ f (reflect a x))
    (hP1 : DifferentiableAt ℝ (polarize a f) x)
    (hP2 : DifferentiableAt ℝ (polarize a f) (reflect a x)) :
    ‖fderiv ℝ (polarize a f) x‖ ^ 2 + ‖fderiv ℝ (polarize a f) (reflect a x)‖ ^ 2 =
      ‖fderiv ℝ f x‖ ^ 2 + ‖fderiv ℝ f (reflect a x)‖ ^ 2 := by
  set σ := reflect a
  set P := polarize a f
  set g := f ∘ σ
  have hg : DifferentiableAt ℝ g x := differentiableAt_comp_reflect hf2
  have hQ : DifferentiableAt ℝ (P ∘ σ) x := differentiableAt_comp_reflect hP2
  rw [← norm_fderiv_comp_reflect hf2, ← norm_fderiv_comp_reflect hP2]
  have hH : ∀ᶠ y in 𝓝 x, 0 < ⟪y, a⟫ :=
    (isOpen_lt continuous_const (continuous_id.inner continuous_const)).mem_nhds hx
  have hPmax : ∀ᶠ y in 𝓝 x, P y = max (f y) (g y) :=
    hH.mono fun y hy => polarize_of_nonneg hy.le
  have hQmin : ∀ᶠ y in 𝓝 x, (P ∘ σ) y = min (f y) (g y) := hH.mono fun y hy => by
    have : ⟪σ y, a⟫ < 0 := by rw [inner_reflect_left ha]; linarith
    simp only [Function.comp, P, polarize_of_neg this, σ, reflect_reflect, g]
    exact min_comm _ _
  have hgc : Continuous g := hfc.comp (reflect a).continuous
  rcases lt_trichotomy (f x) (g x) with h | h | h
  · -- `P = g`, `P ∘ σ = f` near `x`
    have h' : ∀ᶠ y in 𝓝 x, f y < g y :=
      (isOpen_lt hfc hgc).mem_nhds h
    have e1 : P =ᶠ[𝓝 x] g := (hPmax.and h').mono fun y hy => by rw [hy.1, max_eq_right hy.2.le]
    have e2 : P ∘ σ =ᶠ[𝓝 x] f :=
      (hQmin.and h').mono fun y hy => by rw [hy.1, min_eq_left hy.2.le]
    rw [e1.fderiv_eq, e2.fderiv_eq]; ring
  · -- the local-minimum trick
    have d1 : fderiv ℝ P x = fderiv ℝ f x :=
      (fderiv_eq_of_eventually_le hf1 hP1
        (hPmax.mono fun y hy => by rw [hy]; exact le_max_left _ _)
        (by rw [hPmax.self_of_nhds, h, max_self])).symm
    have d2 : fderiv ℝ (P ∘ σ) x = fderiv ℝ f x :=
      fderiv_eq_of_eventually_le hQ hf1
        (hQmin.mono fun y hy => by rw [hy]; exact min_le_left _ _)
        (by rw [hQmin.self_of_nhds, h, min_self])
    have d3 : fderiv ℝ g x = fderiv ℝ f x :=
      (fderiv_eq_of_eventually_le hg hP1
        (hPmax.mono fun y hy => by rw [hy]; exact le_max_right _ _)
        (by rw [hPmax.self_of_nhds, h, max_self])).trans d1
    rw [d1, d2, d3]
  · have h' : ∀ᶠ y in 𝓝 x, g y < f y :=
      (isOpen_lt hgc hfc).mem_nhds h
    have e1 : P =ᶠ[𝓝 x] f := (hPmax.and h').mono fun y hy => by rw [hy.1, max_eq_left hy.2.le]
    have e2 : P ∘ σ =ᶠ[𝓝 x] g :=
      (hQmin.and h').mono fun y hy => by rw [hy.1, min_eq_right hy.2.le]
    rw [e1.fderiv_eq, e2.fderiv_eq]

lemma integral_eq_of_ae_add_reflect {a : EuclideanSpace ℝ (Fin n)}
    {G H : EuclideanSpace ℝ (Fin n) → ℝ} (hG : Integrable G (gaussMeasure n))
    (hH : Integrable H (gaussMeasure n))
    (h : ∀ᵐ x ∂gaussMeasure n, G x + G (reflect a x) = H x + H (reflect a x)) :
    ∫ x, G x ∂gaussMeasure n = ∫ x, H x ∂gaussMeasure n := by
  have hemb := (reflect a).toHomeomorph.measurableEmbedding
  have hGσ : Integrable (fun x => G (reflect a x)) (gaussMeasure n) :=
    (measurePreserving_reflect.integrable_comp_emb hemb).2 hG
  have hHσ : Integrable (fun x => H (reflect a x)) (gaussMeasure n) :=
    (measurePreserving_reflect.integrable_comp_emb hemb).2 hH
  have := integral_congr_ae h
  rw [integral_add hG hGσ, integral_add hH hHσ, integral_comp_reflect G,
    integral_comp_reflect H] at this
  linarith

lemma integrable_norm_fderiv_sq {w : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ≥0}
    (hw : LipschitzWith L w) :
    Integrable (fun x => ‖fderiv ℝ w x‖ ^ 2) (gaussMeasure n) :=
  (integrable_const ((L : ℝ) ^ 2)).mono'
    ((measurable_fderiv ℝ w).norm.pow_const 2).aestronglyMeasurable
    (ae_of_all _ fun x => by
      rw [Real.norm_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_le_of_lipschitz ℝ hw) 2)

/-- **Polarization preserves the Dirichlet energy.** -/
theorem dirichletEnergy_polarize (ha : ‖a‖ = 1) {L : ℝ≥0} (hf : LipschitzWith L f) :
    dirichletEnergy (polarize a f) = dirichletEnergy f := by
  have hP := lipschitzWith_polarize ha hf
  have hac : gaussMeasure n ≪ volume := withDensity_absolutelyContinuous _ _
  have d1 := hac.ae_le hf.ae_differentiableAt
  have d2 := hac.ae_le hP.ae_differentiableAt
  unfold dirichletEnergy
  refine integral_eq_of_ae_add_reflect (a := a) (integrable_norm_fderiv_sq hP)
    (integrable_norm_fderiv_sq hf) ?_
  filter_upwards [d1, d2, ae_comp_reflect (a := a) d1, ae_comp_reflect (a := a) d2,
    ae_inner_ne_zero ha] with x h1 h2 h3 h4 h5
  rcases h5.lt_or_gt with hx | hx
  · have hx' : 0 < ⟪reflect a x, a⟫ := by rw [inner_reflect_left ha]; linarith
    have := norm_fderiv_polarize_add_of_pos ha hf.continuous hx' h3
      (by rwa [reflect_reflect]) h4 (by rwa [reflect_reflect])
    rw [reflect_reflect] at this
    linarith
  · exact norm_fderiv_polarize_add_of_pos ha hf.continuous hx h1 h3 h2 h4

end PolarizeEnergy

/-! ### Polarization increases the first moment -/

section Moment

variable {a e : EuclideanSpace ℝ (Fin n)} {f : EuclideanSpace ℝ (Fin n) → ℝ}

lemma polarize_sub_mul_inner_nonneg (x : EuclideanSpace ℝ (Fin n)) :
    0 ≤ (polarize a f x - f x) * ⟪x, a⟫ := by
  by_cases hx : 0 ≤ ⟪x, a⟫
  · rw [polarize_of_nonneg hx]
    exact mul_nonneg (sub_nonneg.2 (le_max_left _ _)) hx
  · push Not at hx
    rw [polarize_of_neg hx]
    exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 (min_le_left _ _)) hx.le

lemma abs_le_of_lipschitzWith_of_map_zero {w : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ≥0}
    (hw : LipschitzWith L w) (h0 : w 0 = 0) (x : EuclideanSpace ℝ (Fin n)) :
    |w x| ≤ L * ‖x‖ := by
  have := hw.dist_le_mul x 0
  rwa [Real.dist_eq, h0, sub_zero, dist_zero_right] at this

lemma integrable_mul_inner {w : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ≥0}
    (hw : LipschitzWith L w) (h0 : w 0 = 0) (e : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun x => w x * ⟪x, e⟫) (gaussMeasure n) :=
  ((integrable_norm_pow_gaussMeasure (n := n) 2).const_mul (L * ‖e‖)).mono'
    (hw.continuous.mul (continuous_id.inner continuous_const)).aestronglyMeasurable
    (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_mul]
      calc |w x| * |⟪x, e⟫| ≤ (L * ‖x‖) * (‖x‖ * ‖e‖) :=
            mul_le_mul (abs_le_of_lipschitzWith_of_map_zero hw h0 x)
              (abs_real_inner_le_norm x e) (abs_nonneg _) (by positivity)
        _ = L * ‖e‖ * ‖x‖ ^ 2 := by ring)

lemma polarize_map_zero (h0 : f 0 = 0) : polarize a f 0 = 0 := by
  rw [polarize_of_nonneg (by simp), map_zero, h0, max_self]

variable (ha : ‖a‖ = 1)
include ha

/-- The pair defect `T(x)` of the first moment, `T ≥ 0` when `⟪a, e⟫ ≥ 0`. -/
lemma polarize_moment_pair (x : EuclideanSpace ℝ (Fin n)) :
    (polarize a f x - f x) * ⟪x, e⟫ +
        (polarize a f (reflect a x) - f (reflect a x)) * ⟪reflect a x, e⟫ =
      2 * ((polarize a f x - f x) * ⟪x, a⟫) * ⟪a, e⟫ := by
  have hsum := comp_polarize_add ha (f := f) id x
  simp only [id] at hsum
  have : polarize a f (reflect a x) - f (reflect a x) = -(polarize a f x - f x) := by linarith
  rw [this]
  linear_combination (polarize a f x - f x) * inner_reflect_sub ha x e

/-- **Polarization increases `J_e`** when `⟪a, e⟫ ≥ 0`. -/
theorem gaussMoment_le_polarize (hae : 0 ≤ ⟪a, e⟫) {L : ℝ≥0} (hf : LipschitzWith L f)
    (h0 : f 0 = 0) : gaussMoment e f ≤ gaussMoment e (polarize a f) := by
  have hP := lipschitzWith_polarize ha hf
  have hP0 := polarize_map_zero (a := a) h0
  have i1 := integrable_mul_inner hf h0 e
  have i2 := integrable_mul_inner hP hP0 e
  have hd : Integrable (fun x => (polarize a f x - f x) * ⟪x, e⟫) (gaussMeasure n) :=
    (i2.sub i1).congr (ae_of_all _ fun x => by simp only [Pi.sub_apply]; ring)
  have hemb := (reflect a).toHomeomorph.measurableEmbedding
  have hdσ : Integrable (fun x => (polarize a f (reflect a x) - f (reflect a x)) *
      ⟪reflect a x, e⟫) (gaussMeasure n) :=
    (measurePreserving_reflect.integrable_comp_emb hemb
      (g := fun y => (polarize a f y - f y) * ⟪y, e⟫)).2 hd
  have key : 0 ≤ ∫ x, ((polarize a f x - f x) * ⟪x, e⟫ +
      (polarize a f (reflect a x) - f (reflect a x)) * ⟪reflect a x, e⟫) ∂gaussMeasure n := by
    refine integral_nonneg fun x => ?_
    rw [polarize_moment_pair ha x]
    have := polarize_sub_mul_inner_nonneg (a := a) (f := f) x
    exact mul_nonneg (mul_nonneg zero_le_two this) hae
  have hc : ∫ x, (polarize a f (reflect a x) - f (reflect a x)) * ⟪reflect a x, e⟫
      ∂gaussMeasure n = ∫ x, (polarize a f x - f x) * ⟪x, e⟫ ∂gaussMeasure n :=
    integral_comp_reflect (fun y => (polarize a f y - f y) * ⟪y, e⟫)
  rw [integral_add hd hdσ, hc] at key
  have : ∫ x, (polarize a f x - f x) * ⟪x, e⟫ ∂gaussMeasure n =
      gaussMoment e (polarize a f) - gaussMoment e f := by
    unfold gaussMoment
    rw [← integral_sub i2 i1]
    congr 1; funext x; ring
  unfold gaussMoment at this ⊢
  linarith

/-- **Rigidity**: if polarization does not increase `J_e` (with `⟪a, e⟫ > 0`), then `f` already
favours the side of `a`: `f (σ x) ≤ f x` whenever `⟪x, a⟫ > 0`. -/
theorem le_of_gaussMoment_polarize_eq (hae : 0 < ⟪a, e⟫) {L : ℝ≥0} (hf : LipschitzWith L f)
    (h0 : f 0 = 0) (heq : gaussMoment e (polarize a f) = gaussMoment e f)
    {x : EuclideanSpace ℝ (Fin n)} (hx : 0 < ⟪x, a⟫) : f (reflect a x) ≤ f x := by
  have hP := lipschitzWith_polarize ha hf
  have hP0 := polarize_map_zero (a := a) h0
  have i1 := integrable_mul_inner hf h0 e
  have i2 := integrable_mul_inner hP hP0 e
  set T : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun y => 2 * ((polarize a f y - f y) * ⟪y, a⟫) * ⟪a, e⟫ with hT
  have hT0 : 0 ≤ T := fun y => by
    have := polarize_sub_mul_inner_nonneg (a := a) (f := f) y
    exact mul_nonneg (mul_nonneg zero_le_two this) hae.le
  have hTc : Continuous T := by
    have h1 := continuous_polarize ha hf.continuous
    have h2 := hf.continuous
    simp only [hT]; fun_prop
  have hemb := (reflect a).toHomeomorph.measurableEmbedding
  have hd : Integrable (fun y => (polarize a f y - f y) * ⟪y, e⟫) (gaussMeasure n) :=
    (i2.sub i1).congr (ae_of_all _ fun x => by simp only [Pi.sub_apply]; ring)
  have hdσ : Integrable (fun y => (polarize a f (reflect a y) - f (reflect a y)) *
      ⟪reflect a y, e⟫) (gaussMeasure n) :=
    (measurePreserving_reflect.integrable_comp_emb hemb
      (g := fun y => (polarize a f y - f y) * ⟪y, e⟫)).2 hd
  have hTint : Integrable T (gaussMeasure n) := by
    refine (hd.add hdσ).congr (ae_of_all _ fun y => ?_)
    simp only [hT, Pi.add_apply]; exact polarize_moment_pair ha y
  have hT_eq : ∫ y, T y ∂gaussMeasure n = 0 := by
    have : ∫ y, T y ∂gaussMeasure n = ∫ y, ((polarize a f y - f y) * ⟪y, e⟫ +
        (polarize a f (reflect a y) - f (reflect a y)) * ⟪reflect a y, e⟫) ∂gaussMeasure n :=
      integral_congr_ae (ae_of_all _ fun y => (polarize_moment_pair ha y).symm)
    have hc : ∫ x, (polarize a f (reflect a x) - f (reflect a x)) * ⟪reflect a x, e⟫
        ∂gaussMeasure n = ∫ x, (polarize a f x - f x) * ⟪x, e⟫ ∂gaussMeasure n :=
      integral_comp_reflect (fun y => (polarize a f y - f y) * ⟪y, e⟫)
    rw [this, integral_add hd hdσ, hc]
    have h2 : ∫ y, (polarize a f y - f y) * ⟪y, e⟫ ∂gaussMeasure n =
        gaussMoment e (polarize a f) - gaussMoment e f := by
      unfold gaussMoment
      rw [← integral_sub i2 i1]
      congr 1; funext y; ring
    rw [h2, heq]; ring
  -- `T ≡ 0` since it is continuous, nonnegative, with zero integral
  have hTx : T x = 0 := by
    by_contra hne
    have hpos : 0 < T x := lt_of_le_of_ne (hT0 x) (Ne.symm hne)
    have := (integral_pos_iff_support_of_nonneg hT0 hTint).2
      (lt_of_lt_of_le (gaussMeasure_pos_of_isOpen (isOpen_lt continuous_const hTc) ⟨x, hpos⟩)
        (measure_mono fun y (hy : 0 < T y) => hy.ne'))
    linarith
  simp only [hT] at hTx
  have h1 : polarize a f x - f x = 0 := by
    rcases mul_eq_zero.1 hTx with h | h
    · rcases mul_eq_zero.1 h with h | h
      · norm_num at h
      · rcases mul_eq_zero.1 h with h | h
        · exact h
        · exact absurd h hx.ne'
    · exact absurd h hae.ne'
  rw [polarize_of_nonneg hx.le, sub_eq_zero] at h1
  rw [← h1]; exact le_max_right _ _

/-- Polarization preserves the admissible class. -/
theorem AdmissibleClass.polarize {L : ℝ≥0} {D M : ℝ} {m : ℝ≥0∞}
    (h : AdmissibleClass L D M m f) : AdmissibleClass L D M m (polarize a f) := by
  obtain ⟨hL, hnn, hhom, hM, hD, hm⟩ := h
  refine ⟨lipschitzWith_polarize ha hL, polarize_nonneg hnn, isOneHomogeneous_polarize hhom,
    ?_, ?_, ?_⟩
  · rw [gaussL2_polarize ha hL.continuous, hM]
  · rw [dirichletEnergy_polarize ha hL]; exact hD
  · rw [gaussMeasure_polarize_pos ha hL.continuous]; exact hm

end Moment

end Sperner
