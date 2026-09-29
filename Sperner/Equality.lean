/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Sperner.Equality.Rigidity
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Calculus.Rademacher

/-!
# The equality case of Sperner's inequality

If `v ≥ 0` is Lipschitz, one-homogeneous, harmonic on its (connected) positivity set `U`, and
`U` has exactly half of the Gaussian measure, then `U` is an open half-space `{⟪x, e⟫ > 0}` and
`v = a ⟪x, e⟫` on `U` with `a > 0`.

## Proof

By the energy inequality and the Faber–Krahn inequality, `v` is a minimizer of
`Q(f) = ∫ |Df|² dγ - ∫ f² dγ` (`Sperner/Equality/Minimizer.lean`).
1. Choose a unit vector `e` maximizing `e ↦ J_e(v) = ∫ v ⟪x, e⟫ dγ` (a linear function of `e`).
2. For every unit `a` with `⟪a, e⟫ > 0`, rigidity of polarization
   (`Sperner/Equality/Rigidity.lean`) gives `v ∘ σ_a ≤ v` or `v ≤ v ∘ σ_a` on `{⟪x, a⟫ > 0}`;
   in the second case `P_a v = v ∘ σ_a` and `J_e(v ∘ σ_a) = J_{σ_a e}(v) ≤ J_e(v) ≤ J_e(P_a v)`,
   so the rigidity of `J_e` under polarization gives the first case anyway. Hence `v` is
   cap-symmetric about `e`.
3. Cap symmetry and `2 γ(U) = γ(ℝⁿ)` give `U ⊆ {⟪x, e⟫ > 0}`; if the inclusion were strict, `U`
   would lie in a cone `{⟪x, e⟫ ≥ s |x|}`, `s > 0`, and the strict Gaussian Poincaré inequality
   would contradict `Q(v) = 0`. So `U` is the half-space.
4. With `ℓ = ⟪x, e⟫⁺`: `Q(ℓ) = 0` and `B(v, ℓ) = 0`, so `Q(v - a ℓ) = 0` for every `a`. Splitting
   `f = v - a ℓ` into `f⁺` and `f⁻` (supported in the half-space), `Q(f⁺) = Q(f⁻) = 0`, and the
   strict Faber–Krahn inequality forbids `f⁺` and `f⁻` from both being nonzero. So `v ≤ a ℓ` or
   `v ≥ a ℓ` for every `a ≥ 0`; comparing at `e` gives `v = v(e) ℓ`.
-/

open MeasureTheory Set Filter Topology InnerProductSpace
open scoped NNReal ENNReal RealInnerProductSpace Laplacian

@[expose] public noncomputable section

namespace Sperner

variable {n : ℕ}

/-! ### Positive and negative parts -/

section Parts

variable {f : EuclideanSpace ℝ (Fin n) → ℝ}

lemma norm_fderiv_sq_eq_posPart_add_negPart {x : EuclideanSpace ℝ (Fin n)} (hfc : Continuous f)
    (hp : DifferentiableAt ℝ (fun y => max (f y) 0) x)
    (hm : DifferentiableAt ℝ (fun y => max (-f y) 0) x) :
    ‖fderiv ℝ f x‖ ^ 2 =
      ‖fderiv ℝ (fun y => max (f y) 0) x‖ ^ 2 + ‖fderiv ℝ (fun y => max (-f y) 0) x‖ ^ 2 := by
  rcases lt_trichotomy (f x) 0 with h | h | h
  · have e1 : (fun y => max (f y) 0) =ᶠ[𝓝 x] fun _ => 0 :=
      Filter.eventually_of_mem ((isOpen_lt hfc continuous_const).mem_nhds h)
        fun y (hy : f y < 0) => max_eq_right hy.le
    have e2 : (fun y => max (-f y) 0) =ᶠ[𝓝 x] fun y => -f y :=
      Filter.eventually_of_mem ((isOpen_lt hfc continuous_const).mem_nhds h) fun y (hy : f y < 0) =>
        max_eq_left (by linarith)
    rw [e1.fderiv_eq, e2.fderiv_eq, fderiv_const_apply, fderiv_fun_neg, norm_neg, norm_zero]
    ring
  · have h1 : fderiv ℝ (fun y => max (f y) 0) x = 0 :=
      fderiv_eq_zero_of_nonneg_of_eq_zero (fun y => le_max_right _ _) (by simp [h])
    have h2 : fderiv ℝ (fun y => max (-f y) 0) x = 0 :=
      fderiv_eq_zero_of_nonneg_of_eq_zero (fun y => le_max_right _ _) (by simp [h])
    have hsplit : f = fun y => max (f y) 0 - max (-f y) 0 := by
      funext y
      rcases le_total (f y) 0 with hy | hy
      · rw [max_eq_right hy, max_eq_left (by linarith)]; ring
      · rw [max_eq_left hy, max_eq_right (by linarith)]; ring
    have h3 : fderiv ℝ f x = 0 := by
      rw [hsplit, fderiv_fun_sub hp hm, h1, h2, sub_zero]
    rw [h1, h2, h3]; simp
  · have e1 : (fun y => max (f y) 0) =ᶠ[𝓝 x] f :=
      Filter.eventually_of_mem ((isOpen_lt continuous_const hfc).mem_nhds h)
        fun y (hy : 0 < f y) => max_eq_left hy.le
    have e2 : (fun y => max (-f y) 0) =ᶠ[𝓝 x] fun _ => 0 :=
      Filter.eventually_of_mem ((isOpen_lt continuous_const hfc).mem_nhds h) fun y (hy : 0 < f y) =>
        max_eq_right (by linarith)
    rw [e1.fderiv_eq, e2.fderiv_eq, fderiv_const_apply, norm_zero]
    ring

lemma dirichletEnergy_eq_posPart_add_negPart {L : ℝ≥0} (hf : LipschitzWith L f) :
    dirichletEnergy f =
      dirichletEnergy (fun y => max (f y) 0) + dirichletEnergy (fun y => max (-f y) 0) := by
  have hp : LipschitzWith L fun y => max (f y) 0 := hf.max_const 0
  have hm : LipschitzWith L fun y => max (-f y) 0 := hf.neg.max_const 0
  have hac : gaussMeasure n ≪ volume := withDensity_absolutelyContinuous _ _
  unfold dirichletEnergy
  rw [← integral_add (integrable_norm_fderiv_sq hp) (integrable_norm_fderiv_sq hm)]
  refine integral_congr_ae ?_
  filter_upwards [hac.ae_le hp.ae_differentiableAt, hac.ae_le hm.ae_differentiableAt] with x h2 h3
  exact norm_fderiv_sq_eq_posPart_add_negPart hf.continuous h2 h3

lemma gaussL2_eq_posPart_add_negPart {L : ℝ≥0} (hf : LipschitzWith L f) (h0 : f 0 = 0) :
    gaussL2 f = gaussL2 (fun y => max (f y) 0) + gaussL2 (fun y => max (-f y) 0) := by
  have hp : LipschitzWith L fun y => max (f y) 0 := hf.max_const 0
  have hm : LipschitzWith L fun y => max (-f y) 0 := hf.neg.max_const 0
  unfold gaussL2
  rw [← integral_add (integrable_sq_of_lipschitzWith hp (by simp [h0]))
    (integrable_sq_of_lipschitzWith hm (by simp [h0]))]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  rcases le_total (f y) 0 with hy | hy
  · simp only [max_eq_right hy, max_eq_left (neg_nonneg.2 hy)]; ring
  · simp only [max_eq_left hy, max_eq_right (neg_nonpos.2 hy)]; ring

lemma IsOneHomogeneous.max_zero (hf : IsOneHomogeneous f) :
    IsOneHomogeneous fun y => max (f y) 0 := fun x t ht => by
  change max (f (t • x)) 0 = t * max (f x) 0
  rw [hf x t ht, mul_max_of_nonneg _ _ ht.le, mul_zero]

lemma IsOneHomogeneous.neg (hf : IsOneHomogeneous f) : IsOneHomogeneous fun y => -f y :=
  fun x t ht => by change -f (t • x) = t * -f x; rw [hf x t ht]; ring

end Parts

/-! ### The half-space profile `⟪x, e⟫⁺` -/

section HalfSpace

variable {e : EuclideanSpace ℝ (Fin n)}

/-- The half-space profile `x ↦ ⟪x, e⟫⁺`. -/
def halfSpaceFn (e : EuclideanSpace ℝ (Fin n)) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  max ⟪x, e⟫ 0

lemma lipschitzWith_inner_right (he : ‖e‖ = 1) :
    LipschitzWith 1 fun x : EuclideanSpace ℝ (Fin n) => ⟪x, e⟫ :=
  LipschitzWith.of_dist_le_mul fun x y => by
    rw [Real.dist_eq, ← inner_sub_left, NNReal.coe_one, one_mul, dist_eq_norm]
    exact (abs_real_inner_le_norm _ _).trans (by rw [he, mul_one])

lemma lipschitzWith_halfSpaceFn (he : ‖e‖ = 1) : LipschitzWith 1 (halfSpaceFn e) :=
  (lipschitzWith_inner_right he).max_const 0

lemma isOneHomogeneous_inner_right : IsOneHomogeneous fun x : EuclideanSpace ℝ (Fin n) => ⟪x, e⟫ :=
  fun x t _ => by simp [real_inner_smul_left]

lemma isOneHomogeneous_halfSpaceFn : IsOneHomogeneous (halfSpaceFn e) :=
  isOneHomogeneous_inner_right.max_zero

lemma halfSpaceFn_nonneg (x : EuclideanSpace ℝ (Fin n)) : 0 ≤ halfSpaceFn e x := le_max_right _ _

lemma halfSpaceFn_pos_iff {x : EuclideanSpace ℝ (Fin n)} : 0 < halfSpaceFn e x ↔ 0 < ⟪x, e⟫ := by
  simp [halfSpaceFn]

lemma harmonicAt_inner_right (x : EuclideanSpace ℝ (Fin n)) :
    HarmonicAt (fun y : EuclideanSpace ℝ (Fin n) => ⟪y, e⟫) x := by
  have hfun : (fun y : EuclideanSpace ℝ (Fin n) => ⟪y, e⟫) = ⇑(innerSL ℝ e) := by
    funext y; simp [real_inner_comm]
  have hfd : fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) => ⟪y, e⟫) = fun _ => innerSL ℝ e := by
    funext w; rw [hfun]; exact (innerSL ℝ e).fderiv
  have h2 : ∀ z, iteratedFDeriv ℝ 2 (fun y : EuclideanSpace ℝ (Fin n) => ⟪y, e⟫) z = 0 := by
    intro z; ext m
    rw [iteratedFDeriv_two_apply, hfd, fderiv_const_apply]
    simp
  refine ⟨by rw [hfun]; exact (innerSL ℝ e).contDiff.contDiffAt, Eventually.of_forall fun y => ?_⟩
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp [h2]

lemma harmonicAt_halfSpaceFn {x : EuclideanSpace ℝ (Fin n)} (hx : 0 < ⟪x, e⟫) :
    HarmonicAt (halfSpaceFn e) x := by
  have hinc : Continuous fun y : EuclideanSpace ℝ (Fin n) => ⟪y, e⟫ := by fun_prop
  have : halfSpaceFn e =ᶠ[𝓝 x] fun y => ⟪y, e⟫ :=
    Filter.eventually_of_mem ((isOpen_lt continuous_const hinc).mem_nhds
      (show x ∈ {y | 0 < ⟪y, e⟫} from hx)) fun y (hy : 0 < ⟪y, e⟫) => max_eq_left hy.le
  exact (harmonicAt_congr_nhds this).2 (harmonicAt_inner_right x)

/-- `Q(⟪x, e⟫⁺) = 0`: the half-space profile realizes the Gaussian Rayleigh quotient `1`. -/
lemma dirichletEnergy_halfSpaceFn (hn : 2 ≤ n) (he : ‖e‖ = 1) :
    dirichletEnergy (halfSpaceFn e) = gaussL2 (halfSpaceFn e) := by
  refine le_antisymm (dirichletEnergy_le_gaussL2 (lipschitzWith_halfSpaceFn he) halfSpaceFn_nonneg
    isOneHomogeneous_halfSpaceFn fun x hx => harmonicAt_halfSpaceFn (halfSpaceFn_pos_iff.1 hx))
    (gaussL2_le_dirichletEnergy hn (lipschitzWith_halfSpaceFn he) halfSpaceFn_nonneg
      isOneHomogeneous_halfSpaceFn ?_)
  have : {x | 0 < halfSpaceFn e x} = {x | 0 < ⟪x, e⟫} := by ext x; exact halfSpaceFn_pos_iff
  rw [this, two_mul_gaussMeasure_halfSpace he]

end HalfSpace

/-! ### Comparison with multiples of the half-space profile -/

/-- A minimizer whose positivity set is the half-space `{⟪x, e⟫ > 0}` is comparable with every
nonnegative multiple of `⟪x, e⟫⁺`. -/
theorem le_or_ge_mul_halfSpaceFn (hn : 2 ≤ n) {v : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ≥0}
    (hv : LipschitzWith L v) (hnn : ∀ x, 0 ≤ v x) (hhom : IsOneHomogeneous v)
    (hmin : dirichletEnergy v ≤ gaussL2 v) {e : EuclideanSpace ℝ (Fin n)} (he : ‖e‖ = 1)
    (hU : {x | 0 < v x} = {x | 0 < ⟪x, e⟫}) {a : ℝ} (ha : 0 ≤ a) :
    (∀ x, v x ≤ a * halfSpaceFn e x) ∨ (∀ x, a * halfSpaceFn e x ≤ v x) := by
  set ℓ := halfSpaceFn e with hℓdef
  have hH := two_mul_gaussMeasure_halfSpace (n := n) he
  have hhalf : 2 * gaussMeasure n {x | 0 < v x} ≤ gaussMeasure n univ := by rw [hU, hH]
  have hℓL := lipschitzWith_halfSpaceFn he
  have hℓhom : IsOneHomogeneous ℓ := isOneHomogeneous_halfSpaceFn
  have hv0 := hhom.map_zero
  have hℓ0 := hℓhom.map_zero
  -- `Q(v) = 0`, `B(v, ℓ) = 0`, `Q(ℓ) = 0`
  have hQv : dirichletEnergy v - gaussL2 v = 0 := by
    have := gaussL2_le_dirichletEnergy hn hv hnn hhom hhalf; linarith
  have hB : gaussBilin v ℓ = 0 := gaussBilin_eq_zero hn hv hnn hhom hmin hhalf hℓL hℓhom
    fun x hx => by
      have : 0 < ⟪x, e⟫ := halfSpaceFn_pos_iff.1 (lt_of_le_of_ne (halfSpaceFn_nonneg x) hx.symm)
      have hx' : x ∈ {x | 0 < ⟪x, e⟫} := this
      rw [← hU] at hx'; exact hx'
  have hQℓ : dirichletEnergy ℓ - gaussL2 ℓ = 0 := by
    rw [dirichletEnergy_halfSpaceFn hn he]; ring
  -- `f = v - a ℓ` has `Q(f) = 0`
  set f : EuclideanSpace ℝ (Fin n) → ℝ := fun y => v y + (-a) * ℓ y with hfdef
  have hfL := lipschitzWith_add_mul hv hℓL (-a)
  have hfhom : IsOneHomogeneous f := fun x t ht => by
    change v (t • x) + -a * ℓ (t • x) = t * (v x + -a * ℓ x)
    rw [hhom x t ht, hℓhom x t ht]; ring
  have hQf : dirichletEnergy f - gaussL2 f = 0 := by
    rw [quadratic_expansion hv hℓL hv0 hℓ0 (-a), hQv, hB, hQℓ]; ring
  -- split into positive and negative parts
  set fp : EuclideanSpace ℝ (Fin n) → ℝ := fun y => max (f y) 0
  set fm : EuclideanSpace ℝ (Fin n) → ℝ := fun y => max (-f y) 0
  have hfpL : LipschitzWith (L + ‖-a‖₊ * 1) fp := hfL.max_const 0
  have hfmL : LipschitzWith (L + ‖-a‖₊ * 1) fm := hfL.neg.max_const 0
  have hfphom : IsOneHomogeneous fp := hfhom.max_zero
  have hfmhom : IsOneHomogeneous fm := hfhom.neg.max_zero
  have hsplit : (dirichletEnergy fp - gaussL2 fp) + (dirichletEnergy fm - gaussL2 fm) = 0 := by
    rw [← hQf, dirichletEnergy_eq_posPart_add_negPart hfL,
      gaussL2_eq_posPart_add_negPart hfL hfhom.map_zero]
    ring
  have hfpH : ∀ x, 0 < fp x → 0 < ⟪x, e⟫ := fun x hx => by
    have hfx : 0 < f x := by simpa [fp] using hx
    have : 0 < v x := by
      have := mul_nonneg ha (halfSpaceFn_nonneg (e := e) x)
      simp only [hfdef] at hfx
      linarith
    have hx' : x ∈ {x | 0 < v x} := this
    rw [hU] at hx'; exact hx'
  have hfmH : ∀ x, 0 < fm x → 0 < ⟪x, e⟫ := fun x hx => by
    have hfx : f x < 0 := by simpa [fm] using hx
    simp only [hfdef] at hfx
    have : 0 < ℓ x := by
      by_contra h
      have h0 : ℓ x = 0 := le_antisymm (not_lt.1 h) (halfSpaceFn_nonneg x)
      rw [h0, mul_zero, add_zero] at hfx
      linarith [hnn x]
    exact halfSpaceFn_pos_iff.1 this
  have hhalf' : ∀ g : EuclideanSpace ℝ (Fin n) → ℝ, (∀ x, 0 < g x → 0 < ⟪x, e⟫) →
      2 * gaussMeasure n {x | 0 < g x} ≤ gaussMeasure n univ := fun g hg => by
    rw [← hH]; exact mul_le_mul_right (measure_mono fun x hx => hg x hx) 2
  have hQp := gaussL2_le_dirichletEnergy hn hfpL (fun _ => le_max_right _ _) hfphom (hhalf' fp hfpH)
  have hQm := gaussL2_le_dirichletEnergy hn hfmL (fun _ => le_max_right _ _) hfmhom (hhalf' fm hfmH)
  have hQp0 : gaussL2 fp = dirichletEnergy fp := by linarith
  -- `f⁺` and `f⁻` cannot both be nonzero
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩ := hcon
  have hfc : Continuous f := hfL.continuous
  set A := {x | 0 < fp x}
  set B := {x | 0 < fm x}
  have hAo : IsOpen A := isOpen_lt continuous_const hfpL.continuous
  have hBo : IsOpen B := isOpen_lt continuous_const hfmL.continuous
  have hx₁A : x₁ ∈ A := by
    change 0 < max (f x₁) 0
    exact lt_max_of_lt_left (by simp only [hfdef]; linarith)
  have hx₂B : x₂ ∈ B := by
    change 0 < max (-f x₂) 0
    exact lt_max_of_lt_left (by simp only [hfdef]; linarith)
  have hAB : Disjoint A B := Set.disjoint_left.2 fun x hxA hxB => by
    have h1 : 0 < f x := by simpa [A, fp] using hxA
    have h2 : f x < 0 := by simpa [B, fm] using hxB
    linarith
  have hsub : A ∪ B ⊆ {x | 0 < ⟪x, e⟫} := by
    rintro x (hx | hx)
    · exact hfpH x hx
    · exact hfmH x hx
  have hmeas := measure_mono (μ := gaussMeasure n) hsub
  rw [measure_union hAB hBo.measurableSet] at hmeas
  have hBpos := gaussMeasure_pos_of_isOpen hBo ⟨x₂, hx₂B⟩
  have hfin : gaussMeasure n A ≠ ⊤ := measure_ne_top _ _
  have hlt : gaussMeasure n A < gaussMeasure n {x | 0 < ⟪x, e⟫} :=
    lt_of_lt_of_le (ENNReal.lt_add_right hfin hBpos.ne') hmeas
  have hsmall : 2 * gaussMeasure n A < gaussMeasure n univ := by
    rw [← hH, mul_comm 2, mul_comm 2]
    exact ENNReal.mul_lt_mul_left two_ne_zero ENNReal.ofNat_ne_top hlt
  have := gaussL2_lt_dirichletEnergy hn hfpL (fun _ => le_max_right _ _) hfphom ⟨x₁, hx₁A⟩ hsmall
  linarith

/-! ### Maximizing the first moment over directions -/

lemma gaussMoment_eq_inner {v : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ≥0} (hv : LipschitzWith L v)
    (hv0 : v 0 = 0) (e : EuclideanSpace ℝ (Fin n)) :
    gaussMoment e v = ⟪∫ x, v x • x ∂gaussMeasure n, e⟫ := by
  have hint : Integrable (fun x => v x • x) (gaussMeasure n) := by
    refine ((integrable_norm_pow_gaussMeasure (n := n) 2).const_mul L).mono'
      (hv.continuous.smul continuous_id).aestronglyMeasurable (ae_of_all _ fun x => ?_)
    rw [norm_smul, Real.norm_eq_abs, sq, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (abs_le_mul_norm_of_lipschitzWith hv hv0 x) (norm_nonneg x)
  rw [real_inner_comm, ← integral_inner hint e, gaussMoment]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [inner_smul_right, real_inner_comm]

lemma gaussMoment_comp_reflect {a : EuclideanSpace ℝ (Fin n)} (e : EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin n) → ℝ) :
    gaussMoment e (fun x => v (reflect a x)) = gaussMoment (reflect a e) v := by
  have h := integral_comp_reflect (a := a) (fun y => v y * ⟪reflect a y, e⟫)
  simp only [reflect_reflect] at h
  unfold gaussMoment
  rw [h]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only
  congr 1
  rw [← (reflect a).inner_map_map, reflect_reflect]

/-- A direction maximizing `J_e(v)` over unit vectors `e`. -/
lemma exists_isMaxOn_gaussMoment_sphere (hn : 2 ≤ n) {v : EuclideanSpace ℝ (Fin n) → ℝ}
    {L : ℝ≥0} (hv : LipschitzWith L v) (hv0 : v 0 = 0) :
    ∃ e : EuclideanSpace ℝ (Fin n), ‖e‖ = 1 ∧
      ∀ e' : EuclideanSpace ℝ (Fin n), ‖e'‖ = 1 → gaussMoment e' v ≤ gaussMoment e v := by
  obtain ⟨e₀, he₀⟩ := exists_unit_vector hn
  have hc : Continuous fun e : EuclideanSpace ℝ (Fin n) => gaussMoment e v := by
    simp_rw [gaussMoment_eq_inner hv hv0]
    exact continuous_const.inner continuous_id
  obtain ⟨e, he, hmax⟩ := (isCompact_sphere (0 : EuclideanSpace ℝ (Fin n)) 1).exists_isMaxOn
    ⟨e₀, by simpa using he₀⟩ hc.continuousOn
  refine ⟨e, by simpa using he, fun e' he' => hmax (by simpa using he')⟩

/-- **Equality case.** A one-homogeneous harmonic "eigenfunction" whose connected positivity set
has exactly half of the Gaussian measure is a multiple of `⟪x, e⟫⁺`. -/
theorem eq_halfSpace_of_two_mul_gaussMeasure_eq (hn : 2 ≤ n)
    {v : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ≥0}
    (hv : LipschitzWith L v) (hnn : ∀ x, 0 ≤ v x) (hhom : IsOneHomogeneous v)
    (hharm : ∀ x, 0 < v x → HarmonicAt v x) (hconn : IsConnected {x | 0 < v x})
    (hhalf : 2 * gaussMeasure n {x | 0 < v x} = gaussMeasure n univ) :
    ∃ e : EuclideanSpace ℝ (Fin n), ‖e‖ = 1 ∧ {x | 0 < v x} = {x | 0 < ⟪x, e⟫} ∧
      ∃ a : ℝ, 0 < a ∧ ∀ x, 0 < v x → v x = a * ⟪x, e⟫ := by
  set U := {x | 0 < v x} with hUdef
  have hv0 : v 0 = 0 := hhom.map_zero
  have hmin : dirichletEnergy v ≤ gaussL2 v := dirichletEnergy_le_gaussL2 hv hnn hhom hharm
  have hhalf' : 2 * gaussMeasure n U ≤ gaussMeasure n univ := hhalf.le
  -- 1. a direction maximizing the first moment
  obtain ⟨e, he, hmax⟩ := exists_isMaxOn_gaussMoment_sphere hn hv hv0
  -- 2. cap symmetry about `e`
  have hsym : ∀ a : EuclideanSpace ℝ (Fin n), ‖a‖ = 1 → 0 < ⟪a, e⟫ →
      ∀ x, 0 < ⟪x, a⟫ → v (reflect a x) ≤ v x := by
    intro a ha hae
    rcases polarize_dichotomy hn ha hv hnn hhom hmin hhalf' hharm hconn.isPreconnected with
      h | h
    · exact h
    · have hP : polarize a v = fun x => v (reflect a x) :=
        funext (polarize_eq_comp_reflect ha h)
      have h1 := gaussMoment_le_polarize ha hae.le hv hv0 (e := e)
      have h2 : gaussMoment e (polarize a v) ≤ gaussMoment e v := by
        rw [hP, gaussMoment_comp_reflect]
        exact hmax _ (by rw [LinearIsometryEquiv.norm_map, he])
      exact fun x hx => le_of_gaussMoment_polarize_eq ha hae hv hv0 (le_antisymm h2 h1) hx
  -- 3. the positivity set is the half-space
  have hUH : ∀ x, 0 < v x → 0 < ⟪x, e⟫ :=
    inner_pos_of_two_mul_le he hv.continuous hhom hsym hhalf'
  have hHU : ∀ x, 0 < ⟪x, e⟫ → 0 < v x := by
    intro x₀ hx₀
    by_contra hle
    have hvx₀ : v x₀ = 0 := le_antisymm (not_lt.1 hle) (hnn x₀)
    have hx₀0 : x₀ ≠ 0 := by rintro rfl; simp at hx₀
    have hn₀ : 0 < ‖x₀‖ := norm_pos_iff.2 hx₀0
    set θ₀ := ‖x₀‖⁻¹ • x₀
    have hθ₀ : ‖θ₀‖ = 1 := by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn₀.ne']
    have hs : 0 < ⟪θ₀, e⟫ := by rw [real_inner_smul_left]; positivity
    have hvθ₀ : v θ₀ = 0 := by rw [hhom x₀ _ (inv_pos.2 hn₀), hvx₀, mul_zero]
    have hcone : ∀ x, 0 < v x → ⟪θ₀, e⟫ * ‖x‖ ≤ ⟪x, e⟫ := by
      intro x hx
      obtain ⟨hx0, hθ, hvθ⟩ := normalize_pos hhom hx
      have hnx : 0 < ‖x‖ := norm_pos_iff.2 hx0
      by_contra hlt
      push Not at hlt
      have : ⟪‖x‖⁻¹ • x, e⟫ < ⟪θ₀, e⟫ := by
        rw [real_inner_smul_left, inv_mul_lt_iff₀ hnx]; linarith
      have := le_of_norm_eq_of_inner_lt hsym (hθ₀.trans hθ.symm) this
      rw [hvθ₀] at this
      exact absurd hvθ (not_lt.2 this)
    have := gaussL2_lt_dirichletEnergy_of_subset_cone hn hv hnn hhom hs hcone hconn.nonempty
    linarith
  have hUeq : U = {x | 0 < ⟪x, e⟫} := Set.ext fun x => ⟨hUH x, hHU x⟩
  -- 4. comparison with `⟪x, e⟫⁺`
  have hℓe : halfSpaceFn e e = 1 := by
    simp [halfSpaceFn, he]
  set a := v e with hadef
  have hapos : 0 < a := hHU e (by rw [real_inner_self_eq_norm_sq, he]; norm_num)
  have hcmp := fun b (hb : 0 ≤ b) => le_or_ge_mul_halfSpaceFn hn hv hnn hhom hmin he hUeq hb
  have hle : ∀ x, v x ≤ a * halfSpaceFn e x := by
    intro x
    by_contra hlt
    push Not at hlt
    have hℓx : 0 < halfSpaceFn e x := by
      by_contra h
      have h0 : halfSpaceFn e x = 0 := le_antisymm (not_lt.1 h) (halfSpaceFn_nonneg x)
      rcases hcmp (a + 1) (by linarith) with h1 | h1
      · have := h1 x; rw [h0, mul_zero] at this hlt; linarith
      · have := h1 e; rw [hℓe, mul_one] at this; linarith
    set ε := (v x - a * halfSpaceFn e x) / (2 * halfSpaceFn e x)
    have hε : 0 < ε := div_pos (by linarith) (by positivity)
    rcases hcmp (a + ε) (by linarith) with h1 | h1
    · have := h1 x
      have hεℓ : ε * halfSpaceFn e x = (v x - a * halfSpaceFn e x) / 2 := by
        simp only [ε]; field_simp
      nlinarith
    · have := h1 e; rw [hℓe, mul_one] at this; linarith
  have hge : ∀ x, a * halfSpaceFn e x ≤ v x := by
    intro x
    by_contra hlt
    push Not at hlt
    have hℓx : 0 < halfSpaceFn e x := by
      by_contra h
      have h0 : halfSpaceFn e x = 0 := le_antisymm (not_lt.1 h) (halfSpaceFn_nonneg x)
      rw [h0, mul_zero] at hlt; linarith [hnn x]
    set ε := min (a / 2) ((a * halfSpaceFn e x - v x) / (2 * halfSpaceFn e x))
    have hε : 0 < ε := lt_min (by linarith) (div_pos (by linarith) (by positivity))
    have hεa : ε ≤ a / 2 := min_le_left _ _
    have hεx : ε * halfSpaceFn e x ≤ (a * halfSpaceFn e x - v x) / 2 := by
      have := min_le_right (a / 2) ((a * halfSpaceFn e x - v x) / (2 * halfSpaceFn e x))
      rw [le_div_iff₀ (by positivity)] at this
      linarith
    rcases hcmp (a - ε) (by linarith) with h1 | h1
    · have := h1 e; rw [hℓe, mul_one] at this; linarith
    · have := h1 x
      nlinarith
  refine ⟨e, he, hUeq, a, hapos, fun x hx => ?_⟩
  have hx' := hUH x hx
  have := le_antisymm (hle x) (hge x)
  rw [this, halfSpaceFn, max_eq_left hx'.le]

end Sperner
