/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Sperner.GaussIBP
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# The energy inequality for one-homogeneous harmonic functions

If `v ≥ 0` is Lipschitz, one-homogeneous, and harmonic where it is positive, then
`∫ |Dv|² dγ ≤ ∫ v² dγ` (in fact equality holds). Formally: the Ornstein–Uhlenbeck operator
`L = Δ - x · ∇` satisfies `L v = -v` on `{v > 0}` (harmonicity and Euler's identity
`x · ∇v = v`), and one integrates by parts against `S(k v - 1) v ζ(x/k)` with the smooth
monotone step `S = Real.smoothTransition` and a fixed smooth bump `ζ`; the terms that are hard
to control have a favourable sign.

## Main results

* `Sperner.fderiv_apply_self_of_isOneHomogeneous`: Euler's identity `Dv(x) x = v(x)`.
* `Sperner.integral_fderiv_apply_gradient_mul_gaussWeight`: the weak form of `L v = -v`,
  `∫ Dη(∇v) e^{-|x|²/2} = ∫ η v e^{-|x|²/2}` for `C¹` test functions `η` with compact support in
  `{v > 0}`.
* `Sperner.dirichletEnergy_le_gaussL2`: the energy inequality.
-/

open MeasureTheory Set Filter Topology InnerProductSpace Metric
open scoped NNReal RealInnerProductSpace ContDiff

@[expose] public noncomputable section

namespace Sperner

variable {n : ℕ}

/-- **Euler's identity** for one-homogeneous functions: `Dv(x) x = v(x)`. -/
lemma fderiv_apply_self_of_isOneHomogeneous {v : EuclideanSpace ℝ (Fin n) → ℝ}
    (hhom : IsOneHomogeneous v) {x : EuclideanSpace ℝ (Fin n)}
    (hd : DifferentiableAt ℝ v x) : fderiv ℝ v x x = v x := by
  have h1 : HasDerivAt (fun t : ℝ => v (t • x)) (fderiv ℝ v x x) 1 := by
    have hs : HasDerivAt (fun t : ℝ => t • x) x 1 := by
      simpa using (hasDerivAt_id (1 : ℝ)).smul_const x
    have hd' : HasFDerivAt v (fderiv ℝ v x) ((1 : ℝ) • x) := by
      rw [one_smul]; exact hd.hasFDerivAt
    exact hd'.comp_hasDerivAt 1 hs
  have h2 : HasDerivAt (fun t : ℝ => v (t • x)) (v x) 1 := by
    have : HasDerivAt (fun t : ℝ => t * v x) (v x) 1 := by
      simpa using (hasDerivAt_id (1 : ℝ)).mul_const (v x)
    refine this.congr_of_eventuallyEq ?_
    filter_upwards [lt_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact hhom x t ht
  exact h1.unique h2

/-- At a zero of a nonnegative function (a global minimum), the derivative vanishes. -/
lemma fderiv_eq_zero_of_nonneg_of_eq_zero {v : EuclideanSpace ℝ (Fin n) → ℝ}
    (hnn : ∀ y, 0 ≤ v y) {x : EuclideanSpace ℝ (Fin n)}
    (hx : v x = 0) : fderiv ℝ v x = 0 := by
  by_cases hd : DifferentiableAt ℝ v x
  · refine IsLocalMin.fderiv_eq_zero ?_
    exact Filter.Eventually.of_forall fun y => by rw [hx]; exact hnn y
  · exact fderiv_zero_of_not_differentiableAt hd

lemma inner_gradient_right (f : EuclideanSpace ℝ (Fin n) → ℝ) (x y : EuclideanSpace ℝ (Fin n)) :
    ⟪y, gradient f x⟫ = fderiv ℝ f x y := by
  rw [gradient, real_inner_comm, toDual_symm_apply]

lemma norm_gradient (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖gradient f x‖ = ‖fderiv ℝ f x‖ := by
  rw [gradient, LinearIsometryEquiv.norm_map]

lemma fderiv_apply_gradient (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ f x (gradient f x) = ‖fderiv ℝ f x‖ ^ 2 := by
  rw [← inner_gradient_right, real_inner_self_eq_norm_sq, norm_gradient]

lemma clm_apply_eq_sum_inner {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (EuclideanSpace ℝ (Fin n))) (ℓ : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (w : EuclideanSpace ℝ (Fin n)) : ℓ w = ∑ i, ⟪b i, w⟫ * ℓ (b i) := by
  conv_lhs => rw [← b.sum_repr' w]
  simp [map_sum, map_smul]

/-- A Lipschitz function vanishing at the origin grows linearly. -/
lemma abs_le_mul_norm_of_lipschitzWith {v : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ≥0}
    (hv : LipschitzWith L v)
    (h0 : v 0 = 0) (x : EuclideanSpace ℝ (Fin n)) : |v x| ≤ L * ‖x‖ := by
  have := hv.dist_le_mul x 0
  rwa [Real.dist_eq, h0, sub_zero, dist_zero_right] at this

lemma IsOneHomogeneous.apply_zero {v : EuclideanSpace ℝ (Fin n) → ℝ} (hhom : IsOneHomogeneous v) :
    v 0 = 0 := by
  have := hhom 0 2 two_pos
  rw [smul_zero] at this
  linarith

section WeakEquation

variable {v : EuclideanSpace ℝ (Fin n) → ℝ} {η : EuclideanSpace ℝ (Fin n) → ℝ}

/-- **Weak form of `L v = -v`** on `{v > 0}`: for a `C¹` test function `η` with compact support
inside `{v > 0}`, `∫ Dη(∇v) e^{-|x|²/2} = ∫ η v e^{-|x|²/2}`. -/
theorem integral_fderiv_apply_gradient_mul_gaussWeight (hhom : IsOneHomogeneous v)
    (hharm : ∀ x, 0 < v x → HarmonicAt v x) (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η)
    (hηU : tsupport η ⊆ {x | 0 < v x}) :
    Integrable (fun x => fderiv ℝ η x (gradient v x) * gaussWeight x) ∧
      ∫ x, fderiv ℝ η x (gradient v x) * gaussWeight x = ∫ x, η x * v x * gaussWeight x := by
  set b := EuclideanSpace.basisFun (Fin n) ℝ
  set F : Fin n → EuclideanSpace ℝ (Fin n) → ℝ := fun i y => η y * fderiv ℝ v y (b i) with hF
  have hη0 : ∀ y, y ∉ tsupport η → η =ᶠ[𝓝 y] 0 := fun y hy =>
    notMem_tsupport_iff_eventuallyEq.1 hy
  have hηz : ∀ y, ¬ 0 < v y → η y = 0 := fun y hy =>
    image_eq_zero_of_notMem_tsupport fun h => hy (hηU h)
  -- `∂ᵢv` is `C¹` near points of `{v > 0}`
  have hdv : ∀ y, 0 < v y → ContDiffAt ℝ 1 (fderiv ℝ v) y := fun y hy =>
    (hharm y hy).1.fderiv_right (m := 1) (by norm_num)
  have hFcd : ∀ i, ContDiff ℝ 1 (F i) := by
    intro i
    refine contDiff_iff_contDiffAt.2 fun y => ?_
    by_cases hy : y ∈ tsupport η
    · exact hη.contDiffAt.mul ((hdv y (hηU hy)).clm_apply contDiffAt_const)
    · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [hη0 y hy] with z hz
      simp [hF, hz]
  have hFc : ∀ i, HasCompactSupport (F i) := fun i => hηc.mul_right
  -- product rule for `F i` in direction `b i`
  have hFd : ∀ i y, fderiv ℝ (F i) y (b i) = fderiv ℝ η y (b i) * fderiv ℝ v y (b i) +
      η y * fderiv ℝ (fderiv ℝ v) y (b i) (b i) := by
    intro i y
    by_cases hy : y ∈ tsupport η
    · have hd1 : DifferentiableAt ℝ η y := hη.differentiable one_ne_zero y
      have hd2 : DifferentiableAt ℝ (fderiv ℝ v) y :=
        (hdv y (hηU hy)).differentiableAt one_ne_zero
      have hd3 : HasFDerivAt (fun z => fderiv ℝ v z (b i))
          ((fderiv ℝ (fderiv ℝ v) y).flip (b i)) y := by
        have := hd2.hasFDerivAt.clm_apply (hasFDerivAt_const (b i) y)
        simpa using this
      rw [show F i = η * (fun z => fderiv ℝ v z (b i)) from rfl,
        (hd1.hasFDerivAt.mul hd3).fderiv]
      simp only [add_apply, smul_apply,
        ContinuousLinearMap.flip_apply, smul_eq_mul]
      ring
    · have h1 : fderiv ℝ (F i) y = 0 := by
        have : F i =ᶠ[𝓝 y] fun _ => 0 := by
          filter_upwards [hη0 y hy] with z hz
          simp [hF, hz]
        rw [this.fderiv_eq]; simp
      have h2 : fderiv ℝ η y = 0 := by
        rw [(hη0 y hy).fderiv_eq]; simp
      rw [h1, h2, image_eq_zero_of_notMem_tsupport hy]
      simp
  -- integration by parts in direction `b i`
  have hgd : ∀ x i, fderiv ℝ gaussWeight x (b i) = -(⟪x, b i⟫ * gaussWeight x) :=
    fun x i => fderiv_gaussWeight_apply x (b i)
  have hcont_g : Continuous fun x : EuclideanSpace ℝ (Fin n) => gaussWeight x :=
    continuous_gaussWeight
  have hFcont : ∀ i, Continuous (F i) := fun i => (hFcd i).continuous
  have hDFcont : ∀ i, Continuous fun x => fderiv ℝ (F i) x (b i) :=
    fun i => ((hFcd i).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hDFc : ∀ i, HasCompactSupport fun x => fderiv ℝ (F i) x (b i) := by
    intro i
    refine (HasCompactSupport.fderiv (𝕜 := ℝ) (hFc i)).mono' fun x hx => ?_
    refine subset_tsupport _ fun h => hx ?_
    simp [h]
  have hint1 : ∀ i, Integrable fun x => fderiv ℝ (F i) x (b i) * gaussWeight x := fun i =>
    ((hDFcont i).mul hcont_g).integrable_of_hasCompactSupport (hDFc i).mul_right
  have hint2 : ∀ i, Integrable fun x => F i x * (⟪x, b i⟫ * gaussWeight x) := fun i =>
    ((hFcont i).mul ((continuous_id.inner continuous_const).mul
      hcont_g)).integrable_of_hasCompactSupport
      (hFc i).mul_right
  have hibp : ∀ i, ∫ x, fderiv ℝ (F i) x (b i) * gaussWeight x =
      ∫ x, F i x * (⟪x, b i⟫ * gaussWeight x) := by
    intro i
    have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (f := F i)
      (g := gaussWeight) (v := b i) (hint1 i)
      (by simp_rw [hgd]; exact ((hint2 i).neg).congr (Filter.Eventually.of_forall fun x => by
        simp))
      (((hFcont i).mul hcont_g).integrable_of_hasCompactSupport (hFc i).mul_right)
      (fun x _ => (hFcd i).differentiable one_ne_zero x)
      (fun x _ => differentiable_gaussWeight x)
    simp_rw [hgd, mul_neg, integral_neg, neg_inj] at h
    exact h.symm
  -- pointwise identities
  have hpt1 : ∀ x, fderiv ℝ η x (gradient v x) * gaussWeight x =
      ∑ i, fderiv ℝ (F i) x (b i) * gaussWeight x := by
    intro x
    simp_rw [hFd, ← Finset.sum_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
    have hlap : η x * ∑ i, fderiv ℝ (fderiv ℝ v) x (b i) (b i) = 0 := by
      by_cases hx : 0 < v x
      · have hΔ := (hharm x hx).2.eq_of_nhds
        rw [laplacian_eq_iteratedFDeriv_orthonormalBasis v b] at hΔ
        simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at hΔ
        rw [hΔ]; simp
      · rw [hηz x hx, zero_mul]
    rw [hlap, add_zero, clm_apply_eq_sum_inner b (fderiv ℝ η x)]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_gradient_right, mul_comm]
  have hpt2 : ∀ x, η x * v x * gaussWeight x = ∑ i, F i x * (⟪x, b i⟫ * gaussWeight x) := by
    intro x
    simp only [hF]
    by_cases hx : 0 < v x
    · have hd : DifferentiableAt ℝ v x := (hharm x hx).1.differentiableAt (by norm_num)
      rw [← fderiv_apply_self_of_isOneHomogeneous hhom hd,
        clm_apply_eq_sum_inner b (fderiv ℝ v x) x, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [real_inner_comm]; ring
    · simp [hηz x hx]
  have hintL : Integrable fun x => fderiv ℝ η x (gradient v x) * gaussWeight x :=
    (integrable_finsetSum _ fun i _ => hint1 i).congr
      (Filter.Eventually.of_forall fun x => (hpt1 x).symm)
  refine ⟨hintL, ?_⟩
  calc ∫ x, fderiv ℝ η x (gradient v x) * gaussWeight x
      = ∫ x, ∑ i, fderiv ℝ (F i) x (b i) * gaussWeight x := by simp_rw [hpt1]
    _ = ∑ i, ∫ x, fderiv ℝ (F i) x (b i) * gaussWeight x :=
        integral_finsetSum _ fun i _ => hint1 i
    _ = ∑ i, ∫ x, F i x * (⟪x, b i⟫ * gaussWeight x) := by simp_rw [hibp]
    _ = ∫ x, ∑ i, F i x * (⟪x, b i⟫ * gaussWeight x) :=
        (integral_finsetSum _ fun i _ => hint2 i).symm
    _ = ∫ x, η x * v x * gaussWeight x := by simp_rw [hpt2]

end WeakEquation

/-- **Energy inequality.** A nonnegative, one-homogeneous, Lipschitz function which is harmonic
on its positivity set has Gaussian Rayleigh quotient at most `1`. -/
theorem dirichletEnergy_le_gaussL2 {v : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ≥0}
    (hv : LipschitzWith L v) (hnn : ∀ x, 0 ≤ v x) (hhom : IsOneHomogeneous v)
    (hharm : ∀ x, 0 < v x → HarmonicAt v x) :
    dirichletEnergy v ≤ gaussL2 v := by
  have hvc : Continuous v := hv.continuous
  have hv0 : v 0 = 0 := hhom.apply_zero
  have hvle : ∀ x, v x ≤ L * ‖x‖ := fun x =>
    (le_abs_self _).trans (abs_le_mul_norm_of_lipschitzWith hv hv0 x)
  have hDv : ∀ x, ‖fderiv ℝ v x‖ ≤ L := fun x => norm_fderiv_le_of_lipschitz ℝ hv
  have hL0 : (0 : ℝ) ≤ L := L.2
  have hg0 : ∀ x : EuclideanSpace ℝ (Fin n), 0 < gaussWeight x := gaussWeight_pos
  -- the cutoffs
  let ζ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) := ⟨1, 2, one_pos, one_lt_two⟩
  obtain ⟨Cζ, hCζ⟩ :=
    ((ζ.contDiff (n := 1)).continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    (HasCompactSupport.fderiv (𝕜 := ℝ) ζ.hasCompactSupport)
  have hCζ0 : 0 ≤ Cζ := (norm_nonneg _).trans (hCζ 0)
  set S := Real.smoothTransition with hSdef
  set k : ℕ → ℝ := fun m => (m : ℝ) + 1 with hk
  have hkpos : ∀ m, 0 < k m := fun m => by positivity
  have hkinv : ∀ m, (k m)⁻¹ ≤ 1 := fun m =>
    inv_le_one_of_one_le₀ (by simp only [hk]; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)])
  set Z : ℕ → EuclideanSpace ℝ (Fin n) → ℝ := fun m x => ζ ((k m)⁻¹ • x) with hZ
  set η : ℕ → EuclideanSpace ℝ (Fin n) → ℝ := fun m x => S (k m * v x - 1) * v x * Z m x
    with hη
  have hZc : ∀ m, ContDiff ℝ 1 (Z m) := fun m => ζ.contDiff.comp (contDiff_const_smul _)
  have hZd : ∀ m x, HasFDerivAt (Z m) ((fderiv ℝ ζ ((k m)⁻¹ • x)).comp
      ((k m)⁻¹ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))) x := fun m x =>
    ((ζ.contDiff (n := 1)).differentiable one_ne_zero _).hasFDerivAt.comp x
      ((hasFDerivAt_id x).const_smul (k m)⁻¹)
  have hZn : ∀ m x, ‖fderiv ℝ (Z m) x‖ ≤ Cζ * (k m)⁻¹ := by
    intro m x
    rw [(hZd m x).fderiv]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    gcongr
    · exact hCζ _
    · refine (norm_smul_le _ _).trans ?_
      rw [Real.norm_of_nonneg (inv_nonneg.2 (hkpos m).le)]
      exact mul_le_of_le_one_right (inv_nonneg.2 (hkpos m).le) ContinuousLinearMap.norm_id_le
  have hZ0 : ∀ m x, 0 ≤ Z m x := fun m x => ζ.nonneg
  have hZ1 : ∀ m x, Z m x ≤ 1 := fun m x => ζ.le_one
  have hZlim : ∀ x, ∀ᶠ m in atTop, Z m x = 1 := by
    intro x
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop ‖x‖] with m hm
    refine ζ.one_of_mem_closedBall ?_
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 (hkpos m).le)]
    change (k m)⁻¹ * ‖x‖ ≤ 1
    rw [inv_mul_le_iff₀ (hkpos m), mul_one]
    simp only [hk]; linarith
  have hS01 : ∀ t, 0 ≤ S t ∧ S t ≤ 1 := fun t =>
    ⟨Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩
  have hSlim : ∀ x, 0 < v x → ∀ᶠ m in atTop, S (k m * v x - 1) = 1 := by
    intro x hx
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (2 / v x)] with m hm
    refine Real.smoothTransition.one_of_one_le ?_
    have : 2 ≤ k m * v x := by
      rw [div_le_iff₀ hx] at hm
      simp only [hk]; nlinarith
    linarith
  have hS0 : ∀ x m, ¬ 0 < v x → S (k m * v x - 1) = 0 := by
    intro x m hx
    have : v x = 0 := le_antisymm (not_lt.1 hx) (hnn x)
    exact Real.smoothTransition.zero_of_nonpos (by rw [this]; norm_num)
  -- the test functions
  have hηloc : ∀ m x, v x < (k m)⁻¹ → η m =ᶠ[𝓝 x] 0 := by
    intro m x hx
    filter_upwards [(hvc.tendsto x).eventually (gt_mem_nhds hx)] with y hy
    have : k m * v y - 1 ≤ 0 := by
      have := mul_lt_mul_of_pos_left hy (hkpos m)
      rw [mul_inv_cancel₀ (hkpos m).ne'] at this
      linarith
    have hS : S (k m * v y - 1) = 0 := Real.smoothTransition.zero_of_nonpos this
    simp [hη, hS]
  have hηcd : ∀ m, ContDiff ℝ 1 (η m) := by
    intro m
    refine contDiff_iff_contDiffAt.2 fun x => ?_
    by_cases hx : 0 < v x
    · have hv1 : ContDiffAt ℝ 1 v x := (hharm x hx).1.of_le (by norm_num)
      exact ((Real.smoothTransition.contDiffAt.comp x
        ((contDiffAt_const.mul hv1).sub contDiffAt_const)).mul hv1).mul (hZc m).contDiffAt
    · have h0 : v x = 0 := le_antisymm (not_lt.1 hx) (hnn x)
      refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      exact hηloc m x (by rw [h0]; exact inv_pos.2 (hkpos m))
  have hηcs : ∀ m, HasCompactSupport (η m) := fun m =>
    show HasCompactSupport ((fun x => S (k m * v x - 1) * v x) * Z m) from
      (ζ.hasCompactSupport.comp_smul (inv_ne_zero (hkpos m).ne')).mul_left
  have hηU : ∀ m, tsupport (η m) ⊆ {x | 0 < v x} := by
    intro m
    refine (closure_minimal (s := Function.support (η m)) (t := {x | (k m)⁻¹ ≤ v x}) ?_
      (isClosed_le continuous_const hvc)).trans fun x hx => (inv_pos.2 (hkpos m)).trans_le hx
    intro x hx
    by_contra hlt
    exact hx ((hηloc m x (not_le.1 hlt)).eq_of_nhds)
  -- pointwise lower bound for `Dη(∇v)`
  have hpt : ∀ m x, S (k m * v x - 1) * ‖fderiv ℝ v x‖ ^ 2 * Z m x +
      S (k m * v x - 1) * v x * fderiv ℝ (Z m) x (gradient v x) ≤
        fderiv ℝ (η m) x (gradient v x) := by
    intro m x
    by_cases hx : 0 < v x
    · have hvd := ((hharm x hx).1.differentiableAt (by norm_num)).hasFDerivAt
      have hSd : HasDerivAt S (deriv S (k m * v x - 1)) (k m * v x - 1) :=
        ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero _).hasDerivAt
      have h1 : HasFDerivAt (fun y => k m * v y - 1) (k m • fderiv ℝ v x) x :=
        (hvd.const_mul (k m)).sub_const 1
      have h3 := ((hSd.comp_hasFDerivAt x h1).mul hvd).mul (hZd m x)
      have hS' : 0 ≤ deriv S (k m * v x - 1) := Real.smoothTransition.monotone.deriv_nonneg
      rw [show η m = (S ∘ fun y => k m * v y - 1) * v * Z m from rfl, h3.fderiv,
        ← (hZd m x).fderiv]
      simp only [add_apply, smul_apply, smul_eq_mul,
        Function.comp, fderiv_apply_gradient, Pi.mul_apply]
      have := mul_nonneg (mul_nonneg (mul_nonneg (hZ0 m x) (hnn x)) hS')
        (mul_nonneg (hkpos m).le (sq_nonneg ‖fderiv ℝ v x‖))
      nlinarith
    · have h0 : v x = 0 := le_antisymm (not_lt.1 hx) (hnn x)
      have : fderiv ℝ (η m) x = 0 := by
        rw [(hηloc m x (by rw [h0]; exact inv_pos.2 (hkpos m))).fderiv_eq]; simp
      rw [this, hS0 x m hx]
      simp
  -- the three families of integrands
  have hgm : Measurable (gradient v) :=
    (toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.continuous.measurable.comp (measurable_fderiv ℝ v)
  have hSc : ∀ m, Continuous fun x => S (k m * v x - 1) := fun m =>
    Real.smoothTransition.continuous.comp ((continuous_const.mul hvc).sub continuous_const)
  have hBm : ∀ m, Measurable fun x => fderiv ℝ (Z m) x (gradient v x) := fun m =>
    (continuous_fst.clm_apply continuous_snd).measurable.comp
      (((hZc m).continuous_fderiv one_ne_zero).measurable.prodMk hgm)
  have hgint : Integrable fun x : EuclideanSpace ℝ (Fin n) => gaussWeight x :=
    integrable_gaussWeight
  have hmom : ∀ j : ℕ, Integrable fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ j * gaussWeight x := by
    intro j
    refine (integrable_norm_pow_mul_exp_neg_mul_sq_norm (n := n) (b := 1 / 2) (by norm_num) j).congr
      (Filter.Eventually.of_forall fun x => ?_)
    simp only [gaussWeight]; congr 2; ring
  set A : ℕ → EuclideanSpace ℝ (Fin n) → ℝ :=
    fun m x => S (k m * v x - 1) * ‖fderiv ℝ v x‖ ^ 2 * Z m x * gaussWeight x with hA
  set B : ℕ → EuclideanSpace ℝ (Fin n) → ℝ :=
    fun m x => S (k m * v x - 1) * v x * fderiv ℝ (Z m) x (gradient v x) * gaussWeight x with hB
  set C : ℕ → EuclideanSpace ℝ (Fin n) → ℝ := fun m x => η m x * v x * gaussWeight x with hC
  have hAm : ∀ m, AEStronglyMeasurable (A m) volume := fun m =>
    ((((hSc m).measurable.mul ((measurable_fderiv ℝ v).norm.pow_const 2)).mul
      (hZc m).continuous.measurable).mul continuous_gaussWeight.measurable).aestronglyMeasurable
  have hBmeas : ∀ m, AEStronglyMeasurable (B m) volume := fun m =>
    ((((hSc m).measurable.mul hvc.measurable).mul (hBm m)).mul
      continuous_gaussWeight.measurable).aestronglyMeasurable
  have hSZ : ∀ m x, 0 ≤ S (k m * v x - 1) * Z m x ∧ S (k m * v x - 1) * Z m x ≤ 1 := by
    intro m x
    have h1 := hS01 (k m * v x - 1)
    exact ⟨mul_nonneg h1.1 (hZ0 m x), (mul_le_of_le_one_left (hZ0 m x) h1.2).trans (hZ1 m x)⟩
  have hAbd : ∀ m x, |A m x| ≤ L ^ 2 * gaussWeight x := by
    intro m x
    have h2 : ‖fderiv ℝ v x‖ ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hDv x) 2
    have hA' : A m x = (S (k m * v x - 1) * Z m x) * (‖fderiv ℝ v x‖ ^ 2 * gaussWeight x) := by
      simp only [hA]; ring
    have h3 : ‖fderiv ℝ v x‖ ^ 2 * gaussWeight x ≤ L ^ 2 * gaussWeight x :=
      mul_le_mul_of_nonneg_right h2 (hg0 x).le
    rw [hA', abs_of_nonneg (mul_nonneg (hSZ m x).1 (by have := hg0 x; positivity))]
    calc _ ≤ 1 * (L ^ 2 * gaussWeight x) :=
          mul_le_mul (hSZ m x).2 h3 (by have := hg0 x; positivity) zero_le_one
      _ = _ := one_mul _
  have hBbd : ∀ m x, |B m x| ≤ (L * (Cζ * L)) * (‖x‖ ^ 1 * gaussWeight x) * (k m)⁻¹ := by
    intro m x
    have h1 := hS01 (k m * v x - 1)
    have h2 : |fderiv ℝ (Z m) x (gradient v x)| ≤ Cζ * (k m)⁻¹ * L := by
      refine ((fderiv ℝ (Z m) x).le_opNorm _).trans ?_
      rw [norm_gradient]
      exact mul_le_mul (hZn m x) (hDv x) (norm_nonneg _) (by positivity)
    have hB' : |B m x| = S (k m * v x - 1) *
        (v x * |fderiv ℝ (Z m) x (gradient v x)| * gaussWeight x) := by
      simp only [hB, abs_mul, abs_of_nonneg h1.1, abs_of_nonneg (hnn x), abs_of_pos (hg0 x)]
      ring
    have h3 : v x * |fderiv ℝ (Z m) x (gradient v x)| * gaussWeight x ≤
        (L * ‖x‖) * (Cζ * (k m)⁻¹ * L) * gaussWeight x :=
      mul_le_mul_of_nonneg_right (mul_le_mul (hvle x) h2 (abs_nonneg _) (by positivity))
        (hg0 x).le
    rw [hB']
    calc _ ≤ 1 * ((L * ‖x‖) * (Cζ * (k m)⁻¹ * L) * gaussWeight x) :=
          mul_le_mul h1.2 h3 (by have := hg0 x; have := hnn x; positivity) zero_le_one
      _ = _ := by ring
  have hCbd : ∀ m x, |C m x| ≤ L ^ 2 * (‖x‖ ^ 2 * gaussWeight x) := by
    intro m x
    have h2 : v x * v x ≤ (L * ‖x‖) * (L * ‖x‖) :=
      mul_self_le_mul_self (hnn x) (hvle x)
    have hC' : C m x = (S (k m * v x - 1) * Z m x) * (v x * v x * gaussWeight x) := by
      simp only [hC, hη]; ring
    have h3 : v x * v x * gaussWeight x ≤ (L * ‖x‖) * (L * ‖x‖) * gaussWeight x :=
      mul_le_mul_of_nonneg_right h2 (hg0 x).le
    rw [hC', abs_of_nonneg (mul_nonneg (hSZ m x).1
      (by have := hg0 x; have := hnn x; positivity))]
    calc _ ≤ 1 * ((L * ‖x‖) * (L * ‖x‖) * gaussWeight x) :=
          mul_le_mul (hSZ m x).2 h3 (by have := hg0 x; have := hnn x; positivity) zero_le_one
      _ = _ := by ring
  have hAint : ∀ m, Integrable (A m) := fun m =>
    (hgint.const_mul _).mono' (hAm m) (Filter.Eventually.of_forall fun x => hAbd m x)
  have hBint : ∀ m, Integrable (B m) := fun m =>
    (((hmom 1).const_mul _).mul_const _).mono' (hBmeas m)
      (Filter.Eventually.of_forall fun x => hBbd m x)
  -- the inequality for each `m`
  have hineq : ∀ m, (∫ x, A m x) + ∫ x, B m x ≤ ∫ x, C m x := by
    intro m
    obtain ⟨hint, heq⟩ :=
      integral_fderiv_apply_gradient_mul_gaussWeight hhom hharm (hηcd m) (hηcs m) (hηU m)
    rw [← integral_add (hAint m) (hBint m), show (∫ x, C m x) = _ from heq.symm]
    refine integral_mono ((hAint m).add (hBint m)) hint fun x => ?_
    have := mul_le_mul_of_nonneg_right (hpt m x) (hg0 x).le
    simp only [hA, hB]
    linarith
  -- limits
  have hAlim : Tendsto (fun m => ∫ x, A m x) atTop
      (𝓝 (∫ x, ‖fderiv ℝ v x‖ ^ 2 * gaussWeight x)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => L ^ 2 * gaussWeight x) hAm
      (hgint.const_mul _) (fun m => Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]; exact hAbd m x) (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : 0 < v x
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [hSlim x hx, hZlim x] with m h1 h2
      simp only [hA, h1, h2]; ring
    · have h0 : v x = 0 := le_antisymm (not_lt.1 hx) (hnn x)
      have hd : fderiv ℝ v x = 0 := fderiv_eq_zero_of_nonneg_of_eq_zero hnn h0
      simp [hA, hd]
  have hBpt : ∀ x, Tendsto (fun m => B m x) atTop (𝓝 0) := by
    intro x
    refine squeeze_zero_norm (fun m => (hBbd m x).trans_eq rfl) ?_
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
      ((L * (Cζ * L)) * (‖x‖ ^ 1 * gaussWeight x))
    simp only [mul_zero] at h
    refine h.congr fun m => ?_
    simp [hk, one_div]
  have hBlim : Tendsto (fun m => ∫ x, B m x) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (f := fun _ => (0 : ℝ))
      (fun x => (L * (Cζ * L)) * (‖x‖ ^ 1 * gaussWeight x)) hBmeas
      ((hmom 1).const_mul _) (fun m => Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]
        exact (hBbd m x).trans (mul_le_of_le_one_right (mul_nonneg (mul_nonneg hL0
          (mul_nonneg hCζ0 hL0)) (mul_nonneg (pow_nonneg (norm_nonneg x) 1) (hg0 x).le))
          (hkinv m)))
      (Filter.Eventually.of_forall hBpt)
    simpa using h
  have hClim : Tendsto (fun m => ∫ x, C m x) atTop (𝓝 (∫ x, v x ^ 2 * gaussWeight x)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => L ^ 2 * (‖x‖ ^ 2 * gaussWeight x))
      (fun m => ((((hSc m).mul hvc).mul (hZc m).continuous).mul hvc |>.mul
        continuous_gaussWeight).aestronglyMeasurable)
      ((hmom 2).const_mul _) (fun m => Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]; exact hCbd m x) (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : 0 < v x
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [hSlim x hx, hZlim x] with m h1 h2
      simp only [hC, hη, h1, h2]; ring
    · have h0 : v x = 0 := le_antisymm (not_lt.1 hx) (hnn x)
      simp [hC, hη, h0]
  have hfinal := le_of_tendsto_of_tendsto' (hAlim.add hBlim) hClim hineq
  rw [add_zero] at hfinal
  rw [dirichletEnergy, gaussL2, integral_gaussMeasure, integral_gaussMeasure]
  simp_rw [mul_comm (gaussWeight _)]
  exact hfinal

end Sperner
