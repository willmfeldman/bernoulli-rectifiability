/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Blowup.Constancy
public import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Algebra.Ring.IsFormallyReal
import InnerVariational.Sobolev.WeakGradient
import GMTFoundations.Sobolev.Lattice
import InnerVariational.Sobolev.Lipschitz
public import GMTFoundations.Defs.Sobolev

/-!
# Theorem 5.3, step (a): the explicit form of the blow-up limit

Step (a), the first paragraph of the proof of Theorem 5.3 of Kriventsov–Weiss (full reference
below), reads: `v` is independent of `x'` on `A = B_1 \ B̄_{1/2}`, so by homogeneity
`v = β₊ (x_n)₊^N + β₋ (x_n)₋^N`. The paper calls the first claim "immediate from the assumption".
The assumption gives `∂_i v = 0` a.e. on `A` for `i < n`, which yields independence of `x'` only
on connected components of the `x'`-slices of `A`. For `n = 2` the implication
`∂_i v = 0 ⇒ independence` does not hold on its own: `v(x_1, x_2) = sgn(x_1) ψ(x_2)`, with
`0 ≢ ψ ∈ C_c^∞(-1/2, 1/2)`, has `∂_1 v = 0` on `A` but depends on `x_1`. It follows from the
homogeneity of `v` and the connectedness of the half-annuli, which is how it is proved here.
This file proves the explicit form directly from the weak Euler identity
`⟪∇v, x⟫ = N v` and the vanishing of the tangential gradient `∇v = ⟪∇v, ν⟫ ν`. On a connected
open set `U ⊆ {⟪ν, x⟫ > 0}` the function `⟪ν, x⟫^{-N} v` has zero weak gradient, so it is a.e.
constant.

## Main results

* `contDiff_mul_of_contDiffOn_of_tsupport_subset`: a function smooth on an open set, times a
  smooth function supported inside that set, is smooth.
* `hasWeakGradient_mul_contDiffOn`: weak product rule for a factor that is smooth only on
  the open domain.
* `exists_ae_eq_mul_inner_rpow`: the explicit form `v = β ⟪ν, x⟫^N` a.e. on `U`.
* `isPreconnected_ball_diff_closedBall_inter_inner_pos`: half-annuli are connected.
* `exists_ae_eq_explicit_form`: Theorem 5.3, step (a) on the annulus,
  `v = β₊ ⟪ν,x⟫₊^N + β₋ ⟪ν,x⟫₋^N`.

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

/-- A function smooth on an open set `U`, times a smooth function with topological support in
`U`, is smooth everywhere. -/
theorem contDiff_mul_of_contDiffOn_of_tsupport_subset {U : Set (Rn n)} (hU : IsOpen U)
    {η φ : Rn n → ℝ} {k : WithTop ℕ∞} (hη : ContDiffOn ℝ k η U) (hφ : ContDiff ℝ k φ)
    (hφU : tsupport φ ⊆ U) : ContDiff ℝ k (fun x => η x * φ x) := by
  refine contDiff_iff_contDiffAt.2 fun x => ?_
  by_cases hx : x ∈ U
  · exact (hη.contDiffAt (hU.mem_nhds hx)).mul hφ.contDiffAt
  · have hx' : x ∉ tsupport φ := fun h => hx (hφU h)
    have hev : (fun x => η x * φ x) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx'] with y hy
      rw [hy, Pi.zero_apply, mul_zero]
    exact contDiffAt_const.congr_of_eventuallyEq hev

/-- `v · h` is integrable on `U` when `v ∈ L¹_loc(U)` and `h` is continuous on a compact `K ⊆ U`
and vanishes on `U \ K`. -/
theorem integrableOn_mul_of_eqOn_zero {U K : Set (Rn n)} (hU : MeasurableSet U) (hK : IsCompact K)
    (hKU : K ⊆ U) {v h : Rn n → ℝ} (hv : LocallyIntegrableOn v U) (hh : ContinuousOn h K)
    (h0 : ∀ x ∈ U \ K, h x = 0) : IntegrableOn (fun x => v x * h x) U :=
  ((hv.integrableOn_compact_subset hKU hK).mul_continuousOn hh hK).of_forall_sdiff_eq_zero hU
    fun x hx => by simp [h0 x hx]

/-- **Weak product rule with a locally smooth factor.** If `G` is the weak gradient of `v` on the
open set `U` and `η` is smooth on `U` (no global bound needed), then `η G + v ∇η` is the weak
gradient of `η v` on `U`. -/
theorem hasWeakGradient_mul_contDiffOn {U : Set (Rn n)} (hU : IsOpen U) {v η : Rn n → ℝ}
    {G : Rn n → Rn n} (hv : GMTFoundations.HasWeakGradient U v G)
    (hη : ContDiffOn ℝ (⊤ : ℕ∞) η U) :
    GMTFoundations.HasWeakGradient U (fun x => η x * v x)
      (fun x => η x • G x + v x • gradient η x) := by
  have hvl : LocallyIntegrableOn v U := hv.1
  have hGl : LocallyIntegrableOn G U := hv.2.1
  have hηc : ContinuousOn η U := hη.continuousOn
  have hgη : ContinuousOn (gradient η) U :=
    (InnerProductSpace.toDual ℝ (Rn n)).symm.continuous.comp_continuousOn
      (hη.continuousOn_fderiv_of_isOpen hU (by simp))
  refine HasWeakGradient.of_single (hvl.continuousOn_mul hηc hU.isLocallyClosed)
    ((hGl.continuousOn_smul hU.isLocallyClosed hηc).add
      (hvl.smul_continuousOn hU.isLocallyClosed hgη)) fun i φ hφ hφc hφU => ?_
  have hcoord : ∀ x, (η x • G x + v x • gradient η x) i =
      η x * G x i + fderiv ℝ η x (EuclideanSpace.single i 1) * v x := by
    intro x
    rw [PiLp.add_apply, PiLp.smul_apply, PiLp.smul_apply, smul_eq_mul, smul_eq_mul,
      gradient_apply_eq_fderiv, mul_comm (v x)]
  simp only [hcoord]
  have hK : IsCompact (tsupport φ) := hφc
  have hηd : ∀ x ∈ U, DifferentiableAt ℝ η x := fun x hx =>
    (hη.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  set ψ : Rn n → ℝ := fun x => η x * φ x with hψ_def
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := contDiff_mul_of_contDiffOn_of_tsupport_subset hU hη hφ hφU
  have hψs : tsupport ψ ⊆ tsupport φ := tsupport_mul_subset_right
  have hψc : HasCompactSupport ψ := hK.of_isClosed_subset (isClosed_tsupport ψ) hψs
  have hweak := HasWeakGradient.single hv i hψ hψc (hψs.trans hφU)
  have hpt : ∀ x ∈ U, fderiv ℝ ψ x (EuclideanSpace.single i 1) =
      η x * fderiv ℝ φ x (EuclideanSpace.single i 1) +
        φ x * fderiv ℝ η x (EuclideanSpace.single i 1) := by
    intro x hx
    have hd : HasFDerivAt ψ (η x • fderiv ℝ φ x + φ x • fderiv ℝ η x) x :=
      (hηd x hx).hasFDerivAt.mul (hφd x).hasFDerivAt
    rw [hd.fderiv]
    simp [smul_eq_mul]
  have hφ0 : ∀ x ∈ U \ tsupport φ, φ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport hx.2
  have hI1 : IntegrableOn (fun x => v x * fderiv ℝ ψ x (EuclideanSpace.single i 1)) U :=
    integrableOn_mul_of_eqOn_zero hU.measurableSet hK hφU hvl
      ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const).continuousOn
      fun x hx => by
        rw [fderiv_of_notMem_tsupport ℝ fun h => hx.2 (hψs h)]
        rfl
  have hdη : ContinuousOn (fun x => fderiv ℝ η x (EuclideanSpace.single i 1)) U :=
    (hη.continuousOn_fderiv_of_isOpen hU (by simp)).clm_apply continuousOn_const
  have hI2 : IntegrableOn
      (fun x => v x * (φ x * fderiv ℝ η x (EuclideanSpace.single i 1))) U :=
    integrableOn_mul_of_eqOn_zero hU.measurableSet hK hφU hvl
      (hφ.continuous.continuousOn.mul (hdη.mono hφU)) fun x hx => by rw [hφ0 x hx, zero_mul]
  have hGil : LocallyIntegrableOn (fun x => G x i) U := by
    simpa [EuclideanSpace.inner_single_right] using
      GMTFoundations.locallyIntegrableOn_inner_apply hGl (EuclideanSpace.single i 1)
  have hI3 : IntegrableOn (fun x => G x i * ψ x) U :=
    integrableOn_mul_of_eqOn_zero hU.measurableSet hK hφU hGil hψ.continuous.continuousOn
      fun x hx => by simp only [ψ, hφ0 x hx, mul_zero]
  have hL : ∫ x in U, η x * v x * fderiv ℝ φ x (EuclideanSpace.single i 1) =
      ∫ x in U, (v x * fderiv ℝ ψ x (EuclideanSpace.single i 1) -
        v x * (φ x * fderiv ℝ η x (EuclideanSpace.single i 1))) := by
    refine setIntegral_congr_fun hU.measurableSet fun x hx => ?_
    simp only [hpt x hx]
    ring
  have hR : ∫ x in U, (η x * G x i + fderiv ℝ η x (EuclideanSpace.single i 1) * v x) * φ x =
      (∫ x in U, G x i * ψ x) +
        ∫ x in U, v x * (φ x * fderiv ℝ η x (EuclideanSpace.single i 1)) := by
    rw [← integral_add hI3 hI2]
    refine setIntegral_congr_fun hU.measurableSet fun x _ => ?_
    simp only [ψ]
    ring
  rw [hL, integral_sub hI1 hI2, hweak, hR]
  ring

/-- **Theorem 5.3, step (a), explicit form on one side** (corrected argument, see the module
docstring).
Let `U` be a connected open set on which `⟪ν, x⟫ > 0`, and let `v` have weak gradient `G` on `U`
(so `v, G ∈ L¹_loc(U)`) satisfying, a.e. on `U`,
* the weak Euler identity `⟪G, x⟫ = N v` (Lemma 5.1 (3), as at the end of its proof), and
* vanishing tangential gradient `G = ⟪G, ν⟫ ν` (the limit of the hypothesis of Theorem 5.3).

Then `v = β ⟪ν, x⟫^N` a.e. on `U` for a constant `β`. Apply it to the two halves
`A_± = A ∩ {±⟪ν, x⟫ > 0}` of the annulus (with `ν` and `-ν`), which are connected for all
`n ≥ 2`. -/
theorem exists_ae_eq_mul_inner_rpow {U : Set (Rn n)} (hU : IsOpen U) (hUc : IsPreconnected U)
    {ν : Rn n} (hUν : ∀ x ∈ U, 0 < ⟪ν, x⟫) {N : ℝ} {v : Rn n → ℝ} {G : Rn n → Rn n}
    (hW : GMTFoundations.HasWeakGradient U v G)
    (heuler : ∀ᵐ x ∂(volume.restrict U), ⟪G x, x⟫ = N * v x)
    (htan : ∀ᵐ x ∂(volume.restrict U), G x = ⟪G x, ν⟫ • ν) :
    ∃ β : ℝ, ∀ᵐ x ∂(volume.restrict U), v x = β * ⟪ν, x⟫ ^ N := by
  set η : Rn n → ℝ := fun x => ⟪ν, x⟫ ^ (-N) with hη_def
  have hlin : ∀ x, HasFDerivAt (fun y : Rn n => ⟪ν, y⟫) (innerSL ℝ ν) x := fun x =>
    (innerSL ℝ ν).hasFDerivAt
  have hηfd : ∀ x ∈ U, HasFDerivAt η ((-N * ⟪ν, x⟫ ^ (-N - 1)) • innerSL ℝ ν) x := fun x hx =>
    (Real.hasDerivAt_rpow_const (Or.inl (hUν x hx).ne')).comp_hasFDerivAt x (hlin x)
  have hη : ContDiffOn ℝ (⊤ : ℕ∞) η U := fun x hx =>
    ((Real.contDiffAt_rpow_const_of_ne (hUν x hx).ne').comp x
      (innerSL ℝ ν).contDiff.contDiffAt).contDiffWithinAt
  -- `w = ⟪ν, x⟫^{-N} v` has zero weak gradient on `U`.
  have hW0 : GMTFoundations.HasWeakGradient U (fun x => η x * v x) (fun _ => (0 : Rn n)) := by
    refine (hasWeakGradient_mul_contDiffOn hU hW hη).congr_ae ?_
    filter_upwards [heuler, htan, self_mem_ae_restrict hU.measurableSet] with x he ht hx
    ext i
    rw [PiLp.add_apply, PiLp.smul_apply, PiLp.smul_apply, smul_eq_mul, smul_eq_mul,
      gradient_apply_eq_fderiv, mul_comm (v x)]
    have hx0 : 0 < ⟪ν, x⟫ := hUν x hx
    rw [(hηfd x hx).fderiv]
    have hGi : G x i = ⟪G x, ν⟫ * ν i := by
      conv_lhs => rw [ht]
      simp
    have hGx : ⟪G x, x⟫ = ⟪G x, ν⟫ * ⟪ν, x⟫ := by
      conv_lhs => rw [ht]
      rw [inner_smul_left]
      simp
    have hrp : ⟪ν, x⟫ ^ (-N - 1) = ⟪ν, x⟫ ^ (-N) / ⟪ν, x⟫ := Real.rpow_sub_one hx0.ne' _
    simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, hGi, hrp,
      EuclideanSpace.inner_single_right, η, PiLp.zero_apply]
    rw [hGx] at he
    field_simp
    simp only [conj_trivial]
    linear_combination (⟪ν, x⟫ ^ (-N) * ν i) * he
  obtain ⟨c, hc⟩ := exists_ae_eq_const_of_hasWeakGrad_zero hU hUc hW0
  refine ⟨c, ?_⟩
  filter_upwards [hc, self_mem_ae_restrict hU.measurableSet] with x hx hxU
  have hx0 : 0 < ⟪ν, x⟫ := hUν x hxU
  have h1 : ⟪ν, x⟫ ^ N * ⟪ν, x⟫ ^ (-N) = 1 := by
    rw [← Real.rpow_add hx0, add_neg_cancel, Real.rpow_zero]
  simp only [η] at hx
  calc v x = (⟪ν, x⟫ ^ N * ⟪ν, x⟫ ^ (-N)) * v x := by rw [h1, one_mul]
    _ = ⟪ν, x⟫ ^ N * (⟪ν, x⟫ ^ (-N) * v x) := by ring
    _ = c * ⟪ν, x⟫ ^ N := by rw [hx, mul_comm]

/-- The open half-annulus `{r₁ < ‖x‖ < r₂, ⟪ν, x⟫ > 0}` is preconnected (for `0 ≤ r₁`). It is the
image of `(r₁, r₂) × {⟪ν, z⟫ > 0}` under `(r, z) ↦ r z/‖z‖`. -/
theorem isPreconnected_ball_diff_closedBall_inter_inner_pos (ν : Rn n) {r₁ r₂ : ℝ}
    (hr₁ : 0 ≤ r₁) :
    IsPreconnected ((ball (0 : Rn n) r₂ \ closedBall 0 r₁) ∩ {x | 0 < ⟪ν, x⟫}) := by
  set H : Set (Rn n) := {z | 0 < ⟪ν, z⟫} with hH_def
  have hH : IsPreconnected H :=
    (convex_halfSpace_gt (innerₛₗ ℝ ν).isLinear 0).isPreconnected
  have hne : ∀ z ∈ H, z ≠ 0 := by
    rintro z hz rfl
    simp [H] at hz
  set f : ℝ × Rn n → Rn n := fun p => (p.1 / ‖p.2‖) • p.2 with hf_def
  have hcont : ContinuousOn f (Ioo r₁ r₂ ×ˢ H) := by
    refine ContinuousOn.smul
      (continuousOn_fst.div (continuous_norm.comp continuous_snd).continuousOn
        fun p hp => norm_ne_zero_iff.2 (hne _ hp.2)) continuousOn_snd
  have himage : f '' (Ioo r₁ r₂ ×ˢ H) = (ball (0 : Rn n) r₂ \ closedBall 0 r₁) ∩ H := by
    ext x
    constructor
    · rintro ⟨⟨r, z⟩, ⟨⟨hr1, hr2⟩, hz⟩, rfl⟩
      have hz0 : ‖z‖ ≠ 0 := norm_ne_zero_iff.2 (hne z hz)
      have hr0 : 0 < r := lt_of_le_of_lt hr₁ hr1
      have hnorm : ‖f (r, z)‖ = r := by
        simp only [f, norm_smul, Real.norm_eq_abs, abs_div, abs_norm, abs_of_pos hr0]
        field_simp
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [mem_ball_zero_iff, hnorm]; exact hr2
      · rw [mem_closedBall_zero_iff, hnorm, not_le]; exact hr1
      · simp only [H, mem_ofPred_eq, f, inner_smul_right]
        exact mul_pos (div_pos hr0 (norm_pos_iff.2 (hne z hz))) hz
    · rintro ⟨⟨hx2, hx1⟩, hxH⟩
      rw [mem_ball_zero_iff] at hx2
      rw [mem_closedBall_zero_iff, not_le] at hx1
      refine ⟨(‖x‖, x), ⟨⟨hx1, hx2⟩, hxH⟩, ?_⟩
      have hx0 : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 (hne x hxH)
      simp [f, div_self hx0]
  rw [← himage]
  exact (isPreconnected_Ioo.prod hH).image f hcont

/-- The hyperplane `{⟪ν, x⟫ = 0}` is Lebesgue-null for `ν ≠ 0`. -/
theorem volume_inner_eq_zero {ν : Rn n} (hν : ν ≠ 0) :
    volume {x : Rn n | ⟪ν, x⟫ = 0} = 0 := by
  have hker : {x : Rn n | ⟪ν, x⟫ = 0} = (LinearMap.ker (innerₛₗ ℝ ν) : Set (Rn n)) := by
    ext x
    simp
  rw [hker]
  refine Measure.addHaar_submodule volume _ fun htop => ?_
  have hν' : ν ∈ LinearMap.ker (innerₛₗ ℝ ν) := htop ▸ Submodule.mem_top
  rw [LinearMap.mem_ker, innerₛₗ_apply_apply, real_inner_self_eq_norm_sq] at hν'
  exact hν (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hν'))

/-- **Theorem 5.3, step (a)** (corrected argument, see the module docstring). On the annulus
`A = B_{r₂} \ B̄_{r₁}` (`0 ≤ r₁`), let `v` have weak gradient `G` on `A` (so `v, G ∈ L¹_loc(A)`),
satisfying a.e. on `A` the weak Euler identity `⟪G, x⟫ = N v` and
`G = ⟪G, ν⟫ ν` for a vector `ν`. Then there are constants `βp = β₊`, `βm = β₋` with
`v = β₊ ⟪ν, x⟫^N` a.e. on `{⟪ν, x⟫ > 0}` and `v = β₋ (−⟪ν, x⟫)^N` a.e. on `{⟪ν, x⟫ < 0}`
(for `ν ≠ 0` the hyperplane `{⟪ν, x⟫ = 0}` is null, `volume_inner_eq_zero`). The paper's case
is `ν = e_n`, `r₁ = 1/2`, `r₂ = 1`, where the paper writes the second term as
"`β₋ (x_−)_+^{N_∞}`"; we write `β₋ (x_n)_−^{N_∞}`. -/
theorem exists_ae_eq_explicit_form {r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁) {ν : Rn n} {N : ℝ}
    {v : Rn n → ℝ} {G : Rn n → Rn n}
    (hW : GMTFoundations.HasWeakGradient (ball 0 r₂ \ closedBall 0 r₁) v G)
    (heuler : ∀ᵐ x ∂(volume.restrict (ball 0 r₂ \ closedBall 0 r₁)), ⟪G x, x⟫ = N * v x)
    (htan : ∀ᵐ x ∂(volume.restrict (ball 0 r₂ \ closedBall 0 r₁)), G x = ⟪G x, ν⟫ • ν) :
    ∃ βp βm : ℝ, ∀ᵐ x ∂(volume.restrict (ball 0 r₂ \ closedBall 0 r₁)),
      (0 < ⟪ν, x⟫ → v x = βp * ⟪ν, x⟫ ^ N) ∧ (⟪ν, x⟫ < 0 → v x = βm * (-⟪ν, x⟫) ^ N) := by
  set A : Set (Rn n) := ball 0 r₂ \ closedBall 0 r₁ with hA_def
  have hAo : IsOpen A := isOpen_ball.sdiff isClosed_closedBall
  -- One side, for a direction `μ` with `G = ⟪G, μ⟫ μ`.
  have side : ∀ μ : Rn n, (∀ᵐ x ∂(volume.restrict A), G x = ⟪G x, μ⟫ • μ) →
      ∃ β : ℝ, ∀ᵐ x ∂(volume.restrict (A ∩ {x | 0 < ⟪μ, x⟫})), v x = β * ⟪μ, x⟫ ^ N := by
    intro μ hμ
    have hUo : IsOpen (A ∩ {x | 0 < ⟪μ, x⟫}) :=
      hAo.inter (isOpen_lt continuous_const (continuous_const.inner continuous_id))
    have hsub : A ∩ {x | 0 < ⟪μ, x⟫} ⊆ A := inter_subset_left
    refine exists_ae_eq_mul_inner_rpow hUo
      (isPreconnected_ball_diff_closedBall_inter_inner_pos μ hr₁) (fun x hx => hx.2)
      (HasWeakGradient.mono hW hsub) (ae_restrict_of_ae_restrict_of_subset hsub heuler)
      (ae_restrict_of_ae_restrict_of_subset hsub hμ)
  obtain ⟨βp, hp⟩ := side ν htan
  have htan' : ∀ᵐ x ∂(volume.restrict A), G x = ⟪G x, -ν⟫ • -ν := by
    filter_upwards [htan] with x hx
    rw [inner_neg_right, neg_smul_neg]
    exact hx
  obtain ⟨βm, hm⟩ := side (-ν) htan'
  refine ⟨βp, βm, ?_⟩
  have hmeas : ∀ μ : Rn n, MeasurableSet (A ∩ {x | 0 < ⟪μ, x⟫}) := fun μ =>
    (hAo.inter (isOpen_lt continuous_const (continuous_const.inner continuous_id))).measurableSet
  rw [ae_restrict_iff' (hmeas ν)] at hp
  rw [ae_restrict_iff' (hmeas (-ν))] at hm
  filter_upwards [ae_restrict_of_ae hp, ae_restrict_of_ae hm, self_mem_ae_restrict
    (hAo.measurableSet)] with x hxp hxm hxA
  refine ⟨fun hx => hxp ⟨hxA, hx⟩, fun hx => ?_⟩
  have h' : 0 < ⟪-ν, x⟫ := by rw [inner_neg_left]; linarith
  have := hxm ⟨hxA, h'⟩
  rwa [inner_neg_left] at this

end InnerVariational
