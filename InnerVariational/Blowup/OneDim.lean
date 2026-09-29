/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Blowup.ExplicitForm
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Data.Real.Hom
public import GMTFoundations.Defs.Sobolev

/-!
# Theorem 5.3, step (c): rigidity of the one-dimensional profile

Step (c) of the proof of Theorem 5.3 of Kriventsov–Weiss (full reference below), the paragraph
containing equation (5.15), passes the domain variation identity to the limit `v = β ⟪ν, x⟫^N`
(on a side where `β ≠ 0`). With
the test field `ξ = φ ν`, the identity reads `∫ ⟪ν, x⟫^{2N-2} ∂_ν φ = 0` for all
`φ ∈ C_c^∞(U)`. Integrating by parts gives `(2N − 2) ∫ ⟪ν, x⟫^{2N-3} φ = 0`, and a nonnegative
bump `φ` shows `N = 1`.

With `ξ = φ ν` no Fubini argument in the tangential directions is needed: for `∇v = h' ν`,
`|∇v|² div ξ − 2⟪∇v, Dξ ∇v⟫ = −h'² ∂_ν φ`.

## Main results

* `eq_zero_of_integral_inner_rpow_mul_fderiv_eq_zero`: if `∫ ⟪ν, x⟫^p ∂_νφ = 0` for all
  `φ ∈ C_c^∞(U)`, `U ⊆ {⟪ν, x⟫ > 0}` open and nonempty, then `p = 0`.
* `eq_one_of_integral_inner_rpow_mul_fderiv_eq_zero`: the case `p = 2N − 2`, giving `N = 1`.
* `eq_one_of_weakEuler_of_domainVariation`: Theorem 5.3, steps (a) + (c) for the blow-up limit. From
  the weak Euler identity, the vanishing tangential gradient, `v ≢ 0`, and the limit domain
  variation identity for `ξ = φ ν`, conclude `N = 1`.

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

/-- The derivative of `x ↦ ⟪ν, x⟫^p` where `⟪ν, x⟫ > 0`. -/
theorem hasFDerivAt_inner_rpow {ν x : Rn n} (hx : 0 < ⟪ν, x⟫) (p : ℝ) :
    HasFDerivAt (fun y : Rn n => ⟪ν, y⟫ ^ p) ((p * ⟪ν, x⟫ ^ (p - 1)) • innerSL ℝ ν) x :=
  (Real.hasDerivAt_rpow_const (Or.inl hx.ne')).comp_hasFDerivAt x (innerSL ℝ ν).hasFDerivAt

/-- `x ↦ ⟪ν, x⟫^p` is smooth where `⟪ν, x⟫ > 0`. -/
theorem contDiffOn_inner_rpow {U : Set (Rn n)} {ν : Rn n} (hUν : ∀ x ∈ U, 0 < ⟪ν, x⟫) (p : ℝ)
    {k : WithTop ℕ∞} : ContDiffOn ℝ k (fun y : Rn n => ⟪ν, y⟫ ^ p) U := fun x hx =>
  ((Real.contDiffAt_rpow_const_of_ne (hUν x hx).ne').comp x
    (innerSL ℝ ν).contDiff.contDiffAt).contDiffWithinAt

/-- **Rigidity of the one-dimensional profile.** Let `U` be a nonempty open set with
`⟪ν, x⟫ > 0` on `U`, where `‖ν‖ = 1`. If `∫ ⟪ν, x⟫^p ∂_νφ = 0` for every `φ ∈ C_c^∞(U)`, then
`p = 0`. -/
theorem eq_zero_of_integral_inner_rpow_mul_fderiv_eq_zero {U : Set (Rn n)} (hU : IsOpen U)
    (hUne : U.Nonempty) {ν : Rn n} (hν : ‖ν‖ = 1) (hUν : ∀ x ∈ U, 0 < ⟪ν, x⟫) {p : ℝ}
    (h : ∀ φ : Rn n → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∫ x, ⟪ν, x⟫ ^ p * fderiv ℝ φ x ν = 0) : p = 0 := by
  obtain ⟨x₀, hx₀⟩ := hUne
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU x₀ hx₀
  let b : ContDiffBump x₀ := ⟨r / 4, r / 2, by positivity, by linarith⟩
  set φ : Rn n → ℝ := ⇑b with hφ_def
  have hφs : tsupport φ ⊆ U := by
    rw [hφ_def, b.tsupport_eq]
    exact (closedBall_subset_ball (by simp only [b]; linarith)).trans hrU
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := b.contDiff
  have hK : IsCompact (tsupport φ) := b.hasCompactSupport
  set η : Rn n → ℝ := fun y => ⟪ν, y⟫ ^ p with hη_def
  have hη : ContDiffOn ℝ (⊤ : ℕ∞) η U := contDiffOn_inner_rpow hUν p
  set ψ : Rn n → ℝ := fun x => η x * φ x with hψ_def
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := contDiff_mul_of_contDiffOn_of_tsupport_subset hU hη hφ hφs
  have hψs : tsupport ψ ⊆ tsupport φ := tsupport_mul_subset_right
  have hψc : HasCompactSupport ψ := hK.of_isClosed_subset (isClosed_tsupport ψ) hψs
  -- `∫ ∂_ν ψ = 0`.
  have hint0 : ∫ x, fderiv ℝ ψ x ν = 0 := by
    have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
      (f := fun _ : Rn n => (1 : ℝ)) (g := ψ) (v := ν) (by simp)
      (by
        simpa using ((hψ.continuous_fderiv (by simp)).clm_apply
          continuous_const).integrable_of_hasCompactSupport (hψc.fderiv_apply (𝕜 := ℝ) ν))
      (by simpa using hψ.continuous.integrable_of_hasCompactSupport hψc)
      (fun x _ => differentiableAt_const _) (fun x _ => hψ.differentiable (by simp) x)
    simpa using hibp
  -- The product rule, valid everywhere since `φ` vanishes near every point outside `U`.
  have hpt : ∀ x, fderiv ℝ ψ x ν = η x * fderiv ℝ φ x ν + fderiv ℝ η x ν * φ x := by
    intro x
    by_cases hx : x ∈ U
    · have hd : HasFDerivAt ψ (η x • fderiv ℝ φ x + φ x • fderiv ℝ η x) x :=
        ((hη.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt.mul
          ((hφ.differentiable (by simp)) x).hasFDerivAt
      rw [hd.fderiv]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      ring
    · have hxφ : x ∉ tsupport φ := fun h => hx (hφs h)
      rw [fderiv_of_notMem_tsupport ℝ (fun h => hxφ (hψs h)), fderiv_of_notMem_tsupport ℝ hxφ,
        image_eq_zero_of_notMem_tsupport hxφ]
      simp
  have hdφ : Continuous fun x => fderiv ℝ φ x ν :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdφs : tsupport (fun x => fderiv ℝ φ x ν) ⊆ tsupport φ := tsupport_fderiv_apply_subset ℝ ν
  have hc1 : Continuous fun x => η x * fderiv ℝ φ x ν :=
    contDiff_zero.1 (contDiff_mul_of_contDiffOn_of_tsupport_subset hU
      (contDiffOn_inner_rpow (k := 0) hUν p) (contDiff_zero.2 hdφ) (hdφs.trans hφs))
  have hs1 : HasCompactSupport fun x => η x * fderiv ℝ φ x ν :=
    hK.of_isClosed_subset (isClosed_tsupport _) (tsupport_mul_subset_right.trans hdφs)
  have hDc : ContinuousOn (fun x => fderiv ℝ η x ν) U :=
    (hη.continuousOn_fderiv_of_isOpen hU (by simp)).clm_apply continuousOn_const
  have hc2 : Continuous fun x => fderiv ℝ η x ν * φ x :=
    contDiff_zero.1 (contDiff_mul_of_contDiffOn_of_tsupport_subset hU
      (contDiffOn_zero.2 hDc) (contDiff_zero.2 hφ.continuous) hφs)
  have hs2 : HasCompactSupport fun x => fderiv ℝ η x ν * φ x :=
    hK.of_isClosed_subset (isClosed_tsupport _) tsupport_mul_subset_right
  have h0 : ∫ x, η x * fderiv ℝ φ x ν = 0 := h φ hφ b.hasCompactSupport hφs
  have hsplit : ∫ x, fderiv ℝ ψ x ν =
      (∫ x, η x * fderiv ℝ φ x ν) + ∫ x, fderiv ℝ η x ν * φ x := by
    simp_rw [hpt]
    exact integral_add (hc1.integrable_of_hasCompactSupport hs1)
      (hc2.integrable_of_hasCompactSupport hs2)
  rw [hint0, h0, zero_add] at hsplit
  -- `∂_ν η = p ⟪ν, x⟫^{p-1}` on `U`.
  have hD : ∀ x, fderiv ℝ η x ν * φ x = p * (⟪ν, x⟫ ^ (p - 1) * φ x) := by
    intro x
    by_cases hx : x ∈ U
    · rw [(hasFDerivAt_inner_rpow (hUν x hx) p).fderiv]
      simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul,
        real_inner_self_eq_norm_sq, hν]
      ring
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hφs h))]
      simp
  simp_rw [hD] at hsplit
  rw [integral_const_mul] at hsplit
  -- `∫ ⟪ν, x⟫^{p-1} φ > 0`.
  have hg : Continuous fun x => ⟪ν, x⟫ ^ (p - 1) * φ x :=
    contDiff_zero.1 (contDiff_mul_of_contDiffOn_of_tsupport_subset hU
      (contDiffOn_inner_rpow (k := 0) hUν (p - 1)) (contDiff_zero.2 hφ.continuous) hφs)
  have hgs : HasCompactSupport fun x => ⟪ν, x⟫ ^ (p - 1) * φ x :=
    hK.of_isClosed_subset (isClosed_tsupport _) tsupport_mul_subset_right
  have hgnn : 0 ≤ fun x => ⟪ν, x⟫ ^ (p - 1) * φ x := by
    intro x
    by_cases hx : x ∈ U
    · exact mul_nonneg (Real.rpow_nonneg (hUν x hx).le _) b.nonneg
    · simp only [Pi.zero_apply]
      rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hφs h)), mul_zero]
  have hgx₀ : ⟪ν, x₀⟫ ^ (p - 1) * φ x₀ ≠ 0 := by
    have hb : φ x₀ = 1 :=
      b.one_of_mem_closedBall (mem_closedBall_self (by simp only [b]; positivity))
    rw [hb, mul_one]
    exact (Real.rpow_pos_of_pos (hUν x₀ hx₀) _).ne'
  have hpos := hg.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := volume) hgs hgnn hgx₀
  exact (mul_eq_zero.1 hsplit.symm).resolve_right hpos.ne'

/-- **Theorem 5.3, step (c), conclusion** (equation (5.15) and the sentence after it). If
`∫ ⟪ν, x⟫^{2N-2} ∂_νφ = 0` for every `φ ∈ C_c^∞(U)`, with `U ⊆ {⟪ν, x⟫ > 0}` open and nonempty
and `‖ν‖ = 1`, then `N = 1`. -/
theorem eq_one_of_integral_inner_rpow_mul_fderiv_eq_zero {U : Set (Rn n)} (hU : IsOpen U)
    (hUne : U.Nonempty) {ν : Rn n} (hν : ‖ν‖ = 1) (hUν : ∀ x ∈ U, 0 < ⟪ν, x⟫) {N : ℝ}
    (h : ∀ φ : Rn n → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∫ x, ⟪ν, x⟫ ^ (2 * N - 2) * fderiv ℝ φ x ν = 0) : N = 1 := by
  have := eq_zero_of_integral_inner_rpow_mul_fderiv_eq_zero hU hUne hν hUν h
  linarith

/-- **Theorem 5.3, step (c), one side.** Let `U = A ∩ {⟪μ, x⟫ > 0}` be nonempty, `‖μ‖ = 1`, and
suppose that a.e. on `A` the weak Euler identity `⟪G, x⟫ = N v` and `G = ⟪G, μ⟫ μ` hold, with
`v = β ⟪μ, x⟫^N` on `{⟪μ, x⟫ > 0}` and `N β ≠ 0`. If the limit domain variation identity
`∫_A ⟪G, μ⟫² ∂_μ φ = 0` holds for `φ ∈ C_c^∞(A)`, then `N = 1`. -/
theorem eq_one_of_explicit_side {A : Set (Rn n)} (hA : IsOpen A) {μ : Rn n} (hμ : ‖μ‖ = 1)
    {N β : ℝ} (hNβ : N * β ≠ 0) {v : Rn n → ℝ} {G : Rn n → Rn n}
    (hne : (A ∩ {x | 0 < ⟪μ, x⟫}).Nonempty)
    (hside : ∀ᵐ x ∂(volume.restrict A), 0 < ⟪μ, x⟫ → v x = β * ⟪μ, x⟫ ^ N)
    (heuler : ∀ᵐ x ∂(volume.restrict A), ⟪G x, x⟫ = N * v x)
    (htan : ∀ᵐ x ∂(volume.restrict A), G x = ⟪G x, μ⟫ • μ)
    (hdv : ∀ φ : Rn n → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ A ∩ {x | 0 < ⟪μ, x⟫} → ∫ x in A, ⟪G x, μ⟫ ^ 2 * fderiv ℝ φ x μ = 0) :
    N = 1 := by
  have hUo : IsOpen (A ∩ {x | 0 < ⟪μ, x⟫}) :=
    hA.inter (isOpen_lt continuous_const (continuous_const.inner continuous_id))
  refine eq_one_of_integral_inner_rpow_mul_fderiv_eq_zero hUo hne hμ (fun x hx => hx.2) ?_
  intro φ hφ hφc hφU
  have hφA : tsupport φ ⊆ A := hφU.trans inter_subset_left
  have hdφ0 : ∀ x, x ∉ tsupport φ → fderiv ℝ φ x μ = 0 := fun x hx => by
    rw [fderiv_of_notMem_tsupport ℝ hx]
    rfl
  have hae : ∀ᵐ x ∂(volume.restrict A), ⟪G x, μ⟫ ^ 2 * fderiv ℝ φ x μ =
      (N * β) ^ 2 * (⟪μ, x⟫ ^ (2 * N - 2) * fderiv ℝ φ x μ) := by
    filter_upwards [hside, heuler, htan] with x hs he ht
    by_cases hx : x ∈ tsupport φ
    · have hxp : 0 < ⟪μ, x⟫ := (hφU hx).2
      have hGx : ⟪G x, x⟫ = ⟪G x, μ⟫ * ⟪μ, x⟫ := by
        conv_lhs => rw [ht]
        rw [inner_smul_left]
        simp
      rw [hs hxp, hGx] at he
      have hGμ : ⟪G x, μ⟫ = N * β * ⟪μ, x⟫ ^ (N - 1) := by
        rw [← mul_div_cancel_right₀ ⟪G x, μ⟫ hxp.ne', he, Real.rpow_sub_one hxp.ne']
        ring
      have hpow : ⟪μ, x⟫ ^ (2 * N - 2) = (⟪μ, x⟫ ^ (N - 1)) ^ 2 := by
        rw [show 2 * N - 2 = (N - 1) * 2 by ring, Real.rpow_mul hxp.le, Real.rpow_two]
      rw [hGμ, hpow]
      ring
    · rw [hdφ0 x hx]
      ring
  have h1 := hdv φ hφ hφc hφU
  rw [integral_congr_ae hae, integral_const_mul] at h1
  have h2 : ∫ x in A, ⟪μ, x⟫ ^ (2 * N - 2) * fderiv ℝ φ x μ = 0 :=
    (mul_eq_zero.1 h1).resolve_left (pow_ne_zero 2 hNβ)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_] at h2
  · exact h2
  · rw [hdφ0 x fun h => hx (hφA h), mul_zero]

/-- **Theorem 5.3, steps (a) + (c) for the blow-up limit** (with the corrected argument for step (a)
of `Blowup/ExplicitForm.lean`). Let
`A = B_{r₂} \ B̄_{r₁}` with `0 ≤ r₁ < r₂`, `‖ν‖ = 1`, `N ≠ 0`. Let `v` have weak gradient `G`
on `A` (so `v, G ∈ L¹_loc(A)`) such that, a.e. on `A`,
* the weak Euler identity `⟪G, x⟫ = N v` holds (Lemma 5.1 (3)), and
* the tangential gradient vanishes, `G = ⟪G, ν⟫ ν` (the hypothesis of Theorem 5.3 in the limit).

If `v` is not a.e. zero on `A`, and the limit of the domain variation identity holds for the test
fields `ξ = φ ν`, namely `∫_A ⟪G, ν⟫² ∂_ν φ = 0` for all `φ ∈ C_c^∞(A \ {⟪ν, x⟫ = 0})` (this
is the first equality of (5.15) for `ξ = φ ν`, on the sets `U ⋐ A \ {x_n = 0}` of the proof of
Theorem 5.3), then `N = 1`. -/
theorem eq_one_of_weakEuler_of_domainVariation {r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁) (hr : r₁ < r₂)
    {ν : Rn n} (hν : ‖ν‖ = 1) {N : ℝ} (hN : N ≠ 0) {v : Rn n → ℝ} {G : Rn n → Rn n}
    (hW : GMTFoundations.HasWeakGradient (ball 0 r₂ \ closedBall 0 r₁) v G)
    (heuler : ∀ᵐ x ∂(volume.restrict (ball 0 r₂ \ closedBall 0 r₁)), ⟪G x, x⟫ = N * v x)
    (htan : ∀ᵐ x ∂(volume.restrict (ball 0 r₂ \ closedBall 0 r₁)), G x = ⟪G x, ν⟫ • ν)
    (hv0 : ¬ v =ᵐ[volume.restrict (ball 0 r₂ \ closedBall 0 r₁)] 0)
    (hdv : ∀ φ : Rn n → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ (ball 0 r₂ \ closedBall 0 r₁) ∩ {x | ⟪ν, x⟫ ≠ 0} →
      ∫ x in ball 0 r₂ \ closedBall 0 r₁, ⟪G x, ν⟫ ^ 2 * fderiv ℝ φ x ν = 0) : N = 1 := by
  set A : Set (Rn n) := ball 0 r₂ \ closedBall 0 r₁ with hA_def
  have hAo : IsOpen A := isOpen_ball.sdiff isClosed_closedBall
  obtain ⟨βp, βm, hβ⟩ := exists_ae_eq_explicit_form hr₁ hW heuler htan
  have hne : ∀ μ : Rn n, ‖μ‖ = 1 → (A ∩ {x | 0 < ⟪μ, x⟫}).Nonempty := by
    intro μ hμ
    have hc : 0 < (r₁ + r₂) / 2 := by linarith
    refine ⟨((r₁ + r₂) / 2) • μ, ⟨?_, ?_⟩, ?_⟩
    · rw [mem_ball_zero_iff, norm_smul, hμ, Real.norm_eq_abs, abs_of_pos hc, mul_one]
      linarith
    · rw [mem_closedBall_zero_iff, norm_smul, hμ, Real.norm_eq_abs, abs_of_pos hc, mul_one,
        not_le]
      linarith
    · simp only [mem_setOf_eq, inner_smul_right, real_inner_self_eq_norm_sq, hμ, one_pow,
        mul_one]
      exact hc
  have hνm : ‖-ν‖ = 1 := by rw [norm_neg, hν]
  by_cases hp : βp = 0
  · by_cases hm : βm = 0
    · exfalso
      apply hv0
      have hν0 : ν ≠ 0 := by
        rintro rfl
        simp at hν
      have hnull : ∀ᵐ x ∂(volume.restrict A), x ∉ {x : Rn n | ⟪ν, x⟫ = 0} :=
        ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 (volume_inner_eq_zero hν0))
      filter_upwards [hβ, hnull] with x hx hx0
      rcases lt_or_gt_of_ne (show ⟪ν, x⟫ ≠ 0 from hx0) with h | h
      · simp [hx.2 h, hm]
      · simp [hx.1 h, hp]
    · refine eq_one_of_explicit_side hAo hνm (mul_ne_zero hN hm) (hne _ hνm) ?_ heuler ?_ ?_
      · filter_upwards [hβ] with x hx hxp
        rw [inner_neg_left] at hxp ⊢
        exact hx.2 (by linarith)
      · filter_upwards [htan] with x hx
        rw [inner_neg_right, neg_smul_neg]
        exact hx
      · intro φ hφ hφc hφA
        have := hdv φ hφ hφc fun x hx => ⟨(hφA hx).1,
          ne_of_lt (by simpa [inner_neg_left] using (hφA hx).2)⟩
        simp only [inner_neg_right, neg_sq, map_neg, mul_neg, integral_neg, this, neg_zero]
  · exact eq_one_of_explicit_side hAo hν (mul_ne_zero hN hp) (hne ν hν)
      (by filter_upwards [hβ] with x hx using hx.1) heuler htan fun φ hφ hφc hφA =>
        hdv φ hφ hφc fun x hx => ⟨(hφA hx).1, (hφA hx).2.ne'⟩

end InnerVariational
