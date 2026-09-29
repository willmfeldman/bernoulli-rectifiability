/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Monotonicity.Limits
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Real.StarOrdered
import InnerVariational.Monotonicity.Blowup
import InnerVariational.Monotonicity.Radial
public import InnerVariational.Defs.Quantities
import InnerVariational.Kernel.BV
import InnerVariational.Kernel.Subharmonic
public import InnerVariational.Defs.VariationalSolution
import InnerVariational.Kernel.Energy
public import InnerVariational.Kernel.Harmonic
import InnerVariational.Kernel.IBP
import InnerVariational.Basic.Polar
import InnerVariational.Basic.LipschitzFTC

/-!
# Homogeneity of blow-ups (Proposition 3.4, last claim)

The last claim of Proposition 3.4 of Kriventsov–Weiss (see the references) and the
corresponding step in the proof of Proposition 3.5. This file contains the analytic tools; the
statements about
blow-ups `u_{x, r_k} → u₀` of a variational solution (`u(x) = 0`, `u₀` Lipschitz and harmonic on
`{u₀ > 0}`, Euler's identity, homogeneity `u₀(t y) = t u₀(y)`) are in `Monotonicity/Density.lean`
(`IsVariationalSolution.blowup_homogeneous` and neighbours).

## Proof

`integral_annulus_sub_inner_sq_le`: integrating the derivative formula of Proposition 3.4 over
`(s, t)` bounds `∫_{B_t(x)∖B_s(x)} (u − ∇u·(y−x))²` by `t^{n+2}/2 (M_x(t) − M_x(s))` (the
polar-coordinates annulus formula). For the rescalings,
`M_0(u_{x,r_k}; t) − M_0(u_{x,r_k}; s) = M_x(r_k t) − M_x(r_k s) → 0`. The strong `L²_loc`
convergence of gradients (`Blowup.lean`) and uniform convergence give
`∫_{B_t∖B_s} (u₀ − ∇u₀·y)² = 0`. On the open set `{u₀ > 0}`, where `u₀` is smooth, this gives
`∇u₀·y = u₀` everywhere (`inner_gradient_eq_of_tendsto_monotonicityM_sub`); on `{u₀ = 0}` both
sides vanish, since `∇u₀ = 0` there.

Homogeneity then follows from Euler's identity by an ODE argument along rays
(`homogeneous_of_inner_gradient_eq`): on `{s > 0 : u₀(s y) > 0}` the function `s ↦ u₀(s y)/s`
has zero derivative, and a connectedness argument on `(0, ∞)` shows it is constant.

Proposition 3.4 lists homogeneity of blow-ups; its proof covers monotonicity and refers to [22]
for the rest. We derive homogeneity after strong `W^{1,2}_loc` convergence of the rescalings, as
in the proof of Proposition 3.5.

`integral_norm_gradient_sq_eq_of_inner_gradient_eq` records the consequence used for (3.10):
`t ∫_{B_t} |∇u₀|² = ∫_{∂B_t} u₀²` for every `t` (the energy identity (3.8) plus Euler's
identity, as in the proof of Proposition 3.5).

## References

* D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
  DOI 10.1002/cpa.22226; arXiv:2306.10131. Unqualified result and equation numbers in this file
  refer to this paper, in the numbering of arXiv v2.
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

/-! ### Integrability helpers -/

/-- A bounded function that is a.e. strongly measurable on a compact set is integrable there. -/
theorem integrableOn_of_abs_le {f : Rn n → ℝ} {K : Set (Rn n)} (hK : IsCompact K)
    (hf : AEStronglyMeasurable f (volume.restrict K)) {M : ℝ} (hM : ∀ y ∈ K, |f y| ≤ M) :
    IntegrableOn f K :=
  IntegrableOn.of_bound hK.measure_lt_top hf M
    ((ae_restrict_iff' hK.measurableSet).2 (.of_forall fun y hy => by
      rw [Real.norm_eq_abs]; exact hM y hy))

/-- `(f(y) − ∇f(y)·(y − x))²` is integrable on a compact set where `f` is continuous and `∇f` is
bounded. -/
theorem integrableOn_sub_inner_sq {f : Rn n → ℝ} {K : Set (Rn n)} (hK : IsCompact K)
    (hf : ContinuousOn f K) {L : ℝ} (hL : ∀ y ∈ K, ‖gradient f y‖ ≤ L) (x : Rn n) :
    IntegrableOn (fun y => (f y - ⟪gradient f y, y - x⟫) ^ 2) K := by
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hf
  obtain ⟨D, hD⟩ := (hK.image (continuous_id.sub continuous_const)).isBounded.exists_norm_le
  have hm : AEStronglyMeasurable (fun y => (f y - ⟪gradient f y, y - x⟫) ^ 2)
      (volume.restrict K) :=
    ((hf.aestronglyMeasurable hK.measurableSet).sub
      ((measurable_gradient f).inner (measurable_id.sub_const x)).aestronglyMeasurable).pow 2
  refine integrableOn_of_abs_le hK hm (M := (B + L * D) ^ 2) fun y hy => ?_
  have h1 : |f y| ≤ B := by rw [← Real.norm_eq_abs]; exact hB y hy
  have h2 : ‖y - x‖ ≤ D := hD _ ⟨y, hy, rfl⟩
  have h3 : |⟪gradient f y, y - x⟫| ≤ L * D :=
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul (hL y hy) h2 (norm_nonneg _) ((norm_nonneg _).trans (hL y hy)))
  rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) ((abs_sub _ _).trans (add_le_add h1 h3)) 2

/-! ### Homogeneity from Euler's identity -/

/-- **Euler's identity implies homogeneity.** Let `f ≥ 0` be continuous, differentiable where it
is positive, with `∇f(y)·y = f(y)` wherever `f(y) > 0`. Then `f(t y) = t f(y)` for all `t > 0`. -/
theorem homogeneous_of_inner_gradient_eq {f : Rn n → ℝ} (hc : Continuous f)
    (hf0 : ∀ y, 0 ≤ f y) (hdiff : ∀ y, 0 < f y → DifferentiableAt ℝ f y)
    (heuler : ∀ y, 0 < f y → ⟪gradient f y, y⟫ = f y) :
    ∀ t, 0 < t → ∀ y, f (t • y) = t * f y := by
  -- The positive case.
  have key : ∀ y, 0 < f y → ∀ t, 0 < t → f (t • y) = t * f y := by
    intro y hy
    set g : ℝ → ℝ := fun s => f (s • y) with hgdef
    set q : ℝ → ℝ := fun s => g s / s with hqdef
    have hgc : Continuous g := hc.comp (continuous_id.smul continuous_const)
    -- `q' = 0` where `g > 0`.
    have hderiv : ∀ s, 0 < s → 0 < g s → HasDerivAt q 0 s := by
      intro s hs hgs
      have hg' : HasDerivAt g ⟪gradient f (s • y), y⟫ s := by
        have h1 := (hdiff _ hgs).hasFDerivAt.comp_hasDerivAt s ((hasDerivAt_id s).smul_const y)
        simp only [one_smul] at h1
        rw [← Kernel.inner_gradient_left] at h1
        exact h1
      have he : ⟪gradient f (s • y), y⟫ = g s / s := by
        have := heuler _ hgs
        rw [real_inner_smul_right] at this
        rw [eq_div_iff hs.ne']
        change _ = f (s • y)
        rw [← this]
        ring
      have := hg'.div (hasDerivAt_id s) hs.ne'
      convert this using 1
      rw [he]
      simp only [id]
      field_simp
      ring
    -- Local constancy of `q` near a point where `g > 0`.
    have hloc : ∀ s, 0 < s → 0 < g s → ∀ᶠ s' in 𝓝 s, q s' = q s := by
      intro s hs hgs
      have hV : {s' | 0 < s' ∧ 0 < g s'} ∈ 𝓝 s :=
        inter_mem (Ioi_mem_nhds hs) ((hgc.continuousAt).preimage_mem_nhds (Ioi_mem_nhds hgs))
      obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.1 hV
      filter_upwards [ball_mem_nhds s hε] with s' hs'
      have hdiffq : DifferentiableOn ℝ q (ball s ε) := fun z hz =>
        (hderiv z (hεV hz).1 (hεV hz).2).differentiableAt.differentiableWithinAt
      exact isOpen_ball.is_const_of_deriv_eq_zero (convex_ball s ε).isPreconnected hdiffq
        (fun z hz => (hderiv z (hεV hz).1 (hεV hz).2).deriv) hs' (mem_ball_self hε)
    set a := f y
    have hq1 : q 1 = a := by simp [hqdef, hgdef, a]
    set U := interior {s | q s = a}
    have hsub : ∀ s, 0 < s → q s = a → s ∈ U := by
      intro s hs hqs
      have hgs : 0 < g s := by
        have : g s = s * a := by rw [← hqs, hqdef]; field_simp
        rw [this]; exact mul_pos hs hy
      rw [mem_interior_iff_mem_nhds]
      filter_upwards [hloc s hs hgs] with s' hs'
      rw [hs', hqs]
    have hIoi : Ioi (0 : ℝ) ⊆ U := by
      refine isPreconnected_Ioi.subset_of_closure_inter_subset isOpen_interior
        ⟨1, mem_Ioi.2 one_pos, hsub 1 one_pos hq1⟩ ?_
      rintro s ⟨hs, hs0⟩
      refine hsub s hs0 ?_
      have hqc : ContinuousAt q s :=
        hgc.continuousAt.div continuousAt_id (ne_of_gt hs0)
      have h1 := mem_closure_image hqc (closure_mono interior_subset hs)
      have h2 : q '' {s | q s = a} ⊆ {a} := by
        rintro _ ⟨z, hz, rfl⟩; exact hz
      have := closure_mono h2 h1
      rwa [closure_singleton, mem_singleton_iff] at this
    intro t ht
    have := interior_subset (hIoi ht)
    simp only [mem_setOf_eq, hqdef, hgdef] at this
    rw [div_eq_iff ht.ne'] at this
    rw [this]; ring
  intro t ht y
  rcases (hf0 y).lt_or_eq with hy | hy
  · exact key y hy t ht
  · rw [← hy, mul_zero]
    refine le_antisymm (not_lt.1 fun hpos => ?_) (hf0 _)
    have := key (t • y) hpos t⁻¹ (inv_pos.2 ht)
    rw [smul_smul, inv_mul_cancel₀ ht.ne', one_smul, ← hy] at this
    exact absurd this (ne_of_lt (mul_pos (inv_pos.2 ht) hpos))

namespace IsVariationalSolution

variable {Ω : Set (Rn n)} {C : ℝ≥0} {u χ : Rn n → ℝ} {x : Rn n} {R : ℝ}

/-! ### The annulus bound from the derivative of `M` -/

/-- **Integrated Proposition 3.4**: for `0 < s ≤ t < R`, `B_R(x) ⊆ Ω`,
`∫_{B_t(x) ∖ B_s(x)} (u − ∇u·(y−x))² ≤ (t^{n+2} / 2) (M_x(t) − M_x(s))`. -/
theorem integral_annulus_sub_inner_sq_le [NeZero n] (h : IsVariationalSolution Ω C u χ)
    (hR : ball x R ⊆ Ω) {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (htR : t < R) :
    ∫ y in ball x t \ ball x s, (u y - ⟪gradient u y, y - x⟫) ^ 2 ≤
      t ^ (n + 2) / 2 * (monotonicityM u χ x t - monotonicityM u χ x s) := by
  set F : Rn n → ℝ := fun y => (u y - ⟪gradient u y, y - x⟫) ^ 2 with hFdef
  have ht : 0 < t := hs.trans_le hst
  have hK : closedBall x t ⊆ Ω := (closedBall_subset_ball htR).trans hR
  have hFint : IntegrableOn F (ball x t) :=
    (integrableOn_sub_inner_sq (isCompact_closedBall x t) (h.continuousOn.mono hK)
      (fun y hy => h.norm_gradient_le (hK hy)) x).mono_set ball_subset_closedBall
  rw [integral_ball_diff_ball hs.le hst hFint]
  set d := h.radialData hR hs hst htR
  have hSI0 : ∀ σ, 0 < σ → 0 ≤ sphereIntegral F x σ := fun σ hσ =>
    sphereIntegral_nonneg hσ.le fun _ _ => sq_nonneg _
  have key := AbsolutelyContinuousOnInterval.integral_le_sub_of_ae_le
    (f := monotonicityM u χ x)
    (f' := fun σ => 2 / σ ^ (n + 2) * sphereIntegral F x σ)
    (g := fun σ => 2 / t ^ (n + 2) * sphereIntegral F x σ) hst
    d.absolutelyContinuousOnInterval_monotonicityM
    (ae_mem_Ioo_imp_mono hs.le htR.le (h.hasDerivAt_monotonicityM_ae hR))
    (.of_forall fun σ hσ => mul_nonneg (by positivity) (hSI0 σ (hs.trans hσ.1)))
    (.of_forall fun σ hσ => by
      have hσ0 : 0 < σ := hs.trans hσ.1
      refine mul_le_mul_of_nonneg_right ?_ (hSI0 σ hσ0)
      exact div_le_div_of_nonneg_left zero_le_two (by positivity)
        (pow_le_pow_left₀ hσ0.le hσ.2.le _))
  rw [intervalIntegral.integral_const_mul] at key
  have htp : 0 < t ^ (n + 2) := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ htp] at key
  linarith

/-! ### Euler's identity for limits -/

/-- **Euler's identity for limits** (proof of Proposition 3.5). Let `(w_k, χ_k)` be variational
solutions on `B_ρ` with a common constant, `w_k → w₀` locally uniformly on `B_ρ`, and
`M_0(w_k; t) − M_0(w_k; s) → 0` for all `0 < s ≤ t < ρ`. Then `∇w₀(y)·y = w₀(y)` at every
`y ∈ B_ρ ∖ {0}` with `w₀(y) > 0`. -/
theorem inner_gradient_eq_of_tendsto_monotonicityM_sub [NeZero n] {w χw : ℕ → Rn n → ℝ}
    {w₀ : Rn n → ℝ} {ρ : ℝ} (hw : ∀ k, IsVariationalSolution (ball 0 ρ) C (w k) (χw k))
    (hconv : TendstoLocallyUniformlyOn w w₀ atTop (ball 0 ρ))
    (hM : ∀ s t, 0 < s → s ≤ t → t < ρ → Tendsto (fun k =>
      monotonicityM (w k) (χw k) 0 t - monotonicityM (w k) (χw k) 0 s) atTop (𝓝 0))
    {y : Rn n} (hy : y ∈ ball 0 ρ) (hy0 : y ≠ 0) (hpos : 0 < w₀ y) :
    ⟪gradient w₀ y, y⟫ = w₀ y := by
  have hwL : ∀ k, IsLipHarmonicPos (ball 0 ρ) (w k) := fun k => (hw k).isLipHarmonicPos
  have hL : ∀ k x r, ball x r ⊆ ball 0 ρ → LipschitzOnWith C (w k) (ball x r) :=
    fun k => (hw k).lipschitzOnWith
  have h0 := IsLipHarmonicPos.of_tendstoLocallyUniformlyOn hwL hL hconv
  set a := ‖y‖
  have ha : 0 < a := norm_pos_iff.2 hy0
  have haρ : a < ρ := mem_ball_zero_iff.1 hy
  set s := a / 2
  set t := (a + ρ) / 2
  have hs : 0 < s := by positivity
  have hsa : s < a := by simp only [s]; linarith
  have hat : a < t := by simp only [t]; linarith
  have htρ : t < ρ := by simp only [t]; linarith
  have hst : s ≤ t := (hsa.trans hat).le
  set A := ball (0 : Rn n) t \ ball 0 s
  set K := closedBall (0 : Rn n) t
  have hK : IsCompact K := isCompact_closedBall _ _
  have hKρ : K ⊆ ball 0 ρ := closedBall_subset_ball htρ
  have hAK : A ⊆ K := diff_subset.trans ball_subset_closedBall
  have hAm : MeasurableSet A := measurableSet_ball.diff measurableSet_ball
  have hnormK : ∀ z ∈ K, ‖z‖ ≤ t := fun z hz => mem_closedBall_zero_iff.1 hz
  set F₀ : Rn n → ℝ := fun z => w₀ z - ⟪gradient w₀ z, z⟫ with hF₀def
  set F : ℕ → Rn n → ℝ := fun k z => w k z - ⟪gradient (w k) z, z⟫ with hFdef
  have hg0 : ∀ z ∈ ball (0 : Rn n) ρ, ‖gradient w₀ z‖ ≤ C := fun z hz =>
    norm_gradient_le_of_tendstoLocallyUniformlyOn hwL hL hconv hz
  have hgk : ∀ k, ∀ z ∈ ball (0 : Rn n) ρ, ‖gradient (w k) z‖ ≤ C := fun k z hz =>
    (hw k).norm_gradient_le hz
  -- Integrability.
  have hI₀ : IntegrableOn (fun z => F₀ z ^ 2) K := by
    simpa [hF₀def] using integrableOn_sub_inner_sq hK (h0.continuousOn.mono hKρ)
      (fun z hz => hg0 z (hKρ hz)) 0
  have hIk : ∀ k, IntegrableOn (fun z => F k z ^ 2) K := fun k => by
    simpa [hFdef] using integrableOn_sub_inner_sq hK ((hw k).continuousOn.mono hKρ)
      (fun z hz => hgk k z (hKρ hz)) 0
  have hIu : ∀ k, IntegrableOn (fun z => (w₀ z - w k z) ^ 2) K := fun k =>
    ((h0.continuousOn.sub (hw k).continuousOn).pow 2).mono hKρ |>.integrableOn_compact hK
  have hIg : ∀ k, IntegrableOn (fun z => ‖gradient (w k) z - gradient w₀ z‖ ^ 2) K := fun k =>
    integrableOn_of_abs_le hK
      (((measurable_gradient _).sub (measurable_gradient _)).norm.pow_const 2).aestronglyMeasurable
      (M := (2 * C) ^ 2) fun z hz => by
        rw [abs_of_nonneg (sq_nonneg _)]
        refine pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans ?_) 2
        linarith [hgk k z (hKρ hz), hg0 z (hKρ hz)]
  -- The pointwise bound.
  have hpt : ∀ k, ∀ z ∈ K, F₀ z ^ 2 ≤ 2 * F k z ^ 2 + 4 * (w₀ z - w k z) ^ 2 +
      4 * t ^ 2 * ‖gradient (w k) z - gradient w₀ z‖ ^ 2 := by
    intro k z hz
    set c := ⟪gradient (w k) z - gradient w₀ z, z⟫
    have hsplit : F₀ z = F k z + (w₀ z - w k z) + c := by
      simp only [hF₀def, hFdef, c, inner_sub_left]; ring
    have hc : c ^ 2 ≤ t ^ 2 * ‖gradient (w k) z - gradient w₀ z‖ ^ 2 := by
      have h1 : |c| ≤ ‖gradient (w k) z - gradient w₀ z‖ * t :=
        (abs_real_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_left (hnormK z hz) (norm_nonneg _))
      rw [← sq_abs]
      calc |c| ^ 2 ≤ (‖gradient (w k) z - gradient w₀ z‖ * t) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) h1 2
        _ = _ := by ring
    rw [hsplit]
    nlinarith [sq_nonneg (F k z - (w₀ z - w k z) - c), sq_nonneg (w₀ z - w k z - c)]
  -- The bound on `∫_A F₀²`.
  have hbound : ∀ k, ∫ z in A, F₀ z ^ 2 ≤
      2 * (t ^ (n + 2) / 2 * (monotonicityM (w k) (χw k) 0 t - monotonicityM (w k) (χw k) 0 s))
        + 4 * (∫ z in A, (w₀ z - w k z) ^ 2)
        + 4 * t ^ 2 * ∫ z in K, ‖gradient (w k) z - gradient w₀ z‖ ^ 2 := by
    intro k
    have hA1 : ∫ z in A, F k z ^ 2 ≤
        t ^ (n + 2) / 2 * (monotonicityM (w k) (χw k) 0 t - monotonicityM (w k) (χw k) 0 s) := by
      have := (hw k).integral_annulus_sub_inner_sq_le (subset_refl _) hs hst htρ
      simpa [hFdef, sub_zero] using this
    have hA2 : ∫ z in A, ‖gradient (w k) z - gradient w₀ z‖ ^ 2 ≤
        ∫ z in K, ‖gradient (w k) z - gradient w₀ z‖ ^ 2 :=
      setIntegral_mono_set (hIg k) (.of_forall fun _ => sq_nonneg _) (.of_forall hAK)
    calc ∫ z in A, F₀ z ^ 2
        ≤ ∫ z in A, (2 * F k z ^ 2 + 4 * (w₀ z - w k z) ^ 2 +
            4 * t ^ 2 * ‖gradient (w k) z - gradient w₀ z‖ ^ 2) :=
          setIntegral_mono_on (hI₀.mono_set hAK)
            (((((hIk k).mono_set hAK).const_mul 2).fun_add
              (((hIu k).mono_set hAK).const_mul 4)).fun_add
              (((hIg k).mono_set hAK).const_mul _)) hAm fun z hz => hpt k z (hAK hz)
      _ = 2 * (∫ z in A, F k z ^ 2) + 4 * (∫ z in A, (w₀ z - w k z) ^ 2) +
            4 * t ^ 2 * ∫ z in A, ‖gradient (w k) z - gradient w₀ z‖ ^ 2 := by
          rw [integral_add ((((hIk k).mono_set hAK).const_mul 2).fun_add
              (((hIu k).mono_set hAK).const_mul 4)) (((hIg k).mono_set hAK).const_mul _),
            integral_add (((hIk k).mono_set hAK).const_mul 2)
              (((hIu k).mono_set hAK).const_mul 4),
            integral_const_mul, integral_const_mul, integral_const_mul]
      _ ≤ _ := by gcongr
  -- The bound tends to zero.
  have hlim1 := (hM s t hs hst htρ).const_mul (t ^ (n + 2) / 2) |>.const_mul 2
  have hlim2 : Tendsto (fun k => ∫ z in A, (w₀ z - w k z) ^ 2) atTop (𝓝 0) := by
    have hunif := (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_ball).1 hconv K hKρ hK
    have h := tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict A)
      (F := fun k z => (w₀ z - w k z) ^ 2) (f := fun _ => (0 : ℝ)) (fun _ => 1)
      (.of_forall fun k => ((hIu k).mono_set hAK).aestronglyMeasurable)
      ((Metric.tendstoUniformlyOn_iff.1 hunif 1 one_pos).mono fun k hk =>
        (ae_restrict_iff' hAm).2 (.of_forall fun z hz => by
          have h1 := hk z (hAK hz)
          rw [Real.dist_eq] at h1
          have key : (w₀ z - w k z) ^ 2 ≤ 1 := by
            rw [← sq_abs]; nlinarith [abs_nonneg (w₀ z - w k z)]
          change ‖(w₀ z - w k z) ^ 2‖ ≤ 1
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          exact key))
      (integrableOn_const ((measure_mono hAK).trans_lt hK.measure_lt_top).ne)
      ((ae_restrict_iff' hAm).2 (.of_forall fun z hz => by
        have := ((hconv.tendsto_at (hKρ (hAK hz))).const_sub (w₀ z)).pow 2
        simpa using this))
    simpa using h
  have hlim3 := (tendsto_setIntegral_norm_gradient_sub_sq hwL hL hconv hK hKρ).const_mul
    (4 * t ^ 2)
  have hlim := (hlim1.add (hlim2.const_mul 4)).add hlim3
  simp only [mul_zero, add_zero] at hlim
  have hzero : ∫ z in A, F₀ z ^ 2 = 0 :=
    le_antisymm (ge_of_tendsto' hlim hbound)
      (setIntegral_nonneg hAm fun _ _ => sq_nonneg _)
  -- `F₀ = 0` a.e. on `A`, hence everywhere on the open set `A° ∩ {w₀ > 0}`.
  have hae : F₀ =ᵐ[volume.restrict A] 0 := by
    have := (setIntegral_eq_zero_iff_of_nonneg_ae (.of_forall fun _ => sq_nonneg _)
      (hI₀.mono_set hAK)).1 hzero
    filter_upwards [this] with z hz
    simpa using hz
  set P := (ball (0 : Rn n) ρ ∩ {z | 0 < w₀ z}) ∩ (ball 0 t \ closedBall 0 s)
  have hPo : IsOpen P := h0.isOpen_pos.inter (isOpen_ball.sdiff isClosed_closedBall)
  have hPA : P ⊆ A := fun z hz => ⟨hz.2.1, fun h' => hz.2.2 (ball_subset_closedBall h')⟩
  have hyP : y ∈ P := ⟨⟨hy, hpos⟩, mem_ball_zero_iff.2 hat,
    fun h' => absurd (mem_closedBall_zero_iff.1 h') (not_le.2 hsa)⟩
  have hcont : ContinuousOn F₀ P := by
    have hgrad : ContinuousOn (gradient w₀) (ball (0 : Rn n) ρ ∩ {z | 0 < w₀ z}) :=
      Kernel.continuousOn_gradient h0.isOpen_pos (h0.contDiffOn.of_le (by norm_num))
    exact (h0.continuousOn.mono fun z hz => hz.1.1).sub
      ((hgrad.mono fun z hz => hz.1).inner continuousOn_id)
  have heq := Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae_restrict_of_subset hPA hae) hPo
    hcont continuousOn_const hyP
  simp only [hF₀def, Pi.zero_apply, sub_eq_zero] at heq
  exact heq.symm

end IsVariationalSolution

/-! ### The energy of a limit satisfying Euler's identity -/

/-- **Energy of a one-homogeneous limit** (proof of Proposition 3.5): if `w₀` is Lipschitz,
harmonic on `{w₀ > 0}` in `B_ρ`, and satisfies Euler's identity `∇w₀(y)·y = w₀(y)` on
`B_ρ ∩ {w₀ > 0} ∖ {0}`, then `t ∫_{B_t} |∇w₀|² = ∫_{∂B_t} w₀²` for every `0 < t < ρ`. -/
theorem integral_norm_gradient_sq_eq_of_inner_gradient_eq [NeZero n] {w₀ : Rn n → ℝ} {ρ : ℝ}
    (h0 : IsLipHarmonicPos (ball 0 ρ) w₀)
    (heuler : ∀ y ∈ ball (0 : Rn n) ρ, y ≠ 0 → 0 < w₀ y → ⟪gradient w₀ y, y⟫ = w₀ y)
    {t : ℝ} (ht : 0 < t) (htρ : t < ρ) :
    t * ∫ y in ball 0 t, ‖gradient w₀ y‖ ^ 2 = sphereIntegral (fun y => w₀ y ^ 2) 0 t := by
  set G : ℝ → ℝ := fun s => s * ∫ y in ball (0 : Rn n) s, ‖gradient w₀ y‖ ^ 2
  set S : ℝ → ℝ := fun s => sphereIntegral (fun y => w₀ y ^ 2) 0 s
  have hae : ∀ᵐ s, s ∈ Ioo 0 ρ → G s = S s := by
    filter_upwards [h0.energy_eq_sphere_ae' (subset_refl _)] with s hs hsρ
    simp only [G, S]
    rw [hs hsρ, ← sphereIntegral_const_mul]
    refine sphereIntegral_congr hsρ.1.le fun y hy => ?_
    have hyn : ‖y‖ = s := by rw [mem_sphere, dist_zero_right] at hy; exact hy
    have hyρ : y ∈ ball (0 : Rn n) ρ := mem_ball_zero_iff.2 (hyn ▸ hsρ.2)
    have hy0 : y ≠ 0 := by
      rintro rfl; rw [norm_zero] at hyn; exact hsρ.1.ne hyn
    rw [sub_zero, real_inner_smul_right]
    rcases (h0.nonneg y hyρ).lt_or_eq with hpos | hzero
    · rw [heuler y hyρ hy0 hpos]
      have hs0 : s ≠ 0 := hsρ.1.ne'
      field_simp
    · rw [← hzero]; ring
  obtain ⟨L, hL⟩ := h0.exists_norm_gradient_le
  have hGc : ContinuousOn G (Ioo 0 ρ) := by
    have hlip := lipschitzOnWith_integral_ball (x := (0 : Rn n)) (R := ρ) (M := (L : ℝ) ^ 2)
      (f := fun y => ‖gradient w₀ y‖ ^ 2)
      ((measurable_gradient w₀).norm.pow_const 2).aestronglyMeasurable
      fun y hy => by
        rw [abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hL y hy) 2
    exact continuousOn_id.mul (hlip.continuousOn.mono Ioo_subset_Icc_self)
  have hSc : ContinuousOn S (Ioo 0 ρ) := by
    intro s hs
    have h1 := continuousAt_sphereIntegral isOpen_ball (h0.continuousOn.pow 2)
      (x := (0 : Rn n)) (s := s) (by
        rw [abs_of_pos hs.1]; exact closedBall_subset_ball hs.2)
    have h2 : ContinuousAt (fun s : ℝ => ((0 : Rn n), s)) s :=
      (continuous_const.prodMk continuous_id).continuousAt
    exact (ContinuousAt.comp (f := fun s : ℝ => ((0 : Rn n), s)) h1 h2).continuousWithinAt
  have hae' : G =ᵐ[volume.restrict (Ioo 0 ρ)] S := by
    rw [EventuallyEq, ae_restrict_iff' measurableSet_Ioo]
    exact hae
  exact Measure.eqOn_open_of_ae_eq hae' isOpen_Ioo hGc hSc ⟨ht, htρ⟩

end InnerVariational
