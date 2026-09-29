/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Blowup.Limit
public import InnerVariational.Blowup.Renormalization
public import InnerVariational.Kernel.Harmonic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Data.Real.StarOrdered
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Real.Hom
import InnerVariational.Blowup.ExplicitForm
import InnerVariational.Blowup.DomainVariation
public import InnerVariational.Blowup.Sobolev
import InnerVariational.Sobolev.WeakGradient
public import InnerVariational.Defs.Quantities
public import InnerVariational.Kernel.BV
import InnerVariational.Kernel.IBP
import InnerVariational.Basic.SphereIntegral
import InnerVariational.Basic.Polar
import InnerVariational.Sobolev.Lipschitz
public import InnerVariational.Blowup.Profile.Limit

/-!
# Theorem 5.3, steps (d)–(e), and the normalization for a renormalized sequence

Steps (d) and (e) of the proof of Theorem 5.3 of Kriventsov–Weiss (full reference below), that
is, its last two paragraphs, together with the normalization `β = α(n)` (the remark after the
statement of Theorem 5.3), for an abstract renormalized sequence `v_k`. The frequency input is
supplied in `Blowup/Approx1D.lean`.

Along the subsequence of Lemma 5.1 the limit is `v = β₊ ⟪ν₀, y⟫₊ + β₋ ⟪ν₀, y⟫₋` on
`A = B_1 \ B̄_{1/2}` (step (a) with `N = 1`, `Blowup/ExplicitForm.lean`).
* Step (d): `∫ |∇v_k|² η = −∫ v_k ∇v_k·∇η` (the `v_k` are harmonic where positive)
  passes to the limit (strong times weak convergence), and the limit satisfies the same identity
  (`v Δv = 0`, proved here by a one-dimensional integration by parts on each side of the
  hyperplane). Hence `∇v_k → ∇v` in `L²(A')`, `A' = B_{7/8} \ B̄_{5/8}`.
* Step (e): the limit domain variation for `ξ = φ ν₀`, `φ ∈ C_c^∞(A')` crossing the
  hyperplane, gives `(β₊² − β₋²) ∫_{⟪ν₀, y⟫ > 0} ∂_{ν₀} φ = 0`, so `β₊ = β₋`.
* Normalization: `∫_A v_k² → ∫_{1/2}^1 s^{n+1} ds` (the radial mass identity) gives
  `β² ∫_{∂B_1} y_1² = 1`, that is `β = α(n)`.

## Main results

* `exists_subseq_tendsto_profile`, `tendsto_profile_of_renormalized`: Theorem 5.3, steps (d)–(e) for
  a renormalized sequence, along a subsequence and for the full sequence.

## Faithfulness notes

* The paper normalizes by `∫_{∂B_1} v² = 1`, passed to the limit by the compact trace embedding.
  Here the trace is not used: the radial mass identity `∫_A v_k² → ∫_{1/2}^1 s^{n+1} ds` (from
  Lemma 4.3 with `N(1) → 1`) is passed to the limit through strong `L²(A)` convergence.
* The paper concludes step (d) with "(5.15) is valid for any `ξ ∈ C_c^1(A')`". Only the first
  equality of (5.15), `0 = ∫ (h')² ∂_n ξ_n`, extends to fields crossing `{x_n = 0}`; the second,
  `= −∫ 2 h' h'' ξ_n`, needs `ξ` supported off the hyperplane, since integrating by parts across
  it produces exactly the jump term used in step (e). Step (e) here uses only the first equality.

## Reference

* D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
  DOI 10.1002/cpa.22226; arXiv:2306.10131 (numbering of arXiv v2).
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

/-! ### Theorem 5.3, steps (d)–(e) and the normalization for a renormalized sequence -/

section Profile

variable [NeZero n]

set_option maxHeartbeats 400000 in
-- A long assembly proof: it carries the `L²` facts about the Lemma 5.1 limit through steps (a)–(e).
/-- **Theorem 5.3, steps (d)–(e) along a subsequence.** Let `v_k` satisfy the hypotheses of
`eq_one_of_renormalized` with `N = 1` (Lipschitz on `B̄_1`, nonnegative, bounded in
`W^{1,2}(B_1)`, vanishing Euler defect, vanishing tangential energy and vanishing domain-variation
defect on `A = B_1 \ B̄_{1/2}`), and in addition
* the energy identity `∫ |∇v_k|² η = −∫ v_k ∇v_k·∇η` for `η ∈ C_c^∞(A)` (`v_k` is harmonic where
  positive, as used in step (d));
* the radial mass identity `∫_A v_k² → ∫_{1/2}^1 s^{n+1} ds` (it replaces `∫_{∂B_1} v_k² = 1` and
  the trace convergence of Lemma 5.1).

Then along a subsequence `θ`, on `A' = B_{7/8} \ B̄_{5/8}`,
`∫_{A'} (v_{θ k} − α(n) |⟪y, ν_{θ k}⟫|)² → 0` and
`∫_{A'} |∇v_{θ k} − α(n) ∇|⟪y, ν_{θ k}⟫||² → 0`.

Proof: the limit `v` of Lemma 5.1 is `β₊ ⟪ν₀, y⟫₊ + β₋ ⟪ν₀, y⟫₋` on `A` (step (a) with `N = 1`),
`β_± ≥ 0`. Step (d): the energy identity of `v_k` passes to the limit (strong times weak), and
`v` satisfies it too (one-dimensional integration by parts on each side of `{⟪ν₀, y⟫ = 0}`), so
`∫ |∇v_k − ∇v|² η → 0` for a cut-off `η = 1` on `A'`. Step (e): the limit domain variation for
`ξ = φ ν₀`, `φ ∈ C_c^∞(A')` crossing the hyperplane, gives
`(β₊² − β₋²) ∫_{⟪ν₀, y⟫ > 0} ∂_{ν₀} φ = 0`,
so `β₊ = β₋ =: β`. The mass identity gives `β² ∫_A ⟪ν₀, y⟫² = ∫_{1/2}^1 s^{n+1} ds`, i.e.
`β² ∫_{∂B_1} y_1² = 1`, so `β = α(n)`. -/
theorem exists_subseq_tendsto_profile (hn : 2 ≤ n) (v : ℕ → Rn n → ℝ) {C : ℝ}
    {ν : ℕ → Rn n} (hν : ∀ k, ‖ν k‖ = 1)
    (hLip : ∀ k, ∃ L, LipschitzOnWith L (v k) (closedBall 0 1))
    (hbd : ∀ k, ∫ y in ball (0 : Rn n) 1, (v k y ^ 2 + ‖gradient (v k) y‖ ^ 2) ≤ C)
    (hnn : ∀ k, ∀ y ∈ ball (0 : Rn n) 1, 0 ≤ v k y)
    (hE : Tendsto (fun k => ∫ y in ball (0 : Rn n) 1 \ closedBall 0 (1 / 2),
      (⟪gradient (v k) y, y⟫ - v k y) ^ 2) atTop (𝓝 0))
    (htan : Tendsto (fun k => ∫ y in ball (0 : Rn n) 1 \ closedBall 0 (1 / 2),
      ‖gradient (v k) y - ⟪gradient (v k) y, ν k⟫ • ν k‖ ^ 2) atTop (𝓝 0))
    (hmass : Tendsto (fun k => ∫ y in ball (0 : Rn n) 1 \ closedBall 0 (1 / 2), v k y ^ 2) atTop
      (𝓝 (∫ s in (1 / 2 : ℝ)..1, s ^ (n + 1))))
    (hdv : ∀ φ : Rn n → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ ball (0 : Rn n) 1 \ closedBall 0 (1 / 2) → ∀ e : Rn n,
      Tendsto (fun k => ∫ y, Kernel.gradVariation (v k) (fun z => φ z • e) y) atTop (𝓝 0))
    (henergy : ∀ η : Rn n → ℝ, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      tsupport η ⊆ ball (0 : Rn n) 1 \ closedBall 0 (1 / 2) → ∀ k,
      ∫ y, ‖gradient (v k) y‖ ^ 2 * η y = -∫ y, v k y * ⟪gradient (v k) y, gradient η y⟫) :
    ∃ θ : ℕ → ℕ, Tendsto θ atTop atTop ∧
      Tendsto (fun k => ∫ y in ball (0 : Rn n) (7 / 8) \ closedBall 0 (5 / 8),
        (v (θ k) y - alphaN n * absProfile (ν (θ k)) 0 y) ^ 2) atTop (𝓝 0) ∧
      Tendsto (fun k => ∫ y in ball (0 : Rn n) (7 / 8) \ closedBall 0 (5 / 8),
        ‖gradient (v (θ k)) y - alphaN n • gradient (absProfile (ν (θ k)) 0) y‖ ^ 2) atTop
        (𝓝 0) := by
  set B : Set (Rn n) := ball 0 1 with hB
  set A : Set (Rn n) := ball (0 : Rn n) 1 \ closedBall 0 (1 / 2) with hA
  set A' : Set (Rn n) := ball (0 : Rn n) (7 / 8) \ closedBall 0 (5 / 8) with hA'
  set α := alphaN n with hα
  have hAo : IsOpen A := isOpen_ball.sdiff isClosed_closedBall
  have hAm : MeasurableSet A := hAo.measurableSet
  have hAB : A ⊆ B := diff_subset
  have hA'm : MeasurableSet A' := (isOpen_ball.sdiff isClosed_closedBall).measurableSet
  have hA'A : A' ⊆ A := fun y hy => ⟨ball_subset_ball (by norm_num) hy.1, fun h => hy.2
    (closedBall_subset_closedBall (by norm_num) h)⟩
  have hA'B : A' ⊆ B := hA'A.trans hAB
  have hle : ∀ {S : Set (Rn n)}, S ⊆ B → volume.restrict S ≤ volume.restrict B := fun h =>
    Measure.restrict_mono h le_rfl
  have hμA : (volume.restrict B).restrict A = volume.restrict A :=
    Measure.restrict_restrict_of_subset hAB
  haveI : IsFiniteMeasure (volume.restrict A) :=
    isFiniteMeasure_restrict.2 ((measure_mono hAB).trans_lt measure_ball_lt_top).ne
  haveI : IsFiniteMeasure (volume.restrict A') :=
    isFiniteMeasure_restrict.2 ((measure_mono hA'B).trans_lt measure_ball_lt_top).ne
  obtain ⟨θ, hθt, ν₀, hν₀, hνθ, F, G, hFB, hGB, hWB, hconv, hweak, hFnn, heuler, htanG, -⟩ :=
    exists_subseq_limit_data v (N := 1) hν hLip hbd hnn (by simpa only [one_mul] using hE) htan
  have hν₀0 : ν₀ ≠ 0 := by rintro rfl; simp at hν₀
  /- `L²` memberships. -/
  have hvB : ∀ k, MemLp (v k) 2 (volume.restrict B) := fun k =>
    (memH1_gradient_of_lipschitzOnWith isOpen_ball isBounded_ball
      ((hLip k).choose_spec.mono ball_subset_closedBall)).1
  have hgB : ∀ k, MemLp (gradient (v k)) 2 (volume.restrict B) := fun k =>
    (memH1_gradient_of_lipschitzOnWith isOpen_ball isBounded_ball
      ((hLip k).choose_spec.mono ball_subset_closedBall)).2.1
  have hvA : ∀ k, MemLp (v k) 2 (volume.restrict A) := fun k => (hvB k).mono_measure (hle hAB)
  have hgA : ∀ k, MemLp (gradient (v k)) 2 (volume.restrict A) := fun k =>
    (hgB k).mono_measure (hle hAB)
  have hFA : MemLp F 2 (volume.restrict A) := hFB.mono_measure (hle hAB)
  have hGA : MemLp G 2 (volume.restrict A) := hGB.mono_measure (hle hAB)
  have hgA_bd : ∀ k, ∫ y in A, ‖gradient (v k) y‖ ^ 2 ≤ C := by
    intro k
    calc ∫ y in A, ‖gradient (v k) y‖ ^ 2 ≤ ∫ y in B, ‖gradient (v k) y‖ ^ 2 :=
          setIntegral_mono_set (MemLp.integrable_norm_sq (hgB k))
            (Eventually.of_forall fun y => by positivity) hAB.eventuallyLE
      _ ≤ ∫ y in B, (v k y ^ 2 + ‖gradient (v k) y‖ ^ 2) := by
          have hi : IntegrableOn (fun y => v k y ^ 2 + ‖gradient (v k) y‖ ^ 2) B :=
            (hvB k).integrable_sq.add (MemLp.integrable_norm_sq (hgB k))
          exact setIntegral_mono (MemLp.integrable_norm_sq (hgB k)) hi fun y => by
            nlinarith [sq_nonneg (v k y)]
      _ ≤ C := hbd k
  have hweakA : WeakTendstoL2 (volume.restrict A) (fun k => gradient (v (θ k))) G := by
    have := hweak.restrict hAm
    rwa [hμA] at this
  have hconvA : Tendsto (fun k => ∫ y in A, (v (θ k) y - F y) ^ 2) atTop (𝓝 0) := by
    refine squeeze_zero (fun k => setIntegral_nonneg hAm fun y _ => sq_nonneg _)
      (fun k => ?_) hconv
    exact setIntegral_mono_set ((hvB _).sub hFB).integrable_sq
      (Eventually.of_forall fun y => sq_nonneg _) hAB.eventuallyLE
  /- Step (a) with `N = 1`: the explicit form of the limit. -/
  have hWA : GMTFoundations.HasWeakGradient A F G := HasWeakGradient.mono hWB hAB
  obtain ⟨βp, βm, hβ⟩ := exists_ae_eq_explicit_form (r₁ := 1 / 2) (r₂ := 1) (by norm_num) hWA
    heuler htanG
  have hnull : ∀ᵐ y ∂(volume.restrict A), ⟪ν₀, y⟫ ≠ 0 :=
    ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 (volume_inner_eq_zero hν₀0))
  have hside : ∀ᵐ y ∂(volume.restrict A),
      (0 < ⟪ν₀, y⟫ → F y = βp * ⟪ν₀, y⟫ ∧ ⟪G y, ν₀⟫ = βp) ∧
      (⟪ν₀, y⟫ < 0 → F y = βm * -⟪ν₀, y⟫ ∧ ⟪G y, ν₀⟫ = -βm) := by
    filter_upwards [hβ, heuler, htanG] with y hy he ht
    have hGy : ⟪G y, y⟫ = ⟪G y, ν₀⟫ * ⟪ν₀, y⟫ := by
      conv_lhs => rw [ht]
      rw [inner_smul_left, conj_trivial]
    rw [hGy, one_mul] at he
    refine ⟨fun hp => ?_, fun hm => ?_⟩
    · have hF := hy.1 hp
      rw [Real.rpow_one] at hF
      refine ⟨hF, ?_⟩
      rw [hF] at he
      exact mul_right_cancel₀ hp.ne' he
    · have hF := hy.2 hm
      rw [Real.rpow_one] at hF
      refine ⟨hF, ?_⟩
      rw [hF] at he
      have h2 : ⟪G y, ν₀⟫ * ⟪ν₀, y⟫ = -βm * ⟪ν₀, y⟫ := by rw [he]; ring
      exact mul_right_cancel₀ hm.ne h2
  /- `β₊, β₋ ≥ 0`, because `v ≥ 0`. -/
  have hex : ∀ S : Set (Rn n), IsOpen S → S.Nonempty → ∀ {p : Rn n → Prop},
      (∀ᵐ y ∂(volume.restrict S), p y) → ∃ y, p y := by
    intro S hS hne p h
    haveI : (ae (volume.restrict S)).NeBot := ae_neBot.2 (by
      rw [Ne, Measure.restrict_eq_zero]
      exact (hS.measure_pos volume hne).ne')
    exact h.exists
  have hpt : ∀ s : ℝ, 1 / 2 < |s| → |s| < 1 → s • ν₀ ∈ A ∧ ⟪ν₀, s • ν₀⟫ = s := by
    intro s h1 h2
    have hn' : ‖s • ν₀‖ = |s| := by rw [norm_smul, hν₀, Real.norm_eq_abs, mul_one]
    refine ⟨⟨mem_ball_zero_iff.2 (by rw [hn']; exact h2), fun h => ?_⟩, ?_⟩
    · rw [mem_closedBall_zero_iff, hn'] at h
      linarith
    · rw [inner_smul_right, real_inner_self_eq_norm_sq, hν₀]
      ring
  have hβp : 0 ≤ βp := by
    have hS : IsOpen (A ∩ {y | 0 < ⟪ν₀, y⟫}) :=
      hAo.inter (isOpen_lt continuous_const (continuous_const.inner continuous_id))
    obtain ⟨hmem, hval⟩ := hpt (3 / 4) (by norm_num [abs_of_pos]) (by norm_num [abs_of_pos])
    obtain ⟨y, hy1, hy2, hy3⟩ := hex _ hS ⟨_, hmem, show 0 < ⟪ν₀, (3 / 4 : ℝ) • ν₀⟫ by
      rw [hval]; norm_num⟩
      ((ae_restrict_of_ae_restrict_of_subset inter_subset_left hside).and
        ((ae_restrict_of_ae_restrict_of_subset (inter_subset_left.trans hAB) hFnn).and
          (ae_restrict_mem hS.measurableSet)))
    have hF := (hy1.1 hy3.2).1
    by_contra h
    push Not at h
    have : F y < 0 := by rw [hF]; exact mul_neg_of_neg_of_pos h hy3.2
    linarith
  have hβm : 0 ≤ βm := by
    have hS : IsOpen (A ∩ {y | ⟪ν₀, y⟫ < 0}) :=
      hAo.inter (isOpen_lt (continuous_const.inner continuous_id) continuous_const)
    obtain ⟨hmem, hval⟩ := hpt (-(3 / 4)) (by norm_num [abs_of_neg]) (by norm_num [abs_of_neg])
    obtain ⟨y, hy1, hy2, hy3⟩ := hex _ hS ⟨_, hmem, show ⟪ν₀, (-(3 / 4) : ℝ) • ν₀⟫ < 0 by
      rw [hval]; norm_num⟩
      ((ae_restrict_of_ae_restrict_of_subset inter_subset_left hside).and
        ((ae_restrict_of_ae_restrict_of_subset (inter_subset_left.trans hAB) hFnn).and
          (ae_restrict_mem hS.measurableSet)))
    have hF := (hy1.2 hy3.2).1
    by_contra h
    push Not at h
    have : F y < 0 := by
      rw [hF]
      exact mul_neg_of_neg_of_pos h (neg_pos.2 hy3.2)
    linarith
  /- Step (d): strong convergence on `A'` via the energy identity. -/
  obtain ⟨η, hηs, hηc, hηA, hη0, hη1, hηA'⟩ := exists_cutoff_annulus (n := n)
  obtain ⟨Lη, hLη⟩ := hηs.lipschitzWith_of_hasCompactSupport hηc (by simp)
  have hgη : ∀ y, ‖gradient η y‖ ≤ Lη := Kernel.norm_gradient_le_of_lipschitz hLη
  have hgηm : AEStronglyMeasurable (gradient η) (volume.restrict A) :=
    (measurable_gradient η).aestronglyMeasurable
  have hηm : AEStronglyMeasurable η (volume.restrict A) := hηs.continuous.aestronglyMeasurable
  have hηb : ∀ᵐ y ∂(volume.restrict A), ‖η y‖ ≤ 1 := Eventually.of_forall fun y => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hη0 y)]
    exact hη1 y
  have hηout : ∀ y ∉ A, η y = 0 := fun y hy =>
    image_eq_zero_of_notMem_tsupport fun h => hy (hηA h)
  have hgηout : ∀ y ∉ A, gradient η y = 0 := fun y hy =>
    Kernel.gradient_eq_zero_of_notMem_tsupport fun h => hy (hηA h)
  have hηG : MemLp (fun y => η y • G y) 2 (volume.restrict A) := by
    refine hGA.of_le (hηm.smul hGA.1) ?_
    filter_upwards [hηb] with y hy
    rw [norm_smul]
    exact mul_le_of_le_one_left (norm_nonneg _) hy
  have iG : Integrable (fun y => ‖G y‖ ^ 2 * η y) (volume.restrict A) :=
    (MemLp.integrable_norm_sq hGA).mul_bdd hηm hηb
  have hL3 := integral_mul_inner_gradient_eq_of_explicit hν₀ hFA hGA hside htanG hnull hηs hηc
    hηA
  -- The energy identity of `v_k` passes to the limit.
  have hL1 := tendsto_integral_mul_inner_of_tendsto (fun k => hvA (θ k)) hFA (fun k => hgA (θ k))
    hgηm (NNReal.coe_nonneg Lη) hgη (fun k => hgA_bd _) hconvA hweakA
  have hL2 : Tendsto (fun k => ∫ y in A, ⟪gradient (v (θ k)) y, η y • G y⟫) atTop
      (𝓝 (∫ y in A, ⟪G y, η y • G y⟫)) := hweakA (fun y => η y • G y) hηG
  have hE1 : ∀ k, ∫ y in A, ‖gradient (v k) y‖ ^ 2 * η y =
      -∫ y in A, v k y * ⟪gradient (v k) y, gradient η y⟫ := fun k => by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by rw [hηout y hy, mul_zero]),
      setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun y hy => by rw [hgηout y hy, inner_zero_right, mul_zero])]
    exact henergy η hηs hηc hηA k
  have hexp : ∀ k, ∫ y in A, ‖gradient (v (θ k)) y - G y‖ ^ 2 * η y =
      (∫ y in A, ‖gradient (v (θ k)) y‖ ^ 2 * η y) -
        2 * (∫ y in A, ⟪gradient (v (θ k)) y, η y • G y⟫) + ∫ y in A, ‖G y‖ ^ 2 * η y := by
    intro k
    have i1 : Integrable (fun y => ‖gradient (v (θ k)) y‖ ^ 2 * η y) (volume.restrict A) :=
      (MemLp.integrable_norm_sq (hgA _)).mul_bdd hηm hηb
    have i2 : Integrable (fun y => ⟪gradient (v (θ k)) y, η y • G y⟫) (volume.restrict A) :=
      MemLp.integrable_inner_two (hgA _) hηG
    have e1 : ∫ y in A, ‖gradient (v (θ k)) y - G y‖ ^ 2 * η y =
        ∫ y in A, ((‖gradient (v (θ k)) y‖ ^ 2 * η y -
          2 * ⟪gradient (v (θ k)) y, η y • G y⟫) + ‖G y‖ ^ 2 * η y) :=
      integral_congr_ae (Eventually.of_forall fun y => by
        simp only
        rw [norm_sub_sq_real, inner_smul_right]
        ring)
    rw [e1, integral_add (f := fun y => ‖gradient (v (θ k)) y‖ ^ 2 * η y -
        2 * ⟪gradient (v (θ k)) y, η y • G y⟫) (g := fun y => ‖G y‖ ^ 2 * η y)
        (i1.sub (i2.const_mul 2)) iG,
      integral_sub (f := fun y => ‖gradient (v (θ k)) y‖ ^ 2 * η y)
        (g := fun y => 2 * ⟪gradient (v (θ k)) y, η y • G y⟫) i1 (i2.const_mul 2),
      integral_const_mul]
  have hT : Tendsto (fun k => ∫ y in A, ‖gradient (v (θ k)) y - G y‖ ^ 2 * η y) atTop (𝓝 0) := by
    have hlim := ((hL1.neg).sub (hL2.const_mul 2)).add_const (∫ y in A, ‖G y‖ ^ 2 * η y)
    have hGG : ∫ y in A, ⟪G y, η y • G y⟫ = ∫ y in A, ‖G y‖ ^ 2 * η y :=
      integral_congr_ae (Eventually.of_forall fun y => by
        simp only
        rw [inner_smul_right, real_inner_self_eq_norm_sq]
        ring)
    have hval : -(∫ y in A, F y * ⟪G y, gradient η y⟫) - 2 * (∫ y in A, ⟪G y, η y • G y⟫) +
        (∫ y in A, ‖G y‖ ^ 2 * η y) = 0 := by
      rw [hL3, hGG]
      ring
    rw [hval] at hlim
    refine hlim.congr fun k => ?_
    rw [hexp k, hE1 (θ k)]
  have hSA' : Tendsto (fun k => ∫ y in A', ‖gradient (v (θ k)) y - G y‖ ^ 2) atTop (𝓝 0) := by
    refine squeeze_zero (fun k => setIntegral_nonneg hA'm fun y _ => sq_nonneg _) (fun k => ?_) hT
    have i : Integrable (fun y => ‖gradient (v (θ k)) y - G y‖ ^ 2 * η y) (volume.restrict A) :=
      (MemLp.integrable_norm_sq ((hgA _).sub hGA)).mul_bdd hηm hηb
    calc ∫ y in A', ‖gradient (v (θ k)) y - G y‖ ^ 2
        = ∫ y in A', ‖gradient (v (θ k)) y - G y‖ ^ 2 * η y :=
          setIntegral_congr_fun hA'm fun y hy => by rw [hηA' y hy, mul_one]
      _ ≤ ∫ y in A, ‖gradient (v (θ k)) y - G y‖ ^ 2 * η y :=
          setIntegral_mono_set i (Eventually.of_forall fun y => mul_nonneg (sq_nonneg _) (hη0 y))
            hA'A.eventuallyLE
  /- Step (e): `β₊ = β₋`. -/
  obtain ⟨φ, hφs, hφc, hφA', hjump⟩ := exists_jump_testFunction hn hν₀
  have hKA : tsupport φ ⊆ A := hφA'.trans hA'A
  have hξ : IsSmoothTestField A (fun z => φ z • ν₀) :=
    ⟨hφs.smul contDiff_const, hφc.smul_right, (tsupport_smul_subset_left _ _).trans hKA⟩
  obtain ⟨D, hD⟩ := hξ.isLipTestField.1
  have hlimQ := tendsto_integral_gradVariation (v := fun k => v (θ k)) hD
    ((tsupport_smul_subset_left _ _).trans hφA') (fun k => (hgB _).mono_measure (hle hA'B))
    (hGB.mono_measure (hle hA'B)) hSA'
  have h0 := tendsto_nhds_unique hlimQ ((hdv φ hφs hφc hKA ν₀).comp hθt)
  have hQ : ∀ᵐ y ∂(volume.restrict A'),
      (‖G y‖ ^ 2 * divergence (fun z => φ z • ν₀) y -
        2 * ⟪G y, fderiv ℝ (fun z => φ z • ν₀) y (G y)⟫) =
      -(⟪G y, ν₀⟫ ^ 2 * fderiv ℝ φ y ν₀) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hA'A htanG] with y hy
    have := quadratic_smul_const_eq (hφs.differentiable (by simp)) hν₀ ⟪G y, ν₀⟫ y
    rw [← hy] at this
    exact this
  rw [integral_congr_ae hQ, integral_neg, neg_eq_zero] at h0
  have hβsq : βp ^ 2 = βm ^ 2 := sq_eq_sq_of_integral_mul_fderiv_eq_zero
    (ae_restrict_of_ae_restrict_of_subset hA'A hside)
    (ae_restrict_of_ae_restrict_of_subset hA'A hnull)
    hφs hφc hφA' hjump h0
  have hβpm : βm = βp := le_antisymm (by nlinarith) (by nlinarith)
  /- The normalization `β = α(n)` (remark after Theorem 5.3), via the radial mass identity. -/
  have hmassF : ∫ y in A, F y ^ 2 = ∫ s in (1 / 2 : ℝ)..1, s ^ (n + 1) := by
    have hq := tendsto_integral_quadratic (μ := volume.restrict A) (F := fun k => v (θ k))
      (G := F) (fun k => hvA _) hFA (a := fun _ => 1) (A := fun _ => 0) (M := 1) zero_le_one
      aestronglyMeasurable_const aestronglyMeasurable_const (fun _ => by simp) (fun _ => by simp)
      (by simpa only [Real.norm_eq_abs, sq_abs] using hconvA)
    simp only [mul_one, ContinuousLinearMap.zero_apply, inner_zero_right, mul_zero, sub_zero,
      Real.norm_eq_abs, sq_abs] at hq
    exact tendsto_nhds_unique hq (hmass.comp hθt)
  have hFsq : ∀ᵐ y ∂(volume.restrict A), F y ^ 2 = βp ^ 2 * ⟪ν₀, y⟫ ^ 2 := by
    filter_upwards [hside, hnull] with y hs h0
    rcases lt_or_gt_of_ne h0 with hneg | hpos
    · rw [(hs.2 hneg).1, hβpm]
      ring
    · rw [(hs.1 hpos).1]
      ring
  rw [integral_congr_ae hFsq, integral_const_mul, integral_annulus_inner_sq hν₀] at hmassF
  have hm0 : 0 < ∫ s in (1 / 2 : ℝ)..1, s ^ (n + 1) :=
    intervalIntegral.intervalIntegral_pos_of_pos_on ((continuous_pow _).intervalIntegrable _ _)
      (fun s hs => pow_pos (by linarith [hs.1]) _) (by norm_num)
  have hβσ : βp ^ 2 * sphereIntegral (fun y : Rn n => y 0 ^ 2) 0 1 = 1 := by
    have h1 : (βp ^ 2 * sphereIntegral (fun y : Rn n => y 0 ^ 2) 0 1 - 1) *
        ∫ s in (1 / 2 : ℝ)..1, s ^ (n + 1) = 0 := by
      rw [sub_mul, mul_assoc, hmassF, one_mul, sub_self]
    exact sub_eq_zero.1 ((mul_eq_zero.1 h1).resolve_right hm0.ne')
  have hαβ : α = βp := by
    rw [hα, alphaN, one_div, ← Real.sqrt_inv, ← eq_inv_of_mul_eq_one_left hβσ,
      Real.sqrt_sq hβp]
  /- The profile: `v = α(n) |⟪ν₀, y⟫|` and `∇v = α(n) sgn(⟪ν₀, y⟫) ν₀` a.e. on `A`. -/
  have hFα : ∀ᵐ y ∂(volume.restrict A), F y = α * |⟪y, ν₀⟫| := by
    filter_upwards [hside, hnull] with y hs h0
    rw [real_inner_comm]
    rcases lt_or_gt_of_ne h0 with hneg | hpos
    · rw [(hs.2 hneg).1, abs_of_neg hneg, hβpm, hαβ]
    · rw [(hs.1 hpos).1, abs_of_pos hpos, hαβ]
  have hGα : ∀ᵐ y ∂(volume.restrict A),
      (0 < ⟪y, ν₀⟫ → G y = α • ν₀) ∧ (⟪y, ν₀⟫ < 0 → G y = -(α • ν₀)) := by
    filter_upwards [hside, htanG] with y hs ht
    rw [real_inner_comm]
    refine ⟨fun hp => ?_, fun hm => ?_⟩
    · rw [ht, (hs.1 hp).2, hαβ]
    · rw [ht, (hs.2 hm).2, hβpm, hαβ, neg_smul]
  have hnull' : ∀ᵐ y ∂(volume.restrict A'), ⟪y, ν₀⟫ ≠ 0 := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hA'A hnull] with y hy
    rwa [real_inner_comm]
  /- Conclusion (1): `v_{θ k} → α(n) |⟪y, ν_{θ k}⟫|` in `L²(A')`. -/
  have hvA' : ∀ k, MemLp (v k) 2 (volume.restrict A') := fun k =>
    (hvB k).mono_measure (hle hA'B)
  have hFA' : MemLp F 2 (volume.restrict A') := hFB.mono_measure (hle hA'B)
  have hball' : ∀ y ∈ A', ‖y‖ ≤ 1 := fun y hy =>
    ((mem_ball_zero_iff.1 hy.1).trans (by norm_num)).le
  have habs : ∀ k, ∀ y ∈ A', |⟪y, ν (θ k)⟫| ≤ 1 := fun k y hy =>
    (abs_real_inner_le_norm _ _).trans (by
      rw [hν, mul_one]
      exact ((mem_ball_zero_iff.1 hy.1).trans (by norm_num)).le)
  have hprof : ∀ k, MemLp (fun y => α * absProfile (ν (θ k)) 0 y) 2 (volume.restrict A') :=
    fun k => by
      refine MemLp.of_bound (continuous_const.mul
        (lipschitzWith_absProfile (hν (θ k))).continuous).aestronglyMeasurable |α| ?_
      filter_upwards [self_mem_ae_restrict hA'm] with y hy
      simp only [absProfile, sub_zero, Real.norm_eq_abs, abs_mul, abs_abs]
      exact mul_le_of_le_one_right (abs_nonneg _) (habs k y hy)
  have hR1b := tendsto_setIntegral_sq_sub_absProfile hA'm hball' hFA' (fun k => hν (θ k)) hνθ
    (ae_restrict_of_ae_restrict_of_subset hA'A hFα)
  have hR1a : Tendsto (fun k => ∫ y in A', ‖v (θ k) y - F y‖ ^ 2) atTop (𝓝 0) := by
    refine squeeze_zero (fun k => setIntegral_nonneg hA'm fun y _ => sq_nonneg _) (fun k => ?_)
      hconv
    simp only [Real.norm_eq_abs, sq_abs]
    exact setIntegral_mono_set ((hvB _).sub hFB).integrable_sq
      (Eventually.of_forall fun y => sq_nonneg _) hA'B.eventuallyLE
  have hR1 := tendsto_integral_norm_sub_sq_of_tendsto_of_tendsto (μ := volume.restrict A')
    (f := fun k => v (θ k)) (g := F) (h := fun k y => α * absProfile (ν (θ k)) 0 y)
    (fun k => hvA' _) hFA' hprof hR1a (by simpa only [Real.norm_eq_abs, sq_abs] using hR1b)
  /- Conclusion (2): `∇v_{θ k} → α(n) ∇|⟪y, ν_{θ k}⟫|` in `L²(A')`. -/
  have hgA' : ∀ k, MemLp (gradient (v k)) 2 (volume.restrict A') := fun k =>
    (hgB k).mono_measure (hle hA'B)
  have hGA' : MemLp G 2 (volume.restrict A') := hGB.mono_measure (hle hA'B)
  have hgradle : ∀ k y, ‖α • gradient (absProfile (ν (θ k)) 0) y‖ ≤ |α| := fun k y => by
    rw [norm_smul, Real.norm_eq_abs]
    refine mul_le_of_le_one_right (abs_nonneg _) ?_
    have := Kernel.norm_gradient_le_of_lipschitz (lipschitzWith_absProfile (hν (θ k))) y
    simpa using this
  have hgprof : ∀ k, MemLp (fun y => α • gradient (absProfile (ν (θ k)) 0) y) 2
      (volume.restrict A') := fun k =>
    MemLp.of_bound ((measurable_gradient _).aestronglyMeasurable.const_smul α) |α|
      (Eventually.of_forall fun y => hgradle k y)
  have hR2b := tendsto_setIntegral_norm_sub_gradient_absProfile hGA' (fun k => hν (θ k)) hνθ
    (ae_restrict_of_ae_restrict_of_subset hA'A hGα) hnull'
  have hR2 := tendsto_integral_norm_sub_sq_of_tendsto_of_tendsto (μ := volume.restrict A')
    (f := fun k => gradient (v (θ k))) (g := G)
    (h := fun k y => α • gradient (absProfile (ν (θ k)) 0) y) (fun k => hgA' _) hGA' hgprof hSA'
    hR2b
  refine ⟨θ, hθt, ?_, hR2⟩
  simpa only [Real.norm_eq_abs, sq_abs] using hR1

/-- **Theorem 5.3, steps (d)–(e) for a renormalized sequence, full sequence.** Under the hypotheses
of `exists_subseq_tendsto_profile`, on `A' = B_{7/8} \ B̄_{5/8}`,
`∫_{A'} (v_k − α(n) |⟪y, ν_k⟫|)² → 0` and `∫_{A'} |∇v_k − α(n) ∇|⟪y, ν_k⟫||² → 0`. Every
subsequence has a further subsequence along which this holds, and the limits do not depend on the
subsequence. -/
theorem tendsto_profile_of_renormalized (hn : 2 ≤ n) (v : ℕ → Rn n → ℝ) {C : ℝ}
    {ν : ℕ → Rn n} (hν : ∀ k, ‖ν k‖ = 1)
    (hLip : ∀ k, ∃ L, LipschitzOnWith L (v k) (closedBall 0 1))
    (hbd : ∀ k, ∫ y in ball (0 : Rn n) 1, (v k y ^ 2 + ‖gradient (v k) y‖ ^ 2) ≤ C)
    (hnn : ∀ k, ∀ y ∈ ball (0 : Rn n) 1, 0 ≤ v k y)
    (hE : Tendsto (fun k => ∫ y in ball (0 : Rn n) 1 \ closedBall 0 (1 / 2),
      (⟪gradient (v k) y, y⟫ - v k y) ^ 2) atTop (𝓝 0))
    (htan : Tendsto (fun k => ∫ y in ball (0 : Rn n) 1 \ closedBall 0 (1 / 2),
      ‖gradient (v k) y - ⟪gradient (v k) y, ν k⟫ • ν k‖ ^ 2) atTop (𝓝 0))
    (hmass : Tendsto (fun k => ∫ y in ball (0 : Rn n) 1 \ closedBall 0 (1 / 2), v k y ^ 2) atTop
      (𝓝 (∫ s in (1 / 2 : ℝ)..1, s ^ (n + 1))))
    (hdv : ∀ φ : Rn n → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ ball (0 : Rn n) 1 \ closedBall 0 (1 / 2) → ∀ e : Rn n,
      Tendsto (fun k => ∫ y, Kernel.gradVariation (v k) (fun z => φ z • e) y) atTop (𝓝 0))
    (henergy : ∀ η : Rn n → ℝ, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      tsupport η ⊆ ball (0 : Rn n) 1 \ closedBall 0 (1 / 2) → ∀ k,
      ∫ y, ‖gradient (v k) y‖ ^ 2 * η y = -∫ y, v k y * ⟪gradient (v k) y, gradient η y⟫) :
    Tendsto (fun k => ∫ y in ball (0 : Rn n) (7 / 8) \ closedBall 0 (5 / 8),
        (v k y - alphaN n * absProfile (ν k) 0 y) ^ 2) atTop (𝓝 0) ∧
      Tendsto (fun k => ∫ y in ball (0 : Rn n) (7 / 8) \ closedBall 0 (5 / 8),
        ‖gradient (v k) y - alphaN n • gradient (absProfile (ν k) 0) y‖ ^ 2) atTop (𝓝 0) := by
  refine ⟨tendsto_of_subseq_tendsto fun ns hns => ?_, tendsto_of_subseq_tendsto fun ns hns => ?_⟩
  · obtain ⟨θ, -, h, -⟩ := exists_subseq_tendsto_profile hn (fun k => v (ns k))
      (ν := fun k => ν (ns k)) (fun k => hν _) (fun k => hLip _) (fun k => hbd _)
      (fun k => hnn _) (hE.comp hns) (htan.comp hns) (hmass.comp hns)
      (fun φ h1 h2 h3 e => (hdv φ h1 h2 h3 e).comp hns) (fun η h1 h2 h3 k => henergy η h1 h2 h3 _)
    exact ⟨θ, h⟩
  · obtain ⟨θ, -, -, h⟩ := exists_subseq_tendsto_profile hn (fun k => v (ns k))
      (ν := fun k => ν (ns k)) (fun k => hν _) (fun k => hLip _) (fun k => hbd _)
      (fun k => hnn _) (hE.comp hns) (htan.comp hns) (hmass.comp hns)
      (fun φ h1 h2 h3 e => (hdv φ h1 h2 h3 e).comp hns) (fun η h1 h2 h3 k => henergy η h1 h2 h3 _)
    exact ⟨θ, h⟩

end Profile

end InnerVariational
