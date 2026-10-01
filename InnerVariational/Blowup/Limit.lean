/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Blowup.DomainVariation
public import InnerVariational.Blowup.OneDim
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Algebra.Order.Ring.Star
import InnerVariational.Blowup.Renormalized
public import InnerVariational.Blowup.Sobolev
import InnerVariational.Sobolev.WeakGradient
public import InnerVariational.Kernel.BV
import InnerVariational.Sobolev.Lipschitz
import InnerVariational.Defs.Calculus

/-!
# Theorem 5.3 for renormalized sequences: `N_∞ = 1`

This file assembles Lemma 5.1 and steps (a)–(c) of the proof of Theorem 5.3 of Kriventsov–Weiss
(full reference below) for an abstract renormalized sequence `v_k`. We label the paragraphs
of that proof: (a) the explicit form `β₊ (x_n)₊^N + β₋ (x_n)₋^N` of the limit; (b) strong
convergence of the gradients away from `{x_n = 0}`; (c) the limit domain variation (5.15) and
`N_∞ = 1`; (d) strong convergence on `B_{7/8} \ B_{5/8}`; (e) `β₊ = β₋`. The frequency input
(the bounds coming from `u_k` being variational solutions) is supplied in `Blowup/Approx1D.lean`.

## Main result

* `eq_one_of_renormalized`: let `v_k` be Lipschitz on `B̄_1`, nonnegative, bounded in
  `W^{1,2}(B_1)`, with vanishing Euler defect `∫_A (∇v_k·y − N v_k)² → 0` and vanishing tangential
  energy `∫_A |∇v_k − ⟪∇v_k, ν_k⟫ ν_k|² → 0` on `A = B_1 \ B̄_{1/2}`, with mass bounded below,
  `∫_A v_k² ≥ c₀ > 0`, and with vanishing domain-variation defect for the test fields `ξ = φ e`,
  `φ ∈ C_c^∞(A)`. Then `N = 1` (if `N ≠ 0`).

## Faithfulness notes

* The mass lower bound replaces the paper's normalization `∫_{∂B_1} v² = 1` and the trace
  convergence of Lemma 5.1. It is what makes `v ≢ 0`.
* The domain-variation defect is the quantity `∫ (|∇v_k|² div ξ − 2 ∇v_k·Dξ∇v_k)`. For
  `v_k = u_k/√H_k` it equals `−∫ χ_k div ξ / H_k`, which `Blowup/Approx1D.lean` bounds by
  `V_0(u_k; 1)`, as in the paragraph before (5.15) ("using that `V_0(u_k; 1) → 0`").

## References

* D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
  DOI 10.1002/cpa.22226; arXiv:2306.10131. Result and equation numbers refer to arXiv v2.
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ} [NeZero n]

/-- **Lemma 5.1 and Theorem 5.3, step (b) for a renormalized sequence: the limit data.** Let
`v_k` be Lipschitz on `B̄_1`, nonnegative, bounded in `W^{1,2}(B_1)`, with vanishing Euler defect
`∫_A (∇v_k·y − N v_k)² → 0` and vanishing tangential energy `∫_A |∇v_k − ⟪∇v_k, ν_k⟫ ν_k|² → 0`
on `A = B_1 \ B̄_{1/2}`, `‖ν_k‖ = 1`. Then along a subsequence `θ`:
* `ν_{θ k} → ν₀`, `‖ν₀‖ = 1`;
* `v_{θ k} → F` strongly in `L²(B_1)` and `∇v_{θ k} ⇀ G` weakly in `L²(B_1)`, where `G` is the weak
  gradient of `F` on `B_1` (Lemma 5.1);
* `F ≥ 0` a.e. on `B_1`, and a.e. on `A` the weak Euler identity `⟪G, y⟫ = N F` holds and
  `G = ⟪G, ν₀⟫ ν₀`;
* `∇v_{θ k} → G` strongly in `L²(K)` for every measurable `K ⊆ A` on which `|⟪ν₀, y⟫|` is bounded
  below (step (b) of the proof of Theorem 5.3). -/
theorem exists_subseq_limit_data (v : ℕ → Rn n → ℝ) {C N : ℝ}
    {ν : ℕ → Rn n} (hν : ∀ k, ‖ν k‖ = 1)
    (hLip : ∀ k, ∃ L, LipschitzOnWith L (v k) (closedBall 0 1))
    (hbd : ∀ k, ∫ y in ball (0 : Rn n) 1, (v k y ^ 2 + ‖gradient (v k) y‖ ^ 2) ≤ C)
    (hnn : ∀ k, ∀ y ∈ ball (0 : Rn n) 1, 0 ≤ v k y)
    (hE : Tendsto (fun k => ∫ y in ball (0 : Rn n) 1 \ closedBall 0 (1 / 2),
      (⟪gradient (v k) y, y⟫ - N * v k y) ^ 2) atTop (𝓝 0))
    (htan : Tendsto (fun k => ∫ y in ball (0 : Rn n) 1 \ closedBall 0 (1 / 2),
      ‖gradient (v k) y - ⟪gradient (v k) y, ν k⟫ • ν k‖ ^ 2) atTop (𝓝 0)) :
    ∃ θ : ℕ → ℕ, Tendsto θ atTop atTop ∧ ∃ ν₀ : Rn n, ‖ν₀‖ = 1 ∧
      Tendsto (fun k => ν (θ k)) atTop (𝓝 ν₀) ∧ ∃ (F : Rn n → ℝ) (G : Rn n → Rn n),
      MemLp F 2 (volume.restrict (ball 0 1)) ∧ MemLp G 2 (volume.restrict (ball 0 1)) ∧
      GMTFoundations.HasWeakGradient (ball 0 1) F G ∧
      Tendsto (fun k => ∫ y in ball (0 : Rn n) 1, (v (θ k) y - F y) ^ 2) atTop (𝓝 0) ∧
      WeakTendstoL2 (volume.restrict (ball 0 1)) (fun k => gradient (v (θ k))) G ∧
      (∀ᵐ y ∂(volume.restrict (ball (0 : Rn n) 1)), 0 ≤ F y) ∧
      (∀ᵐ y ∂(volume.restrict (ball (0 : Rn n) 1 \ closedBall 0 (1 / 2))), ⟪G y, y⟫ = N * F y) ∧
      (∀ᵐ y ∂(volume.restrict (ball (0 : Rn n) 1 \ closedBall 0 (1 / 2))),
        G y = ⟪G y, ν₀⟫ • ν₀) ∧
      ∀ K : Set (Rn n), MeasurableSet K → K ⊆ ball (0 : Rn n) 1 \ closedBall 0 (1 / 2) →
        ∀ c : ℝ, 0 < c → (∀ y ∈ K, c ≤ |⟪ν₀, y⟫|) →
        Tendsto (fun k => ∫ y in K, ‖gradient (v (θ k)) y - G y‖ ^ 2) atTop (𝓝 0) := by
  set B : Set (Rn n) := ball 0 1 with hB
  set A : Set (Rn n) := ball (0 : Rn n) 1 \ closedBall 0 (1 / 2) with hA
  have hAo : IsOpen A := isOpen_ball.sdiff isClosed_closedBall
  have hAm : MeasurableSet A := hAo.measurableSet
  have hAB : A ⊆ B := sdiff_subset
  have hle : ∀ {S : Set (Rn n)}, S ⊆ B → volume.restrict S ≤ volume.restrict B := fun h =>
    Measure.restrict_mono h le_rfl
  have hμA : (volume.restrict B).restrict A = volume.restrict A :=
    Measure.restrict_restrict_of_subset hAB
  -- A convergent subsequence of directions.
  obtain ⟨ν₀, hν₀mem, ψ, hψ, hνψ⟩ := (isCompact_sphere (0 : Rn n) 1).tendsto_subseq
    (x := ν) fun k => by simp [hν k]
  have hν₀ : ‖ν₀‖ = 1 := by simpa using hν₀mem
  -- Lemma 5.1.
  obtain ⟨φ, hφ, F, G, W, hconv, hweak, hFnn, heuler⟩ := exists_subseq_tendsto_weakEuler
    (fun k => v (ψ k)) C N (fun k => hLip _) (fun k => hbd _) (fun k => hnn _)
    (hE.comp hψ.tendsto_atTop)
  set θ : ℕ → ℕ := fun k => ψ (φ k) with hθ
  have hθt : Tendsto θ atTop atTop := (hψ.comp hφ).tendsto_atTop
  -- `L²` memberships.
  have hW : ∀ k, GMTFoundations.MemH1 B (v k) (gradient (v k)) := fun k =>
    memH1_gradient_of_lipschitzOnWith isOpen_ball isBounded_ball
      ((hLip k).choose_spec.mono ball_subset_closedBall)
  have hvB : ∀ k, MemLp (v k) 2 (volume.restrict B) := fun k => (hW k).1
  have hgB : ∀ k, MemLp (gradient (v k)) 2 (volume.restrict B) := fun k => (hW k).2.1
  have hFB : MemLp F 2 (volume.restrict B) := W.1
  have hGB : MemLp G 2 (volume.restrict B) := W.2.1
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
  -- The limit gradient is parallel to `ν₀` (Theorem 5.3, hypothesis in the limit).
  have hweakA : WeakTendstoL2 (volume.restrict A) (fun k => gradient (v (θ k))) G := by
    have := hweak.restrict hAm
    rwa [hμA] at this
  have htanθ : Tendsto (fun k => ∫ y in A, ‖tangentialPart (ν (θ k)) (gradient (v (θ k)) y)‖ ^ 2)
      atTop (𝓝 0) := by
    refine (htan.comp hθt).congr fun k => ?_
    simp only [Function.comp_apply, tangentialPart_apply, real_inner_comm]
  have hνθ : Tendsto (fun k => ν (θ k)) atTop (𝓝 ν₀) := hνψ.comp hφ.tendsto_atTop
  have hGtan : ∀ᵐ y ∂(volume.restrict A), tangentialPart ν₀ (G y) = 0 :=
    ae_tangentialPart_eq_zero_of_weakTendstoL2 hweakA (fun k => hgA _) hGA (fun k => hgA_bd _)
      (fun k => hν _) hνθ htanθ
  have hP := tendsto_integral_norm_tangentialPart_sq (fun k => hgA (θ k)) (fun k => hgA_bd _)
    (fun k => hν _) hνθ htanθ
  -- Strong `L²(A)` convergence of `v_k`.
  have hconvA : Tendsto (fun k => ∫ y in A, (v (θ k) y - F y) ^ 2) atTop (𝓝 0) := by
    refine squeeze_zero (fun k => setIntegral_nonneg hAm fun y _ => sq_nonneg _)
      (fun k => ?_) hconv
    exact setIntegral_mono_set ((hvB _).sub hFB).integrable_sq
      (Eventually.of_forall fun y => sq_nonneg _) hAB.eventuallyLE
  -- `⟪∇v_k, y⟫ → ⟪∇v, y⟫` strongly in `L²(A)` (vanishing Euler defect + weak Euler identity).
  have hGiA : MemLp (fun y => ⟪G y, y⟫) 2 (volume.restrict A) :=
    memLp_inner_id_of_subset_ball hAm hAB hGA
  have hR : Tendsto (fun k => ∫ y in A, (⟪gradient (v (θ k)) y, y⟫ - ⟪G y, y⟫) ^ 2) atTop
      (𝓝 0) := by
    have hlim := ((hE.comp hθt).const_mul 2).add (hconvA.const_mul (2 * N ^ 2))
    simp only [mul_zero, add_zero] at hlim
    refine squeeze_zero (fun k => setIntegral_nonneg hAm fun y _ => sq_nonneg _)
      (fun k => ?_) hlim
    have hIk : MemLp (fun y => ⟪gradient (v (θ k)) y, y⟫) 2 (volume.restrict A) :=
      memLp_inner_id_of_subset_ball hAm hAB (hgA _)
    have i1 : Integrable (fun y => (⟪gradient (v (θ k)) y, y⟫ - N * v (θ k) y) ^ 2)
        (volume.restrict A) := (hIk.sub ((hvA _).const_mul N)).integrable_sq
    have i2 : Integrable (fun y => (v (θ k) y - F y) ^ 2) (volume.restrict A) :=
      ((hvA _).sub hFA).integrable_sq
    calc ∫ y in A, (⟪gradient (v (θ k)) y, y⟫ - ⟪G y, y⟫) ^ 2
        ≤ ∫ y in A, (2 * (⟪gradient (v (θ k)) y, y⟫ - N * v (θ k) y) ^ 2 +
            2 * N ^ 2 * (v (θ k) y - F y) ^ 2) := by
          refine integral_mono_ae (hIk.sub hGiA).integrable_sq
            ((i1.const_mul 2).add (i2.const_mul _)) ?_
          filter_upwards [heuler] with y hy
          rw [hy]
          nlinarith [sq_nonneg ((⟪gradient (v (θ k)) y, y⟫ - N * v (θ k) y) -
            N * (v (θ k) y - F y))]
      _ = 2 * (∫ y in A, (⟪gradient (v (θ k)) y, y⟫ - N * v (θ k) y) ^ 2) +
            2 * N ^ 2 * ∫ y in A, (v (θ k) y - F y) ^ 2 := by
          rw [integral_add (i1.const_mul 2) (i2.const_mul _), integral_const_mul,
            integral_const_mul]
  have hball : ∀ᵐ y ∂(volume.restrict A), ‖y‖ ≤ 1 := by
    filter_upwards [self_mem_ae_restrict hAm] with y hy
    exact (mem_ball_zero_iff.1 hy.1).le
  refine ⟨θ, hθt, ν₀, hν₀, hνθ, F, G, hFB, hGB, W.2.2, hconv, hweak, hFnn, heuler, ?_,
    fun K hKm hKA c hc hcK => ?_⟩
  · filter_upwards [hGtan] with x hx
    exact (tangentialPart_eq_zero_iff ν₀ (G x)).1 hx
  · have hstrong := tendsto_setIntegral_norm_sub_sq_of_tangentialPart (fun k => hgA (θ k)) hGA
      hball hν₀ hGtan hP hR hKm hc hcK
    rwa [Measure.restrict_restrict_of_subset hKA] at hstrong

/-- **Theorem 5.3, steps (a)–(c), for a renormalized sequence: `N_∞ = 1`.** See the module
docstring for the hypotheses. The proof extracts a subsequence along which `ν_k → ν₀` and Lemma 5.1
applies (`exists_subseq_limit_data`). The limit `v` then satisfies the weak Euler identity,
has gradient parallel to `ν₀` (`ae_tangentialPart_eq_zero_of_weakTendstoL2`), is not `0` (mass
bound), and satisfies (5.15) for `ξ = φ ν₀` away from `{⟪ν₀, x⟫ = 0}` (steps (b)–(c)). Then
`eq_one_of_weakEuler_of_domainVariation` gives `N = 1`. -/
theorem eq_one_of_renormalized (v : ℕ → Rn n → ℝ) {C N c₀ : ℝ} (hN : N ≠ 0) (hc₀ : 0 < c₀)
    {ν : ℕ → Rn n} (hν : ∀ k, ‖ν k‖ = 1)
    (hLip : ∀ k, ∃ L, LipschitzOnWith L (v k) (closedBall 0 1))
    (hbd : ∀ k, ∫ y in ball (0 : Rn n) 1, (v k y ^ 2 + ‖gradient (v k) y‖ ^ 2) ≤ C)
    (hnn : ∀ k, ∀ y ∈ ball (0 : Rn n) 1, 0 ≤ v k y)
    (hE : Tendsto (fun k => ∫ y in ball (0 : Rn n) 1 \ closedBall 0 (1 / 2),
      (⟪gradient (v k) y, y⟫ - N * v k y) ^ 2) atTop (𝓝 0))
    (htan : Tendsto (fun k => ∫ y in ball (0 : Rn n) 1 \ closedBall 0 (1 / 2),
      ‖gradient (v k) y - ⟪gradient (v k) y, ν k⟫ • ν k‖ ^ 2) atTop (𝓝 0))
    (hmass : ∀ k, c₀ ≤ ∫ y in ball (0 : Rn n) 1 \ closedBall 0 (1 / 2), v k y ^ 2)
    (hdv : ∀ φ : Rn n → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ ball (0 : Rn n) 1 \ closedBall 0 (1 / 2) → ∀ e : Rn n,
      Tendsto (fun k => ∫ y, Kernel.gradVariation (v k) (fun z => φ z • e) y) atTop (𝓝 0)) :
    N = 1 := by
  set B : Set (Rn n) := ball 0 1 with hB
  set A : Set (Rn n) := ball (0 : Rn n) 1 \ closedBall 0 (1 / 2) with hA
  have hAo : IsOpen A := isOpen_ball.sdiff isClosed_closedBall
  have hAm : MeasurableSet A := hAo.measurableSet
  have hAB : A ⊆ B := sdiff_subset
  have hle : ∀ {S : Set (Rn n)}, S ⊆ B → volume.restrict S ≤ volume.restrict B := fun h =>
    Measure.restrict_mono h le_rfl
  obtain ⟨θ, hθt, ν₀, hν₀, -, F, G, hFB, hGB, hWB, hconv, -, -, heuler, htanG, hstrongK⟩ :=
    exists_subseq_limit_data v hν hLip hbd hnn hE htan
  have hgB : ∀ k, MemLp (gradient (v k)) 2 (volume.restrict B) := fun k =>
    (memH1_gradient_of_lipschitzOnWith isOpen_ball isBounded_ball
      ((hLip k).choose_spec.mono ball_subset_closedBall)).2.1
  have hvB : ∀ k, MemLp (v k) 2 (volume.restrict B) := fun k =>
    (memH1_gradient_of_lipschitzOnWith isOpen_ball isBounded_ball
      ((hLip k).choose_spec.mono ball_subset_closedBall)).1
  have hGtan : ∀ᵐ y ∂(volume.restrict A), tangentialPart ν₀ (G y) = 0 := by
    filter_upwards [htanG] with y hy
    exact (tangentialPart_eq_zero_iff ν₀ (G y)).2 hy
  -- Strong `L²(A)` convergence of `v_k`.
  have hconvA : Tendsto (fun k => ∫ y in A, (v (θ k) y - F y) ^ 2) atTop (𝓝 0) := by
    refine squeeze_zero (fun k => setIntegral_nonneg hAm fun y _ => sq_nonneg _)
      (fun k => ?_) hconv
    exact setIntegral_mono_set ((hvB _).sub hFB).integrable_sq
      (Eventually.of_forall fun y => sq_nonneg _) hAB.eventuallyLE
  -- `v ≢ 0` on `A` (the mass bound).
  have hv0 : ¬ F =ᵐ[volume.restrict A] 0 := by
    intro h0
    have e : ∀ k, ∫ y in A, v (θ k) y ^ 2 = ∫ y in A, (v (θ k) y - F y) ^ 2 := fun k =>
      integral_congr_ae (by filter_upwards [h0] with y hy; simp [hy])
    have h1 : Tendsto (fun k => ∫ y in A, v (θ k) y ^ 2) atTop (𝓝 0) := by
      simpa only [e] using hconvA
    have := ge_of_tendsto' h1 fun k => hmass (θ k)
    linarith
  -- Steps (b)–(c): the limit domain variation identity for `ξ = ϕ ν₀`.
  have hdvlim : ∀ ϕ : Rn n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ϕ → HasCompactSupport ϕ →
      tsupport ϕ ⊆ A ∩ {x | ⟪ν₀, x⟫ ≠ 0} →
      ∫ x in A, ⟪G x, ν₀⟫ ^ 2 * fderiv ℝ ϕ x ν₀ = 0 := by
    intro ϕ hϕ hϕc hϕA
    set K := tsupport ϕ with hK
    have hKm : MeasurableSet K := (isClosed_tsupport ϕ).measurableSet
    have hKA : K ⊆ A := hϕA.trans inter_subset_left
    obtain ⟨c, hc, hcK⟩ : ∃ c > 0, ∀ y ∈ K, c ≤ |⟪ν₀, y⟫| := by
      rcases K.eq_empty_or_nonempty with hK0 | hKne
      · exact ⟨1, one_pos, by simp [hK0]⟩
      · obtain ⟨y₀, hy₀, hmin⟩ := hϕc.isCompact.exists_isMinOn hKne
          (f := fun y : Rn n => |⟪ν₀, y⟫|)
          ((continuous_const (y := ν₀)).inner continuous_id).abs.continuousOn
        exact ⟨|⟪ν₀, y₀⟫|, abs_pos.2 (hϕA hy₀).2, fun y hy => isMinOn_iff.1 hmin y hy⟩
    have hstrong := hstrongK K hKm hKA c hc hcK
    have hξ : IsSmoothTestField A (fun z => ϕ z • ν₀) :=
      ⟨hϕ.smul contDiff_const, hϕc.smul_right, (tsupport_smul_subset_left _ _).trans hKA⟩
    obtain ⟨D, hD⟩ := hξ.isLipTestField.1
    have hlimQ := tendsto_integral_gradVariation (v := fun k => v (θ k)) hD
      (tsupport_smul_subset_left _ _) (fun k => (hgB _).mono_measure (hle (hKA.trans hAB)))
      (hGB.mono_measure (hle (hKA.trans hAB))) hstrong
    have h0 := tendsto_nhds_unique hlimQ ((hdv ϕ hϕ hϕc hKA ν₀).comp hθt)
    have hQ : ∀ᵐ y ∂(volume.restrict K),
        (‖G y‖ ^ 2 * divergence (fun z => ϕ z • ν₀) y -
          2 * ⟪G y, fderiv ℝ (fun z => ϕ z • ν₀) y (G y)⟫) =
        -(⟪G y, ν₀⟫ ^ 2 * fderiv ℝ ϕ y ν₀) := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hKA hGtan] with y hy
      rw [tangentialPart_apply, sub_eq_zero] at hy
      have := quadratic_smul_const_eq (hϕ.differentiable (by simp)) hν₀ ⟪ν₀, G y⟫ y
      rw [← hy] at this
      rw [this, real_inner_comm ν₀ (G y)]
    rw [integral_congr_ae hQ, integral_neg, neg_eq_zero] at h0
    have hf0 : ∀ x ∉ K, ⟪G x, ν₀⟫ ^ 2 * fderiv ℝ ϕ x ν₀ = 0 := fun x hx => by
      rw [fderiv_of_notMem_tsupport ℝ hx]
      simp
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => hf0 x fun h => hx (hKA h),
      ← setIntegral_eq_integral_of_forall_compl_eq_zero hf0]
    exact h0
  -- Assembly: Theorem 5.3, steps (a) + (c).
  have hWA : GMTFoundations.HasWeakGradient A F G := HasWeakGradient.mono hWB hAB
  exact eq_one_of_weakEuler_of_domainVariation (r₁ := 1 / 2) (r₂ := 1) (by norm_num)
    (by norm_num) hν₀ hN hWA heuler htanG hv0 hdvlim

end InnerVariational
