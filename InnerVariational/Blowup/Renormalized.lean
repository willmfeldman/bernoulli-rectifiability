/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Blowup.Sobolev
public import InnerVariational.Registry.Sobolev
public import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Data.Real.StarOrdered
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Ring.Star
import InnerVariational.Sobolev.Lipschitz

/-!
# Lemma 5.1: limits of renormalized blow-up sequences (analytic core)

This file proves the Sobolev part of Lemma 5.1 of Kriventsov–Weiss (full reference below). The
input is a sequence `v_k` of Lipschitz functions on
`B̄_1`, bounded in `W^{1,2}(B_1)`, nonnegative, with vanishing Euler defect
`∫_A (∇v_k·y − N v_k)² → 0` on `A = B_1 \ B̄_{1/2}`. The output is a subsequence and a limit
`v ∈ W^{1,2}(B_1)` (`GMTFoundations.MemH1`, with the weak gradient as explicit data) with:

* `v_k → v` strongly in `L²(B_1)` and `∇v_k ⇀ ∇v` weakly in `L²(B_1)`;
* `v ≥ 0` a.e. on `B_1` (Lemma 5.1 (1));
* the **weak Euler identity** `∇v(y)·y = N v(y)` a.e. on `A` (Lemma 5.1 (3), in the form
  obtained at the end of its proof).

The frequency input (the bound on `∫_{B_1} |∇v_k|²` from `V_0(u_k;1) → 0`, and equation (4.13)
integrated over `1/2 < r < 1`, which gives the vanishing Euler defect) comes from the frequency
formula of Section 4 and is combined with this file in `Blowup/Limit.lean`.

## Faithfulness notes

* Lemma 5.1 (3) is stated as the weak Euler identity, not as pointwise homogeneity via the
  trace. The Euler identity is all that the proof of Theorem 5.3 needs.
* Lemma 5.1 (4) (`∫_{∂B_1} v² = 1`) is replaced by the radial mass identity
  `∫_A v_k² → ∫_{1/2}^1 s^{n+1} ds` in the case `N_∞ = 1` (see `Blowup/Renormalization.lean`),
  so the compactness of the trace `W^{1,2}(B_1) → L²(∂B_1)` is not used.
* Lemma 5.1 (2) (subharmonicity of `v`) is not needed by Theorem 5.3 and is not formalized.

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

omit [NeZero n] in
/-- On the unit ball, `‖⟪g, y⟫‖ ≤ ‖g‖`. -/
theorem norm_inner_le_of_mem_ball_one {g y : Rn n} (hy : y ∈ ball (0 : Rn n) 1) :
    ‖⟪g, y⟫‖ ≤ ‖g‖ := by
  have hy1 : ‖y‖ ≤ 1 := (mem_ball_zero_iff.1 hy).le
  calc ‖⟪g, y⟫‖ ≤ ‖g‖ * ‖y‖ := norm_inner_le_norm g y
    _ ≤ ‖g‖ * 1 := by gcongr
    _ = ‖g‖ := mul_one _

omit [NeZero n] in
/-- `y ↦ ⟪g y, y⟫` is in `L²(Ω)` for `g ∈ L²(Ω)` and `Ω ⊆ B_1`. -/
theorem memLp_inner_id_of_subset_ball {Ω : Set (Rn n)} (hΩ : MeasurableSet Ω)
    (hΩB : Ω ⊆ ball 0 1) {g : Rn n → Rn n} (hg : MemLp g 2 (volume.restrict Ω)) :
    MemLp (fun y => ⟪g y, y⟫) 2 (volume.restrict Ω) := by
  refine hg.of_le (hg.1.inner aestronglyMeasurable_id) ?_
  filter_upwards [self_mem_ae_restrict hΩ] with y hy
  exact norm_inner_le_of_mem_ball_one (hΩB hy)

/-- If `f k → F` strongly in `L²(μ)` and `f k ≥ 0` `μ`-a.e., then `F ≥ 0` `μ`-a.e. -/
theorem ae_nonneg_of_tendsto_integral_sq_sub {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : ℕ → α → ℝ} {F : α → ℝ} (hf : ∀ k, MemLp (f k) 2 μ) (hF : MemLp F 2 μ)
    (hnn : ∀ k, ∀ᵐ x ∂μ, 0 ≤ f k x)
    (h : Tendsto (fun k => ∫ x, (f k x - F x) ^ 2 ∂μ) atTop (𝓝 0)) : ∀ᵐ x ∂μ, 0 ≤ F x := by
  set m : α → ℝ := fun x => min (F x) 0 ^ 2
  have hm_int : Integrable m μ := by
    refine hF.integrable_sq.mono'
      ((hF.1.aemeasurable.min aemeasurable_const).pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    simp only [m, Real.norm_eq_abs, abs_pow, sq_abs]
    rcases le_total 0 (F x) with h0 | h0
    · rw [min_eq_right h0]; nlinarith [sq_nonneg (F x)]
    · rw [min_eq_left h0]
  have hle : ∀ k, ∫ x, m x ∂μ ≤ ∫ x, (f k x - F x) ^ 2 ∂μ := by
    intro k
    refine integral_mono_ae hm_int ((hf k).sub hF).integrable_sq ?_
    filter_upwards [hnn k] with x hx
    simp only [m]
    rcases le_total 0 (F x) with h0 | h0
    · rw [min_eq_right h0]; nlinarith [sq_nonneg (f k x - F x)]
    · rw [min_eq_left h0]; nlinarith
  have h0 : ∫ x, m x ∂μ ≤ 0 := ge_of_tendsto' h hle
  have hm0 : ∫ x, m x ∂μ = 0 :=
    le_antisymm h0 (integral_nonneg fun x => sq_nonneg _)
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) hm_int).1 hm0
  filter_upwards [hae] with x hx
  have : min (F x) 0 = 0 := pow_eq_zero_iff two_ne_zero |>.1 hx
  exact min_eq_right_iff.1 this

/-- If `∫ ‖F‖² ≤ 0` for `F ∈ L²`, then `F = 0` a.e. -/
theorem ae_eq_zero_of_integral_norm_sq_nonpos {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {F : α → E} (hF : MemLp F 2 μ)
    (h : ∫ x, ‖F x‖ ^ 2 ∂μ ≤ 0) : F =ᵐ[μ] 0 := by
  have h0 : ∫ x, ‖F x‖ ^ 2 ∂μ = 0 := le_antisymm h (integral_nonneg fun x => sq_nonneg _)
  have hae :=
    (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) (MemLp.integrable_norm_sq hF)).1 h0
  filter_upwards [hae] with x hx
  simpa using hx

/-- **Lemma 5.1, analytic core.** Let `v_k` be Lipschitz on `B̄_1`, nonnegative
on `B_1`, with `∫_{B_1} (v_k² + |∇v_k|²) ≤ C`, and with vanishing Euler defect on
`A = B_1 \ B̄_{1/2}`: `∫_A (∇v_k·y − N v_k)² → 0`. Then along a subsequence `v_k → v` strongly
in `L²(B_1)` and `∇v_k ⇀ ∇v` weakly in `L²(B_1)`, where `v ∈ W^{1,2}(B_1)` (weak gradient `G`),
`v ≥ 0` a.e. on `B_1`, and `∇v(y)·y = N v(y)` a.e. on `A`.

The Euler identity is the last display of the proof of Lemma 5.1, which as printed reads
"`∇v(y)·y − N_∞ v(y)` almost everywhere" and is missing "`= 0`". It is obtained as there from
lower semicontinuity of the convex functional `w ↦ ∫_A |∇w·y − N w|²`. -/
theorem exists_subseq_tendsto_weakEuler (v : ℕ → Rn n → ℝ) (C N : ℝ)
    (hLip : ∀ k, ∃ L, LipschitzOnWith L (v k) (closedBall 0 1))
    (hbd : ∀ k, ∫ y in ball (0 : Rn n) 1, (v k y ^ 2 + ‖gradient (v k) y‖ ^ 2) ≤ C)
    (hnn : ∀ k, ∀ y ∈ ball (0 : Rn n) 1, 0 ≤ v k y)
    (hE : Tendsto (fun k => ∫ y in ball (0 : Rn n) 1 \ closedBall 0 (1 / 2),
      (⟪gradient (v k) y, y⟫ - N * v k y) ^ 2) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ (F : Rn n → ℝ) (G : Rn n → Rn n),
      GMTFoundations.MemH1 (ball 0 1) F G ∧
      Tendsto (fun k => ∫ y in ball (0 : Rn n) 1, (v (φ k) y - F y) ^ 2) atTop (𝓝 0) ∧
      WeakTendstoL2 (volume.restrict (ball 0 1)) (fun k => gradient (v (φ k))) G ∧
      (∀ᵐ y ∂(volume.restrict (ball (0 : Rn n) 1)), 0 ≤ F y) ∧
      (∀ᵐ y ∂(volume.restrict (ball (0 : Rn n) 1 \ closedBall 0 (1 / 2))),
        ⟪G y, y⟫ = N * F y) := by
  set B : Set (Rn n) := ball 0 1 with hB
  set A : Set (Rn n) := ball (0 : Rn n) 1 \ closedBall 0 (1 / 2) with hA
  have hAm : MeasurableSet A := measurableSet_ball.diff measurableSet_closedBall
  have hAB : A ⊆ B := diff_subset
  have hμA : (volume.restrict B).restrict A = volume.restrict A :=
    Measure.restrict_restrict_of_subset hAB
  obtain ⟨φ, hφ, F, -, G, hF, -, hG, hconv, -, hweak, -⟩ :=
    Registry.rellich_trace_weak_compactness v C hLip hbd
  -- Each `v k` is a `W^{1,2}(B_1)` function with weak gradient `gradient (v k)`.
  have hlip : ∀ k, ∃ L, LipschitzOnWith L (v k) B := fun k =>
    (hLip k).imp fun _ h => h.mono ball_subset_closedBall
  have W : ∀ k, GMTFoundations.MemH1 B (v k) (gradient (v k)) := fun k =>
    memH1_gradient_of_lipschitzOnWith isOpen_ball isBounded_ball (hlip k).choose_spec
  have hvL2 : ∀ k, MemLp (v k) 2 (volume.restrict B) := fun k => (W k).1
  have hgL2 : ∀ k, MemLp (gradient (v k)) 2 (volume.restrict B) := fun k => (W k).2.1
  have hweak' : WeakTendstoL2 (volume.restrict B) (fun k => gradient (v (φ k))) G := hweak
  have hgrad : GMTFoundations.HasWeakGradient B F G :=
    hasWeakGrad_of_tendsto (f := fun k => v (φ k)) (fun k => hvL2 _) hF hconv hG hweak'
      fun k => (W (φ k)).2.2
  refine ⟨φ, hφ, F, G, ⟨hF, hG, hgrad⟩, hconv, hweak', ?_, ?_⟩
  · -- `v ≥ 0` (Lemma 5.1 (1)).
    refine ae_nonneg_of_tendsto_integral_sq_sub (fun k => hvL2 (φ k)) hF (fun k => ?_) hconv
    filter_upwards [self_mem_ae_restrict measurableSet_ball] with y hy
    exact hnn _ y hy
  · -- The weak Euler identity (Lemma 5.1 (3), end of its proof).
    set Φ : ℕ → Rn n → ℝ := fun k y => ⟪gradient (v (φ k)) y, y⟫ - N * v (φ k) y
    set Φinf : Rn n → ℝ := fun y => ⟪G y, y⟫ - N * F y
    have hgA : ∀ k, MemLp (gradient (v k)) 2 (volume.restrict A) := fun k => by
      simpa only [hμA] using (hgL2 k).restrict A
    have hGA : MemLp G 2 (volume.restrict A) := by
      convert hG.restrict A using 1; exact hμA.symm
    have hvA : ∀ k, MemLp (v k) 2 (volume.restrict A) := fun k => by
      simpa only [hμA] using (hvL2 k).restrict A
    have hFA : MemLp F 2 (volume.restrict A) := by
      convert hF.restrict A using 1; exact hμA.symm
    have hIk : ∀ k, MemLp (fun y => ⟪gradient (v (φ k)) y, y⟫) 2 (volume.restrict A) :=
      fun k => memLp_inner_id_of_subset_ball hAm hAB (hgA _)
    have hI : MemLp (fun y => ⟪G y, y⟫) 2 (volume.restrict A) :=
      memLp_inner_id_of_subset_ball hAm hAB hGA
    -- `⟪∇v_k, y⟫ ⇀ ⟪∇v, y⟫` weakly in `L²(A)`.
    have hw1 : WeakTendstoL2 (volume.restrict A) (fun k y => ⟪gradient (v (φ k)) y, y⟫)
        (fun y => ⟪G y, y⟫) := by
      intro h hh
      have hhy : MemLp (fun y => h y • y) 2 (volume.restrict A) := by
        refine hh.of_le (hh.1.smul aestronglyMeasurable_id) ?_
        filter_upwards [self_mem_ae_restrict hAm] with y hy
        have hy1 : ‖y‖ ≤ 1 := (mem_ball_zero_iff.1 (hAB hy)).le
        rw [norm_smul]
        calc ‖h y‖ * ‖y‖ ≤ ‖h y‖ * 1 := by gcongr
          _ = ‖h y‖ := mul_one _
      have e : ∀ g : Rn n → Rn n, ∀ y, ⟪⟪g y, y⟫, h y⟫ = ⟪g y, h y • y⟫ := by
        intro g y
        rw [RCLike.inner_apply, inner_smul_right, conj_trivial]
      have hr := (hweak'.restrict hAm) (fun y => h y • y) (by rw [hμA]; exact hhy)
      rw [hμA] at hr
      simpa only [e] using hr
    -- `v_k → v` weakly in `L²(A)`.
    have hw2 : WeakTendstoL2 (volume.restrict A) (fun k => v (φ k)) F := by
      have := weakTendstoL2_of_tendsto_integral_norm_sub_sq (fun k => hvL2 (φ k)) hF
        (by simpa only [Real.norm_eq_abs, sq_abs] using hconv)
      simpa only [hμA] using this.restrict hAm
    have hw : WeakTendstoL2 (volume.restrict A) Φ Φinf := by
      have := hw1.add (hw2.const_smul (-N)) hIk (fun k => (hvA _).const_smul (-N)) hI
        (hFA.const_smul (-N))
      have e1 : Φ = fun k y => ⟪gradient (v (φ k)) y, y⟫ + (-N) • v (φ k) y := by
        funext k y
        simp only [Φ, smul_eq_mul]
        ring
      have e2 : Φinf = fun y => ⟪G y, y⟫ + (-N) • F y := by
        funext y
        simp only [Φinf, smul_eq_mul]
        ring
      rw [e1, e2]
      exact this
    have hΦk : ∀ k, MemLp (Φ k) 2 (volume.restrict A) := fun k =>
      (hIk k).sub ((hvA _).const_mul N)
    have hΦ : MemLp Φinf 2 (volume.restrict A) := hI.sub (hFA.const_mul N)
    have hlim : Tendsto (fun k => ∫ y, ‖Φ k y‖ ^ 2 ∂(volume.restrict A)) atTop (𝓝 0) := by
      simpa only [Φ, Real.norm_eq_abs, sq_abs] using hE.comp hφ.tendsto_atTop
    have hle := hw.integral_norm_sq_le_of_tendsto hΦk hΦ hlim
    filter_upwards [ae_eq_zero_of_integral_norm_sq_nonpos hΦ hle] with y hy
    simp only [Φinf, Pi.zero_apply] at hy
    linarith

end InnerVariational
