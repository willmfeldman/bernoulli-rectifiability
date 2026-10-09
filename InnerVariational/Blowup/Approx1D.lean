/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Blowup.Profile
public import InnerVariational.Blowup.Approx1DQ
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Algebra.Order.Ring.Star
import InnerVariational.Blowup.Renormalization
import InnerVariational.Blowup.Limit
import InnerVariational.Frequency.Concrete
import InnerVariational.Monotonicity.Radial
public import InnerVariational.Defs.Quantities
public import InnerVariational.Kernel.BV
import InnerVariational.Kernel.Subharmonic
import InnerVariational.Sobolev.Lipschitz

/-!
# Frequency blow-ups: Lemma 5.1 and Theorem 5.3 in the form used later

Lemma 5.1 and Theorem 5.3 of Kriventsov–Weiss (full reference below), stated for the
variational solutions `u_k` themselves, in the form used by the proofs of Theorem 6.3 (frequency
drop dichotomy, `Estimates/Dichotomy.lean`) and Lemma 8.5 (singular points of density one,
`Singular/FlatPoint.lean`). The statements do not mention Sobolev spaces; the Sobolev machinery
stays inside `InnerVariational/Blowup/`.

## Setting (the standing assumptions of Section 5)

`(u_k, χ_k)` are variational solutions on `Ω ⊇ B̄_2` with
* `0 ∈ closure {u_k > 0}` and `M_0(u_k; 1/2) ≥ |B_1|` (the paper writes `M_0(u; 1/2)`, and
  `0 ∈ {u_k > 0}` and `B_2 ⊆ Ω`; we use the closure and `B̄_2 ⊆ Ω`);
* `N_0(u_k; 2) ≤ N₊` and `δ_k = N_0(u_k; 2) − N_0(u_k; 1/2) → 0`.

The Lipschitz constants `C_V k` may vary with `k`. The paper imposes no uniform bound, and none is
kept under the renormalization `v_k = u_k / √H_0(u_k; 1)`.

## Main statements

* `approx1D_limit_frequency_eq_one`: Theorem 5.3's conclusion `N_∞ = 1` in its direction-free
  form. If the tangential energy `∫_A |∇u_k − ⟪∇u_k, ν_k⟫ν_k|² / H_0(u_k; 1)` tends to `0` on
  `A = B_1 \ B̄_{1/2}` for unit vectors `ν_k`, then `N_0(u_k; 1/2) → 1`.
* `approx1D_limit_tendsto_profile`: the refined form used in the proof of Lemma 8.5.
  `v_k − α(n)|y·ν_k| → 0` strongly in `W^{1,2}(B_{7/8} \ B̄_{5/8})`, written with `u_k` and
  `H_0(u_k; 1)` in the style of `Statements.main_theorem_iv`.

## Proof of `approx1D_limit_frequency_eq_one`

Every subsequence has a further subsequence along which `N_0(u_k; 1/2) → N_∞ ∈ [1, N₊]`
(`eq_one_of_tendsto_frequencyN_half` shows `N_∞ = 1`). There the renormalized sequence
`v_k = u_k / √H_0(u_k; 1)` is fed to `eq_one_of_renormalized` (`Blowup/Limit.lean`: Lemma 5.1 and
steps (a)–(c) of the proof of Theorem 5.3); the frequency input comes from
`Blowup/Renormalization.lean` (Lemmas 4.1, 4.3–4.5 and equation (4.13) integrated over `A`). The
only compactness theorem used is Rellich's (`Registry.rellich_trace_weak_compactness`).
The hypothesis `2 ≤ n` is not used here: step (a) is argued on the connected half-annuli
(`Blowup/ExplicitForm.lean`), which works for every `n`.

## Proof of `approx1D_limit_tendsto_profile`

`renormalized_properties` collects the facts about `v_k` (including the energy identity and, since
`N_0(u_k; 1/2) → 1`, the radial mass identity `∫_A v_k² → ∫_{1/2}^1 s^{n+1} ds`), and
`tendsto_profile_of_renormalized` (`Blowup/Profile.lean`: Theorem 5.3, steps (d)–(e) and the
normalization `β = α(n)`) gives the `W^{1,2}(A')` convergence. Again only Rellich's theorem
is used; the compactness of the trace on `∂B_1` is not.

## Faithfulness notes

* **Direction-free form, direction depending on `k`.** Rotate each `u_k` by an isometry `R_k`
  with `R_k e_n = ν_k`. Every hypothesis and conclusion concerns one `u_k` at a time and is
  invariant under isometries fixing `0`, so this form is equivalent to the paper's coordinate
  form and not stronger. It spares the users the rotation step: in the proof of Theorem 6.3 the
  basis `e_1, …, e_n` is built from the points `a_i^k`, so the direction `e_n` depends on `k`.
* **Full sequence.** The paper's conclusions hold along the subsequence of Lemma 5.1. Their
  limits (`1`, and the profile `α(n)|y·ν_k|` in rotated coordinates) do not depend on the
  subsequence, and every hypothesis passes to subsequences. So the full sequence converges.
* **Independence of `x'`.** The paper calls the `x'`-independence of the limit "immediate from
  the assumption". For `n = 2` it does not follow from the vanishing of tangential derivatives
  alone; it uses the homogeneity of the limit. We use the weak Euler identity on the two
  half-annuli (`Blowup/ExplicitForm.lean`).
* **Scale in the proof of Theorem 6.3.** The paper renormalizes at scale `18` there, which uses
  frequency pinching on `[9, 36]`, while `[1, 20]` is what is controlled. We apply these
  statements at scale `10` (see `approx1D_limit_frequency_eq_one`).

## References

* D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
  DOI 10.1002/cpa.22226; arXiv:2306.10131. Result and equation numbers refer to arXiv v2.
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

/-- For `Q ≡ 1` (`L = 0`, `c = C' = 1`, so `κ = 0`), the hypotheses of the Lipschitz-coefficient
form of Theorem 5.3 follow from those of the constant-coefficient form: `Z_0(u_k; 1/2) ≥ 0`, and
`Ñ_0(u_k; s) = N_0(u_k; s)` for `0 < s ≤ 2`. -/
private theorem one_hypotheses [NeZero n] {Ω : Set (Rn n)} {C_V : ℕ → ℝ≥0} {u χ : ℕ → Rn n → ℝ}
    (hsol : ∀ k, IsVariationalSolution Ω (C_V k) (u k) (χ k))
    (hΩ : closedBall (0 : Rn n) 2 ⊆ Ω)
    (hM : ∀ k, unitBallVolume n ≤ monotonicityM (u k) (χ k) 0 (1 / 2)) :
    (∀ k, 0 ≤ modMonotonicityM (weissKappa 0 1 1) (fun _ => 1) (u k) (χ k) 0 (1 / 2)) ∧
    ∀ k s, 0 < s → s ≤ 2 →
      modFrequencyN (weissKappa 0 1 1) (fun _ => 1) (u k) (χ k) 0 s =
        frequencyN (u k) (χ k) 0 s := by
  have hb : ∀ s : ℝ, s ≤ 2 → ball (0 : Rn n) s ⊆ Ω := fun s hs =>
    ball_subset_closedBall.trans ((closedBall_subset_closedBall hs).trans hΩ)
  refine ⟨fun k => ?_, fun k s hs hs2 => ?_⟩
  · rw [weissKappa_zero, (hsol k).modMonotonicityM_one (by norm_num) (hb _ (by norm_num))]
    linarith [hM k]
  · rw [weissKappa_zero, (hsol k).modFrequencyN_one hs (hb s hs2)]

/-- **The renormalized sequence `v_k = u_k / √H_0(u_k; 1)` and its properties** (the setting of
Section 5 and the proof of Lemma 5.1). Under the hypotheses of `approx1D_limit_frequency_eq_one`,
with
`N_0(u_k; 1/2) → N_∞`:
* `v_k` is Lipschitz on `B̄_1`, nonnegative, and bounded in `W^{1,2}(B_1)`: `∫_{B_1} v_k² ≤ 1` and
  `∫_{B_1} |∇v_k|² = N(1) + V(1)` (by (4.11), as in the proof of Lemma 5.1);
* the Euler defect `∫_A (∇v_k·y − N_∞ v_k)²` tends to `0` ((4.13) integrated over `A`, as in the
  proof of Lemma 5.1);
* the tangential energy tends to `0` (the hypothesis);
* the mass on `A` is bounded below (Lemma 4.3);
* the domain-variation defect `≤ n D V_0(u_k; 1)` tends to `0` (Lemma 4.5, as in step (c) of the
  proof of Theorem 5.3);
* the energy identity `∫ |∇v_k|² η = −∫ v_k ∇v_k·∇η` holds for `η ∈ C_c^∞(A)` (`v_k` is harmonic
  where positive, as in step (d) of the proof of Theorem 5.3);
* if `N_∞ = 1`, then `∫_A v_k² → ∫_{1/2}^1 s^{n+1} ds` (Lemma 4.3 with `C(N₊) → 1`; this radial
  mass identity replaces the normalization `∫_{∂B_1} v_k² = 1`). -/
theorem renormalized_properties [NeZero n] {Ω : Set (Rn n)}
    {C_V : ℕ → ℝ≥0} {u χ : ℕ → Rn n → ℝ} {Nplus : ℝ} {ν : ℕ → Rn n}
    (hsol : ∀ k, IsVariationalSolution Ω (C_V k) (u k) (χ k))
    (hΩ : closedBall (0 : Rn n) 2 ⊆ Ω)
    (hcl : ∀ k, (0 : Rn n) ∈ closure {y | 0 < u k y})
    (hM : ∀ k, unitBallVolume n ≤ monotonicityM (u k) (χ k) 0 (1 / 2))
    (hN : ∀ k, frequencyN (u k) (χ k) 0 2 ≤ Nplus)
    (hδ : Tendsto (fun k => frequencyN (u k) (χ k) 0 2 - frequencyN (u k) (χ k) 0 (1 / 2))
      atTop (𝓝 0))
    (htan : Tendsto (fun k => (∫ y in ball (0 : Rn n) 1 \ closedBall 0 (1 / 2),
        ‖gradient (u k) y - ⟪gradient (u k) y, ν k⟫ • ν k‖ ^ 2) / heightH (u k) 0 1) atTop (𝓝 0))
    {Ninf : ℝ} (hlim : Tendsto (fun k => frequencyN (u k) (χ k) 0 (1 / 2)) atTop (𝓝 Ninf))
    (v : ℕ → Rn n → ℝ) (hv : ∀ k y, v k y = (√(heightH (u k) 0 1))⁻¹ * u k y) :
    (∀ k, ∃ L, LipschitzOnWith L (v k) (closedBall 0 1)) ∧
    (∃ C, ∀ k, ∫ y in ball (0 : Rn n) 1, (v k y ^ 2 + ‖gradient (v k) y‖ ^ 2) ≤ C) ∧
    (∀ k, ∀ y ∈ ball (0 : Rn n) 1, 0 ≤ v k y) ∧
    Tendsto (fun k => ∫ y in ball (0 : Rn n) 1 \ closedBall 0 (1 / 2),
      (⟪gradient (v k) y, y⟫ - Ninf * v k y) ^ 2) atTop (𝓝 0) ∧
    Tendsto (fun k => ∫ y in ball (0 : Rn n) 1 \ closedBall 0 (1 / 2),
      ‖gradient (v k) y - ⟪gradient (v k) y, ν k⟫ • ν k‖ ^ 2) atTop (𝓝 0) ∧
    (∃ c₀ : ℝ, 0 < c₀ ∧ ∀ k, c₀ ≤ ∫ y in ball (0 : Rn n) 1 \ closedBall 0 (1 / 2), v k y ^ 2) ∧
    (∀ φ : Rn n → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ ball (0 : Rn n) 1 \ closedBall 0 (1 / 2) → ∀ e : Rn n,
      Tendsto (fun k => ∫ y, Kernel.gradVariation (v k) (fun z => φ z • e) y) atTop (𝓝 0)) ∧
    (∀ η : Rn n → ℝ, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      tsupport η ⊆ ball (0 : Rn n) 1 \ closedBall 0 (1 / 2) → ∀ k,
      ∫ y, ‖gradient (v k) y‖ ^ 2 * η y = -∫ y, v k y * ⟪gradient (v k) y, gradient η y⟫) ∧
    (Ninf = 1 → Tendsto (fun k => ∫ y in ball (0 : Rn n) 1 \ closedBall 0 (1 / 2), v k y ^ 2)
      atTop (𝓝 (∫ s in (1 / 2 : ℝ)..1, s ^ (n + 1)))) := by
  obtain ⟨hZ, hE⟩ := one_hypotheses hsol hΩ hM
  have e2 := fun k => hE k 2 two_pos le_rfl
  have e12 := fun k => hE k (1 / 2) (by norm_num) (by norm_num)
  exact renormalizedQ_properties (Q := fun _ _ => 1) (L := fun _ => 0) (c := fun _ => 1)
    (C' := fun _ => 1)
    (fun _ => QBounds.one Ω) (fun k => (hsol k).toQ) hΩ (fun _ => by simp [weissKappa_zero]) hcl
    hZ (fun k => (e2 k).trans_le (hN k)) (by simpa only [e2, e12] using hδ) htan
    (by simpa only [e12] using hlim) v hv

/-- **Theorem 5.3 along a sequence with `N_0(u_k; 1/2) → N_∞`: `N_∞ = 1`.** This is the core of
`approx1D_limit_frequency_eq_one`. The renormalized sequence `v_k = u_k / √H_0(u_k; 1)` satisfies
the hypotheses of `eq_one_of_renormalized` (`renormalized_properties`). -/
theorem eq_one_of_tendsto_frequencyN_half [NeZero n] {Ω : Set (Rn n)}
    {C_V : ℕ → ℝ≥0} {u χ : ℕ → Rn n → ℝ} {Nplus : ℝ} {ν : ℕ → Rn n} (hν : ∀ k, ‖ν k‖ = 1)
    (hsol : ∀ k, IsVariationalSolution Ω (C_V k) (u k) (χ k))
    (hΩ : closedBall (0 : Rn n) 2 ⊆ Ω)
    (hcl : ∀ k, (0 : Rn n) ∈ closure {y | 0 < u k y})
    (hM : ∀ k, unitBallVolume n ≤ monotonicityM (u k) (χ k) 0 (1 / 2))
    (hN : ∀ k, frequencyN (u k) (χ k) 0 2 ≤ Nplus)
    (hδ : Tendsto (fun k => frequencyN (u k) (χ k) 0 2 - frequencyN (u k) (χ k) 0 (1 / 2))
      atTop (𝓝 0))
    (htan : Tendsto (fun k => (∫ y in ball (0 : Rn n) 1 \ closedBall 0 (1 / 2),
        ‖gradient (u k) y - ⟪gradient (u k) y, ν k⟫ • ν k‖ ^ 2) / heightH (u k) 0 1) atTop (𝓝 0))
    {Ninf : ℝ} (hlim : Tendsto (fun k => frequencyN (u k) (χ k) 0 (1 / 2)) atTop (𝓝 Ninf)) :
    Ninf = 1 := by
  have hNinf : 1 ≤ Ninf := ge_of_tendsto' hlim fun k =>
    ((hsol k).frequencyN_half_le_one_le_two hΩ (hcl k) (hM k)).1
  obtain ⟨hLip, ⟨C, hbd⟩, hnn, hE, htan', ⟨c₀, hc₀, hmass⟩, hdv, -, -⟩ :=
    renormalized_properties hsol hΩ hcl hM hN hδ htan hlim _ fun _ _ => rfl
  exact eq_one_of_renormalized _ (by linarith) hc₀ hν hLip hbd hnn hE htan' hmass hdv

/-- **Theorem 5.3, direction-free form for the solutions `u_k`: `N_∞ = 1`.**
Let `(u_k, χ_k)` be variational solutions on `Ω ⊇ B̄_2` (constants `C_V k`, not uniform) with
`0 ∈ closure {u_k > 0}`, `M_0(u_k; 1/2) ≥ |B_1|`, `N_0(u_k; 2) ≤ N₊`, and
`N_0(u_k; 2) − N_0(u_k; 1/2) → 0`. Suppose that for unit vectors `ν_k` the tangential part of
the renormalized energy on `A = B_1 \ B̄_{1/2}` vanishes in the limit:
`∫_A |∇u_k − ⟪∇u_k, ν_k⟫ ν_k|² / H_0(u_k; 1) → 0`. Then `N_0(u_k; 1/2) → 1`.

This is the paper's hypothesis `Σ_{i<n} ∫_A |∂_i v_k|² → 0` for `v_k = u_k/√H_0(u_k;1)`, with
`e_n` replaced by `ν_k`. Rotating `u_k` by an
isometry sending `e_n` to `ν_k` reduces this form to the paper's. The paper concludes along
the subsequence of Lemma 5.1. The limit `1` does not depend on the subsequence, so the whole
sequence converges.

**Use in the proof of Theorem 6.3.** The paper renormalizes at `a_0^k` at scale `18`, which
uses the pinching `N_{a_0}(u_k; 36) − N_{a_0}(u_k; 9) → 0`, while `[1, 20]` is the range
controlled. We apply this theorem to `ũ_k(y) = u_k(a_0 + 10 y)/10` instead
(any scale in `[8, 10]` works). The pinching interval `[1/2, 2]` then maps into
`[5, 20] ⊆ [1, 20]`, and `A ↦ B_{10}(a_0) \ B̄_5(a_0) ⊆ B_{18}(a_0) \ B_4(a_0)`. -/
theorem approx1D_limit_frequency_eq_one [NeZero n] (_hn : 2 ≤ n) {Ω : Set (Rn n)}
    {C_V : ℕ → ℝ≥0} {u χ : ℕ → Rn n → ℝ} {Nplus : ℝ} {ν : ℕ → Rn n} (hν : ∀ k, ‖ν k‖ = 1)
    (hsol : ∀ k, IsVariationalSolution Ω (C_V k) (u k) (χ k))
    (hΩ : closedBall (0 : Rn n) 2 ⊆ Ω)
    (hcl : ∀ k, (0 : Rn n) ∈ closure {y | 0 < u k y})
    (hM : ∀ k, unitBallVolume n ≤ monotonicityM (u k) (χ k) 0 (1 / 2))
    (hN : ∀ k, frequencyN (u k) (χ k) 0 2 ≤ Nplus)
    (hδ : Tendsto (fun k => frequencyN (u k) (χ k) 0 2 - frequencyN (u k) (χ k) 0 (1 / 2))
      atTop (𝓝 0))
    (htan : Tendsto (fun k => (∫ y in ball (0 : Rn n) 1 \ closedBall 0 (1 / 2),
        ‖gradient (u k) y - ⟪gradient (u k) y, ν k⟫ • ν k‖ ^ 2) / heightH (u k) 0 1) atTop (𝓝 0)) :
    Tendsto (fun k => frequencyN (u k) (χ k) 0 (1 / 2)) atTop (𝓝 1) := by
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  have hfreq := fun k => (hsol k).frequencyN_half_le_one_le_two hΩ (hcl k) (hM k)
  have hb : ∀ k, frequencyN (u (ns k)) (χ (ns k)) 0 (1 / 2) ∈ Icc 1 Nplus := fun k =>
    ⟨(hfreq _).1, (hfreq _).2.1.trans ((hfreq _).2.2.trans (hN _))⟩
  obtain ⟨Ninf, -, ms, hms, hlim⟩ := isCompact_Icc.tendsto_subseq hb
  have hns' : Tendsto (fun k => ns (ms k)) atTop atTop := hns.comp hms.tendsto_atTop
  have h1 := eq_one_of_tendsto_frequencyN_half (u := fun k => u (ns (ms k)))
    (χ := fun k => χ (ns (ms k))) (C_V := fun k => C_V (ns (ms k))) (ν := fun k => ν (ns (ms k)))
    (fun k => hν _) (fun k => hsol _) hΩ (fun k => hcl _) (fun k => hM _) (fun k => hN _)
    (hδ.comp hns') (htan.comp hns') (Ninf := Ninf) hlim
  exact ⟨ms, h1 ▸ hlim⟩

/-- **Theorem 5.3, refined form (strong `W^{1,2}` convergence on `A' = B_{7/8} \ B̄_{5/8}`).**
Under the hypotheses of `approx1D_limit_frequency_eq_one`, with `H_k = H_0(u_k; 1)`:
* `N_0(u_k; 1/2) → 1`;
* `∫_{A'} (u_k − √H_k α(n) |y·ν_k|)² / H_k → 0`;
* `∫_{A'} |∇u_k − √H_k α(n) ∇|y·ν_k||² / H_k → 0`.

The last two say `v_k = u_k/√H_k` is `W^{1,2}(A')`-close to `α(n)|y·ν_k|`. For constant `ν_k = ν`
this is strong convergence `v_k → α(n)|y·ν|`. This is the paper's `v = α(n)|x_n|` on `A` (the
conclusion of Theorem 5.3, with `α(n)` fixed by the normalization) together with the strong
convergence on `A'` from step (d) of its proof. The proof is `tendsto_profile_of_renormalized`
applied to `v_k = u_k/√H_k` (`renormalized_properties`). `∇|y·ν_k|` is Mathlib's `gradient`,
which is `sgn(y·ν_k) ν_k` off the null hyperplane `{y·ν_k = 0}`. The paper gets these along a
subsequence. The limit profile does not depend on the subsequence, so they hold for the whole
sequence. -/
theorem approx1D_limit_tendsto_profile [NeZero n] (hn : 2 ≤ n) {Ω : Set (Rn n)}
    {C_V : ℕ → ℝ≥0} {u χ : ℕ → Rn n → ℝ} {Nplus : ℝ} {ν : ℕ → Rn n} (hν : ∀ k, ‖ν k‖ = 1)
    (hsol : ∀ k, IsVariationalSolution Ω (C_V k) (u k) (χ k))
    (hΩ : closedBall (0 : Rn n) 2 ⊆ Ω)
    (hcl : ∀ k, (0 : Rn n) ∈ closure {y | 0 < u k y})
    (hM : ∀ k, unitBallVolume n ≤ monotonicityM (u k) (χ k) 0 (1 / 2))
    (hN : ∀ k, frequencyN (u k) (χ k) 0 2 ≤ Nplus)
    (hδ : Tendsto (fun k => frequencyN (u k) (χ k) 0 2 - frequencyN (u k) (χ k) 0 (1 / 2))
      atTop (𝓝 0))
    (htan : Tendsto (fun k => (∫ y in ball (0 : Rn n) 1 \ closedBall 0 (1 / 2),
        ‖gradient (u k) y - ⟪gradient (u k) y, ν k⟫ • ν k‖ ^ 2) / heightH (u k) 0 1) atTop (𝓝 0)) :
    Tendsto (fun k => frequencyN (u k) (χ k) 0 (1 / 2)) atTop (𝓝 1) ∧
    Tendsto (fun k => (∫ y in ball (0 : Rn n) (7 / 8) \ closedBall 0 (5 / 8),
        (u k y - √(heightH (u k) 0 1) * alphaN n * absProfile (ν k) 0 y) ^ 2) /
          heightH (u k) 0 1) atTop (𝓝 0) ∧
    Tendsto (fun k => (∫ y in ball (0 : Rn n) (7 / 8) \ closedBall 0 (5 / 8),
        ‖gradient (u k) y -
          (√(heightH (u k) 0 1) * alphaN n) • gradient (absProfile (ν k) 0) y‖ ^ 2) /
          heightH (u k) 0 1) atTop (𝓝 0) := by
  obtain ⟨hZ, hE⟩ := one_hypotheses hsol hΩ hM
  have e2 := fun k => hE k 2 two_pos le_rfl
  have e12 := fun k => hE k (1 / 2) (by norm_num) (by norm_num)
  exact ⟨approx1D_limit_frequency_eq_one hn hν hsol hΩ hcl hM hN hδ htan,
    (approx1DQ_limit_tendsto_profile (Q := fun _ _ => 1) (L := fun _ => 0) (c := fun _ => 1)
      (C' := fun _ => 1) hn hν
      (fun _ => QBounds.one Ω) (fun k => (hsol k).toQ) hΩ (fun _ => by simp [weissKappa_zero]) hcl
      hZ (fun k => (e2 k).trans_le (hN k)) (by simpa only [e2, e12] using hδ) htan).2⟩

end InnerVariational
