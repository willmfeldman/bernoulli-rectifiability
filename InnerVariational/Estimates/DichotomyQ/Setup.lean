/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Estimates.Dichotomy.Setup
public import InnerVariational.Frequency.SigmaHQ
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

/-!
# Theorem 6.3 with a Lipschitz coefficient: comparability and the one-step estimate

The deterministic part of the proof of Theorem 6.3 of D. Kriventsov and G. S. Weiss,
*Rectifiability, finite Hausdorff measure, and compactness for non-minimizing Bernoulli free
boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3, DOI 10.1002/cpa.22226; arXiv:2306.10131
(numbering of arXiv v2), for a variational solution with a Lipschitz coefficient `Q`
(`QBounds Ω Q L c C'`, `κ = weissKappa L c C'`). A single configuration is considered:

* a solution `(u, χ)` with `B_{50r}(x) ⊆ Ω` and the standing smallness `κ · 50 r ≤ 1/2`;
* a level `l ≤ N₊` and a tolerance `ε`;
* points `y ∈ B̄_r(x)` that are *pinched* for the modified frequency `Ñ = N + κ² s²/2`
  (`modFrequencyN`): `y ∈ closure {u > 0}`, `Z_y(t) ≥ 0` for some `t ∈ (0, r]` (`Z` is the shifted
  Weiss energy `modMonotonicityM`), `Ñ_y(20r) ≤ l` and `Ñ_y(r) > l − ε` (`IsPinchedQ`).

The proof follows the constant-coefficient case (`Estimates/Dichotomy/Setup.lean`). The one new
point is the homogeneity estimate at a pinched point: the annulus estimate with a Lipschitz
coefficient contains the term `(Ñ_y(r) − κ² (20r)²/2 − l)²`, and the shift `κ² (20r)²/2` is
controlled by the pinching itself, since the growth of `Ñ` gives
`(399/8) κ² r² ≤ Ñ_y(20r) − Ñ_y(r) < ε`.

## Main results

* `IsPinchedQ.modFrequencyN_mem`: `Ñ_y(s) ∈ (l − ε, l]` for `s ∈ [r, 20r]`.
* `IsPinchedQ.setIntegral_homogeneity_le`:
  `∫_{B_{20r}(y) ∖ B_r(y)} (∇u·(z−y) − l u)² ≤ (20r)^{n+2} H_y(u; 20r) (4ε + 144ε²)`.
* `exists_heightH_comparisonQ`: `H_a(u; 20r) ≤ K H_{a₀}(u; 10r)` for pinched `a`, `a₀`.
* `exists_tangential_boundQ`: the one-step estimate, with the factor `4ε + 144ε²`.
-/

open MeasureTheory Metric Set Filter Module InnerProductSpace
open scoped NNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational.Dichotomy

variable {n : ℕ}

/-- A point `y ∈ B̄_r(x)` is *pinched* at level `l` with tolerance `ε` for the modified frequency
`Ñ = modFrequencyN κ`: `y ∈ closure {u > 0}`, `Z_y(t) ≥ 0` for some `t ∈ (0, r]`,
`Ñ_y(20r) ≤ l` and `Ñ_y(r) > l − ε`. -/
structure IsPinchedQ (κ : ℝ) (Q u χ : Rn n → ℝ) (x : Rn n) (r l ε : ℝ) (y : Rn n) : Prop where
  mem_closedBall : y ∈ closedBall x r
  mem_closure : y ∈ closure {z | 0 < u z}
  exists_modMonotonicityM : ∃ t, 0 < t ∧ t ≤ r ∧ 0 ≤ modMonotonicityM κ Q u χ y t
  modFrequencyN_le : modFrequencyN κ Q u χ y (20 * r) ≤ l
  lt_modFrequencyN : l - ε < modFrequencyN κ Q u χ y r

namespace IsPinchedQ

variable {Ω : Set (Rn n)} {C : ℝ≥0} {Q u χ : Rn n → ℝ} {L : ℝ≥0} {c C' : ℝ} {x y : Rn n}
  {r l ε κ : ℝ}

theorem closedBall_subset (hΩ : ball x (50 * r) ⊆ Ω)
    (hy : IsPinchedQ κ Q u χ x r l ε y) {s : ℝ} (hs : s < 49 * r) : closedBall y s ⊆ Ω := by
  refine (closedBall_subset_ball' ?_).trans hΩ
  have := Metric.mem_closedBall.1 hy.mem_closedBall
  linarith

theorem mem_domain (hr : 0 < r) (hΩ : ball x (50 * r) ⊆ Ω)
    (hy : IsPinchedQ κ Q u χ x r l ε y) : y ∈ Ω :=
  hy.closedBall_subset hΩ (s := 0) (by linarith) (mem_closedBall_self le_rfl)

variable [NeZero n]

/-- At a pinched point, for `s ∈ [r, 20r]`: `Z_y(s) ≥ 0`, `Ñ_y` is nondecreasing on `[r, 20r]`,
and `Ñ_y(s) ∈ (l − ε, l]`. -/
theorem modFrequencyN_mem (hQ : QBounds Ω Q L c C') (h : IsVariationalSolutionQ Ω C Q u χ)
    (hr : 0 < r) (hκ : weissKappa L c C' * (50 * r) ≤ 1 / 2) (hΩ : ball x (50 * r) ⊆ Ω)
    (hy : IsPinchedQ (weissKappa L c C') Q u χ x r l ε y) :
    (∀ s ∈ Icc r (20 * r), 0 ≤ modMonotonicityM (weissKappa L c C') Q u χ y s) ∧
      MonotoneOn (modFrequencyN (weissKappa L c C') Q u χ y) (Icc r (20 * r)) ∧
      ∀ s ∈ Icc r (20 * r), l - ε < modFrequencyN (weissKappa L c C') Q u χ y s ∧
        modFrequencyN (weissKappa L c C') Q u χ y s ≤ l := by
  obtain ⟨t, ht, htr, hZ⟩ := hy.exists_modMonotonicityM
  have hk := hQ.weissKappa_nonneg (hy.mem_domain hr hΩ)
  have hκ20 : weissKappa L c C' * (20 * r) ≤ 1 / 2 := by nlinarith
  have hΩ20 := hy.closedBall_subset hΩ (s := 20 * r) (by linarith)
  have hmono := h.monotoneOn_modFrequencyN hQ hy.mem_closure ht hZ hκ20 hΩ20
  have hsub : Icc r (20 * r) ⊆ Icc t (20 * r) := Icc_subset_Icc_left htr
  refine ⟨fun s hs => h.modMonotonicityM_nonneg hQ hy.mem_closure ht hZ hκ20 hΩ20 (hsub hs),
    hmono.mono hsub, fun s hs => ⟨?_, ?_⟩⟩
  · exact hy.lt_modFrequencyN.trans_le
      (hmono (hsub (left_mem_Icc.2 (by linarith))) (hsub hs) hs.1)
  · exact (hmono (hsub hs) (hsub (right_mem_Icc.2 (by linarith))) hs.2).trans
      hy.modFrequencyN_le

/-- At a pinched point the pinching controls `κ r`: `(399/8) κ² r² < ε`. -/
theorem sq_mul_sq_lt (hQ : QBounds Ω Q L c C') (h : IsVariationalSolutionQ Ω C Q u χ)
    (hr : 0 < r) (hκ : weissKappa L c C' * (50 * r) ≤ 1 / 2) (hΩ : ball x (50 * r) ⊆ Ω)
    (hy : IsPinchedQ (weissKappa L c C') Q u χ x r l ε y) :
    399 / 8 * (weissKappa L c C' ^ 2 * r ^ 2) < ε := by
  obtain ⟨t, ht, htr, hZ⟩ := hy.exists_modMonotonicityM
  have hk := hQ.weissKappa_nonneg (hy.mem_domain hr hΩ)
  have hκ20 : weissKappa L c C' * (20 * r) ≤ 1 / 2 := by nlinarith
  have hΩ20 := hy.closedBall_subset hΩ (s := 20 * r) (by linarith)
  have hg := h.sq_mul_sub_sq_le_modFrequencyN_sub hQ hy.mem_closure ht hZ hκ20 hΩ20
    ⟨htr, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith : r ≤ 20 * r)
  have h1 := hy.modFrequencyN_le
  have h2 := hy.lt_modFrequencyN
  nlinarith

/-- **Integrated (4.13) at a pinched point**, with the fixed degree `l`:
`∫_{B_{20r}(y) ∖ B_r(y)} (∇u·(z − y) − l u)² ≤ (20r)^{n+2} H_y(u; 20r) (4ε + 144ε²)`. -/
theorem setIntegral_homogeneity_le (hQ : QBounds Ω Q L c C')
    (h : IsVariationalSolutionQ Ω C Q u χ) (hr : 0 < r)
    (hκ : weissKappa L c C' * (50 * r) ≤ 1 / 2) (hΩ : ball x (50 * r) ⊆ Ω)
    (hy : IsPinchedQ (weissKappa L c C') Q u χ x r l ε y) :
    ∫ z in ball y (20 * r) \ ball y r, (⟪gradient u z, z - y⟫ - l * u z) ^ 2 ≤
      (20 * r) ^ (n + 2) * heightH u y (20 * r) * (4 * ε + 144 * ε ^ 2) := by
  set κ := weissKappa L c C' with hκdef
  obtain ⟨t, ht, htr, hZ⟩ := hy.exists_modMonotonicityM
  obtain ⟨-, hmono, hN⟩ := hy.modFrequencyN_mem hQ h hr hκ hΩ
  have hk : 0 ≤ κ := hQ.weissKappa_nonneg (hy.mem_domain hr hΩ)
  have hκ20 : κ * (20 * r) ≤ 1 / 2 := by nlinarith
  have hΩ20 := hy.closedBall_subset hΩ (s := 20 * r) (by linarith)
  have hbound := h.integral_annulus_sq_inner_gradient_sub_le hQ hy.mem_closure ht htr
    (by linarith) hZ hκ20 hΩ20 l
  have hH := h.heightH_pos hQ hy.mem_closure (by linarith : (0 : ℝ) < 20 * r) hΩ20
  have hP : 0 ≤ (20 * r) ^ (n + 2) * heightH u y (20 * r) :=
    mul_nonneg (pow_nonneg (by linarith) _) hH.le
  obtain ⟨h1l, h1u⟩ := hN r (left_mem_Icc.2 (by linarith))
  obtain ⟨h2l, h2u⟩ := hN (20 * r) (right_mem_Icc.2 (by linarith))
  have hle := hmono (left_mem_Icc.2 (by linarith)) (right_mem_Icc.2 (by linarith))
    (by linarith : r ≤ 20 * r)
  have hε : 0 ≤ ε := by linarith
  have hkr := hy.sq_mul_sq_lt hQ h hr hκ hΩ
  have hkr0 : 0 ≤ κ ^ 2 * r ^ 2 := by positivity
  have hshift : κ ^ 2 * (20 * r) ^ 2 / 2 ≤ 5 * ε := by nlinarith
  have hshift0 : 0 ≤ κ ^ 2 * (20 * r) ^ 2 / 2 := by positivity
  have hsq2 : (modFrequencyN κ Q u χ y (20 * r) - l) ^ 2 ≤ ε ^ 2 :=
    sq_le_sq' (by linarith) (by linarith)
  have hsq1 : (modFrequencyN κ Q u χ y r - κ ^ 2 * (20 * r) ^ 2 / 2 - l) ^ 2 ≤ (6 * ε) ^ 2 :=
    sq_le_sq' (by linarith) (by linarith)
  have hmax : max ((modFrequencyN κ Q u χ y (20 * r) - l) ^ 2)
      ((modFrequencyN κ Q u χ y r - κ ^ 2 * (20 * r) ^ 2 / 2 - l) ^ 2) ≤ 36 * ε ^ 2 :=
    max_le (by nlinarith) (by nlinarith)
  set I := 2 * (modFrequencyN κ Q u χ y (20 * r) - modFrequencyN κ Q u χ y r) +
    2 * max ((modFrequencyN κ Q u χ y (20 * r) - l) ^ 2)
      ((modFrequencyN κ Q u χ y r - κ ^ 2 * (20 * r) ^ 2 / 2 - l) ^ 2) with hI
  have hI0 : 0 ≤ I := by
    have : 0 ≤ max ((modFrequencyN κ Q u χ y (20 * r) - l) ^ 2)
        ((modFrequencyN κ Q u χ y r - κ ^ 2 * (20 * r) ^ 2 / 2 - l) ^ 2) :=
      le_max_of_le_left (sq_nonneg _)
    rw [hI]; linarith
  have hIle : I ≤ 2 * ε + 72 * ε ^ 2 := by rw [hI]; linarith
  have hE : Real.exp (κ ^ 2 * (20 * r) ^ 2 / 8) ≤ 2 :=
    (exp_sq_mul_sq_div_eight_le hk (by linarith) hκ20).trans exp_one_div_thirtyTwo_le_two
  have hE0 : 0 ≤ Real.exp (κ ^ 2 * (20 * r) ^ 2 / 8) := (Real.exp_pos _).le
  refine hbound.trans ?_
  calc Real.exp (κ ^ 2 * (20 * r) ^ 2 / 8) * ((20 * r) ^ (n + 2) * heightH u y (20 * r)) * I
      ≤ 2 * ((20 * r) ^ (n + 2) * heightH u y (20 * r)) * (2 * ε + 72 * ε ^ 2) := by
        have := mul_le_mul hE hIle hI0 zero_le_two
        nlinarith
    _ = (20 * r) ^ (n + 2) * heightH u y (20 * r) * (4 * ε + 144 * ε ^ 2) := by ring

end IsPinchedQ

/-! ### Uniform comparability of `H` -/

/-- **Uniform comparability of `H`** with a Lipschitz coefficient. There is `K = K(n, N₊)` such
that for pinched points `a₀, a` at a level `l ≤ N₊` with `κ · 50r ≤ 1/2`,
`H_{a₀}(u; 20r) ≤ K H_{a₀}(u; 10r)` and `H_a(u; 20r) ≤ K H_{a₀}(u; 10r)`. -/
theorem exists_heightH_comparisonQ (n : ℕ) [NeZero n] (Np : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (Ω : Set (Rn n)) (C : ℝ≥0) (Q u χ : Rn n → ℝ) (L : ℝ≥0) (c C' : ℝ)
      (x a₀ a : Rn n) (r l ε : ℝ),
      QBounds Ω Q L c C' → IsVariationalSolutionQ Ω C Q u χ → 0 < r →
      weissKappa L c C' * (50 * r) ≤ 1 / 2 → ball x (50 * r) ⊆ Ω → l ≤ Np →
      IsPinchedQ (weissKappa L c C') Q u χ x r l ε a₀ →
      IsPinchedQ (weissKappa L c C') Q u χ x r l ε a →
      heightH u a₀ (20 * r) ≤ K * heightH u a₀ (10 * r) ∧
        heightH u a (20 * r) ≤ K * heightH u a₀ (10 * r) := by
  set Np' := max Np 2 with hNp'
  have hNp1 : 1 < Np' := lt_of_lt_of_le one_lt_two (le_max_right _ _)
  set K₆ := heightHChangeConst n with hK₆def
  have hK₆ : 0 < K₆ := heightHChangeConst_pos n
  set D := Abstract.RadialData.doublingConst Np' with hD
  have hDpos : 0 < D := Abstract.RadialData.doublingConst_pos _
  refine ⟨D + D * (K₆ * D), by have := mul_pos hDpos (mul_pos hK₆ hDpos); linarith, ?_⟩
  intro Ω C Q u χ L c C' x a₀ a r l ε hQ h hr hκ hΩ hl ha₀ ha
  have hk := hQ.weissKappa_nonneg (ha₀.mem_domain hr hΩ)
  have hκ20 : weissKappa L c C' * (20 * r) ≤ 1 / 2 := by nlinarith
  obtain ⟨hZ₀, -, hN₀⟩ := ha₀.modFrequencyN_mem hQ h hr hκ hΩ
  obtain ⟨hZ, -, hN⟩ := ha.modFrequencyN_mem hQ h hr hκ hΩ
  have hΩ₀ := ha₀.closedBall_subset hΩ (s := 20 * r) (by linarith)
  have hΩa := ha.closedBall_subset hΩ (s := 20 * r) (by linarith)
  have hNle : ∀ {y}, (∀ s ∈ Icc r (20 * r),
      l - ε < modFrequencyN (weissKappa L c C') Q u χ y s ∧
        modFrequencyN (weissKappa L c C') Q u χ y s ≤ l) →
      modFrequencyN (weissKappa L c C') Q u χ y (20 * r) ≤ Np' := fun hN' =>
    ((hN' (20 * r) (right_mem_Icc.2 (by linarith))).2.trans hl).trans (le_max_left _ _)
  have e4 : 20 * r / 4 = 5 * r := by ring
  -- doubling at `a₀`: `H_{a₀}(20r) ≤ D H_{a₀}(10r)`
  have hd₀ : heightH u a₀ (20 * r) ≤ D * heightH u a₀ (10 * r) :=
    (h.heightH_doubling hQ ha₀.mem_closure (t := 10 * r) (by linarith) (by linarith)
      (by linarith) (hZ₀ _ ⟨by linarith, by linarith⟩) hκ20 hΩ₀ hNp1 (hNle hN₀)
      ⟨le_rfl, by linarith⟩).2
  -- doubling at `a`: `H_a(20r) ≤ D H_a(25r/2)`
  have hda : heightH u a (20 * r) ≤ D * heightH u a (5 / 8 * (20 * r)) :=
    (h.heightH_doubling hQ ha.mem_closure (t := 10 * r) (by linarith) (by linarith)
      (by linarith) (hZ _ ⟨by linarith, by linarith⟩) hκ20 hΩa hNp1 (hNle hN)
      ⟨by linarith, by linarith⟩).2
  -- change of point from `a₀` to `a`: `H_a(25r/2) ≤ K₆ H_{a₀}(20r)`
  have hdist : a ∈ ball a₀ (20 * r / 4) := by
    rw [e4, mem_ball]
    have h1 := mem_closedBall.1 ha.mem_closedBall
    have h2 := mem_closedBall.1 ha₀.mem_closedBall
    have := dist_triangle_right a a₀ x
    linarith
  have hca := h.heightH_change_of_point_le hQ (by linarith : (0 : ℝ) < 20 * r) hΩ₀ hdist
  have hH₀ : 0 ≤ heightH u a₀ (10 * r) :=
    (h.heightH_pos hQ ha₀.mem_closure (by linarith)
      (ha₀.closedBall_subset hΩ (by linarith))).le
  have hDKD := mul_nonneg hDpos.le (mul_nonneg hK₆.le (mul_nonneg hDpos.le hH₀))
  refine ⟨hd₀.trans (by nlinarith [hDKD]), ?_⟩
  calc heightH u a (20 * r) ≤ D * heightH u a (5 / 8 * (20 * r)) := hda
    _ ≤ D * (K₆ * heightH u a₀ (20 * r)) := mul_le_mul_of_nonneg_left hca hDpos.le
    _ ≤ D * (K₆ * (D * heightH u a₀ (10 * r))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hd₀ hK₆.le) hDpos.le
    _ ≤ (D + D * (K₆ * D)) * heightH u a₀ (10 * r) := by nlinarith [mul_nonneg hDpos.le hH₀]

/-! ### The one-step estimate -/

/-- **The one-step estimate with a Lipschitz coefficient.** There is `K = K(n, N₊, δ)` with the
following property. Let `a₀` and `a_1, …, a_{n−1}` be pinched for `Ñ` at a level `l ≤ N₊` with
tolerance `ε`, with `κ · 50r ≤ 1/2`, and let the Gram–Schmidt vectors `e_i` of the `a_i − a₀` be
orthonormal combinations of the `a_j − a₀` with coefficients at most `(δr)⁻¹ (1 + 2/δ)^i`. Then
for the unit normal `ν` of the `e_i`,
`∫_{B_{10r}(a₀) ∖ B_{5r}(a₀)} |∇u − ⟪∇u, ν⟫ν|² ≤ K (4ε + 144ε²) (10r)ⁿ H_{a₀}(u; 10r)`. -/
theorem exists_tangential_boundQ (n : ℕ) [NeZero n] (Np : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (Ω : Set (Rn n)) (C : ℝ≥0) (Q u χ : Rn n → ℝ) (L : ℝ≥0) (c C' : ℝ)
      (x a₀ : Rn n) (a : Fin (n - 1) → Rn n) (r l ε : ℝ),
      QBounds Ω Q L c C' → IsVariationalSolutionQ Ω C Q u χ → 0 < r →
      weissKappa L c C' * (50 * r) ≤ 1 / 2 → ball x (50 * r) ⊆ Ω → l ≤ Np →
      IsPinchedQ (weissKappa L c C') Q u χ x r l ε a₀ →
      (∀ i, IsPinchedQ (weissKappa L c C') Q u χ x r l ε (a i)) →
      Orthonormal ℝ (gramSchmidtNormed ℝ fun j => a j - a₀) →
      (∀ i : Fin (n - 1), ∃ c : Fin (n - 1) → ℝ,
        (∀ j, |c j| ≤ (δ * r)⁻¹ * (1 + 2 / δ) ^ (i : ℕ)) ∧
        gramSchmidtNormed ℝ (fun j => a j - a₀) i = ∑ j, c j • (a j - a₀)) →
      ∃ ν : Rn n, ‖ν‖ = 1 ∧
        ∫ z in ball a₀ (10 * r) \ ball a₀ (10 * r / 2),
            ‖gradient u z - ⟪gradient u z, ν⟫ • ν‖ ^ 2 ≤
          K * (4 * ε + 144 * ε ^ 2) * ((10 * r) ^ n * heightH u a₀ (10 * r)) := by
  obtain ⟨Kc, hKc, hcomp⟩ := exists_heightH_comparisonQ n Np
  refine ⟨tangentialConst n δ Kc, tangentialConst_nonneg n hδ hKc.le, ?_⟩
  intro Ω C Q u χ L c C' x a₀ a r l ε hQ h hr hκ hΩ hl ha₀ ha he hc
  set e := gramSchmidtNormed ℝ fun j => a j - a₀ with he_def
  set w : Fin (n - 1) → Rn n := fun j => a j - a₀ with hw
  obtain ⟨ν, hν, hνe⟩ := exists_unit_forall_norm_sub_inner_smul_sq
    (Nat.sub_add_cancel (NeZero.one_le (n := n))) he
  refine ⟨ν, hν, ?_⟩
  set m : ℝ := ((n - 1 : ℕ) : ℝ) with hm
  set B := (δ * r)⁻¹ * (1 + 2 / δ) ^ n with hB
  have hbase : 1 ≤ 1 + 2 / δ := le_add_of_nonneg_right (by positivity)
  have hcB : ∀ j, ∃ c : Fin (n - 1) → ℝ, (∀ i, |c i| ≤ B) ∧ e j = ∑ i, c i • w i := by
    intro j
    obtain ⟨c, hcb, hce⟩ := hc j
    refine ⟨c, fun i => (hcb i).trans ?_, hce⟩
    have hj : (j : ℕ) ≤ n := by have := j.isLt; omega
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hbase hj) (inv_pos.2 (mul_pos hδ hr)).le
  -- the homogeneity defects
  set F : Rn n → Rn n → ℝ := fun y z => (⟪gradient u z, z - y⟫ - l * u z) ^ 2 with hF
  set A : Set (Rn n) := ball a₀ (10 * r) \ ball a₀ (10 * r / 2) with hA
  have hAm : MeasurableSet A := measurableSet_ball.diff measurableSet_ball
  have hlip := h.lipschitzOnWith x (50 * r) hΩ
  have hdist : ∀ {y : Rn n}, IsPinchedQ (weissKappa L c C') Q u χ x r l ε y →
      dist a₀ y ≤ 2 * r := fun {y} hy => by
    have h1 := mem_closedBall.1 hy.mem_closedBall
    have h2 := mem_closedBall.1 ha₀.mem_closedBall
    have := dist_triangle_right a₀ y x
    linarith
  have hAann : ∀ {y : Rn n}, IsPinchedQ (weissKappa L c C') Q u χ x r l ε y →
      A ⊆ ball y (20 * r) \ ball y r := by
    intro y hy z hz
    have hd := hdist hy
    have hz1 : dist z a₀ < 10 * r := hz.1
    have hz2 : ¬ dist z a₀ < 10 * r / 2 := hz.2
    have t1 := dist_triangle z a₀ y
    have t2 := dist_triangle z y a₀
    rw [dist_comm y a₀] at t2
    refine ⟨mem_ball.2 (by linarith), fun hzy => hz2 ?_⟩
    have : dist z y < r := hzy
    linarith
  have hannU : ∀ {y : Rn n}, IsPinchedQ (weissKappa L c C') Q u χ x r l ε y →
      ball y (20 * r) \ ball y r ⊆ ball x (50 * r) := by
    intro y hy z hz
    have h1 := mem_closedBall.1 hy.mem_closedBall
    have hz1 : dist z y < 20 * r := hz.1
    have := dist_triangle z y x
    exact mem_ball.2 (by linarith)
  have hint : ∀ {y : Rn n}, IsPinchedQ (weissKappa L c C') Q u χ x r l ε y →
      IntegrableOn (F y) A := fun {y} hy =>
    integrableOn_sq_inner_gradient_sub_mul_of_lipschitzOnWith hlip hAm
      ((hAann hy).trans (hannU hy)) _ l
  have hintA : ∀ {y : Rn n}, IsPinchedQ (weissKappa L c C') Q u χ x r l ε y →
      ∫ z in A, F y z ≤ (20 * r) ^ (n + 2) * heightH u y (20 * r) * (4 * ε + 144 * ε ^ 2) := by
    intro y hy
    refine le_trans ?_ (hy.setIntegral_homogeneity_le hQ h hr hκ hΩ)
    refine setIntegral_mono_set
      (integrableOn_sq_inner_gradient_sub_mul_of_lipschitzOnWith hlip
        (measurableSet_ball.diff measurableSet_ball) (hannU hy) _ l)
      (Eventually.of_forall fun z => sq_nonneg _) (hAann hy).eventuallyLE
  -- pointwise bound
  set G : Rn n → ℝ := fun z => m ^ 2 * B ^ 2 * ∑ i, (2 * F a₀ z + 2 * F (a i) z) with hG
  have hpt : ∀ z, ‖gradient u z - ⟪gradient u z, ν⟫ • ν‖ ^ 2 ≤ G z := by
    intro z
    rw [hG, hνe]
    dsimp only
    refine (sum_sq_inner_le_of_eq_sum_smul hcB (gradient u z)).trans ?_
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (by positivity)
    have key : ⟪w i, gradient u z⟫ = (⟪gradient u z, z - a₀⟫ - l * u z) -
        (⟪gradient u z, z - a i⟫ - l * u z) := by
      rw [hw]
      dsimp only
      rw [inner_sub_left, inner_sub_right, inner_sub_right, real_inner_comm (gradient u z) (a i),
        real_inner_comm (gradient u z) a₀]
      ring
    rw [key, hF]
    dsimp only
    nlinarith [sq_nonneg ((⟪gradient u z, z - a₀⟫ - l * u z) +
      (⟪gradient u z, z - a i⟫ - l * u z))]
  have hsumint : ∀ i, IntegrableOn (fun z => 2 * F a₀ z + 2 * F (a i) z) A :=
    fun i => (Integrable.const_mul (hint ha₀) 2).add (Integrable.const_mul (hint (ha i)) 2)
  have hGint : IntegrableOn G A := by
    rw [hG]
    exact Integrable.const_mul (integrable_finsetSum _ fun i _ => hsumint i) _
  have hle : ∫ z in A, ‖gradient u z - ⟪gradient u z, ν⟫ • ν‖ ^ 2 ≤ ∫ z in A, G z :=
    integral_mono_of_nonneg (Eventually.of_forall fun z => sq_nonneg _) hGint
      (Eventually.of_forall hpt)
  -- integrate the pointwise bound
  set H' := heightH u a₀ (10 * r) with hH'
  set P := (20 * r) ^ (n + 2) * (4 * ε + 144 * ε ^ 2) with hP
  have hε : 0 ≤ ε := by
    obtain ⟨-, hmono, -⟩ := ha₀.modFrequencyN_mem hQ h hr hκ hΩ
    have := hmono (left_mem_Icc.2 (by linarith)) (right_mem_Icc.2 (by linarith))
      (by linarith : r ≤ 20 * r)
    linarith [ha₀.lt_modFrequencyN, ha₀.modFrequencyN_le]
  have hPnn : 0 ≤ P := mul_nonneg (pow_nonneg (by linarith) _) (by positivity)
  have hGval : ∫ z in A, G z = m ^ 2 * B ^ 2 *
      ∑ i, (2 * (∫ z in A, F a₀ z) + 2 * ∫ z in A, F (a i) z) := by
    rw [hG]
    dsimp only
    rw [integral_const_mul, integral_finsetSum _ fun i _ => hsumint i]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_add (Integrable.const_mul (hint ha₀) 2) (Integrable.const_mul (hint (ha i)) 2),
      integral_const_mul, integral_const_mul]
  have hsum : ∑ i, (2 * (∫ z in A, F a₀ z) + 2 * ∫ z in A, F (a i) z) ≤
      m * (4 * P * Kc * H') := by
    calc ∑ i, (2 * (∫ z in A, F a₀ z) + 2 * ∫ z in A, F (a i) z) ≤
        ∑ _i : Fin (n - 1), (4 * P * Kc * H') := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h0 := hintA ha₀
          have hi := hintA (ha i)
          obtain ⟨hc₀, hci⟩ := hcomp Ω C Q u χ L c C' x a₀ (a i) r l ε hQ h hr hκ hΩ hl ha₀
            (ha i)
          have e1 : (20 * r) ^ (n + 2) * heightH u a₀ (20 * r) * (4 * ε + 144 * ε ^ 2) =
              P * heightH u a₀ (20 * r) := by rw [hP]; ring
          have e2 : (20 * r) ^ (n + 2) * heightH u (a i) (20 * r) * (4 * ε + 144 * ε ^ 2) =
              P * heightH u (a i) (20 * r) := by rw [hP]; ring
          rw [e1] at h0
          rw [e2] at hi
          have h0' := h0.trans (mul_le_mul_of_nonneg_left hc₀ hPnn)
          have hi' := hi.trans (mul_le_mul_of_nonneg_left hci hPnn)
          have e3 : 2 * (P * (Kc * heightH u a₀ (10 * r))) +
              2 * (P * (Kc * heightH u a₀ (10 * r))) = 4 * P * Kc * H' := by rw [hH']; ring
          exact le_trans (add_le_add (mul_le_mul_of_nonneg_left h0' zero_le_two)
            (mul_le_mul_of_nonneg_left hi' zero_le_two)) (le_of_eq e3)
      _ = m * (4 * P * Kc * H') := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hB2 : 0 ≤ m ^ 2 * B ^ 2 := by positivity
  calc ∫ z in A, ‖gradient u z - ⟪gradient u z, ν⟫ • ν‖ ^ 2 ≤ ∫ z in A, G z := hle
    _ = m ^ 2 * B ^ 2 * ∑ i, (2 * (∫ z in A, F a₀ z) + 2 * ∫ z in A, F (a i) z) := hGval
    _ ≤ m ^ 2 * B ^ 2 * (m * (4 * P * Kc * H')) :=
        mul_le_mul_of_nonneg_left hsum hB2
    _ = tangentialConst n δ Kc * (4 * ε + 144 * ε ^ 2) * ((10 * r) ^ n * H') := by
      rw [hB, hP, hm, tangentialConst, pow_mul']
      generalize (1 + 2 / δ) ^ n = X
      have hr0 : r ≠ 0 := hr.ne'
      have hδ0 : δ ≠ 0 := hδ.ne'
      field_simp
      ring

end InnerVariational.Dichotomy
