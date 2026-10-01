/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Frequency.Concrete
public import InnerVariational.Estimates.Dichotomy.Rescale
public import InnerVariational.Estimates.GeneralPosition
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import InnerVariational.Homogeneity.RayCalculus
public import InnerVariational.Defs.Quantities
public import InnerVariational.Defs.VariationalSolution

/-!
# Theorem 6.3: uniform comparability and the one-step estimate

This file contains the deterministic part of the proof of Theorem 6.3 of D. Kriventsov and
G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for non-minimizing
Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3, DOI 10.1002/cpa.22226;
arXiv:2306.10131 (numbering of arXiv v2). A single configuration is considered, with no sequence
and no limit:

* a variational solution `(u, χ)` with `B̄_{50r}(x) ⊆ Ω`;
* a level `l ≤ N₊` and a tolerance `ε ≥ 0`;
* points `y ∈ B̄_r(x)` that are *pinched*: `y ∈ closure {u > 0}`, `M_y(u; t) ≥ |B_1|` for some
  `t ∈ (0, r]`, `N_y(u; 20r) ≤ l` and `N_y(u; r) > l − ε` (`IsPinched`).

In the proof of Theorem 6.3, `l` is the maximal frequency `N̄` and the pinched points are the
points of the set `E`.

## Main results

* `IsPinched.frequencyN_mem`: `N_y(u; s) ∈ (l − ε, l]` for `s ∈ [r, 20r]`.
* `IsPinched.setIntegral_homogeneity_le`: the integrated (4.13) at a pinched point with the fixed
  degree `l`, `∫_{B_{20r}(y) ∖ B_r(y)} (∇u·(z−y) − l u)² ≤ (20r)^{n+2} H_y(u; 20r) (ε + 2ε²)`.
* `exists_heightH_comparison`: uniform comparability of `H`,
  `H_{a}(u; 20r) ≤ K H_{a₀}(u; 10r)` for pinched `a`, `a₀` with `|a − a₀| ≤ 2r`.
* `exists_unit_forall_norm_sub_inner_smul_sq`: the unit normal `ν` of an orthonormal family of
  `n − 1` vectors, with `|g − ⟪g,ν⟫ν|² = Σ_j ⟪e_j, g⟫²`.
* `exists_tangential_bound`: the one-step estimate. For pinched `a₀, a_1, …, a_{n−1}` in
  `δ r`-general position, the tangential energy of `u` on `B_{10r}(a₀) ∖ B_{5r}(a₀)` with
  respect to the unit normal `ν` of the `a_i − a₀` is at most `K (ε + 2ε²) (10r)^n H_{a₀}(u; 10r)`,
  with `K = K(n, N₊, δ)`.

## Deviations from the paper's proof

* **Lemma 6.2 is not used.** The paper applies Lemma 6.2 to pass from the
  homogeneity about `a₀` and about `a_i` to the smallness of `∇u·(a_i − a₀)`. Both degrees are the
  same number `N̄`, so the first step of the proof of Lemma 6.2 suffices:
  `∇u·(a_i − a₀) = (∇u·(z − a₀) − N̄u) − (∇u·(z − a_i) − N̄u)`. This also avoids a boundary case of
  the paper's argument: Lemma 6.2 is stated for `x ∈ B_1` (open), but it is applied at scale
  `ρ = 2` to points with `|a_i − a₀| ≤ 2` (equality is possible, for two antipodal points of
  `∂B_1`), and then no admissible scale exists.
* **Scale 10.** We renormalize at scale `10` rather than `18` (paper), because the frequency
  pinching is available on `[1, 20]`. The annulus is `B_{10r}(a₀) ∖ B_{5r}(a₀)`, the image of
  the annulus `B_1 ∖ B̄_{1/2}` of Theorem 5.3 under `y ↦ a₀ + 10 r y`, and `[1/2, 2] ↦ [5r, 20r]`.
* **Comparability of `H`.** The paper compares every `H_y(u; s)` with `H_0(u; 50)`
  through Lemma 4.6 centred at `0`. Lemma 4.6 needs its centre in `closure {u > 0}` with
  `M ≥ |B_1|` and `N_0(u; 50) ≤ N₊`, none of which is assumed at `0`. We centre Lemma 4.6 at
  `a₀` with radius `20r`, which only needs the pinching of `a₀`.
-/

open MeasureTheory Metric Set Filter Module InnerProductSpace
open scoped NNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational.Dichotomy

variable {n : ℕ}

/-! ### Linear algebra -/

/-- The unit normal of an orthonormal family of `n − 1` vectors in `ℝⁿ`: the tangential part of
`g` has squared norm `Σ_j ⟪e_j, g⟫²`. -/
theorem exists_unit_forall_norm_sub_inner_smul_sq {k : ℕ} (hk : k + 1 = n) {e : Fin k → Rn n}
    (he : Orthonormal ℝ e) :
    ∃ ν : Rn n, ‖ν‖ = 1 ∧ ∀ g : Rn n, ‖g - ⟪g, ν⟫ • ν‖ ^ 2 = ∑ j, ⟪e j, g⟫ ^ 2 := by
  subst hk
  set v : Fin (k + 1) → Rn (k + 1) := Fin.snoc e 0 with hv
  have hvs : Orthonormal ℝ ((range Fin.castSucc).domRestrict v) := by
    rw [orthonormal_iff_ite] at he ⊢
    rintro ⟨_, i, rfl⟩ ⟨_, j, rfl⟩
    simp only [Set.domRestrict_apply, hv, Fin.snoc_castSucc, he i j]
    simp [Subtype.ext_iff, Fin.castSucc_inj]
  have hcard : finrank ℝ (Rn (k + 1)) = Fintype.card (Fin (k + 1)) := by
    rw [finrank_euclideanSpace_fin, Fintype.card_fin]
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq hcard hvs
  have hbe : ∀ j, b (Fin.castSucc j) = e j := fun j => by
    rw [hb _ ⟨j, rfl⟩, hv, Fin.snoc_castSucc]
  have hν : ‖b (Fin.last k)‖ = 1 := b.orthonormal.1 _
  refine ⟨b (Fin.last k), hν, fun g => ?_⟩
  have hp := b.sum_sq_norm_inner_right g
  rw [Fin.sum_univ_castSucc] at hp
  simp only [hbe, Real.norm_eq_abs, sq_abs] at hp
  rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, hν, Real.norm_eq_abs, mul_one, sq_abs,
    real_inner_comm (b (Fin.last k)) g]
  linear_combination -hp

/-- If each `e_j` is a combination `Σ_i c_i w_i` with `|c_i| ≤ B`, then
`Σ_j ⟪e_j, g⟫² ≤ k² B² Σ_i ⟪w_i, g⟫²`. -/
theorem sum_sq_inner_le_of_eq_sum_smul {k : ℕ} {e w : Fin k → Rn n} {B : ℝ}
    (hc : ∀ j, ∃ c : Fin k → ℝ, (∀ i, |c i| ≤ B) ∧ e j = ∑ i, c i • w i) (g : Rn n) :
    ∑ j, ⟪e j, g⟫ ^ 2 ≤ k ^ 2 * B ^ 2 * ∑ i, ⟪w i, g⟫ ^ 2 := by
  have hW : 0 ≤ ∑ i, ⟪w i, g⟫ ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hj : ∀ j, ⟪e j, g⟫ ^ 2 ≤ k * B ^ 2 * ∑ i, ⟪w i, g⟫ ^ 2 := by
    intro j
    obtain ⟨c, hcB, hce⟩ := hc j
    rw [hce, sum_inner]
    simp only [real_inner_smul_left]
    have hc2 : ∑ i, c i ^ 2 ≤ k * B ^ 2 := by
      have hci : ∀ i, c i ^ 2 ≤ B ^ 2 := fun i => by
        rw [← sq_abs (c i)]
        exact pow_le_pow_left₀ (abs_nonneg _) (hcB i) 2
      calc ∑ i, c i ^ 2 ≤ ∑ _i : Fin k, B ^ 2 := Finset.sum_le_sum fun i _ => hci i
        _ = k * B ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    calc (∑ i, c i * ⟪w i, g⟫) ^ 2 ≤ (∑ i, c i ^ 2) * ∑ i, ⟪w i, g⟫ ^ 2 :=
          Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ ≤ (k * B ^ 2) * ∑ i, ⟪w i, g⟫ ^ 2 := mul_le_mul_of_nonneg_right hc2 hW
  calc ∑ j, ⟪e j, g⟫ ^ 2 ≤ ∑ _j : Fin k, k * B ^ 2 * ∑ i, ⟪w i, g⟫ ^ 2 :=
        Finset.sum_le_sum fun j _ => hj j
    _ = k ^ 2 * B ^ 2 * ∑ i, ⟪w i, g⟫ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-! ### Integrability -/

/-- The homogeneity defect `(∇u·(z − y) − l u)²` of a function Lipschitz on a ball is integrable
on measurable subsets of the ball. -/
theorem integrableOn_sq_inner_gradient_sub_mul_of_lipschitzOnWith {u : Rn n → ℝ} {C : ℝ≥0}
    {c : Rn n} {R : ℝ} (hu : LipschitzOnWith C u (ball c R)) {S : Set (Rn n)}
    (hS : MeasurableSet S) (hSU : S ⊆ ball c R) (y : Rn n) (l : ℝ) :
    IntegrableOn (fun z => (⟪gradient u z, z - y⟫ - l * u z) ^ 2) S := by
  obtain ⟨g, hg, hug⟩ := hu.extend_real
  have hint := LipschitzWith.integrableOn_sq_inner_gradient_sub_mul hg hS
    (isBounded_ball.subset hSU) (p := fun z => z - y) (by fun_prop) l
  refine hint.congr_fun (fun z hz => ?_) hS
  have hzU := hSU hz
  have h : u =ᶠ[nhds z] g := Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hzU) hug
  have hgrad : gradient u z = gradient g z := by simp only [gradient, h.fderiv_eq]
  simp only [hgrad, hug hzU]

/-! ### Pinched points -/

/-- A point `y ∈ B̄_r(x)` is *pinched* at level `l` with tolerance `ε` if `y ∈ closure {u > 0}`,
`M_y(u; t) ≥ |B_1|` for some `t ∈ (0, r]`, `N_y(u; 20r) ≤ l` and `N_y(u; r) > l − ε`. In the
proof of Theorem 6.3 these are the points of `E`, with `l = N̄`. -/
structure IsPinched (u χ : Rn n → ℝ) (x : Rn n) (r l ε : ℝ) (y : Rn n) : Prop where
  mem_closedBall : y ∈ closedBall x r
  mem_closure : y ∈ closure {z | 0 < u z}
  exists_monotonicityM : ∃ t, 0 < t ∧ t ≤ r ∧ unitBallVolume n ≤ monotonicityM u χ y t
  frequencyN_le : frequencyN u χ y (20 * r) ≤ l
  lt_frequencyN : l - ε < frequencyN u χ y r

namespace IsPinched

variable {Ω : Set (Rn n)} {C : ℝ≥0} {u χ : Rn n → ℝ} {x y : Rn n} {r l ε : ℝ}

theorem closedBall_subset (hΩ : ball x (50 * r) ⊆ Ω)
    (hy : IsPinched u χ x r l ε y) {s : ℝ} (hs : s < 49 * r) : closedBall y s ⊆ Ω := by
  refine (closedBall_subset_ball' ?_).trans hΩ
  have := Metric.mem_closedBall.1 hy.mem_closedBall
  linarith

variable [NeZero n]

/-- At a pinched point, `M_y(u; s) ≥ |B_1|`, `N_y(u; s) ≥ 1` and `N_y` is nondecreasing on
`[r, 20 r]`, and `N_y(u; s) ∈ (l − ε, l]` there. -/
theorem frequencyN_mem (h : IsVariationalSolution Ω C u χ) (hr : 0 < r)
    (hΩ : ball x (50 * r) ⊆ Ω) (hy : IsPinched u χ x r l ε y) :
    (∀ s ∈ Icc r (20 * r), unitBallVolume n ≤ monotonicityM u χ y s) ∧
      MonotoneOn (frequencyN u χ y) (Icc r (20 * r)) ∧
      ∀ s ∈ Icc r (20 * r), l - ε < frequencyN u χ y s ∧ frequencyN u χ y s ≤ l := by
  obtain ⟨t, ht, htr, hM⟩ := hy.exists_monotonicityM
  have hΩ20 := hy.closedBall_subset hΩ (s := 20 * r) (by linarith)
  have hmono := h.monotoneOn_frequencyN hy.mem_closure ht hM hΩ20
  have hone : ∀ s ∈ Icc t (20 * r), 1 ≤ frequencyN u χ y s := fun _ hs =>
    h.one_le_frequencyN hy.mem_closure ht hM hΩ20 hs
  have hsub : Icc r (20 * r) ⊆ Icc t (20 * r) := Icc_subset_Icc_left htr
  refine ⟨fun s hs => ?_, hmono.mono hsub, fun s hs => ⟨?_, ?_⟩⟩
  · have hs0 : 0 < s := hr.trans_le hs.1
    have hH := h.heightH_pos hy.mem_closure hs0 (hy.closedBall_subset hΩ (by linarith [hs.2]))
    have h1 := hone s (hsub hs)
    rw [frequencyN, le_div_iff₀ hH, one_mul] at h1
    rw [monotonicityM]
    linarith
  · exact hy.lt_frequencyN.trans_le
      (hmono (hsub (left_mem_Icc.2 (by linarith))) (hsub hs) hs.1)
  · exact (hmono (hsub hs) (hsub (right_mem_Icc.2 (by linarith))) hs.2).trans hy.frequencyN_le

/-- **Integrated (4.13) at a pinched point** (proof of Theorem 6.3), with the fixed degree `l`:
`∫_{B_{20r}(y) ∖ B_r(y)} (∇u·(z − y) − l u)² ≤ (20r)^{n+2} H_y(u; 20r) (ε + 2ε²)`. -/
theorem setIntegral_homogeneity_le (h : IsVariationalSolution Ω C u χ) (hr : 0 < r)
    (hΩ : ball x (50 * r) ⊆ Ω) (hy : IsPinched u χ x r l ε y) :
    ∫ z in ball y (20 * r) \ ball y r, (⟪gradient u z, z - y⟫ - l * u z) ^ 2 ≤
      (20 * r) ^ (n + 2) * heightH u y (20 * r) * (ε + 2 * ε ^ 2) := by
  obtain ⟨t, ht, htr, hM⟩ := hy.exists_monotonicityM
  obtain ⟨-, -, hN⟩ := hy.frequencyN_mem h hr hΩ
  have hΩ20 := hy.closedBall_subset hΩ (s := 20 * r) (by linarith)
  have hbound := h.integral_annulus_sq_inner_gradient_sub_le hy.mem_closure ht htr
    (by linarith) hM hΩ20 l
  have hH := h.heightH_pos hy.mem_closure (by linarith) hΩ20
  have hP : 0 ≤ (20 * r) ^ (n + 2) * heightH u y (20 * r) :=
    mul_nonneg (pow_nonneg (by linarith) _) hH.le
  obtain ⟨h1l, h1u⟩ := hN r (left_mem_Icc.2 (by linarith))
  obtain ⟨h2l, h2u⟩ := hN (20 * r) (right_mem_Icc.2 (by linarith))
  have hε : 0 ≤ ε := by linarith
  have hsq : ∀ s, l - ε < s → s ≤ l → (s - l) ^ 2 ≤ ε ^ 2 := fun s h1 h2 =>
    sq_le_sq' (by linarith) (by linarith)
  have hmax : max ((frequencyN u χ y (20 * r) - l) ^ 2) ((frequencyN u χ y r - l) ^ 2) ≤ ε ^ 2 :=
    max_le (hsq _ h2l h2u) (hsq _ h1l h1u)
  refine hbound.trans (mul_le_mul_of_nonneg_left ?_ hP)
  linarith

end IsPinched

/-! ### Uniform comparability of `H` -/

/-- **Uniform comparability of `H`** (proof of Theorem 6.3, with Lemma 4.6 centred at `a₀`
instead of `0`; see the module docstring). There is
`K = K(n, N₊)` such that for pinched points `a₀, a` at a level `l ≤ N₊` with `|a − a₀| ≤ 2r`,
`H_a(u; 20r) ≤ K H_{a₀}(u; 10r)`. Also `H_{a₀}(u; 20r) ≤ K H_{a₀}(u; 10r)`. -/
theorem exists_heightH_comparison (n : ℕ) [NeZero n] (Np : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (Ω : Set (Rn n)) (C : ℝ≥0) (u χ : Rn n → ℝ) (x a₀ a : Rn n) (r l ε : ℝ),
      IsVariationalSolution Ω C u χ → 0 < r → ball x (50 * r) ⊆ Ω → l ≤ Np →
      IsPinched u χ x r l ε a₀ → IsPinched u χ x r l ε a →
      heightH u a₀ (20 * r) ≤ K * heightH u a₀ (10 * r) ∧
        heightH u a (20 * r) ≤ K * heightH u a₀ (10 * r) := by
  set Np' := max Np 2 with hNp'
  have hNp1 : 1 < Np' := lt_of_lt_of_le one_lt_two (le_max_right _ _)
  set K₆ := heightHChangeConst n with hK₆def
  have hK₆ : 0 < K₆ := heightHChangeConst_pos n
  set D := Abstract.RadialData.doublingConst Np' with hD
  have hDpos : 0 < D := Abstract.RadialData.doublingConst_pos _
  refine ⟨D + D * (K₆ * D), by have := mul_pos hDpos (mul_pos hK₆ hDpos); linarith, ?_⟩
  intro Ω C u χ x a₀ a r l ε h hr hΩ hl ha₀ ha
  obtain ⟨hM₀, -, hN₀⟩ := ha₀.frequencyN_mem h hr hΩ
  obtain ⟨hM, -, hN⟩ := ha.frequencyN_mem h hr hΩ
  have hΩ₀ := ha₀.closedBall_subset hΩ (s := 20 * r) (by linarith)
  have hΩa := ha.closedBall_subset hΩ (s := 20 * r) (by linarith)
  have hNle : ∀ {y}, (∀ s ∈ Icc r (20 * r), l - ε < frequencyN u χ y s ∧ frequencyN u χ y s ≤ l) →
      frequencyN u χ y (20 * r) ≤ Np' := fun hN' =>
    ((hN' (20 * r) (right_mem_Icc.2 (by linarith))).2.trans hl).trans (le_max_left _ _)
  have e2 : 20 * r / 2 = 10 * r := by ring
  have e4 : 20 * r / 4 = 5 * r := by ring
  -- doubling at `a₀`: `H_{a₀}(20r) ≤ D H_{a₀}(10r)`
  have hd₀ : heightH u a₀ (20 * r) ≤ D * heightH u a₀ (10 * r) := by
    exact (h.heightH_doubling ha₀.mem_closure (t := 10 * r) (by linarith) (by linarith)
      (by linarith) (hM₀ _ ⟨by linarith, by linarith⟩) hΩ₀ hNp1 (hNle hN₀)
      ⟨le_rfl, by linarith⟩).2
  -- doubling at `a`: `H_a(20r) ≤ D H_a(25r/2)`
  have hda : heightH u a (20 * r) ≤ D * heightH u a (5 / 8 * (20 * r)) :=
    (h.heightH_doubling ha.mem_closure (t := 10 * r) (by linarith) (by linarith)
      (by linarith) (hM _ ⟨by linarith, by linarith⟩) hΩa hNp1 (hNle hN)
      ⟨by linarith, by linarith⟩).2
  -- change of point from `a₀` to `a`: `H_a(25r/2) ≤ K₆ H_{a₀}(20r)`
  have hdist : a ∈ ball a₀ (20 * r / 4) := by
    rw [e4, mem_ball]
    have h1 := mem_closedBall.1 ha.mem_closedBall
    have h2 := mem_closedBall.1 ha₀.mem_closedBall
    have := dist_triangle_right a a₀ x
    linarith
  have hca := h.heightH_change_of_point_le (by linarith : (0 : ℝ) < 20 * r) hΩ₀ hdist
  have hH₀ : 0 ≤ heightH u a₀ (10 * r) :=
    (h.heightH_pos ha₀.mem_closure (by linarith) (ha₀.closedBall_subset hΩ (by linarith))).le
  have hDKD := mul_nonneg hDpos.le (mul_nonneg hK₆.le (mul_nonneg hDpos.le hH₀))
  refine ⟨hd₀.trans (by nlinarith [hDKD]), ?_⟩
  calc heightH u a (20 * r) ≤ D * heightH u a (5 / 8 * (20 * r)) := hda
    _ ≤ D * (K₆ * heightH u a₀ (20 * r)) := mul_le_mul_of_nonneg_left hca hDpos.le
    _ ≤ D * (K₆ * (D * heightH u a₀ (10 * r))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hd₀ hK₆.le) hDpos.le
    _ ≤ (D + D * (K₆ * D)) * heightH u a₀ (10 * r) := by nlinarith [mul_nonneg hDpos.le hH₀]

/-! ### The one-step estimate -/

/-- The constant of the one-step estimate,
`4 (n−1)³ (1 + 2/δ)^{2n} 20^{n+2} Q / (δ² 10ⁿ)`, where `Q` is the comparability constant. -/
def tangentialConst (n : ℕ) (δ Q : ℝ) : ℝ :=
  4 * ((n - 1 : ℕ) : ℝ) ^ 3 * (1 + 2 / δ) ^ (2 * n) * 20 ^ (n + 2) * Q / (δ ^ 2 * 10 ^ n)

theorem tangentialConst_nonneg (n : ℕ) {δ Q : ℝ} (hδ : 0 < δ) (hQ : 0 ≤ Q) :
    0 ≤ tangentialConst n δ Q := by
  unfold tangentialConst
  have h1 : 0 ≤ 1 + 2 / δ := by have := div_pos two_pos hδ; linarith
  exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (pow_nonneg h1 _))
    (by positivity)) hQ) (by positivity)

/-- **The one-step estimate** (proof of Theorem 6.3, at scale `10r` instead of the paper's `18`;
see the module docstring). There is
`K = K(n, N₊, δ)` with the following property. Let `a₀` and `a_1, …, a_{n−1}` be pinched at a
level `l ≤ N₊` with tolerance `ε`, and let the Gram–Schmidt vectors `e_i` of the `a_i − a₀` be
orthonormal combinations of the `a_j − a₀` with coefficients at most `(δr)⁻¹ (1 + 2/δ)^i` (as
produced by `exists_generalPosition_orthonormal`). Then for the unit normal `ν` of the `e_i`,
`∫_{B_{10r}(a₀) ∖ B_{5r}(a₀)} |∇u − ⟪∇u, ν⟫ν|² ≤ K (ε + 2ε²) (10r)ⁿ H_{a₀}(u; 10r)`. -/
theorem exists_tangential_bound (n : ℕ) [NeZero n] (Np : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (Ω : Set (Rn n)) (C : ℝ≥0) (u χ : Rn n → ℝ) (x a₀ : Rn n)
      (a : Fin (n - 1) → Rn n) (r l ε : ℝ),
      IsVariationalSolution Ω C u χ → 0 < r → ball x (50 * r) ⊆ Ω → l ≤ Np →
      IsPinched u χ x r l ε a₀ → (∀ i, IsPinched u χ x r l ε (a i)) →
      Orthonormal ℝ (gramSchmidtNormed ℝ fun j => a j - a₀) →
      (∀ i : Fin (n - 1), ∃ c : Fin (n - 1) → ℝ,
        (∀ j, |c j| ≤ (δ * r)⁻¹ * (1 + 2 / δ) ^ (i : ℕ)) ∧
        gramSchmidtNormed ℝ (fun j => a j - a₀) i = ∑ j, c j • (a j - a₀)) →
      ∃ ν : Rn n, ‖ν‖ = 1 ∧
        ∫ z in ball a₀ (10 * r) \ ball a₀ (10 * r / 2),
            ‖gradient u z - ⟪gradient u z, ν⟫ • ν‖ ^ 2 ≤
          K * (ε + 2 * ε ^ 2) * ((10 * r) ^ n * heightH u a₀ (10 * r)) := by
  obtain ⟨Q, hQ, hcomp⟩ := exists_heightH_comparison n Np
  refine ⟨tangentialConst n δ Q, tangentialConst_nonneg n hδ hQ.le, ?_⟩
  intro Ω C u χ x a₀ a r l ε h hr hΩ hl ha₀ ha he hc
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
  have hdist : ∀ {y : Rn n}, IsPinched u χ x r l ε y → dist a₀ y ≤ 2 * r := fun {y} hy => by
    have h1 := mem_closedBall.1 hy.mem_closedBall
    have h2 := mem_closedBall.1 ha₀.mem_closedBall
    have := dist_triangle_right a₀ y x
    linarith
  have hAann : ∀ {y : Rn n}, IsPinched u χ x r l ε y → A ⊆ ball y (20 * r) \ ball y r := by
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
  have hannU : ∀ {y : Rn n}, IsPinched u χ x r l ε y →
      ball y (20 * r) \ ball y r ⊆ ball x (50 * r) := by
    intro y hy z hz
    have h1 := mem_closedBall.1 hy.mem_closedBall
    have hz1 : dist z y < 20 * r := hz.1
    have := dist_triangle z y x
    exact mem_ball.2 (by linarith)
  have hint : ∀ {y : Rn n}, IsPinched u χ x r l ε y → IntegrableOn (F y) A := fun {y} hy =>
    integrableOn_sq_inner_gradient_sub_mul_of_lipschitzOnWith hlip hAm
      ((hAann hy).trans (hannU hy)) _ l
  have hintA : ∀ {y : Rn n}, IsPinched u χ x r l ε y →
      ∫ z in A, F y z ≤ (20 * r) ^ (n + 2) * heightH u y (20 * r) * (ε + 2 * ε ^ 2) := by
    intro y hy
    refine le_trans ?_ (hy.setIntegral_homogeneity_le h hr hΩ)
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
  set P := (20 * r) ^ (n + 2) * (ε + 2 * ε ^ 2) with hP
  have hε : 0 ≤ ε := by
    have h1 := ha₀.frequencyN_le
    obtain ⟨-, hmono, -⟩ := ha₀.frequencyN_mem h hr hΩ
    have := hmono (left_mem_Icc.2 (by linarith)) (right_mem_Icc.2 (by linarith))
      (by linarith : r ≤ 20 * r)
    linarith [ha₀.lt_frequencyN]
  have hPnn : 0 ≤ P := mul_nonneg (pow_nonneg (by linarith) _) (add_nonneg hε (by positivity))
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
      m * (4 * P * Q * H') := by
    calc ∑ i, (2 * (∫ z in A, F a₀ z) + 2 * ∫ z in A, F (a i) z) ≤
        ∑ _i : Fin (n - 1), (4 * P * Q * H') := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h0 := hintA ha₀
          have hi := hintA (ha i)
          obtain ⟨hc₀, hci⟩ := hcomp Ω C u χ x a₀ (a i) r l ε h hr hΩ hl ha₀ (ha i)
          have e1 : (20 * r) ^ (n + 2) * heightH u a₀ (20 * r) * (ε + 2 * ε ^ 2) =
              P * heightH u a₀ (20 * r) := by rw [hP]; ring
          have e2 : (20 * r) ^ (n + 2) * heightH u (a i) (20 * r) * (ε + 2 * ε ^ 2) =
              P * heightH u (a i) (20 * r) := by rw [hP]; ring
          rw [e1] at h0
          rw [e2] at hi
          have h0' := h0.trans (mul_le_mul_of_nonneg_left hc₀ hPnn)
          have hi' := hi.trans (mul_le_mul_of_nonneg_left hci hPnn)
          have e3 : 2 * (P * (Q * heightH u a₀ (10 * r))) + 2 * (P * (Q * heightH u a₀ (10 * r))) =
              4 * P * Q * H' := by rw [hH']; ring
          exact le_trans (add_le_add (mul_le_mul_of_nonneg_left h0' zero_le_two)
            (mul_le_mul_of_nonneg_left hi' zero_le_two)) (le_of_eq e3)
      _ = m * (4 * P * Q * H') := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hB2 : 0 ≤ m ^ 2 * B ^ 2 := by positivity
  calc ∫ z in A, ‖gradient u z - ⟪gradient u z, ν⟫ • ν‖ ^ 2 ≤ ∫ z in A, G z := hle
    _ = m ^ 2 * B ^ 2 * ∑ i, (2 * (∫ z in A, F a₀ z) + 2 * ∫ z in A, F (a i) z) := hGval
    _ ≤ m ^ 2 * B ^ 2 * (m * (4 * P * Q * H')) :=
        mul_le_mul_of_nonneg_left hsum hB2
    _ = tangentialConst n δ Q * (ε + 2 * ε ^ 2) * ((10 * r) ^ n * H') := by
      rw [hB, hP, hm, tangentialConst, pow_mul']
      generalize (1 + 2 / δ) ^ n = X
      have hr0 : r ≠ 0 := hr.ne'
      have hδ0 : δ ≠ 0 := hδ.ne'
      field_simp
      ring

end InnerVariational.Dichotomy
