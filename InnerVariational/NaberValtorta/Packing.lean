/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.NaberValtorta.Discrete
public import InnerVariational.Basic.Polar
public import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import GMTFoundations.Defs.Setup

/-!
# Packing and covering by balls in `ℝⁿ`

Elementary volume-counting facts used by the Naber–Valtorta argument (Lemma 7.1 and Theorem 7.2)
of D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
DOI 10.1002/cpa.22226; arXiv:2306.10131 (numbering of arXiv v2).

* `card_mul_volume_ball_le`: disjoint balls of radius `a` inside `U` number at most
  `|U| / (ω_n aⁿ)`.
* `card_le_of_pairwise_le_dist`: an `a`-separated finite subset of `B̄_ρ(z)` has at most
  `(2ρ/a + 1)ⁿ` points.
* `exists_net`: every bounded set `A` has a finite maximal `a`-separated subset `F ⊆ A`. The balls
  `B_a(y)`, `y ∈ F`, then cover `A`. `net A a` is a choice of such a set.
* `exists_cover_ball`: `B_ρ(z)` is covered by at most `(2ρ/a + 1)ⁿ` balls of radius `a`.
* `card_mul_le_of_subset_thickening` (tube packing): an `a`-separated subset of `B̄_ρ(x)` within
  distance `b` of an affine subspace of dimension `≤ n − 2` has at most
  `(2b + a)² (2ρ + a)^{n−2} / (ω_n (a/2)ⁿ)` points. This is the count `C_S δ₂^{2−n}` of small-drop
  balls in the proof of Theorem 7.2. The proof compares volumes in an orthonormal
  basis whose first two vectors are orthogonal to the subspace.
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational.NaberValtorta

variable {n : ℕ}

/-! ### Volume of balls -/

theorem nontrivial_rn (hn : 0 < n) : Nontrivial (Rn n) :=
  Module.nontrivial_of_finrank_pos (R := ℝ) (by simpa using hn)

theorem volume_ball_zero_one_lt_top : volume (ball (0 : Rn n) 1) < ∞ :=
  measure_ball_lt_top

theorem volume_ball_eq (x : Rn n) {r : ℝ} (hr : 0 < r) :
    volume (ball x r) = ENNReal.ofReal (unitBallVolume n * r ^ n) := by
  rw [Measure.addHaar_ball_of_pos volume x hr, finrank_euclideanSpace_fin, unitBallVolume,
    ENNReal.ofReal_mul' (by positivity), ENNReal.ofReal_toReal volume_ball_zero_one_lt_top.ne,
    mul_comm]

theorem volume_closedBall_eq (x : Rn n) {r : ℝ} (hr : 0 ≤ r) :
    volume (closedBall x r) = ENNReal.ofReal (unitBallVolume n * r ^ n) := by
  rw [Measure.addHaar_closedBall volume x hr, finrank_euclideanSpace_fin, unitBallVolume,
    ENNReal.ofReal_mul' (by positivity), ENNReal.ofReal_toReal volume_ball_zero_one_lt_top.ne,
    mul_comm]

/-! ### Packing -/

/-- Pairwise disjoint balls of radius `a > 0` contained in `U`: `#F · ω_n aⁿ ≤ |U|`. -/
theorem card_mul_volume_ball_le {F : Finset (Rn n)} {a : ℝ} (ha : 0 < a)
    {U : Set (Rn n)} (hdisj : (F : Set (Rn n)).PairwiseDisjoint fun y => ball y a)
    (hU : ∀ y ∈ F, ball y a ⊆ U) :
    ENNReal.ofReal (F.card * (unitBallVolume n * a ^ n)) ≤ volume U := by
  have hω := (unitBallVolume_pos n).le
  calc ENNReal.ofReal (F.card * (unitBallVolume n * a ^ n))
      = ∑ y ∈ F, volume (ball y a) := by
        rw [Finset.sum_congr rfl fun y _ => volume_ball_eq y ha, Finset.sum_const,
          nsmul_eq_mul, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
    _ = volume (⋃ y ∈ F, ball y a) :=
        (measure_biUnion_finset hdisj fun _ _ => measurableSet_ball).symm
    _ ≤ volume U := measure_mono (iUnion₂_subset hU)

/-- Pairwise `2a`-separated points have pairwise disjoint balls of radius `a`. -/
theorem pairwiseDisjoint_ball_of_pairwise {F : Set (Rn n)} {a : ℝ}
    (hF : F.Pairwise fun x y => 2 * a ≤ dist x y) : F.PairwiseDisjoint fun y => ball y a :=
  fun x hx y hy hxy => ball_disjoint_ball (by linarith [hF hx hy hxy])

/-- An `a`-separated finite subset of `B̄_ρ(z)` has at most `(2ρ/a + 1)ⁿ` points. -/
theorem card_le_of_pairwise_le_dist {F : Finset (Rn n)} {z : Rn n} {ρ a : ℝ}
    (ha : 0 < a) (hρ : 0 ≤ ρ) (hFz : ↑F ⊆ closedBall z ρ)
    (hF : (F : Set (Rn n)).Pairwise fun x y => a ≤ dist x y) :
    (F.card : ℝ) ≤ (2 * ρ / a + 1) ^ n := by
  have hω := unitBallVolume_pos n
  have hdisj : (F : Set (Rn n)).PairwiseDisjoint fun y => ball y (a / 2) :=
    pairwiseDisjoint_ball_of_pairwise fun x hx y hy hxy => by linarith [hF hx hy hxy]
  have hU : ∀ y ∈ F, ball y (a / 2) ⊆ ball z (ρ + a / 2) := fun y hy =>
    ball_subset_ball' (by linarith [mem_closedBall.1 (hFz hy)])
  have h := (card_mul_volume_ball_le (by positivity) hdisj hU).trans_eq
    (volume_ball_eq z (by positivity))
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
  have ha2 : 0 < (a / 2) ^ n := by positivity
  have key : (F.card : ℝ) * (a / 2) ^ n ≤ (ρ + a / 2) ^ n := by
    refine le_of_mul_le_mul_left ?_ hω
    calc unitBallVolume n * ((F.card : ℝ) * (a / 2) ^ n)
        = F.card * (unitBallVolume n * (a / 2) ^ n) := by ring
      _ ≤ unitBallVolume n * (ρ + a / 2) ^ n := h
  have hq : (2 * ρ / a + 1) ^ n = (ρ + a / 2) ^ n / (a / 2) ^ n := by
    rw [← div_pow]
    congr 1
    field_simp
  rw [hq, le_div_iff₀ ha2]
  exact key

/-- Two points of an `a`-separated set cannot lie in one ball of radius `a / 2`. -/
theorem card_le_one_of_pairwise_le_dist {F : Finset (Rn n)} {p : Rn n} {σ a : ℝ}
    (hσ : 2 * σ ≤ a) (hFp : ↑F ⊆ ball p σ)
    (hF : (F : Set (Rn n)).Pairwise fun x y => a ≤ dist x y) : F.card ≤ 1 := by
  rw [Finset.card_le_one]
  intro x hx y hy
  by_contra hxy
  have h1 := mem_ball.1 (hFp hx)
  have h2 := mem_ball.1 (hFp hy)
  have := hF hx hy hxy
  linarith [dist_triangle_right x y p]

/-! ### Nets -/

open scoped Classical in
/-- A bounded set has a finite maximal `a`-separated subset. The balls of radius `a` around
its points cover the set. -/
theorem exists_net {A : Set (Rn n)} {z : Rn n} {ρ : ℝ} (hA : A ⊆ closedBall z ρ)
    {a : ℝ} (ha : 0 < a) :
    ∃ F : Finset (Rn n), ↑F ⊆ A ∧ (F : Set (Rn n)).Pairwise (fun x y => a ≤ dist x y) ∧
      A ⊆ ⋃ y ∈ F, ball y a := by
  rcases A.eq_empty_or_nonempty with rfl | ⟨w, hw⟩
  · exact ⟨∅, by simp, by simp, empty_subset _⟩
  have hρ : 0 ≤ ρ := by
    have := mem_closedBall.1 (hA hw)
    linarith [dist_nonneg (x := w) (y := z)]
  let Q : ℕ → Prop := fun m => ∃ F : Finset (Rn n), ↑F ⊆ A ∧
    (F : Set (Rn n)).Pairwise (fun x y => a ≤ dist x y) ∧ F.card = m
  let M : ℕ := ⌊(2 * ρ / a + 1) ^ n⌋₊
  have hQM : ∀ m, Q m → m ≤ M := by
    rintro m ⟨F, hFA, hF, rfl⟩
    exact Nat.le_floor (card_le_of_pairwise_le_dist ha hρ (hFA.trans hA) hF)
  have hQ0 : Q 0 := ⟨∅, by simp, by simp, rfl⟩
  obtain ⟨F, hFA, hF, hcard⟩ := Nat.findGreatest_spec (P := Q) (Nat.zero_le M) hQ0
  refine ⟨F, hFA, hF, fun x hx => ?_⟩
  by_contra hxF
  simp only [mem_iUnion, mem_ball, not_exists, not_lt] at hxF
  have hxnot : x ∉ F := fun hxF' => by
    have := hxF x hxF'
    rw [dist_self] at this
    linarith
  have hQ' : Q (Nat.findGreatest Q M + 1) := by
    refine ⟨insert x F, ?_, ?_, ?_⟩
    · rw [Finset.coe_insert]
      exact insert_subset hx hFA
    · rw [Finset.coe_insert]
      refine hF.insert fun y hy _ => ⟨hxF y hy, ?_⟩
      rw [dist_comm]
      exact hxF y hy
    · rw [Finset.card_insert_of_notMem hxnot, hcard]
  have := Nat.le_findGreatest (hQM _ hQ') hQ'
  omega

open scoped Classical in
/-- A choice of a finite maximal `a`-separated subset of `A` (see `exists_net`). It is `∅` when
none exists. -/
def net (A : Set (Rn n)) (a : ℝ) : Finset (Rn n) :=
  if h : ∃ F : Finset (Rn n), ↑F ⊆ A ∧ (F : Set (Rn n)).Pairwise (fun x y => a ≤ dist x y) ∧
      A ⊆ ⋃ y ∈ F, ball y a then h.choose else ∅

theorem net_spec {A : Set (Rn n)} {z : Rn n} {ρ : ℝ} (hA : A ⊆ closedBall z ρ)
    {a : ℝ} (ha : 0 < a) :
    ↑(net A a) ⊆ A ∧ (net A a : Set (Rn n)).Pairwise (fun x y => a ≤ dist x y) ∧
      A ⊆ ⋃ y ∈ net A a, ball y a := by
  have h := exists_net hA ha
  rw [net, dif_pos h]
  exact h.choose_spec

theorem net_subset (A : Set (Rn n)) (a : ℝ) : ↑(net A a) ⊆ A := by
  classical
  unfold net
  split_ifs with h
  · exact h.choose_spec.1
  · simp

theorem net_pairwise (A : Set (Rn n)) (a : ℝ) :
    (net A a : Set (Rn n)).Pairwise (fun x y => a ≤ dist x y) := by
  classical
  unfold net
  split_ifs with h
  · exact h.choose_spec.2.1
  · simp

theorem subset_net {A : Set (Rn n)} {z : Rn n} {ρ : ℝ} (hA : A ⊆ closedBall z ρ)
    {a : ℝ} (ha : 0 < a) : A ⊆ ⋃ y ∈ net A a, ball y a :=
  (net_spec hA ha).2.2

/-- A ball `B_ρ(z)` is covered by at most `(2ρ/a + 1)ⁿ` balls of radius `a` centred in it. -/
theorem exists_cover_ball (z : Rn n) {ρ a : ℝ} (hρ : 0 ≤ ρ) (ha : 0 < a) :
    ∃ F : Finset (Rn n), (F.card : ℝ) ≤ (2 * ρ / a + 1) ^ n ∧ ball z ρ ⊆ ⋃ y ∈ F, ball y a := by
  obtain ⟨hFA, hF, hcov⟩ := net_spec (ball_subset_closedBall (x := z) (ε := ρ)) ha
  exact ⟨_, card_le_of_pairwise_le_dist ha hρ (hFA.trans ball_subset_closedBall) hF, hcov⟩

/-! ### Tube packing -/

/-- If `dim W ≤ n − 2`, then `ℝⁿ` has an orthonormal basis whose first two vectors are
orthogonal to `W`. -/
theorem exists_orthonormalBasis_orthogonal (hn : 2 ≤ n) {W : Submodule ℝ (Rn n)}
    (hW : Module.finrank ℝ W ≤ n - 2) :
    ∃ b : OrthonormalBasis (Fin n) ℝ (Rn n), ∀ i : Fin n, (i : ℕ) < 2 → b i ∈ Wᗮ := by
  have hdim : 2 ≤ Module.finrank ℝ Wᗮ := by
    have := W.finrank_add_finrank_orthogonal
    rw [finrank_euclideanSpace_fin] at this
    omega
  set e := stdOrthonormalBasis ℝ Wᗮ
  let v : Fin n → Rn n := fun i => if h : (i : ℕ) < 2 then (e ⟨i, by omega⟩ : Rn n) else 0
  have hv : Orthonormal ℝ (({i : Fin n | (i : ℕ) < 2} : Set (Fin n)).restrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Set.mem_setOf_eq] at hi hj
    simp only [Set.restrict_apply, v, dif_pos hi, dif_pos hj, Subtype.mk.injEq]
    rw [← Submodule.coe_inner, orthonormal_iff_ite.1 e.orthonormal]
    simp only [Fin.mk.injEq, Fin.val_inj]
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq
    (by rw [finrank_euclideanSpace_fin, Fintype.card_fin])
  refine ⟨b, fun i hi => ?_⟩
  rw [hb i hi]
  simp only [v, dif_pos hi]
  exact (e _).2

/-- `∏_{i < n} (A if i < 2 else B) = A² B^{n-2}` for `n ≥ 2`. -/
theorem prod_fin_ite_lt_two (hn : 2 ≤ n) (A B : ℝ) :
    ∏ i : Fin n, (if (i : ℕ) < 2 then A else B) = A ^ 2 * B ^ (n - 2) := by
  rw [Fin.prod_univ_eq_prod_range (fun k => if k < 2 then A else B) n, Finset.prod_ite,
    Finset.prod_const, Finset.prod_const]
  have h1 : (Finset.range n).filter (· < 2) = Finset.range 2 := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  have h2 := Finset.card_filter_add_card_filter_not (s := Finset.range n) (· < 2)
  rw [h1, Finset.card_range, Finset.card_range] at h2
  rw [h1, Finset.card_range, show ((Finset.range n).filter fun k => ¬k < 2).card = n - 2 by omega]

/-- **Tube packing.** Let `L` be an affine subspace of `ℝⁿ` of dimension `≤ n − 2`, and let
`F ⊆ B̄_ρ(x)` be an `a`-separated finite set within distance `b` of `L`. Then
`#F · ω_n (a/2)ⁿ ≤ (2b + a)² (2ρ + a)^{n−2}`. So `#F ≤ C(n) (b/a + 1)² (ρ/a + 1)^{n-2}`: the count
has the exponent `n − 2` of the dimension of `L` rather than `n`. -/
theorem card_mul_le_of_subset_thickening (hn : 2 ≤ n) {L : AffineSubspace ℝ (Rn n)}
    (hL : Module.finrank ℝ L.direction ≤ n - 2) {F : Finset (Rn n)} {x : Rn n} {ρ a b : ℝ}
    (ha : 0 < a) (hρ : 0 ≤ ρ) (hb : 0 ≤ b) (hFx : ↑F ⊆ closedBall x ρ)
    (hFL : ↑F ⊆ thickening b (L : Set (Rn n)))
    (hF : (F : Set (Rn n)).Pairwise fun y z => a ≤ dist y z) :
    (F.card : ℝ) * (unitBallVolume n * (a / 2) ^ n) ≤
      (2 * b + a) ^ 2 * (2 * ρ + a) ^ (n - 2) := by
  rcases (L : Set (Rn n)).eq_empty_or_nonempty with hLe | ⟨l₀, hl₀⟩
  · have hF0 : F = ∅ := by
      rw [← Finset.coe_eq_empty]
      exact subset_empty_iff.1 (hFL.trans (by rw [hLe, thickening_empty]))
    subst hF0
    simp only [Finset.card_empty, Nat.cast_zero, zero_mul]
    positivity
  obtain ⟨e, he⟩ := exists_orthonormalBasis_orthogonal hn hL
  set w : Fin n → ℝ := fun i => if (i : ℕ) < 2 then 2 * b + a else 2 * ρ + a with hw
  set m : Fin n → ℝ := fun i => if (i : ℕ) < 2 then ⟪e i, l₀⟫ else ⟪e i, x⟫ with hm
  set f : Rn n → (Fin n → ℝ) := fun z => WithLp.ofLp (e.repr z) with hf_def
  have hf : MeasurePreserving f volume volume :=
    (PiLp.volume_preserving_ofLp (Fin n)).comp e.measurePreserving_repr
  set B : Set (Fin n → ℝ) := univ.pi fun i => Ioo (m i - w i / 2) (m i + w i / 2) with hB
  have hfi : ∀ z i, f z i = ⟪e i, z⟫ := fun z i => e.repr_apply_apply z i
  have hnorm : ∀ i (v : Rn n), |⟪e i, v⟫| ≤ ‖v‖ := fun i v => by
    have := abs_real_inner_le_norm (e i) v
    rwa [e.orthonormal.1 i, one_mul] at this
  have hsub : ∀ y ∈ F, ball y (a / 2) ⊆ f ⁻¹' B := by
    intro y hy z hz
    have hzy := mem_ball.1 hz
    rw [mem_preimage, hB, Set.mem_univ_pi]
    intro i
    suffices h : |⟪e i, z⟫ - m i| < w i / 2 by
      rw [hfi, mem_Ioo]
      constructor <;> linarith [(abs_lt.1 h).1, (abs_lt.1 h).2]
    by_cases hi : (i : ℕ) < 2
    · obtain ⟨l, hl, hyl⟩ := mem_thickening_iff.1 (hFL hy)
      have h0 : ⟪e i, l - l₀⟫ = 0 :=
        Submodule.inner_left_of_mem_orthogonal (L.vsub_mem_direction hl hl₀) (he i hi)
      have hsplit : ⟪e i, z⟫ - m i = ⟪e i, z - l⟫ := by
        simp only [hm, if_pos hi]
        rw [← inner_sub_right, show z - l₀ = (z - l) + (l - l₀) by abel, inner_add_right, h0,
          add_zero]
      rw [hsplit]
      refine (hnorm i _).trans_lt ?_
      rw [← dist_eq_norm]
      simp only [hw, if_pos hi]
      linarith [dist_triangle z y l]
    · have hsplit : ⟪e i, z⟫ - m i = ⟪e i, z - x⟫ := by
        simp only [hm, if_neg hi]
        rw [← inner_sub_right]
      rw [hsplit]
      refine (hnorm i _).trans_lt ?_
      rw [← dist_eq_norm]
      simp only [hw, if_neg hi]
      linarith [dist_triangle z y x, mem_closedBall.1 (hFx hy)]
  have hdisj : (F : Set (Rn n)).PairwiseDisjoint fun y => ball y (a / 2) :=
    pairwiseDisjoint_ball_of_pairwise fun y hy z hz hyz => by linarith [hF hy hz hyz]
  have hwpos : ∀ i, 0 ≤ w i := fun i => by
    simp only [hw]
    split_ifs <;> positivity
  have key := (card_mul_volume_ball_le (by positivity) hdisj hsub).trans_eq
    (hf.measure_preimage (MeasurableSet.univ_pi fun _ => measurableSet_Ioo).nullMeasurableSet)
  rw [hB, Real.volume_pi_Ioo,
    Finset.prod_congr rfl (fun i _ => by rw [show m i + w i / 2 - (m i - w i / 2) = w i by ring]),
    ← ENNReal.ofReal_prod_of_nonneg (fun i _ => hwpos i),
    ENNReal.ofReal_le_ofReal_iff (Finset.prod_nonneg fun i _ => hwpos i), hw,
    prod_fin_ite_lt_two hn] at key
  exact key

end InnerVariational.NaberValtorta
