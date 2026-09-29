/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.NaberValtorta.MainQ
public import InnerVariational.NaberValtorta.MainFrequency
public import InnerVariational.Singular.Tangent
public import InnerVariational.Frequency.ConcreteQ.Rescale
import InnerVariational.NaberValtorta.CoveringLimit
import InnerVariational.NaberValtorta.Reifenberg
import InnerVariational.Monotonicity.DensityQ

/-!
# Theorem 7.2 (3) and the local structure of `Σ^H_Q` with a Lipschitz coefficient

For a variational solution `(u, χ)` with a Lipschitz coefficient `Q` (`QBounds Ω Q L c C'`,
`κ = weissKappa L c C'`) on an open set `Ω`, Theorem 7.2 of D. Kriventsov and G. S. Weiss,
*Rectifiability, finite Hausdorff measure, and compactness for non-minimizing Bernoulli free
boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3, DOI 10.1002/cpa.22226; arXiv:2306.10131
(numbering of arXiv v2), gives:

* `hausdorffN_not_tendsto_modFrequencyN_eq_zero`: `Ñ_x(u; r) → 1` as `r → 0+` for
  `ℋ^{n-1}`-a.e. `x ∈ Σ^H_Q`, where `Ñ = N + κ² r²/2` is the modified frequency;
* `hausdorffN_not_tendsto_weightedFrequencyN_eq_zero`: the same for the frequency
  `N = weightedFrequencyN` itself (`Ñ − N = κ² r²/2 → 0`);
* `sigmaHQ_inter_ball_structure`: for `x₀ ∈ Σ^H_Q`, `B̄_ρ(x₀) ⊆ Ω` and `κ ρ ≤ 1/2`, the set
  `Σ^H_Q ∩ B_{ρ/100}(x₀)` has finite `ℋ^{n-1}` measure and is countably `ℋ^{n-1}`-rectifiable.

None of these assumes a smallness of `κ`: they are local, and the rescaling `u_{x₀,ρ}` has the
coefficient `Q(x₀ + ρ ·)` with `κ̃ = ρ κ` (`weissKappa_toNNReal_mul`), which is `≤ 1/2` for small
`ρ`.

## Proof

As for `Q ≡ 1` (`NaberValtorta/MainFrequency.lean`, `Singular/Tangent.lean`): the local form on
`B_{1/100}` with `0 ∈ Σ^H_Q(B_1)` and `κ ≤ 1/2` from the fourth conclusion of
`hausdorffN_le_and_rectifiable_and_frequency` with the data of `NaberValtorta/InstanceQ.lean`
(respectively from `sigmaHQ_main`); the rescaled local form via the scaling of `Ñ`, of `M^q(0+)`
and of `ℋ^{n-1}`; and a countable cover (Lindelöf).
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational.NaberValtorta

variable {n : ℕ}

/-! ### Rescaling at a general point -/

section Rescale

/-- `s ↦ ρ s` maps `𝓝[>] 0` to itself for `ρ > 0`. -/
theorem tendsto_const_mul_nhdsGT_zero' {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun s : ℝ => ρ * s) (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have h := ((continuous_const_mul ρ).tendsto (0 : ℝ)).mono_left
      (nhdsWithin_le_nhds (s := Ioi 0))
    simpa using h
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact mul_pos hρ hs

theorem rescale_coeff_eq (Q : Rn n → ℝ) (a y : Rn n) (ρ : ℝ) :
    (fun z => (fun w => Q (a + ρ • w)) (y + (1 : ℝ) • z)) = fun z => Q (a + ρ • y + ρ • z) := by
  funext z
  simp only [one_smul, smul_add, add_assoc]

/-- `Ñ_y(u_{a,ρ}; s)` with the coefficient `Q(a + ρ ·)` and `κ̃ = ρ κ` is `Ñ_{a+ρy}(u; ρ s)` with
`κ`. -/
theorem modFrequencyN_oneHomRescale_apply [NeZero n] (Q u χ : Rn n → ℝ) (a y : Rn n) {ρ : ℝ}
    (hρ : 0 < ρ) (κ s : ℝ) :
    modFrequencyN (ρ * κ) (fun z => Q (a + ρ • z)) (oneHomRescale u a ρ) (chiRescale χ a ρ) y s =
      modFrequencyN κ Q u χ (a + ρ • y) (ρ * s) := by
  have h1 := modFrequencyN_oneHomRescale (fun z => Q (a + ρ • z)) (oneHomRescale u a ρ)
    (chiRescale χ a ρ) y one_pos (ρ * κ) s
  rw [one_mul, one_mul, oneHomRescale_oneHomRescale_one, chiRescale_chiRescale_one,
    rescale_coeff_eq] at h1
  rw [← h1, modFrequencyN_oneHomRescale Q u χ (a + ρ • y) hρ κ s]

/-- `M^q_y(u_{a,ρ}; s) = M^q_{a+ρy}(u; ρ s)`. -/
theorem monotonicityMq_oneHomRescale_apply [NeZero n] (q : ℝ) (u χ : Rn n → ℝ) (a y : Rn n)
    {ρ : ℝ} (hρ : 0 < ρ) (s : ℝ) :
    monotonicityMq q (oneHomRescale u a ρ) (chiRescale χ a ρ) y s =
      monotonicityMq q u χ (a + ρ • y) (ρ * s) := by
  have h1 := monotonicityMq_rescale (oneHomRescale u a ρ) (chiRescale χ a ρ) y q one_pos s
  rw [one_mul, oneHomRescale_oneHomRescale_one, chiRescale_chiRescale_one] at h1
  rw [← h1, monotonicityMq_rescale u χ (a + ρ • y) q hρ s]

variable {Ω : Set (Rn n)} {C : ℝ≥0} {Q u χ : Rn n → ℝ} {L : ℝ≥0} {c C' : ℝ}

/-- `M^q_y(u_{a,ρ}; 0+) = M^q_{a+ρy}(u; 0+)` at the frozen value `q = Q(a + ρ y)`. -/
theorem MzeroQ_oneHomRescale_apply [NeZero n] (hQ : QBounds Ω Q L c C')
    (h : IsVariationalSolutionQ Ω C Q u χ) (a y : Rn n) {ρ : ℝ} (hρ : 0 < ρ)
    (hy : a + ρ • y ∈ Ω) :
    MzeroQ (Q (a + ρ • y)) (oneHomRescale u a ρ) (chiRescale χ a ρ) y =
      MzeroQ (Q (a + ρ • y)) u χ (a + ρ • y) := by
  have hT := (h.tendsto_MzeroQ hQ hy).comp (tendsto_const_mul_nhdsGT_zero' hρ)
  refine Tendsto.limUnder_eq (hT.congr fun s => ?_)
  simp only [Function.comp_apply, monotonicityMq_oneHomRescale_apply _ u χ a y hρ s]

/-- If `a + ρ y ∈ Σ^H_Q(Ω)` and `|y| < 1`, then `y ∈ Σ^H_Q(B_1)` for the rescaling
`(Q(a + ρ ·), u_{a,ρ}, χ_{a,ρ})`. -/
theorem mem_sigmaHQ_oneHomRescale [NeZero n] (hQ : QBounds Ω Q L c C')
    (h : IsVariationalSolutionQ Ω C Q u χ) (a y : Rn n) {ρ : ℝ} (hρ : 0 < ρ)
    (hy : a + ρ • y ∈ sigmaHQ Ω Q u χ) (hy1 : ‖y‖ < 1) :
    y ∈ sigmaHQ (ball 0 1) (fun z => Q (a + ρ • z)) (oneHomRescale u a ρ) (chiRescale χ a ρ) :=
  ⟨mem_ball_zero_iff.2 hy1, (mem_closure_oneHomRescale_iff u a y hρ).2 hy.2.1, by
    change ((Q (a + ρ • y) ^ 2 * unitBallVolume n : ℝ) : EReal) ≤
      MzeroQ (Q (a + ρ • y)) (oneHomRescale u a ρ) (chiRescale χ a ρ) y
    rw [MzeroQ_oneHomRescale_apply hQ h a y hρ hy.1]
    exact hy.2.2⟩

/-- A radius `ρ > 0` with `B̄_ρ(x) ⊆ Ω` and `κ ρ ≤ 1/2`, for `x ∈ Ω` open and `κ ≥ 0`. -/
theorem exists_radius_of_mem {x : Rn n} (hΩ : IsOpen Ω) (hx : x ∈ Ω) {κ : ℝ} (hk : 0 ≤ κ) :
    ∃ ρ, 0 < ρ ∧ closedBall x ρ ⊆ Ω ∧ κ * ρ ≤ 1 / 2 := by
  obtain ⟨ε, hε, hεΩ⟩ := Metric.isOpen_iff.1 hΩ x hx
  refine ⟨min (ε / 2) (1 / (2 * (κ + 1))), lt_min (half_pos hε) (by positivity),
    (closedBall_subset_ball ((min_le_left _ _).trans_lt (half_lt_self hε))).trans hεΩ, ?_⟩
  calc κ * min (ε / 2) (1 / (2 * (κ + 1))) ≤ κ * (1 / (2 * (κ + 1))) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) hk
    _ ≤ 1 / 2 := by
        rw [mul_one_div, div_le_iff₀ (by positivity)]
        linarith

end Rescale

/-! ### Theorem 7.2 (3) -/

section Frequency

variable {Ω : Set (Rn n)} {C_V : ℝ≥0} {Q u χ : Rn n → ℝ} {L : ℝ≥0} {c C' : ℝ}

/-- **Theorem 7.2 (3) with a Lipschitz coefficient, local form**. For a variational solution on
an open `Ω ⊇ B̄_1` with `κ ≤ 1/2` and `0 ∈ Σ^H_Q(B_1)`, `Ñ_x(u; r) → 1` as `r → 0+` for
`ℋ^{n-1}`-a.e. `x ∈ Σ^H_Q(B_1) ∩ B_{1/100}`. -/
theorem hausdorffN_not_tendsto_modFrequencyN_ball_eq_zero (hn : 2 ≤ n)
    (hQ : QBounds Ω Q L c C') (h : IsVariationalSolutionQ Ω C_V Q u χ)
    (hΩ : closedBall 0 1 ⊆ Ω) (hκ : weissKappa L c C' ≤ 1 / 2)
    (h0 : (0 : Rn n) ∈ sigmaHQ (ball 0 1) Q u χ) :
    hausdorffN n (n - 1) {x | x ∈ sigmaHQ (ball 0 1) Q u χ ∩ ball 0 (1 / 100) ∧
      ¬ Tendsto (modFrequencyN (weissKappa L c C') Q u χ x) (𝓝[>] 0) (𝓝 1)} = 0 := by
  haveI : NeZero n := ⟨by omega⟩
  set κ := weissKappa L c C' with hκdef
  have hk : 0 ≤ κ := weissKappa_nonneg_of_closedBall hQ hΩ
  have hB1 : ball (0 : Rn n) 1 ⊆ Ω := ball_subset_closedBall.trans hΩ
  -- constants, with `N₊ := Ñ_0(u; 1)`
  obtain ⟨Np, hNp⟩ := modFrequencyN_change_of_point n (modFrequencyN κ Q u χ 0 1)
  obtain ⟨CJ, hCJ⟩ := jonesBetaSqQ_le n Np
  set ε := dichotomyEpsQ n hn Np with hε_def
  have hεpos : ∀ δ, 0 < δ → 0 < ε δ := fun δ hδ => (dichotomyEpsQ_spec n hn Np hδ).1.1
  obtain ⟨C₂, -, H₂⟩ := hausdorffN_le_and_rectifiable_and_frequency hn CJ Np ε hεpos
  -- the cover
  set r₀ : ℝ := 1 / 240 with hr₀_def
  have hr₀ : 0 < r₀ := by norm_num [hr₀_def]
  obtain ⟨F', hF'sub, hF'fin, hcover⟩ :=
    finite_cover_balls_of_compact (isCompact_closedBall (0 : Rn n) (1 / 100)) hr₀
  set F := hF'fin.toFinset with hF_def
  have hcK : ∀ p ∈ F, closedBall p (5 * r₀) ⊆ closedBall (0 : Rn n) (1 / 10) := by
    intro p hp
    have := mem_closedBall.1 (hF'sub (hF'fin.mem_toFinset.1 hp))
    refine closedBall_subset_closedBall' ?_
    rw [hr₀_def]
    linarith
  have hBK : ball (0 : Rn n) (1 / 100) ⊆ closedBall 0 (1 / 10) :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by norm_num))
  -- the specialised upstream facts
  have hCJu := fun x r μ => hCJ Ω C_V Q u χ L c C' x r μ hQ h
  have hεu : ∀ δ, 0 < δ → ∀ (x : Rn n) (r t : ℝ), 0 < r → κ * (50 * r) ≤ 1 / 2 →
      ball x (50 * r) ⊆ Ω → t ∈ Ioc 0 r →
      let Nmax := sSup ((fun y => modFrequencyN κ Q u χ y (20 * r)) ''
        (closedBall x r ∩ sigmaHQr Ω Q u χ κ t))
      Nmax ≤ Np → Nmax < 1 + δ ∨ ∃ P : AffineSubspace ℝ (Rn n),
        Module.finrank ℝ P.direction ≤ n - 2 ∧
        {y ∈ closedBall x r ∩ sigmaHQr Ω Q u χ κ t |
          Nmax - modFrequencyN κ Q u χ y r < ε δ} ⊆ thickening (δ * r) (P : Set (Rn n)) :=
    fun δ hδ x r t => (dichotomyEpsQ_spec n hn Np hδ).2 Ω C_V Q u χ L c C' x r t hQ h
  have h0Ω : (0 : Rn n) ∈ sigmaHQ Ω Q u χ := ⟨hB1 h0.1, h0.2.1, h0.2.2⟩
  have h4Ω : closedBall (0 : Rn n) (1 / 4) ⊆ Ω :=
    (closedBall_subset_closedBall (by norm_num)).trans hΩ
  have hZ4 : 0 ≤ modMonotonicityM κ Q u χ 0 (1 / 4) :=
    h.modMonotonicityM_nonneg_of_mem_sigmaHQ hQ h0Ω (by norm_num) (by nlinarith) h4Ω
  have hN : ∀ z ∈ closedBall (0 : Rn n) (1 / 10), ∀ ρ, 0 < ρ → ρ < 1 / 2 →
      modFrequencyN κ Q u χ z ρ ≤ Np := by
    intro z hz ρ hρ hρ2
    refine hNp Ω C_V Q u χ L c C' 0 1 hQ h one_pos hΩ h0.2.1 hZ4 (by linarith) le_rfl z ?_ ρ hρ
      (by linarith)
    have := mem_closedBall.1 hz
    rw [mem_ball]
    linarith
  have hmemr : ∀ z ∈ sigmaHQ (ball 0 1) Q u χ ∩ closedBall 0 (1 / 10), ∀ ρ, 0 < ρ → ρ ≤ 1 / 6 →
      z ∈ sigmaHQr Ω Q u χ κ ρ := fun z hz ρ hρ hρ6 =>
    h.mem_sigmaHQr_of_mem_sigmaHQ hQ ⟨hB1 hz.1.1, hz.1.2.1, hz.1.2.2⟩ hρ (by nlinarith)
      (closedBall_subset_of_mem_K hΩ hz.2 (by linarith))
  let J := solJonesDataQ hQ h hΩ hκ hCJu (sigmaHQ (ball 0 1) Q u χ ∩ closedBall 0 (1 / 10)) 0
    le_rfl (measurableSet_sigmaHQ_inter hQ h hΩ) inter_subset_right
    (fun z hz ρ hρ _ hρ6 => hmemr z hz ρ hρ hρ6) (fun z hz => hN z hz.2)
  have hD : ∀ p ∈ F, ∀ s, 0 < s → ∃ D : NVData n CJ Np ε, D.t ≤ s ∧
      J.S ∩ closedBall p (5 * r₀) ⊆ D.S ∧
      (∀ z ∈ J.S ∩ closedBall p (5 * r₀), D.N z = J.N z) ∧
      2 * r₀ ≤ D.R ∧ closedBall p (5 * r₀) ⊆ D.K := by
    intro p hp s hs
    have hτ : 0 < min s r₀ := lt_min hs hr₀
    have hτR : min s r₀ ≤ 1 / 120 := (min_le_right _ _).trans (by rw [hr₀_def]; norm_num)
    refine ⟨solNVDataQ hQ h hΩ hκ hCJu ε hεu (min s r₀) hτ hτR hN, min_le_left _ _, ?_,
      fun z _ => rfl, by change 2 * r₀ ≤ 1 / 120; rw [hr₀_def]; norm_num, hcK p hp⟩
    rintro z ⟨hz, -⟩
    exact ⟨hmemr z hz _ hτ (by linarith), hz.2⟩
  have H := fun p (hp : p ∈ F) => H₂ J p r₀ rfl hr₀
    (by change 2 * r₀ ≤ 1 / 120; rw [hr₀_def]; norm_num) (hD p hp)
  refine measure_mono_null ?_
    ((measure_biUnion_null_iff F.countable_toSet).2 fun p hp => (H p hp).2.2.2)
  rintro x ⟨⟨hxH, hxB⟩, hxN⟩
  obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.1 (hcover (ball_subset_closedBall hxB))
  refine mem_iUnion₂.2 ⟨p, hF'fin.mem_toFinset.2 hp, ⟨⟨hxH, hBK hxB⟩, hxp⟩, fun hT => hxN ?_⟩
  refine hT.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with r hr
  exact solNQ_eq h hΩ κ (hBK hxB) hr.1.le (by linarith [hr.2])

/-- **Theorem 7.2 (3) with a Lipschitz coefficient, rescaled local form.** Let `x₀ ∈ Σ^H_Q(Ω)`,
`B̄_{ρ₀}(x₀) ⊆ Ω` and `κ ρ₀ ≤ 1/2`. Then `Ñ_x(u; r) → 1` as `r → 0+` for `ℋ^{n-1}`-a.e.
`x ∈ Σ^H_Q(Ω) ∩ B_{ρ₀/100}(x₀)`. -/
theorem hausdorffN_not_tendsto_modFrequencyN_inter_ball_eq_zero (hn : 2 ≤ n)
    (hQ : QBounds Ω Q L c C') (h : IsVariationalSolutionQ Ω C_V Q u χ) {x₀ : Rn n}
    (hx₀ : x₀ ∈ sigmaHQ Ω Q u χ) {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) (hB : closedBall x₀ ρ₀ ⊆ Ω)
    (hκ : weissKappa L c C' * ρ₀ ≤ 1 / 2) :
    hausdorffN n (n - 1) {x | (x ∈ sigmaHQ Ω Q u χ ∧
      ¬ Tendsto (modFrequencyN (weissKappa L c C') Q u χ x) (𝓝[>] 0) (𝓝 1)) ∧
      x ∈ ball x₀ (ρ₀ / 100)} = 0 := by
  haveI : NeZero n := ⟨by omega⟩
  have hsol := h.rescale x₀ hρ₀
  have hQ' := hQ.rescale x₀ hρ₀
  have hκ' : weissKappa (Real.toNNReal ρ₀ * L) c C' ≤ 1 / 2 := by
    rw [weissKappa_toNNReal_mul hρ₀.le, mul_comm]
    exact hκ
  have hΩ' : closedBall (0 : Rn n) 1 ⊆ (fun y => x₀ + ρ₀ • y) ⁻¹' Ω := by
    intro y hy
    refine hB ?_
    rw [mem_closedBall, dist_zero_right] at hy
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hρ₀.le]
    calc ρ₀ * ‖y‖ ≤ ρ₀ * 1 := mul_le_mul_of_nonneg_left hy hρ₀.le
      _ = ρ₀ := mul_one ρ₀
  have h0 := mem_sigmaHQ_oneHomRescale hQ h x₀ 0 hρ₀ (by simpa using hx₀) (by simp)
  have hloc := hausdorffN_not_tendsto_modFrequencyN_ball_eq_zero hn hQ' hsol hΩ' hκ' h0
  rw [hausdorffN_eq_mul_preimage_affine (p := x₀) hρ₀ (n - 1)]
  refine mul_eq_zero_of_right _ (measure_mono_null ?_ hloc)
  rintro y ⟨⟨hyH, hyN⟩, hyB⟩
  have hy : ‖y‖ < 1 / 100 := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hρ₀.le]
      at hyB
    have h1 : ρ₀ * ‖y‖ < ρ₀ * (1 / 100) := by linarith
    exact lt_of_mul_lt_mul_left h1 hρ₀.le
  refine ⟨⟨mem_sigmaHQ_oneHomRescale hQ h x₀ y hρ₀ hyH (by linarith), mem_ball_zero_iff.2 hy⟩,
    fun hT => hyN ?_⟩
  rw [weissKappa_toNNReal_mul hρ₀.le] at hT
  refine (hT.comp (tendsto_div_const_nhdsGT_zero hρ₀)).congr fun s => ?_
  rw [Function.comp_apply, modFrequencyN_oneHomRescale_apply Q u χ x₀ y hρ₀]
  congr 1
  field_simp

/-- **Theorem 7.2 (3) with a Lipschitz coefficient**, for a variational solution on any open
`Ω`: the modified frequency satisfies `Ñ_x(u; r) → 1` as `r → 0+` for `ℋ^{n-1}`-a.e.
`x ∈ Σ^H_Q(Ω)`. -/
theorem hausdorffN_not_tendsto_modFrequencyN_eq_zero (hn : 2 ≤ n) (hQ : QBounds Ω Q L c C')
    (h : IsVariationalSolutionQ Ω C_V Q u χ) :
    hausdorffN n (n - 1) {x | x ∈ sigmaHQ Ω Q u χ ∧
      ¬ Tendsto (modFrequencyN (weissKappa L c C') Q u χ x) (𝓝[>] 0) (𝓝 1)} = 0 := by
  have hρ : ∀ x ∈ Ω, ∃ ρ, 0 < ρ ∧ closedBall x ρ ⊆ Ω ∧ weissKappa L c C' * ρ ≤ 1 / 2 :=
    fun x hx => exists_radius_of_mem h.isOpen hx (hQ.weissKappa_nonneg hx)
  choose! ρ hρpos hρsub hρκ using hρ
  set E := {x | x ∈ sigmaHQ Ω Q u χ ∧
    ¬ Tendsto (modFrequencyN (weissKappa L c C') Q u χ x) (𝓝[>] 0) (𝓝 1)} with hE
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun i : sigmaHQ Ω Q u χ => ball (i : Rn n) (ρ i / 100)) fun _ => isOpen_ball
  have hcov : E ⊆ ⋃ i ∈ T, E ∩ ball (i : Rn n) (ρ i / 100) := by
    intro x hx
    have hx' : x ∈ ⋃ i : sigmaHQ Ω Q u χ, ball (i : Rn n) (ρ i / 100) := by
      have := hρpos x hx.1.1
      exact mem_iUnion.2 ⟨⟨x, hx.1⟩, mem_ball_self (by positivity)⟩
    rw [← hTU] at hx'
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 hx'
    exact mem_iUnion₂.2 ⟨i, hi, hx, hxi⟩
  refine measure_mono_null hcov ((measure_biUnion_null_iff hTc).2 fun i _ => ?_)
  exact hausdorffN_not_tendsto_modFrequencyN_inter_ball_eq_zero hn hQ h i.2 (hρpos i i.2.1)
    (hρsub i i.2.1) (hρκ i i.2.1)

/-- `N_x(s) → 1` as `s → 0+` if `Ñ_x(s) = N_x(s) + κ² s²/2 → 1`. -/
theorem tendsto_weightedFrequencyN_of_tendsto_modFrequencyN {κ : ℝ} {x : Rn n}
    (hT : Tendsto (modFrequencyN κ Q u χ x) (𝓝[>] 0) (𝓝 1)) :
    Tendsto (weightedFrequencyN Q u χ x) (𝓝[>] 0) (𝓝 1) := by
  have hq : Tendsto (fun s : ℝ => κ ^ 2 * s ^ 2 / 2) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun s : ℝ => κ ^ 2 * s ^ 2 / 2) (𝓝 0) (𝓝 (κ ^ 2 * 0 ^ 2 / 2)) :=
      ((continuous_const.mul (continuous_pow 2)).div_const 2).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  have := hT.sub hq
  rw [sub_zero] at this
  refine this.congr fun s => ?_
  simp [modFrequencyN]

/-- **Theorem 7.2 (3) with a Lipschitz coefficient**, for the frequency
`N = weightedFrequencyN`: `N_x(u; r) → 1` as `r → 0+` for `ℋ^{n-1}`-a.e. `x ∈ Σ^H_Q(Ω)`. -/
theorem hausdorffN_not_tendsto_weightedFrequencyN_eq_zero (hn : 2 ≤ n)
    (hQ : QBounds Ω Q L c C') (h : IsVariationalSolutionQ Ω C_V Q u χ) :
    hausdorffN n (n - 1) {x | x ∈ sigmaHQ Ω Q u χ ∧
      ¬ Tendsto (weightedFrequencyN Q u χ x) (𝓝[>] 0) (𝓝 1)} = 0 := by
  refine measure_mono_null ?_ (hausdorffN_not_tendsto_modFrequencyN_eq_zero hn hQ h)
  rintro x ⟨hx1, hx2⟩
  exact ⟨hx1, fun hT => hx2 (tendsto_weightedFrequencyN_of_tendsto_modFrequencyN hT)⟩

/-- **Theorem 7.2 (3) with a Lipschitz coefficient, rescaled local form**, for the frequency
`N = weightedFrequencyN`. -/
theorem hausdorffN_not_tendsto_weightedFrequencyN_inter_ball_eq_zero (hn : 2 ≤ n)
    (hQ : QBounds Ω Q L c C') (h : IsVariationalSolutionQ Ω C_V Q u χ) {x₀ : Rn n}
    (hx₀ : x₀ ∈ sigmaHQ Ω Q u χ) {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) (hB : closedBall x₀ ρ₀ ⊆ Ω)
    (hκ : weissKappa L c C' * ρ₀ ≤ 1 / 2) :
    hausdorffN n (n - 1) {x | (x ∈ sigmaHQ Ω Q u χ ∧
      ¬ Tendsto (weightedFrequencyN Q u χ x) (𝓝[>] 0) (𝓝 1)) ∧
      x ∈ ball x₀ (ρ₀ / 100)} = 0 := by
  refine measure_mono_null ?_
    (hausdorffN_not_tendsto_modFrequencyN_inter_ball_eq_zero hn hQ h hx₀ hρ₀ hB hκ)
  rintro x ⟨⟨hx1, hx2⟩, hx3⟩
  exact ⟨⟨hx1, fun hT => hx2 (tendsto_weightedFrequencyN_of_tendsto_modFrequencyN hT)⟩, hx3⟩

end Frequency

/-! ### Local structure of `Σ^H_Q` -/

/-- **Theorem 7.2 (1)–(2) with a Lipschitz coefficient, localized.** For `x₀ ∈ Σ^H_Q(Ω)`,
`B̄_ρ(x₀) ⊆ Ω` and `κ ρ ≤ 1/2`, the set `Σ^H_Q ∩ B_{ρ/100}(x₀)` has finite `ℋ^{n-1}` measure and
is countably `ℋ^{n-1}`-rectifiable. Proof: `sigmaHQ_main` for the rescaling `u_{x₀,ρ}`. -/
theorem sigmaHQ_inter_ball_structure (hn : 2 ≤ n) {Ω : Set (Rn n)} {C_V : ℝ≥0}
    {Q u χ : Rn n → ℝ} {L : ℝ≥0} {c C' : ℝ} (hQ : QBounds Ω Q L c C')
    (h : IsVariationalSolutionQ Ω C_V Q u χ) {x₀ : Rn n} (hx₀ : x₀ ∈ sigmaHQ Ω Q u χ) {ρ : ℝ}
    (hρ : 0 < ρ) (hB : closedBall x₀ ρ ⊆ Ω) (hκ : weissKappa L c C' * ρ ≤ 1 / 2) :
    hausdorffN n (n - 1) (sigmaHQ Ω Q u χ ∩ ball x₀ (ρ / 100)) < ∞ ∧
      IsCountablyRectifiable n (n - 1) (sigmaHQ Ω Q u χ ∩ ball x₀ (ρ / 100)) := by
  haveI : NeZero n := ⟨by omega⟩
  have hsol := h.rescale x₀ hρ
  have hQ' := hQ.rescale x₀ hρ
  set v := oneHomRescale u x₀ ρ
  set η := chiRescale χ x₀ ρ
  set Qt : Rn n → ℝ := fun z => Q (x₀ + ρ • z)
  have hκ' : weissKappa (Real.toNNReal ρ * L) c C' ≤ 1 / 2 := by
    rw [weissKappa_toNNReal_mul hρ.le, mul_comm]
    exact hκ
  have hΩ' : closedBall (0 : Rn n) 1 ⊆ (fun y => x₀ + ρ • y) ⁻¹' Ω := by
    intro y hy
    refine hB ?_
    rw [mem_closedBall, dist_zero_right] at hy
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hρ.le]
    calc ρ * ‖y‖ ≤ ρ * 1 := mul_le_mul_of_nonneg_left hy hρ.le
      _ = ρ := mul_one ρ
  have h0 : (0 : Rn n) ∈ sigmaHQ (ball 0 1) Qt v η :=
    mem_sigmaHQ_oneHomRescale hQ h x₀ 0 hρ (by simpa using hx₀) (by simp)
  obtain ⟨Cm, hCm⟩ := sigmaHQ_main hn
    (modFrequencyN (weissKappa (Real.toNNReal ρ * L) c C') Qt v η 0 1)
  obtain ⟨-, H⟩ := hCm _ C_V Qt v η _ c C' hQ' hsol hΩ' hκ' le_rfl
  obtain ⟨-, hfin, hrect⟩ := H h0
  -- the preimage of our set lies in `Σ^H_Q(v) ∩ B_{1/100}`
  have hpre : (fun y : Rn n => x₀ + ρ • y) ⁻¹' (sigmaHQ Ω Q u χ ∩ ball x₀ (ρ / 100)) ⊆
      sigmaHQ (ball 0 1) Qt v η ∩ ball 0 (1 / 100) := by
    rintro y ⟨hyH, hyB⟩
    have hy : ‖y‖ < 1 / 100 := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hρ.le]
        at hyB
      have h1 : ρ * ‖y‖ < ρ * (1 / 100) := by linarith
      exact lt_of_mul_lt_mul_left h1 hρ.le
    exact ⟨mem_sigmaHQ_oneHomRescale hQ h x₀ y hρ hyH (by linarith), mem_ball_zero_iff.2 hy⟩
  constructor
  · rw [hausdorffN_eq_mul_preimage_affine (p := x₀) hρ (n - 1)]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      ((measure_mono hpre).trans_lt (hfin.trans_lt ENNReal.ofReal_lt_top))
  · have himg : sigmaHQ Ω Q u χ ∩ ball x₀ (ρ / 100) ⊆
        (fun z => x₀ + ρ • z) '' (sigmaHQ (ball 0 1) Qt v η ∩ ball 0 (1 / 100)) := by
      intro y hy
      refine ⟨ρ⁻¹ • (y - x₀), hpre ?_, ?_⟩
      · rw [mem_preimage]
        rwa [smul_smul, mul_inv_cancel₀ hρ.ne', one_smul, add_sub_cancel]
      · change x₀ + ρ • (ρ⁻¹ • (y - x₀)) = y
        rw [smul_smul, mul_inv_cancel₀ hρ.ne', one_smul, add_sub_cancel]
    exact (Singular.IsCountablyRectifiable.image_affine hrect x₀ hρ).mono himg

end InnerVariational.NaberValtorta
