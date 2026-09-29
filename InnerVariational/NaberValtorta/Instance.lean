/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.NaberValtorta.CoveringLimit
public import InnerVariational.NaberValtorta.Inputs
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Topology.EMetricSpace.Paracompact
public import InnerVariational.NaberValtorta.Data
import GMTFoundations.GMT.Polar

/-!
# The Naber–Valtorta data of a variational solution, and Theorem 7.2

This file instantiates the abstract data of `NaberValtorta/Data.lean` for a variational solution
`(u, χ)` on an open set `Ω ⊇ B̄_1`, and proves Theorem 7.2 (1)–(2) of D. Kriventsov and
G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for non-minimizing
Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3, DOI 10.1002/cpa.22226;
arXiv:2306.10131 (numbering of arXiv v2), in the exact form of `Statements.sigmaH_main`
(`sigmaH_main` below).

## The data

Fix `K = B̄_{1/10}` and the scale `R = 1/120`. For `z ∈ K` and `ρ ≤ R`, the ball `B̄_{50ρ}(z)` lies
in `B_1`, and `50 R < 1/2` is inside the range of Lemma 4.6 applied at `(0, 1)`.

* `N z r := frequencyN ũ χ̃ z r`, where `ũ = Ω.indicator u` and `χ̃ = Ω.indicator χ`. For
  `B̄_r(z) ⊆ Ω` this is `N_z(u; r)` (`frequencyN_indicator`), and `z ↦ N z r` is measurable for
  every `r` (`measurable_frequencyN`), by Tonelli-type measurability of parametric integrals.
  No continuity of `N` in the centre is needed.
* `solJonesData`: a `JonesData` on any measurable `S ⊆ K` with `S ⊆ Σ^H_ρ(Ω)` for `ρ ∈ [t, 1/6]`,
  `ρ > 0`, and `N_z(u; ρ) ≤ N'` for `ρ ∈ (0, 1/2)`. The monotonicity fields come from Lemma 4.1
  and the Jones field from Theorem 6.1.
* `solNVData`: for `t ∈ (0, R]`, the `NVData` with `S = Σ^H_t(Ω) ∩ K`. The dichotomy is
  Theorem 6.3, whose set `B̄_r(x) ∩ Σ^H_t` equals `S ∩ B̄_r(x)` when `B̄_r(x) ⊆ K`.
* For `t = 0`, the Jones data have `S = Σ^H(B_1) ∩ K`, and `solNVData` at `t = min(s, R)`
  provides the `NVData` for `s → 0` that Theorem 7.2 (2) uses.

The bound `N' = K(n, N₊)` comes from Lemma 4.6 at `(0, 1)`, which is where `N_0(u; 1) ≤ N₊` and
`B̄_1 ⊆ Ω` enter: the paper assumes the solution on `B_1`, while `N_0(u; 1)` involves `u` on
`∂B_1`. `Σ^H` and `Σ^H_t` of the statement are relative
to `B_1`, and they agree on `K` with the sets relative to `Ω` (`mem_sigmaHr_ball_iff`).

## Inputs

The proof uses the results restated in `NaberValtorta/Inputs.lean`: Proposition 3.4,
Lemmas 4.1 and 4.6, Theorem 6.1 and Theorem 6.3.
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational.NaberValtorta

variable {n : ℕ}

/-! ### Measurability in the centre -/

section Measurability

/-- `z ↦ ∫_{B_r(z)} g` is measurable for measurable `g`. -/
theorem measurable_setIntegral_ball {g : Rn n → ℝ} (hg : Measurable g) (r : ℝ) :
    Measurable fun z : Rn n => ∫ y in ball z r, g y := by
  have h : (fun z : Rn n => ∫ y in ball z r, g y) = fun z => ∫ y, (ball z r).indicator g y := by
    funext z
    rw [integral_indicator measurableSet_ball]
  rw [h]
  refine (StronglyMeasurable.integral_prod_right
    (f := fun z y => (ball z r).indicator g y) ?_).measurable
  refine Measurable.stronglyMeasurable ?_
  have hs : MeasurableSet {p : Rn n × Rn n | dist p.2 p.1 < r} :=
    measurableSet_lt (continuous_snd.dist continuous_fst).measurable measurable_const
  convert (hg.comp measurable_snd).indicator hs using 1

/-- `z ↦ ∫_{∂B_r(z)} f` is measurable for measurable `f`. -/
theorem measurable_sphereIntegral {f : Rn n → ℝ} (hf : Measurable f) (r : ℝ) :
    Measurable fun z : Rn n => sphereIntegral f z r := by
  unfold sphereIntegral
  refine Measurable.const_mul ?_ _
  refine (StronglyMeasurable.integral_prod_right
    (f := fun (z : Rn n) (ω : sphere (0 : Rn n) 1) => f (z + r • (ω : Rn n))) ?_).measurable
  exact (hf.comp (measurable_fst.add (measurable_snd.subtype_val.const_smul r))).stronglyMeasurable

theorem measurable_gradient (f : Rn n → ℝ) : Measurable (gradient f) :=
  (InnerProductSpace.toDual ℝ (Rn n)).symm.continuous.measurable.comp (measurable_fderiv ℝ f)

theorem measurable_energyD (u : Rn n → ℝ) {χ : Rn n → ℝ} (hχ : Measurable χ) (r : ℝ) :
    Measurable fun z => energyD u χ z r :=
  (measurable_setIntegral_ball (((measurable_gradient u).norm.pow_const 2).add hχ) r).const_mul _

theorem measurable_heightH {u : Rn n → ℝ} (hu : Measurable u) (r : ℝ) :
    Measurable fun z => heightH u z r :=
  (measurable_sphereIntegral (hu.pow_const 2) r).const_mul _

theorem measurable_monotonicityM {u χ : Rn n → ℝ} (hu : Measurable u) (hχ : Measurable χ)
    (r : ℝ) : Measurable fun z => monotonicityM u χ z r :=
  (measurable_energyD u hχ r).sub (measurable_heightH hu r)

theorem measurable_frequencyN {u χ : Rn n → ℝ} (hu : Measurable u) (hχ : Measurable χ)
    (r : ℝ) : Measurable fun z => frequencyN u χ z r :=
  ((measurable_energyD u hχ r).sub_const _).div (measurable_heightH hu r)

end Measurability

/-! ### Extension by zero outside `Ω` -/

section Indicator

variable {Ω : Set (Rn n)} {u χ : Rn n → ℝ} {z : Rn n} {r : ℝ}

theorem measurable_indicator_of_continuousOn (hΩ : IsOpen Ω) (hu : ContinuousOn u Ω) :
    Measurable (Ω.indicator u) := by
  classical
  rw [← piecewise_eq_indicator]
  exact hu.measurable_piecewise continuousOn_const hΩ.measurableSet

theorem energyD_indicator (hΩ : IsOpen Ω) (hz : ball z r ⊆ Ω) :
    energyD (Ω.indicator u) (Ω.indicator χ) z r = energyD u χ z r := by
  unfold energyD
  congr 1
  refine setIntegral_congr_fun measurableSet_ball fun y hy => ?_
  have hyΩ := hz hy
  have hev : Ω.indicator u =ᶠ[𝓝 y] u :=
    Filter.eventuallyEq_of_mem (hΩ.mem_nhds hyΩ) fun w hw => indicator_of_mem hw u
  simp only [hev.gradient_eq, indicator_of_mem hyΩ]

theorem heightH_indicator (hr : 0 ≤ r) (hz : closedBall z r ⊆ Ω) :
    heightH (Ω.indicator u) z r = heightH u z r := by
  unfold heightH sphereIntegral
  congr 2
  refine integral_congr_ae (.of_forall fun ω => ?_)
  have hmem : z + r • (ω : Rn n) ∈ Ω := by
    refine hz ?_
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hr, norm_eq_of_mem_sphere ω, mul_one]
  simp only [indicator_of_mem hmem]

theorem frequencyN_indicator (hΩ : IsOpen Ω) (hr : 0 ≤ r) (hz : closedBall z r ⊆ Ω) :
    frequencyN (Ω.indicator u) (Ω.indicator χ) z r = frequencyN u χ z r := by
  unfold frequencyN
  rw [energyD_indicator hΩ (ball_subset_closedBall.trans hz), heightH_indicator hr hz]

theorem monotonicityM_indicator (hΩ : IsOpen Ω) (hr : 0 ≤ r) (hz : closedBall z r ⊆ Ω) :
    monotonicityM (Ω.indicator u) (Ω.indicator χ) z r = monotonicityM u χ z r := by
  unfold monotonicityM
  rw [energyD_indicator hΩ (ball_subset_closedBall.trans hz), heightH_indicator hr hz]

end Indicator

/-! ### Geometry of `K = B̄_{1/10}` -/

section Geometry

variable {Ω : Set (Rn n)} {z : Rn n} {r : ℝ}

theorem closedBall_subset_ball_one (hz : z ∈ closedBall (0 : Rn n) (1 / 10)) (hr : r < 9 / 10) :
    closedBall z r ⊆ ball 0 1 := by
  refine closedBall_subset_ball' ?_
  rw [mem_closedBall] at hz
  linarith

theorem closedBall_subset_of_mem_K (hΩ : closedBall (0 : Rn n) 1 ⊆ Ω)
    (hz : z ∈ closedBall (0 : Rn n) (1 / 10)) (hr : r < 9 / 10) : closedBall z r ⊆ Ω :=
  (closedBall_subset_ball_one hz hr).trans (ball_subset_closedBall.trans hΩ)

theorem mem_ball_one_of_mem_K (hz : z ∈ closedBall (0 : Rn n) (1 / 10)) : z ∈ ball (0 : Rn n) 1 :=
  closedBall_subset_ball_one hz (r := 0) (by norm_num) (mem_closedBall_self le_rfl)

/-- On `K = B̄_{1/10}` and for `t < 9/10`, `Σ^H_t` relative to `B_1` is `Σ^H_t` relative to any
`Ω ⊇ B_1`. -/
theorem mem_sigmaHr_ball_iff {u χ : Rn n → ℝ} (hΩ : closedBall (0 : Rn n) 1 ⊆ Ω)
    (hz : z ∈ closedBall (0 : Rn n) (1 / 10)) {t : ℝ} (ht : t < 9 / 10) :
    z ∈ sigmaHr (ball 0 1) u χ t ↔ z ∈ sigmaHr Ω u χ t := by
  have hB : ball (0 : Rn n) 1 ⊆ Ω := ball_subset_closedBall.trans hΩ
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨hB h1, h2.trans hB, h3, h4⟩
  · rintro ⟨-, -, h3, h4⟩
    exact ⟨mem_ball_one_of_mem_K hz, closedBall_subset_ball_one hz ht, h3, h4⟩

end Geometry

/-! ### The data -/

section Data

variable [NeZero n] {Ω : Set (Rn n)} {C_V : ℝ≥0} {u χ : Rn n → ℝ}

/-- The frequency used in the data: `N_z(u; r)` computed for the extension by zero of `(u, χ)`
outside `Ω`. It is measurable in `z` and agrees with `N_z(u; r)` when `B̄_r(z) ⊆ Ω`. -/
abbrev solN (Ω : Set (Rn n)) (u χ : Rn n → ℝ) : Rn n → ℝ → ℝ :=
  frequencyN (Ω.indicator u) (Ω.indicator χ)

omit [NeZero n] in
theorem solN_eq (h : IsVariationalSolution Ω C_V u χ) (hΩ : closedBall (0 : Rn n) 1 ⊆ Ω)
    {z : Rn n} (hz : z ∈ closedBall (0 : Rn n) (1 / 10)) {r : ℝ} (hr : 0 ≤ r) (hr' : r < 9 / 10) :
    solN Ω u χ z r = frequencyN u χ z r :=
  frequencyN_indicator h.isOpen hr (closedBall_subset_of_mem_K hΩ hz hr')

/-- The Jones data of a variational solution on a set `S ⊆ B̄_{1/10}` (see the module docstring).
The hypotheses: `S ⊆ Σ^H_ρ(Ω)` for every `ρ ∈ [t, 1/6]`, `ρ > 0`; `N_z(u; ρ) ≤ N'` on `S` for
`ρ ∈ (0, 1/2)` (from Lemma 4.6); and Theorem 6.1 for `(u, χ)` with the bound `N'` and the
constant `CJ`. -/
def solJonesData (h : IsVariationalSolution Ω C_V u χ) (hΩ : closedBall (0 : Rn n) 1 ⊆ Ω)
    {CJ Np : ℝ}
    (hCJ : ∀ (x : Rn n) (r : ℝ) (μ : Measure (Rn n)), 0 < r →
      closedBall x (50 * r) ⊆ Ω → IsFiniteMeasure μ → μ (sigmaHr Ω u χ r)ᶜ = 0 →
      x ∈ sigmaHr Ω u χ r → frequencyN u χ x (50 * r) ≤ Np →
      jonesBetaSq μ x r ≤ ENNReal.ofReal (CJ / r ^ (n - 1)) *
        ∫⁻ y in ball x r, ENNReal.ofReal (frequencyN u χ y (20 * r) - frequencyN u χ y r) ∂μ)
    (S : Set (Rn n)) (t : ℝ) (ht : 0 ≤ t) (hSm : MeasurableSet S)
    (hSK : S ⊆ closedBall 0 (1 / 10))
    (hS : ∀ z ∈ S, ∀ ρ, 0 < ρ → t ≤ ρ → ρ ≤ 1 / 6 → z ∈ sigmaHr Ω u χ ρ)
    (hN : ∀ z ∈ S, ∀ ρ, 0 < ρ → ρ < 1 / 2 → frequencyN u χ z ρ ≤ Np) : JonesData n CJ where
  S := S
  N := solN Ω u χ
  t := t
  R := 1 / 120
  t_nonneg := ht
  R_pos := by norm_num
  measurableSet_S := hSm
  measurable_N r _ _ :=
    measurable_frequencyN (measurable_indicator_of_continuousOn h.isOpen h.continuousOn)
      h.measurable_chi r
  monotoneOn z hz a ha b hb hab := by
    have ha0 : 0 < a := lt_of_le_of_lt ht ha.1
    have hmem := hS z hz ((t + a) / 2) (by linarith [ha.1]) (by linarith [ha.1])
      (by linarith [ha.1, ha.2])
    have hmono := (Inputs.frequencyN_monotoneOn h hmem.2.2.1 (by linarith [ha.1]) hmem.2.2.2
      (closedBall_subset_of_mem_K hΩ (hSK hz) (r := 1 / 6) (by norm_num))).1
    rw [solN_eq h hΩ (hSK hz) ha0.le (by linarith [ha.2]),
      solN_eq h hΩ (hSK hz) (ha0.trans_le hab).le (by linarith [hb.2])]
    exact hmono ⟨by linarith [ha.1], by linarith [ha.2]⟩ ⟨by linarith [ha.1], by linarith [hb.2]⟩
      hab
  one_le z hz a ha := by
    have ha0 : 0 < a := lt_of_le_of_lt ht ha.1
    have hmem := hS z hz ((t + a) / 2) (by linarith [ha.1]) (by linarith [ha.1])
      (by linarith [ha.1, ha.2])
    have h1 := (Inputs.frequencyN_monotoneOn h hmem.2.2.1 (by linarith [ha.1]) hmem.2.2.2
      (closedBall_subset_of_mem_K hΩ (hSK hz) (r := 1 / 6) (by norm_num))).2
    rw [solN_eq h hΩ (hSK hz) ha0.le (by linarith [ha.2])]
    exact h1 a ⟨by linarith [ha.1], by linarith [ha.2]⟩
  jones μ hμ hμS y hy ρ hρ htρ hρR := by
    have hae : ∀ᵐ z ∂μ, z ∈ S := mem_ae_iff.2 hμS
    have hsub : S ⊆ sigmaHr Ω u χ ρ := fun z hz => hS z hz ρ hρ htρ (by linarith)
    have key := hCJ y ρ μ hρ (closedBall_subset_of_mem_K hΩ (hSK hy) (by linarith)) hμ
      (measure_mono_null (compl_subset_compl.2 hsub) hμS) (hsub hy)
      (hN y hy (50 * ρ) (by linarith) (by linarith))
    refine key.trans_eq ?_
    congr 1
    refine lintegral_congr_ae (ae_restrict_of_ae (hae.mono fun z hz => ?_))
    simp only [solN_eq h hΩ (hSK hz) (by linarith : (0 : ℝ) ≤ 20 * ρ) (by linarith),
      solN_eq h hΩ (hSK hz) hρ.le (by linarith)]

omit [NeZero n] in
/-- `Σ^H_t(Ω) ∩ B̄_{1/10}` is measurable for `0 ≤ t < 9/10`. -/
theorem measurableSet_sigmaHr_inter (h : IsVariationalSolution Ω C_V u χ)
    (hΩ : closedBall (0 : Rn n) 1 ⊆ Ω) {t : ℝ} (ht : 0 ≤ t) (ht' : t < 9 / 10) :
    MeasurableSet (sigmaHr Ω u χ t ∩ closedBall 0 (1 / 10)) := by
  have heq : sigmaHr Ω u χ t ∩ closedBall 0 (1 / 10) =
      (closedBall 0 (1 / 10) ∩ closure {y | 0 < u y}) ∩
        {z | unitBallVolume n ≤ monotonicityM (Ω.indicator u) (Ω.indicator χ) z t} := by
    ext z
    constructor
    · rintro ⟨⟨-, -, h3, h4⟩, hz⟩
      refine ⟨⟨hz, h3⟩, ?_⟩
      rw [mem_setOf_eq, monotonicityM_indicator h.isOpen ht (closedBall_subset_of_mem_K hΩ hz ht')]
      exact h4
    · rintro ⟨⟨hz, h3⟩, h4⟩
      rw [mem_setOf_eq, monotonicityM_indicator h.isOpen ht
        (closedBall_subset_of_mem_K hΩ hz ht')] at h4
      exact ⟨⟨closedBall_subset_of_mem_K hΩ hz (r := 0) (by norm_num) (mem_closedBall_self le_rfl),
        closedBall_subset_of_mem_K hΩ hz ht', h3, h4⟩, hz⟩
  rw [heq]
  exact (measurableSet_closedBall.inter isClosed_closure.measurableSet).inter
    (measurableSet_le measurable_const
      (measurable_monotonicityM (measurable_indicator_of_continuousOn h.isOpen h.continuousOn)
        h.measurable_chi t))

/-- `Σ^H(B_1) ∩ B̄_{1/10}` is measurable. By Proposition 3.4 the condition `M_z(r) ≥ |B_1|` for
all admissible `r` reduces to rational `r ∈ (0, 1/2]`. -/
theorem measurableSet_sigmaH_inter (h : IsVariationalSolution Ω C_V u χ)
    (hΩ : closedBall (0 : Rn n) 1 ⊆ Ω) :
    MeasurableSet (sigmaH (ball 0 1) u χ ∩ closedBall 0 (1 / 10)) := by
  have heq : sigmaH (ball 0 1) u χ ∩ closedBall 0 (1 / 10) =
      (closedBall 0 (1 / 10) ∩ closure {y | 0 < u y}) ∩
        ⋂ q ∈ {q : ℚ | 0 < q ∧ (q : ℝ) ≤ 1 / 2},
          {z | unitBallVolume n ≤ monotonicityM (Ω.indicator u) (Ω.indicator χ) z q} := by
    ext z
    simp only [mem_inter_iff, mem_iInter, mem_setOf_eq]
    constructor
    · rintro ⟨⟨-, h2, h3⟩, hz⟩
      refine ⟨⟨hz, h2⟩, fun q hq => ?_⟩
      have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.1
      rw [monotonicityM_indicator h.isOpen hq0.le
        (closedBall_subset_of_mem_K hΩ hz (by linarith [hq.2]))]
      exact h3 q hq0 (closedBall_subset_ball_one hz (by linarith [hq.2]))
    · rintro ⟨⟨hz, h2⟩, h3⟩
      refine ⟨⟨mem_ball_one_of_mem_K hz, h2, fun r hr hrB => ?_⟩, hz⟩
      obtain ⟨q, hq0, hqr⟩ := exists_rat_btwn (lt_min hr (by norm_num : (0 : ℝ) < 1 / 2))
      have hq2 : (q : ℝ) ≤ 1 / 2 := hqr.le.trans (min_le_right _ _)
      have hqr' : (q : ℝ) ≤ r := hqr.le.trans (min_le_left _ _)
      have hMq := h3 q ⟨by exact_mod_cast hq0, hq2⟩
      rw [monotonicityM_indicator h.isOpen hq0.le
        (closedBall_subset_of_mem_K hΩ hz (by linarith))] at hMq
      exact hMq.trans (Inputs.monotonicityM_le h hq0 hqr'
        (hrB.trans (ball_subset_closedBall.trans hΩ)))
  rw [heq]
  refine (measurableSet_closedBall.inter isClosed_closure.measurableSet).inter ?_
  refine MeasurableSet.biInter (to_countable _) fun q _ => ?_
  exact measurableSet_le measurable_const
    (measurable_monotonicityM (measurable_indicator_of_continuousOn h.isOpen h.continuousOn)
      h.measurable_chi q)

/-- The Naber–Valtorta data of a variational solution at the scale `t ∈ (0, 1/120]`:
`S = Σ^H_t(Ω) ∩ B̄_{1/10}`, `K = B̄_{1/10}`, `R = 1/120` (see the module docstring).
The dichotomy is Theorem 6.3 with the bound `N'` and the function `ε`. -/
def solNVData (h : IsVariationalSolution Ω C_V u χ)
    (hΩ : closedBall (0 : Rn n) 1 ⊆ Ω) {CJ Np : ℝ}
    (hCJ : ∀ (x : Rn n) (r : ℝ) (μ : Measure (Rn n)), 0 < r →
      closedBall x (50 * r) ⊆ Ω → IsFiniteMeasure μ → μ (sigmaHr Ω u χ r)ᶜ = 0 →
      x ∈ sigmaHr Ω u χ r → frequencyN u χ x (50 * r) ≤ Np →
      jonesBetaSq μ x r ≤ ENNReal.ofReal (CJ / r ^ (n - 1)) *
        ∫⁻ y in ball x r, ENNReal.ofReal (frequencyN u χ y (20 * r) - frequencyN u χ y r) ∂μ)
    (ε : ℝ → ℝ)
    (hε : ∀ δ, 0 < δ → ∀ (x : Rn n) (r t : ℝ), 0 < r → ball x (50 * r) ⊆ Ω → t ∈ Icc 0 r →
      (closedBall x r ∩ sigmaHr Ω u χ t).Nonempty →
      let Nmax := sSup ((fun y => frequencyN u χ y (20 * r)) '' (closedBall x r ∩ sigmaHr Ω u χ t))
      Nmax ≤ Np → Nmax < 1 + δ ∨ ∃ L : AffineSubspace ℝ (Rn n),
        Module.finrank ℝ L.direction ≤ n - 2 ∧
        {y ∈ closedBall x r ∩ sigmaHr Ω u χ t | Nmax - frequencyN u χ y r < ε δ} ⊆
          thickening (δ * r) (L : Set (Rn n)))
    (t : ℝ) (ht : 0 < t) (htR : t ≤ 1 / 120)
    (hN : ∀ z ∈ closedBall (0 : Rn n) (1 / 10), ∀ ρ, 0 < ρ → ρ < 1 / 2 →
      frequencyN u χ z ρ ≤ Np) : NVData n CJ Np ε where
  toJonesData := solJonesData h hΩ hCJ (sigmaHr Ω u χ t ∩ closedBall 0 (1 / 10)) t ht.le
    (measurableSet_sigmaHr_inter h hΩ ht.le (by linarith)) inter_subset_right
    (fun z hz ρ hρ htρ hρ6 => ⟨hz.1.1, closedBall_subset_of_mem_K hΩ hz.2 (by linarith),
      hz.1.2.2.1, hz.1.2.2.2.trans (Inputs.monotonicityM_le h ht htρ
        (closedBall_subset_of_mem_K hΩ hz.2 (by linarith)))⟩)
    (fun z hz => hN z hz.2)
  K := closedBall 0 (1 / 10)
  le_Nplus z hz r hr := by
    change solN Ω u χ z r ≤ Np
    have hr0 : 0 < r := ht.trans hr.1
    have hr6 : r ≤ 1 / 6 := by
      have : r ≤ 20 * (1 / 120 : ℝ) := hr.2
      linarith
    rw [solN_eq h hΩ hz.2 hr0.le (by linarith)]
    exact hN z hz.2 r hr0 (by linarith)
  dichotomy δ hδ x r hr htr hrR hxK hne := by
    change r ≤ 1 / 120 at hrR
    change maxFrequency (sigmaHr Ω u χ t ∩ closedBall 0 (1 / 10)) (solN Ω u χ) x r < 1 + δ ∨
      ∃ L : AffineSubspace ℝ (Rn n), Module.finrank ℝ L.direction ≤ n - 2 ∧
        {y | y ∈ (sigmaHr Ω u χ t ∩ closedBall 0 (1 / 10)) ∩ closedBall x r ∧
          maxFrequency (sigmaHr Ω u χ t ∩ closedBall 0 (1 / 10)) (solN Ω u χ) x r -
            solN Ω u χ y r < ε δ} ⊆ thickening (δ * r) (L : Set (Rn n))
    change (sigmaHr Ω u χ t ∩ closedBall 0 (1 / 10) ∩ closedBall x r).Nonempty at hne
    have hx : x ∈ closedBall (0 : Rn n) (1 / 10) := hxK (mem_closedBall_self hr.le)
    have hset : sigmaHr Ω u χ t ∩ closedBall 0 (1 / 10) ∩ closedBall x r =
        closedBall x r ∩ sigmaHr Ω u χ t := by
      ext y
      constructor
      · rintro ⟨⟨h1, -⟩, h2⟩
        exact ⟨h2, h1⟩
      · rintro ⟨h2, h1⟩
        exact ⟨⟨h1, hxK h2⟩, h2⟩
    have hmax : maxFrequency (sigmaHr Ω u χ t ∩ closedBall 0 (1 / 10)) (solN Ω u χ) x r =
        sSup ((fun y => frequencyN u χ y (20 * r)) '' (closedBall x r ∩ sigmaHr Ω u χ t)) := by
      unfold maxFrequency
      rw [hset]
      congr 1
      refine image_congr fun y hy => ?_
      exact solN_eq h hΩ (hxK hy.1) (by linarith) (by linarith)
    rw [hset] at hne
    have hx50 : ball x (50 * r) ⊆ Ω := by
      refine ball_subset_closedBall.trans (closedBall_subset_of_mem_K hΩ hx ?_)
      linarith
    have hNmax : sSup ((fun y => frequencyN u χ y (20 * r)) '' (closedBall x r ∩ sigmaHr Ω u χ t))
        ≤ Np := by
      refine csSup_le (hne.image _) (forall_mem_image.2 fun y hy => ?_)
      exact hN y (hxK hy.1) (20 * r) (by linarith) (by linarith)
    rcases hε δ hδ x r t hr hx50 ⟨ht.le, htr⟩ hne hNmax with h1 | ⟨L, hL, hsub⟩
    · left
      rw [hmax]
      exact h1
    · right
      refine ⟨L, hL, fun y hy => hsub ⟨?_, ?_⟩⟩
      · rw [← hset]
        exact hy.1
      · have := hy.2
        rw [hmax, solN_eq h hΩ (hxK hy.1.2) (by linarith) (by linarith)] at this
        exact this

end Data

end InnerVariational.NaberValtorta
