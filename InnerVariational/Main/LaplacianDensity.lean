/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Main.ModelLaplacian
public import InnerVariational.Singular.Density
public import InnerVariational.Singular.HeightLimit
public import InnerVariational.Frequency.Concrete
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Data.Real.StarOrdered
import InnerVariational.Main.RieszMeasure
public import InnerVariational.Defs.LaplacianMeasure
import InnerVariational.Kernel.Rescale
public import InnerVariational.Defs.VariationalSolution
import InnerVariational.Basic.Polar

/-!
# Upper bound and density of the Laplacian measure

Let `(u, χ)` be a variational solution on `Ω` and `ρ = Δu` its Laplacian measure
(`Main.exists_hasDistribLaplacianOn`). This file proves the two facts about `ρ` which the proof
of Theorem 8.7 of D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and
compactness for non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025),
no. 3, DOI 10.1002/cpa.22226; arXiv:2306.10131 (numbering of arXiv v2), needs besides
Corollary 8.4:

* **Upper bound** (`exists_measure_ball_le`, the cutoff argument of the proof of Lemma 3.3):
  `ρ(B_r(x)) ≤ K r^{n-1}` whenever `B̄_{2r}(x) ⊆ Ω`. Test with `η((· − x)/r)`, `η = 1` on `B_1`,
  and use `∫ Δη_{x,r} = 0` and `|u − u(x)| ≤ 2 C_V r` on `B_{2r}(x)`.
* **Density on `Σ^H`** (`hausdorffN_not_tendsto_laplacian_density_eq_zero`, end of the proof of
  Theorem 8.7): for `ℋ^{n-1}`-a.e. `x ∈ Σ^H`,
  `ρ(B_r(x)) / (ω_{n-1} r^{n-1}) → 2 α(n) √(H_x(u; 0+))`.

## Proof of the density on `Σ^H`

The paper passes to the weak-* limit of `Δv_{x,r}`. We test directly. By Lemma 8.5 (1)
(`Singular.renormalized_tendsto_alpha_ae`, the `L²` part with `R = 2`), for a.e. `x ∈ Σ^H` there is
a unit `ν` with `∫_{B_{2r}(x)} (u − m_r)² = o(r^{n+2} H_r)`, where `m_r = √H_r α |⟪· − x, ν⟫|` and
`H_r = H_x(u; r)`. For `η ∈ C^∞_c(B_2)` and `η_r = η((· − x)/r)`:

* `∫ m_r Δη_r = √H_r α r^{n-1} ∫ |⟪z, ν⟫| Δη = 2 √H_r α r^{n-1} ∫_{ℝ^{n-1}} η(L w) dw`
  (scaling and the model Laplacian `Δ|⟪·, ν⟫| = 2 ℋ^{n-1}⌊ν^⊥`, `Main/ModelLaplacian.lean`);
* `|∫ (u − m_r) Δη_r| ≤ ‖u − m_r‖_{L²(B_{2r})} ‖Δη_r‖_{L²} = o(r^{n-1} √H_r)` (Cauchy–Schwarz).

So `r^{1-n} ∫ η_r dρ → 2α√H_x(0+) ∫ η(L w) dw` (`tendsto_integral_mul_laplacian_scaleTest`).
Squeezing `1_{B_1}` between cutoffs `η⁻ ≤ 1_{B_1} ≤ η⁺` with `1_{B_s} ≤ η⁻`, `η⁺ ≤ 1_{B_t}`,
`s < 1 < t`, gives the density. No portmanteau step and no Hausdorff measure on hyperplanes
are needed.
-/

open MeasureTheory Metric Set Filter Topology Laplacian
open scoped NNReal ENNReal ContDiff RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational.Main

variable {n : ℕ}

/-! ### Bounds for rescaled test functions -/

/-- A test function has a bounded Laplacian. -/
theorem exists_abs_laplacian_le {η : Rn n → ℝ} (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η) :
    ∃ M, ∀ z, |Δ η z| ≤ M := by
  obtain ⟨M, hM⟩ := (continuous_laplacian hη).bounded_above_of_compact_support
    (hηc.mono' ((subset_tsupport _).trans (tsupport_laplacian_subset η)))
  exact ⟨M, fun z => by simpa [Real.norm_eq_abs] using hM z⟩

theorem abs_laplacian_scaleTest_le {η : Rn n → ℝ} (hη : ContDiff ℝ ∞ η) {M : ℝ}
    (hM : ∀ z, |Δ η z| ≤ M) (x : Rn n) (r : ℝ) (y : Rn n) :
    |Δ (scaleTest η x r) y| ≤ (r⁻¹) ^ 2 * M := by
  rw [laplacian_scaleTest (hη.of_le (by norm_cast)), abs_mul, abs_of_nonneg (sq_nonneg _)]
  exact mul_le_mul_of_nonneg_left (hM _) (sq_nonneg _)

/-- `∫ |⟪y − x, ν⟫| Δη_{x,r}(y) dy = r^{n-1} ∫ |⟪z, ν⟫| Δη(z) dz`. -/
theorem integral_absProfile_mul_laplacian_scaleTest (hn : 1 ≤ n) {η : Rn n → ℝ}
    (hη : ContDiff ℝ ∞ η) (ν x : Rn n) {r : ℝ} (hr : 0 < r) :
    ∫ y, absProfile ν x y * Δ (scaleTest η x r) y = r ^ (n - 1) * ∫ z, |⟪z, ν⟫| * Δ η z := by
  have h := Kernel.integral_comp_similarity (fun y => absProfile ν x y * Δ (scaleTest η x r) y)
    x hr (LinearIsometryEquiv.refl ℝ (Rn n))
  have e : ∀ z : Rn n, absProfile ν x (x + r • (LinearIsometryEquiv.refl ℝ (Rn n)) z) *
      Δ (scaleTest η x r) (x + r • (LinearIsometryEquiv.refl ℝ (Rn n)) z) =
      r⁻¹ * (|⟪z, ν⟫| * Δ η z) := fun z => by
    rw [laplacian_scaleTest (hη.of_le (by norm_cast))]
    simp only [LinearIsometryEquiv.coe_refl, id_eq, absProfile_apply, add_sub_cancel_left,
      smul_smul, inv_mul_cancel₀ hr.ne', one_smul, inner_smul_left, abs_mul,
      RCLike.conj_to_real, abs_of_pos hr]
    field_simp
  simp_rw [e] at h
  rw [integral_const_mul] at h
  have hrn : r ^ n = r ^ (n - 1) * r := by
    rw [← pow_succ]
    congr 1
    omega
  have hpos : 0 < r ^ n := pow_pos hr n
  set I := ∫ y, absProfile ν x y * Δ (scaleTest η x r) y
  calc I = r ^ n * ((r ^ n)⁻¹ * I) := by field_simp
    _ = r ^ n * (r⁻¹ * ∫ z, |⟪z, ν⟫| * Δ η z) := by rw [h]
    _ = r ^ (n - 1) * ∫ z, |⟪z, ν⟫| * Δ η z := by rw [hrn]; field_simp

/-! ### The upper bound `ρ(B_r(x)) ≤ K r^{n-1}` -/

section UpperBound

variable {Ω : Set (Rn n)} {C : ℝ≥0} {u χ : Rn n → ℝ}

/-- `ρ(B_r(x)) ≤ ∫ η_{x,r} dρ` for a cutoff `0 ≤ η ≤ 1` with `η = 1` on `B̄_1`. -/
theorem measure_ball_le_integral_scaleTest {ρ : Measure (Rn n)} {η : Rn n → ℝ}
    (hη01 : ∀ z, 0 ≤ η z ∧ η z ≤ 1) (hη1 : ∀ z ∈ closedBall (0 : Rn n) 1, η z = 1)
    (x : Rn n) {r : ℝ} (hr : 0 < r) (hint : Integrable (scaleTest η x r) ρ) :
    ρ (ball x r) ≤ ENNReal.ofReal (∫ y, scaleTest η x r y ∂ρ) := by
  rw [ofReal_integral_eq_lintegral_ofReal hint (.of_forall fun y => (hη01 _).1)]
  calc ρ (ball x r) = ∫⁻ y, (ball x r).indicator 1 y ∂ρ :=
        (lintegral_indicator_one measurableSet_ball).symm
    _ ≤ _ := lintegral_mono fun y => by
        by_cases hy : y ∈ ball x r
        · have hy' : r⁻¹ • (y - x) ∈ closedBall (0 : Rn n) 1 := by
            rw [mem_ball, dist_eq_norm] at hy
            rw [mem_closedBall_zero_iff, norm_smul, norm_inv, Real.norm_of_nonneg hr.le,
              inv_mul_le_iff₀ hr]
            linarith
          rw [indicator_of_mem hy, Pi.one_apply, scaleTest_apply, hη1 _ hy', ENNReal.ofReal_one]
        · rw [indicator_of_notMem hy]
          exact zero_le

/-- **Upper bound for the Laplacian measure** (the cutoff argument of the proof of Lemma 3.3).
The Laplacian measure of a variational solution satisfies `ρ(B_r(x)) ≤ K r^{n-1}` whenever
`B̄_{2r}(x) ⊆ Ω`. -/
theorem exists_measure_ball_le (hn : 1 ≤ n) (h : IsVariationalSolution Ω C u χ)
    {ρ : Measure (Rn n)} (hρ : HasDistribLaplacianOn Ω u ρ) :
    ∃ K : ℝ, ∀ x r, 0 < r → closedBall x (2 * r) ⊆ Ω →
      ρ (ball x r) ≤ ENNReal.ofReal (K * r ^ (n - 1)) := by
  obtain ⟨η, hηT, hη01, hη1⟩ := exists_isTestFunction_eq_one (isCompact_closedBall (0 : Rn n) 1)
    isOpen_ball (closedBall_subset_ball (by norm_num : (1 : ℝ) < 2))
  obtain ⟨M, hM⟩ := exists_abs_laplacian_le hηT.1 hηT.2.1
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  refine ⟨2 * C * M * 2 ^ n * unitBallVolume n, fun x r hr hB => ?_⟩
  have hB2 : ball x (2 * r) ⊆ Ω := ball_subset_closedBall.trans hB
  have hsupp : tsupport (scaleTest η x r) ⊆ ball x (2 * r) := by
    have := tsupport_scaleTest_subset_ball hηT.2.1 hηT.2.2 x hr
    rwa [mul_comm] at this
  have hT : IsTestFunction Ω (scaleTest η x r) :=
    ⟨contDiff_scaleTest hηT.1 x r, hasCompactSupport_scaleTest hηT.2.1 x hr.ne', hsupp.trans hB2⟩
  have hint : Integrable (scaleTest η x r) ρ := integrable_of_tsupport_subset hT.2.1
    (hρ.1 _ hT.2.1 hT.2.2) hT.1.continuous subset_rfl
  refine (measure_ball_le_integral_scaleTest hη01 hη1 x hr hint).trans
    (ENNReal.ofReal_le_ofReal ?_)
  rw [← hρ.2 _ hT]
  have hI1 := integrable_mul_laplacian h.isOpen h.continuousOn hT
  have hI2 : Integrable (Δ (scaleTest η x r)) :=
    (continuous_laplacian hT.1).integrable_of_hasCompactSupport
      (hT.2.1.mono' ((subset_tsupport _).trans (tsupport_laplacian_subset _)))
  have e : ∫ y, u y * Δ (scaleTest η x r) y = ∫ y, (u y - u x) * Δ (scaleTest η x r) y := by
    have hpt : ∀ y, (u y - u x) * Δ (scaleTest η x r) y =
        u y * Δ (scaleTest η x r) y - u x * Δ (scaleTest η x r) y := fun y => by ring
    simp_rw [hpt]
    rw [integral_sub hI1 (hI2.const_mul (u x)), integral_const_mul,
      integral_laplacian_eq_zero h.isOpen hT, mul_zero, sub_zero]
  rw [e]
  set c := 2 * C * r * ((r⁻¹) ^ 2 * M) with hc
  have hbd : ∀ y, ‖(u y - u x) * Δ (scaleTest η x r) y‖ ≤
      (ball x (2 * r)).indicator (fun _ => c) y := by
    intro y
    by_cases hy : y ∈ ball x (2 * r)
    · rw [indicator_of_mem hy, Real.norm_eq_abs, abs_mul]
      have hlip := (h.lipschitzOnWith x (2 * r) hB2).dist_le_mul y hy x
        (mem_ball_self (by positivity : (0 : ℝ) < 2 * r))
      rw [Real.dist_eq] at hlip
      have hyx : dist y x < 2 * r := hy
      refine mul_le_mul ?_ (abs_laplacian_scaleTest_le hηT.1 hM x r y) (abs_nonneg _)
        (by positivity)
      calc |u y - u x| ≤ C * dist y x := hlip
        _ ≤ C * (2 * r) := mul_le_mul_of_nonneg_left hyx.le C.2
        _ = 2 * C * r := by ring
    · have hy' : y ∉ tsupport (scaleTest η x r) := fun h' => hy (hsupp h')
      rw [indicator_of_notMem hy, laplacian_eq_zero_of_notMem_tsupport hy', mul_zero, norm_zero]
  have hgi : Integrable ((ball x (2 * r)).indicator fun _ => c) :=
    (integrableOn_const measure_ball_lt_top.ne).integrable_indicator measurableSet_ball
  refine (le_abs_self _).trans ?_
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le hgi (.of_forall hbd)).trans (le_of_eq ?_)
  rw [integral_indicator_const _ measurableSet_ball, smul_eq_mul, measureReal_def,
    volume_ball_toReal x (by positivity), hc]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  field_simp
  ring

end UpperBound

/-! ### The blow-up limit of `r^{1-n} ∫ u Δη_{x,r}` -/

theorem continuous_absProfile (ν x : Rn n) : Continuous (absProfile ν x) :=
  ((continuous_id.sub continuous_const).inner continuous_const).abs

/-- If `u` is `L²`-close to the profile `√H_r α |⟪· − x, ν⟫|` on `B_{2r}(x)` at scale
`r^{n+2} H_r` (Lemma 8.5 (1)), then `r^{1-n} ∫ u Δη_{x,r} → √H₀ α ∫ |⟪z, ν⟫| Δη(z) dz` for every
`η ∈ C^∞_c(B_2)`. -/
theorem tendsto_integral_mul_laplacian_scaleTest (hn : 1 ≤ n) {Ω : Set (Rn n)} (hΩ : IsOpen Ω)
    {u : Rn n → ℝ} (hu : ContinuousOn u Ω) {x : Rn n} (hx : x ∈ Ω) {ν : Rn n} {α H₀ : ℝ}
    {H : ℝ → ℝ} (hH : Tendsto H (𝓝[>] 0) (𝓝 H₀)) (hHpos : ∀ᶠ r in 𝓝[>] 0, 0 < H r)
    (hL2 : Tendsto (fun r => (∫ y in ball x (2 * r), (u y - √(H r) * α * absProfile ν x y) ^ 2) /
      (r ^ (n + 2) * H r)) (𝓝[>] 0) (𝓝 0))
    {η : Rn n → ℝ} (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hη2 : tsupport η ⊆ ball 0 2) :
    Tendsto (fun r => (∫ y, u y * Δ (scaleTest η x r) y) / r ^ (n - 1)) (𝓝[>] 0)
      (𝓝 (√H₀ * α * ∫ z, |⟪z, ν⟫| * Δ η z)) := by
  obtain ⟨δ, hδ, hδΩ⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hΩ.mem_nhds hx)
  obtain ⟨M, hM⟩ := exists_abs_laplacian_le hη hηc
  set c := ∫ z, |⟪z, ν⟫| * Δ η z with hcdef
  set E : ℝ → ℝ := fun r =>
    ∫ y, (u y - √(H r) * α * absProfile ν x y) * Δ (scaleTest η x r) y with hEdef
  have hev : ∀ᶠ r in 𝓝[>] 0, 0 < r ∧ 2 * r < δ ∧ 0 < H r := by
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (by positivity : (0 : ℝ) < δ / 2),
      hHpos] with r hr hr2 hHr
    exact ⟨hr, by linarith [hr2.2], hHr⟩
  have hsuppB : ∀ r, 0 < r → tsupport (scaleTest η x r) ⊆ ball x (2 * r) := fun r hr => by
    have := tsupport_scaleTest_subset_ball hηc hη2 x hr
    rwa [mul_comm] at this
  -- the decomposition `u = m_r + (u - m_r)`
  have hdec : ∀ᶠ r in 𝓝[>] 0, (∫ y, u y * Δ (scaleTest η x r) y) / r ^ (n - 1) =
      √(H r) * α * c + E r / r ^ (n - 1) := by
    filter_upwards [hev] with r ⟨hr, hrδ, _⟩
    have hT : IsTestFunction Ω (scaleTest η x r) :=
      ⟨contDiff_scaleTest hη x r, hasCompactSupport_scaleTest hηc x hr.ne',
        (hsuppB r hr).trans (ball_subset_closedBall.trans
          ((closedBall_subset_closedBall hrδ.le).trans hδΩ))⟩
    have hT' : IsTestFunction univ (scaleTest η x r) := ⟨hT.1, hT.2.1, subset_univ _⟩
    have hI1 := integrable_mul_laplacian hΩ hu hT
    have hI2 := integrable_mul_laplacian isOpen_univ (continuous_absProfile ν x).continuousOn hT'
    have hE : E r = (∫ y, u y * Δ (scaleTest η x r) y) -
        √(H r) * α * (r ^ (n - 1) * c) := by
      rw [← integral_absProfile_mul_laplacian_scaleTest hn hη ν x hr, ← integral_const_mul,
        ← integral_sub hI1 (hI2.const_mul _)]
      refine integral_congr_ae (.of_forall fun y => ?_)
      simp only
      ring
    rw [hE]
    have : 0 < r ^ (n - 1) := pow_pos hr _
    field_simp
    ring
  -- the error term, by Cauchy–Schwarz on `B_{2r}(x)`
  have herr : Tendsto (fun r => E r / r ^ (n - 1)) (𝓝[>] 0) (𝓝 0) := by
    set V := unitBallVolume n
    set a : ℝ → ℝ := fun r =>
      (∫ y in ball x (2 * r), (u y - √(H r) * α * absProfile ν x y) ^ 2) / (r ^ (n + 2) * H r)
      with hadef
    have hb : Tendsto (fun r => a r * H r * (M ^ 2 * 2 ^ n * V)) (𝓝[>] 0) (𝓝 0) := by
      simpa using (hL2.mul hH).mul_const (M ^ 2 * 2 ^ n * V)
    have hbd : ∀ᶠ r in 𝓝[>] 0, (E r / r ^ (n - 1)) ^ 2 ≤ a r * H r * (M ^ 2 * 2 ^ n * V) := by
      filter_upwards [hev] with r ⟨hr, hrδ, hHr⟩
      set B := ball x (2 * r)
      set F : Rn n → ℝ := fun y => u y - √(H r) * α * absProfile ν x y with hFdef
      set G : Rn n → ℝ := Δ (scaleTest η x r) with hGdef
      have hBΩ : closedBall x (2 * r) ⊆ Ω := (closedBall_subset_closedBall hrδ.le).trans hδΩ
      have hFc : ContinuousOn F (closedBall x (2 * r)) :=
        (hu.mono hBΩ).sub (continuous_const.mul (continuous_absProfile ν x)).continuousOn
      have hGc : Continuous G := continuous_laplacian (contDiff_scaleTest hη x r)
      have hK := isCompact_closedBall x (2 * r)
      have iF2 : IntegrableOn (fun y => F y ^ 2) B :=
        ((hFc.pow 2).integrableOn_compact hK).mono_set ball_subset_closedBall
      have iG2 : IntegrableOn (fun y => G y ^ 2) B :=
        ((hGc.continuousOn.pow 2).integrableOn_compact hK).mono_set ball_subset_closedBall
      have iFG : IntegrableOn (fun y => F y * G y) B :=
        ((hFc.mul hGc.continuousOn).integrableOn_compact hK).mono_set ball_subset_closedBall
      have hEB : E r = ∫ y in B, F y * G y := by
        refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_).symm
        change F y * Δ (scaleTest η x r) y = 0
        rw [laplacian_eq_zero_of_notMem_tsupport fun h' => hy (hsuppB r hr h'), mul_zero]
      have hcs := sq_integral_mul_le iF2 iG2 iFG
      have hG2 : ∫ y in B, G y ^ 2 ≤ ((r⁻¹) ^ 2 * M) ^ 2 * volume.real B := by
        refine (le_abs_self _).trans ?_
        rw [← Real.norm_eq_abs]
        refine norm_setIntegral_le_of_norm_le_const measure_ball_lt_top fun y _ => ?_
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (abs_laplacian_scaleTest_le hη hM x r y) 2
      have hF2 : ∫ y in B, F y ^ 2 = a r * (r ^ (n + 2) * H r) :=
        (div_mul_cancel₀ _ (by positivity)).symm
      have hF0 : 0 ≤ ∫ y in B, F y ^ 2 := integral_nonneg fun y => sq_nonneg _
      have hvol : volume.real B = (2 * r) ^ n * V := by
        rw [measureReal_def, volume_ball_toReal x (by positivity)]
      have key : (E r) ^ 2 ≤
          a r * (r ^ (n + 2) * H r) * (((r⁻¹) ^ 2 * M) ^ 2 * ((2 * r) ^ n * V)) := by
        rw [hEB, ← hF2, ← hvol]
        exact hcs.trans (mul_le_mul_of_nonneg_left hG2 hF0)
      have hpow : r ^ (n + 2) * r ^ n = (r ^ (n - 1)) ^ 2 * r ^ 4 := by
        rw [← pow_add, ← pow_mul, ← pow_add]
        congr 1
        omega
      rw [div_pow, div_le_iff₀ (by positivity)]
      refine key.trans (le_of_eq ?_)
      have hr0 : r ≠ 0 := hr.ne'
      calc a r * (r ^ (n + 2) * H r) * (((r⁻¹) ^ 2 * M) ^ 2 * ((2 * r) ^ n * V))
          = a r * H r * (M ^ 2 * 2 ^ n * V) * (r ^ (n + 2) * r ^ n) * (r⁻¹) ^ 4 := by ring
        _ = a r * H r * (M ^ 2 * 2 ^ n * V) * (r ^ (n - 1)) ^ 2 := by
          rw [hpow]
          field_simp
    have hsq : Tendsto (fun r => √(a r * H r * (M ^ 2 * 2 ^ n * V))) (𝓝[>] 0) (𝓝 0) := by
      simpa using (Real.continuous_sqrt.tendsto 0).comp hb
    refine squeeze_zero_norm' ?_ hsq
    filter_upwards [hbd] with r hr
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hr
  have h1 : Tendsto (fun r => √(H r) * α * c) (𝓝[>] 0) (𝓝 (√H₀ * α * c)) :=
    (((Real.continuous_sqrt.tendsto H₀).comp hH).mul_const α).mul_const c
  simpa using (h1.add herr).congr' (hdec.mono fun r hr => hr.symm)

/-! ### The density of the Laplacian measure on `Σ^H` -/

/-- `η ∘ L` is integrable for a test function `η` and a linear isometric embedding `L`. -/
theorem integrable_comp_linearIsometry {m : ℕ} (L : Rn m →ₗᵢ[ℝ] Rn n) {η : Rn n → ℝ}
    (hη : Continuous η) (hηc : HasCompactSupport η) : Integrable fun w => η (L w) := by
  refine (hη.comp L.continuous).integrable_of_hasCompactSupport ?_
  obtain ⟨R, hR⟩ := hηc.isCompact.isBounded.subset_closedBall 0
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Rn m) R) fun w hw => ?_
  change η (L w) = 0
  refine image_eq_zero_of_notMem_tsupport fun hmem => hw ?_
  have := mem_closedBall_zero_iff.1 (hR hmem)
  rwa [LinearIsometry.norm_map, ← mem_closedBall_zero_iff] at this

/-- `ω_m s^m ≤ ∫ η(L w) dw` if `0 ≤ η` and `η = 1` on `B̄_s`. -/
theorem le_integral_comp_linearIsometry {m : ℕ} (L : Rn m →ₗᵢ[ℝ] Rn n) {η : Rn n → ℝ}
    (hη : Continuous η) (hηc : HasCompactSupport η) (hη0 : ∀ z, 0 ≤ η z) {s : ℝ} (hs : 0 < s)
    (hη1 : ∀ z ∈ closedBall (0 : Rn n) s, η z = 1) :
    s ^ m * unitBallVolume m ≤ ∫ w, η (L w) := by
  rw [← volume_ball_toReal 0 hs, ← measureReal_def, ← integral_indicator_one measurableSet_ball]
  refine integral_mono ((integrableOn_const measure_ball_lt_top.ne).integrable_indicator
    measurableSet_ball) (integrable_comp_linearIsometry L hη hηc) fun w => ?_
  by_cases hw : w ∈ ball (0 : Rn m) s
  · rw [indicator_of_mem hw, Pi.one_apply, hη1]
    rw [mem_closedBall_zero_iff, LinearIsometry.norm_map]
    exact (mem_ball_zero_iff.1 hw).le
  · rw [indicator_of_notMem hw]
    exact hη0 _

/-- `∫ η(L w) dw ≤ ω_m t^m` if `η ≤ 1` and `tsupport η ⊆ B_t`. -/
theorem integral_comp_linearIsometry_le {m : ℕ} (L : Rn m →ₗᵢ[ℝ] Rn n) {η : Rn n → ℝ}
    (hη : Continuous η) (hηc : HasCompactSupport η) (hη1 : ∀ z, η z ≤ 1) {t : ℝ} (ht : 0 < t)
    (hηt : tsupport η ⊆ ball 0 t) :
    ∫ w, η (L w) ≤ t ^ m * unitBallVolume m := by
  rw [← volume_ball_toReal 0 ht, ← measureReal_def, ← integral_indicator_one measurableSet_ball]
  refine integral_mono (integrable_comp_linearIsometry L hη hηc)
    ((integrableOn_const measure_ball_lt_top.ne).integrable_indicator measurableSet_ball)
    fun w => ?_
  by_cases hw : w ∈ ball (0 : Rn m) t
  · rw [indicator_of_mem hw, Pi.one_apply]
    exact hη1 _
  · rw [indicator_of_notMem hw]
    refine le_of_eq (image_eq_zero_of_notMem_tsupport fun hmem => hw ?_)
    have := mem_ball_zero_iff.1 (hηt hmem)
    rwa [LinearIsometry.norm_map, ← mem_ball_zero_iff] at this

/-- **The density at a point where the blow-up is the one-dimensional profile.** If `ρ = Δu` on
`Ω` and `u` is `L²`-close to `√H_r α |⟪· − x, ν⟫|` on `B_{2r}(x)` at scale `r^{n+2} H_r`, with
`H_r → H₀`, then `ρ(B_r(x)) / (ω_{n-1} r^{n-1}) → 2 α √H₀`. -/
theorem tendsto_measure_ball_div_of_profile (hn : 2 ≤ n) {Ω : Set (Rn n)} (hΩ : IsOpen Ω)
    {u : Rn n → ℝ} (hu : ContinuousOn u Ω) {ρ : Measure (Rn n)}
    (hρ : HasDistribLaplacianOn Ω u ρ) {x : Rn n} (hx : x ∈ Ω) {ν : Rn n} (hν : ‖ν‖ = 1)
    {α H₀ : ℝ} {H : ℝ → ℝ} (hH : Tendsto H (𝓝[>] 0) (𝓝 H₀)) (hHpos : ∀ᶠ r in 𝓝[>] 0, 0 < H r)
    (hα : 0 ≤ α)
    (hL2 : Tendsto (fun r => (∫ y in ball x (2 * r), (u y - √(H r) * α * absProfile ν x y) ^ 2) /
      (r ^ (n + 2) * H r)) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun r => ρ (ball x r) / ENNReal.ofReal (unitBallVolume (n - 1) * r ^ (n - 1)))
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal (2 * α * √H₀))) := by
  obtain ⟨L, -, hL⟩ := exists_integral_abs_inner_mul_laplacian (by omega : 1 ≤ n) hν
  set v₁ := unitBallVolume (n - 1) with hvdef
  have hv0 : 0 < v₁ := unitBallVolume_pos _
  set A := 2 * α * √H₀ with hAdef
  have hA : 0 ≤ A := by positivity
  obtain ⟨δ, hδ, hδΩ⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hΩ.mem_nhds hx)
  -- small radii
  have hsmall : ∀ᶠ r in 𝓝[>] 0, 0 < r ∧ 2 * r < δ := by
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (by positivity : (0 : ℝ) < δ / 2)]
      with r hr hr2
    exact ⟨hr, by linarith [hr2.2]⟩
  have hBΩ : ∀ r, 2 * r < δ → closedBall x (2 * r) ⊆ Ω := fun r hr =>
    (closedBall_subset_closedBall hr.le).trans hδΩ
  have hTest : ∀ η : Rn n → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ ball 0 2 →
      ∀ r, 0 < r → 2 * r < δ → IsTestFunction Ω (scaleTest η x r) := fun η hη hηc hη2 r hr hrδ =>
    isTestFunction_scaleTest hη hηc hη2 x hr (by
      rw [mul_comm]
      exact ball_subset_closedBall.trans (hBΩ r hrδ))
  -- the limit of `r^{1-n} ∫ η_{x,r} dρ`
  have hJ : ∀ η : Rn n → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ ball 0 2 →
      Tendsto (fun r => (∫ y, scaleTest η x r y ∂ρ) / r ^ (n - 1)) (𝓝[>] 0)
        (𝓝 (A * ∫ w, η (L w))) := by
    intro η hη hηc hη2
    have h1 := tendsto_integral_mul_laplacian_scaleTest (by omega) hΩ hu hx hH hHpos hL2 hη hηc
      hη2 (ν := ν)
    rw [hL η hη hηc] at h1
    have e : √H₀ * α * (2 * ∫ w, η (L w)) = A * ∫ w, η (L w) := by rw [hAdef]; ring
    rw [e] at h1
    refine h1.congr' ?_
    filter_upwards [hsmall] with r ⟨hr, hrδ⟩
    rw [hρ.2 _ (hTest η hη hηc hη2 r hr hrδ)]
  have hfin : ∀ r, 0 < r → 2 * r < δ → ρ (ball x r) < ⊤ := fun r hr hrδ =>
    (measure_mono (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))))
      |>.trans_lt (hρ.1 _ (isCompact_closedBall x (2 * r)) (hBΩ r hrδ))
  have hintρ : ∀ η : Rn n → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ ball 0 2 →
      ∀ r, 0 < r → 2 * r < δ → Integrable (scaleTest η x r) ρ := fun η hη hηc hη2 r hr hrδ => by
    have hT := hTest η hη hηc hη2 r hr hrδ
    exact integrable_of_tsupport_subset hT.2.1 (hρ.1 _ hT.2.1 hT.2.2) hT.1.continuous subset_rfl
  set F : ℝ → ℝ := fun r => (ρ (ball x r)).toReal / (v₁ * r ^ (n - 1)) with hFdef
  have hF0 : ∀ᶠ r in 𝓝[>] 0, 0 ≤ F r := by
    filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    exact div_nonneg ENNReal.toReal_nonneg (by positivity)
  have hFlim : Tendsto F (𝓝[>] 0) (𝓝 A) := by
    refine tendsto_order.2 ⟨fun a' ha' => ?_, fun a' ha' => ?_⟩
    · -- lower bound
      rcases lt_or_ge a' 0 with ha0 | ha0
      · filter_upwards [hF0] with r hr
        exact ha0.trans_le hr
      have hApos : 0 < A := ha0.trans_lt ha'
      have hcs : Tendsto (fun s : ℝ => A * s ^ (n - 1)) (𝓝[<] 1) (𝓝 A) := by
        have : Continuous fun s : ℝ => A * s ^ (n - 1) := continuous_const.mul (continuous_pow _)
        simpa using (this.tendsto 1).mono_left nhdsWithin_le_nhds
      obtain ⟨s, hs1, hs2⟩ := ((hcs.eventually (lt_mem_nhds ha')).and
        (Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1))).exists
      obtain ⟨η, hηT, hη01, hη1⟩ := exists_isTestFunction_eq_one
        (isCompact_closedBall (0 : Rn n) s) isOpen_ball (closedBall_subset_ball hs2.2)
      have hη2 : tsupport η ⊆ ball 0 2 := hηT.2.2.trans (ball_subset_ball (by norm_num))
      have hI := le_integral_comp_linearIsometry L hηT.1.continuous hηT.2.1
        (fun z => (hη01 z).1) hs2.1 hη1
      have hlt : a' * v₁ < A * ∫ w, η (L w) :=
        calc a' * v₁ < A * s ^ (n - 1) * v₁ := mul_lt_mul_of_pos_right hs1 hv0
          _ = A * (s ^ (n - 1) * v₁) := by ring
          _ ≤ A * ∫ w, η (L w) := mul_le_mul_of_nonneg_left hI hA
      filter_upwards [(hJ η hηT.1 hηT.2.1 hη2).eventually (lt_mem_nhds hlt), hsmall]
        with r hr ⟨hr0, hrδ⟩
      -- `∫ η_{x,r} dρ ≤ ρ(B_r(x))`
      have hle : ∫ y, scaleTest η x r y ∂ρ ≤ (ρ (ball x r)).toReal := by
        rw [← measureReal_def, ← integral_indicator_one measurableSet_ball]
        refine integral_mono (hintρ η hηT.1 hηT.2.1 hη2 r hr0 hrδ)
          ((integrableOn_const (hfin r hr0 hrδ).ne).integrable_indicator measurableSet_ball)
          fun y => ?_
        by_cases hy : y ∈ ball x r
        · rw [indicator_of_mem hy, Pi.one_apply]
          exact (hη01 _).2
        · rw [indicator_of_notMem hy]
          refine le_of_eq (image_eq_zero_of_notMem_tsupport fun hmem => hy ?_)
          have := tsupport_scaleTest_subset_ball hηT.2.1 hηT.2.2 x hr0 hmem
          rwa [mul_one] at this
      have hpos : 0 < r ^ (n - 1) := pow_pos hr0 _
      rw [hFdef]
      simp only
      rw [lt_div_iff₀ (by positivity)]
      rw [lt_div_iff₀ hpos] at hr
      nlinarith
    · -- upper bound
      have hcs : Tendsto (fun t : ℝ => A * t ^ (n - 1)) (𝓝[>] 1) (𝓝 A) := by
        have : Continuous fun t : ℝ => A * t ^ (n - 1) := continuous_const.mul (continuous_pow _)
        simpa using (this.tendsto 1).mono_left nhdsWithin_le_nhds
      obtain ⟨t, ht1, ht2⟩ := ((hcs.eventually (gt_mem_nhds ha')).and
        (Ioo_mem_nhdsGT (by norm_num : (1 : ℝ) < 2))).exists
      obtain ⟨η, hηT, hη01, hη1⟩ := exists_isTestFunction_eq_one
        (isCompact_closedBall (0 : Rn n) 1) isOpen_ball (closedBall_subset_ball ht2.1)
      have hη2 : tsupport η ⊆ ball 0 2 := hηT.2.2.trans (ball_subset_ball ht2.2.le)
      have hI := integral_comp_linearIsometry_le L hηT.1.continuous hηT.2.1
        (fun z => (hη01 z).2) (by linarith [ht2.1]) hηT.2.2
      have hlt : A * ∫ w, η (L w) < a' * v₁ :=
        calc A * ∫ w, η (L w) ≤ A * (t ^ (n - 1) * v₁) := mul_le_mul_of_nonneg_left hI hA
          _ = A * t ^ (n - 1) * v₁ := by ring
          _ < a' * v₁ := mul_lt_mul_of_pos_right ht1 hv0
      filter_upwards [(hJ η hηT.1 hηT.2.1 hη2).eventually (gt_mem_nhds hlt), hsmall]
        with r hr ⟨hr0, hrδ⟩
      have hle : (ρ (ball x r)).toReal ≤ ∫ y, scaleTest η x r y ∂ρ := by
        have h1 := measure_ball_le_integral_scaleTest hη01 hη1 x hr0
          (hintρ η hηT.1 hηT.2.1 hη2 r hr0 hrδ)
        exact ENNReal.toReal_le_of_le_ofReal
          (integral_nonneg fun y => (hη01 _).1) h1
      have hpos : 0 < r ^ (n - 1) := pow_pos hr0 _
      rw [hFdef]
      simp only
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hpos] at hr
      nlinarith
  -- back to `ℝ≥0∞`
  have hconv : ∀ᶠ r in 𝓝[>] 0, ENNReal.ofReal (F r) =
      ρ (ball x r) / ENNReal.ofReal (v₁ * r ^ (n - 1)) := by
    filter_upwards [hsmall] with r ⟨hr, hrδ⟩
    rw [hFdef]
    simp only
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_toReal (hfin r hr hrδ).ne]
  exact (ENNReal.tendsto_ofReal hFlim).congr' hconv

variable {Ω : Set (Rn n)} {C : ℝ≥0} {u χ : Rn n → ℝ} in
/-- **Density of the Laplacian measure on `Σ^H`** (end of the proof of Theorem 8.7). For
`ℋ^{n-1}`-a.e. `x ∈ Σ^H`, the Laplacian measure has density
`ρ(B_r(x)) / (ω_{n-1} r^{n-1}) → 2 α(n) √(H_x(u; 0+))`. From Lemma 8.5 (1) and the model
Laplacian (`Main/ModelLaplacian.lean`). -/
theorem hausdorffN_not_tendsto_laplacian_density_eq_zero [NeZero n] (hn : 2 ≤ n)
    (h : IsVariationalSolution Ω C u χ) {ρ : Measure (Rn n)} (hρ : HasDistribLaplacianOn Ω u ρ) :
    hausdorffN n (n - 1) {x | x ∈ sigmaH Ω u χ ∧ ¬ Tendsto
      (fun r => ρ (ball x r) / ENNReal.ofReal (unitBallVolume (n - 1) * r ^ (n - 1)))
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal (2 * alphaN n * √(heightHZero u x))))} = 0 := by
  refine measure_mono_null ?_ (Singular.renormalized_tendsto_alpha_ae hn h)
  rintro x ⟨hxS, hx⟩
  refine ⟨hxS, fun ⟨ν, hν, hR⟩ => hx ?_⟩
  obtain ⟨δ, hδ, hδΩ⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (h.isOpen.mem_nhds hxS.1)
  have hHpos : ∀ᶠ r in 𝓝[>] 0, 0 < heightH u x r := by
    filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
    exact h.heightH_pos hxS.2.1 hr.1 ((closedBall_subset_closedBall hr.2.le).trans hδΩ)
  exact tendsto_measure_ball_div_of_profile hn h.isOpen h.continuousOn hρ hxS.1 hν
    (Singular.tendsto_heightH_zero h hxS) hHpos (Singular.alphaN_pos (n := n)).le (hR 2 two_pos).1

end InnerVariational.Main
