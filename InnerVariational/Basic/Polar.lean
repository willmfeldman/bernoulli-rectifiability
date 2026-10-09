/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Basic.Setup
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import GMTFoundations.Defs.Setup

/-!
# Polar coordinates on `ℝⁿ`

This file develops polar coordinates for Lebesgue measure on `Rn n`, in terms of the sphere
measure `sphereMeasure n` of `Basic/Setup.lean`. The key input is Mathlib's
`Measure.measurePreserving_homeomorphUnitSphereProd`: the map `y ↦ (y / ‖y‖, ‖y‖)` sends
Lebesgue measure on `ℝⁿ ∖ {0}` to `σ ⊗ r^{n-1} dr` on `S^{n-1} × (0, ∞)`.

## Main results

* `integral_eq_integral_Ioi_sphere`: `∫ g = ∫_0^∞ t^{n-1} ∫_{S^{n-1}} g(t ω) dσ(ω) dt`.
* `integral_ball_diff_ball`, `integral_ball_eq`: the annulus and ball formulas
  `∫_{B_b(x) ∖ B_a(x)} f = ∫_a^b sphereIntegral f x s ds`.
* `intervalIntegrable_sphereIntegral`: `s ↦ sphereIntegral f x s` is interval integrable when `f`
  is integrable on the ball.
* `sphereMeasure_real_univ`, `sphereIntegral_const`: `σ(S^{n-1}) = n |B_1|`.
* `ae_sphere_ae_of_ae`: a property that holds Lebesgue-a.e. holds, along `σ`-a.e. ray from `x`,
  for a.e. radius. `ae_ae_smul_notMem` and `ae_ae_add_smul_notMem`: a Lebesgue-null set meets a.e.
  line `t ↦ t • y`, resp. `t ↦ y + t • v`, in a null set of parameters.
* `LipschitzOnWith.ae_sphere_ae_hasDerivAt`: along `σ`-a.e. ray, a function Lipschitz on
  `ball x R` has radial derivative `⟪∇u(x + t ω), ω⟫` for a.e. `t ∈ (0, R)`.

## Dimension

Most statements assume `[NeZero n]`, i.e. `n ≥ 1`. For `n = 0` the space `Rn 0` is a point of
Lebesgue measure `1` and the sphere is empty, so the polar formula fails.
-/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

/-! ### The polar homeomorphism -/

theorem finrank_Rn (n : ℕ) : Module.finrank ℝ (Rn n) = n := finrank_euclideanSpace_fin

instance (n : ℕ) : IsFiniteMeasure (sphereMeasure n) := by
  unfold sphereMeasure; infer_instance

/-- Polar coordinates: `y ↦ (y / ‖y‖, ‖y‖)` sends Lebesgue measure on `ℝⁿ ∖ {0}` to
`σ ⊗ r^{n-1} dr`. -/
theorem measurePreserving_polar (n : ℕ) :
    MeasurePreserving (homeomorphUnitSphereProd (Rn n))
      (Measure.comap Subtype.val (volume : Measure (Rn n)))
      ((sphereMeasure n).prod (Measure.volumeIoiPow (n - 1))) := by
  have := (volume : Measure (Rn n)).measurePreserving_homeomorphUnitSphereProd
  rw [finrank_Rn] at this
  exact this

theorem homeomorphUnitSphereProd_smul_eq (y : ({0}ᶜ : Set (Rn n))) :
    (((homeomorphUnitSphereProd (Rn n)) y).2 : ℝ) • (((homeomorphUnitSphereProd (Rn n)) y).1 : Rn n)
      = y := by
  rw [← homeomorphUnitSphereProd_symm_apply_coe, Homeomorph.symm_apply_apply]

variable {E : Type*} [NormedAddCommGroup E]

/-! ### The radial measure `r^k dr` on `(0, ∞)` -/

theorem integral_volumeIoiPow [NormedSpace ℝ E] (k : ℕ) (F : ℝ → E) :
    ∫ t : Ioi (0 : ℝ), F t ∂Measure.volumeIoiPow k = ∫ t in Ioi (0 : ℝ), t ^ k • F t := by
  simp only [Measure.volumeIoiPow, ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul,
    integral_subtype_comap measurableSet_Ioi fun a => Real.toNNReal (a ^ k) • F a,
    setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_]
  · rw [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg (le_of_lt ht) _)]
  · exact (measurable_subtype_coe.pow_const _).real_toNNReal

theorem integrable_volumeIoiPow_iff [NormedSpace ℝ E] (k : ℕ) {F : ℝ → E} :
    Integrable (fun t : Ioi (0 : ℝ) => F t) (Measure.volumeIoiPow k) ↔
      IntegrableOn (fun t => t ^ k • F t) (Ioi 0) := by
  rw [Measure.volumeIoiPow, integrable_withDensity_iff_integrable_smul' (by fun_prop) (by simp),
    integrableOn_iff_comap_subtypeVal measurableSet_Ioi]
  refine integrable_congr (.of_forall fun t => ?_)
  simp [ENNReal.toReal_ofReal (pow_nonneg (le_of_lt t.2) _)]

/-! ### Polar formulas on all of `ℝⁿ` -/

/-- Polar coordinates, product form. -/
theorem integral_eq_integral_prod_polar [NormedSpace ℝ E] [NeZero n] (g : Rn n → E) :
    ∫ y, g y = ∫ p : sphere (0 : Rn n) 1 × Ioi (0 : ℝ), g ((p.2 : ℝ) • (p.1 : Rn n))
      ∂(sphereMeasure n).prod (Measure.volumeIoiPow (n - 1)) := by
  have h := (measurePreserving_polar n).integral_comp
    (homeomorphUnitSphereProd (Rn n)).measurableEmbedding
    (fun p => g ↑((homeomorphUnitSphereProd (Rn n)).symm p))
  simp only [Homeomorph.symm_apply_apply, homeomorphUnitSphereProd_symm_apply_coe] at h
  rw [← h, integral_subtype_comap (measurableSet_singleton _).compl,
    restrict_compl_singleton]

/-- Polar coordinates, product form, for integrability. -/
theorem integrable_iff_integrable_prod_polar [NeZero n] {g : Rn n → E} :
    Integrable g ↔ Integrable (fun p : sphere (0 : Rn n) 1 × Ioi (0 : ℝ) =>
      g ((p.2 : ℝ) • (p.1 : Rn n))) ((sphereMeasure n).prod (Measure.volumeIoiPow (n - 1))) := by
  have h := (measurePreserving_polar n).integrable_comp_emb
    (homeomorphUnitSphereProd (Rn n)).measurableEmbedding
    (g := fun p => g ↑((homeomorphUnitSphereProd (Rn n)).symm p))
  simp only [Function.comp_def, homeomorphUnitSphereProd_symm_apply_coe,
    homeomorphUnitSphereProd_smul_eq] at h
  rw [← h]
  have := integrableOn_iff_comap_subtypeVal (f := g) (μ := volume)
    (measurableSet_singleton (0 : Rn n)).compl
  rw [IntegrableOn, restrict_compl_singleton] at this
  exact this

/-- **Polar coordinates**: `∫ g = ∫_0^∞ t^{n-1} ∫_{S^{n-1}} g(t ω) dσ(ω) dt`. -/
theorem integral_eq_integral_Ioi_sphere [NormedSpace ℝ E] [NeZero n] {g : Rn n → E}
    (hg : Integrable g) :
    ∫ y, g y = ∫ t in Ioi (0 : ℝ), t ^ (n - 1) • ∫ ω, g (t • (ω : Rn n)) ∂sphereMeasure n := by
  rw [integral_eq_integral_prod_polar,
    integral_prod_symm _ (integrable_iff_integrable_prod_polar.1 hg)]
  exact integral_volumeIoiPow (n - 1) fun t => ∫ ω, g (t • (ω : Rn n)) ∂sphereMeasure n

/-- The radial profile `t ↦ t^{n-1} ∫_{S^{n-1}} g(t ω) dσ` of an integrable function is
integrable on `(0, ∞)`. -/
theorem integrableOn_Ioi_sphere [NormedSpace ℝ E] [NeZero n] {g : Rn n → E}
    (hg : Integrable g) :
    IntegrableOn (fun t : ℝ => t ^ (n - 1) • ∫ ω, g (t • (ω : Rn n)) ∂sphereMeasure n) (Ioi 0) :=
  (integrable_volumeIoiPow_iff (n - 1)).1
    (integrable_iff_integrable_prod_polar.1 hg).integral_prod_right

/-! ### Total mass of the sphere -/

/-- `σ(S^{n-1}) = n |B_1|`, real version. -/
theorem sphereMeasure_real_univ (n : ℕ) : (sphereMeasure n).real univ = n * unitBallVolume n := by
  rw [sphereMeasure, Measure.toSphere_real_apply_univ, finrank_Rn]
  rfl

theorem unitBallVolume_pos (n : ℕ) : 0 < unitBallVolume n :=
  ENNReal.toReal_pos (measure_ball_pos volume (0 : Rn n) one_pos).ne' measure_ball_lt_top.ne

/-- `∫_{∂B_s(x)} c = n |B_1| s^{n-1} c`. -/
theorem sphereIntegral_const (c : ℝ) (x : Rn n) (s : ℝ) :
    sphereIntegral (fun _ => c) x s = n * unitBallVolume n * s ^ (n - 1) * c := by
  rw [sphereIntegral, integral_const, smul_eq_mul, sphereMeasure_real_univ]
  ring

/-! ### Ball and annulus formulas -/

theorem preimage_add_left_ball (x : Rn n) (r : ℝ) : (x + ·) ⁻¹' ball x r = ball 0 r := by
  ext y; simp [mem_ball, dist_eq_norm]

theorem norm_smul_sphere {t : ℝ} (ht : 0 ≤ t) (ω : sphere (0 : Rn n) 1) :
    ‖t • (ω : Rn n)‖ = t := by
  rw [norm_smul, norm_eq_of_mem_sphere ω, mul_one, Real.norm_of_nonneg ht]

theorem add_smul_mem_ball_iff {x : Rn n} {t r : ℝ} (ht : 0 ≤ t) (ω : sphere (0 : Rn n) 1) :
    x + t • (ω : Rn n) ∈ ball x r ↔ t < r := by
  rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul_sphere ht]

/-- Translating a set integral over a ball to the origin. -/
theorem setIntegral_ball_diff_ball_eq [NormedSpace ℝ E] (f : Rn n → E) (x : Rn n) (a b : ℝ) :
    ∫ y in ball x b \ ball x a, f y = ∫ y in ball 0 b \ ball 0 a, f (x + y) := by
  have h := (measurePreserving_add_left (volume : Measure (Rn n)) x).setIntegral_preimage_emb
    (measurableEmbedding_addLeft x) f (ball x b \ ball x a)
  rw [preimage_sdiff, preimage_add_left_ball, preimage_add_left_ball] at h
  exact h.symm

theorem integrableOn_ball_diff_ball_iff {f : Rn n → E} {x : Rn n} {a b : ℝ} :
    IntegrableOn f (ball x b \ ball x a) ↔
      IntegrableOn (fun y => f (x + y)) (ball 0 b \ ball 0 a) := by
  have h := (measurePreserving_add_left (volume : Measure (Rn n)) x).integrableOn_comp_preimage
    (measurableEmbedding_addLeft x) (f := f) (s := ball x b \ ball x a)
  rw [preimage_sdiff, preimage_add_left_ball, preimage_add_left_ball] at h
  exact h.symm

/-- **Annulus formula**: `∫_{B_b(x) ∖ B_a(x)} f = ∫_a^b ∫_{∂B_s(x)} f ds`. -/
theorem integral_ball_diff_ball [NeZero n] {f : Rn n → ℝ} {x : Rn n} {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hf : IntegrableOn f (ball x b)) :
    ∫ y in ball x b \ ball x a, f y = ∫ s in a..b, sphereIntegral f x s := by
  set S : Set (Rn n) := ball 0 b \ ball 0 a with hS
  have hSm : MeasurableSet S := measurableSet_ball.diff measurableSet_ball
  have hint : IntegrableOn (fun y => f (x + y)) S :=
    integrableOn_ball_diff_ball_iff.1 (hf.mono_set sdiff_subset)
  rw [setIntegral_ball_diff_ball_eq, ← integral_indicator hSm,
    integral_eq_integral_Ioi_sphere ((integrable_indicator_iff hSm).2 hint)]
  have key : ∀ t : ℝ, 0 < t → t ≠ a → t ≠ b → t ^ (n - 1) •
      ∫ ω, S.indicator (fun y => f (x + y)) (t • (ω : Rn n)) ∂sphereMeasure n =
      (Ioc a b).indicator (sphereIntegral f x) t := by
    intro t ht hta htb
    have hmem : ∀ ω : sphere (0 : Rn n) 1, t • (ω : Rn n) ∈ S ↔ t ∈ Ioc a b := by
      intro ω
      simp only [hS, Set.mem_sdiff, mem_ball_zero_iff, norm_smul_sphere ht.le, not_lt, mem_Ioc]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨lt_of_le_of_ne h2 (Ne.symm hta), h1.le⟩
      · rintro ⟨h1, h2⟩; exact ⟨lt_of_le_of_ne h2 htb, h1.le⟩
    by_cases htab : t ∈ Ioc a b
    · rw [indicator_of_mem htab, sphereIntegral, smul_eq_mul]
      congr 1
      refine integral_congr_ae (.of_forall fun ω => ?_)
      exact indicator_of_mem ((hmem ω).2 htab) _
    · rw [indicator_of_notMem htab]
      have : ∀ ω : sphere (0 : Rn n) 1,
          S.indicator (fun y => f (x + y)) (t • (ω : Rn n)) = 0 :=
        fun ω => indicator_of_notMem (fun h => htab ((hmem ω).1 h)) _
      simp [this]
  have hae : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), t ^ (n - 1) •
      ∫ ω, S.indicator (fun y => f (x + y)) (t • (ω : Rn n)) ∂sphereMeasure n =
      (Ioc a b).indicator (sphereIntegral f x) t := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (Real.volume_singleton (a := a)),
      measure_eq_zero_iff_ae_notMem.1 (Real.volume_singleton (a := b))] with t hta htb ht
    exact key t ht hta htb
  rw [integral_congr_ae hae, setIntegral_indicator measurableSet_Ioc,
    inter_eq_right.2 (show Ioc a b ⊆ Ioi 0 from fun t ht => lt_of_le_of_lt ha ht.1),
    intervalIntegral.integral_of_le hab]

/-- **Ball formula**: `∫_{B_r(x)} f = ∫_0^r ∫_{∂B_s(x)} f ds`. -/
theorem integral_ball_eq [NeZero n] {f : Rn n → ℝ} {x : Rn n} {r : ℝ} (hr : 0 ≤ r)
    (hf : IntegrableOn f (ball x r)) :
    ∫ y in ball x r, f y = ∫ s in (0 : ℝ)..r, sphereIntegral f x s := by
  rw [← integral_ball_diff_ball le_rfl hr hf, ball_zero, sdiff_empty]

/-- If `f` is integrable on `B_b(x)`, then `s ↦ ∫_{∂B_s(x)} f` is integrable on `(0, b)`. -/
theorem intervalIntegrable_sphereIntegral [NeZero n] {f : Rn n → ℝ} {x : Rn n} {b : ℝ}
    (hb : 0 ≤ b) (hf : IntegrableOn f (ball x b)) :
    IntervalIntegrable (sphereIntegral f x) volume 0 b := by
  have hint : IntegrableOn (fun y => f (x + y)) (ball 0 b) := by
    have := integrableOn_ball_diff_ball_iff (f := f) (x := x) (a := 0) (b := b)
    rw [ball_zero, ball_zero, sdiff_empty, sdiff_empty] at this
    exact this.1 hf
  have h :=
    (integrableOn_Ioi_sphere ((integrable_indicator_iff measurableSet_ball).2 hint)).mono_set
    (Ioo_subset_Ioi_self : Ioo (0 : ℝ) b ⊆ Ioi 0)
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hb]
  refine h.congr_fun (fun t ht => ?_) measurableSet_Ioo
  simp only [sphereIntegral, smul_eq_mul]
  congr 1
  refine integral_congr_ae (.of_forall fun ω => ?_)
  refine indicator_of_mem ?_ _
  rw [mem_ball_zero_iff, norm_smul_sphere ht.1.le]
  exact ht.2

/-! ### Null sets along rays -/

/-- If a property holds for Lebesgue-a.e. `y`, then for `σ`-a.e. direction `ω` it holds at
`x + t ω` for a.e. `t > 0`. -/
theorem ae_sphere_ae_of_ae [NeZero n] {p : Rn n → Prop} (h : ∀ᵐ y, p y) (x : Rn n) :
    ∀ᵐ (ω : sphere (0 : Rn n) 1) ∂sphereMeasure n, ∀ᵐ t : ℝ, 0 < t → p (x + t • (ω : Rn n)) := by
  have h1 : ∀ᵐ y, p (x + y) :=
    (measurePreserving_add_left (volume : Measure (Rn n)) x).quasiMeasurePreserving.ae h
  have h2 : ∀ᵐ y : ({0}ᶜ : Set (Rn n)) ∂Measure.comap Subtype.val volume, p (x + y) :=
    (ae_restrict_iff_subtype (p := fun y => p (x + y)) (measurableSet_singleton 0).compl).1
      (ae_restrict_of_ae h1)
  have h3 : ∀ᵐ q ∂(sphereMeasure n).prod (Measure.volumeIoiPow (n - 1)),
      p (x + (q.2 : ℝ) • (q.1 : Rn n)) := by
    rw [← (measurePreserving_polar n).map_eq,
      (homeomorphUnitSphereProd (Rn n)).measurableEmbedding.ae_map_iff]
    filter_upwards [h2] with y hy
    rwa [homeomorphUnitSphereProd_smul_eq]
  filter_upwards [Measure.ae_ae_of_ae_prod h3] with ω hω
  rw [Measure.volumeIoiPow, ae_withDensity_iff (by fun_prop)] at hω
  have h5 := (ae_restrict_iff_subtype (μ := volume)
    (p := fun t : ℝ => ENNReal.ofReal (t ^ (n - 1)) ≠ 0 → p (x + t • (ω : Rn n)))
    measurableSet_Ioi).2 hω
  rw [ae_restrict_iff' measurableSet_Ioi] at h5
  filter_upwards [h5] with t ht htpos
  exact ht htpos (ENNReal.ofReal_pos.2 (pow_pos htpos _)).ne'

/-- A Lebesgue-null set `Z` meets a.e. line `t ↦ t • y` through the origin in a null set. -/
theorem ae_ae_smul_notMem {Z : Set (Rn n)} (hZ : volume Z = 0) :
    ∀ᵐ y : Rn n, ∀ᵐ t : ℝ, t • y ∉ Z := by
  set Z' := toMeasurable volume Z
  have hZ'm : MeasurableSet Z' := measurableSet_toMeasurable _ _
  have hZ'0 : volume Z' = 0 := by rw [measure_toMeasurable]; exact hZ
  have hS : MeasurableSet {q : Rn n × ℝ | q.2 • q.1 ∈ Z'} :=
    hZ'm.preimage (continuous_snd.smul continuous_fst).measurable
  have h0 : (volume : Measure (Rn n)).prod (volume : Measure ℝ)
      {q : Rn n × ℝ | q.2 • q.1 ∈ Z'} = 0 := by
    rw [Measure.prod_apply_symm hS]
    have : ∀ᵐ t : ℝ, volume ((fun y : Rn n => (y, t)) ⁻¹' {q : Rn n × ℝ | q.2 • q.1 ∈ Z'}) = 0 := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 (Real.volume_singleton (a := 0))] with t ht
      have ht0 : t ≠ 0 := ht
      change volume ((fun y : Rn n => t • y) ⁻¹' Z') = 0
      rw [preimage_smul₀ ht0, Measure.addHaar_smul, hZ'0, mul_zero]
    rw [lintegral_congr_ae this, lintegral_zero]
  have h1 : ∀ᵐ q : Rn n × ℝ ∂(volume.prod volume), q.2 • q.1 ∉ Z' :=
    measure_eq_zero_iff_ae_notMem.1 h0
  filter_upwards [Measure.ae_ae_of_ae_prod h1] with y hy
  filter_upwards [hy] with t ht
  exact fun h => ht (subset_toMeasurable _ _ h)

/-- A Lebesgue-null set `Z` meets a.e. line `t ↦ y + t • v` in a null set. -/
theorem ae_ae_add_smul_notMem {Z : Set (Rn n)} (hZ : volume Z = 0) (v : Rn n) :
    ∀ᵐ y : Rn n, ∀ᵐ t : ℝ, y + t • v ∉ Z := by
  set Z' := toMeasurable volume Z
  have hZ'm : MeasurableSet Z' := measurableSet_toMeasurable _ _
  have hZ'0 : volume Z' = 0 := by rw [measure_toMeasurable]; exact hZ
  have hS : MeasurableSet {q : Rn n × ℝ | q.1 + q.2 • v ∈ Z'} :=
    hZ'm.preimage (continuous_fst.add (continuous_snd.smul continuous_const)).measurable
  have h0 : (volume : Measure (Rn n)).prod (volume : Measure ℝ)
      {q : Rn n × ℝ | q.1 + q.2 • v ∈ Z'} = 0 := by
    rw [Measure.prod_apply_symm hS]
    have : ∀ t : ℝ,
        volume ((fun y : Rn n => (y, t)) ⁻¹' {q : Rn n × ℝ | q.1 + q.2 • v ∈ Z'}) = 0 := by
      intro t
      change volume ((fun y : Rn n => y + t • v) ⁻¹' Z') = 0
      rw [measure_preimage_add_right, hZ'0]
    rw [lintegral_congr_ae (.of_forall this), lintegral_zero]
  have h1 : ∀ᵐ q : Rn n × ℝ ∂(volume.prod volume), q.1 + q.2 • v ∉ Z' :=
    measure_eq_zero_iff_ae_notMem.1 h0
  filter_upwards [Measure.ae_ae_of_ae_prod h1] with y hy
  filter_upwards [hy] with t ht
  exact fun h => ht (subset_toMeasurable _ _ h)

/-- **Radial derivatives of Lipschitz functions.** If `u` is Lipschitz on `B_R(x)`, then for
`σ`-a.e. `ω` and a.e. `t ∈ (0, R)`, `u` is differentiable at `x + t ω` and
`d/dt u(x + t ω) = ⟪∇u(x + t ω), ω⟫`. -/
theorem _root_.LipschitzOnWith.ae_sphere_ae_hasDerivAt [NeZero n] {u : Rn n → ℝ} {C : ℝ≥0}
    {x : Rn n} {R : ℝ} (hu : LipschitzOnWith C u (ball x R)) :
    ∀ᵐ (ω : sphere (0 : Rn n) 1) ∂sphereMeasure n, ∀ᵐ t, t ∈ Ioo 0 R →
      DifferentiableAt ℝ u (x + t • (ω : Rn n)) ∧
      HasDerivAt (fun τ : ℝ => u (x + τ • (ω : Rn n)))
        (⟪gradient u (x + t • (ω : Rn n)), (ω : Rn n)⟫) t := by
  have hdiff : ∀ᵐ y, y ∈ ball x R → DifferentiableAt ℝ u y := by
    filter_upwards [hu.ae_differentiableWithinAt_of_mem (μ := volume)] with y hy hyb
    exact (hy hyb).differentiableAt (isOpen_ball.mem_nhds hyb)
  filter_upwards [ae_sphere_ae_of_ae hdiff x] with ω hω
  filter_upwards [hω] with t ht htR
  have hd := ht htR.1 ((add_smul_mem_ball_iff htR.1.le ω).2 htR.2)
  refine ⟨hd, ?_⟩
  have hray : HasDerivAt (fun τ : ℝ => x + τ • (ω : Rn n)) (ω : Rn n) t := by
    simpa using ((hasDerivAt_id t).smul_const (ω : Rn n)).const_add x
  have := hd.hasFDerivAt.comp_hasDerivAt t hray
  convert this using 1
  · rfl
  · rw [inner_gradient_left]

end InnerVariational
