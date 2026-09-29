/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Frequency.Concrete
public import InnerVariational.Regular.Perimeter
public import InnerVariational.Singular.Tangent
import Mathlib.Data.Real.StarOrdered
import InnerVariational.NaberValtorta.MainFrequency
public import InnerVariational.Defs.HighestDensity
public import InnerVariational.Defs.VariationalSolution
import InnerVariational.Basic.Polar
public import GMTFoundations.Defs.GMT

/-!
# Blow-ups and density at singular points (Lemma 8.5)

Lemma 8.5 of D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and
compactness for non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025),
no. 3, DOI 10.1002/cpa.22226; arXiv:2306.10131 (numbering of arXiv v2). Let `(u, χ)` be a
variational solution on `Ω`. For `ℋ^{n-1}`-a.e. `x ∈ Σ^H`:

1. the renormalized functions `v_{x,r}(y) = u(x + r y) / (r √(H_x(u; r)))` converge to
   `α(n) |y · ν|` strongly in `W^{1,2}_loc(ℝⁿ)`, for a unit vector `ν`
   (`renormalized_tendsto_alpha_ae`);
2. `{u > 0}` has Lebesgue density `1` at `x` (`density_pos_eq_one_ae`).

## Encoding of (1)

For `R > 0` the change of variables `y ↦ x + r y` turns the `W^{1,2}(B_R)` distance between
`v_{x,r}` and `α(n)|y·ν|` into integrals of `u` over `B_{Rr}(x)`:
* `∫_{B_R} |v_{x,r} − α(n)|y·ν||²` equals
  `(r^{n+2} H_x(r))⁻¹ ∫_{B_{Rr}(x)} (u − √(H_x(r)) α(n) |(y−x)·ν|)²`;
* `∫_{B_R} |∇v_{x,r} − α(n)∇|y·ν||²` equals
  `(r^n H_x(r))⁻¹ ∫_{B_{Rr}(x)} |∇u − √(H_x(r)) α(n) ∇|(y−x)·ν||²`.
We state (1) in this form, as `Statements.main_theorem_iv` (Theorem 1.2 (iv) in corrected form)
and `approx1D_limit_tendsto_profile` do. Since `∫_{∂B_r(x)} u² = r^{n+1} H_x(r)`, the gradient
part with `R = 1` is exactly the corrected second display of Theorem 1.2 (iv).
`H_x(u; r) > 0` for small `r` on `Σ^H` (`IsVariationalSolution.heightH_pos`), so Lean's
`a / 0 = 0` plays no role.

## Proof of (2) from (1)

The paper derives (2) from (1) by an a.e.-subsequence and Fatou. We use a direct
Chebyshev bound instead. On `Z_r = B_r(x) ∩ {u = 0}` the integrand of the `L²` part is
`H_x(r) α(n)² |(y−x)·ν|²`, so `r^{-n-2} ∫_{Z_r} |(y−x)·ν|² → 0`. Split `Z_r` into the slab
`{|(y−x)·ν| < ε r}`, of volume `r^n |S_ε|` with `S_ε = {z ∈ B_1 : |z·ν| < ε}`, and its complement,
of volume `≤ (ε r)^{-2} ∫_{Z_r} |(y−x)·ν|²`. As `|S_ε| → 0` when `ε → 0` (the hyperplane `ν^⊥` is
Lebesgue-null), `|Z_r| / |B_r| → 0`.

## Proof of (1)

This follows the paper's proof of Lemma 8.5. Outside an `ℋ^{n-1}`-null set, `x ∈ Σ^H` satisfies
`N_x(u; 0+) = 1` (Theorem 7.2 (3), `NaberValtorta.hausdorffN_not_tendsto_frequencyN_eq_zero`) and
`Σ^H` is flat at `x` in some direction `ν` (`hausdorffN_not_isFlatAt_eq_zero`: localized
Theorem 7.2 (1)–(2) plus the existence of approximate tangent planes a.e. on rectifiable sets,
P. Mattila, *Geometry of Sets and Measures in Euclidean Spaces*, Cambridge Univ. Press, 1995,
Theorem 15.19). At such a point, `tendsto_profile_of_isFlatAt` (`Singular/FlatPoint.lean`)
proves the convergence: Lemma 4.3, Lemma 4.5 and the continuity of `y ↦ N_y`, the frequency
pinching estimates of §6, Theorem 5.3 in the form `approx1D_limit_tendsto_profile` at every
scale, and the assembly of annuli (`Singular/Annuli.lean`).
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

namespace Singular

variable {Ω : Set (Rn n)} {C : ℝ≥0} {u χ : Rn n → ℝ}

/-- **Lemma 8.5 (1)**. Let `(u, χ)` be a variational
solution on `Ω`. For `ℋ^{n-1}`-a.e. `x ∈ Σ^H` there is a unit vector `ν` such that, for every
`R > 0`, as `r → 0+`,
* `(r^{n+2} H_x(u; r))⁻¹ ∫_{B_{Rr}(x)} (u − √(H_x(u; r)) α(n) |(y−x)·ν|)² → 0`,
* `(r^n H_x(u; r))⁻¹ ∫_{B_{Rr}(x)} |∇u − √(H_x(u; r)) α(n) ∇|(y−x)·ν||² → 0`.

By the change of variables `y ↦ x + r y` (module docstring), this says that
`v_{x,r}(y) = u(x + r y) / (r √(H_x(u; r)))` converges to `α(n) |y·ν|` in `W^{1,2}(B_R)` for every
`R`, i.e. strongly in `W^{1,2}_loc(ℝⁿ)`. The paper writes `|y_n|` after choosing coordinates with
`ν = e_n`. -/
theorem renormalized_tendsto_alpha_ae [NeZero n] (hn : 2 ≤ n)
    (h : IsVariationalSolution Ω C u χ) :
    hausdorffN n (n - 1) {x | x ∈ sigmaH Ω u χ ∧ ¬ ∃ ν : Rn n, ‖ν‖ = 1 ∧ ∀ R : ℝ, 0 < R →
      Tendsto (fun r => (∫ y in ball x (R * r),
          (u y - √(heightH u x r) * alphaN n * absProfile ν x y) ^ 2) /
          (r ^ (n + 2) * heightH u x r)) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun r => (∫ y in ball x (R * r),
          ‖gradient u y - (√(heightH u x r) * alphaN n) • gradient (absProfile ν x) y‖ ^ 2) /
          (r ^ n * heightH u x r)) (𝓝[>] 0) (𝓝 0)} = 0 := by
  refine measure_mono_null ?_ (measure_union_null
    (NaberValtorta.hausdorffN_not_tendsto_frequencyN_eq_zero hn h)
    (hausdorffN_not_isFlatAt_eq_zero hn h))
  rintro x ⟨hxS, hx⟩
  by_cases hN : Tendsto (frequencyN u χ x) (𝓝[>] 0) (𝓝 1)
  · by_cases hF : ∃ ν : Rn n, ‖ν‖ = 1 ∧ IsFlatAt Ω u χ x ν
    · obtain ⟨ν, hν, hfl⟩ := hF
      exact absurd ⟨ν, hν, fun R hR => tendsto_profile_of_isFlatAt h hxS hN hn hν hfl R hR⟩ hx
    · exact Or.inr ⟨hxS, hF⟩
  · exact Or.inl ⟨hxS, hN⟩

/-! ### Density helpers -/

/-- Densities only see a neighbourhood of the point: `HasDensity (U ∩ E) x d ↔ HasDensity E x d`
for a neighbourhood `U` of `x`. -/
theorem hasDensity_inter_iff {U E : Set (Rn n)} {x : Rn n} (hU : U ∈ 𝓝 x) {d : ℝ} :
    HasDensity (U ∩ E) x d ↔ HasDensity E x d := by
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.1 hU
  refine tendsto_congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
  have : U ∩ E ∩ ball x r = E ∩ ball x r := by
    rw [inter_comm U E, inter_assoc,
      inter_eq_right.2 ((ball_subset_ball hr.2.le).trans hδU)]
  rw [this]

/-! ### Slabs -/

/-- The slab `S_ε = {z ∈ B_1 : |z·ν| < ε}`. -/
def slab (ν : Rn n) (ε : ℝ) : Set (Rn n) :=
  {z | z ∈ ball (0 : Rn n) 1 ∧ |⟪z, ν⟫| < ε}

theorem isOpen_slab (ν : Rn n) (ε : ℝ) : IsOpen (slab ν ε) :=
  isOpen_ball.inter (isOpen_lt (f := fun z : Rn n => |⟪z, ν⟫|) (g := fun _ => ε)
    (continuous_abs.comp (continuous_id.inner continuous_const)) continuous_const)

/-- `|S_ε| → 0` as `ε → 0+`: the slabs decrease to `B_1 ∩ ν^⊥`, a Lebesgue-null set. -/
theorem tendsto_volume_slab {ν : Rn n} (hν : ν ≠ 0) :
    Tendsto (fun ε => volume (slab ν ε)) (𝓝[>] 0) (𝓝 0) := by
  have h := tendsto_measure_biInter_gt (μ := volume) (s := slab ν) (a := (0 : ℝ))
    (fun r _ => (isOpen_slab ν r).measurableSet.nullMeasurableSet)
    (fun i j _ hij z hz => ⟨hz.1, hz.2.trans_le hij⟩)
    ⟨1, one_pos, (measure_ne_top_of_subset (fun z hz => hz.1) measure_ball_lt_top.ne)⟩
  have hne : (ℝ ∙ ν)ᗮ ≠ ⊤ := by
    intro htop
    have hmem : ν ∈ (ℝ ∙ ν)ᗮ := htop ▸ Submodule.mem_top
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_self_eq_norm_sq] at hmem
    exact hν (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hmem))
  have h0 : volume (⋂ r > (0 : ℝ), slab ν r) = 0 := by
    refine measure_mono_null (fun z hz => ?_) (Measure.addHaar_submodule volume _ hne)
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_comm]
    simp only [mem_iInter] at hz
    by_contra hne0
    exact lt_irrefl _ (hz _ (abs_pos.2 hne0)).2
  rw [h0] at h
  exact h

/-- `|{y ∈ B_r(x) : |(y−x)·ν| < ε r}| = r^n |S_ε|`. -/
theorem volume_slab_scaled (x ν : Rn n) {r : ℝ} (hr : 0 < r) (ε : ℝ) :
    volume {y | y ∈ ball x r ∧ |⟪y - x, ν⟫| < ε * r} =
      ENNReal.ofReal (r ^ n) * volume (slab ν ε) := by
  have hset : {y | y ∈ ball x r ∧ |⟪y - x, ν⟫| < ε * r} =
      (fun y => -x + y) ⁻¹' ((r⁻¹ • ·) ⁻¹' slab ν ε) := by
    ext y
    simp only [slab, mem_setOf_eq, mem_preimage, mem_ball, dist_eq_norm, sub_zero]
    rw [neg_add_eq_sub, norm_smul, real_inner_smul_left, abs_mul, Real.norm_eq_abs, abs_inv,
      abs_of_pos hr, inv_mul_lt_iff₀ hr, inv_mul_lt_iff₀ hr, mul_one, mul_comm r ε]
  rw [hset, measure_preimage_add, Measure.addHaar_preimage_smul volume (inv_ne_zero hr.ne'),
    finrank_euclideanSpace_fin, inv_pow, inv_inv, abs_of_pos (pow_pos hr n)]

/-- `α(n) > 0`: the integral of `y₁²` over the unit sphere is positive. -/
theorem alphaN_pos [NeZero n] : 0 < alphaN n := by
  have hS : 0 < sphereIntegral (fun y : Rn n => y 0 ^ 2) 0 1 := by
    have hc : Continuous fun y : Rn n => y 0 ^ 2 := by fun_prop
    haveI : (sphereMeasure n).IsOpenPosMeasure := by unfold sphereMeasure; infer_instance
    rw [sphereIntegral, one_pow, one_mul]
    set e : sphere (0 : Rn n) 1 := ⟨EuclideanSpace.single 0 1, by simp⟩
    refine integral_pos_of_integrable_nonneg_nonzero (x := e)
      (hc.comp (continuous_add_smul_sphere 0 1)) (hc.sphereIntegrable 0 1)
      (fun ω => sq_nonneg _) ?_
    simp [e]
  rw [alphaN]
  positivity

/-! ### Lemma 8.5 (2) from Lemma 8.5 (1) -/

/-- **(1) ⇒ (2) at a point** (proof of Lemma 8.5). Let `u` be continuous on an open set `Ω`, and
let `x ∈ Ω` with `H_x(u; r) > 0` whenever `B̄_r(x) ⊆ Ω` (as on `Σ^H`). If, for a unit vector `ν`,
`(r^{n+2} H_x(r))⁻¹ ∫_{B_r(x)} (u − √(H_x(r)) α(n) |(y−x)·ν|)² → 0`, then `{u > 0}` has density
`1` at `x`. Chebyshev's inequality on `B_r(x) \ {u > 0}` (where the integrand is
`≥ H_x(r) α(n)² |(y−x)·ν|²`) plus the slab bound replaces the paper's Fatou argument. -/
theorem hasDensity_pos_of_tendsto' [NeZero n] (hΩ : IsOpen Ω) (hu : ContinuousOn u Ω)
    {x : Rn n} (hxΩ : x ∈ Ω) (hHpos : ∀ r, 0 < r → closedBall x r ⊆ Ω → 0 < heightH u x r)
    {ν : Rn n} (hν : ‖ν‖ = 1)
    (hL : Tendsto (fun r => (∫ y in ball x r,
        (u y - √(heightH u x r) * alphaN n * absProfile ν x y) ^ 2) /
        (r ^ (n + 2) * heightH u x r)) (𝓝[>] 0) (𝓝 0)) :
    HasDensity {y | 0 < u y} x 1 := by
  obtain ⟨F, hFdef⟩ : ∃ F : Set (Rn n), F = Ω ∩ {y | 0 < u y} := ⟨_, rfl⟩
  have hFo : IsOpen F := hFdef ▸ hu.isOpen_inter_preimage hΩ isOpen_Ioi
  rw [← hasDensity_inter_iff (hΩ.mem_nhds hxΩ), ← hFdef]
  set α := alphaN n with hαdef
  have hα : 0 < α := alphaN_pos
  have hB1 := unitBallVolume_pos n
  have hν0 : ν ≠ 0 := fun h0 => by rw [h0, norm_zero] at hν; exact zero_ne_one hν
  set I : ℝ → ℝ := fun r => (∫ y in ball x r,
      (u y - √(heightH u x r) * α * absProfile ν x y) ^ 2) / (r ^ (n + 2) * heightH u x r)
    with hIdef
  set ρ : ℝ → ℝ := fun r => (volume (ball x r \ F)).toReal / (volume (ball x r)).toReal
    with hρdef
  obtain ⟨δ, hδ, hδΩ⟩ := Metric.isOpen_iff.1 hΩ x hxΩ
  -- the key bound `ρ(r) ≤ (|S_ε| + I(r)/(α² ε²)) / |B_1|`
  have hbound : ∀ r ∈ Ioo 0 δ, ∀ ε > 0,
      ρ r ≤ ((volume (slab ν ε)).toReal + I r / (α ^ 2 * ε ^ 2)) / unitBallVolume n := by
    intro r hr ε hε
    have hrΩ : closedBall x r ⊆ Ω := (closedBall_subset_ball hr.2).trans hδΩ
    have hH : 0 < heightH u x r := hHpos r hr.1 hrΩ
    set H := heightH u x r with hHdef
    set g : Rn n → ℝ := fun y => (u y - √H * α * absProfile ν x y) ^ 2 with hgdef
    have hgc : ContinuousOn g (closedBall x r) := by
      have hp : Continuous (absProfile ν x) := by unfold absProfile; fun_prop
      exact ((hu.mono hrΩ).sub (continuousOn_const.mul hp.continuousOn)).pow 2
    have hgi : IntegrableOn g (ball x r) :=
      (hgc.integrableOn_compact (isCompact_closedBall x r)).mono_set ball_subset_closedBall
    set t : ℝ := H * α ^ 2 * (ε * r) ^ 2 with htdef
    have ht : 0 < t := by rw [htdef]; have := hr.1; positivity
    have hcheb := mul_meas_ge_le_integral_of_nonneg (μ := volume.restrict (ball x r)) (f := g)
      (.of_forall fun y => sq_nonneg _) hgi t
    rw [measureReal_def, Measure.restrict_apply' measurableSet_ball] at hcheb
    -- `B_r(x) \ F` lies in the slab or in `{t ≤ g}`
    have hsub : ball x r \ F ⊆
        {y | y ∈ ball x r ∧ |⟪y - x, ν⟫| < ε * r} ∪ ({y | t ≤ g y} ∩ ball x r) := by
      rintro y ⟨hyB, hyF⟩
      have hyΩ : y ∈ Ω := hrΩ (ball_subset_closedBall hyB)
      have huy : u y ≤ 0 := not_lt.1 fun hp => hyF (hFdef ▸ ⟨hyΩ, hp⟩)
      by_cases hs : |⟪y - x, ν⟫| < ε * r
      · exact Or.inl ⟨hyB, hs⟩
      · refine Or.inr ⟨?_, hyB⟩
        rw [not_lt] at hs
        have hc0 : 0 ≤ √H * α * absProfile ν x y := by
          rw [absProfile_apply]; positivity
        have hsq : (ε * r) ^ 2 ≤ |⟪y - x, ν⟫| ^ 2 :=
          pow_le_pow_left₀ (by have := hr.1; positivity) hs 2
        change t ≤ (u y - √H * α * absProfile ν x y) ^ 2
        calc t = H * α ^ 2 * (ε * r) ^ 2 := rfl
          _ ≤ H * α ^ 2 * |⟪y - x, ν⟫| ^ 2 := mul_le_mul_of_nonneg_left hsq (by positivity)
          _ = (√H * α * absProfile ν x y) ^ 2 := by
            rw [absProfile_apply, mul_pow, mul_pow, Real.sq_sqrt hH.le]
          _ ≤ (u y - √H * α * absProfile ν x y) ^ 2 := by
            nlinarith [mul_nonneg (neg_nonneg.2 huy) hc0, sq_nonneg (u y)]
    have hne1 : volume {y | y ∈ ball x r ∧ |⟪y - x, ν⟫| < ε * r} ≠ ⊤ :=
      measure_ne_top_of_subset (fun y hy => hy.1) measure_ball_lt_top.ne
    have hne2 : volume ({y | t ≤ g y} ∩ ball x r) ≠ ⊤ :=
      measure_ne_top_of_subset inter_subset_right measure_ball_lt_top.ne
    have hV : (volume (ball x r \ F)).toReal ≤
        r ^ n * (volume (slab ν ε)).toReal + (volume ({y | t ≤ g y} ∩ ball x r)).toReal := by
      have h1 : volume (ball x r \ F) ≤ volume {y | y ∈ ball x r ∧ |⟪y - x, ν⟫| < ε * r} +
          volume ({y | t ≤ g y} ∩ ball x r) := (measure_mono hsub).trans (measure_union_le _ _)
      have h2 := (ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hne1, hne2⟩) h1).trans_eq
        (ENNReal.toReal_add hne1 hne2)
      rwa [volume_slab_scaled x ν hr.1 ε, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (pow_nonneg hr.1.le n)] at h2
    have hW : (volume ({y | t ≤ g y} ∩ ball x r)).toReal ≤ r ^ n * (I r / (α ^ 2 * ε ^ 2)) := by
      have hIr : I r = (∫ y in ball x r, g y) / (r ^ (n + 2) * H) := rfl
      have hr0 : r ≠ 0 := hr.1.ne'
      have hH0 : H ≠ 0 := hH.ne'
      have hα0 : α ≠ 0 := hα.ne'
      have hε0 : ε ≠ 0 := hε.ne'
      have hGt : (∫ y in ball x r, g y) / t = r ^ n * (I r / (α ^ 2 * ε ^ 2)) := by
        rw [hIr, htdef]
        field_simp
        ring
      rw [← hGt, le_div_iff₀ ht]
      linarith
    have hBr := volume_ball_toReal x hr.1
    simp only [hρdef]
    rw [hBr, div_le_div_iff₀ (by have := hr.1; positivity) hB1]
    calc (volume (ball x r \ F)).toReal * unitBallVolume n
        ≤ (r ^ n * (volume (slab ν ε)).toReal + r ^ n * (I r / (α ^ 2 * ε ^ 2))) *
            unitBallVolume n := by gcongr; linarith
      _ = ((volume (slab ν ε)).toReal + I r / (α ^ 2 * ε ^ 2)) *
            (r ^ n * unitBallVolume n) := by ring
  -- `ρ → 0`
  have hρ : Tendsto ρ (𝓝[>] 0) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro η hη
    have hs := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (tendsto_volume_slab hν0)
    rw [ENNReal.toReal_zero] at hs
    obtain ⟨ε, hεs, hε⟩ := ((hs.eventually (gt_mem_nhds
      (by positivity : 0 < η * unitBallVolume n / 2))).and eventually_mem_nhdsWithin).exists
    have hε' : (0 : ℝ) < ε := hε
    have hL' : Tendsto I (𝓝[>] 0) (𝓝 0) := hL
    filter_upwards [Ioo_mem_nhdsGT hδ, hL'.eventually (gt_mem_nhds
      (by positivity : 0 < η * unitBallVolume n / 2 * (α ^ 2 * ε ^ 2)))] with r hr hIr
    have hρ0 : 0 ≤ ρ r := div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hρ0]
    have hI' : I r / (α ^ 2 * ε ^ 2) < η * unitBallVolume n / 2 :=
      (div_lt_iff₀ (by positivity)).2 hIr
    have hεs' : (volume (slab ν ε)).toReal < η * unitBallVolume n / 2 := hεs
    refine (hbound r hr ε hε').trans_lt ((div_lt_iff₀ hB1).2 ?_)
    linarith
  -- conclusion: the density of `F` is `1 - ρ`
  have h1 : Tendsto (fun r => 1 - ρ r) (𝓝[>] 0) (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hρ
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  have hB : 0 < (volume (ball x r)).toReal :=
    ENNReal.toReal_pos (measure_ball_pos volume x hr).ne' measure_ball_lt_top.ne
  have hsplit : (volume (ball x r ∩ F)).toReal + (volume (ball x r \ F)).toReal =
      (volume (ball x r)).toReal := by
    rw [← ENNReal.toReal_add (measure_ne_top_of_subset inter_subset_left measure_ball_lt_top.ne)
      (measure_ne_top_of_subset diff_subset measure_ball_lt_top.ne),
      measure_inter_add_diff _ hFo.measurableSet]
  simp only [hρdef]
  rw [inter_comm F, eq_div_iff hB.ne', sub_mul, div_mul_cancel₀ _ hB.ne', one_mul]
  linarith

/-- **(1) ⇒ (2) at a point** (proof of Lemma 8.5), for a variational solution: see
`hasDensity_pos_of_tendsto'`. -/
theorem hasDensity_pos_of_tendsto [NeZero n] (h : IsVariationalSolution Ω C u χ) {x : Rn n}
    (hx : x ∈ sigmaH Ω u χ) {ν : Rn n} (hν : ‖ν‖ = 1)
    (hL : Tendsto (fun r => (∫ y in ball x r,
        (u y - √(heightH u x r) * alphaN n * absProfile ν x y) ^ 2) /
        (r ^ (n + 2) * heightH u x r)) (𝓝[>] 0) (𝓝 0)) :
    HasDensity {y | 0 < u y} x 1 :=
  hasDensity_pos_of_tendsto' h.isOpen h.continuousOn hx.1
    (fun _ hr hrΩ => h.heightH_pos hx.2.1 hr hrΩ) hν hL

/-- **Lemma 8.5 (2)**. Let `(u, χ)` be a variational
solution on `Ω`. At `ℋ^{n-1}`-a.e. `x ∈ Σ^H` the Lebesgue density of `{u > 0}` exists and
equals `1`. Proved from Lemma 8.5 (1) (`renormalized_tendsto_alpha_ae`, the `L²` part with
`R = 1`) by `hasDensity_pos_of_tendsto`. -/
theorem density_pos_eq_one_ae [NeZero n] (hn : 2 ≤ n) (h : IsVariationalSolution Ω C u χ) :
    hausdorffN n (n - 1) {x | x ∈ sigmaH Ω u χ ∧ ¬ HasDensity {y | 0 < u y} x 1} = 0 := by
  refine measure_mono_null ?_ (renormalized_tendsto_alpha_ae hn h)
  rintro x ⟨hxS, hxd⟩
  refine ⟨hxS, fun ⟨ν, hν, hR⟩ => hxd ?_⟩
  exact hasDensity_pos_of_tendsto h hxS hν (by simpa only [one_mul] using (hR 1 one_pos).1)

end Singular

end InnerVariational
