/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Regular.ChiInterior
public import InnerVariational.Registry.BV
public import InnerVariational.Registry.Harmonic
public import InnerVariational.Registry.GMT
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Real.StarOrdered
import InnerVariational.Regular.ZeroGradient
import InnerVariational.Monotonicity.HighestDensity
import InnerVariational.Monotonicity.Density
public import InnerVariational.Monotonicity.Limits
import InnerVariational.Kernel.Rescale
import InnerVariational.Monotonicity.Blowup
import InnerVariational.Kernel.BV
import InnerVariational.Kernel.RellichPohozaev
import InnerVariational.Kernel.Subharmonic
import InnerVariational.Basic.SphereIntegral
import InnerVariational.Basic.Polar
public import GMTFoundations.Defs.GMT

/-!
# The density dichotomy at zeros of `u` (Lemma 8.1)

Lemma 8.1 of D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and
compactness for non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025),
no. 3, DOI 10.1002/cpa.22226; arXiv:2306.10131 (numbering of arXiv v2). Let `(u, χ)` be a
variational solution on `Ω`, `2 ≤ n`, and `x ∈ Ω` with `u(x) = 0`. Then

* `M_x(u; 0+) ∈ {0} ∪ [|B_1|/2, |B_1|]` (`Mzero_eq_zero_or_half_le`);
* `M_x(u; 0+) = 0` only if `x ∈ {u = 0}°` (`mem_interior_of_Mzero_eq_zero`);
* if `x ∈ ∂{u > 0}` and the blow-ups `u(x + r ·)/r` tend to `0`, then `M_x(u; 0+) = |B_1|`
  (`Mzero_eq_of_tendsto_rescale_zero`; the last line of the paper's proof reads `1`, the intended
  value being `|B_1|`).

Consequently `|B_1|/2 ≤ M_x(u; 0+) ≤ |B_1|` on `Ω ∩ ∂{u > 0}` (`half_le_Mzero_of_mem_frontier`).

## Proof

Take a blow-up `u_{x,r_k} → u₀` (`exists_tendsto_rescale`, from `exists_blowup_subseq`).
It is one-homogeneous, `C_V`-Lipschitz, and harmonic on `{u₀ > 0}` (proof of Proposition 3.5).

* If `u₀ ≢ 0`, Sperner's inequality (E. Sperner, Jr., *Zur Symmetrisierung von Funktionen auf
  Sphären*, Math. Z. 134 (1973), 317–327; `Registry.sperner_half_volume`, proved in the
  `Sperner` library) gives `|{u₀ > 0} ∩ B_1| ≥ |B_1|/2`, and `χ ≥ χ_{u>0}` gives
  `|{u₀ > 0} ∩ B_1| ≤ lim ∫_{B_1} χ_{x,r_k} = M_x(0+)` (`measureReal_pos_inter_ball_le`; the
  second paragraph of the proof of Lemma 8.1).
* If `u₀ ≡ 0`, Lemma 3.3 bounds the perimeter of `{χ_{x,r_k} = 1}` in `B_{3/2}`, so by BV
  compactness (L. C. Evans and R. F. Gariepy, *Measure Theory and Fine Properties of Functions*,
  rev. ed., CRC Press, 2015, Theorem 5.5; `Registry/BV.lean`) a subsequence `χ_{x,r_k} → χ₀`
  a.e. The inner variation passes to the limit:
  `∫ χ₀ div ξ = −lim ∫ (|∇u_k|² div ξ − 2∇u_k·Dξ∇u_k) = 0`, because `∇u_k → ∇u₀ = 0` in
  `L²_loc` (proof of Proposition 3.5). So `χ₀` is a constant `c ∈ {0, 1}` on `B_1`, and
  `M_x(0+) = lim ∫_{B_1} χ_{x,r_k} = c |B_1| ∈ {0, |B_1|}`
  (`eq_zero_or_eq_of_tendsto_rescale_zero`; the last paragraph of the proof of Lemma 8.1).

The openness argument (third paragraph of the proof): `M` is upper semicontinuous
(Proposition 3.5), so `{M_y(0+) < |B_1|/4}` is a neighbourhood `B_δ(x)` of a point with
`M_x(0+) = 0`. By the dichotomy, every `y ∈ B_δ(x)` has `u(y) > 0` (density of `{χ = 1}` is `1`)
or `M_y(0+) = 0` (density `0`). So the essential boundary of `{χ = 1}` misses `B_δ(x)`, and
Federer's theorem (H. Federer, *Geometric Measure Theory*, Springer, 1969, 4.5.11 and 4.5.6;
`Registry.ae_trivial_of_essentialBoundary_inter_ball`, proved in gmt-foundations,
https://github.com/willmfeldman/gmt-foundations, v0.1.0) makes `{χ = 1}` null or full there.
Full contradicts density `0` at `x`; null forces `{u > 0} ∩ B_δ(x) = ∅`.

## Ordering of the paper's argument

The paper's second paragraph gives `M_x(0+) ≥ |B_1|/2` whenever some blow-up is nonzero. The case
where *every* blow-up vanishes, which the openness argument needs at every point of `B_δ(x)`, is
proved at the end of the paper's argument (the limit of `χ(x + r ·)` is constant, using the
`L¹_loc` compactness of `χ(x + r_k ·)` from Lemma 3.3 and BV compactness). Here it is proved first
(`eq_zero_or_eq_of_tendsto_rescale_zero`), and then the dichotomy.
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

namespace Regular

/-- `∫_{B_1} χ_{x,r_k} → m` when `r^{-n} ∫_{B_r(x)} χ → m` and `r_k → 0+`. -/
theorem tendsto_setIntegral_chiRescale {χ : Rn n → ℝ} {x : Rn n} {m : ℝ}
    (hd : Tendsto (fun r => (r ^ n)⁻¹ * ∫ y in ball x r, χ y) (𝓝[>] 0) (𝓝 m)) {r : ℕ → ℝ}
    (hr : ∀ k, 0 < r k) (hr0 : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun k => ∫ y in ball (0 : Rn n) 1, chiRescale χ x (r k) y) atTop (𝓝 m) := by
  have h1 : Tendsto r atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.2 ⟨hr0, .of_forall hr⟩
  refine (hd.comp h1).congr fun k => ?_
  rw [Function.comp_apply, setIntegral_chiRescale χ x (hr k) 1, mul_one]

end Regular

namespace IsVariationalSolution

variable {Ω : Set (Rn n)} {C : ℝ≥0} {u χ : Rn n → ℝ} {x : Rn n}

/-! ### Densities of `{χ = 1}` -/

/-- The Lebesgue density of `Ω ∩ {χ = 1}` at `x` is `d / |B_1|` when `r^{-n} ∫_{B_r(x)} χ → d`. -/
theorem hasDensity_of_tendsto (h : IsVariationalSolution Ω C u χ) {δ : ℝ} (hδ : 0 < δ)
    (hδΩ : ball x δ ⊆ Ω) {d : ℝ}
    (hd : Tendsto (fun r => (r ^ n)⁻¹ * ∫ y in ball x r, χ y) (𝓝[>] 0) (𝓝 d)) :
    HasDensity (Ω ∩ {y | χ y = 1}) x (d / unitBallVolume n) := by
  unfold HasDensity
  refine (hd.div_const (unitBallVolume n)).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
  have hball : ball x r ⊆ Ω := (ball_subset_ball hr.2.le).trans hδΩ
  have hE : Ω ∩ {y | χ y = 1} ∩ ball x r = {y | χ y = 1} ∩ ball x r := by
    ext y
    exact ⟨fun hy => ⟨hy.1.2, hy.2⟩, fun hy => ⟨⟨hball hy.2, hy.1⟩, hy.2⟩⟩
  have hrn : r ^ n ≠ 0 := pow_ne_zero n hr.1.ne'
  have hB : unitBallVolume n ≠ 0 := (unitBallVolume_pos n).ne'
  rw [hE, volume_ball_toReal x hr.1, ← measureReal_def, ← h.setIntegral_chi_eq_measureReal hball]
  field_simp

/-- Near a point with `u > 0`, `{χ = 1}` has density `1`. -/
theorem hasDensity_one_of_pos (h : IsVariationalSolution Ω C u χ) (hx : x ∈ Ω)
    (hpos : 0 < u x) : HasDensity (Ω ∩ {y | χ y = 1}) x 1 := by
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.1 h.isOpen_pos x ⟨hx, hpos⟩
  have hc : ∀ᵐ z ∂(volume.restrict (ball x ε)), χ z = 1 := by
    rw [ae_restrict_iff' measurableSet_ball]
    filter_upwards [h.ae_chi_eq_one] with z hz hzb
    exact hz (hεsub hzb).1 (hεsub hzb).2
  have := h.hasDensity_of_tendsto hε (hεsub.trans inter_subset_left)
    (Regular.tendsto_density_of_ae_eq_const hε hc)
  rwa [one_mul, div_self (unitBallVolume_pos n).ne'] at this

/-! ### Blow-ups at a zero of `u` -/

/-- Every sequence `r_k → 0+` has a subsequence along which `u_{x,r_k}` converges locally
uniformly (Arzelà–Ascoli, as in the proof of Proposition 3.5), provided `u(x) = 0`. -/
theorem exists_tendsto_rescale (h : IsVariationalSolution Ω C u χ) (hx : x ∈ Ω) (hux : u x = 0)
    {r : ℕ → ℝ} (hr : ∀ k, 0 < r k) (hr0 : Tendsto r atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ u₀ : Rn n → ℝ,
      TendstoLocallyUniformly (fun k => oneHomRescale u x (r (φ k))) u₀ atTop := by
  obtain ⟨R, hR0, hR⟩ := h.exists_ball_subset hx
  have hρ : Tendsto (fun k => R / r k) atTop atTop := by
    have h1 : Tendsto r atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.2 ⟨hr0, .of_forall hr⟩
    simpa [div_eq_mul_inv] using (tendsto_inv_nhdsGT_zero.comp h1).const_mul_atTop hR0
  have hLip : ∀ k, LipschitzOnWith C (oneHomRescale u x (r k)) (ball 0 (R / r k)) := fun k =>
    (h.rescale x (hr k)).lipschitzOnWith 0 _ (ball_div_subset_preimage (hr k) hR)
  have hM0 : ∀ k, |oneHomRescale u x (r k) 0| ≤ 0 := fun k => by simp [hux]
  obtain ⟨φ, hφ, u₀, -, hconv⟩ := exists_blowup_subseq hρ (fun k => div_pos hR0 (hr k)) hLip hM0
  exact ⟨φ, hφ, u₀, hconv⟩

section Blowup

variable [NeZero n] (h : IsVariationalSolution Ω C u χ) (hx : x ∈ Ω) {m : ℝ}
  (hm : Tendsto (monotonicityM u χ x) (𝓝[>] 0) (𝓝 m))
  (hd : Tendsto (fun r => (r ^ n)⁻¹ * ∫ y in ball x r, χ y) (𝓝[>] 0) (𝓝 m))
  {r : ℕ → ℝ} (hr : ∀ k, 0 < r k) (hr0 : Tendsto r atTop (𝓝 0))
include h hx hm hd hr hr0

/-- **Lower semicontinuity of the positivity set** (proof of Lemma 8.1): for a blow-up `u₀`,
`|{u₀ > 0} ∩ B_1| ≤ lim ∫_{B_1} χ_{x,r_k} = M_x(u; 0+)`, since `χ ≥ χ_{u>0}` and
`χ_{u₀>0} ≤ liminf χ_{u_{x,r_k}>0}`. -/
theorem measureReal_pos_inter_ball_le {u₀ : Rn n → ℝ}
    (hconv : TendstoLocallyUniformly (fun k => oneHomRescale u x (r k)) u₀ atTop) :
    volume.real ({y | 0 < u₀ y} ∩ ball (0 : Rn n) 1) ≤ m := by
  obtain ⟨R, hR0, hR⟩ := h.exists_ball_subset hx
  obtain ⟨k₀, hw, hconv', -⟩ := h.blowup_window hR0 hR hm hr hr0 hconv two_pos
  set w : ℕ → Rn n → ℝ := fun j => oneHomRescale u x (r (j + k₀)) with hwdef
  set χw : ℕ → Rn n → ℝ := fun j => chiRescale χ x (r (j + k₀)) with hχwdef
  set U₀ : Set (Rn n) := {y | 0 < u₀ y} ∩ ball (0 : Rn n) 1 with hU₀def
  have hu₀c : Continuous u₀ := (blowup_lipschitzWith h hx hr hr0 hconv).continuous
  have hU₀ : MeasurableSet U₀ :=
    (isOpen_lt continuous_const hu₀c).measurableSet.inter measurableSet_ball
  have hU₀B : U₀ ⊆ ball 0 1 := inter_subset_right
  have hB12 : ball (0 : Rn n) 1 ⊆ ball 0 2 := ball_subset_ball one_le_two
  have hU₀f : volume U₀ ≠ ⊤ := ((measure_mono hU₀B).trans_lt measure_ball_lt_top).ne
  set S : ℕ → Set (Rn n) := fun j => ball 0 2 ∩ w j ⁻¹' Ioi 0 with hSdef
  have hS : ∀ j, MeasurableSet (S j) := fun j =>
    ((hw j).continuousOn.isOpen_inter_preimage isOpen_ball isOpen_Ioi).measurableSet
  -- (a) `∫_{U₀} 1_{S_j} ≤ ∫_{B_1} χ_{x,r_j}`
  have ha : ∀ j, ∫ y in U₀, (S j).indicator 1 y ≤ ∫ y in ball (0 : Rn n) 1, χw j y := by
    intro j
    have hχint : IntegrableOn (χw j) (ball 0 1) :=
      IntegrableOn.of_bound measure_ball_lt_top
        ((hw j).aestronglyMeasurable_chi measurableSet_ball hB12) 1
        ((ae_restrict_iff' measurableSet_ball).2 (.of_forall fun y hy => by
          rw [Real.norm_eq_abs]; exact (hw j).abs_chi_le_one (hB12 hy)))
    have hχnn : 0 ≤ᵐ[volume.restrict (ball 0 1)] χw j :=
      (ae_restrict_iff' measurableSet_ball).2 (.of_forall fun y hy => (hw j).chi_nonneg (hB12 hy))
    have hSint : IntegrableOn ((S j).indicator (1 : Rn n → ℝ)) U₀ :=
      IntegrableOn.of_bound hU₀f.lt_top (measurable_one.indicator (hS j)).aestronglyMeasurable 1
        (.of_forall fun y => by
          by_cases hy : y ∈ S j <;> simp [hy])
    calc ∫ y in U₀, (S j).indicator 1 y ≤ ∫ y in U₀, χw j y := by
          refine setIntegral_mono_ae_restrict hSint (hχint.mono_set hU₀B) ?_
          filter_upwards [ae_restrict_of_ae_restrict_of_subset (hU₀B.trans hB12)
            (hw j).posIndicator_le_chi, ae_restrict_mem hU₀] with y hy hyU
          have hy2 := hB12 (hU₀B hyU)
          calc (S j).indicator 1 y = posIndicator (w j) y := by
                by_cases hp : 0 < w j y
                · simp only [indicator_of_mem (show y ∈ S j from ⟨hy2, hp⟩),
                    posIndicator_of_pos hp, Pi.one_apply]
                · rw [indicator_of_notMem fun h' => hp h'.2, posIndicator_of_nonpos (not_lt.1 hp)]
            _ ≤ χw j y := hy
      _ ≤ ∫ y in ball (0 : Rn n) 1, χw j y :=
          setIntegral_mono_set hχint hχnn (.of_forall hU₀B)
  -- (b) `∫_{U₀} 1_{S_j} → |U₀|`
  have hb : Tendsto (fun j => ∫ y in U₀, (S j).indicator (1 : Rn n → ℝ) y) atTop
      (𝓝 (volume.real U₀)) := by
    have e : ∫ _ in U₀, (1 : ℝ) = volume.real U₀ := by
      rw [setIntegral_const, smul_eq_mul, mul_one]
    rw [← e]
    refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
      (fun j => (measurable_one.indicator (hS j)).aestronglyMeasurable)
      (integrableOn_const hU₀f) (fun j => .of_forall fun y => ?_) ?_
    · by_cases hy : y ∈ S j <;> simp [hy]
    · filter_upwards [ae_restrict_mem hU₀] with y hy
      have hy2 := hB12 (hU₀B hy)
      have hev : ∀ᶠ j in atTop, 0 < w j y := (hconv'.tendsto_at hy2).eventually (lt_mem_nhds hy.1)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev] with j hj
      simp only [indicator_of_mem (show y ∈ S j from ⟨hy2, hj⟩), Pi.one_apply]
  -- (c) `∫_{B_1} χ_{x,r_j} → m`
  have hc : Tendsto (fun j => ∫ y in ball (0 : Rn n) 1, χw j y) atTop (𝓝 m) :=
    (tendsto_add_atTop_iff_nat k₀).2 (Regular.tendsto_setIntegral_chiRescale hd hr hr0)
  exact le_of_tendsto_of_tendsto' hb hc ha

/-- **Sperner step** (proof of Lemma 8.1): if a blow-up `u₀` is not identically zero, then
`M_x(u; 0+) ≥ |B_1|/2`. Uses Sperner's inequality (`Registry.sperner_half_volume`). -/
theorem half_le_of_tendsto_rescale (hn : 2 ≤ n) {u₀ : Rn n → ℝ}
    (hconv : TendstoLocallyUniformly (fun k => oneHomRescale u x (r k)) u₀ atTop) {y₀ : Rn n}
    (hy₀ : 0 < u₀ y₀) : unitBallVolume n / 2 ≤ m := by
  have hH := blowup_isLipHarmonicPos h hx hr hr0 hconv
  have hR07 := Registry.sperner_half_volume hn ⟨C, blowup_lipschitzWith h hx hr hr0 hconv⟩
    (fun y => hH.nonneg y trivial) (fun y t ht => blowup_homogeneous h hx hr hr0 hconv t ht y) hy₀
    (fun y hy => hH.harmonicAt y trivial
      (connectedComponentIn_subset _ _ hy : y ∈ {y | 0 < u₀ y}))
  refine hR07.1.trans ((ENNReal.toReal_mono ?_ (measure_mono
    (inter_subset_inter_left _ (connectedComponentIn_subset _ _)))).trans
    (measureReal_pos_inter_ball_le h hx hm hd hr hr0 hconv))
  exact ((measure_mono inter_subset_right).trans_lt measure_ball_lt_top).ne

/-- **Zero blow-ups** (last paragraph of the proof of Lemma 8.1, completed; see the module
docstring). If `u_{x,r_k} → 0` locally uniformly along some `r_k → 0+`, then
`M_x(u; 0+) ∈ {0, |B_1|}`. Uses Lemma 3.3, BV compactness and the strong `L²_loc` convergence of
gradients (proof of Proposition 3.5). -/
theorem eq_zero_or_eq_of_tendsto_rescale_zero
    (hconv : TendstoLocallyUniformly (fun k => oneHomRescale u x (r k)) (fun _ => 0) atTop) :
    m = 0 ∨ m = unitBallVolume n := by
  obtain ⟨R, hR0, hR⟩ := h.exists_ball_subset hx
  obtain ⟨k₀, hw, hconv', -⟩ := h.blowup_window hR0 hR hm hr hr0 hconv (ρ := 4) (by norm_num)
  set w : ℕ → Rn n → ℝ := fun j => oneHomRescale u x (r (j + k₀)) with hwdef
  set χw : ℕ → Rn n → ℝ := fun j => chiRescale χ x (r (j + k₀)) with hχwdef
  set V : Set (Rn n) := ball 0 (3 * 1 / 2) with hVdef
  have hV4 : V ⊆ ball 0 4 := ball_subset_ball (by norm_num)
  have hB1V : ball (0 : Rn n) 1 ⊆ V := ball_subset_ball (by norm_num)
  set f : ℕ → Rn n → ℝ := fun j => (ball (0 : Rn n) 4).indicator (χw j) with hfdef
  have hfm : ∀ j, Measurable (f j) := fun j => (hw j).measurable_chi
  have hf01 : ∀ j, ∀ y ∈ ball (0 : Rn n) 4, f j y = 0 ∨ f j y = 1 := fun j y hy => by
    simp only [hfdef, indicator_of_mem hy]
    exact (hw j).chi_mem y hy
  have hfb : ∀ j, ∀ y ∈ V, |f j y| ≤ 1 := fun j y hy => by
    rcases hf01 j y (hV4 hy) with h0 | h0 <;> simp [h0]
  have hfχ : ∀ j (ξ : Rn n → Rn n), tsupport ξ ⊆ ball (0 : Rn n) 4 →
      ∫ y, f j y * divergence ξ y = ∫ y, χw j y * divergence ξ y := by
    intro j ξ hξ
    congr 1
    funext y
    by_cases hy : y ∈ ball (0 : Rn n) 4
    · simp only [hfdef, indicator_of_mem hy]
    · simp only [hfdef, indicator_of_notMem hy,
        divergence_eq_zero_of_notMem_tsupport fun h' => hy (hξ h'), mul_zero]
  -- Lemma 3.3 on `B_{3/2}` for the rescaled solutions
  have hcl : closedBall (0 : Rn n) (2 * 1) ⊆ ball 0 4 := closedBall_subset_ball (by norm_num)
  have hTV : ∀ K, IsCompact K → K ⊆ V → ∃ W, IsOpen W ∧ K ⊆ W ∧ W ⊆ V ∧ ∃ P : ℝ, ∀ j,
      ∀ ψ : Rn n → Rn n, ContDiff ℝ 1 ψ → HasCompactSupport ψ → tsupport ψ ⊆ W →
        (∀ y, ‖ψ y‖ ≤ 1) → ∫ y, f j y * divergence ψ y ≤ P := by
    intro K _ hKV
    refine ⟨V, isOpen_ball, hKV, subset_rfl,
      2 ^ (n + 1) * volume.real (ball (0 : Rn n) 1) * C ^ 2 * 1 * 1 ^ (n - 1),
      fun j ψ hψ hψc hψV hψ1 => ?_⟩
    have hψL : IsLipTestField (ball (0 : Rn n) (3 * 1 / 2)) ψ :=
      ⟨ContDiff.lipschitzWith_of_hasCompactSupport hψc hψ one_ne_zero, hψc, hψV⟩
    rw [hfχ j ψ (hψV.trans hV4)]
    exact (le_abs_self _).trans ((hw j).chi_divergence_bound one_pos hcl hψL hψ1)
  obtain ⟨φ, hφ, f₀, hf₀m, -, hf₀ae⟩ :=
    Registry.exists_subseq_tendsto_of_integral_mul_divergence_le isOpen_ball f hfm hfb hTV
  -- `f₀ ∈ {0, 1}` a.e. on `V`
  have h01 : ∀ᵐ y ∂(volume.restrict V), f₀ y = 0 ∨ f₀ y = 1 := by
    filter_upwards [hf₀ae, ae_restrict_mem measurableSet_ball] with y hy hyV
    have hcl01 : IsClosed ({0, 1} : Set ℝ) := (Set.toFinite _).isClosed
    exact hcl01.mem_of_tendsto hy (.of_forall fun j => hf01 (φ j) y (hV4 hyV))
  -- the limit identity `∫ f₀ div ξ = 0` on `B_1`
  have hlimid : ∀ ξ, IsSmoothTestField (ball (0 : Rn n) 1) ξ →
      ∫ y, f₀ y * divergence ξ y = 0 := by
    intro ξ hξ
    have hξL := hξ.isLipTestField
    obtain ⟨⟨D, hD⟩, hξc, hξB⟩ := hξL
    have hξ4 : IsLipTestField (ball (0 : Rn n) 4) ξ := hξ.isLipTestField.mono (hB1V.trans hV4)
    have hK4 : tsupport ξ ⊆ ball (0 : Rn n) 4 := hξB.trans (hB1V.trans hV4)
    have h1 : Tendsto (fun j => ∫ y, f (φ j) y * divergence ξ y) atTop
        (𝓝 (∫ y, f₀ y * divergence ξ y)) := by
      refine tendsto_integral_of_dominated_convergence
        (fun y => (tsupport ξ).indicator (fun _ => (n : ℝ) * D) y)
        (fun j => ((hfm _).mul (Kernel.measurable_divergence ξ)).aestronglyMeasurable)
        ((integrableOn_const hξc.isCompact.measure_lt_top.ne).integrable_indicator
          (isClosed_tsupport ξ).measurableSet) (fun j => .of_forall fun y => ?_) ?_
      · dsimp only
        by_cases hy : y ∈ tsupport ξ
        · rw [indicator_of_mem hy, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
          calc |f (φ j) y| * |divergence ξ y| ≤ 1 * ((n : ℝ) * D) :=
                mul_le_mul (hfb _ y (hB1V (hξB hy))) (Kernel.abs_divergence_le hD y)
                  (abs_nonneg _) zero_le_one
            _ = (n : ℝ) * D := one_mul _
        · rw [indicator_of_notMem hy, divergence_eq_zero_of_notMem_tsupport hy, mul_zero,
            norm_zero]
      · filter_upwards [(ae_restrict_iff' measurableSet_ball).1 hf₀ae] with y hy
        by_cases hyV : y ∈ V
        · exact (hy hyV).mul_const _
        · have : y ∉ tsupport ξ := fun h' => hyV (hB1V (hξB h'))
          simp [divergence_eq_zero_of_notMem_tsupport this]
    have hg := tendsto_setIntegral_norm_gradient_sub_sq (fun j => (hw j).isLipHarmonicPos)
      (fun j => (hw j).lipschitzOnWith) hconv' hξc.isCompact hK4
    have e0 : ∀ y, gradient (fun _ : Rn n => (0 : ℝ)) y = 0 := fun y => gradient_fun_const y 0
    simp only [e0, sub_zero] at hg
    have hbound : ∀ j, |∫ y, f (φ j) y * divergence ξ y| ≤
        ((n : ℝ) * D + 2 * D) * ∫ y in tsupport ξ, ‖gradient (w (φ j)) y‖ ^ 2 := by
      intro j
      rw [hfχ _ ξ hK4, (hw (φ j)).integral_chi_mul_divergence_eq hξ4, abs_neg,
        ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := tsupport ξ)
          fun y hy => Kernel.gradVariation_eq_zero_of_notMem_tsupport (u := w (φ j)) hy,
        ← Real.norm_eq_abs, ← integral_const_mul]
      refine norm_integral_le_of_norm_le ((IntegrableOn.of_bound hξc.isCompact.measure_lt_top
        ((measurable_gradient _).norm.pow_const 2).aestronglyMeasurable ((C : ℝ) ^ 2)
        ((ae_restrict_iff' (isClosed_tsupport ξ).measurableSet).2
          (.of_forall fun y hy => ?_))).const_mul _) (.of_forall fun y => ?_)
      · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) ((hw (φ j)).norm_gradient_le (hK4 hy)) 2
      · rw [Real.norm_eq_abs]
        calc |Kernel.gradVariation (w (φ j)) ξ y|
            ≤ ‖gradient (w (φ j)) y‖ ^ 2 * (n * D) + 2 * (‖gradient (w (φ j)) y‖ ^ 2 * D) :=
              Kernel.abs_gradVariation_le hD le_rfl
          _ = ((n : ℝ) * D + 2 * D) * ‖gradient (w (φ j)) y‖ ^ 2 := by ring
    have h2 : Tendsto (fun j => ∫ y, f (φ j) y * divergence ξ y) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun j => ?_) (by
        simpa using (hg.comp hφ.tendsto_atTop).const_mul ((n : ℝ) * D + 2 * D))
      rw [Real.norm_eq_abs]
      exact hbound j
    exact tendsto_nhds_unique h1 h2
  -- `f₀` is a.e. constant on `B_1`
  have hloc : LocallyIntegrableOn f₀ (ball (0 : Rn n) 1) :=
    IntegrableOn.locallyIntegrableOn (IntegrableOn.of_bound measure_ball_lt_top
      hf₀m.aestronglyMeasurable 1 (by
        filter_upwards [ae_restrict_of_ae_restrict_of_subset hB1V h01] with y hy
        rcases hy with h0 | h0 <;> simp [h0]))
  obtain ⟨c, hc⟩ := Regular.exists_ae_eq_const_of_integral_mul_divergence_eq_zero isOpen_ball
    (convex_ball (0 : Rn n) 1).isPreconnected hloc hlimid
  have hne : (ae (volume.restrict (ball (0 : Rn n) 1))).NeBot :=
    ae_neBot.2 fun h0 => (measure_ball_pos volume (0 : Rn n) one_pos).ne'
      (Measure.restrict_eq_zero.1 h0)
  obtain ⟨y, hyc, hy01⟩ := (hc.and (ae_restrict_of_ae_restrict_of_subset hB1V h01)).exists
  -- `m = c |B_1|`
  have hm1 : Tendsto (fun j => ∫ y in ball (0 : Rn n) 1, f (φ j) y) atTop
      (𝓝 (c * unitBallVolume n)) := by
    have := tendsto_integral_of_dominated_convergence (μ := volume.restrict (ball (0 : Rn n) 1))
      (F := fun j y => f (φ j) y) (f := f₀) (fun _ => (1 : ℝ))
      (fun j => (hfm _).aestronglyMeasurable) (integrableOn_const measure_ball_lt_top.ne)
      (fun j => (ae_restrict_iff' measurableSet_ball).2 (.of_forall fun y hy => by
        rw [Real.norm_eq_abs]; exact hfb _ y (hB1V hy)))
      (ae_restrict_of_ae_restrict_of_subset hB1V hf₀ae)
    rwa [setIntegral_congr_ae measurableSet_ball ((ae_restrict_iff' measurableSet_ball).1 hc),
      setIntegral_const, smul_eq_mul, mul_comm] at this
  have hm2 : Tendsto (fun j => ∫ y in ball (0 : Rn n) 1, f (φ j) y) atTop (𝓝 m) := by
    have := ((tendsto_add_atTop_iff_nat k₀).2
      (Regular.tendsto_setIntegral_chiRescale hd hr hr0)).comp hφ.tendsto_atTop
    refine this.congr fun j => ?_
    simp only [Function.comp_apply]
    refine setIntegral_congr_fun measurableSet_ball fun y hy => ?_
    simp only [hfdef, indicator_of_mem (hB1V.trans hV4 hy), hχwdef]
  have hmc : m = c * unitBallVolume n := tendsto_nhds_unique hm2 hm1
  rcases hy01 with h0 | h1
  · left; rw [hmc, ← hyc, h0, zero_mul]
  · right; rw [hmc, ← hyc, h1, one_mul]

end Blowup

/-! ### Lemma 8.1 -/

/-- **Lemma 8.1**, first claim. If `2 ≤ n`, `x ∈ Ω` and
`u(x) = 0`, then `M_x(u; 0+)` is a real number `m ∈ {0} ∪ [|B_1|/2, |B_1|]`. -/
theorem Mzero_eq_zero_or_half_le [NeZero n] (hn : 2 ≤ n) (h : IsVariationalSolution Ω C u χ)
    (hx : x ∈ Ω) (hux : u x = 0) : ∃ m : ℝ, Mzero u χ x = m ∧
      (m = 0 ∨ unitBallVolume n / 2 ≤ m) ∧ m ≤ unitBallVolume n := by
  obtain ⟨m, hmM, hm, hd⟩ := h.tendsto_monotonicityM_zero hx hux
  refine ⟨m, hmM, ?_, ?_⟩
  · have hr : ∀ k : ℕ, 0 < 1 / ((k : ℝ) + 1) := fun k => by positivity
    have hr0 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    obtain ⟨φ, hφ, u₀, hconv⟩ := h.exists_tendsto_rescale hx hux hr hr0
    have hr' : ∀ k, 0 < 1 / ((φ k : ℝ) + 1) := fun k => hr (φ k)
    have hr0' : Tendsto (fun k => 1 / ((φ k : ℝ) + 1)) atTop (𝓝 0) :=
      hr0.comp hφ.tendsto_atTop
    by_cases hpos : ∃ y₀, 0 < u₀ y₀
    · obtain ⟨y₀, hy₀⟩ := hpos
      exact Or.inr (half_le_of_tendsto_rescale h hx hm hd hr' hr0' hn hconv hy₀)
    · push Not at hpos
      have hH := blowup_isLipHarmonicPos h hx hr' hr0' hconv
      have hu₀ : u₀ = fun _ => 0 :=
        funext fun y => le_antisymm (hpos y) (hH.nonneg y trivial)
      rw [hu₀] at hconv
      rcases eq_zero_or_eq_of_tendsto_rescale_zero h hx hm hd hr' hr0' hconv with h0 | h1
      · exact Or.inl h0
      · right; rw [h1]; linarith [unitBallVolume_pos n]
  · have := h.Mzero_le_unitBallVolume hx
    rwa [hmM, EReal.coe_le_coe_iff] at this

/-- **Lemma 8.1**, second claim.
`M_x(u; 0+) = 0` only if `x` is in the interior of `{u = 0}`. -/
theorem mem_interior_of_Mzero_eq_zero [NeZero n] (hn : 2 ≤ n) (h : IsVariationalSolution Ω C u χ)
    (hx : x ∈ Ω) (hM : Mzero u χ x = 0) : x ∈ interior {y | u y = 0} := by
  have hB := unitBallVolume_pos n
  have hev : ∀ᶠ y in 𝓝 x, Mzero u χ y < ((unitBallVolume n / 4 : ℝ) : EReal) := by
    have := h.upperSemicontinuousOn_Mzero x hx ((unitBallVolume n / 4 : ℝ) : EReal) (by
      change Mzero u χ x < ((unitBallVolume n / 4 : ℝ) : EReal)
      rw [hM]
      exact_mod_cast (by positivity : (0 : ℝ) < unitBallVolume n / 4))
    rwa [h.isOpen.nhdsWithin_eq hx] at this
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.1 (hev.and (h.isOpen.mem_nhds hx))
  set E : Set (Rn n) := Ω ∩ {y | χ y = 1} with hEdef
  have hess : essentialBoundary E ∩ ball x δ = ∅ := by
    refine eq_empty_iff_forall_notMem.2 fun y ⟨hyE, hyB⟩ => ?_
    obtain ⟨hyM, hyΩ⟩ := hδsub hyB
    rcases (h.nonneg y hyΩ).lt_or_eq with hpos | hzero
    · exact hyE.2 (h.hasDensity_one_of_pos hyΩ hpos)
    · obtain ⟨ε, hε, hεΩ⟩ := Metric.isOpen_iff.1 h.isOpen y hyΩ
      obtain ⟨m, hmM, -, hd⟩ := h.tendsto_monotonicityM_zero hyΩ hzero.symm
      obtain ⟨m', hm'M, hm'01, -⟩ := h.Mzero_eq_zero_or_half_le hn hyΩ hzero.symm
      have hmm' : m = m' := by rw [hmM] at hm'M; exact_mod_cast hm'M
      have hm0 : m = 0 := by
        rcases hm'01 with h0 | hhalf
        · rw [hmm', h0]
        · exfalso
          rw [hmM] at hyM
          have := EReal.coe_lt_coe_iff.1 hyM
          linarith
      have := h.hasDensity_of_tendsto hε hεΩ hd
      rw [hm0, zero_div] at this
      exact hyE.1 this
  rcases Registry.ae_trivial_of_essentialBoundary_inter_ball hn h.measurableSet_chi_eq_one hess
    with h0 | h1
  · -- `{χ = 1}` is null in `B_δ(x)`, so `{u > 0} ∩ B_δ(x) = ∅`
    have hnull : volume (Ω ∩ {y | 0 < u y} ∩ ball x δ) = 0 := by
      refine measure_mono_null_ae ?_ h0
      filter_upwards [h.ae_chi_eq_one] with z hz
      rintro ⟨⟨hzΩ, hzp⟩, hzb⟩
      exact ⟨⟨hzΩ, hz hzΩ hzp⟩, hzb⟩
    have hempty : Ω ∩ {y | 0 < u y} ∩ ball x δ = ∅ :=
      ((h.isOpen_pos.inter isOpen_ball).measure_eq_zero_iff volume).1 hnull
    rw [mem_interior]
    refine ⟨ball x δ, fun y hy => ?_, isOpen_ball, mem_ball_self hδ⟩
    have hyΩ := (hδsub hy).2
    refine le_antisymm (not_lt.1 fun hp => ?_) (h.nonneg y hyΩ)
    exact eq_empty_iff_forall_notMem.1 hempty y ⟨⟨hyΩ, hp⟩, hy⟩
  · -- `{χ = 1}` is full in `B_δ(x)`: contradicts density `0` at `x`
    exfalso
    have hux : u x = 0 := by
      rcases (h.nonneg x hx).lt_or_eq with hpos | h0
      · rw [h.Mzero_eq_bot_of_pos hx hpos] at hM; exact absurd hM EReal.bot_ne_zero
      · exact h0.symm
    obtain ⟨m, hmM, -, hd⟩ := h.tendsto_monotonicityM_zero hx hux
    have hm0 : m = 0 := by rw [hM] at hmM; exact_mod_cast hmM.symm
    have hc : ∀ᵐ z ∂(volume.restrict (ball x δ)), χ z = 1 := by
      rw [ae_restrict_iff' measurableSet_ball]
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 h1] with z hz hzb
      by_contra hne
      exact hz ⟨hzb, fun hzE => hne hzE.2⟩
    have := tendsto_nhds_unique hd (Regular.tendsto_density_of_ae_eq_const hδ hc)
    rw [hm0, one_mul] at this
    linarith

/-- **Lemma 8.1**, last claim, with `M_x(u; 0+) = |B_1|` (the last line of the paper's proof
reads `1`; the intended value is `|B_1|`). If `x ∈ Ω ∩ ∂{u > 0}` and `u_{x,r_k} → 0` locally
uniformly along some `r_k → 0+`, then `M_x(u; 0+) = |B_1|`. The paper assumes `u(x + r ·)/r → 0` as
`r → 0`; convergence along one sequence suffices. -/
theorem Mzero_eq_of_tendsto_rescale_zero [NeZero n] (hn : 2 ≤ n)
    (h : IsVariationalSolution Ω C u χ) (hx : x ∈ Ω) (hfr : x ∈ frontier {y | 0 < u y})
    {r : ℕ → ℝ} (hr : ∀ k, 0 < r k) (hr0 : Tendsto r atTop (𝓝 0))
    (hconv : TendstoLocallyUniformly (fun k => oneHomRescale u x (r k)) (fun _ => 0) atTop) :
    Mzero u χ x = unitBallVolume n := by
  obtain ⟨hcl, hux⟩ := (h.mem_frontier_pos_iff hx).1 hfr
  obtain ⟨m, hmM, hm, hd⟩ := h.tendsto_monotonicityM_zero hx hux
  rcases eq_zero_or_eq_of_tendsto_rescale_zero h hx hm hd hr hr0 hconv with h0 | h1
  · exfalso
    have hint := h.mem_interior_of_Mzero_eq_zero hn hx (by rw [hmM, h0, EReal.coe_zero])
    obtain ⟨y, hyint, hypos⟩ := mem_closure_iff.1 hcl _ isOpen_interior hint
    have hy0 : u y = 0 := interior_subset (s := {y | u y = 0}) hyint
    have hyp : 0 < u y := hypos
    rw [hy0] at hyp
    exact lt_irrefl _ hyp
  · rw [hmM, h1]

/-- On the free boundary, `|B_1|/2 ≤ M_x(u; 0+) ≤ |B_1|` (used in the proofs of Lemmas 8.2
and 8.3). -/
theorem half_le_Mzero_of_mem_frontier [NeZero n] (hn : 2 ≤ n) (h : IsVariationalSolution Ω C u χ)
    (hx : x ∈ Ω) (hfr : x ∈ frontier {y | 0 < u y}) : ∃ m : ℝ, Mzero u χ x = m ∧
      unitBallVolume n / 2 ≤ m ∧ m ≤ unitBallVolume n := by
  obtain ⟨hcl, hux⟩ := (h.mem_frontier_pos_iff hx).1 hfr
  obtain ⟨m, hmM, hm01, hm1⟩ := h.Mzero_eq_zero_or_half_le hn hx hux
  refine ⟨m, hmM, ?_, hm1⟩
  rcases hm01 with h0 | hhalf
  · exfalso
    have hint := h.mem_interior_of_Mzero_eq_zero hn hx (by rw [hmM, h0, EReal.coe_zero])
    obtain ⟨y, hyint, hypos⟩ := mem_closure_iff.1 hcl _ isOpen_interior hint
    have hy0 : u y = 0 := interior_subset (s := {y | u y = 0}) hyint
    have hyp : 0 < u y := hypos
    rw [hy0] at hyp
    exact lt_irrefl _ hyp
  · exact hhalf

end IsVariationalSolution

end InnerVariational
