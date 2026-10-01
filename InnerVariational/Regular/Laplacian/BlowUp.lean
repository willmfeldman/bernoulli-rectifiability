/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Regular.Viscosity
public import InnerVariational.Regular.Bump
public import InnerVariational.Singular.Density
public import InnerVariational.Defs.LaplacianMeasure
public import InnerVariational.Main.RieszMeasure
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
import InnerVariational.Regular.HarmonicCone
import InnerVariational.Regular.Perimeter
import InnerVariational.Regular.Density
import InnerVariational.Registry.GMT
import InnerVariational.Vendor.Analysis.LocalCompactness
import InnerVariational.Regular.ZeroGradient
import InnerVariational.Monotonicity.HighestDensity
import InnerVariational.Monotonicity.Density
import InnerVariational.Kernel.Rescale
import InnerVariational.Monotonicity.Blowup
import InnerVariational.Kernel.Subharmonic
public import InnerVariational.Defs.VariationalSolution
import InnerVariational.Kernel.IBP
import InnerVariational.Basic.SphereIntegral
import InnerVariational.Basic.Polar
public import InnerVariational.Regular.Laplacian.Measure

/-!
# Blow-ups at reduced-boundary points and Corollary 8.4

Corollary 8.4 of D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and
compactness for non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025),
no. 3, DOI 10.1002/cpa.22226; arXiv:2306.10131 (numbering of arXiv v2), in the form used by
Theorem 8.7: if `(u, χ)` is a variational solution on `Ω`, `2 ≤ n`, and `Σ^H = ∅`, then

  `Δu = ℋ^{n-1}⌊∂*{u > 0}` in `Ω` in the sense of distributions

(`IsVariationalSolution.laplacian_eq_of_sigmaH_empty`). No connectedness of `Ω` is needed. The
analyticity of `∂*{u > 0}` and the dimension bound for `∂{u > 0} \ ∂*{u > 0}` (De Silva's
`ε`-regularity, D. De Silva, *Free boundary regularity for a problem with right hand side*,
Interfaces Free Bound. 13 (2011), 223–238, Theorem 1.1, and Weiss's dimension reduction,
G. S. Weiss, *Partial regularity for a minimum problem with free boundary*, J. Geom. Anal. 9
(1999), 317–326, Theorem 4.5) are not formalized; Theorem 8.7 only uses the measure identity.

## Proof (measure-theoretic, no free-boundary regularity)

The proof of Corollary 8.4 covers the regularity of `∂*{u > 0}` and the dimension bound; the
identity `Δu = ℋ^{n-1}⌊∂*{u > 0}` is obtained here by a Lebesgue-point argument with De Giorgi's
blow-up, using the density bound `Δu(B_r) ≤ C r^{n-1}` of Lemma 3.3, without any regularity of
the free boundary.

Write `E = Ω ∩ {u > 0}`, `S = Ω ∩ ∂{u > 0}`, `ℋ = ℋ^{n-1}`, `σ = ℋ⌊S`.

1. `u` is subharmonic (Prop 3.2), so `Δu = ρ` is a Radon measure on `Ω` (Riesz;
   `Main.exists_hasDistribLaplacianOn`). `ρ` lives on `S` (`u` is harmonic on `{u > 0}` and
   vanishes on `{u = 0}°`), and `ρ(B_r(x)) ≤ K r^{n-1}` (cutoff argument of Lemma 3.3).
2. `E` has locally finite perimeter in `Ω` (Lemma 8.2 on balls and the local BV structure
   theorem, L. C. Evans and R. F. Gariepy, *Measure Theory and Fine Properties of Functions*,
   rev. ed., CRC Press, 2015, §5.7–5.8), and `S = Ω ∩ ∂ᵉE` (Lemma 8.1). By Federer's theorem
   (H. Federer, *Geometric Measure Theory*, Springer, 1969, 4.5.6) every Gauss–Green measure of
   `E` is `σ`; by the De Giorgi–Federer structure theorem (Federer 4.5.6; F. Maggi, *Sets of
   Finite Perimeter and Geometric Variational Problems*, Cambridge Univ. Press, 2012,
   Theorems 15.5 and 15.9), `S` is rectifiable and `ℋ(S \ ∂*E) = 0`. The Radon–Nikodym and
   density theorems (Federer 2.10.19, 3.2.19) then give `ρ ≪ σ`. These geometric measure theory
   results are proved in gmt-foundations (https://github.com/willmfeldman/gmt-foundations,
   v0.1.0).
3. Let `θ = dρ/dσ`. At a reduced-boundary point `x` with averaged normal `v` that is a Lebesgue
   point of `θ` (Besicovitch), test with the bump `ψ_r = bump((· − x)/r)`:
   * `r^{1-n} ∫ ψ_r dσ → c := ∫_{⟪z,v⟫<0} ⟪∇bump, v⟫ > 0`. Indeed
     `∫ ψ_r ⟪v, ν⟫ dσ = ∫_E div(ψ_r v)`, the blow-ups of `E` converge to `{⟪z, v⟫ < 0}` in `L¹_loc`
     (De Giorgi; Maggi, Theorem 15.5), and `∫ ψ_r (1 − ⟪v, ν⟫) dσ = o(r^{n-1})` because the
     averages of `ν` converge to `v`.
   * `r^{1-n} ∫ ψ_r dρ = −∫ ⟪∇u_{x,r}, ∇bump⟫ → c` along a sequence: the blow-up `u₀` vanishes on
     `{⟪z, v⟫ > 0}` (the blow-up of `E` is the other half-space), so `u₀ = a ⟪z, −v⟫₊` (by the
     equality case of Sperner's inequality, E. Sperner, Jr., *Zur Symmetrisierung von Funktionen
     auf Sphären*, Math. Z. 134 (1973), 317–327) and
     the half-space computation of Lemma 8.3 gives `a = 1`.
   * `∫ ψ_r θ dσ − θ(x) ∫ ψ_r dσ = o(r^{n-1})` at a Lebesgue point.
   Hence `θ(x) = 1`, so `ρ = σ = ℋ⌊∂*E`.

The paper instead invokes the regularity of `∂*{u > 0}` (analytic graphs with `|∇u| = 1`).
-/

open MeasureTheory Metric Set Filter Topology InnerProductSpace Laplacian
open scoped NNReal ENNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

namespace IsVariationalSolution

variable {Ω : Set (Rn n)} {C : ℝ≥0} {u χ : Rn n → ℝ} {x : Rn n}

/-! ### Blow-ups at reduced-boundary points -/

/-- `L¹` convergence of the blow-ups of `χ` to the half-space indicator, from the blow-up of
`E = Ω ∩ {u > 0}` and `χ = χ_E` a.e. near `x`. -/
theorem tendsto_setIntegral_abs_chiRescale_sub [NeZero n] (h : IsVariationalSolution Ω C u χ)
    {R₁ : ℝ} (hR₁ : 0 < R₁) (hB : ball x R₁ ⊆ Ω)
    (hae : ∀ᵐ y ∂(volume.restrict (ball x R₁)), χ y = posIndicator u y) {v : Rn n}
    (hDG : HasDensity (symmDiff (Ω ∩ {y | 0 < u y}) {y | ⟪y - x, v⟫ < 0}) x 0) :
    Tendsto (fun r => ∫ z in ball (0 : Rn n) 1,
      |chiRescale χ x r z - {z : Rn n | ⟪z, v⟫ < 0}.indicator 1 z|) (𝓝[>] 0) (𝓝 0) := by
  set E : Set (Rn n) := Ω ∩ {y | 0 < u y} with hEdef
  set Hx : Set (Rn n) := {y | ⟪y - x, v⟫ < 0} with hHxdef
  set H : Set (Rn n) := {z | ⟪z, v⟫ < 0} with hHdef
  set A : Set (Rn n) := symmDiff E Hx with hAdef
  have hHxm : MeasurableSet Hx :=
    (isOpen_lt ((continuous_id.sub continuous_const).inner continuous_const)
      continuous_const).measurableSet
  have hA : MeasurableSet A := h.isOpen_pos.measurableSet.symmDiff hHxm
  set q : ℝ → ℝ := fun s => (volume (A ∩ ball x s)).toReal / (volume (ball x s)).toReal
    with hqdef
  have key : ∀ r ∈ Ioo 0 R₁, ∫ z in ball (0 : Rn n) 1, |chiRescale χ x r z - H.indicator 1 z| =
      unitBallVolume n * q r := by
    intro r hr
    set F : Rn n → ℝ := (ball (0 : Rn n) 1).indicator
      (fun z => |chiRescale χ x r z - H.indicator 1 z|) with hFdef
    have hcv := Regular.integral_comp_rescale F x hr.1
    have e : ∀ y, F (r⁻¹ • (y - x)) =
        (ball x r).indicator (fun y => |χ y - Hx.indicator 1 y|) y := fun y => by
      have hxy : x + r • r⁻¹ • (y - x) = y := by
        rw [smul_smul, mul_inv_cancel₀ hr.1.ne', one_smul, add_sub_cancel]
      have hball : r⁻¹ • (y - x) ∈ ball (0 : Rn n) 1 ↔ y ∈ ball x r := by
        rw [mem_ball_zero_iff, norm_smul, norm_inv, Real.norm_of_nonneg hr.1.le, mem_ball,
          dist_eq_norm, inv_mul_lt_iff₀ hr.1, mul_one]
      have hH : r⁻¹ • (y - x) ∈ H ↔ y ∈ Hx := by
        simp only [hHdef, hHxdef, mem_ofPred_eq, real_inner_smul_left]
        constructor
        · intro h'
          by_contra hc
          exact (not_lt.2 (mul_nonneg (inv_nonneg.2 hr.1.le) (not_lt.1 hc))) h'
        · exact fun h' => mul_neg_of_pos_of_neg (inv_pos.2 hr.1) h'
      by_cases hy : y ∈ ball x r
      · rw [hFdef, indicator_of_mem (hball.2 hy), indicator_of_mem hy, chiRescale_apply, hxy]
        by_cases hyH : y ∈ Hx
        · rw [indicator_of_mem (hH.2 hyH), indicator_of_mem hyH, Pi.one_apply, Pi.one_apply]
        · rw [indicator_of_notMem (fun h' => hyH (hH.1 h')), indicator_of_notMem hyH]
      · rw [hFdef, indicator_of_notMem (fun h' => hy (hball.1 h')), indicator_of_notMem hy]
    have hae2 : (fun y => F (r⁻¹ • (y - x))) =ᵐ[volume] (A ∩ ball x r).indicator 1 := by
      filter_upwards [(ae_restrict_iff' measurableSet_ball).1 hae] with y hy
      rw [e]
      by_cases hyB : y ∈ ball x r
      · have hyR : y ∈ ball x R₁ := ball_subset_ball hr.2.le hyB
        have hyΩ : y ∈ Ω := hB hyR
        rw [indicator_of_mem hyB, hy hyR]
        by_cases hp : 0 < u y
        · have hyE : y ∈ E := ⟨hyΩ, hp⟩
          rw [posIndicator_of_pos hp]
          by_cases hyH : y ∈ Hx
          · rw [indicator_of_mem hyH, indicator_of_notMem (fun h' => ?_)]
            · simp
            · rcases Set.mem_symmDiff.1 h'.1 with ⟨-, h''⟩ | ⟨-, h''⟩
              · exact h'' hyH
              · exact h'' hyE
          · rw [indicator_of_notMem hyH, indicator_of_mem
              (show y ∈ A ∩ ball x r from ⟨Set.mem_symmDiff.2 (Or.inl ⟨hyE, hyH⟩), hyB⟩)]
            simp
        · have hyE : y ∉ E := fun h' => hp h'.2
          rw [posIndicator_of_nonpos (not_lt.1 hp)]
          by_cases hyH : y ∈ Hx
          · rw [indicator_of_mem hyH, indicator_of_mem
              (show y ∈ A ∩ ball x r from ⟨Set.mem_symmDiff.2 (Or.inr ⟨hyH, hyE⟩), hyB⟩)]
            simp
          · rw [indicator_of_notMem hyH, indicator_of_notMem (fun h' => ?_)]
            · simp
            · rcases Set.mem_symmDiff.1 h'.1 with ⟨h'', -⟩ | ⟨h'', -⟩
              · exact hyE h''
              · exact hyH h''
      · rw [indicator_of_notMem hyB, indicator_of_notMem (fun h' => hyB h'.2)]
    have h3 : ∫ y, F (r⁻¹ • (y - x)) = (volume (A ∩ ball x r)).toReal := by
      rw [integral_congr_ae hae2, integral_indicator_one (hA.inter measurableSet_ball),
        measureReal_def]
    rw [← integral_indicator measurableSet_ball]
    change ∫ z, F z = _
    have hB0 := unitBallVolume_pos n
    have hvol := volume_ball_toReal x hr.1
    rw [hqdef]
    simp only
    rw [hvol]
    rw [h3] at hcv
    field_simp
    rw [hcv, mul_div_right_comm, div_self (pow_ne_zero n hr.1.ne'), one_mul]
  have hq : Tendsto (fun r => unitBallVolume n * q r) (𝓝[>] 0) (𝓝 0) := by
    simpa using hDG.const_mul (unitBallVolume n)
  refine hq.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hR₁] with r hr
  exact (key r hr).symm

/-- **Blow-up at a reduced-boundary point.** If `x ∈ Ω ∩ ∂{u > 0}` and `Ω ∩ {u > 0}` blows up to
`{⟪z, v⟫ < 0}` at `x`, then along some `r_k → 0+` the blow-ups converge to `⟪z, −v⟫₊`, so
`∫ ⟪∇u_{x,r_k}, ∇bump⟫ → −halfSpaceFlux v`. -/
theorem exists_tendsto_integral_inner_gradient_bump [NeZero n] (hn : 2 ≤ n)
    (h : IsVariationalSolution Ω C u χ) (hS : sigmaH Ω u χ = ∅)
    (hx : x ∈ Ω ∩ frontier {y | 0 < u y}) {v : Rn n} (hv : ‖v‖ = 1)
    (hDG : HasDensity (symmDiff (Ω ∩ {y | 0 < u y}) {y | ⟪y - x, v⟫ < 0}) x 0) :
    ∃ r : ℕ → ℝ, (∀ k, 0 < r k) ∧ Tendsto r atTop (𝓝 0) ∧
      Tendsto (fun k => ∫ z, ⟪gradient (oneHomRescale u x (r k)) z, gradient Regular.bump z⟫)
        atTop (𝓝 (-Regular.halfSpaceFlux v)) := by
  obtain ⟨hxΩ, hfr⟩ := hx
  have hux : u x = 0 := ((h.mem_frontier_pos_iff hxΩ).1 hfr).2
  obtain ⟨m, -, hm⟩ := h.exists_tendsto_monotonicityM_of_eq_zero hxΩ hux
  obtain ⟨R₀, hR₀, hR₀Ω⟩ := h.exists_ball_subset hxΩ
  have hae := h.ae_chi_eq_posIndicator_of_mem_frontier hn hS hfr hR₀ hR₀Ω
  have hL1 := h.tendsto_setIntegral_abs_chiRescale_sub hR₀ hR₀Ω hae hDG
  -- a blow-up sequence
  have hs : ∀ k : ℕ, 0 < 1 / ((k : ℝ) + 1) := fun k => by positivity
  have hs0 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨φ, hφ, u₀, hconv⟩ := h.exists_tendsto_rescale hxΩ hux hs hs0
  set r : ℕ → ℝ := fun k => 1 / ((φ k : ℝ) + 1) with hrdef
  have hr : ∀ k, 0 < r k := fun k => hs (φ k)
  have hr0 : Tendsto r atTop (𝓝 0) := hs0.comp hφ.tendsto_atTop
  have hLip := blowup_lipschitzWith h hxΩ hr hr0 hconv
  have hH := blowup_isLipHarmonicPos h hxΩ hr hr0 hconv
  have hhom := blowup_homogeneous h hxΩ hr hr0 hconv
  obtain ⟨k₀, hw, hconv', -⟩ := h.blowup_window hR₀ hR₀Ω hm hr hr0 hconv (ρ := 4) (by norm_num)
  set w : ℕ → Rn n → ℝ := fun j => oneHomRescale u x (r (j + k₀)) with hwdef
  set χw : ℕ → Rn n → ℝ := fun j => chiRescale χ x (r (j + k₀)) with hχwdef
  set fw : ℕ → Rn n → ℝ := fun j => (ball (0 : Rn n) 4).indicator (χw j) with hfwdef
  have hfwm : ∀ j, Measurable (fw j) := fun j => (hw j).measurable_chi
  have hfw01 : ∀ j y, fw j y = 0 ∨ fw j y = 1 := fun j y => by
    by_cases hy : y ∈ ball (0 : Rn n) 4
    · simp only [hfwdef, indicator_of_mem hy]
      exact (hw j).chi_mem y hy
    · simp [hfwdef, indicator_of_notMem hy]
  have hfwb : ∀ j y, |fw j y| ≤ 1 := fun j y => by
    rcases hfw01 j y with h0 | h0 <;> simp [h0]
  have hB14 : ball (0 : Rn n) 1 ⊆ ball 0 4 := ball_subset_ball (by norm_num)
  have hrk : Tendsto (fun j => r (j + k₀)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨(tendsto_add_atTop_iff_nat k₀).2 hr0, .of_forall fun j => hr _⟩
  set f₀ : Rn n → ℝ := {z : Rn n | ⟪z, v⟫ < 0}.indicator 1 with hf₀def
  have hHm : MeasurableSet {z : Rn n | ⟪z, v⟫ < 0} :=
    (Regular.isOpen_halfSpace_neg v).measurableSet
  have hf₀m : Measurable f₀ := measurable_one.indicator hHm
  have hf₀b : ∀ y, |f₀ y| ≤ 1 := fun y => by
    by_cases hy : y ∈ {z : Rn n | ⟪z, v⟫ < 0} <;> simp [hf₀def, hy]
  have hL1' : Tendsto (fun j => ∫ z in ball (0 : Rn n) 1, |fw j z - f₀ z|) atTop (𝓝 0) := by
    refine (hL1.comp hrk).congr fun j => setIntegral_congr_fun measurableSet_ball fun z hz => ?_
    simp only [hfwdef, indicator_of_mem (hB14 hz), hχwdef]
  -- the limit domain variation identity with `f₀`
  have hid : ∀ ξ, IsSmoothTestField (ball (0 : Rn n) 1) ξ →
      (∫ y, Kernel.gradVariation u₀ ξ y) + ∫ y, f₀ y * divergence ξ y = 0 := by
    intro ξ hξ
    obtain ⟨⟨D, hD⟩, hξc, hξB⟩ := hξ.isLipTestField
    have hξ4 : IsLipTestField (ball (0 : Rn n) 4) ξ := hξ.isLipTestField.mono hB14
    have hK4 : tsupport ξ ⊆ ball (0 : Rn n) 4 := hξB.trans hB14
    have hfχ : ∀ j, ∫ y, fw j y * divergence ξ y = ∫ y, χw j y * divergence ξ y := by
      intro j
      congr 1
      funext y
      by_cases hy : y ∈ ball (0 : Rn n) 4
      · simp only [hfwdef, indicator_of_mem hy]
      · simp only [hfwdef, indicator_of_notMem hy,
          divergence_eq_zero_of_notMem_tsupport fun h' => hy (hK4 h'), mul_zero]
    have h1 : Tendsto (fun j => ∫ y, fw j y * divergence ξ y) atTop
        (𝓝 (∫ y, f₀ y * divergence ξ y)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun _ => norm_nonneg _) (fun j => ?_)
        (by simpa using hL1'.const_mul ((n : ℝ) * D))
      rw [Real.norm_eq_abs]
      exact Regular.abs_integral_mul_divergence_sub_le (hfwm j) hf₀m (hfwb j) hf₀b hD hξc hξB
    have hg := tendsto_setIntegral_norm_gradient_sub_sq (fun j => (hw j).isLipHarmonicPos)
      (fun j => (hw j).lipschitzOnWith) hconv' hξc.isCompact hK4
    have h2 : Tendsto (fun j => ∫ y, Kernel.gradVariation (w j) ξ y) atTop
        (𝓝 (∫ y, Kernel.gradVariation u₀ ξ y)) :=
      Regular.tendsto_integral_gradVariation hD hξc (L := C)
        (fun j y hy => (hw j).norm_gradient_le (hK4 hy))
        (fun y _ => Kernel.norm_gradient_le_of_lipschitz hLip y) hg
    have h3 : ∀ j, ∫ y, fw j y * divergence ξ y = -∫ y, Kernel.gradVariation (w j) ξ y :=
      fun j => by rw [hfχ j, (hw j).integral_chi_mul_divergence_eq hξ4]
    have h4 := tendsto_nhds_unique h1 (h2.neg.congr fun j => (h3 j).symm)
    rw [h4]
    ring
  -- `u₀ = 0` on `B_1 ∩ {⟪z, v⟫ > 0}`
  have hB1 : ∀ z ∈ ball (0 : Rn n) 1, 0 < ⟪z, v⟫ → u₀ z = 0 := by
    set U := {z | 0 < u₀ z} ∩ ball (0 : Rn n) 1 ∩ {z | 0 < ⟪z, v⟫} with hUdef
    have hUo : IsOpen U := ((isOpen_lt continuous_const hLip.continuous).inter isOpen_ball).inter
      (isOpen_lt continuous_const (continuous_id.inner continuous_const))
    have hUB : U ⊆ ball (0 : Rn n) 1 := fun z hz => hz.1.2
    have hUfin : volume U < ∞ := (measure_mono hUB).trans_lt measure_ball_lt_top
    -- `fw j → 1` a.e. on `U`
    have hposae : ∀ᵐ y ∂(volume.restrict (ball (0 : Rn n) 4)),
        ∀ j, posIndicator (w j) y ≤ χw j y :=
      ae_all_iff.2 fun j => (hw j).posIndicator_le_chi
    have hlimU : ∀ᵐ y ∂(volume.restrict U), Tendsto (fun j => fw j y) atTop (𝓝 1) := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset (hUB.trans hB14) hposae,
        ae_restrict_mem hUo.measurableSet] with y hy hyU
      have hy4 : y ∈ ball (0 : Rn n) 4 := hB14 (hUB hyU)
      have hc := hconv'.tendsto_at hy4
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hc.eventually (lt_mem_nhds hyU.1.1)] with j hj
      have h1 : posIndicator (w j) y ≤ chiRescale χ x (r (j + k₀)) y := hy j
      rw [posIndicator_of_pos hj] at h1
      simp only [hfwdef, indicator_of_mem hy4, hχwdef]
      rcases (hw j).chi_mem y hy4 with h0 | h0
      · rw [h0] at h1
        norm_num at h1
      · exact h0.symm
    have hconvU : Tendsto (fun j => ∫ y in U, fw j y) atTop (𝓝 (∫ y in U, (1 : ℝ))) :=
      tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
        (fun j => (hfwm j).aestronglyMeasurable) (integrableOn_const hUfin.ne)
        (fun j => .of_forall fun y => by rw [Real.norm_eq_abs]; exact hfwb j y) hlimU
    have hle : ∀ j, ∫ y in U, fw j y ≤ ∫ y in ball (0 : Rn n) 1, |fw j y - f₀ y| := by
      intro j
      have hon : IntegrableOn (fun y => |fw j y - f₀ y|) (ball (0 : Rn n) 1) :=
        IntegrableOn.of_bound measure_ball_lt_top
          ((hfwm j).sub hf₀m).abs.aestronglyMeasurable 2 (.of_forall fun y => by
            rw [Real.norm_eq_abs, abs_abs]
            exact (abs_sub _ _).trans (by linarith [hfwb j y, hf₀b y]))
      calc ∫ y in U, fw j y = ∫ y in U, |fw j y - f₀ y| := by
            refine setIntegral_congr_fun hUo.measurableSet fun y hy => ?_
            have hf0 : f₀ y = 0 := by
              simp only [hf₀def]
              exact indicator_of_notMem (show y ∉ {z : Rn n | ⟪z, v⟫ < 0} from
                fun h' => lt_asymm (show 0 < ⟪y, v⟫ from hy.2) h') _
            rw [hf0, sub_zero]
            rcases hfw01 j y with h0 | h0 <;> simp [h0]
        _ ≤ ∫ y in ball (0 : Rn n) 1, |fw j y - f₀ y| :=
            setIntegral_mono_set hon (.of_forall fun y => abs_nonneg _) hUB.eventuallyLE
    have hU0 : ∫ y in U, (1 : ℝ) ≤ 0 :=
      le_of_tendsto_of_tendsto' hconvU hL1' hle
    have hUvol : volume U = 0 := by
      rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def] at hU0
      have := le_antisymm hU0 ENNReal.toReal_nonneg
      rcases (ENNReal.toReal_eq_zero_iff _).1 this with h0 | h0
      · exact h0
      · exact absurd h0 hUfin.ne
    intro z hz hzv
    by_contra hne
    have hpos : 0 < u₀ z := lt_of_le_of_ne (hH.nonneg z trivial) (Ne.symm hne)
    exact (hUo.measure_pos volume ⟨z, ⟨⟨hpos, hz⟩, hzv⟩⟩).ne' hUvol
  -- by homogeneity and continuity, `u₀ = 0` on `{⟪z, v⟫ ≥ 0}`
  have hU : ∀ z, 0 < ⟪z, v⟫ → u₀ z = 0 := by
    intro z hzv
    set t : ℝ := 1 / (2 * (‖z‖ + 1)) with htdef
    have ht : 0 < t := by positivity
    have htz : t • z ∈ ball (0 : Rn n) 1 := by
      rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg ht.le, htdef]
      rw [div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]
      linarith [norm_nonneg z]
    have h0 := hB1 _ htz (by rw [real_inner_smul_left]; positivity)
    rw [hhom t ht z] at h0
    exact (mul_eq_zero.1 h0).resolve_left ht.ne'
  have hU' : ∀ z, 0 ≤ ⟪z, v⟫ → u₀ z = 0 := by
    intro z hz
    rcases hz.lt_or_eq with hz | hz
    · exact hU z hz
    · refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) (hH.nonneg z trivial)
      have hC1 : (0 : ℝ) < C + 1 := by positivity
      set w' := z + (ε / (C + 1)) • v with hw'def
      have hvv : ⟪v, v⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hv, one_pow]
      have hw'0 : u₀ w' = 0 := hU _ (by
        rw [hw'def, inner_add_left, real_inner_smul_left, hvv, ← hz, zero_add, mul_one]
        positivity)
      have hd := hLip.dist_le_mul z w'
      rw [Real.dist_eq, hw'0, sub_zero, dist_eq_norm, hw'def, sub_add_cancel_left, norm_neg,
        norm_smul, hv, mul_one, Real.norm_of_nonneg (by positivity)] at hd
      have h1 : u₀ z ≤ C * (ε / (C + 1)) := (le_abs_self _).trans hd
      have h2 : (C : ℝ) * (ε / (C + 1)) ≤ ε := by
        rw [mul_div_assoc', div_le_iff₀ hC1]
        nlinarith [NNReal.coe_nonneg C]
      linarith
  -- the upper bound `u₀ ≤ (C + 1) ⟪z, e⟫₊` with `e = −v`
  set e : Rn n := -v with hedef
  have he : ‖e‖ = 1 := by rw [hedef, norm_neg, hv]
  have hve : ∀ z, ⟪z, e⟫ = -⟪z, v⟫ := fun z => by rw [hedef, inner_neg_right]
  have hvv : ⟪v, v⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hv, one_pow]
  have hle : ∀ z, u₀ z ≤ max (((C : ℝ) + 1) * ⟪z, e⟫) 0 := by
    intro z
    by_cases hz : 0 ≤ ⟪z, v⟫
    · rw [hU' z hz]
      exact le_max_right _ _
    · push Not at hz
      set z' := z - ⟪z, e⟫ • e with hz'def
      have hz'v : ⟪z', v⟫ = 0 := by
        rw [hz'def, inner_sub_left, real_inner_smul_left, hve, hedef, inner_neg_left, hvv]
        ring
      have h0 := hU' z' hz'v.ge
      have hd := hLip.dist_le_mul z z'
      rw [Real.dist_eq, h0, sub_zero, dist_eq_norm, hz'def, sub_sub_cancel, norm_smul, he,
        mul_one, Real.norm_eq_abs, abs_of_pos (show 0 < ⟪z, e⟫ by rw [hve]; linarith)] at hd
      refine le_trans ((le_abs_self _).trans hd) (le_trans ?_ (le_max_left _ _))
      have hze : 0 < ⟪z, e⟫ := by rw [hve]; linarith
      nlinarith
  -- the classification and the half-space computation
  have hf₀e : ∀ y, f₀ y * 1 = {y : Rn n | 0 < ⟪y, e⟫}.indicator 1 y := fun y => by
    have hiff : ⟪y, v⟫ < 0 ↔ 0 < ⟪y, e⟫ := by rw [hve]; constructor <;> intro h' <;> linarith
    by_cases hy : ⟪y, v⟫ < 0
    · rw [hf₀def, indicator_of_mem (show y ∈ {z : Rn n | ⟪z, v⟫ < 0} from hy),
        indicator_of_mem (show y ∈ {y : Rn n | 0 < ⟪y, e⟫} from hiff.1 hy), Pi.one_apply,
        mul_one]
    · rw [hf₀def, indicator_of_notMem (show y ∉ {z : Rn n | ⟪z, v⟫ < 0} from hy),
        indicator_of_notMem (show y ∉ {y : Rn n | 0 < ⟪y, e⟫} from fun h' => hy (hiff.2 h'))]
      ring
  have hu₀ : u₀ = fun z => 1 * max ⟪z, e⟫ 0 := by
    by_cases hex : ∃ y₀, 0 < u₀ y₀
    · obtain ⟨y₀, hy₀⟩ := hex
      obtain ⟨a, ha, hua⟩ := Regular.eq_mul_max_of_le_max hn hLip (fun y => hH.nonneg y trivial)
        hhom (fun y hy => hH.harmonicAt y trivial hy) hy₀ he (by positivity) hle
      have hu₀' : u₀ = fun z => a * max ⟪z, e⟫ 0 := funext hua
      have ha1 : a = 1 := by
        refine Regular.eq_one_of_halfSpace he ha hf₀m (.of_forall fun y => ?_)
          (.of_forall fun y hy => ?_) fun ξ hξ => ?_
        · by_cases hy : y ∈ {z : Rn n | ⟪z, v⟫ < 0} <;> simp [hf₀def, hy]
        · have := hf₀e y
          rw [mul_one, indicator_of_mem (show y ∈ {y : Rn n | 0 < ⟪y, e⟫} from hy),
            Pi.one_apply] at this
          exact this
        · rw [← hu₀']
          exact hid ξ hξ
      rw [hu₀', ha1]
    · exfalso
      push Not at hex
      have hu0 : ∀ y, gradient u₀ y = 0 := fun y =>
        hH.gradient_eq_zero_of_eq_zero trivial (le_antisymm (hex y) (hH.nonneg y trivial))
      obtain ⟨ξ, hξ, hne⟩ := Regular.exists_integral_indicator_divergence_ne_zero he
      have h1 := hid ξ hξ
      have hz : ∫ y, Kernel.gradVariation u₀ ξ y = 0 := integral_eq_zero_of_ae
        (.of_forall fun y => Kernel.gradVariation_eq_zero_of_gradient_eq_zero (hu0 y))
      rw [hz, zero_add] at h1
      have hEq : ∫ y, {y : Rn n | 0 < ⟪y, e⟫}.indicator (divergence ξ) y =
          ∫ y, f₀ y * divergence ξ y := by
        congr 1
        funext y
        have := hf₀e y
        rw [mul_one] at this
        rw [this]
        by_cases hy : y ∈ {y : Rn n | 0 < ⟪y, e⟫}
        · rw [indicator_of_mem hy, indicator_of_mem hy, Pi.one_apply, one_mul]
        · rw [indicator_of_notMem hy, indicator_of_notMem hy, zero_mul]
      exact hne (hEq.trans h1)
  -- the gradient integrals converge
  refine ⟨fun j => r (j + k₀), fun j => hr _, (tendsto_add_atTop_iff_nat k₀).2 hr0, ?_⟩
  have hcB4 : closedBall (0 : Rn n) 1 ⊆ ball 0 4 := closedBall_subset_ball (by norm_num)
  have hlim := Regular.tendsto_integral_inner_gradient_bump (L := C)
    (fun j y hy => (hw j).norm_gradient_le (hcB4 hy))
    (fun y _ => Kernel.norm_gradient_le_of_lipschitz hLip y)
    (tendsto_setIntegral_norm_gradient_sub_sq (fun j => (hw j).isLipHarmonicPos)
      (fun j => (hw j).lipschitzOnWith) hconv' (isCompact_closedBall 0 1) hcB4)
  convert hlim using 2
  rw [hu₀]
  have hae2 : (fun z => ⟪gradient (fun z => 1 * max ⟪z, e⟫ 0) z, gradient Regular.bump z⟫)
      =ᵐ[volume] {z : Rn n | ⟪z, v⟫ < 0}.indicator (fun z => -⟪gradient Regular.bump z, v⟫) := by
    filter_upwards [Regular.ae_inner_ne_zero (show e ≠ 0 by rw [← norm_ne_zero_iff, he]; norm_num)]
      with z hz
    rcases hz.lt_or_gt with hneg | hpos
    · rw [Regular.gradient_mul_max_of_neg 1 hneg, inner_zero_left,
        indicator_of_notMem (show z ∉ {z : Rn n | ⟪z, v⟫ < 0} by
          simp only [mem_ofPred_eq, not_lt]; rw [hve] at hneg; linarith)]
    · rw [Regular.gradient_mul_max_of_pos 1 hpos, one_smul,
        indicator_of_mem (show z ∈ {z : Rn n | ⟪z, v⟫ < 0} by
          simp only [mem_ofPred_eq]; rw [hve] at hpos; linarith),
        hedef, inner_neg_left, real_inner_comm]
  rw [integral_congr_ae hae2, integral_indicator hHm, integral_neg, Regular.halfSpaceFlux]

/-! ### Corollary 8.4 -/

/-- The Laplacian measure agrees with `ℋ^{n-1}⌊(Ω ∩ ∂{u > 0})` once it is absolutely
continuous with respect to it (step 3 of the module docstring). -/
theorem eq_hausdorffN_of_absolutelyContinuous [NeZero n] (hn : 2 ≤ n)
    (h : IsVariationalSolution Ω C u χ) (hS : sigmaH Ω u χ = ∅) {ρ : Measure (Rn n)}
    (hρ : HasDistribLaplacianOn Ω u ρ)
    (hac : ρ ≪ (hausdorffN n (n - 1)).restrict (Ω ∩ frontier {y | 0 < u y})) :
    ρ = (hausdorffN n (n - 1)).restrict (Ω ∩ frontier {y | 0 < u y}) := by
  set E : Set (Rn n) := Ω ∩ {y | 0 < u y} with hEdef
  set S : Set (Rn n) := Ω ∩ frontier {y | 0 < u y} with hSdef
  set σ := (hausdorffN n (n - 1)).restrict S with hσdef
  have hEm : MeasurableSet E := h.isOpen_pos.measurableSet
  have hSm : MeasurableSet S := h.isOpen.measurableSet.inter isClosed_frontier.measurableSet
  have hSeq : S = Ω ∩ essentialBoundary E := h.inter_frontier_pos_eq hn hS
  -- every Gauss–Green measure of `E` is `σ` (Federer 4.5.6)
  have hpairσ : ∀ μ ν, IsGaussGreenPair Ω E μ ν → μ = σ := fun μ ν hp => by
    rw [Registry.IsGaussGreenPair.eq_hausdorffN_restrict hn h.isOpen hEm hp, hσdef, hSeq]
  obtain ⟨μ₀, ν₀, hpair₀⟩ := h.hasLocallyFinitePerimeter_inter_pos hn hS
  have hσK : ∀ K, IsCompact K → K ⊆ Ω → σ K < ∞ := fun K hK hKΩ => by
    rw [← hpairσ _ _ hpair₀]
    exact hpair₀.lt_top_of_isCompact K hK hKΩ
  have hσΩ : σ Ωᶜ = 0 := by
    rw [hσdef, Measure.restrict_apply h.isOpen.measurableSet.compl,
      show Ωᶜ ∩ S = ∅ from eq_empty_of_forall_notMem fun y hy => hy.1 hy.2.1, measure_empty]
  have hρΩ : ρ Ωᶜ = 0 := hac hσΩ
  have : SigmaFinite σ := Regular.sigmaFinite_of_isCompact h.isOpen hσΩ hσK
  have : SigmaFinite ρ := Regular.sigmaFinite_of_isCompact h.isOpen hρΩ hρ.1
  set θ := ρ.rnDeriv σ with hθdef
  have hθm : Measurable θ := Measure.measurable_rnDeriv ρ σ
  have hρθ : σ.withDensity θ = ρ := Measure.withDensity_rnDeriv_eq ρ σ hac
  have hρint : ∀ g : Rn n → ℝ, ∫ y, g y ∂ρ = ∫ y, g y * (θ y).toReal ∂σ := fun g => by
    rw [← hρθ, integral_withDensity_eq_integral_toReal_smul hθm (Measure.rnDeriv_lt_top ρ σ)]
    congr 1
    funext y
    rw [smul_eq_mul, mul_comm]
  -- the reduced boundary has full `σ`-measure (De Giorgi–Federer structure theorem)
  obtain ⟨-, hnull, -⟩ := Registry.HasLocallyFinitePerimeter.rectifiable_essentialBoundary hn
    h.isOpen hEm ⟨μ₀, ν₀, hpair₀⟩
  rw [← hSeq] at hnull
  have hred : ∀ᵐ x ∂σ, x ∈ reducedBoundary Ω E := by
    rw [ae_iff, hσdef, Measure.restrict_apply' hSm]
    exact measure_mono_null (show {x | x ∉ reducedBoundary Ω E} ∩ S ⊆ S \ reducedBoundary Ω E
      from fun y hy => ⟨hy.2, hy.1⟩) hnull
  have hSmem : ∀ᵐ x ∂σ, x ∈ S := ae_restrict_mem hSm
  obtain ⟨Kσ, hKσ⟩ := h.exists_hausdorffN_closedBall_inter_le hn hS
  have hKσ' : ∀ x r, 0 < r → closedBall x (4 * r) ⊆ Ω →
      σ (closedBall x r) ≤ ENNReal.ofReal (Kσ * r ^ (n - 1)) := fun x r hr hB => by
    rw [hσdef, Measure.restrict_apply isClosed_closedBall.measurableSet]
    exact hKσ x r hr hB
  -- the local claim: `θ = 1` a.e. on every ball `B` with `B̄ ⊆ Ω`
  have hloc : ∀ c R, 0 < R → closedBall c R ⊆ Ω → ∀ᵐ x ∂σ.restrict (ball c R), θ x = 1 := by
    intro c R hR hRΩ
    set σB := σ.restrict (ball c R) with hσBdef
    have : IsFiniteMeasure σB := ⟨by
      rw [hσBdef, Measure.restrict_apply_univ]
      exact (measure_mono ball_subset_closedBall).trans_lt
        (hσK _ (isCompact_closedBall c R) hRΩ)⟩
    set f : Rn n → ℝ := fun y => (θ y).toReal with hfdef
    have hfint : Integrable f σB := by
      refine integrable_toReal_of_lintegral_ne_top hθm.aemeasurable ?_
      rw [hσBdef, Measure.setLIntegral_rnDeriv hac]
      exact ((measure_mono ball_subset_closedBall).trans_lt
        (hρ.1 _ (isCompact_closedBall c R) hRΩ)).ne
    have hleb := (Besicovitch.vitaliFamily σB).ae_tendsto_lintegral_enorm_sub_div
      hfint.locallyIntegrable
    filter_upwards [hleb, ae_restrict_mem measurableSet_ball,
      ae_restrict_of_ae (Measure.rnDeriv_lt_top ρ σ), ae_restrict_of_ae hred,
      ae_restrict_of_ae hSmem] with x hxleb hxB hxθ hxred hxS
    obtain ⟨R', hR', hR'B⟩ : ∃ R', 0 < R' ∧ closedBall x (4 * R') ⊆ ball c R := by
      obtain ⟨ε, hε, hεB⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (isOpen_ball.mem_nhds hxB)
      exact ⟨ε / 4, by positivity, by rw [mul_div_cancel₀ _ (by norm_num : (4 : ℝ) ≠ 0)]; exact hεB⟩
    have hB4Ω : closedBall x (4 * R') ⊆ Ω := hR'B.trans (ball_subset_closedBall.trans hRΩ)
    have hcBR' : closedBall x R' ⊆ ball c R :=
      (closedBall_subset_closedBall (by linarith)).trans hR'B
    -- the Lebesgue point property for `σ`
    have hleb' : Tendsto (fun r => (∫⁻ y in closedBall x r, ‖f y - f x‖ₑ ∂σ) /
        σ (closedBall x r)) (𝓝[>] 0) (𝓝 0) := by
      refine (hxleb.comp (Besicovitch.tendsto_filterAt σB x)).congr' ?_
      filter_upwards [Ioo_mem_nhdsGT hR'] with r hr
      have hsub : closedBall x r ⊆ ball c R :=
        (closedBall_subset_closedBall hr.2.le).trans hcBR'
      simp only [Function.comp_apply, hσBdef,
        Measure.restrict_restrict isClosed_closedBall.measurableSet, inter_eq_left.2 hsub,
        Measure.restrict_apply isClosed_closedBall.measurableSet]
    have hfi : IntegrableOn f (closedBall x R') σ := by
      have := hfint.restrict (s := closedBall x R')
      rwa [hσBdef, Measure.restrict_restrict isClosed_closedBall.measurableSet,
        inter_eq_left.2 hcBR'] at this
    -- the reduced-boundary data at `x`
    obtain ⟨hxΩ, μx, νx, hpx, hposx, v, hv, hlimx⟩ := hxred
    have hμx : μx = σ := hpairσ μx νx hpx
    subst hμx
    have hDG := Regular.hasDensity_symmDiff_halfSpace hn h.isOpen hEm hpx hxΩ hposx hv hlimx
    obtain ⟨r, hr, hr0, hconv⟩ := h.exists_tendsto_integral_inner_gradient_bump hn hS hxS hv hDG
    have hrk : Tendsto r atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.2 ⟨hr0, .of_forall hr⟩
    have hKball : ∀ᶠ s in 𝓝[>] 0, σ (ball x s) ≤ ENNReal.ofReal (Kσ * s ^ (n - 1)) := by
      filter_upwards [Ioo_mem_nhdsGT hR'] with s hs
      exact (measure_mono ball_subset_closedBall).trans (hKσ' x s hs.1
        ((closedBall_subset_closedBall (by linarith [hs.2])).trans hB4Ω))
    have h2 := (Regular.tendsto_integral_scaledBump_of_isGaussGreenPair h.isOpen hEm hpx hxΩ hv
      hlimx hDG hKball).comp hrk
    have h1 : Tendsto (fun k => (r k ^ (n - 1))⁻¹ * ∫ y, Regular.scaledBump x (r k) y * f y ∂σ)
        atTop (𝓝 (Regular.halfSpaceFlux v)) := by
      have hneg := hconv.neg
      rw [neg_neg] at hneg
      refine hneg.congr' ?_
      filter_upwards [hr0.eventually (gt_mem_nhds hR')] with k hk
      have hB' : closedBall x (r k) ⊆ Ω :=
        (closedBall_subset_closedBall (by linarith [hr k])).trans hB4Ω
      rw [← hρint, h.integral_scaledBump_eq hρ (hr k) hB']
      field_simp [(pow_pos (hr k) (n - 1)).ne']
    have hfx := Regular.eq_one_of_tendsto_integral_scaledBump hR'
      (hσK _ (isCompact_closedBall x R')
        ((closedBall_subset_closedBall (by linarith)).trans hB4Ω)) hfi
      (fun s hs => hKσ' x s hs.1 ((closedBall_subset_closedBall (by linarith [hs.2])).trans hB4Ω))
      hleb' hr hr0 (Regular.halfSpaceFlux_pos hv) h1 (h2.congr fun k => rfl)
    exact (ENNReal.toReal_eq_one_iff _).1 hfx
  -- globalize
  have hae : θ =ᵐ[σ] 1 := by
    rw [Filter.EventuallyEq, ae_iff]
    refine measure_mono_null (t := ({x | ¬θ x = 1} ∩ Ω) ∪ Ωᶜ) (fun y hy => ?_)
      (measure_union_null ?_ hσΩ)
    · by_cases hyΩ : y ∈ Ω
      · exact Or.inl ⟨hy, hyΩ⟩
      · exact Or.inr hyΩ
    refine measure_null_of_locally_null _ fun x hx => ?_
    obtain ⟨R, hR, hRΩ⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (h.isOpen.mem_nhds hx.2)
    refine ⟨{x | ¬θ x = 1} ∩ Ω ∩ ball x R, inter_mem_nhdsWithin _ (ball_mem_nhds x hR), ?_⟩
    have := hloc x R hR hRΩ
    rw [ae_iff, Measure.restrict_apply' measurableSet_ball] at this
    exact measure_mono_null (show {x | ¬θ x = 1} ∩ Ω ∩ ball x R ⊆ {x | ¬θ x = 1} ∩ ball x R
      from fun y hy => ⟨hy.1.1, hy.2⟩) this
  rw [← hρθ, withDensity_congr_ae hae, withDensity_one]

/-- **Corollary 8.4**, measure identity. Let `(u, χ)` be a
variational solution on `Ω`, `2 ≤ n`, with `Σ^H = ∅`. Then `Δu = ℋ^{n-1}⌊∂*{u > 0}` in `Ω` in the
sense of distributions. Connectedness of `Ω` (assumed in the paper) is not needed. -/
theorem laplacian_eq_of_sigmaH_empty [NeZero n] (hn : 2 ≤ n) (h : IsVariationalSolution Ω C u χ)
    (hS : sigmaH Ω u χ = ∅) :
    HasDistribLaplacianOn Ω u
      ((hausdorffN n (n - 1)).restrict (reducedBoundary Ω {y | 0 < u y})) := by
  set E : Set (Rn n) := Ω ∩ {y | 0 < u y} with hEdef
  set S : Set (Rn n) := Ω ∩ frontier {y | 0 < u y} with hSdef
  have hEm : MeasurableSet E := h.isOpen_pos.measurableSet
  have hSm : MeasurableSet S := h.isOpen.measurableSet.inter isClosed_frontier.measurableSet
  obtain ⟨ρ, hρΩ, hρ⟩ :=
    Main.exists_hasDistribLaplacianOn h.isOpen h.continuousOn h.weaklySubharmonic
  obtain ⟨μ, ν, hpair⟩ := h.hasLocallyFinitePerimeter_inter_pos hn hS
  have hSeq : S = Ω ∩ essentialBoundary E := h.inter_frontier_pos_eq hn hS
  have hμ : μ = (hausdorffN n (n - 1)).restrict S := by
    rw [Registry.IsGaussGreenPair.eq_hausdorffN_restrict hn h.isOpen hEm hpair, hSeq]
  obtain ⟨hrect, hnull, hsub⟩ :=
    Registry.HasLocallyFinitePerimeter.rectifiable_essentialBoundary hn h.isOpen hEm ⟨μ, ν, hpair⟩
  rw [← hSeq] at hrect hnull
  have hfin : ∀ K, IsCompact K → K ⊆ Ω → hausdorffN n (n - 1) (K ∩ S) < ∞ := by
    intro K hK hKΩ
    have := hpair.lt_top_of_isCompact K hK hKΩ
    rwa [hμ, Measure.restrict_apply hK.isClosed.measurableSet] at this
  obtain ⟨Kρ, hKρ⟩ := h.exists_measure_ball_le hρ
  have hρS : ρ Sᶜ = 0 := h.measure_compl_inter_frontier_eq_zero hρΩ hρ
  have hR12 := Registry.eq_withDensity_upperDensity hn h.isOpen hSm inter_subset_left hrect hfin
    hρS Kρ hKρ
  have hac : ρ ≪ (hausdorffN n (n - 1)).restrict S := by
    rw [hR12]
    exact withDensity_absolutelyContinuous _ _
  have hρσ := h.eq_hausdorffN_of_absolutelyContinuous hn hS hρ hac
  have hσ : (hausdorffN n (n - 1)).restrict S =
      (hausdorffN n (n - 1)).restrict (reducedBoundary Ω {y | 0 < u y}) := by
    rw [← Regular.reducedBoundary_inter h.isOpen]
    refine Measure.restrict_congr_set ?_
    have hRS : reducedBoundary Ω E ⊆ S := fun y hy => by
      rw [hSeq]
      exact ⟨hy.1, hsub hy⟩
    refine (ae_eq_set).2 ⟨?_, ?_⟩
    · exact hnull
    · rw [sdiff_eq_empty.2 hRS, measure_empty]
  rw [← hσ, ← hρσ]
  exact hρ

end IsVariationalSolution

end InnerVariational
