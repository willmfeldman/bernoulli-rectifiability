/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Defs.Calculus
public import InnerVariational.Vendor.Analysis.LocalCompactness
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Data.Real.StarOrdered
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import GMTFoundations.Defs.Calculus
import Mathlib.MeasureTheory.Group.Integral

/-!
# BV compactness in `L¹_loc`

A sequence `χ_n`, uniformly bounded on an open `U ⊆ ℝᵈ` and with locally uniformly bounded total
variation (duality form: `∫ χ_n div ψ ≤ P_K` for `C¹` fields `|ψ| ≤ 1` supported in a compact
`K ⊆ U`), has a subsequence converging in `L¹_loc(U)`.

Proof: for a cut-off `ζ`, `w_n = ζ χ_n` has total variation on `ℝᵈ` at most
`P_{tsupport ζ} + M ‖∇ζ‖_{L¹}` (`div(ζψ) = ζ div ψ + ∇ζ · ψ`), hence
`|∫ (w_n(· + h) - w_n) φ| ≤ |h| TV(w_n)` for `|φ| ≤ 1` (differentiate
`F(t) = ∫ w φ(· - t h)` in `t`), hence `∫ |w_n(· + h) - w_n| ≤ |h| TV(w_n)` by
`L¹`–`L^∞` duality (approximating the sign of the increment by smooth functions clamped to
`[-1, 1]`). Conclude with `exists_tendstoLpLoc_subseq_of_cutoff` for `p = 1`.

## Main results

* `integral_abs_le_of_forall_integral_mul_le`: `L¹`–`L^∞` duality against smooth test functions.
* `integral_abs_comp_add_sub_le_of_TV`: the `L¹` translation estimate.
* `exists_tendstoLpLoc_subseq_of_TV`: BV compactness in `L¹_loc`.

## References

* L. C. Evans and R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised
  edition, CRC Press, 2015, §5.2 (compactness in `BV`).
* L. Ambrosio, N. Fusco and D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, Oxford Univ. Press, 2000, Theorem 3.23.
-/

@[expose] public section

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal ContDiff Gradient

namespace InnerVariational.Vendor.Analysis

variable {d : ℕ}

/-! ### Divergence computations -/

theorem divergence_smul_const {φ : Rn d → ℝ} {x : Rn d} (hφ : DifferentiableAt ℝ φ x) (k : Rn d) :
    divergence (fun y ↦ φ y • k) x = fderiv ℝ φ x k := by
  rw [divergence, fderiv_smul_const hφ k]
  exact LinearMap.trace_smulRight _ _

theorem divergence_smul {ζ : Rn d → ℝ} {ψ : Rn d → Rn d} {x : Rn d} (hζ : DifferentiableAt ℝ ζ x)
    (hψ : DifferentiableAt ℝ ψ x) :
    divergence (fun y ↦ ζ y • ψ y) x = ζ x * divergence ψ x + fderiv ℝ ζ x (ψ x) := by
  rw [divergence, fderiv_fun_smul hζ hψ, ContinuousLinearMap.coe_add, map_add,
    ContinuousLinearMap.coe_smul, map_smul, smul_eq_mul, divergence]
  congr 1
  exact LinearMap.trace_smulRight _ _

theorem continuous_trace_clm :
    Continuous fun L : Rn d →L[ℝ] Rn d ↦ LinearMap.trace ℝ (Rn d) L.toLinearMap :=
  LinearMap.continuous_of_finiteDimensional
    ((LinearMap.trace ℝ (Rn d)).comp (ContinuousLinearMap.coeLM ℝ))

theorem continuous_divergence {ψ : Rn d → Rn d} (hψ : ContDiff ℝ 1 ψ) :
    Continuous (divergence ψ) :=
  continuous_trace_clm.comp (hψ.continuous_fderiv one_ne_zero)

theorem tsupport_divergence_subset (ψ : Rn d → Rn d) : tsupport (divergence ψ) ⊆ tsupport ψ :=
  closure_minimal (fun _ hx ↦ by
    by_contra h'
    exact hx (divergence_eq_zero_of_notMem_tsupport h')) (isClosed_tsupport _)

/-! ### Differentiation of a translated pairing -/

/-- **Differentiation of a translated pairing.** For `w` locally integrable and `φ ∈ C¹_c`,
`t ↦ ∫ w(y) φ(y - t h) dy` has derivative `∫ w(y) (-Dφ(y - t h) h) dy`. -/
theorem hasDerivAt_integral_mul_comp_sub_smul {w : Rn d → ℝ} (hw : LocallyIntegrable w)
    {φ : Rn d → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) (h : Rn d) (t₀ : ℝ) :
    HasDerivAt (fun t : ℝ ↦ ∫ y, w y * φ (y - t • h))
      (∫ y, w y * -(fderiv ℝ φ (y - t₀ • h) h)) t₀ := by
  obtain ⟨C, hC⟩ := (hφ.continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    (hφc.fderiv (𝕜 := ℝ))
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  set S := cthickening (‖h‖ * (|t₀| + 1)) (tsupport φ)
  have hS : IsCompact S := hφc.isCompact.cthickening
  have hmemS : ∀ y (t : ℝ), t ∈ ball t₀ 1 → y - t • h ∈ tsupport φ → y ∈ S := by
    intro y t ht hy
    refine mem_cthickening_of_dist_le y _ _ _ hy ?_
    rw [dist_eq_norm, sub_sub_cancel, norm_smul, Real.norm_eq_abs, mul_comm]
    have h1 := abs_sub_abs_le_abs_sub t t₀
    rw [mem_ball, Real.dist_eq] at ht
    gcongr
    linarith
  have hwS : IntegrableOn w S := hw.integrableOn_isCompact hS
  have hφt : ∀ t : ℝ, Continuous fun y ↦ φ (y - t • h) :=
    fun t ↦ hφ.continuous.comp (continuous_id.sub continuous_const)
  have hφtc : ∀ t : ℝ, HasCompactSupport fun y ↦ φ (y - t • h) :=
    fun t ↦ hφc.comp_homeomorph (Homeomorph.subRight (t • h))
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t y ↦ w y * φ (y - t • h)) (F' := fun t y ↦ w y * -(fderiv ℝ φ (y - t • h) h))
    (bound := S.indicator fun y ↦ ‖w y‖ * (C * ‖h‖)) (ball_mem_nhds t₀ one_pos)
    (Eventually.of_forall fun t ↦
      hw.aestronglyMeasurable.mul (hφt t).aestronglyMeasurable) ?_ ?_ ?_ ?_ ?_).2
  · have := hw.integrable_smul_right_of_hasCompactSupport (hφt t₀) (hφtc t₀)
    simpa only [smul_eq_mul] using this
  · refine hw.aestronglyMeasurable.mul (Continuous.aestronglyMeasurable ?_)
    exact (((hφ.continuous_fderiv one_ne_zero).comp (continuous_id.sub continuous_const)).clm_apply
      continuous_const).neg
  · refine Eventually.of_forall fun y t ht ↦ ?_
    simp only
    by_cases hy : y - t • h ∈ tsupport φ
    · rw [indicator_of_mem (hmemS y t ht hy), norm_mul, norm_neg]
      gcongr
      exact (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr; exact hC _)
    · have h0 : fderiv ℝ φ (y - t • h) = 0 :=
        image_eq_zero_of_notMem_tsupport fun hh ↦ hy (tsupport_fderiv_subset ℝ hh)
      rw [h0]
      simp only [ContinuousLinearMap.zero_apply, neg_zero, mul_zero, norm_zero]
      exact indicator_nonneg (fun _ _ ↦ by positivity) _
  · rw [integrable_indicator_iff hS.measurableSet]
    exact (hwS.norm.mul_const _)
  · refine Eventually.of_forall fun y t _ ↦ ?_
    have h1 : HasDerivAt (fun s : ℝ ↦ y - s • h) (-h) t := by
      simpa using ((hasDerivAt_id t).smul_const h).const_sub y
    have h2 := ((hφ.differentiable one_ne_zero) (y - t • h)).hasFDerivAt.comp_hasDerivAt t h1
    have h3 := h2.const_mul (w y)
    simpa only [Function.comp_def, ContinuousLinearMap.map_neg] using h3

/-- Choice of `δ` for a linear translation modulus `|h| B`. -/
theorem exists_pos_ofReal_mul_le {B : ℝ≥0∞} (hB : B ≠ ⊤) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ r : ℝ, r < δ → ENNReal.ofReal r * B ≤ ε := by
  rcases eq_or_ne ε ⊤ with rfl | hεt
  · exact ⟨1, one_pos, fun _ _ ↦ le_top⟩
  have hεr : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεt
  refine ⟨ε.toReal / (B.toReal + 1), by positivity, fun r hr ↦ ?_⟩
  rcases le_or_gt r 0 with hr0 | hr0
  · rw [ENNReal.ofReal_of_nonpos hr0, zero_mul]; exact zero_le
  rw [← ENNReal.ofReal_toReal hB, ← ENNReal.ofReal_mul hr0.le, ← ENNReal.ofReal_toReal hεt]
  refine ENNReal.ofReal_le_ofReal ?_
  have hB0 : 0 ≤ B.toReal := ENNReal.toReal_nonneg
  have : r * (B.toReal + 1) ≤ ε.toReal := by
    rw [lt_div_iff₀ (by positivity)] at hr; linarith
  nlinarith

/-! ### A smooth clamp -/

/-- A smooth odd clamp `c : ℝ → [-1, 1]` with `c(0) = 0`, `c(±1) = ±1`. -/
noncomputable def clamp (a : ℝ) : ℝ := Real.smoothTransition a - Real.smoothTransition (-a)

theorem contDiff_clamp : ContDiff ℝ ∞ clamp :=
  Real.smoothTransition.contDiff.sub (Real.smoothTransition.contDiff.comp contDiff_neg)

theorem abs_clamp_le (a : ℝ) : |clamp a| ≤ 1 := by
  rcases le_total 0 a with ha | ha
  · rw [clamp, Real.smoothTransition.zero_of_nonpos (x := -a) (by linarith), sub_zero,
      abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact Real.smoothTransition.le_one _
  · rw [clamp, Real.smoothTransition.zero_of_nonpos ha, zero_sub, abs_neg,
      abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact Real.smoothTransition.le_one _

theorem clamp_zero : clamp 0 = 0 := by simp [clamp]

theorem clamp_one : clamp 1 = 1 := by
  simp [clamp, Real.smoothTransition.one_of_one_le le_rfl,
    Real.smoothTransition.zero_of_nonpos (show (-1 : ℝ) ≤ 0 by norm_num)]

theorem clamp_neg_one : clamp (-1) = -1 := by
  simp [clamp, Real.smoothTransition.one_of_one_le le_rfl,
    Real.smoothTransition.zero_of_nonpos (show (-1 : ℝ) ≤ 0 by norm_num)]

theorem exists_lipschitzWith_clamp : ∃ K : NNReal, LipschitzWith K clamp := by
  have hc : Continuous (deriv clamp) :=
    (contDiff_clamp.of_le (by exact_mod_cast le_top) : ContDiff ℝ 1 clamp).continuous_deriv
      le_rfl
  have hcs : HasCompactSupport (deriv clamp) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := (-1 : ℝ)) (b := 1)) fun x hx ↦ ?_
    rw [mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with hx | hx
    · have : clamp =ᶠ[𝓝 x] fun _ ↦ -1 := (gt_mem_nhds hx).mono fun y hy ↦ by
        rw [clamp, Real.smoothTransition.zero_of_nonpos (by linarith),
          Real.smoothTransition.one_of_one_le (by linarith)]
        ring
      rw [this.deriv_eq, deriv_const]
    · have : clamp =ᶠ[𝓝 x] fun _ ↦ 1 := (lt_mem_nhds hx).mono fun y hy ↦ by
        rw [clamp, Real.smoothTransition.one_of_one_le (by linarith),
          Real.smoothTransition.zero_of_nonpos (by linarith)]
        ring
      rw [this.deriv_eq, deriv_const]
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hcs
  refine ⟨C.toNNReal, lipschitzWith_of_nnnorm_deriv_le
    (contDiff_clamp.differentiable (by simp)) fun x ↦ ?_⟩
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal']
  exact (hC x).trans (le_max_left _ _)

/-! ### `L¹`–`L^∞` duality -/

/-- **`L¹`–`L^∞` duality against smooth test functions.** If `g` is bounded, vanishes off a
compact set, and `∫ g φ ≤ A` for all `φ ∈ C^∞_c` with `|φ| ≤ 1`, then `∫ |g| ≤ A`. -/
theorem integral_abs_le_of_forall_integral_mul_le {g : Rn d → ℝ}
    (hg : AEStronglyMeasurable g volume) {S : Set (Rn d)} (hS : IsCompact S)
    (hgS : ∀ x ∉ S, g x = 0) {Mg : ℝ} (hMg : ∀ x, |g x| ≤ Mg) {A : ℝ}
    (hA : ∀ φ : Rn d → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → (∀ x, |φ x| ≤ 1) →
      ∫ x, g x * φ x ≤ A) :
    ∫ x, |g x| ≤ A := by
  have hMg0 : 0 ≤ Mg := (abs_nonneg _).trans (hMg 0)
  haveI : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.2 hS.measure_lt_top.ne
  have hgi : Integrable g volume := by
    have h1 : IntegrableOn g S := Measure.integrableOn_of_bounded hS.measure_lt_top.ne
      hg (Eventually.of_forall fun x ↦ (Real.norm_eq_abs _).symm ▸ hMg x)
    exact h1.integrable_of_forall_notMem_eq_zero hgS
  -- a measurable sign of `g`, cut off to `S`
  set gm := hg.mk g
  have hgm : Measurable gm := hg.stronglyMeasurable_mk.measurable
  set s0 : Rn d → ℝ := fun x ↦ if 0 ≤ gm x then 1 else -1 with hs0
  have hs0m : Measurable s0 :=
    Measurable.ite (measurableSet_le measurable_const hgm) measurable_const measurable_const
  have hs01 : ∀ x, |s0 x| = 1 := fun x ↦ by simp only [hs0]; split_ifs <;> simp
  set s : Rn d → ℝ := S.indicator s0 with hs
  have hsm : Measurable s := hs0m.indicator hS.measurableSet
  have hs1 : ∀ x, |s x| ≤ 1 := fun x ↦ by
    simp only [hs, indicator]; split_ifs
    · exact (hs01 x).le
    · simp
  have hsL1 : MemLp s 1 volume := by
    rw [hs, memLp_indicator_iff_restrict hS.measurableSet]
    exact MemLp.of_bound hs0m.aestronglyMeasurable 1
      (Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs, hs01 x])
  have hgs : ∫ x, g x * s x = ∫ x, |g x| := by
    refine integral_congr_ae ?_
    filter_upwards [hg.ae_eq_mk] with x hx
    simp only [hs, indicator]
    by_cases hxS : x ∈ S
    · rw [if_pos hxS]
      simp only [hs0]
      split_ifs with h
      · rw [mul_one, abs_of_nonneg (by rw [hx]; exact h)]
      · rw [abs_of_neg (by rw [hx]; exact not_le.1 h)]; ring
    · rw [if_neg hxS, hgS x hxS]; simp
  obtain ⟨K, hK⟩ := exists_lipschitzWith_clamp
  have hcs : ∀ x, clamp (s x) = s x := fun x ↦ by
    simp only [hs, indicator, hs0]; split_ifs <;> simp [clamp_zero, clamp_one, clamp_neg_one]
  rw [← hgs]
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  set η := ε / ((Mg + 1) * (K + 1))
  have hη : 0 < η := by positivity
  obtain ⟨φ₀, hφ₀c, hφ₀, hφ₀s⟩ := hsL1.exist_eLpNorm_sub_le (by norm_num) le_rfl hη
  set φ : Rn d → ℝ := fun x ↦ clamp (φ₀ x)
  have hφ : ContDiff ℝ ∞ φ := contDiff_clamp.comp hφ₀
  have hφc : HasCompactSupport φ := hφ₀c.comp_left clamp_zero
  have hφ1 : ∀ x, |φ x| ≤ 1 := fun x ↦ abs_clamp_le _
  have hφi : Integrable φ volume := hφ.continuous.integrable_of_hasCompactSupport hφc
  have hsφ : Integrable (s - φ₀) volume :=
    memLp_one_iff_integrable.1 (hsL1.sub (hφ₀.continuous.memLp_of_hasCompactSupport hφ₀c))
  have hsφr : ∫ x, |s x - φ₀ x| ≤ η := by
    have h1 := hφ₀s
    rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm hsφ] at h1
    simpa [Real.norm_eq_abs] using (ENNReal.ofReal_le_ofReal_iff hη.le).1 h1
  have hgsi : Integrable (fun x ↦ g x * s x) volume :=
    hgi.mul_bdd (c := 1) hsm.aestronglyMeasurable
      (Eventually.of_forall fun x ↦ (Real.norm_eq_abs _).symm ▸ hs1 x)
  have hgφi : Integrable (fun x ↦ g x * φ x) volume :=
    hgi.mul_bdd (c := 1) hφ.continuous.aestronglyMeasurable
      (Eventually.of_forall fun x ↦ (Real.norm_eq_abs _).symm ▸ hφ1 x)
  have hdiff : (∫ x, g x * s x) - ∫ x, g x * φ x ≤ Mg * (K * η) := by
    rw [← integral_sub hgsi hgφi]
    calc ∫ x, (g x * s x - g x * φ x)
        ≤ ∫ x, Mg * (K * |s x - φ₀ x|) := by
          refine integral_mono (hgsi.sub hgφi)
            ((hsφ.abs.const_mul K).const_mul Mg) fun x ↦ ?_
          have hL : |s x - φ x| ≤ K * |s x - φ₀ x| := by
            have := hK.dist_le_mul (s x) (φ₀ x)
            simpa [Real.dist_eq, hcs x, φ] using this
          calc g x * s x - g x * φ x ≤ |g x| * |s x - φ x| := by
                rw [← mul_sub, ← abs_mul]; exact le_abs_self _
            _ ≤ Mg * (K * |s x - φ₀ x|) :=
                mul_le_mul (hMg x) hL (abs_nonneg _) hMg0
      _ = Mg * (K * ∫ x, |s x - φ₀ x|) := by rw [integral_const_mul, integral_const_mul]
      _ ≤ Mg * (K * η) := by gcongr
  have hbound : Mg * (K * η) ≤ ε := by
    have hK0 : (0 : ℝ) ≤ K := K.2
    have : Mg * (K * η) = ε * (Mg * K / ((Mg + 1) * (K + 1))) := by
      simp only [η]; field_simp
    rw [this]
    refine mul_le_of_le_one_right hε.le ?_
    rw [div_le_one (by positivity)]
    nlinarith
  have := hA φ hφ hφc hφ1
  linarith

/-! ### The `L¹` translation estimate from the total variation -/

/-- **Pairing bound from the total variation.** If `∫ w div ψ ≤ P` for all `C¹_c` fields with
`|ψ| ≤ 1`, then `|∫ (w(· + h) - w) φ| ≤ |h| P` for `φ ∈ C¹_c` with `|φ| ≤ 1`. -/
theorem abs_integral_comp_add_sub_mul_le_of_TV {w : Rn d → ℝ} (hw : LocallyIntegrable w volume)
    {P : ℝ} (hTV : ∀ ψ : Rn d → Rn d, ContDiff ℝ 1 ψ → HasCompactSupport ψ → (∀ x, ‖ψ x‖ ≤ 1) →
      ∫ x, w x * divergence ψ x ≤ P)
    (h : Rn d) {φ : Rn d → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (hφ1 : ∀ x, |φ x| ≤ 1) :
    |∫ x, (w (x + h) - w x) * φ x| ≤ ‖h‖ * P := by
  have hP : 0 ≤ P := by
    have := hTV 0 contDiff_const HasCompactSupport.zero (fun _ ↦ by simp)
    simpa [divergence] using this
  have hφt : ∀ t : ℝ, Continuous fun y ↦ φ (y - t • h) :=
    fun t ↦ hφ.continuous.comp (continuous_id.sub continuous_const)
  have hφtc : ∀ t : ℝ, HasCompactSupport fun y ↦ φ (y - t • h) :=
    fun t ↦ hφc.comp_homeomorph (Homeomorph.subRight (t • h))
  have hint : ∀ t : ℝ, Integrable (fun y ↦ w y * φ (y - t • h)) volume := fun t ↦ by
    simpa only [smul_eq_mul] using hw.integrable_smul_right_of_hasCompactSupport (hφt t) (hφtc t)
  set F : ℝ → ℝ := fun t ↦ ∫ y, w y * φ (y - t • h) with hF
  have hpair : ∫ x, (w (x + h) - w x) * φ x = F 1 - F 0 := by
    have i1 : Integrable (fun x ↦ w (x + h) * φ x) volume := by
      have := (hint 1).comp_add_right h
      simpa only [one_smul, add_sub_cancel_right] using this
    have i2 : Integrable (fun x ↦ w x * φ x) volume := by
      simpa only [zero_smul, sub_zero] using hint 0
    have e1 : ∫ x, w (x + h) * φ x = ∫ y, w y * φ (y - h) := by
      rw [← integral_sub_right_eq_self (fun x ↦ w (x + h) * φ x) h]
      simp only [sub_add_cancel]
    simp only [hF, one_smul, zero_smul, sub_zero, sub_mul]
    rw [integral_sub i1 i2, e1]
  -- `|∫ w Dφ(· - t h) k| ≤ P` for unit `k`
  have hunit : ∀ t : ℝ, ∀ k : Rn d, ‖k‖ ≤ 1 →
      ∫ y, w y * fderiv ℝ φ (y - t • h) k ≤ P := by
    intro t k hk
    have hψ : ContDiff ℝ 1 fun y ↦ φ (y - t • h) • k :=
      (hφ.comp (contDiff_id.sub contDiff_const)).smul contDiff_const
    have hψc : HasCompactSupport fun y ↦ φ (y - t • h) • k := (hφtc t).smul_right
    have hψ1 : ∀ y, ‖φ (y - t • h) • k‖ ≤ 1 := fun y ↦ by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_one₀ (hφ1 _) (norm_nonneg _) hk
    have := hTV _ hψ hψc hψ1
    convert this using 3 with y
    rw [divergence_smul_const, fderiv_comp_sub]
    exact ((hφ.comp (contDiff_id.sub contDiff_const)).differentiable one_ne_zero) y
  have hderiv : ∀ t : ℝ, HasDerivAt F (∫ y, w y * -(fderiv ℝ φ (y - t • h) h)) t :=
    hasDerivAt_integral_mul_comp_sub_smul hw hφ hφc h
  have hbound : ∀ t : ℝ, ‖∫ y, w y * -(fderiv ℝ φ (y - t • h) h)‖ ≤ ‖h‖ * P := by
    intro t
    rcases eq_or_ne h 0 with rfl | hh
    · simp
    set k : Rn d := ‖h‖⁻¹ • h
    have hk : ‖k‖ ≤ 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hh)]
    have hk' : ‖-k‖ ≤ 1 := by rwa [norm_neg]
    have hhk : ∀ y, fderiv ℝ φ (y - t • h) h = ‖h‖ * fderiv ℝ φ (y - t • h) k := fun y ↦ by
      rw [show k = ‖h‖⁻¹ • h from rfl, map_smul, smul_eq_mul, ← mul_assoc,
        mul_inv_cancel₀ (norm_ne_zero_iff.2 hh), one_mul]
    have e : ∫ y, w y * -(fderiv ℝ φ (y - t • h) h) =
        -(‖h‖ * ∫ y, w y * fderiv ℝ φ (y - t • h) k) := by
      rw [← integral_const_mul, ← integral_neg]
      congr 1; funext y; rw [hhk]; ring
    have h1 := hunit t k hk
    have h2 := hunit t (-k) hk'
    simp only [map_neg, mul_neg, integral_neg] at h2
    rw [e, norm_neg, norm_mul, norm_norm, Real.norm_eq_abs]
    gcongr
    exact abs_le.2 ⟨by linarith, h1⟩
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' (f := F) (a := 0) (b := 1)
    (fun t _ ↦ (hderiv t).hasDerivWithinAt) (fun t _ ↦ hbound t) 1 (by simp)
  rw [hpair, ← Real.norm_eq_abs]
  simpa using hmvt

/-- **`L¹` translation estimate from the total variation.** For `w` bounded, vanishing off a
compact set, with `∫ w div ψ ≤ P` for all `C¹_c` fields `|ψ| ≤ 1`:
`∫ |w(· + h) - w| ≤ |h| P`. -/
theorem integral_abs_comp_add_sub_le_of_TV {w : Rn d → ℝ} (hwm : AEStronglyMeasurable w volume)
    {T : Set (Rn d)} (hT : IsCompact T) (hwT : ∀ x ∉ T, w x = 0) {Mw : ℝ}
    (hMw : ∀ x, |w x| ≤ Mw) {P : ℝ}
    (hTV : ∀ ψ : Rn d → Rn d, ContDiff ℝ 1 ψ → HasCompactSupport ψ → (∀ x, ‖ψ x‖ ≤ 1) →
      ∫ x, w x * divergence ψ x ≤ P) (h : Rn d) :
    ∫ x, |w (x + h) - w x| ≤ ‖h‖ * P := by
  have hwi : Integrable w volume := by
    have h1 : IntegrableOn w T := Measure.integrableOn_of_bounded hT.measure_lt_top.ne
      hwm (Eventually.of_forall fun x ↦ (Real.norm_eq_abs _).symm ▸ hMw x)
    exact h1.integrable_of_forall_notMem_eq_zero hwT
  have hwl : LocallyIntegrable w volume := hwi.locallyIntegrable
  set S := ((fun x ↦ x - h) '' T) ∪ T
  have hS : IsCompact S := (hT.image (continuous_sub_right h)).union hT
  refine integral_abs_le_of_forall_integral_mul_le (S := S)
    ((hwm.comp_measurePreserving (measurePreserving_add_right volume h)).sub hwm) hS
    (fun x hx ↦ ?_) (Mg := 2 * Mw) (fun x ↦ ?_) (fun φ hφ hφc hφ1 ↦ ?_)
  · have hx1 : x + h ∉ T := fun hxT ↦ hx (Or.inl ⟨x + h, hxT, add_sub_cancel_right x h⟩)
    have hx2 : x ∉ T := fun hxT ↦ hx (Or.inr hxT)
    simp [hwT _ hx1, hwT _ hx2]
  · calc |w (x + h) - w x| ≤ |w (x + h)| + |w x| := abs_sub _ _
      _ ≤ 2 * Mw := by linarith [hMw (x + h), hMw x]
  · exact (le_abs_self _).trans (abs_integral_comp_add_sub_mul_le_of_TV hwl hTV h
      (hφ.of_le (by exact_mod_cast le_top)) hφc hφ1)

/-! ### BV compactness -/

theorem eLpNorm_one_eq_ofReal_integral_abs {g : Rn d → ℝ} (hg : Integrable g volume) :
    eLpNorm g 1 volume = ENNReal.ofReal (∫ x, |g x|) := by
  rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm hg]
  rfl

/-- A function bounded on a compact `T`, a.e.-strongly measurable there, times a continuous
function vanishing off `T`, is integrable. -/
theorem integrable_mul_of_restrict {T : Set (Rn d)} (hT : IsCompact T) {χ c : Rn d → ℝ}
    (hχ : AEStronglyMeasurable χ (volume.restrict T)) {M : ℝ} (hχb : ∀ x ∈ T, |χ x| ≤ M)
    (hc : Continuous c) (hc0 : ∀ x ∉ T, c x = 0) : Integrable (fun x ↦ χ x * c x) volume := by
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support (HasCompactSupport.intro hT hc0)
  have h1 : IntegrableOn (fun x ↦ χ x * c x) T := by
    refine ⟨hχ.mul hc.aestronglyMeasurable.restrict,
      .restrict_of_bounded (C := M * C) hT.measure_lt_top ?_⟩
    filter_upwards [ae_restrict_mem hT.measurableSet] with x hx
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul (hχb x hx) (hC x) (norm_nonneg _) ((abs_nonneg _).trans (hχb x hx))
  exact h1.integrable_of_forall_notMem_eq_zero fun x hx ↦ by rw [hc0 x hx, mul_zero]

/-- **BV compactness in `L¹_loc`** (used through `Registry/BV.lean`). The total variation
bound is in duality form, on each compact `K ⊆ U`: `∫ χ_n div ψ ≤ P_K` for all `C¹` fields `ψ`
supported in `K` with `|ψ| ≤ 1`. -/
theorem exists_tendstoLpLoc_subseq_of_TV {U : Set (Rn d)} (hU : IsOpen U) (χ : ℕ → Rn d → ℝ)
    (hmeas : ∀ n, AEStronglyMeasurable (χ n) (volume.restrict U))
    (hbdd : ∃ M : ℝ, ∀ n, ∀ x ∈ U, |χ n x| ≤ M)
    (hTV : ∀ K, IsCompact K → K ⊆ U → ∃ P : ℝ, ∀ n, ∀ ψ : Rn d → Rn d, ContDiff ℝ 1 ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ K → (∀ x, ‖ψ x‖ ≤ 1) →
        ∫ x, χ n x * divergence ψ x ≤ P) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ χ₀ : Rn d → ℝ, Measurable χ₀ ∧
      ∀ K ⊆ U, IsCompact K →
        Tendsto (fun n ↦ eLpNorm (χ (φ n) - χ₀) 1 (volume.restrict K)) atTop (𝓝 0) := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ 1) := ⟨le_rfl⟩
  obtain ⟨M₁, hM₁⟩ := hbdd
  set M := max M₁ 0
  have hM : ∀ n, ∀ x ∈ U, |χ n x| ≤ M := fun n x hx ↦ (hM₁ n x hx).trans (le_max_left _ _)
  refine exists_tendstoLpLoc_subseq_of_cutoff ENNReal.one_ne_top hU χ ?_
  intro ζ hζ hζc hζU hζ01
  set T := tsupport ζ
  have hT : IsCompact T := hζc
  have hTm : MeasurableSet T := hT.measurableSet
  obtain ⟨P, hP⟩ := hTV T hT hζU
  have hζ1 : ContDiff ℝ 1 ζ := hζ.of_le (by exact_mod_cast le_top)
  obtain ⟨Z, hZ⟩ := (hζ1.continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    (hζc.fderiv (𝕜 := ℝ))
  have hZ0 : 0 ≤ Z := (norm_nonneg _).trans (hZ 0)
  have hζ0 : ∀ x ∉ T, ζ x = 0 := fun x hx ↦ image_eq_zero_of_notMem_tsupport hx
  have hχT : ∀ n, AEStronglyMeasurable (χ n) (volume.restrict T) :=
    fun n ↦ (hmeas n).mono_measure (Measure.restrict_mono hζU le_rfl)
  have hχb : ∀ n, ∀ x ∈ T, |χ n x| ≤ M := fun n x hx ↦ hM n x (hζU hx)
  set w : ℕ → Rn d → ℝ := fun n x ↦ ζ x * χ n x with hw
  have hwT : ∀ n, ∀ x ∉ T, w n x = 0 := fun n x hx ↦ by simp [hw, hζ0 x hx]
  have hwb : ∀ n x, |w n x| ≤ M := fun n x ↦ by
    by_cases hx : x ∈ T
    · rw [hw, abs_mul, abs_of_nonneg (hζ01 x).1]
      calc ζ x * |χ n x| ≤ 1 * M :=
            mul_le_mul (hζ01 x).2 (hχb n x hx) (abs_nonneg _) zero_le_one
        _ = M := one_mul M
    · rw [hwT n x hx, abs_zero]; exact le_max_right _ _
  have hwi : ∀ n, Integrable (w n) volume := fun n ↦ by
    have := integrable_mul_of_restrict hT (hχT n) (hχb n) hζ.continuous hζ0
    simpa only [hw, mul_comm] using this
  -- total variation of `w n` on the whole space
  set B : ℝ := max P 0 + M * Z * volume.real T
  have hwTV : ∀ n, ∀ ψ : Rn d → Rn d, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      (∀ x, ‖ψ x‖ ≤ 1) → ∫ x, w n x * divergence ψ x ≤ B := by
    intro n ψ hψ hψc hψ1
    set ζψ : Rn d → Rn d := fun y ↦ ζ y • ψ y
    have hζψ : ContDiff ℝ 1 ζψ := hζ1.smul hψ
    have hζψT : tsupport ζψ ⊆ T := tsupport_smul_subset_left _ _
    have hdiv : ∀ x, w n x * divergence ψ x =
        χ n x * divergence ζψ x - χ n x * fderiv ℝ ζ x (ψ x) := fun x ↦ by
      rw [divergence_smul (hζ1.differentiable one_ne_zero x)
        (hψ.differentiable one_ne_zero x)]
      simp only [hw]; ring
    have hdiv0 : ∀ x ∉ T, divergence ζψ x = 0 := fun x hx ↦
      image_eq_zero_of_notMem_tsupport fun h ↦ hx (hζψT (tsupport_divergence_subset ζψ h))
    have hDζ0 : ∀ x ∉ T, fderiv ℝ ζ x (ψ x) = 0 := fun x hx ↦ by
      rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hx (tsupport_fderiv_subset ℝ h))]; rfl
    have hcDζ : Continuous fun x ↦ fderiv ℝ ζ x (ψ x) :=
      (hζ1.continuous_fderiv one_ne_zero).clm_apply hψ.continuous
    have i1 := integrable_mul_of_restrict hT (hχT n) (hχb n) (continuous_divergence hζψ) hdiv0
    have i2 := integrable_mul_of_restrict hT (hχT n) (hχb n) hcDζ hDζ0
    simp_rw [hdiv]
    rw [integral_sub i1 i2]
    -- the first term is bounded by the total variation on `T`
    have hfirst : ∫ x, χ n x * divergence ζψ x ≤ max P 0 := by
      refine (hP n ζψ hζψ hζc.smul_right hζψT fun x ↦ ?_).trans (le_max_left _ _)
      simp only [ζψ, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hζ01 x).1]
      exact mul_le_one₀ (hζ01 x).2 (norm_nonneg _) (hψ1 x)
    -- the second term is bounded by `M Z |T|`
    have hsecond : -∫ x, χ n x * fderiv ℝ ζ x (ψ x) ≤ M * Z * volume.real T := by
      have hb : ∀ x, |χ n x * fderiv ℝ ζ x (ψ x)| ≤ T.indicator (fun _ ↦ M * Z) x := by
        intro x
        by_cases hx : x ∈ T
        · rw [indicator_of_mem hx, abs_mul]
          refine mul_le_mul (hχb n x hx) ?_ (abs_nonneg _) (le_max_right _ _)
          rw [← Real.norm_eq_abs]
          calc ‖fderiv ℝ ζ x (ψ x)‖ ≤ ‖fderiv ℝ ζ x‖ * ‖ψ x‖ :=
                ContinuousLinearMap.le_opNorm _ _
            _ ≤ Z * 1 := mul_le_mul (hZ x) (hψ1 x) (norm_nonneg _) hZ0
            _ = Z := mul_one Z
        · rw [indicator_of_notMem hx, hDζ0 x hx, mul_zero, abs_zero]
      calc -∫ x, χ n x * fderiv ℝ ζ x (ψ x)
          ≤ |∫ x, χ n x * fderiv ℝ ζ x (ψ x)| := neg_le_abs _
        _ ≤ ∫ x, |χ n x * fderiv ℝ ζ x (ψ x)| := abs_integral_le_integral_abs
        _ ≤ ∫ x, T.indicator (fun _ ↦ M * Z) x :=
            integral_mono i2.abs
              ((integrable_indicator_iff hTm).2 (integrableOn_const hT.measure_lt_top.ne)) hb
        _ = M * Z * volume.real T := by
            rw [integral_indicator_const _ hTm, smul_eq_mul, mul_comm]
    linarith
  refine ⟨fun n ↦ memLp_one_iff_integrable.2 (hwi n),
    ⟨ENNReal.ofReal (M * volume.real T), ENNReal.ofReal_ne_top, fun n ↦ ?_⟩, fun ε hε ↦ ?_⟩
  · rw [eLpNorm_one_eq_ofReal_integral_abs (hwi n)]
    refine ENNReal.ofReal_le_ofReal ?_
    calc ∫ x, |w n x| ≤ ∫ x, T.indicator (fun _ ↦ M) x :=
          integral_mono (hwi n).abs
            ((integrable_indicator_iff hTm).2 (integrableOn_const hT.measure_lt_top.ne)) fun x ↦ by
            by_cases hx : x ∈ T
            · rw [indicator_of_mem hx]; exact hwb n x
            · rw [indicator_of_notMem hx, hwT n x hx, abs_zero]
      _ = M * volume.real T := by rw [integral_indicator_const _ hTm, smul_eq_mul, mul_comm]
  · obtain ⟨ρ, hρ, hρε⟩ := exists_pos_ofReal_mul_le (B := ENNReal.ofReal B)
      ENNReal.ofReal_ne_top hε
    refine ⟨ρ, hρ, fun n h hh ↦ ?_⟩
    have hint : Integrable (fun x ↦ w n (x + h) - w n x) volume :=
      ((hwi n).comp_add_right h).sub (hwi n)
    have hest := integral_abs_comp_add_sub_le_of_TV (hwi n).aestronglyMeasurable hT (hwT n)
      (hwb n) (hwTV n) h
    have hB0 : 0 ≤ B := by
      have := hwTV n 0 contDiff_const HasCompactSupport.zero (fun _ ↦ by simp)
      simpa [divergence] using this
    calc eLpNorm (fun x ↦ ζ (x + h) * χ n (x + h) - ζ x * χ n x) 1 volume
        = ENNReal.ofReal (∫ x, |w n (x + h) - w n x|) :=
          eLpNorm_one_eq_ofReal_integral_abs hint
      _ ≤ ENNReal.ofReal (‖h‖ * B) := ENNReal.ofReal_le_ofReal hest
      _ = ENNReal.ofReal ‖h‖ * ENNReal.ofReal B := ENNReal.ofReal_mul (norm_nonneg _)
      _ ≤ ε := hρε _ hh

end InnerVariational.Vendor.Analysis
