/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Kernel.Harmonic
public import InnerVariational.Defs.VariationalSolution
public import InnerVariational.Kernel.VariationalQ
import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import InnerVariational.Kernel.IBP
import InnerVariational.Registry.Sobolev

/-!
# Proposition 3.2: variational solutions are harmonic on `{u > 0}` and subharmonic

Kriventsov–Weiss, Proposition 3.2 (full reference below): a variational solution
`(u, χ)` on `Ω` is harmonic on `Ω ∩ {u > 0}` and subharmonic on `Ω`.

## Main results

* `IsVariationalSolutionQ.harmonicOn_pos`: `u` is harmonic at every `x ∈ Ω` with `u x > 0`.
* `IsVariationalSolutionQ.isLipHarmonicPos`: `(u, Ω)` satisfies `IsLipHarmonicPos`.
* `IsVariationalSolutionQ.weaklySubharmonic`, `IsVariationalSolutionQ.weaklySubharmonic_sq`:
  `u` and `u²` are weakly subharmonic on `Ω`.

The results are proved for a Lipschitz coefficient `Q` with `0 < c ≤ Q ≤ C` (`QBounds`); the
statements for `IsVariationalSolution` (the coefficient `Q ≡ 1`) are their specializations.

## Proof

We follow the paper. For `φ ∈ C^∞_c(Ω ∩ {u > 0})` and a fixed vector `e`, test the inner variation
with `ξ = φ e`. Since `χ = 1` a.e. on `{u > 0}`, the quadratic part
`∫ (|∇u|² div ξ − 2 ∇u · Dξ ∇u)` of the inner variation vanishes
(`IsVariationalSolutionQ.integral_gradVariation_eq_zero_of_pos`: the remaining terms form
`∫ div (Q² ξ) = 0`). Integrating by parts (for Lipschitz functions,
`Registry.integral_mul_fderiv_eq_neg`) gives `∫ φ ∂_e u Δu = 0`
(`integral_mul_fderiv_mul_laplacian_eq_zero`). The paper writes this as `∫ ξ·∇u Δu = 0`. Hence
`∂_e u Δu = 0` on `{u > 0}` by the fundamental lemma of the calculus of variations and continuity.
On the open set `{Δu ≠ 0} ∩ {u > 0}` this forces `∇u = 0`, hence `D²u = 0` and `Δu = 0`, so that set
is empty. The paper argues through the closure of `{∇u ≠ 0}`; the two arguments are the same.
Subharmonicity is proved for any `IsLipHarmonicPos` function in `Kernel/Harmonic.lean`. The paper
proves it "in the viscosity sense"; we prove the distributional statement `IsWeaklySubharmonicOn`
directly.

## References

* D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
  DOI 10.1002/cpa.22226; arXiv:2306.10131. Result and equation numbers refer to arXiv v2.
-/

open MeasureTheory Metric Set Filter Topology Laplacian InnerProductSpace
open scoped NNReal ENNReal ContDiff RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

namespace Kernel

/-- A product `φ h` with `φ ∈ C¹`, `h ∈ C¹(V)` and `tsupport φ ⊆ V` is `C¹` on all of `ℝⁿ`. -/
theorem contDiff_mul_of_tsupport {V : Set (Rn n)} (hV : IsOpen V) {φ h : Rn n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hh : ContDiffOn ℝ 1 h V) (hφV : tsupport φ ⊆ V) :
    ContDiff ℝ 1 fun y => φ y * h y := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y ∈ V
  · exact hφ.contDiffAt.mul (hh.contDiffAt (hV.mem_nhds hy))
  · have : (fun y => φ y * h y) =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 (fun h' => hy (hφV h'))] with z hz
      simp only [Pi.zero_apply] at hz
      simp [hz]
    exact contDiffAt_const.congr_of_eventuallyEq this

/-- A function continuous on the open set `V` and vanishing off a compact `K ⊆ V` is
integrable. -/
theorem integrable_of_continuousOn_of_isCompact {V K : Set (Rn n)} (hV : IsOpen V)
    (hK : IsCompact K) (hKV : K ⊆ V) {f : Rn n → ℝ} (hf : ContinuousOn f V)
    (h0 : ∀ y ∉ K, f y = 0) : Integrable f := by
  have hts : tsupport f ⊆ K := closure_minimal (fun y hy => by
    by_contra h'; exact hy (h0 y h')) hK.isClosed
  exact (hf.continuous_of_tsupport_subset hV (hts.trans hKV)).integrable_of_hasCompactSupport
    (hK.of_isClosed_subset (isClosed_tsupport f) hts)

theorem continuousOn_gradient {V : Set (Rn n)} (hV : IsOpen V) {u : Rn n → ℝ}
    (hu : ContDiffOn ℝ 1 u V) : ContinuousOn (gradient u) V :=
  (toDual ℝ (Rn n)).symm.continuous.comp_continuousOn
    (hu.continuousOn_fderiv_of_isOpen hV le_rfl)

end Kernel

namespace IsVariationalSolutionQ

variable {Ω : Set (Rn n)} {C : ℝ≥0} {Q u χ : Rn n → ℝ} {L : ℝ≥0} {c C' : ℝ}

/-- The identity `∫ φ ∂_e u Δu = 0` for `φ ∈ C^∞_c(Ω ∩ {u > 0})`. It comes from the inner
variation in the direction `ξ = φ e` (proof of Proposition 3.2). -/
theorem integral_mul_fderiv_mul_laplacian_eq_zero (h : IsVariationalSolutionQ Ω C Q u χ)
    (hQ : QBounds Ω Q L c C')
    {φ : Rn n → ℝ} (hφ : IsTestFunction (Ω ∩ {x | 0 < u x}) φ) (e : Rn n) :
    ∫ y, φ y * (fderiv ℝ u y e * Δ u y) = 0 := by
  set V := Ω ∩ {x | 0 < u x}
  have hV : IsOpen V := h.isOpen_pos
  have hu : ContDiffOn ℝ 2 u V := h.contDiffOn
  have hu1 : ContDiffOn ℝ 1 u V := hu.of_le (by norm_num)
  obtain ⟨hφs, hφc, hφV⟩ := hφ
  set K := tsupport φ
  have hK : IsCompact K := hφc
  have hφ0 : ∀ y ∉ K, φ y = 0 := fun y hy => image_eq_zero_of_notMem_tsupport hy
  have hdφ0 : ∀ y ∉ K, fderiv ℝ φ y = 0 := fun y hy => Kernel.fderiv_eq_zero_of_notMem_tsupport hy
  have hφd : ∀ y, DifferentiableAt ℝ φ y := fun y => hφs.differentiable (by simp) y
  have hφ1 : ContDiff ℝ 1 φ := hφs.of_le (by simp)
  have hdφc : Continuous (fderiv ℝ φ) := hφs.continuous_fderiv (by simp)
  -- the test field `ξ = φ e`
  set ξ : Rn n → Rn n := fun y => φ y • e with hξ
  have hξV : IsLipTestField V ξ :=
    IsSmoothTestField.isLipTestField ⟨hφs.smul contDiff_const, hφc.smul_right,
      (tsupport_smul_subset_left φ fun _ => e).trans hφV⟩
  have hDξ : ∀ y, fderiv ℝ ξ y = (fderiv ℝ φ y).smulRight e := fun y => fderiv_smul_const (hφd y) e
  have hdiv : ∀ y, divergence ξ y = fderiv ℝ φ y e := by
    intro y
    rw [divergence, hDξ, ContinuousLinearMap.coe_smulRight, LinearMap.trace_smulRight]
    rfl
  -- auxiliary functions
  set pe : Rn n → ℝ := fun z => fderiv ℝ u z e with hpe
  have hpe1 : ContDiffOn ℝ 1 pe V := Kernel.contDiffOn_fderiv_apply hV hu e
  set q : Rn n → ℝ := fun z => ‖gradient u z‖ ^ 2 with hq
  set b := Kernel.stdBasis n
  have hq_eq : q = fun z => ∑ i, fderiv ℝ u z (b i) ^ 2 :=
    funext fun z => Kernel.norm_gradient_sq_eq_sum u z
  have hq1 : ContDiffOn ℝ 1 q V := by
    rw [hq_eq]
    exact ContDiffOn.sum fun i _ => (Kernel.contDiffOn_fderiv_apply hV hu (b i)).pow 2
  set g : Rn n → ℝ := fun y => φ y * pe y with hg
  have hg1 : ContDiff ℝ 1 g := Kernel.contDiff_mul_of_tsupport hV hφ1 hpe1 hφV
  have hgc : HasCompactSupport g := hφc.mul_right
  have hgK : tsupport g ⊆ K := tsupport_mul_subset_left
  have hgL : ∃ C, LipschitzWith C g := hg1.lipschitzWith_of_hasCompactSupport hgc one_ne_zero
  have hint : ∀ f : Rn n → ℝ, ContinuousOn f V → (∀ y ∉ K, f y = 0) → Integrable f :=
    fun f hf h0 => Kernel.integrable_of_continuousOn_of_isCompact hV hK hφV hf h0
  have hgradu : ContinuousOn (gradient u) V := Kernel.continuousOn_gradient hV hu1
  -- step 1: the quadratic part of the inner variation along `ξ` vanishes
  have hIV : ∫ y, (q y * fderiv ℝ φ y e - 2 * (fderiv ℝ φ y (gradient u y) * pe y)) = 0 := by
    rw [← h.integral_gradVariation_eq_zero_of_pos hQ hξV]
    refine integral_congr_ae (.of_forall fun y => ?_)
    simp only [Kernel.gradVariation, hdiv, hDξ, ContinuousLinearMap.smulRight_apply,
      real_inner_smul_right, Kernel.inner_gradient_left, hq, hpe]
  -- step 2: the pointwise identity on `V`
  have hD : ∀ y ∈ V, fderiv ℝ q y e = 2 * fderiv ℝ (fderiv ℝ u) y e (gradient u y) := by
    intro y hy
    have hdu := Kernel.differentiableAt_fderiv_of_contDiffOn hV hu hy
    have hpi : ∀ i, HasFDerivAt (fun z => fderiv ℝ u z (b i))
        (fderiv ℝ (fun z => fderiv ℝ u z (b i)) y) y := fun i =>
      (((Kernel.contDiffOn_fderiv_apply hV hu (b i)).contDiffAt (hV.mem_nhds hy)).differentiableAt
        one_ne_zero).hasFDerivAt
    have hsum := HasFDerivAt.fun_sum (u := Finset.univ) fun i _ => (hpi i).pow 2
    rw [hq_eq, hsum.fderiv]
    simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, Kernel.fderiv_fderiv_apply hdu]
    conv_rhs => rw [Kernel.gradient_eq_sum u y]
    simp only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast
    ring
  have hG : ∀ y ∈ V, ⟪gradient u y, gradient g y⟫ =
      φ y * fderiv ℝ (fderiv ℝ u) y (gradient u y) e + pe y * fderiv ℝ φ y (gradient u y) := by
    intro y hy
    have hdu := Kernel.differentiableAt_fderiv_of_contDiffOn hV hu hy
    have hpd : HasFDerivAt pe (fderiv ℝ pe y) y :=
      ((hpe1.contDiffAt (hV.mem_nhds hy)).differentiableAt one_ne_zero).hasFDerivAt
    have hgd : HasFDerivAt g _ y := (hφd y).hasFDerivAt.mul hpd
    rw [Kernel.inner_gradient_right, hgd.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, hpe]
    rw [Kernel.fderiv_fderiv_apply hdu]
  have hsymm : ∀ y ∈ V, ∀ v w : Rn n,
      fderiv ℝ (fderiv ℝ u) y v w = fderiv ℝ (fderiv ℝ u) y w v := fun y hy =>
    (hu.contDiffAt (hV.mem_nhds hy)).isSymmSndFDerivAt (by simp)
  have hPI : ∀ y, q y * fderiv ℝ φ y e - 2 * (fderiv ℝ φ y (gradient u y) * pe y) =
      (q y * fderiv ℝ φ y e + φ y * fderiv ℝ q y e) - 2 * ⟪gradient u y, gradient g y⟫ := by
    intro y
    by_cases hyK : y ∈ K
    · rw [hD y (hφV hyK), hG y (hφV hyK), hsymm y (hφV hyK) e (gradient u y)]
      ring
    · rw [hdφ0 y hyK, hφ0 y hyK,
        Kernel.gradient_eq_zero_of_notMem_tsupport (fun h' => hyK (hgK h'))]
      simp
  -- step 3: integrate
  have hA1 : Integrable fun y => q y * fderiv ℝ φ y e + φ y * fderiv ℝ q y e :=
    hint _ ((hq1.continuousOn.mul (hdφc.clm_apply continuous_const).continuousOn).add
      (hφs.continuous.continuousOn.mul
        ((hq1.continuousOn_fderiv_of_isOpen hV le_rfl).clm_apply continuousOn_const)))
      (fun y hy => by simp [hdφ0 y hy, hφ0 y hy])
  have hA2 : Integrable fun y => ⟪gradient u y, gradient g y⟫ :=
    hint _ (hgradu.inner ((toDual ℝ (Rn n)).symm.continuous.comp
      (hg1.continuous_fderiv one_ne_zero)).continuousOn)
      (fun y hy => by
        rw [Kernel.gradient_eq_zero_of_notMem_tsupport (fun h' => hy (hgK h')), inner_zero_right])
  have hq0 : ∫ y, (q y * fderiv ℝ φ y e + φ y * fderiv ℝ q y e) = 0 := by
    have := Registry.integral_mul_fderiv_eq_neg hV (Kernel.locallyLipschitzOn_of_contDiffOn hV hq1)
      (hφs.lipschitzWith_of_hasCompactSupport hφc (by simp)) hφc hφV e
    rw [integral_add (f := fun y => q y * fderiv ℝ φ y e) (g := fun y => φ y * fderiv ℝ q y e)
      (hint _ (hq1.continuousOn.mul (hdφc.clm_apply continuous_const).continuousOn)
      (fun y hy => by simp [hdφ0 y hy]))
      (hint _ (hφs.continuous.continuousOn.mul
        ((hq1.continuousOn_fderiv_of_isOpen hV le_rfl).clm_apply continuousOn_const))
      (fun y hy => by simp [hφ0 y hy])), this]
    ring
  have hibp := Kernel.integral_inner_gradient_eq_neg_laplacian hV hu hgL hgc (hgK.trans hφV)
  simp_rw [hPI] at hIV
  rw [integral_sub hA1 (hA2.const_mul 2), integral_const_mul, hq0, hibp] at hIV
  have : ∫ y, g y * Δ u y = 0 := by linarith
  simpa only [hg, mul_assoc] using this

/-- `∂_e u Δu = 0` on `Ω ∩ {u > 0}`. -/
theorem fderiv_mul_laplacian_eq_zero (h : IsVariationalSolutionQ Ω C Q u χ)
    (hQ : QBounds Ω Q L c C') (e : Rn n)
    {y : Rn n} (hy : y ∈ Ω ∩ {x | 0 < u x}) :
    fderiv ℝ u y e * Δ u y = 0 := by
  set V := Ω ∩ {x | 0 < u x}
  have hV : IsOpen V := h.isOpen_pos
  have hu : ContDiffOn ℝ 2 u V := h.contDiffOn
  set b := Kernel.stdBasis n
  have hD2 : ContinuousOn (fderiv ℝ (fderiv ℝ u)) V :=
    (hu.fderiv_of_isOpen hV (m := 1) (by norm_num)).continuousOn_fderiv_of_isOpen hV le_rfl
  have hΔ : ContinuousOn (Δ u) V := by
    have : Δ u = fun y => ∑ i, fderiv ℝ (fderiv ℝ u) y (b i) (b i) :=
      funext fun y => Kernel.laplacian_apply_eq_sum u y
    rw [this]
    exact continuousOn_finsetSum _ fun i _ =>
      (hD2.clm_apply continuousOn_const).clm_apply continuousOn_const
  set f : Rn n → ℝ := fun y => fderiv ℝ u y e * Δ u y
  have hf : ContinuousOn f V :=
    ((Kernel.contDiffOn_fderiv_apply hV hu e).continuousOn).mul hΔ
  have hae := hV.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume)
    (hf.locallyIntegrableOn hV.measurableSet) (fun g hg hgc hgV => by
      simpa only [smul_eq_mul] using
        h.integral_mul_fderiv_mul_laplacian_eq_zero hQ ⟨hg, hgc, hgV⟩ e)
  set W := V ∩ f ⁻¹' {0}ᶜ
  have hW : IsOpen W := hf.isOpen_inter_preimage hV isOpen_compl_singleton
  have hW0 : volume W = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hae] with z hz hzW
    exact hzW.2 (hz hzW.1)
  have hWe : W = ∅ := (hW.measure_eq_zero_iff volume).1 hW0
  by_contra hne
  have : y ∈ W := ⟨hy, hne⟩
  rw [hWe] at this
  exact this

/-- `Δu = 0` on `Ω ∩ {u > 0}` (proof of Proposition 3.2). -/
theorem laplacian_eq_zero (h : IsVariationalSolutionQ Ω C Q u χ)
    (hQ : QBounds Ω Q L c C') {y : Rn n}
    (hy : y ∈ Ω ∩ {x | 0 < u x}) : Δ u y = 0 := by
  set V := Ω ∩ {x | 0 < u x}
  have hV : IsOpen V := h.isOpen_pos
  have hu : ContDiffOn ℝ 2 u V := h.contDiffOn
  have hΔ : ContinuousOn (Δ u) V := by
    have hD2 : ContinuousOn (fderiv ℝ (fderiv ℝ u)) V :=
      (hu.fderiv_of_isOpen hV (m := 1) (by norm_num)).continuousOn_fderiv_of_isOpen hV le_rfl
    have : Δ u = fun y => ∑ i, fderiv ℝ (fderiv ℝ u) y (Kernel.stdBasis n i)
        (Kernel.stdBasis n i) := funext fun y => Kernel.laplacian_apply_eq_sum u y
    rw [this]
    exact continuousOn_finsetSum _ fun i _ =>
      (hD2.clm_apply continuousOn_const).clm_apply continuousOn_const
  by_contra hne
  set W := V ∩ Δ u ⁻¹' {0}ᶜ
  have hW : IsOpen W := hΔ.isOpen_inter_preimage hV isOpen_compl_singleton
  have hyW : y ∈ W := ⟨hy, hne⟩
  -- on `W`, `Du = 0`
  have hDu : fderiv ℝ u =ᶠ[𝓝 y] fun _ => 0 := by
    filter_upwards [hW.mem_nhds hyW] with z hz
    ext e
    have := h.fderiv_mul_laplacian_eq_zero hQ e hz.1
    rw [ContinuousLinearMap.zero_apply]
    exact (mul_eq_zero.1 this).resolve_right hz.2
  have hD2 : fderiv ℝ (fderiv ℝ u) y = 0 := by
    rw [hDu.fderiv_eq]
    simp
  apply hne
  rw [Kernel.laplacian_apply_eq_sum, hD2]
  simp

/-- **Proposition 3.2**: a variational solution is harmonic on `Ω ∩ {u > 0}`. -/
theorem harmonicOn_pos (h : IsVariationalSolutionQ Ω C Q u χ)
    (hQ : QBounds Ω Q L c C') {x : Rn n} (hx : x ∈ Ω)
    (hpos : 0 < u x) : HarmonicAt u x := by
  have hxV : Ω ∩ {x | 0 < u x} ∈ 𝓝 x := h.isOpen_pos.mem_nhds ⟨hx, hpos⟩
  exact ⟨h.contDiffOn.contDiffAt hxV,
    Filter.mem_of_superset hxV fun y hy => h.laplacian_eq_zero hQ hy⟩

/-- A variational solution satisfies `IsLipHarmonicPos`. -/
theorem isLipHarmonicPos (h : IsVariationalSolutionQ Ω C Q u χ)
    (hQ : QBounds Ω Q L c C') : IsLipHarmonicPos Ω u where
  isOpen := h.isOpen
  nonneg := h.nonneg
  lipschitzOnWith := ⟨C, h.lipschitzOnWith⟩
  harmonicAt _ hx hpos := h.harmonicOn_pos hQ hx hpos

/-- **Proposition 3.2**: a variational solution is weakly subharmonic on `Ω`. -/
theorem weaklySubharmonic (h : IsVariationalSolutionQ Ω C Q u χ)
    (hQ : QBounds Ω Q L c C') : IsWeaklySubharmonicOn Ω u :=
  (h.isLipHarmonicPos hQ).weaklySubharmonic

/-- `u²` is weakly subharmonic on `Ω`. With the sub-mean-value property of weakly
subharmonic functions this gives the monotonicity of the spherical means of `u²`. -/
theorem weaklySubharmonic_sq (h : IsVariationalSolutionQ Ω C Q u χ)
    (hQ : QBounds Ω Q L c C') :
    IsWeaklySubharmonicOn Ω fun z => u z ^ 2 :=
  (h.isLipHarmonicPos hQ).weaklySubharmonic_sq

end IsVariationalSolutionQ

namespace IsVariationalSolution

variable {Ω : Set (Rn n)} {C : ℝ≥0} {u χ : Rn n → ℝ}

theorem isOpen_pos (h : IsVariationalSolution Ω C u χ) : IsOpen (Ω ∩ {x | 0 < u x}) :=
  h.toQ.isOpen_pos

/-- `χ = 1` a.e. on `Ω ∩ {u > 0}`. -/
theorem ae_chi_eq_one (h : IsVariationalSolution Ω C u χ) :
    ∀ᵐ y, y ∈ Ω → 0 < u y → χ y = 1 :=
  h.toQ.ae_chi_eq_one

/-- The identity `∫ φ ∂_e u Δu = 0` for `φ ∈ C^∞_c(Ω ∩ {u > 0})`. It comes from the inner
variation in the direction `ξ = φ e` (proof of Proposition 3.2). -/
theorem integral_mul_fderiv_mul_laplacian_eq_zero (h : IsVariationalSolution Ω C u χ)
    {φ : Rn n → ℝ} (hφ : IsTestFunction (Ω ∩ {x | 0 < u x}) φ) (e : Rn n) :
    ∫ y, φ y * (fderiv ℝ u y e * Δ u y) = 0 :=
  h.toQ.integral_mul_fderiv_mul_laplacian_eq_zero (QBounds.one Ω) hφ e

/-- `∂_e u Δu = 0` on `Ω ∩ {u > 0}`. -/
theorem fderiv_mul_laplacian_eq_zero (h : IsVariationalSolution Ω C u χ) (e : Rn n)
    {y : Rn n} (hy : y ∈ Ω ∩ {x | 0 < u x}) : fderiv ℝ u y e * Δ u y = 0 :=
  h.toQ.fderiv_mul_laplacian_eq_zero (QBounds.one Ω) e hy

/-- `Δu = 0` on `Ω ∩ {u > 0}` (proof of Proposition 3.2). -/
theorem laplacian_eq_zero (h : IsVariationalSolution Ω C u χ) {y : Rn n}
    (hy : y ∈ Ω ∩ {x | 0 < u x}) : Δ u y = 0 :=
  h.toQ.laplacian_eq_zero (QBounds.one Ω) hy

/-- **Proposition 3.2**: a variational solution is harmonic on `Ω ∩ {u > 0}`. -/
theorem harmonicOn_pos (h : IsVariationalSolution Ω C u χ) {x : Rn n} (hx : x ∈ Ω)
    (hpos : 0 < u x) : HarmonicAt u x :=
  h.toQ.harmonicOn_pos (QBounds.one Ω) hx hpos

/-- A variational solution satisfies `IsLipHarmonicPos`. -/
theorem isLipHarmonicPos (h : IsVariationalSolution Ω C u χ) : IsLipHarmonicPos Ω u :=
  h.toQ.isLipHarmonicPos (QBounds.one Ω)

/-- **Proposition 3.2**: a variational solution is weakly subharmonic on `Ω`. -/
theorem weaklySubharmonic (h : IsVariationalSolution Ω C u χ) : IsWeaklySubharmonicOn Ω u :=
  h.toQ.weaklySubharmonic (QBounds.one Ω)

/-- `u²` is weakly subharmonic on `Ω`. With the sub-mean-value property of weakly
subharmonic functions this gives the monotonicity of the spherical means of `u²`. -/
theorem weaklySubharmonic_sq (h : IsVariationalSolution Ω C u χ) :
    IsWeaklySubharmonicOn Ω fun z => u z ^ 2 :=
  h.toQ.weaklySubharmonic_sq (QBounds.one Ω)

end IsVariationalSolution

end InnerVariational
