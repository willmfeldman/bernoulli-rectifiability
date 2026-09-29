/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Main.RieszMeasure
public import InnerVariational.Kernel.IBP
public import InnerVariational.Kernel.Rescale
public import InnerVariational.Blowup.Profile
public import InnerVariational.Singular.FlatPoint
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Data.Real.Hom
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import GMTFoundations.Defs.Calculus

/-!
# The Laplacian of the one-dimensional profile, and rescaled test functions

Two elementary facts used in the density computation at the end of the proof of Theorem 8.7 of
D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
DOI 10.1002/cpa.22226; arXiv:2306.10131 (numbering of arXiv v2):

* **The model Laplacian** (in Lebesgue form). For a unit
  vector `ν` there is a linear isometric embedding `L : ℝ^{n-1} → ℝⁿ` onto `ν^⊥` such that
  `∫ |⟪z, ν⟫| Δη(z) dz = 2 ∫_{ℝ^{n-1}} η(L w) dw` for every `η ∈ C^∞_c(ℝⁿ)`
  (`exists_integral_abs_inner_mul_laplacian`). This is `Δ|⟪·, ν⟫| = 2 ℋ^{n-1}⌊ν^⊥`, stated without
  Hausdorff measure, so that the identification of `ℋ^{n-1}` on a hyperplane with Lebesgue
  measure is not needed. Proof: integrate by parts once
  (`Kernel.integral_mul_laplacian_eq_neg`), so only `∂_ν η` appears; rotate `ν` to `e₀` by a
  reflection; Fubini in the first coordinate; `∫_ℝ sign(t) g'(t) dt = −2 g(0)`.
* **Rescaled test functions** `η_{x,r} = η((· − x)/r)` (`scaleTest`): support, smoothness, and
  `Δη_{x,r} = r^{-2} (Δη)((· − x)/r)` (`laplacian_scaleTest`).
-/

open MeasureTheory Metric Set Filter Topology Laplacian
open scoped ContDiff RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational.Main

variable {n : ℕ}

/-! ### The Laplacian commutes with dilations and translations -/

/-- `Δ(η(c(· − x)))(y) = c² Δη(c(y − x))`. -/
theorem laplacian_comp_smul_sub {η : Rn n → ℝ} (hη : ContDiff ℝ 2 η) (x : Rn n) (c : ℝ)
    (y : Rn n) : Δ (fun z => η (c • (z - x))) y = c ^ 2 * Δ η (c • (y - x)) := by
  set b := EuclideanSpace.basisFun (Fin n) ℝ
  have key : ∀ f : Rn n → ℝ, ∀ p, Δ f p = ∑ i, iteratedFDeriv ℝ 2 f p ![b i, b i] := fun f p => by
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f b]
  set g : Rn n → ℝ := fun w => η (w - c • x) with hg
  have hgs : ContDiff ℝ 2 g := hη.comp (contDiff_id.sub contDiff_const)
  have e : (fun z => η (c • (z - x))) = fun z => g (c • z) := by
    funext z
    simp only [hg, smul_sub]
  have hD : iteratedFDeriv ℝ 2 (fun z => η (c • (z - x))) y =
      c ^ 2 • iteratedFDeriv ℝ 2 η (c • (y - x)) := by
    rw [e, iteratedFDeriv_comp_const_smul c hgs]
    simp only [hg]
    rw [iteratedFDeriv_comp_sub, smul_sub]
  rw [key, key, hD, Finset.mul_sum]
  rfl

/-! ### Rescaled test functions -/

/-- The rescaled function `η_{x,r}(y) = η((y − x)/r)`. -/
def scaleTest (η : Rn n → ℝ) (x : Rn n) (r : ℝ) : Rn n → ℝ :=
  fun y => η (r⁻¹ • (y - x))

@[simp] theorem scaleTest_apply (η : Rn n → ℝ) (x : Rn n) (r : ℝ) (y : Rn n) :
    scaleTest η x r y = η (r⁻¹ • (y - x)) := rfl

theorem contDiff_scaleTest {η : Rn n → ℝ} {k : WithTop ℕ∞} (hη : ContDiff ℝ k η) (x : Rn n)
    (r : ℝ) : ContDiff ℝ k (scaleTest η x r) :=
  hη.comp ((contDiff_id.sub contDiff_const).const_smul r⁻¹)

theorem laplacian_scaleTest {η : Rn n → ℝ} (hη : ContDiff ℝ 2 η) (x : Rn n) (r : ℝ)
    (y : Rn n) : Δ (scaleTest η x r) y = (r⁻¹) ^ 2 * Δ η (r⁻¹ • (y - x)) :=
  laplacian_comp_smul_sub hη x r⁻¹ y

/-- The support of `η_{x,r}` is the image of that of `η` under `z ↦ x + r z`. -/
theorem tsupport_scaleTest_subset {η : Rn n → ℝ} (hη : HasCompactSupport η) (x : Rn n) {r : ℝ}
    (hr : r ≠ 0) : tsupport (scaleTest η x r) ⊆ (fun z => x + r • z) '' tsupport η := by
  refine closure_minimal (fun y hy => ⟨r⁻¹ • (y - x), subset_tsupport _ hy, ?_⟩)
    ((hη.image (continuous_const.add (continuous_const_smul r))).isClosed)
  simp only
  rw [smul_smul, mul_inv_cancel₀ hr, one_smul, add_sub_cancel]

theorem tsupport_scaleTest_subset_ball {η : Rn n → ℝ} (hη : HasCompactSupport η) {s : ℝ}
    (hηs : tsupport η ⊆ ball 0 s) (x : Rn n) {r : ℝ} (hr : 0 < r) :
    tsupport (scaleTest η x r) ⊆ ball x (r * s) := by
  refine (tsupport_scaleTest_subset hη x hr.ne').trans ?_
  rintro _ ⟨z, hz, rfl⟩
  have hz' := mem_ball_zero_iff.1 (hηs hz)
  rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr.le]
  exact mul_lt_mul_of_pos_left hz' hr

theorem hasCompactSupport_scaleTest {η : Rn n → ℝ} (hη : HasCompactSupport η) (x : Rn n) {r : ℝ}
    (hr : r ≠ 0) : HasCompactSupport (scaleTest η x r) :=
  (hη.image (continuous_const.add (continuous_const_smul r))).of_isClosed_subset
    (isClosed_tsupport _) (tsupport_scaleTest_subset hη x hr)

/-- `η_{x,r}` is a test function on `Ω` if `tsupport η ⊆ B_s` and `B_{rs}(x) ⊆ Ω`. -/
theorem isTestFunction_scaleTest {Ω : Set (Rn n)} {η : Rn n → ℝ} (hη : ContDiff ℝ ∞ η)
    (hηc : HasCompactSupport η) {s : ℝ} (hηs : tsupport η ⊆ ball 0 s) (x : Rn n) {r : ℝ}
    (hr : 0 < r) (hΩ : ball x (r * s) ⊆ Ω) : IsTestFunction Ω (scaleTest η x r) :=
  ⟨contDiff_scaleTest hη x r, hasCompactSupport_scaleTest hηc x hr.ne',
    (tsupport_scaleTest_subset_ball hηc hηs x hr).trans hΩ⟩

/-- `∫ Δφ = 0` for a test function `φ`. -/
theorem integral_laplacian_eq_zero {Ω : Set (Rn n)} (hΩ : IsOpen Ω) {φ : Rn n → ℝ}
    (hφ : IsTestFunction Ω φ) : ∫ y, Δ φ y = 0 := by
  have h := Kernel.integral_mul_laplacian_eq_neg hΩ (f := fun _ => (1 : ℝ))
    (LipschitzWith.const (1 : ℝ)).locallyLipschitz.locallyLipschitzOn hφ
  simp only [one_mul] at h
  rw [h]
  have : ∀ y, gradient (fun _ : Rn n => (1 : ℝ)) y = 0 := fun y => gradient_const y (1 : ℝ)
  simp [this]

/-! ### Coordinates `ℝ × ℝ^m ≅ ℝ^{m+1}` -/

/-- The embedding `w ↦ (0, w)` of `ℝ^m` into `ℝ^{m+1}`. -/
def insZero (m : ℕ) : Rn m →ₗᵢ[ℝ] Rn (m + 1) where
  toFun w := WithLp.toLp 2 (Fin.cons (0 : ℝ) (WithLp.ofLp w) : Fin (m + 1) → ℝ)
  map_add' v w := by
    ext i
    cases i using Fin.cases <;> simp
  map_smul' c w := by
    ext i
    cases i using Fin.cases <;> simp
  norm_map' w := by
    simp [EuclideanSpace.norm_eq, Fin.sum_univ_succ]

@[simp] theorem insZero_apply_zero (m : ℕ) (w : Rn m) : (insZero m w) 0 = 0 := rfl

/-- The measurable equivalence `(t, w) ↦ (t, w₀, …, w_{m-1})`. -/
def splitFirst (m : ℕ) : ℝ × Rn m ≃ᵐ Rn (m + 1) :=
  (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
      (MeasurableEquiv.toLp 2 (Fin m → ℝ)).symm).trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0).symm.trans (MeasurableEquiv.toLp 2 _))

theorem splitFirst_apply (m : ℕ) (t : ℝ) (w : Rn m) :
    splitFirst m (t, w) = t • EuclideanSpace.single 0 1 + insZero m w := by
  ext i
  cases i using Fin.cases <;>
    simp [splitFirst, insZero, MeasurableEquiv.piFinSuccAbove_symm_apply,
      MeasurableEquiv.prodCongr]

theorem measurePreserving_splitFirst (m : ℕ) :
    MeasurePreserving (splitFirst m) (volume.prod volume) volume := by
  have h1 : MeasurePreserving (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
      (MeasurableEquiv.toLp 2 (Fin m → ℝ)).symm) (volume.prod volume) (volume.prod volume) :=
    (MeasurePreserving.id volume).prod
      (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp _)
  have h2 : MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm
      (volume.prod volume) volume :=
    (measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => (volume : Measure ℝ)) 0).symm
  have h3 : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin (m + 1) → ℝ)) volume volume :=
    PiLp.volume_preserving_toLp _
  exact h3.comp (h2.comp h1)

/-! ### The model Laplacian -/

/-- `∫_ℝ sign(t) g'(t) dt = −2 g(0)` for a `C¹` function `g` with compact support, written with the
two half-lines. -/
theorem integral_sign_mul_deriv {g g' : ℝ → ℝ} (hg : ∀ t, HasDerivAt g (g' t) t)
    (hg' : Continuous g') (hgc : HasCompactSupport g) :
    ∫ t, ((Ioi 0).indicator g' t - (Iio 0).indicator g' t) = -2 * g 0 := by
  have hgd : g' = deriv g := funext fun t => (hg t).deriv.symm
  have hg'c : HasCompactSupport g' := by
    rw [hgd]
    exact hgc.deriv
  have hint : Integrable g' := hg'.integrable_of_hasCompactSupport hg'c
  have hcont : Continuous g := continuous_iff_continuousAt.2 fun t => (hg t).continuousAt
  have htop : Tendsto g atTop (𝓝 0) := hgc.is_zero_at_infty.mono_left atTop_le_cocompact
  have hbot : Tendsto g atBot (𝓝 0) := hgc.is_zero_at_infty.mono_left atBot_le_cocompact
  rw [integral_sub (hint.indicator measurableSet_Ioi) (hint.indicator measurableSet_Iio)]
  have h1 : ∫ t, (Ioi 0).indicator g' t = 0 - g 0 := by
    rw [integral_indicator measurableSet_Ioi]
    exact integral_Ioi_of_hasDerivAt_of_tendsto hcont.continuousWithinAt (fun t _ => hg t)
      hint.integrableOn htop
  have h2 : ∫ t, (Iio 0).indicator g' t = g 0 - 0 := by
    rw [integral_indicator measurableSet_Iio,
      ← integral_Iic_eq_integral_Iio]
    exact integral_Iic_of_hasDerivAt_of_tendsto hcont.continuousWithinAt (fun t _ => hg t)
      hint.integrableOn hbot
  rw [h1, h2]
  ring

/-- **The model Laplacian** (Lebesgue form): `Δ|⟪·, ν⟫| = 2 ℋ^{m}⌊ν^⊥` on `ℝ^{m+1}`,
tested against `η ∈ C^∞_c`, with `ℋ^m⌊ν^⊥` written as the image of Lebesgue measure on `ℝ^m`
under a linear isometric embedding `L` onto `ν^⊥`. -/
theorem exists_integral_abs_inner_mul_laplacian' {m : ℕ} {ν : Rn (m + 1)} (hν : ‖ν‖ = 1) :
    ∃ L : Rn m →ₗᵢ[ℝ] Rn (m + 1), (∀ w, ⟪L w, ν⟫ = 0) ∧
      ∀ η : Rn (m + 1) → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
        ∫ z, |⟪z, ν⟫| * Δ η z = 2 * ∫ w, η (L w) := by
  set e₀ : Rn (m + 1) := EuclideanSpace.single 0 1 with he₀
  have he₀n : ‖e₀‖ = 1 := by simp [he₀]
  set R := Submodule.reflection (ℝ ∙ (ν - e₀))ᗮ with hRdef
  have hR : R ν = e₀ := Submodule.reflection_sub (hν.trans he₀n.symm)
  have hRe : R e₀ = ν := by rw [← hR, Submodule.reflection_reflection]
  set L : Rn m →ₗᵢ[ℝ] Rn (m + 1) := R.toLinearIsometry.comp (insZero m) with hLdef
  have hL : ∀ w, L w = R (insZero m w) := fun w => rfl
  have hLν : ∀ w, ⟪L w, ν⟫ = 0 := fun w => by
    rw [hL, ← hRe, LinearIsometryEquiv.inner_map_map, he₀, EuclideanSpace.inner_single_right]
    simp
  refine ⟨L, hLν, fun η hη hηc => ?_⟩
  have hpt : ∀ t w, R (splitFirst m (t, w)) = t • ν + L w := fun t w => by
    rw [splitFirst_apply, map_add, map_smul, hRe, hL]
  have hinner : ∀ t w, ⟪t • ν + L w, ν⟫ = t := fun t w => by
    rw [inner_add_left, hLν, inner_smul_left, real_inner_self_eq_norm_sq, hν]
    simp
  -- Step 1: integrate by parts once
  set f := absProfile ν 0 with hfdef
  have hf : LocallyLipschitzOn univ f :=
    (lipschitzWith_absProfile hν).locallyLipschitz.locallyLipschitzOn
  have hibp := Kernel.integral_mul_laplacian_eq_neg isOpen_univ hf ⟨hη, hηc, subset_univ _⟩
  have hlhs : ∫ z, |⟪z, ν⟫| * Δ η z = ∫ z, f z * Δ η z := by simp [hfdef]
  -- Step 2: `⟪∇f, ∇η⟫ = sign(⟪z, ν⟫) ∂_ν η` off the hyperplane `ν^⊥`
  set D : Rn (m + 1) → ℝ := fun z => fderiv ℝ η z ν with hDdef
  have hDc : Continuous D := (hη.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDs : HasCompactSupport D := hηc.fderiv_apply ℝ ν
  have hDi : Integrable D := hDc.integrable_of_hasCompactSupport hDs
  set G : Rn (m + 1) → ℝ := fun z =>
    {z | 0 < ⟪z, ν⟫}.indicator D z - {z | ⟪z, ν⟫ < 0}.indicator D z with hGdef
  have hmeas_pos : MeasurableSet {z : Rn (m + 1) | 0 < ⟪z, ν⟫} :=
    measurableSet_lt measurable_const (continuous_id.inner continuous_const).measurable
  have hmeas_neg : MeasurableSet {z : Rn (m + 1) | ⟪z, ν⟫ < 0} :=
    measurableSet_lt (continuous_id.inner continuous_const).measurable measurable_const
  have hGi : Integrable G := (hDi.indicator hmeas_pos).sub (hDi.indicator hmeas_neg)
  have hae : (fun z => ⟪gradient f z, gradient η z⟫) =ᵐ[volume] G := by
    have hnull : volume {z : Rn (m + 1) | ⟪z, ν⟫ = 0} = 0 := by
      have e : {z : Rn (m + 1) | ⟪z, ν⟫ = 0} = ((ℝ ∙ ν)ᗮ : Submodule ℝ (Rn (m + 1))) := by
        ext z
        simp [Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_comm]
      rw [e]
      refine Measure.addHaar_submodule _ _ fun htop => ?_
      have hmem : ν ∈ (ℝ ∙ ν)ᗮ := htop ▸ Submodule.mem_top
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_self_eq_norm_sq, hν]
        at hmem
      norm_num at hmem
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with z hz
    rcases lt_trichotomy ⟪z, ν⟫ 0 with h | h | h
    · have h1 : z ∉ {z : Rn (m + 1) | 0 < ⟪z, ν⟫} := fun h' => absurd h (not_lt.2 (le_of_lt h'))
      rw [hfdef, gradient_absProfile_of_neg h, inner_neg_left, Kernel.inner_gradient_right, hGdef]
      simp only
      rw [indicator_of_notMem h1, indicator_of_mem (show z ∈ {z : Rn (m + 1) | ⟪z, ν⟫ < 0} from h)]
      ring
    · exact absurd h hz
    · have h1 : z ∉ {z : Rn (m + 1) | ⟪z, ν⟫ < 0} := fun h' => absurd h (not_lt.2 (le_of_lt h'))
      rw [hfdef, gradient_absProfile_of_pos h, Kernel.inner_gradient_right, hGdef]
      simp only
      rw [indicator_of_notMem h1, indicator_of_mem (show z ∈ {z : Rn (m + 1) | 0 < ⟪z, ν⟫} from h)]
      ring
  -- Step 3: rotate and split off the `ν`-coordinate
  have hrot : ∫ z, G z = ∫ y, G (R y) :=
    ((R.measurePreserving).integral_comp R.toHomeomorph.measurableEmbedding G).symm
  have hsplit : ∫ y, G (R y) = ∫ p : ℝ × Rn m, G (R (splitFirst m p)) ∂(volume.prod volume) :=
    ((measurePreserving_splitFirst m).integral_comp' fun y => G (R y)).symm
  have hFi : Integrable (fun p : ℝ × Rn m => G (R (splitFirst m p))) (volume.prod volume) := by
    have h1 : Integrable (fun y => G (R y)) :=
      (R.measurePreserving).integrable_comp_of_integrable hGi
    exact (measurePreserving_splitFirst m).integrable_comp_of_integrable h1
  rw [integral_prod_symm _ hFi] at hsplit
  -- Step 4: the one-dimensional integrals
  obtain ⟨ρ, hρ⟩ := hηc.isCompact.isBounded.subset_closedBall 0
  have hinner1 : ∀ w : Rn m, ∫ t, G (R (splitFirst m (t, w))) = -2 * η (L w) := by
    intro w
    have hgd : ∀ t : ℝ, HasDerivAt (fun t => η (t • ν + L w)) (D (t • ν + L w)) t := by
      intro t
      have h1 : HasDerivAt (fun t : ℝ => t • ν + L w) ν t := by
        simpa using ((hasDerivAt_id t).smul_const ν).add_const (L w)
      have h2 := ((hη.differentiable (by simp)).differentiableAt (x := t • ν + L w)).hasFDerivAt
      exact h2.comp_hasDerivAt t h1
    have hgc : HasCompactSupport fun t : ℝ => η (t • ν + L w) := by
      refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) ρ) fun t ht => ?_
      refine image_eq_zero_of_notMem_tsupport fun hmem => ht ?_
      have h1 := mem_closedBall_zero_iff.1 (hρ hmem)
      rw [mem_closedBall_zero_iff, Real.norm_eq_abs]
      calc |t| = |⟪t • ν + L w, ν⟫| := by rw [hinner]
        _ ≤ ‖t • ν + L w‖ * ‖ν‖ := abs_real_inner_le_norm _ _
        _ ≤ ρ := by rw [hν, mul_one]; exact h1
    have hgc' : Continuous fun t : ℝ => D (t • ν + L w) :=
      hDc.comp ((continuous_id.smul continuous_const).add continuous_const)
    have e : ∀ t, G (R (splitFirst m (t, w))) =
        (Ioi 0).indicator (fun t => D (t • ν + L w)) t -
          (Iio 0).indicator (fun t => D (t • ν + L w)) t := by
      intro t
      rw [hpt, hGdef]
      simp only [indicator, mem_setOf_eq, mem_Ioi, mem_Iio, hinner]
    simp_rw [e]
    rw [integral_sign_mul_deriv hgd hgc' hgc, zero_smul, zero_add]
  simp_rw [hinner1] at hsplit
  rw [hlhs, hibp, integral_congr_ae hae, hrot, hsplit, integral_const_mul]
  ring

/-- **The model Laplacian** (Lebesgue form) on `ℝⁿ`, `n ≥ 1`. -/
theorem exists_integral_abs_inner_mul_laplacian (hn : 1 ≤ n) {ν : Rn n} (hν : ‖ν‖ = 1) :
    ∃ L : Rn (n - 1) →ₗᵢ[ℝ] Rn n, (∀ w, ⟪L w, ν⟫ = 0) ∧
      ∀ η : Rn n → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
        ∫ z, |⟪z, ν⟫| * Δ η z = 2 * ∫ w, η (L w) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact exists_integral_abs_inner_mul_laplacian' hν

end InnerVariational.Main
