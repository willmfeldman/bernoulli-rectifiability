/-
Copyright (c) 2026 The Tau Ceti contributors, William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, William M. Feldman
-/
module

public import Sperner.Vendor.Weyl.Weyl
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Harmonic functions are weakly harmonic

Let `E` be a finite-dimensional real inner product space with an additive Haar measure `μ`.

* `integral_laplacian_mul_eq_integral_mul_laplacian`: Green's second identity against a test
  function, `∫ Δχ · u = ∫ χ · Δu` for `u ∈ C²(U)` and `χ ∈ C^∞_c(U)`.
* `weaklyHarmonicOn_of_harmonicOnNhd`: a harmonic function on an open set is weakly harmonic
  there, in the sense of `Sperner.Vendor.Analysis.WeaklyHarmonicOn`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Classics in Mathematics, Springer, Berlin, 2001 (reprint of the 1998 edition), Theorem 2.1.

## Provenance

* Vendored from elliptic-bernoulli-foundations (W. M. Feldman),
  https://github.com/willmfeldman/elliptic-bernoulli-foundations, release v0.1.0, path
  `EllipticBernoulli/Harmonic/Basic.lean`, section `Green`. License: Apache-2.0.
* That file ports TauCeti, https://github.com/TauCetiProject/TauCeti, path
  `TauCeti/Analysis/Sobolev/WeakDeriv/Laplacian.lean`, commit
  90cca67c0c8e91cd30b0d46cb58101f8c5c59236. License: Apache-2.0. Upstream notice:
  `Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.`
* Extent: `integral_laplacian_mul_eq_integral_mul_laplacian` (verbatim) and
  `HarmonicOnNhd.weaklyHarmonicOn` (verbatim, renamed `weaklyHarmonicOn_of_harmonicOnNhd`).
* Changes (Sperner): namespace `EllipticBernoulli` → `Sperner.Vendor`;
  `ViscositySolns.Analysis` names replaced by the vendored `Sperner.Vendor.Analysis` names;
  `public section` → `@[expose] public section`. Mathematical content unchanged.
-/

open InnerProductSpace MeasureTheory Metric Module Set Filter Topology
open scoped ContDiff Laplacian
open Sperner.Vendor.Analysis (WeaklyHarmonicOn laplacian_eq_sum_fderiv_fderiv)

@[expose] public section

namespace Sperner.Vendor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section Green

variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- **Green's second identity against a test function.** For `u` of class `C²` on an open set
`U` and a smooth `χ` with compact support in `U`, `∫ Δχ · u = ∫ χ · Δu`. -/
theorem integral_laplacian_mul_eq_integral_mul_laplacian {U : Set E} (hU : IsOpen U)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ U) :
    ∫ x, Δ χ x * u x ∂μ = ∫ x, χ x * Δ u x ∂μ := by
  set b := stdOrthonormalBasis ℝ E
  have hu1 : ContDiffOn ℝ 1 (fderiv ℝ u) U := hu.fderiv_of_isOpen hU (by norm_num)
  have hdu : ∀ v, ContDiffOn ℝ 1 (fun y ↦ fderiv ℝ u y v) U := fun v ↦
    hu1.clm_apply contDiffOn_const
  have hu_diff : ∀ x ∈ U, DifferentiableAt ℝ u x := fun x hx ↦
    (hu.differentiableOn (by norm_num) x hx).differentiableAt (hU.mem_nhds hx)
  have hdu_diff : ∀ v, ∀ x ∈ U, DifferentiableAt ℝ (fun y ↦ fderiv ℝ u y v) x := fun v x hx ↦
    ((hdu v).differentiableOn one_ne_zero x hx).differentiableAt (hU.mem_nhds hx)
  have hddu_cont : ∀ v, ContinuousOn (fun y ↦ fderiv ℝ (fun z ↦ fderiv ℝ u z v) y v) U :=
    fun v ↦ ((hdu v).continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const
  have hΔu : ∀ x ∈ U, Δ u x = ∑ i, fderiv ℝ (fun y ↦ fderiv ℝ u y (b i)) x (b i) := by
    intro x hx
    rw [laplacian_eq_iteratedFDeriv_orthonormalBasis _ b]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [iteratedFDeriv_two_apply, fderiv_clm_apply
      ((hu1.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hx))
      (differentiableAt_const _)]
    simp
  have hΔχ : ∀ x, Δ χ x = ∑ i, fderiv ℝ (fun y ↦ fderiv ℝ χ y (b i)) x (b i) :=
    laplacian_eq_sum_fderiv_fderiv b (hχ.of_le (by norm_cast))
  -- smooth directional derivatives of `χ`, supported in `tsupport χ`
  have hDχ : ∀ v, ContDiff ℝ ∞ (fun y ↦ fderiv ℝ χ y v) ∧
      tsupport (fun y ↦ fderiv ℝ χ y v) ⊆ tsupport χ := fun v ↦
    ⟨(hχ.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const, tsupport_fderiv_apply_subset ℝ v⟩
  have hDDχ : ∀ v, ContDiff ℝ ∞ (fun y ↦ fderiv ℝ (fun z ↦ fderiv ℝ χ z v) y v) ∧
      tsupport (fun y ↦ fderiv ℝ (fun z ↦ fderiv ℝ χ z v) y v) ⊆ tsupport χ := fun v ↦
    ⟨(((hDχ v).1).fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const,
      (tsupport_fderiv_apply_subset ℝ v).trans (hDχ v).2⟩
  -- integrability of the products
  have hint : ∀ φ g : E → ℝ, Continuous φ → tsupport φ ⊆ tsupport χ → ContinuousOn g U →
      Integrable (fun x ↦ φ x * g x) μ := by
    intro φ g hφ hφs hg
    have hφc : HasCompactSupport φ := hχc.mono' (subset_tsupport φ |>.trans hφs)
    exact ((hφ.continuousOn.mul hg).continuous_of_tsupport_subset hU
      ((tsupport_mul_subset_left).trans (hφs.trans hχU))).integrable_of_hasCompactSupport
      hφc.mul_right
  have hucont : ContinuousOn u U := hu.continuousOn
  have hdu_cont : ∀ v, ContinuousOn (fun y ↦ fderiv ℝ u y v) U := fun v ↦ (hdu v).continuousOn
  -- one direction
  have hdir : ∀ v, ∫ x, fderiv ℝ (fun y ↦ fderiv ℝ χ y v) x v * u x ∂μ =
      ∫ x, χ x * fderiv ℝ (fun y ↦ fderiv ℝ u y v) x v ∂μ := by
    intro v
    have e1 : ∫ x, fderiv ℝ χ x v * fderiv ℝ u x v ∂μ =
        -∫ x, fderiv ℝ (fun y ↦ fderiv ℝ χ y v) x v * u x ∂μ :=
      integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
        (hint _ _ (hDDχ v).1.continuous (hDDχ v).2 hucont)
        (hint _ _ (hDχ v).1.continuous (hDχ v).2 (hdu_cont v))
        (hint _ _ (hDχ v).1.continuous (hDχ v).2 hucont)
        (fun x _ ↦ ((hDχ v).1.differentiable (by simp)) x)
        (fun x hx ↦ hu_diff x (hχU ((hDχ v).2 hx)))
    have e2 : ∫ x, χ x * fderiv ℝ (fun y ↦ fderiv ℝ u y v) x v ∂μ =
        -∫ x, fderiv ℝ χ x v * fderiv ℝ u x v ∂μ :=
      integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
        (hint _ _ (hDχ v).1.continuous (hDχ v).2 (hdu_cont v))
        (hint _ _ hχ.continuous le_rfl (hddu_cont v))
        (hint _ _ hχ.continuous le_rfl (hdu_cont v))
        (fun x _ ↦ (hχ.differentiable (by simp)) x)
        (fun x hx ↦ hdu_diff v x (hχU hx))
    linarith
  calc ∫ x, Δ χ x * u x ∂μ
      = ∑ i, ∫ x, fderiv ℝ (fun y ↦ fderiv ℝ χ y (b i)) x (b i) * u x ∂μ := by
        simp_rw [hΔχ, Finset.sum_mul]
        exact integral_finsetSum _ fun i _ ↦
          hint _ _ (hDDχ (b i)).1.continuous (hDDχ (b i)).2 hucont
    _ = ∑ i, ∫ x, χ x * fderiv ℝ (fun y ↦ fderiv ℝ u y (b i)) x (b i) ∂μ :=
        Finset.sum_congr rfl fun i _ ↦ hdir (b i)
    _ = ∫ x, χ x * Δ u x ∂μ := by
        rw [← integral_finsetSum _ fun i _ ↦ hint _ _ hχ.continuous le_rfl (hddu_cont (b i))]
        refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
        by_cases hx : x ∈ U
        · simp only [hΔu x hx, Finset.mul_sum]
        · have : χ x = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ hx (hχU h)
          simp [this]

/-- **A harmonic function is weakly harmonic.** -/
theorem weaklyHarmonicOn_of_harmonicOnNhd {U : Set E} (hU : IsOpen U) {u : E → ℝ}
    (hu : HarmonicOnNhd u U) : WeaklyHarmonicOn μ u U := by
  intro χ hχ hχc hχU
  simp_rw [smul_eq_mul]
  rw [integral_laplacian_mul_eq_integral_mul_laplacian hU hu.contDiffOn hχ hχc hχU]
  refine integral_eq_zero_of_ae (ae_of_all _ fun x ↦ ?_)
  by_cases hx : x ∈ U
  · simp [(hu x hx).2.eq_of_nhds]
  · simp [image_eq_zero_of_notMem_tsupport fun h ↦ hx (hχU h)]

end Green

end Sperner.Vendor
