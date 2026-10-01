/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Blowup.Constancy
public import InnerVariational.Defs.Calculus
import InnerVariational.Sobolev.WeakGradient
public import GMTFoundations.Defs.Calculus

/-!
# Zero distributional gradient implies constant, divergence form

Let `U ⊆ ℝⁿ` be open and connected, and let `g ∈ L¹_loc(U)` satisfy `∫ g div ξ = 0` for every
`ξ ∈ C^∞_c(U; ℝⁿ)`. Then `g` is a.e. equal to a constant on `U`.

This is the fact used at the start of §8.1 of D. Kriventsov and G. S. Weiss, *Rectifiability,
finite Hausdorff measure, and compactness for non-minimizing Bernoulli free boundaries*, Comm.
Pure Appl. Math. 78 (2025), no. 3, DOI 10.1002/cpa.22226; arXiv:2306.10131 (numbering of
arXiv v2): `∫ χ div ξ = 0` on `{u = 0}°` forces `χ` to be constant on each connected component.
The weak-gradient form is proved in `Blowup/Constancy.lean`
(`exists_ae_eq_const_of_hasWeakGrad_zero`). This file only translates the divergence form into
that one, with the test fields `ξ = φ e_i`.
-/

open MeasureTheory Metric Set Filter Topology
open scoped ContDiff

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

namespace Regular

/-- `div (φ e)(y) = ∂_e φ(y)` for a differentiable scalar `φ` and a constant vector `e`. -/
theorem divergence_smul_const {φ : Rn n → ℝ} (hφ : Differentiable ℝ φ) (e y : Rn n) :
    divergence (fun z => φ z • e) y = fderiv ℝ φ y e := by
  rw [divergence, fderiv_smul_const (hφ y) e, ContinuousLinearMap.coe_smulRight,
    LinearMap.trace_smulRight]
  rfl

/-- **Zero distributional gradient implies constant.**
Let `U` be open and preconnected, `g ∈ L¹_loc(U)`, and `∫ g div ξ = 0` for every
`ξ ∈ C^∞_c(U; ℝⁿ)`. Then `g = c` a.e. on `U` for some constant `c`. -/
theorem exists_ae_eq_const_of_integral_mul_divergence_eq_zero {U : Set (Rn n)} (hU : IsOpen U)
    (hUc : IsPreconnected U) {g : Rn n → ℝ} (hg : LocallyIntegrableOn g U)
    (h : ∀ ξ, IsSmoothTestField U ξ → ∫ y, g y * divergence ξ y = 0) :
    ∃ c, ∀ᵐ y ∂(volume.restrict U), g y = c := by
  refine exists_ae_eq_const_of_hasWeakGrad_zero hU hUc
    (HasWeakGradient.of_single hg locallyIntegrableOn_zero fun i φ hφ hφc hφU => ?_)
  set e : Rn n := EuclideanSpace.single i 1
  have hφ' : ContDiff ℝ ∞ φ := hφ
  have hφd : Differentiable ℝ φ := hφ'.differentiable (by simp)
  have hξ : IsSmoothTestField U (fun z => φ z • e) :=
    ⟨hφ'.smul contDiff_const, hφc.smul_right, (tsupport_smul_subset_left φ fun _ => e).trans hφU⟩
  have h0 := h _ hξ
  simp only [divergence_smul_const hφd] at h0
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by
    rw [fderiv_of_notMem_tsupport (𝕜 := ℝ) fun h' => hy (hφU h'),
      zero_apply, mul_zero], h0]
  simp

end Regular

end InnerVariational
