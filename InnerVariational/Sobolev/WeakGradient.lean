/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Basic.Setup
public import GMTFoundations.Sobolev.Lattice
import Mathlib.Data.Real.Hom
public import GMTFoundations.Defs.Sobolev

/-!
# Weak gradients: coordinate form and restriction

Complements to gmt-foundations' weak gradients `GMTFoundations.HasWeakGradient U u G`
(`GMTFoundations/Defs/Sobolev.lean`), whose defining identity is tested against smooth compactly
supported `φ` and every direction `v`.

## Main results

* `InnerVariational.HasWeakGradient.single`: the identity in the coordinate directions,
  `∫_U u ∂ᵢφ = -∫_U Gᵢ φ`.
* `InnerVariational.HasWeakGradient.of_single`: conversely, the coordinate identities and local
  integrability of `u` and `G` give a weak gradient.
* `InnerVariational.HasWeakGradient.mono`: a weak gradient on `U` is one on every `V ⊆ U`.
-/

open MeasureTheory Set
open scoped ContDiff RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ} {U V : Set (Rn n)} {u : Rn n → ℝ} {G : Rn n → Rn n}

/-- **Coordinate form of the weak-gradient identity:** `∫_U u ∂ᵢφ = -∫_U Gᵢ φ`. -/
theorem HasWeakGradient.single (hW : GMTFoundations.HasWeakGradient U u G) (i : Fin n)
    {φ : Rn n → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) :
    ∫ x in U, u x * fderiv ℝ φ x (EuclideanSpace.single i 1) = -∫ x in U, G x i * φ x := by
  rw [hW.2.2 φ hφ hφc hφU]
  simp [EuclideanSpace.inner_single_right]

/-- **A weak gradient from the coordinate identities.** If `u` and `G` are locally integrable on
`U` and `∫_U u ∂ᵢφ = -∫_U Gᵢ φ` for every coordinate `i` and every `φ ∈ C_c^∞(U)`, then `G` is a
weak gradient of `u` on `U`. -/
theorem HasWeakGradient.of_single (hu : LocallyIntegrableOn u U) (hG : LocallyIntegrableOn G U)
    (h : ∀ i : Fin n, ∀ φ : Rn n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∫ x in U, u x * fderiv ℝ φ x (EuclideanSpace.single i 1) = -∫ x in U, G x i * φ x) :
    GMTFoundations.HasWeakGradient U u G := by
  refine ⟨hu, hG, fun φ hφ hφc hφU v => ?_⟩
  set e : Fin n → Rn n := fun i => EuclideanSpace.single i 1 with he
  have hv : v = ∑ i, v i • e i := by
    ext j
    simp [e, Pi.single_apply]
  have hL : ∀ x, u x * fderiv ℝ φ x v = ∑ i, v i * (u x * fderiv ℝ φ x (e i)) := by
    intro x
    conv_lhs => rw [hv]
    simp only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hR : ∀ x, ⟪G x, v⟫ * φ x = ∑ i, v i * (G x i * φ x) := by
    intro x
    conv_lhs => rw [hv]
    simp only [inner_sum, inner_smul_right, e, EuclideanSpace.inner_single_right, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by simp; ring
  have i1 : ∀ i, Integrable (fun x => v i * (u x * fderiv ℝ φ x (e i))) (volume.restrict U) :=
    fun i => ((GMTFoundations.integrable_fderiv_apply_mul hu hφ hφc hφU (e i)).const_mul
      (v i)).integrableOn
  have i2 : ∀ i, Integrable (fun x => v i * (G x i * φ x)) (volume.restrict U) := by
    intro i
    refine ((GMTFoundations.integrable_inner_mul hG hφ.continuous hφc hφU (e i)).const_mul
      (v i)).integrableOn.congr (Filter.Eventually.of_forall fun x => ?_)
    simp [e, EuclideanSpace.inner_single_right]
  simp_rw [hL, hR]
  rw [integral_finsetSum _ fun i _ => i1 i, integral_finsetSum _ fun i _ => i2 i,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, integral_const_mul, h i φ hφ hφc hφU, mul_neg]

/-- **Restriction:** a weak gradient on `U` is a weak gradient on every `V ⊆ U`. -/
theorem HasWeakGradient.mono (hW : GMTFoundations.HasWeakGradient U u G) (hVU : V ⊆ U) :
    GMTFoundations.HasWeakGradient V u G :=
  GMTFoundations.HasWeakGradient.of_integral_eq (hW.1.mono_set hVU) (hW.2.1.mono_set hVU)
    fun _ hφ hφc hφV v => hW.integral_eq hφ hφc (hφV.trans hVU) v

end InnerVariational
