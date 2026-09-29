/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Defs.VariationalSolution
public import InnerVariational.Foundations.Bridge
public import EllipticBernoulli.Classical.InnerVariation
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import EllipticBernoulli.Defs.Variational
public import EllipticBernoulli.Defs.Regularity

/-!
# Inner variation of classical solutions, from `EllipticBernoulli` (foundations)

This file proves that the domain variation of a classical solution vanishes, the key step of
"classical solutions are variational solutions". The inner variation `innerVariation u χ_{u>0} ξ`
of this library is the set integral over `Ω` of `innerVarIntegrand` with `Q ≡ 1` from the
dependency elliptic-bernoulli-foundations v0.1.0
(https://github.com/willmfeldman/elliptic-bernoulli-foundations)
(both integrands vanish off `tsupport ξ ⊆ Ω`), which the dependency proves vanishes for classical
solutions (`EllipticBernoulli.IsClassicalSolution.integral_innerVarIntegrand_eq_zero`).

Kriventsov–Weiss (§9, after Definition 9.1) say that the domain-variation identity (3.5) "can be
verified through integration by parts". That integration by parts needs `|∇u| → 1` uniformly up
to the free boundary, which the definition of classical solution does not state (it only gives
the normal derivative `1` at each free-boundary point); the dependency proves it.

## References

* D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
  DOI 10.1002/cpa.22226; arXiv:2306.10131. Result and equation numbers refer to arXiv v2.
-/

@[expose] public section

open MeasureTheory Set InnerProductSpace
open scoped RealInnerProductSpace

namespace InnerVariational

variable {n : ℕ}

theorem eb_divergence_eq (ξ : Rn n → Rn n) (x : Rn n) :
    EllipticBernoulli.divergence ξ x = divergence ξ x := rfl

theorem divergence_of_notMem_tsupport {ξ : Rn n → Rn n} {x : Rn n} (hx : x ∉ tsupport ξ) :
    divergence ξ x = 0 := by
  simp [divergence, fderiv_of_notMem_tsupport ℝ hx]

theorem eb_posSet_indicator_eq {U : Set (Rn n)} {u : Rn n → ℝ} {x : Rn n} (hx : x ∈ U) :
    (EllipticBernoulli.posSet u U).indicator (1 : Rn n → ℝ) x = posIndicator u x := by
  by_cases h : 0 < u x
  · rw [indicator_of_mem (show x ∈ EllipticBernoulli.posSet u U from ⟨hx, h⟩), posIndicator,
      indicator_of_mem (show x ∈ {y | 0 < u y} from h)]
  · rw [indicator_of_notMem (show x ∉ EllipticBernoulli.posSet u U from fun hx' ↦ h hx'.2),
      posIndicator, indicator_of_notMem (show x ∉ {y | 0 < u y} from h)]

theorem eb_innerVarIntegrand_one (u χ : Rn n → ℝ) (ξ : Rn n → Rn n) (x : Rn n) :
    EllipticBernoulli.innerVarIntegrand (fun _ ↦ 1) u χ ξ x =
      (‖gradient u x‖ ^ 2 + χ x) * divergence ξ x -
        2 * ⟪gradient u x, fderiv ℝ ξ x (gradient u x)⟫ := by
  simp [EllipticBernoulli.innerVarIntegrand, eb_divergence_eq]

theorem innerVariation_posIndicator_eq_eb_setIntegral {U : Set (Rn n)} {u : Rn n → ℝ}
    {ξ : Rn n → Rn n} (hξ : tsupport ξ ⊆ U) :
    innerVariation u (posIndicator u) ξ =
      ∫ x in U, EllipticBernoulli.innerVarIntegrand (fun _ ↦ 1) u
        ((EllipticBernoulli.posSet u U).indicator 1) ξ x := by
  have hoff : ∀ x, x ∉ tsupport ξ → EllipticBernoulli.innerVarIntegrand (fun _ ↦ 1) u
      ((EllipticBernoulli.posSet u U).indicator 1) ξ x = 0 := fun x hx ↦ by
    simp [eb_innerVarIntegrand_one, divergence_of_notMem_tsupport hx,
      fderiv_of_notMem_tsupport ℝ hx]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ hoff x fun h ↦ hx (hξ h),
    innerVariation]
  congr 1
  funext x
  by_cases hx : x ∈ tsupport ξ
  · rw [eb_innerVarIntegrand_one, eb_posSet_indicator_eq (hξ hx)]
  · rw [hoff x hx]
    simp [divergence_of_notMem_tsupport hx, fderiv_of_notMem_tsupport ℝ hx]

theorem innerVariation_posIndicator_eq_zero_of_eb {Ω : Set (Rn n)} {u : Rn n → ℝ}
    {ξ : Rn n → Rn n} (hu : EllipticBernoulli.IsClassicalSolution Ω (fun _ ↦ 1) u)
    (hξ : IsLipTestField Ω ξ) : innerVariation u (posIndicator u) ξ = 0 := by
  obtain ⟨hξL, hξc, hξΩ⟩ := hξ
  rw [innerVariation_posIndicator_eq_eb_setIntegral hξΩ]
  exact EllipticBernoulli.IsClassicalSolution.integral_innerVarIntegrand_eq_zero hu
    ⟨0, (LipschitzWith.const (1 : ℝ)).lipschitzOnWith⟩ ⟨1, one_pos, fun _ _ ↦ le_rfl⟩ hξL hξc hξΩ

end InnerVariational
