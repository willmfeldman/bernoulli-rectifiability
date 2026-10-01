/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Frequency.Abstract
public import InnerVariational.Kernel.RellichPohozaev
public import InnerVariational.Kernel.BV
public import InnerVariational.Defs.Quantities
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Algebra.Ring.IsFormallyReal
import InnerVariational.Kernel.Subharmonic
public import InnerVariational.Defs.VariationalSolution
import InnerVariational.Kernel.Energy
public import InnerVariational.Basic.SphereIntegral
import InnerVariational.Basic.Polar
import InnerVariational.Basic.LipschitzFTC

/-!
# The monotonicity formula (Proposition 3.4)

Proposition 3.4 of Kriventsov–Weiss (the monotonicity formula of Weiss, see the references).
Let `(u, χ)` be a variational solution on `Ω` and `B_R(x) ⊆ Ω`. Then
`M_x(u; s) = D_x(u; s) − H_x(u; s)` is nondecreasing on `(0, R)`, locally Lipschitz there, and
for a.e. `s`
`M_x'(s) = (2 / s^{n+2}) ∫_{∂B_s(x)} (u(y) − (y − x)·∇u(y))²`.

This file instantiates the abstract radial calculus `Abstract.RadialData` of
`Frequency/Abstract.lean` for a variational solution, so that all of §3.3 and Section 4 of the
paper (the frequency formula, doubling, …) follow from that file.

## Main definitions

* `IsVariationalSolution.radialData`: the radial data of `(u, χ)` at `x` on `[a, b]`,
  `0 < a ≤ b < R`, with `ω = |B_1|`.

## Main results

* `IsVariationalSolution.hasDerivAt_energyD_ae`: the derivative of `D` (proof of
  Proposition 3.4), from the Rellich–Pohozaev identity (3.7) and the energy identity (3.8), in
  the combined form (3.9).
* `IsVariationalSolution.hasDerivAt_heightH_ae`: the derivative of `H` (proof of
  Proposition 3.4).
* `IsVariationalSolution.hasDerivAt_monotonicityM_ae`: the derivative of `M` (Proposition 3.4).
* `IsVariationalSolution.monotoneOn_monotonicityM`: `M` is nondecreasing on `(0, R)`.
* `IsVariationalSolution.monotoneOn_monotonicityM_Ioc`: on `(0, R]` when `B̄_R(x) ⊆ Ω`.
* `IsVariationalSolution.exists_lipschitzOnWith_monotonicityM`: `M` is Lipschitz on `[a, b]`,
  `0 < a ≤ b < R` (the absolute continuity in Proposition 3.4).
* `IsVariationalSolution.energyD_identity_ae`: identity (3.9).

## Notes

The paper works with `Q ≡ 1`, and so do we. Error terms that a Lipschitz-`Q` version would add
(`O(s)` in `D'`) would enter only through `hasDerivAt_energyD_ae`; the rest of the file is the
one-variable bookkeeping that `RadialData` records.

## References

* D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
  DOI 10.1002/cpa.22226; arXiv:2306.10131. Unqualified result and equation numbers in this file
  refer to this paper, in the numbering of arXiv v2.
* G. S. Weiss, *Partial regularity for weak solutions of an elliptic free boundary problem*,
  Comm. Partial Differential Equations 23 (1998), 439–455, Theorems 3.1 and 4.1 (the source
  cited for Proposition 3.4).
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

/-! ### Elementary helpers -/

/-- A function that is measurable along the sphere and bounded there is sphere integrable. -/
theorem sphereIntegrable_of_bound {g : Rn n → ℝ} {x : Rn n} {s M : ℝ}
    (hm : AEStronglyMeasurable (fun ω : sphere (0 : Rn n) 1 => g (x + s • (ω : Rn n)))
      (sphereMeasure n))
    (hb : ∀ y ∈ sphere x s, |g y| ≤ M) (hs : 0 ≤ s) : SphereIntegrable g x s :=
  Integrable.of_bound hm M (.of_forall fun ω => by
    rw [Real.norm_eq_abs]; exact hb _ (add_smul_mem_sphere hs ω))

/-- `s ↦ (s^k)⁻¹ f(s)` is Lipschitz on `[a, b]`, `0 < a`, if `f` is. -/
theorem exists_lipschitzOnWith_inv_pow_mul {f : ℝ → ℝ} {K : ℝ≥0} {a b : ℝ}
    (hf : LipschitzOnWith K f (Icc a b)) (ha : 0 < a) (k : ℕ) :
    ∃ K', LipschitzOnWith K' (fun s => (s ^ k)⁻¹ * f s) (Icc a b) := by
  have hc : ContDiffOn ℝ 1 (fun s : ℝ => (s ^ k)⁻¹) (Icc a b) :=
    ((contDiff_id.pow k).contDiffOn).inv fun s hs => pow_ne_zero _ (ha.trans_le hs.1).ne'
  obtain ⟨K₁, hK₁⟩ := hc.exists_lipschitzOnWith one_ne_zero (convex_Icc a b) isCompact_Icc
  obtain ⟨A, hA⟩ := hK₁.exists_abs_le isCompact_Icc
  obtain ⟨B, hB⟩ := hf.exists_abs_le isCompact_Icc
  exact hK₁.exists_mul hf hA hB

/-- If `B̄_R(x)` lies in the open set `Ω`, then so does `B_{R'}(x)` for some `R' > R`. -/
theorem exists_gt_ball_subset {Ω : Set (Rn n)} (hΩ : IsOpen Ω) {x : Rn n} {R : ℝ} (hR : 0 ≤ R)
    (h : closedBall x R ⊆ Ω) : ∃ R' > R, ball x R' ⊆ Ω := by
  obtain ⟨δ, hδ, hsub⟩ := (isCompact_closedBall x R).exists_thickening_subset_open hΩ h
  rw [thickening_closedBall hδ hR] at hsub
  exact ⟨δ + R, by linarith, hsub⟩

namespace IsVariationalSolution

variable {Ω : Set (Rn n)} {x : Rn n} {R s : ℝ}

theorem add_smul_mem_of_lt (hR : ball x R ⊆ Ω) (hs : 0 ≤ s) (hsR : s < R)
    (ω : sphere (0 : Rn n) 1) : x + s • (ω : Rn n) ∈ Ω :=
  hR ((add_smul_mem_ball_iff hs ω).2 hsR)

theorem sphere_subset_of_lt (hR : ball x R ⊆ Ω) (hsR : s < R) :
    sphere x s ⊆ Ω := fun _ hy =>
  hR (mem_ball.2 ((mem_sphere.1 hy).trans_lt hsR))

theorem aestronglyMeasurable_sphere_of_measurable {g : Rn n → ℝ} (hg : Measurable g) :
    AEStronglyMeasurable (fun ω : sphere (0 : Rn n) 1 => g (x + s • (ω : Rn n)))
      (sphereMeasure n) :=
  (hg.comp (continuous_add_smul_sphere x s).measurable).aestronglyMeasurable

end IsVariationalSolution

/-! ### Sphere integrals for a variational solution with a coefficient `Q`

These only use the Lipschitz bound on `u` and the measurability of `χ`; the versions for
`Q ≡ 1` below are their specialisations. -/

namespace IsVariationalSolutionQ

open Kernel IsVariationalSolution

variable {Ω : Set (Rn n)} {C : ℝ≥0} {Q u χ : Rn n → ℝ} {x : Rn n} {R : ℝ} {L : ℝ≥0}
  {c C' : ℝ}

theorem sq_norm_gradient_le (h : IsVariationalSolutionQ Ω C Q u χ) {y : Rn n} (hy : y ∈ Ω) :
    ‖gradient u y‖ ^ 2 ≤ (C : ℝ) ^ 2 :=
  pow_le_pow_left₀ (norm_nonneg _) (h.norm_gradient_le hy) 2

section Sphere

variable {s : ℝ}

theorem aestronglyMeasurable_sphere_chi (h : IsVariationalSolutionQ Ω C Q u χ)
    (hR : ball x R ⊆ Ω) (hs : 0 ≤ s) (hsR : s < R) :
    AEStronglyMeasurable (fun ω : sphere (0 : Rn n) 1 => χ (x + s • (ω : Rn n)))
      (sphereMeasure n) :=
  (aestronglyMeasurable_sphere_of_measurable h.measurable_chi).congr
    (.of_forall fun ω => indicator_of_mem (add_smul_mem_of_lt hR hs hsR ω) χ)

/-- `|u| ≤ |u(x)| + C s` on `∂B_s(x)`. -/
theorem abs_le_of_mem_sphere (h : IsVariationalSolutionQ Ω C Q u χ) (hR : ball x R ⊆ Ω)
    (hs : 0 ≤ s) (hsR : s < R) {y : Rn n} (hy : y ∈ sphere x s) : |u y| ≤ |u x| + C * s := by
  have hx : x ∈ ball x R := mem_ball_self (hs.trans_lt hsR)
  have hy' : y ∈ ball x R := mem_ball.2 ((mem_sphere.1 hy).trans_lt hsR)
  have h1 := (h.lipschitzOnWith x R hR).dist_le_mul y hy' x hx
  rw [Real.dist_eq, mem_sphere.1 hy] at h1
  have := abs_sub_abs_le_abs_sub (u y) (u x)
  linarith

theorem abs_inner_le_of_mem_sphere (h : IsVariationalSolutionQ Ω C Q u χ) (hR : ball x R ⊆ Ω)
    (hs : 0 ≤ s) (hsR : s < R) {y : Rn n} (hy : y ∈ sphere x s) :
    |⟪gradient u y, y - x⟫| ≤ C * s := by
  rw [← Real.norm_eq_abs]
  refine (norm_inner_le_norm _ _).trans ?_
  rw [← dist_eq_norm, mem_sphere.1 hy]
  exact mul_le_mul_of_nonneg_right (h.norm_gradient_le (sphere_subset_of_lt hR hsR hy)) hs

theorem sphereIntegrable_u_sq (h : IsVariationalSolutionQ Ω C Q u χ) (hR : ball x R ⊆ Ω)
    (hs : 0 ≤ s) (hsR : s < R) : SphereIntegrable (fun y => u y ^ 2) x s :=
  (h.continuousOn.mono (sphere_subset_of_lt hR hsR)).pow 2 |>.sphereIntegrable hs

theorem sphereIntegrable_inner_sq (h : IsVariationalSolutionQ Ω C Q u χ) (hR : ball x R ⊆ Ω)
    (hs : 0 ≤ s) (hsR : s < R) : SphereIntegrable (fun y => ⟪gradient u y, y - x⟫ ^ 2) x s :=
  sphereIntegrable_of_bound
    (aestronglyMeasurable_sphere_of_measurable
      (((measurable_gradient u).inner (measurable_id.sub_const x)).pow_const 2))
    (fun y hy => by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (h.abs_inner_le_of_mem_sphere hR hs hsR hy) 2) hs

theorem sphereIntegrable_mix (h : IsVariationalSolutionQ Ω C Q u χ) (hR : ball x R ⊆ Ω)
    (hs : 0 ≤ s) (hsR : s < R) :
    SphereIntegrable (fun y => u y * ⟪gradient u y, y - x⟫) x s := by
  have hm : AEStronglyMeasurable (fun ω : sphere (0 : Rn n) 1 => u (x + s • (ω : Rn n)) *
      ⟪gradient u (x + s • (ω : Rn n)), x + s • (ω : Rn n) - x⟫) (sphereMeasure n) :=
    ((h.continuousOn.comp_continuous (continuous_add_smul_sphere x s)
      (add_smul_mem_of_lt hR hs hsR)).aestronglyMeasurable).mul
      (aestronglyMeasurable_sphere_of_measurable (g := fun y => ⟪gradient u y, y - x⟫)
        ((measurable_gradient u).inner (measurable_id.sub_const x)))
  exact sphereIntegrable_of_bound hm
    (fun y hy => by
      rw [abs_mul]
      exact mul_le_mul (h.abs_le_of_mem_sphere hR hs hsR hy)
        (h.abs_inner_le_of_mem_sphere hR hs hsR hy) (abs_nonneg _)
        ((abs_nonneg _).trans (h.abs_le_of_mem_sphere hR hs hsR hy))) hs

/-- **Cauchy–Schwarz on `∂B_s(x)`**: `(∫ u ∇u·(y−x))² ≤ ∫ u² ∫ (∇u·(y−x))²`. -/
theorem sq_sphereIntegral_mix_le (h : IsVariationalSolutionQ Ω C Q u χ) (hR : ball x R ⊆ Ω)
    (hs : 0 ≤ s) (hsR : s < R) :
    sphereIntegral (fun y => u y * ⟪gradient u y, y - x⟫) x s ^ 2 ≤
      sphereIntegral (fun y => u y ^ 2) x s *
        sphereIntegral (fun y => ⟪gradient u y, y - x⟫ ^ 2) x s :=
  sq_sphereIntegral_mul_le (h.sphereIntegrable_u_sq hR hs hsR)
    (h.sphereIntegrable_inner_sq hR hs hsR) (h.sphereIntegrable_mix hR hs hsR)

/-- `∫_{∂B_s(x)} (u − ∇u·(y−x))² = ∫ (∇u·(y−x))² − 2 ∫ u ∇u·(y−x) + ∫ u²`. -/
theorem sphereIntegral_sub_inner_sq (h : IsVariationalSolutionQ Ω C Q u χ) (hR : ball x R ⊆ Ω)
    (hs : 0 ≤ s) (hsR : s < R) :
    sphereIntegral (fun y => (u y - ⟪gradient u y, y - x⟫) ^ 2) x s =
      sphereIntegral (fun y => ⟪gradient u y, y - x⟫ ^ 2) x s -
        2 * sphereIntegral (fun y => u y * ⟪gradient u y, y - x⟫) x s +
        sphereIntegral (fun y => u y ^ 2) x s := by
  have e : (fun y => (u y - ⟪gradient u y, y - x⟫) ^ 2) =
      fun y => (⟪gradient u y, y - x⟫ ^ 2 - 2 * (u y * ⟪gradient u y, y - x⟫)) + u y ^ 2 := by
    ext y; ring
  have hm : SphereIntegrable (fun y => 2 * (u y * ⟪gradient u y, y - x⟫)) x s :=
    (h.sphereIntegrable_mix hR hs hsR).const_mul 2
  have hd : SphereIntegrable
      (fun y => ⟪gradient u y, y - x⟫ ^ 2 - 2 * (u y * ⟪gradient u y, y - x⟫)) x s :=
    (h.sphereIntegrable_inner_sq hR hs hsR).sub hm
  rw [e, sphereIntegral_add hd (h.sphereIntegrable_u_sq hR hs hsR),
    sphereIntegral_sub (h.sphereIntegrable_inner_sq hR hs hsR) hm, sphereIntegral_const_mul]

end Sphere

/-- The energy identity (3.8) with the normal `(y − x)`:
`∫_{B_s(x)} |∇u|² = s⁻¹ ∫_{∂B_s(x)} u ∇u·(y − x)` for a.e. `s ∈ (0, R)`. -/
theorem integral_norm_gradient_sq_eq_ae [NeZero n] (hQ : QBounds Ω Q L c C')
    (h : IsVariationalSolutionQ Ω C Q u χ) (hR : ball x R ⊆ Ω) :
    ∀ᵐ s, s ∈ Ioo 0 R → ∫ y in ball x s, ‖gradient u y‖ ^ 2 =
      s⁻¹ * sphereIntegral (fun y => u y * ⟪gradient u y, y - x⟫) x s := by
  filter_upwards [(h.isLipHarmonicPos hQ).energy_eq_sphere_ae' hR] with s hs hsR
  rw [hs hsR, ← sphereIntegral_const_mul]
  refine sphereIntegral_congr hsR.1.le fun y _ => ?_
  rw [real_inner_smul_right]
  ring

/-- **Derivative of `H`**: for a.e. `s ∈ (0, R)`,
`H_x'(s) = −(2/s) H_x(s) + (2 / s^{n+2}) ∫_{∂B_s(x)} u ∇u·(y−x)`. -/
theorem hasDerivAt_heightH_ae [NeZero n] (h : IsVariationalSolutionQ Ω C Q u χ)
    (hR : ball x R ⊆ Ω) :
    ∀ᵐ s, s ∈ Ioo 0 R →
      HasDerivAt (heightH u x) (-(2 / s) * heightH u x s +
        2 / s ^ (n + 2) * sphereIntegral (fun y => u y * ⟪gradient u y, y - x⟫) x s) s := by
  filter_upwards [(h.lipschitzOnWith x R hR).ae_hasDerivAt_sphereIntegral_sq] with s hP hsR
  have hs0 : s ≠ 0 := hsR.1.ne'
  have hinv : HasDerivAt (fun t : ℝ => (t ^ (n + 1))⁻¹)
      (-(↑(n + 1) * s ^ (n + 1 - 1)) / (s ^ (n + 1)) ^ 2) s :=
    (hasDerivAt_pow (n + 1) s).inv (pow_ne_zero (n + 1) hs0)
  refine (hinv.mul (hP hsR)).congr_deriv ?_
  rw [heightH]
  simp only [Nat.add_sub_cancel]
  push_cast
  field_simp
  ring

end IsVariationalSolutionQ

namespace IsVariationalSolution

open Kernel

variable {Ω : Set (Rn n)} {C : ℝ≥0} {u χ : Rn n → ℝ} {x : Rn n} {R : ℝ}

/-! ### Integrability -/

theorem sq_norm_gradient_le (h : IsVariationalSolution Ω C u χ) {y : Rn n} (hy : y ∈ Ω) :
    ‖gradient u y‖ ^ 2 ≤ (C : ℝ) ^ 2 :=
  h.toQ.sq_norm_gradient_le hy

theorem integrableOn_norm_gradient_sq (h : IsVariationalSolution Ω C u χ)
    (hR : ball x R ⊆ Ω) : IntegrableOn (fun y => ‖gradient u y‖ ^ 2) (ball x R) :=
  IntegrableOn.of_bound measure_ball_lt_top
    ((measurable_gradient u).norm.pow_const 2).aestronglyMeasurable ((C : ℝ) ^ 2)
    ((ae_restrict_iff' measurableSet_ball).2 (.of_forall fun y hy => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact h.sq_norm_gradient_le (hR hy)))

theorem integrableOn_chi (h : IsVariationalSolution Ω C u χ) (hR : ball x R ⊆ Ω) :
    IntegrableOn χ (ball x R) :=
  IntegrableOn.of_bound measure_ball_lt_top (h.aestronglyMeasurable_chi measurableSet_ball hR) 1
    ((ae_restrict_iff' measurableSet_ball).2 (.of_forall fun y hy => by
      rw [Real.norm_eq_abs]; exact h.abs_chi_le_one (hR hy)))

theorem integrableOn_energy (h : IsVariationalSolution Ω C u χ) (hR : ball x R ⊆ Ω) :
    IntegrableOn (fun y => ‖gradient u y‖ ^ 2 + χ y) (ball x R) :=
  (h.integrableOn_norm_gradient_sq hR).add (h.integrableOn_chi hR)

/-- `∫_{B_R(x)} (1 − χ) = |B_1| R^n − ∫_{B_R(x)} χ`. -/
theorem integral_one_sub_chi (h : IsVariationalSolution Ω C u χ) (hR : ball x R ⊆ Ω)
    (hR0 : 0 < R) :
    ∫ y in ball x R, (1 - χ y) = unitBallVolume n * R ^ n - ∫ y in ball x R, χ y := by
  have h1 : IntegrableOn (fun _ : Rn n => (1 : ℝ)) (ball x R) :=
    integrableOn_const measure_ball_lt_top.ne
  rw [integral_sub h1 (h.integrableOn_chi hR), setIntegral_const, smul_eq_mul, mul_one,
    measureReal_def, volume_ball_toReal x hR0, mul_comm]

/-- `∫_{B_s(x)} (|∇u|² + χ) = ∫_{B_s(x)} |∇u|² + ∫_{B_s(x)} χ`. -/
theorem integral_energy_eq (h : IsVariationalSolution Ω C u χ) (hR : ball x R ⊆ Ω) :
    ∫ y in ball x R, (‖gradient u y‖ ^ 2 + χ y) =
      (∫ y in ball x R, ‖gradient u y‖ ^ 2) + ∫ y in ball x R, χ y :=
  integral_add (h.integrableOn_norm_gradient_sq hR) (h.integrableOn_chi hR)

section Sphere

variable {s : ℝ}

theorem aestronglyMeasurable_sphere_u (h : IsVariationalSolution Ω C u χ) (hR : ball x R ⊆ Ω)
    (hs : 0 ≤ s) (hsR : s < R) :
    AEStronglyMeasurable (fun ω : sphere (0 : Rn n) 1 => u (x + s • (ω : Rn n)))
      (sphereMeasure n) :=
  (h.continuousOn.comp_continuous (continuous_add_smul_sphere x s)
    (add_smul_mem_of_lt hR hs hsR)).aestronglyMeasurable

theorem aestronglyMeasurable_sphere_chi (h : IsVariationalSolution Ω C u χ) (hR : ball x R ⊆ Ω)
    (hs : 0 ≤ s) (hsR : s < R) :
    AEStronglyMeasurable (fun ω : sphere (0 : Rn n) 1 => χ (x + s • (ω : Rn n)))
      (sphereMeasure n) :=
  h.toQ.aestronglyMeasurable_sphere_chi hR hs hsR

/-- `|u| ≤ |u(x)| + C s` on `∂B_s(x)`. -/
theorem abs_le_of_mem_sphere (h : IsVariationalSolution Ω C u χ) (hR : ball x R ⊆ Ω)
    (hs : 0 ≤ s) (hsR : s < R) {y : Rn n} (hy : y ∈ sphere x s) : |u y| ≤ |u x| + C * s :=
  h.toQ.abs_le_of_mem_sphere hR hs hsR hy

theorem abs_inner_le_of_mem_sphere (h : IsVariationalSolution Ω C u χ) (hR : ball x R ⊆ Ω)
    (hs : 0 ≤ s) (hsR : s < R) {y : Rn n} (hy : y ∈ sphere x s) :
    |⟪gradient u y, y - x⟫| ≤ C * s :=
  h.toQ.abs_inner_le_of_mem_sphere hR hs hsR hy

theorem sphereIntegrable_u_sq (h : IsVariationalSolution Ω C u χ) (hR : ball x R ⊆ Ω)
    (hs : 0 ≤ s) (hsR : s < R) : SphereIntegrable (fun y => u y ^ 2) x s :=
  h.toQ.sphereIntegrable_u_sq hR hs hsR

theorem sphereIntegrable_inner_sq (h : IsVariationalSolution Ω C u χ) (hR : ball x R ⊆ Ω)
    (hs : 0 ≤ s) (hsR : s < R) : SphereIntegrable (fun y => ⟪gradient u y, y - x⟫ ^ 2) x s :=
  h.toQ.sphereIntegrable_inner_sq hR hs hsR

theorem sphereIntegrable_mix (h : IsVariationalSolution Ω C u χ) (hR : ball x R ⊆ Ω)
    (hs : 0 ≤ s) (hsR : s < R) :
    SphereIntegrable (fun y => u y * ⟪gradient u y, y - x⟫) x s :=
  h.toQ.sphereIntegrable_mix hR hs hsR

theorem sphereIntegrable_energy (h : IsVariationalSolution Ω C u χ) (hR : ball x R ⊆ Ω)
    (hs : 0 ≤ s) (hsR : s < R) :
    SphereIntegrable (fun y => ‖gradient u y‖ ^ 2 + χ y) x s := by
  have hm : AEStronglyMeasurable (fun ω : sphere (0 : Rn n) 1 =>
      ‖gradient u (x + s • (ω : Rn n))‖ ^ 2 + χ (x + s • (ω : Rn n))) (sphereMeasure n) :=
    (aestronglyMeasurable_sphere_of_measurable (g := fun y => ‖gradient u y‖ ^ 2)
      ((measurable_gradient u).norm.pow_const 2)).add
      (h.aestronglyMeasurable_sphere_chi hR hs hsR)
  exact sphereIntegrable_of_bound (M := (C : ℝ) ^ 2 + 1) hm
    (fun y hy => by
      have hyΩ := sphere_subset_of_lt hR hsR hy
      have a1 := h.sq_norm_gradient_le hyΩ
      have a2 := h.abs_chi_le_one hyΩ
      have a3 : 0 ≤ ‖gradient u y‖ ^ 2 := sq_nonneg _
      rw [abs_le] at a2 ⊢
      constructor <;> linarith) hs

/-- **Cauchy–Schwarz on `∂B_s(x)`**: `(∫ u ∇u·(y−x))² ≤ ∫ u² ∫ (∇u·(y−x))²`. -/
theorem sq_sphereIntegral_mix_le (h : IsVariationalSolution Ω C u χ) (hR : ball x R ⊆ Ω)
    (hs : 0 ≤ s) (hsR : s < R) :
    sphereIntegral (fun y => u y * ⟪gradient u y, y - x⟫) x s ^ 2 ≤
      sphereIntegral (fun y => u y ^ 2) x s *
        sphereIntegral (fun y => ⟪gradient u y, y - x⟫ ^ 2) x s :=
  h.toQ.sq_sphereIntegral_mix_le hR hs hsR

/-- `∫_{∂B_s(x)} (u − ∇u·(y−x))² = ∫ (∇u·(y−x))² − 2 ∫ u ∇u·(y−x) + ∫ u²`. -/
theorem sphereIntegral_sub_inner_sq (h : IsVariationalSolution Ω C u χ) (hR : ball x R ⊆ Ω)
    (hs : 0 ≤ s) (hsR : s < R) :
    sphereIntegral (fun y => (u y - ⟪gradient u y, y - x⟫) ^ 2) x s =
      sphereIntegral (fun y => ⟪gradient u y, y - x⟫ ^ 2) x s -
        2 * sphereIntegral (fun y => u y * ⟪gradient u y, y - x⟫) x s +
        sphereIntegral (fun y => u y ^ 2) x s :=
  h.toQ.sphereIntegral_sub_inner_sq hR hs hsR

end Sphere

/-! ### Identity (3.9) and the derivatives of `D` and `H` -/

/-- The energy identity (3.8) with the normal `(y − x)`:
`∫_{B_s(x)} |∇u|² = s⁻¹ ∫_{∂B_s(x)} u ∇u·(y − x)` for a.e. `s ∈ (0, R)`. -/
theorem integral_norm_gradient_sq_eq_ae [NeZero n] (h : IsVariationalSolution Ω C u χ)
    (hR : ball x R ⊆ Ω) :
    ∀ᵐ s, s ∈ Ioo 0 R → ∫ y in ball x s, ‖gradient u y‖ ^ 2 =
      s⁻¹ * sphereIntegral (fun y => u y * ⟪gradient u y, y - x⟫) x s :=
  IsVariationalSolutionQ.integral_norm_gradient_sq_eq_ae (QBounds.one Ω) h.toQ hR

/-- **Identity (3.9)**, multiplied by `s^n`: for a.e. `s ∈ (0, R)`,
`n ∫_{B_s(x)} (|∇u|² + χ) = s ∫_{∂B_s(x)} (|∇u|² + χ) − (2/s) ∫_{∂B_s(x)} (∇u·(y−x))²
  + (2/s) ∫_{∂B_s(x)} u ∇u·(y−x)`.
It combines the Rellich–Pohozaev identity (3.7) with the energy identity (3.8). -/
theorem integral_energy_identity_ae [NeZero n] (h : IsVariationalSolution Ω C u χ)
    (hR : ball x R ⊆ Ω) :
    ∀ᵐ s, s ∈ Ioo 0 R →
      (n : ℝ) * ∫ y in ball x s, (‖gradient u y‖ ^ 2 + χ y) =
        s * sphereIntegral (fun y => ‖gradient u y‖ ^ 2 + χ y) x s -
          2 / s * sphereIntegral (fun y => ⟪gradient u y, y - x⟫ ^ 2) x s +
          2 / s * sphereIntegral (fun y => u y * ⟪gradient u y, y - x⟫) x s := by
  filter_upwards [h.rellich_pohozaev_ae hR, h.integral_norm_gradient_sq_eq_ae hR]
    with s hRP hG hsR
  have hs0 : 0 < s := hsR.1
  have hsR' : ball x s ⊆ Ω := (ball_subset_ball hsR.2.le).trans hR
  have hP : sphereIntegral (fun y => ‖gradient u y‖ ^ 2 + χ y -
      2 * ⟪gradient u y, ‖y - x‖⁻¹ • (y - x)⟫ ^ 2) x s =
      sphereIntegral (fun y => ‖gradient u y‖ ^ 2 + χ y) x s -
        2 * (s ^ 2)⁻¹ * sphereIntegral (fun y => ⟪gradient u y, y - x⟫ ^ 2) x s := by
    have e : sphereIntegral (fun y => ‖gradient u y‖ ^ 2 + χ y -
        2 * ⟪gradient u y, ‖y - x‖⁻¹ • (y - x)⟫ ^ 2) x s =
        sphereIntegral (fun y => ‖gradient u y‖ ^ 2 + χ y -
          2 * (s ^ 2)⁻¹ * ⟪gradient u y, y - x⟫ ^ 2) x s := by
      refine sphereIntegral_congr hs0.le fun y hy => ?_
      rw [mem_sphere, dist_eq_norm] at hy
      rw [hy, real_inner_smul_right]
      ring
    have hI : SphereIntegrable (fun y => 2 * (s ^ 2)⁻¹ * ⟪gradient u y, y - x⟫ ^ 2) x s :=
      (h.sphereIntegrable_inner_sq hR hs0.le hsR.2).const_mul _
    rw [e, sphereIntegral_sub (h.sphereIntegrable_energy hR hs0.le hsR.2) hI,
      sphereIntegral_const_mul]
  replace hRP := hRP hsR
  rw [hP] at hRP
  rw [h.integral_energy_eq hsR']
  set G := ∫ y in ball x s, ‖gradient u y‖ ^ 2
  set X := ∫ y in ball x s, χ y
  set T := sphereIntegral (fun y => ‖gradient u y‖ ^ 2 + χ y) x s
  set Rad := sphereIntegral (fun y => ⟪gradient u y, y - x⟫ ^ 2) x s
  set Mix := sphereIntegral (fun y => u y * ⟪gradient u y, y - x⟫) x s
  have hG' := hG hsR
  have e1 : s * (2 * (s ^ 2)⁻¹ * Rad) = 2 / s * Rad := by field_simp
  have e2 : s⁻¹ * Mix = Mix / s := inv_mul_eq_div s Mix
  rw [mul_sub, e1] at hRP
  rw [e2] at hG'
  have e3 : 2 / s * Mix = 2 * (Mix / s) := by ring
  rw [e3, ← hG']
  linarith

/-- **Identity (3.9)**: for a.e. `s ∈ (0, R)`,
`n D_x(s) = s^{-n} (s ∫_{∂B_s(x)} (|∇u|² + χ) − (2/s) ∫_{∂B_s(x)} (∇u·(y−x))²
  + (2/s) ∫_{∂B_s(x)} u ∇u·(y−x))`. -/
theorem energyD_identity_ae [NeZero n] (h : IsVariationalSolution Ω C u χ)
    (hR : ball x R ⊆ Ω) :
    ∀ᵐ s, s ∈ Ioo 0 R →
      (n : ℝ) * energyD u χ x s =
        (s ^ n)⁻¹ * (s * sphereIntegral (fun y => ‖gradient u y‖ ^ 2 + χ y) x s -
          2 / s * sphereIntegral (fun y => ⟪gradient u y, y - x⟫ ^ 2) x s +
          2 / s * sphereIntegral (fun y => u y * ⟪gradient u y, y - x⟫) x s) := by
  filter_upwards [h.integral_energy_identity_ae hR] with s hs hsR
  rw [energyD, ← hs hsR]
  ring

/-- **Derivative of `D`** (proof of Proposition 3.4): for a.e. `s ∈ (0, R)`,
`D_x'(s) = (2 / s^{n+2}) (∫_{∂B_s(x)} (∇u·(y−x))² − ∫_{∂B_s(x)} u ∇u·(y−x))`. -/
theorem hasDerivAt_energyD_ae [NeZero n] (h : IsVariationalSolution Ω C u χ)
    (hR : ball x R ⊆ Ω) :
    ∀ᵐ s, s ∈ Ioo 0 R →
      HasDerivAt (energyD u χ x)
        (2 / s ^ (n + 2) * (sphereIntegral (fun y => ⟪gradient u y, y - x⟫ ^ 2) x s -
          sphereIntegral (fun y => u y * ⟪gradient u y, y - x⟫) x s)) s := by
  filter_upwards [h.integral_energy_identity_ae hR,
    ae_hasDerivAt_integral_ball (h.integrableOn_energy hR)] with s hid hF hsR
  have hs0 : s ≠ 0 := hsR.1.ne'
  have hinv : HasDerivAt (fun t : ℝ => (t ^ n)⁻¹) (-(↑n * s ^ (n - 1)) / (s ^ n) ^ 2) s :=
    (hasDerivAt_pow n s).inv (pow_ne_zero n hs0)
  refine (hinv.mul (hF hsR)).congr_deriv ?_
  have key := hid hsR
  set F := ∫ y in ball x s, (‖gradient u y‖ ^ 2 + χ y)
  set T := sphereIntegral (fun y => ‖gradient u y‖ ^ 2 + χ y) x s
  set Rad := sphereIntegral (fun y => ⟪gradient u y, y - x⟫ ^ 2) x s
  set Mix := sphereIntegral (fun y => u y * ⟪gradient u y, y - x⟫) x s
  obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos (NeZero.pos n)).symm⟩
  subst hm
  simp only [Nat.add_sub_cancel]
  push_cast at key ⊢
  have hF' : F = (s * T - 2 / s * Rad + 2 / s * Mix) / (m + 1) := by
    rw [← key]; field_simp
  rw [hF']
  field_simp
  ring

/-- **Derivative of `H`** (proof of Proposition 3.4): for a.e. `s ∈ (0, R)`,
`H_x'(s) = −(2/s) H_x(s) + (2 / s^{n+2}) ∫_{∂B_s(x)} u ∇u·(y−x)`. -/
theorem hasDerivAt_heightH_ae [NeZero n] (h : IsVariationalSolution Ω C u χ)
    (hR : ball x R ⊆ Ω) :
    ∀ᵐ s, s ∈ Ioo 0 R →
      HasDerivAt (heightH u x) (-(2 / s) * heightH u x s +
        2 / s ^ (n + 2) * sphereIntegral (fun y => u y * ⟪gradient u y, y - x⟫) x s) s :=
  h.toQ.hasDerivAt_heightH_ae hR

/-- **Derivative of `M`** (Proposition 3.4): for a.e. `s ∈ (0, R)`,
`M_x'(s) = (2 / s^{n+2}) ∫_{∂B_s(x)} (u(y) − (y − x)·∇u(y))²`. -/
theorem hasDerivAt_monotonicityM_ae [NeZero n] (h : IsVariationalSolution Ω C u χ)
    (hR : ball x R ⊆ Ω) :
    ∀ᵐ s, s ∈ Ioo 0 R →
      HasDerivAt (monotonicityM u χ x)
        (2 / s ^ (n + 2) * sphereIntegral (fun y => (u y - ⟪gradient u y, y - x⟫) ^ 2) x s) s := by
  filter_upwards [h.hasDerivAt_energyD_ae hR, h.hasDerivAt_heightH_ae hR] with s hD hH hsR
  have hs0 : s ≠ 0 := hsR.1.ne'
  refine ((hD hsR).sub (hH hsR)).congr_deriv ?_
  rw [h.sphereIntegral_sub_inner_sq hR hsR.1.le hsR.2, heightH]
  field_simp
  ring

/-! ### The radial data of a variational solution -/

/-- `s ↦ ∫_{B_s(x)} (|∇u|² + χ)` is Lipschitz on `[0, b]`, `b < R`. -/
theorem exists_lipschitzOnWith_integral_energy [NeZero n] (h : IsVariationalSolution Ω C u χ)
    (hR : ball x R ⊆ Ω) {b : ℝ} (hbR : b < R) :
    ∃ K, LipschitzOnWith K (fun s => ∫ y in ball x s, (‖gradient u y‖ ^ 2 + χ y)) (Icc 0 b) := by
  have hb : ball x b ⊆ Ω := (ball_subset_ball hbR.le).trans hR
  refine ⟨_, lipschitzOnWith_integral_ball (M := (C : ℝ) ^ 2 + 1)
    (h.integrableOn_energy hb).aestronglyMeasurable fun y hy => ?_⟩
  have hyΩ := hb hy
  have a1 := h.sq_norm_gradient_le hyΩ
  have a2 := h.abs_chi_le_one hyΩ
  have a3 : 0 ≤ ‖gradient u y‖ ^ 2 := sq_nonneg _
  rw [abs_le] at a2 ⊢
  constructor <;> linarith

/-- The radial data (`Abstract.RadialData`) of a variational solution `(u, χ)` at `x`, on
`[a, b]` with `0 < a ≤ b < R` and `B_R(x) ⊆ Ω`, with `ω = |B_1|`. The radial integrals are
`∫_{B_s(x)} |∇u|²`, `∫_{B_s(x)} χ`, `∫_{∂B_s(x)} u²`, `∫_{∂B_s(x)} u ∇u·(y−x)`,
`∫_{∂B_s(x)} (∇u·(y−x))²`, and `D`, `H` are `energyD u χ x`, `heightH u x`. -/
def radialData [NeZero n] (h : IsVariationalSolution Ω C u χ) (hR : ball x R ⊆ Ω) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hbR : b < R) : Abstract.RadialData n (unitBallVolume n) a b where
  gradInt s := ∫ y in ball x s, ‖gradient u y‖ ^ 2
  chiInt s := ∫ y in ball x s, χ y
  sphSq s := sphereIntegral (fun y => u y ^ 2) x s
  sphMix s := sphereIntegral (fun y => u y * ⟪gradient u y, y - x⟫) x s
  sphRad s := sphereIntegral (fun y => ⟪gradient u y, y - x⟫ ^ 2) x s
  energyD := energyD u χ x
  heightH := heightH u x
  pos := ha
  le := hab
  energyD_eq s hs := by
    have hsΩ : ball x s ⊆ Ω := (ball_subset_ball (hs.2.trans hbR.le)).trans hR
    rw [energyD, h.integral_energy_eq hsΩ, div_eq_inv_mul]
  heightH_eq s _ := by rw [heightH, div_eq_inv_mul]
  lipschitzOnWith_energyD := by
    obtain ⟨K, hK⟩ := h.exists_lipschitzOnWith_integral_energy hR hbR
    exact exists_lipschitzOnWith_inv_pow_mul (hK.mono (Icc_subset_Icc_left ha.le)) ha n
  lipschitzOnWith_heightH := by
    obtain ⟨K, hK⟩ := (h.lipschitzOnWith x R hR).lipschitzOnWith_sphereIntegral_sq hbR
    exact exists_lipschitzOnWith_inv_pow_mul (hK.mono (Icc_subset_Icc_left ha.le)) ha (n + 1)
  chiInt_le s hs := by
    have hs0 : 0 < s := ha.trans_le hs.1
    have hsΩ : ball x s ⊆ Ω := (ball_subset_ball (hs.2.trans hbR.le)).trans hR
    have h1 : IntegrableOn (fun _ : Rn n => (1 : ℝ)) (ball x s) :=
      integrableOn_const measure_ball_lt_top.ne
    calc ∫ y in ball x s, χ y ≤ ∫ y in ball x s, (1 : ℝ) :=
          setIntegral_mono_on (h.integrableOn_chi hsΩ) h1 measurableSet_ball fun y hy =>
            (abs_le.1 (h.abs_chi_le_one (hsΩ hy))).2
      _ = unitBallVolume n * s ^ n := by
          rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def,
            volume_ball_toReal x hs0, mul_comm]
  monotoneOn_sub_chiInt := by
    have key : ∀ s ∈ Icc a b, unitBallVolume n * s ^ n - ∫ y in ball x s, χ y =
        ∫ y in ball x s, (1 - χ y) := by
      intro s hs
      have hs0 : 0 < s := ha.trans_le hs.1
      have hsΩ : ball x s ⊆ Ω := (ball_subset_ball (hs.2.trans hbR.le)).trans hR
      rw [h.integral_one_sub_chi hsΩ hs0]
    intro s hs t ht hst
    simp only
    rw [key s hs, key t ht]
    have htΩ : ball x t ⊆ Ω := (ball_subset_ball (ht.2.trans hbR.le)).trans hR
    have h1 : IntegrableOn (fun _ : Rn n => (1 : ℝ)) (ball x t) :=
      integrableOn_const measure_ball_lt_top.ne
    refine setIntegral_mono_set (h1.sub (h.integrableOn_chi htΩ))
      ((ae_restrict_iff' measurableSet_ball).2 (.of_forall fun y hy => ?_))
      (.of_forall (ball_subset_ball hst))
    exact sub_nonneg.2 (abs_le.1 (h.abs_chi_le_one (htΩ hy))).2
  gradInt_eq := by
    refine ae_mem_Ioo_imp_mono ha.le hbR.le ?_
    filter_upwards [h.integral_norm_gradient_sq_eq_ae hR] with s hs hsR
    rw [hs hsR, inv_mul_eq_div]
  hasDerivAt_energyD := ae_mem_Ioo_imp_mono ha.le hbR.le (h.hasDerivAt_energyD_ae hR)
  hasDerivAt_heightH := ae_mem_Ioo_imp_mono ha.le hbR.le (h.hasDerivAt_heightH_ae hR)
  sphSq_nonneg := .of_forall fun s hs =>
    sphereIntegral_nonneg (ha.trans hs.1).le fun y _ => sq_nonneg _
  sphRad_nonneg := .of_forall fun s hs =>
    sphereIntegral_nonneg (ha.trans hs.1).le fun y _ => sq_nonneg _
  sq_sphMix_le := .of_forall fun s hs =>
    h.sq_sphereIntegral_mix_le hR (ha.trans hs.1).le (hs.2.trans_le hbR.le)

section RadialData

variable [NeZero n] (h : IsVariationalSolution Ω C u χ) (hR : ball x R ⊆ Ω) {a b : ℝ}
  (ha : 0 < a) (hab : a ≤ b) (hbR : b < R)

@[simp] theorem radialData_energyD : (h.radialData hR ha hab hbR).energyD = energyD u χ x := rfl

@[simp] theorem radialData_heightH : (h.radialData hR ha hab hbR).heightH = heightH u x := rfl

@[simp] theorem radialData_monotonicityM :
    (h.radialData hR ha hab hbR).monotonicityM = monotonicityM u χ x := rfl

@[simp] theorem radialData_frequencyN :
    (h.radialData hR ha hab hbR).frequencyN = frequencyN u χ x := rfl

theorem radialData_volumeV {s : ℝ} (hs : s ∈ Icc a b) :
    (h.radialData hR ha hab hbR).volumeV s = volumeV u χ x s := by
  have hs0 : 0 < s := ha.trans_le hs.1
  have hsΩ : ball x s ⊆ Ω := (ball_subset_ball (hs.2.trans hbR.le)).trans hR
  simp only [Abstract.RadialData.volumeV, radialData, volumeV]
  rw [h.integral_one_sub_chi hsΩ hs0]
  congr 1
  field_simp

end RadialData

/-! ### Proposition 3.4: monotonicity -/

/-- `M_x` is Lipschitz on `[a, b]` for `0 < a ≤ b < R` (proof of Proposition 3.4). -/
theorem exists_lipschitzOnWith_monotonicityM [NeZero n] (h : IsVariationalSolution Ω C u χ)
    (hR : ball x R ⊆ Ω) {a b : ℝ} (ha : 0 < a) (hbR : b < R) :
    ∃ K, LipschitzOnWith K (monotonicityM u χ x) (Icc a b) := by
  rcases le_total a b with hab | hba
  · set d := h.radialData hR ha hab hbR
    obtain ⟨K₁, hK₁⟩ := d.lipschitzOnWith_energyD
    obtain ⟨K₂, hK₂⟩ := d.lipschitzOnWith_heightH
    exact ⟨K₁ + K₂, hK₁.sub hK₂⟩
  · refine ⟨0, fun s hs t ht => ?_⟩
    have : s = t := by
      rcases hs with ⟨h1, h2⟩; rcases ht with ⟨h3, h4⟩
      exact le_antisymm (h2.trans (hba.trans h3)) (h4.trans (hba.trans h1))
    simp [this]

/-- **Proposition 3.4**: `s ↦ M_x(u; s)` is nondecreasing on `(0, R)` when
`B_R(x) ⊆ Ω`. -/
theorem monotoneOn_monotonicityM [NeZero n] (h : IsVariationalSolution Ω C u χ)
    (hR : ball x R ⊆ Ω) : MonotoneOn (monotonicityM u χ x) (Ioo 0 R) := by
  intro s hs t ht hst
  have := (h.radialData hR hs.1 hst ht.2).monotoneOn_monotonicityM
  exact this ⟨le_rfl, hst⟩ ⟨hst, le_rfl⟩ hst

/-- **Proposition 3.4** on `(0, R]` when `B̄_R(x) ⊆ Ω`. -/
theorem monotoneOn_monotonicityM_Ioc [NeZero n] (h : IsVariationalSolution Ω C u χ)
    (hR : closedBall x R ⊆ Ω) : MonotoneOn (monotonicityM u χ x) (Ioc 0 R) := by
  intro s hs t ht hst
  obtain ⟨R', hRR', hR'⟩ := exists_gt_ball_subset h.isOpen (ht.1.le.trans ht.2) hR
  exact h.monotoneOn_monotonicityM hR' ⟨hs.1, hs.2.trans_lt hRR'⟩ ⟨ht.1, ht.2.trans_lt hRR'⟩ hst

/-- `M_x(s) ≤ M_x(t)` for `0 < s ≤ t` and `B̄_t(x) ⊆ Ω`. -/
theorem monotonicityM_le [NeZero n] (h : IsVariationalSolution Ω C u χ) {s t : ℝ}
    (hs : 0 < s) (hst : s ≤ t) (ht : closedBall x t ⊆ Ω) :
    monotonicityM u χ x s ≤ monotonicityM u χ x t :=
  h.monotoneOn_monotonicityM_Ioc ht ⟨hs, hst⟩ ⟨hs.trans_le hst, le_rfl⟩ hst

end IsVariationalSolution

end InnerVariational
