/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Frequency.AbstractError
public import InnerVariational.Kernel.RellichPohozaev
public import InnerVariational.Monotonicity.Radial
public import InnerVariational.Defs.VariationalSolutionQ
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Algebra.Ring.IsFormallyReal
import InnerVariational.Kernel.Subharmonic
import InnerVariational.Kernel.Energy
public import InnerVariational.Basic.SphereIntegral
import InnerVariational.Basic.Polar
import InnerVariational.Basic.LipschitzFTC

/-!
# The monotonicity formula with a Lipschitz coefficient

Let `(u, χ)` be a variational solution on `Ω` for a coefficient `Q` with `QBounds Ω Q L c C'`,
that is, a critical point of `∫ (|∇u|² + Q² χ)` with respect to inner variations, and let
`B_R(x) ⊆ Ω`. This file instantiates the radial calculus with an error term,
`Abstract.RadialDataErr` of `Frequency/AbstractError.lean`, for `(u, χ)` at `x`.

## The weighted normalisation

With `G(s) = ∫_{B_s(x)} |∇u|²` and `W_Q(s) = ∫_{B_s(x)} Q² (1 − χ)`, set
`ω = Q(x)² |B_1|` and
`D^w_x(s) = s^{-n} (G(s) − W_Q(s)) + ω` (`weightedEnergyD`),
`M^w_x(s) = D^w_x(s) − H_x(s)` (`weightedMonotonicityM`).
In the notation of `RadialDataErr`, `chiInt s = ω sⁿ − W_Q(s)`. The Rellich–Pohozaev identity with
the coefficient `Q` (`IsVariationalSolutionQ.rellich_pohozaev_weighted_ae`) and the energy
identity (3.8), which only uses the harmonicity of `u` on `{u > 0}`, give for a.e. `s`

`(D^w)'(s) = (2 / s^{n+2}) ∫_{∂B_s(x)} ((∇u·(y−x))² − u ∇u·(y−x)) + e(s)`,
`e(s) = −s^{-n-1} ∫_{B_s(x)} (1 − χ) ∇(Q²)·(y − x)`.

Since `|∇(Q²)| ≤ 2 C' L` and `Q² ≥ c²` on `Ω`, and `0 ≤ 1 − χ ≤ 1`,
`|e(s)| ≤ κ s^{-n} W_Q(s)` with `κ = 2 C' L / c²`.

The paper treats `Q ≡ 1`, where `D^w = D`, `e = 0`, and this is the radial data of
`Monotonicity/Radial.lean`.

## Main definitions

* `weightedEnergyD`, `weightedMonotonicityM`: the quantities `D^w` and `M^w` above.
* `IsVariationalSolutionQ.radialDataErr`: the radial data with error of `(u, χ)` at `x` on
  `[a, b]`, `0 < a ≤ b < R`, with `ω = Q(x)² |B_1|` and `κ = 2 C' L / c²`.

## Main results

* `IsVariationalSolutionQ.hasDerivAt_weightedEnergyD_ae`: the derivative of `D^w`.
* `IsVariationalSolutionQ.abs_errTerm_le`: the bound on the error term.
* `IsVariationalSolutionQ.monotoneOn_weightedMonotonicityM_add`: the almost-monotonicity
  `M^w_x(s) + A s` nondecreasing on `(0, R)`, `A = κ C'² |B_1|`.
* `IsVariationalSolutionQ.abs_monotonicityMq_sub_le`: `|M^{Q(x)}_x(s) − M^w_x(s)| ≤ 2 C' L |B_1| s`,
  comparing with the Weiss energy `monotonicityMq` with the coefficient frozen at `Q(x)`.

## References

* D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
  DOI 10.1002/cpa.22226; arXiv:2306.10131. Unqualified result and equation numbers in this file
  refer to this paper, in the numbering of arXiv v2.
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

/-- The weighted energy `D^w_x(s) = s^{-n} ∫_{B_s(x)} (|∇u|² − Q² (1 − χ)) + Q(x)² |B_1|`.
For `Q ≡ 1` and `s > 0` it is `energyD u χ x s`. -/
def weightedEnergyD (Q u χ : Rn n → ℝ) (x : Rn n) (s : ℝ) : ℝ :=
  (s ^ n)⁻¹ * (∫ y in ball x s, (‖gradient u y‖ ^ 2 - Q y ^ 2 * (1 - χ y))) +
    Q x ^ 2 * unitBallVolume n

/-- The weighted Weiss energy `M^w_x(s) = D^w_x(s) − H_x(s)`. -/
def weightedMonotonicityM (Q u χ : Rn n → ℝ) (x : Rn n) (s : ℝ) : ℝ :=
  weightedEnergyD Q u χ x s - heightH u x s

/-- The constant `κ = 2 C' L / c²` bounding `‖∇(Q²)‖ / Q²`. -/
def weissKappa (L : ℝ≥0) (c C' : ℝ) : ℝ := 2 * C' * L / c ^ 2

/-- The constant `A = κ C'² |B_1|` of the almost-monotonicity of `M^w`. -/
def weissConst (n : ℕ) (L : ℝ≥0) (c C' : ℝ) : ℝ := weissKappa L c C' * (C' ^ 2 * unitBallVolume n)

namespace IsVariationalSolutionQ

open Kernel IsVariationalSolution

variable {Ω : Set (Rn n)} {C : ℝ≥0} {Q u χ : Rn n → ℝ} {x : Rn n} {R : ℝ} {L : ℝ≥0}
  {c C' : ℝ}

/-! ### Integrability and pointwise bounds -/

theorem one_sub_chi_nonneg (h : IsVariationalSolutionQ Ω C Q u χ) {y : Rn n} (hy : y ∈ Ω) :
    0 ≤ 1 - χ y :=
  sub_nonneg.2 (h.chi_le_one hy)

theorem one_sub_chi_le_one (h : IsVariationalSolutionQ Ω C Q u χ) {y : Rn n} (hy : y ∈ Ω) :
    1 - χ y ≤ 1 := by
  linarith [h.chi_nonneg hy]

theorem weight_nonneg (h : IsVariationalSolutionQ Ω C Q u χ) {y : Rn n} (hy : y ∈ Ω) :
    0 ≤ Q y ^ 2 * (1 - χ y) :=
  mul_nonneg (sq_nonneg _) (h.one_sub_chi_nonneg hy)

theorem weight_le (hQ : QBounds Ω Q L c C') (h : IsVariationalSolutionQ Ω C Q u χ) {y : Rn n}
    (hy : y ∈ Ω) : Q y ^ 2 * (1 - χ y) ≤ C' ^ 2 :=
  (mul_le_mul (hQ.sq_le hy) (h.one_sub_chi_le_one hy) (h.one_sub_chi_nonneg hy)
    (sq_nonneg _)).trans (le_of_eq (mul_one _))

theorem integrableOn_norm_gradient_sq (hQ : QBounds Ω Q L c C')
    (h : IsVariationalSolutionQ Ω C Q u χ) {s : ℝ} (hs : ball x s ⊆ Ω) :
    IntegrableOn (fun y => ‖gradient u y‖ ^ 2) (ball x s) :=
  (h.integrableOn_rellich_weighted_terms (x := x) hQ hs).1

theorem integrableOn_weight (hQ : QBounds Ω Q L c C') (h : IsVariationalSolutionQ Ω C Q u χ)
    {s : ℝ} (hs : ball x s ⊆ Ω) : IntegrableOn (fun y => Q y ^ 2 * (1 - χ y)) (ball x s) :=
  (h.integrableOn_rellich_weighted_terms (x := x) hQ hs).2.1

theorem integrableOn_errTerm (hQ : QBounds Ω Q L c C') (h : IsVariationalSolutionQ Ω C Q u χ)
    {s : ℝ} (hs : ball x s ⊆ Ω) :
    IntegrableOn (fun y => (1 - χ y) * fderiv ℝ (fun z => Q z ^ 2) y (y - x)) (ball x s) :=
  (h.integrableOn_rellich_weighted_terms (x := x) hQ hs).2.2

theorem integrableOn_one_sub_chi (h : IsVariationalSolutionQ Ω C Q u χ) {s : ℝ}
    (hs : ball x s ⊆ Ω) : IntegrableOn (fun y => 1 - χ y) (ball x s) :=
  (integrableOn_const measure_ball_lt_top.ne).sub
    (IntegrableOn.of_bound measure_ball_lt_top (h.aestronglyMeasurable_chi measurableSet_ball hs) 1
      ((ae_restrict_iff' measurableSet_ball).2 (.of_forall fun y hy => by
        rw [Real.norm_eq_abs]; exact h.abs_chi_le_one (hs hy))))

theorem integrableOn_weightedEnergy (hQ : QBounds Ω Q L c C')
    (h : IsVariationalSolutionQ Ω C Q u χ) {s : ℝ} (hs : ball x s ⊆ Ω) :
    IntegrableOn (fun y => ‖gradient u y‖ ^ 2 - Q y ^ 2 * (1 - χ y)) (ball x s) :=
  (h.integrableOn_norm_gradient_sq hQ hs).sub (h.integrableOn_weight hQ hs)

theorem integral_weightedEnergy_eq (hQ : QBounds Ω Q L c C')
    (h : IsVariationalSolutionQ Ω C Q u χ) {s : ℝ} (hs : ball x s ⊆ Ω) :
    ∫ y in ball x s, (‖gradient u y‖ ^ 2 - Q y ^ 2 * (1 - χ y)) =
      (∫ y in ball x s, ‖gradient u y‖ ^ 2) - ∫ y in ball x s, Q y ^ 2 * (1 - χ y) :=
  integral_sub (h.integrableOn_norm_gradient_sq hQ hs) (h.integrableOn_weight hQ hs)

theorem integral_weight_nonneg (h : IsVariationalSolutionQ Ω C Q u χ) {s : ℝ}
    (hs : ball x s ⊆ Ω) : 0 ≤ ∫ y in ball x s, Q y ^ 2 * (1 - χ y) :=
  setIntegral_nonneg measurableSet_ball fun _ hy => h.weight_nonneg (hs hy)

/-- `W_Q(s) ≤ C'² |B_1| sⁿ`. -/
theorem integral_weight_le (hQ : QBounds Ω Q L c C') (h : IsVariationalSolutionQ Ω C Q u χ)
    {s : ℝ} (hs0 : 0 < s) (hs : ball x s ⊆ Ω) :
    ∫ y in ball x s, Q y ^ 2 * (1 - χ y) ≤ C' ^ 2 * unitBallVolume n * s ^ n := by
  have h1 : IntegrableOn (fun _ : Rn n => C' ^ 2) (ball x s) :=
    integrableOn_const measure_ball_lt_top.ne
  calc ∫ y in ball x s, Q y ^ 2 * (1 - χ y) ≤ ∫ y in ball x s, C' ^ 2 :=
        setIntegral_mono_on (h.integrableOn_weight hQ hs) h1 measurableSet_ball fun y hy =>
          h.weight_le hQ (hs hy)
    _ = C' ^ 2 * unitBallVolume n * s ^ n := by
        rw [setIntegral_const, smul_eq_mul, measureReal_def, volume_ball_toReal x hs0]
        ring

/-- `s ↦ W_Q(s)` is nondecreasing on radii with `B_s(x) ⊆ Ω`. -/
theorem integral_weight_mono (hQ : QBounds Ω Q L c C') (h : IsVariationalSolutionQ Ω C Q u χ)
    {s t : ℝ} (hst : s ≤ t) (ht : ball x t ⊆ Ω) :
    ∫ y in ball x s, Q y ^ 2 * (1 - χ y) ≤ ∫ y in ball x t, Q y ^ 2 * (1 - χ y) :=
  setIntegral_mono_set (h.integrableOn_weight hQ ht)
    ((ae_restrict_iff' measurableSet_ball).2 (.of_forall fun _ hy => h.weight_nonneg (ht hy)))
    (.of_forall (ball_subset_ball hst))

/-- **The error bound**: `|∫_{B_s(x)} (1 − χ) ∇(Q²)·(y − x)| ≤ (2 C' L / c²) s W_Q(s)`. -/
theorem abs_integral_errTerm_le (hQ : QBounds Ω Q L c C') (h : IsVariationalSolutionQ Ω C Q u χ)
    {s : ℝ} (hs0 : 0 < s) (hs : ball x s ⊆ Ω) :
    |∫ y in ball x s, (1 - χ y) * fderiv ℝ (fun z => Q z ^ 2) y (y - x)| ≤
      weissKappa L c C' * s * ∫ y in ball x s, Q y ^ 2 * (1 - χ y) := by
  have hx : x ∈ Ω := hs (mem_ball_self hs0)
  have hC' : 0 ≤ C' := hQ.nonneg_of_mem hx
  have hc2 : 0 < c ^ 2 := pow_pos hQ.pos 2
  have hint : IntegrableOn (fun y => weissKappa L c C' * s * (Q y ^ 2 * (1 - χ y))) (ball x s) :=
    (h.integrableOn_weight hQ hs).const_mul _
  rw [← integral_const_mul]
  refine (abs_integral_le_integral_abs).trans (setIntegral_mono_on
    (h.integrableOn_errTerm hQ hs).abs hint measurableSet_ball fun y hy => ?_)
  have hyΩ := hs hy
  have h1 : ‖y - x‖ ≤ s := by rw [← dist_eq_norm]; exact (mem_ball.1 hy).le
  have h2 := hQ.abs_fderiv_sq_apply_le h.isOpen hyΩ (y - x)
  have h3 := h.one_sub_chi_nonneg hyΩ
  have h4 := hQ.sq_le_sq hyΩ
  rw [abs_mul, abs_of_nonneg h3]
  calc (1 - χ y) * |fderiv ℝ (fun z => Q z ^ 2) y (y - x)| ≤ (1 - χ y) * (2 * C' * L * s) :=
        mul_le_mul_of_nonneg_left (h2.trans (by gcongr)) h3
    _ = weissKappa L c C' * s * (c ^ 2 * (1 - χ y)) := by
        rw [weissKappa]; field_simp [hQ.pos.ne']
    _ ≤ weissKappa L c C' * s * (Q y ^ 2 * (1 - χ y)) := by
        have : 0 ≤ weissKappa L c C' * s := by rw [weissKappa]; positivity
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h4 h3) this

/-! ### Sphere integrals -/

section Sphere

variable {s : ℝ}

theorem sphereIntegrable_weightedEnergy (hQ : QBounds Ω Q L c C')
    (h : IsVariationalSolutionQ Ω C Q u χ) (hR : ball x R ⊆ Ω) (hs : 0 ≤ s) (hsR : s < R) :
    SphereIntegrable (fun y => ‖gradient u y‖ ^ 2 - Q y ^ 2 * (1 - χ y)) x s := by
  have hQc : AEStronglyMeasurable (fun ω : sphere (0 : Rn n) 1 => Q (x + s • (ω : Rn n)) ^ 2)
      (sphereMeasure n) :=
    ((hQ.continuousOn.comp_continuous (continuous_add_smul_sphere x s)
      (add_smul_mem_of_lt hR hs hsR)).pow 2).aestronglyMeasurable
  have hm : AEStronglyMeasurable (fun ω : sphere (0 : Rn n) 1 =>
      ‖gradient u (x + s • (ω : Rn n))‖ ^ 2 -
        Q (x + s • (ω : Rn n)) ^ 2 * (1 - χ (x + s • (ω : Rn n)))) (sphereMeasure n) :=
    (aestronglyMeasurable_sphere_of_measurable (g := fun y => ‖gradient u y‖ ^ 2)
      ((measurable_gradient u).norm.pow_const 2)).sub
      (hQc.mul (aestronglyMeasurable_const.sub (h.aestronglyMeasurable_sphere_chi hR hs hsR)))
  exact sphereIntegrable_of_bound (M := (C : ℝ) ^ 2 + C' ^ 2) hm
    (fun y hy => by
      have hyΩ := sphere_subset_of_lt hR hsR hy
      have a1 := h.sq_norm_gradient_le hyΩ
      have a2 := h.weight_le hQ hyΩ
      have a3 := h.weight_nonneg hyΩ
      have a4 : 0 ≤ ‖gradient u y‖ ^ 2 := sq_nonneg _
      rw [abs_le]
      constructor <;> linarith) hs

end Sphere

/-! ### The weighted identity and the derivatives of `D^w` and `H` -/

/-- **The weighted identity**: for a.e. `s ∈ (0, R)`,
`n ∫_{B_s(x)} (|∇u|² − Q²(1 − χ)) = s ∫_{∂B_s(x)} (|∇u|² − Q²(1 − χ))
  − (2/s) ∫_{∂B_s(x)} (∇u·(y−x))² + (2/s) ∫_{∂B_s(x)} u ∇u·(y−x)
  + ∫_{B_s(x)} (1 − χ) ∇(Q²)·(y − x)`.
It combines the Rellich–Pohozaev identity with the coefficient `Q` and the energy identity (3.8);
for `Q ≡ 1` it is (3.9) multiplied by `sⁿ`. -/
theorem integral_weightedEnergy_identity_ae [NeZero n] (hQ : QBounds Ω Q L c C')
    (h : IsVariationalSolutionQ Ω C Q u χ) (hR : ball x R ⊆ Ω) :
    ∀ᵐ s, s ∈ Ioo 0 R →
      (n : ℝ) * ∫ y in ball x s, (‖gradient u y‖ ^ 2 - Q y ^ 2 * (1 - χ y)) =
        s * sphereIntegral (fun y => ‖gradient u y‖ ^ 2 - Q y ^ 2 * (1 - χ y)) x s -
          2 / s * sphereIntegral (fun y => ⟪gradient u y, y - x⟫ ^ 2) x s +
          2 / s * sphereIntegral (fun y => u y * ⟪gradient u y, y - x⟫) x s +
          ∫ y in ball x s, (1 - χ y) * fderiv ℝ (fun z => Q z ^ 2) y (y - x) := by
  filter_upwards [h.rellich_pohozaev_weighted_ae hQ hR, h.integral_norm_gradient_sq_eq_ae hQ hR]
    with s hRP hG hsR
  have hs0 : 0 < s := hsR.1
  have hsR' : ball x s ⊆ Ω := (ball_subset_ball hsR.2.le).trans hR
  have hP : sphereIntegral (fun y => ‖gradient u y‖ ^ 2 - Q y ^ 2 * (1 - χ y) -
      2 * ⟪gradient u y, ‖y - x‖⁻¹ • (y - x)⟫ ^ 2) x s =
      sphereIntegral (fun y => ‖gradient u y‖ ^ 2 - Q y ^ 2 * (1 - χ y)) x s -
        2 * (s ^ 2)⁻¹ * sphereIntegral (fun y => ⟪gradient u y, y - x⟫ ^ 2) x s := by
    have e : sphereIntegral (fun y => ‖gradient u y‖ ^ 2 - Q y ^ 2 * (1 - χ y) -
        2 * ⟪gradient u y, ‖y - x‖⁻¹ • (y - x)⟫ ^ 2) x s =
        sphereIntegral (fun y => ‖gradient u y‖ ^ 2 - Q y ^ 2 * (1 - χ y) -
          2 * (s ^ 2)⁻¹ * ⟪gradient u y, y - x⟫ ^ 2) x s := by
      refine sphereIntegral_congr hs0.le fun y hy => ?_
      rw [mem_sphere, dist_eq_norm] at hy
      rw [hy, real_inner_smul_right]
      ring
    have hI : SphereIntegrable (fun y => 2 * (s ^ 2)⁻¹ * ⟪gradient u y, y - x⟫ ^ 2) x s :=
      (h.sphereIntegrable_inner_sq hR hs0.le hsR.2).const_mul _
    rw [e, sphereIntegral_sub (h.sphereIntegrable_weightedEnergy hQ hR hs0.le hsR.2) hI,
      sphereIntegral_const_mul]
  replace hRP := hRP hsR
  rw [hP] at hRP
  rw [h.integral_weightedEnergy_eq hQ hsR']
  set G := ∫ y in ball x s, ‖gradient u y‖ ^ 2
  set W := ∫ y in ball x s, Q y ^ 2 * (1 - χ y)
  set E := ∫ y in ball x s, (1 - χ y) * fderiv ℝ (fun z => Q z ^ 2) y (y - x)
  set T := sphereIntegral (fun y => ‖gradient u y‖ ^ 2 - Q y ^ 2 * (1 - χ y)) x s
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

/-- The error term `e(s) = −s^{-n-1} ∫_{B_s(x)} (1 − χ) ∇(Q²)·(y − x)` in the derivative of
`D^w`. -/
def errTerm (Q χ : Rn n → ℝ) (x : Rn n) (s : ℝ) : ℝ :=
  -((s ^ (n + 1))⁻¹ * ∫ y in ball x s, (1 - χ y) * fderiv ℝ (fun z => Q z ^ 2) y (y - x))

/-- **Derivative of `D^w`**: for a.e. `s ∈ (0, R)`,
`(D^w)'(s) = (2 / s^{n+2}) (∫_{∂B_s(x)} (∇u·(y−x))² − ∫_{∂B_s(x)} u ∇u·(y−x)) + e(s)`. -/
theorem hasDerivAt_weightedEnergyD_ae [NeZero n] (hQ : QBounds Ω Q L c C')
    (h : IsVariationalSolutionQ Ω C Q u χ) (hR : ball x R ⊆ Ω) :
    ∀ᵐ s, s ∈ Ioo 0 R →
      HasDerivAt (weightedEnergyD Q u χ x)
        (2 / s ^ (n + 2) * (sphereIntegral (fun y => ⟪gradient u y, y - x⟫ ^ 2) x s -
          sphereIntegral (fun y => u y * ⟪gradient u y, y - x⟫) x s) + errTerm Q χ x s) s := by
  filter_upwards [h.integral_weightedEnergy_identity_ae hQ hR,
    ae_hasDerivAt_integral_ball (h.integrableOn_weightedEnergy hQ hR)] with s hid hF hsR
  have hs0 : s ≠ 0 := hsR.1.ne'
  have hinv : HasDerivAt (fun t : ℝ => (t ^ n)⁻¹) (-(↑n * s ^ (n - 1)) / (s ^ n) ^ 2) s :=
    (hasDerivAt_pow n s).inv (pow_ne_zero n hs0)
  refine ((hinv.mul (hF hsR)).add_const (Q x ^ 2 * unitBallVolume n)).congr_deriv ?_
  have key := hid hsR
  rw [errTerm]
  set F := ∫ y in ball x s, (‖gradient u y‖ ^ 2 - Q y ^ 2 * (1 - χ y))
  set T := sphereIntegral (fun y => ‖gradient u y‖ ^ 2 - Q y ^ 2 * (1 - χ y)) x s
  set Rad := sphereIntegral (fun y => ⟪gradient u y, y - x⟫ ^ 2) x s
  set Mix := sphereIntegral (fun y => u y * ⟪gradient u y, y - x⟫) x s
  set E := ∫ y in ball x s, (1 - χ y) * fderiv ℝ (fun z => Q z ^ 2) y (y - x)
  obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos (NeZero.pos n)).symm⟩
  subst hm
  simp only [Nat.add_sub_cancel]
  push_cast at key ⊢
  have hF' : F = (s * T - 2 / s * Rad + 2 / s * Mix + E) / (m + 1) := by
    rw [← key]; field_simp
  rw [hF']
  field_simp
  ring

/-- `|e(s)| ≤ κ s^{-n} W_Q(s)` with `κ = 2 C' L / c²`. -/
theorem abs_errTerm_le (hQ : QBounds Ω Q L c C') (h : IsVariationalSolutionQ Ω C Q u χ)
    {s : ℝ} (hs0 : 0 < s) (hs : ball x s ⊆ Ω) :
    |errTerm Q χ x s| ≤
      weissKappa L c C' * ((s ^ n)⁻¹ * ∫ y in ball x s, Q y ^ 2 * (1 - χ y)) := by
  have hb := h.abs_integral_errTerm_le hQ hs0 hs
  rw [errTerm, abs_neg, abs_mul, abs_of_pos (inv_pos.2 (pow_pos hs0 _))]
  calc (s ^ (n + 1))⁻¹ * |∫ y in ball x s, (1 - χ y) * fderiv ℝ (fun z => Q z ^ 2) y (y - x)|
      ≤ (s ^ (n + 1))⁻¹ * (weissKappa L c C' * s * ∫ y in ball x s, Q y ^ 2 * (1 - χ y)) :=
        mul_le_mul_of_nonneg_left hb (inv_nonneg.2 (pow_pos hs0 _).le)
    _ = _ := by rw [pow_succ]; field_simp

/-! ### The radial data -/

/-- `s ↦ ∫_{B_s(x)} (|∇u|² − Q² (1 − χ))` is Lipschitz on `[0, b]`, `b < R`. -/
theorem exists_lipschitzOnWith_integral_weightedEnergy [NeZero n] (hQ : QBounds Ω Q L c C')
    (h : IsVariationalSolutionQ Ω C Q u χ) (hR : ball x R ⊆ Ω) {b : ℝ} (hbR : b < R) :
    ∃ K, LipschitzOnWith K
      (fun s => ∫ y in ball x s, (‖gradient u y‖ ^ 2 - Q y ^ 2 * (1 - χ y))) (Icc 0 b) := by
  have hb : ball x b ⊆ Ω := (ball_subset_ball hbR.le).trans hR
  refine ⟨_, lipschitzOnWith_integral_ball (M := (C : ℝ) ^ 2 + C' ^ 2)
    (h.integrableOn_weightedEnergy hQ hb).aestronglyMeasurable fun y hy => ?_⟩
  have hyΩ := hb hy
  have a1 := h.sq_norm_gradient_le hyΩ
  have a2 := h.weight_le hQ hyΩ
  have a3 := h.weight_nonneg hyΩ
  have a4 : 0 ≤ ‖gradient u y‖ ^ 2 := sq_nonneg _
  rw [abs_le]
  constructor <;> linarith

/-- The radial data with error (`Abstract.RadialDataErr`) of a variational solution `(u, χ)` for
the coefficient `Q` at `x`, on `[a, b]` with `0 < a ≤ b < R` and `B_R(x) ⊆ Ω`, with
`ω = Q(x)² |B_1|` and `κ = 2 C' L / c²`. The radial integrals are `∫_{B_s(x)} |∇u|²`,
`ω sⁿ − ∫_{B_s(x)} Q² (1 − χ)`, `∫_{∂B_s(x)} u²`, `∫_{∂B_s(x)} u ∇u·(y−x)`,
`∫_{∂B_s(x)} (∇u·(y−x))²`; `D` and `H` are `weightedEnergyD Q u χ x` and `heightH u x`, and the
error is `errTerm Q χ x`. -/
def radialDataErr [NeZero n] (hQ : QBounds Ω Q L c C') (h : IsVariationalSolutionQ Ω C Q u χ)
    (hR : ball x R ⊆ Ω) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbR : b < R) :
    Abstract.RadialDataErr n (Q x ^ 2 * unitBallVolume n) (weissKappa L c C') a b where
  gradInt s := ∫ y in ball x s, ‖gradient u y‖ ^ 2
  chiInt s := Q x ^ 2 * unitBallVolume n * s ^ n - ∫ y in ball x s, Q y ^ 2 * (1 - χ y)
  sphSq s := sphereIntegral (fun y => u y ^ 2) x s
  sphMix s := sphereIntegral (fun y => u y * ⟪gradient u y, y - x⟫) x s
  sphRad s := sphereIntegral (fun y => ⟪gradient u y, y - x⟫ ^ 2) x s
  energyD := weightedEnergyD Q u χ x
  heightH := heightH u x
  err := errTerm Q χ x
  pos := ha
  le := hab
  kappa_nonneg := by
    have hx : x ∈ Ω := hR (mem_ball_self (ha.trans_le hab |>.trans hbR))
    have := hQ.nonneg_of_mem hx
    rw [weissKappa]
    positivity
  energyD_eq s hs := by
    have hs0 : 0 < s := ha.trans_le hs.1
    have hsΩ : ball x s ⊆ Ω := (ball_subset_ball (hs.2.trans hbR.le)).trans hR
    rw [weightedEnergyD, h.integral_weightedEnergy_eq hQ hsΩ]
    field_simp
    ring
  heightH_eq s _ := by rw [heightH, div_eq_inv_mul]
  lipschitzOnWith_energyD := by
    obtain ⟨K, hK⟩ := h.exists_lipschitzOnWith_integral_weightedEnergy hQ hR hbR
    obtain ⟨K', hK'⟩ :=
      exists_lipschitzOnWith_inv_pow_mul (hK.mono (Icc_subset_Icc_left ha.le)) ha n
    exact ⟨K' + 0, hK'.add (LipschitzWith.const _).lipschitzOnWith⟩
  lipschitzOnWith_heightH := by
    obtain ⟨K, hK⟩ := (h.lipschitzOnWith x R hR).lipschitzOnWith_sphereIntegral_sq hbR
    exact exists_lipschitzOnWith_inv_pow_mul (hK.mono (Icc_subset_Icc_left ha.le)) ha (n + 1)
  chiInt_le s hs := by
    have hsΩ : ball x s ⊆ Ω := (ball_subset_ball (hs.2.trans hbR.le)).trans hR
    have := h.integral_weight_nonneg (x := x) hsΩ
    linarith
  monotoneOn_sub_chiInt := by
    intro s hs t ht hst
    have htΩ : ball x t ⊆ Ω := (ball_subset_ball (ht.2.trans hbR.le)).trans hR
    have := h.integral_weight_mono (x := x) hQ hst htΩ
    simp only
    linarith
  gradInt_eq := by
    refine ae_mem_Ioo_imp_mono ha.le hbR.le ?_
    filter_upwards [h.integral_norm_gradient_sq_eq_ae hQ hR] with s hs hsR
    rw [hs hsR, inv_mul_eq_div]
  hasDerivAt_energyD := ae_mem_Ioo_imp_mono ha.le hbR.le (h.hasDerivAt_weightedEnergyD_ae hQ hR)
  abs_err_le := .of_forall fun s hs => by
    have hs0 : 0 < s := ha.trans hs.1
    have hsΩ : ball x s ⊆ Ω := (ball_subset_ball (hs.2.trans hbR).le).trans hR
    have e : Q x ^ 2 * unitBallVolume n -
        (Q x ^ 2 * unitBallVolume n * s ^ n - ∫ y in ball x s, Q y ^ 2 * (1 - χ y)) / s ^ n =
        (s ^ n)⁻¹ * ∫ y in ball x s, Q y ^ 2 * (1 - χ y) := by
      field_simp
      ring
    rw [e]
    exact h.abs_errTerm_le hQ hs0 hsΩ
  hasDerivAt_heightH := ae_mem_Ioo_imp_mono ha.le hbR.le (h.hasDerivAt_heightH_ae hR)
  sphSq_nonneg := .of_forall fun s hs =>
    sphereIntegral_nonneg (ha.trans hs.1).le fun y _ => sq_nonneg _
  sphRad_nonneg := .of_forall fun s hs =>
    sphereIntegral_nonneg (ha.trans hs.1).le fun y _ => sq_nonneg _
  sq_sphMix_le := .of_forall fun s hs =>
    h.sq_sphereIntegral_mix_le hR (ha.trans hs.1).le (hs.2.trans_le hbR.le)

section RadialDataErr

variable [NeZero n] (hQ : QBounds Ω Q L c C') (h : IsVariationalSolutionQ Ω C Q u χ)
  (hR : ball x R ⊆ Ω) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbR : b < R)

@[simp] theorem radialDataErr_energyD :
    (h.radialDataErr hQ hR ha hab hbR).energyD = weightedEnergyD Q u χ x := rfl

@[simp] theorem radialDataErr_heightH : (h.radialDataErr hQ hR ha hab hbR).heightH = heightH u x :=
  rfl

@[simp] theorem radialDataErr_err : (h.radialDataErr hQ hR ha hab hbR).err = errTerm Q χ x := rfl

@[simp] theorem radialDataErr_monotonicityM :
    (h.radialDataErr hQ hR ha hab hbR).monotonicityM = weightedMonotonicityM Q u χ x := rfl

end RadialDataErr

end IsVariationalSolutionQ

end InnerVariational
