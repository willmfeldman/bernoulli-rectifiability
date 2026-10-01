/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Defs.VariationalSolution
public import InnerVariational.Defs.Quantities
public import InnerVariational.Defs.Solutions
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import GMTFoundations.Defs.Calculus

/-!
# Variational solutions with a Lipschitz coefficient

The generalization of `IsVariationalSolution` to the functional `∫ (|∇u|² + Q² χ)` with a
Lipschitz coefficient `Q : ℝⁿ → ℝ` in place of the constant coefficient `1`.

* `innerVariationQ Q u χ ξ = ∫ ((|∇u|² + Q² χ) div ξ − 2 ∇u · Dξ ∇u + ∇(Q²) · ξ χ)`, the inner
  variation of `∫ (|∇u|² + Q² χ)` in the direction `ξ`;
* `IsVariationalSolutionQ Ω C_V Q u χ`: the definition of a variational solution with the inner
  variation replaced by `innerVariationQ`;
* `QBounds Ω Q L c C`: `Q` is `L`-Lipschitz on `Ω` and `c ≤ Q ≤ C` on `Ω` with `c > 0`;
* `energyDq`, `monotonicityMq`, `MzeroQ`: the quantities `D`, `M`, `M(0+)` with the coefficient
  frozen at a constant `q`, that is, with `χ` replaced by `q² χ`;
* `sigmaHQ`: the set of highest density for a Lipschitz coefficient `Q`;
* `IsViscositySolutionQ Ω Q u`: viscosity solutions of `|∇u| = Q` on the free boundary.

For `Q ≡ 1` everything reduces to the corresponding notion of `Defs/VariationalSolution.lean`,
`Defs/Quantities.lean`, `Defs/HighestDensity.lean` and `Defs/Solutions.lean`
(`isVariationalSolutionQ_one_iff`, `monotonicityMq_one`, `isViscositySolutionQ_one_iff`). For
`Q ≡ q` a positive constant, `(u, χ)` is a `Q`-variational solution if and only if `(u/q, χ)` is
an ordinary variational solution (`isVariationalSolutionQ_const_iff`).

## References

* D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
  DOI 10.1002/cpa.22226; arXiv:2306.10131. Result and equation numbers refer to arXiv v2.
-/

open MeasureTheory Metric Set Filter Topology Laplacian InnerProductSpace
open scoped NNReal ContDiff RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

/-- The inner variation of the functional `∫ (|∇u|² + Q² χ)` in the direction `ξ`:
`∫ ((|∇u|² + Q² χ) div ξ − 2 ∇u · Dξ ∇u + ∇(Q²) · ξ χ)`. For `Q ≡ 1` this is
`innerVariation`. -/
def innerVariationQ (Q u χ : Rn n → ℝ) (ξ : Rn n → Rn n) : ℝ :=
  ∫ x, ((‖gradient u x‖ ^ 2 + Q x ^ 2 * χ x) * divergence ξ x
    - 2 * ⟪gradient u x, fderiv ℝ ξ x (gradient u x)⟫
    + fderiv ℝ (fun y => Q y ^ 2) x (ξ x) * χ x)

/-- `(u, χ)` is a variational solution on `Ω` with gradient constant `C_V` for the coefficient
`Q`. The fields are those of `IsVariationalSolution`, with the inner variation identity replaced
by `innerVariationQ Q u χ ξ = 0`. Bounds on `Q` are not part of the definition, see
`QBounds`. -/
structure IsVariationalSolutionQ (Ω : Set (Rn n)) (C_V : ℝ≥0) (Q u χ : Rn n → ℝ) : Prop where
  /-- `Ω` is open. -/
  isOpen : IsOpen Ω
  /-- `u : Ω → [0, ∞)`. -/
  nonneg : ∀ x ∈ Ω, 0 ≤ u x
  /-- `u ∈ C⁰(Ω)`. -/
  continuousOn : ContinuousOn u Ω
  /-- `u ∈ C²(Ω ∩ {u > 0})`. -/
  contDiffOn : ContDiffOn ℝ 2 u (Ω ∩ {x | 0 < u x})
  /-- `|∇u| ≤ C_V` on `Ω`, encoded as a Lipschitz bound on every ball in `Ω`. -/
  lipschitzOnWith : ∀ x r, ball x r ⊆ Ω → LipschitzOnWith C_V u (ball x r)
  /-- `χ` is Borel measurable on `Ω`. -/
  measurable_chi : Measurable (Ω.indicator χ)
  /-- `χ` takes values in `{0, 1}` on `Ω`. -/
  chi_mem : ∀ x ∈ Ω, χ x = 0 ∨ χ x = 1
  /-- `χ_{u>0} ≤ χ` Lebesgue-a.e. on `Ω`. -/
  posIndicator_le_chi : ∀ᵐ x ∂(volume.restrict Ω), posIndicator u x ≤ χ x
  /-- The domain-variation identity for every `ξ ∈ C^{0,1}_c(Ω; ℝⁿ)`. -/
  innerVariationQ_eq_zero : ∀ ξ, IsLipTestField Ω ξ → innerVariationQ Q u χ ξ = 0

/-- Bounds on the coefficient: `Q` is `L`-Lipschitz on `Ω` and `c ≤ Q ≤ C` on `Ω`, with
`c > 0`. -/
structure QBounds (Ω : Set (Rn n)) (Q : Rn n → ℝ) (L : ℝ≥0) (c C : ℝ) : Prop where
  /-- `Q` is `L`-Lipschitz on `Ω`. -/
  lipschitzOnWith : LipschitzOnWith L Q Ω
  /-- The lower bound is positive. -/
  pos : 0 < c
  /-- `Q ≥ c` on `Ω`. -/
  le : ∀ x ∈ Ω, c ≤ Q x
  /-- `Q ≤ C` on `Ω`. -/
  le' : ∀ x ∈ Ω, Q x ≤ C

/-! ### Quantities with a frozen coefficient -/

/-- `D^q_x(u; r) = r^{-n} ∫_{B_r(x)} (|∇u|² + q² χ)`: the quantity `energyD` with the coefficient
frozen at the constant `q`. -/
def energyDq (q : ℝ) (u χ : Rn n → ℝ) (x : Rn n) (r : ℝ) : ℝ :=
  (r ^ n)⁻¹ * ∫ y in ball x r, (‖gradient u y‖ ^ 2 + q ^ 2 * χ y)

/-- `M^q_x(u; r) = D^q_x(u; r) − H_x(u; r)`: the Weiss quantity `monotonicityM` with the
coefficient frozen at `q`. -/
def monotonicityMq (q : ℝ) (u χ : Rn n → ℝ) (x : Rn n) (r : ℝ) : ℝ :=
  energyDq q u χ x r - heightH u x r

/-- `M^q_x(u; 0+) = lim_{r → 0+} M^q_x(u; r)`, valued in `EReal`. This is junk where the limit
does not exist. -/
def MzeroQ (q : ℝ) (u χ : Rn n → ℝ) (x : Rn n) : EReal :=
  limUnder (𝓝[>] (0 : ℝ)) fun r => (monotonicityMq q u χ x r : EReal)

/-- The set of highest density for the coefficient `Q`:
`x ∈ Ω`, `x ∈ closure {u > 0}` and `M^{Q(x)}_x(u; 0+) ≥ Q(x)² |B_1|`. This is the form with the
limit at the point, because for a non-constant coefficient the quantity `M` is only
almost-monotone in the radius. -/
def sigmaHQ (Ω : Set (Rn n)) (Q u χ : Rn n → ℝ) : Set (Rn n) :=
  {x | x ∈ Ω ∧ x ∈ closure {y | 0 < u y} ∧
    ((Q x ^ 2 * unitBallVolume n : ℝ) : EReal) ≤ MzeroQ (Q x) u χ x}

/-- Viscosity solutions of the one-phase Bernoulli problem with free boundary condition
`|∇u| = Q`. This is `IsViscositySolution` with the constant `1` in the two gradient conclusions
replaced by `Q x`. -/
structure IsViscositySolutionQ (Ω : Set (Rn n)) (Q u : Rn n → ℝ) : Prop where
  /-- `u ∈ C⁰(Ω)`. -/
  continuousOn : ContinuousOn u Ω
  /-- `u ≥ 0` on `Ω`. -/
  nonneg : ∀ x ∈ Ω, 0 ≤ u x
  /-- `u` is harmonic in `Ω ∩ {u > 0}`. -/
  harmonicAt : ∀ x ∈ Ω, 0 < u x → HarmonicAt u x
  /-- Touching from below: `φ ≤ u` near a free boundary point forces `|∇φ(x)| ≤ Q(x)`. -/
  norm_gradient_le : ∀ x ∈ Ω ∩ frontier {y | 0 < u y}, ∀ r, 0 < r → ball x r ⊆ Ω →
    ∀ φ : Rn n → ℝ, ContDiff ℝ ∞ φ → φ x = 0 → (∀ y ∈ ball x r, φ y ≤ u y) →
      ‖gradient φ x‖ ≤ Q x
  /-- Touching from above: `φ₊ ≥ u` near a free boundary point forces `|∇φ(x)| ≥ Q(x)`. -/
  one_le_norm_gradient : ∀ x ∈ Ω ∩ frontier {y | 0 < u y}, ∀ r, 0 < r → ball x r ⊆ Ω →
    ∀ φ : Rn n → ℝ, ContDiff ℝ ∞ φ → φ x = 0 → (∀ y ∈ ball x r, u y ≤ max (φ y) 0) →
      Q x ≤ ‖gradient φ x‖

/-! ### Reduction to `Q ≡ 1` -/

theorem energyDq_one (u χ : Rn n → ℝ) (x : Rn n) (r : ℝ) :
    energyDq 1 u χ x r = energyD u χ x r := by
  simp [energyDq, energyD]

theorem monotonicityMq_one : (monotonicityMq 1 : (Rn n → ℝ) → _) = monotonicityM := by
  funext u χ x r
  simp [monotonicityMq, monotonicityM, energyDq_one]

theorem innerVariationQ_one (u χ : Rn n → ℝ) (ξ : Rn n → Rn n) :
    innerVariationQ (fun _ => 1) u χ ξ = innerVariation u χ ξ := by
  simp [innerVariationQ, innerVariation]

theorem isViscositySolutionQ_one_iff {Ω : Set (Rn n)} {u : Rn n → ℝ} :
    IsViscositySolutionQ Ω (fun _ => 1) u ↔ IsViscositySolution Ω u :=
  ⟨fun h => ⟨h.continuousOn, h.nonneg, h.harmonicAt, h.norm_gradient_le, h.one_le_norm_gradient⟩,
    fun h => ⟨h.continuousOn, h.nonneg, h.harmonicAt, h.norm_gradient_le, h.one_le_norm_gradient⟩⟩

theorem isVariationalSolutionQ_one_iff {Ω : Set (Rn n)} {C : ℝ≥0} {u χ : Rn n → ℝ} :
    IsVariationalSolutionQ Ω C (fun _ => 1) u χ ↔ IsVariationalSolution Ω C u χ := by
  constructor
  · intro h
    exact ⟨h.isOpen, h.nonneg, h.continuousOn, h.contDiffOn, h.lipschitzOnWith, h.measurable_chi,
      h.chi_mem, h.posIndicator_le_chi, fun ξ hξ => by
        rw [← innerVariationQ_one]; exact h.innerVariationQ_eq_zero ξ hξ⟩
  · intro h
    exact ⟨h.isOpen, h.nonneg, h.continuousOn, h.contDiffOn, h.lipschitzOnWith, h.measurable_chi,
      h.chi_mem, h.posIndicator_le_chi, fun ξ hξ => by
        rw [innerVariationQ_one]; exact h.innerVariation_eq_zero ξ hξ⟩

/-! ### Constant coefficients -/

theorem gradient_div_const (u : Rn n → ℝ) (q : ℝ) (x : Rn n) :
    gradient (fun y => u y / q) x = q⁻¹ • gradient u x := by
  have : (fun y => u y / q) = q⁻¹ • u := by
    ext y; simp [div_eq_inv_mul]
  rw [this]
  simp only [gradient]
  rw [fderiv_const_smul_field, Pi.smul_apply]
  simp

theorem posIndicator_div_const (u : Rn n → ℝ) {q : ℝ} (hq : 0 < q) :
    posIndicator (fun y => u y / q) = posIndicator u := by
  funext x
  by_cases h : 0 < u x
  · rw [posIndicator_of_pos h, posIndicator_of_pos (div_pos h hq)]
  · rw [posIndicator_of_nonpos (not_lt.1 h),
      posIndicator_of_nonpos (div_nonpos_of_nonpos_of_nonneg (not_lt.1 h) hq.le)]

theorem innerVariationQ_const (u χ : Rn n → ℝ) (ξ : Rn n → Rn n) {q : ℝ} (hq : q ≠ 0) :
    innerVariationQ (fun _ => q) u χ ξ = q ^ 2 * innerVariation (fun y => u y / q) χ ξ := by
  rw [innerVariationQ, innerVariation, ← integral_const_mul]
  congr 1
  funext x
  have h0 : fderiv ℝ (fun _ : Rn n => q ^ 2) x = 0 := by
    rw [fderiv_fun_const]; rfl
  simp only [gradient_div_const u q, norm_smul, inner_smul_left, map_smul, inner_smul_right,
    h0, zero_apply, zero_mul, add_zero,
    Real.norm_eq_abs, mul_pow, sq_abs, conj_trivial]
  field_simp

/-- For a constant coefficient `q > 0`, `(u, χ)` is a `Q`-variational solution if and only if
`(u / q, χ)` is an ordinary variational solution, with the gradient constant divided by `q`. -/
theorem isVariationalSolutionQ_const_iff {Ω : Set (Rn n)} {C : ℝ≥0} {u χ : Rn n → ℝ} {q : ℝ≥0}
    (hq : 0 < q) :
    IsVariationalSolutionQ Ω C (fun _ => (q : ℝ)) u χ ↔
      IsVariationalSolution Ω (C / q) (fun y => u y / q) χ := by
  have hq' : (0 : ℝ) < q := hq
  have hset : Ω ∩ {x | 0 < u x / q} = Ω ∩ {x | 0 < u x} := by
    ext x; simp [div_pos_iff_of_pos_right hq']
  have hlip : ∀ s : Set (Rn n), LipschitzOnWith (C / q) (fun y => u y / q) s ↔
      LipschitzOnWith C u s := by
    intro s
    rw [lipschitzOnWith_iff_dist_le_mul, lipschitzOnWith_iff_dist_le_mul]
    refine forall₂_congr fun x _ => forall₂_congr fun y _ => ?_
    rw [Real.dist_eq, Real.dist_eq, ← sub_div, abs_div, abs_of_pos hq', NNReal.coe_div,
      div_mul_eq_mul_div, div_le_div_iff_of_pos_right hq']
  constructor
  · intro h
    refine ⟨h.isOpen, fun x hx => div_nonneg (h.nonneg x hx) hq'.le,
      h.continuousOn.div_const _, ?_, fun x r hr => (hlip _).2 (h.lipschitzOnWith x r hr),
      h.measurable_chi, h.chi_mem, ?_, fun ξ hξ => ?_⟩
    · rw [hset]; exact h.contDiffOn.div_const _
    · rw [posIndicator_div_const u hq']; exact h.posIndicator_le_chi
    · have := h.innerVariationQ_eq_zero ξ hξ
      rw [innerVariationQ_const u χ ξ hq'.ne'] at this
      exact (mul_eq_zero.1 this).resolve_left (pow_ne_zero 2 hq'.ne')
  · intro h
    refine ⟨h.isOpen, fun x hx => ?_, ?_, ?_, fun x r hr => (hlip _).1 (h.lipschitzOnWith x r hr),
      h.measurable_chi, h.chi_mem, ?_, fun ξ hξ => ?_⟩
    · simpa [div_nonneg_iff, hq'.not_ge] using h.nonneg x hx
    · have := h.continuousOn.mul_const (q : ℝ)
      simpa [div_mul_cancel₀ _ hq'.ne'] using this
    · have := ContDiffOn.mul h.contDiffOn (contDiffOn_const (c := (q : ℝ)))
      rw [hset] at this
      simpa [div_mul_cancel₀ _ hq'.ne'] using this
    · have := h.posIndicator_le_chi
      rwa [posIndicator_div_const u hq'] at this
    · rw [innerVariationQ_const u χ ξ hq'.ne', h.innerVariation_eq_zero ξ hξ, mul_zero]

end InnerVariational
