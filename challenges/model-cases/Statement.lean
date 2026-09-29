import Mathlib

/-!
# Trusted statement: model solutions (non-vacuity check)

This file imports Mathlib only. It is the complete trusted surface of the `model-cases`
challenge: `Challenge.lean` and `Solution.lean` both state the claim below.

This is a sanity check, not a theorem of the paper: it shows that the definitions of the other
challenges are satisfied by the basic explicit solutions, and that `Σ^H` separates them.

## Source

D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
DOI 10.1002/cpa.22226, arXiv:2306.10131. Numbers refer to arXiv version 2 (`[K–W]` below).

The two model solutions are the one-dimensional examples of [K–W, §3.1], extended to `ℝⁿ`:

* the half-plane solution `u = (y_n)⁺ = max(y_n, 0)`, `χ = χ_{u>0}`, the blow-up at regular free
  boundary points. Its free boundary point `0` has density `1/2`: `M_0(u; 0+) = |B₁| / 2`, so
  `0 ∉ Σ^H`.
* the two-plane solution `u = |y_n|`, `χ = χ_{u>0}`, a "multiplicity 2" point: `M_0(u; 0+) = |B₁|`,
  so `0 ∈ Σ^H`.

Both are variational solutions on `ℝⁿ` with constant `C_V = 1`. The claim also checks the
normalization of `α(n)` stated in [K–W, §8.2]: `H_0(α(n)|y_n|; r) = 1` for every `r > 0`.

## What it guards against

* A vacuous definition of variational solution: the domain-variation identity, the Lipschitz
  bound, and the other conditions are met by two explicit, genuinely different solutions, neither
  of them differentiable on its free boundary.
* A trivial `Σ^H`: it contains the two-plane point and excludes the half-plane point.
* A wrong normalization of `α(n)` or of the sphere integrals in `H`.

It does not test the domain-variation identity negatively (a pair that fails it), and it does
not compute a reduced boundary or a Laplacian measure.

## Vocabulary

The definitions are the same as in the `main-theorem` and `sigma-h` challenges: normalized
Hausdorff measure `hausdorffN`, `divergence`, `IsVariationalSolution`, `H_x(u; r)`, `D_x(u; r)`,
`M_x(u; r)`, `Σ^H` and `α(n)`. The ambient space is `ℝⁿ = EuclideanSpace ℝ (Fin n)`, `n ≥ 1`.
-/

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace KWChallenge

/-- The Euclidean space `ℝⁿ`. -/
abbrev Rn (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- `ω_n = |B₁|`, the Lebesgue measure of the unit ball of `ℝⁿ`. -/
def unitBallVolume (n : ℕ) : ℝ :=
  (volume (ball (0 : Rn n) 1)).toReal

/-- The normalized `d`-dimensional Hausdorff measure `ℋ^d = (ω_d / 2^d) μH[d]` on `ℝⁿ`. -/
def hausdorffN (n d : ℕ) : Measure (Rn n) :=
  ENNReal.ofReal (unitBallVolume d / 2 ^ d) • (Measure.hausdorffMeasure (d : ℝ))

/-- The divergence `div ξ(x) = tr Dξ(x)` of a vector field `ξ : ℝⁿ → ℝⁿ`. -/
def divergence {n : ℕ} (ξ : Rn n → Rn n) (x : Rn n) : ℝ :=
  LinearMap.trace ℝ (Rn n) (fderiv ℝ ξ x : Rn n →ₗ[ℝ] Rn n)

/-- The characteristic function `χ_{u>0}` of the positivity set of `u`. -/
def posIndicator {n : ℕ} (u : Rn n → ℝ) : Rn n → ℝ :=
  {x | 0 < u x}.indicator 1

/-- **Variational solutions** [K–W, §3.2]. A pair `(u, χ)` is a variational solution on the open
set `Ω` with constant `C_V` if

1. `u : Ω → [0, ∞)`, `u ∈ C⁰(Ω) ∩ C²({u > 0})`, and `|∇u| ≤ C_V` on `Ω`;
2. `χ : Ω → {0, 1}` is Borel measurable;
3. `χ_{u>0} ≤ χ` Lebesgue-a.e. on `Ω`;
4. for every Lipschitz vector field `ξ` with compact support in `Ω`,
   `∫ ((|∇u|² + χ) div ξ − 2 ∇u · Dξ ∇u) = 0`
   (the first variation of `∫ (|∇u|² + χ)` under the domain deformations `x ↦ x + t ξ(x)`).

Encoding: `|∇u| ≤ C_V` is stated as "`u` is `C_V`-Lipschitz on every ball contained in `Ω`";
for a function that is locally Lipschitz in `Ω` this is equivalent to `|∇u| ≤ C_V` a.e., since
balls are convex. Borel measurability of `χ` on `Ω` is measurability of `χ` extended by `0`
outside `Ω`. `C²({u > 0})` is `C²` on the open set `Ω ∩ {u > 0}`. The integrand in 4. vanishes
outside the support of `ξ`, and it is bounded, so the integral is a genuine Lebesgue integral. -/
structure IsVariationalSolution {n : ℕ} (Ω : Set (Rn n)) (C_V : ℝ≥0) (u χ : Rn n → ℝ) :
    Prop where
  /-- `Ω` is open. -/
  isOpen : IsOpen Ω
  /-- `u ≥ 0` on `Ω`. -/
  nonneg : ∀ x ∈ Ω, 0 ≤ u x
  /-- `u` is continuous on `Ω`. -/
  continuousOn : ContinuousOn u Ω
  /-- `u` is `C²` on `Ω ∩ {u > 0}`. -/
  contDiffOn : ContDiffOn ℝ 2 u (Ω ∩ {x | 0 < u x})
  /-- `|∇u| ≤ C_V` on `Ω`: `u` is `C_V`-Lipschitz on every ball contained in `Ω`. -/
  lipschitzOnWith : ∀ x r, ball x r ⊆ Ω → LipschitzOnWith C_V u (ball x r)
  /-- `χ` is Borel measurable on `Ω`. -/
  measurable_chi : Measurable (Ω.indicator χ)
  /-- `χ` takes the values `0` and `1` on `Ω`. -/
  chi_mem : ∀ x ∈ Ω, χ x = 0 ∨ χ x = 1
  /-- `χ_{u>0} ≤ χ` almost everywhere on `Ω`. -/
  posIndicator_le_chi : ∀ᵐ x ∂(volume.restrict Ω), posIndicator u x ≤ χ x
  /-- The domain-variation identity, for every Lipschitz `ξ` with compact support in `Ω`. -/
  innerVariation_eq_zero : ∀ ξ : Rn n → Rn n, (∃ L, LipschitzWith L ξ) → HasCompactSupport ξ →
    tsupport ξ ⊆ Ω →
    ∫ x, ((‖gradient u x‖ ^ 2 + χ x) * divergence ξ x -
      2 * ⟪gradient u x, fderiv ℝ ξ x (gradient u x)⟫) = 0

/-- `D_x(u; r) = r^{-n} ∫_{B_r(x)} (|∇u|² + χ)` [K–W, §3.3]. -/
def energyD {n : ℕ} (u χ : Rn n → ℝ) (x : Rn n) (r : ℝ) : ℝ :=
  (r ^ n)⁻¹ * ∫ y in ball x r, (‖gradient u y‖ ^ 2 + χ y)

/-- `H_x(u; r) = r^{-(n+1)} ∫_{∂B_r(x)} u² dℋ^{n-1}` [K–W, §3.3]. -/
def heightH {n : ℕ} (u : Rn n → ℝ) (x : Rn n) (r : ℝ) : ℝ :=
  (r ^ (n + 1))⁻¹ * ∫ y in sphere x r, u y ^ 2 ∂hausdorffN n (n - 1)

/-- The Weiss energy `M_x(u; r) = D_x(u; r) − H_x(u; r)` [K–W, §3.3]. -/
def monotonicityM {n : ℕ} (u χ : Rn n → ℝ) (x : Rn n) (r : ℝ) : ℝ :=
  energyD u χ x r - heightH u x r

/-- The set of highest density [K–W, §6]:
`Σ^H = {x ∈ Ω : x ∈ closure {u > 0} and M_x(u; 0+) ≥ |B₁|}`. The condition `M_x(u; 0+) ≥ |B₁|`
is written "`M_x(u; r)` converges, as `r → 0+`, to a real number `m ≥ |B₁|`". For a variational
solution `r ↦ M_x(u; r)` is nondecreasing [K–W, Proposition 3.4], so `M_x(u; 0+)` exists in
`[−∞, ∞)`, and it is `≥ |B₁|` exactly when it is a real number `≥ |B₁|`. -/
def sigmaH {n : ℕ} (Ω : Set (Rn n)) (u χ : Rn n → ℝ) : Set (Rn n) :=
  {x | x ∈ Ω ∧ x ∈ closure {y | 0 < u y} ∧
    ∃ m : ℝ, Tendsto (monotonicityM u χ x) (𝓝[>] 0) (𝓝 m) ∧ unitBallVolume n ≤ m}

/-- The index of the last coordinate `y_n` of `ℝⁿ`. -/
def lastCoord (n : ℕ) [NeZero n] : Fin n :=
  ⟨n - 1, Nat.sub_one_lt (NeZero.ne n)⟩

/-- `α(n) = (∫_{∂B₁} y_n² dℋ^{n-1})^{-1/2}` [K–W, §8.2]. -/
def alphaN (n : ℕ) [NeZero n] : ℝ :=
  1 / √(∫ y in sphere (0 : Rn n) 1, y (lastCoord n) ^ 2 ∂hausdorffN n (n - 1))

/-- The half-plane solution `u(y) = max(y_n, 0)`. -/
def halfPlaneSolution (n : ℕ) [NeZero n] : Rn n → ℝ :=
  fun y => max (y (lastCoord n)) 0

/-- The two-plane solution `u(y) = |y_n|`. -/
def twoPlaneSolution (n : ℕ) [NeZero n] : Rn n → ℝ :=
  fun y => |y (lastCoord n)|

/-- **Model solutions.** For every `n ≥ 1`:

* `((y_n)⁺, χ_{(y_n)⁺ > 0})` is a variational solution on `ℝⁿ` with constant `1`, and
  `0 ∉ Σ^H` for it;
* `(|y_n|, χ_{|y_n| > 0})` is a variational solution on `ℝⁿ` with constant `1`, and `0 ∈ Σ^H`
  for it;
* `H_0(α(n)|y_n|; r) = 1` for every `r > 0`. -/
def ModelCasesClaim (n : ℕ) [NeZero n] : Prop :=
  (IsVariationalSolution univ 1 (halfPlaneSolution n) (posIndicator (halfPlaneSolution n)) ∧
    (0 : Rn n) ∉ sigmaH univ (halfPlaneSolution n) (posIndicator (halfPlaneSolution n))) ∧
  (IsVariationalSolution univ 1 (twoPlaneSolution n) (posIndicator (twoPlaneSolution n)) ∧
    (0 : Rn n) ∈ sigmaH univ (twoPlaneSolution n) (posIndicator (twoPlaneSolution n))) ∧
  ∀ r : ℝ, 0 < r → heightH (fun y => alphaN n * |y (lastCoord n)|) 0 r = 1

end KWChallenge
