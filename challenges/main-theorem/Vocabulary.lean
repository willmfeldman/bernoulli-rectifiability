module

public import Mathlib

/-!
# Trusted statements: the Main Theorem and the identification of `χ` and of `Δu`

This file imports Mathlib only. It is the complete trusted surface of the `main-theorem`
challenge: `Challenge.lean` and `Solution.lean` both state the four claims below.

## Source

D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
DOI 10.1002/cpa.22226, arXiv:2306.10131. Numbers refer to arXiv version 2 (`[K–W]` below).

* `MainTheoremClaim`: [K–W, Theorem 1.2], items (i)–(iv).
* `ChiIdentificationClaim`: [K–W, Theorem 8.6], `χ = χ_{u>0}` unless `u ≡ 0`.
* `LaplacianMeasureClaim`: [K–W, Theorem 8.7], rectifiability of the free boundary and the formula
  for `Δu`.
* `ModelCasesClaim`: a non-vacuity check, not a theorem of the paper (see "Non-vacuity check"
  below).

## Vocabulary

Every notion is defined below from Mathlib. The ambient space is
`ℝⁿ = EuclideanSpace ℝ (Fin n)` with Lebesgue measure `volume`, and every claim assumes `n ≥ 2`.
The functions `u, χ` are total functions `ℝⁿ → ℝ`; only their values on the open set `Ω` enter
the definitions and the conclusions.

* `hausdorffN n d = (ω_d / 2^d) μH[d]`, the `d`-dimensional Hausdorff measure `ℋ^d` with the
  normalization of Evans–Gariepy (`ω_d = |B₁ ⊆ ℝ^d|`), so that `ℋ^n` is Lebesgue measure.
* `divergence ξ x = tr Dξ(x)`, from Mathlib's Fréchet derivative `fderiv`. `gradient u x` is
  Mathlib's gradient. At points of non-differentiability both are `0` by Mathlib's convention;
  for the Lipschitz functions and fields below this is a Lebesgue-null set (Rademacher).
* `IsVariationalSolution Ω C_V u χ`: the definition of [K–W, §3.2], written out in full
  (see its docstring), including the domain-variation identity.
* `heightH`, `energyD`, `monotonicityM`: the quantities `H_x(u; r)`, `D_x(u; r)`,
  `M_x(u; r) = D_x(u; r) − H_x(u; r)` of [K–W, §3.3]. Sphere integrals are integrals over
  `sphere x r` against `ℋ^{n-1}`.
* `sigmaH Ω u χ`: the set of highest density
  `Σ^H = {x ∈ Ω : x ∈ closure {u > 0}, M_x(u; 0+) ≥ |B₁|}` of [K–W, §6].
* `heightHZero u x = H_x(u; 0+)`, the limit of `H_x(u; r)` as `r → 0+`.
* `alphaN n = α(n) = (∫_{∂B₁} y_n² dℋ^{n-1})^{-1/2}` [K–W, §8.2].
* `IsCountablyRectifiable n k S`: up to an `ℋ^k`-null set, `S` is covered by countably many
  Lipschitz images of `ℝ^k`.
* `IsGaussGreenPair`, `reducedBoundary`: De Giorgi's reduced boundary `∂*E ∩ Ω`, defined from
  the perimeter measure and outer normal of `E` (see the docstrings).
* `laplacianMeasure Ω u χ = ℋ^{n-1}⌊∂*{u>0} + 2 α(n) √(H_x(u; 0+)) ℋ^{n-1}⌊Σ^H`, and
  `HasDistribLaplacianOn Ω u μ`: `Δu = μ` in `Ω` in the sense of distributions, with `μ` a
  Radon measure on `Ω`.
* `halfPlaneSolution n = (y_n)⁺` and `twoPlaneSolution n = |y_n|`: the model solutions of the
  non-vacuity check.

"For `ℋ^{n-1}`-a.e. `x ∈ A`, `P x`" is written `ℋ^{n-1} {x ∈ A | ¬ P x} = 0`: the exceptional set
is `ℋ^{n-1}`-null as an outer measure, so no measurability of `A` is needed.
`∂{u > 0}` in `Ω` is `Ω ∩ frontier {u > 0}`; since `Ω` is open, this is the relative boundary and
depends only on `u` on `Ω`.

## Differences from the printed paper

* [K–W, Theorem 1.2 (iii)] is printed with a set `Σ_**` and with
  `H_x(u; 0+) = lim r^{-2} ⨍_{∂B_r(x)} u²` (an average). The body of the paper, [K–W, Theorem 8.7],
  whose proof also proves Theorem 1.2 (iii), uses `Σ^H` and the unaveraged
  `H_x(u; r) = r^{-(n+1)} ∫_{∂B_r(x)} u² dℋ^{n-1}` of §3.3, and `α(n)` is normalized for the
  unaveraged quantity (`H_0(α(n)|y_n|; r) = 1`). With the average the formula would be off by the
  factor `|∂B₁|^{1/2}`. Both claims here use the body's form.
* [K–W, Theorem 1.2 (iv)], second display, is printed as
  `r ∫_{B_r(x)} |∇(u − α(n)|(y − x)·ν|)|² / ∫_{∂B_r(x)} u² → 0`, without the factor
  `√(H_x(u; r))` that [K–W, Lemma 8.5 (1)] carries. The factor is needed: for the variational
  solution `u = 2α(n)|y_n|`, `χ ≡ 1` on `Ω = ℝⁿ`, every point of `{y_n = 0}` lies in
  `∂{u > 0} \ ∂*{u > 0}`, and there the ratio is at least `α(n)² |B₁| / 4` for every unit vector
  `ν`, while with the factor (here `√(H_x(u; r)) = 2`) the ratio is `0` for `ν = e_n`. The claim
  below includes the factor.
* The claims include two statements that the paper uses without listing them in the theorems:
  the limit `H_x(u; 0+)` exists at every point of `Σ^H` (stated after [K–W, Theorem 8.6]), so that
  the density of the Laplacian measure is not a junk value; and `{u > 0}` has locally finite
  perimeter in `Ω` (a Gauss–Green pair exists), so that `∂*{u > 0}` is not vacuous.

## Non-vacuity check

`ModelCasesClaim` is a sanity check, not a theorem of the paper (see the docstring of
`challenge_model_cases` in `Challenge.lean`). Its model solutions are the one-dimensional examples
of [K–W, §3.1], extended to `ℝⁿ` (`n ≥ 1`): the half-plane solution `u = (y_n)⁺`, the blow-up at
regular free boundary points, with `M_0(u; 0+) = |B₁| / 2`, so `0 ∉ Σ^H`; and the two-plane
solution `u = |y_n|`, a "multiplicity 2" point, with `M_0(u; 0+) = |B₁|`, so `0 ∈ Σ^H`. In both
`χ = χ_{u>0}` and `C_V = 1`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Set Filter Topology Laplacian
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

/-- `ξ ∈ C^∞_c(Ω; ℝⁿ)`: `ξ` is smooth and has compact support contained in `Ω`. -/
def IsSmoothTestField {n : ℕ} (Ω : Set (Rn n)) (ξ : Rn n → Rn n) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ξ ∧ HasCompactSupport ξ ∧ tsupport ξ ⊆ Ω

/-- `φ ∈ C^∞_c(Ω)`: `φ` is smooth and has compact support contained in `Ω`. -/
def IsTestFunction {n : ℕ} (Ω : Set (Rn n)) (φ : Rn n → ℝ) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ω

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

/-- `H_x(u; 0+) = lim_{r → 0+} H_x(u; r)`. Mathlib's `limUnder` returns an arbitrary value where
the limit does not exist; the claims below assert that it exists at every point of `Σ^H`, which
is the only place where it is used. -/
def heightHZero {n : ℕ} (u : Rn n → ℝ) (x : Rn n) : ℝ :=
  limUnder (𝓝[>] (0 : ℝ)) (heightH u x)

/-- The index of the last coordinate `y_n` of `ℝⁿ`. -/
def lastCoord (n : ℕ) [NeZero n] : Fin n :=
  ⟨n - 1, Nat.sub_one_lt (NeZero.ne n)⟩

/-- `α(n) = (∫_{∂B₁} y_n² dℋ^{n-1})^{-1/2}` [K–W, §8.2], normalized so that
`H_0(α(n)|y_n|; r) = 1`. -/
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

/-- `S ⊆ ℝⁿ` is countably `ℋ^k`-rectifiable: up to an `ℋ^k`-null set it is contained in a countable
union of Lipschitz images of `ℝ^k`. (Lipschitz images of all of `ℝ^k` rather than of subsets of
`ℝ^k`: a Lipschitz map on a subset extends to `ℝ^k`, componentwise by McShane's theorem.) -/
def IsCountablyRectifiable (n k : ℕ) (S : Set (Rn n)) : Prop :=
  ∃ f : ℕ → Rn k → Rn n, (∀ i, ∃ C, LipschitzWith C (f i)) ∧
    hausdorffN n k (S \ ⋃ i, range (f i)) = 0

/-- A Gauss–Green pair `(μ, ν)` for `E` in `Ω`: `μ` is a Radon measure on `Ω`, `ν` a `μ`-a.e. unit
vector field, and `∫_E div φ = ∫ ⟪φ, ν⟫ dμ` for all `φ ∈ C^∞_c(Ω; ℝⁿ)`. By De Giorgi's structure
theorem (Evans–Gariepy, *Measure Theory and Fine Properties of Functions*, revised ed., 2015,
Theorem 5.1) such a pair exists exactly when `E` has locally finite perimeter in `Ω`, and then
`μ = |Dχ_E|⌊Ω` is the perimeter measure and `ν` the measure-theoretic outer unit normal. The pair
is unique: `Dχ_E` determines the vector measure `ν μ`, and `μ = |ν μ|`. -/
structure IsGaussGreenPair {n : ℕ} (Ω E : Set (Rn n)) (μ : Measure (Rn n)) (ν : Rn n → Rn n) :
    Prop where
  /-- `μ` is concentrated on `Ω`. -/
  measure_compl : μ Ωᶜ = 0
  /-- `μ` is finite on compact subsets of `Ω`. -/
  lt_top_of_isCompact : ∀ K, IsCompact K → K ⊆ Ω → μ K < ∞
  /-- `ν` is measurable. -/
  measurable_normal : Measurable ν
  /-- `ν` is a unit vector `μ`-a.e. -/
  norm_normal : ∀ᵐ x ∂μ, ‖ν x‖ = 1
  /-- The Gauss–Green formula `∫_E div φ = ∫ ⟪φ, ν⟫ dμ` for `φ ∈ C^∞_c(Ω; ℝⁿ)`. -/
  integral_divergence : ∀ φ : Rn n → Rn n, IsSmoothTestField Ω φ →
    ∫ x in E, divergence φ x = ∫ x, ⟪φ x, ν x⟫ ∂μ

/-- De Giorgi's reduced boundary `∂*E ∩ Ω` (Evans–Gariepy, Definition 5.4, with open balls): the
points `x ∈ Ω` with `μ(B_r(x)) > 0` for all `r > 0` at which the averages `⨍_{B_r(x)} ν dμ`
converge, as `r → 0+`, to a unit vector, where `(μ, ν)` is the Gauss–Green pair of `E` in `Ω`.
Since the pair is unique, the existential quantifier does not change the set. -/
def reducedBoundary {n : ℕ} (Ω E : Set (Rn n)) : Set (Rn n) :=
  {x | x ∈ Ω ∧ ∃ μ ν, IsGaussGreenPair Ω E μ ν ∧ (∀ r, 0 < r → 0 < μ (ball x r)) ∧
    ∃ v : Rn n, ‖v‖ = 1 ∧
      Tendsto (fun r => (μ (ball x r)).toReal⁻¹ • ∫ y in ball x r, ν y ∂μ) (𝓝[>] 0) (𝓝 v)}

/-- The measure `ℋ^{n-1}⌊∂*{u>0} + 2 α(n) √(H_x(u; 0+)) ℋ^{n-1}⌊Σ^H` of [K–W, Theorem 8.7], with
the reduced boundary taken in `Ω`. -/
def laplacianMeasure {n : ℕ} [NeZero n] (Ω : Set (Rn n)) (u χ : Rn n → ℝ) : Measure (Rn n) :=
  (hausdorffN n (n - 1)).restrict (reducedBoundary Ω {x | 0 < u x}) +
    ((hausdorffN n (n - 1)).restrict (sigmaH Ω u χ)).withDensity
      (fun x => ENNReal.ofReal (2 * alphaN n * √(heightHZero u x)))

/-- `Δu = μ` in `Ω` in the sense of distributions, with `μ` a Radon measure on `Ω`: `μ` is finite
on compact subsets of `Ω`, and `∫ u Δφ = ∫ φ dμ` for every `φ ∈ C^∞_c(Ω)`, where `Δ` is Mathlib's
Laplacian. -/
def HasDistribLaplacianOn {n : ℕ} (Ω : Set (Rn n)) (u : Rn n → ℝ) (μ : Measure (Rn n)) : Prop :=
  (∀ K, IsCompact K → K ⊆ Ω → μ K < ∞) ∧
    ∀ φ, IsTestFunction Ω φ → ∫ x, u x * Δ φ x = ∫ x, φ x ∂μ

/-- **[K–W, Theorem 1.2]** (Main Theorem). Let `n ≥ 2` and let `(u, χ)` be a variational solution,
with some constant `C_V`, on a domain (open and connected set) `Ω ⊆ ℝⁿ`. Then:

(i) either `u ≡ 0` on `Ω`, or `χ = χ_{u>0}` a.e. on `Ω`;

(ii) `Ω ∩ ∂{u > 0}` is countably `ℋ^{n-1}`-rectifiable and has locally finite `ℋ^{n-1}`-measure
  in `Ω`;

(iii) `H_x(u; r) → H_x(u; 0+)` as `r → 0+` at every `x ∈ Σ^H`, and
  `Δu = ℋ^{n-1}⌊∂*{u>0} + 2 α(n) √(H_x(u; 0+)) ℋ^{n-1}⌊Σ^H` in `Ω` in the sense of distributions;

(iv) at `ℋ^{n-1}`-a.e. `x ∈ Ω ∩ ∂{u > 0} \ ∂*{u > 0}`, as `r → 0+`,
  `r ∫_{B_r(x)} (|∇u|² + χ − 1) / ∫_{∂B_r(x)} u² dℋ^{n-1} → 1`, and for some unit vector `ν`,
  `r ∫_{B_r(x)} |∇(u − √(H_x(u; r)) α(n) |(y − x)·ν|)|² / ∫_{∂B_r(x)} u² dℋ^{n-1} → 0`.

See the module docstring for the form of (iii) and the normalization `√(H_x(u; r))` in (iv). -/
def MainTheoremClaim (n : ℕ) [NeZero n] : Prop :=
  2 ≤ n → ∀ (Ω : Set (Rn n)) (C_V : ℝ≥0) (u χ : Rn n → ℝ),
    IsConnected Ω → IsVariationalSolution Ω C_V u χ →
    -- (i)
    ((∀ x ∈ Ω, u x = 0) ∨ χ =ᵐ[volume.restrict Ω] posIndicator u) ∧
    -- (ii)
    (IsCountablyRectifiable n (n - 1) (Ω ∩ frontier {x | 0 < u x}) ∧
      ∀ K, IsCompact K → K ⊆ Ω → hausdorffN n (n - 1) (K ∩ frontier {x | 0 < u x}) < ∞) ∧
    -- (iii)
    ((∀ x ∈ sigmaH Ω u χ, Tendsto (heightH u x) (𝓝[>] 0) (𝓝 (heightHZero u x))) ∧
      HasDistribLaplacianOn Ω u (laplacianMeasure Ω u χ)) ∧
    -- (iv)
    hausdorffN n (n - 1) {x | x ∈ Ω ∧ x ∈ frontier {y | 0 < u y} ∧
      x ∉ reducedBoundary Ω {y | 0 < u y} ∧
      ¬ (Tendsto (fun r => r * (∫ y in ball x r, (‖gradient u y‖ ^ 2 + χ y - 1)) /
            ∫ y in sphere x r, u y ^ 2 ∂hausdorffN n (n - 1)) (𝓝[>] 0) (𝓝 1) ∧
          ∃ ν : Rn n, ‖ν‖ = 1 ∧
            Tendsto (fun r => r * (∫ y in ball x r,
                ‖gradient u y - (√(heightH u x r) * alphaN n) •
                  gradient (fun z => |⟪z - x, ν⟫|) y‖ ^ 2) /
              ∫ y in sphere x r, u y ^ 2 ∂hausdorffN n (n - 1)) (𝓝[>] 0) (𝓝 0))} = 0

/-- **[K–W, Theorem 8.6]** (identification of `χ`). Let `n ≥ 2` and let `(u, χ)` be a variational
solution on an open and connected set `Ω ⊆ ℝⁿ`. Then either `u ≡ 0` on `Ω`, or `χ = χ_{u>0}`
almost everywhere on `Ω`. -/
def ChiIdentificationClaim (n : ℕ) : Prop :=
  2 ≤ n → ∀ (Ω : Set (Rn n)) (C_V : ℝ≥0) (u χ : Rn n → ℝ),
    IsConnected Ω → IsVariationalSolution Ω C_V u χ →
    (∀ x ∈ Ω, u x = 0) ∨ χ =ᵐ[volume.restrict Ω] posIndicator u

/-- **[K–W, Theorem 8.7]** (identification of `Δu`). Let `n ≥ 2` and let `(u, χ)` be a variational
solution on an open set `Ω ⊆ ℝⁿ`. Then `Ω ∩ ∂{u > 0}` is countably `ℋ^{n-1}`-rectifiable and has
locally finite `ℋ^{n-1}`-measure in `Ω`, and
`Δu = ℋ^{n-1}⌊∂*{u>0} + 2 α(n) √(H_x(u; 0+)) ℋ^{n-1}⌊Σ^H` in `Ω` in the sense of distributions.

In addition, the claim asserts that `{u > 0}` has a Gauss–Green pair in `Ω` (locally finite
perimeter), so that `∂*{u > 0}` is defined by a genuine perimeter measure, and that
`H_x(u; r) → H_x(u; 0+)` as `r → 0+` at every `x ∈ Σ^H`. -/
def LaplacianMeasureClaim (n : ℕ) [NeZero n] : Prop :=
  2 ≤ n → ∀ (Ω : Set (Rn n)) (C_V : ℝ≥0) (u χ : Rn n → ℝ), IsVariationalSolution Ω C_V u χ →
    IsCountablyRectifiable n (n - 1) (Ω ∩ frontier {x | 0 < u x}) ∧
    (∀ K, IsCompact K → K ⊆ Ω → hausdorffN n (n - 1) (K ∩ frontier {x | 0 < u x}) < ∞) ∧
    (∃ μ ν, IsGaussGreenPair Ω {x | 0 < u x} μ ν) ∧
    (∀ x ∈ sigmaH Ω u χ, Tendsto (heightH u x) (𝓝[>] 0) (𝓝 (heightHZero u x))) ∧
    HasDistribLaplacianOn Ω u (laplacianMeasure Ω u χ)

end KWChallenge

end
