module

public import Mathlib

/-!
# Trusted statement: compactness of classical solutions

This file imports Mathlib only. It is the complete trusted surface of the `classical-compactness`
challenge: `Challenge.lean` and `Solution.lean` both state the claim below.

## Source

D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
DOI 10.1002/cpa.22226, arXiv:2306.10131. Numbers refer to arXiv version 2 (`[K–W]` below).

* `ClassicalCompactnessClaim`: [K–W, Theorem 9.3], which is [K–W, Theorem 1.3] of the introduction:
  limits of uniformly Lipschitz classical solutions of the one-phase Bernoulli problem are
  variational solutions, with Hausdorff and `L¹_loc` convergence of the free boundaries and
  positivity sets, the bound `α(n) √(H_x(u; 0+)) ≤ 1` on `Σ^H`, and the conclusions of
  [K–W, Theorem 8.7].

## Vocabulary

Every notion is defined below from Mathlib; apart from `IsClassicalSolution` the definitions are
the same as in the `main-theorem` challenge. The ambient space is `ℝⁿ = EuclideanSpace ℝ (Fin n)`
with Lebesgue measure `volume`, and the claim assumes `n ≥ 2`.

* `IsClassicalSolution Ω u`: classical solutions of the one-phase Bernoulli problem
  [K–W, Definition 9.1] (see its docstring).
* `hausdorffN n d = (ω_d / 2^d) μH[d]`, the normalized Hausdorff measure `ℋ^d`.
* `IsVariationalSolution Ω C_V u χ`: the definition of [K–W, §3.2], written out in full.
* `heightH`, `energyD`, `monotonicityM`: `H_x(u; r)`, `D_x(u; r)`, `M_x(u; r)` of [K–W, §3.3];
  sphere integrals are integrals over `sphere x r` against `ℋ^{n-1}`.
* `sigmaH Ω u χ = Σ^H`, the set of highest density [K–W, §6], and
  `heightHZero u x = H_x(u; 0+) = lim_{r → 0+} H_x(u; r)`.
* `alphaN n = α(n) = (∫_{∂B₁} y_n² dℋ^{n-1})^{-1/2}` [K–W, §8.2].
* `IsCountablyRectifiable`, `IsGaussGreenPair`, `reducedBoundary`: countable
  `ℋ^k`-rectifiability, and De Giorgi's reduced boundary defined from the perimeter measure and
  outer normal.
* `laplacianMeasure Ω u χ = ℋ^{n-1}⌊∂*{u>0} + 2 α(n) √(H_x(u; 0+)) ℋ^{n-1}⌊Σ^H` and
  `HasDistribLaplacianOn Ω u μ` (`Δu = μ` in `Ω` in the sense of distributions).
* Mathlib's `TendstoLocallyUniformlyOn` (locally uniform convergence in `B₁`) and `frontier`.

"For `ℋ^{n-1}`-a.e. `x ∈ A`, `P x`" is written `ℋ^{n-1} {x ∈ A | ¬ P x} = 0`.

## Differences from the printed paper

* [K–W, Theorem 9.3] prints the hypothesis `sup_k ‖∇u_k‖_{C^{0,1}(B₁)} < ∞`, which would be a
  `C^{1,1}` bound. The intended hypothesis, as in [K–W, Theorem 1.3], is
  `sup_k ‖u_k‖_{C^{0,1}(B₁)} < ∞`; it is stated as `|u_k| ≤ C` on `B₁` and `u_k` `C`-Lipschitz on
  `B₁`, with one constant `C`.
* "`(u, χ_{u>0})` is a variational solution" is stated on `B₁` with the constant `C_V = C` of the
  hypothesis; the limit `u` is also `C`-Lipschitz on `B₁`.
* [K–W, Theorem 1.3] is printed with `Σ_**` and with an averaged `H_x(u; 0+)`; the claim uses the
  form of [K–W, Theorem 9.3], with `Σ^H` and the unaveraged `H` of §3.3, for which `α(n)` is
  normalized (see the `main-theorem` challenge).
* "`∂{u_k > 0} → ∂{u > 0}` locally in `B₁` in the Hausdorff topology" is stated as: for every
  compact `K ⊆ B₁` and `ε > 0`, eventually every point of `K ∩ ∂{u > 0}` is within `ε` of
  `B₁ ∩ ∂{u_k > 0}`, and every point of `K ∩ ∂{u_k > 0}` is within `ε` of `B₁ ∩ ∂{u > 0}`.
  "`χ_{u_k>0} → χ_{u>0}` in `L¹_loc(B₁)`" is `∫_K |χ_{u_k>0} − χ_{u>0}| → 0` for every compact
  `K ⊆ B₁`.
* The claim adds that `H_x(u; r) → H_x(u; 0+)` as `r → 0+` at every `x ∈ Σ^H`, so that
  `H_x(u; 0+)` is not a junk value.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Set Filter Topology Laplacian InnerProductSpace
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

/-- **Classical solutions** of the one-phase Bernoulli problem [K–W, Definition 9.1]. On the open
set `Ω`, `u : Ω → [0, ∞)` is Lipschitz and harmonic in `{u > 0}`, the free boundary `∂{u > 0}` is
locally a smooth hypersurface, and at each free boundary point `x`, for each unit normal `ν` to
`∂{u > 0}` at `x` pointing into `{u > 0}` (`u(x + tν) > 0` for small `t > 0`),
`(u(x + tν) − u(x)) / t → 1` as `t → 0+`.

Encoding: "`∂{u > 0}` is locally the graph of a smooth function" is stated as "near `x`,
`∂{u > 0}` is the zero set of a smooth `F` with `∇F(x) ≠ 0`"; the two are equivalent by the
implicit function theorem. The unit normals at `x` are then `±∇F(x) / |∇F(x)|`, independent of
`F`. "Harmonic in `{u > 0}`" is Mathlib's `HarmonicAt` (`C²` near the point, with vanishing
Laplacian nearby) at each point of `Ω ∩ {u > 0}`. -/
structure IsClassicalSolution {n : ℕ} (Ω : Set (Rn n)) (u : Rn n → ℝ) : Prop where
  /-- `Ω` is open. -/
  isOpen : IsOpen Ω
  /-- `u` is Lipschitz on `Ω`. -/
  lipschitzOnWith : ∃ L, LipschitzOnWith L u Ω
  /-- `u ≥ 0` on `Ω`. -/
  nonneg : ∀ x ∈ Ω, 0 ≤ u x
  /-- `u` is harmonic on `Ω ∩ {u > 0}`. -/
  harmonicAt : ∀ x ∈ Ω, 0 < u x → HarmonicAt u x
  /-- Smooth free boundary, and the free boundary condition along each inward unit normal. -/
  free_boundary : ∀ x ∈ Ω ∩ frontier {y | 0 < u y}, ∃ r, 0 < r ∧ ∃ F : Rn n → ℝ,
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F ∧ gradient F x ≠ 0 ∧
    ball x r ∩ frontier {y | 0 < u y} = ball x r ∩ {y | F y = 0} ∧
    ∀ s : ℝ, (s = 1 ∨ s = -1) →
      (∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < u (x + t • (s * ‖gradient F x‖⁻¹) • gradient F x)) →
      Tendsto (fun t => (u (x + t • (s * ‖gradient F x‖⁻¹) • gradient F x) - u x) / t)
        (𝓝[>] 0) (𝓝 1)

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

/-- **[K–W, Theorem 9.3] = [K–W, Theorem 1.3]** (compactness of classical solutions). Let `n ≥ 2`
and let `u_k` be classical solutions on `B₁` with `sup_k ‖u_k‖_{C^{0,1}(B₁)} ≤ C`: `|u_k| ≤ C` on
`B₁` and `u_k` is `C`-Lipschitz on `B₁`. Then along a subsequence `u_{φ(k)}`, `u_{φ(k)} → u`
locally uniformly in `B₁`, and:

* `u` is `C`-Lipschitz on `B₁`, and `(u, χ_{u>0})` is a variational solution on `B₁` with
  constant `C`;
* `H_x(u; r) → H_x(u; 0+)` as `r → 0+` at every `x ∈ Σ^H`, and `α(n) √(H_x(u; 0+)) ≤ 1` for
  `ℋ^{n-1}`-a.e. `x ∈ Σ^H` (`Σ^H` of `(u, χ_{u>0})` in `B₁`);
* either `u ≡ 0` on `B₁`, or `χ_{u_{φ(k)}>0} → χ_{u>0}` in `L¹_loc(B₁)` and
  `∂{u_{φ(k)} > 0} → ∂{u > 0}` locally in `B₁` in the Hausdorff sense;
* `B₁ ∩ ∂{u > 0}` is countably `ℋ^{n-1}`-rectifiable with locally finite `ℋ^{n-1}`-measure in
  `B₁`, and `Δu = ℋ^{n-1}⌊∂*{u>0} + 2 α(n) √(H_x(u; 0+)) ℋ^{n-1}⌊Σ^H` in `B₁`. -/
def ClassicalCompactnessClaim (n : ℕ) [NeZero n] : Prop :=
  2 ≤ n → ∀ (u : ℕ → Rn n → ℝ), (∀ k, IsClassicalSolution (ball 0 1) (u k)) → ∀ C : ℝ≥0,
    (∀ k, ∀ x ∈ ball (0 : Rn n) 1, |u k x| ≤ C) → (∀ k, LipschitzOnWith C (u k) (ball 0 1)) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : Rn n → ℝ,
      TendstoLocallyUniformlyOn (fun k => u (φ k)) v atTop (ball 0 1) ∧
      LipschitzOnWith C v (ball 0 1) ∧
      IsVariationalSolution (ball 0 1) C v (posIndicator v) ∧
      (∀ x ∈ sigmaH (ball 0 1) v (posIndicator v),
        Tendsto (heightH v x) (𝓝[>] 0) (𝓝 (heightHZero v x))) ∧
      hausdorffN n (n - 1) {x | x ∈ sigmaH (ball 0 1) v (posIndicator v) ∧
        ¬ alphaN n * √(heightHZero v x) ≤ 1} = 0 ∧
      ((∀ x ∈ ball (0 : Rn n) 1, v x = 0) ∨
        ((∀ K, IsCompact K → K ⊆ ball 0 1 →
            Tendsto (fun k => ∫ x in K, |posIndicator (u (φ k)) x - posIndicator v x|) atTop
              (𝓝 0)) ∧
          ∀ K, IsCompact K → K ⊆ ball 0 1 → ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
            (∀ x ∈ K ∩ frontier {y | 0 < v y},
              ∃ y ∈ ball 0 1 ∩ frontier {y | 0 < u (φ k) y}, dist x y < ε) ∧
            (∀ x ∈ K ∩ frontier {y | 0 < u (φ k) y},
              ∃ y ∈ ball 0 1 ∩ frontier {y | 0 < v y}, dist x y < ε))) ∧
      IsCountablyRectifiable n (n - 1) (ball 0 1 ∩ frontier {x | 0 < v x}) ∧
      (∀ K, IsCompact K → K ⊆ ball 0 1 →
        hausdorffN n (n - 1) (K ∩ frontier {x | 0 < v x}) < ∞) ∧
      HasDistribLaplacianOn (ball 0 1) v (laplacianMeasure (ball 0 1) v (posIndicator v))

end KWChallenge

end
