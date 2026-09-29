import Mathlib

/-!
# Trusted statements: variational solutions with a Lipschitz coefficient

This file imports Mathlib only. It is the complete trusted surface of the `lipschitz-q`
challenge: `Challenge.lean` and `Solution.lean` both state the six claims below.

## Source

D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
DOI 10.1002/cpa.22226, arXiv:2306.10131. Numbers refer to arXiv version 2 (`[K–W]` below).

The paper treats the functional `∫ (|∇u|² + χ)`, that is, the constant coefficient `Q ≡ 1`. The
claims below are for the functional `∫ (|∇u|² + Q² χ)` with a Lipschitz coefficient `Q`,
`0 < c ≤ Q ≤ C'`. The paper does not state them; each is the Lipschitz-coefficient form of a
result of the paper for `Q ≡ 1`.

* `SigmaHQDensityClaim`: the density characterization of `Σ^H`, the form in which the
  introduction of [K–W] writes `Σ^H` (for `Q ≡ 1`, the definition of [K–W, §6] together with
  [K–W, Proposition 3.5]).
* `SigmaHQClosedClaim`: `Σ^H` is relatively closed in `Ω` ([K–W, §6], from the upper
  semicontinuity in [K–W, Proposition 3.5]).
* `ViscosityQClaim`: `u` is a viscosity solution of `|∇u| = Q` on `Ω \ Σ^H`
  ([K–W, Lemma 8.3]).
* `BlowupLimitQClaim`: blow-up limits exist and are variational solutions on `ℝⁿ` for the
  constant coefficient `Q(x)` (the first paragraph of the proof of [K–W, Theorem 9.3], applied
  to the rescalings (3.6)).
* `BlowupHomogeneousQClaim`: blow-up limits are homogeneous of degree one
  ([K–W, Proposition 3.4], last claim).
* `ChiIdentificationQClaim`: either `u ≡ 0` and `χ = 1` a.e., or `χ = χ_{u>0}` a.e.
  ([K–W, Theorem 8.6]), for a solution given near each point of a connected set.

## Vocabulary

Every notion is defined below from Mathlib; `unitBallVolume`, `hausdorffN`, `divergence`,
`posIndicator` and `heightH` are the same as in the `main-theorem` challenge. The ambient space
is `ℝⁿ = EuclideanSpace ℝ (Fin n)` with Lebesgue measure `volume`, and every claim assumes
`n ≥ 2`. `Q, u, χ` are total functions `ℝⁿ → ℝ`; only their values on `Ω` enter the definitions.

* `hausdorffN n d = (ω_d / 2^d) μH[d]`, the normalized Hausdorff measure `ℋ^d`.
* `divergence ξ x = tr Dξ(x)`; `gradient u x` is Mathlib's gradient.
* `IsVariationalSolutionQ Ω C_V Q u χ`: the definition of variational solution of [K–W, §3.2]
  with the domain-variation identity of `∫ (|∇u|² + Q² χ)` in place of that of
  `∫ (|∇u|² + χ)`, written out in full (see its docstring). For `Q ≡ 1` it is the definition of
  the `main-theorem` challenge.
* `QBounds Ω Q L c C'`: `Q` is `L`-Lipschitz on `Ω` and `0 < c ≤ Q ≤ C'` on `Ω`.
* `energyDq`, `heightH`, `monotonicityMq`: the quantities `D`, `H`, `M = D − H` of [K–W, §3.3]
  with the coefficient frozen at a constant `q`, that is, with `χ` replaced by `q² χ` in `D`.
  Sphere integrals are integrals over `sphere x r` against `ℋ^{n-1}`.
* `sigmaHQ Ω Q u χ = Σ^H = {x ∈ Ω : x ∈ closure {u > 0}, M^{Q(x)}_x(u; 0+) ≥ Q(x)² |B₁|}`, the
  set of highest density with the coefficient frozen at the point. For `Q ≡ 1` it is the `Σ^H`
  of [K–W, §6].
* `IsViscositySolutionQ Ω Q u`: viscosity solutions of `Δu = 0` in `{u > 0}`, `|∇u| = Q` on
  `∂{u > 0}` ([K–W, Definition 8.1] with `1` replaced by `Q(x)`).
* `oneHomRescale u x r = u_{x,r} = u(x + r ·) / r` and `chiRescale χ x r = χ_{x,r} = χ(x + r ·)`,
  the rescalings (3.6).

## Differences from the paper

* The paper states these results for `Q ≡ 1` only; see above.
* `Σ^H` is defined with the limit `M^{Q(x)}_x(u; 0+)`, as in [K–W, §6]. For a non-constant
  coefficient `r ↦ M^{Q(x)}_x(u; r)` is only almost monotone (`M + C r` is nondecreasing), so the
  limit exists in `[−∞, ∞)`, but the characterization "`M_x(u; r) ≥ |B₁|` for every `r`" of the
  constant case is not available.
* The density characterization is stated with the relative free boundary
  `frontier {y ∈ Ω : u(y) > 0}` and the density `|{χ = 1} ∩ B_r(x)| / |B_r(x)| → 1`.
* The blow-up limit claim is stated along a sequence `r_k → 0+` along which `u_{x,r_k}` converges
  locally uniformly (such sequences exist by Arzelà–Ascoli, since `u_{x,r}` is `C_V`-Lipschitz
  with `u_{x,r}(0) = 0` at free boundary points); `χ_{x,r_k}` converges in `L¹_loc(ℝⁿ)` along a
  further subsequence. The limit is a solution with the constant coefficient `Q(x)` and the same
  gradient constant `C_V`.
* The identification of `χ` is stated for a set `U` that is connected and on which `(u, χ)` is a
  solution near every point, with a coefficient bounded and Lipschitz on each neighbourhood. If
  `u ≡ 0` on `U` it also asserts `χ = 1` a.e. on `U`.
-/

noncomputable section

open MeasureTheory Metric Set Filter Topology InnerProductSpace
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

/-- **Variational solutions with a coefficient `Q`**. A pair `(u, χ)` is a variational solution
on the open set `Ω` with constant `C_V` for the coefficient `Q` if

1. `u : Ω → [0, ∞)`, `u ∈ C⁰(Ω) ∩ C²({u > 0})`, and `|∇u| ≤ C_V` on `Ω`;
2. `χ : Ω → {0, 1}` is Borel measurable;
3. `χ_{u>0} ≤ χ` Lebesgue-a.e. on `Ω`;
4. for every Lipschitz vector field `ξ` with compact support in `Ω`,
   `∫ ((|∇u|² + Q² χ) div ξ − 2 ∇u · Dξ ∇u + ∇(Q²) · ξ χ) = 0`
   (the first variation of `∫ (|∇u|² + Q² χ)` under the domain deformations `x ↦ x + t ξ(x)`).

Items 1–3 and the encoding are those of the definition of [K–W, §3.2] (see the `main-theorem`
challenge); for `Q ≡ 1` the definition is that one. `∇(Q²) · ξ` is written
`D(Q²)(x) ξ(x)`, with Mathlib's Fréchet derivative, which is `0` where `Q²` is not
differentiable; for `Q` Lipschitz on `Ω` this is a Lebesgue-null subset of `Ω` (Rademacher).
Bounds on `Q` are not part of the definition; the claims assume them separately (`QBounds`). -/
structure IsVariationalSolutionQ {n : ℕ} (Ω : Set (Rn n)) (C_V : ℝ≥0) (Q u χ : Rn n → ℝ) :
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
  /-- The domain-variation identity of `∫ (|∇u|² + Q² χ)`, for every Lipschitz `ξ` with compact
  support in `Ω`. -/
  innerVariationQ_eq_zero : ∀ ξ : Rn n → Rn n, (∃ L, LipschitzWith L ξ) → HasCompactSupport ξ →
    tsupport ξ ⊆ Ω →
    ∫ x, ((‖gradient u x‖ ^ 2 + Q x ^ 2 * χ x) * divergence ξ x -
      2 * ⟪gradient u x, fderiv ℝ ξ x (gradient u x)⟫ +
      fderiv ℝ (fun y => Q y ^ 2) x (ξ x) * χ x) = 0

/-- Bounds on the coefficient: `Q` is `L`-Lipschitz on `Ω` and `c ≤ Q ≤ C'` on `Ω`, with
`c > 0`. -/
structure QBounds {n : ℕ} (Ω : Set (Rn n)) (Q : Rn n → ℝ) (L : ℝ≥0) (c C' : ℝ) : Prop where
  /-- `Q` is `L`-Lipschitz on `Ω`. -/
  lipschitzOnWith : LipschitzOnWith L Q Ω
  /-- The lower bound is positive. -/
  pos : 0 < c
  /-- `Q ≥ c` on `Ω`. -/
  le : ∀ x ∈ Ω, c ≤ Q x
  /-- `Q ≤ C'` on `Ω`. -/
  le' : ∀ x ∈ Ω, Q x ≤ C'

/-- `D^q_x(u; r) = r^{-n} ∫_{B_r(x)} (|∇u|² + q² χ)`: the quantity `D_x(u; r)` of [K–W, §3.3]
with the coefficient frozen at the constant `q`. -/
def energyDq {n : ℕ} (q : ℝ) (u χ : Rn n → ℝ) (x : Rn n) (r : ℝ) : ℝ :=
  (r ^ n)⁻¹ * ∫ y in ball x r, (‖gradient u y‖ ^ 2 + q ^ 2 * χ y)

/-- `H_x(u; r) = r^{-(n+1)} ∫_{∂B_r(x)} u² dℋ^{n-1}` [K–W, §3.3]. -/
def heightH {n : ℕ} (u : Rn n → ℝ) (x : Rn n) (r : ℝ) : ℝ :=
  (r ^ (n + 1))⁻¹ * ∫ y in sphere x r, u y ^ 2 ∂hausdorffN n (n - 1)

/-- The Weiss energy `M^q_x(u; r) = D^q_x(u; r) − H_x(u; r)` [K–W, §3.3] with the coefficient
frozen at `q`. -/
def monotonicityMq {n : ℕ} (q : ℝ) (u χ : Rn n → ℝ) (x : Rn n) (r : ℝ) : ℝ :=
  energyDq q u χ x r - heightH u x r

/-- The set of highest density for the coefficient `Q`:
`Σ^H = {x ∈ Ω : x ∈ closure {u > 0} and M^{Q(x)}_x(u; 0+) ≥ Q(x)² |B₁|}`. The condition is
written "`M^{Q(x)}_x(u; r)` converges, as `r → 0+`, to a real number `m ≥ Q(x)² |B₁|`". For a
variational solution with `QBounds`, `M^{Q(x)}_x(u; r) + C r` is nondecreasing in `r` for some
`C`, so the limit `M^{Q(x)}_x(u; 0+)` exists in `[−∞, ∞)`, and it is `≥ Q(x)² |B₁|` exactly when
it is a real number `≥ Q(x)² |B₁|`. For `Q ≡ 1` this is the `Σ^H` of [K–W, §6]. -/
def sigmaHQ {n : ℕ} (Ω : Set (Rn n)) (Q u χ : Rn n → ℝ) : Set (Rn n) :=
  {x | x ∈ Ω ∧ x ∈ closure {y | 0 < u y} ∧
    ∃ m : ℝ, Tendsto (monotonicityMq (Q x) u χ x) (𝓝[>] 0) (𝓝 m) ∧
      Q x ^ 2 * unitBallVolume n ≤ m}

/-- **Viscosity solutions with a coefficient `Q`** ([K–W, Definition 8.1] with the free boundary
condition `|∇u| = Q`). `u : Ω → [0, ∞)` is continuous and harmonic in `{u > 0}`. For every free
boundary point `x ∈ Ω ∩ ∂{u > 0}`, every ball `B_r(x) ⊆ Ω` and every smooth `φ` with `φ(x) = 0`:
`φ ≤ u` on `B_r(x)` implies `|∇φ(x)| ≤ Q(x)`, and `φ₊ ≥ u` on `B_r(x)` implies
`|∇φ(x)| ≥ Q(x)`. "Harmonic in `{u > 0}`" is Mathlib's `HarmonicAt` (`C²` near the point, with
vanishing Laplacian nearby) at each point of `Ω ∩ {u > 0}`. -/
structure IsViscositySolutionQ {n : ℕ} (Ω : Set (Rn n)) (Q u : Rn n → ℝ) : Prop where
  /-- `u` is continuous on `Ω`. -/
  continuousOn : ContinuousOn u Ω
  /-- `u ≥ 0` on `Ω`. -/
  nonneg : ∀ x ∈ Ω, 0 ≤ u x
  /-- `u` is harmonic in `Ω ∩ {u > 0}`. -/
  harmonicAt : ∀ x ∈ Ω, 0 < u x → HarmonicAt u x
  /-- Touching from below: `φ ≤ u` near a free boundary point forces `|∇φ(x)| ≤ Q(x)`. -/
  norm_gradient_le : ∀ x ∈ Ω ∩ frontier {y | 0 < u y}, ∀ r, 0 < r → ball x r ⊆ Ω →
    ∀ φ : Rn n → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → φ x = 0 →
      (∀ y ∈ ball x r, φ y ≤ u y) → ‖gradient φ x‖ ≤ Q x
  /-- Touching from above: `φ₊ ≥ u` near a free boundary point forces `|∇φ(x)| ≥ Q(x)`. -/
  one_le_norm_gradient : ∀ x ∈ Ω ∩ frontier {y | 0 < u y}, ∀ r, 0 < r → ball x r ⊆ Ω →
    ∀ φ : Rn n → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → φ x = 0 →
      (∀ y ∈ ball x r, u y ≤ max (φ y) 0) → Q x ≤ ‖gradient φ x‖

/-- The one-homogeneous rescaling `u_{x,r}(y) = u(x + r y) / r` [K–W, (3.6)]. -/
def oneHomRescale {n : ℕ} (u : Rn n → ℝ) (x : Rn n) (r : ℝ) : Rn n → ℝ :=
  fun y => u (x + r • y) / r

/-- The rescaling `χ_{x,r}(y) = χ(x + r y)` [K–W, (3.6)]. -/
def chiRescale {n : ℕ} (χ : Rn n → ℝ) (x : Rn n) (r : ℝ) : Rn n → ℝ :=
  fun y => χ (x + r • y)

/-- **Density characterization of `Σ^H`**, Lipschitz coefficient. Let `n ≥ 2` and let `(u, χ)` be
a variational solution on `Ω` for a coefficient `Q` with `QBounds Ω Q L c C'`. Then `x ∈ Σ^H` if
and only if `x ∈ Ω` lies on the relative free boundary `frontier {y ∈ Ω : u(y) > 0}` and
`|{χ = 1} ∩ B_r(x)| / |B_r(x)| → 1` as `r → 0+`. -/
def SigmaHQDensityClaim (n : ℕ) : Prop :=
  2 ≤ n → ∀ (Ω : Set (Rn n)) (C_V : ℝ≥0) (Q u χ : Rn n → ℝ) (L : ℝ≥0) (c C' : ℝ),
    QBounds Ω Q L c C' → IsVariationalSolutionQ Ω C_V Q u χ → ∀ x : Rn n,
    x ∈ sigmaHQ Ω Q u χ ↔ x ∈ Ω ∧ x ∈ frontier {y | y ∈ Ω ∧ 0 < u y} ∧
      Tendsto (fun r => volume ({y | χ y = 1} ∩ ball x r) / volume (ball x r)) (𝓝[>] 0)
        (𝓝 1)

/-- **`Σ^H` is relatively closed in `Ω`**, Lipschitz coefficient: under the hypotheses of
`SigmaHQDensityClaim`, `closure Σ^H ∩ Ω ⊆ Σ^H`. -/
def SigmaHQClosedClaim (n : ℕ) : Prop :=
  2 ≤ n → ∀ (Ω : Set (Rn n)) (C_V : ℝ≥0) (Q u χ : Rn n → ℝ) (L : ℝ≥0) (c C' : ℝ),
    QBounds Ω Q L c C' → IsVariationalSolutionQ Ω C_V Q u χ →
    closure (sigmaHQ Ω Q u χ) ∩ Ω ⊆ sigmaHQ Ω Q u χ

/-- **Viscosity property off `Σ^H`** ([K–W, Lemma 8.3]), Lipschitz coefficient: under the
hypotheses of `SigmaHQDensityClaim`, `u` is a viscosity solution of `|∇u| = Q` on the open set
`Ω \ Σ^H`. -/
def ViscosityQClaim (n : ℕ) : Prop :=
  2 ≤ n → ∀ (Ω : Set (Rn n)) (C_V : ℝ≥0) (Q u χ : Rn n → ℝ) (L : ℝ≥0) (c C' : ℝ),
    QBounds Ω Q L c C' → IsVariationalSolutionQ Ω C_V Q u χ →
    IsViscositySolutionQ (Ω \ sigmaHQ Ω Q u χ) Q u

/-- **Blow-up limits**, Lipschitz coefficient. Let `n ≥ 2`, let `(u, χ)` be a variational solution
on `Ω` with constant `C_V` for a coefficient `Q` with `QBounds Ω Q L c C'`, let `x ∈ Ω`, and let
`r_k → 0+` with `u_{x,r_k} → u₀` locally uniformly on `ℝⁿ`. Then along a subsequence
`χ_{x,r_k} → χ₀` in `L¹_loc(ℝⁿ)`, where `(u₀, χ₀)` is a variational solution on `ℝⁿ` with
constant `C_V` for the constant coefficient `Q(x)`. -/
def BlowupLimitQClaim (n : ℕ) : Prop :=
  2 ≤ n → ∀ (Ω : Set (Rn n)) (C_V : ℝ≥0) (Q u χ : Rn n → ℝ) (L : ℝ≥0) (c C' : ℝ),
    QBounds Ω Q L c C' → IsVariationalSolutionQ Ω C_V Q u χ → ∀ x ∈ Ω, ∀ r : ℕ → ℝ,
    (∀ k, 0 < r k) → Tendsto r atTop (𝓝 0) → ∀ u₀ : Rn n → ℝ,
    TendstoLocallyUniformly (fun k => oneHomRescale u x (r k)) u₀ atTop →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ χ₀ : Rn n → ℝ,
      IsVariationalSolutionQ univ C_V (fun _ => Q x) u₀ χ₀ ∧
      ∀ K : Set (Rn n), IsCompact K →
        Tendsto (fun k => ∫ y in K, |chiRescale χ x (r (φ k)) y - χ₀ y|) atTop (𝓝 0)

/-- **Blow-up limits are homogeneous** ([K–W, Proposition 3.4], last claim), Lipschitz
coefficient: under the hypotheses of `BlowupLimitQClaim`, `u₀(t y) = t u₀(y)` for all `t > 0`
and `y ∈ ℝⁿ`. -/
def BlowupHomogeneousQClaim (n : ℕ) : Prop :=
  2 ≤ n → ∀ (Ω : Set (Rn n)) (C_V : ℝ≥0) (Q u χ : Rn n → ℝ) (L : ℝ≥0) (c C' : ℝ),
    QBounds Ω Q L c C' → IsVariationalSolutionQ Ω C_V Q u χ → ∀ x ∈ Ω, ∀ r : ℕ → ℝ,
    (∀ k, 0 < r k) → Tendsto r atTop (𝓝 0) → ∀ u₀ : Rn n → ℝ,
    TendstoLocallyUniformly (fun k => oneHomRescale u x (r k)) u₀ atTop →
    ∀ t : ℝ, 0 < t → ∀ y : Rn n, u₀ (t • y) = t * u₀ y

/-- **Identification of `χ`** ([K–W, Theorem 8.6]), Lipschitz coefficient. Let `n ≥ 2` and let
`U ⊆ ℝⁿ` be connected. Suppose every `x ∈ U` has an open neighbourhood `V ⊆ U` on which `(u, χ)`
is a variational solution, with some constant `C_V`, for the coefficient `Q`, and `Q` satisfies
`QBounds V Q L c C'` for some `L, c, C'`. Then either `u ≡ 0` on `U` and `χ = 1` a.e. on `U`, or
`χ = χ_{u>0}` a.e. on `U`. -/
def ChiIdentificationQClaim (n : ℕ) : Prop :=
  2 ≤ n → ∀ (U : Set (Rn n)) (Q u χ : Rn n → ℝ), IsConnected U →
    (∀ x ∈ U, ∃ V : Set (Rn n), IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      ∃ (C_V L : ℝ≥0) (c C' : ℝ), QBounds V Q L c C' ∧ IsVariationalSolutionQ V C_V Q u χ) →
    ((∀ x ∈ U, u x = 0) ∧ ∀ᵐ y ∂(volume.restrict U), χ y = 1) ∨
      χ =ᵐ[volume.restrict U] posIndicator u

end KWChallenge
