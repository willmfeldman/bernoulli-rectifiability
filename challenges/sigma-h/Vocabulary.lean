module

public import Mathlib

/-!
# Trusted statements: size and frequency on the set of highest density

This file imports Mathlib only. It is the complete trusted surface of the `sigma-h` challenge:
`Challenge.lean` and `Solution.lean` both state the two claims below.

## Source

D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
DOI 10.1002/cpa.22226, arXiv:2306.10131. Numbers refer to arXiv version 2 (`[K–W]` below).

* `SigmaHMainClaim`: [K–W, Theorem 7.2] (1)–(2), the Minkowski-content (neighbourhood volume),
  Hausdorff-measure and rectifiability bounds for `Σ^H`, proved by a Naber–Valtorta covering
  argument.
* `SigmaHFrequencyClaim`: [K–W, Theorem 7.2] (3), `N_x(u; 0+) = 1` at `ℋ^{n-1}`-a.e. `x ∈ Σ^H`.

## Vocabulary

Every notion is defined below from Mathlib; the definitions are the same as in the
`main-theorem` challenge. The ambient space is `ℝⁿ = EuclideanSpace ℝ (Fin n)` with Lebesgue
measure `volume`, and every claim assumes `n ≥ 2`. `u, χ` are total functions `ℝⁿ → ℝ`.

* `hausdorffN n d = (ω_d / 2^d) μH[d]`, the normalized Hausdorff measure `ℋ^d`.
* `divergence ξ x = tr Dξ(x)`; `gradient u x` is Mathlib's gradient.
* `IsVariationalSolution Ω C_V u χ`: the definition of [K–W, §3.2], written out in full.
* `energyD`, `heightH`, `monotonicityM`, `frequencyN`: `D_x(u; r)`, `H_x(u; r)`,
  `M_x(u; r) = D − H` of [K–W, §3.3] and the frequency `N_x(u; r) = (D_x(u; r) − |B₁|) / H_x(u; r)`
  of [K–W, §4]. Sphere integrals are integrals over `sphere x r` against `ℋ^{n-1}`. Where
  `H_x(u; r) = 0` the paper sets `N_x(u; r) = −∞`; here the value is `0` (Lean's `x / 0 = 0`).
  This does not matter below: at points of `Σ^H`, `H_x(u; r) > 0` for every `r > 0` with
  `B̄_r(x) ⊆ Ω` (`u ≥ 0` is subharmonic and positive somewhere near `x`), and the bound `N₊` in the
  hypotheses is arbitrary.
* `sigmaH Ω u χ = Σ^H = {x ∈ Ω : x ∈ closure {u > 0}, M_x(u; 0+) ≥ |B₁|}` and
  `sigmaHr Ω u χ t = Σ^H_t = {x ∈ Ω : B_t(x) ⋐ Ω, x ∈ closure {u > 0}, M_x(u; t) ≥ |B₁|}` [K–W, §6].
* `IsCountablyRectifiable n k S`: up to an `ℋ^k`-null set, `S` is covered by countably many
  Lipschitz images of `ℝ^k`.
* The `s`-neighbourhood `B_s(A)` of a set `A` is Mathlib's `thickening s A`.

"For `ℋ^{n-1}`-a.e. `x ∈ A`, `P x`" is written `ℋ^{n-1} {x ∈ A | ¬ P x} = 0`.

## Differences from the printed paper

[K–W, Theorem 7.2] reads: "Let `(u, χ)` be a variational solution on `B₁`, with `0 ∈ Σ^H_t` for
some `t ∈ [0, 1]` and `N_0(u; 1) ≤ N₊`. Then there is `C = C(N₊, n)` such that (1) for every
`s ≥ t`, `|B_s(Σ^H_t ∩ B_{1/100}(x))| ≤ C s`; (2) if `t = 0`, then
`ℋ^{n-1}(Σ^H ∩ B_{1/100}(x)) ≤ C` and `Σ^H ∩ B_{1/100}` is countably `ℋ^{n-1}`-rectifiable;
(3) `N_x(u; 0+) = 1` at `ℋ^{n-1}`-a.e. `x ∈ Σ^H`." The claims differ as follows.

* In (1)–(2) the solution is assumed on an open set `Ω ⊇ B̄₁`, not only on `B₁`, while `Σ^H` and
  `Σ^H_t` are still taken relative to `B₁`. The hypothesis `N_0(u; 1) ≤ N₊` involves
  `∫_{∂B₁} u²`, which a solution on the open ball `B₁` does not constrain; if the values on `∂B₁`
  are prescribed independently, the bound can fail. For example, for `n = 2`, take
  `u = |Re z^k|` in `B₁`, `χ ≡ 1`, and `u ≡ c` on `∂B₁`:
  then `N_0(u; 1) ≤ 1` once `c` is large (depending on `k`), while `Σ^H ∩ B_{1/100}` contains the
  `k` lines `{Re z^k = 0}` near `0`, so `ℋ¹(Σ^H ∩ B_{1/100}) ≥ 2k / 100` is unbounded in `k`.
* `B_{1/100}(x)` (with `x` unbound) is read as `B_{1/100}`, centred at `0`.
* (1) is stated for `t ≤ s ≤ 1`; only small scales are used, and for large `s` the left side
  grows like `sⁿ`.
* The case `t = 0` is stated with `Σ^H` (`Σ^H_0` is read as `Σ^H`), and there the
  neighbourhood bound is claimed for all `0 < s ≤ 1`. The case `t = 1` is vacuous
  (`Σ^H_1` needs `B₁ ⋐ B₁`), so `t ∈ (0, 1)` in effect.
* (3) is stated, as in the paper, for a solution on `B₁`; `N_x(u; 0+) = 1` is the convergence
  `N_x(u; r) → 1` as `r → 0+`.
-/

@[expose] public section

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

/-- The frequency `N_x(u; r) = (D_x(u; r) − |B₁|) / H_x(u; r)` [K–W, §4]. -/
def frequencyN {n : ℕ} (u χ : Rn n → ℝ) (x : Rn n) (r : ℝ) : ℝ :=
  (energyD u χ x r - unitBallVolume n) / heightH u x r

/-- The set of highest density [K–W, §6]:
`Σ^H = {x ∈ Ω : x ∈ closure {u > 0} and M_x(u; 0+) ≥ |B₁|}`. The condition `M_x(u; 0+) ≥ |B₁|`
is written "`M_x(u; r)` converges, as `r → 0+`, to a real number `m ≥ |B₁|`". For a variational
solution `r ↦ M_x(u; r)` is nondecreasing [K–W, Proposition 3.4], so `M_x(u; 0+)` exists in
`[−∞, ∞)`, and it is `≥ |B₁|` exactly when it is a real number `≥ |B₁|`. -/
def sigmaH {n : ℕ} (Ω : Set (Rn n)) (u χ : Rn n → ℝ) : Set (Rn n) :=
  {x | x ∈ Ω ∧ x ∈ closure {y | 0 < u y} ∧
    ∃ m : ℝ, Tendsto (monotonicityM u χ x) (𝓝[>] 0) (𝓝 m) ∧ unitBallVolume n ≤ m}

/-- `Σ^H_t = {x ∈ Ω : B_t(x) ⋐ Ω, x ∈ closure {u > 0}, M_x(u; t) ≥ |B₁|}` [K–W, §6]. For `t > 0`,
`B_t(x) ⋐ Ω` (compact closure in `Ω`) is `B̄_t(x) ⊆ Ω`. -/
def sigmaHr {n : ℕ} (Ω : Set (Rn n)) (u χ : Rn n → ℝ) (t : ℝ) : Set (Rn n) :=
  {x | x ∈ Ω ∧ closedBall x t ⊆ Ω ∧ x ∈ closure {y | 0 < u y} ∧
    unitBallVolume n ≤ monotonicityM u χ x t}

/-- `S ⊆ ℝⁿ` is countably `ℋ^k`-rectifiable: up to an `ℋ^k`-null set it is contained in a countable
union of Lipschitz images of `ℝ^k`. (Lipschitz images of all of `ℝ^k` rather than of subsets of
`ℝ^k`: a Lipschitz map on a subset extends to `ℝ^k`, componentwise by McShane's theorem.) -/
def IsCountablyRectifiable (n k : ℕ) (S : Set (Rn n)) : Prop :=
  ∃ f : ℕ → Rn k → Rn n, (∀ i, ∃ C, LipschitzWith C (f i)) ∧
    hausdorffN n k (S \ ⋃ i, range (f i)) = 0

/-- **[K–W, Theorem 7.2] (1)–(2).** For every `n ≥ 2` and `N₊` there is a constant `C` such that
the following holds for every variational solution `(u, χ)`, with any constant `C_V`, on an open
set `Ω ⊇ B̄₁` with `N_0(u; 1) ≤ N₊` (with `Σ^H`, `Σ^H_t` taken relative to `B₁`):

1. if `0 ∈ Σ^H_t` with `t > 0`, then `|B_s(Σ^H_t ∩ B_{1/100})| ≤ C s` for `t ≤ s ≤ 1`;
2. if `0 ∈ Σ^H`, then `|B_s(Σ^H ∩ B_{1/100})| ≤ C s` for `0 < s ≤ 1`,
   `ℋ^{n-1}(Σ^H ∩ B_{1/100}) ≤ C`, and `Σ^H ∩ B_{1/100}` is countably `ℋ^{n-1}`-rectifiable.

The constant depends only on `n` and `N₊` (the quantifier order `∀ N₊, ∃ C, ∀ C_V u χ t`). -/
def SigmaHMainClaim (n : ℕ) : Prop :=
  2 ≤ n → ∀ Nplus : ℝ, ∃ C : ℝ, ∀ (Ω : Set (Rn n)) (C_V : ℝ≥0) (u χ : Rn n → ℝ),
    IsVariationalSolution Ω C_V u χ → closedBall 0 1 ⊆ Ω → frequencyN u χ 0 1 ≤ Nplus →
      (∀ t : ℝ, 0 < t → (0 : Rn n) ∈ sigmaHr (ball 0 1) u χ t → ∀ s : ℝ, t ≤ s → s ≤ 1 →
        volume (thickening s (sigmaHr (ball 0 1) u χ t ∩ ball 0 (1 / 100))) ≤
          ENNReal.ofReal (C * s)) ∧
      ((0 : Rn n) ∈ sigmaH (ball 0 1) u χ →
        (∀ s : ℝ, 0 < s → s ≤ 1 →
          volume (thickening s (sigmaH (ball 0 1) u χ ∩ ball 0 (1 / 100))) ≤
            ENNReal.ofReal (C * s)) ∧
        hausdorffN n (n - 1) (sigmaH (ball 0 1) u χ ∩ ball 0 (1 / 100)) ≤ ENNReal.ofReal C ∧
        IsCountablyRectifiable n (n - 1) (sigmaH (ball 0 1) u χ ∩ ball 0 (1 / 100)))

/-- **[K–W, Theorem 7.2] (3).** Let `n ≥ 2` and let `(u, χ)` be a variational solution on `B₁`
with `N_0(u; 1) ≤ N₊`, and with `0 ∈ Σ^H` or `0 ∈ Σ^H_t` for some `t > 0`. Then
`N_x(u; r) → 1` as `r → 0+` for `ℋ^{n-1}`-a.e. `x ∈ Σ^H`. -/
def SigmaHFrequencyClaim (n : ℕ) : Prop :=
  2 ≤ n → ∀ (C_V : ℝ≥0) (u χ : Rn n → ℝ), IsVariationalSolution (ball 0 1) C_V u χ →
    ∀ Nplus : ℝ, frequencyN u χ 0 1 ≤ Nplus →
    ((0 : Rn n) ∈ sigmaH (ball 0 1) u χ ∨ ∃ t : ℝ, 0 < t ∧ (0 : Rn n) ∈ sigmaHr (ball 0 1) u χ t) →
    hausdorffN n (n - 1)
      {x | x ∈ sigmaH (ball 0 1) u χ ∧ ¬ Tendsto (frequencyN u χ x) (𝓝[>] 0) (𝓝 1)} = 0

end KWChallenge

end
