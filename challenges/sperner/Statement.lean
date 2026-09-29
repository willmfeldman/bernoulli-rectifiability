import Mathlib

/-!
# Trusted statement: Sperner's inequality for one-homogeneous harmonic functions

This file imports Mathlib only. It is the complete trusted surface of the `sperner` challenge:
`Challenge.lean` and `Solution.lean` both state the claim below.

## Source

E. Sperner, *Zur Symmetrisierung von Funktionen auf Sphären*, Math. Z. 134 (1973), 317–327.

Sperner's inequality says that among open subsets of the unit sphere `S^{n-1}` with a given first
Dirichlet eigenvalue of the Laplace–Beltrami operator, spherical caps have the least area. It is
used in D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness
for non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
DOI 10.1002/cpa.22226, arXiv:2306.10131 (numbering of arXiv v2), in the proofs of Lemma 8.1 and
Lemma 8.3, in the following form: a one-homogeneous blow-up `u₀ ≥ 0` that is harmonic in
`{u₀ > 0}` has, on each component of `{u₀ > 0} ∩ ∂B₁`, a positive Dirichlet eigenfunction with
eigenvalue `n − 1`. The cap with first eigenvalue `n − 1` is the half-sphere, so each such
component has at least half the area of the sphere, and equality holds only for a half-sphere, on
which `u₀` is linear.

## The claim

The claim is stated for the cone over the spherical domain, so that no spherical calculus is
needed: `U` is the connected component of `{u > 0}` through a point `y₀`, and "`U ∩ ∂B₁` has at
least half the area of `∂B₁`" is the equivalent statement `|U ∩ B₁| ≥ |B₁| / 2` about the cone.
All notions are Mathlib's: `EuclideanSpace ℝ (Fin n)` with Lebesgue measure `volume`,
`LipschitzWith`, `connectedComponentIn`, and `InnerProductSpace.HarmonicAt` (`C²` near the point
with vanishing Laplacian nearby).
-/

noncomputable section

open MeasureTheory Metric Set InnerProductSpace
open scoped NNReal RealInnerProductSpace

namespace SpernerChallenge

/-- **Sperner's inequality**, homogeneous form, with the equality case. Let `n ≥ 2`, let
`u : ℝⁿ → [0, ∞)` be Lipschitz and one-homogeneous (`u(t y) = t u(y)` for `t > 0`), let
`u(y₀) > 0`, and let `U` be the connected component of `{u > 0}` containing `y₀`. If `u` is
harmonic at every point of `U`, then `|U ∩ B₁| ≥ |B₁| / 2`. If equality holds, then `U` is an
open half-space `{y : ⟪y, e⟫ > 0}` with `‖e‖ = 1`, and `u(y) = a ⟪y, e⟫` on `U` for some `a > 0`. -/
def SpernerHalfVolumeClaim (n : ℕ) : Prop :=
  2 ≤ n → ∀ u : EuclideanSpace ℝ (Fin n) → ℝ, (∃ L, LipschitzWith L u) → (∀ y, 0 ≤ u y) →
    (∀ y (t : ℝ), 0 < t → u (t • y) = t * u y) → ∀ y₀ : EuclideanSpace ℝ (Fin n), 0 < u y₀ →
    (∀ y ∈ connectedComponentIn {y | 0 < u y} y₀, HarmonicAt u y) →
    (volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal / 2 ≤
        (volume (connectedComponentIn {y | 0 < u y} y₀ ∩ ball 0 1)).toReal ∧
      ((volume (connectedComponentIn {y | 0 < u y} y₀ ∩ ball 0 1)).toReal =
          (volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal / 2 →
        ∃ e : EuclideanSpace ℝ (Fin n), ‖e‖ = 1 ∧
          connectedComponentIn {y | 0 < u y} y₀ = {y | 0 < ⟪y, e⟫} ∧
          ∃ a : ℝ, 0 < a ∧ ∀ y ∈ connectedComponentIn {y | 0 < u y} y₀, u y = a * ⟪y, e⟫)

end SpernerChallenge
