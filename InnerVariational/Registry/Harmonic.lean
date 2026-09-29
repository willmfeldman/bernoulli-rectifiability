/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Defs.Calculus
public import InnerVariational.Analysis.Harnack
public import InnerVariational.Analysis.HarmonicLimit
public import InnerVariational.Analysis.SubMeanValue
public import InnerVariational.Harmonic.SpernerGlue
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Registry: harmonic and subharmonic functions

Classical results on harmonic and subharmonic functions used by the proof, all proved in this
repository:

* `sperner_half_volume`: Sperner's inequality, in the form used for one-homogeneous blow-ups in
  the proofs of Lemmas 8.1 and 8.3 of Kriventsov–Weiss. Proved in the `Sperner` library of this
  repository (which depends on Mathlib only), via `Harmonic/SpernerGlue.lean`.
* `harmonicAt_of_tendstoLocallyUniformlyOn`, `harnack_inequality`: interior estimates
  (Weierstrass-type convergence theorem for harmonic functions) and the Harnack inequality
  (Gilbarg–Trudinger, Thms 2.8, 2.10 and 2.5). Proved in `Analysis/HarmonicLimit.lean` and
  `Analysis/Harnack.lean`.
* `IsWeaklySubharmonicOn.le_average`: continuous weakly subharmonic functions satisfy the
  sub-mean-value property (Gilbarg–Trudinger, Thm 2.1). Proved in `Analysis/SubMeanValue.lean`.

## References

* D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
  DOI 10.1002/cpa.22226; arXiv:2306.10131. Result numbers refer to arXiv v2.
* E. Sperner, *Zur Symmetrisierung von Funktionen auf Sphären*, Math. Z. 134 (1973), 317–327.
* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Springer, 2001 (reprint of the 1998 ed.).
-/

open MeasureTheory Metric Set Filter Topology InnerProductSpace
open scoped NNReal ENNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational.Registry

variable {n : ℕ}

/-- **Sperner's inequality, homogeneous form.** Let `u₀ ≥ 0` be Lipschitz and
one-homogeneous on `ℝⁿ`, `n ≥ 2`, and let `U` be the connected component of `{u₀ > 0}` through
`y₀`. Suppose `u₀` is harmonic on `U`. Then `u₀` vanishes on `∂U`, and its trace on
`U ∩ S^{n-1}` is a positive Dirichlet eigenfunction with eigenvalue `n − 1`. Sperner's
inequality then gives `|U ∩ B_1| ≥ |B_1|/2`. In the equality case `U` is an open half-space
`{⟪y, e⟫ > 0}`, and `u₀ = a⟪y, e⟫` on `U` with `a > 0` (simplicity of the first eigenvalue of the
hemisphere). Proved in the `Sperner` library; see `Harmonic/SpernerGlue.lean`. -/
theorem sperner_half_volume (hn : 2 ≤ n) {u₀ : Rn n → ℝ} (hLip : ∃ L, LipschitzWith L u₀)
    (hnn : ∀ y, 0 ≤ u₀ y) (hhom : ∀ y (t : ℝ), 0 < t → u₀ (t • y) = t * u₀ y) {y₀ : Rn n}
    (hy₀ : 0 < u₀ y₀) (hharm : ∀ y ∈ connectedComponentIn {y | 0 < u₀ y} y₀, HarmonicAt u₀ y) :
    unitBallVolume n / 2 ≤
        (volume (connectedComponentIn {y | 0 < u₀ y} y₀ ∩ ball 0 1)).toReal ∧
      ((volume (connectedComponentIn {y | 0 < u₀ y} y₀ ∩ ball 0 1)).toReal =
          unitBallVolume n / 2 →
        ∃ e : Rn n, ‖e‖ = 1 ∧ connectedComponentIn {y | 0 < u₀ y} y₀ = {y | 0 < ⟪y, e⟫} ∧
          ∃ a : ℝ, 0 < a ∧ ∀ y ∈ connectedComponentIn {y | 0 < u₀ y} y₀, u₀ y = a * ⟪y, e⟫) := by
  exact Harmonic.sperner_half_volume hn hLip hnn hhom hy₀ hharm

/-- **Convergence of harmonic functions** (Weierstrass-type; Gilbarg–Trudinger, Thms 2.8 and
2.10). A locally uniform limit of harmonic functions on an open set is harmonic,
and the gradients converge locally uniformly. Proved in `Analysis/HarmonicLimit.lean`. -/
theorem harmonicAt_of_tendstoLocallyUniformlyOn {U : Set (Rn n)} (hU : IsOpen U)
    {F : ℕ → Rn n → ℝ} {f : Rn n → ℝ} (hF : ∀ k, ∀ x ∈ U, HarmonicAt (F k) x)
    (hconv : TendstoLocallyUniformlyOn F f atTop U) :
    (∀ x ∈ U, HarmonicAt f x) ∧
      TendstoLocallyUniformlyOn (fun k => gradient (F k)) (gradient f) atTop U := by
  exact Analysis.harmonicAt_of_tendstoLocallyUniformlyOn hU hF hconv

/-- **Harnack inequality** (Gilbarg–Trudinger, Thm 2.5). There is `C = C(n)` such that
every nonnegative harmonic function on `B_{2r}(x)` satisfies `f(y) ≤ C f(z)` for `y, z ∈ B_r(x)`.
Proved in `Analysis/Harnack.lean`. -/
theorem harnack_inequality [NeZero n] :
    ∃ C : ℝ, ∀ (f : Rn n → ℝ) (x : Rn n) (r : ℝ), 0 < r →
      (∀ y ∈ ball x (2 * r), HarmonicAt f y ∧ 0 ≤ f y) →
      ∀ y ∈ ball x r, ∀ z ∈ ball x r, f y ≤ C * f z := by
  exact Analysis.harnack_inequality

/-- **Sub-mean-value property** (Gilbarg–Trudinger, Thm 2.1, for `C²` functions; the weak case is
proved by a radial test-function argument). A continuous weakly subharmonic function on an open `Ω`
satisfies `u(x) ≤ ⨍_{∂B_r(x)} u` and `u(x) ≤ ⨍_{B_r(x)} u` whenever `closedBall x r ⊆ Ω`, `r > 0`.
Here `|∂B_r| = n |B_1| r^{n-1}` and `|B_r| = r^n |B_1|`. Proved in `Analysis/SubMeanValue.lean`. -/
theorem IsWeaklySubharmonicOn.le_average [NeZero n] {Ω : Set (Rn n)} (hΩ : IsOpen Ω)
    {u : Rn n → ℝ} (hu : ContinuousOn u Ω) (hsub : IsWeaklySubharmonicOn Ω u) {x : Rn n}
    {r : ℝ} (hr : 0 < r) (hball : closedBall x r ⊆ Ω) :
    u x * (n * unitBallVolume n * r ^ (n - 1)) ≤ sphereIntegral u x r ∧
      u x * (r ^ n * unitBallVolume n) ≤ ∫ y in ball x r, u y := by
  exact Analysis.IsWeaklySubharmonicOn.le_average hΩ hu hsub hr hball

end InnerVariational.Registry
