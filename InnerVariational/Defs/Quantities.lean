/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Defs.VariationalSolution
public import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
public import GMTFoundations.Defs.Setup

/-!
# Monotonicity and frequency quantities

The scalar quantities of Kriventsov–Weiss (full reference below):

* `energyD u χ x r = D_x(u; r) = r^{-n} ∫_{B_r(x)} (|∇u|² + χ)` (Section 3.3);
* `heightH u x r = H_x(u; r) = r^{-(n+1)} ∫_{∂B_r(x)} u² dℋ^{n-1}` (Section 3.3);
* `monotonicityM = D − H`, the Weiss monotonicity formula (Section 3.3);
* `frequencyN = (D − |B_1|) / H`, the frequency (Section 4);
* `volumeV = r^{-n} ∫_{B_r(x)} (1 − χ) / H`, the volume difference (Section 4; see the note on
  the factor `r^{-n}` below);
* the one-homogeneous rescaling `u_{x,r}(y) = u(x + r y)/r`, `χ_{x,r}(y) = χ(x + r y)`
  (equation (3.6));
* `heightHZero u x = H_x(u; 0+)` (Section 8.3; the limit exists on `Σ^H` because `H_x(u; ·)` is
  nondecreasing there);
* `alphaN n = α(n) = (∫_{∂B_1} y_1² dℋ^{n-1})^{-1/2}` (Section 8.2);
* `absProfile ν x y = |(y − x)·ν|`, the one-dimensional profile of Theorem 1.2 (iv).

## Conventions

* All quantities are defined for all `r : ℝ`. They are only meaningful for `0 < r`, and every
  use assumes it. `sphereIntegral` is junk for `r ≤ 0`.
* `N` is real-valued. Where `H = 0` the paper sets `N = −∞`; Lean gives `x / 0 = 0`.
  Every use has `H > 0` available.
* The paper prints the volume difference as `V_x(u; r) = ∫_{B_r(x)} (1 − χ) / H_x(u; r)`,
  without the factor `r^{-n}`, which (4.11), `N + V = r ∫_{B_r}|∇u|² / ∫_{∂B_r} u²`, uses; the
  two agree at `r = 1`. We include the factor `r^{-n}`.
* `H` is the unaveraged quantity of Section 3.3, which is the one that `α(n)` normalizes. (The
  introduction writes `H_x(u; 0+)` with a spherical average; see `Defs/LaplacianMeasure.lean`.)
* `α(n)` uses the first coordinate `y 0` rather than the paper's `y_n`. The two agree by the
  rotation invariance of `ℋ^{n-1}⌊∂B_1` (the surface measure `toSphere` is normalized
  `ℋ^{n-1}` and is rotation invariant). This requires `[NeZero n]`.

## References

* D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
  DOI 10.1002/cpa.22226; arXiv:2306.10131. Result and equation numbers refer to arXiv v2.
* G. S. Weiss, *Partial regularity for a minimum problem with free boundary*, J. Geom. Anal. 9
  (1999), 317–326 (the monotonicity formula).
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

/-- `D_x(u; r) = r^{-n} ∫_{B_r(x)} (|∇u|² + χ)` (Section 3.3). -/
def energyD (u χ : Rn n → ℝ) (x : Rn n) (r : ℝ) : ℝ :=
  (r ^ n)⁻¹ * ∫ y in ball x r, (‖gradient u y‖ ^ 2 + χ y)

/-- `H_x(u; r) = r^{-(n+1)} ∫_{∂B_r(x)} u² dℋ^{n-1}` (Section 3.3). The sphere integral is the
one of `Basic/Setup.lean`. -/
def heightH (u : Rn n → ℝ) (x : Rn n) (r : ℝ) : ℝ :=
  (r ^ (n + 1))⁻¹ * sphereIntegral (fun y => u y ^ 2) x r

/-- The Weiss monotonicity formula `M_x(u; r) = D_x(u; r) − H_x(u; r)` (Section 3.3). -/
def monotonicityM (u χ : Rn n → ℝ) (x : Rn n) (r : ℝ) : ℝ :=
  energyD u χ x r - heightH u x r

/-- The frequency `N_x(u; r) = (D_x(u; r) − |B_1|) / H_x(u; r)` (Section 4).
Where `H = 0` this is `0` (Lean's division), not the paper's `−∞`. -/
def frequencyN (u χ : Rn n → ℝ) (x : Rn n) (r : ℝ) : ℝ :=
  (energyD u χ x r - unitBallVolume n) / heightH u x r

/-- The volume difference `V_x(u; r) = r^{-n} ∫_{B_r(x)} (1 − χ) / H_x(u; r)`.
The paper's printed definition (Section 4) omits `r^{-n}`, which identity (4.11) uses; see
`frequencyN_add_volumeV`. -/
def volumeV (u χ : Rn n → ℝ) (x : Rn n) (r : ℝ) : ℝ :=
  (r ^ n)⁻¹ * (∫ y in ball x r, (1 - χ y)) / heightH u x r

/-- The one-homogeneous rescaling `u_{x,r}(y) = u(x + r y) / r` (equation (3.6)). -/
def oneHomRescale (u : Rn n → ℝ) (x : Rn n) (r : ℝ) : Rn n → ℝ :=
  fun y => u (x + r • y) / r

/-- The rescaling `χ_{x,r}(y) = χ(x + r y)` accompanying `oneHomRescale` (equation (3.6)). -/
def chiRescale (χ : Rn n → ℝ) (x : Rn n) (r : ℝ) : Rn n → ℝ :=
  fun y => χ (x + r • y)

/-- `H_x(u; 0+) = lim_{r → 0+} H_x(u; r)`. This is junk where the limit does not exist. The limit
exists on `Σ^H`, where `H_x(u; ·)` is nondecreasing (Section 8.3 of the paper). -/
def heightHZero (u : Rn n → ℝ) (x : Rn n) : ℝ :=
  limUnder (𝓝[>] (0 : ℝ)) (heightH u x)

/-- The dimensional constant `α(n) = (∫_{∂B_1} y_1² dℋ^{n-1})^{-1/2}` (Section 8.2), normalized so
that `H_0(α(n)|y_1|; r) ≡ 1`. The paper uses the last coordinate `y_n`. By rotation invariance
of the surface measure the value is the same. -/
def alphaN (n : ℕ) [NeZero n] : ℝ :=
  1 / √(sphereIntegral (fun y : Rn n => y 0 ^ 2) 0 1)

/-- The one-dimensional profile `y ↦ |(y − x) · ν|` (Theorem 1.2 (iv), Lemma 8.5). -/
def absProfile (ν x : Rn n) : Rn n → ℝ :=
  fun y => |⟪y - x, ν⟫|

@[simp] theorem oneHomRescale_apply (u : Rn n → ℝ) (x : Rn n) (r : ℝ) (y : Rn n) :
    oneHomRescale u x r y = u (x + r • y) / r := rfl

@[simp] theorem chiRescale_apply (χ : Rn n → ℝ) (x : Rn n) (r : ℝ) (y : Rn n) :
    chiRescale χ x r y = χ (x + r • y) := rfl

@[simp] theorem absProfile_apply (ν x y : Rn n) : absProfile ν x y = |⟪y - x, ν⟫| := rfl

/-- Unfolding `M = D − H`. -/
theorem monotonicityM_eq (u χ : Rn n → ℝ) (x : Rn n) (r : ℝ) :
    monotonicityM u χ x r = energyD u χ x r - heightH u x r := rfl

/-- `N > 1` is equivalent to `M > |B_1|` when `H > 0`, from `N > 1 ⟺ D − |B_1| > H`. -/
theorem one_lt_frequencyN_iff {u χ : Rn n → ℝ} {x : Rn n} {r : ℝ} (hH : 0 < heightH u x r) :
    1 < frequencyN u χ x r ↔ unitBallVolume n < monotonicityM u χ x r := by
  rw [frequencyN, monotonicityM, one_lt_div hH]
  constructor <;> intro h <;> linarith

/-- The Lebesgue measure of `B_r(x)` is `r^n |B_1|` for `r > 0`. -/
theorem volume_ball_toReal (x : Rn n) {r : ℝ} (hr : 0 < r) :
    (volume (ball x r)).toReal = r ^ n * unitBallVolume n := by
  rw [Measure.addHaar_ball_of_pos volume x hr, finrank_euclideanSpace_fin,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hr.le n), unitBallVolume]

/-- Identity (4.11): `N + V = r^{-n} ∫_{B_r(x)} |∇u|² / H`. The equivalent printed
form is `r ∫_{B_r}|∇u|² / ∫_{∂B_r} u²`. This uses the factor `r^{-n}` in `V`, which the paper's
printed definition of `V` omits. It is pure
algebra plus `∫_{B_r} 1 = r^n |B_1|`. No sign condition on `H` is needed, because both sides
use the same denominator. -/
theorem frequencyN_add_volumeV {u χ : Rn n → ℝ} {x : Rn n} {r : ℝ} (hr : 0 < r)
    (hu : IntegrableOn (fun y => ‖gradient u y‖ ^ 2) (ball x r))
    (hχ : IntegrableOn χ (ball x r)) :
    frequencyN u χ x r + volumeV u χ x r =
      (r ^ n)⁻¹ * (∫ y in ball x r, ‖gradient u y‖ ^ 2) / heightH u x r := by
  have h1 : IntegrableOn (fun _ : Rn n => (1 : ℝ)) (ball x r) :=
    integrableOn_const (measure_ball_lt_top).ne
  have hsum : (∫ y in ball x r, (‖gradient u y‖ ^ 2 + χ y)) =
      (∫ y in ball x r, ‖gradient u y‖ ^ 2) + ∫ y in ball x r, χ y := integral_add hu hχ
  have hdiff : (∫ y in ball x r, (1 - χ y)) = (∫ y in ball x r, (1 : ℝ)) - ∫ y in ball x r, χ y :=
    integral_sub h1 hχ
  have hone : (∫ y in ball x r, (1 : ℝ)) = r ^ n * unitBallVolume n := by
    rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def, volume_ball_toReal x hr]
  have hrn : r ^ n ≠ 0 := pow_ne_zero n hr.ne'
  rw [frequencyN, volumeV, ← add_div, energyD, hsum, hdiff, hone]
  congr 1
  rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ hrn, one_mul]
  ring

end InnerVariational
