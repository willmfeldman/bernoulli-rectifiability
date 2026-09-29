/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Defs.HighestDensity
public import InnerVariational.Monotonicity.Radial
public import InnerVariational.Frequency.Concrete
public import InnerVariational.Estimates.Dichotomy
public import InnerVariational.Estimates.L2Subspace
public import InnerVariational.Defs.VariationalSolution
public import GMTFoundations.Defs.GMT

/-!
# Inputs from Sections 3, 4 and 6 for the instantiation of Theorem 7.2

Instantiating the abstract Naber–Valtorta data (`NaberValtorta/Data.lean`) for a variational
solution (`NaberValtorta/Instance.lean`) uses the following results of D. Kriventsov and
G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for non-minimizing
Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3, DOI 10.1002/cpa.22226;
arXiv:2306.10131 (numbering of arXiv v2). This file restates them in the form used there; each is
a one-line application of the library result that proves it.

* Proposition 3.4, monotonicity of `M` (`Monotonicity/Radial.lean`).
* Lemma 4.1 (monotonicity of `N` and `N ≥ 1`) and the frequency part of Lemma 4.6 (change of
  point) (`Frequency/Concrete.lean`).
* Theorem 6.1 (`L²`-subspace approximation), proved by `InnerVariational.jonesBetaSq_le`
  (`Estimates/L2Subspace.lean`).
* Theorem 6.3 (frequency drop dichotomy), proved by `InnerVariational.frequency_drop_dichotomy`
  (`Estimates/Dichotomy.lean`), which has literally the same statement.

The names live in the namespace `InnerVariational.NaberValtorta.Inputs`, so that they do not
clash with the names of the library results.

## Faithfulness

Every statement here is at most as strong as the corresponding statement of the paper.

* `B_r(x) ⊂⊂ Ω` is encoded as `closedBall x r ⊆ Ω` whenever a quantity at radius `r` is used:
  the quantities at radius `r` read `u` on `∂B_r(x)`, which a solution on the open ball `B_r(x)`
  does not constrain.
* Lemma 4.1 is stated on the half-open interval `(t, R]` with `B̄_R(x) ⊆ Ω`. Since `Ω` is open,
  `B_{R'}(x) ⊆ Ω` for some `R' > R`, and the paper gives the conclusion on `(t, R') ⊇ (t, R]`.
* Lemma 4.6 claims `N_y(s) ≤ max{1, C N_x(r)}` with `C = C(n)`. Here the bound is some
  `K = K(n, N₊)`, which is what the paper's proof gives (see `frequencyN_change_of_point`).
* In Theorem 6.1 the solution is assumed on `B_{50r}(x)` (the paper writes `B_{8r}(x)`). In
  Theorem 6.3, the maximum `N^max` is a supremum, whose attainment is never used.
-/

open MeasureTheory Metric Set
open scoped NNReal ENNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational.NaberValtorta.Inputs

variable {n : ℕ}

/-- **Proposition 3.4**. `s ↦ M_x(u; s)` is nondecreasing:
`M_x(s) ≤ M_x(t)` for `0 < s ≤ t` and `B̄_t(x) ⊆ Ω`. -/
theorem monotonicityM_le [NeZero n] {Ω : Set (Rn n)} {C : ℝ≥0} {u χ : Rn n → ℝ}
    (h : IsVariationalSolution Ω C u χ) {x : Rn n} {s t : ℝ} (hs : 0 < s) (hst : s ≤ t)
    (ht : closedBall x t ⊆ Ω) : monotonicityM u χ x s ≤ monotonicityM u χ x t :=
  h.monotonicityM_le hs hst ht

/-- **Lemma 4.1**. If `x ∈ closure {u > 0}`,
`M_x(u; t) ≥ |B_1|` and `B̄_R(x) ⊆ Ω` with `0 < t`, then `s ↦ N_x(u; s)` is nondecreasing on
`(t, R]` and `N_x(u; s) ≥ 1` there. -/
theorem frequencyN_monotoneOn [NeZero n] {Ω : Set (Rn n)} {C : ℝ≥0} {u χ : Rn n → ℝ}
    (h : IsVariationalSolution Ω C u χ) {x : Rn n} (hx : x ∈ closure {y | 0 < u y}) {t R : ℝ}
    (ht : 0 < t) (hM : unitBallVolume n ≤ monotonicityM u χ x t) (hΩ : closedBall x R ⊆ Ω) :
    MonotoneOn (frequencyN u χ x) (Ioc t R) ∧ ∀ s ∈ Ioc t R, 1 ≤ frequencyN u χ x s :=
  h.monotoneOn_frequencyN_Ioc hx ht hM hΩ

/-- **Lemma 4.6**, the bound on `N`. If
`x ∈ closure {u > 0}`, `M_x(u; r/4) ≥ |B_1|`, `N_x(u; r) ≤ N₊` and `B̄_r(x) ⊆ Ω`, then
`N_y(u; s) ≤ K` for every `y ∈ B_{r/4}(x)` and `0 < s < r/2`, with `K = K(n, N₊)`.

The paper states `N_y(s) ≤ max{1, C N_x(r)}` with `C = C(n)`. The step
`D_y(5/8) ≤ (8/5)ⁿ D_0(1)` in its proof leaves a term of order `|B_1| / H_y` that `N_0` does
not control; we prove the bound with `K = K(n, N₊)` via (4.11), (4.12) and Lemma 4.3, which is
what the later applications use. -/
theorem frequencyN_change_of_point (n : ℕ) [NeZero n] (Np : ℝ) :
    ∃ K : ℝ, ∀ (Ω : Set (Rn n)) (C : ℝ≥0) (u χ : Rn n → ℝ) (x : Rn n) (r : ℝ),
      IsVariationalSolution Ω C u χ → 0 < r → closedBall x r ⊆ Ω →
      x ∈ closure {y | 0 < u y} → unitBallVolume n ≤ monotonicityM u χ x (r / 4) →
      frequencyN u χ x r ≤ Np → ∀ y ∈ ball x (r / 4), ∀ s, 0 < s → s < r / 2 →
        frequencyN u χ y s ≤ K :=
  InnerVariational.frequencyN_change_of_point n Np

/-- **Theorem 6.1** (`InnerVariational.jonesBetaSq_le`), with the solution on `B̄_{50r}(x)`
(the paper writes `B_{8r}(x)`). There is `C = C(N₊, n)` such that for every finite measure
`μ` carried by `Σ^H_r`, every `x ∈ Σ^H_r` with `N_x(u; 50r) ≤ N₊`,
`β²_μ(x, r) ≤ C r^{1-n} ∫_{B_r(x)} (N_y(u; 20r) − N_y(u; r)) dμ(y)`. -/
theorem jonesBetaSq_le (n : ℕ) [NeZero n] (Np : ℝ) :
    ∃ CJ : ℝ, ∀ (Ω : Set (Rn n)) (C : ℝ≥0) (u χ : Rn n → ℝ) (x : Rn n) (r : ℝ)
      (μ : Measure (Rn n)), IsVariationalSolution Ω C u χ → 0 < r →
      closedBall x (50 * r) ⊆ Ω → IsFiniteMeasure μ → μ (sigmaHr Ω u χ r)ᶜ = 0 →
      x ∈ sigmaHr Ω u χ r → frequencyN u χ x (50 * r) ≤ Np →
      jonesBetaSq μ x r ≤ ENNReal.ofReal (CJ / r ^ (n - 1)) *
        ∫⁻ y in ball x r, ENNReal.ofReal (frequencyN u χ y (20 * r) - frequencyN u χ y r) ∂μ := by
  exact InnerVariational.jonesBetaSq_le n Np

/-- **Theorem 6.3** (`InnerVariational.frequency_drop_dichotomy`), with the maximum `N^max`
replaced by a supremum (its attainment is never used). For `δ > 0` there is
`ε = ε(N₊, δ, n) ∈ (0, 1)` such that, with `N^max = sup {N_y(20r) : y ∈ B̄_r(x) ∩ Σ^H_t} ≤ N₊`,
either `N^max < 1 + δ`, or `{y ∈ B̄_r(x) ∩ Σ^H_t : N^max − N_y(r) < ε}` lies in the
`δ r`-neighbourhood of an affine subspace of dimension `≤ n − 2`. -/
theorem frequency_drop_dichotomy (n : ℕ) [NeZero n] (hn : 2 ≤ n) (Np δ : ℝ) (hδ : 0 < δ) :
    ∃ ε ∈ Ioo (0 : ℝ) 1, ∀ (Ω : Set (Rn n)) (C_V : ℝ≥0) (u χ : Rn n → ℝ) (x : Rn n) (r t : ℝ),
      IsVariationalSolution Ω C_V u χ → 0 < r → ball x (50 * r) ⊆ Ω → t ∈ Icc 0 r →
      (closedBall x r ∩ sigmaHr Ω u χ t).Nonempty →
      let Nmax := sSup ((fun y => frequencyN u χ y (20 * r)) '' (closedBall x r ∩ sigmaHr Ω u χ t))
      Nmax ≤ Np → Nmax < 1 + δ ∨ ∃ L : AffineSubspace ℝ (Rn n),
        Module.finrank ℝ L.direction ≤ n - 2 ∧
        {y ∈ closedBall x r ∩ sigmaHr Ω u χ t | Nmax - frequencyN u χ y r < ε} ⊆
          thickening (δ * r) (L : Set (Rn n)) := by
  exact InnerVariational.frequency_drop_dichotomy n hn Np δ hδ

end InnerVariational.NaberValtorta.Inputs
