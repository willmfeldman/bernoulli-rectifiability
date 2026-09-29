/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.NaberValtorta.Discrete
public import GMTFoundations.Defs.GMT

/-!
# Abstract data for the Naber–Valtorta argument

Section 7 of D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and
compactness for non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025),
no. 3, DOI 10.1002/cpa.22226; arXiv:2306.10131 (numbering of arXiv v2), uses a variational
solution only through a few properties of its frequency `N_y(u; r)` on the set `Σ^H_t`. This file
isolates them.

* `maxFrequency S N x r = sup {N_y(20 r) : y ∈ S ∩ B̄_r(x)}`, the paper's `N^max_t(x, r)`
  (defined at the start of §7, where the bound variable `x` shadows the centre `x`; here it is
  `y`).
* `JonesData n CJ`: a set `S`, a family of "frequencies" `N z : ℝ → ℝ`, and scales `t ≤ R` such
  that on `S` each `N z` is nondecreasing and `≥ 1` on `(t, 20 R]`, and the Jones numbers of every
  finite measure carried by `S` are controlled by frequency drops (Theorem 6.1, with
  constant `CJ`).
* `NVData n CJ Nplus ε`: a `JonesData` which also satisfies `N ≤ Nplus` and the frequency-drop
  dichotomy of Theorem 6.3 on the balls contained in a set `K`.

Lemma 7.1 is proved for `JonesData` (`NaberValtorta/VolumeEstimate.lean`) and the covering
argument of Theorem 7.2 for `NVData`. The constants `CJ`, `Nplus` and the function `ε` are
parameters of the structures, so every constant produced by those proofs depends only on
`(n, CJ, Nplus, ε)`.

## Encoding

* `Σ` is a reserved token in Lean, so the set is called `S`.
* The scales are absolute. The paper rescales every ball to `B_1`. Here scale invariance is
  encoded by requiring the hypotheses at every point of `S` and every scale in `[t, R]`. Only the
  Reifenberg theorems (`NaberValtorta/Reifenberg.lean`) are applied to rescaled balls.
* For a variational solution (`NaberValtorta/Instance.lean`), `S = Σ^H_t ∩ K`,
  `N = frequencyN u χ` on `S`, `CJ` is the constant of Theorem 6.1 for the bound `Nplus` given by
  Lemma 4.6, and `ε` is the function `δ ↦ ε(δ)` of Theorem 6.3.
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational.NaberValtorta

variable {n : ℕ}

/-- `N^max(x, r) = sup {N_y(20 r) : y ∈ S ∩ B̄_r(x)}` (the paper's `N^max_t(x, r)` of §7, with the
bound variable renamed to `y`).
It is `0` (the junk value of `sSup`) when the set is empty or unbounded above. -/
def maxFrequency (S : Set (Rn n)) (N : Rn n → ℝ → ℝ) (x : Rn n) (r : ℝ) : ℝ :=
  sSup ((fun y => N y (20 * r)) '' (S ∩ closedBall x r))

/-- Abstract hypotheses of Lemma 7.1.

* `N z` is nondecreasing and `≥ 1` on `(t, 20 R]` for `z ∈ S` (Lemma 4.1).
* `jones`: Theorem 6.1 in the form used in the proof of Lemma 7.1. For every finite measure `μ`
  carried by `S`, every `y ∈ S` and every `ρ ∈ [t, R]`, `ρ > 0`,
  `β²_μ(y, ρ) ≤ CJ ρ^{1-n} ∫_{B_ρ(y)} (N_z(20ρ) − N_z(ρ)) dμ(z)`. -/
structure JonesData (n : ℕ) (CJ : ℝ) where
  /-- The set, `Σ^H_t` in the paper. -/
  S : Set (Rn n)
  /-- The frequency, `N z r = N_z(u; r)` in the paper. -/
  N : Rn n → ℝ → ℝ
  /-- The smallest scale `t`. -/
  t : ℝ
  /-- The largest scale at which the Jones estimate holds. -/
  R : ℝ
  t_nonneg : 0 ≤ t
  R_pos : 0 < R
  measurableSet_S : MeasurableSet S
  measurable_N : ∀ r, 0 < r → r ≤ 20 * R → Measurable fun z => N z r
  monotoneOn : ∀ z ∈ S, MonotoneOn (N z) (Ioc t (20 * R))
  one_le : ∀ z ∈ S, ∀ r ∈ Ioc t (20 * R), 1 ≤ N z r
  jones : ∀ μ : Measure (Rn n), IsFiniteMeasure μ → μ Sᶜ = 0 →
    ∀ y ∈ S, ∀ ρ, 0 < ρ → t ≤ ρ → ρ ≤ R →
      jonesBetaSq μ y ρ ≤ ENNReal.ofReal (CJ / ρ ^ (n - 1)) *
        ∫⁻ z in ball y ρ, ENNReal.ofReal (N z (20 * ρ) - N z ρ) ∂μ

/-- Abstract hypotheses of Theorem 7.2: a `JonesData` with `N ≤ Nplus` on `S`, and the
dichotomy of Theorem 6.3 on every ball `B̄_r(x) ⊆ K` with `r ∈ [t, R]`: either
`N^max(x, r) < 1 + δ`, or the points `y ∈ S ∩ B̄_r(x)` with small frequency drop
`N^max(x, r) − N_y(r) < ε(δ)` lie within `δ r` of an affine subspace of dimension `≤ n − 2`. -/
structure NVData (n : ℕ) (CJ Nplus : ℝ) (ε : ℝ → ℝ) extends JonesData n CJ where
  /-- The region in which the dichotomy holds. -/
  K : Set (Rn n)
  le_Nplus : ∀ z ∈ S, ∀ r ∈ Ioc t (20 * R), N z r ≤ Nplus
  dichotomy : ∀ δ, 0 < δ → ∀ (x : Rn n) (r : ℝ), 0 < r → t ≤ r → r ≤ R → closedBall x r ⊆ K →
    (S ∩ closedBall x r).Nonempty →
    maxFrequency S N x r < 1 + δ ∨
      ∃ L : AffineSubspace ℝ (Rn n), Module.finrank ℝ L.direction ≤ n - 2 ∧
        {y | y ∈ S ∩ closedBall x r ∧ maxFrequency S N x r - N y r < ε δ} ⊆
          thickening (δ * r) (L : Set (Rn n))

namespace JonesData

variable {CJ : ℝ} (J : JonesData n CJ)

/-- The frequency drop `N_z(b) − N_z(a)` is nonnegative for `t < a ≤ b ≤ 20 R`. -/
theorem sub_nonneg_of_le {z : Rn n} (hz : z ∈ J.S) {a b : ℝ} (ha : J.t < a) (hab : a ≤ b)
    (hb : b ≤ 20 * J.R) : 0 ≤ J.N z b - J.N z a :=
  sub_nonneg.2 (J.monotoneOn z hz ⟨ha, hab.trans hb⟩ ⟨ha.trans_le hab, hb⟩ hab)

end JonesData

end InnerVariational.NaberValtorta
