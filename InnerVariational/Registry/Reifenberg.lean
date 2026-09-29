/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Defs.HighestDensity
public import InnerVariational.Defs.GMT
public import GMTFoundations.Reifenberg.Discrete
public import GMTFoundations.Reifenberg.Rectifiable
public import Mathlib.Order.CompletePartialOrder
public import GMTFoundations.Defs.GMT

/-!
# Registry: Naber–Valtorta Reifenberg theorems

Classical results used by the proof, imported from the dependency gmt-foundations v0.1.0
(https://github.com/willmfeldman/gmt-foundations): the codimension-one (`k = n − 1`) cases of the
Reifenberg-type theorems of Naber–Valtorta (cited `[NV]`, arXiv:1504.02043):

* `discrete_reifenberg`: the discrete rectifiable-Reifenberg theorem [NV, Thm 3.4], used in the
  proof of Lemma 7.1 (1) of Kriventsov–Weiss;
* `rectifiable_reifenberg`: the rectifiable-Reifenberg theorem [NV, Thm 3.3], used in the proof of
  Lemma 7.1 (3) of Kriventsov–Weiss.

## Relation to the printed statements of [NV]

[NV, Def. 3.1] defines `D^k_μ(x, r) = inf_L r^{-(k+2)} ∫_{B_r(x)} d²(y, L) dμ` only when
`μ(B_r(x)) ≥ ε_n r^k`, and sets it to `0` otherwise. The hypotheses (3.7) and (3.10) are required
only on balls with `μ(B_r(x)) ≥ ε_n r^k`. [NV, Remark 3.2] allows replacing `ε_n` by any smaller
bound, zero included. With `ε_n = 0`, `D^{n-1}_μ` is our `jonesBetaSq μ` and the hypotheses are
required on *all* balls `B_r(x) ⊆ B_2`. That is what is stated below.

Further restrictions, which make the statements weaker than [NV]:
* `discrete_reifenberg` is stated for finite collections of balls. The use in Lemma 7.1 (1) bounds
  the size of arbitrary countable disjoint collections, which follows by applying it to finite
  subcollections.
* `rectifiable_reifenberg` additionally assumes `S` Borel, `ℋ^{n-1}(S) < ∞` and an upper density
  bound `ℋ^{n-1}(S ∩ B_r(x)) ≤ C r^{n-1}` (with `δ` depending on `C`), and it concludes only the
  rectifiability of `S ∩ B_1`, not the sharp measure bound of [NV]. These hypotheses hold in its use
  in the proof of Lemma 7.1 (3), where `ν = ℋ^{n-1}⌊(Σ^H ∩ B_1)` has finite mass and the density
  bound follows from the Hausdorff measure bound of Lemma 7.1 (3). They also guarantee the
  measurability of the integrand, for which the `lintegral` is the true integral.

## References

* A. Naber and D. Valtorta, *Rectifiable-Reifenberg and the regularity of stationary and minimizing
  harmonic maps*, Ann. of Math. 185 (2017), 131–227; arXiv:1504.02043.
* D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
  DOI 10.1002/cpa.22226; arXiv:2306.10131. Result numbers refer to arXiv v2.
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational.Registry

variable {n : ℕ}

open scoped Classical in
/-- **Discrete rectifiable-Reifenberg theorem** ([NV, Thm 3.4], `k = n − 1`, `ε_n = 0` by
[NV, Remark 3.2]). There are `δ(n) > 0` and `D(n)` with the following property. Let
`{B_{r_j}(x_j)}_{j ∈ J}` be a finite collection of disjoint balls contained in `B_2`, and
`μ = Σ_j ω_{n-1} r_j^{n-1} δ_{x_j}`. If for every ball `B_s(y) ⊆ B_2`
`∫_{B_s(y)} ∫_0^s β²_μ(z, t) dt/t dμ(z) < δ² s^{n-1}`,
then `Σ_{x_j ∈ B_1} r_j^{n-1} < D`. -/
theorem discrete_reifenberg (hn : 2 ≤ n) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ D : ℝ, ∀ {ι : Type} (J : Finset ι) (x : ι → Rn n) (r : ι → ℝ),
      (∀ j ∈ J, 0 < r j) → (∀ j ∈ J, ball (x j) (r j) ⊆ ball 0 2) →
      (J : Set ι).Pairwise (fun i j => Disjoint (ball (x i) (r i)) (ball (x j) (r j))) →
      (∀ (y : Rn n) (s : ℝ), 0 < s → ball y s ⊆ ball 0 2 →
        ∫⁻ z in ball y s, (∫⁻ t in Ioo 0 s,
            jonesBetaSq (∑ j ∈ J, ENNReal.ofReal (unitBallVolume (n - 1) * r j ^ (n - 1)) •
              Measure.dirac (x j)) z t / ENNReal.ofReal t)
          ∂(∑ j ∈ J, ENNReal.ofReal (unitBallVolume (n - 1) * r j ^ (n - 1)) •
              Measure.dirac (x j)) <
          ENNReal.ofReal (δ ^ 2 * s ^ (n - 1))) →
      ∑ j ∈ J with x j ∈ ball 0 1, r j ^ (n - 1) < D := by
  -- proved in gmt-foundations v0.1.0
  exact GMTFoundations.discrete_reifenberg hn

/-- **Rectifiable-Reifenberg theorem** ([NV, Thm 3.3], `k = n − 1`, `ε_n = 0` by [NV, Remark 3.2]),
rectifiability part only, under an upper density bound. For every `C` there is `δ(n, C) > 0` with
the following property. Let `S ⊆ B_2` be Borel with `ℋ^{n-1}(S) < ∞` and
`ℋ^{n-1}(S ∩ B_r(x)) ≤ C r^{n-1}` for every ball, and assume that for every ball `B_s(y) ⊆ B_2`
`∫_{S ∩ B_s(y)} ∫_0^s β²_{ℋ^{n-1}⌊S}(z, t) dt/t dℋ^{n-1}(z) < δ² s^{n-1}`.
Then `S ∩ B_1` is countably `ℋ^{n-1}`-rectifiable.

Compared with [NV, Thm 3.3], the density bound hypothesis is added (`δ` may depend on `C`), and
the sharp conclusion `ℋ^{n-1}(S ∩ B_r(x)) ≤ (1 + ε) ω_{n-1} r^{n-1}` is dropped. Its use, in the
proof of Lemma 7.1 (3) of Kriventsov–Weiss (`NaberValtorta/Rectifiable.lean`), needs only
rectifiability and has the density bound from the first part of Lemma 7.1 (3). This allows a
big-pieces-of-Lipschitz-graphs proof instead of the argument of [NV, §5]. -/
theorem rectifiable_reifenberg (hn : 2 ≤ n) (C : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ S : Set (Rn n), MeasurableSet S → S ⊆ ball 0 2 →
      hausdorffN n (n - 1) S < ∞ →
      (∀ (x : Rn n) (r : ℝ), 0 < r →
        hausdorffN n (n - 1) (S ∩ ball x r) ≤ ENNReal.ofReal (C * r ^ (n - 1))) →
      (∀ (y : Rn n) (s : ℝ), 0 < s → ball y s ⊆ ball 0 2 →
        ∫⁻ z in S ∩ ball y s, (∫⁻ t in Ioo 0 s,
            jonesBetaSq ((hausdorffN n (n - 1)).restrict S) z t / ENNReal.ofReal t)
          ∂hausdorffN n (n - 1) < ENNReal.ofReal (δ ^ 2 * s ^ (n - 1))) →
      IsCountablyRectifiable n (n - 1) (S ∩ ball 0 1) := by
  -- proved in gmt-foundations v0.1.0
  exact GMTFoundations.rectifiable_reifenberg hn C

end InnerVariational.Registry
