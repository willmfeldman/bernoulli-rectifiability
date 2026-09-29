/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Registry.GMT
public import GMTFoundations.Defs.GMT

/-!
# Federer's criterion: an `ℋ^{n-1}`-null essential boundary forces a trivial set

A Federer-type criterion: if the essential boundary `∂ᵉE` of a measurable set `E ⊆ ℝⁿ` is
`ℋ^{n-1}`-null in a ball, then `E` is trivial (a.e. empty or a.e. full) in that ball. It is
proved in gmt-foundations (https://github.com/willmfeldman/gmt-foundations, v0.1.0) and
restated here as `Registry.ae_trivial_of_hausdorffN_essentialBoundary_inter_ball`; this file
gives it the name used in the identification of `χ`. The classical argument, from
H. Federer, *Geometric Measure Theory*, Springer, 1969:

* 4.5.11: if `ℋ^{n-1}(K ∩ ∂ᵉE) < ∞` for every compact `K ⊆ U`, then `E` has locally finite
  perimeter in `U`;
* 4.5.6 (1): `|Dχ_E|⌊U = ℋ^{n-1}⌊(∂ᵉE ∩ U)`, which vanishes here;
* 4.5.3: a `BV` function with vanishing derivative on a ball is a.e. constant.

The special case `∂ᵉE ∩ B = ∅` is `Registry.ae_trivial_of_essentialBoundary_inter_ball`.

## Use

Theorem 8.6 of D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and
compactness for non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025),
no. 3, DOI 10.1002/cpa.22226; arXiv:2306.10131 (numbering of arXiv v2), identifies `χ`. Its
proof argues through the perimeter of a "pathological" component `U` of `{u = 0}°`:
`ℋ^{n-1}(∂U ∩ Ω)` is locally finite by Theorem 7.2, so `U` has locally finite perimeter (this
step is itself Federer 4.5.11), and the relative isoperimetric inequality gives
`ℋ^{n-1}(∂*U ∩ Ω') > 0`. With the criterion above the perimeter is not needed: `∂ᵉU ∩ Ω` is
`ℋ^{n-1}`-null by Lemma 8.5 (2), so `U` is trivial in every ball.
-/

open MeasureTheory Metric Set

@[expose] public noncomputable section

namespace InnerVariational.Singular.FedererCriterion

variable {n : ℕ}

/-- **Federer's criterion for trivial sets.** If the essential boundary of a measurable set `E`
is `ℋ^{n-1}`-null in a ball, then `E` is Lebesgue-a.e. empty or a.e. full in that ball.
Federer 4.5.11 (locally finite perimeter from `ℋ^{n-1}`-finiteness of `∂ᵉE`), 4.5.6 (1)
(`|Dχ_E| = ℋ^{n-1}⌊∂ᵉE = 0`), 4.5.3 (constancy). It generalizes
`Registry.ae_trivial_of_essentialBoundary_inter_ball`, which is the case
`∂ᵉE ∩ B_r(c) = ∅`. -/
theorem ae_trivial_of_hausdorffN_essentialBoundary_inter_ball (hn : 2 ≤ n) {E : Set (Rn n)}
    (hE : MeasurableSet E) {c : Rn n} {r : ℝ}
    (h : hausdorffN n (n - 1) (essentialBoundary E ∩ ball c r) = 0) :
    volume (E ∩ ball c r) = 0 ∨ volume (ball c r \ E) = 0 :=
  Registry.ae_trivial_of_hausdorffN_essentialBoundary_inter_ball hn hE h

end InnerVariational.Singular.FedererCriterion
