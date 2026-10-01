/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Defs.Calculus
public import GMTFoundations.Defs.GMT
public import GMTFoundations.GMT.ApproxTangent

/-!
# Geometric measure theory vocabulary

Elementary encodings of the GMT notions used by Kriventsov–Weiss (full references below):

* `IsCountablyRectifiable n k S`: `S` is countably `ℋ^k`-rectifiable (Federer 3.2.14). Up to an
  `ℋ^k`-null set, `S` is covered by countably many Lipschitz images of `ℝ^k`.
* `IsGaussGreenPair Ω E μ ν`: `μ` is a Radon measure on `Ω` and `ν` a `μ`-a.e. unit vector field
  with `∫_E div φ = ∫ φ · ν dμ` for all `φ ∈ C^∞_c(Ω; ℝⁿ)`. By De Giorgi's structure theory
  `μ = |Dχ_E|⌊Ω` and `ν` is the measure-theoretic outer normal.
* `HasLocallyFinitePerimeter Ω E`: a Gauss–Green pair exists.
* `reducedBoundary Ω E = ∂*E ∩ Ω` (De Giorgi; Maggi, Def. 15.1).
* `HasDensity E x d`, `lebesgueDensity E x`: Lebesgue density of `E` at `x`.
* `essentialBoundary E = ∂ᵉE` (Federer's measure-theoretic boundary `∂_M E`, 4.5.11).

## Remarks on faithfulness

* Lipschitz images of all of `ℝ^k` rather than of bounded subsets: each Lipschitz map on a subset
  of `ℝ^k` extends to a Lipschitz map on `ℝ^k` (McShane, componentwise), so the notions agree.
* The Gauss–Green pair is unique when it exists. The distribution `Dχ_E` determines the vector
  measure `ν μ` on `Ω`, and then `μ = |ν μ|` because `‖ν‖ = 1` `μ`-a.e. So `reducedBoundary` does
  not depend on which pair witnesses it.
* `essentialBoundary`: Federer's `∂_M E` is the set of points where both `E` and `ℝⁿ \ E` have
  positive upper density. For measurable `E` the density ratios lie in `[0, 1]` and add up to one.
  So "upper density of `E` is `0`" is `HasDensity E x 0`, and "upper density of the complement is
  `0`" is `HasDensity E x 1`. Hence `x ∉ ∂_M E ⟺ HasDensity E x 0 ∨ HasDensity E x 1`.

Apart from `lebesgueDensity`, these notions are defined in the dependency gmt-foundations v0.1.0
(https://github.com/willmfeldman/gmt-foundations) and re-exported here.

## References

* D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
  DOI 10.1002/cpa.22226; arXiv:2306.10131.
* H. Federer, *Geometric Measure Theory*, Grundlehren der mathematischen Wissenschaften 153,
  Springer, 1969.
* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Cambridge Studies in
  Advanced Mathematics 135, Cambridge University Press, 2012.
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

/-! `IsCountablyRectifiable`, `IsGaussGreenPair`, `HasLocallyFinitePerimeter`, `reducedBoundary`,
`HasDensity` and `essentialBoundary` are GMT-foundations' (`GMTFoundations/Defs/GMT.lean`),
re-exported. `IsGaussGreenPair` is a structure, so a local copy would be a different type, and
the GMT-foundations theorems would not apply to it. -/
export GMTFoundations (IsCountablyRectifiable IsGaussGreenPair HasLocallyFinitePerimeter
  reducedBoundary HasDensity essentialBoundary)

/-- The Lebesgue density of `E` at `x`. It is junk where the limit does not exist. -/
def lebesgueDensity (E : Set (Rn n)) (x : Rn n) : ℝ :=
  limUnder (𝓝[>] (0 : ℝ)) fun r => (volume (E ∩ ball x r)).toReal / (volume (ball x r)).toReal

theorem reducedBoundary_subset (Ω E : Set (Rn n)) : reducedBoundary Ω E ⊆ Ω :=
  fun _ hx => hx.1

theorem HasDensity.lebesgueDensity_eq {E : Set (Rn n)} {x : Rn n} {d : ℝ} (h : HasDensity E x d) :
    lebesgueDensity E x = d :=
  h.limUnder_eq

/-- For dot notation on `GMTFoundations.HasDensity` (see `Defs/Calculus.lean`). -/
alias _root_.GMTFoundations.HasDensity.lebesgueDensity_eq := HasDensity.lebesgueDensity_eq

/-- Countable rectifiability passes to subsets. Dot notation `h.mono` finds GMT-foundations'
`GMTFoundations.IsCountablyRectifiable.mono` (`GMT/ApproxTangent.lean`, imported above for it). -/
theorem IsCountablyRectifiable.mono {k : ℕ} {S T : Set (Rn n)} (h : IsCountablyRectifiable n k T)
    (hST : S ⊆ T) : IsCountablyRectifiable n k S := by
  obtain ⟨f, hf, hnull⟩ := h
  exact ⟨f, hf, measure_mono_null (sdiff_subset_sdiff_left hST) hnull⟩

end InnerVariational
