/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Defs.GMT
public import GMTFoundations.GMT.HausdorffLebesgue
public import GMTFoundations.GMT.SphereMeasure
public import GMTFoundations.GMT.Density
public import GMTFoundations.GMT.ApproxTangent
public import GMTFoundations.Perimeter.GaussGreenPair
public import GMTFoundations.Perimeter.Local
public import GMTFoundations.Perimeter.BlowUp
public import GMTFoundations.Perimeter.Structure
public import GMTFoundations.Perimeter.Criterion
public import GMTFoundations.Defs.GMT

/-!
# Registry: geometric measure theory

Classical results from geometric measure theory used by the proof, stated in the elementary
encodings of `Defs/GMT.lean`. Every entry is imported from the dependency gmt-foundations v0.1.0
(https://github.com/willmfeldman/gmt-foundations); each proof here is a one-line `exact`.

* `map_sphereMeasure_eq_hausdorffN`: `sphereMeasure` is normalized `ℋ^{n-1}` on the unit sphere
  (Federer 3.2.46; Mattila, Thm 3.4).
* `hausdorffN_self_eq_volume`, `map_volume_affineIsometry_eq_hausdorffN`: normalized `ℋ^d` on
  `ℝ^d` is Lebesgue measure, and hence so on affine hyperplanes (Federer 2.10.35, via the
  isodiametric inequality, Evans–Gariepy, Thm 2.2).
* `ae_trivial_of_hausdorffN_essentialBoundary_inter_ball`,
  `ae_trivial_of_essentialBoundary_inter_ball`, `IsGaussGreenPair.eq_hausdorffN_restrict`:
  Federer's structure results for sets of locally finite perimeter (Federer 4.5.11, 4.5.6, 4.5.3;
  Evans–Gariepy, §§5.8 and 5.11).
* `HasLocallyFinitePerimeter.rectifiable_essentialBoundary`, `hasDensity_symmDiff_halfSpace`:
  De Giorgi–Federer rectifiability of the essential boundary, and De Giorgi's blow-up to a
  half-space at reduced-boundary points (Federer 4.5.6; Maggi, Thms 15.5, 15.9 and 16.2;
  Evans–Gariepy, §5.7).
* `eq_withDensity_upperDensity`: the density theorem plus Radon–Nikodym for measures dominated by
  `ℋ^{n-1}⌊S` on a rectifiable set `S` (Federer 2.10.19, 3.2.19).
* `hausdorffN_not_approxTangent_eq_zero`: approximate tangent planes of rectifiable sets
  (Mattila, Thm 15.19).
* `exists_isGaussGreenPair_of_integral_divergence_le`, `hasLocallyFinitePerimeter_of_local`: the
  BV structure theorem (Riesz representation of `Dχ_E`), globally and in the `BV_loc` form
  (Evans–Gariepy, Thm 5.1).

Hypotheses are sometimes *stronger* than the textbook ones (e.g. `2 ≤ n`, `MeasurableSet E`,
finiteness assumptions), so the statements here are special cases of the cited results.

## References

* D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
  DOI 10.1002/cpa.22226; arXiv:2306.10131. Result numbers refer to arXiv v2.
* H. Federer, *Geometric Measure Theory*, Springer, 1969.
* L. C. Evans and R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, rev. ed.,
  CRC Press, 2015.
* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Cambridge Univ. Press,
  2012.
* P. Mattila, *Geometry of Sets and Measures in Euclidean Spaces*, Cambridge Univ. Press, 1995.
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational.Registry

variable {n : ℕ}

/-- **Surface measure is Hausdorff measure.** The surface measure
`sphereMeasure n = volume.toSphere` on `S^{n-1}` is the normalized Hausdorff measure
`ℋ^{n-1}⌊S^{n-1}`. Federer 3.2.46 (area of the sphere), together with the uniqueness of
rotation-invariant measures on `S^{n-1}` (Mattila, Thm 3.4). This identifies the sphere integrals
of this library with the paper's `∫_{∂B_r} … dℋ^{n-1}`. Proved in gmt-foundations. -/
theorem map_sphereMeasure_eq_hausdorffN [NeZero n] :
    (sphereMeasure n).map (Subtype.val) =
      (hausdorffN n (n - 1)).restrict (sphere (0 : Rn n) 1) := by
  exact GMTFoundations.GMT.map_sphereMeasure_eq_hausdorffN

/-- **Hausdorff measure is Lebesgue measure.** On `ℝ^d` the normalized Hausdorff measure `ℋ^d`
is Lebesgue measure. Federer 2.10.35, via the isodiametric inequality (Evans–Gariepy, Thm 2.2).
Proved in gmt-foundations. -/
theorem hausdorffN_self_eq_volume (d : ℕ) : hausdorffN d d = (volume : Measure (Rn d)) := by
  exact GMTFoundations.GMT.hausdorffN_self_eq_volume d

/-- **Hausdorff measure on hyperplanes.** On an affine hyperplane `p + L(ℝ^{n-1})`, where `L` is a
linear isometric embedding, `ℋ^{n-1}` is the image of `(n-1)`-dimensional Lebesgue measure. It
follows from `hausdorffN_self_eq_volume` and the isometry invariance of `μH`. Proved in
gmt-foundations. -/
theorem map_volume_affineIsometry_eq_hausdorffN (L : Rn (n - 1) →ₗᵢ[ℝ] Rn n) (p : Rn n) :
    (volume : Measure (Rn (n - 1))).map (fun y => p + L y) =
      (hausdorffN n (n - 1)).restrict (range fun y => p + L y) := by
  exact GMTFoundations.GMT.map_volume_affineIsometry_eq_hausdorffN L p

/-- **Sets with null essential boundary are trivial.** If the essential boundary of a measurable set
`E` is `ℋ^{n-1}`-null in a ball, then `E` is Lebesgue-a.e. empty or a.e. full in that ball. Federer
4.5.11 (an `ℋ^{n-1}`-finite essential boundary gives locally finite perimeter), 4.5.6 (1)
(`|Dχ_E| = ℋ^{n-1}⌊∂ᵉE = 0`), and 4.5.3 (constancy / relative isoperimetric inequality). Proved in
gmt-foundations. -/
theorem ae_trivial_of_hausdorffN_essentialBoundary_inter_ball (hn : 2 ≤ n) {E : Set (Rn n)}
    (hE : MeasurableSet E) {c : Rn n} {r : ℝ}
    (h : hausdorffN n (n - 1) (essentialBoundary E ∩ ball c r) = 0) :
    volume (E ∩ ball c r) = 0 ∨ volume (ball c r \ E) = 0 := by
  -- proved in gmt-foundations v0.1.0
  exact GMTFoundations.ae_trivial_of_hausdorffN_essentialBoundary_inter_ball hn hE h

/-- **Sets with empty essential boundary are trivial.** If the essential boundary of a
measurable set `E` does not meet a ball, then `E` is Lebesgue-a.e. empty or a.e. full in that ball
(the argument at the end of the proof of Lemma 8.1 of the paper). The case `∂ᵉE ∩ B = ∅` of
`ae_trivial_of_hausdorffN_essentialBoundary_inter_ball`. -/
theorem ae_trivial_of_essentialBoundary_inter_ball (hn : 2 ≤ n) {E : Set (Rn n)}
    (hE : MeasurableSet E) {c : Rn n} {r : ℝ} (h : essentialBoundary E ∩ ball c r = ∅) :
    volume (E ∩ ball c r) = 0 ∨ volume (ball c r \ E) = 0 :=
  ae_trivial_of_hausdorffN_essentialBoundary_inter_ball hn hE (by rw [h, measure_empty])

/-- **Perimeter measure is `ℋ^{n-1}` on the essential boundary.** The Gauss–Green measure of a set
of locally finite perimeter is `ℋ^{n-1}` restricted to the essential boundary:
`|Dχ_E|⌊Ω = ℋ^{n-1}⌊(∂ᵉE ∩ Ω)`. Federer 4.5.6 (1); Evans–Gariepy, §§5.8 and 5.11. -/
theorem IsGaussGreenPair.eq_hausdorffN_restrict (hn : 2 ≤ n) {Ω E : Set (Rn n)}
    {μ : Measure (Rn n)} {ν : Rn n → Rn n} (hΩ : IsOpen Ω) (hE : MeasurableSet E)
    (h : IsGaussGreenPair Ω E μ ν) :
    μ = (hausdorffN n (n - 1)).restrict (Ω ∩ essentialBoundary E) := by
  -- proved in gmt-foundations v0.1.0
  exact GMTFoundations.IsGaussGreenPair.eq_hausdorffN_restrict hn hΩ hE h

/-- **De Giorgi–Federer structure theorem.** For a measurable set of locally finite perimeter in
`Ω`: the essential boundary in `Ω` is countably `ℋ^{n-1}`-rectifiable, it differs from the reduced
boundary by an `ℋ^{n-1}`-null set, and the reduced boundary is contained in it (points of `∂*E`
have density `1/2`). Federer 4.5.6; Maggi, Thms 15.5, 15.9 and 16.2. -/
theorem HasLocallyFinitePerimeter.rectifiable_essentialBoundary (hn : 2 ≤ n)
    {Ω E : Set (Rn n)} (hΩ : IsOpen Ω) (hE : MeasurableSet E)
    (h : HasLocallyFinitePerimeter Ω E) :
    IsCountablyRectifiable n (n - 1) (Ω ∩ essentialBoundary E) ∧
      hausdorffN n (n - 1) ((Ω ∩ essentialBoundary E) \ reducedBoundary Ω E) = 0 ∧
      reducedBoundary Ω E ⊆ essentialBoundary E := by
  -- proved in gmt-foundations v0.1.0
  exact GMTFoundations.HasLocallyFinitePerimeter.rectifiable_essentialBoundary hn hΩ hE h

/-- **De Giorgi's blow-up theorem at reduced-boundary points.** Let `(μ, ν)` be a
Gauss–Green pair for `E` in `Ω` and let `x ∈ Ω` be a point of `supp μ` at which the averages of
the outer normal `ν` converge to a unit vector `v` (so `x ∈ ∂*E`). Then the blow-ups `(E − x)/r`
converge in `L¹_loc` to the half-space `{⟪z, v⟫ < 0}`: `E △ {y : ⟪y − x, v⟫ < 0}` has density `0`
at `x`. Evans–Gariepy, §5.7; Maggi, Thm 15.5. The hypothesis `2 ≤ n` is extra. -/
theorem hasDensity_symmDiff_halfSpace (hn : 2 ≤ n) {Ω E : Set (Rn n)} (hΩ : IsOpen Ω)
    (hE : MeasurableSet E) {μ : Measure (Rn n)} {ν : Rn n → Rn n} (h : IsGaussGreenPair Ω E μ ν)
    {x : Rn n} (hx : x ∈ Ω) (hpos : ∀ r, 0 < r → 0 < μ (ball x r)) {v : Rn n} (hv : ‖v‖ = 1)
    (hlim : Tendsto (fun r => (μ (ball x r)).toReal⁻¹ • ∫ y in ball x r, ν y ∂μ) (𝓝[>] 0)
      (𝓝 v)) :
    HasDensity (symmDiff E {y | ⟪y - x, v⟫ < 0}) x 0 := by
  -- proved in gmt-foundations v0.1.0
  exact GMTFoundations.hasDensity_symmDiff_halfSpace hn hΩ hE h hx hpos hv hlim

/-- **Density theorem plus Radon–Nikodym.** Let `S ⊆ Ω` be a Borel, countably
`ℋ^{n-1}`-rectifiable set with locally finite `ℋ^{n-1}` measure in `Ω`. Let `ρ` be a measure
concentrated on `S` with `ρ(B_r(x)) ≤ C r^{n-1}` whenever `closedBall x (2r) ⊆ Ω`. Then
`ρ = θ ℋ^{n-1}⌊S` with `θ(x) = limsup_{r→0} ρ(B_r(x)) / (ω_{n-1} r^{n-1})`. Federer 2.10.19 (1)
(absolute continuity from the upper density bound), Radon–Nikodym, Federer 3.2.19 (density `1` of
`ℋ^{n-1}⌊S` a.e. on rectifiable `S`), and Besicovitch differentiation (Federer 2.9). This is the
step in the proof of Theorem 8.7 of the paper that writes the singular part of `Δu` as a density
times `ℋ^{n-1}⌊Σ^H`. Proved in gmt-foundations. -/
theorem eq_withDensity_upperDensity (hn : 2 ≤ n) {Ω S : Set (Rn n)} (hΩ : IsOpen Ω)
    (hS : MeasurableSet S) (hSΩ : S ⊆ Ω) (hrect : IsCountablyRectifiable n (n - 1) S)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω → hausdorffN n (n - 1) (K ∩ S) < ∞)
    {ρ : Measure (Rn n)} (hρS : ρ Sᶜ = 0) (C : ℝ)
    (hbd : ∀ x r, 0 < r → closedBall x (2 * r) ⊆ Ω →
      ρ (ball x r) ≤ ENNReal.ofReal (C * r ^ (n - 1))) :
    ρ = ((hausdorffN n (n - 1)).restrict S).withDensity fun x =>
      limsup (fun r => ρ (ball x r) / ENNReal.ofReal (unitBallVolume (n - 1) * r ^ (n - 1)))
        (𝓝[>] 0) := by
  exact GMTFoundations.GMT.eq_withDensity_upperDensity' hn hΩ hS hSΩ hrect hfin hρS C hbd

/-- **Approximate tangent planes.** Let `S ⊆ Ω` be a Borel, countably
`ℋ^{n-1}`-rectifiable set with locally finite `ℋ^{n-1}` measure in `Ω`. For `ℋ^{n-1}`-a.e.
`x ∈ S` there is a unit vector `ν` such that the blow-ups
`E ↦ ℋ^{n-1}(S ∩ (x + rE)) / r^{n-1}` converge weakly-* to `ℋ^{n-1}⌊ν^⊥` as `r → 0+`. The
exceptional set is written as an `ℋ^{n-1}`-null set. Mattila, Thm 15.19; Federer 3.2.19. Proved in
gmt-foundations. -/
theorem hausdorffN_not_approxTangent_eq_zero (hn : 2 ≤ n) {Ω S : Set (Rn n)} (hΩ : IsOpen Ω)
    (hS : MeasurableSet S) (hSΩ : S ⊆ Ω) (hrect : IsCountablyRectifiable n (n - 1) S)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω → hausdorffN n (n - 1) (K ∩ S) < ∞) :
    hausdorffN n (n - 1) {x | x ∈ S ∧ ¬ ∃ ν : Rn n, ‖ν‖ = 1 ∧
      ∀ φ : Rn n → ℝ, Continuous φ → HasCompactSupport φ →
        Tendsto (fun r => (r ^ (n - 1))⁻¹ * ∫ y in S, φ (r⁻¹ • (y - x)) ∂hausdorffN n (n - 1))
          (𝓝[>] 0) (𝓝 (∫ y in {y | ⟪y, ν⟫ = 0}, φ y ∂hausdorffN n (n - 1)))} = 0 := by
  exact GMTFoundations.GMT.hausdorffN_not_approxTangent_eq_zero hn
    (GMTFoundations.GMT.hausdorffN_self_eq_volume _) hΩ hS hSΩ hrect hfin

/-- **BV structure theorem.** Let `E` be measurable and `U` open.
If `|∫_E div φ| ≤ C sup|φ|` for every `φ ∈ C^∞_c(U; ℝⁿ)`, then `E` has a Gauss–Green pair in `U`
with total mass `≤ C`. This is the Riesz representation of the vector distribution `Dχ_E`
(Evans–Gariepy, Thm 5.1). It turns the estimate of Lemma 3.3 of the paper into a perimeter
measure. -/
theorem exists_isGaussGreenPair_of_integral_divergence_le (hn : 2 ≤ n) {U E : Set (Rn n)}
    (hU : IsOpen U) (hE : MeasurableSet E) (C : ℝ)
    (h : ∀ φ : Rn n → Rn n, IsSmoothTestField U φ →
      |∫ x in E, divergence φ x| ≤ C * ⨆ x, ‖φ x‖) :
    ∃ μ ν, IsGaussGreenPair U E μ ν ∧ μ U ≤ ENNReal.ofReal C := by
  -- proved in gmt-foundations v0.1.0
  exact GMTFoundations.exists_isGaussGreenPair_of_integral_divergence_le hn hU hE C h

/-- **BV structure theorem, `BV_loc` form.** If a measurable `E`
satisfies, near each point of the open set `U`, a bound `|∫_E div φ| ≤ C sup|φ|` for
`φ ∈ C^∞_c(B_r(x); ℝⁿ)`, then `E` has a Gauss–Green pair on all of `U`. This is Evans–Gariepy,
Thm 5.1, as stated there, for `χ_E ∈ BV_loc(U)`: a local bound near each point is equivalent to a
bound on every `V ⋐ U` (finite cover and a partition of unity). -/
theorem hasLocallyFinitePerimeter_of_local (hn : 2 ≤ n) {U E : Set (Rn n)} (hU : IsOpen U)
    (hE : MeasurableSet E)
    (h : ∀ x ∈ U, ∃ r > 0, ball x r ⊆ U ∧ ∃ C : ℝ, ∀ φ : Rn n → Rn n,
      IsSmoothTestField (ball x r) φ → |∫ y in E, divergence φ y| ≤ C * ⨆ y, ‖φ y‖) :
    HasLocallyFinitePerimeter U E := by
  -- proved in gmt-foundations v0.1.0
  exact GMTFoundations.hasLocallyFinitePerimeter_of_local hn hU hE h

end InnerVariational.Registry
