/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Singular.FlatPointQ
public import InnerVariational.Singular.Density
public import InnerVariational.Singular.Tangent
public import InnerVariational.NaberValtorta.InstanceQ
public import InnerVariational.Registry.GMT
public import GMTFoundations.Defs.GMT

/-!
# Blow-ups and density at singular points with a Lipschitz coefficient (Lemma 8.5)

Lemma 8.5 of D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and
compactness for non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025),
no. 3, DOI 10.1002/cpa.22226; arXiv:2306.10131 (numbering of arXiv v2), for a variational
solution `(u, χ)` with a Lipschitz coefficient `Q` (`QBounds Ω Q L c C'`). For `ℋ^{n-1}`-a.e.
`x ∈ Σ^H_Q`:

1. the renormalized functions `v_{x,r}(y) = u(x + r y) / (r √(H_x(u; r)))` converge to
   `α(n) |y · ν|` strongly in `W^{1,2}_loc(ℝⁿ)`, for a unit vector `ν`
   (`renormalized_tendsto_alpha_aeQ`, in the integral form of
   `Singular.renormalized_tendsto_alpha_ae`);
2. `{u > 0}` has Lebesgue density `1` at `x` (`density_pos_eq_one_aeQ`).

The paper treats `Q ≡ 1`. The proof is the same: outside an `ℋ^{n-1}`-null set, `x ∈ Σ^H_Q` has
modified frequency `Ñ_x(u; 0+) = 1` (Theorem 7.2 (3) with a Lipschitz coefficient,
`NaberValtorta.hausdorffN_not_tendsto_modFrequencyN_eq_zero`) and `Σ^H_Q` is flat at `x`
(`hausdorffN_not_isFlatAtQ_eq_zero`: the local structure of `Σ^H_Q`,
`NaberValtorta.sigmaHQ_inter_ball_structure`, and the existence of approximate tangent planes
a.e. on rectifiable sets, P. Mattila, *Geometry of Sets and Measures in Euclidean Spaces*,
Cambridge Univ. Press, 1995, Theorem 15.19). At such a point `tendsto_profile_of_isFlatAtQ`
(`Singular/FlatPointQ.lean`) gives (1), and (2) follows by the Chebyshev argument of
`Singular.hasDensity_pos_of_tendsto'`.
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational

namespace Singular

variable {n : ℕ} {Ω : Set (Rn n)} {C : ℝ≥0} {Q u χ : Rn n → ℝ} {L : ℝ≥0} {c C' : ℝ}

/-- **Approximate tangent plane ⇒ flatness** (proof of Lemma 8.5). If `S ⊆ Σ^H_Q` and the
blow-ups of `ℋ^{n-1}⌊S` at `x` converge to `ℋ^{n-1}⌊ν^⊥`, then `Σ^H_Q` is flat at `x` in
direction `ν`. -/
theorem isFlatAtQ_of_tendsto (hn : 2 ≤ n) {S : Set (Rn n)} (hS : S ⊆ sigmaHQ Ω Q u χ)
    {x ν : Rn n} (hν : ‖ν‖ = 1)
    (hT : ∀ φ : Rn n → ℝ, Continuous φ → HasCompactSupport φ →
      Tendsto (fun r => (r ^ (n - 1))⁻¹ * ∫ y in S, φ (r⁻¹ • (y - x)) ∂hausdorffN n (n - 1))
        (𝓝[>] 0) (𝓝 (∫ y in {y | ⟪y, ν⟫ = 0}, φ y ∂hausdorffN n (n - 1)))) :
    IsFlatAtQ Ω Q u χ x ν :=
  eventually_nonempty_inter_ball_of_tendsto hn hS hν hT

/-- **`Σ^H_Q` is flat at `ℋ^{n-1}`-a.e. of its points** (proof of Lemma 8.5), from the local
structure of `Σ^H_Q` (Theorem 7.2 (1)–(2)) and the existence of approximate tangent planes a.e.
on rectifiable sets. -/
theorem hausdorffN_not_isFlatAtQ_eq_zero (hn : 2 ≤ n) (hQ : QBounds Ω Q L c C')
    (h : IsVariationalSolutionQ Ω C Q u χ) :
    hausdorffN n (n - 1)
      {x | x ∈ sigmaHQ Ω Q u χ ∧ ¬ ∃ ν : Rn n, ‖ν‖ = 1 ∧ IsFlatAtQ Ω Q u χ x ν} = 0 := by
  haveI : NeZero n := ⟨by omega⟩
  have hρ : ∀ x ∈ Ω, ∃ ρ, 0 < ρ ∧ closedBall x ρ ⊆ Ω ∧ weissKappa L c C' * ρ ≤ 1 / 2 :=
    fun x hx => NaberValtorta.exists_radius_of_mem h.isOpen hx (hQ.weissKappa_nonneg hx)
  choose! ρ hρpos hρsub hρκ using hρ
  set E := {x | x ∈ sigmaHQ Ω Q u χ ∧ ¬ ∃ ν : Rn n, ‖ν‖ = 1 ∧ IsFlatAtQ Ω Q u χ x ν} with hE
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun i : sigmaHQ Ω Q u χ => ball (i : Rn n) (ρ i / 100)) fun _ => isOpen_ball
  have hcov : E ⊆ ⋃ i ∈ T, E ∩ ball (i : Rn n) (ρ i / 100) := by
    intro x hx
    have hx' : x ∈ ⋃ i : sigmaHQ Ω Q u χ, ball (i : Rn n) (ρ i / 100) := by
      have := hρpos x hx.1.1
      exact mem_iUnion.2 ⟨⟨x, hx.1⟩, mem_ball_self (by positivity)⟩
    rw [← hTU] at hx'
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 hx'
    exact mem_iUnion₂.2 ⟨i, hi, hx, hxi⟩
  refine measure_mono_null hcov ((measure_biUnion_null_iff hTc).2 fun i _ => ?_)
  -- one ball of the cover
  set B := ball (i : Rn n) (ρ i / 100) with hB
  set S := sigmaHQ Ω Q u χ ∩ B with hS
  obtain ⟨hfin, hrect⟩ := NaberValtorta.sigmaHQ_inter_ball_structure hn hQ h i.2
    (hρpos i i.2.1) (hρsub i i.2.1) (hρκ i i.2.1)
  have hSm : MeasurableSet S := (NaberValtorta.measurableSet_sigmaHQ hQ h).inter measurableSet_ball
  have hR13 := Registry.hausdorffN_not_approxTangent_eq_zero hn isOpen_ball hSm
    inter_subset_right hrect fun K _ _ => (measure_mono inter_subset_right).trans_lt hfin
  refine measure_mono_null ?_ hR13
  rintro x ⟨⟨hxH, hxnot⟩, hxB⟩
  refine ⟨⟨hxH, hxB⟩, fun ⟨ν, hν, hT⟩ => hxnot ⟨ν, hν, ?_⟩⟩
  exact isFlatAtQ_of_tendsto hn inter_subset_left hν hT

/-- **Lemma 8.5 (1) with a Lipschitz coefficient**. For `ℋ^{n-1}`-a.e. `x ∈ Σ^H_Q` there is a
unit vector `ν` such that, for every `R > 0`, as `r → 0+`,
* `(r^{n+2} H_x(u; r))⁻¹ ∫_{B_{Rr}(x)} (u − √(H_x(u; r)) α(n) |(y−x)·ν|)² → 0`,
* `(r^n H_x(u; r))⁻¹ ∫_{B_{Rr}(x)} |∇u − √(H_x(u; r)) α(n) ∇|(y−x)·ν||² → 0`.

That is, `v_{x,r}(y) = u(x + r y) / (r √(H_x(u; r)))` converges to `α(n) |y·ν|` strongly in
`W^{1,2}_loc(ℝⁿ)` (see `Singular.renormalized_tendsto_alpha_ae` for the change of variables). -/
theorem renormalized_tendsto_alpha_aeQ [NeZero n] (hn : 2 ≤ n) (hQ : QBounds Ω Q L c C')
    (h : IsVariationalSolutionQ Ω C Q u χ) :
    hausdorffN n (n - 1) {x | x ∈ sigmaHQ Ω Q u χ ∧ ¬ ∃ ν : Rn n, ‖ν‖ = 1 ∧ ∀ R : ℝ, 0 < R →
      Tendsto (fun r => (∫ y in ball x (R * r),
          (u y - √(heightH u x r) * alphaN n * absProfile ν x y) ^ 2) /
          (r ^ (n + 2) * heightH u x r)) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun r => (∫ y in ball x (R * r),
          ‖gradient u y - (√(heightH u x r) * alphaN n) • gradient (absProfile ν x) y‖ ^ 2) /
          (r ^ n * heightH u x r)) (𝓝[>] 0) (𝓝 0)} = 0 := by
  refine measure_mono_null ?_ (measure_union_null
    (NaberValtorta.hausdorffN_not_tendsto_modFrequencyN_eq_zero hn hQ h)
    (hausdorffN_not_isFlatAtQ_eq_zero hn hQ h))
  rintro x ⟨hxS, hx⟩
  by_cases hN : Tendsto (modFrequencyN (weissKappa L c C') Q u χ x) (𝓝[>] 0) (𝓝 1)
  · by_cases hF : ∃ ν : Rn n, ‖ν‖ = 1 ∧ IsFlatAtQ Ω Q u χ x ν
    · obtain ⟨ν, hν, hfl⟩ := hF
      exact absurd ⟨ν, hν, fun R hR => tendsto_profile_of_isFlatAtQ hQ h hxS hN hn hν hfl R hR⟩
        hx
    · exact Or.inr ⟨hxS, hF⟩
  · exact Or.inl ⟨hxS, hN⟩

/-- **Lemma 8.5 (2) with a Lipschitz coefficient**. At `ℋ^{n-1}`-a.e. `x ∈ Σ^H_Q` the Lebesgue
density of `{u > 0}` exists and equals `1`. -/
theorem density_pos_eq_one_aeQ [NeZero n] (hn : 2 ≤ n) (hQ : QBounds Ω Q L c C')
    (h : IsVariationalSolutionQ Ω C Q u χ) :
    hausdorffN n (n - 1) {x | x ∈ sigmaHQ Ω Q u χ ∧ ¬ HasDensity {y | 0 < u y} x 1} = 0 := by
  refine measure_mono_null ?_ (renormalized_tendsto_alpha_aeQ hn hQ h)
  rintro x ⟨hxS, hxd⟩
  refine ⟨hxS, fun ⟨ν, hν, hR⟩ => hxd ?_⟩
  exact hasDensity_pos_of_tendsto' h.isOpen h.continuousOn hxS.1
    (fun _ hr hrΩ => h.heightH_pos hQ hxS.2.1 hr hrΩ) hν
    (by simpa only [one_mul] using (hR 1 one_pos).1)

end Singular

end InnerVariational
