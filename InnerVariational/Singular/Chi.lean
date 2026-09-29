/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Singular.Density
public import InnerVariational.Singular.FedererCriterion
import Mathlib.Geometry.Euclidean.Volume.Measure
public import Mathlib.Order.CompletePartialOrder
import InnerVariational.Regular.Perimeter
import InnerVariational.Regular.ChiInterior
import InnerVariational.Monotonicity.HighestDensity
public import InnerVariational.Defs.HighestDensity
public import InnerVariational.Monotonicity.Limits
import InnerVariational.Kernel.Subharmonic
import InnerVariational.Basic.Polar
public import GMTFoundations.Defs.GMT

/-!
# Identification of `χ` (Theorem 8.6)

Theorem 8.6 of D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and
compactness for non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025),
no. 3, DOI 10.1002/cpa.22226; arXiv:2306.10131 (numbering of arXiv v2). Let `(u, χ)` be a
variational solution on an open connected `Ω`. Then either `u ≡ 0` or `χ = χ_{u>0}` a.e.
(`Singular.chi_eq_indicator`).

## Proof

Let `A` be the *pathological set* (`pathologicalSet`): the points near which `u = 0` and `χ = 1`
a.e. It is open. By the upper semicontinuity of `M_x(u; 0+)` (Prop 3.5), every point of
`Ω ∩ closure A` lies in `A` or in `Σ^H` (`mem_pathologicalSet_or_mem_sigmaH`). Points
of `A` have density `1` in `A`, and points off `closure A` density `0`. At a point of `Σ^H` where
`{u > 0}` has density `1`, `A` (on which `u = 0`) has density `0`. So Lemma 8.5 (2) makes
`∂ᵉA ∩ Ω` an `ℋ^{n-1}`-null set (`essentialBoundary_pathologicalSet_inter_subset`), and Federer's
criterion (an `ℋ^{n-1}`-null essential boundary in a ball forces a trivial set; H. Federer,
*Geometric Measure Theory*, Springer, 1969, 4.5.11 and 4.5.6; see
`Singular/FedererCriterion.lean`) makes
`A` trivial in every ball in `Ω`.
Since `Ω` is connected, `A` is dense in `Ω` (then `u ≡ 0` by continuity) or `A = ∅`.

If `A = ∅`, then `χ = 0` a.e. on `Ω \ closure {u > 0}` (`χ` is locally constant there,
`IsVariationalSolution.exists_ae_eq_const_of_eq_zero`), and `χ = 1` a.e. on `{u > 0}`. The rest,
`Ω ∩ ∂{u > 0}`, is Lebesgue-null (`volume_inter_frontier_pos_eq_zero`): off `Σ^H` by the density
argument of the proof of Lemma 8.2
(`IsVariationalSolution.volume_inter_frontier_pos_eq_zero` on `Ω \ Σ^H`), and `Σ^H` itself is
null (`volume_sigmaH_eq_zero`) by Lemma 8.5 (2) and the Lebesgue density theorem.

## Comparison with the paper

The paper's proof uses Theorem 7.2 twice: for `|∂{u > 0}| = 0`, and for the local
finiteness of `ℋ^{n-1}(∂U ∩ Ω)`, from which it infers that a pathological component `U` has
locally finite perimeter and applies the relative isoperimetric inequality and the density `1/2`
of `U` on its reduced boundary. Both uses are replaced here by Lemma 8.5 (2): an `ℋ^{n-1}`-null
set is Lebesgue-null (`volume_eq_zero_of_hausdorffN_eq_zero`), and Federer 4.5.11 applies to an
`ℋ^{n-1}`-null essential boundary directly. The mathematical content is the same: the paper's
inference "locally finite `ℋ^{n-1}` measure ⇒ locally finite perimeter" is itself Federer 4.5.11.

## Gluing

`chi_eq_indicator_of_local`: the same conclusion on a connected open `U` when `(u, χ)` is only a
variational solution near each point of `U` (with constants that may vary from point to point).
The two alternatives are glued along `U` by connectedness.
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

namespace Singular

/-! ### Measure-theoretic facts -/

/-- `ℋ^{n-1}`-null sets are Lebesgue-null: `ℋ^{n-1}(s) = 0` forces `μH[n](s) = 0`, and
`μH[n]` is a multiple of Lebesgue measure on `ℝⁿ`. -/
theorem volume_eq_zero_of_hausdorffN_eq_zero (hn : 1 ≤ n) {s : Set (Rn n)}
    (h : hausdorffN n (n - 1) s = 0) : volume s = 0 := by
  have hc : ENNReal.ofReal (unitBallVolume (n - 1) / 2 ^ (n - 1)) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (div_pos (unitBallVolume_pos _) (pow_pos two_pos _))).ne'
  have h1 : Measure.hausdorffMeasure ((n - 1 : ℕ) : ℝ) s = 0 := by
    rw [hausdorffN, Measure.smul_apply, smul_eq_mul, mul_eq_zero] at h
    exact h.resolve_left hc
  have hlt : ((n - 1 : ℕ) : ℝ) < ((n : ℕ) : ℝ) := by exact_mod_cast (by omega : n - 1 < n)
  have h2 : Measure.hausdorffMeasure ((n : ℕ) : ℝ) s = 0 :=
    (Measure.hausdorffMeasure_zero_or_top hlt s).resolve_right
      (by rw [h1]; exact ENNReal.zero_ne_top)
  rw [← EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Measure.euclideanHausdorffMeasure_def,
    Measure.smul_apply, h2, smul_zero]

/-- A set has density `1` at each of its interior points. -/
theorem hasDensity_one_of_mem_nhds {E : Set (Rn n)} {x : Rn n} (hE : E ∈ 𝓝 x) :
    HasDensity E x 1 := by
  obtain ⟨δ, hδ, hδE⟩ := Metric.mem_nhds_iff.1 hE
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
  rw [inter_eq_right.2 ((ball_subset_ball hr.2.le).trans hδE), div_self]
  exact (ENNReal.toReal_pos (measure_ball_pos volume x hr.1).ne' measure_ball_lt_top.ne).ne'

/-- A set has density `0` at each point outside its closure. -/
theorem hasDensity_zero_of_notMem_closure {E : Set (Rn n)} {x : Rn n} (hx : x ∉ closure E) :
    HasDensity E x 0 := by
  obtain ⟨δ, hδ, hδE⟩ := Metric.mem_nhds_iff.1 (isClosed_closure.isOpen_compl.mem_nhds hx)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
  have : E ∩ ball x r = ∅ := eq_empty_iff_forall_notMem.2 fun y hy =>
    hδE (ball_subset_ball hr.2.le hy.2) (subset_closure hy.1)
  rw [this, measure_empty, ENNReal.toReal_zero, zero_div]

/-- If `A` and `F` are disjoint and `F` has density `1` at `x`, then `A` has density `0` there. -/
theorem hasDensity_zero_of_disjoint {A F : Set (Rn n)} {x : Rn n} (hA : MeasurableSet A)
    (hAF : Disjoint A F) (hF : HasDensity F x 1) : HasDensity A x 0 := by
  have h1 : Tendsto (fun r => 1 - (volume (F ∩ ball x r)).toReal / (volume (ball x r)).toReal)
      (𝓝[>] 0) (𝓝 0) := by
    have := (tendsto_const_nhds (x := (1 : ℝ))).sub hF
    rwa [sub_self] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h1
    (.of_forall fun r => div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) ?_
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  have hB : 0 < (volume (ball x r)).toReal :=
    ENNReal.toReal_pos (measure_ball_pos volume x hr).ne' measure_ball_lt_top.ne
  have hsum : volume (F ∩ ball x r) + volume (A ∩ ball x r) ≤ volume (ball x r) := by
    rw [← measure_union (Disjoint.mono inter_subset_left inter_subset_left hAF.symm)
      (hA.inter measurableSet_ball)]
    exact measure_mono (union_subset inter_subset_right inter_subset_right)
  have hsum' : (volume (F ∩ ball x r)).toReal + (volume (A ∩ ball x r)).toReal ≤
      (volume (ball x r)).toReal := by
    rw [← ENNReal.toReal_add (measure_ne_top_of_subset inter_subset_right measure_ball_lt_top.ne)
      (measure_ne_top_of_subset inter_subset_right measure_ball_lt_top.ne)]
    exact ENNReal.toReal_mono measure_ball_lt_top.ne hsum
  rw [le_sub_iff_add_le, ← add_div, div_le_one hB]
  linarith

/-! ### The pathological set -/

/-- The *pathological set* of `(u, χ)` in `Ω`: the points `x` with a ball `B_δ(x) ⊆ Ω` on which
`u = 0` and `χ = 1` a.e. It is the union of the components of `{u = 0}°` on which `χ = 1`
(the components `U` in the proof of Theorem 8.6). -/
def pathologicalSet (Ω : Set (Rn n)) (u χ : Rn n → ℝ) : Set (Rn n) :=
  {x | ∃ δ > 0, ball x δ ⊆ Ω ∧ (∀ y ∈ ball x δ, u y = 0) ∧
    ∀ᵐ y ∂(volume.restrict (ball x δ)), χ y = 1}

variable {Ω : Set (Rn n)} {C : ℝ≥0} {u χ : Rn n → ℝ}

theorem isOpen_pathologicalSet : IsOpen (pathologicalSet Ω u χ) := by
  rw [Metric.isOpen_iff]
  rintro x ⟨δ, hδ, hδΩ, hu, hc⟩
  refine ⟨δ, hδ, fun z hz => ?_⟩
  have hsub : ball z (δ - dist z x) ⊆ ball x δ := fun w hw => by
    rw [mem_ball] at hw ⊢
    linarith [dist_triangle w z x]
  exact ⟨δ - dist z x, sub_pos.2 hz, hsub.trans hδΩ, fun y hy => hu y (hsub hy),
    ae_restrict_of_ae_restrict_of_subset hsub hc⟩

theorem pathologicalSet_subset : pathologicalSet Ω u χ ⊆ Ω := fun _ ⟨_, hδ, hδΩ, _⟩ =>
  hδΩ (mem_ball_self hδ)

theorem eq_zero_of_mem_pathologicalSet {x : Rn n} (hx : x ∈ pathologicalSet Ω u χ) : u x = 0 :=
  let ⟨_, hδ, _, hu, _⟩ := hx
  hu x (mem_ball_self hδ)

theorem disjoint_pathologicalSet_pos : Disjoint (pathologicalSet Ω u χ) {y | 0 < u y} :=
  disjoint_left.2 fun y hy hpos => by
    have : 0 < u y := hpos
    rw [eq_zero_of_mem_pathologicalSet hy] at this
    exact lt_irrefl _ this

/-- `M_x(u; 0+) = |B_1|` on the pathological set. -/
theorem Mzero_eq_of_mem_pathologicalSet [NeZero n] (h : IsVariationalSolution Ω C u χ) {x : Rn n}
    (hx : x ∈ pathologicalSet Ω u χ) : Mzero u χ x = unitBallVolume n := by
  obtain ⟨δ, hδ, hδΩ, hu, hc⟩ := hx
  rw [h.Mzero_eq_of_ae_eq_const (hδΩ (mem_ball_self hδ)) (hu x (mem_ball_self hδ)) hδ hc,
    one_mul]

/-- **`∂U ∩ Ω ⊆ Σ^H`** (proof of Theorem 8.6). A point of `Ω` in the closure of the pathological
set lies in it or in `Σ^H`. By upper semicontinuity (Proposition 3.5), `M_x(u; 0+) ≥ |B_1|`. If
`x ∈ closure {u > 0}`, then `x ∈ Σ^H`. Otherwise `u = 0` on a ball around `x`, where `χ` is a.e.
constant, and that constant is `1` because the ball meets the pathological set. -/
theorem mem_pathologicalSet_or_mem_sigmaH [NeZero n] (h : IsVariationalSolution Ω C u χ)
    {x : Rn n} (hx : x ∈ Ω) (hcl : x ∈ closure (pathologicalSet Ω u χ)) :
    x ∈ pathologicalSet Ω u χ ∨ x ∈ sigmaH Ω u χ := by
  have hM : (unitBallVolume n : EReal) ≤ Mzero u χ x := by
    by_contra hlt
    rw [not_le] at hlt
    have hev := h.upperSemicontinuousOn_Mzero x hx _ hlt
    rw [h.isOpen.nhdsWithin_eq hx] at hev
    obtain ⟨y, hyA, hy⟩ := ((mem_closure_iff_frequently.1 hcl).and_eventually hev).exists
    rw [Mzero_eq_of_mem_pathologicalSet h hyA] at hy
    exact lt_irrefl _ hy
  by_cases hpos : x ∈ closure {y | 0 < u y}
  · exact Or.inr (h.mem_sigmaH_iff_le_Mzero.2 ⟨hx, hpos, hM⟩)
  left
  obtain ⟨δ, hδ, hδΩ, hu0⟩ := h.exists_ball_eq_zero hx hpos
  obtain ⟨c, -, hc⟩ := h.exists_ae_eq_const_of_eq_zero isOpen_ball
    (convex_ball x δ).isPreconnected hδΩ hu0
  obtain ⟨z, hzB, hzA⟩ := mem_closure_iff.1 hcl (ball x δ) isOpen_ball (mem_ball_self hδ)
  obtain ⟨δz, hδz, -, -, hcz⟩ := hzA
  have hρ : 0 < min δz (δ - dist z x) := lt_min hδz (sub_pos.2 hzB)
  have hsub1 : ball z (min δz (δ - dist z x)) ⊆ ball z δz := ball_subset_ball (min_le_left _ _)
  have hsub2 : ball z (min δz (δ - dist z x)) ⊆ ball x δ := fun w hw => by
    rw [mem_ball] at hw ⊢
    have := min_le_right δz (δ - dist z x)
    linarith [dist_triangle w z x]
  have hne : (ae (volume.restrict (ball z (min δz (δ - dist z x))))).NeBot :=
    ae_neBot.2 fun h0 => (measure_ball_pos volume z hρ).ne' (Measure.restrict_eq_zero.1 h0)
  obtain ⟨w, hw1, hwc⟩ := ((ae_restrict_of_ae_restrict_of_subset hsub1 hcz).and
    (ae_restrict_of_ae_restrict_of_subset hsub2 hc)).exists
  have hc1 : c = 1 := hwc.symm.trans hw1
  subst hc1
  exact ⟨δ, hδ, hδΩ, hu0, hc⟩

/-- The essential boundary of the pathological set inside `Ω` consists of points of `Σ^H` at
which `{u > 0}` does not have density `1`. -/
theorem essentialBoundary_pathologicalSet_inter_subset [NeZero n]
    (h : IsVariationalSolution Ω C u χ) :
    essentialBoundary (pathologicalSet Ω u χ) ∩ Ω ⊆
      {x | x ∈ sigmaH Ω u χ ∧ ¬ HasDensity {y | 0 < u y} x 1} := by
  rintro x ⟨⟨h0, h1⟩, hx⟩
  by_cases hcl : x ∈ closure (pathologicalSet Ω u χ)
  · rcases mem_pathologicalSet_or_mem_sigmaH h hx hcl with hA | hS
    · exact absurd (hasDensity_one_of_mem_nhds (isOpen_pathologicalSet.mem_nhds hA)) h1
    · exact ⟨hS, fun hd => h0 (hasDensity_zero_of_disjoint isOpen_pathologicalSet.measurableSet
        disjoint_pathologicalSet_pos hd)⟩
  · exact absurd (hasDensity_zero_of_notMem_closure hcl) h0

/-- **Federer's criterion applied to the pathological set.** In every ball `B ⊆ Ω` the
pathological set is null or of full measure (Lemma 8.5 (2) and Federer's criterion,
`Singular.FedererCriterion.ae_trivial_of_hausdorffN_essentialBoundary_inter_ball`). -/
theorem pathologicalSet_ae_trivial [NeZero n] (hn : 2 ≤ n) (h : IsVariationalSolution Ω C u χ)
    {c : Rn n} {r : ℝ} (hball : ball c r ⊆ Ω) :
    volume (pathologicalSet Ω u χ ∩ ball c r) = 0 ∨
      volume (ball c r \ pathologicalSet Ω u χ) = 0 := by
  refine FedererCriterion.ae_trivial_of_hausdorffN_essentialBoundary_inter_ball hn
    isOpen_pathologicalSet.measurableSet (measure_mono_null ?_ (density_pos_eq_one_ae hn h))
  exact fun y hy => essentialBoundary_pathologicalSet_inter_subset h ⟨hy.1, hball hy.2⟩

/-! ### `|∂{u > 0} ∩ Ω| = 0` -/

/-- **`|Σ^H| = 0`.** By Lemma 8.5 (2), outside an `ℋ^{n-1}`-null (hence Lebesgue-null) set, the
points of `Σ^H` are zeros of `u` at which `{u > 0}` has density `1`. The Lebesgue density theorem
makes those a null set. -/
theorem volume_sigmaH_eq_zero [NeZero n] (hn : 2 ≤ n) (h : IsVariationalSolution Ω C u χ) :
    volume (sigmaH Ω u χ) = 0 := by
  set F : Set (Rn n) := Ω ∩ {y | 0 < u y} with hFdef
  have hFm : MeasurableSet F :=
    (h.continuousOn.isOpen_inter_preimage h.isOpen isOpen_Ioi).measurableSet
  have hE1 := volume_eq_zero_of_hausdorffN_eq_zero (by omega) (density_pos_eq_one_ae hn h)
  have hE2 := ae_iff.1 (Regular.ae_hasDensity_indicator hFm)
  refine measure_mono_null (fun x hx => ?_) (measure_union_null hE1 hE2)
  by_cases hd : HasDensity {y | 0 < u y} x 1
  · right
    intro hx'
    have hF1 : HasDensity F x 1 := (hasDensity_inter_iff (h.isOpen.mem_nhds hx.1)).2 hd
    have hxF : x ∉ F := fun hxF => by
      have : 0 < u x := hxF.2
      rw [h.eq_zero_of_mem_sigmaH hx] at this
      exact lt_irrefl _ this
    rw [indicator_of_notMem hxF] at hx'
    exact one_ne_zero (tendsto_nhds_unique hF1 hx')
  · exact Or.inl ⟨hx, hd⟩

/-- **`|Ω ∩ ∂{u > 0}| = 0`** (first step of the proof of Theorem 8.6). Off `Σ^H` this is the
density argument of the proof of Lemma 8.2 on the open set `Ω \ Σ^H`, where `Σ^H` is empty.
`Σ^H` is null by `volume_sigmaH_eq_zero`. -/
theorem volume_inter_frontier_pos_eq_zero [NeZero n] (hn : 2 ≤ n)
    (h : IsVariationalSolution Ω C u χ) : volume (Ω ∩ frontier {y | 0 < u y}) = 0 := by
  have h1 := h.diff_sigmaH.volume_inter_frontier_pos_eq_zero hn h.sigmaH_diff_sigmaH_eq_empty
  refine measure_mono_null (fun x hx => ?_) (measure_union_null h1 (volume_sigmaH_eq_zero hn h))
  by_cases hS : x ∈ sigmaH Ω u χ
  · exact Or.inr hS
  · exact Or.inl ⟨⟨hx.1, hS⟩, hx.2⟩

/-! ### Theorem 8.6 -/

/-- If the pathological set is empty, then `χ = χ_{u>0}` a.e. on `Ω`. -/
theorem ae_chi_eq_posIndicator_of_pathologicalSet_eq_empty [NeZero n] (hn : 2 ≤ n)
    (h : IsVariationalSolution Ω C u χ) (hA : pathologicalSet Ω u χ = ∅) :
    ∀ᵐ y ∂(volume.restrict Ω), χ y = posIndicator u y := by
  -- `χ = 0` a.e. on `Ω \ closure {u > 0}`
  have hG : ∀ᵐ y, y ∈ Ω → y ∉ closure {y | 0 < u y} → χ y = 0 := by
    rw [ae_iff]
    refine measure_null_of_locally_null _ fun x hx => ?_
    simp only [mem_setOf_eq, Classical.not_imp] at hx
    obtain ⟨hxΩ, hncl, -⟩ := hx
    obtain ⟨δ, hδ, hδΩ, hu0⟩ := h.exists_ball_eq_zero hxΩ hncl
    obtain ⟨c, hc01, hc⟩ := h.exists_ae_eq_const_of_eq_zero isOpen_ball
      (convex_ball x δ).isPreconnected hδΩ hu0
    have hc0 : c = 0 := by
      rcases hc01 with h0 | h1
      · exact h0
      · subst h1
        have hxA : x ∈ pathologicalSet Ω u χ := ⟨δ, hδ, hδΩ, hu0, hc⟩
        rw [hA] at hxA
        exact absurd hxA (notMem_empty x)
    subst hc0
    refine ⟨{y | ¬(y ∈ Ω → y ∉ closure {y | 0 < u y} → χ y = 0)} ∩ ball x δ,
      inter_mem_nhdsWithin _ (ball_mem_nhds x hδ), ?_⟩
    rw [ae_restrict_iff' measurableSet_ball, ae_iff] at hc
    refine measure_mono_null (fun z hz => ?_) hc
    simp only [mem_setOf_eq, Classical.not_imp] at hz ⊢
    exact ⟨hz.2, hz.1.2.2⟩
  have hF := volume_inter_frontier_pos_eq_zero hn h
  rw [ae_restrict_iff' h.isOpen.measurableSet]
  filter_upwards [h.ae_chi_eq_one, hG, measure_eq_zero_iff_ae_notMem.1 hF] with y h1 h2 h3 hyΩ
  rcases (h.nonneg y hyΩ).lt_or_eq with hpos | hzero
  · rw [h1 hyΩ hpos, posIndicator_of_pos hpos]
  · have hncl : y ∉ closure {y | 0 < u y} := fun hcl =>
      h3 ⟨hyΩ, (h.mem_frontier_pos_iff hyΩ).2 ⟨hcl, hzero.symm⟩⟩
    rw [h2 hyΩ hncl, posIndicator_of_nonpos hzero.symm.le]

/-- **Theorem 8.6**. Let `(u, χ)` be a variational solution on an
open connected `Ω`. Then either `u ≡ 0` on `Ω` or `χ = χ_{u>0}` a.e. on `Ω`.

This has literally the type of `Statements.chi_eq_indicator` (Theorem 1.2 (i)). The proof is in
the module docstring. It uses Lemma 8.5 (2) (`density_pos_eq_one_ae`) and Federer's criterion
for an `ℋ^{n-1}`-null essential boundary in place of the paper's appeal to Theorem 7.2. -/
theorem chi_eq_indicator (hn : 2 ≤ n) {Ω : Set (Rn n)} {C_V : ℝ≥0} {u χ : Rn n → ℝ}
    (hΩ : IsConnected Ω) (h : IsVariationalSolution Ω C_V u χ) :
    (∀ x ∈ Ω, u x = 0) ∨ χ =ᵐ[volume.restrict Ω] posIndicator u := by
  haveI : NeZero n := ⟨by omega⟩
  set A := pathologicalSet Ω u χ with hAdef
  -- every point of `Ω` is interior to `closure A` or outside `closure A`
  have hcover : Ω ⊆ interior (closure A) ∪ (closure A)ᶜ := by
    intro x hx
    obtain ⟨δ, hδ, hδΩ⟩ := Metric.isOpen_iff.1 h.isOpen x hx
    rcases pathologicalSet_ae_trivial hn h hδΩ with h0 | h1
    · right
      have hempty : A ∩ ball x δ = ∅ :=
        (isOpen_pathologicalSet.inter isOpen_ball).measure_eq_zero_iff volume |>.1 h0
      intro hcl
      obtain ⟨z, hz, hzA⟩ := mem_closure_iff.1 hcl (ball x δ) isOpen_ball (mem_ball_self hδ)
      exact (eq_empty_iff_forall_notMem.1 hempty) z ⟨hzA, hz⟩
    · left
      have hopen : IsOpen (ball x δ \ closure A) := isOpen_ball.sdiff isClosed_closure
      have hempty : ball x δ \ closure A = ∅ :=
        hopen.measure_eq_zero_iff volume |>.1
          (measure_mono_null (diff_subset_diff_right subset_closure) h1)
      exact mem_interior.2 ⟨ball x δ, fun y hy => by
        by_contra hy'
        exact (eq_empty_iff_forall_notMem.1 hempty) y ⟨hy, hy'⟩, isOpen_ball, mem_ball_self hδ⟩
  have hdisj : Ω ∩ (interior (closure A) ∩ (closure A)ᶜ) = ∅ :=
    eq_empty_iff_forall_notMem.2 fun x ⟨_, hxi, hxc⟩ => hxc (interior_subset hxi)
  rcases isPreconnected_iff_subset_of_disjoint.1 hΩ.isPreconnected _ _ isOpen_interior
    isClosed_closure.isOpen_compl hcover hdisj with hsub | hsub
  · -- `A` is dense in `Ω`: `u ≡ 0`
    left
    intro x hx
    have hcl : x ∈ closure A := interior_subset (hsub hx)
    by_contra hne
    have hpos : 0 < u x := lt_of_le_of_ne (h.nonneg x hx) (Ne.symm hne)
    have hN : {y | 0 < u y} ∈ 𝓝 x :=
      (h.continuousOn.continuousAt (h.isOpen.mem_nhds hx)).preimage_mem_nhds (Ioi_mem_nhds hpos)
    obtain ⟨z, hz, hzA⟩ := mem_closure_iff_nhds.1 hcl _ hN
    exact disjoint_left.1 disjoint_pathologicalSet_pos hzA hz
  · -- `A = ∅`: `χ = χ_{u>0}` a.e.
    right
    have hA : A = ∅ := eq_empty_iff_forall_notMem.2 fun x hxA =>
      hsub (pathologicalSet_subset hxA) (subset_closure hxA)
    exact ae_chi_eq_posIndicator_of_pathologicalSet_eq_empty hn h hA

/-- **Theorem 8.6, glued form**. Let `U` be connected and let `(u, χ)` be a variational solution
near every point of `U`: each `x ∈ U` has an open neighbourhood `V ⊆ U` on which `(u, χ)` is a
variational solution with some constant `C_V(x)`. Then either `u ≡ 0` on `U` and `χ = 1` a.e. on
`U`, or `χ = χ_{u>0}` a.e. on `U`.

This is the form that a locally Lipschitz `u` provides: the Lipschitz constant only needs to be
uniform near each point. The proof applies `chi_eq_indicator` on small balls and glues the two
alternatives, `{u = 0, χ = 1 a.e. near x}` and `{χ = χ_{u>0} a.e. near x}`, which are open,
disjoint, and cover `U`. -/
theorem chi_eq_indicator_of_local (hn : 2 ≤ n) {U : Set (Rn n)} {u χ : Rn n → ℝ}
    (hU : IsConnected U)
    (h : ∀ x ∈ U, ∃ V, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ ∃ C : ℝ≥0, IsVariationalSolution V C u χ) :
    ((∀ x ∈ U, u x = 0) ∧ ∀ᵐ y ∂(volume.restrict U), χ y = 1) ∨
      χ =ᵐ[volume.restrict U] posIndicator u := by
  haveI : NeZero n := ⟨by omega⟩
  have hball : ∀ x ∈ U, ∃ δ > 0, ball x δ ⊆ U ∧ ∃ C : ℝ≥0,
      IsVariationalSolution (ball x δ) C u χ := by
    intro x hx
    obtain ⟨V, hVo, hxV, hVU, C, hC⟩ := h x hx
    obtain ⟨δ, hδ, hδV⟩ := Metric.isOpen_iff.1 hVo x hxV
    exact ⟨δ, hδ, hδV.trans hVU, C, hC.mono isOpen_ball hδV⟩
  have hUo : IsOpen U := isOpen_iff_mem_nhds.2 fun x hx => by
    obtain ⟨V, hVo, hxV, hVU, -⟩ := h x hx
    exact mem_of_superset (hVo.mem_nhds hxV) hVU
  have hsub : ∀ (x z : Rn n) (δ : ℝ), z ∈ ball x δ → ball z (δ - dist z x) ⊆ ball x δ :=
    fun x z δ hz w hw => by
      rw [mem_ball] at hw ⊢
      linarith [dist_triangle w z x]
  set P : Set (Rn n) := {x | ∃ δ > 0, ball x δ ⊆ U ∧ (∀ y ∈ ball x δ, u y = 0) ∧
    ∀ᵐ y ∂(volume.restrict (ball x δ)), χ y = 1} with hPdef
  set Q : Set (Rn n) := {x | ∃ δ > 0, ball x δ ⊆ U ∧
    ∀ᵐ y ∂(volume.restrict (ball x δ)), χ y = posIndicator u y} with hQdef
  have hPo : IsOpen P := by
    rw [Metric.isOpen_iff]
    rintro x ⟨δ, hδ, hδU, hu, hc⟩
    exact ⟨δ, hδ, fun z hz => ⟨δ - dist z x, sub_pos.2 hz, (hsub x z δ hz).trans hδU,
      fun y hy => hu y (hsub x z δ hz hy), ae_restrict_of_ae_restrict_of_subset (hsub x z δ hz) hc⟩⟩
  have hQo : IsOpen Q := by
    rw [Metric.isOpen_iff]
    rintro x ⟨δ, hδ, hδU, hc⟩
    exact ⟨δ, hδ, fun z hz => ⟨δ - dist z x, sub_pos.2 hz, (hsub x z δ hz).trans hδU,
      ae_restrict_of_ae_restrict_of_subset (hsub x z δ hz) hc⟩⟩
  have hcover : U ⊆ P ∪ Q := by
    intro x hx
    obtain ⟨δ, hδ, hδU, C, hC⟩ := hball x hx
    rcases chi_eq_indicator hn ((convex_ball x δ).isConnected (nonempty_ball.2 hδ)) hC with
      hu | hae
    · obtain ⟨c, hc01, hc⟩ := hC.exists_ae_eq_const_of_eq_zero isOpen_ball
        (convex_ball x δ).isPreconnected subset_rfl hu
      rcases hc01 with rfl | rfl
      · right
        refine ⟨δ, hδ, hδU, ?_⟩
        filter_upwards [hc, ae_restrict_mem measurableSet_ball] with y hy hyB
        rw [hy, posIndicator_of_nonpos (hu y hyB).le]
      · exact Or.inl ⟨δ, hδ, hδU, hu, hc⟩
    · exact Or.inr ⟨δ, hδ, hδU, hae⟩
  have hdisj : U ∩ (P ∩ Q) = ∅ := by
    refine eq_empty_iff_forall_notMem.2 fun x ⟨_, ⟨δ₁, hδ₁, _, hu, hc1⟩, ⟨δ₂, hδ₂, _, hc2⟩⟩ => ?_
    have hδ : 0 < min δ₁ δ₂ := lt_min hδ₁ hδ₂
    have hne : (ae (volume.restrict (ball x (min δ₁ δ₂)))).NeBot :=
      ae_neBot.2 fun h0 => (measure_ball_pos volume x hδ).ne' (Measure.restrict_eq_zero.1 h0)
    obtain ⟨y, ⟨hy1, hy2⟩, hyB⟩ :=
      (((ae_restrict_of_ae_restrict_of_subset (ball_subset_ball (min_le_left _ _)) hc1).and
        (ae_restrict_of_ae_restrict_of_subset (ball_subset_ball (min_le_right _ _)) hc2)).and
        (ae_restrict_mem measurableSet_ball)).exists
    rw [posIndicator_of_nonpos (hu y (ball_subset_ball (min_le_left _ _) hyB)).le] at hy2
    exact one_ne_zero (hy1.symm.trans hy2)
  rcases isPreconnected_iff_subset_of_disjoint.1 hU.isPreconnected P Q hPo hQo hcover hdisj with
    hP | hQ
  · left
    refine ⟨fun x hx => ?_, ?_⟩
    · obtain ⟨δ, hδ, -, hu, -⟩ := hP hx
      exact hu x (mem_ball_self hδ)
    rw [ae_restrict_iff' hUo.measurableSet, ae_iff]
    refine measure_null_of_locally_null _ fun x hx => ?_
    simp only [mem_setOf_eq, Classical.not_imp] at hx
    obtain ⟨δ, hδ, -, -, hc⟩ := hP hx.1
    refine ⟨{y | ¬(y ∈ U → χ y = 1)} ∩ ball x δ,
      inter_mem_nhdsWithin _ (ball_mem_nhds x hδ), ?_⟩
    rw [ae_restrict_iff' measurableSet_ball, ae_iff] at hc
    refine measure_mono_null (fun z hz => ?_) hc
    simp only [mem_setOf_eq, Classical.not_imp] at hz ⊢
    exact ⟨hz.2, hz.1.2⟩
  · right
    rw [EventuallyEq, ae_restrict_iff' hUo.measurableSet, ae_iff]
    refine measure_null_of_locally_null _ fun x hx => ?_
    simp only [mem_setOf_eq, Classical.not_imp] at hx
    obtain ⟨δ, hδ, -, hc⟩ := hQ hx.1
    refine ⟨{y | ¬(y ∈ U → χ y = posIndicator u y)} ∩ ball x δ,
      inter_mem_nhdsWithin _ (ball_mem_nhds x hδ), ?_⟩
    rw [ae_restrict_iff' measurableSet_ball, ae_iff] at hc
    refine measure_mono_null (fun z hz => ?_) hc
    simp only [mem_setOf_eq, Classical.not_imp] at hz ⊢
    exact ⟨hz.2, hz.1.2⟩

end Singular

end InnerVariational
