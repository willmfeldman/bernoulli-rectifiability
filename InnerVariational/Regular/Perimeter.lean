/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Regular.Density
import InnerVariational.Registry.GMT
import InnerVariational.Regular.ChiInterior
import InnerVariational.Monotonicity.HighestDensity
public import InnerVariational.Defs.HighestDensity
import InnerVariational.Monotonicity.Density
import InnerVariational.Kernel.BV
import InnerVariational.Kernel.Subharmonic
public import InnerVariational.Defs.VariationalSolution
import InnerVariational.Basic.Polar
public import GMTFoundations.Defs.GMT

/-!
# The regular free boundary has locally finite perimeter (Lemma 8.2)

Lemma 8.2 of D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and
compactness for non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025),
no. 3, DOI 10.1002/cpa.22226; arXiv:2306.10131 (numbering of arXiv v2). Let `(u, χ)` be a
variational solution on a connected open set `Ω` with `Σ^H = ∅` and `2 ≤ n`. Then

* either `u ≡ 0` (and then `χ = 1` a.e.), or `χ = χ_{u>0}` a.e. on `Ω`
  (`eq_zero_or_ae_chi_eq_posIndicator`);
* `{u > 0}` has locally finite perimeter in `Ω` (`hasLocallyFinitePerimeter_pos`);
* `ℋ^{n-1}(∂{u > 0} ∩ B_r(x)) ≤ C(C_V) r^{n-1}` whenever `B̄_{2r}(x) ⊆ Ω`
  (`hausdorffN_frontier_pos_inter_ball_le`, with `C = 2^{n+1} |B_1| C_V²`).

Only the dichotomy uses connectedness. The perimeter bound and `|∂{u > 0} ∩ Ω| = 0` are local.

## Localization to `Ω \ Σ^H`

For applying Lemma 8.3 (variational solutions are viscosity solutions off `Σ^H`) on
`Ω' = Ω \ Σ^H`:

* `IsVariationalSolution.sigmaH_eq_inter_of_subset`: `Σ^H(Ω') = Σ^H(Ω) ∩ Ω'` for open `Ω' ⊆ Ω`;
* `IsVariationalSolution.isOpen_diff_sigmaH`: `Ω \ Σ^H` is open (`Σ^H` is relatively closed);
* `IsVariationalSolution.diff_sigmaH`, `IsVariationalSolution.sigmaH_diff_sigmaH_eq_empty`:
  `(u, χ)` is a variational solution on `Ω \ Σ^H`, and its `Σ^H` there is empty.

## Proof

The paper's proof argues: `χ = χ_{u>0}` off `∂{u > 0}` ("as discussed at the start of
this section"); on `∂{u > 0} ∩ Ω` the density `M_x(0+)/|B_1|` of `{χ = 1}` lies in `[1/2, 1)` by
Lemma 8.1 and `Σ^H = ∅`, so `∂{u > 0} ∩ Ω ⊆ ∂ᵉ{χ = 1}`, and Lemma 3.3 with Federer's
`|Dχ_E| = ℋ^{n-1}⌊∂ᵉE` (H. Federer, *Geometric Measure Theory*, Springer, 1969, 4.5.6 and
4.5.11; the BV structure theorem, L. C. Evans and R. F. Gariepy, *Measure Theory and Fine
Properties of Functions*, rev. ed., CRC Press, 2015, §5.7–5.8; both proved in gmt-foundations,
https://github.com/willmfeldman/gmt-foundations, v0.1.0) bounds its measure.

* The "start of the section" step (§8.1): the set `A` of points near which `u = 0` and
  `χ = 1` a.e. is open, and relatively closed in `Ω`: at `x ∈ closure A ∩ Ω` upper
  semicontinuity gives `M_x(0+) ≥ |B_1|`, so `x ∉ closure {u > 0}` (as `Σ^H = ∅`), so `u = 0` near
  `x`, where `χ` is constant (`Regular/ChiInterior.lean`) and hence `1`. If `A = Ω` then
  `u ≡ 0`; if `A = ∅` then `χ = 0` a.e. on `Ω \ closure {u > 0}`.
* `|∂{u > 0} ∩ Ω| = 0`: we use the Lebesgue density theorem (densities are `0` or `1` a.e.)
  instead of the paper's `ℋ^{n-1}`-finiteness, which would need the comparison of `ℋ^n` with
  Lebesgue measure.
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

namespace Regular

/-- **Lebesgue density theorem** in the form of `HasDensity`: for measurable `E`, a.e. point has
density `1_E(x)`. From `Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet`, with closed
balls replaced by open ones (`|∂B_r(x)| = 0`). -/
theorem ae_hasDensity_indicator {E : Set (Rn n)} (hE : MeasurableSet E) :
    ∀ᵐ x, HasDensity E x (E.indicator 1 x) := by
  filter_upwards [Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet volume hE] with x hx
  unfold HasDensity
  have hfin : E.indicator (1 : Rn n → ℝ≥0∞) x ≠ ⊤ := by
    by_cases hxE : x ∈ E <;> simp [hxE]
  have hval : (E.indicator (1 : Rn n → ℝ≥0∞) x).toReal = E.indicator (1 : Rn n → ℝ) x := by
    by_cases hxE : x ∈ E <;> simp [hxE]
  have h1 := (ENNReal.tendsto_toReal hfin).comp hx
  rw [hval] at h1
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  have hcb : volume (closedBall x r) = volume (ball x r) := by
    rw [Measure.addHaar_closedBall _ _ hr.le, Measure.addHaar_ball_of_pos _ _ hr]
  have hdiff : volume (closedBall x r \ ball x r) = 0 := by
    rw [measure_diff ball_subset_closedBall measurableSet_ball.nullMeasurableSet
      measure_ball_lt_top.ne, hcb, tsub_self]
  have hEcb : volume (E ∩ closedBall x r) = volume (E ∩ ball x r) := by
    refine le_antisymm ?_ (measure_mono (inter_subset_inter_right _ ball_subset_closedBall))
    calc volume (E ∩ closedBall x r) ≤ volume ((E ∩ ball x r) ∪ (closedBall x r \ ball x r)) := by
          refine measure_mono fun y hy => ?_
          by_cases hyb : y ∈ ball x r
          · exact Or.inl ⟨hy.1, hyb⟩
          · exact Or.inr ⟨hy.2, hyb⟩
      _ ≤ volume (E ∩ ball x r) + volume (closedBall x r \ ball x r) := measure_union_le _ _
      _ = volume (E ∩ ball x r) := by rw [hdiff, add_zero]
  simp only [Function.comp_apply]
  rw [hEcb, hcb, ENNReal.toReal_div]

end Regular

namespace IsVariationalSolution

variable {Ω : Set (Rn n)} {C : ℝ≥0} {u χ : Rn n → ℝ} {x : Rn n}

/-! ### Localization to `Ω \ Σ^H` -/

/-- `Σ^H` is local: for open `Ω' ⊆ Ω`, `Σ^H(Ω') = Σ^H(Ω) ∩ Ω'` (from the density
characterization `mem_sigmaH_iff_tendsto_volume`). -/
theorem sigmaH_eq_inter_of_subset [NeZero n] (h : IsVariationalSolution Ω C u χ)
    {Ω' : Set (Rn n)} (hΩ' : IsOpen Ω') (hsub : Ω' ⊆ Ω) :
    sigmaH Ω' u χ = sigmaH Ω u χ ∩ Ω' := by
  ext y
  rw [(h.mono hΩ' hsub).mem_sigmaH_iff_tendsto_volume, mem_inter_iff,
    h.mem_sigmaH_iff_tendsto_volume]
  constructor
  · rintro ⟨hy, hcl, huy, hlim⟩
    exact ⟨⟨hsub hy, hcl, huy, hlim⟩, hy⟩
  · rintro ⟨⟨-, hcl, huy, hlim⟩, hy⟩
    exact ⟨hy, hcl, huy, hlim⟩

/-- `Ω \ Σ^H` is open (start of §8.1: `Σ^H` is relatively closed, by upper semicontinuity of
`x ↦ M_x(u; 0+)`). -/
theorem isOpen_diff_sigmaH [NeZero n] (h : IsVariationalSolution Ω C u χ) :
    IsOpen (Ω \ sigmaH Ω u χ) := by
  have e : Ω \ sigmaH Ω u χ = Ω ∩ (closure (sigmaH Ω u χ))ᶜ := by
    ext y
    constructor
    · rintro ⟨hy, hyS⟩
      exact ⟨hy, fun hcl => hyS (h.closure_sigmaH_inter_subset ⟨hcl, hy⟩)⟩
    · rintro ⟨hy, hyc⟩
      exact ⟨hy, fun hyS => hyc (subset_closure hyS)⟩
  rw [e]
  exact h.isOpen.inter isClosed_closure.isOpen_compl

/-- `(u, χ)` is a variational solution on `Ω \ Σ^H`. -/
theorem diff_sigmaH [NeZero n] (h : IsVariationalSolution Ω C u χ) :
    IsVariationalSolution (Ω \ sigmaH Ω u χ) C u χ :=
  h.mono h.isOpen_diff_sigmaH diff_subset

/-- On `Ω' = Ω \ Σ^H`, the set of highest density is empty. So the results below (and
Lemma 8.3) apply on `Ω'`. -/
theorem sigmaH_diff_sigmaH_eq_empty [NeZero n] (h : IsVariationalSolution Ω C u χ) :
    sigmaH (Ω \ sigmaH Ω u χ) u χ = ∅ := by
  rw [h.sigmaH_eq_inter_of_subset h.isOpen_diff_sigmaH diff_subset]
  exact inter_diff_self _ _

/-! ### Densities on the free boundary -/

/-- A point of `Ω` outside `closure {u > 0}` has a ball in `Ω` on which `u = 0`. -/
theorem exists_ball_eq_zero (h : IsVariationalSolution Ω C u χ) (hx : x ∈ Ω)
    (hncl : x ∉ closure {y | 0 < u y}) :
    ∃ δ > 0, ball x δ ⊆ Ω ∧ ∀ y ∈ ball x δ, u y = 0 := by
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.1
    (inter_mem (isClosed_closure.isOpen_compl.mem_nhds hncl) (h.isOpen.mem_nhds hx))
  refine ⟨δ, hδ, fun y hy => (hδsub hy).2, fun y hy => ?_⟩
  exact le_antisymm (not_lt.1 fun hp => (hδsub hy).1 (subset_closure hp))
    (h.nonneg y (hδsub hy).2)

/-- On `∂{u > 0} ∩ Ω`, if `Σ^H = ∅`, then `{χ = 1}` has a density `d ∈ [1/2, 1)` (proof of
Lemma 8.2):
`d = M_x(0+)/|B_1|` with `M_x(0+) ∈ [|B_1|/2, |B_1|)` by Lemma 8.1 and `x ∉ Σ^H`. -/
theorem exists_hasDensity_of_mem_frontier [NeZero n] (hn : 2 ≤ n)
    (h : IsVariationalSolution Ω C u χ) (hS : sigmaH Ω u χ = ∅)
    (hx : x ∈ Ω ∩ frontier {y | 0 < u y}) :
    ∃ d : ℝ, HasDensity (Ω ∩ {y | χ y = 1}) x d ∧ 1 / 2 ≤ d ∧ d < 1 := by
  obtain ⟨hxΩ, hfr⟩ := hx
  obtain ⟨hcl, hux⟩ := (h.mem_frontier_pos_iff hxΩ).1 hfr
  obtain ⟨m, hmM, hhalf, hle⟩ := h.half_le_Mzero_of_mem_frontier hn hxΩ hfr
  obtain ⟨m', hm'M, -, hd⟩ := h.tendsto_monotonicityM_zero hxΩ hux
  have hmm : m' = m := by rw [hmM] at hm'M; exact_mod_cast hm'M.symm
  obtain ⟨ε, hε, hεΩ⟩ := Metric.isOpen_iff.1 h.isOpen x hxΩ
  have hB := unitBallVolume_pos n
  refine ⟨m / unitBallVolume n, by rw [← hmm]; exact h.hasDensity_of_tendsto hε hεΩ hd, ?_, ?_⟩
  · rw [le_div_iff₀ hB]; linarith
  · rw [div_lt_one hB]
    refine lt_of_le_of_ne hle fun heq => ?_
    exact eq_empty_iff_forall_notMem.1 hS x
      (h.mem_sigmaH_iff_le_Mzero.2 ⟨hxΩ, hcl, le_of_eq (by rw [hmM, heq])⟩)

/-- `∂{u > 0} ∩ Ω ⊆ ∂ᵉ{χ = 1}` when `Σ^H = ∅` (proof of Lemma 8.2). -/
theorem frontier_pos_inter_subset_essentialBoundary [NeZero n] (hn : 2 ≤ n)
    (h : IsVariationalSolution Ω C u χ) (hS : sigmaH Ω u χ = ∅) :
    Ω ∩ frontier {y | 0 < u y} ⊆ essentialBoundary (Ω ∩ {y | χ y = 1}) := fun y hy => by
  obtain ⟨d, hd, hd1, hd2⟩ := h.exists_hasDensity_of_mem_frontier hn hS hy
  exact ⟨fun h0 => by have := tendsto_nhds_unique hd h0; linarith,
    fun h1 => by have := tendsto_nhds_unique hd h1; linarith⟩

/-- `|∂{u > 0} ∩ Ω| = 0` when `Σ^H = ∅` (proof of Lemma 8.2), by the Lebesgue density theorem. -/
theorem volume_inter_frontier_pos_eq_zero [NeZero n] (hn : 2 ≤ n)
    (h : IsVariationalSolution Ω C u χ) (hS : sigmaH Ω u χ = ∅) :
    volume (Ω ∩ frontier {y | 0 < u y}) = 0 := by
  set E : Set (Rn n) := Ω ∩ {y | χ y = 1} with hEdef
  refine measure_mono_null (t := {y | ¬ HasDensity E y (E.indicator 1 y)}) (fun y hy hy' => ?_)
    (ae_iff.1 (Regular.ae_hasDensity_indicator h.measurableSet_chi_eq_one))
  obtain ⟨d, hd, hd1, hd2⟩ := h.exists_hasDensity_of_mem_frontier hn hS hy
  have := tendsto_nhds_unique hd hy'
  by_cases hyE : y ∈ E
  · rw [indicator_of_mem hyE, Pi.one_apply] at this; linarith
  · rw [indicator_of_notMem hyE] at this; linarith

/-! ### Lemma 8.2 -/

/-- **Lemma 8.2**, dichotomy. On a connected open `Ω` with
`Σ^H = ∅`: either `u ≡ 0` and `χ = 1` a.e., or `χ = χ_{u>0}` a.e. on `Ω`. (If `u ≡ 0` and `χ = 0`
a.e., the second alternative holds.) -/
theorem eq_zero_or_ae_chi_eq_posIndicator [NeZero n] (hn : 2 ≤ n)
    (h : IsVariationalSolution Ω C u χ) (hΩc : IsPreconnected Ω) (hS : sigmaH Ω u χ = ∅) :
    ((∀ y ∈ Ω, u y = 0) ∧ ∀ᵐ y ∂(volume.restrict Ω), χ y = 1) ∨
      ∀ᵐ y ∂(volume.restrict Ω), χ y = posIndicator u y := by
  set A : Set (Rn n) := {x | ∃ δ > 0, ball x δ ⊆ Ω ∧ (∀ y ∈ ball x δ, u y = 0) ∧
    ∀ᵐ y ∂(volume.restrict (ball x δ)), χ y = 1} with hAdef
  have hAopen : IsOpen A := by
    rw [Metric.isOpen_iff]
    rintro x ⟨δ, hδ, hδΩ, hu, hc⟩
    refine ⟨δ, hδ, fun z hz => ?_⟩
    have hsub : ball z (δ - dist z x) ⊆ ball x δ := fun w hw => by
      rw [mem_ball] at hw ⊢
      linarith [dist_triangle w z x]
    exact ⟨δ - dist z x, sub_pos.2 hz, hsub.trans hδΩ, fun y hy => hu y (hsub hy),
      ae_restrict_of_ae_restrict_of_subset hsub hc⟩
  have hAM : ∀ x ∈ A, Mzero u χ x = unitBallVolume n := by
    rintro x ⟨δ, hδ, hδΩ, hu, hc⟩
    rw [h.Mzero_eq_of_ae_eq_const (hδΩ (mem_ball_self hδ)) (hu x (mem_ball_self hδ)) hδ hc,
      one_mul]
  -- `A` is relatively closed in `Ω`
  have hkey : ∀ x ∈ Ω, x ∈ closure A → x ∈ A := by
    intro x hx hcl
    have hM : (unitBallVolume n : EReal) ≤ Mzero u χ x := by
      by_contra hlt
      rw [not_le] at hlt
      have hev := h.upperSemicontinuousOn_Mzero x hx _ hlt
      rw [h.isOpen.nhdsWithin_eq hx] at hev
      obtain ⟨y, hyA, hy⟩ := ((mem_closure_iff_frequently.1 hcl).and_eventually hev).exists
      rw [hAM y hyA] at hy
      exact lt_irrefl _ hy
    have hncl : x ∉ closure {y | 0 < u y} := fun hc =>
      eq_empty_iff_forall_notMem.1 hS x (h.mem_sigmaH_iff_le_Mzero.2 ⟨hx, hc, hM⟩)
    obtain ⟨δ, hδ, hδΩ, hu0⟩ := h.exists_ball_eq_zero hx hncl
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
  have hcover : Ω ⊆ A ∪ (closure A)ᶜ := fun x hx => by
    by_cases hcl : x ∈ closure A
    · exact Or.inl (hkey x hx hcl)
    · exact Or.inr hcl
  have hdisj : Ω ∩ (A ∩ (closure A)ᶜ) = ∅ :=
    eq_empty_iff_forall_notMem.2 fun x ⟨_, hxA, hxc⟩ => hxc (subset_closure hxA)
  rcases isPreconnected_iff_subset_of_disjoint.1 hΩc A (closure A)ᶜ hAopen
    isClosed_closure.isOpen_compl hcover hdisj with hsub | hsub
  · -- `A = Ω`: `u ≡ 0` and `χ = 1` a.e.
    left
    refine ⟨fun x hx => ?_, ?_⟩
    · obtain ⟨δ, hδ, -, hu, -⟩ := hsub hx
      exact hu x (mem_ball_self hδ)
    · rw [ae_restrict_iff' h.isOpen.measurableSet, ae_iff]
      refine measure_mono_null (t := Ω ∩ {y | χ y ≠ 1}) (fun y hy => ?_) ?_
      · simp only [mem_setOf_eq, Classical.not_imp] at hy
        exact hy
      · refine measure_null_of_locally_null _ fun y hy => ?_
        obtain ⟨δ, hδ, -, -, hc⟩ := hsub hy.1
        refine ⟨Ω ∩ {y | χ y ≠ 1} ∩ ball y δ, inter_mem_nhdsWithin _ (ball_mem_nhds y hδ), ?_⟩
        rw [ae_restrict_iff' measurableSet_ball, ae_iff] at hc
        refine measure_mono_null (fun z hz => ?_) hc
        simp only [mem_setOf_eq, Classical.not_imp]
        exact ⟨hz.2, hz.1.2⟩
  · -- `A = ∅`: `χ = χ_{u>0}` a.e.
    right
    have hA : ∀ x ∈ Ω, x ∉ A := fun x hx hxA => hsub hx (subset_closure hxA)
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
          exact absurd ⟨δ, hδ, hδΩ, hu0, hc⟩ (hA x hxΩ)
      subst hc0
      refine ⟨{y | ¬(y ∈ Ω → y ∉ closure {y | 0 < u y} → χ y = 0)} ∩ ball x δ,
        inter_mem_nhdsWithin _ (ball_mem_nhds x hδ), ?_⟩
      rw [ae_restrict_iff' measurableSet_ball, ae_iff] at hc
      refine measure_mono_null (fun z hz => ?_) hc
      simp only [mem_setOf_eq, Classical.not_imp] at hz ⊢
      exact ⟨hz.2, hz.1.2.2⟩
    have hF := h.volume_inter_frontier_pos_eq_zero hn hS
    rw [ae_restrict_iff' h.isOpen.measurableSet]
    filter_upwards [h.ae_chi_eq_one, hG, measure_eq_zero_iff_ae_notMem.1 hF] with y h1 h2 h3 hyΩ
    rcases (h.nonneg y hyΩ).lt_or_eq with hpos | hzero
    · rw [h1 hyΩ hpos, posIndicator_of_pos hpos]
    · have hncl : y ∉ closure {y | 0 < u y} := fun hcl =>
        h3 ⟨hyΩ, (h.mem_frontier_pos_iff hyΩ).2 ⟨hcl, hzero.symm⟩⟩
      rw [h2 hyΩ hncl, posIndicator_of_nonpos hzero.symm.le]

/-- **Lemma 3.3 as a perimeter measure** (with the BV structure theorem): `{χ = 1}` has a
Gauss–Green pair on
`B_{3r/2}(x)` with total mass `≤ 2^{n+1} |B_1| C_V² r^{n-1}` when `B̄_{2r}(x) ⊆ Ω`. -/
theorem exists_isGaussGreenPair_chi [NeZero n] (hn : 2 ≤ n) (h : IsVariationalSolution Ω C u χ)
    {r : ℝ} (hr : 0 < r) (hball : closedBall x (2 * r) ⊆ Ω) :
    ∃ μ ν, IsGaussGreenPair (ball x (3 * r / 2)) (Ω ∩ {y | χ y = 1}) μ ν ∧
      μ (ball x (3 * r / 2)) ≤
        ENNReal.ofReal (2 ^ (n + 1) * volume.real (ball (0 : Rn n) 1) * C ^ 2 * r ^ (n - 1)) :=
  Registry.exists_isGaussGreenPair_of_integral_divergence_le hn isOpen_ball
    h.measurableSet_chi_eq_one _ fun φ hφ =>
      (h.abs_setIntegral_divergence_le hr hball hφ).trans_eq (by ring)

/-- **Lemma 8.2**, perimeter bound. If `Σ^H = ∅` and
`B̄_{2r}(x) ⊆ Ω`, then `ℋ^{n-1}(∂{u > 0} ∩ B_r(x)) ≤ 2^{n+1} |B_1| C_V² r^{n-1}`. Connectedness
of `Ω` is not needed. -/
theorem hausdorffN_frontier_pos_inter_ball_le [NeZero n] (hn : 2 ≤ n)
    (h : IsVariationalSolution Ω C u χ) (hS : sigmaH Ω u χ = ∅) {r : ℝ} (hr : 0 < r)
    (hball : closedBall x (2 * r) ⊆ Ω) :
    hausdorffN n (n - 1) (frontier {y | 0 < u y} ∩ ball x r) ≤
      ENNReal.ofReal (2 ^ (n + 1) * volume.real (ball (0 : Rn n) 1) * C ^ 2 * r ^ (n - 1)) := by
  obtain ⟨μ, ν, hpair, hμ⟩ := h.exists_isGaussGreenPair_chi hn hr hball
  have hμeq := Registry.IsGaussGreenPair.eq_hausdorffN_restrict hn isOpen_ball
    h.measurableSet_chi_eq_one hpair
  have hsub : frontier {y | 0 < u y} ∩ ball x r ⊆ ball x (3 * r / 2) ∩
      (ball x (3 * r / 2) ∩ essentialBoundary (Ω ∩ {y | χ y = 1})) := by
    rintro y ⟨hyf, hyr⟩
    have hyU : y ∈ ball x (3 * r / 2) := ball_subset_ball (by linarith) hyr
    have hyΩ : y ∈ Ω :=
      hball ((ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))) hyr)
    exact ⟨hyU, hyU, h.frontier_pos_inter_subset_essentialBoundary hn hS ⟨hyΩ, hyf⟩⟩
  calc hausdorffN n (n - 1) (frontier {y | 0 < u y} ∩ ball x r)
      ≤ hausdorffN n (n - 1) (ball x (3 * r / 2) ∩
          (ball x (3 * r / 2) ∩ essentialBoundary (Ω ∩ {y | χ y = 1}))) := measure_mono hsub
    _ = μ (ball x (3 * r / 2)) := by rw [hμeq, Measure.restrict_apply isOpen_ball.measurableSet]
    _ ≤ _ := hμ

/-- **Lemma 8.2**, locally finite perimeter. If
`χ = χ_{u>0}` a.e. on `Ω` (the second alternative of the dichotomy), then `Ω ∩ {u > 0}` has a
Gauss–Green pair on every `B_{3r/2}(x)` with `B̄_{2r}(x) ⊆ Ω`. -/
theorem hasLocallyFinitePerimeter_pos [NeZero n] (hn : 2 ≤ n) (h : IsVariationalSolution Ω C u χ)
    (hae : ∀ᵐ y ∂(volume.restrict Ω), χ y = posIndicator u y) {r : ℝ} (hr : 0 < r)
    (hball : closedBall x (2 * r) ⊆ Ω) :
    HasLocallyFinitePerimeter (ball x (3 * r / 2)) (Ω ∩ {y | 0 < u y}) := by
  obtain ⟨μ, ν, hpair, -⟩ := h.exists_isGaussGreenPair_chi hn hr hball
  have hset : (Ω ∩ {y | 0 < u y} : Set (Rn n)) =ᵐ[volume] (Ω ∩ {y | χ y = 1} : Set (Rn n)) := by
    rw [ae_restrict_iff' h.isOpen.measurableSet] at hae
    filter_upwards [hae] with y hy
    refine propext ⟨fun hy' => ?_, fun hy' => ?_⟩
    · have := hy hy'.1
      rw [posIndicator_of_pos hy'.2] at this
      exact ⟨hy'.1, this⟩
    · refine ⟨hy'.1, ?_⟩
      by_contra hp
      have := hy hy'.1
      rw [posIndicator_of_nonpos (not_lt.1 hp), hy'.2] at this
      exact one_ne_zero this
  exact ⟨μ, ν, { hpair with
    integral_divergence := fun φ hφ => by
      rw [setIntegral_congr_set hset]
      exact hpair.integral_divergence φ hφ }⟩

end IsVariationalSolution

end InnerVariational
