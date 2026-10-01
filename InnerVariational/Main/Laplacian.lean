/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Main.LaplacianDensity
public import InnerVariational.Main.Distributional
public import InnerVariational.Singular.Chi
public import InnerVariational.Regular.Laplacian
import InnerVariational.Main.Covering
import InnerVariational.Main.RieszMeasure
public import InnerVariational.Defs.LaplacianMeasure
import InnerVariational.Singular.Density
import InnerVariational.NaberValtorta.Hausdorff
import InnerVariational.Regular.Perimeter
import InnerVariational.Registry.GMT
import InnerVariational.Defs.GMT
import InnerVariational.Kernel.BV
import InnerVariational.Kernel.Subharmonic
public import InnerVariational.Defs.VariationalSolution

/-!
# Theorem 8.7: the Laplacian of a variational solution

Theorem 8.7 of D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and
compactness for non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025),
no. 3, DOI 10.1002/cpa.22226; arXiv:2306.10131 (numbering of arXiv v2). For a variational
solution `(u, χ)` on an open `Ω` (no connectedness), in the sense of distributions on `Ω`,

  `Δu = ℋ^{n-1}⌊∂*{u > 0} + 2 α(n) √(H_x(u; 0+)) ℋ^{n-1}⌊Σ^H`

(`hasDistribLaplacianOn_laplacianMeasure`, and `laplacian_measure_eq` with exactly the
statement of `Statements.laplacian_measure_eq`).

## Proof

Let `ρ = Δu`, a measure on `Ω` (`exists_hasDistribLaplacianOn`), `Ω' = Ω \ Σ^H`,
`E = Ω ∩ {u > 0}`, `ℋ = ℋ^{n-1}`. Since `Ω = Ω' ⊔ Σ^H`, `ρ = ρ⌊Ω' + ρ⌊Σ^H`.

* **Off `Σ^H`** (Corollary 8.4, in the form
  `IsVariationalSolution.laplacian_eq_of_sigmaH_empty`): on `Ω'`, `Σ^H(Ω') = ∅`, so
  `Δu = ℋ⌊∂*_{Ω'}{u > 0}` on `Ω'`. By uniqueness of the Laplacian measure
  (`HasDistribLaplacianOn.eq`), `ρ⌊Ω' = ℋ⌊∂*_{Ω'}{u > 0}`.
* **Reduced boundaries** (`reducedBoundary_pos_ae_eq`). `E` has locally finite perimeter in every
  open `U ⊆ Ω` (Lemma 3.3 and Theorem 8.6 on balls, and the local form of the `BV` structure
  theorem; no connectedness), so by the De Giorgi–Federer structure theorem (H. Federer,
  *Geometric Measure Theory*, Springer, 1969, 4.5.6)
  `∂*_U{u > 0} = U ∩ ∂ᵉE` up to `ℋ`-null sets. Densities are local, and
  `ℋ(Σ^H ∩ ∂ᵉE) = 0` (Lemma 8.5 (2): `{u > 0}` has density `1` a.e. on `Σ^H`), so
  `ℋ⌊∂*_{Ω'}{u > 0} = ℋ⌊∂*_Ω{u > 0}`. The argument uses `ℋ(∂*{u > 0} ∩ Σ^H) = 0`, which
  follows from Lemma 8.5 (2) and is proved here
  (`hausdorffN_sigmaH_inter_essentialBoundary_eq_zero`).
* **On `Σ^H`**. `ρ` lives on `S = (Ω ∩ ∂{u > 0}) ∪ Σ^H`, which is Borel, rectifiable and locally
  `ℋ`-finite (Theorem 8.7, first part), and `ρ(B_r(x)) ≤ K r^{n-1}`
  (`Main/LaplacianDensity.lean`). The density theorem for measures absolutely continuous with
  respect to `ℋ⌊S` (Federer 2.10.19 and 3.2.19; proved in gmt-foundations,
  https://github.com/willmfeldman/gmt-foundations, v0.1.0) gives `ρ = θ ℋ⌊S` with `θ` the upper
  `(n-1)`-density of `ρ`, and `θ = 2α√(H(0+))` `ℋ`-a.e. on `Σ^H` (`Main/LaplacianDensity.lean`).
  Hence `ρ⌊Σ^H = 2α√(H(0+)) ℋ⌊Σ^H`.
-/

open MeasureTheory Metric Set Filter Topology Laplacian
open scoped NNReal ENNReal

@[expose] public noncomputable section

namespace InnerVariational.Main

variable {n : ℕ} {Ω : Set (Rn n)} {C : ℝ≥0} {u χ : Rn n → ℝ}

/-! ### The positivity set has locally finite perimeter -/

/-- **`Ω ∩ {u > 0}` has locally finite perimeter in `Ω`** (a Gauss–Green pair on all of `Ω`). On a
ball `B ⊆ Ω`, Theorem 8.6 (`Singular.chi_eq_indicator`, applied on the connected `B`) gives either
`u ≡ 0` on `B` or `χ = χ_{u>0}` a.e. on `B`; in both cases Lemma 3.3 bounds `∫_E div φ` for
`φ ∈ C^∞_c(B)`, and the local form of the `BV` structure theorem
(`Registry.hasLocallyFinitePerimeter_of_local`) globalizes. Connectedness of `Ω` is not
needed. -/
theorem hasLocallyFinitePerimeter_inter_pos (hn : 2 ≤ n) (h : IsVariationalSolution Ω C u χ) :
    HasLocallyFinitePerimeter Ω (Ω ∩ {y | 0 < u y}) := by
  have : NeZero n := ⟨by omega⟩
  refine Registry.hasLocallyFinitePerimeter_of_local hn h.isOpen h.isOpen_pos.measurableSet
    fun x hx => ?_
  obtain ⟨r, hr, h2r⟩ := exists_closedBall_two_mul_subset h.isOpen hx
  have hBΩ : ball x r ⊆ Ω := ball_subset_closedBall.trans
    ((closedBall_subset_closedBall (by linarith)).trans h2r)
  set K := 2 ^ (n + 1) * volume.real (ball (0 : Rn n) 1) * (C : ℝ) ^ 2 * r ^ (n - 1) with hKdef
  have hK0 : 0 ≤ K := by positivity
  refine ⟨r, hr, hBΩ, K, fun φ hφ => ?_⟩
  have hsup : 0 ≤ ⨆ y, ‖φ y‖ := Real.iSup_nonneg fun y => norm_nonneg _
  have hz : ∀ y ∉ ball x r, divergence φ y = 0 := fun y hy =>
    divergence_eq_zero_of_notMem_tsupport fun h' => hy (hφ.2.2 h')
  have hloc : ∫ y in Ω ∩ {y | 0 < u y}, divergence φ y =
      ∫ y in ball x r ∩ (Ω ∩ {y | 0 < u y}), divergence φ y :=
    setIntegral_eq_setIntegral_inter_of_eq_zero measurableSet_ball hz
  rcases Singular.chi_eq_indicator hn ((convex_ball x r).isConnected (nonempty_ball.2 hr))
    (h.mono isOpen_ball hBΩ) with hu0 | hae
  · have hempty : ball x r ∩ (Ω ∩ {y | 0 < u y}) = ∅ := eq_empty_of_forall_notMem
      fun y hy => (ne_of_gt (show 0 < u y from hy.2.2)) (hu0 y hy.1)
    rw [hloc, hempty, Measure.restrict_empty, integral_zero_measure, abs_zero]
    exact mul_nonneg hK0 hsup
  · have hset : (ball x r ∩ (Ω ∩ {y | 0 < u y}) : Set (Rn n)) =ᵐ[volume]
        (ball x r ∩ (Ω ∩ {y | χ y = 1}) : Set (Rn n)) := by
      filter_upwards [(ae_restrict_iff' measurableSet_ball).1 hae] with y hy
      refine propext ⟨fun hy' => ⟨hy'.1, hy'.2.1, ?_⟩, fun hy' => ⟨hy'.1, hy'.2.1, ?_⟩⟩
      · rw [mem_ofPred_eq, hy hy'.1, posIndicator_of_pos hy'.2.2]
      · have h1 := hy'.2.2
        rw [mem_ofPred_eq, hy hy'.1] at h1
        by_contra hp
        rw [posIndicator_of_nonpos (not_lt.1 hp)] at h1
        exact zero_ne_one h1
    have hloc' : ∫ y in Ω ∩ {y | χ y = 1}, divergence φ y =
        ∫ y in ball x r ∩ (Ω ∩ {y | χ y = 1}), divergence φ y :=
      setIntegral_eq_setIntegral_inter_of_eq_zero measurableSet_ball hz
    rw [hloc, setIntegral_congr_set hset, ← hloc']
    have hφ' : IsSmoothTestField (ball x (3 * r / 2)) φ :=
      ⟨hφ.1, hφ.2.1, hφ.2.2.trans (ball_subset_ball (by linarith))⟩
    refine (h.abs_setIntegral_divergence_le hr h2r hφ').trans (le_of_eq ?_)
    rw [hKdef]
    ring

/-- **De Giorgi–Federer for `{u > 0}`**: `∂*_Ω{u > 0} = Ω ∩ ∂ᵉ(Ω ∩ {u > 0})` up to an
`ℋ^{n-1}`-null set. -/
theorem reducedBoundary_pos_ae_eq (hn : 2 ≤ n) (h : IsVariationalSolution Ω C u χ) :
    (reducedBoundary Ω {y | 0 < u y} : Set (Rn n)) =ᵐ[hausdorffN n (n - 1)]
      (Ω ∩ essentialBoundary (Ω ∩ {y | 0 < u y}) : Set (Rn n)) := by
  have hEm : MeasurableSet (Ω ∩ {y | 0 < u y}) := h.isOpen_pos.measurableSet
  obtain ⟨-, hnull, hsub⟩ := Registry.HasLocallyFinitePerimeter.rectifiable_essentialBoundary hn
    h.isOpen hEm (hasLocallyFinitePerimeter_inter_pos hn h)
  have hEE : (Ω ∩ (Ω ∩ {y | 0 < u y}) : Set (Rn n)) =ᵐ[volume] (Ω ∩ {y | 0 < u y} : Set (Rn n)) :=
    Filter.EventuallyEq.of_eq (by rw [← inter_assoc, inter_self])
  have hR : reducedBoundary Ω (Ω ∩ {y | 0 < u y}) = reducedBoundary Ω {y | 0 < u y} :=
    Subset.antisymm (reducedBoundary_subset_of_ae_eq h.isOpen.measurableSet hEE)
      (reducedBoundary_subset_of_ae_eq h.isOpen.measurableSet hEE.symm)
  rw [hR] at hnull hsub
  have hsub' : reducedBoundary Ω {y | 0 < u y} ⊆ Ω ∩ essentialBoundary (Ω ∩ {y | 0 < u y}) :=
    fun y hy => ⟨reducedBoundary_subset _ _ hy, hsub hy⟩
  refine ae_eq_set.2 ⟨?_, hnull⟩
  rw [sdiff_eq_empty.2 hsub', measure_empty]

/-- Essential boundaries are local: on an open `U ⊆ Ω`, `U ∩ ∂ᵉ(U ∩ {u>0}) = U ∩ ∂ᵉ(Ω ∩ {u>0})`. -/
theorem inter_essentialBoundary_inter_pos {U : Set (Rn n)} (hU : IsOpen U) (hΩ : IsOpen Ω)
    (hUΩ : U ⊆ Ω) :
    U ∩ essentialBoundary (U ∩ {y | 0 < u y}) = U ∩ essentialBoundary (Ω ∩ {y | 0 < u y}) := by
  ext x
  refine and_congr_right fun hx => ?_
  have e : ∀ d, HasDensity (U ∩ {y | 0 < u y}) x d ↔ HasDensity (Ω ∩ {y | 0 < u y}) x d :=
    fun d => (Singular.hasDensity_inter_iff (hU.mem_nhds hx)).trans
      (Singular.hasDensity_inter_iff (hΩ.mem_nhds (hUΩ hx))).symm
  simp only [essentialBoundary, mem_ofPred_eq, e]

/-- `ℋ^{n-1}(Σ^H ∩ ∂ᵉ(Ω ∩ {u > 0})) = 0`: by Lemma 8.5 (2), `{u > 0}` has density `1` at
`ℋ^{n-1}`-a.e. point of `Σ^H`. Hence `ℋ^{n-1}(∂*{u > 0} ∩ Σ^H) = 0`, which the proof of Theorem 8.7
uses (so that the formula for `Δu` does not count `∂*{u > 0} ∩ Σ^H` twice). -/
theorem hausdorffN_sigmaH_inter_essentialBoundary_eq_zero [NeZero n] (hn : 2 ≤ n)
    (h : IsVariationalSolution Ω C u χ) :
    hausdorffN n (n - 1) (sigmaH Ω u χ ∩ essentialBoundary (Ω ∩ {y | 0 < u y})) = 0 := by
  refine measure_mono_null (?_ : _ ⊆ {x | x ∈ sigmaH Ω u χ ∧ ¬ HasDensity {y | 0 < u y} x 1})
    (Singular.density_pos_eq_one_ae hn h)
  intro x hx
  exact ⟨hx.1, fun hd => hx.2.2 ((Singular.hasDensity_inter_iff (h.isOpen.mem_nhds hx.1.1)).2 hd)⟩

/-! ### Theorem 8.7 -/

/-- The restriction of a Laplacian measure to an open subset is a Laplacian measure there. -/
theorem HasDistribLaplacianOn.restrict {U : Set (Rn n)} {ρ : Measure (Rn n)}
    (hρ : HasDistribLaplacianOn Ω u ρ) (hUΩ : U ⊆ Ω) :
    HasDistribLaplacianOn U u (ρ.restrict U) := by
  refine ⟨fun K hK hKU => (Measure.le_iff'.1 Measure.restrict_le_self K).trans_lt
    (hρ.1 K hK (hKU.trans hUΩ)), fun φ hφ => ?_⟩
  rw [hρ.2 φ ⟨hφ.1, hφ.2.1, hφ.2.2.trans hUΩ⟩]
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy =>
    image_eq_zero_of_notMem_tsupport fun h' => hy (hφ.2.2 h')).symm

/-- **Theorem 8.7**, the distributional identity:
`Δu = ℋ^{n-1}⌊∂*{u>0} + 2α(n)√(H_x(u;0+)) ℋ^{n-1}⌊Σ^H` in `Ω`. -/
theorem hasDistribLaplacianOn_laplacianMeasure [NeZero n] (hn : 2 ≤ n)
    (h : IsVariationalSolution Ω C u χ) :
    HasDistribLaplacianOn Ω u (laplacianMeasure Ω u χ) := by
  set ℋ := hausdorffN n (n - 1) with hℋ
  set SH := sigmaH Ω u χ with hSH
  set Ω' := Ω \ SH with hΩ'
  have h' : IsVariationalSolution Ω' C u χ := h.diff_sigmaH
  have hS' : sigmaH Ω' u χ = ∅ := h.sigmaH_diff_sigmaH_eq_empty
  have hΩ'o : IsOpen Ω' := h.isOpen_diff_sigmaH
  have hSHm : MeasurableSet SH := measurableSet_sigmaH hn h
  obtain ⟨ρ, hρΩ, hρ⟩ := exists_hasDistribLaplacianOn h.isOpen h.continuousOn h.weaklySubharmonic
  -- (1) off `Σ^H`: Corollary 8.4 on `Ω'` and uniqueness
  have h1 : ρ.restrict Ω' = ℋ.restrict (reducedBoundary Ω' {y | 0 < u y}) := by
    refine HasDistribLaplacianOn.eq hΩ'o (HasDistribLaplacianOn.restrict hρ sdiff_subset)
      (h'.laplacian_eq_of_sigmaH_empty hn hS') ?_ ?_
    · rw [Measure.restrict_apply hΩ'o.measurableSet.compl, compl_inter_self, measure_empty]
    · rw [Measure.restrict_apply hΩ'o.measurableSet.compl]
      exact measure_mono_null (fun y hy => hy.1 hy.2.1) measure_empty
  -- (2) on `Σ^H`: the density theorem, the upper bound and the density on `Σ^H`
  set S := (Ω ∩ frontier {y | 0 < u y}) ∪ SH with hSdef
  have hSm : MeasurableSet S :=
    (h.isOpen.measurableSet.inter isClosed_frontier.measurableSet).union hSHm
  have hSΩ : S ⊆ Ω := union_subset inter_subset_left (sigmaH_subset Ω u χ)
  have hrect : IsCountablyRectifiable n (n - 1) S :=
    NaberValtorta.IsCountablyRectifiable.union (isCountablyRectifiable_frontier_pos hn h)
      (isCountablyRectifiable_sigmaH hn h)
  have hfin : ∀ K, IsCompact K → K ⊆ Ω → ℋ (K ∩ S) < ⊤ := fun K hK hKΩ => by
    rw [inter_union_distrib_left]
    refine (measure_union_le _ _).trans_lt (ENNReal.add_lt_top.2 ⟨?_, ?_⟩)
    · exact (measure_mono (inter_subset_inter_right _ inter_subset_right)).trans_lt
        (hausdorffN_inter_frontier_pos_lt_top hn h hK hKΩ)
    · exact hausdorffN_inter_sigmaH_lt_top hn h hK hKΩ
  have hρS : ρ Sᶜ = 0 := by
    have hsub : Sᶜ ⊆ Ωᶜ ∪ (Sᶜ ∩ Ω') := fun y hy => by
      by_cases hyΩ : y ∈ Ω
      · exact Or.inr ⟨hy, hyΩ, fun hySH => hy (Or.inr hySH)⟩
      · exact Or.inl hyΩ
    refine measure_mono_null hsub (measure_union_null hρΩ ?_)
    rw [← Measure.restrict_apply hSm.compl, h1, Measure.restrict_apply hSm.compl]
    exact measure_mono_null (fun y hy => hy.1 (Or.inl
      ((reducedBoundary_pos_subset hn h').trans (inter_subset_inter_left _ sdiff_subset) hy.2)))
      measure_empty
  obtain ⟨K, hK⟩ := exists_measure_ball_le (by omega) h hρ
  have hR12 := Registry.eq_withDensity_upperDensity hn h.isOpen hSm hSΩ hrect hfin hρS K hK
  have hG7 := hausdorffN_not_tendsto_laplacian_density_eq_zero hn h hρ
  have h2 : ρ.restrict SH = (ℋ.restrict SH).withDensity
      (fun x => ENNReal.ofReal (2 * alphaN n * √(heightHZero u x))) := by
    conv_lhs => rw [hR12]
    rw [restrict_withDensity hSHm, Measure.restrict_restrict hSHm,
      inter_eq_left.2 (subset_union_right : SH ⊆ S)]
    refine withDensity_congr_ae ((ae_restrict_iff' hSHm).2 ?_)
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hG7] with x hx hxSH
    by_contra hne
    exact hx ⟨hxSH, fun ht => hne ht.limsup_eq⟩
  -- (3) the reduced boundaries of `{u > 0}` in `Ω'` and in `Ω` agree `ℋ`-a.e.
  have h3 : ℋ.restrict (reducedBoundary Ω' {y | 0 < u y}) =
      ℋ.restrict (reducedBoundary Ω {y | 0 < u y}) := by
    refine Measure.restrict_congr_set ?_
    have hA' := reducedBoundary_pos_ae_eq hn h'
    rw [inter_essentialBoundary_inter_pos hΩ'o h.isOpen sdiff_subset] at hA'
    refine hA'.trans (EventuallyEq.trans ?_ (reducedBoundary_pos_ae_eq hn h).symm)
    have hnull := hausdorffN_sigmaH_inter_essentialBoundary_eq_zero hn h
    set B := essentialBoundary (Ω ∩ {y | 0 < u y})
    have hsub1 : Ω' ∩ B ⊆ Ω ∩ B := fun y hy => ⟨hy.1.1, hy.2⟩
    have hsub2 : (Ω ∩ B) \ (Ω' ∩ B) ⊆ SH ∩ B := by
      rintro y ⟨⟨hyΩ, hyB⟩, hyn⟩
      by_contra hySH
      exact hyn ⟨⟨hyΩ, fun h' => hySH ⟨h', hyB⟩⟩, hyB⟩
    refine ae_eq_set.2 ⟨?_, measure_mono_null hsub2 hnull⟩
    rw [sdiff_eq_empty.2 hsub1, measure_empty]
  -- (4) assemble
  have hρeq : ρ = laplacianMeasure Ω u χ := by
    have hΩeq : Ω = Ω' ∪ SH := (sdiff_union_of_subset (sigmaH_subset Ω u χ)).symm
    calc ρ = ρ.restrict Ω := (Measure.restrict_eq_self_of_ae_mem (ae_iff.2 hρΩ)).symm
      _ = ρ.restrict Ω' + ρ.restrict SH := by
        rw [hΩeq, Measure.restrict_union disjoint_sdiff_left hSHm]
      _ = laplacianMeasure Ω u χ := by rw [h1, h2, h3, laplacianMeasure]
  rw [← hρeq]
  exact hρ

/-- **Theorem 8.7**, with exactly the statement of
`Statements.laplacian_measure_eq`. The first two conjuncts are
`rectifiable_and_locallyFinite_frontier_pos` (Theorem 1.2 (ii)); the third is
`hasDistribLaplacianOn_laplacianMeasure`. -/
theorem laplacian_measure_eq [NeZero n] (hn : 2 ≤ n) (h : IsVariationalSolution Ω C u χ) :
    IsCountablyRectifiable n (n - 1) (Ω ∩ frontier {x | 0 < u x}) ∧
      (∀ K, IsCompact K → K ⊆ Ω → hausdorffN n (n - 1) (K ∩ frontier {x | 0 < u x}) < ∞) ∧
      HasDistribLaplacianOn Ω u (laplacianMeasure Ω u χ) :=
  ⟨isCountablyRectifiable_frontier_pos hn h,
    fun _ hK hKΩ => hausdorffN_inter_frontier_pos_lt_top hn h hK hKΩ,
    hasDistribLaplacianOn_laplacianMeasure hn h⟩

end InnerVariational.Main
