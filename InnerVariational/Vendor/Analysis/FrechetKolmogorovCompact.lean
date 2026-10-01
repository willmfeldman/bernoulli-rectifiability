/-
Copyright (c) 2026 The Tau Ceti contributors, William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, William M. Feldman
-/
module

public import InnerVariational.Vendor.Analysis.BallAverage
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The Fréchet–Kolmogorov compactness criterion in `Lᵖ` (sufficiency)

For `1 ≤ p < ∞`, on a proper normed additive group with an additive Haar measure, a family of
`Lᵖ` functions that is bounded in `Lᵖ`, vanishes a.e. off a fixed bounded set, and has uniformly
small translation increments `‖f(· + h) - f‖_p`, is totally bounded in `Lᵖ`.

Proof (TauCeti): at a scale `r` below the translation modulus, the ball averages `A_r f` are
uniformly within `ε` of the family, uniformly bounded and uniformly equicontinuous
(`uniformEquicontinuous_ballAverage`); Arzelà–Ascoli on a large closed ball `K` gives a finite
uniform net of the averages; the functions vanish off `K`.

## Main results

* `totallyBounded_of_comp_add_sub_of_isBounded_of_ae_eq_zero_compl`
* `exists_tendsto_eLpNorm_subseq_of_translation`: sequential form, for functions.
* `frechetKolmogorov_exists_subseq`: the `L¹` form used for BV compactness: a bounded sequence
  with uniformly small translation increments and supports in a fixed compact set has an
  `L¹`-convergent subsequence.

## Provenance

* Upstream: TauCeti, https://github.com/TauCetiProject/TauCeti
* Path: `TauCeti/MeasureTheory/Function/Lp/FrechetKolmogorov.lean`
* Commit: 91f66a0514e6523efdccddb9e35fb82c96dd6405 (2026-09-24)
* License: Apache-2.0. Upstream `NOTICE`: none.
* Upstream notice: `Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.`;
  upstream authors: The Tau Ceti contributors.
* Extent: `exists_finite_approx_on_isCompact` (verbatim up to renaming),
  `eLpNorm_sub_le_of_approx_of_dist_bdd_on` (adapted: tail terms replaced by an a.e. support
  hypothesis), `totallyBounded_of_comp_add_sub_of_isBounded_of_ae_eq_zero_compl` (adapted from
  upstream's `totallyBounded_of_comp_add_sub_of_unifTight` and the bounded-support corollary of
  the same name).
* Changes: ported from Lean v4.34.0-rc2 to Lean/Mathlib v4.30.0; `module`/`public import`
  removed; namespace `TauCeti` → `InnerVariational.Vendor.Analysis`; only the bounded-support
  form of
  the criterion is kept and proved directly (the tails off the compact set vanish, so upstream's
  `UnifTight` route and its `TightNormed` dependency are not needed; continuity of the ball
  averages comes from their equicontinuity instead of upstream's `Translation.lean`). New
  (W. M. Feldman): `totallyBounded_range_toLp_of_translation`,
  `exists_tendsto_eLpNorm_subseq_of_translation`, `frechetKolmogorov_exists_subseq`.
* Module system: later converted back to a Lean `module` (`public import`,
  `@[expose] public section`), with narrowed Mathlib imports.
-/

@[expose] public noncomputable section

namespace InnerVariational.Vendor.Analysis

open Filter MeasureTheory Metric Set Topology
open scoped ENNReal

section ArzelaAscoli

variable {X F ι : Type*} [PseudoMetricSpace X] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- The finite uniform net on a compact set extracted from Arzelà–Ascoli. -/
theorem exists_finite_approx_on_isCompact {K : Set X} (hK : IsCompact K)
    {g : ι → X → F} {C η : ℝ}
    (hC : ∀ i x, g i x ∈ closedBall (0 : F) C) (hequi : UniformEquicontinuous g) (hη : 0 < η) :
    ∃ t : Set ι, t.Finite ∧ ∀ i, ∃ j ∈ t, ∀ x ∈ K, dist (g i x) (g j x) ≤ η := by
  let _ : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let φ : ι → BoundedContinuousFunction K F := fun i =>
    BoundedContinuousFunction.mkOfCompact
      ⟨fun x : K => g i x, (hequi.equicontinuous.continuous i).comp continuous_subtype_val⟩
  let 𝒜 : Set (BoundedContinuousFunction K F) := Set.range φ
  have hφcoe : ∀ i : ι, ⇑(φ i) = K.domRestrict (g i) := fun i => by
    rfl
  have hφequi : Equicontinuous fun i : ι => (φ i : K → F) := by
    rw [funext hφcoe]
    exact (equicontinuous_restrict_iff _).2 (hequi.equicontinuous.equicontinuousOn K)
  have h𝒜equi : Equicontinuous ((↑) : 𝒜 → K → F) := by
    rw [← Set.comp_rangeSplitting φ]
    exact hφequi.comp (Set.rangeSplitting φ)
  have h𝒜compact : IsCompact (closure 𝒜) :=
    BoundedContinuousFunction.arzela_ascoli (closedBall (0 : F) C)
      (isCompact_closedBall _ _) 𝒜 (by
        intro q x hq
        obtain ⟨i, rfl⟩ := hq
        simpa only [φ, BoundedContinuousFunction.mkOfCompact_apply, ContinuousMap.coe_mk] using
          hC i x) h𝒜equi
  have h𝒜tb : TotallyBounded 𝒜 := h𝒜compact.totallyBounded.subset subset_closure
  obtain ⟨u, hu𝒜, hufin, hucover⟩ := h𝒜tb.exists_subset (dist_mem_uniformity hη)
  let _ : Finite u := hufin.to_subtype
  choose idx hidx using fun q : u => hu𝒜 q.2
  refine ⟨Set.range idx, Set.finite_range idx, fun i => ?_⟩
  obtain ⟨q, hqu, hiq⟩ : ∃ q ∈ u, dist (φ i) q < η := by
    simpa only [mem_iUnion, mem_ofPred_eq, exists_prop] using hucover (Set.mem_range_self i)
  let q' : u := ⟨q, hqu⟩
  refine ⟨idx q', Set.mem_range_self q', fun x hx => ?_⟩
  have hφdist : dist (φ i) (φ (idx q')) < η := by rw [hidx q']; exact hiq
  simpa only [φ, BoundedContinuousFunction.mkOfCompact_apply, ContinuousMap.coe_mk] using
    (BoundedContinuousFunction.dist_coe_le_dist (f := φ i) (g := φ (idx q'))
      ⟨x, hx⟩).trans hφdist.le

end ArzelaAscoli

section LpApproximation

variable {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F]
  {mu : Measure α} {p : ℝ≥0∞}

/-- The comparison estimate: `f` and `f'` vanish a.e. off `K`, are approximated in `Lᵖ` by `A`
and `A'`, and the approximants are uniformly close on `K`. -/
theorem eLpNorm_sub_le_of_approx_of_dist_bdd_on {K : Set α}
    (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hK : MeasurableSet K) {f f' A A' : α → F} {η : ℝ}
    (_hf : AEStronglyMeasurable f mu) (_hf' : AEStronglyMeasurable f' mu)
    (hA : AEStronglyMeasurable A mu) (hA' : AEStronglyMeasurable A' mu)
    (hsupp : ∀ᵐ x ∂mu, x ∉ K → f x = 0) (hsupp' : ∀ᵐ x ∂mu, x ∉ K → f' x = 0)
    (hη : 0 ≤ η) (hmid : ∀ x ∈ K, dist (A x) (A' x) ≤ η) :
    eLpNorm (f - f') p mu ≤
      eLpNorm (A - f) p mu +
        (ENNReal.ofReal η * mu K ^ (1 / p.toReal) + eLpNorm (A' - f') p mu) := by
  have hsplit : (f - f' : α → F) =ᵐ[mu] K.indicator (f - f') := by
    filter_upwards [hsupp, hsupp'] with x hx hx'
    by_cases hxK : x ∈ K
    · rw [Set.indicator_of_mem hxK]
    · rw [Set.indicator_of_notMem hxK, Pi.sub_apply, hx hxK, hx' hxK, sub_zero]
  rw [eLpNorm_congr_ae hsplit]
  have hdecomp : K.indicator (f - f' : α → F) =
      K.indicator (f - A) + (K.indicator (A - A') + K.indicator (A' - f')) := by
    rw [← Set.indicator_add', ← Set.indicator_add']
    congr 1
    abel
  rw [hdecomp]
  refine (eLpNorm_add_le hp).trans ?_
  refine add_le_add ?_ ((eLpNorm_add_le hp).trans (add_le_add ?_ ?_))
  · refine (eLpNorm_indicator_le _ hK).trans ?_
    rw [← neg_sub A f, eLpNorm_neg]
  · exact eLpNorm_indicator_sub_le_of_dist_bdd mu hp' hK.nullMeasurableSet hη
      ((hA.sub hA').indicator hK) hmid
  · exact eLpNorm_indicator_le _ hK

end LpApproximation

section FrechetKolmogorov

variable {E F : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {mu : Measure E} [mu.IsAddHaarMeasure] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The Fréchet–Kolmogorov criterion for a family vanishing almost everywhere off a fixed
bounded set.** For `1 ≤ p < ∞`, an `Lᵖ`-bounded family, vanishing a.e. off a fixed bounded set,
whose translation increments are uniformly small in `Lᵖ`, is totally bounded. -/
theorem totallyBounded_of_comp_add_sub_of_isBounded_of_ae_eq_zero_compl (hp' : p ≠ ∞)
    {S : Set (Lp F p mu)}
    {s : Set E} (hs : Bornology.IsBounded s) (hsupp : ∀ f ∈ S, ∀ᵐ x ∂mu, x ∉ s → f x = 0)
    {M : ℝ≥0∞} (hM : M ≠ ∞) (hbdd : ∀ f ∈ S, eLpNorm f p mu ≤ M)
    (htrans : ∀ ε : ℝ≥0∞, 0 < ε → ∃ δ > 0, ∀ f ∈ S, ∀ h : E, ‖h‖ < δ →
      eLpNorm (fun x => f (x + h) - f x) p mu ≤ ε) :
    TotallyBounded S := by
  have hp : (1 : ℝ≥0∞) ≤ p := Fact.out
  obtain ⟨R, hR⟩ := hs.subset_closedBall 0
  set K : Set E := closedBall (0 : E) R
  have hmeasK : MeasurableSet K := measurableSet_closedBall
  have hsuppK : ∀ f ∈ S, ∀ᵐ x ∂mu, x ∉ K → f x = 0 := fun f hf =>
    (hsupp f hf).mono fun x hx hxK => hx fun hxs => hxK (hR hxs)
  rw [Metric.totallyBounded_iff]
  intro ε hε
  have hε₁ : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / 4) := ENNReal.ofReal_pos.2 (by linarith)
  set ε₁ : ℝ≥0∞ := ENNReal.ofReal (ε / 4)
  obtain ⟨r, hr, hrS⟩ := htrans ε₁ hε₁
  set V : ℝ≥0∞ := mu (ball (0 : E) r)
  -- The uniform `L^∞` bound on the ball averages of the family.
  set Bₑ : ℝ≥0∞ := V ^ (-(p.toReal)⁻¹) * M
  have hV0 : V ≠ 0 := (measure_ball_pos mu 0 hr).ne'
  have hVt : V ≠ ∞ := measure_ball_lt_top.ne
  have hBₑt : Bₑ ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_ne_zero hV0 hVt) hM
  have hgB : ∀ i : S, ∀ x : E,
      ballAverage mu r ⇑(i : Lp F p mu) x ∈ closedBall (0 : F) Bₑ.toReal := fun i x => by
    rw [mem_closedBall, dist_zero_right]
    have h := (enorm_ballAverage_le hp hp' (Lp.aestronglyMeasurable (i : Lp F p mu)) hr x).trans
      (mul_le_mul' le_rfl (hbdd _ i.2))
    simpa [Bₑ, V] using ENNReal.toReal_mono hBₑt h
  -- The uniform equicontinuity of the ball averages, at the fixed scale `r`.
  have hequi : UniformEquicontinuous fun i : S => ballAverage mu r ⇑(i : Lp F p mu) :=
    uniformEquicontinuous_ballAverage hp hp' (fun i => Lp.memLp (i : Lp F p mu)) hr
      fun c hc => by
        obtain ⟨δ, hδ, hδS⟩ := htrans c hc
        exact ⟨δ, hδ, fun i => hδS _ i.2⟩
  have hsmooth : ∀ g ∈ S, eLpNorm (ballAverage mu r ⇑g - ⇑g) p mu ≤ ε₁ := by
    intro g hg
    exact eLpNorm_ballAverage_sub_le hp hp' (Lp.memLp g) hr
      (fun e he => hrS g hg e (by simpa [dist_eq_norm] using he))
  -- The scale of the uniform approximation on `K`, calibrated by the measure of `K`.
  have hKt : mu K ≠ ∞ := measure_closedBall_lt_top.ne
  set W : ℝ≥0∞ := mu K ^ (1 / p.toReal)
  have hWt : W ≠ ∞ := (ENNReal.rpow_lt_top_of_nonneg (by positivity) hKt).ne
  have hWnn : (0 : ℝ) ≤ W.toReal := ENNReal.toReal_nonneg
  set η : ℝ := ε / (4 * (W.toReal + 1)) with hηdef
  have hη : 0 < η := by
    rw [hηdef]; positivity
  have hWη : ENNReal.ofReal η * W ≤ ENNReal.ofReal (ε / 4) := by
    have hkey : W.toReal * η ≤ ε / 4 := by
      have hstep : (W.toReal + 1) * η = ε / 4 := by
        rw [hηdef]; field_simp
      nlinarith [hη.le]
    calc ENNReal.ofReal η * W = ENNReal.ofReal (W.toReal * η) := by
          rw [ENNReal.ofReal_mul hWnn, ENNReal.ofReal_toReal hWt, mul_comm]
      _ ≤ ENNReal.ofReal (ε / 4) := ENNReal.ofReal_le_ofReal hkey
  -- Arzelà–Ascoli supplies a finite uniform net for the restricted ball averages.
  obtain ⟨t, htfin, ht⟩ := exists_finite_approx_on_isCompact
    (isCompact_closedBall (0 : E) R) hgB hequi hη
  refine ⟨Subtype.val '' t, htfin.image (fun i : S => (i : Lp F p mu)), fun f hf => ?_⟩
  obtain ⟨j, hjt, hmid⟩ := ht ⟨f, hf⟩
  refine mem_iUnion₂.2 ⟨(j : Lp F p mu), ⟨j, hjt, rfl⟩, ?_⟩
  set f' : Lp F p mu := (j : Lp F p mu)
  set A : E → F := ballAverage mu r ⇑f
  set A' : E → F := ballAverage mu r ⇑f'
  have hfm : AEStronglyMeasurable (⇑f) mu := Lp.aestronglyMeasurable f
  have hf'm : AEStronglyMeasurable (⇑f') mu := Lp.aestronglyMeasurable f'
  have hAm : AEStronglyMeasurable A mu :=
    ((hequi.uniformContinuous ⟨f, hf⟩).continuous).aestronglyMeasurable
  have hA'm : AEStronglyMeasurable A' mu :=
    ((hequi.uniformContinuous j).continuous).aestronglyMeasurable
  have hmain : eLpNorm (⇑f - ⇑f') p mu ≤ ENNReal.ofReal (3 * ε / 4) := by
    calc eLpNorm (⇑f - ⇑f') p mu
        ≤ eLpNorm (A - ⇑f) p mu + (ENNReal.ofReal η * W + eLpNorm (A' - ⇑f') p mu) :=
          eLpNorm_sub_le_of_approx_of_dist_bdd_on hp hp' hmeasK hfm hf'm hAm hA'm
            (hsuppK f hf) (hsuppK f' j.2) hη.le hmid
      _ ≤ ε₁ + (ENNReal.ofReal (ε / 4) + ε₁) := by
          exact add_le_add (by simpa only [A] using hsmooth f hf)
              (add_le_add hWη (by simpa only [A', f'] using hsmooth (j : Lp F p mu) j.2))
      _ = ENNReal.ofReal (3 * ε / 4) := by
          simp (disch := positivity) only [ε₁, ← ENNReal.ofReal_add]
          congr 1
          ring
  rw [mem_ball, Lp.dist_def]
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmain
  rw [ENNReal.toReal_ofReal (by linarith)] at this
  linarith

/-- **Fréchet–Kolmogorov for a sequence of functions**: the `Lᵖ` classes of a sequence of `Lᵖ`
functions, bounded in `Lᵖ`, vanishing off a fixed bounded set, with uniformly small translation
increments in `Lᵖ`, form a totally bounded set. -/
theorem totallyBounded_range_toLp_of_translation (hp' : p ≠ ∞) (f : ℕ → E → F)
    (hf : ∀ n, MemLp (f n) p mu) {s : Set E} (hs : Bornology.IsBounded s)
    (hsupp : ∀ n, ∀ᵐ x ∂mu, x ∉ s → f n x = 0)
    {M : ℝ≥0∞} (hM : M ≠ ∞) (hbdd : ∀ n, eLpNorm (f n) p mu ≤ M)
    (htrans : ∀ ε : ℝ≥0∞, 0 < ε → ∃ δ > 0, ∀ n, ∀ h : E, ‖h‖ < δ →
      eLpNorm (fun x => f n (x + h) - f n x) p mu ≤ ε) :
    TotallyBounded (range fun n ↦ (hf n).toLp (f n)) := by
  set g : ℕ → Lp F p mu := fun n ↦ (hf n).toLp (f n)
  have hg : ∀ n, (g n : E → F) =ᵐ[mu] f n := fun n ↦ (hf n).coeFn_toLp
  refine totallyBounded_of_comp_add_sub_of_isBounded_of_ae_eq_zero_compl hp' hs ?_ hM ?_ ?_
  · rintro _ ⟨n, rfl⟩
    filter_upwards [hg n, hsupp n] with x hx hx' hxs
    rw [hx, hx' hxs]
  · rintro _ ⟨n, rfl⟩
    rw [eLpNorm_congr_ae (hg n)]
    exact hbdd n
  · intro ε hε
    obtain ⟨δ, hδ, hδS⟩ := htrans ε hε
    refine ⟨δ, hδ, ?_⟩
    rintro _ ⟨n, rfl⟩ h hh
    have hae : (fun x ↦ (g n : E → F) (x + h) - (g n : E → F) x) =ᵐ[mu]
        fun x ↦ f n (x + h) - f n x :=
      ((measurePreserving_add_right mu h).quasiMeasurePreserving.ae_eq_comp (hg n)).sub (hg n)
    rw [eLpNorm_congr_ae hae]
    exact hδS n h hh

/-- **Fréchet–Kolmogorov, sequential form.** For `1 ≤ p < ∞`, a sequence of `Lᵖ` functions,
bounded in `Lᵖ`, vanishing off a fixed bounded set, with uniformly small translation increments
in `Lᵖ`, has a subsequence converging in `Lᵖ`. -/
theorem exists_tendsto_eLpNorm_subseq_of_translation (hp' : p ≠ ∞) (f : ℕ → E → F)
    (hf : ∀ n, MemLp (f n) p mu) {s : Set E} (hs : Bornology.IsBounded s)
    (hsupp : ∀ n, ∀ᵐ x ∂mu, x ∉ s → f n x = 0)
    {M : ℝ≥0∞} (hM : M ≠ ∞) (hbdd : ∀ n, eLpNorm (f n) p mu ≤ M)
    (htrans : ∀ ε : ℝ≥0∞, 0 < ε → ∃ δ > 0, ∀ n, ∀ h : E, ‖h‖ < δ →
      eLpNorm (fun x => f n (x + h) - f n x) p mu ≤ ε) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f₀ : E → F, MemLp f₀ p mu ∧
      Tendsto (fun n ↦ eLpNorm (f (φ n) - f₀) p mu) atTop (𝓝 0) := by
  have hTB := totallyBounded_range_toLp_of_translation hp' f hf hs hsupp hM hbdd htrans
  have hcpt := hTB.closure.isCompact_of_isClosed isClosed_closure
  obtain ⟨a, -, φ, hφ, hlim⟩ :=
    hcpt.tendsto_subseq (fun n ↦ subset_closure (mem_range_self n))
  refine ⟨φ, hφ, a, Lp.memLp a, ?_⟩
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'] at hlim
  refine hlim.congr fun n ↦ eLpNorm_congr_ae ?_
  exact (hf (φ n)).coeFn_toLp.sub EventuallyEq.rfl

end FrechetKolmogorov

section Compactness

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- **Fréchet–Kolmogorov, sufficiency, `L¹` form.** A sequence of integrable functions,
bounded in `L¹`, vanishing outside a fixed compact set, and uniformly continuous under
translations in `L¹`, has a subsequence converging in `L¹`. -/
theorem frechetKolmogorov_exists_subseq (μ : Measure V) [μ.IsAddHaarMeasure] (f : ℕ → V → ℝ)
    (hf : ∀ n, Integrable (f n) μ) (C : ℝ) (hC : ∀ n, ∫ x, |f n x| ∂μ ≤ C) (K : Set V)
    (hK : IsCompact K) (hsupp : ∀ n, ∀ x ∉ K, f n x = 0)
    (htrans : ∀ δ > 0, ∃ ρ > 0, ∀ n, ∀ h : V, ‖h‖ < ρ → ∫ x, |f n (x + h) - f n x| ∂μ < δ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f₀ : V → ℝ, Integrable f₀ μ ∧
      Tendsto (fun n ↦ eLpNorm (f (φ n) - f₀) 1 μ) atTop (𝓝 0) := by
  have : Fact ((1 : ℝ≥0∞) ≤ 1) := ⟨le_rfl⟩
  -- `eLpNorm g 1 = ofReal (∫ |g|)` for integrable `g`
  have key : ∀ g : V → ℝ, Integrable g μ → eLpNorm g 1 μ = ENNReal.ofReal (∫ x, |g x| ∂μ) :=
    fun g hg ↦ by
      rw [eLpNorm_one_eq_lintegral_enorm hg.aestronglyMeasurable,
        ← ofReal_integral_norm_eq_lintegral_enorm hg]
      rfl
  have htrans' : ∀ ε : ℝ≥0∞, 0 < ε → ∃ ρ > 0, ∀ n, ∀ h : V, ‖h‖ < ρ →
      eLpNorm (fun x => f n (x + h) - f n x) 1 μ ≤ ε := by
    intro ε hε
    obtain ⟨δ, hδ, hδε⟩ : ∃ δ : ℝ, 0 < δ ∧ ENNReal.ofReal δ ≤ ε := by
      rcases eq_or_ne ε ∞ with rfl | hεt
      · exact ⟨1, one_pos, le_top⟩
      exact ⟨ε.toReal, ENNReal.toReal_pos hε.ne' hεt, (ENNReal.ofReal_toReal hεt).le⟩
    obtain ⟨ρ, hρ, hρS⟩ := htrans δ hδ
    refine ⟨ρ, hρ, fun n h hh ↦ ?_⟩
    rw [key (fun x ↦ f n (x + h) - f n x) (((hf n).comp_add_right h).sub (hf n))]
    exact (ENNReal.ofReal_le_ofReal (hρS n h hh).le).trans hδε
  obtain ⟨φ, hφ, f₀, hf₀, hlim⟩ := exists_tendsto_eLpNorm_subseq_of_translation (mu := μ)
    (p := 1) ENNReal.one_ne_top f (fun n ↦ memLp_one_iff_integrable.2 (hf n)) hK.isBounded
    (fun n ↦ Eventually.of_forall (hsupp n)) (M := ENNReal.ofReal C) ENNReal.ofReal_ne_top
    (fun n ↦ by rw [key _ (hf n)]; exact ENNReal.ofReal_le_ofReal (hC n)) htrans'
  exact ⟨φ, hφ, f₀, memLp_one_iff_integrable.1 hf₀, hlim⟩

end Compactness

end InnerVariational.Vendor.Analysis
