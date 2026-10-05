module

public import Vocabulary
public import InnerVariational

/-!
# Solution: size and frequency on the set of highest density

The trusted vocabulary of `Vocabulary.lean` is reconciled with the library's, then the library
theorems `InnerVariational.Statements.sigmaH_main` and `sigmaH_main_frequency` are applied.

* `hausdorffN`, `unitBallVolume`, `divergence`, `posIndicator`, `energyD`,
  `IsCountablyRectifiable` are definitionally the library's, and `IsVariationalSolution` has the
  same fields (`isVariationalSolution_iff`).
* Sphere integrals: the library integrates over `∂B_r(x)` with Mathlib's `Measure.toSphere`
  (`GMTFoundations.sphereIntegral`); `integral_sphere_eq` identifies this with the integral against
  `ℋ^{n-1}⌊∂B_r(x)` for `r > 0`. Hence `heightH`, `monotonicityM`, `frequencyN` and `sigmaHr`
  (for `t > 0`) agree with the library's for positive radii.
* `sigmaH`: for a variational solution, the limit form agrees with the library's
  "for every admissible radius" form (`sigmaH_eq`).
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

@[expose] public section

noncomputable section

namespace KWChallenge.Bridge

variable {n : ℕ}

/-- For `r > 0`, the integral over `∂B_r(x)` against `ℋ^{n-1}` is the library's sphere integral. -/
theorem integral_sphere_eq [NeZero n] (f : Rn n → ℝ) (x : Rn n) {r : ℝ} (hr : 0 < r) :
    ∫ y in sphere x r, f y ∂hausdorffN n (n - 1) = GMTFoundations.sphereIntegral f x r := by
  set T : Rn n → Rn n := fun y => r⁻¹ • (y - x) with hTdef
  have hmap :
      (hausdorffN n (n - 1)).map T = ENNReal.ofReal (r ^ (n - 1)) • hausdorffN n (n - 1) := by
    have := GMTFoundations.GMT.map_smul_sub_euclideanHausdorffMeasure (n := n) (n - 1) x hr
    rwa [← GMTFoundations.GMT.hausdorffN_eq_euclideanHausdorffMeasure'] at this
  let e : Rn n ≃ₜ Rn n :=
    (Homeomorph.addRight (-x)).trans (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne'))
  have he : (e : Rn n → Rn n) = T := by
    funext y
    simp [e, hTdef, sub_eq_add_neg]
  have hT : MeasurableEmbedding T := he ▸ e.measurableEmbedding
  have h1 := hT.setIntegral_map (μ := hausdorffN n (n - 1)) (fun z => f (x + r • z))
    (sphere (0 : Rn n) 1)
  rw [hmap, Measure.restrict_smul, integral_smul_measure,
    ENNReal.toReal_ofReal (pow_nonneg hr.le _)] at h1
  have hpre : T ⁻¹' sphere (0 : Rn n) 1 = sphere x r := by
    ext y
    simp only [hTdef, mem_preimage, mem_sphere, dist_eq_norm, sub_zero, norm_smul, norm_inv,
      Real.norm_of_nonneg hr.le]
    rw [inv_mul_eq_div, div_eq_one_iff_eq hr.ne']
  have hfun : ∀ y, x + r • T y = y := fun y => by
    simp [hTdef, smul_smul, mul_inv_cancel₀ hr.ne']
  simp only [hpre, hfun] at h1
  have h2 : ∫ ω, f (x + r • (ω : Rn n)) ∂GMTFoundations.sphereMeasure n =
      ∫ z in sphere (0 : Rn n) 1, f (x + r • z) ∂hausdorffN n (n - 1) := by
    rw [show hausdorffN n (n - 1) = GMTFoundations.hausdorffN n (n - 1) from rfl,
      ← GMTFoundations.GMT.map_sphereMeasure_eq_hausdorffN,
      (MeasurableEmbedding.subtype_coe isClosed_sphere.measurableSet).integral_map]
  rw [GMTFoundations.sphereIntegral, h2, ← h1, smul_eq_mul]

theorem heightH_eq [NeZero n] (u : Rn n → ℝ) (x : Rn n) {r : ℝ} (hr : 0 < r) :
    heightH u x r = InnerVariational.heightH u x r := by
  rw [heightH, InnerVariational.heightH, integral_sphere_eq _ _ hr]

theorem heightH_eventuallyEq [NeZero n] (u : Rn n → ℝ) (x : Rn n) :
    heightH u x =ᶠ[𝓝[>] 0] InnerVariational.heightH u x :=
  eventually_nhdsWithin_of_forall fun _ hr => heightH_eq u x hr

theorem monotonicityM_eventuallyEq [NeZero n] (u χ : Rn n → ℝ) (x : Rn n) :
    monotonicityM u χ x =ᶠ[𝓝[>] 0] InnerVariational.monotonicityM u χ x :=
  eventually_nhdsWithin_of_forall fun _ hr => by
    rw [monotonicityM, InnerVariational.monotonicityM, heightH_eq u x hr]
    rfl

theorem frequencyN_eq [NeZero n] (u χ : Rn n → ℝ) (x : Rn n) {r : ℝ} (hr : 0 < r) :
    frequencyN u χ x r = InnerVariational.frequencyN u χ x r := by
  rw [frequencyN, InnerVariational.frequencyN, heightH_eq u x hr]
  rfl

theorem frequencyN_eventuallyEq [NeZero n] (u χ : Rn n → ℝ) (x : Rn n) :
    frequencyN u χ x =ᶠ[𝓝[>] 0] InnerVariational.frequencyN u χ x :=
  eventually_nhdsWithin_of_forall fun _ hr => frequencyN_eq u χ x hr

theorem sigmaHr_eq [NeZero n] (Ω : Set (Rn n)) (u χ : Rn n → ℝ) {t : ℝ} (ht : 0 < t) :
    sigmaHr Ω u χ t = InnerVariational.sigmaHr Ω u χ t := by
  ext x
  simp only [sigmaHr, InnerVariational.sigmaHr, mem_ofPred_eq, monotonicityM,
    InnerVariational.monotonicityM, heightH_eq u x ht]
  rfl

theorem isVariationalSolution_iff {Ω : Set (Rn n)} {C : ℝ≥0} {u χ : Rn n → ℝ} :
    IsVariationalSolution Ω C u χ ↔ InnerVariational.IsVariationalSolution Ω C u χ :=
  ⟨fun h => ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8, fun ξ hξ => h.9 ξ hξ.1 hξ.2.1 hξ.2.2⟩,
    fun h => ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8, fun ξ h1 h2 h3 => h.9 ξ ⟨h1, h2, h3⟩⟩⟩

theorem sigmaH_eq [NeZero n] {Ω : Set (Rn n)} {C : ℝ≥0} {u χ : Rn n → ℝ}
    (h : InnerVariational.IsVariationalSolution Ω C u χ) :
    sigmaH Ω u χ = InnerVariational.sigmaH Ω u χ := by
  ext x
  rw [h.mem_sigmaH_iff_le_Mzero]
  constructor
  · rintro ⟨hx, hcl, m, hm, hle⟩
    refine ⟨hx, hcl, ?_⟩
    have hm' : Tendsto (InnerVariational.monotonicityM u χ x) (𝓝[>] 0) (𝓝 m) :=
      hm.congr' (monotonicityM_eventuallyEq u χ x)
    rw [tendsto_nhds_unique (h.tendsto_Mzero hx) (EReal.tendsto_coe.2 hm')]
    exact_mod_cast hle
  · rintro ⟨hx, hcl, hle⟩
    have hux : u x = 0 :=
      h.eq_zero_of_mem_sigmaH (h.mem_sigmaH_iff_le_Mzero.2 ⟨hx, hcl, hle⟩)
    obtain ⟨m, hm, hlim, -⟩ := h.tendsto_monotonicityM_zero hx hux
    refine ⟨hx, hcl, m, hlim.congr' (monotonicityM_eventuallyEq u χ x).symm, ?_⟩
    rw [hm] at hle
    exact_mod_cast hle

end KWChallenge.Bridge

open KWChallenge KWChallenge.Bridge

theorem challenge_sigmaH_main (n : ℕ) : SigmaHMainClaim n := by
  intro hn Nplus
  have : NeZero n := ⟨by omega⟩
  obtain ⟨C, hC⟩ := InnerVariational.Statements.sigmaH_main hn Nplus
  refine ⟨C, fun Ω C_V u χ hKW hΩ hN => ?_⟩
  have h := isVariationalSolution_iff.1 hKW
  have h1 : InnerVariational.IsVariationalSolution (ball 0 1) C_V u χ :=
    h.mono isOpen_ball (ball_subset_closedBall.trans hΩ)
  rw [frequencyN_eq _ _ _ one_pos] at hN
  obtain ⟨hA, hB⟩ := hC Ω C_V u χ h hΩ hN
  rw [sigmaH_eq h1]
  refine ⟨fun t ht h0 s hts hs1 => ?_, hB⟩
  rw [sigmaHr_eq _ _ _ ht] at h0 ⊢
  exact hA t ht h0 s hts hs1

theorem challenge_sigmaH_main_frequency (n : ℕ) : SigmaHFrequencyClaim n := by
  intro hn C_V u χ hKW Nplus hN h0
  have : NeZero n := ⟨by omega⟩
  have h := isVariationalSolution_iff.1 hKW
  rw [frequencyN_eq _ _ _ one_pos] at hN
  rw [sigmaH_eq h] at h0 ⊢
  have h0' : (0 : Rn n) ∈ InnerVariational.sigmaH (ball 0 1) u χ ∨
      ∃ t : ℝ, 0 < t ∧ (0 : Rn n) ∈ InnerVariational.sigmaHr (ball 0 1) u χ t := by
    rcases h0 with h0 | ⟨t, ht, h0⟩
    · exact Or.inl h0
    · exact Or.inr ⟨t, ht, by rwa [← sigmaHr_eq (ball (0 : Rn n) 1) u χ ht]⟩
  refine measure_mono_null ?_
    (InnerVariational.Statements.sigmaH_main_frequency hn h Nplus hN h0')
  rintro x ⟨hx, hnot⟩
  exact ⟨hx, fun ht => hnot (ht.congr' (frequencyN_eventuallyEq u χ x).symm)⟩
