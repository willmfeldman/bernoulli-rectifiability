import Statement
import InnerVariational

/-!
# Solution: variational solutions with a Lipschitz coefficient

The trusted vocabulary of `Statement.lean` is reconciled with the library's, then the library
theorems of `InnerVariational/Statements/LipschitzQ.lean` are applied.

* `unitBallVolume`, `hausdorffN`, `divergence`, `posIndicator`, `energyDq`, `oneHomRescale` and
  `chiRescale` are definitionally the library's; `IsVariationalSolutionQ`, `QBounds` and
  `IsViscositySolutionQ` have the same fields (`isVariationalSolutionQ_iff`, `qBounds_iff`).
* Sphere integrals: the library integrates over `∂B_r(x)` with Mathlib's `Measure.toSphere`
  (`GMTFoundations.sphereIntegral`); `integral_sphere_eq` identifies this with the integral against
  `ℋ^{n-1}⌊∂B_r(x)` for `r > 0`. Hence `heightH` and `monotonicityMq` agree with the library's for
  positive radii.
* `sigmaHQ`: for a variational solution with `QBounds`, the limit form "`M` converges to a real
  number `m ≥ Q(x)² |B₁|`" agrees with the library's form `M(0+) ≥ Q(x)² |B₁|` in `EReal`
  (`sigmaHQ_eq`).
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

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

theorem monotonicityMq_eventuallyEq [NeZero n] (q : ℝ) (u χ : Rn n → ℝ) (x : Rn n) :
    monotonicityMq q u χ x =ᶠ[𝓝[>] 0] InnerVariational.monotonicityMq q u χ x :=
  eventually_nhdsWithin_of_forall fun _ hr => by
    rw [monotonicityMq, InnerVariational.monotonicityMq, heightH_eq u x hr]
    rfl

theorem isVariationalSolutionQ_iff {Ω : Set (Rn n)} {C : ℝ≥0} {Q u χ : Rn n → ℝ} :
    IsVariationalSolutionQ Ω C Q u χ ↔ InnerVariational.IsVariationalSolutionQ Ω C Q u χ :=
  ⟨fun h => ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8, fun ξ hξ => h.9 ξ hξ.1 hξ.2.1 hξ.2.2⟩,
    fun h => ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8, fun ξ h1 h2 h3 => h.9 ξ ⟨h1, h2, h3⟩⟩⟩

theorem qBounds_iff {Ω : Set (Rn n)} {Q : Rn n → ℝ} {L : ℝ≥0} {c C' : ℝ} :
    QBounds Ω Q L c C' ↔ InnerVariational.QBounds Ω Q L c C' :=
  ⟨fun h => ⟨h.1, h.2, h.3, h.4⟩, fun h => ⟨h.1, h.2, h.3, h.4⟩⟩

theorem sigmaHQ_eq [NeZero n] {Ω : Set (Rn n)} {C : ℝ≥0} {Q u χ : Rn n → ℝ} {L : ℝ≥0}
    {c C' : ℝ} (hQ : InnerVariational.QBounds Ω Q L c C')
    (h : InnerVariational.IsVariationalSolutionQ Ω C Q u χ) :
    sigmaHQ Ω Q u χ = InnerVariational.sigmaHQ Ω Q u χ := by
  ext x
  constructor
  · rintro ⟨hx, hcl, m, hm, hle⟩
    refine ⟨hx, hcl, ?_⟩
    have hm' : Tendsto (InnerVariational.monotonicityMq (Q x) u χ x) (𝓝[>] 0) (𝓝 m) :=
      hm.congr' (monotonicityMq_eventuallyEq (Q x) u χ x)
    rw [tendsto_nhds_unique (h.tendsto_MzeroQ hQ hx) (EReal.tendsto_coe.2 hm')]
    exact EReal.coe_le_coe_iff.2 hle
  · intro hxS
    obtain ⟨hx, hcl, hle⟩ := hxS
    have hux : u x = 0 := h.eq_zero_of_mem_sigmaHQ hQ ⟨hx, hcl, hle⟩
    obtain ⟨m, hm, hlim⟩ := h.exists_tendsto_monotonicityMq_of_eq_zero hQ hx hux
    refine ⟨hx, hcl, m, hlim.congr' (monotonicityMq_eventuallyEq (Q x) u χ x).symm, ?_⟩
    rw [hm] at hle
    exact EReal.coe_le_coe_iff.1 hle

end KWChallenge.Bridge

open KWChallenge KWChallenge.Bridge

theorem challenge_sigmaHQ_density (n : ℕ) : SigmaHQDensityClaim n := by
  intro hn Ω C_V Q u χ L c C' hQ hKW x
  have : NeZero n := ⟨by omega⟩
  have hQ' := qBounds_iff.1 hQ
  have h := isVariationalSolutionQ_iff.1 hKW
  rw [sigmaHQ_eq hQ' h]
  exact InnerVariational.IsVariationalSolutionQ.mem_sigmaHQ_iff_frontier_inter hQ' h

theorem challenge_sigmaHQ_closed (n : ℕ) : SigmaHQClosedClaim n := by
  intro hn Ω C_V Q u χ L c C' hQ hKW
  have : NeZero n := ⟨by omega⟩
  have hQ' := qBounds_iff.1 hQ
  have h := isVariationalSolutionQ_iff.1 hKW
  rw [sigmaHQ_eq hQ' h]
  exact InnerVariational.IsVariationalSolutionQ.closure_sigmaHQ_inter_subset hQ' h

theorem challenge_viscosityQ (n : ℕ) : ViscosityQClaim n := by
  intro hn Ω C_V Q u χ L c C' hQ hKW
  have : NeZero n := ⟨by omega⟩
  have hQ' := qBounds_iff.1 hQ
  have h := isVariationalSolutionQ_iff.1 hKW
  rw [sigmaHQ_eq hQ' h]
  have hv := InnerVariational.IsVariationalSolutionQ.isViscositySolutionQ_diff_sigmaHQ hn hQ' h
  exact ⟨hv.1, hv.2, hv.3, hv.4, hv.5⟩

theorem challenge_blowup_limitQ (n : ℕ) : BlowupLimitQClaim n := by
  intro _ Ω C_V Q u χ L c C' hQ hKW x hx r hr hr0 u₀ hconv
  obtain ⟨φ, hφ, χ₀, hsol, hL⟩ := InnerVariational.IsVariationalSolutionQ.exists_blowup_limit
    (qBounds_iff.1 hQ) (isVariationalSolutionQ_iff.1 hKW) hx hr hr0 hconv
  exact ⟨φ, hφ, χ₀, isVariationalSolutionQ_iff.2 hsol, hL⟩

theorem challenge_blowup_homogeneousQ (n : ℕ) : BlowupHomogeneousQClaim n := by
  intro hn Ω C_V Q u χ L c C' hQ hKW x hx r hr hr0 u₀ hconv
  have : NeZero n := ⟨by omega⟩
  exact InnerVariational.IsVariationalSolutionQ.blowup_homogeneous
    (qBounds_iff.1 hQ) (isVariationalSolutionQ_iff.1 hKW) hx hr hr0 hconv

theorem challenge_chi_eq_indicatorQ (n : ℕ) : ChiIdentificationQClaim n := by
  intro hn U Q u χ hU hloc
  refine InnerVariational.Singular.chi_eq_indicator_of_localQ (Q := Q) hn hU fun x hx => ?_
  obtain ⟨V, hVo, hxV, hVU, C_V, L, c, C', hQ, hKW⟩ := hloc x hx
  exact ⟨V, hVo, hxV, hVU, C_V, L, c, C', qBounds_iff.1 hQ, isVariationalSolutionQ_iff.1 hKW⟩
