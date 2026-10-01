import Statement
import InnerVariational

/-!
# Solution: the Main Theorem and the identification of `χ` and of `Δu`

The trusted vocabulary of `Statement.lean` is reconciled with the library's, then the library
theorems `InnerVariational.Statements.main_theorem`, `chi_eq_indicator` and
`laplacian_measure_eq` are applied.

* `hausdorffN`, `unitBallVolume`, `divergence`, `posIndicator`, `energyD`,
  `IsCountablyRectifiable`, `HasDistribLaplacianOn` are definitionally the library's.
* `IsVariationalSolution` and `IsGaussGreenPair` have the same fields as the library's
  (`isVariationalSolution_iff`, `isGaussGreenPair_iff`), hence `reducedBoundary` agrees.
* Sphere integrals: the library integrates over `∂B_r(x)` with Mathlib's `Measure.toSphere`
  (`GMTFoundations.sphereIntegral`); `integral_sphere_eq` identifies this with the integral against
  `ℋ^{n-1}⌊∂B_r(x)` for `r > 0` (GMT-foundations' `map_sphereMeasure_eq_hausdorffN` and scaling).
  Hence `heightH`, `monotonicityM` agree for `r > 0`, and `heightHZero` agrees everywhere.
* `alphaN`: the library uses the first coordinate `y_1`; a coordinate swap is an isometry, so
  `∫_{∂B₁} y_n² dℋ^{n-1} = ∫_{∂B₁} y_1² dℋ^{n-1}` (`integral_sphere_last_sq`).
* `sigmaH`: the library's `Σ^H` asks `M_x(u; r) ≥ |B₁|` for every admissible `r`; for a
  variational solution this is equivalent to the limit form (`sigmaH_eq`, from the library's
  `mem_sigmaH_iff_le_Mzero`, `tendsto_Mzero` and `tendsto_monotonicityM_zero`).
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

noncomputable section

namespace InnerVariational.ChallengeHelpers

variable {n : ℕ} {Ω E : Set (Rn n)} {μ : Measure (Rn n)} {ν : Rn n → Rn n}

/-- Set integrals of functions vanishing off a measurable `Ω` only see `Ω ∩ F`. -/
theorem setIntegral_inter_of_eq_zero (hΩ : MeasurableSet Ω) {F : Set (Rn n)}
    {f : Rn n → ℝ} (hf : ∀ y ∉ Ω, f y = 0) : ∫ y in Ω ∩ F, f y = ∫ y in F, f y := by
  rw [← Measure.restrict_restrict hΩ]
  exact setIntegral_eq_integral_of_forall_compl_eq_zero hf

/-- A Gauss–Green pair on an open `Ω` only sees `Ω ∩ E`. -/
theorem isGaussGreenPair_inter_iff (hΩ : IsOpen Ω) :
    IsGaussGreenPair Ω (Ω ∩ E) μ ν ↔ IsGaussGreenPair Ω E μ ν := by
  have key : ∀ φ, IsSmoothTestField Ω φ →
      ∫ y in Ω ∩ E, divergence φ y = ∫ y in E, divergence φ y := fun φ hφ =>
    setIntegral_inter_of_eq_zero hΩ.measurableSet fun y hy =>
      divergence_eq_zero_of_notMem_tsupport fun h' => hy (hφ.2.2 h')
  constructor
  · intro h
    exact { h with
      integral_divergence := fun φ hφ => (key φ hφ).symm.trans (h.integral_divergence φ hφ) }
  · intro h
    exact { h with
      integral_divergence := fun φ hφ => (key φ hφ).trans (h.integral_divergence φ hφ) }

theorem hasLocallyFinitePerimeter_inter_iff (hΩ : IsOpen Ω) :
    HasLocallyFinitePerimeter Ω (Ω ∩ E) ↔ HasLocallyFinitePerimeter Ω E := by
  simp only [HasLocallyFinitePerimeter, isGaussGreenPair_inter_iff hΩ]

end InnerVariational.ChallengeHelpers

namespace KWChallenge.Bridge

variable {n : ℕ}

/-! ### Sphere integrals and `α(n)` -/

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

/-- The swap of the first and last coordinates, a linear isometry of `ℝⁿ`. -/
def swapLast (n : ℕ) [NeZero n] : Rn n ≃ₗᵢ[ℝ] Rn n :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (0 : Fin n) (lastCoord n))

theorem integral_sphere_last_sq [NeZero n] :
    ∫ y in sphere (0 : Rn n) 1, y (lastCoord n) ^ 2 ∂hausdorffN n (n - 1) =
      ∫ y in sphere (0 : Rn n) 1, y 0 ^ 2 ∂hausdorffN n (n - 1) := by
  set P := swapLast n
  have hP : MeasurePreserving P (hausdorffN n (n - 1)) (hausdorffN n (n - 1)) := by
    have := (P.toIsometryEquiv.measurePreserving_hausdorffMeasure ((n - 1 : ℕ) : ℝ))
    exact this.smul_measure _
  have hemb : MeasurableEmbedding P := P.toHomeomorph.measurableEmbedding
  have key := hP.setIntegral_preimage_emb hemb (fun y => y 0 ^ 2) (sphere (0 : Rn n) 1)
  have hpre : P ⁻¹' sphere (0 : Rn n) 1 = sphere 0 1 := by
    ext y
    simp
  have happ : ∀ y : Rn n, (P y) 0 = y (lastCoord n) := fun y => by
    simp [P, swapLast, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply]
  simp only [hpre, happ] at key
  exact key

theorem alphaN_eq [NeZero n] : alphaN n = InnerVariational.alphaN n := by
  rw [alphaN, InnerVariational.alphaN, integral_sphere_last_sq, integral_sphere_eq _ _ one_pos]

/-! ### The monotonicity quantities -/

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

theorem heightHZero_eq [NeZero n] (u : Rn n → ℝ) (x : Rn n) :
    heightHZero u x = InnerVariational.heightHZero u x := by
  rw [heightHZero, InnerVariational.heightHZero, limUnder, limUnder,
    Filter.map_congr (heightH_eventuallyEq u x)]

/-! ### Variational solutions and `Σ^H` -/

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

theorem tendsto_heightHZero [NeZero n] {Ω : Set (Rn n)} {C : ℝ≥0} {u χ : Rn n → ℝ}
    (h : InnerVariational.IsVariationalSolution Ω C u χ) :
    ∀ x ∈ sigmaH Ω u χ, Tendsto (heightH u x) (𝓝[>] 0) (𝓝 (heightHZero u x)) := by
  intro x hx
  rw [sigmaH_eq h] at hx
  rw [heightHZero_eq]
  exact (InnerVariational.Singular.tendsto_heightH_zero h hx).congr'
    (heightH_eventuallyEq u x).symm

/-! ### Reduced boundary and the Laplacian measure -/

theorem isGaussGreenPair_iff {Ω E : Set (Rn n)} {μ : Measure (Rn n)} {ν : Rn n → Rn n} :
    IsGaussGreenPair Ω E μ ν ↔ GMTFoundations.IsGaussGreenPair Ω E μ ν :=
  ⟨fun h => ⟨h.1, h.2, h.3, h.4, h.5⟩, fun h => ⟨h.1, h.2, h.3, h.4, h.5⟩⟩

theorem reducedBoundary_eq (Ω E : Set (Rn n)) :
    reducedBoundary Ω E = GMTFoundations.reducedBoundary Ω E := by
  ext x
  simp only [reducedBoundary, GMTFoundations.reducedBoundary, Set.mem_ofPred_eq,
    isGaussGreenPair_iff]

theorem laplacianMeasure_eq [NeZero n] {Ω : Set (Rn n)} {C : ℝ≥0} {u χ : Rn n → ℝ}
    (h : InnerVariational.IsVariationalSolution Ω C u χ) :
    laplacianMeasure Ω u χ = InnerVariational.laplacianMeasure Ω u χ := by
  simp only [laplacianMeasure, InnerVariational.laplacianMeasure, reducedBoundary_eq,
    sigmaH_eq h, alphaN_eq, heightHZero_eq]
  rfl

theorem hasDistribLaplacianOn_iff {Ω : Set (Rn n)} {u : Rn n → ℝ} {μ : Measure (Rn n)} :
    HasDistribLaplacianOn Ω u μ ↔ InnerVariational.HasDistribLaplacianOn Ω u μ :=
  Iff.rfl

theorem exists_isGaussGreenPair_pos (hn : 2 ≤ n) {Ω : Set (Rn n)} {C : ℝ≥0} {u χ : Rn n → ℝ}
    (h : InnerVariational.IsVariationalSolution Ω C u χ) :
    ∃ μ ν, IsGaussGreenPair Ω {x | 0 < u x} μ ν := by
  obtain ⟨μ, ν, hp⟩ :=
    (InnerVariational.ChallengeHelpers.hasLocallyFinitePerimeter_inter_iff h.isOpen).1
    (InnerVariational.Main.hasLocallyFinitePerimeter_inter_pos hn h)
  exact ⟨μ, ν, isGaussGreenPair_iff.2 hp⟩

/-! ### Theorem 1.2 (iv): the exceptional set -/

theorem exceptional_subset [NeZero n] {Ω : Set (Rn n)} {u χ : Rn n → ℝ} :
    {x | x ∈ Ω ∧ x ∈ frontier {y | 0 < u y} ∧
      x ∉ reducedBoundary Ω {y | 0 < u y} ∧
      ¬ (Tendsto (fun r => r * (∫ y in ball x r, (‖gradient u y‖ ^ 2 + χ y - 1)) /
            ∫ y in sphere x r, u y ^ 2 ∂hausdorffN n (n - 1)) (𝓝[>] 0) (𝓝 1) ∧
          ∃ ν : Rn n, ‖ν‖ = 1 ∧
            Tendsto (fun r => r * (∫ y in ball x r,
                ‖gradient u y - (√(heightH u x r) * alphaN n) •
                  gradient (fun z => |⟪z - x, ν⟫|) y‖ ^ 2) /
              ∫ y in sphere x r, u y ^ 2 ∂hausdorffN n (n - 1)) (𝓝[>] 0) (𝓝 0))} ⊆
    {x | x ∈ Ω ∧ x ∈ frontier {y | 0 < u y} ∧
      x ∉ InnerVariational.reducedBoundary Ω {y | 0 < u y} ∧
      ¬ (Tendsto (fun r => r * (∫ y in ball x r, (‖gradient u y‖ ^ 2 + χ y - 1)) /
            InnerVariational.sphereIntegral (fun y => u y ^ 2) x r) (𝓝[>] 0) (𝓝 1) ∧
          ∃ ν : Rn n, ‖ν‖ = 1 ∧
            Tendsto (fun r => r * (∫ y in ball x r,
                ‖gradient u y - (√(InnerVariational.heightH u x r) * InnerVariational.alphaN n) •
                  gradient (InnerVariational.absProfile ν x) y‖ ^ 2) /
              InnerVariational.sphereIntegral (fun y => u y ^ 2) x r) (𝓝[>] 0) (𝓝 0))} := by
  rintro x ⟨hx, hfr, hred, hnot⟩
  refine ⟨hx, hfr, by rwa [← reducedBoundary_eq], fun ⟨h1, ν, hν, h2⟩ => hnot ⟨?_, ν, hν, ?_⟩⟩
  · refine h1.congr' (eventually_nhdsWithin_of_forall fun r hr => ?_)
    simp only [integral_sphere_eq _ _ hr]
  · refine h2.congr' (eventually_nhdsWithin_of_forall fun r hr => ?_)
    simp only [integral_sphere_eq _ _ hr, heightH_eq _ _ hr, alphaN_eq]
    rfl

end KWChallenge.Bridge

open KWChallenge KWChallenge.Bridge

theorem challenge_main_theorem (n : ℕ) [NeZero n] : MainTheoremClaim n := by
  intro hn Ω C u χ hΩ hKW
  have h := isVariationalSolution_iff.1 hKW
  obtain ⟨hi, hii, hiii, hiv⟩ := InnerVariational.Statements.main_theorem hn hΩ h
  refine ⟨hi, hii, ⟨tendsto_heightHZero h, ?_⟩, measure_mono_null exceptional_subset hiv⟩
  rw [hasDistribLaplacianOn_iff, laplacianMeasure_eq h]
  exact hiii

theorem challenge_chi_eq_indicator (n : ℕ) : ChiIdentificationClaim n := by
  intro hn Ω C u χ hΩ hKW
  exact InnerVariational.Statements.chi_eq_indicator hn hΩ (isVariationalSolution_iff.1 hKW)

theorem challenge_laplacian_measure_eq (n : ℕ) [NeZero n] : LaplacianMeasureClaim n := by
  intro hn Ω C u χ hKW
  have h := isVariationalSolution_iff.1 hKW
  obtain ⟨hrect, hfin, hlap⟩ := InnerVariational.Statements.laplacian_measure_eq hn h
  refine ⟨hrect, hfin, exists_isGaussGreenPair_pos hn h, tendsto_heightHZero h, ?_⟩
  rw [hasDistribLaplacianOn_iff, laplacianMeasure_eq h]
  exact hlap
