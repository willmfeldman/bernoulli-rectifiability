import Statement
import InnerVariational

/-!
# Solution: compactness of classical solutions

The trusted vocabulary of `Statement.lean` is reconciled with the library's, then the library
theorem `InnerVariational.Statements.classical_compactness` is applied.

* `IsClassicalSolution`, `IsVariationalSolution` and `IsGaussGreenPair` have the same fields as
  the library's; `hausdorffN`, `posIndicator`, `IsCountablyRectifiable`, `HasDistribLaplacianOn`
  are definitionally the library's.
* Sphere integrals, `H_x(u; r)`, `H_x(u; 0+)`, `α(n)`, `Σ^H` and the Laplacian measure are
  reconciled exactly as in the `main-theorem` solution (`integral_sphere_eq`,
  `integral_sphere_last_sq`, `sigmaH_eq`, `laplacianMeasure_eq`).
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

noncomputable section

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

theorem isClassicalSolution_iff {Ω : Set (Rn n)} {u : Rn n → ℝ} :
    IsClassicalSolution Ω u ↔ InnerVariational.IsClassicalSolution Ω u :=
  ⟨fun h => ⟨h.1, h.2, h.3, h.4, h.5⟩, fun h => ⟨h.1, h.2, h.3, h.4, h.5⟩⟩

end KWChallenge.Bridge

open KWChallenge KWChallenge.Bridge

theorem challenge_classical_compactness (n : ℕ) [NeZero n] : ClassicalCompactnessClaim n := by
  intro hn u hu C hsup hlip
  obtain ⟨φ, hφ, v, hconv, hvlip, hv, hα, hdich, hrect, hfin, hlap⟩ :=
    InnerVariational.Statements.classical_compactness hn u
      (fun k => isClassicalSolution_iff.1 (hu k)) C hsup hlip
  have hp : posIndicator v = InnerVariational.posIndicator v := rfl
  refine ⟨φ, hφ, v, hconv, hvlip, isVariationalSolution_iff.2 hv, tendsto_heightHZero hv, ?_,
    hdich, hrect, hfin, ?_⟩
  · rw [hp, sigmaH_eq hv]
    simp only [heightHZero_eq, alphaN_eq]
    exact hα
  · rw [hasDistribLaplacianOn_iff, hp, laplacianMeasure_eq hv]
    exact hlap
