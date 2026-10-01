import Statement
import InnerVariational

/-!
# Solution: model solutions

Both model functions are classical solutions of the one-phase problem on `ℝⁿ` (harmonic and
linear where positive, free boundary the hyperplane `{y_n = 0}`, unit slope on each positive
side), so the library's theorem that classical solutions are variational solutions
(`InnerVariational.Registry.IsClassicalSolution.isVariationalSolution`) gives the first and third
items. Membership in `Σ^H` is decided with the library's density characterization
(`mem_sigmaH_iff_tendsto_volume`): the density of `{χ = 1}` at `0` is `1/2` for the half-plane
(reflection symmetry) and `1` for the two-plane solution (the hyperplane is Lebesgue-null). The
normalization of `α(n)` is a scaling computation with the library's sphere integral.

The trusted vocabulary is reconciled with the library's as in the `main-theorem` solution.
-/

open MeasureTheory Metric Set Filter Topology InnerProductSpace
open scoped NNReal ENNReal RealInnerProductSpace Laplacian

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

namespace KWChallenge.Model

open KWChallenge.Bridge

variable {n : ℕ} [NeZero n]

/-- The coordinate function `y ↦ y_n`. -/
abbrev coord (n : ℕ) [NeZero n] : Rn n → ℝ := fun y => y (lastCoord n)

/-- The unit vector `e_n`. -/
def en (n : ℕ) [NeZero n] : Rn n := EuclideanSpace.single (lastCoord n) 1

theorem en_apply : en n (lastCoord n) = 1 := by
  simp [en]

theorem norm_en : ‖en n‖ = 1 := by
  simp [en]

theorem coord_eq_inner (y : Rn n) : coord n y = ⟪en n, y⟫ := by
  simp [en, EuclideanSpace.inner_single_left]

theorem coord_add_smul (x : Rn n) (t : ℝ) (v : Rn n) :
    coord n (x + t • v) = coord n x + t * coord n v := by
  simp [coord]

theorem hasGradientAt_coord (x : Rn n) : HasGradientAt (coord n) (en n) x := by
  have hfun : coord n = fun y => ⟪en n, y⟫ := funext coord_eq_inner
  rw [hfun, hasGradientAt_iff_hasFDerivAt]
  convert (innerSL ℝ (en n)).hasFDerivAt using 1 <;> rfl

theorem gradient_coord (x : Rn n) : gradient (coord n) x = en n :=
  (hasGradientAt_coord x).gradient

theorem contDiff_coord : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (coord n) :=
  (EuclideanSpace.proj (lastCoord n) : Rn n →L[ℝ] ℝ).contDiff

theorem continuous_coord : Continuous (coord n) :=
  (EuclideanSpace.proj (lastCoord n) : Rn n →L[ℝ] ℝ).continuous

theorem lipschitzWith_coord : LipschitzWith 1 (coord n) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [NNReal.coe_one, one_mul, Real.dist_eq, dist_eq_norm]
  have := PiLp.norm_apply_le (x - y) (lastCoord n)
  simpa [coord, Real.norm_eq_abs] using this

theorem harmonicAt_coord (x : Rn n) : HarmonicAt (coord n) x := by
  have hfun : coord n = ⇑(innerSL ℝ (en n)) := funext fun y => by
    rw [coord_eq_inner]
    rfl
  have hfd : fderiv ℝ (coord n) = fun _ => innerSL ℝ (en n) := by
    funext w
    rw [hfun]
    exact (innerSL ℝ (en n)).fderiv
  have h2 : ∀ z, iteratedFDeriv ℝ 2 (coord n) z = 0 := by
    intro z
    ext m
    rw [iteratedFDeriv_two_apply, hfd, fderiv_const_apply]
    simp
  refine ⟨(EuclideanSpace.proj (lastCoord n) : Rn n →L[ℝ] ℝ).contDiff.contDiffAt,
    Eventually.of_forall fun y => ?_⟩
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp [h2]

theorem isOpenMap_coord : IsOpenMap (coord n) :=
  (EuclideanSpace.proj (lastCoord n) : Rn n →L[ℝ] ℝ).isOpenMap fun t =>
    ⟨t • en n, by simp [en]⟩

theorem frontier_coord_preimage (s : Set ℝ) :
    frontier (coord n ⁻¹' s) = coord n ⁻¹' frontier s :=
  (isOpenMap_coord.preimage_frontier_eq_frontier_preimage continuous_coord s).symm

/-- The hyperplane `{y_n = 0}` is Lebesgue-null. -/
theorem volume_hyperplane : volume (coord n ⁻¹' {0}) = 0 := by
  have hker : coord n ⁻¹' {0} =
      (LinearMap.ker (EuclideanSpace.proj (lastCoord n) : Rn n →L[ℝ] ℝ).toLinearMap :
        Set (Rn n)) := by
    ext y
    simp [coord]
  rw [hker]
  refine Measure.addHaar_submodule volume _ fun htop => ?_
  have : en n ∈ LinearMap.ker (EuclideanSpace.proj (lastCoord n) : Rn n →L[ℝ] ℝ).toLinearMap := by
    rw [htop]
    trivial
  simp [en] at this

/-! ### The free boundary condition along `± e_n` -/

theorem inward_point (x : Rn n) (hx : coord n x = 0) (s t : ℝ) :
    coord n (x + t • (s * ‖gradient (coord n) x‖⁻¹) • gradient (coord n) x) = t * s := by
  rw [gradient_coord, norm_en, inv_one, mul_one, coord_add_smul, hx]
  simp [coord, en]

/-! ### The half-plane solution -/

theorem halfPlane_eq : halfPlaneSolution n = fun y => max (coord n y) 0 := rfl

theorem posSet_halfPlane : {y | 0 < halfPlaneSolution n y} = coord n ⁻¹' Ioi 0 := by
  ext y
  simp [halfPlaneSolution, coord]

theorem frontier_halfPlane : frontier {y | 0 < halfPlaneSolution n y} = coord n ⁻¹' {0} := by
  rw [posSet_halfPlane, frontier_coord_preimage, frontier_Ioi]

theorem isClassicalSolution_halfPlane :
    InnerVariational.IsClassicalSolution univ (halfPlaneSolution n) where
  isOpen := isOpen_univ
  lipschitzOnWith := ⟨1, (lipschitzWith_coord.max_const 0).lipschitzOnWith⟩
  nonneg _ _ := le_max_right _ _
  harmonicAt x _ hx := by
    have hx' : 0 < coord n x := by simpa [halfPlaneSolution, coord] using hx
    refine (harmonicAt_congr_nhds ?_).2 (harmonicAt_coord x)
    filter_upwards [(isOpen_lt continuous_const continuous_coord).mem_nhds hx'] with y hy
    exact max_eq_left hy.le
  free_boundary x hx := by
    have hx0 : coord n x = 0 := by
      have := hx.2
      rwa [frontier_halfPlane] at this
    refine ⟨1, one_pos, coord n, contDiff_coord, ?_, ?_, ?_⟩
    · rw [gradient_coord, ← norm_ne_zero_iff, norm_en]
      exact one_ne_zero
    · rw [frontier_halfPlane]
      rfl
    · rintro s (rfl | rfl) hpos
      · refine tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun t (ht : 0 < t) => ?_)
        simp only [halfPlane_eq, inward_point x hx0, mul_one, hx0, max_self, sub_zero,
          max_eq_left ht.le]
        exact (div_self ht.ne').symm
      · exfalso
        obtain ⟨t, h1, ht⟩ := (hpos.and self_mem_nhdsWithin).exists
        simp only [halfPlane_eq, inward_point x hx0] at h1
        rw [max_eq_right (by have : (0 : ℝ) < t := ht; linarith)] at h1
        exact lt_irrefl _ h1

theorem isVariationalSolution_halfPlane :
    InnerVariational.IsVariationalSolution univ 1 (halfPlaneSolution n)
      (InnerVariational.posIndicator (halfPlaneSolution n)) :=
  InnerVariational.Registry.IsClassicalSolution.isVariationalSolution isClassicalSolution_halfPlane
    (lipschitzWith_coord.max_const 0).lipschitzOnWith

/-! ### The two-plane solution -/

theorem twoPlane_eq : twoPlaneSolution n = fun y => |coord n y| := rfl

theorem posSet_twoPlane : {y | 0 < twoPlaneSolution n y} = coord n ⁻¹' {0}ᶜ := by
  ext y
  simp [twoPlaneSolution, coord]

theorem frontier_twoPlane : frontier {y | 0 < twoPlaneSolution n y} = coord n ⁻¹' {0} := by
  rw [posSet_twoPlane, frontier_coord_preimage, frontier_compl, frontier, closure_singleton,
    interior_singleton, sdiff_empty]

theorem lipschitzWith_twoPlane : LipschitzWith 1 (twoPlaneSolution n) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  simp only [NNReal.coe_one, one_mul, twoPlane_eq, Real.dist_eq]
  refine (abs_abs_sub_abs_le_abs_sub _ _).trans ?_
  simpa [Real.dist_eq] using lipschitzWith_coord.dist_le_mul x y

theorem isClassicalSolution_twoPlane :
    InnerVariational.IsClassicalSolution univ (twoPlaneSolution n) where
  isOpen := isOpen_univ
  lipschitzOnWith := ⟨1, lipschitzWith_twoPlane.lipschitzOnWith⟩
  nonneg _ _ := abs_nonneg _
  harmonicAt x _ hx := by
    have hx' : coord n x ≠ 0 := by simpa [twoPlaneSolution, coord] using hx
    rcases hx'.lt_or_gt with hneg | hpos
    · refine (harmonicAt_congr_nhds ?_).2 (harmonicAt_coord x).neg
      filter_upwards [(isOpen_lt continuous_coord continuous_const).mem_nhds hneg] with y hy
      exact abs_of_neg hy
    · refine (harmonicAt_congr_nhds ?_).2 (harmonicAt_coord x)
      filter_upwards [(isOpen_lt continuous_const continuous_coord).mem_nhds hpos] with y hy
      exact abs_of_pos hy
  free_boundary x hx := by
    have hx0 : coord n x = 0 := by
      have := hx.2
      rwa [frontier_twoPlane] at this
    refine ⟨1, one_pos, coord n, contDiff_coord, ?_, ?_, ?_⟩
    · rw [gradient_coord, ← norm_ne_zero_iff, norm_en]
      exact one_ne_zero
    · rw [frontier_twoPlane]
      rfl
    · rintro s hs -
      refine tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun t (ht : 0 < t) => ?_)
      simp only [twoPlane_eq, inward_point x hx0, hx0, abs_zero, sub_zero]
      rcases hs with rfl | rfl
      · rw [mul_one, abs_of_pos ht, div_self ht.ne']
      · rw [mul_neg_one, abs_neg, abs_of_pos ht, div_self ht.ne']

theorem isVariationalSolution_twoPlane :
    InnerVariational.IsVariationalSolution univ 1 (twoPlaneSolution n)
      (InnerVariational.posIndicator (twoPlaneSolution n)) :=
  InnerVariational.Registry.IsClassicalSolution.isVariationalSolution isClassicalSolution_twoPlane
    lipschitzWith_twoPlane.lipschitzOnWith

/-! ### `Σ^H` at the origin -/

omit [NeZero n] in
theorem setOf_posIndicator_eq_one (u : Rn n → ℝ) :
    {y | InnerVariational.posIndicator u y = 1} = {y | 0 < u y} := by
  ext y
  by_cases h : 0 < u y <;> simp [InnerVariational.posIndicator, h]

/-- The half-space `{y_n > 0}` fills half of every ball centred on the hyperplane. -/
theorem volume_half {r : ℝ} (hr : 0 < r) :
    volume (coord n ⁻¹' Ioi 0 ∩ ball (0 : Rn n) r) / volume (ball (0 : Rn n) r) = 2⁻¹ := by
  set P := coord n ⁻¹' Ioi 0 with hP
  set N := coord n ⁻¹' Iio 0 with hN
  set B := ball (0 : Rn n) r with hB
  have hPm : MeasurableSet P := measurableSet_Ioi.preimage continuous_coord.measurable
  have h1 : volume (B ∩ P) + volume (B \ P) = volume B := measure_inter_add_sdiff B hPm
  have h2 : volume (B \ P) = volume (B ∩ N) := by
    have hset : (B \ P) \ coord n ⁻¹' {0} = B ∩ N := by
      ext y
      simp only [hP, hN, hB, Set.mem_sdiff, mem_inter_iff, mem_preimage, mem_Ioi, mem_Iio,
        mem_singleton_iff, not_lt]
      constructor
      · rintro ⟨⟨hb, hle⟩, hne⟩
        exact ⟨hb, lt_of_le_of_ne hle hne⟩
      · rintro ⟨hb, hlt⟩
        exact ⟨⟨hb, hlt.le⟩, hlt.ne⟩
    rw [← hset, measure_sdiff_null volume_hyperplane]
  have h3 : volume (B ∩ N) = volume (B ∩ P) := by
    have hpre : (LinearIsometryEquiv.neg ℝ : Rn n ≃ₗᵢ[ℝ] Rn n) ⁻¹' (B ∩ P) = B ∩ N := by
      ext y
      simp [hP, hN, hB, coord]
    rw [← hpre, (LinearIsometryEquiv.neg ℝ : Rn n ≃ₗᵢ[ℝ] Rn n).measurePreserving.measure_preimage
      (measurableSet_ball.inter hPm).nullMeasurableSet]
  set a := volume (B ∩ P) with ha
  have hBa : volume B = 2 * a := by rw [← h1, h2, h3, two_mul]
  have hB0 : volume B ≠ 0 := (measure_ball_pos volume _ hr).ne'
  have ha0 : a ≠ 0 := fun h => hB0 (by rw [hBa, h, mul_zero])
  have hatop : a ≠ ⊤ := ne_top_of_le_ne_top measure_ball_lt_top.ne
    (measure_mono inter_subset_left)
  rw [inter_comm, ← ha, hBa, ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inl two_ne_zero)
    (Or.inl (by norm_num)), mul_assoc, ENNReal.inv_mul_cancel ha0 hatop, mul_one]

theorem zero_notMem_sigmaH_halfPlane :
    (0 : Rn n) ∉ InnerVariational.sigmaH univ (halfPlaneSolution n)
      (InnerVariational.posIndicator (halfPlaneSolution n)) := by
  intro h0
  obtain ⟨-, -, -, hlim⟩ := isVariationalSolution_halfPlane.mem_sigmaH_iff_tendsto_volume.1 h0
  rw [setOf_posIndicator_eq_one, posSet_halfPlane] at hlim
  have hhalf : Tendsto (fun r => volume (coord n ⁻¹' Ioi 0 ∩ ball (0 : Rn n) r) /
      volume (ball (0 : Rn n) r)) (𝓝[>] 0) (𝓝 2⁻¹) :=
    tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun r hr => (volume_half hr).symm)
  have h12 := tendsto_nhds_unique hlim hhalf
  have : (2 : ℝ≥0∞)⁻¹ < 1 := ENNReal.inv_lt_one.2 (by norm_num)
  exact this.ne h12.symm

theorem zero_mem_sigmaH_twoPlane :
    (0 : Rn n) ∈ InnerVariational.sigmaH univ (twoPlaneSolution n)
      (InnerVariational.posIndicator (twoPlaneSolution n)) := by
  refine isVariationalSolution_twoPlane.mem_sigmaH_iff_tendsto_volume.2
    ⟨mem_univ _, ?_, by simp [twoPlaneSolution], ?_⟩
  · apply frontier_subset_closure
    rw [frontier_twoPlane]
    simp [coord]
  · rw [setOf_posIndicator_eq_one, posSet_twoPlane]
    refine tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun r (hr : 0 < r) => ?_)
    dsimp only
    rw [preimage_compl, inter_comm, ← sdiff_eq, measure_sdiff_null volume_hyperplane,
      ENNReal.div_self (measure_ball_pos volume _ hr).ne' measure_ball_lt_top.ne]

/-! ### The normalization of `α(n)` -/

theorem heightH_alpha {r : ℝ} (hr : 0 < r) :
    heightH (fun y => alphaN n * |y (lastCoord n)|) 0 r = 1 := by
  set K := ∫ ω, (ω : Rn n) (lastCoord n) ^ 2 ∂GMTFoundations.sphereMeasure n with hKdef
  have hI : ∫ y in sphere (0 : Rn n) 1, y (lastCoord n) ^ 2 ∂hausdorffN n (n - 1) = K := by
    rw [integral_sphere_eq _ _ one_pos, GMTFoundations.sphereIntegral]
    simp [hKdef]
  have hα : alphaN n = 1 / √K := by rw [alphaN, hI]
  have hpos : 0 < alphaN n := by
    rw [alphaN_eq]
    exact InnerVariational.Singular.alphaN_pos
  have hK : 0 < K := by
    rw [hα] at hpos
    exact Real.sqrt_pos.1 (one_div_pos.1 hpos)
  have hpow : r ^ (n - 1) * r ^ 2 = r ^ (n + 1) := by
    rw [← pow_add]
    congr 1
    have := NeZero.ne n
    omega
  rw [heightH_eq _ _ hr, InnerVariational.heightH, GMTFoundations.sphereIntegral]
  simp only [zero_add, PiLp.smul_apply, smul_eq_mul, mul_pow, sq_abs]
  rw [integral_const_mul, integral_const_mul, ← hKdef, hα, div_pow, Real.sq_sqrt hK.le]
  have hr' : r ^ (n + 1) ≠ 0 := pow_ne_zero _ hr.ne'
  rw [← hpow] at hr' ⊢
  field_simp

end KWChallenge.Model

open KWChallenge KWChallenge.Bridge KWChallenge.Model

theorem challenge_model_cases (n : ℕ) [NeZero n] : ModelCasesClaim n := by
  have hp : ∀ u : Rn n → ℝ, posIndicator u = InnerVariational.posIndicator u := fun _ => rfl
  refine ⟨⟨isVariationalSolution_iff.2 isVariationalSolution_halfPlane, ?_⟩,
    ⟨isVariationalSolution_iff.2 isVariationalSolution_twoPlane, ?_⟩, fun r hr => heightH_alpha hr⟩
  · rw [hp, sigmaH_eq isVariationalSolution_halfPlane]
    exact zero_notMem_sigmaH_halfPlane
  · rw [hp, sigmaH_eq isVariationalSolution_twoPlane]
    exact zero_mem_sigmaH_twoPlane
