/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Sobolev.Lipschitz
public import InnerVariational.Sobolev.WeakGradient
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Data.Real.StarOrdered
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Real.Hom
public import GMTFoundations.Defs.Sobolev

/-!
# Sobolev API for frequency blow-ups

The `W^{1,2}` layer used in Section 5 of Kriventsov–Weiss, built on the weak gradients
(`GMTFoundations.HasWeakGradient`, `GMTFoundations.MemH1`) of the dependency gmt-foundations
v0.1.0 (https://github.com/willmfeldman/gmt-foundations). A `W^{1,2}` function is an `L²`
function together with an `L²` weak gradient, carried as explicit data.

## Main definitions

* `WeakTendstoL2 μ F G`: weak convergence `F k ⇀ G` in `L²(μ; E)`, meaning
  `∫ ⟪F k, h⟫ → ∫ ⟪G, h⟫` for every `h ∈ L²(μ; E)`. This is the form of weak convergence in
  `exists_weakly_convergent_subseq` (`Blowup/WeakCompactness.lean`).

## Main results

* `WeakTendstoL2.integral_norm_sq_le`, `WeakTendstoL2.integral_norm_sq_le_of_tendsto`: lower
  semicontinuity of `∫ ‖F‖²` under weak `L²` convergence.
* `WeakTendstoL2.tendsto_integral_norm_sub_sq`: weak convergence plus convergence of norms gives
  strong convergence (used twice in the proof of Theorem 5.3: away from the hyperplane
  `{x_n = 0}`, and then on the whole annulus `B_{7/8} \ B_{5/8}`).
* `weakTendstoL2_of_tendsto_integral_norm_sub_sq`: strong `L²` convergence implies weak.
* `hasWeakGrad_of_tendsto`: weak gradients pass to limits. In particular, if Lipschitz
  `f_k → F` in `L²(Ω)` and `∇f_k ⇀ G` weakly in `L²(Ω)`, then `G` is the weak gradient of `F`.

## References

* D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
  DOI 10.1002/cpa.22226; arXiv:2306.10131. Result and equation numbers refer to arXiv v2.
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational

/-! ### Weak convergence in `L²` -/

section WeakL2

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Weak convergence `F k ⇀ G` in `L²(μ; E)`: `∫ ⟪F k, h⟫ → ∫ ⟪G, h⟫` for every `h ∈ L²(μ; E)`. -/
def WeakTendstoL2 (μ : Measure α) (F : ℕ → α → E) (G : α → E) : Prop :=
  ∀ h : α → E, MemLp h 2 μ →
    Tendsto (fun k => ∫ x, ⟪F k x, h x⟫ ∂μ) atTop (𝓝 (∫ x, ⟪G x, h x⟫ ∂μ))

/-- The pointwise inner product of two `L²` functions is integrable. -/
theorem MemLp.integrable_inner_two {f g : α → E} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun x => ⟪f x, g x⟫) μ := by
  refine (L2.integrable_inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)).congr ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
  rw [h1, h2]

/-- The squared norm of an `L²` function is integrable. -/
theorem MemLp.integrable_norm_sq {f : α → E} (hf : MemLp f 2 μ) :
    Integrable (fun x => ‖f x‖ ^ 2) μ := by
  refine ((MemLp.integrable_inner_two hf) hf).congr (Eventually.of_forall fun x => ?_)
  simp only [real_inner_self_eq_norm_sq]

/-- `∫ ⟪f, g⟫` as the `L²` inner product. -/
theorem integral_inner_eq_inner_toLp {f g : α → E} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ∫ x, ⟪f x, g x⟫ ∂μ = ⟪hf.toLp f, hg.toLp g⟫ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
  rw [h1, h2]

/-- `∫ ‖f‖²` as the squared `L²` norm. -/
theorem integral_norm_sq_eq_norm_toLp_sq {f : α → E} (hf : MemLp f 2 μ) :
    ∫ x, ‖f x‖ ^ 2 ∂μ = ‖hf.toLp f‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← integral_inner_eq_inner_toLp hf hf]
  simp only [real_inner_self_eq_norm_sq]

/-- **Cauchy–Schwarz for `L²` integrals.** -/
theorem abs_integral_inner_le {f g : α → E} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ x, ⟪f x, g x⟫ ∂μ| ≤ √(∫ x, ‖f x‖ ^ 2 ∂μ) * √(∫ x, ‖g x‖ ^ 2 ∂μ) := by
  rw [integral_inner_eq_inner_toLp hf hg, integral_norm_sq_eq_norm_toLp_sq hf,
    integral_norm_sq_eq_norm_toLp_sq hg, Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_sq (norm_nonneg _)]
  exact abs_real_inner_le_norm _ _

/-- The pointwise bound `⟪a, b⟫ ≤ (‖a‖² + ‖b‖²)/2`, integrated. -/
theorem integral_inner_le_half_add {f g : α → E} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ∫ x, ⟪f x, g x⟫ ∂μ ≤ ((∫ x, ‖f x‖ ^ 2 ∂μ) + ∫ x, ‖g x‖ ^ 2 ∂μ) / 2 := by
  rw [← integral_add (MemLp.integrable_norm_sq hf) (MemLp.integrable_norm_sq hg), ← integral_div]
  refine integral_mono ((MemLp.integrable_inner_two hf) hg)
    (((MemLp.integrable_norm_sq hf).add (MemLp.integrable_norm_sq hg)).div_const 2) fun x => ?_
  have h := norm_sub_sq_real (f x) (g x)
  have h0 := sq_nonneg ‖f x - g x‖
  simp only
  linarith

/-- **Lower semicontinuity of `∫ ‖F‖²` under weak `L²` convergence**, bound form. If
`F k ⇀ G` in `L²` and eventually `∫ ‖F k‖² ≤ C`, then `∫ ‖G‖² ≤ C`. -/
theorem WeakTendstoL2.integral_norm_sq_le {F : ℕ → α → E} {G : α → E} (hw : WeakTendstoL2 μ F G)
    (hF : ∀ k, MemLp (F k) 2 μ) (hG : MemLp G 2 μ) {C : ℝ}
    (hC : ∀ᶠ k in atTop, ∫ x, ‖F k x‖ ^ 2 ∂μ ≤ C) : ∫ x, ‖G x‖ ^ 2 ∂μ ≤ C := by
  have hlim := hw G hG
  have hGG : ∫ x, ⟪G x, G x⟫ ∂μ = ∫ x, ‖G x‖ ^ 2 ∂μ := by
    simp only [real_inner_self_eq_norm_sq]
  rw [hGG] at hlim
  have hle : ∫ x, ‖G x‖ ^ 2 ∂μ ≤ (C + ∫ x, ‖G x‖ ^ 2 ∂μ) / 2 := by
    refine le_of_tendsto hlim ?_
    filter_upwards [hC] with k hk
    exact (integral_inner_le_half_add (hF k) hG).trans (by linarith)
  linarith

/-- **Lower semicontinuity of `∫ ‖F‖²` under weak `L²` convergence**, limit form:
`∫ ‖G‖² ≤ lim ∫ ‖F k‖²`. -/
theorem WeakTendstoL2.integral_norm_sq_le_of_tendsto {F : ℕ → α → E} {G : α → E}
    (hw : WeakTendstoL2 μ F G) (hF : ∀ k, MemLp (F k) 2 μ) (hG : MemLp G 2 μ) {L : ℝ}
    (hL : Tendsto (fun k => ∫ x, ‖F k x‖ ^ 2 ∂μ) atTop (𝓝 L)) : ∫ x, ‖G x‖ ^ 2 ∂μ ≤ L := by
  have hlim := hw G hG
  have hGG : ∫ x, ⟪G x, G x⟫ ∂μ = ∫ x, ‖G x‖ ^ 2 ∂μ := by
    simp only [real_inner_self_eq_norm_sq]
  rw [hGG] at hlim
  have hle : ∫ x, ‖G x‖ ^ 2 ∂μ ≤ (L + ∫ x, ‖G x‖ ^ 2 ∂μ) / 2 :=
    le_of_tendsto_of_tendsto' hlim ((hL.add_const _).div_const 2) fun k =>
      integral_inner_le_half_add (hF k) hG
  linarith

/-- **Weak convergence plus convergence of norms gives strong convergence** in `L²`. -/
theorem WeakTendstoL2.tendsto_integral_norm_sub_sq {F : ℕ → α → E} {G : α → E}
    (hw : WeakTendstoL2 μ F G) (hF : ∀ k, MemLp (F k) 2 μ) (hG : MemLp G 2 μ)
    (hnorm : Tendsto (fun k => ∫ x, ‖F k x‖ ^ 2 ∂μ) atTop (𝓝 (∫ x, ‖G x‖ ^ 2 ∂μ))) :
    Tendsto (fun k => ∫ x, ‖F k x - G x‖ ^ 2 ∂μ) atTop (𝓝 0) := by
  have hexp : ∀ k, ∫ x, ‖F k x - G x‖ ^ 2 ∂μ =
      (∫ x, ‖F k x‖ ^ 2 ∂μ) - 2 * (∫ x, ⟪F k x, G x⟫ ∂μ) + ∫ x, ‖G x‖ ^ 2 ∂μ := by
    intro k
    simp_rw [norm_sub_sq_real]
    rw [integral_add _ (MemLp.integrable_norm_sq hG),
      integral_sub (MemLp.integrable_norm_sq (hF k)),
      integral_const_mul]
    · exact ((MemLp.integrable_inner_two (hF k)) hG).const_mul 2
    · exact (MemLp.integrable_norm_sq (hF k)).sub
        (((MemLp.integrable_inner_two (hF k)) hG).const_mul 2)
  have hlim := hw G hG
  have hGG : ∫ x, ⟪G x, G x⟫ ∂μ = ∫ x, ‖G x‖ ^ 2 ∂μ := by
    simp only [real_inner_self_eq_norm_sq]
  rw [hGG] at hlim
  simp_rw [hexp]
  have := ((hnorm.sub (hlim.const_mul 2)).add_const (∫ x, ‖G x‖ ^ 2 ∂μ))
  convert this using 2
  ring

/-- **Strong `L²` convergence implies weak `L²` convergence.** -/
theorem weakTendstoL2_of_tendsto_integral_norm_sub_sq {F : ℕ → α → E} {G : α → E}
    (hF : ∀ k, MemLp (F k) 2 μ) (hG : MemLp G 2 μ)
    (h : Tendsto (fun k => ∫ x, ‖F k x - G x‖ ^ 2 ∂μ) atTop (𝓝 0)) : WeakTendstoL2 μ F G := by
  intro φ hφ
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hbound : ∀ k, ‖(∫ x, ⟪F k x, φ x⟫ ∂μ) - ∫ x, ⟪G x, φ x⟫ ∂μ‖ ≤
      √(∫ x, ‖F k x - G x‖ ^ 2 ∂μ) * √(∫ x, ‖φ x‖ ^ 2 ∂μ) := by
    intro k
    rw [← integral_sub ((MemLp.integrable_inner_two (hF k)) hφ)
      ((MemLp.integrable_inner_two hG) hφ)]
    simp_rw [← inner_sub_left]
    exact abs_integral_inner_le ((hF k).sub hG) hφ
  refine squeeze_zero (fun k => norm_nonneg _) hbound ?_
  have : Tendsto (fun k => √(∫ x, ‖F k x - G x‖ ^ 2 ∂μ)) atTop (𝓝 0) := by
    simpa using (Real.continuous_sqrt.tendsto 0).comp h
  simpa using this.mul_const (√(∫ x, ‖φ x‖ ^ 2 ∂μ))

/-- Weak `L²` convergence restricts to measurable subsets. -/
theorem WeakTendstoL2.restrict {F : ℕ → α → E} {G : α → E} (hw : WeakTendstoL2 μ F G)
    {s : Set α} (hs : MeasurableSet s) : WeakTendstoL2 (μ.restrict s) F G := by
  intro h hh
  have hind : MemLp (s.indicator h) 2 μ := (memLp_indicator_iff_restrict hs).2 hh
  have e : ∀ K : α → E, ∫ x, ⟪K x, s.indicator h x⟫ ∂μ = ∫ x, ⟪K x, h x⟫ ∂(μ.restrict s) := by
    intro K
    rw [← integral_indicator hs]
    congr 1
    ext x
    by_cases hx : x ∈ s <;> simp [hx]
  simpa only [e] using hw _ hind

/-- Weak `L²` limits are additive. -/
theorem WeakTendstoL2.add {F F' : ℕ → α → E} {G G' : α → E} (hw : WeakTendstoL2 μ F G)
    (hw' : WeakTendstoL2 μ F' G') (hF : ∀ k, MemLp (F k) 2 μ) (hF' : ∀ k, MemLp (F' k) 2 μ)
    (hG : MemLp G 2 μ) (hG' : MemLp G' 2 μ) :
    WeakTendstoL2 μ (fun k x => F k x + F' k x) (fun x => G x + G' x) := by
  intro h hh
  have e : ∀ {K K' : α → E}, MemLp K 2 μ → MemLp K' 2 μ →
      ∫ x, ⟪K x + K' x, h x⟫ ∂μ = (∫ x, ⟪K x, h x⟫ ∂μ) + ∫ x, ⟪K' x, h x⟫ ∂μ := by
    intro K K' hK hK'
    simp_rw [inner_add_left]
    exact integral_add ((MemLp.integrable_inner_two hK) hh) (MemLp.integrable_inner_two hK' hh)
  simp only [e (hF _) (hF' _), e hG hG']
  exact (hw h hh).add (hw' h hh)

/-- Weak `L²` limits are homogeneous. -/
theorem WeakTendstoL2.const_smul {F : ℕ → α → E} {G : α → E} (hw : WeakTendstoL2 μ F G)
    (c : ℝ) : WeakTendstoL2 μ (fun k x => c • F k x) (fun x => c • G x) := by
  intro h hh
  simp_rw [inner_smul_left, conj_trivial, integral_const_mul]
  exact (hw h hh).const_mul c

end WeakL2

/-! ### Weak gradients of limits (the `W^{1,2}` encoding) -/

section WeakGrad

variable {n : ℕ}

/-- A continuous compactly supported function lies in `L²(Ω)`. -/
theorem memLp_two_restrict_of_continuous_of_hasCompactSupport {E : Type*}
    [NormedAddCommGroup E] {φ : Rn n → E} (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (Ω : Set (Rn n)) : MemLp φ 2 (volume.restrict Ω) :=
  (hφ.memLp_of_hasCompactSupport (μ := volume) hc).restrict Ω

/-- **Weak gradients pass to limits.** If `f k → F` strongly in `L²(Ω)`, `G k ⇀ Ginf` weakly in
`L²(Ω; ℝⁿ)`, and `G k` is the weak gradient of `f k` on `Ω`, then `Ginf` is the weak gradient of
`F` on `Ω`. This identifies the gradient of the Rellich limit in the proof of Lemma 5.1. -/
theorem hasWeakGrad_of_tendsto {Ω : Set (Rn n)} {f : ℕ → Rn n → ℝ} {F : Rn n → ℝ}
    {G : ℕ → Rn n → Rn n} {Ginf : Rn n → Rn n}
    (hf : ∀ k, MemLp (f k) 2 (volume.restrict Ω)) (hF : MemLp F 2 (volume.restrict Ω))
    (hfF : Tendsto (fun k => ∫ x in Ω, (f k x - F x) ^ 2) atTop (𝓝 0))
    (hGinf : MemLp Ginf 2 (volume.restrict Ω)) (hG : WeakTendstoL2 (volume.restrict Ω) G Ginf)
    (hgrad : ∀ k, GMTFoundations.HasWeakGradient Ω (f k) (G k)) :
    GMTFoundations.HasWeakGradient Ω F Ginf := by
  refine HasWeakGradient.of_single
    (locallyIntegrableOn_of_locallyIntegrable_restrict (hF.locallyIntegrable one_le_two))
    (locallyIntegrableOn_of_locallyIntegrable_restrict (hGinf.locallyIntegrable one_le_two))
    fun i φ hφ hφc hφΩ => ?_
  set e : Rn n := EuclideanSpace.single i (1 : ℝ)
  set dφ : Rn n → ℝ := fun x => fderiv ℝ φ x e
  have hdφ : MemLp dφ 2 (volume.restrict Ω) :=
    memLp_two_restrict_of_continuous_of_hasCompactSupport
      ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const) (hφc.fderiv_apply (𝕜 := ℝ) e) Ω
  have hψ : MemLp (fun x => φ x • e) 2 (volume.restrict Ω) :=
    memLp_two_restrict_of_continuous_of_hasCompactSupport (hφ.continuous.smul continuous_const)
      (hφc.smul_right (f' := fun _ => e)) Ω
  have hfw : WeakTendstoL2 (volume.restrict Ω) f F :=
    weakTendstoL2_of_tendsto_integral_norm_sub_sq hf hF
      (by simpa only [Real.norm_eq_abs, sq_abs] using hfF)
  have hinner_e : ∀ v : Rn n, ∀ x, ⟪v, φ x • e⟫ = v i * φ x := by
    intro v x
    simp [e, inner_smul_right, EuclideanSpace.inner_single_right, mul_comm]
  have h1 := hfw dφ hdφ
  have h2 := (hG _ hψ).neg
  simp only [hinner_e] at h2
  simp only [RCLike.inner_apply, conj_trivial] at h1
  have hk : ∀ k, ∫ x in Ω, dφ x * f k x = -∫ x in Ω, G k x i * φ x := by
    intro k
    rw [← HasWeakGradient.single (hgrad k) i hφ hφc hφΩ]
    exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
  simp only [hk] at h1
  have := tendsto_nhds_unique h1 h2
  rw [← this]
  exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)

end WeakGrad

end InnerVariational
