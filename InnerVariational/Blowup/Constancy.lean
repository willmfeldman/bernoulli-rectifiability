/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Blowup.Sobolev
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Algebra.Order.Ring.Star
import InnerVariational.Sobolev.WeakGradient
public import GMTFoundations.Defs.Sobolev

/-!
# Zero weak gradient on a connected open set

If `f` has zero weak gradient on a connected open set `Ω ⊆ ℝⁿ` (in gmt-foundations' sense,
`GMTFoundations.HasWeakGradient`, which includes `f ∈ L¹_loc(Ω)`), then `f` is a.e. equal to a
constant on `Ω`. This is the input for the first step of the proof of Theorem 5.3 of
Kriventsov–Weiss (full reference below), which identifies the limit `v` on the annulus
`A = B_1 \ B̄_{1/2}` as `β₊ (x_n)₊^N + β₋ (x_n)₋^N`. The paper calls the independence of `v` from
`x' = (x_1, …, x_{n-1})` "immediate from the assumption". The assumption only gives `∂_i v = 0`
a.e. on `A` for `i < n`, which forces independence of `x'` only on connected components of the
`x'`-slices of `A`. For `n = 2` the slices with `|x_2| < 1/2` are disconnected, so the implication
`∂_i v = 0 ⇒ independence` does not hold on its own (take
`v(x_1, x_2) = sgn(x_1) ψ(x_2)` with `0 ≢ ψ ∈ C_c^∞(-1/2, 1/2)`); it follows from the homogeneity
of `v` and the connectedness of the half-annuli. We argue as follows: by the weak Euler identity
`∇v·y = N v`, the function `x_n^{-N} v` has zero weak gradient on each connected half
`A_± = A ∩ {±x_n > 0}` of `A`, and this file makes it a.e. constant there.

## Main results

* `hasFDerivAt_convolution_eq_zero_of_hasWeakGrad_zero`: mollifying a function with zero weak
  gradient gives a function with zero derivative wherever the mollifier's support fits in `Ω`.
* `exists_ae_eq_const_ball_of_hasWeakGrad_zero`: local version, a.e. constant on a ball.
* `exists_ae_eq_const_of_hasWeakGrad_zero`: a.e. constant on a connected open set.

## Proof

Mollify: `φ_ε ⋆ f` has derivative `∫ f(t) Dφ_ε(z − t) dt`. The function `t ↦ φ_ε(z − t)` is a test
function, so this vanishes by the weak-gradient identity. So `φ_ε ⋆ f` is constant on a ball.
Lebesgue differentiation (`ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable`)
shows `f` is a.e. constant on the ball. Connectedness propagates the constant.

## References

* D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
  DOI 10.1002/cpa.22226; arXiv:2306.10131. Result and equation numbers refer to arXiv v2.
-/

open MeasureTheory Metric Set Filter Topology ContinuousLinearMap
open scoped NNReal ENNReal Convolution

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

/-- The bump functions with `rOut = 1/(k+1)` and `rIn = rOut/2`. -/
def shrinkingBumpSeq (k : ℕ) : ContDiffBump (0 : Rn n) where
  rIn := 1 / (2 * ((k : ℝ) + 1))
  rOut := 1 / ((k : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := one_div_lt_one_div_of_lt (by positivity) (by linarith)

@[simp] theorem shrinkingBumpSeq_rOut (k : ℕ) :
    (shrinkingBumpSeq (n := n) k).rOut = 1 / ((k : ℝ) + 1) := rfl

theorem shrinkingBumpSeq_rOut_le (k : ℕ) :
    (shrinkingBumpSeq (n := n) k).rOut ≤ 2 * (shrinkingBumpSeq (n := n) k).rIn := by
  simp only [shrinkingBumpSeq]
  have : (0 : ℝ) < k + 1 := by positivity
  field_simp
  rfl

theorem tendsto_shrinkingBumpSeq_rOut :
    Tendsto (fun k => (shrinkingBumpSeq (n := n) k).rOut) atTop (𝓝 0) := by
  simpa only [shrinkingBumpSeq_rOut] using tendsto_one_div_add_atTop_nhds_zero_nat

/-- A continuous linear functional on `ℝⁿ` vanishing on the coordinate vectors is zero. -/
theorem clm_eq_zero_of_single {L : Rn n →L[ℝ] ℝ}
    (h : ∀ i : Fin n, L (EuclideanSpace.single i 1) = 0) : L = 0 := by
  have hb : ∀ i, L ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis i) = 0 := by
    intro i
    simpa using h i
  apply ContinuousLinearMap.coe_injective
  exact (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.ext fun i => by simpa using hb i

/-- The test function `t ↦ φ(z − t)`: its derivative. -/
theorem fderiv_comp_const_sub_apply {φ : Rn n → ℝ} (hφ : Differentiable ℝ φ) (z t v : Rn n) :
    fderiv ℝ (fun y => φ (z - y)) t v = -fderiv ℝ φ (z - t) v := by
  have h : HasFDerivAt (fun y => φ (z - y))
      ((fderiv ℝ φ (z - t)).comp (0 - ContinuousLinearMap.id ℝ (Rn n))) t :=
    (hφ (z - t)).hasFDerivAt.comp t ((hasFDerivAt_const z t).sub (hasFDerivAt_id t))
  rw [h.fderiv]
  simp

/-- **Mollifying a function with zero weak gradient.** Let `f` have zero weak gradient on `Ω`,
let `g` be locally integrable with `g = f` on `closedBall z r ⊆ Ω`, and let `φ` be smooth with
`tsupport φ ⊆ closedBall 0 r`. Then `g ⋆ φ` has zero derivative at `z`. -/
theorem hasFDerivAt_convolution_eq_zero_of_hasWeakGrad_zero {Ω : Set (Rn n)} (hΩ : IsOpen Ω)
    {f g φ : Rn n → ℝ}
    (hW : GMTFoundations.HasWeakGradient Ω f (fun _ => (0 : Rn n))) (hg : LocallyIntegrable g)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) {z : Rn n} {r : ℝ}
    (hφs : tsupport φ ⊆ closedBall 0 r) (hzΩ : closedBall z r ⊆ Ω)
    (hgf : EqOn g f (closedBall z r)) :
    HasFDerivAt (g ⋆[lsmul ℝ ℝ, volume] φ) (0 : Rn n →L[ℝ] ℝ) z := by
  have hφc : HasCompactSupport φ :=
    (isCompact_closedBall 0 r).of_isClosed_subset (isClosed_tsupport φ) hφs
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by exact_mod_cast le_top)
  have hd := hφc.hasFDerivAt_convolution_right (lsmul ℝ ℝ) hg hφ1 z
  suffices hD : (g ⋆[(lsmul ℝ ℝ).precompR (Rn n), volume] fderiv ℝ φ) z = 0 by
    rwa [hD] at hd
  refine clm_eq_zero_of_single fun i => ?_
  set e : Rn n := EuclideanSpace.single i 1
  rw [convolution_precompR_apply (lsmul ℝ ℝ) hg (hφc.fderiv ℝ)
    (hφ1.continuous_fderiv one_ne_zero) z e, convolution_def]
  simp only [lsmul_apply, smul_eq_mul]
  -- The test function `ψ(t) = φ(z − t)`.
  set ψ : Rn n → ℝ := fun t => φ (z - t)
  have hψs : tsupport ψ ⊆ closedBall z r := by
    have : tsupport ψ = (fun t => z - t) ⁻¹' tsupport φ :=
      tsupport_comp_eq_preimage φ (Homeomorph.subLeft z)
    rw [this]
    intro t ht
    have := hφs ht
    rw [mem_closedBall_zero_iff] at this
    rw [mem_closedBall, dist_eq_norm, ← norm_neg, neg_sub]
    exact this
  have hψc : HasCompactSupport ψ :=
    (isCompact_closedBall z r).of_isClosed_subset (isClosed_tsupport ψ) hψs
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := hφ.comp (contDiff_const.sub contDiff_id)
  have hweak := HasWeakGradient.single hW i hψ hψc (hψs.trans hzΩ)
  simp only [PiLp.zero_apply, zero_mul, integral_zero, neg_zero] at hweak
  have hφd : Differentiable ℝ φ := hφ1.differentiable one_ne_zero
  -- Outside `closedBall z r` the integrand vanishes; inside, `g = f`.
  have hpt : ∀ t,
      g t * fderiv ℝ φ (z - t) e = -(Ω.indicator (fun t => f t * fderiv ℝ ψ t e) t) := by
    intro t
    by_cases ht : t ∈ closedBall z r
    · rw [indicator_of_mem (hzΩ ht), fderiv_comp_const_sub_apply hφd, hgf ht]
      ring
    · have h0 : fderiv ℝ φ (z - t) = 0 := by
        refine fderiv_of_notMem_tsupport ℝ fun hmem => ht ?_
        have := hφs hmem
        rw [mem_closedBall_zero_iff] at this
        rw [mem_closedBall, dist_eq_norm, ← norm_neg, neg_sub]
        exact this
      have h1 : fderiv ℝ ψ t e = 0 := by
        rw [fderiv_comp_const_sub_apply hφd, h0]
        simp
      by_cases htΩ : t ∈ Ω
      · rw [indicator_of_mem htΩ, h0, h1]; simp
      · rw [indicator_of_notMem htΩ, h0]; simp
  simp_rw [hpt]
  rw [integral_neg, integral_indicator hΩ.measurableSet, hweak, neg_zero]

/-- **Local constancy.** If `f` has zero weak gradient on the open set `Ω` (in particular
`f ∈ L¹_loc(Ω)`), then every point of `Ω` has a ball around it on which `f` is a.e. constant. -/
theorem exists_ae_eq_const_ball_of_hasWeakGrad_zero {Ω : Set (Rn n)} (hΩ : IsOpen Ω)
    {f : Rn n → ℝ} (hW : GMTFoundations.HasWeakGradient Ω f (fun _ => (0 : Rn n))) {x₀ : Rn n}
    (hx₀ : x₀ ∈ Ω) :
    ∃ R > 0, ∃ c : ℝ, ∀ᵐ x ∂(volume.restrict (ball x₀ R)), f x = c := by
  have hf : LocallyIntegrableOn f Ω := hW.1
  obtain ⟨ε, hε, hεΩ⟩ := Metric.isOpen_iff.1 hΩ x₀ hx₀
  set R := ε / 4 with hR
  have hR0 : 0 < R := by positivity
  set K := closedBall x₀ (2 * R) with hK
  have hKΩ : K ⊆ Ω := (closedBall_subset_ball (by linarith)).trans hεΩ
  set g : Rn n → ℝ := K.indicator f with hg_def
  have hg : LocallyIntegrable g :=
    ((integrable_indicator_iff measurableSet_closedBall).2
      (hf.integrableOn_compact_subset hKΩ (isCompact_closedBall _ _))).locallyIntegrable
  set F : ℕ → Rn n → ℝ := fun k =>
    g ⋆[lsmul ℝ ℝ, volume] (shrinkingBumpSeq (n := n) k).normed volume with hF_def
  -- For large `k`, `F k` is constant on `ball x₀ R`.
  have hconst : ∀ᶠ k in atTop, ∀ z ∈ ball x₀ R, F k z = F k x₀ := by
    have hev : ∀ᶠ k in atTop, (shrinkingBumpSeq (n := n) k).rOut < R :=
      tendsto_shrinkingBumpSeq_rOut.eventually (gt_mem_nhds hR0)
    filter_upwards [hev] with k hk
    set ρ := (shrinkingBumpSeq (n := n) k).rOut with hρ
    have hderiv : ∀ z ∈ ball x₀ R, HasFDerivAt (F k) (0 : Rn n →L[ℝ] ℝ) z := by
      intro z hz
      have hzK : closedBall z ρ ⊆ K := by
        intro y hy
        rw [mem_closedBall] at hy ⊢
        have := mem_ball.1 hz
        calc dist y x₀ ≤ dist y z + dist z x₀ := dist_triangle _ _ _
          _ ≤ 2 * R := by linarith
      refine hasFDerivAt_convolution_eq_zero_of_hasWeakGrad_zero hΩ hW hg
        ((shrinkingBumpSeq (n := n) k).contDiff_normed) ?_ (hzK.trans hKΩ) ?_
      · exact (ContDiffBump.tsupport_normed_eq (f := shrinkingBumpSeq (n := n) k)
          (μ := volume)).subset
      · intro y hy
        exact indicator_of_mem (hzK hy) f
    intro z hz
    exact isOpen_ball.is_const_of_fderiv_eq_zero (convex_ball x₀ R).isPreconnected
      (fun y hy => (hderiv y hy).differentiableAt.differentiableWithinAt)
      (fun y hy => (hderiv y hy).fderiv) hz (mem_ball_self hR0)
  -- Lebesgue differentiation.
  have hae := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (μ := volume)
    (tendsto_shrinkingBumpSeq_rOut (n := n)) (Eventually.of_forall shrinkingBumpSeq_rOut_le) hg
  have hflip : (lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).flip = lsmul ℝ ℝ := by
    ext
    simp
  have hFeq : ∀ k, (shrinkingBumpSeq (n := n) k).normed volume ⋆[lsmul ℝ ℝ, volume] g = F k := by
    intro k
    rw [← convolution_flip, hflip]
  have hball : volume.restrict (ball x₀ R) ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero]
    exact (measure_ball_pos volume x₀ hR0).ne'
  have hgood : ∀ᵐ x ∂(volume.restrict (ball x₀ R)),
      Tendsto (fun k => F k x₀) atTop (𝓝 (f x)) := by
    filter_upwards [ae_restrict_mem measurableSet_ball, ae_restrict_of_ae hae] with x hx hxt
    have hxK : x ∈ K :=
      (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))) hx
    have hfx : f x = g x := (indicator_of_mem hxK f).symm
    rw [hfx]
    refine hxt.congr' ?_
    filter_upwards [hconst] with k hk
    rw [hFeq k]
    exact hk x hx
  have : (ae (volume.restrict (ball x₀ R))).NeBot := ae_neBot.2 hball
  obtain ⟨x₁, hx₁⟩ := hgood.exists
  refine ⟨R, hR0, f x₁, ?_⟩
  filter_upwards [hgood] with x hx
  exact tendsto_nhds_unique hx hx₁

/-- An a.e. property on a ball holds a.e. on a smaller ball around each of its points. -/
theorem exists_ae_restrict_ball_of_mem_ball {p : Rn n → Prop} {x : Rn n} {R : ℝ}
    (h : ∀ᵐ y ∂(volume.restrict (ball x R)), p y) {z : Rn n} (hz : z ∈ ball x R) :
    ∃ R' > 0, ∀ᵐ y ∂(volume.restrict (ball z R')), p y :=
  ⟨R - dist z x, sub_pos.2 (mem_ball.1 hz),
    ae_restrict_of_ae_restrict_of_subset (ball_subset_ball' (by linarith)) h⟩

/-- **Zero weak gradient on a connected open set gives an a.e. constant.** If `f` has zero weak
gradient on the connected open set `Ω ⊆ ℝⁿ`, then `f = c` a.e. on `Ω`. -/
theorem exists_ae_eq_const_of_hasWeakGrad_zero {Ω : Set (Rn n)} (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected Ω) {f : Rn n → ℝ}
    (hW : GMTFoundations.HasWeakGradient Ω f (fun _ => (0 : Rn n))) :
    ∃ c : ℝ, ∀ᵐ x ∂(volume.restrict Ω), f x = c := by
  rcases Ω.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · exact ⟨0, by simp⟩
  obtain ⟨R₀, hR₀, c, hc⟩ := exists_ae_eq_const_ball_of_hasWeakGrad_zero hΩ hW hx₀
  -- `S`: points near which `f = c` a.e.; `T`: points near which `f` is a.e. another constant.
  set S : Set (Rn n) := {x | ∃ R > 0, ∀ᵐ y ∂(volume.restrict (ball x R)), f y = c} with hS_def
  set T : Set (Rn n) :=
    {x | ∃ R > 0, ∃ c' ≠ c, ∀ᵐ y ∂(volume.restrict (ball x R)), f y = c'} with hT_def
  have hS : IsOpen S := by
    refine Metric.isOpen_iff.2 fun x ⟨R, hR, h⟩ => ⟨R, hR, fun z hz => ?_⟩
    exact exists_ae_restrict_ball_of_mem_ball h hz
  have hT : IsOpen T := by
    refine Metric.isOpen_iff.2 fun x ⟨R, hR, c', hc', h⟩ => ⟨R, hR, fun z hz => ?_⟩
    obtain ⟨R', hR', h'⟩ := exists_ae_restrict_ball_of_mem_ball h hz
    exact ⟨R', hR', c', hc', h'⟩
  have hcover : ∀ x ∈ Ω, x ∈ S ∨ x ∈ T := by
    intro x hx
    obtain ⟨R, hR, c', h⟩ := exists_ae_eq_const_ball_of_hasWeakGrad_zero hΩ hW hx
    by_cases hc' : c' = c
    · exact Or.inl ⟨R, hR, hc' ▸ h⟩
    · exact Or.inr ⟨R, hR, c', hc', h⟩
  have hdisj : ∀ x, x ∈ S → x ∈ T → False := by
    rintro x ⟨R, hR, h⟩ ⟨R', hR', c', hc', h'⟩
    have hm : volume.restrict (ball x (min R R')) ≠ 0 := by
      rw [Ne, Measure.restrict_eq_zero]
      exact (measure_ball_pos volume x (lt_min hR hR')).ne'
    have : (ae (volume.restrict (ball x (min R R')))).NeBot := ae_neBot.2 hm
    obtain ⟨y, hy, hy'⟩ :=
      ((ae_restrict_of_ae_restrict_of_subset (ball_subset_ball (min_le_left _ _)) h).and
        (ae_restrict_of_ae_restrict_of_subset (ball_subset_ball (min_le_right _ _)) h')).exists
    exact hc' (hy'.symm.trans hy)
  have hΩS : ∀ x ∈ Ω, x ∈ S := by
    intro x hx
    rcases hcover x hx with h | h
    · exact h
    · obtain ⟨y, -, hyS, hyT⟩ :=
        hΩc S T hS hT (fun z hz => hcover z hz) ⟨x₀, hx₀, R₀, hR₀, hc⟩ ⟨x, hx, h⟩
      exact (hdisj y hyS hyT).elim
  refine ⟨c, ?_⟩
  rw [ae_restrict_iff' hΩ.measurableSet, ae_iff]
  refine measure_null_of_locally_null _ fun x hx => ?_
  have hxΩ : x ∈ Ω := by
    by_contra hn
    exact hx fun h => absurd h hn
  obtain ⟨R, hR, h⟩ := hΩS x hxΩ
  refine ⟨{x | ¬(x ∈ Ω → f x = c)} ∩ ball x R,
    inter_mem_nhdsWithin _ (ball_mem_nhds x hR), ?_⟩
  rw [ae_restrict_iff' measurableSet_ball, ae_iff] at h
  refine measure_mono_null (fun y hy => ?_) h
  intro hyb
  exact hy.1 fun _ => hyb hy.2

end InnerVariational
