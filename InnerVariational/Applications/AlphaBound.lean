/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Applications.FreeBoundaryLimit
public import InnerVariational.Singular.Density
public import InnerVariational.Singular.HeightLimit
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
import InnerVariational.Singular.FlatPoint
import InnerVariational.Blowup.Profile
import InnerVariational.Frequency.Concrete
import InnerVariational.Registry.FreeBoundary
import InnerVariational.Monotonicity.HighestDensity
public import InnerVariational.Defs.HighestDensity
import InnerVariational.Kernel.Rescale
public import InnerVariational.Defs.VariationalSolution
public import InnerVariational.Defs.Solutions
import InnerVariational.Kernel.IBP
import InnerVariational.Basic.Polar

/-!
# The bound `α(n) √(H_x(u; 0+)) ≤ 1` for limits of classical solutions

The last paragraph of the proof of Theorem 9.3 of Kriventsov–Weiss (full reference below). Let `u_k`
be classical solutions on `B_1`, `C`-Lipschitz on `B_1`, with `u_k → v` locally uniformly on `B_1`
and `(v, χ_{v>0})` a variational solution. Then `α(n) √(H_x(v; 0+)) ≤ 1` for `ℋ^{n-1}`-a.e.
`x ∈ Σ^H(v)` (`Applications.hausdorffN_sigmaH_not_alpha_le_one`).

## Proof

1. *Rescaling* (`IsClassicalSolution.comp_affine`). Classical solutions are invariant under
   `u ↦ u(a + ρ ·)/ρ`. So the Alt–Caffarelli gradient bound (Proposition 9.1,
   `Registry.classical_lipschitz_bound`, stated on `B_1` with `u(0) = 0`) applies on every ball
   `B_ρ(x_k) ⊆ B_1` centred at a free boundary point `x_k` of `u_k`
   (`lipschitzOnWith_ball_of_mem_frontier`).
2. *Lipschitz bound for the limit* (`exists_lipschitzOnWith_limit`). If `x ∈ ∂{v > 0}`, then
   `x = lim x_k` with `x_k ∈ ∂{u_k > 0}` (first half of the Hausdorff convergence,
   `eventually_exists_frontier_near`), and step 1 on `B_ρ(x_k)` gives: for each `s ∈ (0, 1)`, `v`
   is `(1 + ω(s))`-Lipschitz on a ball around `x`.
3. *The profile* (`mul_sqrt_le_of_tendsto_gradient`). At a point of Lemma 8.5 (1)
   (`Singular.renormalized_tendsto_alpha_ae`), `∇v ≈ √(H_x(v; r)) α(n) ∇|(y−x)·ν|` in
   `L²(B_r(x))` relative to `r^n H_x(v; r)`. Since `|∇|(y−x)·ν|| = 1` a.e. and `|∇v| ≤ L` near `x`,
   `|B_1| (√(H_x(v; r)) α(n) − L)₊² ≤ H_x(v; r) · o(1)`, so `α(n) √(H_x(v; 0+)) ≤ L`.
   The paper instead bounds `limsup_r ‖u(x + r ·)/r‖_{C^{0,1}(B̄_1)}` by `1`; with the full
   `C^{0,1}` norm that bound fails already for `|y_n|`, so the Lipschitz seminorm is meant. Here
   the gradient part of Lemma 8.5 (1) is used instead, on the ball `B_r(x)` only.
4. Let `s → 0+`: `ω(s) → 0`.

## References

* D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
  DOI 10.1002/cpa.22226; arXiv:2306.10131. Result numbers refer to arXiv v2.
-/

open MeasureTheory Metric Set Filter Topology Laplacian InnerProductSpace
open scoped NNReal ENNReal RealInnerProductSpace ContDiff

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

/-! ### Harmonic functions under `u ↦ u(a + ρ ·)/ρ` -/

/-- `Δ(u(a + ρ ·)/ρ)(y) = ρ Δu(a + ρ y)`. -/
theorem laplacian_comp_affine (u : Rn n → ℝ) (a : Rn n) {ρ : ℝ} (hρ : ρ ≠ 0) (y : Rn n) :
    Δ (fun z => u (a + ρ • z) / ρ) y = ρ * Δ u (a + ρ • y) := by
  set L := Kernel.simLinear ρ hρ (LinearIsometryEquiv.refl ℝ (Rn n)) with hLdef
  have hφ : (fun z => u (a + ρ • z) / ρ) = ρ⁻¹ • ((fun w => u (a + w)) ∘ L) := by
    ext z
    simp [L, div_eq_inv_mul]
  have hD : fderiv ℝ (fun z => u (a + ρ • z) / ρ) = fun z => fderiv ℝ u (a + L z) := by
    funext z
    rw [hφ, fderiv_const_smul_field, Pi.smul_apply, L.comp_right_fderiv, fderiv_comp_add_left]
    ext v
    simp [L, inv_mul_cancel_left₀ hρ]
  have hD2 : fderiv ℝ (fderiv ℝ (fun z => u (a + ρ • z) / ρ)) y =
      (fderiv ℝ (fderiv ℝ u) (a + L y)).comp (L : Rn n →L[ℝ] Rn n) := by
    rw [hD, show (fun z => fderiv ℝ u (a + L z)) = (fun w => fderiv ℝ u (a + w)) ∘ L from rfl,
      L.comp_right_fderiv, fderiv_comp_add_left]
  rw [Kernel.laplacian_apply_eq_sum, Kernel.laplacian_apply_eq_sum, hD2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [L]

/-- If `u` is harmonic at `a + ρ y`, then `u(a + ρ ·)/ρ` is harmonic at `y`. -/
theorem harmonicAt_comp_affine {u : Rn n → ℝ} {a y : Rn n} {ρ : ℝ} (hρ : ρ ≠ 0)
    (h : HarmonicAt u (a + ρ • y)) : HarmonicAt (fun z => u (a + ρ • z) / ρ) y := by
  have hAd : ContDiff ℝ 2 fun z : Rn n => a + ρ • z := contDiff_const.add (contDiff_id.const_smul ρ)
  refine ⟨(h.1.comp y hAd.contDiffAt).div_const ρ, ?_⟩
  filter_upwards [(hAd.continuous.tendsto y).eventually h.2] with z hz
  rw [laplacian_comp_affine u a hρ z]
  simp only [Pi.zero_apply] at hz ⊢
  rw [hz, mul_zero]

theorem dist_affine (a : Rn n) {ρ : ℝ} (hρ : 0 < ρ) (b c : Rn n) :
    dist (a + ρ • b) (a + ρ • c) = ρ * dist b c := by
  rw [dist_eq_norm, dist_eq_norm, add_sub_add_left_eq_sub, ← smul_sub, norm_smul,
    Real.norm_of_nonneg hρ.le]

/-! ### Classical solutions under restriction and rescaling -/

namespace IsClassicalSolution

variable {Ω : Set (Rn n)} {u : Rn n → ℝ}

/-- Restriction of a classical solution to an open subset. -/
theorem mono (h : IsClassicalSolution Ω u) {V : Set (Rn n)} (hV : IsOpen V) (hVΩ : V ⊆ Ω) :
    IsClassicalSolution V u where
  isOpen := hV
  lipschitzOnWith := let ⟨L, hL⟩ := h.lipschitzOnWith; ⟨L, hL.mono hVΩ⟩
  nonneg x hx := h.nonneg x (hVΩ hx)
  harmonicAt x hx := h.harmonicAt x (hVΩ hx)
  free_boundary x hx := h.free_boundary x ⟨hVΩ hx.1, hx.2⟩

/-- **Rescaling.** If `u` is a classical solution on `Ω`, then `u(a + ρ ·)/ρ` is a classical
solution on `{y : a + ρ y ∈ Ω}`, for `ρ > 0`. -/
theorem comp_affine (h : IsClassicalSolution Ω u) (a : Rn n) {ρ : ℝ} (hρ : 0 < ρ) :
    IsClassicalSolution ((fun y => a + ρ • y) ⁻¹' Ω) (fun y => u (a + ρ • y) / ρ) := by
  have hAc : Continuous fun y : Rn n => a + ρ • y := by fun_prop
  set Ah : Rn n ≃ₜ Rn n := (Homeomorph.smulOfNeZero ρ hρ.ne').trans (Homeomorph.addLeft a)
    with hAhdef
  have hpos : {y | 0 < u (a + ρ • y) / ρ} = (fun y => a + ρ • y) ⁻¹' {z | 0 < u z} := by
    ext y
    simp only [mem_ofPred_eq, mem_preimage, div_pos_iff_of_pos_right hρ]
  have hfr : frontier {y | 0 < u (a + ρ • y) / ρ} =
      (fun y => a + ρ • y) ⁻¹' frontier {z | 0 < u z} := by
    rw [hpos]
    exact (Ah.preimage_frontier _).symm
  refine
    { isOpen := h.isOpen.preimage hAc
      lipschitzOnWith := ?_
      nonneg := fun y hy => div_nonneg (h.nonneg _ hy) hρ.le
      harmonicAt := fun y hy hpy =>
        harmonicAt_comp_affine hρ.ne' (h.harmonicAt _ hy ((div_pos_iff_of_pos_right hρ).1 hpy))
      free_boundary := ?_ }
  · obtain ⟨L, hL⟩ := h.lipschitzOnWith
    refine ⟨L, LipschitzOnWith.of_dist_le_mul fun b hb c hc => ?_⟩
    have := hL.dist_le_mul _ hb _ hc
    rw [dist_affine a hρ] at this
    rw [Real.dist_eq, ← sub_div, abs_div, abs_of_pos hρ, div_le_iff₀ hρ, ← Real.dist_eq]
    linarith
  · rintro y ⟨hy, hyfr⟩
    rw [hfr] at hyfr
    obtain ⟨r, hr, F, hF, hFne, hFeq, hFn⟩ := h.free_boundary (a + ρ • y) ⟨hy, hyfr⟩
    have hgF : gradient (fun z => F (a + ρ • z) / ρ) y = gradient F (a + ρ • y) := by
      exact Kernel.gradient_comp_similarity F a hρ (LinearIsometryEquiv.refl ℝ (Rn n)) y
    have hball : ∀ z, z ∈ ball y (r / ρ) ↔ a + ρ • z ∈ ball (a + ρ • y) r := fun z => by
      rw [mem_ball, mem_ball, dist_affine a hρ, lt_div_iff₀ hρ, mul_comm]
    refine ⟨r / ρ, div_pos hr hρ, fun z => F (a + ρ • z) / ρ,
      (hF.comp (contDiff_const.add (contDiff_id.const_smul ρ))).div_const ρ,
      by rwa [hgF], ?_, ?_⟩
    · ext z
      have hz := Set.ext_iff.1 hFeq (a + ρ • z)
      simp only [mem_inter_iff, mem_ofPred_eq] at hz ⊢
      rw [hfr, mem_preimage, hball z, div_eq_zero_iff, or_iff_left hρ.ne']
      exact hz
    · intro s hs hev
      rw [hgF] at hev ⊢
      set N := (s * ‖gradient F (a + ρ • y)‖⁻¹) • gradient F (a + ρ • y) with hNdef
      have hvec : ∀ t : ℝ, a + ρ • (y + t • N) = a + ρ • y + (ρ * t) • N := fun t => by
        rw [smul_add, smul_smul, add_assoc]
      have hmul : ∀ c : ℝ, 0 < c → Tendsto (fun t : ℝ => c * t) (𝓝[>] 0) (𝓝[>] 0) :=
        fun c hc => tendsto_nhdsWithin_iff.2
          ⟨((continuous_const.mul continuous_id).tendsto' 0 0 (mul_zero c)).mono_left
            nhdsWithin_le_nhds, eventually_nhdsWithin_of_forall fun t ht => mul_pos hc ht⟩
      have hev' : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < u (a + ρ • y + t • N) := by
        filter_upwards [(hmul ρ⁻¹ (inv_pos.2 hρ)).eventually hev] with t ht
        rw [hvec, mul_inv_cancel_left₀ hρ.ne', div_pos_iff_of_pos_right hρ] at ht
        exact ht
      refine ((hFn s hs hev').comp (hmul ρ hρ)).congr fun t => ?_
      simp only [Function.comp_apply]
      rw [hvec, div_sub_div_same, div_div]

end IsClassicalSolution

namespace Applications

variable {u : ℕ → Rn n → ℝ} {C : ℝ≥0} {v : Rn n → ℝ}

/-- **The Alt–Caffarelli gradient bound on a small ball.** Let `ω` satisfy the conclusion of
Proposition 9.1 for Lipschitz constant `C` (`Registry.classical_lipschitz_bound C`). If `u` is a
classical solution on `B_1`, `C`-Lipschitz on `B_1`, `u(x₀) = 0` and `B_ρ(x₀) ⊆ B_1`, then `u` is
`(1 + ω(s))`-Lipschitz on `B_{ρ s}(x₀)` for `s ∈ (0, 1)`. -/
theorem lipschitzOnWith_ball_of_mem_frontier {w : ℝ → ℝ}
    (hw : ∀ u : Rn n → ℝ, IsClassicalSolution (ball 0 1) u → LipschitzOnWith C u (ball 0 1) →
      u 0 = 0 → ∀ r ∈ Ioo (0 : ℝ) 1, LipschitzOnWith (1 + w r).toNNReal u (ball 0 r))
    {f : Rn n → ℝ} (hf : IsClassicalSolution (ball 0 1) f) (hlip : LipschitzOnWith C f (ball 0 1))
    {x₀ : Rn n} {ρ : ℝ} (hρ : 0 < ρ) (hball : ball x₀ ρ ⊆ ball 0 1) (hx₀ : f x₀ = 0) {s : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) : LipschitzOnWith (1 + w s).toNNReal f (ball x₀ (ρ * s)) := by
  have hmem : ∀ y : Rn n, ∀ t : ℝ, y ∈ ball (0 : Rn n) t → x₀ + ρ • y ∈ ball x₀ (ρ * t) :=
    fun y t hy => by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hρ.le]
      rw [mem_ball_zero_iff] at hy
      exact mul_lt_mul_of_pos_left hy hρ
  have hmem1 : ∀ y : Rn n, y ∈ ball (0 : Rn n) 1 → x₀ + ρ • y ∈ ball (0 : Rn n) 1 :=
    fun y hy => hball (by have := hmem y 1 hy; rwa [mul_one] at this)
  have hdist : ∀ b c : Rn n, dist (f (x₀ + ρ • b)) (f (x₀ + ρ • c)) =
      ρ * dist (f (x₀ + ρ • b) / ρ) (f (x₀ + ρ • c) / ρ) := fun b c => by
    rw [Real.dist_eq, Real.dist_eq, ← sub_div, abs_div, abs_of_pos hρ,
      mul_div_cancel₀ _ hρ.ne']
  have hg : IsClassicalSolution (ball 0 1) (fun y => f (x₀ + ρ • y) / ρ) :=
    (hf.comp_affine x₀ hρ).mono isOpen_ball hmem1
  have hgL : LipschitzOnWith C (fun y => f (x₀ + ρ • y) / ρ) (ball 0 1) := by
    refine LipschitzOnWith.of_dist_le_mul fun b hb c hc => ?_
    have h1 := hlip.dist_le_mul _ (hmem1 b hb) _ (hmem1 c hc)
    rw [hdist, dist_affine _ hρ] at h1
    have h2 : dist (f (x₀ + ρ • b) / ρ) (f (x₀ + ρ • c) / ρ) ≤ C * dist b c := by
      by_contra hcon
      push Not at hcon
      nlinarith
    exact h2
  have hg0 : (fun y => f (x₀ + ρ • y) / ρ) 0 = 0 := by simp [hx₀]
  have hK := hw _ hg hgL hg0 s hs
  refine LipschitzOnWith.of_dist_le_mul fun z₁ hz₁ z₂ hz₂ => ?_
  have hinv : ∀ z : Rn n, x₀ + ρ • (ρ⁻¹ • (z - x₀)) = z := fun z => by
    rw [smul_smul, mul_inv_cancel₀ hρ.ne', one_smul, add_sub_cancel]
  have hB : ∀ z ∈ ball x₀ (ρ * s), ρ⁻¹ • (z - x₀) ∈ ball (0 : Rn n) s := fun z hz => by
    rw [mem_ball, ← mul_lt_mul_iff_right₀ hρ, ← dist_affine x₀ hρ, hinv]
    simpa using hz
  have h1 := hK.dist_le_mul _ (hB z₁ hz₁) _ (hB z₂ hz₂)
  have h2 := hdist (ρ⁻¹ • (z₁ - x₀)) (ρ⁻¹ • (z₂ - x₀))
  have h3 := dist_affine x₀ hρ (ρ⁻¹ • (z₁ - x₀)) (ρ⁻¹ • (z₂ - x₀))
  rw [hinv, hinv] at h1 h2 h3
  rw [h2, h3]
  calc ρ * dist (f z₁ / ρ) (f z₂ / ρ)
      ≤ ρ * (((1 + w s).toNNReal : ℝ) * dist (ρ⁻¹ • (z₁ - x₀)) (ρ⁻¹ • (z₂ - x₀))) :=
        mul_le_mul_of_nonneg_left h1 hρ.le
    _ = _ := by ring

/-- **Lipschitz bound for the limit near a free boundary point** (proof of Theorem 9.3). If
`x ∈ B_1 ∩ ∂{v > 0}` and `ω` is as in Proposition 9.1, then for every `s ∈ (0, 1)` the limit `v` is
`(1 + ω(s))`-Lipschitz on a ball around `x`. -/
theorem exists_lipschitzOnWith_limit [NeZero n]
    (hu : ∀ k, IsClassicalSolution (ball 0 1) (u k))
    (hlip : ∀ k, LipschitzOnWith C (u k) (ball 0 1))
    (hconv : TendstoLocallyUniformlyOn u v atTop (ball 0 1)) {w : ℝ → ℝ}
    (hw : ∀ u : Rn n → ℝ, IsClassicalSolution (ball 0 1) u → LipschitzOnWith C u (ball 0 1) →
      u 0 = 0 → ∀ r ∈ Ioo (0 : ℝ) 1, LipschitzOnWith (1 + w r).toNNReal u (ball 0 r))
    {x : Rn n} (hx : x ∈ ball (0 : Rn n) 1) (hxfr : x ∈ frontier {y | 0 < v y}) {s : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) :
    ∃ δ > 0, LipschitzOnWith (1 + w s).toNNReal v (ball x δ) := by
  have hx1 : ‖x‖ < 1 := mem_ball_zero_iff.1 hx
  set ρ := (1 - ‖x‖) / 2 with hρdef
  have hρ : 0 < ρ := by rw [hρdef]; linarith
  have h2ρ : ball x (2 * ρ) ⊆ ball 0 1 := fun z hz => by
    rw [mem_ball_zero_iff]
    rw [mem_ball, dist_eq_norm] at hz
    have := norm_le_norm_add_norm_sub' z x
    rw [hρdef] at hz
    linarith
  have hρs : 0 < ρ * s / 2 := by have := hs.1; positivity
  have hρs' : ρ * s / 2 < ρ := by nlinarith [hs.2]
  refine ⟨ρ * s / 2, hρs, ?_⟩
  have hsub : ball x (ρ * s / 2) ⊆ ball 0 1 :=
    (ball_subset_ball (by linarith)).trans h2ρ
  have hev : ∀ᶠ k in atTop, LipschitzOnWith (1 + w s).toNNReal (u k) (ball x (ρ * s / 2)) := by
    filter_upwards [eventually_exists_frontier_near hu hconv isCompact_singleton
      (singleton_subset_iff.2 hx) hρs] with k hk
    obtain ⟨y, ⟨hyB, hyfr⟩, hxy⟩ := hk x ⟨rfl, hxfr⟩
    have hyball : ball y ρ ⊆ ball 0 1 := fun z hz => h2ρ (by
      rw [mem_ball] at hz ⊢
      have := dist_triangle z y x
      rw [dist_comm y x] at this
      linarith)
    have hL := lipschitzOnWith_ball_of_mem_frontier hw (hu k) (hlip k) hρ hyball
      ((hu k).eq_zero_of_mem_frontier hyB hyfr) hs
    refine hL.mono fun z hz => ?_
    rw [mem_ball] at hz ⊢
    have := dist_triangle z x y
    linarith
  refine LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_
  exact le_of_tendsto ((hconv.tendsto_at (hsub ha)).dist (hconv.tendsto_at (hsub hb)))
    (hev.mono fun k hk => hk.dist_le_mul a ha b hb)

/-! ### The profile bound -/

/-- `|∇|(y − x)·ν|| = 1` off the hyperplane `(y − x)·ν = 0`, for a unit vector `ν`. -/
theorem norm_gradient_absProfile_of_ne {ν x y : Rn n} (hν : ‖ν‖ = 1) (hy : ⟪y - x, ν⟫ ≠ 0) :
    ‖gradient (absProfile ν x) y‖ = 1 := by
  have he : absProfile ν x = fun z => absProfile ν 0 (z + -x) := by
    funext z
    simp [absProfile, sub_eq_add_neg]
  have hg : gradient (absProfile ν x) y = gradient (absProfile ν 0) (y + -x) := by
    rw [he, gradient, fderiv_comp_add_right, ← gradient]
  rw [hg, ← sub_eq_add_neg]
  rcases hy.lt_or_gt with hneg | hpos
  · rw [gradient_absProfile_of_neg hneg, norm_neg, hν]
  · rw [gradient_absProfile_of_pos hpos, hν]

/-- The hyperplane `{y : (y − x)·ν = 0}` is Lebesgue-null for `ν ≠ 0`. -/
theorem ae_inner_sub_ne_zero {ν : Rn n} (hν : ν ≠ 0) (x : Rn n) :
    ∀ᵐ y ∂(volume : Measure (Rn n)), ⟪y - x, ν⟫ ≠ 0 := by
  have hne : (ℝ ∙ ν)ᗮ ≠ ⊤ := by
    intro htop
    have hmem : ν ∈ (ℝ ∙ ν)ᗮ := htop ▸ Submodule.mem_top
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_self_eq_norm_sq] at hmem
    exact hν (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hmem))
  have h1 : {y : Rn n | ⟪y - x, ν⟫ = 0} =
      (fun y => y + -x) ⁻¹' (((ℝ ∙ ν)ᗮ : Submodule ℝ (Rn n)) : Set (Rn n)) := by
    ext y
    rw [mem_ofPred_eq, mem_preimage, SetLike.mem_coe,
      Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_comm, sub_eq_add_neg]
  have h0 : volume {y : Rn n | ⟪y - x, ν⟫ = 0} = 0 := by
    rw [h1, measure_preimage_add_right]
    exact Measure.addHaar_submodule volume _ hne
  exact measure_eq_zero_iff_ae_notMem.1 h0

/-- **The profile bound** (proof of Theorem 9.3, in gradient form). Let `|∇v| ≤ L` on `B_δ(x)`,
`H(r) → H₀` as `r → 0+` with `H ≥ 0`, and
`(r^n H(r))⁻¹ ∫_{B_r(x)} |∇v − √(H(r)) α ∇|(y−x)·ν||² → 0` for a unit vector `ν` and `α ≥ 0`.
Then `α √H₀ ≤ L`. -/
theorem mul_sqrt_le_of_tendsto_gradient {x ν : Rn n} (hν : ‖ν‖ = 1) {L δ α H₀ : ℝ}
    (hδ : 0 < δ) (hgrad : ∀ y ∈ ball x δ, ‖gradient v y‖ ≤ L) {H : ℝ → ℝ}
    (hH : Tendsto H (𝓝[>] 0) (𝓝 H₀)) (hH0 : ∀ r, 0 < r → 0 ≤ H r) (hα : 0 ≤ α)
    (hlim : Tendsto (fun r => (∫ y in ball x r,
        ‖gradient v y - (√(H r) * α) • gradient (absProfile ν x) y‖ ^ 2) / (r ^ n * H r))
        (𝓝[>] 0) (𝓝 0)) :
    α * √H₀ ≤ L := by
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hgrad x (mem_ball_self hδ))
  have hν0 : ν ≠ 0 := fun h0 => by rw [h0, norm_zero] at hν; exact zero_ne_one hν
  have hnull := ae_inner_sub_ne_zero hν0 x
  have hB := unitBallVolume_pos n
  set e : ℝ → Rn n → Rn n := fun r y =>
    gradient v y - (√(H r) * α) • gradient (absProfile ν x) y with hedef
  -- the key estimate on `B_r(x)`, `r < δ`
  have hkey : ∀ r ∈ Ioo 0 δ, max (√(H r) * α - L) 0 ^ 2 * (r ^ n * unitBallVolume n) ≤
      ∫ y in ball x r, ‖e r y‖ ^ 2 := by
    rintro r ⟨hr, hrδ⟩
    set c := √(H r) * α with hcdef
    have hc : 0 ≤ c := mul_nonneg (Real.sqrt_nonneg _) hα
    have hint : IntegrableOn (fun y => ‖e r y‖ ^ 2) (ball x r) := by
      refine IntegrableOn.of_bound measure_ball_lt_top
        (((measurable_gradient v).sub ((measurable_gradient _).const_smul c)).norm.pow_const
          2).aestronglyMeasurable ((L + c) ^ 2)
        ((ae_restrict_iff' measurableSet_ball).2 (.of_forall fun y hy => ?_))
      have hy' : y ∈ ball x δ := ball_subset_ball hrδ.le hy
      have h1 : ‖e r y‖ ≤ L + c := by
        refine (norm_sub_le _ _).trans (add_le_add (hgrad y hy') ?_)
        rw [norm_smul, Real.norm_of_nonneg hc]
        exact mul_le_of_le_one_right hc (Singular.norm_gradient_absProfile_le hν x y)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    have hle : ∀ᵐ y ∂(volume.restrict (ball x r)), max (c - L) 0 ^ 2 ≤ ‖e r y‖ ^ 2 := by
      filter_upwards [ae_restrict_of_ae hnull, ae_restrict_mem measurableSet_ball] with y hy hyB
      have hy' : y ∈ ball x δ := ball_subset_ball hrδ.le hyB
      have h1 : c ≤ ‖gradient v y‖ + ‖e r y‖ := by
        have := norm_sub_le (gradient v y) (e r y)
        rw [hedef, sub_sub_cancel, norm_smul, norm_gradient_absProfile_of_ne hν hy,
          Real.norm_of_nonneg hc, mul_one] at this
        exact this
      have h2 : max (c - L) 0 ≤ ‖e r y‖ :=
        max_le (by linarith [hgrad y hy']) (norm_nonneg _)
      exact pow_le_pow_left₀ (le_max_right _ _) h2 2
    have := setIntegral_mono_ae_restrict (integrableOn_const measure_ball_lt_top.ne) hint hle
    rwa [setIntegral_const, smul_eq_mul, measureReal_def, volume_ball_toReal x hr,
      mul_comm] at this
  -- divide by `r^n H(r)`
  have hbound : ∀ r ∈ Ioo 0 δ, max (√(H r) * α - L) 0 ^ 2 ≤
      (∫ y in ball x r, ‖e r y‖ ^ 2) / (r ^ n * H r) * H r / unitBallVolume n := by
    intro r hr
    have hk := hkey r hr
    rcases (hH0 r hr.1).eq_or_lt with h0 | hpos
    · rw [← h0, Real.sqrt_zero, zero_mul, zero_sub, max_eq_right (by linarith), mul_zero,
        zero_div]
      norm_num
    · have hrn : 0 < r ^ n := pow_pos hr.1 n
      have heq : (∫ y in ball x r, ‖e r y‖ ^ 2) / (r ^ n * H r) * H r / unitBallVolume n =
          (∫ y in ball x r, ‖e r y‖ ^ 2) / (r ^ n * unitBallVolume n) := by
        field_simp
      rw [heq, le_div_iff₀ (by positivity)]
      linarith
  have hlimL : Tendsto (fun r => max (√(H r) * α - L) 0 ^ 2) (𝓝[>] 0)
      (𝓝 (max (√H₀ * α - L) 0 ^ 2)) :=
    ((((hH.sqrt).mul_const α).sub_const L).max tendsto_const_nhds).pow 2
  have hlimR : Tendsto (fun r => (∫ y in ball x r, ‖e r y‖ ^ 2) / (r ^ n * H r) * H r /
      unitBallVolume n) (𝓝[>] 0) (𝓝 (0 * H₀ / unitBallVolume n)) :=
    (hlim.mul hH).div_const _
  have hfin := le_of_tendsto_of_tendsto hlimL hlimR
    (Filter.mem_of_superset (Ioo_mem_nhdsGT hδ) fun r hr => hbound r hr)
  rw [zero_mul, zero_div] at hfin
  have hm0 := le_max_right (√H₀ * α - L) 0
  have hm1 := le_max_left (√H₀ * α - L) 0
  nlinarith

/-- **`α(n) √(H_x(v; 0+)) ≤ 1` a.e. on `Σ^H`** (proof of Theorem 9.3), via Proposition 9.1 and
Lemma 8.5 (1). -/
theorem hausdorffN_sigmaH_not_alpha_le_one [NeZero n] (hn : 2 ≤ n)
    (hu : ∀ k, IsClassicalSolution (ball 0 1) (u k))
    (hlip : ∀ k, LipschitzOnWith C (u k) (ball 0 1))
    (hconv : TendstoLocallyUniformlyOn u v atTop (ball 0 1))
    (hv : IsVariationalSolution (ball 0 1) C v (posIndicator v)) :
    hausdorffN n (n - 1) {x | x ∈ sigmaH (ball 0 1) v (posIndicator v) ∧
      ¬ alphaN n * √(heightHZero v x) ≤ 1} = 0 := by
  obtain ⟨w, -, -, hw0, hw⟩ := Registry.classical_lipschitz_bound (n := n) C
  refine measure_mono_null ?_ (Singular.renormalized_tendsto_alpha_ae hn hv)
  rintro x ⟨hxS, hxα⟩
  refine ⟨hxS, fun ⟨ν, hν, hconvν⟩ => hxα ?_⟩
  have hx0 : v x = 0 := hv.eq_zero_of_mem_sigmaH hxS
  have hxfr : x ∈ frontier {y | 0 < v y} := ⟨hxS.2.1, fun hint => by
    have : (0 : ℝ) < v x := interior_subset (s := {y | 0 < v y}) hint
    rw [hx0] at this
    exact lt_irrefl _ this⟩
  have hH := Singular.tendsto_heightH_zero hv hxS
  have hα : 0 ≤ alphaN n := by unfold alphaN; positivity
  have hgradlim := (hconvν 1 one_pos).2
  simp only [one_mul] at hgradlim
  have hbound : ∀ s ∈ Ioo (0 : ℝ) 1, alphaN n * √(heightHZero v x) ≤ max (1 + w s) 0 := by
    intro s hs
    obtain ⟨δ, hδ, hL⟩ := exists_lipschitzOnWith_limit hu hlip hconv hw hxS.1 hxfr hs
    have hgrad : ∀ y ∈ ball x δ, ‖gradient v y‖ ≤ max (1 + w s) 0 := fun y hy => by
      rw [gradient, LinearIsometryEquiv.norm_map, ← Real.coe_toNNReal']
      exact norm_fderiv_le_of_lipschitzOn ℝ (isOpen_ball.mem_nhds hy) hL
    exact mul_sqrt_le_of_tendsto_gradient hν hδ hgrad hH (fun r hr => heightH_nonneg v x hr.le)
      hα hgradlim
  have hlim : Tendsto (fun s => max (1 + w s) 0) (𝓝[>] 0) (𝓝 1) := by
    have := ((hw0.const_add 1).max tendsto_const_nhds : Tendsto (fun s => max (1 + w s) 0)
      (𝓝[>] 0) (𝓝 (max (1 + 0) 0)))
    simpa using this
  exact ge_of_tendsto hlim (Filter.mem_of_superset (Ioo_mem_nhdsGT one_pos) hbound)

end Applications

end InnerVariational
