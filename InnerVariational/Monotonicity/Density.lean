/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Monotonicity.Homogeneity
import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Real.StarOrdered
public import InnerVariational.Monotonicity.Limits
import InnerVariational.Kernel.Rescale
import InnerVariational.Monotonicity.Blowup
import InnerVariational.Monotonicity.Radial
import InnerVariational.Kernel.BV
import InnerVariational.Kernel.RellichPohozaev
import InnerVariational.Kernel.Subharmonic
public import InnerVariational.Kernel.Harmonic
import InnerVariational.Basic.Polar

/-!
# Blow-ups and the density formula (3.10)

The last claim of Proposition 3.4 of Kriventsov–Weiss (see the references), and
Proposition 3.5, including the density formula (3.10). Let `(u, χ)` be a variational solution on
`Ω` and `x ∈ Ω`.

## Blow-ups (Proposition 3.4)

Let `r_k → 0+` and `u_{x, r_k} → u₀` locally uniformly on `ℝⁿ`. Then `u(x) = 0`
(`IsVariationalSolution.eq_zero_of_tendstoLocallyUniformly_rescale`), `u₀` is `C_V`-Lipschitz and
harmonic on `{u₀ > 0}` (`blowup_lipschitzWith`, `blowup_isLipHarmonicPos`), it satisfies Euler's
identity `∇u₀(y)·y = u₀(y)` (`blowup_inner_gradient_eq`), and it is homogeneous of degree one
(`blowup_homogeneous`). Such limits exist along a subsequence of any `r_k → 0+`
(`exists_blowup_subseq`, `Blowup.lean`). The paper's `W^{1,2}` bound is immediate from the
Lipschitz bound.

Proposition 3.4 states, for every `x`, that the rescalings `u_{x,r}` are bounded in `W^{1,2}(D)`
and that their subsequential limits are homogeneous of degree one. This holds only when
`u(x) = 0`: if `u(x) > 0`, then `u_{x,r}(0) = u(x)/r → ∞`. Here the hypothesis is the existence
of a locally uniform limit, which forces `u(x) = 0`.

## Proposition 3.5

* `tendsto_monotonicityM_zero_of_pos`: if `u(x) > 0`, then `M_x(r) → −∞`.
* `tendsto_monotonicityM_zero`, formula (3.10): if `u(x) = 0`, then `M_x(0+)` is a real number
  `m`, `M_x(r) → m`, and `r^{-n} ∫_{B_r(x)} χ → m`. The existence of the second limit is part of
  the statement, as in the paper.
* `Mzero_le_unitBallVolume`: `M_x(0+) ≤ |B_1|`, and `0 ≤ M_x(0+)` when `u(x) = 0`.
* `upperSemicontinuousOn_Mzero` (`Limits.lean`): `x ↦ M_x(0+)` is upper semicontinuous on `Ω`.

`χ` takes values in `{0, 1}` on `Ω`, so `∫_{B_r(x)} χ = |{χ = 1} ∩ B_r(x)|`
(`setIntegral_chi_eq_measureReal`); (3.10) is stated with `∫ χ`.

## Proof of (3.10)

We follow the proof of Proposition 3.5. By the subsequence principle it suffices to show that
each `r_k → 0+` has a subsequence along which `r_k^{-n} ∫_{B_{r_k}(x)} χ → m`. Extract a blow-up
`u₀`. On `B_2`, the rescalings are variational solutions for large `k`, so `∇u_{x,r_k} → ∇u₀` in
`L²(B_1)` (`Blowup.lean`) and `u_{x,r_k} → u₀` uniformly on `∂B_1`. Euler's identity gives
`∫_{B_1} |∇u₀|² = ∫_{∂B_1} u₀²` (`integral_norm_gradient_sq_eq_of_inner_gradient_eq`). Hence
`∫_{B_1} χ_{x,r_k} = M_0(u_{x,r_k}; 1) − ∫_{B_1} |∇u_{x,r_k}|² + ∫_{∂B_1} u_{x,r_k}²
→ m − ∫_{B_1} |∇u₀|² + ∫_{∂B_1} u₀² = m`.

## References

* D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
  DOI 10.1002/cpa.22226; arXiv:2306.10131. Unqualified result and equation numbers in this file
  refer to this paper, in the numbering of arXiv v2.
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

/-! ### Two convergence lemmas -/

/-- `|‖a‖² − ‖b‖²| ≤ 2 L ‖a − b‖` when `‖a‖, ‖b‖ ≤ L`. -/
theorem abs_sq_norm_sub_sq_norm_le {a b : Rn n} {L : ℝ} (ha : ‖a‖ ≤ L) (hb : ‖b‖ ≤ L) :
    |‖a‖ ^ 2 - ‖b‖ ^ 2| ≤ 2 * L * ‖a - b‖ := by
  rw [sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  exact mul_le_mul (by linarith) (abs_norm_sub_norm_le a b) (abs_nonneg _)
    (by linarith [norm_nonneg a])

/-- `L²` convergence of uniformly bounded vector fields on a set of finite measure implies
convergence of `∫ ‖g_k‖²`. -/
theorem tendsto_setIntegral_norm_sq_of_tendsto_sub {S : Set (Rn n)} (hS : MeasurableSet S)
    (hSf : volume S < ⊤) {g : ℕ → Rn n → Rn n} {g₀ : Rn n → Rn n} {L : ℝ}
    (hgm : ∀ k, Measurable (g k)) (hg0m : Measurable g₀) (hgb : ∀ k, ∀ y ∈ S, ‖g k y‖ ≤ L)
    (hg0b : ∀ y ∈ S, ‖g₀ y‖ ≤ L)
    (hlim : Tendsto (fun k => ∫ y in S, ‖g k y - g₀ y‖ ^ 2) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ y in S, ‖g k y‖ ^ 2) atTop (𝓝 (∫ y in S, ‖g₀ y‖ ^ 2)) := by
  have hint : ∀ f : Rn n → ℝ, Measurable f → ∀ M, (∀ y ∈ S, |f y| ≤ M) → IntegrableOn f S :=
    fun f hf M hM => IntegrableOn.of_bound hSf hf.aestronglyMeasurable M
      ((ae_restrict_iff' hS).2 (.of_forall fun y hy => by rw [Real.norm_eq_abs]; exact hM y hy))
  have hL0 : ∀ y ∈ S, 0 ≤ L := fun y hy => (norm_nonneg _).trans (hg0b y hy)
  have hsq : ∀ k, IntegrableOn (fun y => ‖g k y - g₀ y‖ ^ 2) S := fun k =>
    hint _ (((hgm k).sub hg0m).norm.pow_const 2) ((2 * L) ^ 2) fun y hy => by
      rw [abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans (by
        linarith [hgb k y hy, hg0b y hy])) 2
  have hlin : ∀ k, IntegrableOn (fun y => ‖g k y - g₀ y‖) S := fun k =>
    hint _ ((hgm k).sub hg0m).norm (2 * L) fun y hy => by
      rw [abs_of_nonneg (norm_nonneg _)]
      exact (norm_sub_le _ _).trans (by linarith [hgb k y hy, hg0b y hy])
  have hone : IntegrableOn (fun _ : Rn n => (1 : ℝ)) S := integrableOn_const hSf.ne
  -- Cauchy–Schwarz: `(∫_S ‖g_k − g₀‖)² ≤ |S| ∫_S ‖g_k − g₀‖²`.
  have hCS : ∀ k, (∫ y in S, ‖g k y - g₀ y‖) ^ 2 ≤
      (∫ y in S, ‖g k y - g₀ y‖ ^ 2) * volume.real S := by
    intro k
    have := sq_integral_mul_le (μ := volume.restrict S) (F := fun y => ‖g k y - g₀ y‖)
      (G := fun _ => (1 : ℝ)) (hsq k) (by simp only [one_pow]; exact hone)
      (by simp only [mul_one]; exact hlin k)
    simpa [Measure.real, Measure.restrict_apply MeasurableSet.univ] using this
  have hD : Tendsto (fun k => ∫ y in S, ‖g k y - g₀ y‖) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => √((∫ y in S, ‖g k y - g₀ y‖ ^ 2) * volume.real S)) atTop
        (𝓝 0) := by
      simpa using (hlim.mul_const (volume.real S)).sqrt
    refine squeeze_zero (fun k => integral_nonneg fun _ => norm_nonneg _) (fun k => ?_) h1
    exact (le_abs_self _).trans (Real.abs_le_sqrt (hCS k))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hbd : ∀ k, ‖(∫ y in S, ‖g k y‖ ^ 2) - ∫ y in S, ‖g₀ y‖ ^ 2‖ ≤
      2 * L * ∫ y in S, ‖g k y - g₀ y‖ := by
    intro k
    by_cases hSe : S.Nonempty
    · obtain ⟨y₀, hy₀⟩ := hSe
      have hLn : 0 ≤ L := hL0 y₀ hy₀
      rw [← integral_sub (hint _ ((hgm k).norm.pow_const 2) (L ^ 2) fun y hy => by
          rw [abs_of_nonneg (sq_nonneg _)]
          exact pow_le_pow_left₀ (norm_nonneg _) (hgb k y hy) 2)
        (hint _ (hg0m.norm.pow_const 2) (L ^ 2) fun y hy => by
          rw [abs_of_nonneg (sq_nonneg _)]
          exact pow_le_pow_left₀ (norm_nonneg _) (hg0b y hy) 2),
        ← integral_const_mul]
      refine norm_integral_le_of_norm_le ((hlin k).const_mul _)
        ((ae_restrict_iff' hS).2 (.of_forall fun y hy => ?_))
      rw [Real.norm_eq_abs]
      exact abs_sq_norm_sub_sq_norm_le (hgb k y hy) (hg0b y hy)
    · rw [not_nonempty_iff_eq_empty] at hSe
      simp [hSe]
  refine squeeze_zero (fun _ => norm_nonneg _) hbd ?_
  simpa using hD.const_mul (2 * L)

/-- `M_0(u_{x,r_k}, χ_{x,r_k}; t) → m` when `M_x(r) → m` as `r → 0+` and `r_k → 0+`. -/
theorem tendsto_monotonicityM_rescale [NeZero n] {u χ : Rn n → ℝ} {x : Rn n} {m : ℝ}
    (hm : Tendsto (monotonicityM u χ x) (𝓝[>] 0) (𝓝 m)) {r : ℕ → ℝ} (hr : ∀ k, 0 < r k)
    (hr0 : Tendsto r atTop (𝓝 0)) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun k => monotonicityM (oneHomRescale u x (r k)) (chiRescale χ x (r k)) 0 t) atTop
      (𝓝 m) := by
  have e : ∀ k, monotonicityM u χ x (r k * t) =
      monotonicityM (oneHomRescale u x (r k)) (chiRescale χ x (r k)) 0 t := fun k =>
    (monotonicityM_rescale u χ x (hr k) t).symm
  refine (hm.comp (tendsto_nhdsWithin_iff.2 ⟨?_, .of_forall fun k => mul_pos (hr k) ht⟩)).congr e
  simpa using hr0.mul_const t

namespace IsVariationalSolution

variable {Ω : Set (Rn n)} {C : ℝ≥0} {u χ : Rn n → ℝ} {x : Rn n} {R : ℝ}

/-! ### Blow-up sequences -/

/-- For `r_k → 0+`, the rescalings `(u_{x,r_k}, χ_{x,r_k})` are eventually variational solutions
on `B_ρ`. -/
theorem eventually_rescale_ball (h : IsVariationalSolution Ω C u χ) (hR0 : 0 < R)
    (hR : ball x R ⊆ Ω) {r : ℕ → ℝ} (hr : ∀ k, 0 < r k) (hr0 : Tendsto r atTop (𝓝 0)) {ρ : ℝ}
    (hρ : 0 < ρ) : ∀ᶠ k in atTop,
      IsVariationalSolution (ball 0 ρ) C (oneHomRescale u x (r k)) (chiRescale χ x (r k)) := by
  filter_upwards [hr0.eventually (gt_mem_nhds (div_pos hR0 hρ))] with k hk
  refine (h.rescale x (hr k)).mono isOpen_ball
    ((ball_subset_ball ?_).trans (ball_div_subset_preimage (hr k) hR))
  rw [le_div_iff₀ (hr k)]
  rw [lt_div_iff₀ hρ] at hk
  linarith

/-- The blow-up data on the window `B_ρ`: after dropping finitely many terms, the rescalings are
variational solutions on `B_ρ`, converge locally uniformly there, and `M_0(u_{x,r_k}; t) → m`. -/
theorem blowup_window [NeZero n] (h : IsVariationalSolution Ω C u χ) (hR0 : 0 < R)
    (hR : ball x R ⊆ Ω) {m : ℝ} (hm : Tendsto (monotonicityM u χ x) (𝓝[>] 0) (𝓝 m))
    {r : ℕ → ℝ} (hr : ∀ k, 0 < r k) (hr0 : Tendsto r atTop (𝓝 0)) {u₀ : Rn n → ℝ}
    (hconv : TendstoLocallyUniformly (fun k => oneHomRescale u x (r k)) u₀ atTop) {ρ : ℝ}
    (hρ : 0 < ρ) : ∃ k₀ : ℕ,
      (∀ j, IsVariationalSolution (ball 0 ρ) C (oneHomRescale u x (r (j + k₀)))
        (chiRescale χ x (r (j + k₀)))) ∧
      TendstoLocallyUniformlyOn (fun j => oneHomRescale u x (r (j + k₀))) u₀ atTop (ball 0 ρ) ∧
      ∀ t, 0 < t → Tendsto (fun j => monotonicityM (oneHomRescale u x (r (j + k₀)))
        (chiRescale χ x (r (j + k₀))) 0 t) atTop (𝓝 m) := by
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 (h.eventually_rescale_ball hR0 hR hr hr0 hρ)
  refine ⟨k₀, fun j => hk₀ _ (Nat.le_add_left _ _), ?_, fun t ht => ?_⟩
  · exact tendstoLocallyUniformlyOn_comp_add_nat
      ((tendstoLocallyUniformlyOn_univ.2 hconv).mono (subset_univ _)) k₀
  · exact (tendsto_add_atTop_iff_nat k₀).2 (tendsto_monotonicityM_rescale hm hr hr0 ht)

/-- On the window `B_ρ`, a blow-up is Lipschitz, harmonic on its positivity set, and satisfies
Euler's identity away from `0`. -/
theorem blowup_ball [NeZero n] (h : IsVariationalSolution Ω C u χ) (hR0 : 0 < R)
    (hR : ball x R ⊆ Ω) {m : ℝ} (hm : Tendsto (monotonicityM u χ x) (𝓝[>] 0) (𝓝 m))
    {r : ℕ → ℝ} (hr : ∀ k, 0 < r k) (hr0 : Tendsto r atTop (𝓝 0)) {u₀ : Rn n → ℝ}
    (hconv : TendstoLocallyUniformly (fun k => oneHomRescale u x (r k)) u₀ atTop) {ρ : ℝ}
    (hρ : 0 < ρ) :
    IsLipHarmonicPos (ball 0 ρ) u₀ ∧ LipschitzOnWith C u₀ (ball 0 ρ) ∧
      ∀ y ∈ ball (0 : Rn n) ρ, y ≠ 0 → 0 < u₀ y → ⟪gradient u₀ y, y⟫ = u₀ y := by
  obtain ⟨k₀, hw, hconv', hM'⟩ := h.blowup_window hR0 hR hm hr hr0 hconv hρ
  have hwL := fun j => (hw j).isLipHarmonicPos
  have hL := fun j => (hw j).lipschitzOnWith
  refine ⟨IsLipHarmonicPos.of_tendstoLocallyUniformlyOn hwL hL hconv',
    lipschitzOnWith_of_tendstoLocallyUniformlyOn hL hconv' (subset_refl _), ?_⟩
  intro y hy hy0 hpos
  refine inner_gradient_eq_of_tendsto_monotonicityM_sub hw hconv' (fun s t hs hst _ => ?_) hy hy0
    hpos
  simpa using (hM' t (hs.trans_le hst)).sub (hM' s hs)

/-- A blow-up limit at `x` forces `u(x) = 0`. -/
theorem eq_zero_of_tendstoLocallyUniformly_rescale {r : ℕ → ℝ} (hr : ∀ k, 0 < r k)
    (hr0 : Tendsto r atTop (𝓝 0)) {u₀ : Rn n → ℝ}
    (hconv : TendstoLocallyUniformly (fun k => oneHomRescale u x (r k)) u₀ atTop) :
    u x = 0 := by
  have e : ∀ k, r k * oneHomRescale u x (r k) 0 = u x := fun k => by
    rw [oneHomRescale_apply, smul_zero, add_zero]
    field_simp [(hr k).ne']
  have := hr0.mul ((tendstoLocallyUniformlyOn_univ.2 hconv).tendsto_at (mem_univ 0))
  rw [zero_mul] at this
  exact tendsto_nhds_unique tendsto_const_nhds (this.congr e)

section Blowup

variable [NeZero n] (h : IsVariationalSolution Ω C u χ) (hx : x ∈ Ω) {r : ℕ → ℝ}
  (hr : ∀ k, 0 < r k) (hr0 : Tendsto r atTop (𝓝 0)) {u₀ : Rn n → ℝ}
  (hconv : TendstoLocallyUniformly (fun k => oneHomRescale u x (r k)) u₀ atTop)
include h hx hr hr0 hconv

/-- `blowup_ball` for any window, with the hypotheses of the section. -/
theorem blowup_ball' {ρ : ℝ} (hρ : 0 < ρ) :
    IsLipHarmonicPos (ball 0 ρ) u₀ ∧ LipschitzOnWith C u₀ (ball 0 ρ) ∧
      ∀ y ∈ ball (0 : Rn n) ρ, y ≠ 0 → 0 < u₀ y → ⟪gradient u₀ y, y⟫ = u₀ y := by
  obtain ⟨R, hR0, hR⟩ := h.exists_ball_subset hx
  have hux := eq_zero_of_tendstoLocallyUniformly_rescale hr hr0 hconv
  obtain ⟨m, -, hm⟩ := h.exists_tendsto_monotonicityM_of_eq_zero hx hux
  exact h.blowup_ball hR0 hR hm hr hr0 hconv hρ

omit [NeZero n] h hx in
/-- `u₀(0) = 0`. -/
theorem blowup_apply_zero : u₀ 0 = 0 := by
  have hux := eq_zero_of_tendstoLocallyUniformly_rescale hr hr0 hconv
  refine tendsto_nhds_unique ((tendstoLocallyUniformlyOn_univ.2 hconv).tendsto_at (mem_univ 0)) ?_
  simp [hux]

/-- **Blow-ups are Lipschitz** (proof of Proposition 3.5): `u₀` is `C_V`-Lipschitz on `ℝⁿ`. -/
theorem blowup_lipschitzWith : LipschitzWith C u₀ := by
  refine LipschitzWith.of_dist_le_mul fun y z => ?_
  have hρ : 0 < ‖y‖ + ‖z‖ + 1 := by positivity
  have hy : y ∈ ball (0 : Rn n) (‖y‖ + ‖z‖ + 1) := by
    rw [mem_ball_zero_iff]; linarith [norm_nonneg z]
  have hz : z ∈ ball (0 : Rn n) (‖y‖ + ‖z‖ + 1) := by
    rw [mem_ball_zero_iff]; linarith [norm_nonneg y]
  exact (blowup_ball' h hx hr hr0 hconv hρ).2.1.dist_le_mul y hy z hz

/-- **Blow-ups are harmonic on their positivity set** (proof of Proposition 3.5). -/
theorem blowup_isLipHarmonicPos : IsLipHarmonicPos univ u₀ where
  isOpen := isOpen_univ
  nonneg y _ :=
    (blowup_ball' h hx hr hr0 hconv (ρ := ‖y‖ + 1) (by positivity)).1.nonneg y
      (by rw [mem_ball_zero_iff]; linarith)
  lipschitzOnWith := ⟨C, fun _ _ _ => (blowup_lipschitzWith h hx hr hr0 hconv).lipschitzOnWith⟩
  harmonicAt y _ hpos :=
    (blowup_ball' h hx hr hr0 hconv (ρ := ‖y‖ + 1) (by positivity)).1.harmonicAt y
      (by rw [mem_ball_zero_iff]; linarith) hpos

/-- **Euler's identity for blow-ups** (proof of Proposition 3.5): `∇u₀(y)·y = u₀(y)` for every
`y`. -/
theorem blowup_inner_gradient_eq (y : Rn n) : ⟪gradient u₀ y, y⟫ = u₀ y := by
  have h0 := blowup_isLipHarmonicPos h hx hr hr0 hconv
  rcases (h0.nonneg y trivial).lt_or_eq with hpos | hzero
  · have hy0 : y ≠ 0 := by
      rintro rfl; rw [blowup_apply_zero hr hr0 hconv] at hpos; exact lt_irrefl _ hpos
    exact (blowup_ball' h hx hr hr0 hconv (ρ := ‖y‖ + 1) (by positivity)).2.2 y
      (by rw [mem_ball_zero_iff]; linarith) hy0 hpos
  · rw [h0.gradient_eq_zero_of_eq_zero trivial hzero.symm, inner_zero_left, ← hzero]

/-- **Proposition 3.4, last claim**: blow-up limits are homogeneous of degree one,
`u₀(t y) = t u₀(y)` for `t > 0`. As in the proof of Proposition 3.5, this comes after the strong
convergence of the gradients of the rescalings, which it uses. -/
theorem blowup_homogeneous : ∀ t, 0 < t → ∀ y, u₀ (t • y) = t * u₀ y := by
  have h0 := blowup_isLipHarmonicPos h hx hr hr0 hconv
  exact homogeneous_of_inner_gradient_eq (blowup_lipschitzWith h hx hr hr0 hconv).continuous
    (fun y => h0.nonneg y trivial)
    (fun y hpos => (h0.harmonicAt y trivial hpos).1.differentiableAt two_ne_zero)
    (fun y _ => blowup_inner_gradient_eq h hx hr hr0 hconv y)

end Blowup

/-! ### The density formula (3.10) -/

/-- **Formula (3.10) along a blow-up sequence** (proof of Proposition 3.5): if `u(x) = 0`,
`M_x(r) → m`, and `u_{x,r_k} → u₀` locally uniformly, then `r_k^{-n} ∫_{B_{r_k}(x)} χ → m`. -/
theorem tendsto_density_of_tendstoLocallyUniformly [NeZero n] (h : IsVariationalSolution Ω C u χ)
    (hR0 : 0 < R) (hR : ball x R ⊆ Ω) (hux : u x = 0) {m : ℝ}
    (hm : Tendsto (monotonicityM u χ x) (𝓝[>] 0) (𝓝 m)) {r : ℕ → ℝ} (hr : ∀ k, 0 < r k)
    (hr0 : Tendsto r atTop (𝓝 0)) {u₀ : Rn n → ℝ}
    (hconv : TendstoLocallyUniformly (fun k => oneHomRescale u x (r k)) u₀ atTop) :
    Tendsto (fun k => (r k ^ n)⁻¹ * ∫ y in ball x (r k), χ y) atTop (𝓝 m) := by
  obtain ⟨k₀, hw, hconv', hM'⟩ := h.blowup_window hR0 hR hm hr hr0 hconv two_pos
  obtain ⟨h0, -, heuler⟩ := h.blowup_ball hR0 hR hm hr hr0 hconv two_pos
  set w : ℕ → Rn n → ℝ := fun j => oneHomRescale u x (r (j + k₀)) with hwdef
  set χw : ℕ → Rn n → ℝ := fun j => chiRescale χ x (r (j + k₀)) with hχwdef
  refine (tendsto_add_atTop_iff_nat k₀).1 ?_
  have hwL : ∀ j, IsLipHarmonicPos (ball 0 2) (w j) := fun j => (hw j).isLipHarmonicPos
  have hL : ∀ j y s, ball y s ⊆ ball (0 : Rn n) 2 → LipschitzOnWith C (w j) (ball y s) :=
    fun j => (hw j).lipschitzOnWith
  have hE := integral_norm_gradient_sq_eq_of_inner_gradient_eq h0 heuler one_pos one_lt_two
  rw [one_mul] at hE
  have hB1 : ball (0 : Rn n) 1 ⊆ ball 0 2 := ball_subset_ball one_le_two
  -- `∫_{B_1} |∇w_j|² → ∫_{B_1} |∇u₀|²`.
  have hG : Tendsto (fun j => ∫ y in ball (0 : Rn n) 1, ‖gradient (w j) y‖ ^ 2) atTop
      (𝓝 (∫ y in ball (0 : Rn n) 1, ‖gradient u₀ y‖ ^ 2)) := by
    have hK := tendsto_setIntegral_norm_gradient_sub_sq hwL hL hconv'
      (isCompact_closedBall (0 : Rn n) 1) (closedBall_subset_ball one_lt_two)
    refine tendsto_setIntegral_norm_sq_of_tendsto_sub measurableSet_ball measure_ball_lt_top
      (fun _ => measurable_gradient _) (measurable_gradient _) (L := C)
      (fun j y hy => (hw j).norm_gradient_le (hB1 hy))
      (fun y hy => norm_gradient_le_of_tendstoLocallyUniformlyOn hwL hL hconv' (hB1 hy)) ?_
    refine squeeze_zero (fun j => setIntegral_nonneg measurableSet_ball fun _ _ => sq_nonneg _)
      (fun j => ?_) hK
    refine setIntegral_mono_set ?_ (.of_forall fun _ => sq_nonneg _)
      (.of_forall ball_subset_closedBall)
    refine integrableOn_of_abs_le (isCompact_closedBall _ _)
      (((measurable_gradient _).sub (measurable_gradient _)).norm.pow_const 2).aestronglyMeasurable
      (M := (2 * C) ^ 2) fun y hy => ?_
    have hy2 := closedBall_subset_ball one_lt_two hy
    rw [abs_of_nonneg (sq_nonneg _)]
    refine pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans ?_) 2
    linarith [(hw j).norm_gradient_le hy2,
      norm_gradient_le_of_tendstoLocallyUniformlyOn hwL hL hconv' hy2]
  -- `∫_{∂B_1} w_j² → ∫_{∂B_1} u₀²`.
  have hsph : ∀ ω : sphere (0 : Rn n) 1, (0 : Rn n) + (1 : ℝ) • (ω : Rn n) ∈ ball (0 : Rn n) 2 :=
    fun ω => sphere_subset_closedBall.trans (closedBall_subset_ball one_lt_two)
      (add_smul_mem_sphere zero_le_one ω)
  have hS : Tendsto (fun j => sphereIntegral (fun y => w j y ^ 2) 0 1) atTop
      (𝓝 (sphereIntegral (fun y => u₀ y ^ 2) 0 1)) := by
    simp only [sphereIntegral]
    refine Tendsto.const_mul _ ?_
    refine tendsto_integral_of_dominated_convergence (fun _ => (C : ℝ) ^ 2) (fun j => ?_)
      (integrable_const _) (fun j => .of_forall fun ω => ?_) (.of_forall fun ω => ?_)
    · exact (((hw j).continuousOn.pow 2).mono (sphere_subset_closedBall.trans
        (closedBall_subset_ball one_lt_two))).sphereIntegrable zero_le_one |>.aestronglyMeasurable
    · have h1 := (hw j).lipschitzOnWith 0 2 (subset_refl _) |>.dist_le_mul _ (hsph ω) 0
        (mem_ball_self two_pos)
      have hw0 : oneHomRescale u x (r (j + k₀)) 0 = 0 := by simp [hux]
      have hnorm : dist ((0 : Rn n) + (1 : ℝ) • (ω : Rn n)) 0 = 1 := by
        rw [dist_zero_right, zero_add, one_smul]; exact norm_eq_of_mem_sphere ω
      rw [hw0, hnorm, mul_one, Real.dist_eq, sub_zero] at h1
      change ‖oneHomRescale u x (r (j + k₀)) ((0 : Rn n) + (1 : ℝ) • (ω : Rn n)) ^ 2‖ ≤ (C : ℝ) ^ 2
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    · exact (hconv'.tendsto_at (hsph ω)).pow 2
  -- The identity `r^{-n} ∫_{B_r(x)} χ = M_0(w; 1) − ∫_{B_1} |∇w|² + ∫_{∂B_1} w²`.
  have hid : ∀ j, (r (j + k₀) ^ n)⁻¹ * ∫ y in ball x (r (j + k₀)), χ y =
      monotonicityM (w j) (χw j) 0 1 - (∫ y in ball (0 : Rn n) 1, ‖gradient (w j) y‖ ^ 2) +
        sphereIntegral (fun y => w j y ^ 2) 0 1 := by
    intro j
    have e1 := setIntegral_chiRescale χ x (hr (j + k₀)) 1
    rw [mul_one] at e1
    rw [← e1, monotonicityM, energyD, heightH, (hw j).integral_energy_eq hB1]
    simp only [one_pow, inv_one, one_mul]
    ring
  have := ((hM' 1 one_pos).sub hG).add hS
  rw [hE, sub_add_cancel] at this
  exact this.congr fun j => (hid j).symm

/-- **Proposition 3.5, formula (3.10)**: if `u(x) = 0`, then
`M_x(u; 0+)` is a real number `m`, `M_x(r) → m`, and `r^{-n} ∫_{B_r(x)} χ → m` as `r → 0+`. -/
theorem tendsto_monotonicityM_zero [NeZero n] (h : IsVariationalSolution Ω C u χ) (hx : x ∈ Ω)
    (hux : u x = 0) : ∃ m : ℝ, Mzero u χ x = m ∧
      Tendsto (monotonicityM u χ x) (𝓝[>] 0) (𝓝 m) ∧
      Tendsto (fun r => (r ^ n)⁻¹ * ∫ y in ball x r, χ y) (𝓝[>] 0) (𝓝 m) := by
  obtain ⟨R, hR0, hR⟩ := h.exists_ball_subset hx
  obtain ⟨m, hm, hMlim⟩ := h.exists_tendsto_monotonicityM_of_eq_zero hx hux
  refine ⟨m, hm, hMlim, tendsto_of_subseq_tendsto fun ns hns => ?_⟩
  obtain ⟨k₁, hk₁⟩ := eventually_atTop.1 (hns.eventually self_mem_nhdsWithin)
  set r : ℕ → ℝ := fun k => ns (k + k₁) with hrdef
  have hr : ∀ k, 0 < r k := fun k => hk₁ _ (Nat.le_add_left _ _)
  have hr0 : Tendsto r atTop (𝓝 0) :=
    (tendsto_nhds_of_tendsto_nhdsWithin hns).comp (tendsto_add_atTop_nat k₁)
  have hρ : Tendsto (fun k => R / r k) atTop atTop := by
    have h1 : Tendsto r atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.2 ⟨hr0, .of_forall hr⟩
    simpa [div_eq_mul_inv] using (tendsto_inv_nhdsGT_zero.comp h1).const_mul_atTop hR0
  have hLip : ∀ k, LipschitzOnWith C (oneHomRescale u x (r k)) (ball 0 (R / r k)) := fun k =>
    (h.rescale x (hr k)).lipschitzOnWith 0 _ (ball_div_subset_preimage (hr k) hR)
  have hM0 : ∀ k, |oneHomRescale u x (r k) 0| ≤ 0 := fun k => by simp [hux]
  obtain ⟨φ, hφ, u₀, -, hconv⟩ :=
    exists_blowup_subseq hρ (fun k => div_pos hR0 (hr k)) hLip hM0
  exact ⟨fun k => φ k + k₁, h.tendsto_density_of_tendstoLocallyUniformly hR0 hR hux hMlim
    (fun k => hr (φ k)) (hr0.comp hφ.tendsto_atTop) hconv⟩

/-- **Proposition 3.5**: if `u(x) > 0`, then `M_x(r) → −∞` as `r → 0+`. -/
theorem tendsto_monotonicityM_zero_of_pos [NeZero n] (h : IsVariationalSolution Ω C u χ)
    (hx : x ∈ Ω) (hpos : 0 < u x) : Tendsto (monotonicityM u χ x) (𝓝[>] 0) atBot :=
  h.tendsto_monotonicityM_atBot_of_pos hx hpos

/-! ### Bounds on `M_x(0+)` -/

/-- `0 ≤ r^{-n} ∫_{B_r(x)} χ ≤ |B_1|` when `B_r(x) ⊆ Ω`. -/
theorem density_mem_Icc (h : IsVariationalSolution Ω C u χ) {r : ℝ} (hr : 0 < r)
    (hball : ball x r ⊆ Ω) :
    (r ^ n)⁻¹ * ∫ y in ball x r, χ y ∈ Icc 0 (unitBallVolume n) := by
  have h1 : 0 ≤ ∫ y in ball x r, (1 - χ y) :=
    setIntegral_nonneg measurableSet_ball fun y hy =>
      sub_nonneg.2 (abs_le.1 (h.abs_chi_le_one (hball hy))).2
  rw [h.integral_one_sub_chi hball hr] at h1
  have hrn : 0 < r ^ n := pow_pos hr n
  refine ⟨mul_nonneg (inv_nonneg.2 hrn.le)
    (setIntegral_nonneg measurableSet_ball fun y hy => h.chi_nonneg (hball hy)), ?_⟩
  rw [inv_mul_le_iff₀ hrn]
  linarith

/-- **Proposition 3.5**: `M_x(0+) ≤ |B_1|`. -/
theorem Mzero_le_unitBallVolume [NeZero n] (h : IsVariationalSolution Ω C u χ) (hx : x ∈ Ω) :
    Mzero u χ x ≤ unitBallVolume n := by
  rcases (h.nonneg x hx).lt_or_eq with hpos | hux
  · rw [h.Mzero_eq_bot_of_pos hx hpos]; exact bot_le
  obtain ⟨R, hR0, hR⟩ := h.exists_ball_subset hx
  obtain ⟨m, hm, -, hlim⟩ := h.tendsto_monotonicityM_zero hx hux.symm
  rw [hm, EReal.coe_le_coe_iff]
  refine le_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT hR0] with r hr
  exact (h.density_mem_Icc hr.1 ((ball_subset_ball hr.2.le).trans hR)).2

/-- **Proposition 3.5**: `0 ≤ M_x(0+)` when `u(x) = 0`. -/
theorem Mzero_nonneg [NeZero n] (h : IsVariationalSolution Ω C u χ) (hx : x ∈ Ω)
    (hux : u x = 0) : 0 ≤ Mzero u χ x := by
  obtain ⟨R, hR0, hR⟩ := h.exists_ball_subset hx
  obtain ⟨m, hm, -, hlim⟩ := h.tendsto_monotonicityM_zero hx hux
  rw [hm, ← EReal.coe_zero, EReal.coe_le_coe_iff]
  refine ge_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT hR0] with r hr
  exact (h.density_mem_Icc hr.1 ((ball_subset_ball hr.2.le).trans hR)).1

end IsVariationalSolution

end InnerVariational
