/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Blowup.Renormalized
import Mathlib.Data.Real.StarOrdered
import Mathlib.Algebra.Order.Ring.Star
public import InnerVariational.Blowup.Sobolev

/-!
# Vanishing tangential energy passes to weak limits

The hypothesis of Theorem 5.3 of Kriventsov–Weiss says that the tangential part of `∇v_k` tends
to `0` in `L²(A)`. In the rotation-free form of Theorem 5.3 proved in this library
(`Blowup/Approx1D.lean`), the direction `ν_k` may depend on `k`. This file shows that the weak
limit `G` of `∇v_k` then satisfies `G = ⟪G, ν⟫ ν` a.e., where `ν = lim ν_k`.

## Main definitions

* `tangentialPart ν`: the map `w ↦ w − ⟪ν, w⟫ ν` (the projection onto `ν^⊥` for a unit `ν`).

## Main results

* `tendsto_integral_norm_tangentialPart_sq`: the tangential energy with respect to the limit
  direction `ν₀ = lim ν_k` also tends to `0`.
* `ae_tangentialPart_eq_zero_of_weakTendstoL2`: if `F k ⇀ G` weakly in `L²`, `F k` is bounded in
  `L²`, `ν k → ν₀` are unit vectors, and `∫ ‖tangentialPart (ν k) (F k)‖² → 0`, then
  `tangentialPart ν₀ G = 0` a.e.

## References

* D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
  DOI 10.1002/cpa.22226; arXiv:2306.10131. Result and equation numbers refer to arXiv v2.
-/

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational

section Tangential

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The tangential part `w ↦ w − ⟪ν, w⟫ ν` (the projection onto `ν^⊥` when `‖ν‖ = 1`). -/
def tangentialPart (ν : E) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E - (innerSL ℝ ν).smulRight ν

theorem tangentialPart_apply (ν w : E) : tangentialPart ν w = w - ⟪ν, w⟫ • ν := by
  simp [tangentialPart]

/-- `tangentialPart ν` is symmetric. -/
theorem inner_tangentialPart_left (ν w h : E) :
    ⟪tangentialPart ν w, h⟫ = ⟪w, tangentialPart ν h⟫ := by
  simp only [tangentialPart_apply, inner_sub_left, inner_sub_right, inner_smul_left,
    inner_smul_right, conj_trivial]
  rw [real_inner_comm ν w]
  ring

/-- `w = ⟪w, ν⟫ ν` if and only if the tangential part vanishes. -/
theorem tangentialPart_eq_zero_iff (ν w : E) : tangentialPart ν w = 0 ↔ w = ⟪w, ν⟫ • ν := by
  rw [tangentialPart_apply, sub_eq_zero, real_inner_comm]

/-- The tangential part depends Lipschitz-continuously on the direction. -/
theorem norm_tangentialPart_sub_le (ν ν' w : E) :
    ‖tangentialPart ν w - tangentialPart ν' w‖ ≤ (‖ν‖ + ‖ν'‖) * ‖w‖ * ‖ν - ν'‖ := by
  have e : tangentialPart ν w - tangentialPart ν' w = ⟪ν' - ν, w⟫ • ν' + ⟪ν, w⟫ • (ν' - ν) := by
    simp only [tangentialPart_apply, inner_sub_left, sub_smul, smul_sub]
    abel
  rw [e]
  calc ‖⟪ν' - ν, w⟫ • ν' + ⟪ν, w⟫ • (ν' - ν)‖
      ≤ ‖⟪ν' - ν, w⟫ • ν'‖ + ‖⟪ν, w⟫ • (ν' - ν)‖ := norm_add_le _ _
    _ = ‖⟪ν' - ν, w⟫‖ * ‖ν'‖ + ‖⟪ν, w⟫‖ * ‖ν' - ν‖ := by rw [norm_smul, norm_smul]
    _ ≤ (‖ν' - ν‖ * ‖w‖) * ‖ν'‖ + (‖ν‖ * ‖w‖) * ‖ν' - ν‖ :=
        add_le_add (mul_le_mul_of_nonneg_right (norm_inner_le_norm _ _) (norm_nonneg _))
          (mul_le_mul_of_nonneg_right (norm_inner_le_norm _ _) (norm_nonneg _))
    _ = (‖ν‖ + ‖ν'‖) * ‖w‖ * ‖ν - ν'‖ := by
        rw [norm_sub_rev ν' ν]
        ring

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **Tangential energy with respect to a limit direction.** If `∫ ‖F k‖² ≤ C`, the unit vectors
`ν k` converge to `ν₀`, and `∫ ‖F k − ⟪ν k, F k⟫ ν k‖² → 0`, then also
`∫ ‖F k − ⟪ν₀, F k⟫ ν₀‖² → 0`. -/
theorem tendsto_integral_norm_tangentialPart_sq {F : ℕ → α → E} (hF : ∀ k, MemLp (F k) 2 μ)
    {C : ℝ} (hbd : ∀ k, ∫ x, ‖F k x‖ ^ 2 ∂μ ≤ C) {ν : ℕ → E} {ν₀ : E} (hν : ∀ k, ‖ν k‖ = 1)
    (hνlim : Tendsto ν atTop (𝓝 ν₀))
    (htan : Tendsto (fun k => ∫ x, ‖tangentialPart (ν k) (F k x)‖ ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, ‖tangentialPart ν₀ (F k x)‖ ^ 2 ∂μ) atTop (𝓝 0) := by
  have hν₀ : ‖ν₀‖ = 1 := by
    have h := (continuous_norm.tendsto ν₀).comp hνlim
    simp only [Function.comp_def, hν] at h
    exact (tendsto_nhds_unique tendsto_const_nhds h).symm
  set P := tangentialPart ν₀ with hP
  have hPF : ∀ k, MemLp (fun x => P (F k x)) 2 μ := fun k => P.comp_memLp' (hF k)
  have hbound : ∀ k, ∫ x, ‖P (F k x)‖ ^ 2 ∂μ ≤
      2 * (∫ x, ‖tangentialPart (ν k) (F k x)‖ ^ 2 ∂μ) + 8 * ‖ν₀ - ν k‖ ^ 2 * C := by
    intro k
    have hPk : MemLp (fun x => tangentialPart (ν k) (F k x)) 2 μ :=
      (tangentialPart (ν k)).comp_memLp' (hF k)
    have hpt : ∀ x, ‖P (F k x)‖ ^ 2 ≤
        2 * ‖tangentialPart (ν k) (F k x)‖ ^ 2 + 8 * ‖ν₀ - ν k‖ ^ 2 * ‖F k x‖ ^ 2 := by
      intro x
      have h1 := norm_tangentialPart_sub_le ν₀ (ν k) (F k x)
      rw [hν₀, hν k] at h1
      have h2 := norm_le_norm_add_norm_sub' (P (F k x)) (tangentialPart (ν k) (F k x))
      set a := ‖tangentialPart (ν k) (F k x)‖
      set b := ‖P (F k x) - tangentialPart (ν k) (F k x)‖
      have ha : 0 ≤ a := norm_nonneg _
      have hb : 0 ≤ b := norm_nonneg _
      have hc : 0 ≤ ‖F k x‖ * ‖ν₀ - ν k‖ := by positivity
      have h3 : ‖P (F k x)‖ ^ 2 ≤ (a + b) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
      have h4 : b ^ 2 ≤ (2 * (‖F k x‖ * ‖ν₀ - ν k‖)) ^ 2 :=
        pow_le_pow_left₀ hb (by linarith) 2
      nlinarith [sq_nonneg (a - b)]
    calc ∫ x, ‖P (F k x)‖ ^ 2 ∂μ
        ≤ ∫ x, (2 * ‖tangentialPart (ν k) (F k x)‖ ^ 2 +
            8 * ‖ν₀ - ν k‖ ^ 2 * ‖F k x‖ ^ 2) ∂μ :=
          integral_mono (MemLp.integrable_norm_sq (hPF k))
            (((MemLp.integrable_norm_sq hPk).const_mul 2).add
              ((MemLp.integrable_norm_sq (hF k)).const_mul _)) hpt
      _ = 2 * (∫ x, ‖tangentialPart (ν k) (F k x)‖ ^ 2 ∂μ) +
            8 * ‖ν₀ - ν k‖ ^ 2 * ∫ x, ‖F k x‖ ^ 2 ∂μ := by
          rw [integral_add ((MemLp.integrable_norm_sq hPk).const_mul 2)
            ((MemLp.integrable_norm_sq (hF k)).const_mul _), integral_const_mul,
            integral_const_mul]
      _ ≤ _ := by
          gcongr
          exact hbd k
  have hνn : Tendsto (fun k => ‖ν₀ - ν k‖) atTop (𝓝 0) := by
    have := tendsto_iff_norm_sub_tendsto_zero.1 hνlim
    simpa only [norm_sub_rev] using this
  have hRHS : Tendsto (fun k => 2 * (∫ x, ‖tangentialPart (ν k) (F k x)‖ ^ 2 ∂μ) +
      8 * ‖ν₀ - ν k‖ ^ 2 * C) atTop (𝓝 0) := by
    have := (htan.const_mul 2).add (((hνn.pow 2).const_mul 8).mul_const C)
    simpa using this
  exact squeeze_zero (fun k => integral_nonneg fun x => by positivity) hbound hRHS

/-- **Vanishing tangential energy passes to weak limits.** If `F k ⇀ G` weakly in `L²(μ)`,
`∫ ‖F k‖² ≤ C`, the unit vectors `ν k` converge to `ν₀`, and
`∫ ‖F k − ⟪ν k, F k⟫ ν k‖² → 0`, then `G = ⟪G, ν₀⟫ ν₀` a.e. -/
theorem ae_tangentialPart_eq_zero_of_weakTendstoL2 {F : ℕ → α → E} {G : α → E}
    (hw : WeakTendstoL2 μ F G) (hF : ∀ k, MemLp (F k) 2 μ) (hG : MemLp G 2 μ) {C : ℝ}
    (hbd : ∀ k, ∫ x, ‖F k x‖ ^ 2 ∂μ ≤ C) {ν : ℕ → E} {ν₀ : E} (hν : ∀ k, ‖ν k‖ = 1)
    (hνlim : Tendsto ν atTop (𝓝 ν₀))
    (htan : Tendsto (fun k => ∫ x, ‖tangentialPart (ν k) (F k x)‖ ^ 2 ∂μ) atTop (𝓝 0)) :
    ∀ᵐ x ∂μ, tangentialPart ν₀ (G x) = 0 := by
  set P := tangentialPart ν₀ with hP
  have hPF : ∀ k, MemLp (fun x => P (F k x)) 2 μ := fun k => P.comp_memLp' (hF k)
  have hPG : MemLp (fun x => P (G x)) 2 μ := P.comp_memLp' hG
  -- `P F_k ⇀ P G`, since `P` is symmetric.
  have hPw : WeakTendstoL2 μ (fun k x => P (F k x)) (fun x => P (G x)) := by
    intro h hh
    have e : ∀ K : α → E, ∫ x, ⟪P (K x), h x⟫ ∂μ = ∫ x, ⟪K x, P (h x)⟫ ∂μ := fun K => by
      simp_rw [hP, inner_tangentialPart_left]
    simp only [e]
    exact hw _ (P.comp_memLp' hh)
  -- `P F_k → 0` strongly.
  have hlim := tendsto_integral_norm_tangentialPart_sq hF hbd hν hνlim htan
  have hle := hPw.integral_norm_sq_le_of_tendsto hPF hPG hlim
  filter_upwards [ae_eq_zero_of_integral_norm_sq_nonpos hPG hle] with x hx
  simpa using hx

end Tangential

end InnerVariational
