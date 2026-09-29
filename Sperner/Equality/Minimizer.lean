/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Sperner.FaberKrahn
public import Sperner.EnergyInequality
import Mathlib.Analysis.Calculus.Rademacher

/-!
# Minimizers of the Gaussian Rayleigh quotient at the half-space threshold

Let `Q(f) = ∫ |Df|² dγ - ∫ f² dγ`. By the Faber–Krahn inequality, `Q(f) ≥ 0` for every
one-homogeneous Lipschitz `f` (of any sign) with `2 γ{f ≠ 0} ≤ γ(ℝⁿ)`. A nonnegative
one-homogeneous Lipschitz `w` with `Q(w) ≤ 0` and `2 γ{w > 0} ≤ γ(ℝⁿ)` is called a minimizer.
Minimizers satisfy the weak Euler–Lagrange equation
`B(w, ψ) = ∫ ⟨∇w, ∇ψ⟩ dγ - ∫ w ψ dγ = 0` for one-homogeneous Lipschitz `ψ` supported in `{w > 0}`.
-/

open MeasureTheory Set Filter Topology InnerProductSpace
open scoped NNReal ENNReal RealInnerProductSpace Gradient

@[expose] public noncomputable section

namespace Sperner

variable {n : ℕ}

/-! ### The Faber–Krahn inequality for functions of any sign -/

lemma lipschitzWith_abs_comp {f : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) : LipschitzWith L fun x => |f x| :=
  LipschitzWith.of_dist_le_mul fun x y => by
    rw [Real.dist_eq]
    exact (abs_abs_sub_abs_le_abs_sub _ _).trans (by rw [← Real.dist_eq]; exact hf.dist_le_mul x y)

lemma norm_fderiv_abs_le (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Continuous f)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖fderiv ℝ (fun y => |f y|) x‖ ≤ ‖fderiv ℝ f x‖ := by
  rcases lt_trichotomy (f x) 0 with h | h | h
  · have : (fun y => |f y|) =ᶠ[𝓝 x] fun y => -f y :=
      Filter.eventually_of_mem ((isOpen_lt hf continuous_const).mem_nhds h)
        fun y (hy : f y < 0) => abs_of_neg hy
    rw [this.fderiv_eq, fderiv_fun_neg, norm_neg]
  · rw [fderiv_eq_zero_of_nonneg_of_eq_zero (fun y => abs_nonneg (f y)) (by simp [h]), norm_zero]
    exact norm_nonneg _
  · have : (fun y => |f y|) =ᶠ[𝓝 x] f :=
      Filter.eventually_of_mem ((isOpen_lt continuous_const hf).mem_nhds h)
        fun y (hy : 0 < f y) => abs_of_pos hy
    rw [this.fderiv_eq]

lemma dirichletEnergy_abs_le {f : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) : dirichletEnergy (fun x => |f x|) ≤ dirichletEnergy f := by
  unfold dirichletEnergy
  refine integral_mono (integrable_norm_fderiv_sq (lipschitzWith_abs_comp hf))
    (integrable_norm_fderiv_sq hf) fun x => ?_
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_abs_le f hf.continuous x) 2

lemma gaussL2_abs (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    gaussL2 (fun x => |f x|) = gaussL2 f := by
  simp [gaussL2, sq_abs]

/-- **Faber–Krahn for functions of any sign.** -/
theorem gaussL2_le_dirichletEnergy_of_ne (hn : 2 ≤ n) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {L : ℝ≥0} (hf : LipschitzWith L f) (hhom : IsOneHomogeneous f)
    (hhalf : 2 * gaussMeasure n {x | f x ≠ 0} ≤ gaussMeasure n univ) :
    gaussL2 f ≤ dirichletEnergy f := by
  have habs : IsOneHomogeneous fun x => |f x| := fun x t ht => by
    change |f (t • x)| = t * |f x|
    rw [hhom x t ht, abs_mul, abs_of_pos ht]
  have hset : {x | 0 < |f x|} = {x | f x ≠ 0} := by ext x; simp
  have := gaussL2_le_dirichletEnergy hn (lipschitzWith_abs_comp hf) (fun x => abs_nonneg _) habs
    (by rw [hset]; exact hhalf)
  rw [gaussL2_abs] at this
  exact this.trans (dirichletEnergy_abs_le hf)

/-! ### The bilinear form and the first variation -/

/-- The bilinear form `B(w, ψ) = ∫ ⟨∇w, ∇ψ⟩ dγ - ∫ w ψ dγ`. -/
def gaussBilin (w ψ : EuclideanSpace ℝ (Fin n) → ℝ) : ℝ :=
  ∫ x, fderiv ℝ w x (∇ ψ x) ∂gaussMeasure n - ∫ x, w x * ψ x ∂gaussMeasure n

lemma measurable_fderiv_apply_gradient (w ψ : EuclideanSpace ℝ (Fin n) → ℝ) :
    Measurable fun x => fderiv ℝ w x (∇ ψ x) := by
  have h2 : Measurable (∇ ψ) :=
    (toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.continuous.measurable.comp (measurable_fderiv ℝ ψ)
  have hc : Continuous fun p : (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) × EuclideanSpace ℝ (Fin n) =>
      p.1 p.2 := continuous_fst.clm_apply continuous_snd
  exact hc.measurable.comp ((measurable_fderiv ℝ w).prodMk h2)

lemma integrable_fderiv_apply_gradient {w ψ : EuclideanSpace ℝ (Fin n) → ℝ} {L K : ℝ≥0}
    (hw : LipschitzWith L w) (hψ : LipschitzWith K ψ) :
    Integrable (fun x => fderiv ℝ w x (∇ ψ x)) (gaussMeasure n) :=
  (integrable_const ((L : ℝ) * K)).mono' (measurable_fderiv_apply_gradient w ψ).aestronglyMeasurable
    (ae_of_all _ fun x => by
      refine ((fderiv ℝ w x).le_opNorm _).trans ?_
      rw [norm_gradient]
      exact mul_le_mul (norm_fderiv_le_of_lipschitz ℝ hw) (norm_fderiv_le_of_lipschitz ℝ hψ)
        (norm_nonneg _) L.2)

lemma integrable_mul_of_lipschitzWith {w ψ : EuclideanSpace ℝ (Fin n) → ℝ} {L K : ℝ≥0}
    (hw : LipschitzWith L w) (hψ : LipschitzWith K ψ) (hw0 : w 0 = 0) (hψ0 : ψ 0 = 0) :
    Integrable (fun x => w x * ψ x) (gaussMeasure n) :=
  ((integrable_norm_pow_gaussMeasure (n := n) 2).const_mul ((L : ℝ) * K)).mono'
    (hw.continuous.mul hψ.continuous).aestronglyMeasurable
    (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_mul]
      calc |w x| * |ψ x| ≤ (L * ‖x‖) * (K * ‖x‖) :=
            mul_le_mul (abs_le_mul_norm_of_lipschitzWith hw hw0 x)
              (abs_le_mul_norm_of_lipschitzWith hψ hψ0 x) (abs_nonneg _) (by positivity)
        _ = L * K * ‖x‖ ^ 2 := by ring)

/-- Pointwise expansion of `|∇(w + tψ)|²` at points of differentiability. -/
lemma norm_fderiv_add_smul_sq {w ψ : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hw : DifferentiableAt ℝ w x) (hψ : DifferentiableAt ℝ ψ x) (t : ℝ) :
    ‖fderiv ℝ (fun y => w y + t * ψ y) x‖ ^ 2 =
      ‖fderiv ℝ w x‖ ^ 2 + 2 * t * fderiv ℝ w x (∇ ψ x) + t ^ 2 * ‖fderiv ℝ ψ x‖ ^ 2 := by
  have hd : fderiv ℝ (fun y => w y + t * ψ y) x = fderiv ℝ w x + t • fderiv ℝ ψ x := by
    rw [fderiv_fun_add hw (hψ.const_mul t), fderiv_const_mul hψ]
  have hg : ∇ (fun y => w y + t * ψ y) x = ∇ w x + t • ∇ ψ x := by
    simp only [gradient, hd, map_add, map_smul]
  rw [← norm_gradient, hg, norm_add_sq_real, norm_smul, real_inner_smul_right, norm_gradient,
    norm_gradient, Real.norm_eq_abs, mul_pow, sq_abs, real_inner_comm, inner_gradient_right]
  ring

lemma integral_add_three {μ : Measure (EuclideanSpace ℝ (Fin n))}
    {f g h : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hh : Integrable h μ) :
    ∫ x, (f x + g x + h x) ∂μ = ∫ x, f x ∂μ + ∫ x, g x ∂μ + ∫ x, h x ∂μ := by
  rw [integral_add (f := fun x => f x + g x) (hf.add hg) hh, integral_add hf hg]

lemma lipschitzWith_add_mul {w ψ : EuclideanSpace ℝ (Fin n) → ℝ} {L K : ℝ≥0}
    (hw : LipschitzWith L w) (hψ : LipschitzWith K ψ) (t : ℝ) :
    LipschitzWith (L + ‖t‖₊ * K) fun y => w y + t * ψ y :=
  LipschitzWith.of_dist_le_mul fun x y => by
    rw [Real.dist_eq, NNReal.coe_add, NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs]
    have h1 := hw.dist_le_mul x y
    have h2 := hψ.dist_le_mul x y
    rw [Real.dist_eq] at h1 h2
    calc |w x + t * ψ x - (w y + t * ψ y)| = |(w x - w y) + t * (ψ x - ψ y)| := by ring_nf
      _ ≤ |w x - w y| + |t| * |ψ x - ψ y| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ L * dist x y + |t| * (K * dist x y) := by gcongr
      _ = (L + |t| * K) * dist x y := by ring

/-- `Q(w + tψ) = Q(w) + 2t B(w,ψ) + t² Q(ψ)`. -/
lemma quadratic_expansion {w ψ : EuclideanSpace ℝ (Fin n) → ℝ} {L K : ℝ≥0}
    (hw : LipschitzWith L w) (hψ : LipschitzWith K ψ) (hw0 : w 0 = 0) (hψ0 : ψ 0 = 0) (t : ℝ) :
    dirichletEnergy (fun y => w y + t * ψ y) - gaussL2 (fun y => w y + t * ψ y) =
      (dirichletEnergy w - gaussL2 w) + 2 * t * gaussBilin w ψ +
        t ^ 2 * (dirichletEnergy ψ - gaussL2 ψ) := by
  have hac : gaussMeasure n ≪ volume := withDensity_absolutelyContinuous _ _
  have hD : dirichletEnergy (fun y => w y + t * ψ y) =
      dirichletEnergy w + 2 * t * ∫ x, fderiv ℝ w x (∇ ψ x) ∂gaussMeasure n +
        t ^ 2 * dirichletEnergy ψ := by
    unfold dirichletEnergy
    have e : ∀ᵐ x ∂gaussMeasure n, ‖fderiv ℝ (fun y => w y + t * ψ y) x‖ ^ 2 =
        ‖fderiv ℝ w x‖ ^ 2 + 2 * t * fderiv ℝ w x (∇ ψ x) + t ^ 2 * ‖fderiv ℝ ψ x‖ ^ 2 := by
      filter_upwards [hac.ae_le hw.ae_differentiableAt, hac.ae_le hψ.ae_differentiableAt]
        with x h1 h2
      exact norm_fderiv_add_smul_sq h1 h2 t
    rw [integral_congr_ae e]
    have i1 := integrable_norm_fderiv_sq hw
    have i2 := (integrable_fderiv_apply_gradient hw hψ).const_mul (2 * t)
    have i3 := (integrable_norm_fderiv_sq hψ).const_mul (t ^ 2)
    rw [integral_add_three i1 i2 i3, integral_const_mul, integral_const_mul]
  have hL : gaussL2 (fun y => w y + t * ψ y) =
      gaussL2 w + 2 * t * ∫ x, w x * ψ x ∂gaussMeasure n + t ^ 2 * gaussL2 ψ := by
    unfold gaussL2
    have i1 := integrable_sq_of_lipschitzWith hw hw0
    have i2 := integrable_sq_of_lipschitzWith hψ hψ0
    have i3 := integrable_mul_of_lipschitzWith hw hψ hw0 hψ0
    have e : ∀ x, (w x + t * ψ x) ^ 2 = (w x ^ 2 + (2 * t) * (w x * ψ x)) + t ^ 2 * ψ x ^ 2 :=
      fun x => by ring
    simp_rw [e]
    rw [integral_add_three i1 (i3.const_mul (2 * t)) (i2.const_mul (t ^ 2)), integral_const_mul,
      integral_const_mul]
  rw [hD, hL, gaussBilin]
  ring

/-- **First variation.** A minimizer is a weak solution: `B(w, ψ) = 0` for every one-homogeneous
Lipschitz `ψ` vanishing outside `{w > 0}`. -/
theorem gaussBilin_eq_zero (hn : 2 ≤ n) {w ψ : EuclideanSpace ℝ (Fin n) → ℝ} {L K : ℝ≥0}
    (hw : LipschitzWith L w) (hnn : ∀ x, 0 ≤ w x) (hhom : IsOneHomogeneous w)
    (hmin : dirichletEnergy w ≤ gaussL2 w)
    (hhalf : 2 * gaussMeasure n {x | 0 < w x} ≤ gaussMeasure n univ)
    (hψ : LipschitzWith K ψ) (hψhom : IsOneHomogeneous ψ) (hsupp : ∀ x, ψ x ≠ 0 → 0 < w x) :
    gaussBilin w ψ = 0 := by
  have hw0 := hhom.map_zero
  have hψ0 := hψhom.map_zero
  -- `Q(w + tψ) ≥ 0` for every `t`
  have hQ : ∀ t : ℝ, 0 ≤ dirichletEnergy (fun y => w y + t * ψ y) -
      gaussL2 (fun y => w y + t * ψ y) := by
    intro t
    have hL := lipschitzWith_add_mul hw hψ t
    have hh : IsOneHomogeneous fun y => w y + t * ψ y := fun x s hs => by
      change w (s • x) + t * ψ (s • x) = s * (w x + t * ψ x)
      rw [hhom x s hs, hψhom x s hs]; ring
    have hsub : {x | w x + t * ψ x ≠ 0} ⊆ {x | 0 < w x} := by
      intro x hx
      by_contra hw'
      have hwx : w x = 0 := le_antisymm (not_lt.1 hw') (hnn x)
      have hψx : ψ x = 0 := by by_contra h; exact hw' (hsupp x h)
      exact hx (by simp [hwx, hψx])
    have := gaussL2_le_dirichletEnergy_of_ne hn hL hh
      ((mul_le_mul_right (measure_mono hsub) 2).trans hhalf)
    linarith
  have h0 : dirichletEnergy w - gaussL2 w = 0 := by
    have := hQ 0; simp only [zero_mul, add_zero] at this; linarith
  have hexp := fun t => quadratic_expansion hw hψ hw0 hψ0 t
  set B := gaussBilin w ψ
  set C := dirichletEnergy ψ - gaussL2 ψ
  have key : ∀ t : ℝ, 0 ≤ 2 * t * B + t ^ 2 * C := fun t => by
    have := hQ t; rw [hexp t, h0] at this; linarith
  by_contra hB
  have hB2 : 0 < B ^ 2 := by positivity
  have h1 := key (-B / (|C| + 1))
  have hC : C ≤ |C| := le_abs_self C
  have hpos : 0 < |C| + 1 := by positivity
  have : 2 * (-B / (|C| + 1)) * B + (-B / (|C| + 1)) ^ 2 * C =
      B ^ 2 / (|C| + 1) * (C / (|C| + 1) - 2) := by field_simp; ring
  rw [this] at h1
  have h2 : C / (|C| + 1) - 2 < 0 := by
    rw [sub_neg, div_lt_iff₀ hpos]; linarith
  have := mul_neg_of_pos_of_neg (div_pos hB2 hpos) h2
  linarith

end Sperner
