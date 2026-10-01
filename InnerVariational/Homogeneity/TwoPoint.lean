/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Homogeneity.RayCalculus
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus

/-!
# Two-point homogeneity (Lemma 6.2)

This file proves Lemma 6.2 of D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff
measure, and compactness for non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78
(2025), no. 3, DOI 10.1002/cpa.22226; arXiv:2306.10131 (numbering of arXiv v2): if a Lipschitz
function `u` on `ℝⁿ` is almost homogeneous of degree `N₀` about `0` and of degree `Nₓ` about a
point `x ∈ B_1`, both in `L²` of the annulus `B_10 ∖ B_1`, then the degrees nearly agree and `u` is
almost invariant in the direction `x`:
`|N₀ - Nₓ|² ∫_{B_10∖B_1} u² ≤ C δ` and `∫_{B_9∖B_2} |∇u · x|² ≤ C δ`.

Throughout, `Nₚ` denotes the paper's upper bound `N₊` (`₊` cannot appear in a Lean identifier).

## Main results

* `InnerVariational.two_point_homogeneity`: the lemma in the shape of the paper, `∃ C > 0`.
* `InnerVariational.two_point_homogeneity_annulus`: the same with the explicit constants
  `twoPointConst₁ n Nₚ` (first conclusion) and `twoPointConst n Nₚ` (second conclusion).
* `InnerVariational.two_point_homogeneity_scaled`: centre `p`, second point `q`, `|q - p| < ρ`,
  annuli `B_{10ρ}(p) ∖ B_ρ(p)` and `B_{10ρ}(q) ∖ B_ρ(q)`, same constant.
* `InnerVariational.two_point_homogeneity_scaled_of_lipschitzOnWith`: the scaled version for `u`
  Lipschitz only on `B_{20ρ}(p)`.

## Deviations from the paper

* The ray estimate (6.19) and the comparison (6.20) of `∫ u²` over different radii, in the proof
  of Lemma 6.2, are carried out on annuli instead of spheres. This avoids polar coordinates
  entirely (see `Homogeneity/RayCalculus.lean`). The paper's (6.20) is replaced by
  `setIntegral_annulus_one_ten_le`: `∫_{B_10∖B_1} u² ≤ Q (∫_{B_8∖B_6} u² + δ)`.
* The hypotheses `x ≠ 0` and `N₊ > 1` are not used. They are kept in the paper-shaped statement
  `two_point_homogeneity` only.
-/

open MeasureTheory Metric Set Filter Bornology
open scoped NNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

/-! ### Constants (ledger)

With `a = Nₓ - N₀` and `E = e^{2Nₚ} ≥ e^{2|a|}`:

The steps refer to the proof of Lemma 6.2 in the paper.

* Step 1 (the first display of the proof): `∫_{B_9∖B_2} (∇u·x + a u)² ≤ 4δ`.
* Segment (6.18): `∫_{B_8∖B_3} (e^a u(y+x) - u(y))² ≤ 4Eδ`.
* Rays ((6.21), (6.22), on annuli): `∫_{B_4∖B_3} (2^{-N} u(2y) - u(y))² ≤ δ` about `0` and `x`.
* Four terms (the triangle inequality after (6.22)):
  `D² 2^{-n} ∫_{B_8∖B_6} u² ≤ 4(1 + 9E)δ`, `D = 2^{-Nₓ} - 2^{-N₀}`.
* Mean value (`|2^{-N_x} - 2^{-N_0}| ≥ c(N₊)|N_x - N_0|`): `c² (N₀ - Nₓ)² ≤ D²`,
  `c = log 2 · 2^{-Nₚ}` (`twoPointMVTConst`).
* Annuli ((6.20), on annuli): `∫_{B_10∖B_1} u² ≤ Q (∫_{B_8∖B_6} u² + δ)`,
  `Q = 20 + 9P`, `P = 2 (5/4)^n ((5/4)^{Nₚ})²` (`twoPointAnnulusConst`).
* Conclusion (6.16): `C₁ = Q (2ⁿ · 4(1 + 9E) / c² + Nₚ²)` (`twoPointConst₁`);
  (6.17): `C = 2 C₁ + 8` (`twoPointConst`).
-/

/-- The mean value constant `c(Nₚ) = log 2 · 2^{-Nₚ}`, so that
`|2^{-p} - 2^{-q}| ≥ c(Nₚ) |p - q|` for `p, q ≤ Nₚ`. -/
def twoPointMVTConst (Nₚ : ℝ) : ℝ := Real.log 2 * (2 : ℝ) ^ (-Nₚ)

/-- The constant `Q(n, Nₚ) = 20 + 18 (5/4)ⁿ ((5/4)^{Nₚ})²` of the annulus comparison
`∫_{B_10∖B_1} u² ≤ Q (∫_{B_8∖B_6} u² + δ)`. -/
def twoPointAnnulusConst (n : ℕ) (Nₚ : ℝ) : ℝ :=
  20 + 9 * (2 * (5 / 4 : ℝ) ^ n * ((5 / 4 : ℝ) ^ Nₚ) ^ 2)

/-- The constant of conclusion (6.16) of Lemma 6.2. -/
def twoPointConst₁ (n : ℕ) (Nₚ : ℝ) : ℝ :=
  twoPointAnnulusConst n Nₚ *
    (2 ^ n * (4 * (1 + 9 * Real.exp (2 * Nₚ))) / twoPointMVTConst Nₚ ^ 2 + Nₚ ^ 2)

/-- The constant `C(n, Nₚ)` of Lemma 6.2; it bounds both conclusions. -/
def twoPointConst (n : ℕ) (Nₚ : ℝ) : ℝ := 2 * twoPointConst₁ n Nₚ + 8

theorem twoPointMVTConst_pos (Nₚ : ℝ) : 0 < twoPointMVTConst Nₚ :=
  mul_pos (Real.log_pos one_lt_two) (Real.rpow_pos_of_pos two_pos _)

theorem twoPointAnnulusConst_pos (n : ℕ) (Nₚ : ℝ) : 0 < twoPointAnnulusConst n Nₚ := by
  unfold twoPointAnnulusConst; positivity

theorem twoPointConst₁_pos (n : ℕ) (Nₚ : ℝ) : 0 < twoPointConst₁ n Nₚ :=
  mul_pos (twoPointAnnulusConst_pos n Nₚ) (add_pos_of_pos_of_nonneg
    (div_pos (by positivity) (pow_pos (twoPointMVTConst_pos Nₚ) 2)) (sq_nonneg _))

theorem twoPointConst_pos (n : ℕ) (Nₚ : ℝ) : 0 < twoPointConst n Nₚ := by
  have := twoPointConst₁_pos n Nₚ
  unfold twoPointConst; linarith

theorem twoPointConst₁_le_twoPointConst (n : ℕ) (Nₚ : ℝ) :
    twoPointConst₁ n Nₚ ≤ twoPointConst n Nₚ := by
  have := twoPointConst₁_pos n Nₚ
  unfold twoPointConst; linarith

/-! ### Elementary inequalities -/

theorem sq_add_le_two_mul_add (a b : ℝ) : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  nlinarith [sq_nonneg (a - b)]

theorem sq_add_add_add_le (a b c d : ℝ) :
    (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c),
    sq_nonneg (b - d), sq_nonneg (c - d)]

/-- `‖f + g‖² ≤ 2 (‖f‖² + ‖g‖²)` in `L²(S)`. -/
theorem setIntegral_sq_add_le {S : Set (Rn n)} {f g : Rn n → ℝ}
    (hf : IntegrableOn (fun y => f y ^ 2) S) (hg : IntegrableOn (fun y => g y ^ 2) S) :
    ∫ y in S, (f y + g y) ^ 2 ≤ 2 * ((∫ y in S, f y ^ 2) + ∫ y in S, g y ^ 2) := by
  rw [← integral_add hf hg, ← integral_const_mul]
  exact integral_mono_of_nonneg (Eventually.of_forall fun y => sq_nonneg _)
    ((hf.add hg).const_mul 2) (Eventually.of_forall fun y => sq_add_le_two_mul_add _ _)

/-- `‖f₁ + f₂ + f₃ + f₄‖² ≤ 4 Σ ‖fᵢ‖²` in `L²(S)`. -/
theorem setIntegral_sq_add_add_add_le {S : Set (Rn n)} {f₁ f₂ f₃ f₄ : Rn n → ℝ}
    (h₁ : IntegrableOn (fun y => f₁ y ^ 2) S) (h₂ : IntegrableOn (fun y => f₂ y ^ 2) S)
    (h₃ : IntegrableOn (fun y => f₃ y ^ 2) S) (h₄ : IntegrableOn (fun y => f₄ y ^ 2) S) :
    ∫ y in S, (f₁ y + f₂ y + f₃ y + f₄ y) ^ 2 ≤
      4 * ((∫ y in S, f₁ y ^ 2) + (∫ y in S, f₂ y ^ 2) + (∫ y in S, f₃ y ^ 2) +
        ∫ y in S, f₄ y ^ 2) := by
  have h₁₂ : IntegrableOn (fun y => f₁ y ^ 2 + f₂ y ^ 2) S := h₁.add h₂
  have h₁₂₃ : IntegrableOn (fun y => f₁ y ^ 2 + f₂ y ^ 2 + f₃ y ^ 2) S := h₁₂.add h₃
  rw [← integral_add h₁ h₂, ← integral_add h₁₂ h₃, ← integral_add h₁₂₃ h₄,
    ← integral_const_mul]
  exact integral_mono_of_nonneg (Eventually.of_forall fun y => sq_nonneg _)
    ((h₁₂₃.add h₄).const_mul 4) (Eventually.of_forall fun y => sq_add_add_add_le _ _ _ _)

/-- *Mean value bound* (the last step of the proof of Lemma 6.2):
`c(Nₚ)² (p - q)² ≤ (2^{-q} - 2^{-p})²` for `p, q ≤ Nₚ`. -/
theorem twoPointMVTConst_sq_mul_le {Nₚ p q : ℝ} (hp : p ≤ Nₚ) (hq : q ≤ Nₚ) :
    twoPointMVTConst Nₚ ^ 2 * (p - q) ^ 2 ≤ ((2 : ℝ) ^ (-q) - (2 : ℝ) ^ (-p)) ^ 2 := by
  have key : ∀ p q : ℝ, p ≤ q → q ≤ Nₚ →
      twoPointMVTConst Nₚ * (q - p) ≤ (2 : ℝ) ^ (-p) - (2 : ℝ) ^ (-q) := by
    intro p q hpq hq
    simp only [twoPointMVTConst, Real.rpow_def_of_pos two_pos]
    set l := Real.log 2
    have hl : 0 < l := Real.log_pos one_lt_two
    have h1 : Real.exp (l * -p) = Real.exp (l * -q) * Real.exp (l * (q - p)) := by
      rw [← Real.exp_add]; congr 1; ring
    have h2 : l * (q - p) + 1 ≤ Real.exp (l * (q - p)) := Real.add_one_le_exp _
    have h3 : Real.exp (l * -Nₚ) ≤ Real.exp (l * -q) := Real.exp_le_exp.2 (by nlinarith)
    have h4 : 0 ≤ l * (q - p) := mul_nonneg hl.le (sub_nonneg.2 hpq)
    rw [h1]
    calc l * Real.exp (l * -Nₚ) * (q - p) = Real.exp (l * -Nₚ) * (l * (q - p)) := by ring
      _ ≤ Real.exp (l * -q) * (l * (q - p)) := mul_le_mul_of_nonneg_right h3 h4
      _ ≤ Real.exp (l * -q) * (Real.exp (l * (q - p)) - 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
      _ = _ := by ring
  have hc := (twoPointMVTConst_pos Nₚ).le
  rcases le_total p q with h | h
  · have := pow_le_pow_left₀ (mul_nonneg hc (sub_nonneg.2 h)) (key p q h hq) 2
    calc twoPointMVTConst Nₚ ^ 2 * (p - q) ^ 2 = (twoPointMVTConst Nₚ * (q - p)) ^ 2 := by ring
      _ ≤ _ := this
      _ = _ := by ring
  · have := pow_le_pow_left₀ (mul_nonneg hc (sub_nonneg.2 h)) (key q p h hp) 2
    calc twoPointMVTConst Nₚ ^ 2 * (p - q) ^ 2 = (twoPointMVTConst Nₚ * (p - q)) ^ 2 := by ring
      _ ≤ _ := this

/-! ### Rays: comparison of `∫ u²` over annuli -/

section Rays

variable {u : Rn n → ℝ} {L : ℝ≥0}

/-- If `1 ≤ a`, `1 ≤ T` and `T b ≤ 10`, the ray segments `[1, T] • y`, `y ∈ B_b ∖ B_a`, stay in
`B_10 ∖ B_1`. -/
theorem smul_mem_annulus_one_ten {T a b : ℝ} (hT : 1 ≤ T) (ha : 1 ≤ a) (hTb : T * b ≤ 10) :
    ∀ y ∈ (annulus a b : Set (Rn n)), ∀ t ∈ Icc 1 T, t • y ∈ (annulus 1 10 : Set (Rn n)) := by
  intro y hy t ht
  rw [mem_annulus] at hy ⊢
  have ht0 : 0 < t := by linarith [ht.1]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.2 ht.1) (norm_nonneg y), hy.1]
  · calc t * ‖y‖ ≤ T * ‖y‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
      _ < T * b := mul_lt_mul_of_pos_left hy.2 (by linarith)
      _ ≤ 10 := hTb

/-- Almost homogeneity on annuli: `∫_{B_b∖B_a} (T^{-N} u(Ty) - u(y))² ≤ (T-1)² δ`. -/
theorem setIntegral_annulus_sq_rpow_mul_sub_le (hu : LipschitzWith L u) {N T a b δ : ℝ}
    (hN : 0 ≤ N) (hT : 1 ≤ T) (ha : 1 ≤ a) (hTb : T * b ≤ 10)
    (H : ∫ z in annulus 1 10, (⟪gradient u z, z⟫ - N * u z) ^ 2 ≤ δ) :
    ∫ y in annulus a b, (T ^ (-N) * u (T • y) - u y) ^ 2 ≤ (T - 1) ^ 2 * δ :=
  (LipschitzWith.setIntegral_sq_rpow_mul_comp_smul_sub_le hu (by linarith) hT
    (measurableSet_annulus a b) (isBounded_annulus a b) (measurableSet_annulus 1 10)
    (isBounded_annulus 1 10) (smul_mem_annulus_one_ten hT ha hTb)).trans
    (mul_le_mul_of_nonneg_left H (sq_nonneg _))

/-- Inner annuli are controlled by outer ones:
`∫_{B_b∖B_a} u² ≤ 2 ∫_{B_{Tb}∖B_{Ta}} u² + 2(T-1)²δ`. -/
theorem setIntegral_annulus_sq_le_of_smul (hu : LipschitzWith L u) {N T a b δ : ℝ}
    (hN : 0 ≤ N) (hT : 1 ≤ T) (ha : 1 ≤ a) (hTb : T * b ≤ 10)
    (H : ∫ z in annulus 1 10, (⟪gradient u z, z⟫ - N * u z) ^ 2 ≤ δ) :
    ∫ y in annulus a b, u y ^ 2 ≤
      2 * (∫ y in annulus (T * a) (T * b), u y ^ 2) + 2 * ((T - 1) ^ 2 * δ) := by
  have hT0 : 0 < T := by linarith
  have hc := hu.continuous
  have hK := setIntegral_annulus_sq_rpow_mul_sub_le hu hN hT ha hTb H
  have hsplit := setIntegral_sq_add_le (S := annulus a b) (f := fun y => T ^ (-N) * u (T • y))
    (g := fun y => -(T ^ (-N) * u (T • y) - u y))
    (integrableOn_of_continuous (by fun_prop) (isBounded_annulus a b))
    (integrableOn_of_continuous (by fun_prop) (isBounded_annulus a b))
  have e1 : ∫ y in annulus a b, (T ^ (-N) * u (T • y) + -(T ^ (-N) * u (T • y) - u y)) ^ 2 =
      ∫ y in annulus a b, u y ^ 2 := integral_congr_ae (Eventually.of_forall fun y => by ring)
  have e2 : ∫ y in annulus a b, (T ^ (-N) * u (T • y)) ^ 2 =
      (T ^ (-N)) ^ 2 * ((T ^ n)⁻¹ * ∫ y in annulus (T * a) (T * b), u y ^ 2) := by
    simp_rw [mul_pow]
    rw [integral_const_mul, setIntegral_annulus_comp_smul (fun y => u y ^ 2) hT0]
  have e3 : ∫ y in annulus a b, (-(T ^ (-N) * u (T • y) - u y)) ^ 2 =
      ∫ y in annulus a b, (T ^ (-N) * u (T • y) - u y) ^ 2 :=
    integral_congr_ae (Eventually.of_forall fun y => by simp only [neg_sq])
  rw [e1, e2, e3] at hsplit
  have hI0 : 0 ≤ ∫ y in annulus (T * a) (T * b), u y ^ 2 :=
    setIntegral_nonneg (measurableSet_annulus _ _) fun _ _ => sq_nonneg _
  have h1 : (T ^ (-N)) ^ 2 ≤ 1 :=
    pow_le_one₀ (Real.rpow_nonneg hT0.le _) (Real.rpow_le_one_of_one_le_of_nonpos hT (by linarith))
  have h2 : (T ^ n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hT)
  have h3 : (T ^ (-N)) ^ 2 * ((T ^ n)⁻¹ * ∫ y in annulus (T * a) (T * b), u y ^ 2) ≤
      ∫ y in annulus (T * a) (T * b), u y ^ 2 := by
    calc _ ≤ 1 * (1 * ∫ y in annulus (T * a) (T * b), u y ^ 2) := by gcongr
      _ = _ := by ring
  calc ∫ y in annulus a b, u y ^ 2 ≤ 2 * ((T ^ (-N)) ^ 2 *
        ((T ^ n)⁻¹ * ∫ y in annulus (T * a) (T * b), u y ^ 2) +
        ∫ y in annulus a b, (T ^ (-N) * u (T • y) - u y) ^ 2) := hsplit
    _ ≤ 2 * ((∫ y in annulus (T * a) (T * b), u y ^ 2) + (T - 1) ^ 2 * δ) := by gcongr
    _ = _ := by ring

/-- Outer annuli are controlled by inner ones:
`∫_{B_{Tb}∖B_{Ta}} u² ≤ 2 Tⁿ (T^N)² (∫_{B_b∖B_a} u² + (T-1)²δ)`. -/
theorem setIntegral_annulus_smul_sq_le (hu : LipschitzWith L u) {N T a b δ : ℝ}
    (hN : 0 ≤ N) (hT : 1 ≤ T) (ha : 1 ≤ a) (hTb : T * b ≤ 10)
    (H : ∫ z in annulus 1 10, (⟪gradient u z, z⟫ - N * u z) ^ 2 ≤ δ) :
    ∫ y in annulus (T * a) (T * b), u y ^ 2 ≤
      2 * T ^ n * (T ^ N) ^ 2 * ((∫ y in annulus a b, u y ^ 2) + (T - 1) ^ 2 * δ) := by
  have hT0 : 0 < T := by linarith
  have hc := hu.continuous
  have hK := setIntegral_annulus_sq_rpow_mul_sub_le hu hN hT ha hTb H
  have hsplit := setIntegral_sq_add_le (S := annulus a b)
    (f := fun y => T ^ N * (T ^ (-N) * u (T • y) - u y)) (g := fun y => T ^ N * u y)
    (integrableOn_of_continuous (by fun_prop) (isBounded_annulus a b))
    (integrableOn_of_continuous (by fun_prop) (isBounded_annulus a b))
  have hTN : T ^ N * T ^ (-N) = 1 := by
    rw [← Real.rpow_add hT0, add_neg_cancel, Real.rpow_zero]
  have e1 : ∫ y in annulus a b, (T ^ N * (T ^ (-N) * u (T • y) - u y) + T ^ N * u y) ^ 2 =
      ∫ y in annulus a b, u (T • y) ^ 2 := integral_congr_ae (Eventually.of_forall fun y => by
    dsimp only
    rw [← mul_add, sub_add_cancel, ← mul_assoc, hTN, one_mul])
  have e2 : ∫ y in annulus a b, (T ^ N * (T ^ (-N) * u (T • y) - u y)) ^ 2 =
      (T ^ N) ^ 2 * ∫ y in annulus a b, (T ^ (-N) * u (T • y) - u y) ^ 2 := by
    simp_rw [mul_pow (T ^ N)]
    rw [integral_const_mul]
  have e3 : ∫ y in annulus a b, (T ^ N * u y) ^ 2 =
      (T ^ N) ^ 2 * ∫ y in annulus a b, u y ^ 2 := by
    simp_rw [mul_pow]
    rw [integral_const_mul]
  rw [e1, e2, e3, setIntegral_annulus_comp_smul (fun y => u y ^ 2) hT0] at hsplit
  have hTn : 0 < T ^ n := by positivity
  have hsplit' := mul_le_mul_of_nonneg_left hsplit hTn.le
  rw [← mul_assoc, mul_inv_cancel₀ hTn.ne', one_mul] at hsplit'
  refine hsplit'.trans ?_
  calc T ^ n * (2 * ((T ^ N) ^ 2 * (∫ y in annulus a b, (T ^ (-N) * u (T • y) - u y) ^ 2) +
        (T ^ N) ^ 2 * ∫ y in annulus a b, u y ^ 2)) =
        2 * T ^ n * ((T ^ N) ^ 2 * ∫ y in annulus a b, (T ^ (-N) * u (T • y) - u y) ^ 2) +
        2 * T ^ n * ((T ^ N) ^ 2 * ∫ y in annulus a b, u y ^ 2) := by ring
    _ ≤ 2 * T ^ n * ((T ^ N) ^ 2 * ((T - 1) ^ 2 * δ)) +
        2 * T ^ n * ((T ^ N) ^ 2 * ∫ y in annulus a b, u y ^ 2) := by gcongr
    _ = _ := by ring

/-- *Annulus comparison* (the paper's (6.20), integrated over annuli instead of spheres):
`∫_{B_10∖B_1} u² ≤ Q (∫_{B_8∖B_6} u² + δ)`. -/
theorem setIntegral_annulus_one_ten_le (hu : LipschitzWith L u) {N Nₚ δ : ℝ} (hN : 0 ≤ N)
    (hNN : N ≤ Nₚ) (hδ : 0 ≤ δ)
    (H : ∫ z in annulus 1 10, (⟪gradient u z, z⟫ - N * u z) ^ 2 ≤ δ) :
    ∫ y in annulus 1 10, u y ^ 2 ≤
      twoPointAnnulusConst n Nₚ * ((∫ y in annulus 6 8, u y ^ 2) + δ) := by
  have hc : Continuous fun y : Rn n => u y ^ 2 := by have := hu.continuous; fun_prop
  have hc0 : ∀ y : Rn n, 0 ≤ u y ^ 2 := fun y => sq_nonneg _
  have hint : ∀ a b : ℝ, IntegrableOn (fun y : Rn n => u y ^ 2) (annulus a b) :=
    fun a b => integrableOn_of_continuous hc (isBounded_annulus a b)
  obtain ⟨I, hI⟩ : ∃ I : ℝ → ℝ → ℝ, I = fun a b => ∫ y in annulus a b, u y ^ 2 := ⟨_, rfl⟩
  have hJ : 0 ≤ I 6 8 := by
    subst hI; exact setIntegral_nonneg (measurableSet_annulus _ _) fun _ _ => sq_nonneg _
  -- splittings
  have s1 : I 1 10 = I 1 3 + I 3 10 := by
    subst hI; exact setIntegral_annulus_eq_add (by norm_num) (by norm_num) (hint 1 10)
  have s2 : I 3 10 = I 3 4 + I 4 10 := by
    subst hI; exact setIntegral_annulus_eq_add (by norm_num) (by norm_num) (hint 3 10)
  have s3 : I 4 10 = I 4 6 + I 6 10 := by
    subst hI; exact setIntegral_annulus_eq_add (by norm_num) (by norm_num) (hint 4 10)
  have s4 : I 6 10 = I 6 8 + I 8 10 := by
    subst hI; exact setIntegral_annulus_eq_add (by norm_num) (by norm_num) (hint 6 10)
  -- monotonicity
  have m1 : I 8 10 ≤ I (15 / 2) 10 := by
    subst hI; exact setIntegral_annulus_mono hc hc0 (by norm_num) le_rfl
  have m2 : I 6 9 ≤ I 6 10 := by
    subst hI; exact setIntegral_annulus_mono hc hc0 le_rfl (by norm_num)
  have m3 : I (10 / 3) 10 ≤ I 3 10 := by
    subst hI; exact setIntegral_annulus_mono hc hc0 (by norm_num) le_rfl
  -- rays
  have r1 : I (15 / 2) 10 ≤ 2 * (5 / 4 : ℝ) ^ n * ((5 / 4 : ℝ) ^ N) ^ 2 * (I 6 8 + 1 / 16 * δ) := by
    subst hI
    have := setIntegral_annulus_smul_sq_le hu hN (T := 5 / 4) (a := 6) (b := 8) (δ := δ)
      (by norm_num) (by norm_num) (by norm_num) H
    rwa [show (5 / 4 : ℝ) * 6 = 15 / 2 by norm_num, show (5 / 4 : ℝ) * 8 = 10 by norm_num,
      show ((5 / 4 : ℝ) - 1) ^ 2 = 1 / 16 by norm_num] at this
  have r2 : I 4 6 ≤ 2 * I 6 9 + 2 * (1 / 4 * δ) := by
    subst hI
    have := setIntegral_annulus_sq_le_of_smul hu hN (T := 3 / 2) (a := 4) (b := 6) (δ := δ)
      (by norm_num) (by norm_num) (by norm_num) H
    rwa [show (3 / 2 : ℝ) * 4 = 6 by norm_num, show (3 / 2 : ℝ) * 6 = 9 by norm_num,
      show ((3 / 2 : ℝ) - 1) ^ 2 = 1 / 4 by norm_num] at this
  have r3 : I 3 4 ≤ 2 * I 6 8 + 2 * (1 * δ) := by
    subst hI
    have := setIntegral_annulus_sq_le_of_smul hu hN (T := 2) (a := 3) (b := 4) (δ := δ)
      (by norm_num) (by norm_num) (by norm_num) H
    rwa [show (2 : ℝ) * 3 = 6 by norm_num, show (2 : ℝ) * 4 = 8 by norm_num,
      show ((2 : ℝ) - 1) ^ 2 = 1 by norm_num] at this
  have r4 : I 1 3 ≤ 2 * I (10 / 3) 10 + 2 * (49 / 9 * δ) := by
    subst hI
    have := setIntegral_annulus_sq_le_of_smul hu hN (T := 10 / 3) (a := 1) (b := 3) (δ := δ)
      (by norm_num) (by norm_num) (by norm_num) H
    rwa [show (10 / 3 : ℝ) * 1 = 10 / 3 by norm_num, show (10 / 3 : ℝ) * 3 = 10 by norm_num,
      show ((10 / 3 : ℝ) - 1) ^ 2 = 49 / 9 by norm_num] at this
  set P := 2 * (5 / 4 : ℝ) ^ n * ((5 / 4 : ℝ) ^ Nₚ) ^ 2 with hP
  have hP0 : 0 ≤ P := by positivity
  have hX : 2 * (5 / 4 : ℝ) ^ n * ((5 / 4 : ℝ) ^ N) ^ 2 ≤ P := by
    have : (5 / 4 : ℝ) ^ N ≤ (5 / 4 : ℝ) ^ Nₚ :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hNN
    have h0 : 0 ≤ (5 / 4 : ℝ) ^ N := by positivity
    rw [hP]; gcongr
  have r1' : I (15 / 2) 10 ≤ P * I 6 8 + P * δ / 16 := by
    refine r1.trans ?_
    calc 2 * (5 / 4 : ℝ) ^ n * ((5 / 4 : ℝ) ^ N) ^ 2 * (I 6 8 + 1 / 16 * δ) ≤
          P * (I 6 8 + 1 / 16 * δ) := mul_le_mul_of_nonneg_right hX (by positivity)
      _ = P * I 6 8 + P * δ / 16 := by ring
  have hexp : twoPointAnnulusConst n Nₚ * (I 6 8 + δ) =
      20 * I 6 8 + 20 * δ + 9 * (P * I 6 8) + 9 * (P * δ) := by
    rw [twoPointAnnulusConst, hP]; ring
  have key : I 1 10 ≤ twoPointAnnulusConst n Nₚ * (I 6 8 + δ) := by
    rw [hexp]
    linarith [mul_nonneg hP0 hδ, mul_nonneg hP0 hJ]
  subst hI
  exact key

end Rays

/-! ### The proof of Lemma 6.2 -/

section Main

variable {u : Rn n → ℝ} {L : ℝ≥0}

/-- Step 1 of the proof of Lemma 6.2: writing `x = y - (y - x)`,
`∫_{B_9∖B_2} (⟪∇u, x⟫ + (Nₓ - N₀) u)² ≤ 4δ`. -/
theorem setIntegral_sq_inner_gradient_add_le (hu : LipschitzWith L u) {x : Rn n}
    (hx : ‖x‖ < 1) {N₀ Nₓ δ : ℝ}
    (H₀ : ∫ y in annulus 1 10, (⟪gradient u y, y⟫ - N₀ * u y) ^ 2 ≤ δ)
    (Hₓ : ∫ y in annulus 1 10, (⟪gradient u (x + y), y⟫ - Nₓ * u (x + y)) ^ 2 ≤ δ) :
    ∫ y in annulus 2 9, (⟪gradient u y, x⟫ + (Nₓ - N₀) * u y) ^ 2 ≤ 4 * δ := by
  have hS := measurableSet_annulus (n := n) 2 9
  have hSb := isBounded_annulus (n := n) 2 9
  have hsub : (annulus 2 9 : Set (Rn n)) ⊆ annulus 1 10 :=
    annulus_subset_annulus (by norm_num) (by norm_num)
  have hf : IntegrableOn (fun y => (⟪gradient u y, y⟫ - N₀ * u y) ^ 2) (annulus 1 10) :=
    LipschitzWith.integrableOn_sq_inner_gradient_sub_mul hu (measurableSet_annulus 1 10)
      (isBounded_annulus 1 10) (p := fun y => y) continuous_id' N₀
  have hg : IntegrableOn (fun y => (⟪gradient u y, y + -x⟫ - Nₓ * u y) ^ 2) (annulus 2 9) :=
    LipschitzWith.integrableOn_sq_inner_gradient_sub_mul hu hS hSb (p := fun y => y + -x)
      (by fun_prop) Nₓ
  have hgx : IntegrableOn (fun z => (⟪gradient u (x + z), z⟫ - Nₓ * u (x + z)) ^ 2)
      (annulus 1 10) := by
    have := LipschitzWith.integrableOn_sq_inner_gradient_sub_mul
      (LipschitzWith.comp_const_add hu x) (measurableSet_annulus 1 10) (isBounded_annulus 1 10)
      (p := fun y => y) continuous_id' Nₓ
    simpa only [gradient_comp_add_left] using this
  have hmaps : ∀ y ∈ (annulus 2 9 : Set (Rn n)), y + -x ∈ (annulus 1 10 : Set (Rn n)) := by
    intro y hy
    rw [mem_annulus] at hy ⊢
    rw [← sub_eq_add_neg]
    have h1 := norm_sub_norm_le y x
    have h2 := norm_sub_le y x
    constructor <;> linarith [hy.1, hy.2]
  have hg_le : ∫ y in annulus 2 9, (⟪gradient u y, y + -x⟫ - Nₓ * u y) ^ 2 ≤ δ := by
    have h := setIntegral_comp_add_le
      (f := fun z => (⟪gradient u (x + z), z⟫ - Nₓ * u (x + z)) ^ 2)
      (fun _ => sq_nonneg _) hS (measurableSet_annulus 1 10) hgx (-x) hmaps
    have e : ∀ y : Rn n, x + (y + -x) = y := fun y => by abel
    simp only [e] at h
    exact h.trans Hₓ
  have hf_le : ∫ y in annulus 2 9, (⟪gradient u y, y⟫ - N₀ * u y) ^ 2 ≤ δ :=
    (setIntegral_mono_set hf (Eventually.of_forall fun _ => sq_nonneg _)
      hsub.eventuallyLE).trans H₀
  have hsplit := setIntegral_sq_add_le (S := annulus 2 9)
    (f := fun y => ⟪gradient u y, y⟫ - N₀ * u y)
    (g := fun y => -(⟪gradient u y, y + -x⟫ - Nₓ * u y)) (hf.mono_set hsub)
    (by simpa only [neg_sq] using hg)
  have e1 : ∫ y in annulus 2 9, (⟪gradient u y, x⟫ + (Nₓ - N₀) * u y) ^ 2 =
      ∫ y in annulus 2 9,
        ((⟪gradient u y, y⟫ - N₀ * u y) + -(⟪gradient u y, y + -x⟫ - Nₓ * u y)) ^ 2 :=
    integral_congr_ae (Eventually.of_forall fun y => by
      dsimp only
      rw [inner_add_right, inner_neg_right]
      ring)
  have e2 : ∫ y in annulus 2 9, (-(⟪gradient u y, y + -x⟫ - Nₓ * u y)) ^ 2 =
      ∫ y in annulus 2 9, (⟪gradient u y, y + -x⟫ - Nₓ * u y) ^ 2 :=
    integral_congr_ae (Eventually.of_forall fun y => neg_sq _)
  rw [e1]
  rw [e2] at hsplit
  linarith

/-- The four-term estimate of the proof of Lemma 6.2 (from (6.18), (6.21), (6.22) and the
triangle inequality):
`(2^{-Nₓ} - 2^{-N₀})² ∫_{B_8∖B_6} u² ≤ 2ⁿ · 4 (1 + 9 e^{2Nₚ}) δ`. -/
theorem sq_rpow_sub_mul_setIntegral_annulus_le (hu : LipschitzWith L u) {x : Rn n}
    (hx : ‖x‖ < 1) {Nₚ N₀ Nₓ δ : ℝ} (hN₀ : N₀ ∈ Icc 1 Nₚ) (hNₓ : Nₓ ∈ Icc 1 Nₚ)
    (H₀ : ∫ y in annulus 1 10, (⟪gradient u y, y⟫ - N₀ * u y) ^ 2 ≤ δ)
    (Hₓ : ∫ y in annulus 1 10, (⟪gradient u (x + y), y⟫ - Nₓ * u (x + y)) ^ 2 ≤ δ) :
    ((2 : ℝ) ^ (-Nₓ) - (2 : ℝ) ^ (-N₀)) ^ 2 * ∫ y in annulus 6 8, u y ^ 2 ≤
      2 ^ n * (4 * (1 + 9 * Real.exp (2 * Nₚ))) * δ := by
  have hc := hu.continuous
  have hδ : 0 ≤ δ :=
    (setIntegral_nonneg (measurableSet_annulus 1 10) fun _ _ => sq_nonneg _).trans H₀
  set a := Nₓ - N₀ with ha_def
  set E := Real.exp (2 * Nₚ) with hE_def
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have ha : |a| ≤ Nₚ := abs_le.2 ⟨by linarith [hN₀.1, hN₀.2, hNₓ.1, hNₓ.2],
    by linarith [hN₀.1, hN₀.2, hNₓ.1, hNₓ.2]⟩
  have hEa : Real.exp (2 * |a|) ≤ E := Real.exp_le_exp.2 (by linarith)
  have hA2 : Real.exp a ^ 2 ≤ E := by
    rw [← Real.exp_nat_mul]
    exact Real.exp_le_exp.2 (by push_cast; linarith [le_abs_self a])
  -- the translate `ux = u (x + ·)`
  obtain ⟨ux, hux⟩ : ∃ f : Rn n → ℝ, f = fun z => u (x + z) := ⟨_, rfl⟩
  have hux_apply : ∀ z, ux z = u (x + z) := fun z => by rw [hux]
  have huxL : LipschitzWith L ux := by rw [hux]; exact LipschitzWith.comp_const_add hu x
  have hcx := huxL.continuous
  have Hₓ' : ∫ z in annulus 1 10, (⟪gradient ux z, z⟫ - Nₓ * ux z) ^ 2 ≤ δ := by
    subst hux; simpa only [gradient_comp_add_left] using Hₓ
  -- step 1 and the segment estimate (6.18)
  have hw := setIntegral_sq_inner_gradient_add_le hu hx H₀ Hₓ
  have hseg : ∫ y in annulus 3 8, (Real.exp a * u (y + x) - u y) ^ 2 ≤ E * (4 * δ) := by
    refine (LipschitzWith.setIntegral_sq_exp_mul_comp_add_sub_le hu a x
      (measurableSet_annulus 3 8) (isBounded_annulus 3 8) (measurableSet_annulus 2 9)
      (isBounded_annulus 2 9) ?_).trans ?_
    · intro y hy t ht
      rw [mem_annulus] at hy ⊢
      have h1 : ‖t • x‖ ≤ ‖x‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
        exact mul_le_of_le_one_left (norm_nonneg _) ht.2
      have h2 := norm_add_le y (t • x)
      have h3 := norm_sub_norm_le y (-(t • x))
      rw [norm_neg, sub_neg_eq_add] at h3
      constructor <;> linarith [hy.1, hy.2]
    · exact mul_le_mul hEa hw
        (setIntegral_nonneg (measurableSet_annulus 2 9) fun _ _ => sq_nonneg _) hE0
  -- rays ((6.19), integrated over annuli as in (6.21) and (6.22))
  have hray₀ : ∫ y in annulus 3 4, ((2 : ℝ) ^ (-N₀) * u ((2 : ℝ) • y) - u y) ^ 2 ≤ δ := by
    have := setIntegral_annulus_sq_rpow_mul_sub_le hu (T := 2) (a := 3) (b := 4)
      (by linarith [hN₀.1]) one_le_two (by norm_num) (by norm_num) H₀
    rwa [show ((2 : ℝ) - 1) ^ 2 = 1 by norm_num, one_mul] at this
  have hrayₓ : ∫ y in annulus 3 4, ((2 : ℝ) ^ (-Nₓ) * ux ((2 : ℝ) • y) - ux y) ^ 2 ≤ δ := by
    have := setIntegral_annulus_sq_rpow_mul_sub_le huxL (T := 2) (a := 3) (b := 4)
      (by linarith [hNₓ.1]) one_le_two (by norm_num) (by norm_num) Hₓ'
    rwa [show ((2 : ℝ) - 1) ^ 2 = 1 by norm_num, one_mul] at this
  -- the fourth term, by scaling `y ↦ 2y`
  have hP₄ : ∫ y in annulus 3 4,
      (Real.exp a * u ((2 : ℝ) • y + x) - u ((2 : ℝ) • y)) ^ 2 ≤ E * (4 * δ) := by
    rw [setIntegral_annulus_comp_smul (fun z => (Real.exp a * u (z + x) - u z) ^ 2) two_pos]
    have hmono := setIntegral_annulus_mono (f := fun z => (Real.exp a * u (z + x) - u z) ^ 2)
      (by fun_prop) (fun _ => sq_nonneg _) (a := 3) (b := 8) (a' := 2 * 3) (b' := 2 * 4)
      (by norm_num) (by norm_num)
    have h2n : ((2 : ℝ) ^ n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ one_le_two)
    have h0 : 0 ≤ ∫ z in annulus (2 * 3) (2 * 4), (Real.exp a * u (z + x) - u z) ^ 2 :=
      setIntegral_nonneg (measurableSet_annulus _ _) fun _ _ => sq_nonneg _
    calc _ ≤ 1 * ∫ z in annulus (2 * 3) (2 * 4), (Real.exp a * u (z + x) - u z) ^ 2 :=
          mul_le_mul_of_nonneg_right h2n h0
      _ ≤ E * (4 * δ) := by rw [one_mul]; exact hmono.trans hseg
  -- the four-term identity
  have hid : ∀ y : Rn n, ((2 : ℝ) ^ (-Nₓ) - (2 : ℝ) ^ (-N₀)) * u ((2 : ℝ) • y) =
      -((2 : ℝ) ^ (-N₀) * u ((2 : ℝ) • y) - u y) + (Real.exp a * u (y + x) - u y) +
        Real.exp a * ((2 : ℝ) ^ (-Nₓ) * ux ((2 : ℝ) • y) - ux y) +
        -(2 : ℝ) ^ (-Nₓ) * (Real.exp a * u ((2 : ℝ) • y + x) - u ((2 : ℝ) • y)) := by
    intro y
    rw [hux_apply, hux_apply, add_comm x ((2 : ℝ) • y), add_comm x y]
    ring
  have hsplit := setIntegral_sq_add_add_add_le (S := annulus 3 4)
    (f₁ := fun y => -((2 : ℝ) ^ (-N₀) * u ((2 : ℝ) • y) - u y))
    (f₂ := fun y => Real.exp a * u (y + x) - u y)
    (f₃ := fun y => Real.exp a * ((2 : ℝ) ^ (-Nₓ) * ux ((2 : ℝ) • y) - ux y))
    (f₄ := fun y => -(2 : ℝ) ^ (-Nₓ) * (Real.exp a * u ((2 : ℝ) • y + x) - u ((2 : ℝ) • y)))
    (integrableOn_of_continuous (by fun_prop) (isBounded_annulus 3 4))
    (integrableOn_of_continuous (by fun_prop) (isBounded_annulus 3 4))
    (integrableOn_of_continuous (by fun_prop) (isBounded_annulus 3 4))
    (integrableOn_of_continuous (by fun_prop) (isBounded_annulus 3 4))
  set D := (2 : ℝ) ^ (-Nₓ) - (2 : ℝ) ^ (-N₀) with hD
  have e0 : ∫ y in annulus 3 4, (-((2 : ℝ) ^ (-N₀) * u ((2 : ℝ) • y) - u y) +
      (Real.exp a * u (y + x) - u y) +
      Real.exp a * ((2 : ℝ) ^ (-Nₓ) * ux ((2 : ℝ) • y) - ux y) +
      -(2 : ℝ) ^ (-Nₓ) * (Real.exp a * u ((2 : ℝ) • y + x) - u ((2 : ℝ) • y))) ^ 2 =
      D ^ 2 * ((2 ^ n)⁻¹ * ∫ y in annulus 6 8, u y ^ 2) := by
    rw [← show (2 : ℝ) * 3 = 6 by norm_num, ← show (2 : ℝ) * 4 = 8 by norm_num,
      ← setIntegral_annulus_comp_smul (fun y => u y ^ 2) two_pos, ← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun y => by
      dsimp only
      rw [← hid y, mul_pow])
  have e1 : ∫ y in annulus 3 4, (-((2 : ℝ) ^ (-N₀) * u ((2 : ℝ) • y) - u y)) ^ 2 =
      ∫ y in annulus 3 4, ((2 : ℝ) ^ (-N₀) * u ((2 : ℝ) • y) - u y) ^ 2 :=
    integral_congr_ae (Eventually.of_forall fun y => neg_sq _)
  have e3 : ∫ y in annulus 3 4, (Real.exp a * ((2 : ℝ) ^ (-Nₓ) * ux ((2 : ℝ) • y) - ux y)) ^ 2 =
      Real.exp a ^ 2 * ∫ y in annulus 3 4, ((2 : ℝ) ^ (-Nₓ) * ux ((2 : ℝ) • y) - ux y) ^ 2 := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun y => mul_pow _ _ _)
  have e4 : ∫ y in annulus 3 4,
      (-(2 : ℝ) ^ (-Nₓ) * (Real.exp a * u ((2 : ℝ) • y + x) - u ((2 : ℝ) • y))) ^ 2 =
      ((2 : ℝ) ^ (-Nₓ)) ^ 2 *
        ∫ y in annulus 3 4, (Real.exp a * u ((2 : ℝ) • y + x) - u ((2 : ℝ) • y)) ^ 2 := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun y => by
      dsimp only
      rw [mul_pow, neg_sq])
  rw [e0, e1, e3, e4] at hsplit
  have hm₂ : ∫ y in annulus 3 4, (Real.exp a * u (y + x) - u y) ^ 2 ≤
      ∫ y in annulus 3 8, (Real.exp a * u (y + x) - u y) ^ 2 :=
    setIntegral_annulus_mono (by fun_prop) (fun _ => sq_nonneg _) le_rfl (by norm_num)
  have h2N : ((2 : ℝ) ^ (-Nₓ)) ^ 2 ≤ 1 :=
    pow_le_one₀ (Real.rpow_nonneg zero_le_two _)
      (Real.rpow_le_one_of_one_le_of_nonpos one_le_two (by linarith [hNₓ.1]))
  have hP₃ : Real.exp a ^ 2 *
      ∫ y in annulus 3 4, ((2 : ℝ) ^ (-Nₓ) * ux ((2 : ℝ) • y) - ux y) ^ 2 ≤ E * δ :=
    mul_le_mul hA2 hrayₓ (setIntegral_nonneg (measurableSet_annulus _ _)
      fun _ _ => sq_nonneg _) hE0
  have hP₄' : ((2 : ℝ) ^ (-Nₓ)) ^ 2 *
      ∫ y in annulus 3 4, (Real.exp a * u ((2 : ℝ) • y + x) - u ((2 : ℝ) • y)) ^ 2 ≤
      1 * (E * (4 * δ)) :=
    mul_le_mul h2N hP₄ (setIntegral_nonneg (measurableSet_annulus _ _)
      fun _ _ => sq_nonneg _) zero_le_one
  have key : D ^ 2 * ((2 ^ n)⁻¹ * ∫ y in annulus 6 8, u y ^ 2) ≤
      4 * (1 + 9 * E) * δ := by
    refine hsplit.trans ?_
    linarith [hray₀, hm₂.trans hseg, hP₃, hP₄']
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  calc D ^ 2 * ∫ y in annulus 6 8, u y ^ 2 =
      2 ^ n * (D ^ 2 * ((2 ^ n)⁻¹ * ∫ y in annulus 6 8, u y ^ 2)) := by
        linear_combination (D ^ 2 * ∫ y in annulus 6 8, u y ^ 2) *
          (mul_inv_cancel₀ h2n.ne').symm
    _ ≤ 2 ^ n * (4 * (1 + 9 * E) * δ) := by gcongr
    _ = 2 ^ n * (4 * (1 + 9 * E)) * δ := by ring

/-- **Lemma 6.2**, unit scale, with explicit constants and
annuli written as `annulus a b = B_b ∖ B_a`. The hypothesis `x ≠ 0` of the paper is not needed. -/
theorem two_point_homogeneity_annulus (hu : LipschitzWith L u) {x : Rn n} (hx : ‖x‖ < 1)
    {Nₚ N₀ Nₓ δ : ℝ} (hN₀ : N₀ ∈ Icc 1 Nₚ) (hNₓ : Nₓ ∈ Icc 1 Nₚ)
    (H₀ : ∫ y in annulus 1 10, (⟪gradient u y, y⟫ - N₀ * u y) ^ 2 ≤ δ)
    (Hₓ : ∫ y in annulus 1 10, (⟪gradient u (x + y), y⟫ - Nₓ * u (x + y)) ^ 2 ≤ δ) :
    (N₀ - Nₓ) ^ 2 * ∫ y in annulus 1 10, u y ^ 2 ≤ twoPointConst₁ n Nₚ * δ ∧
      ∫ y in annulus 2 9, ⟪gradient u y, x⟫ ^ 2 ≤ twoPointConst n Nₚ * δ := by
  have hc := hu.continuous
  have hδ : 0 ≤ δ :=
    (setIntegral_nonneg (measurableSet_annulus 1 10) fun _ _ => sq_nonneg _).trans H₀
  have h4 := sq_rpow_sub_mul_setIntegral_annulus_le hu hx hN₀ hNₓ H₀ Hₓ
  have hmvt := twoPointMVTConst_sq_mul_le (Nₚ := Nₚ) (p := N₀) (q := Nₓ) hN₀.2 hNₓ.2
  have hcpos := twoPointMVTConst_pos Nₚ
  have hJ0 : 0 ≤ ∫ y in annulus 6 8, u y ^ 2 :=
    setIntegral_nonneg (measurableSet_annulus _ _) fun _ _ => sq_nonneg _
  have hJ : (N₀ - Nₓ) ^ 2 * ∫ y in annulus 6 8, u y ^ 2 ≤
      2 ^ n * (4 * (1 + 9 * Real.exp (2 * Nₚ))) * δ / twoPointMVTConst Nₚ ^ 2 := by
    rw [le_div_iff₀ (pow_pos hcpos 2)]
    calc (N₀ - Nₓ) ^ 2 * (∫ y in annulus 6 8, u y ^ 2) * twoPointMVTConst Nₚ ^ 2 =
        (twoPointMVTConst Nₚ ^ 2 * (N₀ - Nₓ) ^ 2) * ∫ y in annulus 6 8, u y ^ 2 := by ring
      _ ≤ ((2 : ℝ) ^ (-Nₓ) - (2 : ℝ) ^ (-N₀)) ^ 2 * ∫ y in annulus 6 8, u y ^ 2 :=
        mul_le_mul_of_nonneg_right hmvt hJ0
      _ ≤ _ := h4
  have hann := setIntegral_annulus_one_ten_le hu (N := N₀) (Nₚ := Nₚ) (by linarith [hN₀.1])
    hN₀.2 hδ H₀
  have hd2 : (N₀ - Nₓ) ^ 2 ≤ Nₚ ^ 2 :=
    sq_le_sq' (by linarith [hN₀.1, hN₀.2, hNₓ.1, hNₓ.2]) (by linarith [hN₀.1, hN₀.2, hNₓ.1, hNₓ.2])
  have hQ := twoPointAnnulusConst_pos n Nₚ
  have hc1 : (N₀ - Nₓ) ^ 2 * ∫ y in annulus 1 10, u y ^ 2 ≤ twoPointConst₁ n Nₚ * δ := by
    calc (N₀ - Nₓ) ^ 2 * ∫ y in annulus 1 10, u y ^ 2 ≤
        (N₀ - Nₓ) ^ 2 * (twoPointAnnulusConst n Nₚ * ((∫ y in annulus 6 8, u y ^ 2) + δ)) :=
          mul_le_mul_of_nonneg_left hann (sq_nonneg _)
      _ = twoPointAnnulusConst n Nₚ *
          ((N₀ - Nₓ) ^ 2 * (∫ y in annulus 6 8, u y ^ 2) + (N₀ - Nₓ) ^ 2 * δ) := by ring
      _ ≤ twoPointAnnulusConst n Nₚ *
          (2 ^ n * (4 * (1 + 9 * Real.exp (2 * Nₚ))) * δ / twoPointMVTConst Nₚ ^ 2 +
            Nₚ ^ 2 * δ) :=
          mul_le_mul_of_nonneg_left (add_le_add hJ (mul_le_mul_of_nonneg_right hd2 hδ)) hQ.le
      _ = twoPointConst₁ n Nₚ * δ := by unfold twoPointConst₁; ring
  refine ⟨hc1, ?_⟩
  have hw := setIntegral_sq_inner_gradient_add_le hu hx H₀ Hₓ
  have hsplit := setIntegral_sq_add_le (S := annulus 2 9)
    (f := fun y => ⟪gradient u y, x⟫ + (Nₓ - N₀) * u y) (g := fun y => -((Nₓ - N₀) * u y))
    (LipschitzWith.integrableOn_sq_inner_gradient_add_mul hu (measurableSet_annulus 2 9)
      (isBounded_annulus 2 9) (p := fun _ => x) continuous_const _)
    (integrableOn_of_continuous (by fun_prop) (isBounded_annulus 2 9))
  have e1 : ∫ y in annulus 2 9, (⟪gradient u y, x⟫ + (Nₓ - N₀) * u y + -((Nₓ - N₀) * u y)) ^ 2 =
      ∫ y in annulus 2 9, ⟪gradient u y, x⟫ ^ 2 :=
    integral_congr_ae (Eventually.of_forall fun y => by ring)
  have e2 : ∫ y in annulus 2 9, (-((Nₓ - N₀) * u y)) ^ 2 =
      (N₀ - Nₓ) ^ 2 * ∫ y in annulus 2 9, u y ^ 2 := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun y => by ring)
  have hmono : ∫ y in annulus 2 9, u y ^ 2 ≤ ∫ y in annulus 1 10, u y ^ 2 :=
    setIntegral_annulus_mono (by fun_prop) (fun _ => sq_nonneg _) (by norm_num) (by norm_num)
  have h3 : (N₀ - Nₓ) ^ 2 * ∫ y in annulus 2 9, u y ^ 2 ≤ twoPointConst₁ n Nₚ * δ :=
    (mul_le_mul_of_nonneg_left hmono (sq_nonneg _)).trans hc1
  rw [e1, e2] at hsplit
  unfold twoPointConst
  linarith

/-- **Lemma 6.2**, in the shape of the paper: for `u` Lipschitz
on `ℝⁿ`, `x ∈ B_1 ∖ {0}` and `N₀, Nₓ ∈ [1, Nₚ]`, almost homogeneity of degree `N₀` about `0` and
of degree `Nₓ` about `x` (both up to `δ` in `L²(B_10 ∖ B_1)`) imply
`|N₀ - Nₓ|² ∫_{B_10∖B_1} u² ≤ C δ` and `∫_{B_9∖B_2} |∇u · x|² ≤ C δ`, with
`C = twoPointConst n Nₚ` depending only on `n` and `Nₚ`. -/
theorem two_point_homogeneity (n : ℕ) (Nₚ : ℝ) (_hN : 1 < Nₚ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : Rn n → ℝ) (L : ℝ≥0), LipschitzWith L u →
      ∀ x : Rn n, x ∈ ball 0 1 → x ≠ 0 → ∀ N₀ Nₓ δ : ℝ, N₀ ∈ Icc 1 Nₚ → Nₓ ∈ Icc 1 Nₚ →
      (∫ y in ball 0 10 \ ball 0 1, (⟪gradient u y, y⟫ - N₀ * u y) ^ 2) ≤ δ →
      (∫ y in ball 0 10 \ ball 0 1, (⟪gradient u (x + y), y⟫ - Nₓ * u (x + y)) ^ 2) ≤ δ →
      (N₀ - Nₓ) ^ 2 * (∫ y in ball 0 10 \ ball 0 1, u y ^ 2) ≤ C * δ ∧
      (∫ y in ball 0 9 \ ball 0 2, ⟪gradient u y, x⟫ ^ 2) ≤ C * δ := by
  refine ⟨twoPointConst n Nₚ, twoPointConst_pos n Nₚ, fun u L hu x hx _ N₀ Nₓ δ h₀ hₓ H₀ Hₓ => ?_⟩
  have hδ : 0 ≤ δ :=
    (setIntegral_nonneg (measurableSet_annulus 1 10) fun _ _ => sq_nonneg _).trans H₀
  obtain ⟨h1, h2⟩ := two_point_homogeneity_annulus hu (mem_ball_zero_iff.1 hx) h₀ hₓ H₀ Hₓ
  exact ⟨h1.trans (mul_le_mul_of_nonneg_right (twoPointConst₁_le_twoPointConst n Nₚ) hδ), h2⟩

/-- **Lemma 6.2, translated and rescaled** (the form used in the proofs of Theorems 6.1, 6.3 and
Lemma 8.5):
centre `p`, second point `q` with `|q - p| < ρ`, annuli `B_{10ρ}(p) ∖ B_ρ(p)` and
`B_{10ρ}(q) ∖ B_ρ(q)`, and the same constant `C = twoPointConst n Nₚ`. -/
theorem two_point_homogeneity_scaled (hu : LipschitzWith L u) {p q : Rn n} {ρ : ℝ}
    (hρ : 0 < ρ) (hpq : dist q p < ρ) {Nₚ N₀ Nₓ δ : ℝ} (hN₀ : N₀ ∈ Icc 1 Nₚ)
    (hNₓ : Nₓ ∈ Icc 1 Nₚ)
    (H₀ : ∫ y in ball p (10 * ρ) \ ball p ρ, (⟪gradient u y, y - p⟫ - N₀ * u y) ^ 2 ≤ δ)
    (Hₓ : ∫ y in ball q (10 * ρ) \ ball q ρ, (⟪gradient u y, y - q⟫ - Nₓ * u y) ^ 2 ≤ δ) :
    (N₀ - Nₓ) ^ 2 * (∫ y in ball p (10 * ρ) \ ball p ρ, u y ^ 2) ≤ twoPointConst n Nₚ * δ ∧
      ∫ y in ball p (9 * ρ) \ ball p (2 * ρ), ⟪gradient u y, q - p⟫ ^ 2 ≤
        twoPointConst n Nₚ * δ := by
  have hρn : 0 < ρ ^ n := pow_pos hρ n
  have hρn' : 0 < (ρ ^ n)⁻¹ := inv_pos.2 hρn
  -- the rescaled function
  obtain ⟨v, hv⟩ : ∃ f : Rn n → ℝ, f = fun z => u (p + ρ • z) := ⟨_, rfl⟩
  have hv_apply : ∀ z, v z = u (p + ρ • z) := fun z => by rw [hv]
  have hvL : LipschitzWith (L * Real.toNNReal ρ) v := by
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    rw [hv_apply, hv_apply]
    calc dist (u (p + ρ • a)) (u (p + ρ • b)) ≤ L * dist (p + ρ • a) (p + ρ • b) :=
          hu.dist_le_mul _ _
      _ = (L * Real.toNNReal ρ : ℝ≥0) * dist a b := by
          rw [dist_add_left, dist_smul₀, Real.norm_eq_abs, abs_of_pos hρ, NNReal.coe_mul,
            Real.coe_toNNReal _ hρ.le, mul_assoc]
  have hgv : ∀ z, gradient v z = ρ • gradient u (p + ρ • z) := fun z => by
    rw [hv]; exact gradient_comp_add_smul u p ρ z
  set x := ρ⁻¹ • (q - p) with hx_def
  have hx : ‖x‖ < 1 := by
    rw [hx_def, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hρ, ← dist_eq_norm,
      inv_mul_lt_iff₀ hρ, mul_one]
    exact hpq
  have hpx : ∀ z : Rn n, p + ρ • (x + z) = q + ρ • z := fun z => by
    rw [hx_def, smul_add, smul_smul, mul_inv_cancel₀ hρ.ne', one_smul]; abel
  have hcov : ∀ (f : Rn n → ℝ) (c : Rn n) (a b : ℝ),
      ∫ z in annulus a b, f (c + ρ • z) = (ρ ^ n)⁻¹ * ∫ y in ball c (ρ * b) \ ball c (ρ * a), f y :=
    fun f c a b => setIntegral_annulus_comp_add_smul f c hρ a b
  -- hypotheses for `v`
  have H₀' : ∫ z in annulus 1 10, (⟪gradient v z, z⟫ - N₀ * v z) ^ 2 ≤ (ρ ^ n)⁻¹ * δ := by
    have e : ∫ z in annulus 1 10, (⟪gradient v z, z⟫ - N₀ * v z) ^ 2 =
        ∫ z in annulus 1 10,
          (fun y => (⟪gradient u y, y - p⟫ - N₀ * u y) ^ 2) (p + ρ • z) :=
      integral_congr_ae (Eventually.of_forall fun z => by
        dsimp only
        rw [hgv, hv_apply, real_inner_smul_left, ← real_inner_smul_right, add_sub_cancel_left])
    have hc' := hcov (fun y => (⟪gradient u y, y - p⟫ - N₀ * u y) ^ 2) p 1 10
    rw [mul_comm ρ 10, mul_one] at hc'
    rw [e, hc']
    exact mul_le_mul_of_nonneg_left H₀ hρn'.le
  have Hₓ' : ∫ z in annulus 1 10, (⟪gradient v (x + z), z⟫ - Nₓ * v (x + z)) ^ 2 ≤
      (ρ ^ n)⁻¹ * δ := by
    have e : ∫ z in annulus 1 10, (⟪gradient v (x + z), z⟫ - Nₓ * v (x + z)) ^ 2 =
        ∫ z in annulus 1 10,
          (fun y => (⟪gradient u y, y - q⟫ - Nₓ * u y) ^ 2) (q + ρ • z) :=
      integral_congr_ae (Eventually.of_forall fun z => by
        dsimp only
        rw [hgv, hv_apply, hpx, real_inner_smul_left, ← real_inner_smul_right,
          add_sub_cancel_left])
    have hc' := hcov (fun y => (⟪gradient u y, y - q⟫ - Nₓ * u y) ^ 2) q 1 10
    rw [mul_comm ρ 10, mul_one] at hc'
    rw [e, hc']
    exact mul_le_mul_of_nonneg_left Hₓ hρn'.le
  obtain ⟨h1, h2⟩ := two_point_homogeneity_annulus hvL hx hN₀ hNₓ H₀' Hₓ'
  have e1 : ∫ z in annulus 1 10, v z ^ 2 =
      (ρ ^ n)⁻¹ * ∫ y in ball p (10 * ρ) \ ball p ρ, u y ^ 2 := by
    have := hcov (fun y => u y ^ 2) p 1 10
    rw [mul_comm ρ 10, mul_one] at this
    rw [← this]
    exact integral_congr_ae (Eventually.of_forall fun z => by dsimp only; rw [hv_apply])
  have e2 : ∫ z in annulus 2 9, ⟪gradient v z, x⟫ ^ 2 =
      (ρ ^ n)⁻¹ * ∫ y in ball p (9 * ρ) \ ball p (2 * ρ), ⟪gradient u y, q - p⟫ ^ 2 := by
    have := hcov (fun y => ⟪gradient u y, q - p⟫ ^ 2) p 2 9
    rw [mul_comm ρ 9, mul_comm ρ 2] at this
    rw [← this]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    dsimp only
    rw [hgv, hx_def, real_inner_smul_left, real_inner_smul_right, ← mul_assoc,
      mul_inv_cancel₀ hρ.ne', one_mul]
  rw [e1] at h1
  rw [e2] at h2
  have hδ : 0 ≤ δ := by
    have := (setIntegral_nonneg (measurableSet_ball.diff measurableSet_ball)
      fun y _ => sq_nonneg (⟪gradient u y, y - p⟫ - N₀ * u y)).trans H₀
    exact this
  constructor
  · have h1' : (ρ ^ n)⁻¹ * ((N₀ - Nₓ) ^ 2 * ∫ y in ball p (10 * ρ) \ ball p ρ, u y ^ 2) ≤
        (ρ ^ n)⁻¹ * (twoPointConst n Nₚ * δ) := by
      calc _ = (N₀ - Nₓ) ^ 2 * ((ρ ^ n)⁻¹ * ∫ y in ball p (10 * ρ) \ ball p ρ, u y ^ 2) := by
            ring
        _ ≤ twoPointConst₁ n Nₚ * ((ρ ^ n)⁻¹ * δ) := h1
        _ ≤ twoPointConst n Nₚ * ((ρ ^ n)⁻¹ * δ) :=
            mul_le_mul_of_nonneg_right (twoPointConst₁_le_twoPointConst n Nₚ)
              (mul_nonneg hρn'.le hδ)
        _ = _ := by ring
    exact le_of_mul_le_mul_left h1' hρn'
  · have h2' : (ρ ^ n)⁻¹ * ∫ y in ball p (9 * ρ) \ ball p (2 * ρ), ⟪gradient u y, q - p⟫ ^ 2 ≤
        (ρ ^ n)⁻¹ * (twoPointConst n Nₚ * δ) := by
      calc _ ≤ twoPointConst n Nₚ * ((ρ ^ n)⁻¹ * δ) := h2
        _ = _ := by ring
    exact le_of_mul_le_mul_left h2' hρn'

/-- **Lemma 6.2, translated and rescaled, for `u` Lipschitz only on `B_{20ρ}(p)`.** The proof only
sees `B_{10ρ}(p) ∪ B_{10ρ}(q) ⊆ B_{11ρ}(p)`; we extend `u` by McShane's extension. -/
theorem two_point_homogeneity_scaled_of_lipschitzOnWith {p q : Rn n} {ρ : ℝ}
    (hu : LipschitzOnWith L u (ball p (20 * ρ))) (hρ : 0 < ρ) (hpq : dist q p < ρ)
    {Nₚ N₀ Nₓ δ : ℝ} (hN₀ : N₀ ∈ Icc 1 Nₚ) (hNₓ : Nₓ ∈ Icc 1 Nₚ)
    (H₀ : ∫ y in ball p (10 * ρ) \ ball p ρ, (⟪gradient u y, y - p⟫ - N₀ * u y) ^ 2 ≤ δ)
    (Hₓ : ∫ y in ball q (10 * ρ) \ ball q ρ, (⟪gradient u y, y - q⟫ - Nₓ * u y) ^ 2 ≤ δ) :
    (N₀ - Nₓ) ^ 2 * (∫ y in ball p (10 * ρ) \ ball p ρ, u y ^ 2) ≤ twoPointConst n Nₚ * δ ∧
      ∫ y in ball p (9 * ρ) \ ball p (2 * ρ), ⟪gradient u y, q - p⟫ ^ 2 ≤
        twoPointConst n Nₚ * δ := by
  obtain ⟨g, hg, hug⟩ := hu.extend_real
  have hgrad : ∀ y ∈ ball p (20 * ρ), gradient u y = gradient g y := fun y hy => by
    have h : u =ᶠ[nhds y] g := Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hy) hug
    simp only [gradient, h.fderiv_eq]
  have hsub₁ : ball p (10 * ρ) \ ball p ρ ⊆ ball p (20 * ρ) :=
    sdiff_subset.trans (ball_subset_ball (by linarith))
  have hsub₂ : ball q (10 * ρ) \ ball q ρ ⊆ ball p (20 * ρ) := by
    intro y hy
    have hy1 : dist y q < 10 * ρ := hy.1
    change dist y p < 20 * ρ
    have := dist_triangle y q p
    linarith
  have hsub₃ : ball p (9 * ρ) \ ball p (2 * ρ) ⊆ ball p (20 * ρ) :=
    sdiff_subset.trans (ball_subset_ball (by linarith))
  have hm := fun (c : Rn n) (r r' : ℝ) =>
    (measurableSet_ball (x := c) (ε := r)).diff (measurableSet_ball (x := c) (ε := r'))
  have e₀ : ∫ y in ball p (10 * ρ) \ ball p ρ, (⟪gradient u y, y - p⟫ - N₀ * u y) ^ 2 =
      ∫ y in ball p (10 * ρ) \ ball p ρ, (⟪gradient g y, y - p⟫ - N₀ * g y) ^ 2 :=
    setIntegral_congr_fun (hm p _ _) fun y hy => by
      simp only [hgrad y (hsub₁ hy), hug (hsub₁ hy)]
  have eₓ : ∫ y in ball q (10 * ρ) \ ball q ρ, (⟪gradient u y, y - q⟫ - Nₓ * u y) ^ 2 =
      ∫ y in ball q (10 * ρ) \ ball q ρ, (⟪gradient g y, y - q⟫ - Nₓ * g y) ^ 2 :=
    setIntegral_congr_fun (hm q _ _) fun y hy => by
      simp only [hgrad y (hsub₂ hy), hug (hsub₂ hy)]
  have e₁ : ∫ y in ball p (10 * ρ) \ ball p ρ, u y ^ 2 =
      ∫ y in ball p (10 * ρ) \ ball p ρ, g y ^ 2 :=
    setIntegral_congr_fun (hm p _ _) fun y hy => by simp only [hug (hsub₁ hy)]
  have e₂ : ∫ y in ball p (9 * ρ) \ ball p (2 * ρ), ⟪gradient u y, q - p⟫ ^ 2 =
      ∫ y in ball p (9 * ρ) \ ball p (2 * ρ), ⟪gradient g y, q - p⟫ ^ 2 :=
    setIntegral_congr_fun (hm p _ _) fun y hy => by simp only [hgrad y (hsub₃ hy)]
  rw [e₀] at H₀
  rw [eₓ] at Hₓ
  rw [e₁, e₂]
  exact two_point_homogeneity_scaled hg hρ hpq hN₀ hNₓ H₀ Hₓ

end Main

end InnerVariational
