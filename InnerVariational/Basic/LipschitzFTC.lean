/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Fundamental theorem of calculus for Lipschitz functions of one variable

Mathlib proves the fundamental theorem of calculus for absolutely continuous functions
(`AbsolutelyContinuousOnInterval.integral_deriv_eq_sub`). This file restates it in the form used
throughout the project:

* `LipschitzOnWith.integral_deriv_eq_sub`: if `f` is Lipschitz on `[a, b]`, then
  `∫ x in a..b, deriv f x = f b - f a`;
* `AbsolutelyContinuousOnInterval.integral_eq_sub_of_ae_hasDerivAt`:
  the same with an a.e. derivative `f'` in place of `deriv f` (integrability of `f'` is automatic);
* `AbsolutelyContinuousOnInterval.monotoneOn_of_ae_hasDerivAt_nonneg`: a function that is
  absolutely continuous on `[a, b]` with a.e. nonnegative derivative on `(a, b)` is monotone on
  `[a, b]`;
* comparison versions: `f' ≤ g'` a.e. implies `f y - f x ≤ g y - g x`.

We also collect some elementary facts on Lipschitz real functions on a set: products of bounded
Lipschitz functions, inverses and logarithms of Lipschitz functions bounded below by a positive
constant are Lipschitz. These are used to show that quotients such as the frequency
`N = (D - ω) / H` are Lipschitz.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped NNReal Topology

section AE

/-- An a.e. statement on `Ioo a b` upgrades to an a.e. statement on `Icc a b`. -/
theorem ae_mem_Icc_imp_of_ae_mem_Ioo {p : ℝ → Prop} {a b : ℝ}
    (h : ∀ᵐ x, x ∈ Ioo a b → p x) : ∀ᵐ x, x ∈ Icc a b → p x := by
  filter_upwards [h, (Ioo_ae_eq_Icc (μ := volume) (a := a) (b := b)).mem_iff] with x hx hiff hmem
  exact hx (hiff.2 hmem)

/-- An a.e. statement on `Ioo a b` upgrades to an a.e. statement on `uIcc a b` when `a ≤ b`. -/
theorem ae_mem_uIcc_imp_of_ae_mem_Ioo {p : ℝ → Prop} {a b : ℝ} (hab : a ≤ b)
    (h : ∀ᵐ x, x ∈ Ioo a b → p x) : ∀ᵐ x, x ∈ uIcc a b → p x := by
  rw [uIcc_of_le hab]
  exact ae_mem_Icc_imp_of_ae_mem_Ioo h

/-- Restrict an a.e. statement on `Ioo a b` to a subinterval `Ioo c d`. -/
theorem ae_mem_Ioo_imp_mono {p : ℝ → Prop} {a b c d : ℝ} (hac : a ≤ c) (hdb : d ≤ b)
    (h : ∀ᵐ x, x ∈ Ioo a b → p x) : ∀ᵐ x, x ∈ Ioo c d → p x := by
  filter_upwards [h] with x hx hmem
  exact hx ⟨hac.trans_lt hmem.1, hmem.2.trans_le hdb⟩

end AE

namespace AbsolutelyContinuousOnInterval

variable {f g f' g' : ℝ → ℝ} {a b : ℝ}

/-- FTC for absolutely continuous functions, with an a.e. derivative. -/
theorem integral_eq_sub_of_ae_hasDerivAt (hf : AbsolutelyContinuousOnInterval f a b)
    (hf' : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt f (f' x) x) :
    ∫ x in a..b, f' x = f b - f a := by
  rw [← hf.integral_deriv_eq_sub]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [hf'] with x hx hmem
  exact (hx (uIoc_subset_uIcc hmem)).deriv.symm

/-- An a.e. derivative of an absolutely continuous function is interval integrable. -/
theorem intervalIntegrable_of_ae_hasDerivAt (hf : AbsolutelyContinuousOnInterval f a b)
    (hf' : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt f (f' x) x) :
    IntervalIntegrable f' volume a b := by
  refine hf.intervalIntegrable_deriv.congr_ae ((ae_restrict_iff' measurableSet_uIoc).2 ?_)
  filter_upwards [hf'] with x hx hmem
  exact (hx (uIoc_subset_uIcc hmem)).deriv

/-- Restriction of absolute continuity to a subinterval of `[a, b]`. -/
theorem mono_Icc (hf : AbsolutelyContinuousOnInterval f a b) {c d : ℝ} (hab : a ≤ b)
    (hc : c ∈ Icc a b) (hd : d ∈ Icc a b) : AbsolutelyContinuousOnInterval f c d := by
  refine hf.mono ?_
  rw [uIcc_of_le hab]
  exact uIcc_subset_Icc hc hd

/-- An absolutely continuous function whose a.e. derivative on `(a, b)` is nonnegative is
monotone on `[a, b]`. -/
theorem monotoneOn_of_ae_hasDerivAt_nonneg (hf : AbsolutelyContinuousOnInterval f a b)
    (hf' : ∀ᵐ x, x ∈ Ioo a b → HasDerivAt f (f' x) x)
    (hf'0 : ∀ᵐ x, x ∈ Ioo a b → 0 ≤ f' x) : MonotoneOn f (Icc a b) := by
  intro x hx y hy hxy
  have hab : a ≤ b := hx.1.trans (hx.2)
  have hxy' : ∀ᵐ t, t ∈ Ioo x y → HasDerivAt f (f' t) t ∧ 0 ≤ f' t := by
    filter_upwards [hf', hf'0] with t h1 h2 ht
    have ht' : t ∈ Ioo a b := ⟨hx.1.trans_lt ht.1, ht.2.trans_le hy.2⟩
    exact ⟨h1 ht', h2 ht'⟩
  have hint := (hf.mono_Icc hab hx hy).integral_eq_sub_of_ae_hasDerivAt
    (f' := f') (ae_mem_uIcc_imp_of_ae_mem_Ioo hxy (hxy'.mono fun t ht hmem => (ht hmem).1))
  have hnonneg : 0 ≤ ∫ t in x..y, f' t := by
    refine intervalIntegral.integral_nonneg_of_ae_restrict hxy ?_
    rw [EventuallyLE, ae_restrict_iff' measurableSet_Icc]
    filter_upwards [ae_mem_Icc_imp_of_ae_mem_Ioo hxy'] with t ht hmem
    exact (ht hmem).2
  linarith

/-- Comparison principle: if `f' ≤ g'` a.e. on `(a, b)`, then `f y - f x ≤ g y - g x` for
`a ≤ x ≤ y ≤ b`. -/
theorem sub_le_sub_of_ae_hasDerivAt_le (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : AbsolutelyContinuousOnInterval g a b)
    (hf' : ∀ᵐ x, x ∈ Ioo a b → HasDerivAt f (f' x) x)
    (hg' : ∀ᵐ x, x ∈ Ioo a b → HasDerivAt g (g' x) x)
    (hle : ∀ᵐ x, x ∈ Ioo a b → f' x ≤ g' x) {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b)
    (hxy : x ≤ y) : f y - f x ≤ g y - g x := by
  have h := (hg.sub hf).monotoneOn_of_ae_hasDerivAt_nonneg (f' := fun x => g' x - f' x)
    (by filter_upwards [hf', hg'] with x h1 h2 hmem using (h2 hmem).sub (h1 hmem))
    (by filter_upwards [hle] with x hx hmem using sub_nonneg.2 (hx hmem)) hx hy hxy
  simp only [Pi.sub_apply] at h
  linarith

end AbsolutelyContinuousOnInterval

namespace LipschitzOnWith

variable {f g f' g' : ℝ → ℝ} {a b : ℝ} {K L : ℝ≥0}

/-- *Fundamental theorem of calculus* for Lipschitz functions:
if `f` is Lipschitz on `[a, b]`, then `∫ x in a..b, deriv f x = f b - f a`. -/
theorem integral_deriv_eq_sub (hf : LipschitzOnWith K f (uIcc a b)) :
    ∫ x in a..b, deriv f x = f b - f a :=
  hf.absolutelyContinuousOnInterval.integral_deriv_eq_sub

/-- A function Lipschitz on `[a, b]` is absolutely continuous on `[a, b]`. -/
theorem absolutelyContinuousOnInterval_of_Icc (hf : LipschitzOnWith K f (Icc a b))
    (hab : a ≤ b) : AbsolutelyContinuousOnInterval f a b :=
  (hf.mono (uIcc_of_le hab).subset).absolutelyContinuousOnInterval

end LipschitzOnWith

/-! ### Algebra of Lipschitz real functions on a set -/

namespace LipschitzOnWith

variable {α : Type*} [PseudoMetricSpace α] {s : Set α} {f g : α → ℝ} {K L : ℝ≥0}

/-- The product of two bounded Lipschitz real functions is Lipschitz. -/
theorem exists_mul (hf : LipschitzOnWith K f s) (hg : LipschitzOnWith L g s) {A B : ℝ}
    (hfA : ∀ x ∈ s, |f x| ≤ A) (hgB : ∀ x ∈ s, |g x| ≤ B) :
    ∃ M, LipschitzOnWith M (fun x => f x * g x) s := by
  refine ⟨Real.toNNReal (A * L + B * K), LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_⟩
  have hfxy := hf.dist_le_mul x hx y hy
  have hgxy := hg.dist_le_mul x hx y hy
  rw [Real.dist_eq] at hfxy hgxy ⊢
  have hA : 0 ≤ A := (abs_nonneg _).trans (hfA x hx)
  have hB : 0 ≤ B := (abs_nonneg _).trans (hgB x hx)
  rw [Real.coe_toNNReal _ (by positivity)]
  have key : f x * g x - f y * g y = f x * (g x - g y) + g y * (f x - f y) := by ring
  calc |f x * g x - f y * g y| ≤ |f x| * |g x - g y| + |g y| * |f x - f y| := by
        rw [key]; exact (abs_add_le _ _).trans (by rw [abs_mul, abs_mul])
    _ ≤ A * (L * dist x y) + B * (K * dist x y) := by
        gcongr
        · exact hfA x hx
        · exact hgB y hy
    _ = (A * L + B * K) * dist x y := by ring

/-- The inverse of a Lipschitz real function bounded below by a positive constant is Lipschitz. -/
theorem exists_inv (hg : LipschitzOnWith K g s) {c : ℝ} (hc : 0 < c) (hgc : ∀ x ∈ s, c ≤ g x) :
    ∃ M, LipschitzOnWith M (fun x => (g x)⁻¹) s := by
  refine ⟨Real.toNNReal (K / c ^ 2), LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_⟩
  have hgxy := hg.dist_le_mul x hx y hy
  rw [Real.dist_eq] at hgxy ⊢
  rw [Real.coe_toNNReal _ (by positivity)]
  have hx0 : 0 < g x := hc.trans_le (hgc x hx)
  have hy0 : 0 < g y := hc.trans_le (hgc y hy)
  have key : (g x)⁻¹ - (g y)⁻¹ = (g y - g x) / (g x * g y) := by field_simp
  rw [key, abs_div, abs_of_pos (mul_pos hx0 hy0), abs_sub_comm]
  have hden : c ^ 2 ≤ g x * g y := by
    rw [sq]; exact mul_le_mul (hgc x hx) (hgc y hy) hc.le hx0.le
  rw [div_le_iff₀ (mul_pos hx0 hy0)]
  calc |g x - g y| ≤ K * dist x y := hgxy
    _ = K / c ^ 2 * dist x y * c ^ 2 := by field_simp
    _ ≤ K / c ^ 2 * dist x y * (g x * g y) := by gcongr

/-- The logarithm of a Lipschitz real function bounded below by a positive constant is
Lipschitz. -/
theorem exists_log (hg : LipschitzOnWith K g s) {c : ℝ} (hc : 0 < c) (hgc : ∀ x ∈ s, c ≤ g x) :
    ∃ M, LipschitzOnWith M (fun x => Real.log (g x)) s := by
  have hlog : LipschitzOnWith (Real.toNNReal c⁻¹) Real.log (Ici c) := by
    refine (convex_Ici c).lipschitzOnWith_of_nnnorm_deriv_le
      (fun x hx => Real.differentiableAt_log (hc.trans_le hx).ne') fun x hx => ?_
    have hx0 : 0 < x := hc.trans_le hx
    rw [Real.deriv_log, ← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 hx0), Real.coe_toNNReal _ (inv_pos.2 hc).le]
    exact inv_anti₀ hc hx
  exact ⟨_, hlog.comp hg fun x hx => hgc x hx⟩

end LipschitzOnWith

/-- A function Lipschitz on a compact set is bounded there. -/
theorem LipschitzOnWith.exists_abs_le {s : Set ℝ} {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzOnWith K f s) (hs : IsCompact s) : ∃ A, ∀ x ∈ s, |f x| ≤ A := by
  obtain ⟨A, hA⟩ := hs.exists_bound_of_continuousOn hf.continuousOn
  exact ⟨A, fun x hx => by simpa [Real.norm_eq_abs] using hA x hx⟩

/-- A function continuous and positive on a nonempty compact set is bounded below by a positive
constant there. -/
theorem ContinuousOn.exists_pos_le_of_isCompact {s : Set ℝ} {f : ℝ → ℝ} (hf : ContinuousOn f s)
    (hs : IsCompact s) (hpos : ∀ x ∈ s, 0 < f x) : ∃ c, 0 < c ∧ ∀ x ∈ s, c ≤ f x := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, by simp⟩
  obtain ⟨x₀, hx₀, hmin⟩ := hs.exists_isMinOn hne hf
  exact ⟨f x₀, hpos x₀ hx₀, fun x hx => hmin hx⟩
