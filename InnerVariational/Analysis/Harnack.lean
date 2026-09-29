/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Basic.Setup
public import InnerVariational.Vendor.Harnack
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import GMTFoundations.Defs.Setup

/-!
# The Harnack inequality on concentric balls

`harnack_inequality`: there is `C = C(n)` such that every function harmonic and nonnegative on
`B_{2r}(x)` satisfies `f(y) ≤ C f(z)` for all `y, z ∈ B_r(x)` (Gilbarg–Trudinger, Thm 2.5).
The constant is `C = 3 ^ (8 n)`.

This file has exactly the statement of `InnerVariational.Registry.harnack_inequality`
(`Registry/Harmonic.lean`) and does not import the registry, so that the registry entry can
delegate to it.

## Proof

The local Harnack inequality `Vendor.HarmonicOnNhd.le_three_pow_mul_of_nonneg` (adapted from
TauCeti, see `Vendor/Harnack.lean`):
if `f` is harmonic and nonnegative on `B_{4ρ}(c)`, then `f(p) ≤ 3ⁿ f(q)` for `p, q ∈ B_ρ(c)`.
For `c ∈ B_r(x)` and `ρ = r / 4` we have `B_{4ρ}(c) ⊆ B_{2r}(x)`. Split the segment from `y` to
`z` (which lies in `B_r(x)` and has length `< 2r`) into eight pieces of length `< r / 4`, and
chain the local estimate along them.

## References

* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Springer, 2001 (reprint of the 1998 edition).
-/

open InnerProductSpace Metric Set Module

@[expose] public noncomputable section

namespace InnerVariational.Analysis

variable {n : ℕ}

/-- **Harnack inequality** (Gilbarg–Trudinger, Theorem 2.5). There is `C = C(n)` such that
every nonnegative harmonic function on `B_{2r}(x)` satisfies `f(y) ≤ C f(z)` for `y, z ∈ B_r(x)`.
One may take `C = 3 ^ (8 n)`. -/
theorem harnack_inequality [NeZero n] :
    ∃ C : ℝ, ∀ (f : Rn n → ℝ) (x : Rn n) (r : ℝ), 0 < r →
      (∀ y ∈ ball x (2 * r), HarmonicAt f y ∧ 0 ≤ f y) →
      ∀ y ∈ ball x r, ∀ z ∈ ball x r, f y ≤ C * f z := by
  refine ⟨((3 : ℝ) ^ n) ^ 8, fun f x r hr hf y hy z hz ↦ ?_⟩
  set p : ℕ → Rn n := fun k ↦ y + ((k : ℝ) / 8) • (z - y) with hp
  have hp_mem : ∀ k ≤ 8, p k ∈ ball x r := fun k hk ↦
    (convex_ball x r).add_smul_sub_mem hy hz
      ⟨by positivity, by rw [div_le_one (by norm_num)]; exact_mod_cast hk⟩
  have hzy : dist z y < 2 * r := by
    rw [mem_ball] at hy hz
    linarith [dist_triangle_right z y x]
  have hstep : ∀ k < 8, f (p k) ≤ 3 ^ n * f (p (k + 1)) := by
    intro k hk
    have hc := hp_mem k hk.le
    have hsub : ball (p k) (4 * (r / 4)) ⊆ ball x (2 * r) :=
      ball_subset_ball' (by rw [mem_ball] at hc; linarith)
    have hdiff : p (k + 1) - p k = (1 / 8 : ℝ) • (z - y) := by
      simp only [hp]
      push_cast
      module
    have hmem : p (k + 1) ∈ ball (p k) (r / 4) := by
      rw [mem_ball, dist_eq_norm, hdiff, norm_smul, ← dist_eq_norm]
      norm_num
      linarith
    have := Vendor.HarmonicOnNhd.le_three_pow_mul_of_nonneg (c := p k) (r := r / 4)
      (fun w hw ↦ (hf w (hsub hw)).1) (fun w hw ↦ (hf w (hsub hw)).2)
      (mem_ball_self (by positivity)) hmem
    rwa [finrank_euclideanSpace_fin] at this
  have hind : ∀ k ≤ 8, f y ≤ ((3 : ℝ) ^ n) ^ k * f (p k) := by
    intro k hk
    induction k with
    | zero => simp [hp]
    | succ k ih =>
      calc f y ≤ ((3 : ℝ) ^ n) ^ k * f (p k) := ih (by omega)
        _ ≤ ((3 : ℝ) ^ n) ^ k * (3 ^ n * f (p (k + 1))) :=
          mul_le_mul_of_nonneg_left (hstep k (by omega)) (by positivity)
        _ = ((3 : ℝ) ^ n) ^ (k + 1) * f (p (k + 1)) := by ring
  have h8 : p 8 = z := by simp [hp]
  simpa [h8] using hind 8 le_rfl

end InnerVariational.Analysis
