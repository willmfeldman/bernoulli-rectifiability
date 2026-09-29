/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Defs.Solutions
public import EllipticBernoulli.Defs.Regularity
import Mathlib.Order.CompletePartialOrder

/-!
# Bridge to `EllipticBernoulli` (foundations)

Translation from this library's definitions to those of the dependency
elliptic-bernoulli-foundations v0.1.0
(https://github.com/willmfeldman/elliptic-bernoulli-foundations). A classical solution in the
sense of `InnerVariational.IsClassicalSolution` is a classical solution of `EllipticBernoulli`
with `Q ≡ 1`. `Rn n` and the dependency's `E n` are the same `EuclideanSpace ℝ (Fin n)`.
-/

@[expose] public section

open Metric Set

namespace InnerVariational

/-- For open `U`, the free boundary `frontier (posSet u U) ∩ U` of `EllipticBernoulli` is
`U ∩ frontier {u > 0}`. -/
theorem eb_freeBoundary_eq_inter_frontier {d : ℕ} {U : Set (Rn d)} (hU : IsOpen U) (u : Rn d → ℝ) :
    EllipticBernoulli.freeBoundary u U = U ∩ frontier {y | 0 < u y} := by
  have h : EllipticBernoulli.posSet u U = {y | 0 < u y} ∩ U := by
    ext y
    simp [EllipticBernoulli.posSet, and_comm]
  rw [EllipticBernoulli.freeBoundary, h, frontier_inter_open_inter hU, inter_comm]

private theorem exists_ball_inter_eq {n : ℕ} {Ω A Z : Set (Rn n)} (hΩ : IsOpen Ω) {x : Rn n}
    (hx : x ∈ Ω) {r : ℝ} (hr : 0 < r) :
    ∃ r', 0 < r' ∧ r' ≤ r ∧ ball x r' ⊆ Ω ∧
      (ball x r ∩ A = ball x r ∩ Z → ball x r' ∩ (Ω ∩ A) = ball x r' ∩ Z) ∧
      (ball x r ∩ (Ω ∩ A) = ball x r ∩ Z → ball x r' ∩ A = ball x r' ∩ Z) := by
  obtain ⟨ρ, hρ, hρΩ⟩ := Metric.isOpen_iff.1 hΩ x hx
  have hsub : ball x (min r ρ) ⊆ ball x r := ball_subset_ball (min_le_left _ _)
  have hsubΩ : ball x (min r ρ) ⊆ Ω := (ball_subset_ball (min_le_right _ _)).trans hρΩ
  refine ⟨min r ρ, lt_min hr hρ, min_le_left _ _, hsubΩ, fun h ↦ ?_, fun h ↦ ?_⟩
  · ext y
    constructor
    · rintro ⟨hy, -, hyA⟩
      exact ⟨hy, (h.le ⟨hsub hy, hyA⟩).2⟩
    · rintro ⟨hy, hyZ⟩
      exact ⟨hy, hsubΩ hy, (h.ge ⟨hsub hy, hyZ⟩).2⟩
  · ext y
    constructor
    · rintro ⟨hy, hyA⟩
      exact ⟨hy, (h.le ⟨hsub hy, hsubΩ hy, hyA⟩).2⟩
    · rintro ⟨hy, hyZ⟩
      exact ⟨hy, (h.ge ⟨hsub hy, hyZ⟩).2.2⟩

/-- A classical solution is a classical solution of `EllipticBernoulli` with `Q ≡ 1`. -/
theorem IsClassicalSolution.toEB {n : ℕ} {Ω : Set (Rn n)} {u : Rn n → ℝ}
    (h : IsClassicalSolution Ω u) : EllipticBernoulli.IsClassicalSolution Ω (fun _ ↦ 1) u where
  isOpen := h.isOpen
  lipschitzOnWith := h.lipschitzOnWith
  nonneg := h.nonneg
  harmonicAt := h.harmonicAt
  free_boundary x hx := by
    rw [eb_freeBoundary_eq_inter_frontier h.isOpen] at hx ⊢
    obtain ⟨r, hr, F, hF, hFx, hball, hnormal⟩ := h.free_boundary x hx
    obtain ⟨r', hr', -, -, H, -⟩ := exists_ball_inter_eq (A := frontier {y | 0 < u y})
      (Z := {y | F y = 0}) h.isOpen hx.1 hr
    exact ⟨r', hr', F, hF, hFx, H hball, hnormal⟩

end InnerVariational
