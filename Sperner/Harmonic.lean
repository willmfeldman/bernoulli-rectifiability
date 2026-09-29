/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Sperner.Basic
public import Sperner.Vendor.HarmonicBasic

/-!
# Harmonic functions: Weyl's lemma, strong maximum principle, isometry invariance

Interface to the vendored harmonic-function infrastructure (`Sperner/Vendor/`), stated on
`ℝⁿ = EuclideanSpace ℝ (Fin n)`:

* `Sperner.harmonicAt_of_integral_mul_laplacian_eq_zero`: **Weyl's lemma**. A function which is
  continuous on an open set `U` and satisfies `∫ u Δφ = 0` for all smooth `φ` with compact
  support in `U` is harmonic on `U`.
* `Sperner.eq_zero_of_harmonicAt_of_nonneg`: **strong maximum principle** in the form used
  here. A nonnegative harmonic function on a preconnected open set that vanishes at one point
  vanishes identically.
* `Sperner.harmonicAt_comp_linearIsometryEquiv`: harmonicity is invariant under linear
  isometries.

The strong maximum principle is proved from the vendored mean-value property with the radial
weight `max 0 (R - |y|)` (the argument of `EllipticBernoulli/Harmonic/StrongMax.lean`, written
anew here for the nonnegative case).
-/

open InnerProductSpace MeasureTheory Metric Set Filter Topology
open scoped ContDiff Laplacian
open Sperner.Vendor.Analysis (WeaklyHarmonicOn weyl_of_weaklyHarmonicOn
  integral_radial_smul_eq_of_weaklyHarmonic laplacian_comp_linearIsometryEquiv_right)

@[expose] public noncomputable section

namespace Sperner

variable {n : ℕ}

/-- **Weyl's lemma.** A continuous function on an open set `U` with `∫ u Δφ = 0` for every
smooth `φ` with compact support in `U` is harmonic on `U`. -/
theorem harmonicAt_of_integral_mul_laplacian_eq_zero {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContinuousOn u U)
    (h : ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ U → ∫ x, u x * Δ φ x = 0) :
    ∀ x ∈ U, InnerProductSpace.HarmonicAt u x := by
  have hw : WeaklyHarmonicOn volume u U := fun χ hχ hχc hχU => by
    simp_rw [smul_eq_mul, mul_comm (Δ χ _)]
    exact h χ hχ hχc hχU
  obtain ⟨hs, hΔ⟩ := weyl_of_weaklyHarmonicOn hU hu hw
  exact fun x hx => ⟨(hs.contDiffAt (hU.mem_nhds hx)).of_le (by norm_cast),
    Filter.eventuallyEq_of_mem (hU.mem_nhds hx) fun y hy => hΔ y hy⟩

/-- Local step of the strong maximum principle: a nonnegative harmonic function vanishing at the
centre of a closed ball inside its domain vanishes on the open ball. -/
lemma eqOn_ball_zero_of_harmonicOnNhd [Nontrivial (EuclideanSpace ℝ (Fin n))]
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : HarmonicOnNhd u U) {x : EuclideanSpace ℝ (Fin n)} {R : ℝ} (_hR : 0 < R)
    (hB : closedBall x R ⊆ U) (hnn : ∀ y ∈ closedBall x R, 0 ≤ u y) (h0 : u x = 0) :
    ∀ y ∈ ball x R, u y = 0 := by
  have hw : WeaklyHarmonicOn volume u U := Vendor.weaklyHarmonicOn_of_harmonicOnNhd hU hu
  have hc : ContinuousOn u U := hu.continuousOn
  set k : ℝ → ℝ := fun r => max 0 (R - r) with hkdef
  have hk : Continuous k := by fun_prop
  have hkR : ∀ r, R < r → k r = 0 := fun r hr => max_eq_left (by linarith)
  have hmv := integral_radial_smul_eq_of_weaklyHarmonic hU hc hw hB hk hkR
  rw [h0, smul_zero] at hmv
  set F : EuclideanSpace ℝ (Fin n) → ℝ := fun y => k ‖y‖ * u (x + y) with hFdef
  have hmaps : MapsTo (fun y => x + y) (closedBall 0 R) U := fun y hy => hB (by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]; simpa using hy)
  have hFcont : ContinuousOn F (closedBall 0 R) :=
    (hk.comp continuous_norm).continuousOn.mul
      (hc.comp (continuous_const.add continuous_id).continuousOn hmaps)
  have hF0 : ∀ y ∉ closedBall (0 : EuclideanSpace ℝ (Fin n)) R, F y = 0 := fun y hy => by
    rw [mem_closedBall, dist_zero_right, not_le] at hy
    simp only [hFdef, hkR _ hy, zero_mul]
  have hFint : Integrable F :=
    (hFcont.integrableOn_compact (isCompact_closedBall 0 R)).integrable_of_forall_notMem_eq_zero
      hF0
  have hFnn : 0 ≤ F := fun y => by
    by_cases hy : y ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) R
    · refine mul_nonneg (le_max_left _ _) (hnn _ ?_)
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]; simpa using hy
    · simp only [Pi.zero_apply]; rw [hF0 y hy]
  have hae : F =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg hFnn hFint).1 (by simpa [hFdef, smul_eq_mul] using hmv)
  have heq := Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae hae) isOpen_ball
    (hFcont.mono ball_subset_closedBall) continuousOn_const
  intro y hy
  have hy' : y - x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) R := by
    rw [mem_ball, dist_zero_right, ← dist_eq_norm]; exact hy
  have h1 := heq hy'
  simp only [hFdef, Pi.zero_apply, add_sub_cancel] at h1
  have hkpos : 0 < k ‖y - x‖ := by
    rw [mem_ball, dist_zero_right] at hy'
    simp only [hkdef]; exact lt_max_of_lt_right (by linarith)
  exact (mul_eq_zero.1 h1).resolve_left hkpos.ne'

/-- **Strong maximum principle** (nonnegative form). A nonnegative harmonic function on a
preconnected open set which vanishes at one point vanishes identically. -/
theorem eq_zero_of_harmonicAt_of_nonneg {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω)
    (hc : IsPreconnected Ω) {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ∀ x ∈ Ω, InnerProductSpace.HarmonicAt u x) (hnn : ∀ x ∈ Ω, 0 ≤ u x)
    {x₀ : EuclideanSpace ℝ (Fin n)} (hx₀ : x₀ ∈ Ω) (h0 : u x₀ = 0) :
    ∀ x ∈ Ω, u x = 0 := by
  rcases subsingleton_or_nontrivial (EuclideanSpace ℝ (Fin n)) with hE | hE
  · intro x _; rw [Subsingleton.elim x x₀]; exact h0
  have hΩh : HarmonicOnNhd u Ω := hu
  set S := {y | y ∈ Ω ∧ u y = 0} with hSdef
  set T := Ω ∩ u ⁻¹' {0}ᶜ with hTdef
  have hS : IsOpen S := by
    rw [Metric.isOpen_iff]
    rintro y ⟨hyΩ, hy0⟩
    obtain ⟨R, hR, hRB⟩ := Metric.isOpen_iff.1 hΩ y hyΩ
    have hB : closedBall y (R / 2) ⊆ Ω := (closedBall_subset_ball (by linarith)).trans hRB
    refine ⟨R / 2, half_pos hR, fun z hz => ⟨hB (ball_subset_closedBall hz), ?_⟩⟩
    exact eqOn_ball_zero_of_harmonicOnNhd hΩ hΩh (half_pos hR) hB (fun w hw => hnn w (hB hw))
      hy0 z hz
  have hT : IsOpen T := hΩh.continuousOn.isOpen_inter_preimage hΩ isOpen_compl_singleton
  have hdisj : Disjoint S T := Set.disjoint_left.2 fun y hyS hyT => hyT.2 hyS.2
  have hcover : Ω ⊆ S ∪ T := fun y hy => by
    by_cases h : u y = 0
    · exact Or.inl ⟨hy, h⟩
    · exact Or.inr ⟨hy, h⟩
  have hsub := IsPreconnected.subset_left_of_subset_union hS hT hdisj hcover
    ⟨x₀, hx₀, hx₀, h0⟩ hc
  exact fun x hx => (hsub hx).2

/-- Harmonicity is invariant under linear isometries. -/
theorem harmonicAt_comp_linearIsometryEquiv
    (R : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (h : InnerProductSpace.HarmonicAt u (R x)) : InnerProductSpace.HarmonicAt (u ∘ R) x := by
  refine ⟨h.1.comp x R.contDiff.contDiffAt, ?_⟩
  rw [laplacian_comp_linearIsometryEquiv_right]
  filter_upwards [h.2.comp_tendsto (R.continuous.tendsto x)] with y hy
  simpa using hy

end Sperner
