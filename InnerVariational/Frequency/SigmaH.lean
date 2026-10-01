/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Frequency.Concrete
public import InnerVariational.Defs.HighestDensity
import InnerVariational.Monotonicity.Radial
public import InnerVariational.Defs.VariationalSolution

/-!
# Structure of `Σ^H` and `Σ^H_r` (preamble of Section 6)

The preamble of Section 6 of D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff
measure, and compactness for non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78
(2025), no. 3, DOI 10.1002/cpa.22226; arXiv:2306.10131 (numbering of arXiv v2). For a
variational solution `(u, χ)` on `Ω`, `Σ^H` is the set of free boundary points of highest
density and `Σ^H_r` its radius-`r` version (`Defs/HighestDensity.lean`; there `Σ^H` is defined by
`M_x(u; r) ≥ |B_1|` for every admissible `r`, equivalent to the paper's `M_x(u; 0+) ≥ |B_1|` by
the monotonicity of `M`).

## Main results

* `IsVariationalSolution.mem_sigmaHr_of_le`: `Σ^H_s ∩ Ω_r ⊆ Σ^H_r` for `0 < s ≤ r`.
* `IsVariationalSolution.mem_sigmaH_iff_forall_mem_sigmaHr`: for `x ∈ Ω_r`,
  `x ∈ Σ^H ↔ ∀ s ∈ (0, r), x ∈ Σ^H_s`, i.e. `⋂_{0<s<r} Σ^H_s ∩ Ω_r = Σ^H ∩ Ω_r`.
* `IsVariationalSolution.closure_sigmaHr_inter_subset`: `Σ^H_r` is relatively closed in
  `Ω_r = {x : B̄_r(x) ⊆ Ω}`, from the continuity of `x ↦ M_x(u; r)` (as in the proof of
  Theorem 6.1).
* On `Σ^H`: `N_x ≥ 1` (`one_le_frequencyN_of_mem_sigmaH`), `N_x` is nondecreasing
  (`monotoneOn_frequencyN_of_mem_sigmaH`), and `N_x(u; 0+)` exists and is `≥ 1`
  (`exists_tendsto_frequencyN_zero`). The same on `Σ^H_r` for radii `≥ r`.

## Not in this file

The equivalence with the definition of `Σ^H` in Section 6 by `M_x(u; 0+) ≥ |B_1|`
(`IsVariationalSolution.mem_sigmaH_iff_le_Mzero`), the upper semicontinuity of
`x ↦ M_x(u; 0+)` and the relative closedness of `Σ^H` in `Ω` rest on Proposition 3.5; they are
in `Monotonicity/Limits.lean` and `Monotonicity/HighestDensity.lean`.
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

namespace IsVariationalSolution

variable {Ω : Set (Rn n)} {C : ℝ≥0} {u χ : Rn n → ℝ} {x : Rn n}

section

variable [NeZero n] (h : IsVariationalSolution Ω C u χ)
include h

/-- `Σ^H_s ∩ Ω_r ⊆ Σ^H_r` for `0 < s ≤ r`, by the monotonicity of `M` (Proposition 3.4). -/
theorem mem_sigmaHr_of_le {s r : ℝ} (hs : 0 < s) (hsr : s ≤ r) (hx : x ∈ sigmaHr Ω u χ s)
    (hr : closedBall x r ⊆ Ω) : x ∈ sigmaHr Ω u χ r :=
  ⟨hx.1, hr, hx.2.2.1, hx.2.2.2.trans (h.monotonicityM_le hs hsr hr)⟩

/-- `⋂_{0<s<r} Σ^H_s ∩ Ω_r = Σ^H ∩ Ω_r` (preamble of §6), pointwise: for `x ∈ Ω_r`,
`x ∈ Σ^H ↔ ∀ s ∈ (0, r), x ∈ Σ^H_s`. -/
theorem mem_sigmaH_iff_forall_mem_sigmaHr {r : ℝ} (hr : 0 < r) (hx : closedBall x r ⊆ Ω) :
    x ∈ sigmaH Ω u χ ↔ ∀ s ∈ Ioo 0 r, x ∈ sigmaHr Ω u χ s := by
  constructor
  · intro hxH s hs
    exact mem_sigmaHr_of_mem_sigmaH hxH hs.1 ((closedBall_subset_closedBall hs.2.le).trans hx)
  · intro H
    obtain ⟨hxΩ, -, hcl, -⟩ := H (r / 2) ⟨by positivity, by linarith⟩
    refine ⟨hxΩ, hcl, fun ρ hρ hρΩ => ?_⟩
    set s := min (ρ / 2) (r / 2) with hsdef
    have hs0 : 0 < s := lt_min (by positivity) (by positivity)
    have hsr : s < r := (min_le_right _ _).trans_lt (by linarith)
    have hsρ : s ≤ ρ := (min_le_left _ _).trans (by linarith)
    exact (H s ⟨hs0, hsr⟩).2.2.2.trans (h.monotonicityM_le hs0 hsρ hρΩ)

/-- The set form of `mem_sigmaH_iff_forall_mem_sigmaHr`:
`(⋂_{0<s<r} Σ^H_s) ∩ Ω_r = Σ^H ∩ Ω_r` (preamble of §6). -/
theorem iInter_sigmaHr_inter_eq {r : ℝ} (hr : 0 < r) :
    (⋂ s ∈ Ioo 0 r, sigmaHr Ω u χ s) ∩ {x | closedBall x r ⊆ Ω} =
      sigmaH Ω u χ ∩ {x | closedBall x r ⊆ Ω} := by
  ext y
  simp only [mem_inter_iff, mem_iInter, mem_ofPred_eq]
  constructor
  · rintro ⟨H, hy⟩
    exact ⟨(h.mem_sigmaH_iff_forall_mem_sigmaHr hr hy).2 H, hy⟩
  · rintro ⟨H, hy⟩
    exact ⟨(h.mem_sigmaH_iff_forall_mem_sigmaHr hr hy).1 H, hy⟩

/-- **`Σ^H_r` is relatively closed in `Ω_r`** (preamble of §6): a limit point of `Σ^H_r` that
lies in `Ω_r = {x : B̄_r(x) ⊆ Ω}` lies in `Σ^H_r`. This uses the continuity of
`x ↦ M_x(u; r)`. -/
theorem closure_sigmaHr_inter_subset {r : ℝ} (hr : 0 < r) :
    closure (sigmaHr Ω u χ r) ∩ {x | closedBall x r ⊆ Ω} ⊆ sigmaHr Ω u χ r := by
  rintro y ⟨hycl, hyr⟩
  have hyr' : closedBall y r ⊆ Ω := hyr
  refine ⟨hyr' (mem_closedBall_self hr.le), hyr', ?_, ?_⟩
  · exact closure_minimal (fun z (hz : z ∈ sigmaHr Ω u χ r) => hz.2.2.1) isClosed_closure hycl
  · have hc := h.continuousAt_monotonicityM hr hyr'
    have := mem_closure_iff_nhdsWithin_neBot.1 hycl
    exact ge_of_tendsto (hc.tendsto.mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun z (hz : z ∈ sigmaHr Ω u χ r) => hz.2.2.2)

/-- `N_x(u; r) ≥ 1` for `x ∈ Σ^H` and every admissible `r` (preamble of §6, from Lemma 4.1). -/
theorem one_le_frequencyN_of_mem_sigmaH (hx : x ∈ sigmaH Ω u χ) {r : ℝ} (hr : 0 < r)
    (hΩ : closedBall x r ⊆ Ω) : 1 ≤ frequencyN u χ x r :=
  h.one_le_frequencyN hx.2.1 hr (hx.2.2 r hr hΩ) hΩ ⟨le_rfl, le_rfl⟩

/-- `s ↦ N_x(u; s)` is nondecreasing on `(0, R]` for `x ∈ Σ^H` and `B̄_R(x) ⊆ Ω` (Lemma 4.1). -/
theorem monotoneOn_frequencyN_of_mem_sigmaH (hx : x ∈ sigmaH Ω u χ) {R : ℝ}
    (hΩ : closedBall x R ⊆ Ω) : MonotoneOn (frequencyN u χ x) (Ioc 0 R) := by
  intro s hs t ht hst
  exact h.monotoneOn_frequencyN hx.2.1 hs.1
    (hx.2.2 s hs.1 ((closedBall_subset_closedBall hs.2).trans hΩ)) hΩ ⟨le_rfl, hs.2⟩
    ⟨hst, ht.2⟩ hst

/-- `N_x(u; s) ≥ 1` for `x ∈ Σ^H_r` and `s ∈ [r, R]`, `B̄_R(x) ⊆ Ω`. -/
theorem one_le_frequencyN_of_mem_sigmaHr {r : ℝ} (hr : 0 < r) (hx : x ∈ sigmaHr Ω u χ r)
    {R : ℝ} (hΩ : closedBall x R ⊆ Ω) {s : ℝ} (hs : s ∈ Icc r R) : 1 ≤ frequencyN u χ x s :=
  h.one_le_frequencyN hx.2.2.1 hr hx.2.2.2 hΩ hs

/-- `s ↦ N_x(u; s)` is nondecreasing on `[r, R]` for `x ∈ Σ^H_r` and `B̄_R(x) ⊆ Ω`. -/
theorem monotoneOn_frequencyN_of_mem_sigmaHr {r : ℝ} (hr : 0 < r) (hx : x ∈ sigmaHr Ω u χ r)
    {R : ℝ} (hΩ : closedBall x R ⊆ Ω) : MonotoneOn (frequencyN u χ x) (Icc r R) :=
  h.monotoneOn_frequencyN hx.2.2.1 hr hx.2.2.2 hΩ

/-- **`N_x(u; 0+)` exists and is `≥ 1`** on `Σ^H` (preamble of §6): `s ↦ N_x(u; s)` is
nondecreasing and `≥ 1` near `0`, so it has a limit `N₀ ≥ 1` as `s → 0+`. -/
theorem exists_tendsto_frequencyN_zero (hx : x ∈ sigmaH Ω u χ) :
    ∃ N₀, 1 ≤ N₀ ∧ Tendsto (frequencyN u χ x) (𝓝[>] 0) (𝓝 N₀) := by
  obtain ⟨R, hR, hΩ⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (h.isOpen.mem_nhds hx.1)
  have hmono := (h.monotoneOn_frequencyN_of_mem_sigmaH hx hΩ).mono Ioo_subset_Ioc_self
  have hne : (Ioo (0 : ℝ) R).Nonempty := nonempty_Ioo.2 hR
  have hge : ∀ b ∈ frequencyN u χ x '' Ioo 0 R, 1 ≤ b := by
    rintro _ ⟨s, hs, rfl⟩
    exact h.one_le_frequencyN_of_mem_sigmaH hx hs.1
      ((closedBall_subset_closedBall hs.2.le).trans hΩ)
  refine ⟨sInf (frequencyN u χ x '' Ioo 0 R), le_csInf (hne.image _) hge, ?_⟩
  exact hmono.tendsto_nhdsWithin_Ioo_right hne ⟨1, hge⟩

end

end IsVariationalSolution

end InnerVariational
