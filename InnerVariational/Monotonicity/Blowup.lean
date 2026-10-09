/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Monotonicity.Radial
public import InnerVariational.Registry.Harmonic
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
public import InnerVariational.Kernel.Harmonic
import InnerVariational.Kernel.IBP
import InnerVariational.Basic.SphereIntegral

/-!
# Compactness of Lipschitz blow-ups

The compactness step in the proof of Proposition 3.5 of Kriventsov–Weiss (see the references).
Let `w_k ≥ 0` be Lipschitz on the balls of an open set `U` with a common constant `L`, harmonic on
`U ∩ {w_k > 0}`, and `w_k → w₀` locally uniformly on `U`. Then

* `w₀` has the same properties (`IsLipHarmonicPos.of_tendstoLocallyUniformlyOn`), and
  `∇w_k → ∇w₀` pointwise on `U ∩ {w₀ > 0}` (`tendsto_gradient_of_tendstoLocallyUniformlyOn`);
* `∫ |∇w_k|² η → ∫ |∇w₀|² η` for Lipschitz `η` with compact support in `U`
  (`tendsto_integral_norm_gradient_sq_mul`);
* `∇w_k → ∇w₀` strongly in `L²_loc(U)`: `∫ |∇w_k − ∇w₀|² η → 0`
  (`tendsto_integral_norm_gradient_sub_sq_mul`) and `∫_K |∇w_k − ∇w₀|² → 0` for compact `K ⊆ U`
  (`tendsto_setIntegral_norm_gradient_sub_sq`).

The results are used for blow-ups of variational
solutions (Propositions 3.4 and 3.5, Section 8), for Theorem 9.3, and in Section 5.

## Proof

The first item is the classical interior theory of harmonic functions (locally uniform limits of
harmonic functions are harmonic, with locally uniform convergence of gradients; Gilbarg–Trudinger,
Chapter 2), applied near each point of `{w₀ > 0}`, where `w_k > 0` eventually.

For the energy, the paper uses the energy identity `∫ |∇w|² η = −∫ w ∇w·∇η` for `w_k`
and `w₀`, and the convergence `∫ w_k ∇w_k·∇η → ∫ w₀ ∇w₀·∇η`. We prove the latter by dominated
convergence: on `{w₀ > 0}` the integrand converges pointwise, and on `{w₀ = 0}` it is bounded by
`L |∇η| |w_k| → 0`. This replaces the paper's weak `W^{1,2}` convergence.

For strong convergence we split `U` into `{w₀ > 0}`, where `∇w_k → ∇w₀` pointwise (dominated
convergence), and `{w₀ = 0}`, where `∇w₀ = 0` (a minimum). On the latter,
`∫_{w₀=0} |∇w_k|² η = ∫ |∇w_k|² η − ∫_{w₀>0} |∇w_k|² η → ∫ |∇w₀|² η − ∫_{w₀>0} |∇w₀|² η = 0`.
This avoids the paper's "weak convergence plus convergence of norms" step and any Hilbert-space
argument.

## References

* D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
  DOI 10.1002/cpa.22226; arXiv:2306.10131. Unqualified result and equation numbers in this file
  refer to this paper, in the numbering of arXiv v2.
* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  reprint of the 1998 edition, Classics in Mathematics, Springer, 2001.
-/

open MeasureTheory Metric Set Filter Topology InnerProductSpace
open scoped NNReal RealInnerProductSpace UniformConvergence

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

/-! ### Helpers -/

/-- A function Lipschitz with constant `L` on every ball of an open set `U` has `|∇f| ≤ L`
on `U`. -/
theorem norm_gradient_le_of_lipschitzOnWith_ball {U : Set (Rn n)} (hU : IsOpen U)
    {f : Rn n → ℝ} {L : ℝ≥0} (hL : ∀ x r, ball x r ⊆ U → LipschitzOnWith L f (ball x r))
    {y : Rn n} (hy : y ∈ U) : ‖gradient f y‖ ≤ L := by
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU y hy
  rw [Kernel.norm_gradient_eq]
  exact norm_fderiv_le_of_lipschitzOn ℝ (ball_mem_nhds y hr) (hL y r hrU)

/-- Shifting the index of a locally uniformly convergent sequence. -/
theorem tendstoLocallyUniformlyOn_comp_add_nat {U : Set (Rn n)} {w : ℕ → Rn n → ℝ}
    {w₀ : Rn n → ℝ} (h : TendstoLocallyUniformlyOn w w₀ atTop U) (k₀ : ℕ) :
    TendstoLocallyUniformlyOn (fun j => w (j + k₀)) w₀ atTop U := fun u hu x hx => by
  obtain ⟨t, ht, H⟩ := h u hu x hx
  exact ⟨t, ht, (tendsto_add_atTop_nat k₀).eventually H⟩

/-- A Lipschitz cutoff: `0 ≤ η ≤ 1`, `η = 1` on the compact `K`, compact support in the open
`U ⊇ K`. -/
theorem exists_lipschitz_cutoff {U K : Set (Rn n)} (hU : IsOpen U) (hK : IsCompact K)
    (hKU : K ⊆ U) :
    ∃ η : Rn n → ℝ, (∃ C, LipschitzWith C η) ∧ HasCompactSupport η ∧ tsupport η ⊆ U ∧
      (∀ y, 0 ≤ η y) ∧ (∀ y, η y ≤ 1) ∧ ∀ y ∈ K, η y = 1 := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, ⟨0, LipschitzWith.const 0⟩, HasCompactSupport.zero, by simp, fun _ => le_rfl,
      fun _ => zero_le_one, by simp⟩
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  set η : Rn n → ℝ := fun y => max (1 - infDist y K / δ) 0 with hηdef
  have hsupp : Function.support η ⊆ thickening δ K := by
    intro y hy
    rw [Function.mem_support] at hy
    rw [mem_thickening_iff_infDist_lt hne]
    by_contra hge
    push Not at hge
    apply hy
    rw [hηdef]
    refine max_eq_right ?_
    rw [sub_nonpos, le_div_iff₀ hδ, one_mul]
    exact hge
  have hts : tsupport η ⊆ cthickening δ K :=
    (closure_mono hsupp).trans (closure_thickening_subset_cthickening δ K)
  refine ⟨η, ⟨Real.toNNReal δ⁻¹, LipschitzWith.of_dist_le_mul fun y z => ?_⟩,
    (hK.cthickening).of_isClosed_subset (isClosed_tsupport _) hts, hts.trans hδU,
    fun y => le_max_right _ _, fun y => max_le (by
      have := infDist_nonneg (x := y) (s := K)
      have : 0 ≤ infDist y K / δ := div_nonneg this hδ.le
      linarith) zero_le_one, fun y hy => ?_⟩
  · rw [Real.coe_toNNReal _ (inv_nonneg.2 hδ.le)]
    refine (abs_max_sub_max_le_abs _ _ _).trans ?_
    have h1 : |1 - infDist y K / δ - (1 - infDist z K / δ)| = |infDist y K - infDist z K| / δ := by
      rw [show 1 - infDist y K / δ - (1 - infDist z K / δ) = (infDist z K - infDist y K) / δ by
        ring, abs_div, abs_of_pos hδ, abs_sub_comm]
    rw [h1, div_eq_inv_mul]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hδ.le)
    have := (lipschitz_infDist_pt K).dist_le_mul y z
    rw [Real.dist_eq, NNReal.coe_one, one_mul] at this
    rw [← Real.dist_eq] at this
    exact this
  · simp [hηdef, infDist_zero_of_mem hy]

section Limit

variable {U : Set (Rn n)} {w : ℕ → Rn n → ℝ} {w₀ : Rn n → ℝ} {L : ℝ≥0}
  (hw : ∀ k, IsLipHarmonicPos U (w k))
  (hL : ∀ k x r, ball x r ⊆ U → LipschitzOnWith L (w k) (ball x r))
  (hconv : TendstoLocallyUniformlyOn w w₀ atTop U)

include hw hconv in
theorem nonneg_of_tendstoLocallyUniformlyOn {y : Rn n} (hy : y ∈ U) : 0 ≤ w₀ y :=
  ge_of_tendsto' (hconv.tendsto_at hy) fun k => (hw k).nonneg y hy

include hL hconv in
theorem lipschitzOnWith_of_tendstoLocallyUniformlyOn {x : Rn n} {r : ℝ} (hr : ball x r ⊆ U) :
    LipschitzOnWith L w₀ (ball x r) :=
  LipschitzOnWith.of_dist_le_mul fun y hy z hz =>
    le_of_tendsto' ((hconv.tendsto_at (hr hy)).dist (hconv.tendsto_at (hr hz))) fun k =>
      (hL k x r hr).dist_le_mul y hy z hz

include hw hconv in
theorem continuousOn_of_tendstoLocallyUniformlyOn : ContinuousOn w₀ U :=
  hconv.continuousOn (.of_forall fun k => (hw k).continuousOn)

include hw hconv in
/-- Near a point where `w₀ > 0`, eventually `w_k > 0`. -/
theorem eventually_pos_of_tendstoLocallyUniformlyOn {y : Rn n} (hy : y ∈ U) (hpos : 0 < w₀ y) :
    ∃ δ > 0, ball y δ ⊆ U ∧ ∀ᶠ k in atTop, ∀ z ∈ ball y δ, 0 < w k z := by
  have hU := (hw 0).isOpen
  obtain ⟨t, ht, H⟩ := Metric.tendstoLocallyUniformlyOn_iff.1 hconv (w₀ y / 2) (by linarith) y hy
  rw [hU.nhdsWithin_eq hy] at ht
  have hc : {z | w₀ y / 2 < w₀ z} ∈ 𝓝 y :=
    ((continuousOn_of_tendstoLocallyUniformlyOn hw hconv).continuousAt
      (hU.mem_nhds hy)).preimage_mem_nhds (Ioi_mem_nhds (by linarith))
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.1 (inter_mem (inter_mem ht hc) (hU.mem_nhds hy))
  refine ⟨δ, hδ, fun z hz => (hsub hz).2, H.mono fun k hk z hz => ?_⟩
  have h1 := hk z (hsub hz).1.1
  have h2 : w₀ y / 2 < w₀ z := (hsub hz).1.2
  rw [Real.dist_eq] at h1
  have := le_abs_self (w₀ z - w k z)
  linarith

include hw hconv in
/-- Interior estimates near a point of `{w₀ > 0}`: `w₀` is harmonic there and `∇w_k → ∇w₀`
locally uniformly on a ball around it. -/
theorem exists_ball_harmonic_of_tendstoLocallyUniformlyOn {y : Rn n} (hy : y ∈ U)
    (hpos : 0 < w₀ y) :
    ∃ δ > 0, ball y δ ⊆ U ∧ (∀ z ∈ ball y δ, HarmonicAt w₀ z) ∧ ∃ k₀ : ℕ,
      TendstoLocallyUniformlyOn (fun j => gradient (w (j + k₀))) (gradient w₀) atTop
        (ball y δ) := by
  obtain ⟨δ, hδ, hδU, hev⟩ := eventually_pos_of_tendstoLocallyUniformlyOn hw hconv hy hpos
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 hev
  have hF : ∀ j, ∀ z ∈ ball y δ, HarmonicAt (w (j + k₀)) z := fun j z hz =>
    (hw (j + k₀)).harmonicAt z (hδU hz) (hk₀ (j + k₀) (Nat.le_add_left k₀ j) z hz)
  obtain ⟨h1, h2⟩ := Registry.harmonicAt_of_tendstoLocallyUniformlyOn isOpen_ball hF
    ((tendstoLocallyUniformlyOn_comp_add_nat hconv k₀).mono hδU)
  exact ⟨δ, hδ, hδU, h1, k₀, h2⟩

include hw hconv in
/-- `∇w_k(y) → ∇w₀(y)` at every `y ∈ U` with `w₀(y) > 0`. -/
theorem tendsto_gradient_of_tendstoLocallyUniformlyOn {y : Rn n} (hy : y ∈ U)
    (hpos : 0 < w₀ y) : Tendsto (fun k => gradient (w k) y) atTop (𝓝 (gradient w₀ y)) := by
  obtain ⟨δ, hδ, -, -, k₀, h⟩ := exists_ball_harmonic_of_tendstoLocallyUniformlyOn hw hconv hy hpos
  exact (tendsto_add_atTop_iff_nat k₀).1 (h.tendsto_at (mem_ball_self hδ))

include hw hL hconv in
/-- **Blow-up limits** (proof of Proposition 3.5): a locally uniform limit of uniformly Lipschitz
functions harmonic on their positivity sets has the same properties. -/
theorem IsLipHarmonicPos.of_tendstoLocallyUniformlyOn : IsLipHarmonicPos U w₀ where
  isOpen := (hw 0).isOpen
  nonneg _ hy := nonneg_of_tendstoLocallyUniformlyOn hw hconv hy
  lipschitzOnWith := ⟨L, fun _ _ hr => lipschitzOnWith_of_tendstoLocallyUniformlyOn hL hconv hr⟩
  harmonicAt y hy hpos := by
    obtain ⟨δ, hδ, -, h, -⟩ := exists_ball_harmonic_of_tendstoLocallyUniformlyOn hw hconv hy hpos
    exact h y (mem_ball_self hδ)

end Limit

/-! ### Convergence of the energy and strong convergence of gradients -/

section Strong

variable {U : Set (Rn n)} {w : ℕ → Rn n → ℝ} {w₀ : Rn n → ℝ} {L : ℝ≥0}
  (hw : ∀ k, IsLipHarmonicPos U (w k))
  (hL : ∀ k x r, ball x r ⊆ U → LipschitzOnWith L (w k) (ball x r))
  (hconv : TendstoLocallyUniformlyOn w w₀ atTop U)
  {η : Rn n → ℝ} (hη : ∃ C, LipschitzWith C η) (hηc : HasCompactSupport η)
  (hηU : tsupport η ⊆ U)

include hw hL hconv in
theorem norm_gradient_le_of_tendstoLocallyUniformlyOn {y : Rn n} (hy : y ∈ U) :
    ‖gradient w₀ y‖ ≤ L :=
  norm_gradient_le_of_lipschitzOnWith_ball (hw 0).isOpen
    (fun _ _ hr => lipschitzOnWith_of_tendstoLocallyUniformlyOn hL hconv hr) hy

include hw hL hconv hη hηc hηU in
/-- `∫ w_k ∇w_k·∇η → ∫ w₀ ∇w₀·∇η` (dominated convergence). -/
theorem tendsto_integral_mul_inner_gradient :
    Tendsto (fun k => ∫ y, w k y * ⟪gradient (w k) y, gradient η y⟫) atTop
      (𝓝 (∫ y, w₀ y * ⟪gradient w₀ y, gradient η y⟫)) := by
  obtain ⟨Cη, hCη⟩ := hη
  set K := tsupport η
  have hK : IsCompact K := hηc
  have hU := (hw 0).isOpen
  have hgη : ∀ y, ‖gradient η y‖ ≤ Cη := Kernel.norm_gradient_le_of_lipschitz hCη
  have hgη0 : ∀ y ∉ K, gradient η y = 0 := fun y hy =>
    Kernel.gradient_eq_zero_of_notMem_tsupport hy
  have hgw : ∀ k, ∀ y ∈ U, ‖gradient (w k) y‖ ≤ L := fun k y hy =>
    norm_gradient_le_of_lipschitzOnWith_ball hU (hL k) hy
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
    ((continuousOn_of_tendstoLocallyUniformlyOn hw hconv).mono hηU)
  have hunif := Metric.tendstoUniformlyOn_iff.1
    ((tendstoLocallyUniformlyOn_iff_forall_isCompact hU).1 hconv K hηU hK) 1 one_pos
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 hunif
  have hwb : ∀ k ≥ k₀, ∀ y ∈ K, |w k y| ≤ M + 1 := by
    intro k hk y hy
    have h1 := hk₀ k hk y hy
    have h2 := hM y hy
    rw [Real.dist_eq] at h1
    rw [Real.norm_eq_abs] at h2
    have := abs_sub_abs_le_abs_sub (w k y) (w₀ y)
    rw [abs_sub_comm] at h1
    linarith
  have hinner : ∀ k, ∀ y ∈ K, |⟪gradient (w k) y, gradient η y⟫| ≤ L * Cη := fun k y hy =>
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul (hgw k y (hηU hy)) (hgη y) (norm_nonneg _) L.2)
  refine (tendsto_add_atTop_iff_nat k₀).1 ?_
  refine Kernel.tendsto_integral_of_isCompact hK
    (G := fun j y => w (j + k₀) y * ⟪gradient (w (j + k₀)) y, gradient η y⟫)
    (g := fun y => w₀ y * ⟪gradient w₀ y, gradient η y⟫)
    (fun j y hy => by simp [hgη0 y hy]) (fun y hy => by simp [hgη0 y hy])
    (fun j => (((hw (j + k₀)).continuousOn.mono hηU).aestronglyMeasurable
      hK.measurableSet).mul
        ((measurable_gradient _).inner (measurable_gradient η)).aestronglyMeasurable)
    (B := (M + 1) * (L * Cη)) (fun j y hy => ?_) (fun y hy => ?_)
  · rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hwb (j + k₀) (Nat.le_add_left k₀ j) y hy) (hinner _ y hy) (abs_nonneg _)
      ((abs_nonneg _).trans (hwb (j + k₀) (Nat.le_add_left k₀ j) y hy))
  · change Tendsto (fun j => w (j + k₀) y * ⟪gradient (w (j + k₀)) y, gradient η y⟫) atTop
      (𝓝 (w₀ y * ⟪gradient w₀ y, gradient η y⟫))
    have hyU := hηU hy
    have hw_lim := (hconv.tendsto_at hyU).comp (tendsto_add_atTop_nat k₀)
    by_cases hp : 0 < w₀ y
    · exact hw_lim.mul
        (((tendsto_gradient_of_tendstoLocallyUniformlyOn hw hconv hyU hp).comp
          (tendsto_add_atTop_nat k₀)).inner tendsto_const_nhds)
    · have h0 : w₀ y = 0 := le_antisymm (not_lt.1 hp)
        (nonneg_of_tendstoLocallyUniformlyOn hw hconv hyU)
      rw [h0, zero_mul]
      refine squeeze_zero_norm (fun j => ?_) (by
        simpa [h0] using hw_lim.abs.mul_const ((L : ℝ) * Cη))
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (hinner _ y hy) (abs_nonneg _)

include hw hL hconv hη hηc hηU in
/-- **Convergence of the energy** (proof of Proposition 3.5): `∫ |∇w_k|² η → ∫ |∇w₀|² η`. -/
theorem tendsto_integral_norm_gradient_sq_mul :
    Tendsto (fun k => ∫ y, ‖gradient (w k) y‖ ^ 2 * η y) atTop
      (𝓝 (∫ y, ‖gradient w₀ y‖ ^ 2 * η y)) := by
  have h0 := IsLipHarmonicPos.of_tendstoLocallyUniformlyOn hw hL hconv
  rw [h0.integral_norm_gradient_sq_mul hη hηc hηU]
  simp_rw [fun k => (hw k).integral_norm_gradient_sq_mul hη hηc hηU]
  exact (tendsto_integral_mul_inner_gradient hw hL hconv hη hηc hηU).neg

include hw hL hconv hη hηc hηU in
/-- **Strong convergence of gradients** (proof of Proposition 3.5), weighted form:
`∫ |∇w_k − ∇w₀|² η → 0`. -/
theorem tendsto_integral_norm_gradient_sub_sq_mul :
    Tendsto (fun k => ∫ y, ‖gradient (w k) y - gradient w₀ y‖ ^ 2 * η y) atTop (𝓝 0) := by
  have h0 := IsLipHarmonicPos.of_tendstoLocallyUniformlyOn hw hL hconv
  set K := tsupport η
  have hK : IsCompact K := hηc
  have hU := (hw 0).isOpen
  set P := U ∩ {y | 0 < w₀ y} with hPdef
  have hP : MeasurableSet P := h0.isOpen_pos.measurableSet
  have hη0 : ∀ y ∉ K, η y = 0 := fun y hy => image_eq_zero_of_notMem_tsupport hy
  obtain ⟨A, hA⟩ := hη.elim fun C hC => hC.continuous.bounded_above_of_compact_support hηc
  have hηm : Measurable η := hη.elim fun C hC => hC.continuous.measurable
  have hgw : ∀ k, ∀ y ∈ U, ‖gradient (w k) y‖ ≤ L := fun k y hy =>
    norm_gradient_le_of_lipschitzOnWith_ball hU (hL k) hy
  have hgw0 : ∀ y ∈ U, ‖gradient w₀ y‖ ≤ L := fun y hy =>
    norm_gradient_le_of_tendstoLocallyUniformlyOn hw hL hconv hy
  have hsub : ∀ k, ∀ y ∈ U, ‖gradient (w k) y - gradient w₀ y‖ ^ 2 ≤ (2 * L) ^ 2 := by
    intro k y hy
    refine pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans ?_) 2
    linarith [hgw k y hy, hgw0 y hy]
  have hsq : ∀ k, ∀ y ∈ U, ‖gradient (w k) y‖ ^ 2 ≤ (2 * L) ^ 2 := fun k y hy =>
    pow_le_pow_left₀ (norm_nonneg _) ((hgw k y hy).trans (by linarith [L.coe_nonneg])) 2
  have hsq0 : ∀ y ∈ U, ‖gradient w₀ y‖ ^ 2 ≤ (2 * L) ^ 2 := fun y hy =>
    pow_le_pow_left₀ (norm_nonneg _) ((hgw0 y hy).trans (by linarith [L.coe_nonneg])) 2
  -- boundedness of `F η` on `K` when `0 ≤ F ≤ (2L)²` on `U`
  have hbd : ∀ (F : Rn n → ℝ), (∀ y ∈ U, 0 ≤ F y ∧ F y ≤ (2 * L) ^ 2) →
      ∀ y ∈ K, ‖F y * η y‖ ≤ (2 * L) ^ 2 * A := by
    intro F hF y hy
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hF y (hηU hy)).1]
    exact mul_le_mul (hF y (hηU hy)).2 (hA y) (norm_nonneg _) (by positivity)
  have hbdP : ∀ (F : Rn n → ℝ), (∀ y ∈ U, 0 ≤ F y ∧ F y ≤ (2 * L) ^ 2) →
      ∀ y ∈ K, ‖P.indicator (fun y => F y * η y) y‖ ≤ (2 * L) ^ 2 * A := by
    intro F hF y hy
    by_cases hyP : y ∈ P
    · rw [indicator_of_mem hyP]; exact hbd F hF y hy
    · rw [indicator_of_notMem hyP, norm_zero]
      exact mul_nonneg (by positivity) ((norm_nonneg _).trans (hA y))
  have hmeasG : ∀ k, Measurable fun y => ‖gradient (w k) y - gradient w₀ y‖ ^ 2 * η y :=
    fun k => (((measurable_gradient _).sub (measurable_gradient _)).norm.pow_const 2).mul hηm
  have hmeasD : ∀ k, Measurable fun y => ‖gradient (w k) y‖ ^ 2 * η y :=
    fun k => ((measurable_gradient _).norm.pow_const 2).mul hηm
  have hmeasD0 : Measurable fun y => ‖gradient w₀ y‖ ^ 2 * η y :=
    ((measurable_gradient _).norm.pow_const 2).mul hηm
  -- (a) the part on `P` tends to `0`
  have hGlim : Tendsto (fun k => ∫ y, P.indicator
      (fun y => ‖gradient (w k) y - gradient w₀ y‖ ^ 2 * η y) y) atTop
      (𝓝 (∫ _y : Rn n, (0 : ℝ))) := by
    refine Kernel.tendsto_integral_of_isCompact hK
      (fun k y hy => by simp [hη0 y hy]) (fun _ _ => rfl)
      (fun k => ((hmeasG k).indicator hP).aestronglyMeasurable)
      (fun k => hbdP _ fun y hy => ⟨sq_nonneg _, hsub k y hy⟩) (fun y hy => ?_)
    by_cases hyP : y ∈ P
    · simp only [indicator_of_mem hyP]
      have := (((tendsto_gradient_of_tendstoLocallyUniformlyOn hw hconv hyP.1 hyP.2).sub_const
        (gradient w₀ y)).norm.pow 2).mul_const (η y)
      simpa using this
    · simp only [indicator_of_notMem hyP]
      exact tendsto_const_nhds
  -- (b) the energy on `P` converges
  have hDlim : Tendsto (fun k => ∫ y, P.indicator (fun y => ‖gradient (w k) y‖ ^ 2 * η y) y)
      atTop (𝓝 (∫ y, P.indicator (fun y => ‖gradient w₀ y‖ ^ 2 * η y) y)) := by
    refine Kernel.tendsto_integral_of_isCompact hK
      (fun k y hy => by simp [hη0 y hy]) (fun y hy => by simp [hη0 y hy])
      (fun k => ((hmeasD k).indicator hP).aestronglyMeasurable)
      (fun k => hbdP _ fun y hy => ⟨sq_nonneg _, hsq k y hy⟩) (fun y hy => ?_)
    by_cases hyP : y ∈ P
    · simp only [indicator_of_mem hyP]
      exact (((tendsto_gradient_of_tendstoLocallyUniformlyOn hw hconv hyP.1 hyP.2).norm.pow
        2).mul_const (η y))
    · simp only [indicator_of_notMem hyP]
      exact tendsto_const_nhds
  -- off `P`, `∇w₀ = 0` wherever `η ≠ 0`
  have hoff : ∀ y ∉ P, gradient w₀ y = 0 ∨ η y = 0 := by
    intro y hyP
    by_cases hyU : y ∈ U
    · left
      have hle : w₀ y ≤ 0 := not_lt.1 fun hp => hyP ⟨hyU, hp⟩
      exact h0.gradient_eq_zero_of_eq_zero hyU (le_antisymm hle (h0.nonneg y hyU))
    · exact Or.inr (hη0 y fun hy => hyU (hηU hy))
  -- (c) pointwise decomposition
  have hdec : ∀ k y, ‖gradient (w k) y - gradient w₀ y‖ ^ 2 * η y =
      P.indicator (fun y => ‖gradient (w k) y - gradient w₀ y‖ ^ 2 * η y) y +
        (‖gradient (w k) y‖ ^ 2 * η y -
          P.indicator (fun y => ‖gradient (w k) y‖ ^ 2 * η y) y) := by
    intro k y
    by_cases hyP : y ∈ P
    · simp only [indicator_of_mem hyP]; ring
    · simp only [indicator_of_notMem hyP]
      rcases hoff y hyP with h | h
      · rw [h, sub_zero]; ring
      · rw [h]; ring
  -- (d) the limit energy lives on `P`
  have hD0 : (∫ y, P.indicator (fun y => ‖gradient w₀ y‖ ^ 2 * η y) y) =
      ∫ y, ‖gradient w₀ y‖ ^ 2 * η y := by
    refine integral_congr_ae (.of_forall fun y => ?_)
    by_cases hyP : y ∈ P
    · simp only [indicator_of_mem hyP]
    · simp only [indicator_of_notMem hyP]
      rcases hoff y hyP with h | h
      · rw [h]; simp
      · rw [h, mul_zero]
  -- integrability
  have hint : ∀ (F : Rn n → ℝ), Measurable F →
      (∀ y ∈ U, 0 ≤ F y ∧ F y ≤ (2 * L) ^ 2) → Integrable fun y => F y * η y := by
    intro F hFm hF
    exact Kernel.integrable_of_bound_of_isCompact hK (hFm.mul hηm).aestronglyMeasurable
      (hbd F hF) fun y hy => by simp [hη0 y hy]
  have hintP : ∀ (F : Rn n → ℝ), Measurable F →
      (∀ y ∈ U, 0 ≤ F y ∧ F y ≤ (2 * L) ^ 2) → Integrable (P.indicator fun y => F y * η y) :=
    fun F hFm hF => (hint F hFm hF).indicator hP
  have hmain : ∀ k, ∫ y, ‖gradient (w k) y - gradient w₀ y‖ ^ 2 * η y =
      (∫ y, P.indicator (fun y => ‖gradient (w k) y - gradient w₀ y‖ ^ 2 * η y) y) +
        ((∫ y, ‖gradient (w k) y‖ ^ 2 * η y) -
          ∫ y, P.indicator (fun y => ‖gradient (w k) y‖ ^ 2 * η y) y) := by
    intro k
    have hG := hintP _ (((measurable_gradient _).sub (measurable_gradient _)).norm.pow_const 2)
      fun y hy => ⟨sq_nonneg _, hsub k y hy⟩
    have hE := hint _ ((measurable_gradient (w k)).norm.pow_const 2)
      fun y hy => ⟨sq_nonneg _, hsq k y hy⟩
    have hDk := hintP _ ((measurable_gradient (w k)).norm.pow_const 2)
      fun y hy => ⟨sq_nonneg _, hsq k y hy⟩
    rw [integral_congr_ae (μ := volume) (Filter.Eventually.of_forall (hdec k)),
      ← integral_sub hE hDk]
    exact integral_add hG (hE.sub hDk)
  simp_rw [hmain]
  have hE := tendsto_integral_norm_gradient_sq_mul hw hL hconv hη hηc hηU
  rw [← hD0] at hE
  have := hGlim.add (hE.sub hDlim)
  simpa using this

include hw hL hconv in
/-- **Strong convergence of gradients in `L²_loc`** (proof of Proposition 3.5): for compact `K ⊆ U`,
`∫_K |∇w_k − ∇w₀|² → 0`. -/
theorem tendsto_setIntegral_norm_gradient_sub_sq {K : Set (Rn n)} (hK : IsCompact K)
    (hKU : K ⊆ U) :
    Tendsto (fun k => ∫ y in K, ‖gradient (w k) y - gradient w₀ y‖ ^ 2) atTop (𝓝 0) := by
  have hU := (hw 0).isOpen
  obtain ⟨η, hη, hηc, hηU, hη0, hη1, hηK⟩ := exists_lipschitz_cutoff hU hK hKU
  have hlim := tendsto_integral_norm_gradient_sub_sq_mul hw hL hconv hη hηc hηU
  have hηm : Measurable η := hη.elim fun C hC => hC.continuous.measurable
  have hgw : ∀ k, ∀ y ∈ U, ‖gradient (w k) y‖ ≤ L := fun k y hy =>
    norm_gradient_le_of_lipschitzOnWith_ball hU (hL k) hy
  have hgw0 : ∀ y ∈ U, ‖gradient w₀ y‖ ≤ L := fun y hy =>
    norm_gradient_le_of_tendstoLocallyUniformlyOn hw hL hconv hy
  have hsub : ∀ k, ∀ y ∈ U, ‖gradient (w k) y - gradient w₀ y‖ ^ 2 ≤ (2 * L) ^ 2 := by
    intro k y hy
    refine pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans ?_) 2
    linarith [hgw k y hy, hgw0 y hy]
  have hm : ∀ k, Measurable fun y => ‖gradient (w k) y - gradient w₀ y‖ ^ 2 := fun k =>
    ((measurable_gradient _).sub (measurable_gradient _)).norm.pow_const 2
  refine squeeze_zero (fun k => setIntegral_nonneg hK.measurableSet fun _ _ => sq_nonneg _)
    (fun k => ?_) hlim
  have hKt : IsCompact (tsupport η) := hηc
  have hI1 : Integrable (K.indicator fun y => ‖gradient (w k) y - gradient w₀ y‖ ^ 2) :=
    (IntegrableOn.of_bound hK.measure_lt_top (hm k).aestronglyMeasurable ((2 * L) ^ 2)
      ((ae_restrict_iff' hK.measurableSet).2 (.of_forall fun y hy => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hsub k y (hKU hy)))).integrable_indicator hK.measurableSet
  have hI2 : Integrable fun y => ‖gradient (w k) y - gradient w₀ y‖ ^ 2 * η y :=
    Kernel.integrable_of_bound_of_isCompact hKt ((hm k).mul hηm).aestronglyMeasurable
      (M := (2 * L) ^ 2) (fun y hy => by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
          abs_of_nonneg (hη0 y)]
        calc _ ≤ (2 * L : ℝ) ^ 2 * 1 :=
              mul_le_mul (hsub k y (hηU hy)) (hη1 y) (hη0 y) (by positivity)
          _ = _ := mul_one _)
      fun y hy => by simp [image_eq_zero_of_notMem_tsupport hy]
  rw [← integral_indicator hK.measurableSet]
  refine integral_mono hI1 hI2 fun y => ?_
  by_cases hy : y ∈ K
  · rw [indicator_of_mem hy, hηK y hy, mul_one]
  · rw [indicator_of_notMem hy]
    exact mul_nonneg (sq_nonneg _) (hη0 y)

end Strong

/-! ### Arzelà–Ascoli extraction -/

/-- **Arzelà–Ascoli** for uniformly Lipschitz functions on `ℝⁿ` that are bounded at `0`: some
subsequence converges locally uniformly. -/
theorem exists_subseq_tendstoLocallyUniformly_of_lipschitzWith {g : ℕ → Rn n → ℝ} {L : ℝ≥0}
    (hg : ∀ k, LipschitzWith L (g k)) {M : ℝ} (hM : ∀ k, |g k 0| ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g₀ : Rn n → ℝ,
      TendstoLocallyUniformly (fun k => g (φ k)) g₀ atTop := by
  obtain ⟨𝔖, h𝔖⟩ : ∃ 𝔖 : Set (Set (Rn n)), 𝔖 = {K | IsCompact K} := ⟨_, rfl⟩
  have hmem : ∀ K, K ∈ 𝔖 ↔ IsCompact K := fun K => by rw [h𝔖]; rfl
  have : IsCountablyGenerated (uniformity (Rn n →ᵤ[𝔖] ℝ)) :=
    UniformOnFun.isCountablyGenerated_uniformity 𝔖
      (t := fun m : ℕ => closedBall (0 : Rn n) m)
      (fun m => (hmem _).2 (isCompact_closedBall _ _))
      (fun a b hab => closedBall_subset_closedBall (by exact_mod_cast hab))
      (fun K hK => by
        obtain ⟨r, hr⟩ := (IsCompact.isBounded ((hmem K).1 hK)).subset_closedBall (0 : Rn n)
        obtain ⟨m, hm⟩ := exists_nat_ge r
        exact ⟨m, hr.trans (closedBall_subset_closedBall hm)⟩)
  set x : ℕ → (Rn n →ᵤ[𝔖] ℝ) := fun k => UniformOnFun.ofFun 𝔖 (g k)
  set s : Set (Rn n →ᵤ[𝔖] ℝ) := range x
  have hid : (UniformOnFun.ofFun 𝔖 ∘ UniformOnFun.toFun 𝔖 : (Rn n →ᵤ[𝔖] ℝ) → _) = id := rfl
  have hcl : IsCompact (closure s) := by
    refine ArzelaAscoli.isCompact_closure_of_isClosedEmbedding (F := UniformOnFun.toFun 𝔖)
      (fun K hK => (hmem K).1 hK) (by rw [hid]; exact IsClosedEmbedding.id) (fun K _ => ?_)
      (fun K _ y _ => ?_)
    · have hL : ∀ c : s, LipschitzWith L
          ((UniformOnFun.toFun 𝔖 ∘ (Subtype.val : s → (Rn n →ᵤ[𝔖] ℝ))) c) := by
        rintro ⟨_, k, rfl⟩
        exact hg k
      exact ((LipschitzWith.uniformEquicontinuous _ L hL).equicontinuous).equicontinuousOn K
    · refine ⟨closedBall 0 (M + L * ‖y‖), isCompact_closedBall _ _, ?_⟩
      rintro _ ⟨k, rfl⟩
      rw [mem_closedBall, Real.dist_eq, sub_zero]
      have h1 := (hg k).dist_le_mul y 0
      rw [Real.dist_eq, dist_zero_right] at h1
      have h2 := abs_sub_abs_le_abs_sub (g k y) (g k 0)
      change |g k y| ≤ M + L * ‖y‖
      linarith [hM k]
  obtain ⟨a, -, φ, hφ, hlim⟩ := hcl.tendsto_subseq (x := x) fun k => subset_closure ⟨k, rfl⟩
  refine ⟨φ, hφ, UniformOnFun.toFun 𝔖 a, ?_⟩
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  exact fun K hK => (UniformOnFun.tendsto_iff_tendstoUniformlyOn.1 hlim) K ((hmem K).2 hK)

/-- **Blow-up extraction** (Arzelà–Ascoli, as in the proof of Proposition 3.5). Let `f_k` be
`L`-Lipschitz on `B_{ρ_k}`, `ρ_k → ∞`, `ρ_k > 0`, with `f_k(0)` bounded. Then a subsequence
converges locally uniformly on `ℝⁿ` to an `L`-Lipschitz function. -/
theorem exists_blowup_subseq {f : ℕ → Rn n → ℝ} {L : ℝ≥0} {ρ : ℕ → ℝ}
    (hρ : Tendsto ρ atTop atTop) (hρ0 : ∀ k, 0 < ρ k)
    (hLip : ∀ k, LipschitzOnWith L (f k) (ball 0 (ρ k))) {M : ℝ} (hM : ∀ k, |f k 0| ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f₀ : Rn n → ℝ, LipschitzWith L f₀ ∧
      TendstoLocallyUniformly (fun k => f (φ k)) f₀ atTop := by
  choose g hg hfg using fun k => (hLip k).extend_real
  have hg0 : ∀ k, |g k 0| ≤ M := fun k => by
    rw [← hfg k (mem_ball_self (hρ0 k))]; exact hM k
  obtain ⟨φ, hφ, g₀, hlim⟩ := exists_subseq_tendstoLocallyUniformly_of_lipschitzWith hg hg0
  refine ⟨φ, hφ, g₀, LipschitzWith.of_dist_le_mul fun y z => le_of_tendsto'
    (((tendstoLocallyUniformlyOn_univ.2 hlim).tendsto_at (mem_univ y)).dist
      ((tendstoLocallyUniformlyOn_univ.2 hlim).tendsto_at (mem_univ z)))
      fun k => (hg (φ k)).dist_le_mul y z, ?_⟩
  rw [tendstoLocallyUniformly_iff_forall_isCompact] at hlim ⊢
  intro K hK
  obtain ⟨r, hr⟩ := (IsCompact.isBounded hK).subset_ball (0 : Rn n)
  refine (hlim K hK).congr ?_
  filter_upwards [(hρ.comp hφ.tendsto_atTop).eventually_gt_atTop r] with k hk
  exact fun y hy => (hfg (φ k) (mem_ball.2 ((mem_ball.1 (hr hy)).trans hk))).symm

end InnerVariational
