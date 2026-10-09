/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Defs.VariationalSolutionQ
public import InnerVariational.Kernel.VariationalQ
public import InnerVariational.Kernel.BV
public import InnerVariational.Regular.Viscosity.Classification
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
import InnerVariational.Kernel.Subharmonic
import InnerVariational.Regular.DensityQ
import InnerVariational.Monotonicity.HighestDensityQ

/-!
# Lemma 8.3 with a Lipschitz coefficient: viscosity off `Σ^H`

Lemma 8.3 of D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and
compactness for non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025),
no. 3, DOI 10.1002/cpa.22226; arXiv:2306.10131 (numbering of arXiv v2), for a variational solution
`(u, χ)` on `Ω` with a coefficient `Q`, `QBounds Ω Q L c C'`, and `2 ≤ n`. The paper treats
`Q ≡ 1`. Let `x ∈ Ω ∩ ∂{u > 0}` with `x ∉ Σ^H` (`sigmaHQ`), and let `φ` be smooth with
`φ(x) = 0`.

* If `φ ≤ u` near `x`, then `|∇φ(x)| ≤ Q(x)` (`IsVariationalSolutionQ.norm_gradient_le_of_le`).
* If `u ≤ φ₊` near `x`, then `|∇φ(x)| ≥ Q(x)`
  (`IsVariationalSolutionQ.le_norm_gradient_of_le_max`).

These are the two conclusions of `IsViscositySolutionQ`; the case `Q ≡ 1` is
`Regular/Viscosity/Main.lean`. The file also contains the steps of the proof that do not depend
on the coefficient: the classification of blow-ups touched by a plane
(`Regular.norm_le_one_of_le`, `Regular.one_le_norm_of_le_max`), and the blow-up pair data
(`IsVariationalSolution.blowup_chi_data`).

## Proof

Let `q = Q(x)`. By Lemma 8.1 (`MzeroQ_eq_of_tendsto_rescale_zero`) and `x ∉ Σ^H`, the density
`d` of `{χ = 1}` at `x` satisfies `d < |B_1|` (`M^{q}_x(u; 0+) = q² d`), and some blow-up
`u_{x,r_k} → u₀` is not identically zero; it is one-homogeneous, with
`|{u₀ > 0} ∩ B_1| ≤ d < |B_1|` (`exists_blowup_of_notMem_sigmaHQ`). A subsequence of
`χ_{x,r_k}` converges to `χ₀` with `(u₀, χ₀)` a variational solution on `ℝⁿ` for the constant
coefficient `q` (`exists_blowup_limit_ae`). Then `(u₀/q, χ₀)` is a variational solution with
coefficient `1` (`isVariationalSolutionQ_const_iff`). The touching `φ` gives
`⟪∇φ(x)/q, y⟫ ≤ u₀(y)/q` (resp. `u₀(y)/q ≤ ⟪∇φ(x)/q, y⟫₊`), and the classification for
coefficient `1` gives `|∇φ(x)/q| ≤ 1` (resp. `≥ 1`).

For the classification: `u₀/q = a ⟪y, e⟫₊` with `a > 0` (`eq_mul_max_of_le_max`,
`eq_mul_max_of_le`); from above, `{u₀ > 0}` lies in the half-space `{⟪y, e⟫ > 0}`, so each
component has volume `≤ |B_1|/2` and the equality case of Sperner's inequality (E. Sperner, Jr.,
*Zur Symmetrisierung von Funktionen auf Sphären*, Math. Z. 134 (1973), 317–327) applies; from
below, the component through `e` contains the half-space, it is the half-space
(`connectedComponentIn_eq_halfSpace`), and any further component would add `|B_1|/2`. The
half-space computation (`eq_one_of_halfSpace`) gives `a = 1`.
-/

open MeasureTheory Metric Set Filter Topology InnerProductSpace
open scoped NNReal ENNReal RealInnerProductSpace ContDiff

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

namespace Regular

/-- The difference quotients of a smooth `φ` with `φ(x) = 0` along `r_k → 0+`:
`φ(x + r_k y)/r_k → ⟪∇φ(x), y⟫`. -/
theorem tendsto_div_of_contDiff {φ : Rn n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) {x : Rn n} (hφx : φ x = 0) {r : ℕ → ℝ} (hr : ∀ k, 0 < r k)
    (hr0 : Tendsto r atTop (𝓝 0)) (y : Rn n) :
    Tendsto (fun k => φ (x + r k • y) / r k) atTop (𝓝 ⟪gradient φ x, y⟫) := by
  have hd : HasFDerivAt φ (fderiv ℝ φ x) x := (hφ.differentiable (by simp) x).hasFDerivAt
  have hc : Tendsto (fun k => ‖(r k)⁻¹‖) atTop atTop := by
    have h1 : Tendsto r atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.2 ⟨hr0, .of_forall hr⟩
    refine (tendsto_inv_nhdsGT_zero.comp h1).congr fun k => ?_
    rw [Function.comp_apply, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (hr k))]
  have := hd.lim y hc
  rw [gradient, InnerProductSpace.toDual_symm_apply]
  refine this.congr fun k => ?_
  rw [inv_inv, hφx, sub_zero, smul_eq_mul, div_eq_inv_mul]

/-- **Classification step of Lemma 8.3**, touching from below. Let `u₀ ≥ 0` be Lipschitz,
one-homogeneous, harmonic on `{u₀ > 0}`, with `|{u₀ > 0} ∩ B_1| < |B_1|`, and let `f₀` be a
`{0, 1}`-valued function on `B_1`, equal to `1` on `{u₀ > 0}`, such that the limit domain
variation identity holds on `B_1`. If `⟪p, y⟫ ≤ u₀(y)` for all `y`, then `|p| ≤ 1`. -/
theorem norm_le_one_of_le (hn : 2 ≤ n) {u₀ : Rn n → ℝ}
    {L : ℝ≥0} (hLip : LipschitzWith L u₀) (hnn : ∀ y, 0 ≤ u₀ y)
    (hhom : ∀ t, 0 < t → ∀ y, u₀ (t • y) = t * u₀ y) (hharm : ∀ y, 0 < u₀ y → HarmonicAt u₀ y)
    (hvol : volume.real ({y | 0 < u₀ y} ∩ ball (0 : Rn n) 1) < unitBallVolume n)
    {f₀ : Rn n → ℝ} (hf₀m : Measurable f₀)
    (h01 : ∀ᵐ y ∂(volume.restrict (ball (0 : Rn n) 1)), f₀ y = 0 ∨ f₀ y = 1)
    (hpos : ∀ᵐ y ∂(volume.restrict (ball (0 : Rn n) 1)), 0 < u₀ y → f₀ y = 1)
    (hid : ∀ ξ, IsSmoothTestField (ball (0 : Rn n) 1) ξ →
      (∫ y, Kernel.gradVariation u₀ ξ y) + ∫ y, f₀ y * divergence ξ y = 0)
    {p : Rn n} (htouch : ∀ y, ⟪p, y⟫ ≤ u₀ y) : ‖p‖ ≤ 1 := by
  by_cases hp : p = 0
  · rw [hp, norm_zero]; exact zero_le_one
  set β := ‖p‖ with hβdef
  have hβ : 0 < β := norm_pos_iff.2 hp
  set e := β⁻¹ • p with hedef
  have he : ‖e‖ = 1 := by rw [hedef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hβ.ne']
  have hpe : ∀ y, ⟪p, y⟫ = β * ⟪y, e⟫ := fun y => by
    rw [hedef, real_inner_smul_right, real_inner_comm, ← mul_assoc, mul_inv_cancel₀ hβ.ne',
      one_mul]
  have hee : ⟪e, e⟫ = 1 := by rw [real_inner_self_eq_norm_sq, he, one_pow]
  obtain ⟨a, ha, hu₀⟩ := Regular.eq_mul_max_of_le hn hLip hnn hhom hharm hvol he hβ
    (fun y => (hpe y) ▸ htouch y)
  have hu₀' : u₀ = fun z => a * max ⟪z, e⟫ 0 := funext hu₀
  have ha1 : a = 1 := by
    refine Regular.eq_one_of_halfSpace he ha hf₀m h01 ?_ fun ξ hξ => ?_
    · filter_upwards [hpos] with y hy hye
      exact hy (by rw [hu₀ y, max_eq_left hye.le]; exact mul_pos ha hye)
    · have := hid ξ hξ
      rwa [hu₀'] at this
  have := htouch e
  rw [hpe e, hee, mul_one, hu₀ e, hee, max_eq_left zero_le_one, ha1, mul_one] at this
  exact this

/-- **Classification step of Lemma 8.3**, touching from above. Let `u₀ ≥ 0` be Lipschitz,
one-homogeneous, harmonic on `{u₀ > 0}` and not identically zero, and let `f₀` be a
`{0, 1}`-valued function on `B_1`, equal to `1` on `{u₀ > 0}`, such that the limit domain
variation identity holds on `B_1`. If `u₀(y) ≤ ⟪p, y⟫₊` for all `y`, then `|p| ≥ 1`. -/
theorem one_le_norm_of_le_max (hn : 2 ≤ n) {u₀ : Rn n → ℝ}
    {L : ℝ≥0} (hLip : LipschitzWith L u₀) (hnn : ∀ y, 0 ≤ u₀ y)
    (hhom : ∀ t, 0 < t → ∀ y, u₀ (t • y) = t * u₀ y) (hharm : ∀ y, 0 < u₀ y → HarmonicAt u₀ y)
    {y₀ : Rn n} (hy₀ : 0 < u₀ y₀) {f₀ : Rn n → ℝ} (hf₀m : Measurable f₀)
    (h01 : ∀ᵐ y ∂(volume.restrict (ball (0 : Rn n) 1)), f₀ y = 0 ∨ f₀ y = 1)
    (hpos : ∀ᵐ y ∂(volume.restrict (ball (0 : Rn n) 1)), 0 < u₀ y → f₀ y = 1)
    (hid : ∀ ξ, IsSmoothTestField (ball (0 : Rn n) 1) ξ →
      (∫ y, Kernel.gradVariation u₀ ξ y) + ∫ y, f₀ y * divergence ξ y = 0)
    {p : Rn n} (htouch : ∀ y, u₀ y ≤ max ⟪p, y⟫ 0) : 1 ≤ ‖p‖ := by
  by_cases hp : p = 0
  · exfalso
    have := htouch y₀
    rw [hp, inner_zero_left, max_self] at this
    linarith
  set β := ‖p‖ with hβdef
  have hβ : 0 < β := norm_pos_iff.2 hp
  set e := β⁻¹ • p with hedef
  have he : ‖e‖ = 1 := by rw [hedef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hβ.ne']
  have hpe : ∀ y, ⟪p, y⟫ = β * ⟪y, e⟫ := fun y => by
    rw [hedef, real_inner_smul_right, real_inner_comm, ← mul_assoc, mul_inv_cancel₀ hβ.ne',
      one_mul]
  have hee : ⟪e, e⟫ = 1 := by rw [real_inner_self_eq_norm_sq, he, one_pow]
  obtain ⟨a, ha, hu₀⟩ := Regular.eq_mul_max_of_le_max hn hLip hnn hhom hharm hy₀ he hβ
    (fun y => (hpe y) ▸ htouch y)
  have hu₀' : u₀ = fun z => a * max ⟪z, e⟫ 0 := funext hu₀
  have ha1 : a = 1 := by
    refine Regular.eq_one_of_halfSpace he ha hf₀m h01 ?_ fun ξ hξ => ?_
    · filter_upwards [hpos] with y hy hye
      exact hy (by rw [hu₀ y, max_eq_left hye.le]; exact mul_pos ha hye)
    · have := hid ξ hξ
      rwa [hu₀'] at this
  have := htouch e
  rw [hpe e, hee, mul_one, hu₀ e, hee, max_eq_left zero_le_one, ha1, mul_one,
    max_eq_left hβ.le] at this
  exact this

end Regular

namespace IsVariationalSolution

variable {C : ℝ≥0}

/-- The data of a blow-up pair used in the proof of Lemma 8.3, for a variational solution
`(u₀, χ₀)` on `ℝⁿ`: `χ₀` is measurable, `{0, 1}`-valued, equal to `1` a.e. on `{u₀ > 0}`, and the
limit domain variation identity `∫ (|∇u₀|² div ξ − 2 ∇u₀·Dξ ∇u₀) + ∫ χ₀ div ξ = 0` holds for
`ξ ∈ C^∞_c(B_1; ℝⁿ)`. -/
theorem blowup_chi_data {u₀ χ₀ : Rn n → ℝ} (h₀ : IsVariationalSolution univ C u₀ χ₀) :
    Measurable χ₀ ∧
      (∀ᵐ y ∂(volume.restrict (ball (0 : Rn n) 1)), χ₀ y = 0 ∨ χ₀ y = 1) ∧
      (∀ᵐ y ∂(volume.restrict (ball (0 : Rn n) 1)), 0 < u₀ y → χ₀ y = 1) ∧
      ∀ ξ, IsSmoothTestField (ball (0 : Rn n) 1) ξ →
        (∫ y, Kernel.gradVariation u₀ ξ y) + ∫ y, χ₀ y * divergence ξ y = 0 := by
  refine ⟨by simpa using h₀.measurable_chi, .of_forall fun y => h₀.chi_mem y trivial,
    ae_restrict_of_ae (h₀.ae_chi_eq_one.mono fun y hy => hy trivial), fun ξ hξ => ?_⟩
  rw [h₀.integral_chi_mul_divergence_eq (hξ.isLipTestField.mono (subset_univ _))]
  ring

end IsVariationalSolution

namespace IsVariationalSolutionQ

variable {Ω : Set (Rn n)} {C : ℝ≥0} {Q u χ : Rn n → ℝ} {x : Rn n} {L : ℝ≥0} {c C' : ℝ}

/-- A variational solution on `ℝⁿ` is `C_V`-Lipschitz on `ℝⁿ`. -/
theorem lipschitzWith_of_univ (h : IsVariationalSolutionQ univ C Q u χ) : LipschitzWith C u := by
  refine LipschitzWith.of_dist_le_mul fun y z => ?_
  have hy : y ∈ ball (0 : Rn n) (‖y‖ + ‖z‖ + 1) := by
    rw [mem_ball_zero_iff]; linarith [norm_nonneg z]
  have hz : z ∈ ball (0 : Rn n) (‖y‖ + ‖z‖ + 1) := by
    rw [mem_ball_zero_iff]; linarith [norm_nonneg y]
  exact (h.lipschitzOnWith 0 _ (subset_univ _)).dist_le_mul y hy z hz

/-- The blow-up data at a free boundary point `x ∉ Σ^H` (proof of Lemma 8.3): a blow-up
`u_{x,r_k} → u₀` that is one-homogeneous, not identically zero (Lemma 8.1, last claim), with
`|{u₀ > 0} ∩ B_1| < |B_1|`, and a function `χ₀` such that `(u₀, χ₀)` is a variational solution on
`ℝⁿ` for the constant coefficient `Q(x)`. -/
theorem exists_blowup_of_notMem_sigmaHQ (hn : 2 ≤ n) (hQ : QBounds Ω Q L c C')
    (h : IsVariationalSolutionQ Ω C Q u χ) (hx : x ∈ Ω) (hfr : x ∈ frontier {y | 0 < u y})
    (hS : x ∉ sigmaHQ Ω Q u χ) :
    ∃ r : ℕ → ℝ, (∀ k, 0 < r k) ∧ Tendsto r atTop (𝓝 0) ∧ ∃ u₀ : Rn n → ℝ,
      TendstoLocallyUniformly (fun k => oneHomRescale u x (r k)) u₀ atTop ∧
      (∀ t, 0 < t → ∀ y, u₀ (t • y) = t * u₀ y) ∧ (∃ y, 0 < u₀ y) ∧
      volume.real ({y | 0 < u₀ y} ∩ ball (0 : Rn n) 1) < unitBallVolume n ∧
      ∃ χ₀, IsVariationalSolutionQ univ C (fun _ => Q x) u₀ χ₀ := by
  have : NeZero n := ⟨by omega⟩
  obtain ⟨hcl, hux⟩ := (h.mem_frontier_pos_iff hx).1 hfr
  obtain ⟨d, hdM, hd⟩ := h.exists_MzeroQ_eq_sq_mul hQ hx hux
  have hq2 : 0 < Q x ^ 2 := pow_pos (hQ.pos_of_mem hx) 2
  have hdlt : d < unitBallVolume n := by
    by_contra hge
    push Not at hge
    refine hS ⟨hx, hcl, ?_⟩
    rw [hdM, EReal.coe_le_coe_iff]
    exact mul_le_mul_of_nonneg_left hge hq2.le
  have hr : ∀ k : ℕ, 0 < 1 / ((k : ℝ) + 1) := fun k => by positivity
  have hr0 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨φ, hφ, u₀, hconv⟩ := h.exists_tendsto_rescale hx hux hr hr0
  have hr' : ∀ k, 0 < 1 / ((φ k : ℝ) + 1) := fun k => hr (φ k)
  have hr0' : Tendsto (fun k => 1 / ((φ k : ℝ) + 1)) atTop (𝓝 0) := hr0.comp hφ.tendsto_atTop
  obtain ⟨χ₀, hsol, -⟩ := exists_blowup_limit_density hQ h hx hd hr' hr0' hconv
  refine ⟨_, hr', hr0', u₀, hconv, blowup_homogeneous' hQ h hx hr' hr0' hconv, ?_,
    (measureReal_pos_inter_ball_le hQ h hx hd hr' hr0' hconv).trans_lt hdlt, χ₀, hsol⟩
  by_contra hall
  push Not at hall
  have hu₀ : u₀ = fun _ => 0 := funext fun y => le_antisymm (hall y) (hsol.nonneg y trivial)
  rw [hu₀] at hconv
  have hM := MzeroQ_eq_of_tendsto_rescale_zero hn hQ h hx hfr hr' hr0' hconv
  rw [hdM, EReal.coe_eq_coe_iff] at hM
  exact hdlt.ne (mul_left_cancel₀ hq2.ne' hM)

/-- The blow-up `u₀/Q(x)` at a free boundary point `x ∉ Σ^H`, with the data used by the
classification step of Lemma 8.3: a variational solution `(u₀/Q(x), χ₀)` on `ℝⁿ` with coefficient
`1`, one-homogeneous, not identically zero, with `|{u₀ > 0} ∩ B_1| < |B_1|`. -/
theorem exists_blowup_div_of_notMem_sigmaHQ (hn : 2 ≤ n) (hQ : QBounds Ω Q L c C')
    (h : IsVariationalSolutionQ Ω C Q u χ) (hx : x ∈ Ω) (hfr : x ∈ frontier {y | 0 < u y})
    (hS : x ∉ sigmaHQ Ω Q u χ) :
    ∃ r : ℕ → ℝ, (∀ k, 0 < r k) ∧ Tendsto r atTop (𝓝 0) ∧ ∃ u₀ : Rn n → ℝ,
      TendstoLocallyUniformly (fun k => oneHomRescale u x (r k)) u₀ atTop ∧
      (∀ t, 0 < t → ∀ y, u₀ (t • y) / Q x = t * (u₀ y / Q x)) ∧ (∃ y, 0 < u₀ y / Q x) ∧
      volume.real ({y | 0 < u₀ y / Q x} ∩ ball (0 : Rn n) 1) < unitBallVolume n ∧
      ∃ C₀ : ℝ≥0, ∃ χ₀, IsVariationalSolution univ C₀ (fun y => u₀ y / Q x) χ₀ := by
  obtain ⟨r, hr, hr0, u₀, hconv, hhom, ⟨y₀, hy₀⟩, hvol, χ₀, hsol⟩ :=
    exists_blowup_of_notMem_sigmaHQ hn hQ h hx hfr hS
  have hq := hQ.pos_of_mem hx
  have hP : {y | 0 < u₀ y / Q x} = {y | 0 < u₀ y} := by
    ext y; exact div_pos_iff_of_pos_right hq
  refine ⟨r, hr, hr0, u₀, hconv, fun t ht y => by rw [hhom t ht y, mul_div_assoc],
    ⟨y₀, div_pos hy₀ hq⟩, by rwa [hP], _, χ₀, hsol.toConst hq⟩

/-- The touching plane passes to the blow-up: if `φ ≤ u` on `B_ρ(x)` with `φ(x) = 0`, then
`⟪∇φ(x), y⟫ ≤ u₀(y)` for a blow-up `u₀` of `u` at `x`. -/
theorem inner_le_of_le {r : ℕ → ℝ} (hr : ∀ k, 0 < r k) (hr0 : Tendsto r atTop (𝓝 0))
    {u₀ : Rn n → ℝ} (hconv : TendstoLocallyUniformly (fun k => oneHomRescale u x (r k)) u₀ atTop)
    {ρ : ℝ} (hρ : 0 < ρ) {φ : Rn n → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφx : φ x = 0)
    (hle : ∀ y ∈ ball x ρ, φ y ≤ u y) (y : Rn n) : ⟪gradient φ x, y⟫ ≤ u₀ y := by
  have hball : ∀ᶠ k in atTop, x + r k • y ∈ ball x ρ := by
    have : Tendsto (fun k => x + r k • y) atTop (𝓝 x) := by
      simpa using tendsto_const_nhds.add (hr0.smul_const y)
    exact this.eventually (ball_mem_nhds x hρ)
  refine le_of_tendsto_of_tendsto (Regular.tendsto_div_of_contDiff hφ hφx hr hr0 y)
    ((tendstoLocallyUniformlyOn_univ.2 hconv).tendsto_at (mem_univ y)) ?_
  filter_upwards [hball] with k hk
  rw [oneHomRescale_apply]
  exact div_le_div_of_nonneg_right (hle _ hk) (hr k).le

/-- The touching plane passes to the blow-up: if `u ≤ φ₊` on `B_ρ(x)` with `φ(x) = 0`, then
`u₀(y) ≤ ⟪∇φ(x), y⟫₊` for a blow-up `u₀` of `u` at `x`. -/
theorem le_max_inner_of_le_max {r : ℕ → ℝ} (hr : ∀ k, 0 < r k) (hr0 : Tendsto r atTop (𝓝 0))
    {u₀ : Rn n → ℝ} (hconv : TendstoLocallyUniformly (fun k => oneHomRescale u x (r k)) u₀ atTop)
    {ρ : ℝ} (hρ : 0 < ρ) {φ : Rn n → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφx : φ x = 0)
    (hle : ∀ y ∈ ball x ρ, u y ≤ max (φ y) 0) (y : Rn n) : u₀ y ≤ max ⟪gradient φ x, y⟫ 0 := by
  have hball : ∀ᶠ k in atTop, x + r k • y ∈ ball x ρ := by
    have : Tendsto (fun k => x + r k • y) atTop (𝓝 x) := by
      simpa using tendsto_const_nhds.add (hr0.smul_const y)
    exact this.eventually (ball_mem_nhds x hρ)
  refine le_of_tendsto_of_tendsto
    ((tendstoLocallyUniformlyOn_univ.2 hconv).tendsto_at (mem_univ y))
    ((Regular.tendsto_div_of_contDiff hφ hφx hr hr0 y).max tendsto_const_nhds) ?_
  filter_upwards [hball] with k hk
  rw [oneHomRescale_apply, ← zero_div (r k), max_div_div_right (hr k).le]
  exact div_le_div_of_nonneg_right (hle _ hk) (hr k).le

/-- **Lemma 8.3**, touching from below, with a Lipschitz coefficient. If `x ∈ Ω ∩ ∂{u > 0}`,
`x ∉ Σ^H`, `φ` is smooth, `φ(x) = 0` and `φ ≤ u` on `B_ρ(x)`, then `|∇φ(x)| ≤ Q(x)`. -/
theorem norm_gradient_le_of_le (hn : 2 ≤ n) (hQ : QBounds Ω Q L c C')
    (h : IsVariationalSolutionQ Ω C Q u χ) (hx : x ∈ Ω) (hfr : x ∈ frontier {y | 0 < u y})
    (hS : x ∉ sigmaHQ Ω Q u χ) {ρ : ℝ} (hρ : 0 < ρ) {φ : Rn n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφx : φ x = 0) (hle : ∀ y ∈ ball x ρ, φ y ≤ u y) :
    ‖gradient φ x‖ ≤ Q x := by
  obtain ⟨r, hr, hr0, u₀, hconv, hhom, -, hvol, C₀, χ₀, h₀⟩ :=
    exists_blowup_div_of_notMem_sigmaHQ hn hQ h hx hfr hS
  have hq := hQ.pos_of_mem hx
  obtain ⟨hχ₀m, h01, hpos, hid⟩ := h₀.blowup_chi_data
  have htouch : ∀ y, ⟪(Q x)⁻¹ • gradient φ x, y⟫ ≤ u₀ y / Q x := fun y => by
    rw [real_inner_smul_left, inv_mul_eq_div]
    exact div_le_div_of_nonneg_right (inner_le_of_le hr hr0 hconv hρ hφ hφx hle y) hq.le
  have := Regular.norm_le_one_of_le hn h₀.toQ.lipschitzWith_of_univ
    (fun y => h₀.nonneg y trivial) hhom (fun y hy => h₀.harmonicOn_pos trivial hy) hvol hχ₀m h01
    hpos hid htouch
  rwa [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hq), inv_mul_le_iff₀ hq,
    mul_one] at this

/-- **Lemma 8.3**, touching from above, with a Lipschitz coefficient. If `x ∈ Ω ∩ ∂{u > 0}`,
`x ∉ Σ^H`, `φ` is smooth, `φ(x) = 0` and `u ≤ φ₊` on `B_ρ(x)`, then `|∇φ(x)| ≥ Q(x)`. -/
theorem le_norm_gradient_of_le_max (hn : 2 ≤ n) (hQ : QBounds Ω Q L c C')
    (h : IsVariationalSolutionQ Ω C Q u χ) (hx : x ∈ Ω) (hfr : x ∈ frontier {y | 0 < u y})
    (hS : x ∉ sigmaHQ Ω Q u χ) {ρ : ℝ} (hρ : 0 < ρ) {φ : Rn n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφx : φ x = 0) (hle : ∀ y ∈ ball x ρ, u y ≤ max (φ y) 0) :
    Q x ≤ ‖gradient φ x‖ := by
  obtain ⟨r, hr, hr0, u₀, hconv, hhom, ⟨y₀, hy₀⟩, -, C₀, χ₀, h₀⟩ :=
    exists_blowup_div_of_notMem_sigmaHQ hn hQ h hx hfr hS
  have hq := hQ.pos_of_mem hx
  obtain ⟨hχ₀m, h01, hpos, hid⟩ := h₀.blowup_chi_data
  have htouch : ∀ y, u₀ y / Q x ≤ max ⟪(Q x)⁻¹ • gradient φ x, y⟫ 0 := fun y => by
    rw [real_inner_smul_left, inv_mul_eq_div, ← zero_div (Q x), max_div_div_right hq.le]
    exact div_le_div_of_nonneg_right (le_max_inner_of_le_max hr hr0 hconv hρ hφ hφx hle y) hq.le
  have := Regular.one_le_norm_of_le_max hn h₀.toQ.lipschitzWith_of_univ
    (fun y => h₀.nonneg y trivial) hhom (fun y hy => h₀.harmonicOn_pos trivial hy) hy₀ hχ₀m h01
    hpos hid htouch
  rwa [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hq), le_inv_mul_iff₀ hq,
    mul_one] at this

end IsVariationalSolutionQ

end InnerVariational
