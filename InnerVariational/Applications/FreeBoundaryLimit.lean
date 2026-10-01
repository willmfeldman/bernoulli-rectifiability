/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Applications.DensityEstimate
public import InnerVariational.Registry.FreeBoundary
public import InnerVariational.Registry.Harmonic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
public import InnerVariational.Defs.VariationalSolution
public import InnerVariational.Defs.Solutions
import InnerVariational.Basic.Polar

/-!
# Free boundaries of limits of classical solutions

Two steps of the proof of Theorem 9.3 of Kriventsov–Weiss (full reference below). Let `u_k` be
classical solutions on `B_1`, `C`-Lipschitz on `B_1`, with `u_k → v` locally uniformly on `B_1`.

* `eq_zero_of_frequently_pos_on_ball` (Harnack inequality): if `v(x) = 0` and `u_k > 0` on
  `B_δ(x)` for infinitely many `k`, then `v = 0` on `B_{δ/2}(x)`.
* `eventually_exists_frontier_near` and `eventually_exists_frontier_near'`: the two halves of the
  local Hausdorff convergence `∂{u_k > 0} → ∂{v > 0}`, the second one when
  `χ_{u_k>0} → χ_{v>0}` in `L¹_loc` (with Lemma 9.2). Their conjunction is
  `eventually_hausdorff_frontier`.

The paper's second half invokes Proposition 9.1 together with Lemma 9.2. With the uniform
Lipschitz hypothesis `sup_k ‖u_k‖_{C^{0,1}(B_1)} < ∞` (see `Applications/Classical.lean`),
Lemma 9.2 applies directly with constant `C`, so Proposition 9.1 is not needed here.

## References

* D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
  DOI 10.1002/cpa.22226; arXiv:2306.10131. Result numbers refer to arXiv v2.
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

namespace IsClassicalSolution

variable {Ω : Set (Rn n)} {u : Rn n → ℝ}

/-- A classical solution vanishes on its free boundary. -/
theorem eq_zero_of_mem_frontier (h : IsClassicalSolution Ω u) {x : Rn n} (hx : x ∈ Ω)
    (hfr : x ∈ frontier {y | 0 < u y}) : u x = 0 := by
  refine le_antisymm (not_lt.1 fun hpos => hfr.2 ?_) (h.nonneg x hx)
  rw [mem_interior_iff_mem_nhds]
  exact (h.continuousOn.continuousAt (h.isOpen.mem_nhds hx)).preimage_mem_nhds (Ioi_mem_nhds hpos)

/-- On a ball in `Ω` that misses `∂{u > 0}`, a classical solution is either positive everywhere
or zero everywhere. -/
theorem pos_or_eq_zero_of_disjoint_frontier (h : IsClassicalSolution Ω u) {x : Rn n} {δ : ℝ}
    (hδ : ball x δ ⊆ Ω) (hdisj : ∀ z ∈ ball x δ, z ∉ frontier {y | 0 < u y}) :
    (∀ z ∈ ball x δ, 0 < u z) ∨ ∀ z ∈ ball x δ, u z = 0 := by
  have hcover : ball x δ ⊆ interior {y | 0 < u y} ∪ (closure {y | 0 < u y})ᶜ := by
    intro z hz
    by_cases hcl : z ∈ closure {y | 0 < u y}
    · left
      by_contra hint
      exact hdisj z hz ⟨hcl, hint⟩
    · exact Or.inr hcl
  rcases (convex_ball x δ).isPreconnected.subset_or_subset isOpen_interior
    isClosed_closure.isOpen_compl
    (disjoint_compl_right.mono_left interior_subset_closure) hcover with hsub | hsub
  · exact Or.inl fun z hz => interior_subset (s := {y | 0 < u y}) (hsub hz)
  · refine Or.inr fun z hz => le_antisymm (not_lt.1 fun hpos => hsub hz ?_) (h.nonneg z (hδ hz))
    exact subset_closure hpos

end IsClassicalSolution

namespace Applications

variable {u : ℕ → Rn n → ℝ} {C : ℝ≥0} {v : Rn n → ℝ}

/-- A subsequence of a locally uniformly convergent sequence converges locally uniformly. -/
theorem tendstoLocallyUniformlyOn_comp_strictMono {U : Set (Rn n)} {w : ℕ → Rn n → ℝ}
    {w₀ : Rn n → ℝ} (h : TendstoLocallyUniformlyOn w w₀ atTop U) {φ : ℕ → ℕ}
    (hφ : StrictMono φ) : TendstoLocallyUniformlyOn (fun k => w (φ k)) w₀ atTop U :=
  fun s hs x hx => by
    obtain ⟨t, ht, H⟩ := h s hs x hx
    exact ⟨t, ht, hφ.tendsto_atTop.eventually H⟩

/-- **Harnack step** (proof of Theorem 9.3, Harnack inequality). If `v(x) = 0` and, for infinitely
many `k`, `u_k > 0` on `B_δ(x) ⊆ B_1`, then `v = 0` on `B_{δ/2}(x)`. -/
theorem eq_zero_of_frequently_pos_on_ball [NeZero n]
    (hu : ∀ k, IsClassicalSolution (ball 0 1) (u k))
    (hconv : TendstoLocallyUniformlyOn u v atTop (ball 0 1)) {x : Rn n} {δ : ℝ} (hδ : 0 < δ)
    (hxδ : ball x δ ⊆ ball 0 1) (hvx : v x = 0)
    (hfr : ∃ᶠ k in atTop, ∀ z ∈ ball x δ, 0 < u k z) : ∀ y ∈ ball x (δ / 2), v y = 0 := by
  obtain ⟨CH, hCH⟩ := Registry.harnack_inequality (n := n)
  have hx : x ∈ ball (0 : Rn n) 1 := hxδ (mem_ball_self hδ)
  intro y hy
  have hyB : y ∈ ball (0 : Rn n) 1 := hxδ (ball_subset_ball (by linarith) hy)
  have hle : ∃ᶠ k in atTop, (u k y, u k x) ∈ {p : ℝ × ℝ | p.1 ≤ CH * p.2} := by
    refine hfr.mono fun k hk => ?_
    refine hCH (u k) x (δ / 2) (half_pos hδ) (fun z hz => ?_) y hy x (mem_ball_self (half_pos hδ))
    have hz' : z ∈ ball x δ := by rwa [show 2 * (δ / 2) = δ by ring] at hz
    exact ⟨(hu k).harmonicAt z (hxδ hz') (hk z hz'), (hu k).nonneg z (hxδ hz')⟩
  have hcl : IsClosed {p : ℝ × ℝ | p.1 ≤ CH * p.2} :=
    isClosed_le continuous_fst (continuous_const.mul continuous_snd)
  have hmem := hcl.mem_of_frequently_of_tendsto hle
    ((hconv.tendsto_at hyB).prodMk_nhds (hconv.tendsto_at hx))
  have h0 : 0 ≤ v y := ge_of_tendsto' (hconv.tendsto_at hyB) fun k => (hu k).nonneg y hyB
  simp only [mem_ofPred_eq, hvx, mul_zero] at hmem
  exact le_antisymm hmem h0

/-- If `u_k = 0` on `B_δ(x)` for infinitely many `k`, then `v = 0` there. -/
theorem eq_zero_of_frequently_eq_zero_on_ball
    (hconv : TendstoLocallyUniformlyOn u v atTop (ball 0 1)) {x : Rn n} {δ : ℝ}
    (hxδ : ball x δ ⊆ ball 0 1) (hfr : ∃ᶠ k in atTop, ∀ z ∈ ball x δ, u k z = 0) :
    ∀ y ∈ ball x δ, v y = 0 := fun y hy =>
  isClosed_singleton.mem_of_frequently_of_tendsto (hfr.mono fun _ hk => hk y hy)
    (hconv.tendsto_at (hxδ hy))

/-- `v` vanishes on `B_1 ∩ ∂{v > 0}`. -/
theorem eq_zero_of_mem_frontier_limit (hu : ∀ k, IsClassicalSolution (ball 0 1) (u k))
    (hconv : TendstoLocallyUniformlyOn u v atTop (ball 0 1)) {x : Rn n}
    (hx : x ∈ ball (0 : Rn n) 1) (hfr : x ∈ frontier {y | 0 < v y}) : v x = 0 := by
  have hc : ContinuousOn v (ball 0 1) :=
    hconv.continuousOn (.of_forall fun k => (hu k).continuousOn)
  refine le_antisymm (not_lt.1 fun hpos => hfr.2 ?_)
    (ge_of_tendsto' (hconv.tendsto_at hx) fun k => (hu k).nonneg x hx)
  rw [mem_interior_iff_mem_nhds]
  exact (hc.continuousAt (isOpen_ball.mem_nhds hx)).preimage_mem_nhds (Ioi_mem_nhds hpos)

/-- **Hausdorff convergence, first half** (proof of Theorem 9.3). Every point of `K ∩ ∂{v > 0}` is,
for `k` large (uniformly on `K`), within `ε` of `B_1 ∩ ∂{u_k > 0}`. -/
theorem eventually_exists_frontier_near [NeZero n]
    (hu : ∀ k, IsClassicalSolution (ball 0 1) (u k))
    (hconv : TendstoLocallyUniformlyOn u v atTop (ball 0 1)) {K : Set (Rn n)} (hK : IsCompact K)
    (hKB : K ⊆ ball 0 1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ x ∈ K ∩ frontier {y | 0 < v y},
      ∃ y ∈ ball 0 1 ∩ frontier {y | 0 < u k y}, dist x y < ε := by
  by_contra hne
  rw [not_eventually] at hne
  obtain ⟨ψ, hψ, hP⟩ := extraction_of_frequently_atTop hne
  have hP' : ∀ j, ∃ x ∈ K ∩ frontier {y | 0 < v y},
      ∀ y ∈ ball 0 1 ∩ frontier {y | 0 < u (ψ j) y}, ε ≤ dist x y := fun j => by
    have := hP j
    push Not at this
    exact this
  choose x hxK hxfar using hP'
  obtain ⟨x₀, hx₀, ψ', hψ', hlim⟩ := (hK.inter_right isClosed_frontier).tendsto_subseq hxK
  have hx₀B : x₀ ∈ ball (0 : Rn n) 1 := hKB hx₀.1
  obtain ⟨δ₀, hδ₀, hδ₀B⟩ := Metric.isOpen_iff.1 isOpen_ball x₀ hx₀B
  set δ := min δ₀ (ε / 2) with hδdef
  have hδ : 0 < δ := lt_min hδ₀ (half_pos hε)
  have hδB : ball x₀ δ ⊆ ball 0 1 := (ball_subset_ball (min_le_left _ _)).trans hδ₀B
  -- the subsequence `w_j = u_{ψ (ψ' j)}`
  set w : ℕ → Rn n → ℝ := fun j => u (ψ (ψ' j)) with hwdef
  have hwconv : TendstoLocallyUniformlyOn w v atTop (ball 0 1) :=
    tendstoLocallyUniformlyOn_comp_strictMono hconv (hψ.comp hψ')
  have hw : ∀ j, IsClassicalSolution (ball 0 1) (w j) := fun j => hu _
  -- eventually `B_δ(x₀)` misses `∂{w_j > 0}`
  have hev : ∀ᶠ j in atTop, ∀ z ∈ ball x₀ δ, z ∉ frontier {y | 0 < w j y} := by
    filter_upwards [(tendsto_iff_dist_tendsto_zero.1 hlim).eventually (gt_mem_nhds (half_pos hε))]
      with j hj z hz hzfr
    have h1 := hxfar (ψ' j) z ⟨hδB hz, hzfr⟩
    have h2 : dist z x₀ < ε / 2 := (mem_ball.1 hz).trans_le (min_le_right _ _)
    have h3 := dist_triangle (x (ψ' j)) x₀ z
    rw [dist_comm z x₀] at h2
    simp only [Function.comp_apply] at hj
    linarith
  have hdich : ∀ᶠ j in atTop, (∀ z ∈ ball x₀ δ, 0 < w j z) ∨ ∀ z ∈ ball x₀ δ, w j z = 0 :=
    hev.mono fun j hj => (hw j).pos_or_eq_zero_of_disjoint_frontier hδB hj
  have hvx₀ : v x₀ = 0 := eq_zero_of_mem_frontier_limit hu hconv hx₀B hx₀.2
  have hzero : ∀ y ∈ ball x₀ (δ / 2), v y = 0 := by
    rcases frequently_or_distrib.1 hdich.frequently with hpos | hz
    · exact eq_zero_of_frequently_pos_on_ball hw hwconv hδ hδB hvx₀ hpos
    · exact fun y hy => eq_zero_of_frequently_eq_zero_on_ball hwconv hδB hz y
        (ball_subset_ball (by linarith) hy)
  obtain ⟨y, hy, hypos⟩ := mem_closure_iff.1 hx₀.2.1 (ball x₀ (δ / 2)) isOpen_ball
    (mem_ball_self (half_pos hδ))
  have : (0 : ℝ) < v y := hypos
  rw [hzero y hy] at this
  exact lt_irrefl _ this

/-- `χ_{g>0}` is a.e. strongly measurable on every measurable `K ⊆ U` if `g` is continuous on the
open set `U`. -/
theorem aestronglyMeasurable_posIndicator {g : Rn n → ℝ} {U K : Set (Rn n)} (hU : IsOpen U)
    (hg : ContinuousOn g U) (hK : MeasurableSet K) (hKU : K ⊆ U) :
    AEStronglyMeasurable (posIndicator g) (volume.restrict K) := by
  have hae : (U ∩ g ⁻¹' Ioi 0).indicator (1 : Rn n → ℝ) =ᵐ[volume.restrict K] posIndicator g := by
    refine (ae_restrict_iff' hK).2 (.of_forall fun y hy => ?_)
    by_cases hpos : 0 < g y
    · rw [posIndicator_of_pos hpos, indicator_of_mem (show y ∈ U ∩ g ⁻¹' Ioi 0 from
        ⟨hKU hy, hpos⟩)]
      rfl
    · rw [posIndicator_of_nonpos (not_lt.1 hpos), indicator_of_notMem fun h' => hpos h'.2]
  exact (Measurable.aestronglyMeasurable (measurable_one.indicator
    (hg.isOpen_inter_preimage hU isOpen_Ioi).measurableSet)).congr hae

/-- **Hausdorff convergence, second half** (proof of Theorem 9.3, with Lemma 9.2). If
`χ_{u_k>0} → χ_{v>0}` in `L¹_loc(B_1)`, then every point of `K ∩ ∂{u_k > 0}` is, for `k` large
(uniformly on `K`), within `ε` of `B_1 ∩ ∂{v > 0}`. -/
theorem eventually_exists_frontier_near' [NeZero n] (hn : 2 ≤ n)
    (hu : ∀ k, IsClassicalSolution (ball 0 1) (u k))
    (hlip : ∀ k, LipschitzOnWith C (u k) (ball 0 1))
    (hconv : TendstoLocallyUniformlyOn u v atTop (ball 0 1))
    (hL1 : ∀ K, IsCompact K → K ⊆ ball 0 1 →
      Tendsto (fun k => ∫ x in K, |posIndicator (u k) x - posIndicator v x|) atTop (𝓝 0))
    {K : Set (Rn n)} (hK : IsCompact K) (hKB : K ⊆ ball 0 1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ x ∈ K ∩ frontier {y | 0 < u k y},
      ∃ y ∈ ball 0 1 ∩ frontier {y | 0 < v y}, dist x y < ε := by
  by_contra hne
  rw [not_eventually] at hne
  obtain ⟨ψ, hψ, hP⟩ := extraction_of_frequently_atTop hne
  have hP' : ∀ j, ∃ x ∈ K ∩ frontier {y | 0 < u (ψ j) y},
      ∀ y ∈ ball 0 1 ∩ frontier {y | 0 < v y}, ε ≤ dist x y := fun j => by
    have := hP j
    push Not at this
    exact this
  choose x hxK hxfar using hP'
  obtain ⟨x₀, hx₀, ψ', hψ', hlim⟩ := hK.tendsto_subseq fun j => (hxK j).1
  have hx₀B : x₀ ∈ ball (0 : Rn n) 1 := hKB hx₀
  set w : ℕ → Rn n → ℝ := fun j => u (ψ (ψ' j)) with hwdef
  set y : ℕ → Rn n := fun j => x (ψ' j) with hydef
  have hwconv : TendstoLocallyUniformlyOn w v atTop (ball 0 1) :=
    tendstoLocallyUniformlyOn_comp_strictMono hconv (hψ.comp hψ')
  have hw : ∀ j, IsClassicalSolution (ball 0 1) (w j) := fun j => hu _
  have hyfr : ∀ j, y j ∈ frontier {z | 0 < w j z} := fun j => (hxK (ψ' j)).2
  have hyB : ∀ j, y j ∈ ball (0 : Rn n) 1 := fun j => hKB (hxK (ψ' j)).1
  have hwy : ∀ j, w j (y j) = 0 := fun j => (hw j).eq_zero_of_mem_frontier (hyB j) (hyfr j)
  have hvc : ContinuousOn v (ball 0 1) :=
    hconv.continuousOn (.of_forall fun k => (hu k).continuousOn)
  -- `v(x₀) = 0`
  have hvx₀ : v x₀ = 0 := by
    have h1 := hwconv.tendsto_comp (hvc.continuousWithinAt hx₀B) hx₀B
      (tendsto_nhdsWithin_iff.2 ⟨hlim, .of_forall hyB⟩)
    have h0 : (fun j => w j ((x ∘ ψ') j)) = fun _ => (0 : ℝ) := funext hwy
    rw [h0] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  by_cases hfr : x₀ ∈ frontier {z | 0 < v z}
  · -- `x₀` is a free boundary point of `v`, close to `y j`
    obtain ⟨j, hj⟩ := ((tendsto_iff_dist_tendsto_zero.1 hlim).eventually
      (gt_mem_nhds hε)).exists
    have := hxfar (ψ' j) x₀ ⟨hx₀B, hfr⟩
    simp only [Function.comp_apply] at hj
    linarith
  · -- `v = 0` near `x₀`: contradiction with Lemma 9.2
    have hncl : x₀ ∉ closure {z | 0 < v z} := fun hcl => hfr ⟨hcl, fun hint => by
      have : (0 : ℝ) < v x₀ := interior_subset (s := {z | 0 < v z}) hint
      rw [hvx₀] at this
      exact lt_irrefl _ this⟩
    obtain ⟨δ₀, hδ₀, hδ₀sub⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl x₀ hncl
    obtain ⟨δ₁, hδ₁, hδ₁B⟩ := Metric.isOpen_iff.1 isOpen_ball x₀ hx₀B
    set δ := min δ₀ δ₁ with hδdef
    have hδ : 0 < δ := lt_min hδ₀ hδ₁
    set K' := closedBall x₀ (δ / 2) with hK'def
    have hK'δ : K' ⊆ ball x₀ δ := closedBall_subset_ball (half_lt_self hδ)
    have hK'B : K' ⊆ ball 0 1 := hK'δ.trans ((ball_subset_ball (min_le_right _ _)).trans hδ₁B)
    have hvK' : ∀ z ∈ K', posIndicator v z = 0 := fun z hz => by
      refine posIndicator_of_nonpos (not_lt.1 fun hpos => ?_)
      exact hδ₀sub ((ball_subset_ball (min_le_left _ _)) (hK'δ hz)) (subset_closure hpos)
    have hlim0 := (hL1 K' (isCompact_closedBall _ _) hK'B).comp (hψ.comp hψ').tendsto_atTop
    set c : ℝ := unitBallVolume n / (2 * (1 + (C : ℝ) ^ 2)) * (δ / 4) ^ n with hcdef
    have hc : 0 < c := by
      have := unitBallVolume_pos n
      positivity
    have hbound : ∀ᶠ j in atTop,
        c ≤ ∫ z in K', |posIndicator (w j) z - posIndicator v z| := by
      filter_upwards [(tendsto_iff_dist_tendsto_zero.1 hlim).eventually
        (gt_mem_nhds (show 0 < δ / 4 by positivity))] with j hj
      simp only [Function.comp_apply] at hj
      have hBK' : ball (y j) (δ / 4) ⊆ K' := fun z hz => by
        rw [mem_closedBall]
        have := dist_triangle z (y j) x₀
        rw [mem_ball] at hz
        linarith
      have hvar : IsVariationalSolution (ball (y j) (δ / 4)) C (w j) (posIndicator (w j)) :=
        (Registry.IsClassicalSolution.isVariationalSolution (hw j) (hlip _)).mono isOpen_ball
          (hBK'.trans hK'B)
      have h92 := hvar.le_volume_pos_inter_ball hn (by positivity) (hyfr j)
      -- the integrand is `χ_{w_j > 0}` on `K'`
      set S := ball (y j) (δ / 4) ∩ {z | 0 < w j z} with hSdef
      have hSo : IsOpen S :=
        ((hw j).continuousOn.mono (hBK'.trans hK'B)).isOpen_inter_preimage isOpen_ball isOpen_Ioi
      have hwc : ContinuousOn (w j) (ball 0 1) := (hw j).continuousOn
      have hint : IntegrableOn (fun z => |posIndicator (w j) z - posIndicator v z|) K' := by
        refine IntegrableOn.of_bound (measure_closedBall_lt_top) ?_ 1
          ((ae_restrict_iff' measurableSet_closedBall).2 (.of_forall fun z hz => ?_))
        · exact ((aestronglyMeasurable_posIndicator isOpen_ball hwc measurableSet_closedBall
            hK'B).sub (aestronglyMeasurable_posIndicator isOpen_ball hvc measurableSet_closedBall
            hK'B)).norm
        · rw [hvK' z hz, sub_zero, Real.norm_eq_abs, abs_abs]
          by_cases hpos : 0 < w j z
          · rw [posIndicator_of_pos hpos]; norm_num
          · rw [posIndicator_of_nonpos (not_lt.1 hpos)]; norm_num
      have hmono := setIntegral_mono_set hint
        ((ae_restrict_iff' measurableSet_closedBall).2 (.of_forall fun z _ => abs_nonneg _))
        (Eventually.of_forall hBK')
      have heq : ∫ z in ball (y j) (δ / 4), |posIndicator (w j) z - posIndicator v z| =
          volume.real S := by
        have hSB : S ∩ ball (y j) (δ / 4) = S := inter_eq_left.2 inter_subset_left
        rw [← hSB, ← measureReal_restrict_apply hSo.measurableSet,
          ← integral_indicator_one hSo.measurableSet]
        refine setIntegral_congr_fun measurableSet_ball fun z hz => ?_
        rw [hvK' z (hBK' hz), sub_zero]
        by_cases hpos : 0 < w j z
        · rw [posIndicator_of_pos hpos, indicator_of_mem (show z ∈ S from ⟨hz, hpos⟩)]
          simp
        · rw [posIndicator_of_nonpos (not_lt.1 hpos), indicator_of_notMem fun h' => hpos h'.2]
          simp
      calc c ≤ volume.real (ball (y j) (δ / 4) ∩ {z | 0 < w j z}) := h92
        _ = ∫ z in ball (y j) (δ / 4), |posIndicator (w j) z - posIndicator v z| := heq.symm
        _ ≤ _ := hmono
    have := ge_of_tendsto hlim0 hbound
    linarith

/-- **Local Hausdorff convergence of the free boundaries** (proof of Theorem 9.3). -/
theorem eventually_hausdorff_frontier [NeZero n] (hn : 2 ≤ n)
    (hu : ∀ k, IsClassicalSolution (ball 0 1) (u k))
    (hlip : ∀ k, LipschitzOnWith C (u k) (ball 0 1))
    (hconv : TendstoLocallyUniformlyOn u v atTop (ball 0 1))
    (hL1 : ∀ K, IsCompact K → K ⊆ ball 0 1 →
      Tendsto (fun k => ∫ x in K, |posIndicator (u k) x - posIndicator v x|) atTop (𝓝 0)) :
    ∀ K, IsCompact K → K ⊆ ball 0 1 → ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      (∀ x ∈ K ∩ frontier {y | 0 < v y},
        ∃ y ∈ ball 0 1 ∩ frontier {y | 0 < u k y}, dist x y < ε) ∧
      (∀ x ∈ K ∩ frontier {y | 0 < u k y},
        ∃ y ∈ ball 0 1 ∩ frontier {y | 0 < v y}, dist x y < ε) := fun _ hK hKB _ hε =>
  (eventually_exists_frontier_near hu hconv hK hKB hε).and
    (eventually_exists_frontier_near' hn hu hlip hconv hL1 hK hKB hε)

end Applications

end InnerVariational
