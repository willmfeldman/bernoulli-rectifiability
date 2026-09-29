/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Defs.Quantities
public import InnerVariational.Defs.VariationalSolutionQ
public import InnerVariational.Kernel.VariationalQ
import InnerVariational.Applications.CompactnessQ
import InnerVariational.Kernel.Rescale
import InnerVariational.Monotonicity.Limits
import InnerVariational.Monotonicity.DensityQ
import Mathlib.MeasureTheory.Function.Floor

/-!
# Blow-up limits of variational solutions with a Lipschitz coefficient

Let `(u, χ)` be a variational solution on `Ω` for a coefficient `Q` with `QBounds Ω Q L c C'`,
let `x ∈ Ω`, and let `r_k → 0+` be such that the rescalings `u_{x,r_k}(y) = u(x + r_k y) / r_k`
converge locally uniformly on `ℝⁿ` to `u₀`. Then, along a subsequence, the rescalings
`χ_{x,r_k}(y) = χ(x + r_k y)` converge a.e. and in `L¹_loc(ℝⁿ)` to a function `χ₀` such that
`(u₀, χ₀)` is a variational solution on `ℝⁿ` for the constant coefficient `Q(x)`, with the same
gradient constant.

The paper D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and
compactness for non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025),
DOI 10.1002/cpa.22226, arXiv:2306.10131, treats `Q ≡ 1` and does not state this separately. It
combines the rescaling (3.6) with the compactness of variational solutions from the first
paragraph of the proof of Theorem 9.3.

## Main results

* `IsVariationalSolutionQ.exists_blowup_limit_ae`: the blow-up limit, with a.e. and `L¹_loc`
  convergence of `χ_{x,r_k}`.

## Proof

For every radius `ρ > 0` the rescalings are eventually variational solutions on `B_ρ` for the
coefficients `Q_k = Q(x + r_k ·)`, which satisfy `QBounds` with Lipschitz constants `r_k L`
(`IsVariationalSolutionQ.eventually_rescale_ball`). The coefficients `Q_k` converge to `Q(x)`
pointwise (`Q` is continuous at `x`) and `r_k L → 0`, so the compactness theorem
`IsVariationalSolutionQ.exists_subseq_limit` applies on every ball `B_{m+1}`, with a limit for
the constant coefficient `Q(x)`. A diagonal argument over `m ∈ ℕ` gives a single subsequence
that converges a.e. on `ℝⁿ`. The limits on the balls agree a.e. where the balls overlap, so they
glue to a measurable `{0, 1}`-valued `χ₀`, and `(u₀, χ₀)` is a variational solution on `ℝⁿ`
because every test field is supported in some ball. Convergence in `L¹(K)` for compact `K` then
follows by dominated convergence.
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal

@[expose] public section

namespace InnerVariational

variable {n : ℕ}

namespace IsVariationalSolutionQ

/-- Every point `y` lies in the ball `B_{⌊|y|⌋ + 1}`. -/
theorem mem_ball_floor_add_one (y : Rn n) :
    y ∈ ball (0 : Rn n) (⌊‖y‖⌋₊ + 1) := by
  rw [mem_ball_zero_iff]
  exact Nat.lt_floor_add_one _

/-- Gluing over the balls `B_{m+1}`: if `(u, χ_m)` is a variational solution on `B_{m+1}` for the
coefficient `Q` for every `m`, and `χ` is a measurable `{0, 1}`-valued function with `χ = χ_m`
a.e. on `B_{m+1}`, then `(u, χ)` is a variational solution on `ℝⁿ` for `Q`. -/
theorem of_forall_ball {C : ℝ≥0} {Q u χ : Rn n → ℝ} {χs : ℕ → Rn n → ℝ}
    (hs : ∀ m : ℕ, IsVariationalSolutionQ (ball 0 (m + 1)) C Q u (χs m))
    (hχ : Measurable χ) (h01 : ∀ y, χ y = 0 ∨ χ y = 1)
    (hae : ∀ m : ℕ, ∀ᵐ y ∂(volume.restrict (ball (0 : Rn n) (m + 1))), χ y = χs m y) :
    IsVariationalSolutionQ univ C Q u χ := by
  have hmem := mem_ball_floor_add_one (n := n)
  refine ⟨isOpen_univ, fun y _ => (hs _).nonneg y (hmem y), ?_, ?_, ?_, ?_, fun y _ => h01 y,
    ?_, ?_⟩
  · exact (continuous_iff_continuousAt.2 fun y =>
      (hs _).continuousOn.continuousAt (isOpen_ball.mem_nhds (hmem y))).continuousOn
  · refine contDiffOn_of_locally_contDiffOn fun y _ => ⟨_, isOpen_ball, hmem y, ?_⟩
    exact (hs _).contDiffOn.mono fun z hz => ⟨hz.2, hz.1.2⟩
  · intro z ρ _
    refine (hs ⌈ρ + ‖z‖⌉₊).lipschitzOnWith z ρ (ball_subset_ball' ?_)
    rw [dist_zero_right]
    linarith [Nat.le_ceil (ρ + ‖z‖)]
  · simpa using hχ
  · rw [Measure.restrict_univ]
    have h : ∀ m : ℕ, ∀ᵐ y : Rn n, y ∈ ball (0 : Rn n) (m + 1) →
        posIndicator u y ≤ χs m y ∧ χ y = χs m y := fun m =>
      (ae_restrict_iff' measurableSet_ball).1 ((hs m).posIndicator_le_chi.and (hae m))
    filter_upwards [ae_all_iff.2 h] with y hy
    obtain ⟨h1, h2⟩ := hy _ (hmem y)
    rw [h2]
    exact h1
  · intro ξ hξ
    obtain ⟨ρ, hρ⟩ := hξ.2.1.isCompact.isBounded.subset_ball (0 : Rn n)
    set m : ℕ := ⌈ρ⌉₊
    have hsub : tsupport ξ ⊆ ball 0 (m + 1) :=
      hρ.trans (ball_subset_ball (by linarith [Nat.le_ceil ρ]))
    rw [← (hs m).innerVariationQ_eq_zero ξ ⟨hξ.1, hξ.2.1, hsub⟩]
    refine integral_congr_ae ?_
    filter_upwards [(ae_restrict_iff' measurableSet_ball).1 (hae m)] with y hy
    by_cases hyb : y ∈ ball (0 : Rn n) (m + 1)
    · rw [hy hyb]
    · have hyξ : y ∉ tsupport ξ := fun h' => hyb (hsub h')
      simp [divergence_eq_zero_of_notMem_tsupport hyξ, fderiv_of_notMem_tsupport (𝕜 := ℝ) hyξ,
        image_eq_zero_of_notMem_tsupport hyξ]

variable {Ω : Set (Rn n)} {C : ℝ≥0} {Q u χ : Rn n → ℝ} {x : Rn n} {L : ℝ≥0} {c C' : ℝ}

/-- **Blow-up limits of variational solutions with a Lipschitz coefficient.** Let `(u, χ)` be a
variational solution on `Ω` for `Q` with `QBounds Ω Q L c C'`, `x ∈ Ω`, and `r_k → 0+` with
`u_{x,r_k} → u₀` locally uniformly on `ℝⁿ`. Then along a subsequence the rescalings
`χ_{x,r_k} = χ(x + r_k ·)` converge a.e. on `ℝⁿ` and in `L¹_loc(ℝⁿ)` to a function `χ₀` such that
`(u₀, χ₀)` is a variational solution on `ℝⁿ` for the constant coefficient `Q(x)`, with the same
constant `C`. -/
theorem exists_blowup_limit_ae (hQ : QBounds Ω Q L c C') (h : IsVariationalSolutionQ Ω C Q u χ)
    (hx : x ∈ Ω) {r : ℕ → ℝ} (hr : ∀ k, 0 < r k) (hr0 : Tendsto r atTop (𝓝 0))
    {u₀ : Rn n → ℝ}
    (hconv : TendstoLocallyUniformly (fun k => oneHomRescale u x (r k)) u₀ atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ χ₀, IsVariationalSolutionQ univ C (fun _ => Q x) u₀ χ₀ ∧
      (∀ᵐ y, Tendsto (fun k => chiRescale χ x (r (φ k)) y) atTop (𝓝 (χ₀ y))) ∧
      ∀ K, IsCompact K →
        Tendsto (fun k => ∫ y in K, |chiRescale χ x (r (φ k)) y - χ₀ y|) atTop (𝓝 0) := by
  obtain ⟨R, hR0, hR⟩ := Metric.isOpen_iff.1 h.isOpen x hx
  have hmem := mem_ball_floor_add_one (n := n)
  have hQx : ContinuousAt Q x := hQ.continuousOn.continuousAt (h.isOpen.mem_nhds hx)
  -- `Good m g`: along the indices `g k`, `χ_{x,r}` converges a.e. on `B_{m+1}` to some `χ'`
  -- with `(u₀, χ')` a variational solution on `B_{m+1}` for the coefficient `Q(x)`.
  let Good : ℕ → (ℕ → ℕ) → Prop := fun m g => ∃ χ' : Rn n → ℝ,
    IsVariationalSolutionQ (ball 0 (m + 1)) C (fun _ => Q x) u₀ χ' ∧
      ∀ᵐ y ∂(volume.restrict (ball (0 : Rn n) (m + 1))),
        Tendsto (fun k => chiRescale χ x (r (g k)) y) atTop (𝓝 (χ' y))
  -- one step of the extraction, on the ball `B_{m+1}`
  have hstep : ∀ m (g : ℕ → ℕ), StrictMono g → ∃ θ : ℕ → ℕ, StrictMono θ ∧ Good m (g ∘ θ) := by
    intro m g hg
    obtain ⟨k₀, hk₀⟩ := eventually_atTop.1
      (h.eventually_rescale_ball hQ hR0 hR hr hr0 (by positivity : (0 : ℝ) < m + 1))
    have hgk : ∀ j, k₀ ≤ g (j + k₀) := fun j => (Nat.le_add_left k₀ j).trans (hg.id_le _)
    have hgt : Tendsto (fun j => g (j + k₀)) atTop atTop :=
      hg.tendsto_atTop.comp (tendsto_add_atTop_nat k₀)
    have hconv' : TendstoLocallyUniformly (fun j => oneHomRescale u x (r (g (j + k₀)))) u₀
        atTop := fun s hs y => by
      obtain ⟨t, ht, hts⟩ := hconv s hs y
      exact ⟨t, ht, hgt.eventually hts⟩
    have hL : Tendsto (fun j => ((r (g (j + k₀))).toNNReal * L : ℝ≥0) : ℕ → ℝ) atTop (𝓝 0) := by
      have := (hr0.comp hgt).mul_const (L : ℝ)
      rw [zero_mul] at this
      refine this.congr fun j => ?_
      simp only [Function.comp_apply, NNReal.coe_mul, Real.coe_toNNReal _ (hr _).le]
    have hq : ∀ y ∈ ball (0 : Rn n) (m + 1),
        Tendsto (fun j => Q (x + r (g (j + k₀)) • y)) atTop (𝓝 (Q x)) := fun y _ => by
      refine hQx.tendsto.comp ?_
      simpa using tendsto_const_nhds.add ((hr0.comp hgt).smul_const y)
    obtain ⟨-, θ, hθ, χ', hχ', -, hae⟩ := exists_subseq_limit
      (fun j => (hk₀ _ (hgk j)).2) hL hq (fun j => (hk₀ _ (hgk j)).1)
      ((tendstoLocallyUniformlyOn_univ.2 hconv').mono (subset_univ _))
    exact ⟨fun j => θ j + k₀, fun a b hab => Nat.add_lt_add_right (hθ hab) k₀, χ', hχ', hae⟩
  choose! θ hθ hθGood using hstep
  -- the nested subsequences `ψ m`, with `ψ (m + 1) = ψ m ∘ θ (m + 1) (ψ m)`
  let ψ : ℕ → ℕ → ℕ := fun m => Nat.rec (id ∘ θ 0 id) (fun m g => g ∘ θ (m + 1) g) m
  have hψS : ∀ m, ψ (m + 1) = ψ m ∘ θ (m + 1) (ψ m) := fun _ => rfl
  have hψ : ∀ m, StrictMono (ψ m) ∧ Good m (ψ m) := by
    intro m
    induction m with
    | zero => exact ⟨strictMono_id.comp (hθ 0 id strictMono_id), hθGood 0 id strictMono_id⟩
    | succ m ih =>
      rw [hψS]
      exact ⟨ih.1.comp (hθ _ _ ih.1), hθGood _ _ ih.1⟩
  have hτ : ∀ m d, ∃ τ : ℕ → ℕ, StrictMono τ ∧ ψ (m + d) = ψ m ∘ τ := by
    intro m d
    induction d with
    | zero => exact ⟨id, strictMono_id, rfl⟩
    | succ d ih =>
      obtain ⟨τ, hτ, e⟩ := ih
      refine ⟨τ ∘ θ (m + d + 1) (ψ (m + d)), hτ.comp (hθ _ _ (hψ _).1), ?_⟩
      rw [← add_assoc, hψS, e]
      rfl
  -- the diagonal subsequence
  let φ : ℕ → ℕ := fun k => ψ k k
  have hφ : StrictMono φ := strictMono_nat_of_lt_succ fun k => by
    change ψ k k < ψ (k + 1) (k + 1)
    rw [hψS]
    exact (hψ k).1 (lt_of_lt_of_le (Nat.lt_succ_self k) ((hθ _ _ (hψ k).1).id_le _))
  have hφGood : ∀ m, Good m φ := by
    intro m
    choose τ hτm he using hτ m
    have hσ : Tendsto (fun k => τ k (m + k)) atTop atTop :=
      tendsto_atTop_mono (fun k => le_add_self.trans ((hτm k).id_le _)) tendsto_id
    obtain ⟨χ', h1, h2⟩ := (hψ m).2
    refine ⟨χ', h1, h2.mono fun y hy => ?_⟩
    rw [← tendsto_add_atTop_iff_nat m]
    refine (hy.comp hσ).congr fun k => ?_
    have e : φ (k + m) = ψ m (τ k (m + k)) := by
      rw [add_comm k m]
      exact congrFun (he k) (m + k)
    simp only [Function.comp_apply, e]
  choose χs hχs hχae using hφGood
  -- glue the limits
  have hall : ∀ᵐ y : Rn n, ∀ m : ℕ, y ∈ ball (0 : Rn n) (m + 1) →
      Tendsto (fun k => chiRescale χ x (r (φ k)) y) atTop (𝓝 (χs m y)) :=
    ae_all_iff.2 fun m => (ae_restrict_iff' measurableSet_ball).1 (hχae m)
  let χ₀ : Rn n → ℝ := fun y => χs ⌊‖y‖⌋₊ y
  have hχ₀ae : ∀ᵐ y : Rn n, Tendsto (fun k => chiRescale χ x (r (φ k)) y) atTop (𝓝 (χ₀ y)) :=
    hall.mono fun y hy => hy _ (hmem y)
  have hχ₀m : Measurable χ₀ := by
    have e : χ₀ = (fun p : ℕ × Rn n => (ball (0 : Rn n) (p.1 + 1)).indicator (χs p.1) p.2) ∘
        fun y => (⌊‖y‖⌋₊, y) :=
      funext fun y => (indicator_of_mem (hmem y) _).symm
    rw [e]
    exact (measurable_from_prod_countable_right fun m => (hχs m).measurable_chi).comp
      ((Measurable.nat_floor measurable_norm).prodMk measurable_id)
  have h01 : ∀ y, χ₀ y = 0 ∨ χ₀ y = 1 := fun y => (hχs _).chi_mem y (hmem y)
  have hsol : IsVariationalSolutionQ univ C (fun _ => Q x) u₀ χ₀ :=
    of_forall_ball hχs hχ₀m h01 fun m => (ae_restrict_iff' measurableSet_ball).2
      (hall.mono fun y hy hym => tendsto_nhds_unique (hy _ (hmem y)) (hy m hym))
  refine ⟨φ, hφ, χ₀, hsol, hχ₀ae, fun K hK => ?_⟩
  -- `L¹(K)` convergence by dominated convergence
  obtain ⟨ρ, hKρ⟩ := hK.isBounded.subset_ball (0 : Rn n)
  have hKsub : K ⊆ ball 0 (max ρ 1) := hKρ.trans (ball_subset_ball (le_max_left _ _))
  have hev : ∀ᶠ k in atTop, IsVariationalSolutionQ (ball 0 (max ρ 1)) C
      (fun y => Q (x + r (φ k) • y)) (oneHomRescale u x (r (φ k))) (chiRescale χ x (r (φ k))) :=
    (hφ.tendsto_atTop.eventually (h.eventually_rescale_ball hQ hR0 hR hr hr0
      (lt_max_of_lt_right one_pos))).mono fun k hk => hk.1
  haveI : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
  have hlim := tendsto_integral_filter_of_dominated_convergence (l := atTop)
    (μ := volume.restrict K) (F := fun k y => |chiRescale χ x (r (φ k)) y - χ₀ y|)
    (f := fun _ => 0) (fun _ => (1 : ℝ)) ?_ ?_ (integrable_const 1) ?_
  · simpa using hlim
  · filter_upwards [hev] with k hk
    have hm : AEStronglyMeasurable (chiRescale χ x (r (φ k))) (volume.restrict K) :=
      hk.measurable_chi.aestronglyMeasurable.congr ((ae_restrict_iff' hK.measurableSet).2
        (ae_of_all _ fun y hy => indicator_of_mem (hKsub hy) _))
    exact continuous_abs.comp_aestronglyMeasurable (hm.sub hχ₀m.aestronglyMeasurable)
  · filter_upwards [hev] with k hk
    refine (ae_restrict_iff' hK.measurableSet).2 (ae_of_all _ fun y hy => ?_)
    rcases hk.chi_mem y (hKsub hy) with h1 | h1 <;> rcases h01 y with h2 | h2 <;>
      rw [Real.norm_eq_abs, abs_abs, h1, h2] <;> norm_num
  · filter_upwards [ae_restrict_of_ae hχ₀ae] with y hy
    simpa using (hy.sub_const (χ₀ y)).abs

end IsVariationalSolutionQ

end InnerVariational
