/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Basic.Setup
public import InnerVariational.Vendor.Analysis.FrechetKolmogorovCompact
public import InnerVariational.Vendor.Analysis.Cutoff
public import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Order.Ring.Star
public import GMTFoundations.Defs.Setup

/-!
# Local `Lᵖ` compactness from cut-off Fréchet–Kolmogorov bounds

If for every smooth cut-off `ζ` compactly supported in an open `U ⊆ ℝᵈ` the products `ζ u_n` are
bounded in `Lᵖ(ℝᵈ)` and uniformly continuous under translations in `Lᵖ`, then a subsequence of
`u_n` converges in `Lᵖ_loc(U)`.

Proof: a compact exhaustion `K_m` of `U` with cut-offs `ζ_m = 1` on `K_m`; for each `m` the
classes of `ζ_m u_n` form a totally bounded set (Fréchet–Kolmogorov,
`totallyBounded_range_toLp_of_translation`); the sequence `n ↦ (ζ_m u_n)_m` lies in a compact
subset of the countable product `∏_m Lᵖ`, which is first countable, so one subsequence converges in
every coordinate (this replaces the diagonal argument). The limits `L_m` agree a.e. on `K_m`, and
are glued with `Nat.find` into one measurable `u₀`.

## Main results

* `exhaust`: an explicit compact exhaustion of an open set.
* `exists_tendstoLpLoc_subseq_of_cutoff`: the local compactness criterion.
-/

@[expose] public section

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal ContDiff

namespace InnerVariational.Vendor.Analysis

variable {d : ℕ}

/-! ### A compact exhaustion of an open set -/

/-- The compact exhaustion `K_m = B̄_m(0) ∩ {x : dist(x, Uᶜ) ≥ 1/(m+1)}` of an open `U`. -/
def exhaust (U : Set (Rn d)) (m : ℕ) : Set (Rn d) :=
  closedBall 0 m ∩ {x | ∀ y ∉ U, ((m : ℝ) + 1)⁻¹ ≤ dist x y}

theorem isClosed_exhaust (U : Set (Rn d)) (m : ℕ) : IsClosed (exhaust U m) := by
  refine isClosed_closedBall.inter ?_
  simp only [ofPred_forall]
  exact isClosed_biInter fun y _ ↦
    isClosed_le continuous_const (continuous_id.dist continuous_const)

theorem isCompact_exhaust (U : Set (Rn d)) (m : ℕ) : IsCompact (exhaust U m) :=
  (isCompact_closedBall 0 (m : ℝ)).of_isClosed_subset (isClosed_exhaust U m) inter_subset_left

theorem exhaust_subset (U : Set (Rn d)) (m : ℕ) : exhaust U m ⊆ U := by
  intro x hx
  by_contra hxU
  have := hx.2 x hxU
  rw [dist_self] at this
  have : (0 : ℝ) < ((m : ℝ) + 1)⁻¹ := by positivity
  linarith

theorem exhaust_mono (U : Set (Rn d)) : Monotone (exhaust U) := by
  intro m M hmM x hx
  have hmM' : (m : ℝ) ≤ M := by exact_mod_cast hmM
  refine ⟨mem_closedBall.2 ((mem_closedBall.1 hx.1).trans hmM'), fun y hy ↦ ?_⟩
  refine le_trans ?_ (hx.2 y hy)
  gcongr

theorem exists_subset_exhaust {U K : Set (Rn d)} (hU : IsOpen U) (hK : IsCompact K)
    (hKU : K ⊆ U) : ∃ M, K ⊆ exhaust U M := by
  obtain ⟨δ, hδ, hδK⟩ := hK.exists_cthickening_subset_open hU hKU
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  obtain ⟨M, hM⟩ := exists_nat_gt (max R δ⁻¹)
  refine ⟨M, fun x hx ↦ ⟨?_, fun y hy ↦ ?_⟩⟩
  · exact mem_closedBall.2 ((mem_closedBall.1 (hR hx)).trans
      ((le_max_left _ _).trans hM.le))
  · by_contra hlt
    push Not at hlt
    have hinv : ((M : ℝ) + 1)⁻¹ ≤ δ := by
      rw [inv_le_comm₀ (by positivity) hδ]
      linarith [le_max_right R δ⁻¹]
    exact hy (hδK (mem_cthickening_of_dist_le y x δ K hx
      (by rw [dist_comm]; linarith)))

/-! ### The local compactness criterion -/

/-- **Local `Lᵖ` compactness from cut-off Fréchet–Kolmogorov bounds.** -/
theorem exists_tendstoLpLoc_subseq_of_cutoff {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    {U : Set (Rn d)} (hU : IsOpen U) (u : ℕ → Rn d → ℝ)
    (hcut : ∀ ζ : Rn d → ℝ, ContDiff ℝ ∞ ζ → HasCompactSupport ζ → tsupport ζ ⊆ U →
      (∀ x, 0 ≤ ζ x ∧ ζ x ≤ 1) →
      (∀ n, MemLp (fun x ↦ ζ x * u n x) p volume) ∧
      (∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ n, eLpNorm (fun x ↦ ζ x * u n x) p volume ≤ M) ∧
      ∀ ε : ℝ≥0∞, 0 < ε → ∃ δ > 0, ∀ n, ∀ h : Rn d, ‖h‖ < δ →
        eLpNorm (fun x ↦ ζ (x + h) * u n (x + h) - ζ x * u n x) p volume ≤ ε) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ u₀ : Rn d → ℝ, Measurable u₀ ∧
      ∀ K ⊆ U, IsCompact K →
        Tendsto (fun n ↦ eLpNorm (u (φ n) - u₀) p (volume.restrict K)) atTop (𝓝 0) := by
  classical
  set K := exhaust U
  choose ζ hζs hζc hζU hζ01 hζ1 using fun m ↦
    exists_smooth_cutoff (isCompact_exhaust U m) hU (exhaust_subset U m)
  have hc := fun m ↦ hcut (ζ m) (hζs m) (hζc m) (hζU m) (hζ01 m)
  have hmem := fun m ↦ (hc m).1
  have htr := fun m ↦ (hc m).2.2
  choose M hM hbdd using fun m ↦ (hc m).2.1
  set f : ℕ → ℕ → Rn d → ℝ := fun m n x ↦ ζ m x * u n x with hf
  have hsupp : ∀ m n, ∀ᵐ x ∂(volume : Measure (Rn d)), x ∉ tsupport (ζ m) → f m n x = 0 :=
    fun m n ↦ Eventually.of_forall fun x hx ↦ by
      simp only [hf, image_eq_zero_of_notMem_tsupport hx, zero_mul]
  have hTB : ∀ m, TotallyBounded (range fun n ↦ (hmem m n).toLp (f m n)) := fun m ↦
    totallyBounded_range_toLp_of_translation hp (f m) (hmem m) (hζc m).isCompact.isBounded
      (hsupp m) (hM m) (hbdd m) (htr m)
  set F : ℕ → (ℕ → Lp ℝ p (volume : Measure (Rn d))) := fun n m ↦ (hmem m n).toLp (f m n)
  have hC : IsCompact (Set.pi univ fun m ↦ closure (range fun n ↦ (hmem m n).toLp (f m n))) :=
    isCompact_univ_pi fun m ↦ (hTB m).closure.isCompact_of_isClosed isClosed_closure
  obtain ⟨L, -, φ, hφ, hlim⟩ := hC.tendsto_subseq (x := F)
    (fun n ↦ fun m _ ↦ subset_closure (mem_range_self n))
  have hconv : ∀ m, Tendsto (fun n ↦ eLpNorm (f m (φ n) - ⇑(L m)) p volume) atTop (𝓝 0) := by
    intro m
    have h1 := tendsto_pi_nhds.1 hlim m
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'] at h1
    refine h1.congr fun n ↦ eLpNorm_congr_ae ?_
    exact (hmem m (φ n)).coeFn_toLp.sub EventuallyEq.rfl
  set v : ℕ → Rn d → ℝ := fun m ↦ ⇑(L m)
  have hv : ∀ m, Measurable (v m) := fun m ↦ (Lp.stronglyMeasurable (L m)).measurable
  -- the limits agree on the smaller set
  have hagree : ∀ m M, m ≤ M → ∀ᵐ x ∂(volume : Measure (Rn d)), x ∈ K m → v m x = v M x := by
    intro m M hmM
    have hKm : MeasurableSet (K m) := (isClosed_exhaust U m).measurableSet
    have hzero : eLpNorm (v m - v M) p (volume.restrict (K m)) = 0 := by
      have hsum : Tendsto (fun n ↦ eLpNorm (f m (φ n) - v m) p volume +
          eLpNorm (f M (φ n) - v M) p volume) atTop (𝓝 0) := by
        simpa using (hconv m).add (hconv M)
      refine le_antisymm (ge_of_tendsto' hsum fun n ↦ ?_) bot_le
      have heq : (v m - v M) =ᵐ[volume.restrict (K m)]
          (f M (φ n) - v M) - (f m (φ n) - v m) := by
        filter_upwards [ae_restrict_mem hKm] with x hx
        simp only [Pi.sub_apply, hf, hζ1 m x hx, hζ1 M x (exhaust_mono U hmM hx), one_mul]
        ring
      rw [eLpNorm_congr_ae heq]
      refine (eLpNorm_sub_le Fact.out).trans ?_
      rw [add_comm]
      exact add_le_add (eLpNorm_mono_measure _ Measure.restrict_le_self)
        (eLpNorm_mono_measure _ Measure.restrict_le_self)
    rw [eLpNorm_eq_zero_iff (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'] at hzero
    rw [← ae_restrict_iff' hKm]
    filter_upwards [hzero] with x hx
    simpa [sub_eq_zero] using hx
  -- glue the limits
  have hex : ∀ x, ∃ m, x ∈ K m ∪ Uᶜ := by
    intro x
    by_cases hx : x ∈ U
    · obtain ⟨m, hm⟩ := exists_subset_exhaust hU isCompact_singleton (singleton_subset_iff.2 hx)
      exact ⟨m, Or.inl (hm rfl)⟩
    · exact ⟨0, Or.inr hx⟩
  obtain ⟨u₀, hu₀, hu₀def⟩ : ∃ u₀ : Rn d → ℝ, Measurable u₀ ∧ ∀ x, ∃ m, x ∈ K m ∪ Uᶜ ∧
      (∀ k < m, x ∉ K k ∪ Uᶜ) ∧ u₀ x = v m x :=
    by
    refine ⟨fun x ↦ v (Nat.find (hex x)) x, ?_,
      fun x ↦ ⟨_, Nat.find_spec (hex x), fun _ hk ↦ Nat.find_min (hex x) hk, rfl⟩⟩
    convert Measurable.find (p := fun n x ↦ x ∈ K n ∪ Uᶜ) hv
      (fun m ↦ (isClosed_exhaust U m).measurableSet.union hU.measurableSet.compl) hex
  have hu₀K : ∀ M, ∀ᵐ x ∂(volume : Measure (Rn d)), x ∈ K M → u₀ x = v M x := by
    intro M
    have hall : ∀ᵐ x ∂(volume : Measure (Rn d)), ∀ m : ℕ, m ≤ M → x ∈ K m → v m x = v M x := by
      rw [ae_all_iff]; intro m
      by_cases hmM : m ≤ M
      · filter_upwards [hagree m M hmM] with x hx _ using hx
      · exact Eventually.of_forall fun x h ↦ absurd h hmM
    filter_upwards [hall] with x hx hxK
    obtain ⟨m, hm, hmin, hxm⟩ := hu₀def x
    have hxU : x ∈ U := exhaust_subset U M hxK
    have hmM : m ≤ M := by
      by_contra hlt
      exact hmin M (not_le.1 hlt) (Or.inl hxK)
    rw [hxm]
    exact hx m hmM (hm.resolve_right fun h ↦ h hxU)
  refine ⟨φ, hφ, u₀, hu₀, fun C hCU hCc ↦ ?_⟩
  obtain ⟨M', hM'⟩ := exists_subset_exhaust hU hCc hCU
  have hKM : MeasurableSet (K M') := (isClosed_exhaust U M').measurableSet
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hconv M')
    (fun _ ↦ zero_le) (fun n ↦ ?_)
  calc eLpNorm (u (φ n) - u₀) p (volume.restrict C)
      ≤ eLpNorm (u (φ n) - u₀) p (volume.restrict (K M')) :=
        eLpNorm_mono_measure _ (Measure.restrict_mono hM' le_rfl)
    _ = eLpNorm (f M' (φ n) - v M') p (volume.restrict (K M')) := by
        refine eLpNorm_congr_ae ?_
        filter_upwards [ae_restrict_mem hKM, ae_restrict_of_ae (hu₀K M')] with x hx hx'
        simp only [Pi.sub_apply, hf, hζ1 M' x hx, one_mul, hx' hx]
    _ ≤ eLpNorm (f M' (φ n) - v M') p volume :=
        eLpNorm_mono_measure _ Measure.restrict_le_self

end InnerVariational.Vendor.Analysis
