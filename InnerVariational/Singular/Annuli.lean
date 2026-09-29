/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Defs.Quantities
import Mathlib.Data.Real.StarOrdered
import Mathlib.Algebra.Order.Ring.Star
public import GMTFoundations.Defs.Setup

/-!
# From annuli to balls: the assembly step of Lemma 8.5 (1)

In the proof of Lemma 8.5 of D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff
measure, and compactness for non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78
(2025), no. 3, DOI 10.1002/cpa.22226; arXiv:2306.10131 (numbering of arXiv v2): once the
renormalized functions converge to the profile on every annulus `B_R \ B_{R/2}`, they converge on
every ball
`B_R`. This file proves that step abstractly, for a pair `f, q : ℝⁿ → E` and a height function
`H : ℝ → ℝ` (in the application `H = H_x(u; ·)` and `(f, q) = (u, |(y − x)·ν|)` or
`(∇u, ∇|(y − x)·ν|)`).

## Main result

`tendsto_ball_of_tendsto_annulus`: suppose that
* `H > 0` is nondecreasing near `0` and `H(c r)/H(r) → 1` for every `c > 0`;
* on the annuli `A(ρ) = B_{7ρ/8}(x) \ B_{5ρ/8}(x)` (the rescaled annulus `B_{7/8} \ B_{5/8}` of
  the proof of Theorem 5.3), with the normalization of
  scale `ρ`, `ρ^{-m} H(ρ)⁻¹ ∫_{A(ρ)} |f − √H(ρ) α q|² → 0`;
* `∫_{B_s(x)} |f|² ≤ K s^m H(s)` and `∫_{B_s(x)} |q|² ≤ M s^m` for small `s`.
Then `r^{-m} H(r)⁻¹ ∫_{B_{Rr}(x)} |f − √H(r) α q|² → 0` for every `R > 0`.

Proof: `B_{Rr}(x)` is the ball `B_{Rrθ^J}(x)` plus `J` annuli `B_{Rrθ^j} \ B_{Rrθ^{j+1}}` with
`θ = 5/7`. Each annulus is `A(ρ_j)` for `ρ_j = (8/7) R θ^j r`, and the change of normalization
from `ρ_j` to `r` costs a factor `H(ρ_j)/H(r) → 1` (`tendsto_annulus_mul`). The small ball is
bounded by `(2K + 2α²M) (Rθ^J)^m`.
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

@[expose] public noncomputable section

namespace InnerVariational

namespace Singular

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- `‖a + b‖² ≤ 2‖a‖² + 2‖b‖²`. -/
theorem norm_add_sq_le_two_mul (a b : E) : ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h := norm_add_le a b
  have h0 := norm_nonneg (a + b)
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), norm_nonneg a, norm_nonneg b]

/-- `‖a − k b‖² ≤ 2‖a − k' b‖² + 2 (k − k')² ‖b‖²`. -/
theorem norm_sub_smul_sq_le (a b : E) (k k' : ℝ) :
    ‖a - k • b‖ ^ 2 ≤ 2 * ‖a - k' • b‖ ^ 2 + 2 * ((k - k') ^ 2 * ‖b‖ ^ 2) := by
  have e : a - k • b = (a - k' • b) + (k' - k) • b := by
    rw [sub_smul]; abel
  rw [e]
  refine (norm_add_sq_le_two_mul _ _).trans_eq ?_
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, ← neg_sub k k', neg_sq]

/-- **Telescoping over balls.** For `0 ≤ t`, `0 ≤ θ ≤ 1` and `F` integrable on `B_t(x)`,
`∫_{B_t} F = ∫_{B_{tθ^J}} F + Σ_{j < J} ∫_{B_{tθ^j} \ B_{tθ^{j+1}}} F`. -/
theorem setIntegral_ball_eq_add_sum {F : Rn n → ℝ} {x : Rn n} {t θ : ℝ} (ht : 0 ≤ t)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hF : IntegrableOn F (ball x t)) (J : ℕ) :
    ∫ y in ball x t, F y = (∫ y in ball x (t * θ ^ J), F y) +
      ∑ j ∈ Finset.range J, ∫ y in ball x (t * θ ^ j) \ ball x (t * θ ^ (j + 1)), F y := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [ih, Finset.sum_range_succ]
    have hsub : ball x (t * θ ^ (J + 1)) ⊆ ball x (t * θ ^ J) := by
      refine ball_subset_ball (mul_le_mul_of_nonneg_left ?_ ht)
      rw [pow_succ]
      exact mul_le_of_le_one_right (pow_nonneg hθ0 _) hθ1
    have hJ : ball x (t * θ ^ J) ⊆ ball x t :=
      ball_subset_ball (mul_le_of_le_one_right ht (pow_le_one₀ hθ0 hθ1))
    rw [setIntegral_diff measurableSet_ball (hF.mono_set hJ) hsub]
    ring

variable {x : Rn n} {f q : Rn n → E} {m : ℕ} {H : ℝ → ℝ} {α r₀ K M : ℝ}

/-- The annulus `A(ρ) = B_{7ρ/8}(x) \ B_{5ρ/8}(x)`, on which the one-dimensional limit of
Theorem 5.3 is identified. -/
abbrev annulusAt (x : Rn n) (ρ : ℝ) : Set (Rn n) := ball x (ρ * (7 / 8)) \ ball x (ρ * (5 / 8))

/-- **Change of normalization on one annulus.** Under the hypotheses of
`tendsto_ball_of_tendsto_annulus`, for every `c > 0`,
`r^{-m} H(r)⁻¹ ∫_{A(cr)} |f − √H(r) α q|² → 0`. -/
theorem tendsto_annulus_mul (hr₀ : 0 < r₀) (hHpos : ∀ s ∈ Ioo 0 r₀, 0 < H s)
    (hratio : ∀ c, 0 < c → Tendsto (fun r => H (c * r) / H r) (𝓝[>] 0) (𝓝 1))
    (hint : ∀ k : ℝ, IntegrableOn (fun y => ‖f y - k • q y‖ ^ 2) (ball x r₀))
    (hqint : IntegrableOn (fun y => ‖q y‖ ^ 2) (ball x r₀))
    (hq : ∀ s, 0 < s → ∫ y in ball x s, ‖q y‖ ^ 2 ≤ M * s ^ m)
    (hcons : Tendsto (fun ρ => (∫ y in annulusAt x ρ, ‖f y - (√(H ρ) * α) • q y‖ ^ 2) /
      (ρ ^ m * H ρ)) (𝓝[>] 0) (𝓝 0))
    {c : ℝ} (hc : 0 < c) :
    Tendsto (fun r => (∫ y in annulusAt x (c * r), ‖f y - (√(H r) * α) • q y‖ ^ 2) /
      (r ^ m * H r)) (𝓝[>] 0) (𝓝 0) := by
  have hcr : Tendsto (fun r : ℝ => c * r) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h := ((continuous_const_mul c).tendsto (0 : ℝ)).mono_left
        (nhdsWithin_le_nhds (s := Ioi 0))
      simpa using h
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact mul_pos hc hs
  have hrat := hratio c hc
  -- the bound
  set X : ℝ → ℝ := fun ρ => (∫ y in annulusAt x ρ, ‖f y - (√(H ρ) * α) • q y‖ ^ 2) /
    (ρ ^ m * H ρ) with hX
  set g : ℝ → ℝ := fun r => 2 * (X (c * r) * c ^ m * (H (c * r) / H r)) +
    2 * (α ^ 2 * (√(H (c * r) / H r) - 1) ^ 2 * (M * c ^ m)) with hg
  have hglim : Tendsto g (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun r => X (c * r) * c ^ m * (H (c * r) / H r)) (𝓝[>] 0)
        (𝓝 (0 * c ^ m * 1)) := ((hcons.comp hcr).mul_const _).mul hrat
    have hs : Tendsto (fun r => √(H (c * r) / H r)) (𝓝[>] 0) (𝓝 1) := by
      simpa using (Real.continuous_sqrt.tendsto 1).comp hrat
    have h2 : Tendsto (fun r => α ^ 2 * (√(H (c * r) / H r) - 1) ^ 2 * (M * c ^ m))
        (𝓝[>] 0) (𝓝 (α ^ 2 * (1 - 1) ^ 2 * (M * c ^ m))) :=
      (((hs.sub_const 1).pow 2).const_mul _).mul_const _
    simpa [hg] using (h1.const_mul 2).add (h2.const_mul 2)
  refine squeeze_zero' ?_ ?_ hglim
  · filter_upwards [Ioo_mem_nhdsGT hr₀] with r hr
    have hH := hHpos r hr
    have := hr.1
    exact div_nonneg (setIntegral_nonneg (measurableSet_ball.diff measurableSet_ball)
      fun _ _ => sq_nonneg _) (by positivity)
  · have hr₀' : 0 < min r₀ (r₀ / c) := lt_min hr₀ (div_pos hr₀ hc)
    filter_upwards [Ioo_mem_nhdsGT hr₀'] with r hr
    have hr0 := hr.1
    have hr1 : r < r₀ := hr.2.trans_le (min_le_left _ _)
    have hcr1 : c * r < r₀ := by
      have := hr.2.trans_le (min_le_right _ _)
      rw [lt_div_iff₀ hc] at this
      linarith
    have hH := hHpos r ⟨hr0, hr1⟩
    have hHc := hHpos (c * r) ⟨mul_pos hc hr0, hcr1⟩
    set ρ := c * r with hρ
    have hρ0 : 0 < ρ := mul_pos hc hr0
    set A := annulusAt x ρ with hA
    have hAm : MeasurableSet A := measurableSet_ball.diff measurableSet_ball
    have hAB : A ⊆ ball x r₀ := diff_subset.trans (ball_subset_ball (by nlinarith))
    have hAρ : A ⊆ ball x ρ := diff_subset.trans (ball_subset_ball (by nlinarith))
    set k := √(H r) * α
    set k' := √(H ρ) * α
    -- pointwise and integrated bound
    have hI : ∫ y in A, ‖f y - k • q y‖ ^ 2 ≤
        2 * (∫ y in A, ‖f y - k' • q y‖ ^ 2) + 2 * ((k - k') ^ 2 * ∫ y in A, ‖q y‖ ^ 2) := by
      have hi1 := (hint k').mono_set hAB
      have hi2 := hqint.mono_set hAB
      rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul, ← integral_add
        (hi1.const_mul 2) ((hi2.const_mul _).const_mul 2)]
      exact integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _)
        ((hi1.const_mul 2).add ((hi2.const_mul _).const_mul 2))
        (Eventually.of_forall fun y => norm_sub_smul_sq_le _ _ _ _)
    have hQ : ∫ y in A, ‖q y‖ ^ 2 ≤ M * ρ ^ m :=
      (setIntegral_mono_set (hqint.mono_set (ball_subset_ball (by linarith)))
        (Eventually.of_forall fun _ => sq_nonneg _) hAρ.eventuallyLE).trans (hq ρ hρ0)
    have hkk : (k - k') ^ 2 = α ^ 2 * H r * (√(H ρ / H r) - 1) ^ 2 := by
      have hs : √(H ρ / H r) * √(H r) = √(H ρ) := by
        rw [← Real.sqrt_mul (div_nonneg hHc.le hH.le), div_mul_cancel₀ _ hH.ne']
      have hsr : √(H r) ^ 2 = H r := Real.sq_sqrt hH.le
      calc (k - k') ^ 2 = α ^ 2 * (√(H r) - √(H ρ)) ^ 2 := by ring
        _ = α ^ 2 * (√(H r) - √(H ρ / H r) * √(H r)) ^ 2 := by rw [hs]
        _ = α ^ 2 * √(H r) ^ 2 * (√(H ρ / H r) - 1) ^ 2 := by ring
        _ = _ := by rw [hsr]
    have hXρ : ∫ y in A, ‖f y - k' • q y‖ ^ 2 = X ρ * (ρ ^ m * H ρ) := by
      rw [hX]
      dsimp only
      rw [div_mul_cancel₀ _ (by positivity)]
    have hw : 0 < r ^ m * H r := by positivity
    rw [div_le_iff₀ hw]
    refine hI.trans ?_
    rw [hXρ]
    have hQ' : (k - k') ^ 2 * ∫ y in A, ‖q y‖ ^ 2 ≤ (k - k') ^ 2 * (M * ρ ^ m) :=
      mul_le_mul_of_nonneg_left hQ (sq_nonneg _)
    have e1 : X ρ * (ρ ^ m * H ρ) = X ρ * c ^ m * (H ρ / H r) * (r ^ m * H r) := by
      rw [hρ, mul_pow]
      field_simp
    have e2 : (k - k') ^ 2 * (M * ρ ^ m) =
        α ^ 2 * (√(H ρ / H r) - 1) ^ 2 * (M * c ^ m) * (r ^ m * H r) := by
      rw [hkk, hρ, mul_pow]
      ring
    rw [hg]
    dsimp only
    rw [← hρ]
    have e3 : (2 * (X ρ * c ^ m * (H ρ / H r)) +
        2 * (α ^ 2 * (√(H ρ / H r) - 1) ^ 2 * (M * c ^ m))) * (r ^ m * H r) =
        2 * (X ρ * c ^ m * (H ρ / H r) * (r ^ m * H r)) + 2 * ((k - k') ^ 2 * (M * ρ ^ m)) := by
      rw [e2]; ring
    rw [e3, ← e1]
    linarith

/-- **Assembly of the annuli** (proof of Lemma 8.5 (1)), with `H` nondecreasing up to a factor
`D`: `H(s) ≤ D H(r)` for `s ≤ r` near `0`. See the module docstring. -/
theorem tendsto_ball_of_tendsto_annulus' {D : ℝ} (hD : 0 ≤ D) (hm : m ≠ 0) (hr₀ : 0 < r₀)
    (hHpos : ∀ s ∈ Ioo 0 r₀, 0 < H s)
    (hHmono : ∀ s ∈ Ioo 0 r₀, ∀ r ∈ Ioo 0 r₀, s ≤ r → H s ≤ D * H r)
    (hratio : ∀ c, 0 < c → Tendsto (fun r => H (c * r) / H r) (𝓝[>] 0) (𝓝 1))
    (hint : ∀ k : ℝ, IntegrableOn (fun y => ‖f y - k • q y‖ ^ 2) (ball x r₀))
    (hqint : IntegrableOn (fun y => ‖q y‖ ^ 2) (ball x r₀)) (hK : 0 ≤ K)
    (hf : ∀ s ∈ Ioo 0 r₀, ∫ y in ball x s, ‖f y‖ ^ 2 ≤ K * (s ^ m * H s))
    (hq : ∀ s, 0 < s → ∫ y in ball x s, ‖q y‖ ^ 2 ≤ M * s ^ m)
    (hcons : Tendsto (fun ρ => (∫ y in annulusAt x ρ, ‖f y - (√(H ρ) * α) • q y‖ ^ 2) /
      (ρ ^ m * H ρ)) (𝓝[>] 0) (𝓝 0))
    {R : ℝ} (hR : 0 < R) :
    Tendsto (fun r => (∫ y in ball x (R * r), ‖f y - (√(H r) * α) • q y‖ ^ 2) /
      (r ^ m * H r)) (𝓝[>] 0) (𝓝 0) := by
  have hM : 0 ≤ M := by
    have h1 := hq 1 one_pos
    rw [one_pow, mul_one] at h1
    exact (setIntegral_nonneg measurableSet_ball fun _ _ => sq_nonneg _).trans h1
  set θ : ℝ := 5 / 7 with hθ
  have hθ0 : 0 ≤ θ := by norm_num [hθ]
  have hθ1 : θ ≤ 1 := by norm_num [hθ]
  set B : ℝ := 2 * K * D + 2 * α ^ 2 * M with hB
  have hB0 : 0 ≤ B := add_nonneg (mul_nonneg (mul_nonneg two_pos.le hK) hD) (by positivity)
  rw [Metric.tendsto_nhds]
  intro η hη
  -- choose `J` with `B (R θ^J)^m < η / 2` and `R θ^J ≤ 1`
  have h1 : Tendsto (fun J : ℕ => R * θ ^ J) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 (by norm_num [hθ])).const_mul R
  have hlim : Tendsto (fun J : ℕ => B * (R * θ ^ J) ^ m) atTop (𝓝 0) := by
    have h2 := (h1.pow m).const_mul B
    rwa [zero_pow hm, mul_zero] at h2
  obtain ⟨J, hJ, hJ1⟩ := ((hlim.eventually (gt_mem_nhds (half_pos hη))).and
    (h1.eventually (eventually_le_nhds one_pos))).exists
  -- the annulus terms
  set c : ℕ → ℝ := fun j => R * θ ^ j * (8 / 7) with hc
  have hcpos : ∀ j, 0 < c j := fun j => by rw [hc]; positivity
  have hann : ∀ j, Tendsto (fun r => (∫ y in annulusAt x (c j * r),
      ‖f y - (√(H r) * α) • q y‖ ^ 2) / (r ^ m * H r)) (𝓝[>] 0) (𝓝 0) := fun j =>
    tendsto_annulus_mul hr₀ hHpos hratio hint hqint hq hcons (hcpos j)
  have hsum := tendsto_finsetSum (Finset.range J) fun j _ => hann j
  rw [Finset.sum_const_zero] at hsum
  have hR₀ : 0 < r₀ / (R + 1) := div_pos hr₀ (by linarith)
  filter_upwards [hsum.eventually (gt_mem_nhds (half_pos hη)), Ioo_mem_nhdsGT hR₀,
    Ioo_mem_nhdsGT hr₀] with r hr hrR hr1
  have hr0 := hr1.1
  have hH := hHpos r hr1
  have hw : 0 < r ^ m * H r := by positivity
  have hRr : R * r < r₀ := by
    have := hrR.2
    rw [lt_div_iff₀ (by linarith)] at this
    nlinarith
  set k := √(H r) * α with hk
  set F : Rn n → ℝ := fun y => ‖f y - k • q y‖ ^ 2 with hF
  have hFint : IntegrableOn F (ball x (R * r)) := (hint k).mono_set (ball_subset_ball hRr.le)
  have htel := setIntegral_ball_eq_add_sum (F := F) (x := x) (by positivity : 0 ≤ R * r) hθ0 hθ1
    hFint J
  -- identify the annuli
  have hannEq : ∀ j, ball x (R * r * θ ^ j) \ ball x (R * r * θ ^ (j + 1)) =
      annulusAt x (c j * r) := by
    intro j
    rw [annulusAt, hc]
    congr 2
    · ring
    · rw [hθ, pow_succ]; ring
  simp_rw [hannEq] at htel
  -- small ball
  set s := R * r * θ ^ J with hs
  have hs0 : 0 < s := by rw [hs]; positivity
  have hsR : s = R * θ ^ J * r := by rw [hs]; ring
  have hsr : s ≤ r := by rw [hsR]; exact mul_le_of_le_one_left hr0.le hJ1
  have hs1 : s < r₀ := hsr.trans_lt hr1.2
  have hsmall : ∫ y in ball x s, F y ≤ B * (R * θ ^ J) ^ m * (r ^ m * H r) := by
    have hsub : ball x s ⊆ ball x r₀ := ball_subset_ball hs1.le
    have hi1 := ((hint 0).mono_set hsub)
    have hi2 := hqint.mono_set hsub
    have hpt : ∀ y, F y ≤ 2 * ‖f y - (0 : ℝ) • q y‖ ^ 2 + 2 * (k ^ 2 * ‖q y‖ ^ 2) := by
      intro y
      have := norm_sub_smul_sq_le (f y) (q y) k 0
      simpa [hF] using this
    have h1 : ∫ y in ball x s, F y ≤ 2 * (∫ y in ball x s, ‖f y - (0 : ℝ) • q y‖ ^ 2) +
        2 * (k ^ 2 * ∫ y in ball x s, ‖q y‖ ^ 2) := by
      rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul, ← integral_add
        (hi1.const_mul 2) ((hi2.const_mul _).const_mul 2)]
      exact integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _)
        ((hi1.const_mul 2).add ((hi2.const_mul _).const_mul 2)) (Eventually.of_forall hpt)
    have hfs : ∫ y in ball x s, ‖f y - (0 : ℝ) • q y‖ ^ 2 ≤ K * (s ^ m * (D * H r)) := by
      simp only [zero_smul, sub_zero]
      exact (hf s ⟨hs0, hs1⟩).trans (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hHmono s ⟨hs0, hs1⟩ r hr1 hsr) (by positivity)) hK)
    have hk2 : k ^ 2 = H r * α ^ 2 := by rw [hk, mul_pow, Real.sq_sqrt hH.le]
    have hqs := mul_le_mul_of_nonneg_left (hq s hs0) (sq_nonneg k)
    have e : B * (R * θ ^ J) ^ m * (r ^ m * H r) =
        2 * (K * (s ^ m * (D * H r))) + 2 * (k ^ 2 * (M * s ^ m)) := by
      rw [hk2, hsR, hB, mul_pow]; ring
    rw [e]
    linarith
  have hnn : 0 ≤ (∫ y in ball x (R * r), F y) / (r ^ m * H r) :=
    div_nonneg (setIntegral_nonneg measurableSet_ball fun _ _ => sq_nonneg _) hw.le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  change (∫ y in ball x (R * r), F y) / (r ^ m * H r) < η
  rw [htel, add_div, Finset.sum_div]
  have h3 : (∫ y in ball x s, F y) / (r ^ m * H r) < η / 2 := by
    rw [div_lt_iff₀ hw]
    calc _ ≤ B * (R * θ ^ J) ^ m * (r ^ m * H r) := hsmall
      _ < η / 2 * (r ^ m * H r) := mul_lt_mul_of_pos_right hJ hw
  have h4 : ∑ j ∈ Finset.range J, (∫ y in annulusAt x (c j * r), F y) / (r ^ m * H r) <
      η / 2 := hr
  linarith

/-- **Assembly of the annuli** (proof of Lemma 8.5 (1)). See the module docstring. -/
theorem tendsto_ball_of_tendsto_annulus (hm : m ≠ 0) (hr₀ : 0 < r₀)
    (hHpos : ∀ s ∈ Ioo 0 r₀, 0 < H s) (hHmono : MonotoneOn H (Ioo 0 r₀))
    (hratio : ∀ c, 0 < c → Tendsto (fun r => H (c * r) / H r) (𝓝[>] 0) (𝓝 1))
    (hint : ∀ k : ℝ, IntegrableOn (fun y => ‖f y - k • q y‖ ^ 2) (ball x r₀))
    (hqint : IntegrableOn (fun y => ‖q y‖ ^ 2) (ball x r₀)) (hK : 0 ≤ K)
    (hf : ∀ s ∈ Ioo 0 r₀, ∫ y in ball x s, ‖f y‖ ^ 2 ≤ K * (s ^ m * H s))
    (hq : ∀ s, 0 < s → ∫ y in ball x s, ‖q y‖ ^ 2 ≤ M * s ^ m)
    (hcons : Tendsto (fun ρ => (∫ y in annulusAt x ρ, ‖f y - (√(H ρ) * α) • q y‖ ^ 2) /
      (ρ ^ m * H ρ)) (𝓝[>] 0) (𝓝 0))
    {R : ℝ} (hR : 0 < R) :
    Tendsto (fun r => (∫ y in ball x (R * r), ‖f y - (√(H r) * α) • q y‖ ^ 2) /
      (r ^ m * H r)) (𝓝[>] 0) (𝓝 0) :=
  tendsto_ball_of_tendsto_annulus' zero_le_one hm hr₀ hHpos
    (fun _ hs _ hr hsr => (hHmono hs hr hsr).trans_eq (one_mul _).symm) hratio hint hqint hK hf
    hq hcons hR

end Singular

end InnerVariational
