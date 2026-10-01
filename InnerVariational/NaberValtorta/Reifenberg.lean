/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Registry.Reifenberg
public import InnerVariational.NaberValtorta.Discrete
import Mathlib.Tactic.Monotonicity.Lemmas

/-!
# Naber–Valtorta Reifenberg theorems on an arbitrary ball

The discrete and rectifiable Reifenberg theorems of A. Naber and D. Valtorta,
*Rectifiable-Reifenberg and the regularity of stationary and minimizing harmonic maps*, Ann. of
Math. (2) 185 (2017), no. 1, 131–227, Theorems 3.4 and 3.3 ([NV]), are stated in
`Registry.discrete_reifenberg` and `Registry.rectifiable_reifenberg` (proved in gmt-foundations,
https://github.com/willmfeldman/gmt-foundations, v0.1.0), normalised to `B_1 ⊆ B_2`. The proof of
Lemma 7.1 of D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and
compactness for non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025),
no. 3, DOI 10.1002/cpa.22226; arXiv:2306.10131 (numbering of arXiv v2), is carried out here in a
localised form (see `NaberValtorta/VolumeEstimate.lean`) that applies them on balls
`B_σ(p) ⊆ B_{2σ}(p)` of every size. This file states them on such balls.

* `discrete_reifenberg_ball`: [NV, Theorem 3.4] on `B_σ(p) ⊆ B_{2σ}(p)`. The conclusion becomes
  `Σ_{x_j ∈ B_σ(p)} r_j^{n-1} < D σ^{n-1}`.
* `rectifiable_reifenberg_ball`: [NV, Theorem 3.3] on `B_σ(p) ⊆ B_{2σ}(p)`.
* `discrete_reifenberg_finset`: the discrete form for a `2s`-separated `Finset` with equal weights.

The statements are the images of the normalised ones under `z ↦ p + σ z`. All the quantities
scale correctly ([NV], remark after Definition 3.1): for `μ_σ = σ^{n-1} T_#μ`, the identity
`β²_{μ_σ}(Tz, σρ) = β²_μ(z, ρ)` holds (`jonesBetaSq_smul_map_affine`), and `dρ/ρ` is invariant.

Both ball forms are proved from the normalised statements by this change of variables. The
rectifiable form also uses the scaling
`ℋ^k(A) = σ^k ℋ^k(T⁻¹ A)` (`hausdorffN_eq_mul_preimage_affine`, from
`Measure.hausdorffMeasure_smul₀` and translation invariance) and the identity
`ℋ^{n-1}⌊S = σ^{n-1} T_#(ℋ^{n-1}⌊T⁻¹S)`.
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational.NaberValtorta

variable {n : ℕ}

/-- `dρ/ρ` is invariant under `ρ ↦ σ ρ`:
`∫_0^{στ} g(ρ) dρ/ρ = ∫_0^τ g(σρ) dρ/ρ` for `σ > 0`. -/
theorem setLIntegral_Ioo_div_mul {σ : ℝ} (hσ : 0 < σ) (τ : ℝ) (g : ℝ → ℝ≥0∞) :
    ∫⁻ ρ in Ioo 0 (σ * τ), g ρ / ENNReal.ofReal ρ =
      ∫⁻ ρ in Ioo 0 τ, g (σ * ρ) / ENNReal.ofReal ρ := by
  have he : MeasurableEmbedding (σ * ·) :=
    (Homeomorph.mulLeft₀ σ hσ.ne').measurableEmbedding
  have hpre : (σ * ·) ⁻¹' Ioo 0 (σ * τ) = Ioo 0 τ := by
    ext ρ
    simp only [mem_preimage, mem_Ioo]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨pos_of_mul_pos_right h1 hσ.le, lt_of_mul_lt_mul_left h2 hσ.le⟩
    · rintro ⟨h1, h2⟩
      exact ⟨mul_pos hσ h1, mul_lt_mul_of_pos_left h2 hσ⟩
  calc ∫⁻ ρ in Ioo 0 (σ * τ), g ρ / ENNReal.ofReal ρ
      = ENNReal.ofReal σ * ∫⁻ ρ in Ioo 0 (σ * τ), g ρ / ENNReal.ofReal ρ
          ∂(Measure.map (σ * ·) volume) := by
        rw [Real.map_volume_mul_left hσ.ne', Measure.restrict_smul, lintegral_smul_measure,
          smul_eq_mul, ← mul_assoc, abs_inv, abs_of_pos hσ, ← ENNReal.ofReal_mul hσ.le,
          mul_inv_cancel₀ hσ.ne', ENNReal.ofReal_one, one_mul]
    _ = ENNReal.ofReal σ * ∫⁻ ρ in Ioo 0 τ, g (σ * ρ) / ENNReal.ofReal (σ * ρ) := by
        rw [he.restrict_map, he.lintegral_map, hpre]
    _ = ∫⁻ ρ in Ioo 0 τ, g (σ * ρ) / ENNReal.ofReal ρ := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine setLIntegral_congr_fun measurableSet_Ioo fun ρ _ => ?_
        rw [ENNReal.ofReal_mul hσ.le, ← mul_div_assoc,
          ENNReal.mul_div_mul_left _ _ (ENNReal.ofReal_pos.2 hσ).ne' ENNReal.ofReal_ne_top]

open scoped Classical in
/-- **Discrete Reifenberg on an arbitrary ball** ([NV, Theorem 3.4] with Remark 3.2, `k = n − 1`,
rescaled to `B_σ(p) ⊆ B_{2σ}(p)`). There are `δ(n) > 0` and `D(n)` with the following property. Let
`{B_{r_j}(x_j)}_{j ∈ J}` be a finite collection of disjoint balls contained in `B_{2σ}(p)`, and
`μ = Σ_j ω_{n-1} r_j^{n-1} δ_{x_j}`. If for every ball `B_τ(y) ⊆ B_{2σ}(p)`
`∫_{B_τ(y)} ∫_0^τ β²_μ(z, ρ) dρ/ρ dμ(z) < δ² τ^{n-1}`,
then `Σ_{x_j ∈ B_σ(p)} r_j^{n-1} < D σ^{n-1}`.

Proved from `Registry.discrete_reifenberg` by the change of variables `z = p + σ z'`:
the measure `μ` is `σ^{n-1} T_# μ'` for the rescaled family `B_{r_j/σ}((x_j − p)/σ)`. -/
theorem discrete_reifenberg_ball (hn : 2 ≤ n) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ D : ℝ, ∀ (p : Rn n) (σ : ℝ), 0 < σ →
      ∀ {ι : Type} (J : Finset ι) (x : ι → Rn n) (r : ι → ℝ),
      (∀ j ∈ J, 0 < r j) → (∀ j ∈ J, ball (x j) (r j) ⊆ ball p (2 * σ)) →
      (J : Set ι).Pairwise (fun i j => Disjoint (ball (x i) (r i)) (ball (x j) (r j))) →
      (∀ (y : Rn n) (τ : ℝ), 0 < τ → ball y τ ⊆ ball p (2 * σ) →
        ∫⁻ z in ball y τ, (∫⁻ ρ in Ioo 0 τ,
            jonesBetaSq (∑ j ∈ J, ENNReal.ofReal (unitBallVolume (n - 1) * r j ^ (n - 1)) •
              Measure.dirac (x j)) z ρ / ENNReal.ofReal ρ)
          ∂(∑ j ∈ J, ENNReal.ofReal (unitBallVolume (n - 1) * r j ^ (n - 1)) •
              Measure.dirac (x j)) <
          ENNReal.ofReal (δ ^ 2 * τ ^ (n - 1))) →
      ∑ j ∈ J with x j ∈ ball p σ, r j ^ (n - 1) < D * σ ^ (n - 1) := by
  obtain ⟨δ, hδ, D, hD⟩ := Registry.discrete_reifenberg (n := n) hn
  refine ⟨δ, hδ, D, fun p σ hσ ι J x r hr hsub hdisj hjones => ?_⟩
  have hTe := measurableEmbedding_affine (p := p) hσ.ne'
  have hsurj : Function.Surjective fun z : Rn n => p + σ • z :=
    ((Homeomorph.smulOfNeZero σ hσ.ne').trans (Homeomorph.addLeft p)).surjective
  set ω := unitBallVolume (n - 1) with hω
  set x' : ι → Rn n := fun j => σ⁻¹ • (x j - p) with hx'
  set r' : ι → ℝ := fun j => r j / σ with hr'
  have hTx : ∀ j, p + σ • x' j = x j := fun j => by
    rw [hx']
    dsimp only
    rw [smul_smul, mul_inv_cancel₀ hσ.ne', one_smul, add_sub_cancel]
  have hσr : ∀ j, σ * r' j = r j := fun j => by
    rw [hr']
    dsimp only
    field_simp
  have hball : ∀ j, ball (x' j) (r' j) = (fun z => p + σ • z) ⁻¹' ball (x j) (r j) := fun j => by
    rw [← preimage_affine_ball hσ (x' j) (r' j), hTx j, hσr j]
  have hball0 : ∀ ρ, ball (0 : Rn n) ρ = (fun z => p + σ • z) ⁻¹' ball p (σ * ρ) := fun ρ => by
    rw [← preimage_affine_ball hσ (0 : Rn n) ρ, smul_zero, add_zero]
  have hball02 : ball (0 : Rn n) 2 = (fun z => p + σ • z) ⁻¹' ball p (2 * σ) := by
    rw [hball0, mul_comm]
  set μ := discreteMeasure J (fun j => ENNReal.ofReal (ω * r j ^ (n - 1))) x with hμ_def
  set μ' := discreteMeasure J (fun j => ENNReal.ofReal (ω * r' j ^ (n - 1))) x' with hμ'_def
  have hμ : μ = ENNReal.ofReal (σ ^ (n - 1)) • μ'.map (fun z => p + σ • z) := by
    rw [hμ_def, hμ'_def, map_discreteMeasure _ _ _ hTe.measurable, smul_discreteMeasure]
    unfold discreteMeasure
    refine Finset.sum_congr rfl fun j _ => ?_
    dsimp only
    congr 1
    · rw [← ENNReal.ofReal_mul (pow_nonneg hσ.le (n - 1))]
      congr 1
      rw [← hσr j, mul_pow]
      ring
    · simp only [Function.comp_apply, hTx j]
  have hA0 : ENNReal.ofReal (σ ^ (n - 1)) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
  -- change of variables in the outer integral
  have hgen : ∀ (y' : Rn n) (τ' : ℝ) (f : Rn n → ℝ≥0∞),
      ∫⁻ z in ball (p + σ • y') (σ * τ'), f z ∂μ =
        ENNReal.ofReal (σ ^ (n - 1)) * ∫⁻ z' in ball y' τ', f (p + σ • z') ∂μ' := by
    intro y' τ' f
    rw [hμ, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul, hTe.restrict_map,
      hTe.lintegral_map, preimage_affine_ball hσ]
  -- change of variables in the inner integral
  have hI : ∀ (τ' : ℝ) (z' : Rn n),
      ∫⁻ ρ in Ioo 0 (σ * τ'), jonesBetaSq μ (p + σ • z') ρ / ENNReal.ofReal ρ =
        ∫⁻ ρ in Ioo 0 τ', jonesBetaSq μ' z' ρ / ENNReal.ofReal ρ := by
    intro τ' z'
    rw [setLIntegral_Ioo_div_mul hσ τ' fun ρ => jonesBetaSq μ (p + σ • z') ρ, hμ]
    simp_rw [jonesBetaSq_smul_map_affine μ' hσ]
  have key := hD J x' r' (fun j hj => div_pos (hr j hj) hσ)
    (fun j hj => by
      rw [hball j, hball02]
      exact preimage_mono (hsub j hj))
    (fun i hi j hj hij => by
      dsimp only
      rw [hball i, hball j]
      exact (hdisj hi hj hij).preimage _)
    (by
      intro y' τ' hτ' hy'
      have hyb : ball (p + σ • y') (σ * τ') ⊆ ball p (2 * σ) := by
        rw [← hsurj.preimage_subset_preimage_iff, preimage_affine_ball hσ, ← hball02]
        exact hy'
      have h : ∫⁻ z in ball (p + σ • y') (σ * τ'),
          (∫⁻ ρ in Ioo 0 (σ * τ'), jonesBetaSq μ z ρ / ENNReal.ofReal ρ) ∂μ <
          ENNReal.ofReal (δ ^ 2 * (σ * τ') ^ (n - 1)) :=
        hjones _ _ (by positivity) hyb
      rw [hgen y' τ', lintegral_congr fun z' => hI τ' z', mul_pow,
        show δ ^ 2 * (σ ^ (n - 1) * τ' ^ (n - 1)) = σ ^ (n - 1) * (δ ^ 2 * τ' ^ (n - 1)) by ring,
        ENNReal.ofReal_mul (pow_nonneg hσ.le (n - 1))] at h
      exact (ENNReal.mul_lt_mul_iff_right hA0 ENNReal.ofReal_ne_top).1 h)
  have hfilt : J.filter (fun j => x j ∈ ball p σ) = J.filter (fun j => x' j ∈ ball 0 1) := by
    refine Finset.filter_congr fun j _ => ?_
    rw [hball0 1, mem_preimage, hTx j, mul_one]
  calc ∑ j ∈ J with x j ∈ ball p σ, r j ^ (n - 1)
      = ∑ j ∈ J with x' j ∈ ball 0 1, σ ^ (n - 1) * r' j ^ (n - 1) := by
        rw [hfilt]
        exact Finset.sum_congr rfl fun j _ => by rw [← mul_pow, hσr j]
    _ = σ ^ (n - 1) * ∑ j ∈ J with x' j ∈ ball 0 1, r' j ^ (n - 1) := (Finset.mul_sum ..).symm
    _ < σ ^ (n - 1) * D := mul_lt_mul_of_pos_left key (by positivity)
    _ = D * σ ^ (n - 1) := mul_comm _ _

open scoped Pointwise in
/-- Scaling of `ℋ^k` under the homothety `T z = p + σ z`, `σ > 0`:
`ℋ^k(A) = σ^k ℋ^k(T⁻¹ A)` for every set `A`. -/
theorem hausdorffN_eq_mul_preimage_affine {p : Rn n} {σ : ℝ} (hσ : 0 < σ) (k : ℕ)
    (A : Set (Rn n)) :
    hausdorffN n k A =
      ENNReal.ofReal (σ ^ k) * hausdorffN n k ((fun z : Rn n => p + σ • z) ⁻¹' A) := by
  have hpre : (fun z : Rn n => p + σ • z) ⁻¹' A = σ⁻¹ • ((fun z : Rn n => p + z) ⁻¹' A) := by
    rw [← preimage_smul₀ hσ.ne']
    rfl
  have htr : Measure.hausdorffMeasure (k : ℝ) ((fun z : Rn n => p + z) ⁻¹' A) =
      Measure.hausdorffMeasure (k : ℝ) A :=
    (IsometryEquiv.addLeft p).hausdorffMeasure_preimage _ A
  have hc : ENNReal.ofReal (σ ^ k) * ((‖σ⁻¹‖₊ ^ (k : ℝ) : ℝ≥0) : ℝ≥0∞) = 1 := by
    rw [NNReal.rpow_natCast, ← nnnorm_pow, ← enorm_eq_nnnorm, ← ofReal_norm,
      Real.norm_of_nonneg (by positivity), ← ENNReal.ofReal_mul (by positivity), ← mul_pow,
      mul_inv_cancel₀ hσ.ne', one_pow, ENNReal.ofReal_one]
  simp only [hausdorffN, Measure.smul_apply, smul_eq_mul]
  rw [hpre, Measure.hausdorffMeasure_smul₀ (Nat.cast_nonneg k) (inv_ne_zero hσ.ne'), htr,
    ENNReal.smul_def, smul_eq_mul]
  rw [mul_left_comm, ← mul_assoc (ENNReal.ofReal (σ ^ k)), hc, one_mul]

/-- **Rectifiable Reifenberg on an arbitrary ball** ([NV, Theorem 3.3] with Remark 3.2,
`k = n − 1`, rescaled to `B_σ(p) ⊆ B_{2σ}(p)`). Only the rectifiability conclusion is stated, under
an added upper density bound (and `δ` may depend on its constant `C`); the sharp measure bound of
[NV, Theorem 3.3] is not needed. For every `C` there is `δ(n, C) > 0`
with the following property. Let `S ⊆ B_{2σ}(p)` be Borel with `ℋ^{n-1}(S) < ∞` and
`ℋ^{n-1}(S ∩ B_r(x)) ≤ C r^{n-1}` for every ball, and assume that for every ball
`B_τ(y) ⊆ B_{2σ}(p)`
`∫_{S ∩ B_τ(y)} ∫_0^τ β²_{ℋ^{n-1}⌊S}(z, ρ) dρ/ρ dℋ^{n-1}(z) < δ² τ^{n-1}`.
Then `S ∩ B_σ(p)` is countably `ℋ^{n-1}`-rectifiable. The bound is scale invariant, so the same
`C` works after rescaling. -/
theorem rectifiable_reifenberg_ball (hn : 2 ≤ n) (C : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (p : Rn n) (σ : ℝ), 0 < σ →
      ∀ S : Set (Rn n), MeasurableSet S → S ⊆ ball p (2 * σ) →
      hausdorffN n (n - 1) S < ∞ →
      (∀ (x : Rn n) (r : ℝ), 0 < r →
        hausdorffN n (n - 1) (S ∩ ball x r) ≤ ENNReal.ofReal (C * r ^ (n - 1))) →
      (∀ (y : Rn n) (τ : ℝ), 0 < τ → ball y τ ⊆ ball p (2 * σ) →
        ∫⁻ z in S ∩ ball y τ, (∫⁻ ρ in Ioo 0 τ,
            jonesBetaSq ((hausdorffN n (n - 1)).restrict S) z ρ / ENNReal.ofReal ρ)
          ∂hausdorffN n (n - 1) < ENNReal.ofReal (δ ^ 2 * τ ^ (n - 1))) →
      IsCountablyRectifiable n (n - 1) (S ∩ ball p σ) := by
  obtain ⟨δ, hδ, hR⟩ := Registry.rectifiable_reifenberg (n := n) hn C
  refine ⟨δ, hδ, fun p σ hσ S hS hSsub hSfin hloc hjones => ?_⟩
  set T : Rn n → Rn n := fun z => p + σ • z with hT
  have hTe : MeasurableEmbedding T := measurableEmbedding_affine hσ.ne'
  have hsurj : Function.Surjective T :=
    ((Homeomorph.smulOfNeZero σ hσ.ne').trans (Homeomorph.addLeft p)).surjective
  set ℋ := hausdorffN n (n - 1) with hℋ
  set c := ENNReal.ofReal (σ ^ (n - 1)) with hc
  have hc0 : c ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have hscale : ∀ A, ℋ A = c * ℋ (T ⁻¹' A) := hausdorffN_eq_mul_preimage_affine hσ (n - 1)
  have hTinv : ∀ x, T (σ⁻¹ • (x - p)) = x := fun x => by
    simp only [hT, smul_smul, mul_inv_cancel₀ hσ.ne', one_smul, add_sub_cancel]
  have hball0 : ∀ ρ, ball (0 : Rn n) ρ = T ⁻¹' ball p (σ * ρ) := fun ρ => by
    rw [← preimage_affine_ball hσ (0 : Rn n) ρ, smul_zero, add_zero]
  have hball01 : ball (0 : Rn n) 1 = T ⁻¹' ball p σ := by rw [hball0, mul_one]
  have hball02 : ball (0 : Rn n) 2 = T ⁻¹' ball p (2 * σ) := by rw [hball0, mul_comm]
  set S' := T ⁻¹' S with hS'
  have hμ : ℋ.restrict S = c • (ℋ.restrict S').map T := by
    ext A hA
    rw [Measure.smul_apply, Measure.map_apply hTe.measurable hA, Measure.restrict_apply hA,
      Measure.restrict_apply (hTe.measurable hA), smul_eq_mul, hscale (A ∩ S), preimage_inter]
  have hgen : ∀ (y' : Rn n) (τ' : ℝ) (f : Rn n → ℝ≥0∞),
      ∫⁻ z in ball (T y') (σ * τ'), f z ∂(ℋ.restrict S) =
        c * ∫⁻ z' in ball y' τ', f (T z') ∂(ℋ.restrict S') := by
    intro y' τ' f
    rw [hμ, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul, hTe.restrict_map,
      hTe.lintegral_map, preimage_affine_ball hσ]
  have hI : ∀ (τ' : ℝ) (z' : Rn n),
      ∫⁻ ρ in Ioo 0 (σ * τ'), jonesBetaSq (ℋ.restrict S) (T z') ρ / ENNReal.ofReal ρ =
        ∫⁻ ρ in Ioo 0 τ', jonesBetaSq (ℋ.restrict S') z' ρ / ENNReal.ofReal ρ := by
    intro τ' z'
    rw [setLIntegral_Ioo_div_mul hσ τ' fun ρ => jonesBetaSq (ℋ.restrict S) (T z') ρ, hμ]
    exact lintegral_congr fun ρ => congrArg (· / ENNReal.ofReal ρ)
      (jonesBetaSq_smul_map_affine (p := p) (ℋ.restrict S') hσ z' ρ)
  have hS'fin : ℋ S' < ∞ := by
    rw [hscale S] at hSfin
    exact ENNReal.lt_top_of_mul_ne_top_right hSfin.ne hc0
  have hS'loc : ∀ (x' : Rn n) (r' : ℝ), 0 < r' →
      ℋ (S' ∩ ball x' r') ≤ ENNReal.ofReal (C * r' ^ (n - 1)) := by
    intro x' r' hr'
    have h := hloc (T x') (σ * r') (by positivity)
    rw [hscale, preimage_inter, preimage_affine_ball hσ,
      show C * (σ * r') ^ (n - 1) = σ ^ (n - 1) * (C * r' ^ (n - 1)) by ring,
      ENNReal.ofReal_mul (pow_nonneg hσ.le (n - 1))] at h
    exact (ENNReal.mul_le_mul_iff_right hc0 ENNReal.ofReal_ne_top).1 h
  have h2 := hR S' (hS.preimage hTe.measurable)
    (by rw [hball02]; exact preimage_mono hSsub) hS'fin hS'loc
    (by
      intro y' τ' hτ' hy'
      have hyb : ball (T y') (σ * τ') ⊆ ball p (2 * σ) := by
        rw [← hsurj.preimage_subset_preimage_iff, preimage_affine_ball hσ, ← hball02]
        exact hy'
      have h := hjones (T y') (σ * τ') (by positivity) hyb
      rw [inter_comm, ← Measure.restrict_restrict measurableSet_ball, hgen y' τ',
        lintegral_congr fun z' => hI τ' z', mul_pow,
        show δ ^ 2 * (σ ^ (n - 1) * τ' ^ (n - 1)) = σ ^ (n - 1) * (δ ^ 2 * τ' ^ (n - 1)) by ring,
        ENNReal.ofReal_mul (pow_nonneg hσ.le (n - 1))] at h
      rw [inter_comm, ← Measure.restrict_restrict measurableSet_ball]
      exact (ENNReal.mul_lt_mul_iff_right hc0 ENNReal.ofReal_ne_top).1 h)
  obtain ⟨f, hf, hnull⟩ := h2
  have hTlip : LipschitzWith (Real.toNNReal σ) T := LipschitzWith.of_dist_le_mul fun a b => by
    simp only [hT, dist_add_left, dist_smul₀, Real.norm_eq_abs, abs_of_pos hσ,
      Real.coe_toNNReal _ hσ.le, le_refl]
  refine ⟨fun i => T ∘ f i, fun i => ?_, ?_⟩
  · obtain ⟨K, hK⟩ := hf i
    exact ⟨_, hTlip.comp hK⟩
  · rw [hscale, preimage_sdiff, preimage_inter, preimage_iUnion, ← hball01]
    simp_rw [range_comp, hTe.injective.preimage_image]
    rw [hnull, mul_zero]

open scoped Classical in
/-- `discrete_reifenberg_ball` for the discrete measure `Σ_{y ∈ F} ω_{n-1} s^{n-1} δ_y` of a
`2s`-separated finite set `F ⊆ B_σ(p)` with `s ≤ σ`: if the Jones condition holds on every ball
`B_τ(y) ⊆ B_{2σ}(p)`, then `#F · s^{n-1} < D σ^{n-1}`. -/
theorem discrete_reifenberg_finset (hn : 2 ≤ n) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ D : ℝ, ∀ (p : Rn n) (σ s : ℝ), 0 < s → s ≤ σ →
      ∀ F : Finset (Rn n), ↑F ⊆ ball p σ →
      (F : Set (Rn n)).Pairwise (fun y z => 2 * s ≤ dist y z) →
      (∀ (y : Rn n) (τ : ℝ), 0 < τ → ball y τ ⊆ ball p (2 * σ) →
        ∫⁻ z in ball y τ, (∫⁻ ρ in Ioo 0 τ,
            jonesBetaSq (discreteMeasure F (fun _ => ENNReal.ofReal
              (unitBallVolume (n - 1) * s ^ (n - 1))) id) z ρ / ENNReal.ofReal ρ)
          ∂(discreteMeasure F (fun _ => ENNReal.ofReal
              (unitBallVolume (n - 1) * s ^ (n - 1))) id) <
          ENNReal.ofReal (δ ^ 2 * τ ^ (n - 1))) →
      (F.card : ℝ) * s ^ (n - 1) < D * σ ^ (n - 1) := by
  obtain ⟨δ, hδ, D, hD⟩ := discrete_reifenberg_ball (n := n) hn
  refine ⟨δ, hδ, D, fun p σ s hs hsσ F hFp hF hjones => ?_⟩
  have hσ : 0 < σ := hs.trans_le hsσ
  have key := hD p σ hσ F id (fun _ => s) (fun _ _ => hs)
    (fun y hy => ball_subset_ball' (by
      have := mem_ball.1 (hFp hy)
      simp only [id]
      linarith))
    (fun y hy z hz hyz => ball_disjoint_ball (by
      have := hF hy hz hyz
      simp only [id]
      linarith))
    hjones
  have hfilter : F.filter (fun y => id y ∈ ball p σ) = F :=
    Finset.filter_true_of_mem fun y hy => hFp hy
  rwa [hfilter, Finset.sum_const, nsmul_eq_mul] at key

end InnerVariational.NaberValtorta
