/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Basic.Setup
import Mathlib.Order.CompletePartialOrder
import Mathlib.Data.Real.Hom
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Tactic.Monotonicity.Lemmas
public import GMTFoundations.Defs.Setup

/-!
# Points in general position and Gram–Schmidt with bounded coefficients

The linear algebra in the proof of Theorem 6.3 of D. Kriventsov and G. S. Weiss,
*Rectifiability, finite Hausdorff measure, and compactness for non-minimizing Bernoulli free
boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3, DOI 10.1002/cpa.22226; arXiv:2306.10131
(numbering of arXiv v2).

* `IsGeneralPosition δ a₀ a`: each point `a i` (`i : Fin k`) has distance `≥ δ` from the affine
  span of `a₀` and the earlier points `a j`, `j < i`.
* `exists_isGeneralPosition_of_not_subset_thickening`: the greedy selection. A set `E ⊆ ℝⁿ` that
  lies in no `ε`-neighbourhood of an affine subspace of dimension `≤ n − 2` contains points
  `a₀, a 0, …, a (n-2)` in `ε`-general position.
* `orthonormal_gramSchmidtNormed` and `exists_coeff_gramSchmidtNormed`: for points in
  `δ`-general position in a ball of radius `R`, Gram–Schmidt applied to `a i − a₀` gives
  an orthonormal family `e`. Each `e i` is a combination `∑_{j ≤ i} c_j (a j − a₀)` with
  `|c_j| ≤ δ⁻¹ (1 + 2R/δ)^i`.
* `exists_generalPosition_orthonormal`: the two combined, in the form used in the proof of
  Theorem 6.3.

## Coefficient bound in the proof of Theorem 6.3

The proof states that the coefficients have absolute value `≤ 1/δ`; this does not hold in
general. In `ℝ²`, take
`a₀ = (-1/2, 0)`, `a₁ = (-1/2 + δ, 0)`, `a₂ = (1/2, δ)`, all in the closed unit ball for small `δ`,
with `|a₁ − a₀| = δ` and `dist(a₂, a₀ + ℝ(a₁ − a₀)) = δ`. Then `e₁ = (1,0) = (a₁ − a₀)/δ` and
`e₂ = (0,1) = (a₂ − a₀)/δ − (a₁ − a₀)/δ²`. The representation is unique, so the coefficient
`−1/δ²` is forced. We prove `|c| ≤ δ⁻¹ (1 + 2R/δ)^i` (`genPosCoeffBound`); a constant
`C(δ, n)` suffices, which is all that is used in the proof of Theorem 6.3.
-/

open Metric Set InnerProductSpace Module
open scoped RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational

/-! ### Gram–Schmidt with the normalised vectors -/

section GramSchmidt

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι] [WellFoundedLT ι]

theorem gramSchmidtNormed_eq_smul (v : ι → E) (i : ι) :
    gramSchmidtNormed ℝ v i = ‖gramSchmidt ℝ v i‖⁻¹ • gramSchmidt ℝ v i := by
  simp [gramSchmidtNormed]

/-- The Gram–Schmidt recursion written with the normalised vectors:
`g_i = v_i − ∑_{l < i} ⟪e_l, v_i⟫ e_l`. -/
theorem gramSchmidt_eq_sub_sum_inner (v : ι → E) (i : ι) :
    gramSchmidt ℝ v i =
      v i - ∑ l ∈ Finset.Iio i, ⟪gramSchmidtNormed ℝ v l, v i⟫ • gramSchmidtNormed ℝ v l := by
  rw [gramSchmidt_def ℝ v i]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Submodule.starProjection_singleton, gramSchmidtNormed_eq_smul, real_inner_smul_left,
    smul_smul]
  congr 1
  simp only [RCLike.ofReal_real_eq_id, id]
  ring

/-- `v_i − g_i` lies in the span of the earlier `v_l`. -/
theorem sub_gramSchmidt_mem_span (v : ι → E) (i : ι) :
    v i - gramSchmidt ℝ v i ∈ Submodule.span ℝ (v '' Iio i) := by
  rw [gramSchmidt_eq_sub_sum_inner, sub_sub_cancel, ← span_gramSchmidt_Iio ℝ v i]
  refine Submodule.sum_mem _ fun l hl => Submodule.smul_mem _ _ ?_
  rw [gramSchmidtNormed_eq_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, Finset.mem_Iio.1 hl, rfl⟩)

/-- If no `g_i` vanishes, the normalised Gram–Schmidt family is orthonormal. -/
theorem orthonormal_gramSchmidtNormed_of_ne_zero {v : ι → E}
    (h : ∀ i, gramSchmidt ℝ v i ≠ 0) : Orthonormal ℝ (gramSchmidtNormed ℝ v) := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · rw [gramSchmidtNormed_eq_smul]
    exact norm_smul_inv_norm (h i)
  · dsimp only
    rw [gramSchmidtNormed_eq_smul, gramSchmidtNormed_eq_smul, real_inner_smul_left,
      real_inner_smul_right, gramSchmidt_orthogonal ℝ v hij, mul_zero, mul_zero]

end GramSchmidt

/-! ### General position -/

variable {n k : ℕ}

/-- `a₀, a 0, …, a (k-1)` are in `δ`-general position (proof of Theorem 6.3): each `a i` has
distance at least `δ` from the affine span of `a₀` and the `a j` with `j < i`. -/
def IsGeneralPosition (δ : ℝ) (a₀ : Rn n) (a : Fin k → Rn n) : Prop :=
  ∀ i, δ ≤ infDist (a i) (affineSpan ℝ (insert a₀ (a '' Iio i)))

/-- The coefficient bound `δ⁻¹ (1 + 2R/δ)^i` for the `i`-th Gram–Schmidt vector (0-indexed). -/
def genPosCoeffBound (δ R : ℝ) (i : ℕ) : ℝ :=
  δ⁻¹ * (1 + 2 * R / δ) ^ i

theorem genPosCoeffBound_mono {δ R : ℝ} (hδ : 0 < δ) (hR : 0 ≤ R) {i j : ℕ} (hij : i ≤ j) :
    genPosCoeffBound δ R i ≤ genPosCoeffBound δ R j := by
  unfold genPosCoeffBound
  gcongr
  · exact le_add_of_nonneg_right (by positivity)

/-- The differences `a i − a₀` span the direction of the affine span. -/
theorem span_sub_le_direction (a₀ : Rn n) (a : Fin k → Rn n) (s : Set (Fin k)) :
    Submodule.span ℝ ((fun j => a j - a₀) '' s) ≤
      (affineSpan ℝ (insert a₀ (a '' s))).direction := by
  rw [direction_affineSpan, vectorSpan_eq_span_vsub_set_right ℝ (mem_insert a₀ _)]
  apply Submodule.span_mono
  rintro _ ⟨j, hj, rfl⟩
  exact ⟨a j, mem_insert_of_mem _ ⟨j, hj, rfl⟩, rfl⟩

/-- In `δ`-general position the unnormalised Gram–Schmidt vectors have length `≥ δ`:
`‖g_i‖` is the distance from `a i` to the affine span of `a₀` and the earlier points. -/
theorem le_norm_gramSchmidt {δ : ℝ} {a₀ : Rn n} {a : Fin k → Rn n}
    (h : IsGeneralPosition δ a₀ a) (i : Fin k) :
    δ ≤ ‖gramSchmidt ℝ (fun j => a j - a₀) i‖ := by
  set v : Fin k → Rn n := fun j => a j - a₀
  have hw := span_sub_le_direction a₀ a (Iio i) (sub_gramSchmidt_mem_span v i)
  have hq : (v i - gramSchmidt ℝ v i) +ᵥ a₀ ∈ affineSpan ℝ (insert a₀ (a '' Iio i)) :=
    AffineSubspace.vadd_mem_of_mem_direction hw (subset_affineSpan ℝ _ (mem_insert a₀ _))
  refine (h i).trans ((infDist_le_dist_of_mem hq).trans (le_of_eq ?_))
  rw [dist_eq_norm, vadd_eq_add]
  congr 1
  simp only [v]
  abel

/-- **Orthonormality.** For `δ > 0`, Gram–Schmidt applied to `a i − a₀` gives an orthonormal
family. -/
theorem orthonormal_gramSchmidtNormed {δ : ℝ} (hδ : 0 < δ) {a₀ : Rn n} {a : Fin k → Rn n}
    (h : IsGeneralPosition δ a₀ a) :
    Orthonormal ℝ (gramSchmidtNormed ℝ fun j => a j - a₀) :=
  orthonormal_gramSchmidtNormed_of_ne_zero fun i =>
    norm_pos_iff.1 (hδ.trans_le (le_norm_gramSchmidt h i))

/-- `(1 + 2R/δ)^i = 1 + 2R ∑_{l < i} δ⁻¹ (1 + 2R/δ)^l`, summed over `Fin k`. -/
theorem one_add_sum_genPosCoeffBound {δ : ℝ} (hδ : 0 < δ) (R : ℝ) (i : Fin k) :
    1 + ∑ l ∈ Finset.Iio i, 2 * R * genPosCoeffBound δ R l = (1 + 2 * R / δ) ^ (i : ℕ) := by
  have hsum : ∑ l ∈ Finset.Iio i, 2 * R * genPosCoeffBound δ R l =
      ∑ m ∈ Finset.range i, 2 * R * genPosCoeffBound δ R m := by
    rw [← Nat.Iio_eq_range, ← Fin.map_valEmbedding_Iio, Finset.sum_map]
    rfl
  rw [hsum, ← Finset.mul_sum]
  unfold genPosCoeffBound
  rw [← Finset.mul_sum]
  have := geom_sum_mul (1 + 2 * R / δ) i
  rw [add_sub_cancel_left] at this
  have hδ' : δ ≠ 0 := hδ.ne'
  calc 1 + 2 * R * (δ⁻¹ * ∑ m ∈ Finset.range i, (1 + 2 * R / δ) ^ m)
      = 1 + (∑ m ∈ Finset.range i, (1 + 2 * R / δ) ^ m) * (2 * R / δ) := by
        field_simp
    _ = _ := by rw [this]; ring

/-- **Bounded Gram–Schmidt coefficients** (proof of Theorem 6.3; the proof
states `|c_j| ≤ 1/δ`, see the module docstring for the bound proved here). Let
`a₀, a 0, …, a (k-1)` be in `δ`-general position in `closedBall x R`, and let `e` be the normalised
Gram–Schmidt family of the `a j − a₀`. Then `e i = ∑_j c_j (a j − a₀)` with `c_j = 0` for `j > i`
and `|c_j| ≤ δ⁻¹ (1 + 2R/δ)^i`. -/
theorem exists_coeff_gramSchmidtNormed {δ R : ℝ} (hδ : 0 < δ) {x a₀ : Rn n} {a : Fin k → Rn n}
    (h : IsGeneralPosition δ a₀ a) (ha₀ : a₀ ∈ closedBall x R)
    (ha : ∀ i, a i ∈ closedBall x R) (i : Fin k) :
    ∃ c : Fin k → ℝ, (∀ j, i < j → c j = 0) ∧ (∀ j, |c j| ≤ genPosCoeffBound δ R i) ∧
      gramSchmidtNormed ℝ (fun j => a j - a₀) i = ∑ j, c j • (a j - a₀) := by
  set v : Fin k → Rn n := fun j => a j - a₀ with hv_def
  set e := gramSchmidtNormed ℝ v with he_def
  have he : Orthonormal ℝ e := orthonormal_gramSchmidtNormed hδ h
  have hR : 0 ≤ R := dist_nonneg.trans (mem_closedBall.1 ha₀)
  have hv : ∀ j, ‖v j‖ ≤ 2 * R := fun j => by
    rw [hv_def, ← dist_eq_norm]
    have h1 := mem_closedBall.1 (ha j)
    have h2 := mem_closedBall'.1 ha₀
    linarith [dist_triangle (a j) x a₀]
  have hinner : ∀ l j, |⟪e l, v j⟫| ≤ 2 * R := fun l j => by
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [he.1 l, one_mul]
    exact hv j
  induction i using WellFoundedLT.induction with
  | _ i ih =>
  choose! c hc0 hcb hce using ih
  set g := gramSchmidt ℝ v i with hg_def
  have hg : δ ≤ ‖g‖ := le_norm_gramSchmidt h i
  have hg0 : 0 < ‖g‖ := hδ.trans_le hg
  refine ⟨fun j => ‖g‖⁻¹ * ((if j = i then 1 else 0) -
    ∑ l ∈ Finset.Iio i, ⟪e l, v i⟫ * c l j), ?_, ?_, ?_⟩
  · intro j hij
    have hji : j ≠ i := hij.ne'
    have hsum : ∑ l ∈ Finset.Iio i, ⟪e l, v i⟫ * c l j = 0 :=
      Finset.sum_eq_zero fun l hl => by
        rw [hc0 l (Finset.mem_Iio.1 hl) j ((Finset.mem_Iio.1 hl).trans hij), mul_zero]
    simp [hji, hsum]
  · intro j
    have hsum : |∑ l ∈ Finset.Iio i, ⟪e l, v i⟫ * c l j| ≤
        ∑ l ∈ Finset.Iio i, 2 * R * genPosCoeffBound δ R l := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l hl => ?_)
      rw [abs_mul]
      exact mul_le_mul (hinner l i) (hcb l (Finset.mem_Iio.1 hl) j) (abs_nonneg _)
        (by positivity)
    have hite : |(if j = i then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
    rw [abs_mul, abs_inv, abs_norm, genPosCoeffBound, ← one_add_sum_genPosCoeffBound hδ R i]
    calc ‖g‖⁻¹ * |(if j = i then (1 : ℝ) else 0) - ∑ l ∈ Finset.Iio i, ⟪e l, v i⟫ * c l j|
        ≤ ‖g‖⁻¹ * (1 + ∑ l ∈ Finset.Iio i, 2 * R * genPosCoeffBound δ R l) := by
          gcongr
          exact (abs_sub _ _).trans (add_le_add hite hsum)
      _ ≤ δ⁻¹ * (1 + ∑ l ∈ Finset.Iio i, 2 * R * genPosCoeffBound δ R l) := by
          gcongr
          exact add_nonneg zero_le_one (Finset.sum_nonneg fun l _ => by
            unfold genPosCoeffBound
            have : 0 ≤ 1 + 2 * R / δ := by positivity
            positivity)
  · have hrec := gramSchmidt_eq_sub_sum_inner v i
    rw [← hg_def] at hrec
    have hrec' : g = v i - ∑ l ∈ Finset.Iio i, ⟪e l, v i⟫ • ∑ j, c l j • v j := by
      rw [hrec]
      congr 1
      exact Finset.sum_congr rfl fun l hl => by rw [← hce l (Finset.mem_Iio.1 hl)]
    rw [he_def, gramSchmidtNormed_eq_smul, ← hg_def, hrec']
    simp only [mul_smul, sub_smul, ← Finset.smul_sum, Finset.sum_sub_distrib, ite_smul, one_smul,
      zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    congr 2
    simp only [Finset.sum_smul, Finset.smul_sum, mul_smul]
    exact Finset.sum_comm

/-! ### Greedy selection -/

theorem image_snoc_Iio_castSucc {α : Type*} {m : ℕ} (a : Fin m → α) (b : α) (j : Fin m) :
    (Fin.snoc a b : Fin (m + 1) → α) '' Iio (Fin.castSucc j) = a '' Iio j := by
  ext y
  simp only [mem_image, mem_Iio]
  constructor
  · rintro ⟨l, hl, rfl⟩
    cases l using Fin.lastCases with
    | last => exact absurd hl (not_lt.2 (Fin.le_last _))
    | cast l => exact ⟨l, Fin.castSucc_lt_castSucc_iff.1 hl, by simp⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨Fin.castSucc l, Fin.castSucc_lt_castSucc_iff.2 hl, by simp⟩

theorem image_snoc_Iio_last {α : Type*} {m : ℕ} (a : Fin m → α) (b : α) :
    (Fin.snoc a b : Fin (m + 1) → α) '' Iio (Fin.last m) = range a := by
  ext y
  simp only [mem_image, mem_Iio, mem_range]
  constructor
  · rintro ⟨l, hl, rfl⟩
    cases l using Fin.lastCases with
    | last => exact absurd hl (lt_irrefl _)
    | cast l => exact ⟨l, by simp⟩
  · rintro ⟨l, rfl⟩
    exact ⟨Fin.castSucc l, Fin.castSucc_lt_last l, by simp⟩

/-- **Greedy selection** (proof of Theorem 6.3). If `E ⊆ ℝⁿ` is contained in no `ε`-neighbourhood
`Metric.thickening ε L` of an affine subspace `L` with `dim L ≤ n − 2`, then `E` contains points
`a₀, a 0, …, a (n-2)` in `ε`-general position. (In the paper, `ε = δ r` and `E ⊆ B̄_r(x)`.) -/
theorem exists_isGeneralPosition_of_not_subset_thickening {E : Set (Rn n)} {ε : ℝ}
    (hE : ∀ L : AffineSubspace ℝ (Rn n), finrank ℝ L.direction ≤ n - 2 →
      ¬ E ⊆ thickening ε (L : Set (Rn n))) :
    ∃ a₀ ∈ E, ∃ a : Fin (n - 1) → Rn n, (∀ i, a i ∈ E) ∧ IsGeneralPosition ε a₀ a := by
  suffices key : ∀ m ≤ n - 1,
      ∃ a₀ ∈ E, ∃ a : Fin m → Rn n, (∀ i, a i ∈ E) ∧ IsGeneralPosition ε a₀ a from
    key _ le_rfl
  intro m
  induction m with
  | zero =>
    intro _
    obtain ⟨a₀, ha₀⟩ : E.Nonempty := by
      by_contra hne
      refine hE ⊥ (by rw [AffineSubspace.direction_bot, finrank_bot]; exact Nat.zero_le _) ?_
      rw [not_nonempty_iff_eq_empty] at hne
      simp [hne]
    exact ⟨a₀, ha₀, Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ m ih =>
    intro hm
    obtain ⟨a₀, ha₀, a, haE, hgp⟩ := ih (by omega)
    set L := affineSpan ℝ (insert a₀ (range a)) with hL
    have hLdim : finrank ℝ L.direction ≤ n - 2 := by
      rw [hL, direction_affineSpan, ← Fin.range_cons]
      exact (finrank_vectorSpan_range_le ℝ _ (n := m) (by simp)).trans (by omega)
    obtain ⟨b, hbE, hb⟩ := not_subset.1 (hE L hLdim)
    have hLne : (L : Set (Rn n)).Nonempty := ⟨a₀, subset_affineSpan ℝ _ (mem_insert _ _)⟩
    have hbL : ε ≤ infDist b L :=
      not_lt.1 fun hlt => hb ((mem_thickening_iff_infDist_lt hLne).2 hlt)
    refine ⟨a₀, ha₀, Fin.snoc a b, fun i => ?_, fun i => ?_⟩
    · cases i using Fin.lastCases with
      | last => simpa using hbE
      | cast i => simpa using haE i
    · cases i using Fin.lastCases with
      | last => simpa [image_snoc_Iio_last] using hbL
      | cast i => simpa [image_snoc_Iio_castSucc] using hgp i

/-- **General position and bounded orthonormalisation** (proof of Theorem 6.3, with the
corrected coefficient bound of `exists_coeff_gramSchmidtNormed`).
Let `E ⊆ B̄_r(x)`, `δ, r > 0`, and assume that `E` lies in no `δ r`-neighbourhood of an affine
subspace of dimension `≤ n − 2`. Then there are `a₀, a 0, …, a (n-2) ∈ E` in `δ r`-general
position, the normalised Gram–Schmidt family `e` of the `a j − a₀` is orthonormal, and each
`e i = ∑_j c_j (a j − a₀)` with `c_j = 0` for `j > i` and `|c_j| ≤ (δ r)⁻¹ (1 + 2/δ)^i`. -/
theorem exists_generalPosition_orthonormal {E : Set (Rn n)} {x : Rn n} {δ r : ℝ} (hδ : 0 < δ)
    (hr : 0 < r) (hEx : E ⊆ closedBall x r)
    (hE : ∀ L : AffineSubspace ℝ (Rn n), finrank ℝ L.direction ≤ n - 2 →
      ¬ E ⊆ thickening (δ * r) (L : Set (Rn n))) :
    ∃ a₀ ∈ E, ∃ a : Fin (n - 1) → Rn n, (∀ i, a i ∈ E) ∧ IsGeneralPosition (δ * r) a₀ a ∧
      Orthonormal ℝ (gramSchmidtNormed ℝ fun j => a j - a₀) ∧
      ∀ i, ∃ c : Fin (n - 1) → ℝ, (∀ j, i < j → c j = 0) ∧
        (∀ j, |c j| ≤ (δ * r)⁻¹ * (1 + 2 / δ) ^ (i : ℕ)) ∧
        gramSchmidtNormed ℝ (fun j => a j - a₀) i = ∑ j, c j • (a j - a₀) := by
  obtain ⟨a₀, ha₀, a, haE, hgp⟩ := exists_isGeneralPosition_of_not_subset_thickening hE
  have hδr : 0 < δ * r := mul_pos hδ hr
  refine ⟨a₀, ha₀, a, haE, hgp, orthonormal_gramSchmidtNormed hδr hgp, fun i => ?_⟩
  obtain ⟨c, hc0, hcb, hce⟩ :=
    exists_coeff_gramSchmidtNormed hδr hgp (hEx ha₀) (fun j => hEx (haE j)) i
  refine ⟨c, hc0, fun j => (hcb j).trans (le_of_eq ?_), hce⟩
  rw [genPosCoeffBound, mul_div_mul_right _ _ hr.ne']

end InnerVariational
