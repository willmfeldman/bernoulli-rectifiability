/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Sperner.Equality.Weak

/-!
# Rigidity of polarization for harmonic minimizers

Let `v ≥ 0` be Lipschitz, one-homogeneous, harmonic on its preconnected positivity set `U`, and a
minimizer of the Gaussian Rayleigh quotient at the half-space threshold. For a unit vector `a`,
the polarization `w = P_a v` is again a minimizer, hence harmonic on `{w > 0}`
(`Sperner/Equality/Weak.lean`). We show `P_a v ∈ {v, v ∘ σ_a}`, in the form: either
`v (σ_a x) ≤ v x` on the whole open half-space `{⟪x, a⟫ > 0}`, or the reverse inequality holds
there.

The proof is a clopen argument. If `v > v ∘ σ_a` somewhere in `{⟪x, a⟫ > 0}`, the set of points
of `U` near which `w = v` is nonempty, open, and closed in `U`: at a limit point `x ∈ U`, the
strong maximum principle is applied to `w - v ≥ 0` (if `⟪x, a⟫ > 0`), to `v - w ≥ 0` (if
`⟪x, a⟫ < 0` and `v (σ_a x) > 0`; if `v (σ_a x) = 0` then `w < v` near `x`), or, on the hyperplane,
to `w - v` on a half-ball, using that `w - v` is odd under `σ_a`. So `w = v` on `U`. If also
`v < v ∘ σ_a` somewhere in the half-space, then symmetrically `w = v ∘ σ_a` on `σ_a U`, and the
open set `{⟪x, a⟫ > 0, v x < v (σ_a x)}` lies in `{w > 0} \ U`, contradicting
`γ{w > 0} = γ(U)`.
-/

open MeasureTheory Set Filter Topology InnerProductSpace Metric
open scoped NNReal ENNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace Sperner

variable {n : ℕ} {a : EuclideanSpace ℝ (Fin n)}

lemma polarize_comp_reflect (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    polarize a (f ∘ reflect a) = polarize a f := by
  funext x
  by_cases hx : 0 ≤ ⟪x, a⟫
  · simp only [polarize_of_nonneg hx, Function.comp_apply, reflect_reflect, max_comm]
  · push Not at hx
    simp only [polarize_of_neg hx, Function.comp_apply, reflect_reflect, min_comm]

/-- If `f ≤ f ∘ σ_a` on the open half-space `{⟪x, a⟫ > 0}`, then `P_a f = f ∘ σ_a`. -/
lemma polarize_eq_comp_reflect (ha : ‖a‖ = 1) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (h : ∀ x, 0 < ⟪x, a⟫ → f x ≤ f (reflect a x)) (x : EuclideanSpace ℝ (Fin n)) :
    polarize a f x = f (reflect a x) := by
  rcases lt_trichotomy ⟪x, a⟫ 0 with hx | hx | hx
  · have hσ : 0 < ⟪reflect a x, a⟫ := by rw [inner_reflect_left ha]; linarith
    have := h _ hσ
    rw [reflect_reflect] at this
    rw [polarize_of_neg hx, min_eq_right this]
  · rw [polarize_of_nonneg hx.ge, reflect_eq_self_of_inner_eq_zero ha hx, max_self]
  · rw [polarize_of_nonneg hx.le, max_eq_right (h x hx)]

/-- A convex open set on which a harmonic function is nonnegative and vanishes somewhere: the
function vanishes identically there. -/
lemma eq_zero_of_convex {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω) (hc : Convex ℝ Ω)
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ∀ x ∈ Ω, HarmonicAt u x) (hnn : ∀ x ∈ Ω, 0 ≤ u x)
    {x₀ : EuclideanSpace ℝ (Fin n)} (hx₀ : x₀ ∈ Ω) (h0 : u x₀ = 0) : ∀ x ∈ Ω, u x = 0 :=
  eq_zero_of_harmonicAt_of_nonneg hΩ hc.isPreconnected hu hnn hx₀ h0

/-- **One-sided rigidity.** Let `v ≥ 0` be continuous and harmonic on its preconnected
positivity set, and let `w = P_a v` be harmonic on `{w > 0}`. If `v (σ_a x₀) < v x₀` for some
`x₀` with `⟪x₀, a⟫ > 0`, then `P_a v = v` on `{v > 0}`. -/
theorem polarize_eq_of_exists_lt (ha : ‖a‖ = 1) {v : EuclideanSpace ℝ (Fin n) → ℝ}
    (hvc : Continuous v) (hnn : ∀ x, 0 ≤ v x) (hharm : ∀ x, 0 < v x → HarmonicAt v x)
    (hconn : IsPreconnected {x | 0 < v x})
    (hwharm : ∀ x, 0 < polarize a v x → HarmonicAt (polarize a v) x)
    {x₀ : EuclideanSpace ℝ (Fin n)} (hx₀a : 0 < ⟪x₀, a⟫) (hx₀ : v (reflect a x₀) < v x₀) :
    ∀ x, 0 < v x → polarize a v x = v x := by
  set σ := reflect a
  set w := polarize a v with hwdef
  set U := {x | 0 < v x} with hUdef
  have hσc : Continuous σ := (reflect a).continuous
  have hwc : Continuous w := continuous_polarize ha hvc
  have hUo : IsOpen U := isOpen_lt continuous_const hvc
  have hinc : Continuous fun y : EuclideanSpace ℝ (Fin n) => ⟪y, a⟫ :=
    continuous_id.inner continuous_const
  set S := {x | x ∈ U ∧ w =ᶠ[𝓝 x] v} with hSdef
  have hSo : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    rintro x ⟨hxU, hxw⟩
    filter_upwards [hUo.mem_nhds hxU, hxw.eventually_nhds] with y hy1 hy2 using ⟨hy1, hy2⟩
  set T := U ∩ (closure S)ᶜ
  have hTo : IsOpen T := hUo.inter isClosed_closure.isOpen_compl
  have hdisj : Disjoint S T :=
    Set.disjoint_left.2 fun x hxS hxT => hxT.2 (subset_closure hxS)
  -- `x₀ ∈ S`
  have hx₀S : x₀ ∈ S := by
    have hx₀U : x₀ ∈ U := lt_of_le_of_lt (hnn _) hx₀
    refine ⟨hx₀U, ?_⟩
    have h1 : ∀ᶠ y in 𝓝 x₀, 0 < ⟪y, a⟫ := hinc.continuousAt.eventually (lt_mem_nhds hx₀a)
    have h2 : ∀ᶠ y in 𝓝 x₀, v (σ y) < v y :=
      (isOpen_lt (hvc.comp hσc) hvc).mem_nhds hx₀
    filter_upwards [h1, h2] with y hy1 hy2
    rw [hwdef, polarize_of_nonneg hy1.le, max_eq_left hy2.le]
  -- harmonic differences
  have hwh : ∀ y, 0 < w y → 0 < v y → HarmonicAt (w - v) y := fun y h1 h2 =>
    (hwharm y h1).sub (hharm y h2)
  -- points of `S` near a limit point
  have hnear : ∀ x ∈ closure S, ∀ t ∈ 𝓝 x, ∃ y ∈ t, y ∈ S := fun x hx t ht => by
    obtain ⟨y, hy1, hy2⟩ := mem_closure_iff_nhds.1 hx t ht
    exact ⟨y, hy1, hy2⟩
  -- the main claim: `S` is closed in `U`
  have hclosed : ∀ x ∈ U, x ∈ closure S → x ∈ S := by
    intro x hxU hxS
    refine ⟨hxU, ?_⟩
    rcases lt_trichotomy ⟪x, a⟫ 0 with hxa | hxa | hxa
    · -- lower half-space
      by_cases hσx : v (σ x) = 0
      · exfalso
        have hwx : w x < v x := by
          rw [hwdef, polarize_of_neg hxa, hσx]; exact min_lt_of_right_lt hxU
        obtain ⟨y, hy, hyS⟩ := hnear x hxS _ ((isOpen_lt hwc hvc).mem_nhds hwx)
        exact (ne_of_lt hy) hyS.2.eq_of_nhds
      · have hσx' : 0 < v (σ x) := lt_of_le_of_ne (hnn _) (Ne.symm hσx)
        set O := U ∩ {y | 0 < v (σ y)} ∩ {y | ⟪y, a⟫ < 0}
        have hOo : IsOpen O := (hUo.inter (isOpen_lt continuous_const (hvc.comp hσc))).inter
          (isOpen_lt hinc continuous_const)
        obtain ⟨ρ, hρ, hB⟩ := Metric.isOpen_iff.1 hOo x ⟨⟨hxU, hσx'⟩, hxa⟩
        have hwB : ∀ y ∈ ball x ρ, w y = min (v y) (v (σ y)) := fun y hy =>
          polarize_of_neg (hB hy).2
        obtain ⟨y₀, hy₀B, hy₀S⟩ := hnear x hxS _ (ball_mem_nhds x hρ)
        have hzero := eq_zero_of_convex (u := v - w) isOpen_ball (convex_ball x ρ)
          (fun y hy => by
            have hy' := hB hy
            have hwpos : 0 < w y := by rw [hwB y hy]; exact lt_min hy'.1.1 hy'.1.2
            exact (hharm y hy'.1.1).sub (hwharm y hwpos))
          (fun y hy => by
            simp only [Pi.sub_apply, sub_nonneg, hwB y hy]; exact min_le_left _ _)
          hy₀B (by simp [hy₀S.2.eq_of_nhds])
        filter_upwards [ball_mem_nhds x hρ] with y hy
        have := hzero y hy
        simp only [Pi.sub_apply, sub_eq_zero] at this
        exact this.symm
    · -- on the hyperplane
      have hσx : σ x = x := reflect_eq_self_of_inner_eq_zero ha hxa
      set O := U ∩ {y | 0 < v (σ y)}
      have hOo : IsOpen O := hUo.inter (isOpen_lt continuous_const (hvc.comp hσc))
      obtain ⟨ρ, hρ, hB⟩ := Metric.isOpen_iff.1 hOo x ⟨hxU, show 0 < v (σ x) by rw [hσx]; exact hxU⟩
      set B := ball x ρ
      have hσB : ∀ y ∈ B, σ y ∈ B := fun y hy => by
        rw [mem_ball, ← hσx, (reflect a).dist_map]; exact hy
      have hwpos : ∀ y ∈ B, 0 < w y := fun y hy => by
        rcases polarize_pair ha (f := v) y with ⟨h1, -⟩ | ⟨h1, -⟩
        · rw [hwdef, h1]; exact (hB hy).1
        · rw [hwdef, h1]; exact (hB hy).2
      have hodd : ∀ y, (w - v) (σ y) = -(w - v) y := fun y => by
        have := comp_polarize_add ha (f := v) id y
        simp only [id] at this
        simp only [Pi.sub_apply]
        linarith
      set Bp := B ∩ {y | 0 < ⟪y, a⟫}
      have hBpo : IsOpen Bp := isOpen_ball.inter (isOpen_lt continuous_const hinc)
      have hHc : Convex ℝ {y : EuclideanSpace ℝ (Fin n) | 0 < ⟪y, a⟫} := by
        have := convex_halfSpace_gt ((innerSL ℝ a : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ).isLinear)
          (0 : ℝ)
        simpa [real_inner_comm] using this
      have hBpc : Convex ℝ Bp := (convex_ball x ρ).inter hHc
      -- a zero of `w - v` in the upper half-ball
      have hz : ∃ z ∈ Bp, (w - v) z = 0 := by
        obtain ⟨y₀, hy₀B, hy₀S⟩ := hnear x hxS _ (ball_mem_nhds x hρ)
        obtain ⟨ε, hε, hεS⟩ := Metric.isOpen_iff.1 (hSo.inter isOpen_ball) y₀ ⟨hy₀S, hy₀B⟩
        rcases lt_or_ge ⟪y₀, a⟫ 0 with hy₀a | hy₀a
        · refine ⟨σ y₀, ⟨hσB y₀ hy₀B, ?_⟩, ?_⟩
          · change 0 < ⟪reflect a y₀, a⟫
            rw [inner_reflect_left ha]; linarith
          · rw [hodd, Pi.sub_apply, hy₀S.2.eq_of_nhds, sub_self, neg_zero]
        · set y₁ := y₀ + (ε / 2) • a
          have hy₁ : y₁ ∈ ball y₀ ε := by
            rw [mem_ball, dist_eq_norm, show y₁ - y₀ = (ε / 2) • a by simp [y₁], norm_smul, ha,
              Real.norm_of_nonneg (by positivity)]
            linarith
          have hy₁' := hεS hy₁
          refine ⟨y₁, ⟨hy₁'.2, ?_⟩, ?_⟩
          · change 0 < ⟪y₁, a⟫
            simp only [y₁, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, ha]
            nlinarith
          · rw [Pi.sub_apply, hy₁'.1.2.eq_of_nhds, sub_self]
      obtain ⟨z, hzB, hz0⟩ := hz
      have hzero := eq_zero_of_convex (u := w - v) hBpo hBpc
        (fun y hy => hwh y (hwpos y hy.1) (hB hy.1).1)
        (fun y hy => by
          simp only [Pi.sub_apply, sub_nonneg, hwdef, polarize_of_nonneg hy.2.le]
          exact le_max_left _ _) hzB hz0
      filter_upwards [ball_mem_nhds x hρ] with y hy
      rcases lt_trichotomy ⟪y, a⟫ 0 with hya | hya | hya
      · have hσy : σ y ∈ Bp := ⟨hσB y hy, by
          change 0 < ⟪reflect a y, a⟫; rw [inner_reflect_left ha]; linarith⟩
        have h1 := hzero _ hσy
        rw [hodd, neg_eq_zero, Pi.sub_apply, sub_eq_zero] at h1
        exact h1
      · rw [hwdef, polarize_of_nonneg hya.ge, reflect_eq_self_of_inner_eq_zero ha hya, max_self]
      · have h1 := hzero y ⟨hy, hya⟩
        rw [Pi.sub_apply, sub_eq_zero] at h1
        exact h1
    · -- upper half-space
      set O := U ∩ {y | 0 < ⟪y, a⟫}
      have hOo : IsOpen O := hUo.inter (isOpen_lt continuous_const hinc)
      obtain ⟨ρ, hρ, hB⟩ := Metric.isOpen_iff.1 hOo x ⟨hxU, hxa⟩
      have hwB : ∀ y ∈ ball x ρ, w y = max (v y) (v (σ y)) := fun y hy =>
        polarize_of_nonneg (hB hy).2.le
      obtain ⟨y₀, hy₀B, hy₀S⟩ := hnear x hxS _ (ball_mem_nhds x hρ)
      have hzero := eq_zero_of_convex (u := w - v) isOpen_ball (convex_ball x ρ)
        (fun y hy => by
          have hy' := hB hy
          have hwpos : 0 < w y := by rw [hwB y hy]; exact lt_max_of_lt_left hy'.1
          exact hwh y hwpos hy'.1)
        (fun y hy => by
          simp only [Pi.sub_apply, sub_nonneg, hwB y hy]; exact le_max_left _ _)
        hy₀B (by simp [hy₀S.2.eq_of_nhds])
      filter_upwards [ball_mem_nhds x hρ] with y hy
      have := hzero y hy
      simp only [Pi.sub_apply, sub_eq_zero] at this
      exact this
  have hcover : U ⊆ S ∪ T := fun x hx => by
    by_cases h : x ∈ closure S
    · exact Or.inl (hclosed x hx h)
    · exact Or.inr ⟨hx, h⟩
  have hsub := hconn.subset_left_of_subset_union hSo hTo hdisj hcover ⟨x₀, hx₀S.1, hx₀S⟩
  exact fun x hx => (hsub hx).2.eq_of_nhds

/-- **Rigidity of polarization.** For a harmonic minimizer `v` with preconnected positivity set,
either `v ∘ σ_a ≤ v` or `v ≤ v ∘ σ_a` on the whole open half-space `{⟪x, a⟫ > 0}`. -/
theorem polarize_dichotomy (hn : 2 ≤ n) (ha : ‖a‖ = 1) {v : EuclideanSpace ℝ (Fin n) → ℝ}
    {L : ℝ≥0} (hv : LipschitzWith L v) (hnn : ∀ x, 0 ≤ v x) (hhom : IsOneHomogeneous v)
    (hmin : dirichletEnergy v ≤ gaussL2 v)
    (hhalf : 2 * gaussMeasure n {x | 0 < v x} ≤ gaussMeasure n univ)
    (hharm : ∀ x, 0 < v x → HarmonicAt v x) (hconn : IsPreconnected {x | 0 < v x}) :
    (∀ x, 0 < ⟪x, a⟫ → v (reflect a x) ≤ v x) ∨ (∀ x, 0 < ⟪x, a⟫ → v x ≤ v (reflect a x)) := by
  set σ := reflect a
  set w := polarize a v with hwdef
  have hσc : Continuous σ := (reflect a).continuous
  -- `w` is a minimizer, hence harmonic on `{w > 0}`
  have hwharm : ∀ x, 0 < w x → HarmonicAt w x := fun x hx =>
    harmonicAt_of_minimizer hn (lipschitzWith_polarize ha hv) (polarize_nonneg hnn)
      (isOneHomogeneous_polarize hhom)
      (by rw [dirichletEnergy_polarize ha hv, gaussL2_polarize ha hv.continuous]; exact hmin)
      (by rw [gaussMeasure_polarize_pos ha hv.continuous]; exact hhalf) hx
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨x₀, hx₀a, hx₀⟩, ⟨x₁, hx₁a, hx₁⟩⟩ := hcon
  -- `w = v` on `U`
  have h1 := polarize_eq_of_exists_lt ha hv.continuous hnn hharm hconn hwharm hx₁a hx₁
  -- `w = v ∘ σ` on `σ U`
  have hv'c : Continuous (v ∘ σ) := hv.continuous.comp hσc
  have hv'harm : ∀ x, 0 < (v ∘ σ) x → HarmonicAt (v ∘ σ) x := fun x hx =>
    harmonicAt_comp_linearIsometryEquiv (reflect a) (hharm _ hx)
  have hv'conn : IsPreconnected {x | 0 < (v ∘ σ) x} := by
    have : {x | 0 < (v ∘ σ) x} = σ '' {x | 0 < v x} := by
      ext x
      simp only [mem_ofPred_eq, Function.comp_apply, mem_image]
      constructor
      · intro hx; exact ⟨σ x, hx, reflect_reflect x⟩
      · rintro ⟨y, hy, rfl⟩; simpa [σ] using hy
    rw [this]
    exact hconn.image _ hσc.continuousOn
  have h2 := polarize_eq_of_exists_lt ha hv'c (fun x => hnn _) hv'harm hv'conn
    (by rw [polarize_comp_reflect]; exact hwharm) hx₀a
    (by simp only [Function.comp_apply, σ, reflect_reflect]; exact hx₀)
  rw [polarize_comp_reflect] at h2
  -- the open set `O = {⟪x, a⟫ > 0, v x < v (σ x)}` lies in `{w > 0} \ U`
  set O := {x | 0 < ⟪x, a⟫} ∩ {x | v x < v (σ x)}
  have hOo : IsOpen O := (isOpen_lt continuous_const (continuous_id.inner continuous_const)).inter
    (isOpen_lt hv.continuous (hv.continuous.comp hσc))
  have hOne : O.Nonempty := ⟨x₀, hx₀a, hx₀⟩
  have hOU : Disjoint {x | 0 < v x} O := Set.disjoint_left.2 fun x hxU hxO => by
    have e1 := h1 x hxU
    have e2 := h2 x (lt_of_le_of_lt (hnn x) hxO.2)
    simp only [Function.comp_apply] at e2
    have hlt : v x < v (σ x) := hxO.2
    rw [← e1, e2] at hlt
    exact lt_irrefl _ hlt
  have hsub : {x | 0 < v x} ∪ O ⊆ {x | 0 < w x} := by
    rintro x (hx | hx)
    · change 0 < polarize a v x; rw [h1 x hx]; exact hx
    · change 0 < polarize a v x
      have hpos : 0 < (v ∘ σ) x := lt_of_le_of_lt (hnn x) hx.2
      rw [h2 x hpos]; exact hpos
  have hmeas := measure_mono (μ := gaussMeasure n) hsub
  rw [measure_union hOU hOo.measurableSet, hwdef, gaussMeasure_polarize_pos ha hv.continuous]
    at hmeas
  have hOpos := gaussMeasure_pos_of_isOpen hOo hOne
  have hfin : gaussMeasure n {x | 0 < v x} ≠ ⊤ := measure_ne_top _ _
  exact absurd hmeas (not_le.2 (ENNReal.lt_add_right hfin hOpos.ne'))

end Sperner
