/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Defs.Calculus
public import InnerVariational.Sobolev.LocalLipschitz
public import InnerVariational.Blowup.WeakCompactness
public import GMTFoundations.Sobolev.RellichTrace
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import GMTFoundations.Defs.Calculus

/-!
# Registry: Sobolev-type facts in elementary form

Classical Sobolev-type results used by the proof, stated in the elementary form the proofs
need, for Lipschitz functions and `L²` pairings, rather than for Sobolev spaces:

* `rellich_trace_weak_compactness`: Rellich–Kondrachov compactness and compactness of the trace,
  for bounded sequences of Lipschitz functions on `closedBall 0 1` (Evans–Gariepy, §§4.6 and 4.3).
  Imported from the dependency gmt-foundations v0.1.0
  (https://github.com/willmfeldman/gmt-foundations).
* `exists_weakly_convergent_subseq`: weak sequential compactness of bounded sets in `L²`
  (Brezis, Thm 3.18). Proved in `Blowup/WeakCompactness.lean`.
* `integral_mul_divergence_eq_neg`, `integral_mul_fderiv_eq_neg`: integration by parts for
  locally Lipschitz functions, via Rademacher's theorem (Evans–Gariepy, Thm 3.2). Proved in
  `Sobolev/Lipschitz.lean` and `Sobolev/LocalLipschitz.lean`.

## References

* L. C. Evans and R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, rev. ed.,
  CRC Press, 2015.
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Springer,
  2011.
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational.Registry

variable {n : ℕ}

/-- **Rellich–Kondrachov with compact trace** (Evans–Gariepy, §§4.6 and 4.3). Let `f k`
be Lipschitz on the closed unit ball with `∫_{B_1} (f_k² + |∇f_k|²) ≤ C`. Then along a
subsequence:
* `f_k → F` in `L²(B_1)`;
* the traces `f_k|_{∂B_1} → F_tr` in `L²(∂B_1)`;
* `∇f_k ⇀ G` weakly in `L²(B_1; ℝⁿ)`;
* `G` is the weak gradient of `F`: `∫ F div ψ = −∫ ⟪G, ψ⟫` for `ψ ∈ C^∞_c(B_1; ℝⁿ)`.

The limit trace `F_tr` is the trace of `F`; that relation is not stated here. -/
theorem rellich_trace_weak_compactness [NeZero n] (f : ℕ → Rn n → ℝ) (C : ℝ)
    (hLip : ∀ k, ∃ L, LipschitzOnWith L (f k) (closedBall 0 1))
    (hbd : ∀ k, ∫ y in ball (0 : Rn n) 1, (f k y ^ 2 + ‖gradient (f k) y‖ ^ 2) ≤ C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ (F : Rn n → ℝ) (Ftr : sphere (0 : Rn n) 1 → ℝ)
      (G : Rn n → Rn n),
      MemLp F 2 (volume.restrict (ball 0 1)) ∧ MemLp Ftr 2 (sphereMeasure n) ∧
      MemLp G 2 (volume.restrict (ball 0 1)) ∧
      Tendsto (fun k => ∫ y in ball (0 : Rn n) 1, (f (φ k) y - F y) ^ 2) atTop (𝓝 0) ∧
      Tendsto (fun k => ∫ ω, (f (φ k) (ω : Rn n) - Ftr ω) ^ 2 ∂sphereMeasure n) atTop (𝓝 0) ∧
      (∀ h : Rn n → Rn n, MemLp h 2 (volume.restrict (ball 0 1)) →
        Tendsto (fun k => ∫ y in ball (0 : Rn n) 1, ⟪gradient (f (φ k)) y, h y⟫) atTop
          (𝓝 (∫ y in ball (0 : Rn n) 1, ⟪G y, h y⟫))) ∧
      (∀ ψ : Rn n → Rn n, IsSmoothTestField (ball 0 1) ψ →
        ∫ y in ball (0 : Rn n) 1, F y * divergence ψ y =
          -∫ y in ball (0 : Rn n) 1, ⟪G y, ψ y⟫) := by
  -- proved in gmt-foundations v0.1.0
  exact GMTFoundations.rellich_trace_weak_compactness f C hLip hbd

/-- **Weak sequential compactness in `L²`** (Brezis, Thm 3.18). A sequence bounded in
`L²(μ; E)`, with `E` a finite-dimensional real inner product space, has a weakly convergent
subsequence. Proved in `Blowup/WeakCompactness.lean`. -/
theorem exists_weakly_convergent_subseq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (g : ℕ → α → E) (C : ℝ) (hg : ∀ k, MemLp (g k) 2 μ) (hbd : ∀ k, ∫ x, ‖g k x‖ ^ 2 ∂μ ≤ C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ G : α → E, MemLp G 2 μ ∧
      ∀ h : α → E, MemLp h 2 μ →
        Tendsto (fun k => ∫ x, ⟪g (φ k) x, h x⟫ ∂μ) atTop (𝓝 (∫ x, ⟪G x, h x⟫ ∂μ)) := by
  -- proved in `Blowup/WeakCompactness.lean`
  exact InnerVariational.exists_weakly_convergent_subseq g C hg hbd

/-- **Integration by parts, divergence form.** Let `f` be locally Lipschitz on an open set
`Ω` and `ξ ∈ C^{0,1}_c(Ω; ℝⁿ)`. Then `∫ f div ξ = −∫ ⟪∇f, ξ⟫`. The
gradient of `f` exists a.e. by Rademacher's theorem (Evans–Gariepy, Thm 3.2). Proved in
`Sobolev/LocalLipschitz.lean`. -/
theorem integral_mul_divergence_eq_neg {Ω : Set (Rn n)} (hΩ : IsOpen Ω) {f : Rn n → ℝ}
    (hf : LocallyLipschitzOn Ω f) {ξ : Rn n → Rn n} (hξ : IsLipTestField Ω ξ) :
    ∫ x, f x * divergence ξ x = -∫ x, ⟪gradient f x, ξ x⟫ :=
  integral_mul_divergence_eq_neg_of_locallyLipschitzOn hΩ hf hξ

/-- **Integration by parts, scalar form.** Let `f` be locally Lipschitz on an open `Ω`, and
`g` Lipschitz with compact support in `Ω`. Then `∫ f ∂_v g = −∫ g ∂_v f` for every direction
`v`. Proved in `Sobolev/LocalLipschitz.lean`. -/
theorem integral_mul_fderiv_eq_neg {Ω : Set (Rn n)} (hΩ : IsOpen Ω) {f g : Rn n → ℝ}
    (hf : LocallyLipschitzOn Ω f) (hg : ∃ C, LipschitzWith C g) (hgc : HasCompactSupport g)
    (hgΩ : tsupport g ⊆ Ω) (v : Rn n) :
    ∫ x, f x * fderiv ℝ g x v = -∫ x, g x * fderiv ℝ f x v := by
  obtain ⟨C, hC⟩ := hg
  exact hf.integral_mul_fderiv_eq_neg hΩ hC hgc hgΩ v

end InnerVariational.Registry
