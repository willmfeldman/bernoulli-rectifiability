/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Defs.LaplacianMeasure
public import InnerVariational.NaberValtorta.Main
public import InnerVariational.Singular.Chi
public import InnerVariational.NaberValtorta.MainFrequency
public import InnerVariational.Main.MainTheorem
import InnerVariational.Main.Laplacian
public import InnerVariational.Defs.VariationalSolution

/-!
# Headline statements: Theorems 1.2, 7.2, 8.6, 8.7

The main results of D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and
compactness for non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025),
no. 3, DOI 10.1002/cpa.22226; arXiv:2306.10131 (numbering of arXiv v2), stated against the
definitions in `InnerVariational/Defs`: Theorem 7.2 (the set `Σ^H` of highest density),
Theorem 8.6 (identification of `χ`), Theorem 8.7 (the Laplacian measure) and the Main
Theorem 1.2. Each statement is proved elsewhere in the library and only restated here.
Theorem 1.2 (i)–(iii) are derived from Theorems 8.6 and 8.7, exactly as in the paper's proof of
Theorem 1.2 (end of §8).

## Conventions

* `2 ≤ n` throughout. The paper mentions the case `n = 1` only in passing.
* "For `ℋ^{n-1}`-a.e. `x ∈ A`, `P x`" is written `hausdorffN n (n-1) {x | x ∈ A ∧ ¬ P x} = 0`,
  i.e. the exceptional set is `ℋ^{n-1}`-null (as an outer measure). This avoids restricting a
  measure to a possibly non-measurable set.
* `∂{u > 0}` inside `Ω` is `Ω ∩ frontier {x | 0 < u x}`. Since `Ω` is open, this is the relative
  frontier and depends only on `u|_Ω`.
* The introduction states Theorem 1.2 (iii) with a set `Σ_**` and with
  `H_x(u; 0+) = lim r^{-2} ⨍_{∂B_r(x)} u²` (an average). We use the form of Theorem 8.7: the set
  `Σ^H` and the unaveraged `H_x(u; r) = r^{-(n+1)} ∫_{∂B_r(x)} u²` of §3.3, for which `α(n)` is
  normalized.
* Theorem 1.2 (iv), second display: as printed it omits the factor `√(H_x(u; r))` that
  Lemma 8.5 (1) carries; we formalize the version with the factor (see `main_theorem_iv`).
* Theorem 7.2: `B_{1/100}(x)` (with `x` unbound) is read as `B_{1/100}` (centre `0`), and the
  neighbourhood estimate (1) is stated for `t ≤ s ≤ 1`.
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational.Statements

variable {n : ℕ}

/-! ## Theorem 7.2 -/

/-- **Theorem 7.2** (1)–(2). For every `n ≥ 2` and `N₊` there is
`C = C(N₊, n)` such that for every variational solution `(u, χ)` on `B_1` (with any constant
`C_V`) with `N_0(u; 1) ≤ N₊`:

1. if `0 ∈ Σ^H_t` with `t > 0`, then `|B_s(Σ^H_t ∩ B_{1/100})| ≤ C s` for `t ≤ s ≤ 1`;
2. if `0 ∈ Σ^H` (the case `t = 0`; `Σ^H_0` is read as `Σ^H`), then
   `|B_s(Σ^H ∩ B_{1/100})| ≤ C s` for `0 < s ≤ 1`, `ℋ^{n-1}(Σ^H ∩ B_{1/100}) ≤ C`, and
   `Σ^H ∩ B_{1/100}` is countably `ℋ^{n-1}`-rectifiable.

The quantifier order `∀ n N₊, ∃ C, ∀ C_V u χ t` is the paper's: `C` depends only on `N₊` and
`n`. `B_s(A)` is `thickening s A`.

Differences from the printed statement: the ball `B_{1/100}(x)` is centred at `0`; (1) is
stated for `s ≤ 1`; the case `t = 1` is vacuous, since `Σ^H_1` needs `closedBall 0 1 ⊆ B_1`.
The solution is assumed on an open `Ω ⊇ closedBall 0 1` (the paper assumes `B_1`), because
`N_0(u; 1)` involves `u` on `∂B_1`; if boundary values on `∂B_1` are prescribed independently of
`u` on `B_1`, the bound can fail. `Σ^H` is still taken relative to `B_1`. -/
theorem sigmaH_main (hn : 2 ≤ n) (Nplus : ℝ) :
    ∃ C : ℝ, ∀ (Ω : Set (Rn n)) (C_V : ℝ≥0) (u χ : Rn n → ℝ), IsVariationalSolution Ω C_V u χ →
      closedBall 0 1 ⊆ Ω → frequencyN u χ 0 1 ≤ Nplus →
      (∀ t : ℝ, 0 < t → (0 : Rn n) ∈ sigmaHr (ball 0 1) u χ t → ∀ s : ℝ, t ≤ s → s ≤ 1 →
        volume (thickening s (sigmaHr (ball 0 1) u χ t ∩ ball 0 (1 / 100))) ≤
          ENNReal.ofReal (C * s)) ∧
      ((0 : Rn n) ∈ sigmaH (ball 0 1) u χ →
        (∀ s : ℝ, 0 < s → s ≤ 1 →
          volume (thickening s (sigmaH (ball 0 1) u χ ∩ ball 0 (1 / 100))) ≤
            ENNReal.ofReal (C * s)) ∧
        hausdorffN n (n - 1) (sigmaH (ball 0 1) u χ ∩ ball 0 (1 / 100)) ≤ ENNReal.ofReal C ∧
        IsCountablyRectifiable n (n - 1) (sigmaH (ball 0 1) u χ ∩ ball 0 (1 / 100))) := by
  -- Proved in `NaberValtorta/Main.lean`.
  exact NaberValtorta.sigmaH_main hn Nplus

/-- **Theorem 7.2** (3). Under the hypotheses of Theorem 7.2, `N_x(u; 0+) = 1` at
`ℋ^{n-1}`-a.e. `x ∈ Σ^H`.

The conclusion concerns all of `Σ^H` (in `B_1`), while the paper's proof covers
`Σ^H ∩ B_{1/100}`; the global statement follows by applying the local one to the rescalings
`u(x + ρ·)/ρ` at each `x ∈ Σ^H` (where `H_x(ρ) > 0`) and a countable covering. -/
theorem sigmaH_main_frequency (hn : 2 ≤ n) {C_V : ℝ≥0} {u χ : Rn n → ℝ}
    (h : IsVariationalSolution (ball 0 1) C_V u χ) (Nplus : ℝ) (hN : frequencyN u χ 0 1 ≤ Nplus)
    (h0 : (0 : Rn n) ∈ sigmaH (ball 0 1) u χ ∨
      ∃ t : ℝ, 0 < t ∧ (0 : Rn n) ∈ sigmaHr (ball 0 1) u χ t) :
    hausdorffN n (n - 1)
      {x | x ∈ sigmaH (ball 0 1) u χ ∧ ¬ Tendsto (frequencyN u χ x) (𝓝[>] 0) (𝓝 1)} = 0 :=
  NaberValtorta.sigmaH_main_frequency hn h Nplus hN h0

/-! ## Theorem 8.6 -/

/-- **Theorem 8.6**. Let `(u, χ)` be a variational solution on an open connected
`Ω`. Then either `u ≡ 0` on `Ω` or `χ = χ_{u>0}` a.e. on `Ω`. -/
theorem chi_eq_indicator (hn : 2 ≤ n) {Ω : Set (Rn n)} {C_V : ℝ≥0} {u χ : Rn n → ℝ}
    (hΩ : IsConnected Ω) (h : IsVariationalSolution Ω C_V u χ) :
    (∀ x ∈ Ω, u x = 0) ∨ χ =ᵐ[volume.restrict Ω] posIndicator u :=
  Singular.chi_eq_indicator hn hΩ h

/-! ## Theorem 8.7 -/

/-- **Theorem 8.7**. Let `(u, χ)` be a variational solution on `Ω`. Then
`∂{u > 0}` is countably `ℋ^{n-1}`-rectifiable, has locally finite `ℋ^{n-1}`-measure in `Ω`, and
`Δu = ℋ^{n-1}⌊∂*{u>0} + 2α(n)√(H_x(u;0+)) ℋ^{n-1}⌊Σ^H` in `Ω`, distributionally and with a
locally finite right-hand side: `∫ u Δφ = ∫ φ dμ` for every test function `φ` on `Ω`. -/
theorem laplacian_measure_eq [NeZero n] (hn : 2 ≤ n) {Ω : Set (Rn n)} {C_V : ℝ≥0}
    {u χ : Rn n → ℝ} (h : IsVariationalSolution Ω C_V u χ) :
    IsCountablyRectifiable n (n - 1) (Ω ∩ frontier {x | 0 < u x}) ∧
      (∀ K, IsCompact K → K ⊆ Ω → hausdorffN n (n - 1) (K ∩ frontier {x | 0 < u x}) < ∞) ∧
      HasDistribLaplacianOn Ω u (laplacianMeasure Ω u χ) :=
  Main.laplacian_measure_eq hn h

/-! ## Theorem 1.2 -/

/-- **Theorem 1.2 (i)**. On a domain, either `u ≡ 0` or `χ = χ_{u>0}` a.e. -/
theorem main_theorem_i (hn : 2 ≤ n) {Ω : Set (Rn n)} {C_V : ℝ≥0} {u χ : Rn n → ℝ}
    (hΩ : IsConnected Ω) (h : IsVariationalSolution Ω C_V u χ) :
    (∀ x ∈ Ω, u x = 0) ∨ χ =ᵐ[volume.restrict Ω] posIndicator u :=
  chi_eq_indicator hn hΩ h

/-- **Theorem 1.2 (ii)**. The topological free boundary `Ω ∩ ∂{u > 0}` is
countably `ℋ^{n-1}`-rectifiable and has locally finite `ℋ^{n-1}`-measure. -/
theorem main_theorem_ii [NeZero n] (hn : 2 ≤ n) {Ω : Set (Rn n)} {C_V : ℝ≥0} {u χ : Rn n → ℝ}
    (_hΩ : IsConnected Ω) (h : IsVariationalSolution Ω C_V u χ) :
    IsCountablyRectifiable n (n - 1) (Ω ∩ frontier {x | 0 < u x}) ∧
      ∀ K, IsCompact K → K ⊆ Ω → hausdorffN n (n - 1) (K ∩ frontier {x | 0 < u x}) < ∞ :=
  Main.main_theorem_ii hn _hΩ h

/-- **Theorem 1.2 (iii)**, in the form of Theorem 8.7:
`Δu = ℋ^{n-1}⌊∂*{u>0} + 2α(n)√(H_x(u;0+)) ℋ^{n-1}⌊Σ^H` in `Ω`. The paper prints it with a set
`Σ_**` and an averaged `H_x(u; 0+)`; see the module docstring. -/
theorem main_theorem_iii [NeZero n] (hn : 2 ≤ n) {Ω : Set (Rn n)} {C_V : ℝ≥0} {u χ : Rn n → ℝ}
    (_hΩ : IsConnected Ω) (h : IsVariationalSolution Ω C_V u χ) :
    HasDistribLaplacianOn Ω u (laplacianMeasure Ω u χ) :=
  (laplacian_measure_eq hn h).2.2

/-- **Theorem 1.2 (iv)**. At `ℋ^{n-1}`-a.e. `x ∈ Ω ∩ ∂{u>0} \ ∂*{u>0}`:
`r ∫_{B_r(x)} (|∇u|² + χ − 1) / ∫_{∂B_r(x)} u² → 1`, and for some unit vector `ν`,
`r ∫_{B_r(x)} |∇(u − √(H_x(u;r)) α(n) |(y − x)·ν|)|² / ∫_{∂B_r(x)} u² → 0` as `r → 0+`.

The printed second display omits the factor `√(H_x(u; r))` that Lemma 8.5 (1) carries, so it
fails as printed (e.g. `u = 2α(n)|y_n|`, `χ ≡ 1`: every point of `{y_n = 0}` lies in
`∂{u > 0} \ ∂*{u > 0}` and the ratio stays bounded below). We formalize the version with the
factor, which is what Lemma 8.5 (1) gives. -/
theorem main_theorem_iv [NeZero n] (hn : 2 ≤ n) {Ω : Set (Rn n)} {C_V : ℝ≥0} {u χ : Rn n → ℝ}
    (hΩ : IsConnected Ω) (h : IsVariationalSolution Ω C_V u χ) :
    hausdorffN n (n - 1) {x | x ∈ Ω ∧ x ∈ frontier {y | 0 < u y} ∧
      x ∉ reducedBoundary Ω {y | 0 < u y} ∧
      ¬ (Tendsto (fun r => r * (∫ y in ball x r, (‖gradient u y‖ ^ 2 + χ y - 1)) /
            sphereIntegral (fun y => u y ^ 2) x r) (𝓝[>] 0) (𝓝 1) ∧
          ∃ ν : Rn n, ‖ν‖ = 1 ∧
            Tendsto (fun r => r * (∫ y in ball x r,
                ‖gradient u y - (√(heightH u x r) * alphaN n) • gradient (absProfile ν x) y‖ ^ 2) /
              sphereIntegral (fun y => u y ^ 2) x r) (𝓝[>] 0) (𝓝 0))} = 0 :=
  Main.main_theorem_iv hn hΩ h

/-- **Theorem 1.2**, the conjunction of (i)–(iv). Here `(u, χ)` is a variational
solution on a domain (open and connected) `Ω ⊆ ℝⁿ`, `n ≥ 2`. -/
theorem main_theorem [NeZero n] (hn : 2 ≤ n) {Ω : Set (Rn n)} {C_V : ℝ≥0} {u χ : Rn n → ℝ}
    (hΩ : IsConnected Ω) (h : IsVariationalSolution Ω C_V u χ) :
    ((∀ x ∈ Ω, u x = 0) ∨ χ =ᵐ[volume.restrict Ω] posIndicator u) ∧
    (IsCountablyRectifiable n (n - 1) (Ω ∩ frontier {x | 0 < u x}) ∧
      ∀ K, IsCompact K → K ⊆ Ω → hausdorffN n (n - 1) (K ∩ frontier {x | 0 < u x}) < ∞) ∧
    HasDistribLaplacianOn Ω u (laplacianMeasure Ω u χ) ∧
    hausdorffN n (n - 1) {x | x ∈ Ω ∧ x ∈ frontier {y | 0 < u y} ∧
      x ∉ reducedBoundary Ω {y | 0 < u y} ∧
      ¬ (Tendsto (fun r => r * (∫ y in ball x r, (‖gradient u y‖ ^ 2 + χ y - 1)) /
            sphereIntegral (fun y => u y ^ 2) x r) (𝓝[>] 0) (𝓝 1) ∧
          ∃ ν : Rn n, ‖ν‖ = 1 ∧
            Tendsto (fun r => r * (∫ y in ball x r,
                ‖gradient u y - (√(heightH u x r) * alphaN n) • gradient (absProfile ν x) y‖ ^ 2) /
              sphereIntegral (fun y => u y ^ 2) x r) (𝓝[>] 0) (𝓝 0))} = 0 :=
  ⟨main_theorem_i hn hΩ h, main_theorem_ii hn hΩ h, main_theorem_iii hn hΩ h,
    main_theorem_iv hn hΩ h⟩

end InnerVariational.Statements
