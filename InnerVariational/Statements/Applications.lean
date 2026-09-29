/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Defs.LaplacianMeasure
public import InnerVariational.Defs.Solutions
public import InnerVariational.Applications.Classical
public import InnerVariational.Defs.VariationalSolution

/-!
# Headline statements: applications (Theorem 9.3 = Theorem 1.3)

* `classical_compactness`: Theorem 9.3 = Theorem 1.3 of D. Kriventsov and G. S. Weiss,
  *Rectifiability, finite Hausdorff measure, and compactness for non-minimizing Bernoulli free
  boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3, DOI 10.1002/cpa.22226; arXiv:2306.10131
  (numbering of arXiv v2). Theorem 9.3 assumes `sup_k ‖∇u_k‖_{C^{0,1}(B_1)} < ∞`, which would
  require `C^{1,1}` bounds; as in Theorem 1.3, the hypothesis here is
  `sup_k ‖u_k‖_{C^{0,1}(B_1)} < ∞`. The limit is a variational solution on `B_1` with the uniform
  Lipschitz constant as its constant `C_V`.

It uses `Σ^H` in place of the introduction's `Σ_**`, as the body of the paper does (Theorem 9.3).
As in `Statements/Main.lean`, "`ℋ^{n-1}`-a.e. on `A`" is an `ℋ^{n-1}`-null exceptional set.

The proof is in `Applications/Classical.lean`.
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational.Statements

variable {n : ℕ}

/-- **Theorem 9.3 = Theorem 1.3**. Let `u_k` be classical solutions on
`B_1` with `sup_k ‖u_k‖_{C^{0,1}(B_1)} ≤ C`, encoded as `|u_k| ≤ C` and
`u_k` `C`-Lipschitz on `B_1`. Then along a subsequence `u_k → u` locally uniformly in `B_1`, and:
* `u` is `C`-Lipschitz on `B_1`, and `(u, χ_{u>0})` is a variational solution on `B_1` with
  constant `C`;
* `α(n)√(H_x(u; 0+)) ≤ 1` for `ℋ^{n-1}`-a.e. `x ∈ Σ^H(u)`;
* either `u ≡ 0` on `B_1`, or `χ_{u_k>0} → χ_{u>0}` in `L¹_loc(B_1)` and `∂{u_k>0} → ∂{u>0}`
  locally in `B_1` in the Hausdorff sense: for each compact `K ⊆ B_1` and `ε > 0`, eventually
  every point of `K ∩ ∂{u>0}` is within `ε` of `B_1 ∩ ∂{u_k>0}` and vice versa;
* `B_1 ∩ ∂{u>0}` is countably `ℋ^{n-1}`-rectifiable with locally finite `ℋ^{n-1}`-measure,
  and `Δu = ℋ^{n-1}⌊∂*{u>0} + 2α(n)√(H_x(u;0+)) ℋ^{n-1}⌊Σ^H` in `B_1`. -/
theorem classical_compactness [NeZero n] (hn : 2 ≤ n) (u : ℕ → Rn n → ℝ)
    (hu : ∀ k, IsClassicalSolution (ball 0 1) (u k)) (C : ℝ≥0)
    (hsup : ∀ k, ∀ x ∈ ball (0 : Rn n) 1, |u k x| ≤ C)
    (hlip : ∀ k, LipschitzOnWith C (u k) (ball 0 1)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : Rn n → ℝ,
      TendstoLocallyUniformlyOn (fun k => u (φ k)) v atTop (ball 0 1) ∧
      LipschitzOnWith C v (ball 0 1) ∧
      IsVariationalSolution (ball 0 1) C v (posIndicator v) ∧
      hausdorffN n (n - 1) {x | x ∈ sigmaH (ball 0 1) v (posIndicator v) ∧
        ¬ alphaN n * √(heightHZero v x) ≤ 1} = 0 ∧
      ((∀ x ∈ ball (0 : Rn n) 1, v x = 0) ∨
        ((∀ K, IsCompact K → K ⊆ ball 0 1 →
            Tendsto (fun k => ∫ x in K, |posIndicator (u (φ k)) x - posIndicator v x|) atTop
              (𝓝 0)) ∧
          ∀ K, IsCompact K → K ⊆ ball 0 1 → ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
            (∀ x ∈ K ∩ frontier {y | 0 < v y},
              ∃ y ∈ ball 0 1 ∩ frontier {y | 0 < u (φ k) y}, dist x y < ε) ∧
            (∀ x ∈ K ∩ frontier {y | 0 < u (φ k) y},
              ∃ y ∈ ball 0 1 ∩ frontier {y | 0 < v y}, dist x y < ε))) ∧
      IsCountablyRectifiable n (n - 1) (ball 0 1 ∩ frontier {x | 0 < v x}) ∧
      (∀ K, IsCompact K → K ⊆ ball 0 1 →
        hausdorffN n (n - 1) (K ∩ frontier {x | 0 < v x}) < ∞) ∧
      HasDistribLaplacianOn (ball 0 1) v (laplacianMeasure (ball 0 1) v (posIndicator v)) :=
  Applications.classical_compactness hn u hu C hsup hlip

end InnerVariational.Statements
