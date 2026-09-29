/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Applications.Compactness
public import InnerVariational.Applications.AlphaBound
public import InnerVariational.Registry.FreeBoundary
public import InnerVariational.Statements.Main
import Mathlib.Algebra.Order.Ring.Star
public import InnerVariational.Defs.LaplacianMeasure
import InnerVariational.Applications.FreeBoundaryLimit
import InnerVariational.Monotonicity.Blowup
public import InnerVariational.Defs.VariationalSolution
public import InnerVariational.Defs.Solutions

/-!
# Theorem 9.3 = Theorem 1.3: compactness of classical solutions

Theorem 9.3 of Kriventsov–Weiss (full reference below), which proves Theorem 1.3 of the paper.
`Applications.classical_compactness` has exactly the type of `Statements.classical_compactness`.

Two points of the statement differ from the printed one. The hypothesis of Theorem 9.3 reads
`sup_k ‖∇u_k‖_{C^{0,1}(B_1)} < ∞`, which would ask for `C^{1,1}` bounds; as in Theorem 1.3 we
assume `sup_k ‖u_k‖_{C^{0,1}(B_1)} < ∞`, encoded as `|u_k| ≤ C` and `u_k` `C`-Lipschitz on `B_1`.
The set on which `α(n) √(H_x(u; 0+)) ≤ 1` holds and which carries the singular part of `Δu` is
`Σ^H`, as in Theorem 9.3 (Theorem 1.3 writes `Σ_{**}`), and `H_x(u; 0+)` is the unaveraged
`lim_r r^{-(n+1)} ∫_{∂B_r(x)} u²` of the body of the paper, the one that the constant `α(n)` is
normalized for.

## Proof

1. *Extraction.* The `u_k` are `C`-Lipschitz on `B_1` and bounded at `0`; their Lipschitz
   extensions to `ℝⁿ` have a locally uniformly convergent subsequence (Arzelà–Ascoli).
2. *Limit.* `(u_k, χ_{u_k>0})` is a variational solution on `B_1` with constant `C`
   (`Registry.IsClassicalSolution.isVariationalSolution`), so
   `Applications/Compactness.lean` gives `χ_{u_k>0} → χ` in `L¹_loc` along a further subsequence,
   with `(v, χ)` a variational solution.
3. *Theorem 8.6* (`chi_eq_indicator`): `v ≡ 0` or `χ = χ_{v>0}` a.e. In both cases `(v, χ_{v>0})`
   is a variational solution, and in the second `χ_{u_k>0} → χ_{v>0}` in `L¹_loc`.
4. *Theorem 8.7* (`laplacian_measure_eq`) for `(v, χ_{v>0})` gives rectifiability, local finiteness
   and the Laplacian.
5. `α(n) √(H_x(v; 0+)) ≤ 1` a.e. on `Σ^H` (`hausdorffN_sigmaH_not_alpha_le_one`,
   `Applications/AlphaBound.lean`: Proposition 9.1 and Lemma 8.5 (1)) and the Hausdorff
   convergence of the free boundaries (`eventually_hausdorff_frontier`,
   `Applications/FreeBoundaryLimit.lean`: the Harnack inequality and Lemma 9.2).

## References

* D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
  DOI 10.1002/cpa.22226; arXiv:2306.10131. Result numbers refer to arXiv v2.
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace InnerVariational

variable {n : ℕ}

namespace Applications

/-- **Arzelà–Ascoli on `B_1`.** A sequence of functions that are `C`-Lipschitz on `B_1` and bounded
at `0` has a subsequence converging locally uniformly on `B_1` to a `C`-Lipschitz function. -/
theorem exists_subseq_tendstoLocallyUniformlyOn_ball {u : ℕ → Rn n → ℝ} {C : ℝ≥0}
    (hlip : ∀ k, LipschitzOnWith C (u k) (ball 0 1)) {M : ℝ} (hM : ∀ k, |u k 0| ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : Rn n → ℝ, LipschitzWith C v ∧
      TendstoLocallyUniformlyOn (fun k => u (φ k)) v atTop (ball 0 1) := by
  choose g hg hug using fun k => (hlip k).extend_real
  have hg0 : ∀ k, |g k 0| ≤ M := fun k => by
    rw [← hug k (mem_ball_self one_pos)]; exact hM k
  obtain ⟨φ, hφ, v, hlim⟩ := exists_subseq_tendstoLocallyUniformly_of_lipschitzWith hg hg0
  have hlim' := tendstoLocallyUniformlyOn_univ.2 hlim
  refine ⟨φ, hφ, v, LipschitzWith.of_dist_le_mul fun y z => le_of_tendsto'
    ((hlim'.tendsto_at (mem_univ y)).dist (hlim'.tendsto_at (mem_univ z)))
    fun k => (hg (φ k)).dist_le_mul y z, ?_⟩
  exact (hlim'.mono (subset_univ _)).congr fun k y hy => (hug (φ k) hy).symm

/-- **Theorem 9.3** = **Theorem 1.3** of Kriventsov–Weiss, compactness of classical solutions,
with the hypothesis `sup_k ‖u_k‖_{C^{0,1}(B_1)} ≤ C` of Theorem 1.3 (Theorem 9.3 prints
`‖∇u_k‖_{C^{0,1}}`). The limit `v` is a variational solution on `B_1` with the same constant `C`.
Exactly the type of `Statements.classical_compactness`. -/
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
      HasDistribLaplacianOn (ball 0 1) v (laplacianMeasure (ball 0 1) v (posIndicator v)) := by
  -- 1. extraction
  obtain ⟨φ₁, hφ₁, v, hvL, hconv₁⟩ :=
    exists_subseq_tendstoLocallyUniformlyOn_ball hlip fun k => hsup k 0 (mem_ball_self one_pos)
  -- 2. the limit of `(u_k, χ_{u_k>0})`
  have hvar : ∀ k, IsVariationalSolution (ball 0 1) C (u (φ₁ k)) (posIndicator (u (φ₁ k))) :=
    fun k => Registry.IsClassicalSolution.isVariationalSolution (hu _) (hlip _)
  obtain ⟨-, φ₂, hφ₂, χ₀, hχ₀, hχL, -⟩ := IsVariationalSolution.exists_subseq_limit hvar hconv₁
  set φ : ℕ → ℕ := fun k => φ₁ (φ₂ k) with hφdef
  have hφ : StrictMono φ := hφ₁.comp hφ₂
  have hconv : TendstoLocallyUniformlyOn (fun k => u (φ k)) v atTop (ball 0 1) :=
    tendstoLocallyUniformlyOn_comp_strictMono hconv₁ hφ₂
  -- 3. Theorem 8.6
  have hconn : IsConnected (ball (0 : Rn n) 1) :=
    (convex_ball (0 : Rn n) 1).isConnected (nonempty_ball.2 one_pos)
  have hdich := Statements.chi_eq_indicator hn hconn hχ₀
  have hv : IsVariationalSolution (ball 0 1) C v (posIndicator v) := by
    rcases hdich with h0 | hae
    · exact hχ₀.posIndicator_of_eq_zero h0
    · exact hχ₀.posIndicator_of_ae_eq hae
  -- 4. Theorem 8.7
  obtain ⟨hrect, hfin, hlap⟩ := Statements.laplacian_measure_eq hn hv
  refine ⟨φ, hφ, v, hconv, hvL.lipschitzOnWith, hv,
    hausdorffN_sigmaH_not_alpha_le_one hn (fun k => hu (φ k)) (fun k => hlip (φ k)) hconv hv,
    ?_, hrect, hfin, hlap⟩
  -- 5. the dichotomy
  by_cases hv0 : ∀ x ∈ ball (0 : Rn n) 1, v x = 0
  · exact Or.inl hv0
  right
  have hae : χ₀ =ᵐ[volume.restrict (ball 0 1)] posIndicator v := hdich.resolve_left hv0
  have hL1 : ∀ K, IsCompact K → K ⊆ ball 0 1 →
      Tendsto (fun k => ∫ x in K, |posIndicator (u (φ k)) x - posIndicator v x|) atTop
        (𝓝 0) := by
    intro K hK hKB
    refine (hχL K hK hKB).congr fun k => setIntegral_congr_ae hK.measurableSet ?_
    filter_upwards [(ae_restrict_iff' measurableSet_ball).1 hae] with y hy hyK
    rw [hy (hKB hyK)]
  exact ⟨hL1, eventually_hausdorff_frontier hn (fun k => hu (φ k)) (fun k => hlip (φ k)) hconv
    hL1⟩

end Applications

end InnerVariational
