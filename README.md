# Rectifiability of non-minimizing Bernoulli free boundaries, in Lean

A Lean 4 / Mathlib formalization of the main results of D. Kriventsov and G. S. Weiss,
*Rectifiability, finite Hausdorff measure, and compactness for non-minimizing Bernoulli free
boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3, DOI
[10.1002/cpa.22226](https://doi.org/10.1002/cpa.22226), [arXiv:2306.10131](https://arxiv.org/abs/2306.10131).
Theorem numbers below are those of arXiv version 2.

For variational solutions `(u, χ)` of the Bernoulli free boundary problem (critical points of the
Alt–Caffarelli energy with respect to domain variations, not necessarily minimizers), the paper
proves that the free boundary `∂{u > 0}` is countably `ℋ^{n-1}`-rectifiable with locally finite
`ℋ^{n-1}`-measure, identifies `χ` and the measure `Δu` explicitly, and deduces that limits of
classical solutions are variational solutions with the same structure. This repository formalizes
those results in all dimensions `n ≥ 2`. It also proves part of the theory for the functional
`∫ (|∇u|² + Q² χ)` with a Lipschitz coefficient `Q` (see [Lipschitz coefficient](#lipschitz-coefficient)).

The project has over 50,000 lines of Lean in two libraries: `InnerVariational` (the paper) and
`Sperner` (a standalone, Mathlib-only proof of Sperner's inequality for homogeneous harmonic
functions, used in Section 8). It is sorry-free, and each headline theorem below depends only on
the axioms `propext`, `Classical.choice` and `Quot.sound` (`#print axioms`, checked in CI).

## Headline theorems

All in namespace `InnerVariational.Statements`, file `InnerVariational/Statements/Main.lean` or
`InnerVariational/Statements/Applications.lean`, except the last.

| Result | Lean name | Paper |
|---|---|---|
| Structure of the free boundary (i)–(iv) | `main_theorem` | Theorem 1.2 |
| Minkowski and Hausdorff bounds and rectifiability of the top stratum `Σ^H` | `sigmaH_main` | Theorem 7.2 (1)–(2) |
| Frequency one at `ℋ^{n-1}`-a.e. point of `Σ^H` | `sigmaH_main_frequency` | Theorem 7.2 (3) |
| Identification of `χ`: `u ≡ 0` or `χ = χ_{u>0}` a.e. | `chi_eq_indicator` | Theorem 8.6 |
| Identification of the Laplacian: `Δu = ℋ^{n-1}⌊∂*{u>0} + 2α(n)√(H_x(u;0+)) ℋ^{n-1}⌊Σ^H` | `laplacian_measure_eq` | Theorem 8.7 |
| Compactness of classical solutions | `classical_compactness` | Theorem 9.3 = Theorem 1.3 |
| Sperner's inequality with the equality case | `Sperner.sperner_half_volume` | E. Sperner, Jr., Math. Z. 134 (1973), 317–327; used in Lemmas 8.1, 8.3 |

The Lipschitz-coefficient results are listed in the next section.

`formalization.yaml` states each theorem in words. For example, Theorem 8.6, quoted from
`InnerVariational/Statements/Main.lean`:

```lean
theorem chi_eq_indicator (hn : 2 ≤ n) {Ω : Set (Rn n)} {C_V : ℝ≥0} {u χ : Rn n → ℝ}
    (hΩ : IsConnected Ω) (h : IsVariationalSolution Ω C_V u χ) :
    (∀ x ∈ Ω, u x = 0) ∨ χ =ᵐ[volume.restrict Ω] posIndicator u
```

Here `Rn n` is `EuclideanSpace ℝ (Fin n)`, and `IsVariationalSolution Ω C_V u χ` is the paper's
definition (Section 3.2): `u ≥ 0` is continuous on the open set `Ω`, `C²` on `{u > 0}`, with
`|∇u| ≤ C_V`; `χ` is Borel with values in `{0, 1}` and `χ_{u>0} ≤ χ` a.e.; and the first domain
variation of `∫ (|∇u|² + χ)` vanishes for every Lipschitz compactly supported vector field. The
definitions are in `InnerVariational/Defs/`.

## Lipschitz coefficient

The paper studies the functional `∫ (|∇u|² + χ)`. The library also treats
`∫ (|∇u|² + Q² χ)` for a coefficient `Q` that is Lipschitz with `0 < c ≤ Q ≤ C'` on `Ω`, in
dimension `n ≥ 2`. The definitions are in `InnerVariational/Defs/VariationalSolutionQ.lean`:
`IsVariationalSolutionQ Ω C_V Q u χ` (the domain-variation identity of this functional, which
has the extra term `∇(Q²) · ξ χ`), the bounds `QBounds Ω Q L c C'`, the Weiss energy with a frozen
coefficient, the set `sigmaHQ` of highest density, and viscosity solutions of `|∇u| = Q`
(`IsViscositySolutionQ`). For `Q ≡ 1` each reduces to the corresponding notion for the paper's
functional.

The following results are proved for such `Q`, in `InnerVariational/Statements/LipschitzQ.lean`
(namespace `InnerVariational.IsVariationalSolutionQ`, except the last):

| Result | Lean name | Constant-coefficient form |
|---|---|---|
| Density characterization of `Σ^H`: `x ∈ Σ^H` if and only if `x` is a free boundary point where `{χ = 1}` has density one | `mem_sigmaHQ_iff_frontier_inter` | Section 6, Proposition 3.5 |
| `Σ^H` is relatively closed in `Ω` | `closure_sigmaHQ_inter_subset` | Section 6 |
| `u` is a viscosity solution of `\|∇u\| = Q` on `Ω \ Σ^H` | `isViscositySolutionQ_diff_sigmaHQ` | Lemma 8.3 |
| Blow-up limits exist and are variational solutions on `ℝⁿ` for the constant coefficient `Q(x₀)` | `exists_blowup_limit` | proof of Theorem 9.3 |
| Blow-up limits are homogeneous of degree one | `blowup_homogeneous` | Proposition 3.4 |
| Identification of `χ`: `u ≡ 0` and `χ = 1` a.e., or `χ = χ_{u>0}` a.e. | `Singular.chi_eq_indicator_of_localQ` | Theorem 8.6 |

The following results still assume `Q ≡ 1`: the rectifiability and the local finiteness of the
`ℋ^{n-1}`-measure of the free boundary (Theorems 1.2 (ii) and 8.7), the identification of the
Laplacian measure (Theorems 1.2 (iii)–(iv) and 8.7), and the compactness of classical solutions
(Theorem 9.3 = Theorem 1.3). For a Lipschitz coefficient, the library also proves the
corresponding form of Theorem 7.2 for `Σ^H` (local finiteness of `ℋ^{n-1}`, countable
rectifiability, and frequency one `ℋ^{n-1}`-a.e.: `NaberValtorta.sigmaHQ_main`,
`NaberValtorta.sigmaHQ_inter_ball_structure`,
`NaberValtorta.hausdorffN_not_tendsto_weightedFrequencyN_eq_zero`) as supporting results; these
are not among the certified headline theorems.

## Status

All headline theorems are proved, with no `sorry`, `admit`, `axiom` declarations or
`native_decide` anywhere in the libraries. Theorem 1.4 / 10.1 of the paper (limits of a singular
perturbation problem) is **not** included in this release.

Where a formal statement or proof step is set up differently from the paper, the docstring of
the declaration concerned says how and why.

## Proof route

The formalization follows the paper section by section:

- **Monotonicity (Section 3).** The Weiss energy `M_x(u; r)` is monotone for variational
  solutions; blow-ups are homogeneous and densities exist.
- **Frequency (Section 4).** Almost-monotonicity of the frequency `N_x(u; r)` and its behaviour
  under change of centre.
- **Frequency blow-ups (Section 5).** At points of highest density, renormalized blow-ups with
  pinched frequency converge to the one-dimensional profile `α(n)|x_n|`.
- **Core estimates (Section 6).** An `L²`-subspace approximation bounding Jones' β-numbers by
  frequency drops, and a frequency-drop dichotomy.
- **Naber–Valtorta (Section 7).** The covering argument and the discrete and rectifiable
  Reifenberg theorems (from gmt-foundations) give Theorem 7.2.
- **Identification of `Δu` (Section 8).** Regular points (density, viscosity and perimeter
  estimates, using Sperner's inequality), singular points, the identification of `χ`, and the
  formula for `Δu`.
- **Classical solutions (Section 9).** Compactness via BV bounds and the passage to the limit in
  the domain-variation identity.

## Build

The project uses Lean `v4.34.1` and Mathlib `v4.34.1`, as pinned in `lean-toolchain`,
`lakefile.toml` and `lake-manifest.json`. It depends on

- [gmt-foundations](https://github.com/willmfeldman/gmt-foundations) `v0.2.0` (sets of finite
  perimeter, the Reifenberg theorems, Rellich compactness with traces, Hausdorff measure on
  spheres), and
- [elliptic-bernoulli-foundations](https://github.com/willmfeldman/elliptic-bernoulli-foundations)
  `v0.2.0` (Lipschitz regularity of classical solutions and their domain-variation identity),

together with their own pinned dependencies. All libraries use the Lean module system.

```bash
lake exe cache get
lake build
```

`lake build` builds both libraries (`InnerVariational` and `Sperner`); the root modules import
every module. `lake build Sperner` builds the Sperner library alone.

The workflow `.github/workflows/ci.yml` runs on every push and pull request. It builds both
libraries, treating warnings as errors; scans the sources (comments and strings masked) for
`sorry`, `admit`, `axiom` and `native_decide`; checks that no source file reaches 1000 lines and
that every file is a Lean module; validates `formalization.yaml`, resolves its Lean names and
checks that each headline theorem depends on exactly `propext`, `Classical.choice`, `Quot.sound`;
and elaborates every challenge workspace.

## Formalization metadata and comparator challenges

`formalization.yaml` records the headline theorems (Lean names, files, sources and plain-language
statements), the pinned toolchain, the expected axioms, the AI-assistance disclosure and the
comparator challenge inventory.

`challenges/` contains six standalone [Comparator](https://github.com/leanprover/comparator)
workspaces: `main-theorem` (Theorems 1.2, 8.6, 8.7), `sigma-h` (Theorem 7.2),
`classical-compactness` (Theorem 9.3 = 1.3), `sperner`, `model-cases` (a sanity check that
the explicit solutions `(x_n)⁺` and `|x_n|` satisfy the definitions and are separated by `Σ^H`),
and `lipschitz-q` (the six results for a Lipschitz coefficient listed above).
In each, `Statement.lean` imports Mathlib only and states the theorems with every notion,
including variational solutions, written out inline; `Challenge.lean` states them with `sorry`;
and `Solution.lean` proves them from the library. Ordinary CI only elaborates these files. Exact
statement equality and the permitted-axiom check are established by the release workflow
`.github/workflows/release-comparator.yml`, which runs Comparator with pinned tool revisions and
uploads an attestation. See `challenges/README.md`, which also records a review of the challenges.

## Layout

- `InnerVariational/Defs/`: variational and classical solutions, the monotonicity and frequency
  quantities, `Σ^H`, the reduced boundary and the Laplacian measure, and their versions with a
  Lipschitz coefficient.
- `InnerVariational/Statements/`: the headline theorems, and in `LipschitzQ.lean` those for a
  Lipschitz coefficient. Files whose name ends in `Q` hold the Lipschitz-coefficient versions of
  the corresponding files; the constant-coefficient theorems are derived from them.
- `InnerVariational/Basic/`, `Sobolev/`, `Kernel/`: calculus in polar coordinates, weak gradients,
  and the integral identities (integration by parts, Rellich–Pohozaev, energy identities).
- `InnerVariational/Monotonicity/`, `Frequency/`, `Homogeneity/`: Sections 3–4 and the
  homogeneity estimates of Section 6.
- `InnerVariational/Blowup/`: frequency blow-ups (Section 5).
- `InnerVariational/Estimates/`, `NaberValtorta/`: Sections 6–7.
- `InnerVariational/Regular/`, `Singular/`, `Main/`: Section 8 and the assembly of Theorem 1.2.
- `InnerVariational/Applications/`: Section 9.
- `InnerVariational/Registry/`, `Foundations/`, `Analysis/`, `Harmonic/`: classical background
  results (proved here, or imported from the dependencies), stated in the form used by the proof.
- `InnerVariational/Vendor/`: adapted third-party and shared analysis files (see
  `THIRD_PARTY_NOTICES.md`).
- `Sperner/`: Sperner's inequality, a standalone Mathlib-only library.
- `challenges/`: comparator challenge workspaces.
- `scripts/`: the manifest, integrity, challenge and release-comparator checks used by CI.

## Credits

The mathematics is that of D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff
measure, and compactness for non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78
(2025), no. 3, DOI 10.1002/cpa.22226 (arXiv:2306.10131). It builds on A. Naber and D. Valtorta,
*Rectifiable-Reifenberg and the regularity of stationary and minimizing harmonic maps*, Ann. of
Math. (2) 185 (2017), 131–227; H. W. Alt and L. A. Caffarelli, *Existence and regularity for a
minimum problem with free boundary*, J. Reine Angew. Math. 325 (1981), 105–144; G. S. Weiss,
*Partial regularity for weak solutions of an elliptic free boundary problem*, Comm. Partial
Differential Equations 23 (1998), 439–455 (the monotonicity formula), and *Partial regularity for
a minimum problem with free boundary*, J. Geom. Anal. 9 (1999), 317–326;
E. Sperner, Jr., *Zur Symmetrisierung von Funktionen auf Sphären*, Math. Z. 134 (1973), 317–327;
and, for geometric measure theory, L. C. Evans and R. F. Gariepy, *Measure Theory and Fine
Properties of Functions*, revised edition, CRC Press, 2015, and H. Federer, *Geometric Measure
Theory*, Springer, 1969.

Some files contain code adapted from TauCeti (<https://github.com/TauCetiProject/TauCeti>,
Apache-2.0). Each such file keeps the upstream copyright line and has a `## Provenance` section;
`THIRD_PARTY_NOTICES.md` lists them.

The Lean proofs were written by AI coding agents (Claude, by Anthropic) under the author's
mathematical direction and review. The theorem statements and proof routes were reviewed by the
author. Correctness rests on Lean's kernel check, together with the comparator challenges in
`challenges/`.

## License

Apache License 2.0; see `LICENSE`.

## Citation

If you use this formalization, please cite it using the metadata in `CITATION.cff`, and cite the
paper of Kriventsov and Weiss for the mathematics.
