# Comparator challenges

This directory contains standalone [Comparator](https://github.com/leanprover/comparator)
workspaces for the headline theorems of `InnerVariational`, the formalization of

> D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
> non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3,
> DOI [10.1002/cpa.22226](https://doi.org/10.1002/cpa.22226),
> [arXiv:2306.10131](https://arxiv.org/abs/2306.10131).

Theorem numbers refer to arXiv version 2 of the paper. Comparator checks that a solution proves
exactly the statement of a trusted challenge, passes the kernel, and uses only permitted axioms.

Every workspace has:

- `Statement.lean`: the trusted mathematical claims, importing Mathlib only. Every notion the
  claims use (normalized Hausdorff measure, divergence, variational and classical solutions, the
  quantities `D`, `H`, `M`, `N`, the set of highest density `Σ^H`, `H_x(u; 0+)`, `α(n)`,
  countable rectifiability, Gauss–Green pairs and the reduced boundary, the Laplacian measure,
  distributional Laplacians, and in `lipschitz-q` their versions with a Lipschitz coefficient and
  viscosity solutions) is defined in this file from Mathlib, so a reader can check the meaning of
  each claim without reading the library;
- `Challenge.lean`: the trusted wrapper, importing `Statement` only and stating each claim with
  `sorry`;
- `Solution.lean`: the untrusted proof, importing `Statement` and the library and proving the
  same theorems from the library;
- `config.json`: the theorem names and the permitted axioms `propext`, `Quot.sound`,
  `Classical.choice`; and
- `lakefile.toml`: a Lake workspace whose default targets are the trusted modules `Statement`
  and `Challenge` only.

The trusted files are `Statement.lean`, `Challenge.lean`, `config.json` and `lakefile.toml`.
`Solution.lean` is not trusted. Keeping the claims in `Statement.lean` gives both wrappers one
statement surface; Comparator is still the authority on statement equality.

| Workspace | Paper | Challenge theorems | Library theorems | Trusted lines |
|---|---|---|---|---:|
| `main-theorem` | Theorems 1.2, 8.6, 8.7 | `challenge_main_theorem`, `challenge_chi_eq_indicator`, `challenge_laplacian_measure_eq` | `InnerVariational.Statements.main_theorem`, `InnerVariational.Statements.chi_eq_indicator`, `InnerVariational.Statements.laplacian_measure_eq` | 309 |
| `sigma-h` | Theorem 7.2 | `challenge_sigmaH_main`, `challenge_sigmaH_main_frequency` | `InnerVariational.Statements.sigmaH_main`, `InnerVariational.Statements.sigmaH_main_frequency` | 214 |
| `classical-compactness` | Theorem 9.3 (= Theorem 1.3) | `challenge_classical_compactness` | `InnerVariational.Statements.classical_compactness` | 299 |
| `sperner` | Sperner's inequality, used in Lemmas 8.1 and 8.3 | `challenge_sperner_half_volume` | `Sperner.sperner_half_volume` | 66 |
| `model-cases` | sanity check, §3.1 and §8.2 | `challenge_model_cases` | (proved in the solution from library lemmas) | 171 |
| `lipschitz-q` | Lipschitz coefficient: §6 (`Σ^H`), Proposition 3.4, Lemma 8.3, Theorem 8.6, blow-up limits | `challenge_sigmaHQ_density`, `challenge_sigmaHQ_closed`, `challenge_viscosityQ`, `challenge_blowup_limitQ`, `challenge_blowup_homogeneousQ`, `challenge_chi_eq_indicatorQ` | `InnerVariational.IsVariationalSolutionQ.mem_sigmaHQ_iff_frontier_inter`, `.closure_sigmaHQ_inter_subset`, `.isViscositySolutionQ_diff_sigmaHQ`, `.exists_blowup_limit`, `.blowup_homogeneous`, `InnerVariational.Singular.chi_eq_indicator_of_localQ` | 299 |

"Trusted lines" counts `Statement.lean` and `Challenge.lean`. The shared vocabulary (variational
solutions, `Σ^H`, the Laplacian measure) is repeated in each workspace that needs it, since the
workspaces are standalone; the copies are identical.

Coverage: `main-theorem`, `sigma-h`, `classical-compactness` and `sperner` certify the theorems
of the paper, for the constant coefficient `Q ≡ 1` (eight challenge theorems). `lipschitz-q`
certifies the results that are also proved for a Lipschitz coefficient (six challenge theorems;
see the next section). `model-cases` is a sanity check (non-vacuity of the definitions) and is not
counted as theorem coverage. Theorem 1.4 (= Theorem 10.1, singular perturbation limits) is not
part of this release.

## Lipschitz coefficient

The paper studies the functional `∫ (|∇u|² + χ)`. The library also treats
`∫ (|∇u|² + Q² χ)` for a coefficient `Q` that is Lipschitz with `0 < c ≤ Q ≤ C'` on `Ω`, in
dimension `n ≥ 2`. A variational solution for `Q` satisfies the domain-variation identity of this
functional, which has the extra term `∇(Q²) · ξ χ`. The following results are proved for such
`Q`, and `lipschitz-q` certifies them:

- the identification of `χ` (Theorem 8.6): either `u ≡ 0` and `χ = 1` a.e., or `χ = χ_{u>0}` a.e.;
- `Σ^H` is relatively closed in `Ω` (Section 6);
- `u` is a viscosity solution of `|∇u| = Q` on `Ω \ Σ^H` (Lemma 8.3);
- blow-up limits exist along subsequences and are variational solutions on `ℝⁿ` for the constant
  coefficient `Q(x₀)`, with `L¹_loc` convergence of `χ`, and they are homogeneous of degree one
  (Proposition 3.4);
- the density characterization of `Σ^H`: `x ∈ Σ^H` if and only if `x` is a free boundary point at
  which `{χ = 1}` has density one.

Here `Σ^H` is defined with the coefficient frozen at the point:
`M^{Q(x)}_x(u; 0+) ≥ Q(x)² |B₁|`, where `M^q` is the Weiss energy with `χ` replaced by `q² χ`.
For `Q ≡ 1` all of these reduce to the statements for the paper's functional.

The following results are certified for `Q ≡ 1` only: the rectifiability and the local
finiteness of the `ℋ^{n-1}`-measure of the free boundary (Theorems 1.2 (ii) and 7.2), the
identification of the Laplacian measure (Theorem 8.7 and Theorem 1.2 (iii)–(iv)), and the
compactness of classical solutions (Theorem 9.3 = Theorem 1.3). (The library proves a
Lipschitz-coefficient form of Theorem 7.2 as a supporting result, not as a challenge.)

## What ordinary CI establishes

`scripts/check-challenges.sh` builds `Statement`, `Challenge` and `Solution` in every
workspace, then runs `#print axioms` on every theorem listed in each `config.json` and requires
exactly the permitted axioms. It is meant to run in per-commit CI. This catches syntax,
elaboration, missing-proof and axiom regressions only. It does not check that the challenge and
the solution state the same theorems: exact statement equality is established only by the release
comparator workflow.

## Development path

In a trusted checkout, after `lake exe cache get && lake build InnerVariational Sperner` at the
repository root:

```sh
cd challenges/<workspace>
lake build Statement Challenge Solution
```

or, for all workspaces with the axiom check, `scripts/check-challenges.sh` from the
repository root. Every workspace sets `packagesDir = "../../.lake/packages"`, so it shares the
root workspace's dependency checkouts and builds; its `lake-manifest.json` locks the same
revisions as the root manifest, with the root package as a path dependency.

## Release verification path

The release gate is the comparator workflow `.github/workflows/release-comparator.yml` with
`scripts/release-comparator.sh`, adapted from gmt-foundations, on a fresh GitHub-hosted Linux
runner. (Both files, and the per-commit CI workflow, are added with the CI setup; until then the
scripts are run by hand.) It:

1. checks out the exact release commit;
2. fetches the Mathlib cache and builds the trusted library;
3. installs the pinned tools (below);
4. builds only the trusted `Statement` and `Challenge` targets of each workspace, outside the
   sandbox (Comparator's sandbox cannot write the shared dependency folder);
5. runs Comparator on every `challenges/*/config.json`, failing on any statement mismatch or
   unpermitted axiom; and
6. uploads an attestation artifact.

Do not run `lake build Solution`, or otherwise compile `Solution.lean`, in the release workspace
before Comparator has processed it. This ordering follows Comparator's documented threat model.

Pinned release tools:

- Lean and Mathlib: `v4.30.0` (Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`);
- Comparator: `d03acab154d269c06e60e4de7e4cc85deebff94b`;
- `lean4export`: `a3e35a584f59b390667db7269cd37fca8575e4bf`, built with this repository's
  `lean-toolchain`; and
- `landrun`: `5ed4a3db3a4ad930d577215c6b9abaa19df7f99f`.

Comparator runs under `landrun` without the additional `systemd-run` containment that upstream
recommends for a full adversarial guarantee. A passing run establishes Comparator's statement,
kernel and permitted-axiom checks, not that stronger sandbox claim.

The attestation artifact contains `attestation.json` (tested commit and tree SHA, Lean and
Mathlib revisions, the three tool revisions, and each configuration with its result and axiom
check) and the complete per-configuration logs. Before a version tag, dispatch the workflow on
the exact release commit, require it to pass, and attach the artifact to the GitHub release.

## Acceptance record

No Comparator run has been recorded yet. The first release run will be summarized here:

| Date | Commit | Workflow run | Tool revisions | `main-theorem` | `sigma-h` | `classical-compactness` | `sperner` | `model-cases` | `lipschitz-q` |
|---|---|---|---|---|---|---|---|---|---|
| _pending_ | | | | | | | | | |

Local checks at the time of writing: all six workspaces build `Statement`, `Challenge` and
`Solution`, and `#print axioms` on every solution theorem gives exactly `propext`,
`Classical.choice` and `Quot.sound`.

## Review against the challenge-design checklist

Each workspace was reviewed for the usual ways in which a challenge can certify less than it
advertises.

### All workspaces

**Trusted surface.** `Statement.lean` imports Mathlib only and `Challenge.lean` imports
`Statement` only. The claims use Mathlib's `EuclideanSpace`, Lebesgue measure, `μH[d]`,
`fderiv`, `gradient`, `LinearMap.trace`, Bochner integrals, `Measure.restrict`, `withDensity`,
`limUnder`, `Tendsto`, `frontier`, `thickening`, `LipschitzWith`, `ContDiff`, `HarmonicAt` and
the `InnerProductSpace` Laplacian; the derived notions are short definitions in the same file.

**No tautologies.** The paper's notions are written out, not named: the domain-variation identity
`∫ ((|∇u|² + χ) div ξ − 2 ∇u·Dξ∇u) = 0` for Lipschitz test fields, the monotonicity quantities
as explicit integrals, `Σ^H` through the limit `M_x(u; 0+)`, the Laplacian measure as a sum of
restricted Hausdorff measures. Where the library's definitions are already in Mathlib terms
(variational solutions, rectifiability, Gauss–Green pairs), the challenge restates them field by
field and the solution matches them by unfolding. The challenge vocabulary deliberately differs
from the library's in three places, and there the solution uses real theorems:

- sphere integrals are integrals against `ℋ^{n-1}` on `∂B_r(x)`, while the library uses Mathlib's
  polar-coordinates measure `Measure.toSphere`; the solution uses the theorem that the latter is
  `ℋ^{n-1}⌊S^{n-1}` (gmt-foundations) and the scaling of Hausdorff measure;
- `α(n)` is defined with the last coordinate `y_n`, as in the paper, while the library uses `y_1`;
  the solution uses the invariance of Hausdorff measure under the coordinate swap;
- `Σ^H` is defined, as in the paper, by `M_x(u; 0+) ≥ |B₁|`, while the library asks
  `M_x(u; r) ≥ |B₁|` for every admissible `r`; the solution uses the monotonicity formula and the
  existence of `M_x(u; 0+)` (Propositions 3.4 and 3.5).

In `lipschitz-q`, `Σ^H` is defined by "`M^{Q(x)}_x(u; r)` converges to a real number
`m ≥ Q(x)² |B₁|`", while the library compares the limit `M^{Q(x)}_x(u; 0+)`, taken in
`[−∞, ∞]`, with `Q(x)² |B₁|`; the solution uses the existence of this limit (almost-monotonicity)
and the fact that it is a real number where `u(x) = 0`.

**The Gauss–Green pair.** The reduced boundary `∂*E` is defined from a Gauss–Green pair `(μ, ν)`
(a Radon measure and a unit vector field with `∫_E div φ = ∫ φ·ν dμ`), which is how the library
encodes the perimeter measure `|Dχ_E|` and the outer normal. By De Giorgi's structure theorem the
pair exists exactly for sets of locally finite perimeter, and it is unique; `∂*E ∩ Ω` is then the
set of points of the support where the averages of `ν` converge to a unit vector (Evans–Gariepy,
Definition 5.4). The existential quantifier over the pair would make `∂*E` empty if no pair
existed. The Theorem 8.7 challenge therefore also asserts that `{u > 0}` has a Gauss–Green pair
in `Ω`.

**No packaged hypotheses.** Every hypothesis is a condition of the paper's theorem, written out
in the file: `n ≥ 2`, `Ω` open (part of the definition) and connected where the paper says
"domain", the variational or classical solution property, and the explicit bounds of Theorems 7.2
and 9.3.

**Degenerate parameters.** `n ≥ 2` is explicit. `C_V` is universally quantified, so no choice of
it can make a claim easier; the `model-cases` workspace shows that the definition of variational
solution is satisfied by explicit solutions with `C_V = 1`. Constants in the conclusions (`C` in
Theorem 7.2, the subsequence and the limit in Theorem 9.3) are existentially quantified with the
required properties and the paper's dependence (`C = C(N₊, n)`). "For `ℋ^{n-1}`-a.e. `x ∈ A`" is
an `ℋ^{n-1}`-null exceptional set. The integrals in the definitions and conclusions are of
bounded functions on bounded sets (Lipschitz `u`, Lipschitz or smooth compactly supported test
fields), so no condition holds only because Lean assigns `0` to a non-integrable integral. The
junk value of `limUnder` is excluded by asserting that `H_x(u; r) → H_x(u; 0+)` on `Σ^H`.

### `main-theorem`

Theorem 1.2 (i)–(iv) as one conjunction, Theorem 8.6 and Theorem 8.7. Variants, all stated in the
`Statement.lean` docstring:

- (iii) and Theorem 8.7 use the body's form, with `Σ^H` and the unaveraged
  `H_x(u; r) = r^{-(n+1)} ∫_{∂B_r(x)} u²`; the introduction prints `Σ_**` and an averaged `H`, for
  which `α(n)` is not normalized;
- (iv), second display, carries the factor `√(H_x(u; r))` in front of `α(n)|(y − x)·ν|`, which
  Lemma 8.5 (1) supplies and the printed display omits (see the docstring for the model case
  `2α(n)|y_n|`, `χ ≡ 1`);
- the claims add the existence of `H_x(u; 0+)` on `Σ^H` and (Theorem 8.7) a Gauss–Green pair for
  `{u > 0}`.

### `sigma-h`

Theorem 7.2 (1)–(2) with the paper's quantifier order (`∀ N₊, ∃ C, ∀ C_V u χ t`), and 7.2 (3).
Variants: in (1)–(2) the solution is assumed on an open `Ω ⊇ B̄₁`, since `N_0(u; 1)` involves
`u` on `∂B₁`, which a solution on `B₁` alone does not constrain (example in the docstring);
`B_{1/100}(x)` is read as `B_{1/100}`; the neighbourhood bound is for `t ≤ s ≤ 1`, not for all
`s ≥ t`; `t = 0` is stated with `Σ^H`. The frequency uses `N = 0` where `H = 0` (the paper
uses `−∞`); this does not matter, as `H_x(u; r) > 0` at points `x ∈ Σ^H` for small `r > 0`,
and `N₊` is arbitrary.

### `classical-compactness`

Theorem 9.3 (= Theorem 1.3). The hypothesis is `sup_k ‖u_k‖_{C^{0,1}(B₁)} ≤ C` (Theorem 9.3
writes `‖∇u_k‖_{C^{0,1}}`; we use the bound of Theorem 1.3). Classical solutions are defined as
in Definition 9.1, with
"`∂{u > 0}` is locally a smooth graph" stated as "locally the zero set of a smooth `F` with
`∇F(x) ≠ 0`". The limit is a variational solution on `B₁` with constant `C`; local Hausdorff
convergence of the free boundaries and `L¹_loc` convergence of the positivity sets are written out
with compact subsets of `B₁`. The claim adds the existence of `H_x(u; 0+)` on `Σ^H`.

### `sperner`

Sperner's inequality (Math. Z. 134 (1973)) in the homogeneous form used in the proofs of Lemmas
8.1 and 8.3, with the equality case. The `Sperner` library is Mathlib-only and its theorem is
stated in the same Mathlib terms, so the solution is a direct application. This is a hard
technical input rather than a theorem of the paper.

### `model-cases` (sanity check)

The half-plane solution `(y_n)⁺` and the two-plane solution `|y_n|`, with `χ = χ_{u>0}`, are
variational solutions on `ℝⁿ` with `C_V = 1`; `0 ∉ Σ^H` for the first and `0 ∈ Σ^H` for the
second; and `H_0(α(n)|y_n|; r) = 1` for `r > 0`. This guards against a vacuous definition of
variational solution, a trivial `Σ^H`, and a wrong normalization of `α(n)` or of the sphere
integrals. It is labelled a sanity check: it is not a theorem of the paper.

**Not covered.** There is no negative test of the domain-variation identity (a pair such as
`(2(y_n)⁺, χ_{u>0})`, which violates the free boundary condition and is not a variational
solution), and no model computation of a reduced boundary or of a Laplacian measure.

### `lipschitz-q`

The results listed under "Lipschitz coefficient" above, as six challenge theorems (the blow-up
item is split into the existence of the limit and its homogeneity), for a variational solution for a
coefficient `Q` with `QBounds Ω Q L c C'` (`Q` is `L`-Lipschitz on `Ω` and `0 < c ≤ Q ≤ C'`
there). The paper states these results for `Q ≡ 1` only; each challenge is the Lipschitz-coefficient
form of the corresponding statement, and the `Statement.lean` docstring names the result of the
paper that it extends. The domain-variation identity carries the term `D(Q²)(x) ξ(x) χ(x)`, with
Mathlib's `fderiv`; `Q²` is differentiable a.e. on `Ω` (Rademacher) and the term vanishes outside
the support of `ξ`. The bounds `L`, `c`, `C'` and the constant `C_V` are universally quantified.
Variants, all stated in the docstring:

- `Σ^H` uses the coefficient frozen at the point, `M^{Q(x)}_x(u; 0+) ≥ Q(x)² |B₁|`;
- the density characterization uses the relative free boundary `frontier {y ∈ Ω : u(y) > 0}`;
- the blow-up claims are stated along a sequence `r_k → 0+` with `u_{x,r_k} → u₀` locally
  uniformly; the limit `(u₀, χ₀)` is a variational solution on `ℝⁿ` for the constant coefficient
  `Q(x)` with the same `C_V`, and `χ_{x,r_k} → χ₀` in `L¹(K)` for every compact `K` along a
  subsequence;
- the identification of `χ` is stated for a connected set on which `(u, χ)` is a solution near
  every point, and adds `χ = 1` a.e. in the case `u ≡ 0`.

For `Q ≡ 1` the definitions reduce to those of the other workspaces (in the library:
`isVariationalSolutionQ_one_iff`, `isViscositySolutionQ_one_iff`,
`IsVariationalSolution.sigmaHQ_one`).
