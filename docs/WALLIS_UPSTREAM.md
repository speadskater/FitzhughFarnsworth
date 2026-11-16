# Wallis mathlib review package

Three independent patches extract reusable lemmas from the completed Wallis
formalization. The downstream proofs use the extracted implementations, and
their existing public theorem names remain available. The patches contain no
paper-specific imports or constructions.

These are technically checked candidates for human review. They have not been
submitted to mathlib, reviewed by a maintainer, or accepted.

## Baseline and contents

- Mathlib: [`cbe1882f5b62496bdfc6bbe540a2b3f2db852440`](https://github.com/leanprover-community/mathlib4/commit/cbe1882f5b62496bdfc6bbe540a2b3f2db852440),
  matching master when checked on 2026-11-15.
- Lean: `leanprover/lean4:v4.36.0-rc2`.
- [Manifest](../upstream/wallis/manifest.json): source paths, proposed target
  paths, public declarations, and SHA-256 hashes for sources and patches.
- [Validation report](../upstream/wallis/validation.json): independent and
  combined results tied to the exact patch hashes.

| Candidate | Proposed mathlib location | Public declarations |
| --- | --- | --- |
| [Real beta integral](../upstream/wallis/0001-real-beta-integral.patch) | Existing `Analysis/SpecialFunctions/Gamma/Beta.lean` | `Real.integral_rpow_mul_one_sub_rpow` |
| [Balanced Gamma products](../upstream/wallis/0002-balanced-gamma-products.patch) | New `Analysis/SpecialFunctions/Gamma/FiniteProducts.lean`, plus umbrella import | `Real.tendsto_prod_linear_factors` |
| [Closed-section area](../upstream/wallis/0003-closed-region-area.patch) | Existing `MeasureTheory/Measure/Lebesgue/Integral.lean` | `volume_region_between_cc_eq_integral'` and its pointwise variant |

All three patches apply directly to the baseline, in any order or individually.
None requires the midset candidates in [UPSTREAM.md](UPSTREAM.md).

## Mathematical scope and existing APIs

### Real beta integral

For strictly positive real `s` and `t`, the candidate proves

```lean
(∫ x : ℝ in 0..1, x ^ (s - 1) * (1 - x) ^ (t - 1)) =
  Real.Gamma s * Real.Gamma t / Real.Gamma (s + t)
```

The existing `Complex.betaIntegral` and
`Complex.betaIntegral_eq_Gamma_mul_div` already supply the complex result.
This small real-valued interface handles the coercions and real powers once.
Its private helper identifies the real integral with the complex integral;
the public proof then uses the existing Gamma quotient. Positivity ensures
the analytic identity holds, including parameters below one with singular
endpoint behavior. No new definition of the beta function is introduced.

Downstream, `Wallis.integral_beta` is a wrapper, and the p-disk area calculation
uses it for every `p > 0`. Review should decide the best name and whether a
companion real interval-integrability lemma would improve the interface.

### Balanced Gamma products

For a finite index set `s` and positive shifts `x i`, `y i`, assuming
`∑ i ∈ s, x i = ∑ i ∈ s, y i`, the candidate proves

```lean
Tendsto (fun n : ℕ ↦
  ∏ k ∈ Finset.range n, (∏ i ∈ s, (x i + k)) / (∏ i ∈ s, (y i + k)))
  atTop (𝓝 ((∏ i ∈ s, Real.Gamma (y i)) / (∏ i ∈ s, Real.Gamma (x i))))
```

The shared finite index set makes the numbers of factors equal; the empty set
is allowed. Positivity is required only on that set and proves the finite
denominators and Gamma denominator are nonzero. Products start at `k = 0`.
The conclusion concerns the ordered sequence of finite partial products; it
does not assert an unordered `HasProd` result.

The proof combines `Real.GammaSeq_tendsto_Gamma` with two private finite-product
identities. Equal shift sums cancel the power of the index, and equal numbers
of factors cancel the factorial powers. The final shift from `n + 1` to `n`
uses the existing filter theorem.

Both `Wallis.tendsto_balanced_finset_prod` and the two-factor
`Wallis.tendsto_balanced_prod` now specialize this lemma. Review should decide
the name and file placement, and whether any further generality is useful
before adding complex parameters, separate index sets, or a `HasProd` API.
Those extensions are not part of these candidates.

### Measure of a region with closed vertical sections

Let `μ` be a sigma-finite measure on an arbitrary measurable space `α`. For a
measurable set `s` and integrable functions `f`, `g` on `s`, the candidate proves

```lean
μ.prod volume {p : α × ℝ | p.1 ∈ s ∧ p.2 ∈ Icc (f p.1) (g p.1)} =
  ENNReal.ofReal (∫ x in s, g x - f x ∂μ)
```

The primed theorem assumes `f ≤ᵐ[μ.restrict s] g`; the second theorem accepts
pointwise ordering on `s`. Continuity, compactness, and an interval-shaped base
are unnecessary. Both boundary graphs are included, but the entire region
need not be a closed set.

Existing `volume_regionBetween_eq_integral'` and
`volume_regionBetween_eq_integral` cover open vertical sections. The existing
`nullMeasurableSet_region_between_cc` supplies measurability here. The proof
restricts the base measure, applies the product-measure section formula, uses
`Real.volume_Icc`, and converts the nonnegative integral to `ENNReal`.

The Wallis measured-area proof specializes this API to continuous profiles on
`Icc (-1) 1`, preserving the nonconvex `0 < p < 1` case. Review should consider
naming alongside `regionBetween`, whether to offer other endpoint conventions,
and whether the sigma-finiteness assumption should be weakened.

The overlap review searched the pinned Gamma, interval-integral, and Lebesgue
measure APIs for real beta integrals, balanced products, and closed-section
area formulas. The results above are the closest existing interfaces found;
this is not a guarantee against differently formulated results elsewhere.

## Validation

The recorded run used a separate mathlib checkout with its own writable build
cache and no downstream project imports. Each patch alone and their combination
passed `git apply --check`, builds of the changed modules and dependencies,
axiom checks, 15 standard environment linters, and focused text-style checks.

| Case | New declarations audited, including private/generated declarations |
| --- | ---: |
| Beta alone | 2 |
| Products alone | 4 |
| Area alone | 2 |
| Combined | 8 |

Before applying patches, `Snapshot.lean` records the original declarations of
the two existing target modules. Candidate checkers compare all declarations
owned by their modules against this baseline. They use explicit `import all`
to include private declarations, without filtering on the advertised names or
namespaces. The only allowed axioms are `propext`, `Classical.choice`, and
`Quot.sound`.

Negative controls confirmed rejection of an unused private axiom appended to
an existing target module and of a checker missing the private-declaration
import. The validator restores the exact patch contents, rebuilds, and repeats
the combined audit afterward. It reverses its own patches between cases and
finishes with the source checkout clean at the baseline.

The pinned text-style executable checks the direct imports of its argument.
The validator therefore creates a temporary umbrella importing the candidate
modules, so the checks actually inspect their source files. Full mathlib build,
umbrella compilation, and upstream CI are outside the recorded validation scope.
The complete downstream library also passed its build, lint, and axiom checks.
At the original Wallis packaging commit `7261b8f`, the project audit covered
1,137 declarations, including 25 outside the paper namespace, and its rejection
controls passed. This historical count predates the completed normality library.

## Reproduction and maintenance

From this project, confirm that the generated patches and checkers match the
generic modules actually used by the Wallis proofs:

```sh
python3 scripts/package_wallis.py --check
```

After deliberately changing a generic module, omit `--check` to regenerate
the artifacts. Then repeat the isolated validation to refresh its report.
CI checks artifact freshness and that the validation report records the current
patch hashes and dependency pins. The isolated validation is an explicit
separate step and does not run as part of ordinary project CI.

Prepare a clean, separate mathlib checkout at the exact baseline and obtain its
dependencies and cache using `lake exe cache get`. Do not use this project's
`.lake/packages/mathlib` as the validation checkout. The validator refuses that
path and rejects unrelated source changes or a different commit/toolchain.
Build caches must be independently writable; do not hardlink mutable artifacts
from the project's dependency checkout.

Then run from this project, replacing the checkout path below:

```sh
systemd-run --user --scope --quiet -p MemoryMax=6G -p MemorySwapMax=0 \
  env LEAN_NUM_THREADS=1 python3 scripts/check_wallis_upstream.py \
  --mathlib /path/to/mathlib-wallis-review
```

This Linux invocation caps the whole process group at 6 GiB with no swap.
The Python validator runs its commands sequentially and uses one Lean thread;
direct Lean audit invocations also have a 4 GiB allocation limit. On systems
without user systemd scopes, use an equivalent process memory limit. Cache
preparation should use the same resource controls.

The default report is `upstream/wallis/validation.json`; use `--report PATH`
for a separate run record. Detailed command output is saved inside the review
checkout at `.lake/wallis-checks/validation.log`. A failed command stops the
run and attempts to reverse only the patches it applied.

## Human review and submission boundary

The paper's geometric constructions, source-equation corrections, p-disk
specializations, and unbalanced two-factor asymptotics remain downstream.
These three patches are a first set of general interfaces, not a proposal to
move the entire paper into mathlib.

A human contributor still needs to assess the statements, proof choices,
names, placement, duplication, and usefulness, then recheck against the mathlib
revision used for submission. The beta lemma is the smallest starting point;
the other candidates can be reviewed independently.

The code and this preparation were produced with OpenAI Codex.
[Mathlib's contribution policy](https://leanprover-community.github.io/contribute/index.html)
requires human understanding and disclosure of AI assistance, and prohibits
LLM-written GitHub and Zulip comments. These are local technical review notes;
the human contributor should write the eventual submission and discussion.
