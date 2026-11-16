# Normality mathlib review package

Two independent candidate patches extract general calculus lemmas used by the
normality formalization. They are ready for human assessment after local
technical checks. No mathlib submission or maintainer review has occurred.

## Baseline and files

- Mathlib: [`cbe1882f5b62496bdfc6bbe540a2b3f2db852440`](https://github.com/leanprover-community/mathlib4/commit/cbe1882f5b62496bdfc6bbe540a2b3f2db852440).
- Lean: `leanprover/lean4:v4.36.0-rc2`.
- [Manifest](../upstream/normality/manifest.json): source and patch hashes,
  target paths, and public declarations.
- [Validation report](../upstream/normality/validation.json): independent and
  combined results tied to those exact patch hashes.

| Candidate | Proposed existing mathlib file | Public declarations |
| --- | --- | --- |
| [Derivative gluing](../upstream/normality/0001-derivative-gluing.patch) | `Analysis/Calculus/Deriv/Basic.lean` | `HasDerivAt.ite_of_eq` |
| [Convex minimizers](../upstream/normality/0002-convex-minimum.patch) | `Analysis/Convex/Deriv.lean` | `ConvexOn.isMinOn_iff_of_hasDerivAt`, `ConvexOn.isMinOn_iff_deriv_eq_zero` |

Both patches apply independently at the baseline and in either order. They
require none of the midset or Wallis patches. The generic source modules import
only mathlib, and the downstream normality proofs actually use them.

## Derivative gluing

Let `𝕜` be a nontrivially normed field and `F` a normed space over `𝕜`. Suppose
`f g : 𝕜 → F` have the same value and derivative `d` at `x`. For any decidable
predicate `P`, the function

```lean
fun t => if P t then f t else g t
```

has derivative `d` at `x`. There is no continuity or interval hypothesis on
`P`. The two first-order remainders satisfy the same little-o bound, regardless
of which branch is selected.

The lemma works for vector-valued functions and for real or complex scalars.
It makes no assertion of strict differentiability, continuous derivatives,
or differentiability away from `x`.

The nearest existing tools found are the within-set union and congruence
lemmas and `HasDerivAt.of_isLittleO`. The overlap search found no existing
ordinary derivative lemma for an arbitrary selector with matching values and
derivatives. This search is not a guarantee against a differently formulated
API elsewhere.

Downstream use: the p- and q-norms have matching first derivatives at the axis
joins. `Radon.hasDerivAt_joined_horizontal` and
`Radon.hasDerivAt_joined_vertical` now use the extracted lemma.

Human review should decide the name and placement, and whether to introduce
the corresponding Fréchet-derivative statement first. The present patch is
deliberately limited to the derivative API used downstream.

## Convex minimizers

For `ConvexOn ℝ s f`, an interior point `x ∈ interior s`, and
`HasDerivAt f d x`, the first lemma proves

```lean
IsMinOn f s x ↔ d = 0
```

The second lemma replaces the specified derivative with `deriv f x` and
explicitly requires `DifferentiableAt ℝ f x`. That assumption prevents the
default derivative value at a nondifferentiable point from implying minimality.
The interior hypothesis excludes endpoint minima with nonzero derivative.
No differentiability at other points of the convex domain is required.

The proof combines the existing local-minimum derivative test with
`ConvexOn.isMinOn_of_rightDeriv_eq_zero`. It adds a convenient equivalence
around those existing tools, not a new optimization theory. The patch imports
`Analysis/Calculus/LocalExtr/Basic.lean` explicitly.

Downstream use: the criterion turns a zero directional derivative into a
global norm minimum in the joined geometry. The paper-level private wrapper
now specializes the generic result to the real line and the point zero.

Human review should assess whether both statement forms are useful and whether
the existing first-order convexity API is the preferred insertion point.

## Validation and reproduction

Each patch alone and both together passed application checks, native Lake
builds of the affected modules and dependencies, all 15 standard environment
linters, source style, and a module-ownership axiom audit in a separate pinned
mathlib checkout. The validation imports no project proof modules.

| Case | New declarations audited, including generated/private declarations |
| --- | ---: |
| Gluing alone | 2 |
| Minimum alone | 2 |
| Combined | 4 |

`Snapshot.lean` records the unmodified target-module declarations first.
The checkers audit every new owned declaration, including unused private
declarations and unexpected namespaces, and require explicit `import all`.
The only permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`.

The combined run confirmed rejection of an unused private axiom inserted into
an existing target module and rejection of a checker missing `import all`.
It restored the candidate source, rebuilt, repeated the positive check, then
reversed its patches and verified a clean baseline checkout. The shared
validation code is also used by the Wallis package; its existing generated
artifacts remain unchanged.

The full downstream library passed `lake build` (6,152 jobs), its 1,600-declaration
axiom audit, all 15 declaration linters, source-style checks, and the audit's
rejection controls. Its audit includes 28 declarations outside the paper namespace.

```sh
python3 scripts/package_normality.py --check

systemd-run --user --scope --quiet -p MemoryMax=6G -p MemorySwapMax=0 \
  env LEAN_NUM_THREADS=1 python3 scripts/check_normality_upstream.py \
  --mathlib /path/to/clean-pinned-mathlib
```

The checkout must already have its dependencies and cache. Its source and
writable build cache must be independent of the project's dependency checkout,
which the validator refuses to mutate. The process is capped at 6 GiB, runs
sequentially, and uses one Lean thread. Direct audit invocations also use a
4 GiB Lean allocation limit. Logs are retained in `.lake/normality-checks/`.

After changing an extracted module, rerun the generator without `--check`,
then rerun isolated validation. CI checks freshness and matching validation
hashes. The source-style checker uses a temporary umbrella to inspect the
changed modules themselves. Whole-mathlib compilation and upstream CI are
outside this validation record.

## Human review boundary

The p-specific normality map, projective convergence, joined norm, uniqueness
proof, and [circumference correction](NORMALITY_NOTES.md) remain downstream.
These two calculus patches are the initial proposed contributions.

The code and package were produced with OpenAI Codex. Under
[mathlib's contribution policy](https://leanprover-community.github.io/contribute/index.html),
a human contributor must understand the proofs and disclose AI assistance.
The policy also prohibits LLM-written GitHub and Zulip comments. The human
contributor should decide suitability, recheck against the submission baseline,
and write any eventual submission or discussion.
