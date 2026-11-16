# Mathlib preparation

The paper formalizations remain a standalone project. Reusable results from
all three papers have been extracted into seven small candidate patches. These are locally checked proposals; no mathlib pull request
or community message has been posted.

| Paper | Candidates | Review material |
| --- | --- | --- |
| Midsets | Union distance; midset definition and transport | Details below |
| Wallis | Real beta integral; balanced Gamma products; closed-section area formula | [Wallis review guide](WALLIS_UPSTREAM.md), [manifest](../upstream/wallis/manifest.json), [validation report](../upstream/wallis/validation.json) |
| Normality | Derivative gluing; the zero-derivative criterion for convex minima | [Normality review guide](NORMALITY_UPSTREAM.md), [manifest](../upstream/normality/manifest.json), [validation report](../upstream/normality/validation.json) |

The Wallis and normality packages each have independent and combined checks
in a separate mathlib checkout. Their guides give the exact assumptions,
closest existing APIs, downstream uses, and reproduction commands.

## Baseline

- Mathlib: [`cbe1882f5b62496bdfc6bbe540a2b3f2db852440`](https://github.com/leanprover-community/mathlib4/commit/cbe1882f5b62496bdfc6bbe540a2b3f2db852440),
  master checked on 2026-11-15.
- Lean: `leanprover/lean4:v4.36.0-rc2`.
- The complete downstream project uses the same exact pin in `lake-manifest.json`.

## Completed midset refactoring

1. **Existing abstractions.** `Point` is an abbreviation for `WithLp 1 (ℝ × ℝ)`.
   The custom metric instance was removed. Coordinate exchange, reflection,
   and translation use mathlib's existing isometry constructions. The distance
   formula is proved from `WithLp.prod_dist_eq_of_L1`.
2. **General metric API.** The modules under
   `FitzhughFarnsworth/Mathlib/Topology/MetricSpace/` have no paper dependencies.
   They define the generic midset and prove union distance, basic midset
   properties, and transport between different pseudometric spaces. The paper
   wrappers and dynamics actually use these results.
3. **Interfaces and maintenance.** Named configuration lemmas supply recurring
   sign and denominator obligations. Iteration has zero, successor, addition,
   and tail theorems. Even and odd metric-distance limits are individually
   available; the combined correctness result is assembled from those APIs.
   The broad `Mathlib.Tactic` import is gone, slope configuration predicates
   are independent of the geometry, and basic dynamics no longer imports
   convergence. Public definitions are documented, and standard source,
   declaration, and text-style linters are enabled.
4. **Current baseline and small contributions.** Both proposed additions are
   installed and checked in a separate checkout of the pinned mathlib master.
   Their patch files contain no paper imports, coordinate calculations,
   numerical examples, or unrelated refactoring.

## Midset candidate 1: distance to a union

[`0001-infDist-union.patch`](../upstream/0001-infDist-union.patch) adds
`Metric.infDist_union` to the existing `HausdorffDistance.lean` file.

```lean
theorem infDist_union (x : α) (hs : s.Nonempty) (ht : t.Nonempty) :
    infDist x (s ∪ t) = min (infDist x s) (infDist x t)
```

The proof reuses `Metric.infEDist_union` and `ENNReal.toReal_min`. Both
nonemptiness hypotheses are essential because real-valued `infDist` assigns
zero to the empty set. No closedness, completeness, or separation assumption
is needed. This is the smallest candidate to review first.

## Midset candidate 2: midsets

[`0002-midset.patch`](../upstream/0002-midset.patch) adds
`Mathlib/Topology/MetricSpace/Midset.lean` and its umbrella import. It is
independent of candidate 1.

The API consists of `Metric.midset`, membership, symmetry, self-midsets,
intersection inclusion, closedness, singleton and empty-set behavior, and
isometry transport. It assumes only pseudometric spaces. Taking the preimage
of the midset of two images needs an isometry; transporting the full image
or arbitrary preimages uses an isometry equivalence.

The suitability decision is whether mathlib wants this named real-distance
construction, and whether a companion extended-distance definition should
precede it. The present definition follows the paper and explicitly documents
its empty-set convention. This is a design question for reviewers, not an
unproved mathematical claim.

## Reproducing the midset candidate checks

In a fresh mathlib checkout at the baseline commit, apply either patch or both:

```sh
git apply /path/to/FitzhughFarnsworth/upstream/0001-infDist-union.patch
git apply /path/to/FitzhughFarnsworth/upstream/0002-midset.patch
lake exe cache get Mathlib/Topology/MetricSpace/HausdorffDistance.lean
lake build Mathlib.Topology.MetricSpace.HausdorffDistance Mathlib.Topology.MetricSpace.Midset
lake exe lint-style Mathlib.Topology.MetricSpace.HausdorffDistance Mathlib.Topology.MetricSpace.Midset
cp /path/to/FitzhughFarnsworth/upstream/Check.lean CandidateCheck.lean
lake env lean CandidateCheck.lean
```

The final command expects both patches and checks all 16 resulting candidate
declarations, including generated ones, with the standard axiom allowlist and
15 environment linters. `import all` loads their private bodies and metadata.
The full upstream library and CI have not been rebuilt: validation here covers
the changed modules and their dependencies. The complete downstream paper
library is built and audited separately.

The original midset preparation passed with 739 downstream declarations,
including 17 outside the paper namespace. That historical count predates the
Wallis library. Run `lake env lean scripts/Audit.lean` in this project for the
current count. Regression checks reject public axioms, unused private axioms,
unused private unfinished proofs in an unrelated namespace, and incomplete
private-declaration coverage. The audit explicitly loads each project module
with `import all`, and the test checks that this import list covers the entire
source tree, including the extracted Wallis and normality modules.

## Human review and submission

[Mathlib's contribution guide](https://leanprover-community.github.io/contribute/index.html)
requires contributors to understand and justify submitted code and to disclose
AI assistance. These proofs and patches were generated and refactored with
OpenAI Codex (with subagent assistance during the earlier midset work), then
checked with Lean and linters.
A human Lean contributor still needs to review the statements, proofs, naming,
and fit before submission. The candidate patches do not establish that review
has happened.

For the midset candidates, the recommended order is the single union-distance
lemma, then discussion of the midset definition and API. The three Wallis
candidates and two normality candidates are separately reviewable; see their
guides for design decisions.
Any community discussion should be written by
the human contributor: the same policy prohibits LLM-written GitHub and Zulip
comments. The paper-specific dynamics and convergence remain downstream unless
reviewers identify further reusable pieces.
