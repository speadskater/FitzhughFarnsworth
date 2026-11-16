# Area Moments from a Wallis-Type Geometric Construction

**Author:** Joshua M. Fitzhugh

**Status:** Research draft for independent human review, November 2026.

- [Read the PDF](wallis-moments.pdf).
- [LaTeX source](wallis-moments.tex) and [BibTeX references](references.bib).
- [Verification manifest](verification.json), including the fixed proof revision and source hashes.

The manuscript interprets the actual cyclic attachment construction through
measured quarter-disk moments. It includes proofs, geometric illustrations,
integer-order recovery, and the extension obtained by changing the starting
cube's volume. The special-function identities and earlier moment literature
are credited explicitly. Publication priority has not been established.

The final section maps the central statements to Lean declarations and explains
which example calculations and interpretive consequences are outside that
formal correspondence. AI assistance is disclosed in the manuscript.

## Build the PDF

The tested engine is [Tectonic 0.17.0](https://github.com/tectonic-typesetting/tectonic/releases/tag/tectonic%400.17.0).
Its official TeX Live bundle is pinned in `verification.json`. On the first
build, the compiler downloads the support files it needs from that bundle.

From the repository root, with `tectonic` on your PATH:

```sh
python3 papers/wallis-moments/build.py
```

Alternatively, set `TECTONIC` to an absolute executable path. The script also
recognizes the development installation under
`.cache/tools/tectonic-0.17.0/tectonic`.

On Linux, a memory-capped build can be run with:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 \
  python3 papers/wallis-moments/build.py
```

The script enables Tectonic's untrusted-input mode, uses a fixed
source timestamp, and rejects unresolved references, missing characters, and
overflowing boxes before copying the PDF into this directory. Intermediate
files and the full compiler log remain under the ignored `build/` directory.
The PDF is tracked so GitHub readers can inspect it without installing LaTeX.

## Reproduce the formal checks

The manuscript links to proof commit
[`5151013f072b1aaed822bfbc9ee7079fbc7cc2ff`](https://github.com/speadskater/FitzhughFarnsworth/commit/5151013f072b1aaed822bfbc9ee7079fbc7cc2ff).
At that revision, with the pinned dependencies installed, run:

```sh
LEAN_NUM_THREADS=1 lake build
lake env lean -j1 -M4096 scripts/Audit.lean
python3 scripts/lint_project.py
python3 scripts/test_audit.py
```

The recorded checks cover all 1,706 project declarations, including private
declarations, and 15 environment linters. The permitted axioms are
`propext`, `Classical.choice`, and `Quot.sound`. Source hashes in the manifest
identify the four extension modules independently of later repository changes.
The [project roadmap](../../docs/ROADMAP.md#completed-extension-side-ratios-and-area-moments)
describes the hypotheses and the theorem entry points.

## Review scope

The draft needs human review of the mathematical presentation and formal
specifications, a fuller literature review, and an assessment of publication
suitability. It is not a journal submission or a claim that the interpretation
is previously unpublished. The author line names Joshua M. Fitzhugh; the earlier
Fitzhugh–Farnsworth paper is cited as prior work.
