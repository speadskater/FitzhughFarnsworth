#!/usr/bin/env python3
"""Render the two independent normality calculus candidates for human review."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

from package_wallis import BASELINE, ROOT, TOOLCHAIN, checker, git_text, patch_file, path_for, snapshot


PACKAGE = "normality"
OUTPUT = ROOT / "upstream" / PACKAGE
CANDIDATES = [
    {"id": "gluing", "patch": "0001-derivative-gluing.patch", "new_module": False,
     "module": "Mathlib.Analysis.Calculus.Deriv.Basic", "section": "DerivativeGluing",
     "public_declarations": ["HasDerivAt.ite_of_eq"]},
    {"id": "minimum", "patch": "0002-convex-minimum.patch", "new_module": False,
     "module": "Mathlib.Analysis.Convex.Deriv", "section": "ConvexCriticalPoints",
     "public_declarations": ["ConvexOn.isMinOn_iff_of_hasDerivAt",
                             "ConvexOn.isMinOn_iff_deriv_eq_zero"]},
]


def render(mathlib: Path) -> dict[str, str]:
    if git_text(mathlib, "rev-parse", "HEAD").strip() != BASELINE:
        raise RuntimeError("Mathlib checkout must be at the recorded baseline")
    if git_text(mathlib, "show", f"{BASELINE}:lean-toolchain").strip() != TOOLCHAIN:
        raise RuntimeError("The baseline toolchain does not match the package")
    artifacts = {"Snapshot.lean": snapshot(CANDIDATES, package=PACKAGE)}
    manifest = {"baseline": BASELINE, "toolchain": TOOLCHAIN, "candidates": []}
    for candidate in CANDIDATES:
        target = path_for(candidate["module"])
        source = "FitzhughFarnsworth/" + target
        text = (ROOT / source).read_text()
        imports = [line.split("import ", 1)[1] for line in text.splitlines()
                   if line.startswith(("import ", "public import "))]
        if not imports or any(not name.startswith("Mathlib.") for name in imports):
            raise RuntimeError(f"Candidate has a non-mathlib import: {source}")
        old = git_text(mathlib, "show", f"{BASELINE}:{target}")
        existing = {line.split("import ", 1)[1] for line in old.splitlines()
                    if line.startswith(("import ", "public import "))}
        added = [name for name in imports if name != candidate["module"] and name not in existing]
        new = old
        if added:
            additions = "\n".join("public import " + name for name in added) + "\n"
            new = old.replace("module\n\n", "module\n\n" + additions, 1)
        body = text.split("public section\n\n", 1)[1].rstrip()
        section = candidate["section"]
        new = new.rstrip() + f"\n\nsection {section}\n\n" + body + f"\n\nend {section}\n"
        patch = patch_file(target, old, new)
        artifacts[candidate["patch"]] = patch
        check_name = "Check" + candidate["id"].capitalize() + ".lean"
        artifacts[check_name] = checker([candidate], package=PACKAGE)
        manifest["candidates"].append({
            **candidate, "source": source, "target": target, "checker": check_name,
            "source_sha256": hashlib.sha256(text.encode()).hexdigest(),
            "patch_sha256": hashlib.sha256(patch.encode()).hexdigest(),
        })
    artifacts["Check.lean"] = checker(CANDIDATES, package=PACKAGE)
    artifacts["manifest.json"] = json.dumps(manifest, indent=2) + "\n"
    return artifacts


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mathlib", type=Path, default=ROOT / ".lake/packages/mathlib")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    artifacts = render(args.mathlib.resolve())
    if args.check:
        stale = [name for name, text in artifacts.items()
                 if not (OUTPUT / name).exists() or (OUTPUT / name).read_text() != text]
        if stale:
            raise RuntimeError("Stale packaging artifacts: " + ", ".join(stale))
        report_path = OUTPUT / "validation.json"
        if not report_path.exists():
            raise RuntimeError("Missing validation report; run scripts/check_normality_upstream.py")
        report = json.loads(report_path.read_text())
        hashes = {c["patch"]: hashlib.sha256(artifacts[c["patch"]].encode()).hexdigest()
                  for c in CANDIDATES}
        if (report.get("baseline") != BASELINE or report.get("toolchain") != TOOLCHAIN
                or report.get("patch_sha256") != hashes):
            raise RuntimeError("Stale validation report; rerun scripts/check_normality_upstream.py")
        print(f"All {len(artifacts)} normality artifacts and validation hashes match.")
    else:
        OUTPUT.mkdir(parents=True, exist_ok=True)
        for name, text in artifacts.items():
            (OUTPUT / name).write_text(text)
        print(f"Generated {len(artifacts)} normality packaging artifacts.")


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, subprocess.CalledProcessError) as error:
        sys.exit(str(error))
