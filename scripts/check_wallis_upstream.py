#!/usr/bin/env python3
"""Validate each Wallis patch alone, then all together, in a clean pinned mathlib checkout.

The checkout must already have its dependency cache. Only these generated patches
are applied and reversed; unrelated changes are rejected. Checks run sequentially.
The optional report records patch hashes, declaration counts, and audit controls.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

import package_wallis as wallis
from package_wallis import path_for


class Validation:
    def __init__(self, checkout: Path, package=wallis):
        self.package = package
        self.checkout = checkout
        self.scratch = checkout / ".lake" / f"{package.PACKAGE}-checks"
        self.scratch.mkdir(parents=True, exist_ok=True)
        self.log = self.scratch / "validation.log"
        self.log.write_text("")
        self.environment = {**os.environ, "LEAN_NUM_THREADS": "1"}

    def run(self, command: list[str], *, expected_failure: str | None = None) -> str:
        result = subprocess.run(command, cwd=self.checkout, env=self.environment,
                                text=True, capture_output=True, check=False)
        output = result.stdout + result.stderr
        with self.log.open("a") as log:
            log.write(json.dumps(command) + "\n" + output + "\n")
        if expected_failure is not None:
            if result.returncode == 0 or expected_failure not in output:
                raise RuntimeError(f"Expected rejection containing {expected_failure!r}:\n{output}")
        elif result.returncode:
            raise RuntimeError(f"Command failed: {command}\n{output}")
        return output

    def clean(self) -> None:
        if self.run(["git", "rev-parse", "HEAD"]).strip() != self.package.BASELINE:
            raise RuntimeError("The candidate checkout is not at the pinned baseline")
        status = self.run(["git", "status", "--porcelain", "--untracked-files=all"])
        if status:
            raise RuntimeError("Refusing a checkout with unrelated changes:\n" + status)

    def lean(self, filename: str, **kwargs) -> str:
        return self.run(["lake", "env", "lean", "-j1", "-M4096", "-DwarningAsError=true",
                         f"--root={self.scratch}", str(self.scratch / filename)], **kwargs)

    def prepare(self) -> None:
        self.clean()
        if (self.checkout / "lean-toolchain").read_text().strip() != self.package.TOOLCHAIN:
            raise RuntimeError("Toolchain mismatch")
        for name, text in self.package.render(self.checkout).items():
            artifact = self.package.OUTPUT / name
            if not artifact.exists() or artifact.read_text() != text:
                raise RuntimeError(f"Packaging artifact is stale: {name}")
            if name.endswith(".lean"):
                (self.scratch / name).write_text(text)
        self.run(["lake", "build", "lint-style"])
        self.source_path = self.run(["lake", "env", "printenv", "LEAN_SRC_PATH"]).strip()

    def style(self, candidates: list[dict]) -> None:
        # lint-style reads the direct imports of its argument. This temporary
        # umbrella makes the selected candidate files the files actually linted.
        style_module = f"Mathlib.{self.package.PACKAGE.capitalize()}CandidateStyle"
        style_root = self.scratch / path_for(style_module)
        style_root.parent.mkdir(exist_ok=True)
        style_root.write_text("module\n\n" +
                              "\n".join("public import " + c["module"] for c in candidates) + "\n")
        source_path = str(self.scratch) + os.pathsep + self.source_path
        self.run(["lake", "env", "env", f"LEAN_SRC_PATH={source_path}",
                  str(self.checkout / ".lake/build/bin/lint-style"), style_module])

    def check(self, candidates: list[dict], label: str, *, controls: bool = False) -> dict:
        self.clean()
        existing = [c["module"] for c in self.package.CANDIDATES if not c["new_module"]]
        self.run(["lake", "build", *existing])
        self.lean("Snapshot.lean")
        patches = [self.package.OUTPUT / c["patch"] for c in candidates]
        applied: list[Path] = []
        modules = [c["module"] for c in candidates]
        check_name = "Check.lean" if len(candidates) > 1 else "Check" + label.capitalize() + ".lean"
        try:
            for patch in patches:
                self.run(["git", "apply", "--check", str(patch)])
                self.run(["git", "apply", str(patch)])
                applied.append(patch)
            self.run(["git", "diff", "--check"])
            self.run(["lake", "build", *modules])
            output = self.lean(check_name)
            self.style(candidates)
            count = re.search(r"Axiom-audited (\d+) candidate declarations", output)
            linters = re.search(r"Ran (\d+) environment linters", output)
            if count is None or linters is None:
                raise RuntimeError("Candidate checker did not report completed audit and lint results")
            controls_passed: list[str] = []
            if controls:
                # Appending an unused private axiom to an existing large mathlib
                # module tests the baseline-delta audit, independently of names.
                first = self.package.CANDIDATES[0]
                first_checker = "Check" + first["id"].capitalize() + ".lean"
                target = self.checkout / path_for(first["module"])
                original = target.read_text()
                try:
                    target.write_text(original +
                                      "\nprivate axiom candidateAuditNegativeControl : False\n")
                    self.run(["lake", "build", self.package.CANDIDATES[0]["module"]])
                    self.lean(first_checker, expected_failure="unapproved axiom")
                    controls_passed.append("unused private axiom in an existing module rejected")
                finally:
                    target.write_text(original)
                # `import all` is necessary to inspect otherwise hidden private declarations.
                incomplete = (self.scratch / first_checker).read_text().replace(
                    "import all " + first["module"], "import " + first["module"], 1)
                (self.scratch / "CheckMissingPrivate.lean").write_text(incomplete)
                self.run(["lake", "build", *modules])
                self.lean("CheckMissingPrivate.lean", expected_failure="needs explicit `import all`")
                controls_passed.append("missing private-declaration import rejected")
                self.lean(check_name)
            print(f"{label}: build, style, {count[1]} declarations and {linters[1]} linters passed.",
                  flush=True)
            return {"case": label, "patches": [p.name for p in patches], "modules": modules,
                    "declarations_audited": int(count[1]), "environment_linters": int(linters[1]),
                    "build": "passed", "style": "passed", "controls": controls_passed}
        finally:
            for patch in reversed(applied):
                self.run(["git", "apply", "--reverse", "--check", str(patch)])
                self.run(["git", "apply", "--reverse", str(patch)])
            self.clean()


def run_package(package=wallis) -> None:
    parser = argparse.ArgumentParser(description=(
        f"Validate each {package.PACKAGE} patch alone and together in a clean pinned mathlib checkout. "
        "Run sequentially; restore the checkout and record the exact patch hashes."))
    parser.add_argument("--mathlib", required=True, type=Path)
    parser.add_argument("--report", type=Path, default=package.OUTPUT / "validation.json")
    args = parser.parse_args()
    checkout = args.mathlib.resolve()
    if checkout == (package.ROOT / ".lake/packages/mathlib").resolve():
        raise RuntimeError("Use a separate mathlib checkout, not the project's dependency checkout")
    check = Validation(checkout, package)
    check.prepare()
    results = [check.check([candidate], candidate["id"]) for candidate in package.CANDIDATES]
    results.append(check.check(package.CANDIDATES, "combined", controls=True))
    report = {
        "baseline": package.BASELINE, "toolchain": package.TOOLCHAIN,
        "checked_at_utc": datetime.now(timezone.utc).isoformat(timespec="seconds"),
        "scope": "Changed modules and dependencies; not a full mathlib build or CI run",
        "cases": results,
        "patch_sha256": {
            c["patch"]: hashlib.sha256((package.OUTPUT / c["patch"]).read_bytes()).hexdigest()
            for c in package.CANDIDATES
        },
        "checkout_restored_to_clean_baseline": True,
    }
    args.report.parent.mkdir(parents=True, exist_ok=True)
    args.report.write_text(json.dumps(report, indent=2) + "\n")
    print("All independent and combined checks passed; checkout restored to its clean baseline.")


if __name__ == "__main__":
    try:
        run_package()
    except (RuntimeError, subprocess.CalledProcessError) as error:
        sys.exit(str(error))
