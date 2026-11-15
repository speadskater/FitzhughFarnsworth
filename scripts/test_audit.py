#!/usr/bin/env python3
"""Check audit coverage and reject deliberately invalid, isolated proof modules.

Run after ``lake build``. Probe sources and compiled artifacts live in a temporary
directory under .cache; the project proof sources and compiled modules are never
modified. Probe compilation deliberately allows the unfinished-proof warning so
that the axiom audit itself must detect the invalid proof.
"""

from __future__ import annotations

import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[1]
AUDIT = ROOT / "scripts" / "Audit.lean"
IMPORT = re.compile(
    r"^(?:public )?import(?P<all> all)? "
    r"(?P<module>FitzhughFarnsworth(?:\.[A-Za-z0-9_]+)*)$",
    re.MULTILINE,
)


def run(command: list[str], *, env: dict[str, str] | None = None) -> subprocess.CompletedProcess[str]:
    return subprocess.run(command, cwd=ROOT, env=env, text=True, capture_output=True, check=False)


def require_success(result: subprocess.CompletedProcess[str], context: str) -> str:
    output = result.stdout + result.stderr
    if result.returncode:
        raise RuntimeError(f"{context} failed:\n{output}")
    return output


def main() -> None:
    source = AUDIT.read_text(encoding="utf-8")
    modules = {"FitzhughFarnsworth"} | {
        ".".join(path.relative_to(ROOT).with_suffix("").parts)
        for path in (ROOT / "FitzhughFarnsworth").rglob("*.lean")
    }
    imported_all = {match["module"] for match in IMPORT.finditer(source) if match["all"]}
    missing = modules - imported_all
    if missing:
        raise RuntimeError("Audit needs explicit `import all` for: " + ", ".join(sorted(missing)))

    positive = require_success(run(["lake", "env", "lean", str(AUDIT)]), "Project axiom audit")
    if "Axiom audit passed" not in positive:
        raise RuntimeError("Project audit did not report a completed audit")
    print(positive.strip(), flush=True)

    # Use the selected toolchain with a probe-first search path. Lake prepends
    # package paths itself, so adding only an inherited LEAN_PATH is insufficient
    # for a temporary module sharing the project's package prefix.
    lean_prefix = require_success(
        run(["lake", "env", "lean", "--print-prefix"]), "Lean lookup"
    ).strip()
    lean = shutil.which("lean", path=str(Path(lean_prefix) / "bin"))
    if lean is None:
        raise RuntimeError(f"Lean executable not found under {lean_prefix}")
    lean_path = require_success(
        run(["lake", "env", sys.executable, "-c",
             "import os; print(os.environ.get('LEAN_PATH', ''))"]),
        "Lean path lookup",
    ).strip()

    probes = [
        (
            "public axiom outside the project namespace",
            "public axiom AuditOutsideNamespace.forbidden : False\n",
            "AuditOutsideNamespace.forbidden",
        ),
        (
            "unused private axiom outside the project namespace",
            "public theorem AuditOutsideNamespace.visible : True := True.intro\n"
            "private axiom AuditOutsideNamespace.unusedForbidden : False\n",
            "AuditOutsideNamespace.unusedForbidden",
        ),
        (
            "unused private unfinished proof outside the project namespace",
            "public theorem AuditOutsideNamespace.visible : True := True.intro\n"
            "private theorem AuditOutsideNamespace.unfinished : False := by sorry\n",
            "sorryAx",
        ),
    ]
    cache = ROOT / ".cache"
    cache.mkdir(exist_ok=True)
    for index, (description, declaration, expected_axiom) in enumerate(probes):
        with tempfile.TemporaryDirectory(prefix="audit-regression-", dir=cache) as temporary:
            directory = Path(temporary)
            probe = directory / "FitzhughFarnsworth" / "AuditProbe.lean"
            probe.parent.mkdir()
            probe.write_text("module\n\n" + declaration, encoding="utf-8")
            env = os.environ.copy()
            env["LEAN_PATH"] = str(directory) + os.pathsep + lean_path
            require_success(
                run(
                    [lean, f"--root={directory}", "-DwarningAsError=false", "-o",
                     str(probe.with_suffix(".olean")), str(probe)],
                    env=env,
                ),
                "Isolated probe compilation",
            )

            # Retain the audit command exactly, replacing only its project
            # imports with the isolated owned-name probe module.
            audit_copy = directory / "AuditCheck.lean"
            isolated = IMPORT.sub("", source)
            isolated = isolated.replace(
                "import Lean\n", "import all FitzhughFarnsworth.AuditProbe\nimport Lean\n", 1
            )
            audit_copy.write_text(isolated, encoding="utf-8")
            result = run([lean, f"--root={directory}", str(audit_copy)], env=env)
            output = result.stdout + result.stderr
            if (result.returncode == 0 or "unapproved axiom" not in output
                    or expected_axiom not in output):
                raise RuntimeError(f"Audit failed to reject {description}:\n{output}")
            print(f"Audit correctly rejected {description}.", flush=True)

            if index == 0:
                incomplete = isolated.replace(
                    "import all FitzhughFarnsworth.AuditProbe\n",
                    "import FitzhughFarnsworth.AuditProbe\n",
                    1,
                )
                audit_copy.write_text(incomplete, encoding="utf-8")
                result = run([lean, f"--root={directory}", str(audit_copy)], env=env)
                output = result.stdout + result.stderr
                if (result.returncode == 0
                        or "is missing an explicit `import all`" not in output):
                    raise RuntimeError(f"Audit failed to reject incomplete imports:\n{output}")
                print("Audit correctly rejected incomplete private-declaration coverage.", flush=True)


if __name__ == "__main__":
    main()
