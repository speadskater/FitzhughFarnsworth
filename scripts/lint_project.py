#!/usr/bin/env python3
"""Run declaration linters with explicit private-declaration imports.

The pinned Batteries executable currently loads no environment linters when
importing the project dynamically. Elaborating a Lean checker loads them
correctly. Reuse Audit.lean's import list so lint and axiom coverage agree,
and reject empty declaration or linter sets. Run after ``lake build``.
"""

from pathlib import Path
import re
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[1]
IMPORT_ALL = re.compile(r"^import all FitzhughFarnsworth(?:\.[A-Za-z0-9_]+)*$", re.MULTILINE)

CHECK = """
import Batteries.Tactic.Lint

open Lean Elab Command Batteries.Tactic.Lint in
run_cmd do
  let env := (← getEnv).setExporting false
  let decls := env.constants.toList.toArray.filterMap fun (name, _) =>
    if (env.getModuleIdxFor? name).any
        (fun i => (`FitzhughFarnsworth).isPrefixOf env.header.moduleNames[i]!) then
      some name else none
  if decls.isEmpty then throwError "Refusing an empty project lint"
  for imported in env.header.modules do
    if (`FitzhughFarnsworth).isPrefixOf imported.module && !imported.importAll then
      throwError "Project module {imported.module} needs explicit `import all`"
  let linters ← liftCoreM <| getChecks (slow := true) (runOnly := none) (runAlways := none)
  if linters.isEmpty then throwError "No environment linters were loaded"
  let results ← liftCoreM <| lintCore decls linters
  for (linter, failures) in results do
    for (name, message) in failures.toArray do
      logError m!"{linter.name}: {name}: {message}"
  logInfo m!"Checked {decls.size} project declarations with {linters.size} environment linters."
"""


def main() -> int:
    imports = IMPORT_ALL.findall((ROOT / "scripts" / "Audit.lean").read_text(encoding="utf-8"))
    if not imports:
        raise RuntimeError("No project imports found in Audit.lean")
    cache = ROOT / ".cache"
    cache.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="project-lint-", dir=cache) as temporary:
        checker = Path(temporary) / "Lint.lean"
        checker.write_text("module\n\n" + "\n".join(imports) + CHECK, encoding="utf-8")
        return subprocess.run(
            ["lake", "env", "lean", "-j1", "-M4096", str(checker)], cwd=ROOT, check=False
        ).returncode


if __name__ == "__main__":
    raise SystemExit(main())
