#!/usr/bin/env python3
"""Build the review PDF with Tectonic and reject unresolved or overflowing output."""

from __future__ import annotations

import json
import os
from pathlib import Path
import re
import shutil
import subprocess


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
NAME = "wallis-moments"


def main() -> None:
    compiler = os.environ.get("TECTONIC") or shutil.which("tectonic")
    if compiler is None:
        local = ROOT / ".cache" / "tools" / "tectonic-0.17.0" / "tectonic"
        if local.is_file():
            compiler = str(local)
    if compiler is None:
        raise SystemExit(
            "Install Tectonic (tested with 0.17.0), or set TECTONIC to its executable. "
            "See papers/wallis-moments/README.md."
        )
    compiler = str(Path(compiler).resolve())
    metadata = json.loads((HERE / "verification.json").read_text(encoding="utf-8"))
    output = HERE / "build"
    output.mkdir(exist_ok=True)
    env = os.environ.copy()
    env["SOURCE_DATE_EPOCH"] = str(metadata["source_date_epoch"])
    subprocess.run(
        [
            compiler, "--bundle", metadata["tex_bundle_url"],
            "--untrusted", "--keep-logs", "--keep-intermediates",
            "--outdir", str(output), str(HERE / f"{NAME}.tex"),
        ],
        cwd=HERE, env=env, check=True,
    )
    log = (output / f"{NAME}.log").read_text(encoding="utf-8", errors="replace")
    bad = re.findall(
        r"^.*(?:Overfull \\[hv]box|Missing character:|"
        r"LaTeX Warning:.*undefined|There were undefined references|"
        r"There were multiply-defined labels).*$",
        log, re.MULTILINE,
    )
    if bad:
        raise SystemExit("PDF checks failed:\n" + "\n".join(bad))
    pdf = output / f"{NAME}.pdf"
    if not pdf.is_file() or pdf.stat().st_size == 0:
        raise SystemExit("Tectonic did not produce a nonempty PDF.")
    shutil.copyfile(pdf, HERE / pdf.name)
    print(f"Built {HERE / pdf.name}; no unresolved references or overflowing boxes.")


if __name__ == "__main__":
    main()
