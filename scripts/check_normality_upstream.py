#!/usr/bin/env python3
"""Validate the normality candidates separately and together in an isolated mathlib checkout."""

import subprocess
import sys

import package_normality
from check_wallis_upstream import run_package


if __name__ == "__main__":
    try:
        run_package(package_normality)
    except (RuntimeError, subprocess.CalledProcessError) as error:
        sys.exit(str(error))
