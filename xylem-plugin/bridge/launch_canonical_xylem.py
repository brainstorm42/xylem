#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Check or launch the existing canonical Xylem wrapper without installing it."""

from __future__ import annotations

import argparse
import os
from pathlib import Path
import subprocess
import sys


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args, remainder = parser.parse_known_args(argv)
    value = os.environ.get("PROOFBRICKS_ROOT")
    if not value:
        print("PROOFBRICKS_ROOT is required", file=sys.stderr)
        return 2
    wrapper = Path(value).expanduser().resolve() / "20_tools" / "xylem.sh"
    if not wrapper.is_file() or not os.access(wrapper, os.X_OK):
        print(f"canonical Xylem wrapper is not executable: {wrapper}", file=sys.stderr)
        return 2
    if args.check:
        print("canonical Xylem wrapper: PASS")
        print("registration: none")
        return 0
    return subprocess.call([str(wrapper), "mcp", *remainder])


if __name__ == "__main__":
    raise SystemExit(main())
