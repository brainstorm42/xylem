#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Check or launch the package-local example MCP server."""

from __future__ import annotations

import argparse
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[1]


def check() -> int:
    required = [
        ROOT / "mcp" / "bundled_server.py",
        ROOT / "capture" / "declarations.json",
        ROOT / "examples" / "compact-bounds" / "component-record.json",
        ROOT / "runtime" / "bundled_converter.py",
    ]
    missing = [str(path.relative_to(ROOT)) for path in required if not path.is_file()]
    if missing:
        print("bundled MCP check: missing " + ", ".join(missing), file=sys.stderr)
        return 2
    print("bundled MCP check: PASS")
    print("scope: compact-bounds supplied example")
    print("registration: none")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="validate local files without starting stdio")
    args = parser.parse_args(argv)
    if args.check:
        return check()
    from bundled_server import main as server_main
    return server_main()


if __name__ == "__main__":
    raise SystemExit(main())
