#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Print a reviewed config for the existing canonical Xylem stdio server.

The command only prints JSON. It never edits host configuration and never
registers an MCP server.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--proofbricks-root", type=Path, required=True)
    parser.add_argument("--plugin-root", type=Path, required=True)
    args = parser.parse_args(argv)
    proofbricks = args.proofbricks_root.expanduser().resolve()
    plugin = args.plugin_root.expanduser().resolve()
    wrapper = proofbricks / "20_tools" / "xylem.sh"
    launcher = plugin / "bridge" / "launch_canonical_xylem.py"
    if not wrapper.is_file():
        parser.error(f"canonical Xylem wrapper not found: {wrapper}")
    if not launcher.is_file():
        parser.error(f"canonical launcher not found: {launcher}")
    print(json.dumps({"mcpServers": {"xylem": {
        "command": "python3",
        "cwd": str(plugin),
        "args": [str(launcher)],
        "env": {"PROOFBRICKS_ROOT": str(proofbricks)},
        "startup_timeout_sec": 30,
    }}}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
