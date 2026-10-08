#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Create an external Xylem config for a regenerated full Ctrllib capture.

The generated JSON intentionally contains the caller's explicit absolute
paths and should remain in the external E2E output directory. This script
never creates a database, installs packages, or fetches data.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path


PLUGIN_ROOT = Path(__file__).resolve().parents[2]
PACKAGE_ROOT = PLUGIN_ROOT.parent


def inside(path: Path, root: Path) -> bool:
    return path == root or root in path.parents


def file_path(value: str, label: str) -> Path:
    path = Path(value).expanduser().resolve()
    if not path.is_file():
        raise ValueError(f"{label} does not exist: {value}")
    return path


def dir_path(value: str, label: str) -> Path:
    path = Path(value).expanduser().resolve()
    if not path.is_dir():
        raise ValueError(f"{label} does not exist: {value}")
    return path


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--capture", required=True, help="external full declarations.json")
    parser.add_argument("--dot", required=True, help="external module_graph.dot")
    parser.add_argument("--ctrllib", required=True, help="moved candidate ctrllib source directory")
    parser.add_argument("--db", required=True, help="external SQLite output path")
    parser.add_argument("--output", required=True, help="new external config path")
    parser.add_argument("--vault", default=str(PLUGIN_ROOT / "examples/ctrllib-e2e/vault"))
    parser.add_argument("--bricks", default="")
    parser.add_argument("--bib", default="")
    args = parser.parse_args()
    try:
        capture = file_path(args.capture, "capture")
        dot = file_path(args.dot, "module graph")
        ctrllib = dir_path(args.ctrllib, "Ctrllib source")
        vault = dir_path(args.vault, "vault")
        profile = file_path(str(PLUGIN_ROOT / "canonical/brickconverter/profiles/engineering.yaml"), "converter profile")
        bricks = file_path(args.bricks, "Brick input") if args.bricks else None
        bib = file_path(args.bib, "bibliography input") if args.bib else None
        output = Path(args.output).expanduser().resolve()
        if output.exists():
            raise ValueError(f"output config already exists: {output}")
        if inside(output, PACKAGE_ROOT):
            raise ValueError("generated full config must be outside the combined package root")
        database = Path(args.db).expanduser().resolve()
        if inside(database, PACKAGE_ROOT):
            raise ValueError("database target must be outside the combined package root")
        if database.exists():
            raise ValueError(f"database target must be new and absent: {database}")
        output.parent.mkdir(parents=True, exist_ok=True)
        config = {
            "relative_to": "config",
            "paths": {
                "data": str(dot.parent),
                "dot": str(dot),
                "extractor": str(capture),
                "vault": str(vault),
                "bricks": str(bricks) if bricks else "",
                "bib": str(bib) if bib else "",
                "ctrllib": str(ctrllib),
                "db": str(database),
                "converter_capture": str(capture),
                "converter_profile": str(profile),
            },
            "notes": {
                "source": "caller-regenerated full source-first Ctrllib capture",
                "dependency_data": "captured premise records are preserved; Xylem still reports external stubs as unexpanded",
                "no_install_or_fetch": True,
            },
        }
        output.write_text(json.dumps(config, indent=2) + "\n", encoding="utf-8")
        print(json.dumps({"config": str(output), "capture": str(capture), "database": str(database)}, indent=2))
        return 0
    except (OSError, ValueError) as error:
        parser.error(str(error))
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
