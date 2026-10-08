#!/usr/bin/env python3
"""Restore the versioned compressed percolation index into a queryable SQLite file."""

from __future__ import annotations

import argparse
import gzip
import json
import os
import sqlite3
import sys
import tempfile
from pathlib import Path


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--archive", type=Path, default=Path("data/xylem.db.gz"))
    parser.add_argument("--output", type=Path, default=Path("data/xylem.db"))
    parser.add_argument("--config", type=Path, default=None,
                        help="optional local config; rebinds the freshness snapshot for this checkout")
    args = parser.parse_args()
    if not args.archive.is_file():
        raise SystemExit(f"missing archive: {args.archive}")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    fd, temporary = tempfile.mkstemp(prefix=".xylem-restore-", suffix=".db", dir=args.output.parent)
    os.close(fd)
    try:
        with gzip.open(args.archive, "rb") as source, open(temporary, "wb") as target:
            while block := source.read(1024 * 1024):
                target.write(block)
        os.replace(temporary, args.output)
    finally:
        if Path(temporary).exists():
            Path(temporary).unlink()
    if args.config:
        raw = json.loads(args.config.read_text(encoding="utf-8"))
        base = args.config.parent if raw.get("relative_to") == "config" else Path(__file__).resolve().parents[2]
        paths = raw.get("paths", {})
        spec = {}
        for key, config_key in (("dot", "dot"), ("extractor", "extractor"),
                                ("vault", "vault"), ("bibliography", "bib"),
                                ("bricks", "bricks"), ("ctrllib", "ctrllib"),
                                ("source_root", "source_root"), ("components", "components")):
            value = paths.get(config_key, "")
            if value:
                candidate = Path(value).expanduser()
                spec[key] = str((candidate if candidate.is_absolute() else base / candidate).resolve())
            else:
                spec[key] = ""
        sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "canonical" / "xylem"))
        from xylem import input_state  # type: ignore[import-not-found]
        with sqlite3.connect(args.output) as conn:
            payload = json.loads(conn.execute(
                "SELECT payload FROM input_state WHERE id=1").fetchone()[0])
            payload["spec"] = spec
            payload["files"] = input_state.snapshot(spec)
            conn.execute("UPDATE input_state SET payload=? WHERE id=1", (json.dumps(payload),))
            conn.commit()
        print(f"restored {args.output} and rebound freshness to {args.config}")
    else:
        print(f"restored {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
