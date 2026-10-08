#!/usr/bin/env python3
"""Record a content-addressed manifest for the bundled upstream snapshot."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-root", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--source-revision", required=True)
    parser.add_argument("--source-repository", required=True)
    args = parser.parse_args()
    root = args.source_root.resolve()
    files = sorted(
        path for path in root.rglob("*")
        if path.is_file() and ".lake" not in path.parts and ".git" not in path.parts
    )
    records = [{
        "path": str(path.relative_to(root)),
        "bytes": path.stat().st_size,
        "sha256": sha256(path),
    } for path in files]
    manifest = {
        "schema_version": 1,
        "source_repository": args.source_repository,
        "source_revision": args.source_revision,
        "source_root": str(root),
        "file_count": len(records),
        "lean_file_count": sum(path["path"].endswith(".lean") for path in records),
        "files": records,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k: manifest[k] for k in ("file_count", "lean_file_count", "source_revision")}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
