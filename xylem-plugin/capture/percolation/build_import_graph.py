#!/usr/bin/env python3
"""Build a deterministic source-import DOT graph for the pinned Lean corpus.

Lean's elaborated premise capture is the authority for declaration type/proof
edges.  This graph is only the source-level module import layer, retained
separately so navigation can distinguish it from theorem use.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path


IMPORT_RE = re.compile(r"^\s*import\s+(.+?)\s*(?:--.*)?$")
MODULE_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*$")


def module_for(root: Path, path: Path) -> str:
    return path.relative_to(root).with_suffix("").as_posix().replace("/", ".")


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-root", type=Path, required=True)
    parser.add_argument("--dot", type=Path, required=True)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--source-revision", required=True)
    args = parser.parse_args()
    root = args.source_root.resolve()
    files = sorted(
        path for path in root.rglob("*.lean")
        if ".lake" not in path.parts and "scripts" not in path.parts
    )
    modules = {module_for(root, path) for path in files}
    edges: set[tuple[str, str]] = set()
    parse_errors = []
    import_records = []
    for path in files:
        module = module_for(root, path)
        for line_no, raw in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
            match = IMPORT_RE.match(raw)
            if not match:
                continue
            token_text = match.group(1).strip()
            # Lean's import command is one module per line in this corpus. Keep
            # the check explicit: an unexpected shape is reported, never guessed.
            if not MODULE_RE.fullmatch(token_text):
                parse_errors.append({"file": str(path.relative_to(root)), "line": line_no,
                                     "text": raw})
                continue
            dependency = token_text
            edges.add((dependency, module))
            import_records.append({
                "source": module, "dependency": dependency,
                "local": dependency in modules, "file": str(path.relative_to(root)),
                "line": line_no,
            })
    local_edges = sum(item["local"] for item in import_records)
    external_edges = len(import_records) - local_edges
    lines = ["digraph imports {", "  // DOT direction: dependency -> importing module."]
    for dependency, importing in sorted(edges):
        lines.append(f'  "{dependency}" -> "{importing}";')
    lines.append("}")
    dot_bytes = ("\n".join(lines) + "\n").encode("utf-8")
    args.dot.parent.mkdir(parents=True, exist_ok=True)
    args.manifest.parent.mkdir(parents=True, exist_ok=True)
    args.dot.write_bytes(dot_bytes)
    manifest = {
        "schema_version": 1,
        "source_revision": args.source_revision,
        "source_root": str(root),
        "source_files_scanned": len(files),
        "source_modules": len(modules),
        "import_statements": len(import_records),
        "unique_import_edges": len(edges),
        "local_import_edges": local_edges,
        "external_import_edges": external_edges,
        "parse_errors": parse_errors,
        "dot": {"path": str(args.dot), "bytes": len(dot_bytes),
                "sha256": hashlib.sha256(dot_bytes).hexdigest()},
        "unresolved_imports": sorted({item["dependency"] for item in import_records
                                       if not item["local"]}),
    }
    args.manifest.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(manifest, indent=2))
    return 0 if not parse_errors else 1


if __name__ == "__main__":
    raise SystemExit(main())
