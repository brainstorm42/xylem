#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Regenerate the bundled declaration projection with an existing Lean build.

This command never invokes Lake, installs packages, or uses the network. It
compiles the supplied fixture into a disposable directory, runs a
user-supplied authorized capture source, and writes only the proof-free
projection used by the offline converter. No capture adapter is bundled.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile


TARGET = "OAI.Problem326.compact_positive_uniform_bounds"


def run(command: list[str], *, env: dict[str, str], timeout: int) -> subprocess.CompletedProcess[str]:
    result = subprocess.run(command, capture_output=True, text=True, env=env, timeout=timeout, check=False)
    if result.returncode:
        raise RuntimeError(f"Lean command failed with exit code {result.returncode}: {Path(command[0]).name}")
    return result


def projection(raw: dict) -> dict:
    declarations = raw.get("declarations")
    if not isinstance(declarations, list) or len(declarations) != 1:
        raise RuntimeError("capture did not emit exactly one declaration")
    declaration = declarations[0]
    if declaration.get("name") != TARGET:
        raise RuntimeError("capture target differs from CompactBounds target")
    projected = {
        "name": declaration["name"],
        "module": declaration["module"],
        "src_file": declaration["src_file"],
        "kind": declaration["kind"],
        "doc": declaration.get("doc"),
        "range": declaration.get("range"),
        "binders": [
            {"idx": item["idx"], "name": item.get("name"), "binderInfo": item.get("binderInfo"), "tree": None, "type": item["type"]}
            for item in declaration.get("binders", [])
        ],
        "conclusion": declaration["conclusion"],
        "conclusion_tree": None,
        "signature": declaration["signature"],
        "premises": [],
        "axioms": declaration.get("axioms", []),
    }
    return {
        "capture_projection": {
            "status": "generated_from_elaborated_environment",
            "binder_text_complete": True,
            "statement_text_complete": True,
            "proof_terms_included": False,
            "expression_trees_included": False,
            "premises_included": False,
            "tree_omission_reason": "The bundled first-use adapter preserves exact text and binder order without shipping proof-term or dependency-graph payloads.",
        },
        "declarations": [projected],
        "errors": [],
        "generated_from": raw.get("generated_from"),
        "schema_version": 1,
        "toolchain": raw.get("toolchain"),
    }


def manifest_library_roots(manifest: Path) -> list[Path]:
    if not manifest.is_file():
        raise RuntimeError(f"manifest must be a regular file: {manifest}")
    try:
        data = json.loads(manifest.read_text(encoding="utf-8"))
    except json.JSONDecodeError as error:
        raise RuntimeError(f"manifest is not valid JSON: {manifest}") from error
    packages_dir = data.get("packagesDir")
    packages = data.get("packages")
    if not isinstance(packages_dir, str) or not isinstance(packages, list):
        raise RuntimeError("manifest must contain string packagesDir and array packages")
    roots: list[Path] = []
    for package in packages:
        if not isinstance(package, dict) or not isinstance(package.get("name"), str):
            raise RuntimeError("manifest package entries must have string names")
        name = package["name"]
        library = (manifest.parent / packages_dir / name / ".lake" / "build" / "lib" / "lean").resolve()
        if not library.is_dir():
            raise RuntimeError(f"manifest package library root is missing for {name}: {library}")
        if library not in roots:
            roots.append(library)
    if not roots:
        raise RuntimeError(f"manifest contains no package library roots: {manifest}")
    return roots


def main(argv: list[str] | None = None) -> int:
    root = Path(__file__).resolve().parents[1]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", required=True, type=Path, help="existing Lean executable")
    parser.add_argument("--manifest", type=Path, help="Lake manifest; enumerate every package .lake/build/lib/lean root")
    parser.add_argument("--library-root", action="append", type=Path, help="additional compiled Lean library root; repeat for extra roots")
    parser.add_argument("--source", type=Path, default=root / "examples" / "compact-bounds" / "proof" / "CompactBoundsExplicitResolved.lean")
    parser.add_argument(
        "--capture-source",
        type=Path,
        required=True,
        help="user-supplied authorized Lean capture source; not included in this package",
    )
    parser.add_argument("--output", type=Path, default=root / "capture" / "declarations.json")
    parser.add_argument("--timeout", type=int, default=120)
    args = parser.parse_args(argv)
    try:
        requested_output = args.output.expanduser()
        if os.path.lexists(requested_output):
            raise RuntimeError(f"output already exists; refusing to overwrite: {requested_output}")
        output = requested_output.resolve()
        lean = args.lean.expanduser().resolve()
        source = args.source.expanduser().resolve()
        capture_source = args.capture_source.expanduser().resolve()
        if os.environ.get("LEAN_PATH"):
            raise RuntimeError("ambient LEAN_PATH is set; unset it for a bounded capture")
        if not lean.is_file() or not source.is_file() or not capture_source.is_file():
            raise RuntimeError("Lean, source, and capture source must be regular files")
        roots: list[Path] = []
        if args.manifest is not None:
            roots.extend(manifest_library_roots(args.manifest.expanduser().resolve()))
        roots.extend(path.expanduser().resolve() for path in (args.library_root or []))
        roots = list(dict.fromkeys(roots))
        if not roots:
            raise RuntimeError("supply --manifest or at least one --library-root")
        if any(not path.is_dir() for path in roots):
            raise RuntimeError("every --library-root must be an existing directory")
        if args.timeout < 1 or args.timeout > 120:
            raise RuntimeError("--timeout must be between 1 and 120 seconds")
        with tempfile.TemporaryDirectory(prefix="proofbricks-capture-") as scratch:
            scratch_path = Path(scratch)
            out_dir = scratch_path / "out"
            tmp_dir = scratch_path / "tmp"
            out_dir.mkdir()
            tmp_dir.mkdir()
            env = os.environ.copy()
            env["LEAN_PATH"] = os.pathsep.join([str(out_dir), *(str(path) for path in roots)])
            env["TMPDIR"] = str(tmp_dir)
            env["PATH"] = str(lean.parent) + os.pathsep + env.get("PATH", "")
            run([str(lean), "-j1", "-M4096", "-T5000000", "-o", str(out_dir / "CompactBoundsExplicitResolved.olean"), str(source)], env=env, timeout=args.timeout)
            result = run([str(lean), "--run", str(capture_source)], env=env, timeout=args.timeout)
        lines = [line for line in result.stdout.splitlines() if line.strip()]
        if len(lines) != 1:
            raise RuntimeError("capture emitted unexpected non-JSON output")
        payload = projection(json.loads(lines[0]))
        payload["source_sha256"] = hashlib.sha256(source.read_bytes()).hexdigest()
        output.parent.mkdir(parents=True, exist_ok=True)
        serialized = json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True) + "\n"
        try:
            with output.open("x", encoding="utf-8") as handle:
                handle.write(serialized)
        except FileExistsError as error:
            raise RuntimeError(f"output appeared during capture; refusing to overwrite: {output}") from error
        print(json.dumps({"status": "pass", "target": TARGET, "output": str(output), "toolchain": payload["toolchain"], "source_sha256": payload["source_sha256"], "library_root_count": len(roots)}, ensure_ascii=False))
        return 0
    except (OSError, RuntimeError, subprocess.TimeoutExpired, json.JSONDecodeError) as error:
        print(f"capture-declaration: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
