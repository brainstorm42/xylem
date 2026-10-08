#!/usr/bin/env python3
"""Merge the two incompatible percolation Lean surfaces without losing identity.

``Solution.lean`` and ``Challenge.lean`` both define the same public
``BondPercolation.*`` names, so Lean cannot import them in one environment.
This tool keeps two complete elaborated captures and qualifies every local
declaration and local premise with ``solution::`` or ``challenge::``.  Shared
external constants remain shared stubs.  The result is intentionally a
capture artifact, not a proof transformation: rendered signatures and premise
names remain the source environment's facts, while the surface qualification is
only an index namespace.
"""

from __future__ import annotations

import argparse
import gzip
import hashlib
import json
from collections import Counter
from pathlib import Path
from typing import Any


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def load_capture(path: Path) -> tuple[dict[str, Any], bytes]:
    raw = path.read_bytes()
    data = json.loads(raw)
    if not isinstance(data, dict):
        raise ValueError(f"capture is not an object: {path}")
    if data.get("errors"):
        raise ValueError(f"capture reports errors: {path}: {data['errors'][:3]}")
    declarations = data.get("declarations")
    if not isinstance(declarations, list) or not declarations:
        raise ValueError(f"capture has no declarations: {path}")
    projection = data.get("capture_projection")
    if not isinstance(projection, dict):
        raise ValueError(f"capture has no capture_projection: {path}")
    if projection.get("premises_included") is not True:
        raise ValueError(f"capture does not include premises: {path}")
    if projection.get("premises_complete") is not True:
        raise ValueError(f"capture marks premises incomplete: {path}")
    return data, raw


def is_local_record(record: dict[str, Any]) -> bool:
    module = record.get("module")
    return isinstance(module, str) and (
        module == "Percolation"
        or module.startswith("Percolation.")
        or module in {"Solution", "Challenge"}
    )


def qualify(surface: str, name: str) -> str:
    return f"{surface}::{name}"


def transform(data: dict[str, Any], surface: str) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    source = data.get("declarations", [])
    local_names = {
        record["name"] for record in source
        if isinstance(record, dict) and is_local_record(record)
    }
    if len(local_names) != len(source):
        outside = sorted(
            record.get("name", "<unnamed>") for record in source
            if not isinstance(record, dict) or not is_local_record(record)
        )
        raise ValueError(f"{surface} capture contains non-local declarations: {outside[:5]}")

    output: list[dict[str, Any]] = []
    for original in source:
        record = dict(original)
        original_name = record["name"]
        record["name"] = qualify(surface, original_name)
        record["capture_surface"] = surface
        record["source_name"] = original_name
        premises = []
        for premise in record.get("premises") or []:
            item = dict(premise)
            if item.get("name") in local_names:
                item["name"] = qualify(surface, item["name"])
                item["capture_surface"] = surface
            premises.append(item)
        record["premises"] = premises
        output.append(record)

    projection = dict(data["capture_projection"])
    projection["capture_surface"] = surface
    projection["surface_namespace"] = qualify(surface, "<local-declaration>")[:-len("<local-declaration>")]
    return output, projection


def summary(records: list[dict[str, Any]]) -> dict[str, Any]:
    modules = Counter(record["module"] for record in records)
    kinds = Counter(record.get("kind") for record in records)
    premises = [premise for record in records for premise in record.get("premises", [])]
    conclusion_tree_errors = Counter(
        record.get("conclusion_tree_error")
        for record in records
        if record.get("conclusion_tree_error") is not None
    )
    binder_tree_errors = Counter(
        binder.get("tree_error")
        for record in records
        for binder in record.get("binders", [])
        if binder.get("tree_error") is not None
    )
    return {
        "declarations": len(records),
        "modules": len(modules),
        "module_counts": dict(sorted(modules.items())),
        "kinds": dict(sorted(kinds.items())),
        "premise_records": len(premises),
        "type_edge_records": sum(bool(p.get("in_type")) for p in premises),
        "proof_edge_records": sum(bool(p.get("in_proof")) for p in premises),
        "both_type_and_proof": sum(bool(p.get("in_type")) and bool(p.get("in_proof")) for p in premises),
        "external_premise_records": sum(bool(p.get("external")) for p in premises),
        "null_conclusion_trees": sum(record.get("conclusion_tree") is None for record in records),
        "null_binder_trees": sum(
            binder.get("tree") is None
            for record in records
            for binder in record.get("binders", [])
        ),
        "tree_diagnostics": {
            "conclusion_errors": dict(sorted(conclusion_tree_errors.items())),
            "binder_errors": dict(sorted(binder_tree_errors.items())),
            "diagnosed_null_conclusion_trees": sum(conclusion_tree_errors.values()),
            "diagnosed_null_binder_trees": sum(binder_tree_errors.values()),
        },
        "axiom_occurrences": dict(sorted(
            Counter(axiom for record in records for axiom in record.get("axioms", [])).items()
        )),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--solution", type=Path, required=True)
    parser.add_argument("--challenge", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--gzip-output", type=Path, required=True)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--source-revision", required=True)
    parser.add_argument("--source-repository", required=True)
    args = parser.parse_args()

    solution, solution_raw = load_capture(args.solution)
    challenge, challenge_raw = load_capture(args.challenge)
    solution_records, solution_projection = transform(solution, "solution")
    challenge_records, challenge_projection = transform(challenge, "challenge")
    records = solution_records + challenge_records
    names = [record["name"] for record in records]
    if len(names) != len(set(names)):
        raise ValueError("surface qualification did not produce unique declaration ids")

    merged = {
        "schema_version": 1,
        "generated_from": "two separately elaborated percolation surfaces",
        "source_repository": args.source_repository,
        "source_revision": args.source_revision,
        "toolchain": solution.get("toolchain"),
        "capture_projection": {
            "status": "generated_from_two_elaborated_environments",
            "binder_text_complete": all(
                p.get("binder_text_complete") is True
                for p in (solution_projection, challenge_projection)
            ),
            "statement_text_complete": all(
                p.get("statement_text_complete") is True
                for p in (solution_projection, challenge_projection)
            ),
            "expression_trees_included": True,
            "expression_trees_complete": False,
            "tree_diagnostics_included": all(
                p.get("tree_diagnostics_included") is True
                for p in (solution_projection, challenge_projection)
            ),
            "tree_diagnostics_complete": all(
                p.get("tree_diagnostics_complete") is True
                for p in (solution_projection, challenge_projection)
            ),
            "proof_terms_included": False,
            "premises_included": True,
            "premises_complete": True,
            "surfaces": ["solution", "challenge"],
            "surface_namespace": "<surface>::<original-Lean-name>",
            "tree_omission_reason": (
                "Structured expression trees are best-effort per declaration; null trees "
                "are retained as an explicit converter fallback. Proof terms are not serialized."
            ),
        },
        "capture_surfaces": {
            "solution": {
                "environment_imports": ["Percolation", "Solution"],
                "source_json_sha256": sha256_bytes(solution_raw),
                "source_json_bytes": len(solution_raw),
                "summary": summary(solution_records),
            },
            "challenge": {
                "environment_imports": ["Percolation", "Challenge"],
                "source_json_sha256": sha256_bytes(challenge_raw),
                "source_json_bytes": len(challenge_raw),
                "summary": summary(challenge_records),
            },
        },
        "surface_collision": {
            "status": "explicitly_separate",
            "reason": (
                "Solution.lean and Challenge.lean define colliding BondPercolation names; "
                "Lean cannot import both surfaces in one environment."
            ),
            "qualified_examples": [
                "solution::BondPercolation.percolation_continuity",
                "challenge::BondPercolation.percolation_continuity",
            ],
        },
        "declarations": records,
        "errors": [],
    }
    encoded = json.dumps(merged, ensure_ascii=False, separators=(",", ":")).encode("utf-8")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.gzip_output.parent.mkdir(parents=True, exist_ok=True)
    args.manifest.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_bytes(encoded)
    compressed = gzip.compress(encoded, compresslevel=9, mtime=0)
    args.gzip_output.write_bytes(compressed)
    manifest = {
        "schema_version": 1,
        "source_repository": args.source_repository,
        "source_revision": args.source_revision,
        "toolchain": merged["toolchain"],
        "merged_json": {
            "path": str(args.output),
            "bytes": len(encoded),
            "sha256": sha256_bytes(encoded),
        },
        "compressed_json": {
            "path": str(args.gzip_output),
            "bytes": len(compressed),
            "sha256": sha256_bytes(compressed),
            "compression": "gzip level 9, mtime=0",
        },
        "capture_projection": merged["capture_projection"],
        "capture_surfaces": merged["capture_surfaces"],
        "surface_collision": merged["surface_collision"],
        "summary": summary(records),
    }
    args.manifest.write_text(json.dumps(manifest, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps(manifest, indent=2, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
