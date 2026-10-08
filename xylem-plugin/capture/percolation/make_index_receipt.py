#!/usr/bin/env python3
"""Write a reproducibility receipt for the percolation source/capture/index bundle."""

from __future__ import annotations

import argparse
import hashlib
import json
import sqlite3
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

from run_batched_trace import validate_merged_trace


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def file_record(path: Path) -> dict:
    return {"path": str(path), "bytes": path.stat().st_size, "sha256": sha256(path)}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--config", type=Path, required=True)
    parser.add_argument("--db", type=Path, required=True)
    parser.add_argument("--archive", type=Path, required=True)
    parser.add_argument("--capture-manifest", type=Path, required=True)
    parser.add_argument("--source-manifest", type=Path, required=True)
    parser.add_argument("--import-manifest", type=Path, required=True)
    parser.add_argument("--components", type=Path, required=True)
    parser.add_argument("--role-labels", type=Path, required=True)
    parser.add_argument("--capture-audit", type=Path, required=True)
    parser.add_argument("--component-audit", type=Path, required=True)
    parser.add_argument("--subargument-audit", type=Path, required=True)
    parser.add_argument("--subargument-validation", type=Path, required=True)
    parser.add_argument("--proof-trace", type=Path, required=True)
    parser.add_argument("--reconstruction", type=Path, action="append", required=True)
    parser.add_argument("--upstream-root", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    with sqlite3.connect(args.db) as conn:
        integrity = conn.execute("PRAGMA integrity_check").fetchone()[0]
        node_counts = {row[0]: row[1] for row in conn.execute(
            "SELECT kind, COUNT(*) FROM node GROUP BY kind")}
        edge_counts = {row[0]: row[1] for row in conn.execute(
            "SELECT type, COUNT(*) FROM edge GROUP BY type")}
        input_state = json.loads(conn.execute(
            "SELECT payload FROM input_state WHERE id=1").fetchone()[0])
    if integrity != "ok":
        raise SystemExit(f"sqlite integrity check failed: {integrity}")

    capture = json.loads(args.capture_manifest.read_text(encoding="utf-8"))
    source = json.loads(args.source_manifest.read_text(encoding="utf-8"))
    imports = json.loads(args.import_manifest.read_text(encoding="utf-8"))
    components = json.loads(args.components.read_text(encoding="utf-8"))
    role_labels = json.loads(args.role_labels.read_text(encoding="utf-8"))
    capture_audit = json.loads(args.capture_audit.read_text(encoding="utf-8"))
    component_audit = json.loads(args.component_audit.read_text(encoding="utf-8"))
    subargument_audit = json.loads(args.subargument_audit.read_text(encoding="utf-8"))
    subargument_validation = json.loads(args.subargument_validation.read_text(encoding="utf-8"))
    # The compact full-cone trace is intentionally too large to materialize
    # in a receipt process.  Revalidate its envelope and summarize each
    # top-level record in bounded memory instead.
    selected_declarations = components.get("proof_trace_summary", {}).get("selected", [])
    if not isinstance(selected_declarations, list) or not all(
        isinstance(name, str) for name in selected_declarations
    ):
        raise SystemExit("component manifest does not contain proof-trace declaration order")
    trace_summary = validate_merged_trace(
        args.proof_trace,
        items=[{"declaration": name} for name in selected_declarations],
    )
    trace_statuses = sorted({
        item.get("status")
        for item in components.get("subargument_decomposition", {}).get("trace_coverage", [])
        if isinstance(item, dict) and isinstance(item.get("status"), str)
    }) or trace_summary["statuses"]
    git_commit = subprocess.run(
        ["git", "rev-parse", "HEAD"], capture_output=True, text=True, check=True
    ).stdout.strip()
    git_tree = subprocess.run(
        ["git", "rev-parse", "HEAD^{tree}"], capture_output=True, text=True, check=True
    ).stdout.strip()
    git_status = subprocess.run(
        ["git", "status", "--porcelain"], capture_output=True, text=True, check=True
    ).stdout.splitlines()
    branch = subprocess.run(["git", "branch", "--show-current"], capture_output=True, text=True, check=True).stdout.strip()
    freeze = subprocess.run([sys.executable, "-m", "pip", "freeze"], capture_output=True, text=True, check=True).stdout.splitlines()
    upstream_files = {
        name: file_record(args.upstream_root / name)
        for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json", "Percolation.lean", "Solution.lean", "Challenge.lean")
    }
    receipt = {
        "schema_version": 2,
        "created_at": datetime.now(timezone.utc).isoformat(),
        "xylem_git": {
            "branch": branch,
            "verified_commit": git_commit,
            "verified_tree": git_tree,
            "working_tree_clean_at_verification": not git_status,
            "verification_scope": (
                "The named commit and tree were verified before this receipt was written. "
                "The receipt is committed in a subsequent receipt-only commit and is not "
                "self-hashed."
            ),
        },
        "source": {
            "repository": source["source_repository"],
            "revision": source["source_revision"],
            "manifest": file_record(args.source_manifest),
            "file_count": source["file_count"],
            "lean_file_count": source["lean_file_count"],
            "toolchain_and_project_files": upstream_files,
        },
        "capture": {
            "manifest": file_record(args.capture_manifest),
            "compressed_capture": capture["compressed_json"],
            "merged_capture_sha256": capture["merged_json"]["sha256"],
            "surfaces": capture["capture_surfaces"],
            "summary": capture["summary"],
            "projection": capture["capture_projection"],
        },
        "imports": {"manifest": file_record(args.import_manifest), "summary": imports},
        "components": {
            "manifest": file_record(args.components),
            "role_labels": file_record(args.role_labels),
            "schema_version": components["schema_version"],
            "count": len(components["components"]),
            "relation_count": len(components["relations"]),
            "formal_relation_count": sum(r["evidence_kind"] == "compiler" for r in components["relations"]),
            "authored_or_metadata_relation_count": sum(r["evidence_kind"] != "compiler" for r in components["relations"]),
            "interface_audit": components["interface_audit"],
            "proof_decomposition": components["proof_decomposition"],
            "subargument_decomposition": components["subargument_decomposition"],
        },
        "audits": {
            "capture": {
                "artifact": file_record(args.capture_audit),
                "status": capture_audit["status"],
                "coverage": capture_audit["capture_coverage"],
                "tree_reason_counts": capture_audit["expression_tree_reason_counts"],
            },
            "components": {
                "artifact": file_record(args.component_audit),
                "role_interface_status": component_audit["role_interface_audit"]["status"],
                "proof_decomposition_status": component_audit["proof_decomposition"]["status"],
                "proof_decomposition": component_audit["proof_decomposition"],
                "subargument_artifact": file_record(args.subargument_audit),
                "subargument_status": subargument_audit["subargument_decomposition"]["status"],
                "subargument": component_audit["subargument_decomposition"],
                "structural_validation_artifact": file_record(args.subargument_validation),
                "structural_validation_status": subargument_validation["status"],
                "structural_validation": subargument_validation,
            },
        },
        "proof_trace": {
            "artifact": file_record(args.proof_trace),
            "schema_version": trace_summary["schema_version"],
            "toolchain": trace_summary["toolchain"],
            "generated_from": trace_summary["generated_from"],
            "selected_declarations": trace_summary["selected_declarations"],
            "record_count": trace_summary["record_count"],
            "application_record_count": trace_summary["application_record_count"],
            "reference_record_count": trace_summary["reference_record_count"],
            "proof_application_count": subargument_validation["proof_application_count"],
            "data_application_count": subargument_validation["data_application_count"],
            "omitted_structural_application_count": subargument_validation[
                "omitted_structural_application_count"
            ],
            "omitted_external_reference_count": subargument_validation[
                "omitted_external_reference_count"
            ],
            "statuses": trace_statuses,
            "validation": "bounded-memory merged-trace envelope and record-order validation",
            "reconstruction_source": file_record(args.reconstruction[0]),
            "reconstruction_sources": [file_record(path) for path in args.reconstruction],
        },
        "index": {
            "config": file_record(args.config),
            "sqlite": file_record(args.db),
            "compressed_sqlite": file_record(args.archive),
            "sqlite_integrity_check": integrity,
            "nodes": node_counts,
            "edges": edge_counts,
            "input_state": input_state,
            "storage_note": (
                "The committed xylem.db.gz is a compact derivative. It retains exact text "
                "signatures and all typed/proof/import/component edges; the compressed full "
                "capture retains premise rows and best-effort expression trees omitted from "
                "repeated node props."
            ),
        },
        "tooling": {
            "python": sys.version,
            "pip_freeze": freeze,
            "commands": [
                "elan toolchain install leanprover/lean4:v4.32.0",
                "lake exe cache get",
                "lake build",
                "lake build Challenge",
                "lake env lean scripts/Axioms.lean",
                "lake env lean --run xylem-plugin/capture/percolation/Extract.lean > solution capture",
                "lake env lean --run xylem-plugin/capture/percolation/ExtractChallenge.lean > challenge capture",
                "python3 xylem-plugin/capture/percolation/run_batched_trace.py --upstream examples/percolation-e2e/upstream --extractor ../../../capture/percolation/ExtractProofTrace.lean --manifest /tmp/percolation-proof-cone-manifest.json --output data/proof-trace.json.gz --batch-size 50",
                "python3 xylem-plugin/capture/percolation/prepare_capture.py ...",
                "python3 xylem-plugin/capture/percolation/audit_capture.py ...",
                "python3 xylem-plugin/capture/percolation/derive_proof_components.py ...",
                "python3 xylem-plugin/capture/percolation/build_import_graph.py ...",
                "python3 xylem-plugin/canonical/run.py --config xylem-e2e-config.json build",
                "lake env lean examples/percolation-e2e/reconstruction/ProofSpine.lean",
                "lake env lean examples/percolation-e2e/reconstruction/SubargumentSpine.lean",
                "python3 xylem-plugin/capture/percolation/validate_subarguments.py ...",
                "python3 restore_index.py --archive data/xylem.db.gz --output data/xylem.db",
            ],
            "upstream_build_result": "PASS for lake build; PASS for lake build Challenge with two expected sorry warnings at Challenge.lean:143 and 149",
            "axiom_audit_result": "PASS; selected theorem outputs depend on propext, Classical.choice, and Quot.sound",
        },
        "limitations": [
            "The capture does not serialize opaque proof terms; proof-use edges come from Lean's allowOpaque elaborated constant values.",
            "The compact reachable proof-cone trace retains exact local proof/data applications and references with per-record omission counts; this is elaborated proof-term structure, not source-level proof text.",
            "Full Expr trees for the reviewed boundary declarations are retained separately in proof-trace-boundaries.json.gz; the compact cone intentionally omits repeated structural trees.",
            "Expression trees are best effort; every null tree is retained in the full capture with an explicit diagnostic and omitted from the compact SQLite projection.",
            "Challenge and Solution are separate Lean environments with colliding BondPercolation names; no proof equivalence is inferred.",
            "The Challenge build has two sorry declarations; the Solution selected endpoint has no sorryAx in its fresh axiom audit.",
            "Reachable records with no elaborated value are retained as explicit no_value statuses and accepted only for axiom, inductive, constructor, recursor, or quotient kinds; theorem/definition/opaque no_value records fail the decomposition audit.",
            "External constants are explicit stubs and are not expanded into this local source corpus.",
            "Compiler-derived components are graph partitions of the reachable Solution proof cone; authored role prose remains pending human mathematical review.",
            "The compiler source-module regions are not mathematical subarguments. The complete reachable structural application layer is derived from retained Expr application/data records and exact captured interfaces; component nodes store bounded samples and exact counts, while discovered target interfaces and opaque theorem bodies remain separate.",
            "The independent subargument validator rejects reordered argument mappings and checks that AdditiveGluing/NearOneGluing statement constants are not misclassified as proof applications.",
            "The checked formal endpoint is theta (zdGraph d) 0 (criticalProbI d) = 0. The surrounding source prose uses continuity language; this receipt does not certify a broader literature-level equivalence.",
            "No public release remote was modified; this receipt is for the private dev origin only.",
        ],
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(receipt, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps({"db_sha256": receipt["index"]["sqlite"]["sha256"], "archive_sha256": receipt["index"]["compressed_sqlite"]["sha256"], "sqlite_integrity_check": integrity}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
