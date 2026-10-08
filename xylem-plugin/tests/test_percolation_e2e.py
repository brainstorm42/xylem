#!/usr/bin/env python3
"""Regression and end-to-end checks for the pinned percolation Xylem dataset."""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import sqlite3
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / "examples" / "percolation-e2e" / "data"
CONFIG = ROOT / "examples" / "percolation-e2e" / "xylem-e2e-config.json"
DB = DATA / "xylem.db"
ARCHIVE = DATA / "xylem.db.gz"

sys.path.insert(0, str(ROOT / "capture" / "percolation"))
from run_batched_trace import validate_merged_trace  # noqa: E402


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def cli(*args: str) -> subprocess.CompletedProcess[str]:
    env = os.environ.copy()
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    return subprocess.run(
        [sys.executable, str(ROOT / "canonical" / "run.py"), "--config", str(CONFIG), *args],
        cwd=ROOT,
        env=env,
        check=True,
        capture_output=True,
        text=True,
    )


def main() -> int:
    receipt = json.loads((DATA / "reproducibility-receipt.json").read_text(encoding="utf-8"))
    capture = json.loads((DATA / "capture-manifest.json").read_text(encoding="utf-8"))
    imports = json.loads((DATA / "import-graph-manifest.json").read_text(encoding="utf-8"))
    source = json.loads((DATA / "source-manifest.json").read_text(encoding="utf-8"))
    components = json.loads((DATA / "components-generated.json").read_text(encoding="utf-8"))
    capture_audit = json.loads((DATA / "capture-audit.json").read_text(encoding="utf-8"))
    component_audit = json.loads((DATA / "component-audit.json").read_text(encoding="utf-8"))
    subargument_validation = json.loads((DATA / "subargument-validation.json").read_text(encoding="utf-8"))
    selected_declarations = components["proof_trace_summary"]["selected"]
    proof_trace = validate_merged_trace(
        DATA / "proof-trace.json.gz",
        items=[{"declaration": name} for name in selected_declarations],
    )

    assert receipt["schema_version"] == 2
    assert receipt["source"]["revision"] == "795efb86f191735c5481675763537cfb4ff37e55"
    verified_commit = receipt["xylem_git"]["verified_commit"]
    verified_tree = subprocess.run(
        ["git", "rev-parse", f"{verified_commit}^{{tree}}"],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()
    assert verified_tree == receipt["xylem_git"]["verified_tree"]
    assert receipt["xylem_git"]["working_tree_clean_at_verification"] is True
    assert receipt["components"]["schema_version"] == 2
    assert receipt["proof_trace"]["record_count"] == proof_trace["record_count"]
    expected_trace_statuses = sorted({
        item["status"]
        for item in components["subargument_decomposition"]["trace_coverage"]
    })
    assert receipt["proof_trace"]["statuses"] == expected_trace_statuses
    assert receipt["audits"]["capture"]["status"] == "PASS"
    assert receipt["audits"]["components"]["role_interface_status"] == "PASS"
    assert receipt["audits"]["components"]["proof_decomposition_status"] == "PASS"
    assert receipt["audits"]["components"]["subargument_status"] == "PASS"
    assert receipt["audits"]["components"]["structural_validation_status"] == "PASS"
    assert receipt["proof_trace"]["artifact"]["sha256"] == sha256(DATA / "proof-trace.json.gz")
    assert receipt["audits"]["capture"]["artifact"]["sha256"] == sha256(DATA / "capture-audit.json")
    assert receipt["audits"]["components"]["artifact"]["sha256"] == sha256(DATA / "component-audit.json")
    assert receipt["audits"]["components"]["structural_validation_artifact"]["sha256"] == sha256(DATA / "subargument-validation.json")

    assert source["file_count"] == 265
    assert source["lean_file_count"] == 251
    assert imports["source_files_scanned"] == 250
    assert imports["source_modules"] == 250
    assert imports["parse_errors"] == []
    assert capture["capture_projection"]["surfaces"] == ["solution", "challenge"]
    assert capture["capture_projection"]["premises_complete"] is True
    assert capture["capture_projection"]["proof_terms_included"] is False
    assert capture["capture_surfaces"]["solution"]["summary"]["declarations"] == 11773
    assert capture["capture_surfaces"]["challenge"]["summary"]["declarations"] == 11772
    assert capture["summary"]["declarations"] == 23545
    assert capture["summary"]["axiom_occurrences"]["sorryAx"] == 2
    assert capture["capture_projection"]["tree_diagnostics_included"] is True
    assert capture["capture_projection"]["tree_diagnostics_complete"] is True
    assert capture["summary"]["null_conclusion_trees"] == 190
    assert capture["summary"]["null_binder_trees"] == 200
    assert capture_audit["status"] == "PASS"
    assert capture_audit["capture_coverage"]["empty_dependency_declarations"] == 32
    assert capture_audit["capture_coverage"]["empty_dependency_status_counts"] == {
        "valid_zero_dependency": 32
    }
    assert capture_audit["capture_coverage"]["all_null_trees_diagnosed"] is True
    assert component_audit["role_interface_audit"]["status"] == "PASS"
    assert component_audit["proof_decomposition"]["status"] == "PASS"
    assert component_audit["proof_decomposition"]["component_membership_accounted"] is True
    assert component_audit["subargument_decomposition"]["status"] == "PASS"
    assert component_audit["subargument_decomposition"]["selected_trace_count"] == proof_trace["record_count"]
    assert component_audit["subargument_decomposition"]["catalog_component_count"] == 8063
    assert component_audit["subargument_decomposition"]["target_component_count"] == components["subargument_decomposition"]["target_component_count"]
    assert component_audit["subargument_decomposition"]["selected_traces_accounted"] is True
    assert component_audit["subargument_decomposition"]["all_target_application_records_structurally_valid"] is True
    assert component_audit["subargument_decomposition"]["all_structural_traces_captured"] is True
    assert component_audit["subargument_decomposition"]["explicit_no_value_count"] == 180
    assert component_audit["subargument_decomposition"]["unexpected_no_value_records"] == []
    assert component_audit["subargument_decomposition"]["unavailable_trace_records"] == []
    assert subargument_validation["status"] == "PASS"
    assert subargument_validation["selected_trace_count"] == proof_trace["record_count"]
    assert subargument_validation["trace_backed_component_count"] == proof_trace["record_count"]
    assert subargument_validation["trace_application_target_component_count"] == 0
    assert subargument_validation["trace_application_record_count"] == proof_trace["application_record_count"] == 3314889
    assert subargument_validation["trace_reference_record_count"] == proof_trace["reference_record_count"] == 28919499
    assert subargument_validation["exact_context_application_count"] == 3314889
    assert subargument_validation["structural_only_application_count"] == 0
    assert subargument_validation["proof_application_count"] == 106395
    assert subargument_validation["data_application_count"] == 3208494
    assert subargument_validation["omitted_structural_application_count"] == 299496929
    assert subargument_validation["omitted_external_reference_count"] == 622384457
    assert subargument_validation["compiler_relation_count"] == components["subargument_decomposition"]["compiler_relation_count"]
    assert subargument_validation["trace_only_relation_count"] == 0
    assert subargument_validation["negative_tests"]["swapped_arguments"]["status"] == "PASS"
    assert subargument_validation["negative_tests"]["type_only_false_positive"]["status"] == "PASS"
    assert components["schema_version"] == 2
    assert components["interface_audit"]["status"] == "PASS"
    assert components["proof_decomposition"]["reachable_module_components"] == 228
    assert components["proof_decomposition"]["cross_region_relations"] == 1702
    assert components["subargument_decomposition"]["status"] == "PASS"
    assert components["subargument_decomposition"]["catalog_component_count"] == 8063
    assert len(components["components"]) == 8303
    assert len(components["relations"]) == 16358
    trace_components = [
        component for component in components["components"]
        if component.get("kind") == "trace_backed_subargument"
    ]
    assert len(trace_components) == proof_trace["record_count"]
    assert all(
        component["formal_status"] == "trace_backed_structural_application_records"
        and component["proof_trace_evidence"]["trace_status"] in {"captured", "no_value"}
        for component in trace_components
    )
    trace_target_components = [
        component for component in components["components"]
        if component.get("kind") == "trace_application_target"
    ]
    assert len(trace_target_components) == components["subargument_decomposition"]["target_component_count"]
    assert proof_trace["schema_version"] == 1
    assert proof_trace["toolchain"] == "leanprover/lean4:v4.32.0"
    assert proof_trace["generated_from"] == "Solution"
    assert proof_trace["record_count"] == 8063

    with sqlite3.connect(DB) as conn:
        conn.row_factory = sqlite3.Row
        assert conn.execute("PRAGMA integrity_check").fetchone()[0] == "ok"
        node_counts = {r["kind"]: r["count"] for r in conn.execute(
            "SELECT kind, COUNT(*) AS count FROM node GROUP BY kind")}
        edge_counts = {r["type"]: r["count"] for r in conn.execute(
            "SELECT type, COUNT(*) AS count FROM edge GROUP BY type")}
        assert node_counts["declaration"] == 27592
        assert node_counts["component"] == len(components["components"])
        assert edge_counts["USES_IN_TYPE"] == 400846
        assert edge_counts["USES_IN_PROOF"] == 1159853
        assert edge_counts["IMPORTS"] == 877
        assert edge_counts["COMPONENT_RELATION"] == len(components["relations"])
        assert conn.execute(
            "SELECT COUNT(*) FROM node WHERE id='decl:solution::BondPercolation.percolation_continuity'"
        ).fetchone()[0] == 1
        assert conn.execute(
            "SELECT COUNT(*) FROM node WHERE id='decl:challenge::BondPercolation.percolation_continuity'"
        ).fetchone()[0] == 1
        solution_axioms = json.loads(conn.execute(
            "SELECT props FROM node WHERE id='decl:solution::BondPercolation.percolation_continuity'"
        ).fetchone()[0])["axioms"]
        assert "sorryAx" not in solution_axioms
        warning = conn.execute("SELECT payload FROM input_state WHERE id=1").fetchone()[0]
        assert json.loads(warning)["issues"] == []
        for relation in components["relations"]:
            if relation["evidence_kind"] != "compiler":
                continue
            evidence = relation["evidence"]
            assert conn.execute(
                "SELECT 1 FROM edge WHERE src=? AND dst=? AND type=?",
                (f"decl:{evidence['source_declaration']}",
                 f"decl:{evidence['target_declaration']}", evidence["edge_type"]),
            ).fetchone() is not None

    status = json.loads(cli("query", "status", "--json").stdout)
    assert status["fresh"] is True
    assert status["nodes"]["component"] == len(components["components"])
    overview = json.loads(cli("query", "overview", "--surface", "solution", "--json").stdout)
    assert overview["total_components"] == sum(
        component.get("surface") == "solution" for component in components["components"]
    )
    zoom = json.loads(cli("query", "components", "component:all-dimensions-endpoint", "--json").stdout)
    assert zoom["declarations"][0]["source"]["start_line"] == 160
    compiler_component = next(
        component for component in components["components"]
        if component.get("kind") == "compiler_source_module_region"
    )
    compiler_zoom = json.loads(cli(
        "query", "components", f"component:{compiler_component['id']}", "--json"
    ).stdout)
    assert compiler_zoom["component"]["id"] == f"component:{compiler_component['id']}"
    assert compiler_zoom["component"]["metadata"]["formal_status"] == (
        "compiler_derived_source_partition"
    )
    assert compiler_zoom["declarations"]
    trace_component = next(
        component for component in components["components"]
        if component.get("kind") == "trace_backed_subargument"
    )
    trace_zoom = json.loads(cli(
        "query", "components", f"component:{trace_component['id']}", "--json"
    ).stdout)
    assert trace_zoom["component"]["id"] == f"component:{trace_component['id']}"
    assert trace_zoom["component"]["metadata"]["formal_status"] == (
        "trace_backed_structural_application_records"
    )
    trace_evidence = trace_zoom["component"]["metadata"]["proof_trace_evidence"]
    assert trace_evidence["proof_application_sample_count"] >= 0
    assert trace_evidence["data_application_sample_count"] >= 0
    path = json.loads(cli(
        "query", "path", "solution::BondPercolation.percolation_continuity",
        "solution::Percolation.Literature.KozmaNitzan2024_thm6_holds", "--json"
    ).stdout)
    assert path[-1] == "decl:solution::Percolation.Literature.KozmaNitzan2024_thm6_holds"

    # The MCP surface is the same read-only navigation over this selected DB.
    os.environ["XYLEM_DB"] = str(DB)
    sys.path.insert(0, str(ROOT / "canonical" / "xylem"))
    from xylem import server  # noqa: E402
    mcp_overview = server.xylem_query("overview", limit=100)
    assert mcp_overview["ok"] is True
    assert mcp_overview["data"]["total_components"] == len(components["components"])
    mcp_zoom = server.xylem_query("components", query_text="component:all-dimensions-endpoint")
    assert mcp_zoom["ok"] is True
    assert mcp_zoom["data"]["component"]["id"] == "component:all-dimensions-endpoint"
    mcp_compiler_zoom = server.xylem_query(
        "components", query_text=f"component:{compiler_component['id']}"
    )
    assert mcp_compiler_zoom["ok"] is True
    assert mcp_compiler_zoom["data"]["component"]["id"] == f"component:{compiler_component['id']}"

    # Verify the committed archive restores byte-identically to the generated DB.
    with tempfile.TemporaryDirectory(prefix="percolation-e2e-") as scratch:
        restored = Path(scratch) / "xylem.db"
        subprocess.run([
            sys.executable, str(ROOT / "examples" / "percolation-e2e" / "restore_index.py"),
            "--archive", str(ARCHIVE), "--output", str(restored), "--config", str(CONFIG),
        ], cwd=ROOT, check=True, capture_output=True, text=True)
        assert sha256(restored) == sha256(DB) == receipt["index"]["sqlite"]["sha256"]
        sys.path.insert(0, str(ROOT / "canonical" / "xylem"))
        from xylem import input_state  # noqa: E402
        with sqlite3.connect(restored) as restored_conn:
            restored_conn.row_factory = sqlite3.Row
            assert input_state.current_warning(restored_conn) is None
    assert sha256(ARCHIVE) == receipt["index"]["compressed_sqlite"]["sha256"]

    print("percolation_source_capture_coverage: PASS")
    print("percolation_surface_collision_isolated: PASS")
    print("percolation_sqlite_integrity_and_edges: PASS")
    print("percolation_cli_overview_zoom_path: PASS")
    print("percolation_mcp_overview_zoom: PASS")
    print("percolation_archive_restore_identity: PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
