#!/usr/bin/env python3
"""Focused parser-boundary tests for the bounded proof-trace reader."""

from __future__ import annotations

import json
import sys
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "capture" / "percolation"))

from derive_proof_components_bounded import _iter_trace_summaries  # noqa: E402


def fixture_payload() -> str:
    return json.dumps({
        "schema_version": 1,
        "generated_from": "Solution",
        "selected_declarations": ["Fixture.root"],
        "capture_policy": {"expr_tree": "omitted_compact_full_cone"},
        "records": [{
            "declaration": "Fixture.root",
            "status": "captured",
            "kind": "theorem",
            "fuel": 1,
            "tree_status": "omitted_compact_full_cone",
            "application_records": [],
            "reference_records": [],
        }],
    }, separators=(",", ":"))


def read_records(path: Path) -> list[dict]:
    _header, records = _iter_trace_summaries(path, set())
    return list(records)


def expect_rejection(payload: str, label: str) -> None:
    with tempfile.TemporaryDirectory(prefix="xylem-trace-parser-") as directory:
        path = Path(directory) / f"{label}.json"
        path.write_text(payload, encoding="utf-8")
        try:
            read_records(path)
        except ValueError:
            return
        raise AssertionError(f"{label}: malformed trace was accepted")


def main() -> int:
    valid = fixture_payload()
    with tempfile.TemporaryDirectory(prefix="xylem-trace-parser-") as directory:
        path = Path(directory) / "valid.json"
        path.write_text(valid, encoding="utf-8")
        records = read_records(path)
        assert len(records) == 1
        assert records[0]["declaration"] == "Fixture.root"

    expect_rejection(valid[:-1], "missing_enclosing_close")
    expect_rejection(valid[:-2], "missing_records_close")
    expect_rejection(valid + "\n{}", "trailing_json_value")
    expect_rejection(valid + " trailing", "trailing_text")
    print("bounded_trace_parser_boundaries: PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
