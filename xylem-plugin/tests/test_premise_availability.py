#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Regression checks for unavailable versus empty dependency data."""

from __future__ import annotations

import json
from pathlib import Path
import sqlite3
import sys


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "canonical" / "xylem"))

from xylem import navigation  # noqa: E402
from xylem.build import _dependency_capture_status  # noqa: E402


def main() -> int:
    capture = json.loads((ROOT / "capture" / "declarations.json").read_text(encoding="utf-8"))
    declaration = capture["declarations"][0]
    actual = _dependency_capture_status(capture, declaration)
    assert actual["status"] == "unavailable"
    assert "not supplied" in actual["reason"]

    empty = {"capture_projection": {"premises_included": True}, "declarations": []}
    assert _dependency_capture_status(empty, {"premises": []})["status"] == "empty"

    partial = {"capture_projection": {"premises_included": True, "premises_complete": False}}
    assert _dependency_capture_status(partial, {"premises": [{"name": "A"}]})["status"] == "partial"

    captured = {"capture_projection": {"premises_included": True}}
    assert _dependency_capture_status(captured, {"premises": [{"name": "A"}]})["status"] == "captured"

    conn = sqlite3.connect(":memory:")
    conn.row_factory = sqlite3.Row
    conn.execute("CREATE TABLE node (kind TEXT, props TEXT)")
    for state in ("empty", "unavailable", "partial", "captured"):
        conn.execute(
            "INSERT INTO node(kind, props) VALUES ('declaration', ?)",
            (json.dumps({"dependency_capture": {"status": state}}),),
        )
    assert navigation.dependency_capture_summary(conn)["status"] == "partial"
    conn.close()

    print("premises_included_false_is_unavailable: PASS")
    print("empty_partial_captured_states: PASS")
    print("summary_preserves_mixed_dependency_states: PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
