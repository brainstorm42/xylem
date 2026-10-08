#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Check that the included explanation stays tied to the supplied evidence."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
EXAMPLE = ROOT / "examples" / "compact-bounds"


def read(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def main() -> int:
    record = read(EXAMPLE / "component-record.json")
    packet = read(EXAMPLE / "explanation-hS.json")
    capture = read(ROOT / "capture" / "declarations.json")
    component = next(item for item in record["components"] if item["id"] == "compact-bounds-hS")
    declaration = capture["declarations"][0]
    source = EXAMPLE / component["source"]["path"]
    assert hashlib.sha256(source.read_bytes()).hexdigest() == component["source"]["sha256"]
    assert packet["component"]["exact_type"] == component["formal_type"] == "IsCompact S"
    assert "IsCompact (⋃ i, (fun x : ι → ℝ => x i) '' K)" in packet["component"]["recorded_interface"]
    assert packet["component"]["assumption_minimization"] == "not performed"
    assert packet["component"]["declaration"] == declaration["name"]
    assert packet["parent_statement"]["signature"] == declaration["signature"]
    assert len(packet["parent_statement"]["binders"]) == len(declaration["binders"]) == 5
    assert packet["component"]["source"]["sha256"] == component["source"]["sha256"]
    source_lines = source.read_text(encoding="utf-8").splitlines()
    assert source_lines[33].startswith("  let S : Set ℝ")
    assert source_lines[34].startswith("  have hS : IsCompact S")
    assert source_lines[35].strip().startswith("isCompact_iUnion")
    assert packet["status"]["review"] == "separate_agent_review"
    assert packet["capture"]["premise_data_state"] == "unavailable"
    fresh = read(EXAMPLE / "evidence" / "review-corrected-explanations.json")
    assert fresh["status"] == "pass"
    assert fresh["formal_replay_performed"] is False
    assert packet["status"]["engineering"] == "not_assessed"
    print("grounded_packet: PASS")
    print("source_hash_and_span: PASS")
    print("capture_signature_and_binders: PASS")
    print("review_status_is_explicit: PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
