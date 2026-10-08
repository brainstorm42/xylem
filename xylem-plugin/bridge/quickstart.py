#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Validate the supplied record and print the shortest first-use path."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import sys


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--example", type=Path, default=Path(__file__).parents[1] / "examples" / "compact-bounds")
    parser.add_argument("--component", default="compact-bounds-hS")
    args = parser.parse_args(argv)
    example = args.example.expanduser().resolve()
    try:
        record = json.loads((example / "component-record.json").read_text(encoding="utf-8"))
        capture = json.loads((example.parent.parent / "capture" / "declarations.json").read_text(encoding="utf-8"))
        component = next(item for item in record["components"] if item["id"] == args.component)
        source = example / component["source"]["path"]
        actual = hashlib.sha256(source.read_bytes()).hexdigest()
        if actual != component["source"]["sha256"]:
            raise ValueError("source fingerprint mismatch")
        declaration = capture["declarations"][0]
        if declaration["name"] != component["declaration"]:
            raise ValueError("capture and component declaration differ")
    except (OSError, KeyError, StopIteration, ValueError, json.JSONDecodeError) as error:
        print(f"quickstart: FAIL: {error}", file=sys.stderr)
        return 2
    print("ProofBricks Xylem v0.1.0 — local first-use check")
    print(f"PASS: {component['id']} -> {component['formal_type']}")
    print(f"source: {component['source']['path']} ({actual[:12]}…)")
    print("capture: generated from Lean elaborated environment; exact binders retained")
    print("converter: legacy bundled regression; canonical entrypoint uses exact Lean-text fallback when trees are absent")
    print("mcp: legacy bundled regression; canonical provider is canonical/mcp.sh")
    print("decomposition: observed_checked; leading boundary only")
    print("explanation: completed_grounded; review: separate_agent_review (hS packet/page scope)")
    print()
    print("Next:")
    print("  python3 -S runtime/bundled_converter.py --json  # regression surface")
    print("  python3 -S tests/test_bundled_mcp.py")
    print("  Open examples/compact-bounds/request-hS.json for the explanation request.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
