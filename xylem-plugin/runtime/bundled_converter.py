#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Small offline statement renderer for the bundled CompactBounds capture.

This is a dependency-free first-use adapter, not a replacement for the
canonical BrickConverter package. It preserves every captured binder and the
exact Lean text. The display mapping is intentionally conservative and is
reported as ``conventional-only``; it never claims formal or source
equivalence.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import sys


VERSION = "0.1.0"


def load_capture(path: Path) -> dict:
    data = json.loads(path.read_text(encoding="utf-8"))
    if data.get("schema_version") != 1 or not isinstance(data.get("declarations"), list):
        raise ValueError("capture must be schema_version 1 with declarations")
    return data


def select(capture: dict, name: str) -> dict:
    for declaration in capture["declarations"]:
        if declaration.get("name") == name:
            return declaration
    raise ValueError(f"declaration not found in bundled capture: {name}")


def display_math(text: str) -> str | None:
    """Render a deliberately small, text-anchored display surface.

    The capture projection omits expression trees, so this function does not
    parse Lean. It only applies exact-token substitutions to the selected
    CompactBounds strings. Unknown text returns ``None`` and stays verbatim.
    """

    if not isinstance(text, str) or not text.strip():
        return None
    if text == "Type uIota":
        return None
    result = text
    result = result.replace("IsCompact ", r"\operatorname{IsCompact}(")
    if result.startswith(r"\operatorname{IsCompact}("):
        result += ")"
    result = result.replace("Finite ι", r"\operatorname{Finite}(\iota)")
    result = result.replace("Set (ι → ℝ)", r"\operatorname{Set}(\iota \to \mathbb{R})")
    result = result.replace("ℝ", r"\mathbb{R}")
    result = result.replace("ι", r"\iota")
    result = result.replace("ε", r"\varepsilon")
    result = result.replace("⁻¹", r"^{-1}")
    result = result.replace("∀", r"\forall")
    result = result.replace("∃", r"\exists")
    result = result.replace("∈", r"\in")
    result = result.replace("∧", r"\land")
    result = result.replace("→", r"\to")
    result = result.replace("≤", r"\le")
    result = result.replace("≥", r"\ge")
    result = result.replace("≠", r"\ne")
    result = re.sub(r"\bx i\b", "x(i)", result)
    result = re.sub(r"\s+", " ", result).strip()
    return result


def fragment(text: str, *, role: str) -> dict:
    conventional = display_math(text)
    if conventional is None:
        return {
            "exact": text,
            "conventional": None,
            "coverage": "unconverted",
            "reason": "The bundled capture omits expression trees for portability; exact Lean text is retained.",
            "role": role,
        }
    return {
        "exact": text,
        "conventional": conventional,
        "coverage": "conventional-only",
        "reason": "A conservative token display was applied to an exact captured fragment; no semantic equivalence was checked.",
        "role": role,
    }


def statement_record(declaration: dict) -> dict:
    binders = declaration.get("binders")
    if not isinstance(binders, list) or not declaration.get("signature"):
        raise ValueError("capture is missing complete binders or signature")
    rendered_binders = []
    for index, binder in enumerate(binders):
        if binder.get("idx") != index:
            raise ValueError("capture binder indices are not contiguous")
        rendered_binders.append({
            "index": index,
            "name": binder.get("name"),
            "binder_info": binder.get("binderInfo"),
            "type": fragment(binder.get("type", ""), role="binder"),
        })
    conclusion = fragment(declaration.get("conclusion", ""), role="conclusion")
    coverage = {}
    for item in [*rendered_binders, conclusion]:
        status = item["type"]["coverage"] if "type" in item else item["coverage"]
        coverage[status] = coverage.get(status, 0) + 1
    return {
        "declaration": declaration["name"],
        "module": declaration.get("module"),
        "signature": declaration["signature"],
        "binders": rendered_binders,
        "conclusion": conclusion,
        "coverage": {
            "conventional-only": coverage.get("conventional-only", 0),
            "unconverted": coverage.get("unconverted", 0),
            "exact_text_fragments": len(rendered_binders) + 1,
        },
        "proof_translated": False,
        "formal_check_performed": False,
        "source_equivalence_checked": False,
        "acceptance_status": "not_assessed",
    }


def markdown(record: dict) -> str:
    rows = [
        f"# Captured statement — {record['declaration']}",
        "",
        "Bundled first-use rendering. Exact Lean text is retained for every fragment; this page is not a proof or equivalence certificate.",
        "",
        "## Arguments",
        "",
        "| Name | Binder | Display | Exact Lean |",
        "| --- | --- | --- | --- |",
    ]
    for binder in record["binders"]:
        name = binder["name"] or "(anonymous)"
        display = binder["type"]["conventional"] or "—"
        rows.append(f"| `{name}` | `{binder['binder_info']}` | `{display}` | `{binder['type']['exact']}` |")
    conclusion = record["conclusion"]
    rows += ["", "## Conclusion", "", "```text", conclusion["conventional"] or conclusion["exact"], "```", ""]
    rows += ["## Status", "", "- acceptance: `not_assessed`", "- formal check: `not_performed`", "- source equivalence: `not_checked`", "- proof translation: `not_performed`", ""]
    return "\n".join(rows)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--capture", type=Path, default=Path(__file__).parents[1] / "capture" / "declarations.json")
    parser.add_argument("--declaration", default="OAI.Problem326.compact_positive_uniform_bounds")
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args(argv)
    try:
        capture = load_capture(args.capture)
        record = statement_record(select(capture, args.declaration))
    except (OSError, ValueError, json.JSONDecodeError) as error:
        print(f"bundled-converter: {error}", file=sys.stderr)
        return 2
    if args.json:
        payload = {
            "operation": "render-statement",
            "adapter": "proofbricks-bundled-converter",
            "adapter_version": VERSION,
            "capture_toolchain": capture.get("toolchain"),
            "statements": [record],
            "acceptance_status": "not_assessed",
        }
        print(json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True))
    else:
        output = markdown(record) + "\n"
        if args.output:
            args.output.write_text(output, encoding="utf-8")
        else:
            print(output, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
