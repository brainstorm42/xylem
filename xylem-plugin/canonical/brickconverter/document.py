"""Manifest-selected Markdown mathematics translation; prose is never interpreted."""

from __future__ import annotations
from dataclasses import dataclass
import hashlib
from pathlib import Path
from typing import Any
import yaml
from .extractor import declaration_ir, load_capture, select_declaration
from .parser import ParseError, parse_math
from .profiles import load_profile
from .render import RenderError, render

MANIFEST_KEYS = {"schema_version", "document_id", "source", "source_profile", "target_profile", "blocks", "notes"}
BLOCK_KEYS = {"block_id", "source_lines", "latex", "declaration", "formal_status", "unconverted_reason", "scope", "bindings"}

class ManifestError(ValueError): pass

@dataclass(frozen=True)
class BlockResult:
    block_id: str
    conventional: str
    lean_facing: str
    status: str
    reason: str = ""
    semantic_comparison_performed: bool = False
    formal_coverage: str = "unconverted"

def load_manifest(path: str | Path) -> dict[str, Any]:
    path = Path(path); data = yaml.safe_load(path.read_bytes()) or {}
    unknown = sorted(set(data) - MANIFEST_KEYS)
    if unknown: raise ManifestError(f"{path}: unknown keys: {', '.join(unknown)}")
    if data.get("schema_version") != 1: raise ManifestError(f"{path}: unsupported schema_version")
    blocks = data.get("blocks")
    if not isinstance(blocks, list): raise ManifestError(f"{path}: blocks must be a list")
    seen = set()
    for entry in blocks:
        if not isinstance(entry, dict): raise ManifestError(f"{path}: every block must be a mapping")
        extra = sorted(set(entry) - BLOCK_KEYS)
        if extra: raise ManifestError(f"{path}: block has unknown keys: {', '.join(extra)}")
        block_id = entry.get("block_id")
        if not isinstance(block_id, str) or block_id in seen: raise ManifestError(f"{path}: duplicate or invalid block_id {block_id!r}")
        seen.add(block_id)
    return data

def translate_manifest(manifest_path: str | Path, extractor_path: str | Path, source_profile_path: str | Path, target_profile_path: str | Path, *, strict: bool = True) -> tuple[str, list[BlockResult]]:
    manifest = load_manifest(manifest_path); capture = load_capture(extractor_path)
    source_profile, target_profile = load_profile(source_profile_path), load_profile(target_profile_path)
    rows, results = [], []
    for block in manifest["blocks"]:
        latex, decl_name = block.get("latex", ""), block.get("declaration")
        if block.get("formal_status") == "conventional-only":
            linked = "—"
            if decl_name:
                declaration = select_declaration(capture, decl_name)
                linked = f"exact declaration: {declaration['name']}"
            result = BlockResult(
                block["block_id"], latex, linked, "conventional-only",
                block.get("unconverted_reason", "No formal match declared."),
                formal_coverage="conventional-only",
            )
        elif decl_name:
            try:
                original = parse_math(latex, source_profile)
                declaration = select_declaration(capture, decl_name)
                formal = declaration_ir(declaration)
                lean = render(formal, target_profile, target="lean", strict=strict)
                result = BlockResult(
                    block["block_id"],
                    render(original, source_profile, target="latex", strict=strict),
                    lean,
                    "rendered",
                    "Exact declaration linked; semantic comparison not performed.",
                    formal_coverage="linked",
                )
            except (ParseError, RenderError, ValueError) as error:
                if strict: raise
                result = BlockResult(
                    block["block_id"], latex, "—", "unconverted", str(error),
                    formal_coverage="unconverted",
                )
        else:
            result = BlockResult(
                block["block_id"], latex, "—", "unconverted",
                block.get("unconverted_reason", "No declaration identity supplied."),
                formal_coverage="unconverted",
            )
        results.append(result)
        status = result.status + (f": {result.reason}" if result.reason else "")
        rows.append(f"| `{result.block_id}` | ${result.conventional}$ | `{result.lean_facing}` | {status} |")
    source = Path(manifest["source"])
    header = ["# BrickConverter comparison", "", f"> Source: `{source}`. The source proof is not rewritten.", "", "| Step | Conventional notation | Lean-facing notation | Formal status |", "| --- | --- | --- | --- |"]
    return "\n".join(header + rows) + "\n", results
