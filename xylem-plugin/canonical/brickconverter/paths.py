"""Page-resolution contract for ProofBricks proof tools."""

from __future__ import annotations
from pathlib import Path
import re
from typing import Any

MODULE_RE = re.compile(r"^Ctrllib\.([A-Za-z_][A-Za-z0-9_]*)$")
LEAN_FILE_RE = re.compile(r"^([A-Za-z_][A-Za-z0-9_]*)\.lean$")

def resolve_page_module(metadata: dict[str, Any]) -> str | None:
    lean_file = metadata.get("lean_file")
    if "lean_file" in metadata:
        if not isinstance(lean_file, str):
            return None
        match = LEAN_FILE_RE.fullmatch(lean_file)
        if match:
            return f"Ctrllib.{match.group(1)}"
        return None
    module = metadata.get("module")
    if isinstance(module, str) and MODULE_RE.fullmatch(module):
        return module
    return None

def resolve_page_lean_file(metadata: dict[str, Any]) -> str | None:
    module = resolve_page_module(metadata)
    return module.removeprefix("Ctrllib.") + ".lean" if module else None
