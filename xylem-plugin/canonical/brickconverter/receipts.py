"""Deterministic scoped check receipts; no semantic-acceptance inference."""

from __future__ import annotations
import hashlib
import json
from pathlib import Path
from typing import Any

def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()

def sha256_file(path: str | Path) -> str:
    return sha256_bytes(Path(path).read_bytes())

def build_receipt(*, operation: str, inputs: dict[str, str], outputs: dict[str, str], profile: dict[str, Any], declaration: dict[str, Any] | None, checks: dict[str, bool], warnings: list[str], errors: list[str], metadata: dict[str, Any] | None = None, check_scope: str = "existing_declaration_check", formal_check_performed: bool = False) -> dict[str, Any]:
    passed = not warnings and not errors and all(checks.values())
    body = {
        "schema_version": 2,
        "operation": operation,
        "inputs": dict(sorted(inputs.items())),
        "outputs": dict(sorted(outputs.items())),
        "profile": profile,
        "declaration": declaration,
        "checks": dict(sorted(checks.items())),
        "warnings": sorted(warnings),
        "errors": sorted(errors),
        "check_scope": check_scope,
        "check_status": "passed" if passed else "failed",
        "checks_passed": passed,
        "acceptance_status": "not_assessed",
        "formal_check_performed": formal_check_performed,
        "generated_output_formally_checked": False,
        "source_equivalence_checked": False,
        "metadata": metadata or {},
    }
    body["receipt_hash"] = sha256_bytes(json.dumps(body, ensure_ascii=False, sort_keys=True, separators=(",", ":")).encode())
    return body

def write_receipt(path: str | Path, receipt: dict[str, Any]) -> None:
    Path(path).write_text(json.dumps(receipt, ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
