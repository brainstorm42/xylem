#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Offline MCP stdio server for the supplied CompactBounds example.

The tool name matches the canonical Xylem tool, but this server is explicitly
an example-scoped adapter. It does not open SQLite, scan the host checkout, or
pretend to provide canonical graph dependencies.
"""

from __future__ import annotations

import json
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from runtime.bundled_converter import load_capture, select, statement_record  # noqa: E402


VERSION = "0.1.0"
PROTOCOL_VERSION = "2024-11-05"
EXAMPLE = ROOT / "examples" / "compact-bounds"
CAPTURE = ROOT / "capture" / "declarations.json"
RECORD = EXAMPLE / "component-record.json"


def load_record() -> dict:
    data = json.loads(RECORD.read_text(encoding="utf-8"))
    if data.get("schema_version") not in {1, 2}:
        raise ValueError("component record schema_version must be 1 or 2")
    return data


def capture_payload() -> tuple[dict, dict, dict]:
    capture = load_capture(CAPTURE)
    declaration = select(capture, "OAI.Problem326.compact_positive_uniform_bounds")
    statement = statement_record(declaration)
    record = load_record()
    return record, capture, statement


def component_match(component: dict, query: str) -> bool:
    haystack = " ".join(str(component.get(key, "")) for key in ("id", "declaration", "boundary", "formal_type"))
    return query.casefold() in haystack.casefold()


def dependency_capture_state(capture: dict) -> dict:
    projection = capture.get("capture_projection") or {}
    if projection.get("premises_included") is False:
        return {
            "status": "unavailable",
            "counts": {"unavailable": len(capture.get("declarations", []))},
            "note": "dependency records were not supplied; an empty premises list is not evidence of no dependencies",
        }
    declarations = capture.get("declarations", [])
    counts = {"captured" if item.get("premises") else "empty": len(declarations)}
    status = next(iter(counts), "unavailable")
    return {
        "status": status,
        "counts": counts,
        "note": "dependency records were supplied by the declaration capture",
    }


def status_payload(record: dict, capture: dict) -> dict:
    return {
        "status": "bundled_example_ready",
        "package_version": VERSION,
        "scope": "compact-bounds supplied example",
        "graph_indexed": False,
        "canonical_xylem": "not_connected",
        "converter": "bundled_statement_renderer",
        "capture_toolchain": capture.get("toolchain"),
        "components": [item["id"] for item in record["components"]],
        "supported_operations": ["status", "search", "context"],
        "unsupported_operations": ["dependencies", "dependents", "path", "explain", "impact", "discover", "similar"],
        "freshness": "not_assessed",
        "declaration_dependency_data": dependency_capture_state(capture),
    }


def context_payload(record: dict, capture: dict, statement: dict, arguments: dict) -> dict:
    wanted = arguments.get("component_id") or arguments.get("declaration") or "compact-bounds-hS"
    component = next((item for item in record["components"] if item["id"] == wanted or item["declaration"] == wanted), None)
    if component is None:
        raise ValueError(f"component not found: {wanted}")
    return {
        "status": "bundled_context",
        "component": component,
        "exact_statement_capture": {
            "declaration": statement["declaration"],
            "module": statement["module"],
            "signature": statement["signature"],
            "binder_count": len(statement["binders"]),
            "binder_names": [item["name"] for item in statement["binders"]],
            "conclusion_exact": statement["conclusion"]["exact"],
            "dependency_capture": dependency_capture_state(capture),
        },
        "converter_summary": {
            "adapter": "proofbricks-bundled-converter",
            "acceptance_status": statement["acceptance_status"],
            "all_binders_retained": len(statement["binders"]) == 5,
            "formal_check_performed": statement["formal_check_performed"],
            "source_equivalence_checked": statement["source_equivalence_checked"],
            "coverage": statement["coverage"],
        },
        "decomposition": {
            "boundary": component["boundary"],
            "formal_type": component["formal_type"],
            "receipt_status": "observed_pass",
            "scope": "leading proposition boundary only",
        },
        "graph": {"status": "not_connected", "dependency_edges": None},
    }


def query(arguments: dict) -> dict:
    record, capture, statement = capture_payload()
    operation = arguments.get("operation", "status")
    if operation == "status":
        return status_payload(record, capture)
    if operation == "search":
        text = str(arguments.get("query", "")).strip()
        if not text:
            raise ValueError("search requires a non-empty query")
        matches = [item for item in record["components"] if component_match(item, text)]
        return {"status": "bundled_search", "query": text, "matches": matches, "graph": "not_connected"}
    if operation == "context":
        return context_payload(record, capture, statement, arguments)
    if operation in {"dependencies", "dependents", "path", "explain", "impact", "discover", "similar"}:
        return {
            "status": "not_connected",
            "operation": operation,
            "scope": "bundled example has no SQLite graph",
            "next_step": "configure the canonical Xylem MCP after reviewing the emitted host config",
        }
    raise ValueError(f"unsupported bundled operation: {operation}")


def send(message: dict) -> None:
    payload = json.dumps(message, ensure_ascii=False, separators=(",", ":")).encode("utf-8")
    header = f"Content-Length: {len(payload)}\r\n\r\n".encode("ascii")
    sys.stdout.buffer.write(header + payload)
    sys.stdout.buffer.flush()


def send_result(request_id, result: dict) -> None:
    send({"jsonrpc": "2.0", "id": request_id, "result": result})


def send_error(request_id, code: int, message: str) -> None:
    send({"jsonrpc": "2.0", "id": request_id, "error": {"code": code, "message": message}})


def read_message() -> dict | None:
    headers: dict[str, str] = {}
    while True:
        line = sys.stdin.buffer.readline()
        if not line:
            return None
        if line in (b"\r\n", b"\n"):
            break
        if b":" in line:
            key, value = line.decode("ascii", errors="replace").split(":", 1)
            headers[key.strip().lower()] = value.strip()
    length = headers.get("content-length")
    if length is None:
        raise ValueError("MCP message has no Content-Length header")
    raw = sys.stdin.buffer.read(int(length))
    if len(raw) != int(length):
        raise ValueError("MCP message ended before Content-Length bytes")
    value = json.loads(raw.decode("utf-8"))
    if not isinstance(value, dict):
        raise ValueError("MCP message must be a JSON object")
    return value


def handle(message: dict) -> None:
    method = message.get("method")
    request_id = message.get("id")
    if method == "notifications/initialized":
        return
    if method == "initialize":
        requested = message.get("params", {}).get("protocolVersion")
        send_result(request_id, {
            "protocolVersion": requested if isinstance(requested, str) else PROTOCOL_VERSION,
            "capabilities": {"tools": {"listChanged": False}},
            "serverInfo": {"name": "proofbricks-xylem-bundled-example", "version": VERSION},
            "instructions": "Example-scoped xylem_query; canonical graph operations are not connected.",
        })
        return
    if method == "tools/list":
        send_result(request_id, {"tools": [{
            "name": "xylem_query",
            "description": "Query the supplied CompactBounds example record; graph operations report not_connected.",
            "inputSchema": {
                "type": "object",
                "properties": {
                    "operation": {"type": "string", "enum": ["status", "search", "context", "dependencies", "dependents", "path", "explain", "impact", "discover", "similar"]},
                    "query": {"type": "string"},
                    "component_id": {"type": "string"},
                    "declaration": {"type": "string"},
                },
                "additionalProperties": False,
            },
        }]})
        return
    if method == "tools/call":
        params = message.get("params", {})
        if params.get("name") != "xylem_query":
            send_error(request_id, -32602, "unknown tool")
            return
        try:
            payload = query(params.get("arguments") or {})
        except (OSError, ValueError, json.JSONDecodeError) as error:
            send_result(request_id, {"isError": True, "content": [{"type": "text", "text": str(error)}]})
            return
        send_result(request_id, {
            "content": [{"type": "text", "text": json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True)}],
            "structuredContent": payload,
            "isError": False,
        })
        return
    if method and method.startswith("notifications/"):
        return
    if request_id is not None:
        send_error(request_id, -32601, f"method not found: {method}")


def main() -> int:
    while True:
        try:
            message = read_message()
            if message is None:
                return 0
            handle(message)
        except (ValueError, json.JSONDecodeError) as error:
            send_error(None, -32700, str(error))
            return 1


if __name__ == "__main__":
    raise SystemExit(main())
