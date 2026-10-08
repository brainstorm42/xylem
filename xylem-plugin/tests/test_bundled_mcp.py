#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Bounded stdio smoke test for the bundled MCP example."""

from __future__ import annotations

import json
from pathlib import Path
import os
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
SERVER = ROOT / "mcp" / "bundled_server.py"


def write_message(stream, value: dict) -> None:
    raw = json.dumps(value, ensure_ascii=False, separators=(",", ":")).encode("utf-8")
    stream.write(f"Content-Length: {len(raw)}\r\n\r\n".encode("ascii") + raw)
    stream.flush()


def read_message(stream) -> dict:
    headers = {}
    while True:
        line = stream.readline()
        if not line:
            raise AssertionError("bundled MCP closed before response")
        if line in (b"\r\n", b"\n"):
            break
        key, value = line.decode("ascii").split(":", 1)
        headers[key.strip().lower()] = value.strip()
    length = int(headers["content-length"])
    payload = stream.read(length)
    if len(payload) != length:
        raise AssertionError("bundled MCP response was truncated")
    return json.loads(payload.decode("utf-8"))


def tool_payload(response: dict) -> dict:
    assert response["result"]["isError"] is False
    payload = response["result"]["structuredContent"]
    assert json.loads(response["result"]["content"][0]["text"]) == payload
    return payload


def main() -> int:
    env = os.environ.copy()
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    process = subprocess.Popen(
        [sys.executable, "-S", str(SERVER)],
        cwd=ROOT,
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        env=env,
    )
    assert process.stdin is not None and process.stdout is not None
    try:
        write_message(process.stdin, {"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {"protocolVersion": "2024-11-05", "capabilities": {}, "clientInfo": {"name": "smoke", "version": "0"}}})
        initialized = read_message(process.stdout)
        assert initialized["result"]["serverInfo"]["version"] == "0.1.0"
        write_message(process.stdin, {"jsonrpc": "2.0", "method": "notifications/initialized"})
        write_message(process.stdin, {"jsonrpc": "2.0", "id": 2, "method": "tools/list", "params": {}})
        tools = read_message(process.stdout)["result"]["tools"]
        assert [tool["name"] for tool in tools] == ["xylem_query"]

        write_message(process.stdin, {"jsonrpc": "2.0", "id": 3, "method": "tools/call", "params": {"name": "xylem_query", "arguments": {"operation": "status"}}})
        status = tool_payload(read_message(process.stdout))
        assert status["status"] == "bundled_example_ready"
        assert status["canonical_xylem"] == "not_connected"
        assert status["declaration_dependency_data"]["status"] == "unavailable"

        write_message(process.stdin, {"jsonrpc": "2.0", "id": 4, "method": "tools/call", "params": {"name": "xylem_query", "arguments": {"operation": "context", "component_id": "compact-bounds-hS"}}})
        context = tool_payload(read_message(process.stdout))
        assert context["component"]["formal_type"] == "IsCompact S"
        capture = context["exact_statement_capture"]
        assert capture["binder_count"] == 5
        assert capture["binder_names"] == ["ι", None, "K", "hK", "hpos"]
        assert context["converter_summary"]["all_binders_retained"] is True
        assert context["converter_summary"]["acceptance_status"] == "not_assessed"
        assert context["graph"]["status"] == "not_connected"
        assert context["exact_statement_capture"]["dependency_capture"]["status"] == "unavailable"

        write_message(process.stdin, {"jsonrpc": "2.0", "id": 5, "method": "tools/call", "params": {"name": "xylem_query", "arguments": {"operation": "dependencies", "component_id": "compact-bounds-hS"}}})
        unavailable = tool_payload(read_message(process.stdout))
        assert unavailable["status"] == "not_connected"
        assert unavailable["operation"] == "dependencies"
    finally:
        if process.stdin:
            process.stdin.close()
        process.terminate()
        process.wait(timeout=5)
    stderr = process.stderr.read().decode("utf-8") if process.stderr else ""
    if stderr:
        raise AssertionError(f"bundled MCP wrote stderr: {stderr}")
    print("bundled_mcp_stdio: PASS")
    print("initialize: PASS")
    print("tools/list: PASS")
    print("tools/call context CompactBounds: PASS")
    print("unsupported canonical graph operation: explicit not_connected")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
