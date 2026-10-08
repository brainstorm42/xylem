#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Check the plugin-linked canonical MCP config against a moved package copy."""

from __future__ import annotations

import json
from pathlib import Path
import os
import shutil
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[1]


def write_message(stream, value: dict) -> None:
    stream.write((json.dumps(value, ensure_ascii=False, separators=(",", ":")) + "\n").encode("utf-8"))
    stream.flush()


def read_message(stream) -> dict:
    line = stream.readline()
    if not line:
        raise AssertionError("host-config MCP closed before response")
    return json.loads(line.decode("utf-8"))


def tool_payload(response: dict) -> dict:
    result = response["result"]
    assert result["isError"] is False
    return json.loads(result["content"][0]["text"])


def main() -> int:
    config_path = ROOT / ".mcp.json"
    config = json.loads(config_path.read_text(encoding="utf-8"))
    server = config["mcpServers"]["proofbricks-xylem"]
    assert server["cwd"] == "."
    assert server["command"] == "sh"
    assert server["args"] == ["./canonical/mcp.sh"]

    with tempfile.TemporaryDirectory(prefix="proofbricks-moved-plugin-") as scratch:
        moved = Path(scratch) / "moved-package"
        shutil.copytree(ROOT, moved)
        cwd = (moved / server["cwd"]).resolve()
        env = os.environ.copy()
        env["PYTHONDONTWRITEBYTECODE"] = "1"
        env["XYLEM_PYTHON"] = sys.executable
        built = subprocess.run(
            [sys.executable, "canonical/run.py", "build"],
            cwd=cwd,
            capture_output=True,
            text=True,
            env=env,
            check=False,
        )
        assert built.returncode == 0, built.stderr + built.stdout
        process = subprocess.Popen(
            [server["command"], *server["args"]],
            cwd=cwd,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            env=env,
        )
        assert process.stdin is not None and process.stdout is not None
        try:
            write_message(process.stdin, {"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {"protocolVersion": "2024-11-05", "capabilities": {}, "clientInfo": {"name": "moved-host-config", "version": "0"}}})
            initialized = read_message(process.stdout)
            assert initialized["result"]["serverInfo"]["name"] == "xylem"
            write_message(process.stdin, {"jsonrpc": "2.0", "method": "notifications/initialized"})
            write_message(process.stdin, {"jsonrpc": "2.0", "id": 2, "method": "tools/list", "params": {}})
            tools = read_message(process.stdout)["result"]["tools"]
            assert [tool["name"] for tool in tools] == ["xylem_query"]
            operations = tools[0]["inputSchema"]["properties"]["operation"]["enum"]
            assert set(operations) == {"status", "search", "dependencies", "dependents", "path", "similar", "context", "explain", "impact", "discover"}
            write_message(process.stdin, {"jsonrpc": "2.0", "id": 3, "method": "tools/call", "params": {"name": "xylem_query", "arguments": {"operation": "status"}}})
            status = tool_payload(read_message(process.stdout))
            assert status["ok"] is True
            assert status["data"]["nodes"]["declaration"] == 1
            assert status["data"]["declaration_dependency_data"]["status"] == "unavailable"
            assert status["data"]["declaration_dependency_data"]["counts"] == {"unavailable": 1}
            write_message(process.stdin, {"jsonrpc": "2.0", "id": 4, "method": "tools/call", "params": {"name": "xylem_query", "arguments": {"operation": "search", "query_text": "compact"}}})
            search = tool_payload(read_message(process.stdout))
            assert search["ok"] is True
            assert any(item["name"] == "OAI.Problem326.compact_positive_uniform_bounds" for item in search["data"])
            for request_id, operation in ((5, "dependencies"), (6, "dependents"), (7, "impact")):
                write_message(process.stdin, {"jsonrpc": "2.0", "id": request_id,
                                              "method": "tools/call", "params": {
                                                  "name": "xylem_query",
                                                  "arguments": {
                                                      "operation": operation,
                                                      "query_text": "OAI.Problem326.compact_positive_uniform_bounds",
                                                  },
                                              }})
                traversal = tool_payload(read_message(process.stdout))
                assert traversal["ok"] is True
                assert traversal["data"]["direction"] == operation
                assert traversal["data"]["dependency_data"]["status"] == "unavailable"
                assert traversal["data"]["items"] == []
        finally:
            if process.stdin:
                process.stdin.close()
            process.terminate()
            process.wait(timeout=5)
        stderr = process.stderr.read().decode("utf-8") if process.stderr else ""
        assert not stderr, stderr

        target = "OAI.Problem326.compact_positive_uniform_bounds"
        for operation in ("dependencies", "dependents", "impact"):
            completed = subprocess.run(
                [sys.executable, "canonical/run.py", "query", operation, target, "--json"],
                cwd=cwd,
                capture_output=True,
                text=True,
                env=env,
                check=False,
            )
            assert completed.returncode == 0, completed.stderr + completed.stdout
            traversal = json.loads(completed.stdout)
            assert traversal["direction"] == operation
            assert traversal["dependency_data"]["status"] == "unavailable"
            assert traversal["items"] == []

        review = subprocess.run(
            [sys.executable, "canonical/run.py", "query", "review", target, "--json"],
            cwd=cwd,
            capture_output=True,
            text=True,
            env=env,
            check=False,
        )
        assert review.returncode == 0, review.stderr + review.stdout
        report = json.loads(review.stdout)
        assert report["dependency_data"]["status"] == "unavailable"
        for section in ("proof", "type"):
            assert report["dependencies"][section]["status"] == "unavailable"
            assert report["dependencies"][section]["dependency_data"]["status"] == "unavailable"
            assert report["dependencies"][section]["items"] == []
        assert report["affected_local_results"]["dependency_data"]["status"] == "unavailable"

        html_path = moved / "review.html"
        review_html = subprocess.run(
            [sys.executable, "canonical/run.py", "query", "review", target,
             "--output", str(html_path)],
            cwd=cwd,
            capture_output=True,
            text=True,
            env=env,
            check=False,
        )
        assert review_html.returncode == 0, review_html.stderr + review_html.stdout
        rendered = html_path.read_text(encoding="utf-8")
        assert "dependency data state: unavailable" in rendered
        assert "dependency data state=unavailable" in rendered
    print("moved_host_config_canonical_stdio: PASS")
    print("canonical_dependency_traversal_state: PASS")
    print("canonical_review_json_and_html_state: PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
