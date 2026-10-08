<!-- SPDX-License-Identifier: Apache-2.0 -->
# Verification of the corrected package

The current compact CLI/MCP workflows and regression checks passed on macOS arm64. The independent explanation review passed. The full Air source-first run used the same Lean sources and dependency pins supplied here; those bytes are unchanged. Current check-label, freshness-advice, and prose changes were verified separately.

| Check | Result | Evidence scope |
| --- | --- | --- |
| Targeted mathematical/interface/converter/freshness cases | 7 passed | Exact rational interval witnesses, capture/source/interface agreement, parser success/failure, controlled existing-declaration gate success/failure, output and receipt hashes, coverage versus changed-input advice |
| Grounded packet regression | PASS | Source SHA256, source span, parent binders, scoped fresh review |
| Premise-availability regression | PASS | unavailable/empty/partial/captured states |
| Capture safety regression | PASS | Output preservation and library roots |
| Moved host-config regression | PASS | Canonical stdio, traversals, review JSON/HTML |
| Bundled regression MCP | PASS | Initialize, listing, CompactBounds context |
| Current compact CLI workflows | PASS | Build, status twice, search, statement rendering; Ctrllib context/path/dependencies/review |
| Current compact MCP workflows | PASS | Initialize, tool listing, status twice; Ctrllib context/path |
| Independent explanation review | PASS | Mathematical prose and source/interface consistency |
| Rover guide | 16 modules, 68 source declaration links | Links validated against exact declaration lines; private helpers labeled |
| Full source-first build and extraction | PASS in Air run | Same proof sources/pins; 123 modules and 808 declarations |

The declaration-gate success/failure regressions use controlled gate outcomes to verify labels, exit codes, and hashing. They are unit tests rather than a new Lean check. The existing-declaration check hashes rendered output but does not submit that output to Lean. Round-trip checks compare normalized parser IR. Statement rendering keeps acceptance unassessed.

From `xylem-plugin`, use the isolated pinned Python interpreter:

```sh
"$PYTHON" tests/test_release_corrections.py
"$PYTHON" tests/test_grounded_packet.py
"$PYTHON" tests/test_premise_availability.py
"$PYTHON" tests/test_capture_safety.py
"$PYTHON" tests/test_host_config.py
"$PYTHON" tests/test_bundled_mcp.py
```

The [fresh review receipt](../xylem-plugin/examples/compact-bounds/evidence/review-corrected-explanations.json) records its scope. Helper checking summaries remain evidence for their recorded operation; generated CompactBounds helper replay was not performed. Public Markdown uses full paragraphs with code, math, tables, lists, front matter, and intentional line breaks preserved during reflow. The [current inventory](corrected-release-manifest.json) binds the supplied files.

See [tabulated contents and evidence](../RELEASE-SCOPE.md), [full Air verification](AIR-CONSUMER-CHECK.md), and [public regeneration](../xylem-plugin/examples/ctrllib-e2e/REGENERATE-FULL.md).
