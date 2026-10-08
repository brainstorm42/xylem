<!-- SPDX-License-Identifier: Apache-2.0 -->
# Air consumer verification — 2026-10-08

The consumer test passed on a MacBook Air with Apple M2, 24 GB RAM, and macOS 26.6.2 arm64. It used a new isolated folder and venv, public pinned dependencies, and external generated outputs. Existing installations and Downloads files were preserved.

The full build and extraction tested the supplied proof sources and dependency pins. Those files remain unchanged in this package. Current runtime-label and explanation corrections have their own [targeted check](CORRECTION-CHECK.md); the long Lean build was not repeated for those changes.

## Versions and prerequisite boundary

| Component | Observed version |
| --- | --- |
| Python in isolated venv | 3.12.13 |
| Earlier Python test baseline | 3.12.14 |
| PyYAML / MCP | 6.0.3 / 2.2.0 |
| Ctrllib Lean | 4.34.0, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b` |
| Lake | 5.0.0-src+293d5d0 |
| Separate retained CompactBounds evidence | Lean 4.34.1; replay unrun |

The Air already had Python 3.12, Git, curl, tar, and zstd. Installing those prerequisites onto a blank operating system was not tested. The existing Lean toolchain was not used for Ctrllib and was not changed. Transitive Python packages were resolved by pip; only the declared direct dependencies are pinned by this release.

The [public bootstrap guide](../xylem-plugin/examples/ctrllib-e2e/BOOTSTRAP-PUBLIC-MACOS.md) transcribes the actual successful operations using caller-selected paths. It records the inspected Lake configuration and macOS zstd recovery. The [regeneration guide](../xylem-plugin/examples/ctrllib-e2e/REGENERATE-FULL.md) contains the graph and query commands.

## Results

| Stage | Result |
| --- | --- |
| Input archive size and SHA256 | PASS |
| Fresh isolated Python pin installation | PASS |
| CompactBounds quickstart, graph, search, five-binder converter | PASS |
| Documented `canonical/mcp.sh` initialize/list/status/repeated status | PASS |
| Compact Ctrllib CLI/MCP/converter and dependency/path/context queries | PASS |
| Public exact-commit dependency fetch and official Lean asset verification | PASS |
| Official Mathlib cache bootstrap | PASS: 8908 files downloaded/decompressed |
| Shipped source-first compilation | PASS: 123 modules, umbrella, extractor; 460.371 s |
| Extraction | PASS: 808 declarations, exact 123-module coverage, zero errors; 115.106 s |
| Full graph CLI/MCP/converter and repeated status | PASS |

The compact Ctrllib fixture correctly reported `fresh: false`, dependency state `partial`, and the expected 14-module omission warning. Its graph had 250 declarations (five local records), 109 modules, and one explanation page. That warning is expected fixture incompleteness, not failed execution or a claim of full graph freshness.

The regenerated full capture was 892231751 bytes, SHA256 `91f234ee5ab26a00c6aa2eac66dfac71f77de2ef42b889dad1e73ee78955597e`, identical to the earlier full-run receipt. The generated import graph had 123 modules and 140 internal import edges. The full Xylem graph reported:

| Graph measure | Count |
| --- | ---: |
| Modules | 123 |
| Declarations, including external stubs | 3155 |
| Captured local declarations | 808 |
| External declaration stubs | 2347 |
| IMPORTS | 140 |
| USES_IN_TYPE | 26293 |
| USES_IN_PROOF | 68381 |
| DECLARED_IN | 808 |
| PAIRED_WITH | 1 |

Two consecutive full CLI status reads and two MCP status requests were identical, with `fresh: true` and no warning. Dependency state remained `partial` because external stubs were intentionally unexpanded. MCP also passed dependencies, dependents, path, and proof-scoped context queries. The converter reported acceptance `not_assessed`; navigation/rendering success is not theorem decomposition or formal proof acceptance.

## Test limits

All dependency commits matched the [shipped pins](../ctrllib/lake-manifest.json). Ordinary Ctrllib `lake build`/`lake exe extract`, separate CompactBounds 4.34.1 helper replay, Windows, and installation of operating-system prerequisites were not tested. The [portable receipt](air-consumer-verification.json) retains versions, dependency revisions, extraction hash, and counts.
