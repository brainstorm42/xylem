<!-- SPDX-License-Identifier: Apache-2.0 -->
# About Xylem v0.1.0

Xylem provides graph navigation in this package. It carries four deliberately separate layers:

1. the canonical Xylem Python graph builder, query CLI, and MCP server;
2. the canonical BrickConverter statement/document/profile runtime;
3. a proof-free CompactBounds declaration projection and tiny graph input; and
4. an experimental decomposition receipt plus a separately authored
   mathematical explanation.

`canonical/run.py` is a repository-relative/config-relative path adapter. It does not implement a second graph server. The canonical builder creates the configured SQLite graph; the query CLI and canonical MCP read it. The graph records formal dependency edges only when the supplied capture provides premise records. In the CompactBounds projection `premises_included` is false, so status and context explicitly report dependency data as unavailable.

The parent declaration preserves all five binders and its exact conclusion. The canonical converter retains exact Lean text for this tree-free projection. The CompactBounds prose is authored separately and is not converter output or source-equivalence evidence. The native receipts cover the leading `hS` and `hSpos` proposition boundaries only; they do not establish automatic helper-to-graph integration or a full theorem decomposition.

The package-local `mcp/bundled_server.py` and `runtime/bundled_converter.py` are older stdlib-only regression surfaces. They are not the plugin-linked provider. The CompactBounds MCP entrypoint is [`canonical/mcp.sh`](canonical/mcp.sh), and the host configuration is [`.mcp.json`](.mcp.json).

The fixed successor carries the same capture-data state through canonical CLI dependency/dependent traversals, MCP dependency/dependent operations, and the reviewer's JSON/HTML output. `unavailable`, `empty`, `partial`, and `captured` remain distinct states; an empty `items` list is interpreted only with that state.

The adapted source fixture is attributed to `openai/math` at the pinned revision in [`examples/compact-bounds/third_party/openai-math/NOTICE.md`](examples/compact-bounds/third_party/openai-math/NOTICE.md). The direct runtime pins are PyYAML 6.0.3 and MCP 2.2.0; their direct metadata identifies MIT licensing. Lean, Mathlib, the CompactBounds capture tool, and Python packages are external dependencies. The Ctrllib source package and extractor are included at `../ctrllib`.

The shared scope statement is [RELEASE-SCOPE.md](RELEASE-SCOPE.md). The technical account is [TECHNICAL-REPORT.md](TECHNICAL-REPORT.md). For captured Ctrllib dependency navigation and its configured MCP entrypoint, see [the Ctrllib example](examples/ctrllib-e2e/README.md).
