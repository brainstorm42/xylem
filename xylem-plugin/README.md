<!-- SPDX-License-Identifier: Apache-2.0 -->
# Xylem v0.1.0 — ProofBricks plugin

Xylem is the fundamental surface in this package: it inspects one captured Lean declaration, builds a one-module graph from repository-relative inputs, and serves the canonical query/MCP interface. ProofBricks supplies the statement-rendering, decomposition, and explanation components around that surface. The package IDs and tested runtime namespaces retain `proofbricks-xylem` for compatibility; no future repository URL is assumed.

## Concrete example

The example is `OAI.Problem326.compact_positive_uniform_bounds`. For a finite index type `ι` and compact `K : Set (ι → ℝ)`, define

```text
S = ⋃ i : ι, (fun x : ι → ℝ => x i) '' K.
```

The supplied native receipts check the leading facts `hS : IsCompact S` and `hSpos : ∀ y ∈ S, 0 < y`. They do not decompose the whole theorem. The projection retains the exact five-binder statement but does not supply premise records, proof terms, or expression trees. Consequently, a zero dependency-edge count means that dependency data was unavailable, not that the theorem has no dependencies.

The mathematics-first explanation is [`examples/compact-bounds/explanation-hS.md`](examples/compact-bounds/explanation-hS.md). The ordered report is [`TECHNICAL-REPORT.md`](TECHNICAL-REPORT.md).

## Run from the package root

The checked environment is Python 3.12.14 with the pinned direct dependencies `PyYAML==6.0.3` and `mcp==2.2.0`. The package does not install them.

For a fresh isolated consumer install, create a virtual environment in the copied package directory and install the declared pins:

```sh
python3.12 -m venv .venv
.venv/bin/python -m pip install -r canonical/requirements.txt
PYTHON="$PWD/.venv/bin/python"
```

The Air consumer check also passed with Python 3.12.13. Python 3.12.14 above identifies the earlier checked environment rather than an enforced patch-version requirement.

```sh
PYTHON=/path/to/python3.12
"$PYTHON" canonical/run.py build
"$PYTHON" canonical/run.py query status --json
"$PYTHON" canonical/run.py query search compact --json
"$PYTHON" canonical/run.py convert render-statement \
  --declaration OAI.Problem326.compact_positive_uniform_bounds --json
```

The status result should report one declaration and one `DECLARED_IN` edge, with no asserted `USES_IN_TYPE`/`USES_IN_PROOF` edges and a `declaration_dependency_data.status` of `unavailable`. The search returns the CompactBounds declaration. The converter retains five binders and uses exact Lean-text fallback for the tree-free fragments; its output is not a semantic translation claim.

Dependency and dependent traversals return a structured object with `dependency_data` and `items`. In this example `dependency_data.status` is `unavailable` and `items` is empty because premise records were not supplied; the empty list is not a no-dependencies result. The same state is carried by the canonical MCP operations and by `query review --json`/the generated HTML report.

MCP is optional. After the build, run this foreground stdio server from the same package-root directory:

```sh
XYLEM_PYTHON="$PYTHON" canonical/mcp.sh
```

The launcher prefers `.venv/bin/python`, accepts `XYLEM_PYTHON` or `PROOFBRICKS_PYTHON`, checks the pinned dependencies, and never installs packages. Hosts that support MCP can use the package-relative [`.mcp.json`](.mcp.json).

## Supported surfaces

| Surface | Supported scope |
| --- | --- |
| Navigator | canonical CLI/MCP status, search, context, and bounded graph operations over the configured input |
| BrickConverter | canonical statement/document/profile path with exact Lean-text fallback when trees are absent |
| Decomposition | recorded native `hS`/`hSpos` receipts only; not automatic runtime integration |
| Explanation | separately authored CompactBounds mathematics with source and receipt links |

The current graph is setup/statement-inspection evidence only: one module, one declaration, and containment. Source/dependency, containment, import, and conceptual/provenance relationships remain distinct. The older `mcp/bundled_server.py` and `runtime/bundled_converter.py` are retained only as example-scoped regression surfaces; the plugin-linked provider is under [`canonical/`](canonical/).

## Limits

These examples support captured-statement inspection and graph navigation. Formal replay needs an external pinned Lean, Mathlib, and authorized capture environment. Isolated Python installation and the public Lean/Mathlib bootstrap passed on macOS arm64; see the [Air verification boundary](../provenance/AIR-CONSUMER-CHECK.md). Installation of OS prerequisites, separate CompactBounds replay, and Windows execution remain unverified. The adapted OpenAI Math fixture keeps its Apache-2.0 attribution and license.

See [architecture](ABOUT.md), [supported examples](RELEASE-SCOPE.md), and the [Ctrllib navigation guide](examples/ctrllib-e2e/README.md).
