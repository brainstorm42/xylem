<!-- SPDX-License-Identifier: Apache-2.0 -->
# Xylem

Xylem connects formal proofs with explanations and a searchable dependency graph. A ProofBrick pairs a formal proof and its supporting declarations with a people-centred explanation of its assumptions and guarantees. Xylem helps you follow those relationships in a checked Lean development.

Lean checks proofs; Xylem exposes their recorded structure.

## Read a result

1. Start with the [Xylem and ProofBricks reader guide](xylem-plugin/docs/xylem-reader-guide.md).
2. Read the worked [strict-comparisons-to-equality example](xylem-plugin/docs/from-strict-comparisons-to-equality.md), then compare its two one-sided bounds and the equality they recover.
3. Try the [Ctrllib source-first example](xylem-plugin/examples/ctrllib-e2e/README.md) and use search, context, dependencies, and path queries around its result.

## Install and try

You need Git and Python 3.12. From a fresh checkout, create an isolated environment, install the package, and run the compact Ctrllib example:

```sh
GIT_LFS_SKIP_SMUDGE=1 git clone https://github.com/brainstorm42/xylem.git
cd xylem/xylem-plugin
python3.12 -m venv .venv
.venv/bin/python -m pip install canonical/xylem
./try-xylem
```

The compact example does not need the large percolation capture, so the clone command leaves Git LFS pointers untouched. The helper keeps its generated SQLite database in the ignored `graph/` directory. For further CLI and MCP usage, see the [Ctrllib example guide](xylem-plugin/examples/ctrllib-e2e/README.md).

## Current results

The public snapshot includes a CompactBounds navigation example, a source-first Ctrllib example, and a standalone [planar module slice](ctrllib/HANDBOOK-PLANAR.md). The [evaluation status](RESULTS-STATUS.md) records the checked reuse, bound, proof-generalization, and technique-selection results, including the work that remains incomplete. The package also includes an optional [structural-discovery overlay](xylem-plugin/canonical/DISCOVERY.md) for caller-supplied captures.

For related proof-generalization context, see the paper [Automatically Generalizing Proofs and Statements](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2025.12).

## License and provenance

Read the [Apache-2.0 license](LICENSE) and [top-level notices](NOTICE.md). Those notices link the component terms and provenance records; supplied source snapshots, captures, generated graphs, and cited works may retain separate terms.
