<!-- SPDX-License-Identifier: Apache-2.0 -->
# Xylem package

This directory contains the installable Python package used by the public `canonical/run.py` runner. It provides the read-only graph builder, query CLI, MCP server, freshness tracking, statement-navigation helpers, and an optional structural-discovery overlay. It does not bundle a Lean corpus or generated database.

## Install

From the `xylem-plugin` directory:

```sh
python3.12 -m venv .venv
.venv/bin/python -m pip install canonical/xylem
```

Then follow the [public Ctrllib example](../../examples/ctrllib-e2e/README.md), which supplies explicit input paths and keeps generated state in its ignored `graph/` directory. The package also exposes `xylem-build`, `xylem-query`, and `xylem-mcp` for callers that provide their own selected inputs.

The optional `techniques` query is a read-only structural overlay over a caller-supplied fixed capture manifest; see [`../DISCOVERY.md`](../DISCOVERY.md) for its bounded workflow. The package and its runtime are covered by the repository's Apache-2.0 and scoped notice files. PyYAML, MCP, Lean, Mathlib, Lake, and any supplied source or capture retain their own terms.
