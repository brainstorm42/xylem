<!-- SPDX-License-Identifier: Apache-2.0 -->
# Canonical runtime bundle

This directory provides the ProofBricks Python runtimes: `canonical/xylem/xylem/server.py` implements Xylem MCP and `canonical/brickconverter/` implements statement rendering and notation conversion. Run the commands below from the `xylem-plugin` package directory.

## Exact local commands

Use Python 3.10+ with the pinned direct dependencies in [`requirements.txt`](requirements.txt). For a normal isolated setup:

```sh
python3.12 -m venv .venv
.venv/bin/python -m pip install -r canonical/requirements.txt
```

After setup, run:

```sh
PYTHON=.venv/bin/python

"$PYTHON" canonical/run.py build
"$PYTHON" canonical/run.py query status --json
"$PYTHON" canonical/run.py query search compact --json
"$PYTHON" canonical/run.py convert render-statement \
  --declaration OAI.Problem326.compact_positive_uniform_bounds --json
XYLEM_PYTHON="$PYTHON" canonical/mcp.sh
```

The default config is [`example-config.json`](example-config.json). It builds a small graph from the supplied declaration capture and an empty import graph. The capture sets `premises_included` to false, so status/context report dependency data as unavailable rather than treating zero `USES_*` edges as proof of no dependencies. The `dependencies` and `dependents` CLI/MCP results are structured with `dependency_data` and `items`, and the review JSON/HTML carries the same state. This keeps `unavailable`, `empty`, `partial`, and `captured` distinct when an items list is empty. `mcp.sh` then starts the real canonical Xylem MCP stdio server against that configured graph. The launcher prefers `../.venv/bin/python`; set `XYLEM_PYTHON` or `PROOFBRICKS_PYTHON` to override it. If `PyYAML==6.0.3` or `mcp==2.2.0` is missing, it prints the isolated-venv setup command and exits without installing anything. The MCP exposes the canonical `xylem_query` operations: `status`, `search`, `dependencies`, `dependents`, `path`, `similar`, `context`, `explain`, `impact`, and `discover`.

For another supported dataset, copy the config and set `relative_to` to `config`, then provide `dot`, `extractor`, `vault`, `db`, and optional `bricks`, `bib`, `ctrllib`, `data`, `converter_capture`, and `converter_profile` paths. Relative paths are resolved from that config file; absolute paths are accepted. `build` passes these paths to the canonical builder, and `query`/`mcp` set the canonical environment overrides in the current process only.

The canonical BrickConverter remains a statement/document adapter. It retains exact captured Lean text, uses expression trees when supplied, and falls back to exact text for unsupported or tree-free fragments. It does not translate proof terms or certify source equivalence. The bundled CompactBounds projection intentionally has no expression trees, so its reproducible output is exact fallback rather than a semantic notation claim.

The MCP also exposes read-only `overview` and `components` operations when a
configured dataset supplies a validated component overlay. These return
source-backed component metadata and exact declaration zooms; authored
interpretation remains visibly separate from compiler evidence.

## Dependencies and optional formal checks

The direct runtime pins are Python 3.10+, `PyYAML==6.0.3`, and `mcp==2.2.0`. The observed direct package metadata identifies both Python packages as MIT-licensed. `pytest` is only needed for the upstream runtime test suites. Formal `brickconverter check`/`check-statement` additionally require an existing Lean/Ctrllib environment and a user-supplied authorized capture source; those commands are not part of the offline tiny-graph smoke test.

For `round-trip`, schema 2 reports normalized IR equality (`ir_round_trip`). For `check`, schema 2 reports an existing-declaration gate (`checks_passed`); the rendered output is hashed but is not passed to that gate. Both keep acceptance `not_assessed` and distinguish generated-output formal checking from the named-declaration check.

See [runtime attribution](ORIGIN.md) and [the Ctrllib example](../examples/ctrllib-e2e/README.md) for its explicitly configured CLI/MCP route.
