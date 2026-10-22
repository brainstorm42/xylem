<!-- SPDX-License-Identifier: Apache-2.0 -->
# Structural discovery overlay

Xylem's optional `techniques` command is a read-only CPU overlay over a caller-supplied, versioned declaration capture and optional bounded trace or type evidence. It preserves the graph and proof data and emits source-anchored structural proposals. The overlay does not invoke Lean, execute manifest paths, or claim theorem equivalence, mathematical meaning, proof reuse, or benchmark performance.

After installing the package, run it with a fixed manifest:

```sh
PYTHONPATH=canonical/xylem .venv/bin/python -m xylem.query \
  techniques --manifest /path/to/manifest.json --json
```

The canonical runner accepts the same query:

```sh
.venv/bin/python canonical/run.py --config path/to/config.json \
  query techniques --manifest /path/to/manifest.json --json
```

Manifests should declare fixed budgets, training and held-out families, artifact hashes, and authorized roots. MCP checks every resolved manifest input and rejects paths outside its configured roots. Held-out material never feeds proposal acceptance.

The checked runtime receipt reports deterministic replay and CLI/MCP parity for a bounded selected slice. The associated development capture and percolation evidence are not bundled by this release; callers supply their own authorized inputs.
