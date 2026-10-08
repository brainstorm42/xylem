<!-- SPDX-License-Identifier: Apache-2.0 -->
# Ctrllib source-first E2E example

This is the smallest checked example that exercises the packaged Xylem CLI, MCP server, statement converter, and a source-module explanation pointer over real Ctrllib extraction records. The five declaration records are a compact fixture selected from a separate full run over all 123 included source modules. The full formatted capture is about 851 MiB; its hash and counts are in [the verification receipt](../../../provenance/air-consumer-verification.json).

The fixture is intentionally partial. Its premise records are present, but only five local declarations are serialized, so Xylem may show external premise stubs and an incomplete dependency state. That is expected and is not a claim that the source has no other dependencies. The example has no Brick or bibliography input; therefore it demonstrates module-to-explanation navigation but not a source-to-component correspondence.

The compact `query status --json` result is expected to contain `"fresh": false` and a warning naming these 14 source modules absent from the five-record graph: `Ctrllib.AssumeGuarantee`, `Ctrllib.CruiseLag`, `Ctrllib.ElasticAttachment`, `Ctrllib.Examples.ProofSearchReuse`, `Ctrllib.GaussianTail`, `Ctrllib.GiordanoErrata`, `Ctrllib.KoenigDecomposition`, `Ctrllib.NominalMPC`, `Ctrllib.PVSYoung`, `Ctrllib.ReferenceFrameResidual`, `Ctrllib.RoverKinematicCompatibility`, `Ctrllib.SkewCharP`, `Ctrllib.SphericalHelix`, and `Ctrllib.VaRSubadditivity`. The command still returns 0. The dependency state is `partial`, not `captured` or `unavailable`, because selected premise records and external stubs are present.

For the portable full source → extract → graph → CLI/MCP/converter procedure, see [`REGENERATE-FULL.md`](REGENERATE-FULL.md). The checked 808-declaration receipt has also been reproduced from public dependencies on the Air; the guide is the mechanism for user-controlled regeneration.

## Run

From this `xylem-plugin` directory, use the already provisioned pinned Python environment; the package does not install dependencies.

```sh
PYTHON=/path/to/python3.12
CFG=examples/ctrllib-e2e/xylem-e2e-config.json

"$PYTHON" canonical/run.py --config "$CFG" build
"$PYTHON" canonical/run.py --config "$CFG" query status --json
"$PYTHON" canonical/run.py --config "$CFG" query search pointMass --json
"$PYTHON" canonical/run.py --config "$CFG" convert render-statement \
  --declaration Ctrllib.pointMass_tendsto_zero --json
"$PYTHON" canonical/run.py --config "$CFG" query context \
  Ctrllib.pointMass_tendsto_zero --limit 5 --edge-scope proof --json
"$PYTHON" canonical/run.py --config "$CFG" query path \
  Ctrllib.pointMass_tendsto_zero Ctrllib.pmM_inv --json

```

Read the [point-mass explanation](vault/PointMassComFlow.md), then use the full first-level dependency listing as an audit (172 items in the checked fixture):

```sh
"$PYTHON" canonical/run.py --config "$CFG" query dependencies \
  Ctrllib.pointMass_tendsto_zero --depth 1 --json
```

A compact fixture cannot gain omitted modules by rebuilding its unchanged capture. Use full source-first regeneration when full coverage is needed.

The build creates the ignored `graph/xylem.db`. The checked local run also used the same config with `canonical/run.py --config "$CFG" mcp` and completed initialize, tool listing, status, dependency, path, and context requests.

The converter preserves exact Lean text where the compact capture does not provide enough notation structure. This is a rendering fallback, not a semantic translation or formal proof check. The Ctrllib source itself is compiled and extracted separately with its pinned Lean/Lake toolchain; this Xylem example does not run Lake.

## Scope

This example supports bounded graph status, search, dependency/dependent/path/context navigation, MCP queries, statement rendering, and the module-to-explanation pointer. Rendering keeps formal acceptance unassessed; interpret dependency results with the fixture's partial coverage state.

## Select Ctrllib in an MCP host

The default `canonical/mcp.sh` selects CompactBounds. Run Ctrllib explicitly:

```sh
"$PYTHON" canonical/run.py --config "$CFG" mcp
```

For a host, set `cwd` to the absolute copied `xylem-plugin` directory and `command` to the absolute isolated venv interpreter; this sample uses the existing runner (replace those two paths):

```json
{"mcpServers":{"xylem-ctrllib":{
  "command":"/path/to/isolated/venv/bin/python",
  "cwd":"/path/to/copied/xylem-plugin",
  "args":["canonical/run.py","--config","examples/ctrllib-e2e/xylem-e2e-config.json","mcp"]
}}}
```
