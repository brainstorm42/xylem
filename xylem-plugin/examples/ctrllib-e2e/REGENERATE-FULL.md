<!-- SPDX-License-Identifier: Apache-2.0 -->
# Regenerate the full source-to-Xylem path

The shipped source-first runner uses only paths supplied by the caller and an existing Lean/Lake dependency closure. It never runs `lake build`, `lake exe`, a Lake `run_cmd`, a package installer, or a network fetch. The separate dependency-bootstrap step below does fetch public dependencies. The [Air check](../../../provenance/AIR-CONSUMER-CHECK.md) verified this public bootstrap and full regeneration on the original release code.

## Public dependency provisioning on macOS arm64

The Air consumer check provisioned the closure from public sources in a new external test folder. It used Python 3.12.13, the direct Python pins in `canonical/requirements.txt`, Lean 4.34.0, and all nine exact Git revisions in `ctrllib/lake-manifest.json`.

The [portable bootstrap commands](BOOTSTRAP-PUBLIC-MACOS.md) transcribe the tested operations with caller-selected paths and no machine-specific locators. Before running the source-first procedure below:

1. Fetch each public repository URL at its exact manifest `rev`, using
   `git init`, `git fetch --depth=1 origin REV`, and detached `FETCH_HEAD`.
   Inspect the fetched license and Lake configuration. In these pinned files,
   Mathlib has a cache-fetch `post_update` hook and ProofWidgets has npm build
   targets; no top-level `run_cmd` or patch operation was found.
2. Download the official `leanprover/lean4` v4.34.0
   `lean-4.34.0-darwin_aarch64.tar.zst` asset. Verify 561666156 bytes and SHA256
   `69f263fa6e21bbc2466bbfb1affcd92479ee2714c883a07de548e099a5922932`.
   Extract in the external test folder with `zstd -dc ARCHIVE | tar -xf - -C TOOLCHAIN_DIR`.
3. In the public Mathlib checkout, make `.lake/packages/NAME` symlinks to the
   other eight exact public checkouts. Use the downloaded toolchain's `bin`
   directory first on the child process PATH, set `MATHLIB_CACHE_DIR` to a new
   task-local directory, and set `MATHLIB_NO_CACHE_ON_UPDATE=1`. Run the
   downloaded `lake exe cache get` from this public Mathlib checkout.
   The Air run fetched and decompressed 8908 official cache files. This is
   dependency provisioning, separate from Ctrllib compilation.
4. Supply each dependency's existing `.lake/build/lib/lean` as a repeated
   `--lean-path` and each public source root as a repeated `--lean-src-path`.
   Also supply the downloaded Lean `lib/lean` and `src/lean` roots. The CLI
   repository did not need compiled objects in this dependency closure.
   Use dependency paths only; the runner must compile Ctrllib from the supplied source.

This manually provisioned public closure passed the shipped runner on Air: all 123 modules, the umbrella and extractor compiled; extraction returned 808 declarations over exactly 123 modules with zero errors. The formatted capture matched the earlier receipt's SHA256 exactly. Full graph, CLI, MCP, converter, and repeated-status checks passed. No bootstrap installer is shipped, and this macOS observation does not establish Windows support.

## 1. Compile, extract, and write the import graph

Set these variables to paths on the machine doing the regeneration:

```sh
PACKAGE=/path/to/proofbricks-xylem-plugin-v0.1.0-ctrllib-e2e-repro-successor
LEAN=/path/to/existing/lean
PYTHON=/path/to/python3.12
OUT=/tmp/ctrllib-source-first-e2e
```

Pass the existing public dependency object and source roots explicitly, repeating both options for every entry. Both `--lean-path` and `--lean-src-path` are required, so ambient search paths cannot be inherited.

```sh
LEAN_PATH_1=/path/to/existing/dependency/olean/root
LEAN_SRC_PATH_1=/path/to/existing/dependency/source/root
"$PYTHON" "$PACKAGE/ctrllib/tools/source_first_e2e.py" all \
  --lean "$LEAN" \
  --lean-path "$LEAN_PATH_1" \
  --lean-src-path "$LEAN_SRC_PATH_1" \
  --output-root "$OUT"
```

`OUT` must be new or empty and outside the package. The runner compiles the 123 candidate modules, `Ctrllib.lean`, and `Extract.lean` into `OUT/build`, then writes the full `declarations.json` to `OUT/extract` and the internal import graph to `OUT/graph/module_graph.dot`. Candidate source is first in `LEAN_SRC_PATH`; the supplied object paths contain only dependencies. A fresh machine provisions the pinned Lean/Mathlib closure separately using the public bootstrap above. Other platforms and OS prerequisite installation remain unverified. `--lean-path` and `--lean-src-path` may be repeated to provide all entries.

The runner emits bounded receipts in the external output directory. The existing local run used Lean 4.34.0, 8,192 MB, 600 seconds per module, 3,600 seconds total for compilation, and 1,800 seconds for extraction.

## 2. Build the full Xylem graph

Create a temporary config outside the package. The config contains the explicit paths supplied below and should not be copied into a release archive. The helper rejects config and database targets under the combined package root and requires a new external database target:

```sh
"$PYTHON" "$PACKAGE/xylem-plugin/examples/ctrllib-e2e/make_full_e2e_config.py" \
  --capture "$OUT/extract/declarations.json" \
  --dot "$OUT/graph/module_graph.dot" \
  --ctrllib "$PACKAGE/ctrllib" \
  --db "$OUT/xylem.db" \
  --output "$OUT/xylem-full-config.json"

"$PYTHON" "$PACKAGE/xylem-plugin/canonical/run.py" \
  --config "$OUT/xylem-full-config.json" build
```

The full graph should report 123 modules, 3,155 declaration nodes (808 local Ctrllib declarations plus 2,347 external stubs), 140 import edges, 26,293 type-use edges, 68,381 proof-use edges, 808 `DECLARED_IN` edges, and one `PAIRED_WITH` edge from the package explanation page.

## 3. Exercise CLI, converter, and MCP

```sh
"$PYTHON" "$PACKAGE/xylem-plugin/canonical/run.py" \
  --config "$OUT/xylem-full-config.json" query status --json
"$PYTHON" "$PACKAGE/xylem-plugin/canonical/run.py" \
  --config "$OUT/xylem-full-config.json" query search pointMass --json
"$PYTHON" "$PACKAGE/xylem-plugin/canonical/run.py" \
  --config "$OUT/xylem-full-config.json" query dependencies \
  Ctrllib.pointMass_tendsto_zero --depth 1 --json
"$PYTHON" "$PACKAGE/xylem-plugin/canonical/run.py" \
  --config "$OUT/xylem-full-config.json" query dependents \
  Ctrllib.pmM_inv --depth 1 --json
"$PYTHON" "$PACKAGE/xylem-plugin/canonical/run.py" \
  --config "$OUT/xylem-full-config.json" query path \
  Ctrllib.pointMass_tendsto_zero Ctrllib.pmM_inv --json
"$PYTHON" "$PACKAGE/xylem-plugin/canonical/run.py" \
  --config "$OUT/xylem-full-config.json" query context \
  Ctrllib.pointMass_tendsto_zero --limit 5 --edge-scope proof --json
"$PYTHON" "$PACKAGE/xylem-plugin/canonical/run.py" \
  --config "$OUT/xylem-full-config.json" convert render-statement \
  --declaration Ctrllib.pointMass_tendsto_zero --json
"$PYTHON" "$PACKAGE/xylem-plugin/canonical/run.py" \
  --config "$OUT/xylem-full-config.json" mcp
```

The full graph's dependency state is `partial`: captured Ctrllib declarations retain premise records, one captured record has an empty premise list, and 2,347 external stubs are deliberately not expanded. A successful CLI exit or MCP response means the navigation operation ran; it is not a proof-validity or formal-acceptance result.

## Compact fixture warning

The shipped five-record config is deliberately smaller. Its build succeeds, but `query status --json` must report `fresh: false` and an expected warning that these 14 source modules are absent from the compact graph:

```text
Ctrllib.AssumeGuarantee
Ctrllib.CruiseLag
Ctrllib.ElasticAttachment
Ctrllib.Examples.ProofSearchReuse
Ctrllib.GaussianTail
Ctrllib.GiordanoErrata
Ctrllib.KoenigDecomposition
Ctrllib.NominalMPC
Ctrllib.PVSYoung
Ctrllib.ReferenceFrameResidual
Ctrllib.RoverKinematicCompatibility
Ctrllib.SkewCharP
Ctrllib.SphericalHelix
Ctrllib.VaRSubadditivity
```

This warning is expected because only five local declarations are serialized; it is not a failed build and not a no-dependencies result. The same status reports `declaration_dependency_data.status: partial` because external premise stubs and omitted local declarations remain visible without being expanded.
