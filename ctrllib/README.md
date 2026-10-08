<!-- SPDX-License-Identifier: Apache-2.0 -->
# Ctrllib source overlay

This directory contains 123 Lean source modules. The umbrella imports 122; `Ctrllib.AllocationSignConvention` is available as a standalone module.

## Use

With Lean 4.34.0 and the external pinned Lake dependency closure available:

```sh
set -e
lake build Ctrllib
extract_dir="$(mktemp -d "${TMPDIR:-/tmp}/ctrllib-extract.XXXXXX")"
extract_json="$extract_dir/declarations.json"
if lake exe extract >"$extract_json"; then
  printf 'extraction output: %s\n' "$extract_json"
else
  status=$?
  printf 'extractor exited with status %s; stdout retained at %s; no extraction result is claimed\n' \
    "$status" "$extract_json" >&2
  exit "$status"
fi
```

`lake exe extract` emits declaration JSON to stdout. The [public source-first procedure](../xylem-plugin/examples/ctrllib-e2e/REGENERATE-FULL.md) compiled all 123 modules on macOS arm64 and extracted 808 declarations with exact coverage. The ordinary Lake entrypoint above was not run in that test; inspect dependency hooks before execution. The temporary output directory preserves the extractor exit status and existing output files.

## Read the scope

- [`SUBJECT-INDEX.md`](SUBJECT-INDEX.md) — human subject navigation and direct
  Brick mappings.
- [`ROVER-PROVISIONAL.md`](ROVER-PROVISIONAL.md) — the 16-module Rover
  subject collection with source and theorem links.
- [`MODULE-BRICK-MAP.json`](MODULE-BRICK-MAP.json) — exact current manifest
  relations.
- [`IMPORT-CLOSURE.json`](IMPORT-CLOSURE.json) — current module and import counts.
- [`NOTICE.md`](NOTICE.md) — source notices, attribution, and dependency scope.

Use the mathematical source files to inspect exact theorem statements and assumptions, and follow the subject routes to related results.
