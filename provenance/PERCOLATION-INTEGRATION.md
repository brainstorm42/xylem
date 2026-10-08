<!-- SPDX-License-Identifier: Apache-2.0 -->
# Percolation integration provenance

This private v0.1.0 release incorporates the percolation candidate from frozen
Xylem revision `11ec3674ac8d5170b0add8d50a4631c3bbb50e5d`. The candidate was
assembled from the validated LFS archive below; the active development checkout
and its later freshness work were not used.

| Candidate receipt | Value |
| --- | --- |
| Validated archive | `xylem-private-candidate-final-lfs.tar.gz` |
| Archive SHA-256 | `88a8d046499d7623469b5546db66924161101c6f72997c3902e40d1350a2a8c6` |
| Archive bytes | `327507248` |
| Regular-file members | `553` — 552 payload files plus the manifest sidecar |
| Release identity | v0.1.0; private review candidate |

## What the package carries

The example includes the pinned `anthropics/formal-math` source snapshot at
revision `795efb86f191735c5481675763537cfb4ff37e55`, its retained upstream
`LICENSE` and `NOTICE`, both separately elaborated Lean surfaces, the captured
declarations and premise edges, the import graph, component/index manifests,
the compact proof trace and boundary trace, the SQLite query index, and the
reconstruction clients. The source and artifact manifests retain byte counts
and SHA-256 values; the reproducibility receipt records the checked toolchain,
build, extraction, replay, and audit results.

The supported first-use route is [the percolation guide](../xylem-plugin/examples/percolation-e2e/README.md): hydrate LFS, restore the committed SQLite
archive, then use the repository-relative CLI/MCP commands there. The root
[example index](../xylem-plugin/examples/INDEX.md) and the plugin
[release scope](../xylem-plugin/RELEASE-SCOPE.md) provide the corresponding
navigation and review boundary.

## Storage and reproducibility boundary

The three large hydrated artifacts are tracked with Git LFS:

- `components-generated.json` — 859142850 bytes;
- `proof-trace.json.gz` — 188239134 bytes;
- `xylem.db.gz` — 115766644 bytes.

Their LFS pointers belong in Git history while the hydrated objects must be
available from the repository's LFS service for a reader to restore the index.
The archive itself is not an offline rebuild promise: a fresh source build
downloads the pinned Lean/Mathlib cache with `lake exe cache get` and may build
dependencies from the pinned Lake manifest when the cache is absent. The
committed artifacts remain usable for inspection and query after hydration.

The upstream source snapshot is retained under its own license and notice.
The generated capture, audits, index, and navigation records are scoped local
artifacts; they do not grant permission to redistribute the upstream corpus or
claim a stronger semantic result than the recorded checks establish.

The final assembly receipt is kept outside the hashed package inventory so it
can record the release commit, manifest digest, LFS hydration, and smoke-check
results without creating a self-hash cycle. The package manifest remains the
machine-readable inventory for every tracked payload file except itself.

## Assembly-path normalization

The capture tools originally recorded the producer checkout and temporary
capture locations in machine-generated receipt fields. During final assembly,
those path strings were rewritten to package-relative names such as `upstream`
and `data/declarations.json.gz`; the `merged_json` field explicitly identifies
its intermediate as not shipped. The source repository, frozen source revision,
capture counts, artifact byte counts, and artifact SHA-256 values were retained;
only path spelling and the corresponding receipt references to the normalized
manifest bytes/digests changed. This is a packaging normalization step, not a
new source capture or rebuild.
