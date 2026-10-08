<!-- SPDX-License-Identifier: Apache-2.0 -->
# Start here — Xylem and Ctrllib

The current package combines the CompactBounds explanation and the Ctrllib source-first navigation example. Its authoritative inventory is [corrected-release-manifest.json](../provenance/corrected-release-manifest.json). Earlier manifests and receipts describe their named predecessors.

1. [README.md](README.md): isolated Python installation and CompactBounds first use.
2. [Ctrllib example](examples/ctrllib-e2e/README.md): exact statement, bounded context,
   and a dependency path through genuine captured relationships.
3. [Point-mass explanation](examples/ctrllib-e2e/vault/PointMassComFlow.md): the
   equations, assumptions, convergence mechanism, and inverse obligation.
4. [CompactBounds explanation](examples/compact-bounds/explanation-hS.md): compact
   coordinate-image union, retained interfaces, and evidence limits.
5. [Correction check](../provenance/CORRECTION-CHECK.md): scoped changes, tests, and
   fresh explanation review.
6. [Air verification](../provenance/AIR-CONSUMER-CHECK.md) and
   [public bootstrap](examples/ctrllib-e2e/BOOTSTRAP-PUBLIC-MACOS.md): the passed
   consumer install and full 123-module regeneration.

`canonical/mcp.sh` selects CompactBounds. For Ctrllib, use the explicitly configured existing runner and host example in the Ctrllib README. Windows execution, separate Lean 4.34.1 CompactBounds helper replay, helper minimization, and full decomposition remain untested or outside this scope.
