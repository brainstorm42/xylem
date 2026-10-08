<!-- SPDX-License-Identifier: Apache-2.0 -->
# Contents, evidence, and supported use

Xylem provides graph navigation through CLI and foreground MCP. BrickConverter renders captured statements while retaining exact binders and text. Ctrllib supplies Lean sources, pinned dependencies, an extractor, and a public source-first regeneration procedure. The [subject index](ctrllib/SUBJECT-INDEX.md) and [rover theorem guide](ctrllib/ROVER-PROVISIONAL.md) organize the mathematics.

## Current contents

| Content | Count | Route |
| --- | ---: | --- |
| Ctrllib source modules | 123 | [Source library](ctrllib/README.md) |
| Umbrella imports | 122 | [Ctrllib.lean](ctrllib/Ctrllib.lean) |
| Separately importable module | 1 | [AllocationSignConvention](ctrllib/Ctrllib/AllocationSignConvention.lean) |
| Rover modules | 16 | [Geometry, motion, timing, and clearance](ctrllib/ROVER-PROVISIONAL.md) |
| Rover source declaration links | 68 | [Source declaration guide](ctrllib/ROVER-PROVISIONAL.md) |
| CompactBounds parent-statement binders | 5 | [Explanation](xylem-plugin/examples/compact-bounds/explanation-hS.md) |
| Point-mass convergence-statement binders | 7 | [Explanation](xylem-plugin/examples/ctrllib-e2e/vault/PointMassComFlow.md) |

[PVSYoung.lean](ctrllib/Ctrllib/PVSYoung.lean) adapts an attributed Young inequality statement from NASALib's `complex_integration/young.pvs` and cites Berberian's *Fundamentals of Real Analysis*, §3.1.3. Its precise source credit is in [NOTICE.md](ctrllib/NOTICE.md).

## Compact fixtures — current targeted checks

| Measure | CompactBounds | Ctrllib compact fixture |
| --- | ---: | ---: |
| Captured local declarations | 1 | 5 |
| Indexed declarations, including external stubs | 1 | 250 |
| Indexed module nodes | 1 | 109 |
| Authored explanation-page graph nodes | 0 | 1 |
| DECLARED_IN edges | 1 | 5 |
| IMPORTS edges | 0 | 140 |
| USES_IN_TYPE edges | 0 | 142 |
| USES_IN_PROOF edges | 0 | 434 |
| PAIRED_WITH edges | 0 | 1 |
| Declaration dependency-data status | `unavailable` | `partial` |
| Selected-input freshness | `true` | `false` — partial source coverage |
| Repeated CLI and MCP status | stable | stable |

The Ctrllib fixture is a selected navigation example. Full regeneration provides complete local module coverage. CompactBounds dependency-data status means its projection supplies no premise records; zero indexed edges do not assert a dependency-free theorem.

## Full public source-first Air run

| Measure | Result |
| --- | ---: |
| Source modules compiled and covered by extraction | 123 |
| Captured local declarations | 808 |
| Extraction errors | 0 |
| Formatted capture bytes | 892231751 |
| Source build time, seconds | 460.371 |
| Extraction time, seconds | 115.106 |
| Indexed module nodes | 123 |
| Indexed declarations, including external stubs | 3155 |
| External declaration stubs | 2347 |
| IMPORTS edges | 140 |
| USES_IN_TYPE edges | 26293 |
| USES_IN_PROOF edges | 68381 |
| DECLARED_IN edges | 808 |
| PAIRED_WITH edges | 1 |
| Selected-input freshness | `true` |
| Dependency-data status | `partial` — external stubs retain their own data status |
| Repeated CLI and MCP status | stable |

The [verification receipt](provenance/air-consumer-verification.json) records dependency revisions and results. This full run tested the same proof sources and pins supplied here; current converter-label, freshness-advice, and explanation corrections received separate targeted checks.

## Public percolation example

The public v0.1.0 package carries the pinned `formal-math` percolation snapshot,
its two separately elaborated Lean surfaces, the captured declaration and premise
projection, the source-module and trace-backed navigation layers, and the
replayable reconstruction clients. The capture indexes 23,545 declarations;
the machine index records 228 compiler-derived source regions, 13 trace-backed
subargument steps, and authored component metadata. Start with the [percolation
guide](xylem-plugin/examples/percolation-e2e/README.md) and [integration
provenance](provenance/PERCOLATION-INTEGRATION.md). This release is public;
source rebuilding and broader verification claims remain separately scoped below.

## Environment and check scope

| Component or check | Version or result | Scope |
| --- | --- | --- |
| Air OS | macOS 26.6.2 arm64 | Consumer installation and public regeneration |
| Python | 3.12.13 | Isolated venv; direct pins installed |
| PyYAML / MCP | 6.0.3 / 2.2.0 | Declared direct runtime pins |
| Ctrllib Lean / Lake | 4.34.0 / 5.0.0-src+293d5d0 | Public source-first build and extraction |
| CompactBounds helper evidence Lean | 4.34.1 | Recorded checking summaries; fresh helper replay untested |
| Current regression scripts | 6 passed | Includes 7 targeted mathematical/interface/converter/freshness cases |
| Explanation review | independent PASS | Source, mathematics, interfaces; prose review rather than proof certification |
| Statement rendering | `not_assessed` acceptance | Complete captured binders and exact-text fallback |
| Converter round trip | normalized IR equality | Parser/render/parser comparison |
| Converter declaration check | existing declaration | Rendered output is hashed; formal checking of that output is unassessed |

See [public bootstrap](xylem-plugin/examples/ctrllib-e2e/BOOTSTRAP-PUBLIC-MACOS.md), [full regeneration](xylem-plugin/examples/ctrllib-e2e/REGENERATE-FULL.md), and [current verification](provenance/CORRECTION-CHECK.md).

## Limitations

Navigation and notation rendering do not establish theorem equivalence, full
theorem decomposition, or physical-system validation. The waypoint model uses
real arithmetic; applying it to floating-point software requires a separate
correspondence argument. Windows and operating-system prerequisite installation
remain untested.

The percolation source-module regions are source partitions, not mathematical
subargument boundaries. Trace-backed relations are structural evidence from the
captured elaborated terms; opaque theorem bodies remain opaque, external
constants remain stubs, and the authored role prose remains subject to human
review. The Solution and Challenge surfaces are indexed separately because
their names collide; the Challenge surface retains its two deliberate `sorry`
placeholders. The exact formal endpoint is recorded without promoting it to a
broader continuity or literature-equivalence claim.

The committed capture and SQLite index are available after Git LFS hydration.
A fresh source rebuild downloads the pinned Lean/Mathlib cache with `lake exe
cache get` and may build dependencies when the cache is absent; the packaged
evidence therefore supports inspection and replay of the recorded artifacts but
does not promise an offline source rebuild. Source credits and licensing are in
[Ctrllib notices](ctrllib/NOTICE.md), [Xylem notices](xylem-plugin/NOTICE.md),
and the [percolation integration record](provenance/PERCOLATION-INTEGRATION.md).
