# Notices and license scope

The top-level `LICENSE` is the standard Apache-2.0 text. The grant covers package-local files carrying an `SPDX-License-Identifier: Apache-2.0` label or equivalent metadata, the canonical user-owned Xylem/BrickConverter runtime and runner/configuration, and the adapted fixture whose upstream license is retained.

The included `openai/math` fixture is adapted from revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. Its Apache-2.0 license text is retained at `examples/compact-bounds/third_party/openai-math/LICENSE`, and attribution at the adjacent `NOTICE.md`. That upstream notice applies to the fixture.

The instruction skills, authored explanations, capture projections, and example evidence are AI-assisted local records within the scoped grant. Runtime conceptual attribution is recorded in `canonical/ORIGIN.md`. External PyYAML, MCP SDK, Lean, Mathlib, other dependencies, user-supplied capture tools and datasets retain their own terms. Direct PyYAML 6.0.3 and MCP 2.2.0 metadata was observed as MIT.

The private percolation candidate retains the upstream `formal-math` `LICENSE`
and `NOTICE` under `examples/percolation-e2e/upstream/` and records the exact
source revision in its source and reproducibility manifests. Those notices
cover the upstream source snapshot; cited mathematical works and Lean/Mathlib
dependencies remain separate works under their own terms. The generated
capture, audit, index, and navigation artifacts are included as scoped local
records and do not grant permission to publish the upstream corpus or claim
semantic equivalence beyond the checked formal declarations.
