<!-- SPDX-License-Identifier: Apache-2.0 -->
# Architecture

`xylem-plugin/` contains the Python graph navigator, CLI/MCP runner, BrickConverter, and two explanation examples. `ctrllib/` is the independent Lean source library with its pinned Lake configuration and extractor. The source-first runner builds all 123 supplied modules using explicit dependency paths and writes generated output into a caller-selected external directory.

A declaration capture feeds graph navigation and statement rendering. Captured proof/type relationships, module imports, declaration containment, and authored explanation pointers are distinct relationships. A graph edge or a readable equation is not a proof-equivalence result.

The CompactBounds explanation describes compactness and positivity of a union of coordinate images. The Ctrllib example explains a damped point-mass flow and connects its convergence theorem to the inverse obligation it uses. The [Ctrllib subject index](ctrllib/SUBJECT-INDEX.md) also provides rover geometry, timing, motion, and clearance theorem routes.
