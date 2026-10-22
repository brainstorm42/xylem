<!-- SPDX-License-Identifier: Apache-2.0 -->
# Planar handbook module slice

This public slice adds eight standalone, user-authored Lean modules that connect a bounded planar two-link endpoint to source-described velocity, wrench, reference-point, and task interfaces. The modules are source-level formal interfaces; they do not include the handbook PDF, figures, textbook prose, or external code.

## Module closure

1. `HandbookPlanarEndpointJacobian` and `HandbookPlanarTwoLink` provide the typed endpoint/Jacobian adapter and the concrete unit-link two-link endpoint.
2. `HandbookPlanarGeometricVelocity`, `HandbookPlanarWrenchDuality`, and `HandbookPlanarReferencePointShift` provide same-point world/body conversion, force-first wrench duality, and the planar point-shift power identity.
3. `HandbookPlanarBodyOffset`, `HandbookPlanarTaskRank`, and `HandbookPlanarOperationalTask` provide the body-fixed offset derivative and the conditional two-coordinate task/rank client.

Each module imports only existing public Ctrllib or Mathlib modules, so a caller can build one endpoint directly from the `ctrllib` project root:

```sh
lake build Ctrllib.HandbookPlanarOperationalTask
```

The umbrella `Ctrllib` target and its 123-module extraction receipt remain the historical public baseline; this standalone slice is not silently folded into those counts. Build the specific target when inspecting these additions.

## Source boundary

The source comments record the Springer Handbook of Robotics, 2nd edition, and Featherstone's *Spatial v2* as source or comparison locators. The formal files state their coordinate order, same-body reference point, rank domain, and assumptions explicitly. They do not claim a general three-dimensional or Denavit–Hartenberg realization, contact mechanics, physical robot behavior, or stability result beyond the named statements.

Focused author and independent-evaluator checks covered each selected endpoint and its downstream client. Those checks are narrower than a fresh full Ctrllib build, extraction, physical validation, or a general claim about the cited sources.
