# Ctrllib notices

The scoped Apache-2.0 package grant covers authorized Ctrllib overlay material. Per-source notices and attributed sources are retained below.

The following source notices are preserved exactly in their Lean files:

- `Ctrllib/MovingReferenceFlow.lean` — Copyright (c) 2026 Antonia Hoffman. All rights reserved.
- `Ctrllib/ReferenceAdmissibility.lean` — Copyright (c) 2026 Antonia Hoffman. All rights reserved.
- `Ctrllib/ReferenceCalculus.lean` — Copyright (c) 2026 Antonia Hoffman. All rights reserved.
- `Ctrllib/ReferenceTiming.lean` — Copyright (c) 2026 Antonia Hoffman. All rights reserved.
- `Ctrllib/RoverKinematicCompatibility.lean` — Copyright (c) 2026 Antonia Hoffman. All rights reserved.
- `Ctrllib/SphericalHelix.lean` — Copyright (c) 2026 Antonia Hoffman. All rights reserved.

`Ctrllib/PVSYoung.lean` is an attributed statement adapter. It identifies NASALib `complex_integration/young.pvs` at revision `56dab1977c7889b69698227b7b883a188936597c` and cites S. K. Berberian, *Fundamentals of Real Analysis* (Springer, 1991), §3.1.3.

The standalone `HandbookPlanarEndpointJacobian`, `HandbookPlanarTwoLink`, `HandbookPlanarGeometricVelocity`, `HandbookPlanarWrenchDuality`, `HandbookPlanarReferencePointShift`, `HandbookPlanarBodyOffset`, `HandbookPlanarTaskRank`, and `HandbookPlanarOperationalTask` modules are user-authored additions. Their source comments cite the Springer Handbook of Robotics, 2nd edition, and R. Featherstone's *Spatial v2* as source or comparison locators; those works are not included. The modules state their planar conventions and do not copy textbook prose, figures, or source code.

`Ctrllib/ProdNorm.lean` is a user-authored Mathlib-only helper included with an explicit Apache-2.0 source notice. It contains no copied textbook, paper, or third-party source text.

The selected startup-ramp source closure is included as Ctrllib overlay material. Its authored adapter files retain their Apache-2.0 notices; the closure also preserves the existing project notices and dependency terms. `QuadraticForm.lean` identifies NASALib as a mathematical source and explicitly states that it does not copy the PVS representation. `ControllerScalarPilotV2.lean` is an additive interval-certificate client over that closure; it is included as a bounded study artifact, not as a general automated-bound or physical-control claim.

Mathlib and the other Lake dependencies use the revisions in `lake-manifest.json` and retain their own license terms.
