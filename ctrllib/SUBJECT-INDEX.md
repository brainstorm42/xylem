<!-- SPDX-License-Identifier: Apache-2.0 -->
# Ctrllib subject index

This is a navigation view over included source modules. A direct Brick entry means only that the current Brick README manifest names the module. It does not add a theorem, proof, acceptance decision, or physical correspondence.

## Impedance, energy, and mechanics

- `matrix_impedance_stability`: `LinearOperatorFlow`, `MatrixImpedance`.
- `forced_impedance_balance`: `ForcedImpedance`, `IntegratedEnergy`.
- `manipulator_energy_balance`: `ManipulatorEnergy`.
- `koenig_decomposition`: `KoenigDecomposition`; kinetic-energy decomposition.
- `elastic_attachment_balance`: `ElasticAttachment`.

## Manipulator kinematics and tracking

- `circumcentroidal_correction`: `CircumcentroidalCorrection`,
  `CircumcentroidalRank`.
- `circumcentroidal_passivity`: `CircumcentroidalPassivity`.
- `circumcentroidal_update_rank`: `CircumcentroidalRank`.
- `nullspace_projector_lift`: `KernelLift`, `NullspaceMotion`.
- `seven_dof_decoupling`: `SevenDofDecoupling`.
- `seven_dof_nullspace_damping`: `SevenDof`.
- `seven_dof_passivity`: `SevenDof`.
- `seven_dof_task_block`: `SevenDofTaskBlock`.
- `tracking_cascade`, `tracking_cross_term`, `tracking_dissipation`,
  `tracking_jacobian`, `tracking_steady_lag`, `tracking_strict_bound`, and
  `tracking_strict_bound_weighted`: see the exact module map for direct
  current-manifest relations and keep each interface hypothesis visible.

## Weighted allocation

The generic modules `WeightedRightInverse`, `EqualityConstrainedQuadratic`, `WeightedAccelerationCompatibility`, `AllocationRealizationError`, and `AllocationSignConvention` are included as typed algebraic interfaces. These modules provide the weighted-allocation subject route.

## Risk and statistical interfaces

The included CVaR, confidence, tail, estimation, and Bernoulli modules are indexed under their mathematical subjects. Direct manifest relations are listed in [`MODULE-BRICK-MAP.json`](MODULE-BRICK-MAP.json).

## Rover geometry, timing, and clearance

Explore all sixteen modules and their named theorems in [the rover subject guide](ROVER-PROVISIONAL.md), organized into geometry, motion, timing, and clearance. This subject organization is a navigation aid.
