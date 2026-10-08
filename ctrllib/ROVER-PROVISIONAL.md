<!-- SPDX-License-Identifier: Apache-2.0 -->
# Rover geometry, motion, timing, and clearance

These sixteen modules form a subject navigation route through the included Lean library. Source links lead to each module; theorem links lead to its named declarations. Read each theorem's assumptions before applying it.

The waypoint chain models one-step real-arithmetic motion. Using these results for a floating-point controller requires a separate implementation correspondence argument. The full source-first Air build included every module listed here; physical-system validation was not performed.

## Geometry and kinematics

### [RoverPlanarRotation](Ctrllib/RoverPlanarRotation.lean)

- [`planarRotation_coord0`](Ctrllib/RoverPlanarRotation.lean#L28) — private helper
- [`planarRotation_coord1`](Ctrllib/RoverPlanarRotation.lean#L36) — private helper
- [`planarRotation_coord2`](Ctrllib/RoverPlanarRotation.lean#L43) — private helper
- [`planarRotation_isometry`](Ctrllib/RoverPlanarRotation.lean#L51)
- [`planarRotation_diff_coord0`](Ctrllib/RoverPlanarRotation.lean#L73) — private helper
- [`planarRotation_diff_coord1`](Ctrllib/RoverPlanarRotation.lean#L80) — private helper
- [`planarRotation_diff_coord2`](Ctrllib/RoverPlanarRotation.lean#L87) — private helper
- [`planarRotation_diff_apply_sq_le`](Ctrllib/RoverPlanarRotation.lean#L93) — private helper
- [`planarRotation_operator_diff_le`](Ctrllib/RoverPlanarRotation.lean#L142)
- [`planarRotation_heading_error_le`](Ctrllib/RoverPlanarRotation.lean#L158)
- [`planarRotation_heading_lipschitz_le`](Ctrllib/RoverPlanarRotation.lean#L166)

### [RoverPoseGeometry](Ctrllib/RoverPoseGeometry.lean)

- [`rigid_point_error_le`](Ctrllib/RoverPoseGeometry.lean#L10)
- [`rigid_cover_transport`](Ctrllib/RoverPoseGeometry.lean#L27)
- [`time_lipschitz_point_error`](Ctrllib/RoverPoseGeometry.lean#L40)
- [`rover_pose_body_clearance`](Ctrllib/RoverPoseGeometry.lean#L64)

### [RoverKinematicCompatibility](Ctrllib/RoverKinematicCompatibility.lean)

- [`hasDerivAt_kinematic_product`](Ctrllib/RoverKinematicCompatibility.lean#L24)
- [`kinematic_compatibility_on_Icc`](Ctrllib/RoverKinematicCompatibility.lean#L41)
- [`kinematic_compatibility_error_bound_on_Icc`](Ctrllib/RoverKinematicCompatibility.lean#L81)

## Motion, traces, and waypoints

### [RoverTranslationMotion](Ctrllib/RoverTranslationMotion.lean)

- [`affine_segment_bound`](Ctrllib/RoverTranslationMotion.lean#L25) — private helper
- [`two_segment_affine_lipschitz`](Ctrllib/RoverTranslationMotion.lean#L40)
- [`one_knot_lipschitz_of_segment_bounds`](Ctrllib/RoverTranslationMotion.lean#L115)
- [`finite_piecewise_affine_lipschitz`](Ctrllib/RoverTranslationMotion.lean#L161)
- [`piecewise_affine_translation_lipschitz`](Ctrllib/RoverTranslationMotion.lean#L198)
- [`piecewise_affine_heading_lipschitz`](Ctrllib/RoverTranslationMotion.lean#L206)

### [RoverRelativeTrace](Ctrllib/RoverRelativeTrace.lean)

- [`relative_displacement_dist`](Ctrllib/RoverRelativeTrace.lean#L12)
- [`tracePoint_sub`](Ctrllib/RoverRelativeTrace.lean#L18) — private helper
- [`two_moving_discs_trace_certificate`](Ctrllib/RoverRelativeTrace.lean#L25)

### [RoverStepResidual](Ctrllib/RoverStepResidual.lean)

- [`observed_displacement_norm_le`](Ctrllib/RoverStepResidual.lean#L13)
- [`observed_displacement_norm_le_ideal`](Ctrllib/RoverStepResidual.lean#L32)
- [`reconstructed_trajectory_error_le`](Ctrllib/RoverStepResidual.lean#L47)
- [`reconstructed_disc_clearance`](Ctrllib/RoverStepResidual.lean#L81)
- [`reconstructed_displacement_le`](Ctrllib/RoverStepResidual.lean#L108)
- [`residual_disc_step_safe`](Ctrllib/RoverStepResidual.lean#L119)
- [`waypoint_residual_disc_step_safe`](Ctrllib/RoverStepResidual.lean#L137)

### [RoverWaypointModel](Ctrllib/RoverWaypointModel.lean)

- [`waypointVelocity_moving_formula`](Ctrllib/RoverWaypointModel.lean#L18)
- [`waypointVelocity_norm_le`](Ctrllib/RoverWaypointModel.lean#L31)
- [`waypointVelocity_step_fraction`](Ctrllib/RoverWaypointModel.lean#L45)
- [`waypoint_affine_motion_bound`](Ctrllib/RoverWaypointModel.lean#L63)

## Timing and sampled observation

### [RoverClock](Ctrllib/RoverClock.lean)

- [`timestamp_error_decomposition`](Ctrllib/RoverClock.lean#L14)
- [`clocked_delivery_bound`](Ctrllib/RoverClock.lean#L34)
- [`same_clock_delivery_bound`](Ctrllib/RoverClock.lean#L49)

### [RoverAsyncClearance](Ctrllib/RoverAsyncClearance.lean)

- [`rover_async_clearance_lower_bound`](Ctrllib/RoverAsyncClearance.lean#L29)
- [`rover_family_async_clearance_lower_bound`](Ctrllib/RoverAsyncClearance.lean#L58)
- [`rover_body_async_clearance`](Ctrllib/RoverAsyncClearance.lean#L87)

### [RoverSampledClearance](Ctrllib/RoverSampledClearance.lean)

- [`rover_sampled_clearance_lower_bound`](Ctrllib/RoverSampledClearance.lean#L29)
- [`rover_family_sampled_clearance_lower_bound`](Ctrllib/RoverSampledClearance.lean#L59)
- [`rover_sampled_clearance_safe`](Ctrllib/RoverSampledClearance.lean#L82)
- [`rover_body_clearance_of_sample_cover`](Ctrllib/RoverSampledClearance.lean#L103)
- [`rover_body_sampled_clearance`](Ctrllib/RoverSampledClearance.lean#L122)

## Clearance and trace certificates

### [RoverIntervalClearance](Ctrllib/RoverIntervalClearance.lean)

- [`timestamp_error_over_future_interval`](Ctrllib/RoverIntervalClearance.lean#L15)
- [`rover_static_obstacle_interval_clearance`](Ctrllib/RoverIntervalClearance.lean#L35)
- [`clearance_margin_iff_horizon`](Ctrllib/RoverIntervalClearance.lean#L96)

### [RoverHeadingClearance](Ctrllib/RoverHeadingClearance.lean)

- [`rover_heading_rectangle_interval_clearance`](Ctrllib/RoverHeadingClearance.lean#L14)
- [`rover_finite_motion_rectangle_clearance`](Ctrllib/RoverHeadingClearance.lean#L57)

### [RoverConcreteClearance](Ctrllib/RoverConcreteClearance.lean)

- [`rover_rectangle_disc_interval_clearance`](Ctrllib/RoverConcreteClearance.lean#L15)

### [RoverConcreteCovers](Ctrllib/RoverConcreteCovers.lean)

- [`scalar_cell_cover`](Ctrllib/RoverConcreteCovers.lean#L16) — private helper
- [`scalar_cell_cover_zero`](Ctrllib/RoverConcreteCovers.lean#L77) — private helper
- [`scalar_cell_centre_cover`](Ctrllib/RoverConcreteCovers.lean#L87)
- [`rect_cover_exists`](Ctrllib/RoverConcreteCovers.lean#L105) — private helper
- [`planar_rectangle_cell_centre_cover`](Ctrllib/RoverConcreteCovers.lean#L133)
- [`planar_rectangle_cell_centre_lever_arm`](Ctrllib/RoverConcreteCovers.lean#L144)
- [`centred_disc_singleton_cover`](Ctrllib/RoverConcreteCovers.lean#L189)

### [RoverWaypointClearance](Ctrllib/RoverWaypointClearance.lean)

- [`waypoint_disc_step_clearance`](Ctrllib/RoverWaypointClearance.lean#L13)
- [`waypoint_disc_step_safe`](Ctrllib/RoverWaypointClearance.lean#L45)

### [RoverTraceCertificate](Ctrllib/RoverTraceCertificate.lean)

- [`point2_sq_norm_sub`](Ctrllib/RoverTraceCertificate.lean#L8)
- [`normalized_time_mem_unit_interval`](Ctrllib/RoverTraceCertificate.lean#L15)
- [`quad_min_of_certificate`](Ctrllib/RoverTraceCertificate.lean#L23) — private helper
- [`planar_segment_disc_trace_certificate`](Ctrllib/RoverTraceCertificate.lean#L51)
