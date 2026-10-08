/-
Sampled two-rover clearance certificate.

The positions are points in a common Euclidean frame with metre-valued
coordinates. The theorem transfers a separation certificate on stale delivered
points to actual target-time clearance. It does not select a rover controller,
establish pose-estimator error bounds, or identify a simulator trajectory with
a plant.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Ctrllib.InspectionMargin
import Ctrllib.ReferenceTiming

namespace Ctrllib

/-! A pair of tracked points, one from each rover, is enough for the local
certificate. A whole rover body or arm is represented by instantiating the
point theorem over its point index set; the family version keeps coverage
explicit. -/

/-- A stale delivered separation implies actual target-time clearance.

`pDelivered` and `qDelivered` are measurements or cached poses available at
`τ`; `p` and `q` are the corresponding actual point trajectories. The
constants `εp`, `εq` have length units, while `Lp`, `Lq` have length/time units
and `h` has time units. The Euclidean-space type fixes three coordinate
 dimensions and uses the Euclidean norm rather than the default sup norm on an
 unstructured function. -/
theorem rover_sampled_clearance_lower_bound
    {S : Set ℝ}
    {p q : ℝ → EuclideanSpace ℝ (Fin 3)}
    {pDelivered qDelivered : EuclideanSpace ℝ (Fin 3)}
    {Lp Lq : NNReal} {εp εq δ h t τ : ℝ}
    (hp : LipschitzOnWith Lp p S)
    (hq : LipschitzOnWith Lq q S)
    (htau : τ ∈ S) (htarget : t ∈ S)
    (hpDelivered : dist pDelivered (p τ) ≤ εp)
    (hqDelivered : dist qDelivered (q τ) ≤ εq)
    (ht : |t - τ| ≤ h)
    (hsep : δ ≤ dist pDelivered qDelivered) :
    δ - εp - εq - ((Lp : ℝ) + (Lq : ℝ)) * h ≤
      dist (p t) (q t) := by
  have hpTarget' : dist pDelivered (p t) ≤ εp + (Lp : ℝ) * h :=
    dist_delivered_to_target_on_le hp htau htarget hpDelivered ht
  have hqTarget' : dist qDelivered (q t) ≤ εq + (Lq : ℝ) * h :=
    dist_delivered_to_target_on_le hq htau htarget hqDelivered ht
  have hpTarget : dist (p t) pDelivered ≤ εp + (Lp : ℝ) * h := by
    simpa [dist_comm] using hpTarget'
  have hqTarget : dist (q t) qDelivered ≤ εq + (Lq : ℝ) * h := by
    simpa [dist_comm] using hqTarget'
  have heroded := dist_actual_ge_dist_nominal_sub
    pDelivered (p t) qDelivered (q t) hpTarget hqTarget
  linarith

/-- Uniform version for indexed point sets on the two rover bodies. The
represented point sets and their nominal stale separation remain explicit, so
this is a contract for a later coverage argument rather than a body-level
collision theorem. -/
theorem rover_family_sampled_clearance_lower_bound
    {I J : Type*} {S : Set ℝ}
    {p : I → ℝ → EuclideanSpace ℝ (Fin 3)}
    {q : J → ℝ → EuclideanSpace ℝ (Fin 3)}
    {pDelivered : I → EuclideanSpace ℝ (Fin 3)}
    {qDelivered : J → EuclideanSpace ℝ (Fin 3)}
    {Lp Lq : NNReal} {εp εq δ h t τ : ℝ}
    (hp : ∀ i, LipschitzOnWith Lp (p i) S)
    (hq : ∀ j, LipschitzOnWith Lq (q j) S)
    (htau : τ ∈ S) (htarget : t ∈ S)
    (hpDelivered : ∀ i, dist (pDelivered i) (p i τ) ≤ εp)
    (hqDelivered : ∀ j, dist (qDelivered j) (q j τ) ≤ εq)
    (ht : |t - τ| ≤ h)
    (hsep : ∀ i j, δ ≤ dist (pDelivered i) (qDelivered j)) :
    ∀ i j, δ - εp - εq - ((Lp : ℝ) + (Lq : ℝ)) * h ≤
      dist (p i t) (q j t) := by
  intro i j
  exact rover_sampled_clearance_lower_bound
    (hp i) (hq j) htau htarget (hpDelivered i) (hqDelivered j) ht (hsep i j)

/-- Radius-specialized safety form: if the sampled delivered separation margin
 dominates uncertainty and intersample-motion erosion by `R`, then every
 admitted target time has actual point separation at least `R`. -/
theorem rover_sampled_clearance_safe
    {S : Set ℝ}
    {p q : ℝ → EuclideanSpace ℝ (Fin 3)}
    {pDelivered qDelivered : EuclideanSpace ℝ (Fin 3)}
    {Lp Lq : NNReal} {εp εq δ h t τ R : ℝ}
    (hp : LipschitzOnWith Lp p S)
    (hq : LipschitzOnWith Lq q S)
    (htau : τ ∈ S) (htarget : t ∈ S)
    (hpDelivered : dist pDelivered (p τ) ≤ εp)
    (hqDelivered : dist qDelivered (q τ) ≤ εq)
    (ht : |t - τ| ≤ h)
    (hsep : δ ≤ dist pDelivered qDelivered)
    (hmargin : R ≤ δ - εp - εq - ((Lp : ℝ) + (Lq : ℝ)) * h) :
    R ≤ dist (p t) (q t) := by
  exact le_trans hmargin (rover_sampled_clearance_lower_bound
    hp hq htau htarget hpDelivered hqDelivered ht hsep)

/-- Finite or otherwise indexed samples certify whole-body clearance only when
covering radii are supplied. `Bp` and `Bq` are arbitrary represented body
sets in the same Euclidean three-space; the coverage hypotheses are the
explicit bridge from sampled points to all body points. -/
theorem rover_body_clearance_of_sample_cover
    {I J : Type*}
    {Bp Bq : Set (EuclideanSpace ℝ (Fin 3))}
    {p : I → EuclideanSpace ℝ (Fin 3)}
    {q : J → EuclideanSpace ℝ (Fin 3)}
    {ρp ρq δ : ℝ}
    (hpCover : ∀ x ∈ Bp, ∃ i, dist x (p i) ≤ ρp)
    (hqCover : ∀ y ∈ Bq, ∃ j, dist y (q j) ≤ ρq)
    (hsep : ∀ i j, δ ≤ dist (p i) (q j)) :
    ∀ x ∈ Bp, ∀ y ∈ Bq, δ - ρp - ρq ≤ dist x y := by
  intro x hx y hy
  obtain ⟨i, hxi⟩ := hpCover x hx
  obtain ⟨j, hyj⟩ := hqCover y hy
  have heroded := dist_actual_ge_dist_nominal_sub
    (p i) x (q j) y hxi hyj
  linarith [hsep i j]

/-- Delivered sample separation, motion/estimation budgets and target-time
body covers compose into a whole-body distance bound. Covers must hold at t. -/
theorem rover_body_sampled_clearance
    {I J : Type*} {S : Set ℝ}
    {p : I → ℝ → EuclideanSpace ℝ (Fin 3)}
    {q : J → ℝ → EuclideanSpace ℝ (Fin 3)}
    {pDelivered : I → EuclideanSpace ℝ (Fin 3)}
    {qDelivered : J → EuclideanSpace ℝ (Fin 3)}
    {Bp Bq : Set (EuclideanSpace ℝ (Fin 3))}
    {Lp Lq : NNReal} {εp εq δ h t τ ρp ρq : ℝ}
    (hp : ∀ i, LipschitzOnWith Lp (p i) S)
    (hq : ∀ j, LipschitzOnWith Lq (q j) S)
    (htau : τ ∈ S) (htarget : t ∈ S)
    (hpDelivered : ∀ i, dist (pDelivered i) (p i τ) ≤ εp)
    (hqDelivered : ∀ j, dist (qDelivered j) (q j τ) ≤ εq)
    (ht : |t - τ| ≤ h)
    (hsep : ∀ i j, δ ≤ dist (pDelivered i) (qDelivered j))
    (hpcover : ∀ x ∈ Bp, ∃ i, dist x (p i t) ≤ ρp)
    (hqcover : ∀ y ∈ Bq, ∃ j, dist y (q j t) ≤ ρq) :
    ∀ x ∈ Bp, ∀ y ∈ Bq,
      δ - εp - εq - ((Lp : ℝ) + (Lq : ℝ)) * h - ρp - ρq ≤ dist x y := by
  apply rover_body_clearance_of_sample_cover hpcover hqcover
  exact rover_family_sampled_clearance_lower_bound
    hp hq htau htarget hpDelivered hqDelivered ht hsep

end Ctrllib

#print axioms Ctrllib.rover_sampled_clearance_lower_bound
#print axioms Ctrllib.rover_family_sampled_clearance_lower_bound
#print axioms Ctrllib.rover_sampled_clearance_safe
#print axioms Ctrllib.rover_body_clearance_of_sample_cover
#print axioms Ctrllib.rover_body_sampled_clearance
