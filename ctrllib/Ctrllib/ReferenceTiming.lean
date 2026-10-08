/-
Copyright (c) 2026 Antonia Hoffman. All rights reserved.
Authors: Antonia Hoffman
-/
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Basic.NNReal.Defs

/-!
# Timing and delivery-error bounds

These lemmas transfer a delivery error at a timestamp `τ` to a target value at
time `t` under an explicit Lipschitz bound. The paired corollary treats the
velocity and acceleration signals independently; it does not infer a jerk
bound or derivative coherence from either Lipschitz premise.
-/

namespace Ctrllib

section ReferenceTiming

variable {E : Type*} [PseudoMetricSpace E]

/-- A delivery error at `τ` and a timing error from `τ` to `t` combine by the
triangle inequality and a global Lipschitz bound. -/
theorem dist_delivered_to_target_le
    {f : ℝ → E} {y : E} {L : NNReal} {ε h t τ : ℝ}
    (hf : LipschitzWith L f) (hy : dist y (f τ) ≤ ε)
    (ht : |t - τ| ≤ h) :
    dist y (f t) ≤ ε + (L : ℝ) * h := by
  calc
    dist y (f t) ≤ dist y (f τ) + dist (f τ) (f t) := dist_triangle _ _ _
    _ ≤ ε + (L : ℝ) * dist τ t := add_le_add hy (hf.dist_le_mul _ _)
    _ ≤ ε + (L : ℝ) * h := by
      gcongr
      simpa [Real.dist_eq, abs_sub_comm] using ht

/-- The same delivery estimate restricted to a set of admissible timestamps. -/
theorem dist_delivered_to_target_on_le
    {S : Set ℝ} {f : ℝ → E} {y : E} {L : NNReal} {ε h t τ : ℝ}
    (hf : LipschitzOnWith L f S) (hτ : τ ∈ S) (ht' : t ∈ S)
    (hy : dist y (f τ) ≤ ε) (ht : |t - τ| ≤ h) :
    dist y (f t) ≤ ε + (L : ℝ) * h := by
  calc
    dist y (f t) ≤ dist y (f τ) + dist (f τ) (f t) := dist_triangle _ _ _
    _ ≤ ε + (L : ℝ) * dist τ t := add_le_add hy (hf.dist_le_mul τ hτ t ht')
    _ ≤ ε + (L : ℝ) * h := by
      gcongr
      simpa [Real.dist_eq, abs_sub_comm] using ht

variable {V : Type*} [NormedAddCommGroup V]

/-- Simultaneous timing bounds for delivered velocity and acceleration values.

The two signals have independent Lipschitz constants `Lv` and `La`; `ha` is
therefore an independent acceleration regularity premise (for example, a
jerk bound may be used to establish it elsewhere). -/
theorem reference_pair_timing_bound
    {v a : ℝ → V} {vDelivered aDelivered : V}
    {Lv La : NNReal} {εv εa h t τ : ℝ}
    (hv : LipschitzWith Lv v) (ha : LipschitzWith La a)
    (hvDelivered : dist vDelivered (v τ) ≤ εv)
    (haDelivered : dist aDelivered (a τ) ≤ εa)
    (ht : |t - τ| ≤ h) :
    dist vDelivered (v t) ≤ εv + (Lv : ℝ) * h ∧
      dist aDelivered (a t) ≤ εa + (La : ℝ) * h := by
  exact ⟨dist_delivered_to_target_le hv hvDelivered ht,
    dist_delivered_to_target_le ha haDelivered ht⟩

/-- Simultaneous delivery estimates on a common admissible timestamp set. -/
theorem reference_pair_timing_on_bound
    {S : Set ℝ} {v a : ℝ → V} {vDelivered aDelivered : V}
    {Lv La : NNReal} {εv εa h t τ : ℝ}
    (hv : LipschitzOnWith Lv v S) (ha : LipschitzOnWith La a S)
    (hτ : τ ∈ S) (ht' : t ∈ S)
    (hvDelivered : dist vDelivered (v τ) ≤ εv)
    (haDelivered : dist aDelivered (a τ) ≤ εa)
    (ht : |t - τ| ≤ h) :
    dist vDelivered (v t) ≤ εv + (Lv : ℝ) * h ∧
      dist aDelivered (a t) ≤ εa + (La : ℝ) * h := by
  exact ⟨dist_delivered_to_target_on_le hv hτ ht' hvDelivered ht,
    dist_delivered_to_target_on_le ha hτ ht' haDelivered ht⟩

end ReferenceTiming

end Ctrllib

#print axioms Ctrllib.dist_delivered_to_target_le
#print axioms Ctrllib.dist_delivered_to_target_on_le
#print axioms Ctrllib.reference_pair_timing_bound
#print axioms Ctrllib.reference_pair_timing_on_bound
