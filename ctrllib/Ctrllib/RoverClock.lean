import Ctrllib.ReferenceTiming

/-!
Clock and sample-age interface for rover delivery bounds.

All timestamps in these declarations use one declared real-valued seconds
scale. The clock-error premises are the required conversion contract; no clock
model or synchronization mechanism is inferred here.
-/
namespace Ctrllib

/-- Target/sample timestamp error decomposes into target-clock error, reported
sample age, and sample-clock error. -/
theorem timestamp_error_decomposition
    {t ts taus tau ct age cs : ℝ}
    (hTargetClock : |t - ts| ≤ ct)
    (hAge : |ts - taus| ≤ age)
    (hSampleClock : |taus - tau| ≤ cs) :
    |t - tau| ≤ ct + age + cs := by
  have h := abs_add_le (t - ts) (ts - taus + (taus - tau))
  have h' : t - tau = (t - ts) + (ts - taus + (taus - tau)) := by ring
  rw [h']
  calc
    |(t - ts) + (ts - taus + (taus - tau))| ≤
        |t - ts| + |ts - taus + (taus - tau)| := h
    _ ≤ |t - ts| + (|ts - taus| + |taus - tau|) := by
      gcongr
      exact abs_add_le _ _
    _ ≤ ct + age + cs := by linarith

/-- A Lipschitz delivery bound using separately bounded target-clock error,
reported sample age, and sample-clock error. All terms are on the same seconds
scale, and `S` is the admissible timestamp set for the reference signal. -/
theorem clocked_delivery_bound
    {S : Set ℝ} {E : Type*} [PseudoMetricSpace E]
    {f : ℝ → E} {y : E} {L : NNReal}
    {t ts taus tau ε ct age cs : ℝ}
    (hf : LipschitzOnWith L f S) (ht : t ∈ S) (htau : tau ∈ S)
    (hy : dist y (f tau) ≤ ε)
    (hTargetClock : |t - ts| ≤ ct)
    (hAge : |ts - taus| ≤ age)
    (hSampleClock : |taus - tau| ≤ cs) :
    dist y (f t) ≤ ε + (L : ℝ) * (ct + age + cs) := by
  have htime : |t - tau| ≤ ct + age + cs :=
    timestamp_error_decomposition hTargetClock hAge hSampleClock
  exact dist_delivered_to_target_on_le hf htau ht hy htime

/-- Same-clock specialization with one bound `c` for both timestamp readings. -/
theorem same_clock_delivery_bound
    {S : Set ℝ} {E : Type*} [PseudoMetricSpace E]
    {f : ℝ → E} {y : E} {L : NNReal}
    {t ts taus tau ε c age : ℝ}
    (hf : LipschitzOnWith L f S) (ht : t ∈ S) (htau : tau ∈ S)
    (hy : dist y (f tau) ≤ ε)
    (hTargetClock : |t - ts| ≤ c)
    (hAge : |ts - taus| ≤ age)
    (hSampleClock : |taus - tau| ≤ c) :
    dist y (f t) ≤ ε + (L : ℝ) * (2 * c + age) := by
  have h := clocked_delivery_bound hf ht htau hy hTargetClock hAge hSampleClock
  calc
    dist y (f t) ≤ ε + (L : ℝ) * (c + age + c) := h
    _ = ε + (L : ℝ) * (2 * c + age) := by ring

end Ctrllib

#print axioms Ctrllib.timestamp_error_decomposition
#print axioms Ctrllib.clocked_delivery_bound
#print axioms Ctrllib.same_clock_delivery_bound
