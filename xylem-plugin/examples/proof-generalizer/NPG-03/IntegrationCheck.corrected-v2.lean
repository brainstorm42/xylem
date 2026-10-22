import Candidate
import Mathlib

open MeasureTheory
open scoped Interval

namespace NPG03Independent

theorem positive_client {a b : ℝ} (hab : a ≤ b) :
    (fun t : ℝ => t) b - (fun t : ℝ => t) a ≤
      ∫ t in a..b, (2 : ℝ) := by
  apply NewPG03C01.shifted_endpoint_bound
    (V := fun t : ℝ => t) (d := fun _ : ℝ => (1 : ℝ))
    (s := fun _ : ℝ => (2 : ℝ)) hab
  · fun_prop
  · fun_prop
  · fun_prop
  · intro t ht
    exact hasDerivAt_id t
  · intro t ht
    norm_num

theorem specialization_back {T : ℝ} (hT : 0 ≤ T) :
    (fun t : ℝ => t) T - (fun t : ℝ => t) 0 ≤
      ∫ t in (0 : ℝ)..T, (2 : ℝ) := by
  apply NewPG03C01.shifted_endpoint_bound
    (V := fun t : ℝ => t) (d := fun _ : ℝ => (1 : ℝ))
    (s := fun _ : ℝ => (2 : ℝ)) (a := 0) (b := T) hT
  · fun_prop
  · fun_prop
  · fun_prop
  · intro t ht
    exact hasDerivAt_id t
  · intro t ht
    norm_num

section Negative

variable {V d s : ℝ → ℝ} {a b : ℝ}
variable (hab : a ≤ b)
variable (hV : ContinuousOn V (Set.Icc a b))
variable (hd : ContinuousOn d (Set.Icc a b))
variable (hs : ContinuousOn s (Set.Icc a b))
variable (hderiv : ∀ t ∈ Set.Ioo a b, HasDerivAt V (d t) t)
variable (hbound : ∀ t ∈ Set.Icc a b, d t ≤ s t)

#check_failure
  (show V (b + 1) - V a ≤ ∫ t in a..(b + 1), s t from
    NewPG03C01.shifted_endpoint_bound (V := V) (d := d) (s := s) (a := a) (b := b)
      hab hV hd hs hderiv hbound)

end Negative

#print axioms NewPG03C01.shifted_endpoint_bound
#print axioms positive_client
#print axioms specialization_back

end NPG03Independent
