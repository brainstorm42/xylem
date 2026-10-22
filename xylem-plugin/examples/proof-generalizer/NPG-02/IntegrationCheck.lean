import Candidate
import Mathlib

namespace NPG02Independent

theorem positive_client
    {E : Type*} [NormedAddCommGroup E]
    (e : ℕ → E) {r b : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hstep : ∀ j, ‖e (j + 1)‖ ≤ r * ‖e j‖ + b) (k : ℕ) :
    ‖e k‖ ≤ r ^ k * ‖e 0‖ + b * ((1 - r ^ k) / (1 - r)) := by
  exact NewPG.scalar_recurrence_bound
    (a := fun j => ‖e j‖) (r := r) (b := b)
    (fun j => norm_nonneg (e j)) hr0 hr1 hstep k

theorem specialization_back
    {E : Type*} [NormedAddCommGroup E]
    (e : ℕ → E) {r b : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hstep : ∀ j, ‖e (j + 1)‖ ≤ r * ‖e j‖ + b) (k : ℕ) :
    ‖e k‖ ≤ r ^ k * ‖e 0‖ + b * ((1 - r ^ k) / (1 - r)) := by
  exact positive_client e hr0 hr1 hstep k

section Negative

variable {a : ℕ → ℝ} {r b : ℝ}
variable (ha : ∀ j, 0 ≤ a j)
variable (hr0 : 0 ≤ r) (hr1 : r < 1)
variable (hstep : ∀ j, a (j + 1) ≤ r * a j + b) (k : ℕ)

#check_failure
  (show a k ≤ r ^ k * a 0 + b * ((1 + r ^ k) / (1 - r)) from
    NewPG.scalar_recurrence_bound ha hr0 hr1 hstep k)

end Negative

#print axioms NewPG.scalar_recurrence_bound
#print axioms positive_client
#print axioms specialization_back

end NPG02Independent
