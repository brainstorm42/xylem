import Mathlib

namespace NewPG

theorem scalar_recurrence_bound
    {a : ℕ → ℝ} {r b : ℝ}
    (ha : ∀ k, 0 ≤ a k)
    (hr0 : 0 ≤ r)
    (hr1 : r < 1)
    (hstep : ∀ k, a (k + 1) ≤ r * a k + b)
    (k : ℕ) :
    a k ≤ r ^ k * a 0 + b * ((1 - r ^ k) / (1 - r)) := by
  have hden : (1 - r : ℝ) ≠ 0 :=
    ne_of_gt (sub_pos.mpr hr1)
  induction k with
  | zero =>
      simp
  | succ k ih =>
      calc
        a (k + 1) ≤ r * a k + b := hstep k
        _ ≤ r * (r ^ k * a 0 + b * ((1 - r ^ k) / (1 - r))) + b :=
          add_le_add_left (mul_le_mul_of_nonneg_left ih hr0) b
        _ = r ^ (k + 1) * a 0 +
            b * ((1 - r ^ (k + 1)) / (1 - r)) := by
          simp only [pow_succ]
          field_simp [hden] <;> ring

end NewPG
