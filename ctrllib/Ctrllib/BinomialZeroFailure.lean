import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Ctrllib.BinomialConfidence

/-!
Zero-failure endpoint for the exact binomial confidence set (atlas R4).

The existing lower tail specializes at count zero to `(1 - p)^n`.  For a
positive trial count, `p ∈ [0, 1]`, and `0 < δ < 1`, strict inversion gives
`δ < (1 - p)^n ↔ p < 1 - δ ^ (1 / (n : ℝ))`, where the exponent on `δ` is
the real power.  The result keeps the existing strict confidence-set
convention and does not assert a closed reported interval.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology unitInterval

namespace Ctrllib

/-! ### Zero count -/

/-- The binomial lower tail at zero observed failures is `(1 - p)^n`. -/
theorem binomialLowerTail_zero (n : ℕ) (p : I) :
    binomialLowerTail n 0 p = (1 - (p : ℝ)) ^ n := by
  classical
  rw [binomialLowerTail]
  have hmem : 0 ∈ Finset.Iic (min 0 n) := by simp
  rw [Finset.sum_eq_single 0]
  · simp
  · intro b hb hb0
    have hb' : b ≤ min 0 n := Finset.mem_Iic.mp hb
    omega
  · intro hzero
    exact False.elim (hzero hmem)

/-! ### Strict zero-failure inversion -/

/--
Strict zero-failure endpoint inversion.

For `n > 0`, the strict lower-tail test at count zero is equivalent to the
usual real-power endpoint.  The positivity hypotheses make the power map
strictly monotone and exclude the degenerate `n = 0` case.
-/
theorem binomial_zero_failure_iff
    {n : ℕ} (hn : 0 < n) (p : I) {δ : ℝ} (hδ0 : 0 < δ) (_hδ1 : δ < 1) :
    δ < binomialLowerTail n 0 p ↔
      (p : ℝ) < 1 - Real.rpow δ (1 / (n : ℝ)) := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hp1 : (p : ℝ) ≤ 1 := p.property.2
  have hq0 : 0 ≤ 1 - (p : ℝ) := sub_nonneg.mpr hp1
  have hroot_lt_q_iff :
      Real.rpow δ (1 / (n : ℝ)) < 1 - (p : ℝ) ↔
        δ < (1 - (p : ℝ)) ^ n := by
    simpa [one_div, Real.rpow_natCast] using
      (Real.rpow_inv_lt_iff_of_pos (x := δ) (y := 1 - (p : ℝ)) (z := (n : ℝ))
        hδ0.le hq0 hnR)
  rw [binomialLowerTail_zero, ← hroot_lt_q_iff]
  constructor <;> intro h <;> linarith

/-! ### Confidence-set membership -/

/--
Membership in the existing strict confidence set at zero failures is exactly
the strict real-power endpoint condition.
-/
theorem mem_binomialUpperConfidenceSet_zero_iff
    {n : ℕ} (hn : 0 < n) (p : I) {δ : ℝ} (hδ0 : 0 < δ) (_hδ1 : δ < 1) :
    p ∈ binomialUpperConfidenceSet n 0 δ ↔
      (p : ℝ) < 1 - Real.rpow δ (1 / (n : ℝ)) := by
  change δ < binomialLowerTail n 0 p ↔ _
  exact binomial_zero_failure_iff hn p hδ0 _hδ1

end Ctrllib

#print axioms Ctrllib.binomialLowerTail_zero
#print axioms Ctrllib.binomial_zero_failure_iff
#print axioms Ctrllib.mem_binomialUpperConfidenceSet_zero_iff
