import Mathlib.Analysis.MeanInequalities

/-!
# PVS/NASALib Young inequality adapter

This theorem mirrors `youngs_inequality` in NASA's `complex_integration/young.pvs:28`
at NASALib revision `56dab1977c7889b69698227b7b883a188936597c`.
The PVS source imports `power@real_expt`; its nonnegative-base real exponent
is represented here by Lean's `Real.rpow` notation.  This is a statement
adapter, not a proof of semantic equivalence between the PVS and Lean power
definitions.

The PVS source cites S. K. Berberian, *Fundamentals of Real Analysis*,
Springer (1991), §3.1.3 for the inequality.

The conventional derivation is outside this package; the public source identity above is the attribution.
the corresponding local note.
-/

namespace Ctrllib.PVSReuse

/-- NASALib `youngs_inequality`, with the PVS subtype hypotheses made explicit.

For `a,b ≥ 0`, `p,q > 1`, and conjugacy `1/p + 1/q = 1`, the real-power
version of Young's inequality holds. -/
theorem youngs_inequality
    {a b p q : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hp : 1 < p) (hq : 1 < q)
    (hpq : 1 / p + 1 / q = 1) :
    a * b ≤ a ^ p / p + b ^ q / q := by
  apply Real.young_inequality_of_nonneg ha hb
  exact ⟨by simpa [one_div] using hpq, lt_trans zero_lt_one hp, lt_trans zero_lt_one hq⟩

/-- A negative Young scale cannot be admitted in the cross-term adapter:
the displayed scalar inequality fails at `C = s = t = 1`, `lam = -1`. -/
theorem negative_scale_cross_counterexample :
    ¬ ((1 : ℝ) * 1 ≤ (1 * (-1) / 2) * 1 ^ 2 + (1 / (2 * (-1))) * 1 ^ 2) := by
  norm_num

#print axioms Ctrllib.PVSReuse.youngs_inequality
#print axioms Ctrllib.PVSReuse.negative_scale_cross_counterexample

end Ctrllib.PVSReuse
