import Percolation.Literature.BernoulliPercolation
import Percolation.Literature.ConnectivityProofs
import Percolation.Literature.KestenTheorem
import Percolation.Literature.PercolationProofs
import Percolation.Literature.RSWProofs
import Percolation.Literature.SharpnessDCTProofs
import Percolation.Literature.UniquenessInfiniteCluster
import Percolation.Util.Linter

/-!
# Proofs of the critical-probability facts for Bernoulli bond percolation

Discharges of named facts stated in
`BernoulliPercolation.lean`.

* `theta_pos_of_criticalProb_lt_holds : theta_pos_of_criticalProb_lt` — `θ_x(p) > 0` for
  `p > p_c` (Grimmett (1999), §1.4, p. 13), again from `theta_mono_holds`.

Locator note: the docstrings of the two facts in `BernoulliPercolation.lean` cite "§1.4 (1.11)";
in the 2nd edition (1999) the formula `p_c = sup{p : θ(p) = 0}` is equation (1.8) on p. 13 and
`θ(p) = P_p(|C| = ∞)` is (1.6). The statements themselves are as printed (no misstatement).
-/

namespace Percolation.Literature

open MeasureTheory ProbabilityTheory LatticeModels
open scoped ProbabilityTheory ENNReal

variable {V : Type*}

/-- The named fact `theta_pos_of_criticalProb_lt`, `θ_x(p) > 0`
for `p > p_c`. From `p_c = inf ({θ_x > 0} ∪ {1}) < p ≤ 1` there is `q < p` with `θ_x(q) > 0`,
and `θ_x(q) ≤ θ_x(p)` by monotonicity (`Percolation.Literature.theta_mono_holds`). (Grimmett,
*Percolation* (2nd ed., 1999), §1.4, p. 13: "`θ(p) > 0` if `p > p_c`"; monotone coupling
Thm. (2.1), p. 32.) [cite: GrimmettPercolation1999, §1.4 p. 13; Thm. (2.1) p. 32] -/
theorem theta_pos_of_criticalProb_lt_holds : theta_pos_of_criticalProb_lt (V := V) := by
  intro _ G x p h
  obtain ⟨q, hq, hqp⟩ := exists_lt_of_csInf_lt
    (⟨1, Or.inr rfl⟩ : ({q : ℝ | ∃ h : q ∈ unitInterval, 0 < theta G x ⟨q, h⟩} ∪ {1}).Nonempty) h
  rcases hq with ⟨hq01, hθ⟩ | hq1
  · exact hθ.trans_le (theta_mono_holds G x (show (⟨q, hq01⟩ : unitInterval) ≤ p from hqp.le))
  · rw [Set.mem_singleton_iff] at hq1
    exact absurd (hq1 ▸ hqp) (not_lt.2 p.2.2)

/-!
Aizenman–Kesten–Newman, *Comm. Math. Phys.* 111 (1987) 505–531, Prop. 1.1 (p. 507); Grimmett,
*Percolation* (2nd ed., 1999), Thm. (8.1), p. 198 (proof of Burton–Keane 1989); Kesten, *Comm. Math.
Phys.* 74 (1980), Thm. 2 (1.5).
-/

end Percolation.Literature
