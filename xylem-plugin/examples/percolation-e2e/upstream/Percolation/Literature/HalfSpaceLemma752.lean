import Percolation.Literature.BernoulliPercolationProofs
import Percolation.Literature.DualContours
import Percolation.Literature.GMFiniteSize
import Percolation.Util.Linter

/-!
# A one-sided continuity step from the Barsky–Grimmett–Newman argument

`le_of_forall_pos_lt_le`: a continuous function on `[0,1]` that is `≤ c` on `(0, p)` is `≤ c` at `p` (for `p > 0`). This is the
step "`P_p(B(L,H) is good)` is a continuous function of `p`; therefore there exists `p' < p_c` such that …" in Grimmett's
proof of Theorem (7.35) (*Percolation*, 2nd ed., §7.3, p. 169), isolated as a lemma about real functions on the unit interval.
[cite: GrimmettPercolation1999, §7.3 p. 169]
-/

noncomputable section

namespace Percolation.Literature

open MeasureTheory ProbabilityTheory LatticeModels unitInterval
open scoped ProbabilityTheory ENNReal

/-! ## The continuity step at `p_c` -/

/-- A continuous function on `[0,1]` which is `≤ c` on `(0, p)` is `≤ c` at `p`, provided
`p > 0` (the one-sided limit used in Grimmett's assembly, p. 169: "`P_p(B(L,H) is good)` is a
continuous function of `p`. Therefore, there exists `p' < p_c` such that …"). [folklore] -/
theorem le_of_forall_pos_lt_le {f : unitInterval → ℝ} (hf : Continuous f) {p : unitInterval}
    (hp : 0 < (p : ℝ)) {c : ℝ} (h : ∀ q : unitInterval, 0 < (q : ℝ) → (q : ℝ) < p → f q ≤ c) :
    f p ≤ c := by
  by_contra hlt
  push Not at hlt
  have hopen : IsOpen {q : unitInterval | c < f q} := isOpen_lt continuous_const hf
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen p hlt
  set pc : ℝ := (p : ℝ) with hpc_def
  have hpc_le : pc ≤ 1 := p.2.2
  set r : ℝ := max (pc - ε / 2) (pc / 2) with hr_def
  have hr_lt : r < pc := max_lt (by linarith) (by linarith)
  have hr_pos : 0 < r := lt_max_of_lt_right (by linarith)
  have hr_mem : r ∈ unitInterval := ⟨hr_pos.le, hr_lt.le.trans hpc_le⟩
  have hr_ball : (⟨r, hr_mem⟩ : unitInterval) ∈ Metric.ball p ε := by
    rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq, abs_lt]
    change -ε < r - pc ∧ r - pc < ε
    constructor
    · have : pc - ε / 2 ≤ r := le_max_left _ _
      linarith
    · linarith
  have h1 : c < f ⟨r, hr_mem⟩ := hball hr_ball
  have h2 : f ⟨r, hr_mem⟩ ≤ c := h ⟨r, hr_mem⟩ hr_pos hr_lt
  linarith

end Percolation.Literature

end
