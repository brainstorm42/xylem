import Percolation.Literature.CleanSeeds
import Percolation.Util.Linter

/-!
# Placed clean bricks: supports, boxes and exits

The geometric interface between the clean good event
`goodC m L H` of `CleanSeeds.lean` (Grimmett, *Percolation*, 2nd ed. (1999), §7.3, the brick
`B(L,H)` of Lemma (7.36) with the seeds placed just outside its faces) and the block construction of
Lemma (7.52) (Grimmett pp. 169–176, "rotated translates of `B(L,H)`", (A) top stacking, (B) side
stacking, (C) "the intersection of a new brick with the region considered so far must be limited
to a subset of its underside"). proved here:

* `Exitable`, `linked_exitable` — a vertex of `T ∪ S` joined to `b(0)` in `B(L,H)*` is off the
  rim of the top, at height `≥ 1`, and off the corner columns (cf. `topLinked_notMem_rim`).
* `suppC m L H` — the edges `goodC` depends on: the edges of `B(L,H)*` and the clean edges of the
  exitable vertices; `determinedBy_goodC`.
* `dmid e = u + v` (the doubled midpoint of `e = {u,v}`) and the **support box**
  `stdBox L H = [1, 2H+2] × [-(2L+2), 2L+2]²` with `dmid_mem_stdBox_of_mem_suppC`
  (`L ≥ m + 1`, `H ≥ 2m + 2`): the underside plane (doubled height `0`) is excluded, so that a
  brick stacked on a clean seed examines edges disjoint from those of its parent.
* open squares are internally connected (`reachable_of_isSeed_square`);

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §7.3 pp. 163–176.
-/

noncomputable section

namespace Percolation.Literature

open MeasureTheory ProbabilityTheory LatticeModels unitInterval
open scoped ENNReal

namespace BGN

variable {m L H : ℕ}

/-! ## Placements -/

/-- `s² = 1` for a unit sign. [folklore] -/
theorem units_mul_self (u : ℤˣ) : (u : ℤ) * u = 1 := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> simp

/-! ## Exits -/

/-- Clamping to a symmetric interval preserves the weak sign. [folklore] -/
theorem clampZ_nonneg_iff {a : ℤ} (ha : 0 ≤ a) (t : ℤ) :
    (0 ≤ t → 0 ≤ clampZ (-a) a t) ∧ (t ≤ 0 → clampZ (-a) a t ≤ 0) := by
  unfold clampZ; rw [max_def, min_def]; split_ifs <;> constructor <;> intros <;> omega

end BGN

end Percolation.Literature
