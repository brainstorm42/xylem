import Percolation.Literature.HalfSpaceBrickSymmetry
import Percolation.Util.Linter

/-!
# Lemma (7.36) for general seed rules, and the clean seeds of the block construction

Grimmett, *Percolation*, 2nd ed. (1999), §7.3: the
proof of Lemma (7.36) (pp. 164–169) attaches to each vertex `x` of the top or sides of the brick
`B(L,H)` that is joined to `b(0)` in `B(L,H)*` the square `b(x)` and asks that it be a *seed* (all
its edges open); the only properties of the map `x ↦ (edges of b(x))` the printed argument uses are:
(i) these edges "do not intersect the interior of `B(L,H)`" (p. 168 (iv)), so that they are
independent of the linking events; (ii) the edge sets attached to sufficiently separated vertices
are disjoint, "then these include at least `N₁` vertices … such that the squares … are disjoint" (p.
165); (iii) their number is bounded in terms of `m` only, giving the seed probability `p^{|edges|}`
of (7.39); (iv) the rule is symmetric under the reflections of the brick ("By symmetry, the `X_j`
(respectively `Y_i`) have the same distribution", p. 168).

The rule of interest for the block construction of Lemma (7.52) (Grimmett pp. 172–173, (A)–(C): "the
intersection of a new brick with the region considered so far must be limited to a subset of its
underside") is the **clean seed rule** `cleanEdges m L H`: to `x` on the top it attaches the
vertical edge `{x, x + e₀}` and the horizontal square of radius `m` in the plane *just above* the
top, centred above `x` with the centre clamped so that the square stays above the top face; to `x`
on a side `x_a = ±L` the outward edge `{x, x ± e_a}` and the square of radius `m` in the plane just
outside that side, centred next to `x` with the centre clamped in height to `[m+1, H-m-1]` and
transversally, so that the square faces the side. All these edges lie OUTSIDE the brick (beyond its
faces, never below the underside), which is what makes stacked bricks examine disjoint edge sets.

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §7.3, Lemma (7.36) and its proof
  pp. 164–169; (A)–(C) pp. 172–173.
-/

noncomputable section

namespace Percolation.Literature

open MeasureTheory ProbabilityTheory Filter LatticeModels unitInterval
open scoped ENNReal Topology

namespace BGN

/-! ## The clean seed rule -/

section Clean

/-- Clamping an integer to `[lo, hi]`. [folklore] -/
def clampZ (lo hi t : ℤ) : ℤ := max lo (min hi t)

/-- A clamped value lies in the interval (when it is one). [folklore] -/
theorem clampZ_mem {lo hi : ℤ} (h : lo ≤ hi) (t : ℤ) : lo ≤ clampZ lo hi t ∧ clampZ lo hi t ≤ hi := by
  unfold clampZ; rw [max_def, min_def]; split_ifs <;> omega

/-- Clamping moves a point of `[lo - d, hi + d]` by at most `d`. [folklore] -/
theorem abs_clampZ_sub_le {lo hi d : ℤ} (h : lo ≤ hi) (hd : 0 ≤ d) {t : ℤ} (ht1 : lo - d ≤ t) (ht2 : t ≤ hi + d) :
    |clampZ lo hi t - t| ≤ d := by
  unfold clampZ; rw [abs_le, max_def, min_def]; split_ifs <;> omega

/-- Clamping to a symmetric interval is odd. [folklore] -/
theorem clampZ_neg {a : ℤ} (ha : 0 ≤ a) (t : ℤ) : clampZ (-a) a (-t) = -clampZ (-a) a t := by
  unfold clampZ; simp only [max_def, min_def]; split_ifs <;> omega

/-- Clamping by a unit sign. [folklore] -/
theorem clampZ_units_mul {a : ℤ} (ha : 0 ≤ a) (u : ℤˣ) (t : ℤ) : clampZ (-a) a (u * t) = u * clampZ (-a) a t := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp
  · simp [clampZ_neg ha]

variable {m L H : ℕ}

/-! ### Symmetry of the clean rule under the horizontal reflections -/

/-- `Int.sign (u t) = u * Int.sign t` for a unit `u`. [folklore] -/
theorem sign_units_mul (u : ℤˣ) (t : ℤ) : Int.sign ((u : ℤ) * t) = u * Int.sign t := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> simp [Int.sign_neg]

end Clean

end BGN

end Percolation.Literature
