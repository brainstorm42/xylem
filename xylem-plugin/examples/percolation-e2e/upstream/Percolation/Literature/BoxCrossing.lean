import Percolation.Literature.Crossings
import Percolation.Util.Linter

/-!
# The Russo–Seymour–Welsh box-crossing statement at `p = 1/2` on `ℤ²`

The named statement `rsw_half`: for every aspect ratio `ρ > 0` there is `c(ρ) > 0` with
`c ≤ P_{1/2}(LR([0, ⌊ρ n⌋] × [0, n])) ≤ 1 − c` for all `n` with `⌊ρ n⌋ ≥ 1` (Russo 1978; Seymour–Welsh 1978; Grimmett, *Percolation*
(1999), §11.7). It is proved in `RSWLemma.lean` (`rsw_half_holds`), via the RSW lower bound and duality (`RSW.lean`,
`rsw_half_of_lowerBound`).
[cite: GrimmettPercolation1999, §11.7]
-/

namespace Percolation.Literature

open MeasureTheory Filter Topology LatticeModels

noncomputable section

/-! ### RSW on `ℤ²` at `p = 1/2` -/

/-- (Russo–Seymour–Welsh box-crossing property at `p = 1/2` on `ℤ²`; Russo,
Z. Wahrsch. 43 (1978) 39; Seymour–Welsh, Ann. Discrete Math. 3 (1978) 227; Grimmett 1999,
§11.7). For every aspect ratio `ρ > 0` there is `c = c(ρ) > 0` such that
`c ≤ P_{1/2}(LR([0, ⌊ρ n⌋] × [0, n])) ≤ 1 - c` for all `n` with `⌊ρ n⌋ ≥ 1` (which forces
`n ≥ 1`; for `⌊ρ n⌋ = 0` the rectangle degenerates and the probability is `1`). [cite: GrimmettPercolation1999, §11.7] -/
def rsw_half : Prop :=
  ∀ (ρ : ℝ) (hρ : 0 < ρ),
    ∃ c > 0, ∀ n : ℕ, 1 ≤ ⌊ρ * n⌋₊ →
      c ≤ crossingProb half ⌊ρ * n⌋₊ n ∧ crossingProb half ⌊ρ * n⌋₊ n ≤ 1 - c

end

end Percolation.Literature
