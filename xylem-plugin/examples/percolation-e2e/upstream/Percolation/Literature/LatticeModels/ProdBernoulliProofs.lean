import Percolation.Literature.LatticeModels.ProdBernoulli
import Percolation.Util.Linter

/-!
# Inhomogeneous product Bernoulli measures: `prodBernoulli` specialises to Mathlib's `setBernoulli`

Proof of `prodBernoulli_indicator` (`LatticeModels/ProdBernoulli.lean`): with the parameter `p` on `u` and `0` off `u`,
`prodBernoulli` is Mathlib's homogeneous product Bernoulli measure `setBer(u, p)`. [cite: GrimmettPercolation1999, §1.3]
-/

noncomputable section

namespace Percolation.Literature.LatticeModels

open MeasureTheory ProbabilityTheory unitInterval

/-- Proof of `prodBernoulli_indicator`: with parameter `p` on `u` and `0` off `u`, the
inhomogeneous product Bernoulli measure is Mathlib's `setBer(u, p)` (the two infinite products
have the same factors: off `u` the factor is `0 • δ_True + 1 • δ_False = δ_False`).
(Grimmett 1999, §1.3, product measure.) [cite: GrimmettPercolation1999, §1.3] -/
theorem prodBernoulli_indicator_holds {ι : Type*} : prodBernoulli_indicator (ι := ι) := by
  intro u _ p
  unfold prodBernoulli setBernoulli
  congr 1
  congr 1
  funext i
  by_cases hi : i ∈ u
  · simp [hi]
  · simp only [hi, if_false, toNNReal_zero, zero_smul, zero_add, unitInterval.symm_zero,
      toNNReal_one, one_smul]
    rw [← add_smul, toNNReal_add_toNNReal_symm, one_smul]

end Percolation.Literature.LatticeModels

end
