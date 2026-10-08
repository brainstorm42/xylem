import Percolation.Literature.LatticeModels.ProdBernoulliIndependence
import Percolation.Literature.PercolationEvents
import Percolation.Literature.TripodExchange
import Percolation.Literature.TwoClusterConditionalAssociationProofs
import Percolation.Util.Linter

/-!
# Cluster / off-cluster negative correlation given `{s ↮ X}`, the loner-attachment monotonicity, and lone-port sums — corollaries of van den Berg–Häggström–Kahn 2006, Thm. 1.3

Bond percolation with arbitrary edge probabilities on a finite vertex type `V` (`μ = prodBernoulli
w` on `BondConfig V = Set (Sym2 V)`); `C_s` the open edge cluster of `s` (`openEdgeCluster`). BHK's
Theorem 1.3 [VandenbergHaggstromKahn2005, Thm. 1.3 p. 6; here the proved statement
`BHK2006_clusterConditionalPositiveAssociation`] says that given `D_X = {s ↮ X}` (a SET `X ∌ s`) the
cluster `C_s` is positively associated. BHK derive their two-cluster Theorems 1.4/1.5 (for `X =
{t}`) from it by conditioning on `C_s = W` ("display (10)", pp. 7–8; here
`BHK2006.sum_cond_cluster`).

## References

* J. van den Berg, O. Häggström, J. Kahn, *Some conditional correlation inequalities for percolation and
  related processes*, Random Structures Algorithms 29 (2006) 417–435: Thm. 1.3 (p. 6), proof of
  Thm. 1.5 (pp. 7–8, display (10)). [VandenbergHaggstromKahn2005]
* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, Thm. (2.4) p. 34 (Harris–FKG). [GrimmettPercolation1999]
-/

noncomputable section

open MeasureTheory Set
open Percolation.Literature.LatticeModels

namespace Percolation.Literature

variable {V : Type*}

namespace LonePortSum

open BHK2006 DecisionTree
open scoped Classical

/-- `∫_D h dμ` as a finite weighted sum. [folklore] -/
theorem setIntegral_eq_sum [Fintype V] (w : Sym2 V → unitInterval) (D : Set (BondConfig V))
    (h : BondConfig V → ℝ) :
    ∫ ω in D, h ω ∂(prodBernoulli w) =
      ∑ ω, weight (fun e => (w e : ℝ)) ω * (h ω * ind D ω) := by
  rw [← integral_indicator (MeasurableSet.of_discrete : MeasurableSet D),
    integral_prodBernoulli_eq_sum]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases hω : ω ∈ D
  · rw [Set.indicator_of_mem hω, ind_of_mem hω, mul_one]
  · rw [Set.indicator_of_notMem hω, ind_of_not_mem hω]; ring

/-- `μ(D)` as a finite weighted sum. [folklore] -/
theorem measureReal_eq_sum [Fintype V] (w : Sym2 V → unitInterval) (D : Set (BondConfig V)) :
    (prodBernoulli w).real D = ∑ ω, weight (fun e => (w e : ℝ)) ω * ind D ω := by
  rw [← integral_indicator_one (MeasurableSet.of_discrete : MeasurableSet D),
    integral_prodBernoulli_eq_sum]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases hω : ω ∈ D
  · rw [Set.indicator_of_mem hω, ind_of_mem hω, Pi.one_apply]
  · rw [Set.indicator_of_notMem hω, ind_of_not_mem hω, mul_zero]

end LonePortSum

end Percolation.Literature

end
