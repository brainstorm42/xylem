import Percolation.Continuity.CovTau.A2EdgeDefs
import Percolation.Continuity.CovTau.StarBridge
import Percolation.Util.Linter

/-!
# An edge-cluster functional on a restricted cluster: `g (rC U x K) = fcl g x K`

One rewriting lemma for EDGE-cluster functionals in the restricted world `G[U]` (`g_rC_eq_fcl`, for `K ⊆ pairsIn U`), companion
of `Continuity/CovTau/StarBridge.lean`.
[cite: VandenbergHaggstromKahn2005, Thm. 1.1 (pp. 3–5), Thm. 1.4 (p. 7), eq. (6)]
-/

noncomputable section

namespace Percolation.Continuity

namespace CovTauStarN

open Finset MeasureTheory Percolation.Literature Percolation.Literature.DecisionTree
open Percolation.Literature.BHK2006 (weight edgesIn rC rD weight_nonneg)
open SetClusterExploration TreeHarris CovTau
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- `g (rC U x ↑K) = fcl g x K` for `K ⊆ pairsIn U`. [folklore] -/
theorem g_rC_eq_fcl {U : Finset V} (g : Set (Sym2 V) → ℝ) (x : V) {K : Finset (Sym2 V)} (hK : K ⊆ pairsIn U) :
    g (rC U x (↑K : Set (Sym2 V))) = fcl g x K := by
  unfold fcl
  rw [show rC U x (↑K : Set (Sym2 V)) = openEdgeCluster ((↑K : Set (Sym2 V)) ∩ edgesIn U) x from rfl,
    coe_inter_edgesIn_of_subset hK]

end CovTauStarN

end Percolation.Continuity

end
