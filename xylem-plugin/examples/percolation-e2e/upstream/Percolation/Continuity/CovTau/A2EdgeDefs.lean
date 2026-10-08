import Percolation.Continuity.CovTau.A2Push
import Percolation.Continuity.CovTau.A2Star
import Percolation.Util.Linter

/-!
# The fresh expectation `tfE` of an edge-cluster functional in the induced world `G[U]`

`CovTau.tfE w U x g = E_{G[U]} g(C_x)`: the expectation of a function `g` of the open EDGE cluster of `x` for percolation
restricted to the vertex set `U` (the quantity `t_W`, `U = V ∖ W`, of the two-source vocabulary of van den Berg–Häggström–Kahn).
[cite: VandenbergHaggstromKahn2005, Thm. 1.1 (pp. 3–5), §1 p. 3 (`C_s`)] [cite: KozmaNitzan2024, Conj. 1 (p. 3)]
-/

noncomputable section

namespace Percolation.Continuity.CovTau

open Percolation.Literature
open Percolation.Literature.BHK2006
open Percolation.Literature.DecisionTree (ind ind_of_mem ind_of_not_mem ind_nonneg)
open scoped Classical

variable {V : Type*} [Fintype V]

/-! ### The functionals for an edge-cluster functional `g` -/

/-- `t = E_{G[U]} g(C_x)` (`t_W` with `U = V ∖ W`). [folklore] -/
def tfE (w : Sym2 V → ℝ) (U : Finset V) (x : V) (g : Set (Sym2 V) → ℝ) : ℝ :=
  ∑ ω, weight w ω * g (rC U x ω)

end Percolation.Continuity.CovTau
