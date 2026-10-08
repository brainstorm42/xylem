import Percolation.Literature.ConditionalPositiveAssociationProofs
import Percolation.Util.Linter

/-!
# The bystander's cluster: conditioning tools for a BHK inequality with a bystander

Towards `Percolation.Continuity.Statements.AdditiveGluing` (the case `|A∖b| = 2`); first of the helper files proving
the **bystander BHK inequality**: for percolation restricted to `U` (product weight `BHK2006.weight
w` on `Set (Sym2 V)`), a source `s`, a *bystander* `o`, an arbitrary collection `𝓡` of vertex sets
none of which contains `s`, `F ≥ 0` increasing in `C_s`, and all `X, Y ⊆ U`, `E[F(C_s) 1_{E_X}
1_{R_X}] · P(R_Y) ≤ E[F(C_s) 1_{R_{X∩Y}}] · E[1_{E_{X∪Y}} 1_{R_{X∪Y}}]`, where `R_T = {s ↮ T}`
(`BHK2006.rD`) and `E_T = {o ↔ T} ∪ {K ∈ 𝓡}` is the (non-monotone!) **bystander event**, `K =
openCluster (ω ∩ edgesIn U) o` the open vertex cluster of `o` in `G[U]`.

This file (no new definitions; the objects are spelled out): the two conditioning devices —
Everything is stated in the finite product-weight formalism of
`Percolation.Literature.ConditionalPositiveAssociationProofs` (`BHK2006.*`), reused verbatim.
-/

noncomputable section

namespace Percolation.Continuity

open Percolation.Literature Percolation.Literature.BHK2006
open DecisionTree (ind ind_of_mem ind_of_not_mem ind_nonneg)
open scoped Classical

namespace BystanderBHK

variable {V : Type*}

/-! ### Conditioning on the bystander's cluster: `K = W` -/

variable [Fintype V]

omit [Fintype V] in
/-- Indicators of equivalent memberships agree. [folklore] -/
theorem ind_congr {α β : Type*} {D : Set α} {D' : Set β} {a : α} {b : β} (h : a ∈ D ↔ b ∈ D') :
    ind D a = ind D' b := by
  by_cases ha : a ∈ D
  · rw [ind_of_mem ha, ind_of_mem (h.1 ha)]
  · rw [ind_of_not_mem ha, ind_of_not_mem (fun hb => ha (h.2 hb))]

end BystanderBHK

end Percolation.Continuity
