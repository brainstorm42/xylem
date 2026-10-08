import Percolation.Literature.ConditionalPositiveAssociationProofs
import Percolation.Util.Linter

/-!
# Sandwich BHK inequality — preliminaries (towards additive gluing in the case `|A ∖ b| = 2`)

Used by the base case of the sandwich induction.
-/

noncomputable section

open Percolation.Literature Percolation.Literature.BHK2006 DecisionTree

namespace Percolation.Continuity.SandwichBHK

open scoped Classical

/-! Local notations (no new definitions): `ℙ[w] A` the weight-sum probability of the event `A`;
`rF[U, a, b]` the connection event `{a ↔ b}` of `G[U]`; `rV[U, S, ω]` the finite set of vertices of
`G[U]` reachable from the source set `S`; `rE[U, o, R, X]` the **sandwich event**
`{o ↔ X} ∪ ({o ↮ X} ∩ {C(o) ∈ R})` for a collection `R` of vertex sets; `rB[U, Y]` the moat event
(no open edge between `Y` and `U ∖ Y`, i.e. BHK's random set of `Y` is empty). -/

section Graph

variable {V : Type*} [Fintype V]

omit [Fintype V] in
/-- A vertex reachable from `x ≠ y`… the endpoint of a nontrivial open path of `G[U]` lies in `U`.
[folklore] -/
theorem mem_of_reachable {U : Finset V} {ω : Set (Sym2 V)} {x y : V}
    (h : (openGraph (ω ∩ edgesIn U)).Reachable x y) (hne : x ≠ y) : y ∈ U := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  rcases Relation.ReflTransGen.cases_tail h with rfl | ⟨c, -, hcy⟩
  · exact absurd rfl hne
  · exact (adj_iff.1 hcy).2.1.2

/-! #### The moat lemma -/

variable {w : Sym2 V → ℝ}

end Graph

end Percolation.Continuity.SandwichBHK

