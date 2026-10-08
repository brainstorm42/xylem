import Percolation.Literature.InequalitiesProofs
import Percolation.Literature.SharpnessDCTProofs
import Percolation.Util.Linter

/-!
# The depth-first exploration of an open cluster stopped at two targets (Gladkov 2024, §6.2)

Source: N. Gladkov, *Percolation Inequalities and Decision Trees*, arXiv:2408.08457v2 (2024)
[Gladkov2024], §6 (Algorithm 2 "DFS Decision Tree")
and §6.2 (proof of Theorem 6.2): "Let tree `T` perform a DFS starting with the vertex `a` and
put the edges it meets in `S` … After reaching `b` or `c`, the tree `T` stops … Backtracking the
DFS order leaves us with a path `P` from `a` to either `b` or `c`. Note that `T` queries all the
edges of the path `P` and puts them to `S`. Let `Q` be the set of vertices visited by the DFS
that are not in `P` … the DFS queried all edges from `Q` before backtracking and so all of these
edges, including those closed in `C₁`, belong to `S`."

This file formalises that exploration as a deterministic, adaptive edge-revealing process (every
queried edge is revealed; its decision tree in the sense of `DecisionTreeBK.lean` is built), for
configurations `K ⊆ D` of open edges among a finite set `D ⊆ Sym2 V` of edges, and proves the
structural facts the proof of Thm. 6.2 uses.

Not here: the probabilistic estimates.
-/

noncomputable section

namespace Percolation.Literature

namespace Gladkov

open Finset

variable {V : Type*} [DecidableEq V]

/-! ### States and one step of the exploration -/

section Defs

variable (D : Finset (Sym2 V)) (b c : V)

/-- A choice of an element of a finite set, if any. [folklore] -/
def pick (s : Finset (Sym2 V)) : Option (Sym2 V) :=
  if h : s.Nonempty then some h.choose else none

end Defs

section Basic

variable {D : Finset (Sym2 V)} {b c : V}

omit [DecidableEq V] in
/-- `pick` returns an element of the set. [folklore] -/
theorem mem_of_pick_eq_some {s : Finset (Sym2 V)} {e : Sym2 V} (h : pick s = some e) : e ∈ s := by
  unfold pick at h
  split_ifs at h with hs
  rw [Option.some.injEq] at h
  exact h ▸ hs.choose_spec

omit [DecidableEq V] in
/-- `pick` of a nonempty set is `some`. [folklore] -/
theorem pick_ne_none {s : Finset (Sym2 V)} (h : s.Nonempty) : pick s ≠ none := by
  unfold pick; rw [dif_pos h]; exact Option.some_ne_none _

end Basic

end Gladkov

end Percolation.Literature
