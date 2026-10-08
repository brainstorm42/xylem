import Percolation.Literature.CriticalContinuityProofs
import Percolation.Literature.SequentialProbing
import Percolation.Util.Linter

/-!
# Dynamic renormalization: a gadget system on the square macro-lattice percolates

The probabilistic skeleton of the block construction of
Barsky, Grimmett and Newman (Grimmett, *Percolation*, 2nd ed. (1999), §7.3, proof of Lemma (7.52),
pp. 169–176; §7.2, proof of Theorem (7.2) and Lemma (7.24), pp. 152–157), separated from all
geometry and proved. One is given, on top of bond percolation `P_p` on an arbitrary countable graph,
a **gadget system** indexed by the directed edges `(a, d)` of the square lattice `ℤ²` (the
renormalized, or "macro", lattice; Grimmett indexes tubes by `ℤ₊ × ℤ`, p. 170): an attempt along
`(a, d)` starting from a *token* `τ` (the data of a seed reached earlier) examines a finite set of
edges `region a d τ` and, reading the open edges found there, either fails or returns tokens for the
onward attempts out of the macro-vertex `a + d` (Grimmett p. 174: "If all three target zones are
reached in this construction, we declare the vertex … occupied; otherwise, we declare it
unoccupied"; p. 172 (A)–(C): stacking, branching). The axioms are: regions of distinct directed
macro-edges are disjoint and avoid the initial edge set `U₀` (p. 173 (C): "the intersection of a new
brick with the region considered so far must be limited to a subset of its underside"); an attempt
from an admissible token fails with probability at most `ε` (p. 174, (7.56)); success returns
admissible tokens whose anchors are joined by open paths to the anchor of `τ` and lie in the cell of
`a + d`; and the initial tokens are admissible with anchors joined to `x₀` once `U₀` is open (p.
171, (7.55)).

The macro-lattice is then explored edge by edge ("The algorithm to be followed is that utilized in
the proofs of Theorems (1.33) and (7.2)", p. 171): at each step the least unexamined directed edge
from an occupied macro-vertex to an unoccupied one is attempted, each attempt being ONE probe of the
sequential probing scheme of `SequentialProbing.lean`. An infinite occupied macro-cluster carries
infinitely many anchors joined to `x₀`, whence `θ_{x₀}(p) > 0`.

## Design choices (departures from the printed sketch)

Grimmett (pp. 170–176), following Barsky–Grimmett–Newman, examines each macro-VERTEX of
`ℤ₊ × ℤ` once, from one occupied neighbour, and concludes by the stochastic domination of Lemma
(7.24) (Grimmett–Marstrand) by site percolation on `ℤ₊ × ℤ`; the disjointness requirement (C),
p. 173, is dynamic ("the region considered so far"). This file differs as follows. (i) It works on
all of `ℤ²` and attempts each DIRECTED macro-edge separately (an unoccupied cell may be attempted
again from another occupied neighbour), which is what the bond/dual-circuit bookkeeping of
`DualContours.lean` needs. (ii) Disjointness is required STATICALLY: the regions of attempts along
distinct, non-reversed directed macro-edges are disjoint for all admissible tokens (so a model must
reserve, in each cell, one region per incoming direction); this implies (C) along every run
(`fresh_explorer`). (iii) The conclusion is reached by Peierls' counting of dual circuits
(`theta_zd_pos_of_le`'s count `n(n+1)4ⁿ`, threshold `ε ≤ 1/64`) applied to the supermartingale of
`SequentialProbing.lean`, instead of Lemma (7.24); Grimmett's "this holds just as in Lemma (7.24)"
(p. 176) is thus replaced by a self-contained estimate. The percolation conclusion is for the fine
graph at `x₀` (full space), which is what the contradiction in the proof of Theorem (7.35) uses.

## References

* G. Grimmett, *Percolation*, 2nd ed., Grundlehren 321, Springer 1999, §7.2 pp. 152–157, §7.3
  pp. 169–176, §1.4 pp. 15–18 (Peierls' argument).
* D. J. Barsky, G. R. Grimmett, C. M. Newman, Dynamic renormalization and continuity of the
  percolation transition in orthants, in *Spatial Stochastic Processes*, Birkhäuser 1991, 37–55.
-/

noncomputable section

namespace Percolation.Literature

open MeasureTheory ProbabilityTheory Contour ProbeHistory
open scoped ENNReal Classical

/-- The four directions of the square macro-lattice (axis, orientation), as in `DualContours.lean`.
[cite: GrimmettPercolation1999, §7.3 p. 170] -/
abbrev MDir := Fin 2 × Bool

namespace GadgetSystem

variable {V : Type*}

/-! ## The macro-state and its replay from a probing history -/

variable {S}

/-- The target macro-vertex of a directed macro-edge. [folklore] -/
def tgt (e : LatticeModels.Site 2 × MDir) : LatticeModels.Site 2 := e.1 + stepVec e.2

variable (S)

/-! ## Combinatorial invariants of reachable states -/

section Invariants

variable {S}

/-- The target of the reversed edge from the target is the source. [folklore] -/
theorem tgt_tgt_rev (e : LatticeModels.Site 2 × MDir) : tgt (tgt e, rev e.2) = e.1 := by
  simp [tgt, stepVec_rev]

/-- `stepVec` is injective on directions of `ℤ²`. [folklore] -/
theorem stepVec_injective_two : Function.Injective (stepVec : MDir → LatticeModels.Site 2) := by
  intro a b h
  obtain ⟨i, bi⟩ := a
  obtain ⟨j, bj⟩ := b
  fin_cases i <;> fin_cases j <;> cases bi <;> cases bj <;>
    first
    | rfl
    | (exfalso
       have h0 := congrFun h 0
       have h1 := congrFun h 1
       simp [stepVec] at h0 h1)

end Invariants

/-! ## Connectivity: anchors in play are joined to `x₀` -/

section Connectivity

variable {S}

/-- Transitivity of membership in open clusters. [folklore] -/
theorem mem_openCluster_trans {ω : BondConfig V} {x y z : V} (hy : y ∈ openCluster ω x) (hz : z ∈ openCluster ω y) :
    z ∈ openCluster ω x :=
  SimpleGraph.Reachable.trans hy hz

end Connectivity

/-! ## Scores: designated probes and successes read off the history -/

section Scores

variable (Γ : Finset (Sym2 (LatticeModels.Site 2)))

variable {S Γ}

/-- Two directed macro-edges with the same underlying edge are equal or mutually reversed. [folklore] -/
theorem eq_or_rev_of_edge_eq {e e' : LatticeModels.Site 2 × MDir} (h : s(e.1, tgt e) = s(e'.1, tgt e')) :
    e' = e ∨ e' = (tgt e, rev e.2) := by
  rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    have hd : stepVec e'.2 = stepVec e.2 := by
      have := h2; rw [tgt, tgt, h1] at this; exact (add_left_cancel this).symm
    exact Prod.ext h1.symm (stepVec_injective_two hd)
  · right
    have hd : stepVec e'.2 = stepVec (rev e.2) := by
      rw [stepVec_rev]
      have := h2  -- tgt e = e'.1
      have h3 : e'.1 + stepVec e'.2 = e.1 := h1.symm ▸ rfl
      rw [← this, tgt] at h3
      have : stepVec e'.2 = -stepVec e.2 := by
        have h4 := congrArg (· - (e.1 + stepVec e.2)) h3
        simp at h4
        linear_combination h4
      exact this
    exact Prod.ext h2.symm (stepVec_injective_two hd)

end Scores

end GadgetSystem

end Percolation.Literature
