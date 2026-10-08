import Mathlib.Logic.Relation
import Percolation.Literature.SiteConnectionTools
import Percolation.Util.Linter

/-!
# Paths inside a set of vertices: a relational toolkit for site percolation

* `PathIn G A u v` — `u ∈ A` and `u = a₀ ∼ a₁ ∼ ⋯ ∼ a_k = v` is a chain of `G`-adjacent vertices
  all lying in `A` (`Relation.ReflTransGen`; `k = 0` allowed), with the API
  `refl / tail / of_adj / trans / symm / mono`;
* `PathIn.exit_or`, `PathIn.exit` — **first exit**: a path from a vertex of `R` to a vertex
  outside `R` contains an edge `a ∼ b`, `a ∈ R`, `b ∉ R`, preceded by a path inside `R`;
* `PathIn.last_exit` — **last visit**: a path from a vertex of `C` to a vertex outside `C`
  contains an edge `a ∼ b`, `a ∈ C`, `b ∉ C`, followed by a path avoiding `C`
  (Duminil-Copin–Tassion 2016, proof of Thm. 1.1, item 1: "consider the last vertex of the path
  in the cluster");

## References

* H. Duminil-Copin, V. Tassion, A new proof of the sharpness of the phase transition for
  Bernoulli percolation and the Ising model, *Comm. Math. Phys.* 343 (2016) 725–745, proof of
  Thm. 1.1.
* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §1.6 (site percolation, open paths).

## Mathlib / this library

Mathlib: `Relation.ReflTransGen` (with `head`/`tail` induction), `SimpleGraph.Reachable`,
`SimpleGraph.reachable_iff_reflTransGen`, `SimpleGraph.induce`. Mathlib's `SimpleGraph.Walk` API is
about walks in a fixed graph; here the ambient set `A` varies (it is intersected with the random
configuration), which is why a bare `ReflTransGen` predicate is more convenient.
-/

namespace Percolation.Literature

variable {V : Type*} {G : SimpleGraph V}

/-- `PathIn G A u v`: `u ∈ A` and there is a chain `u = a₀ ∼ a₁ ∼ ⋯ ∼ a_k = v` of `G`-adjacent
vertices all lying in `A` (`k = 0` allowed). (Grimmett 1999, §1.6: paths of open vertices.)
[cite: GrimmettPercolation1999, §1.6] -/
def PathIn (G : SimpleGraph V) (A : Set V) (u v : V) : Prop :=
  u ∈ A ∧ Relation.ReflTransGen (fun a b => G.Adj a b ∧ b ∈ A) u v

namespace PathIn

variable {A A' : Set V} {u v w : V}

/-- The trivial path. [folklore] -/
theorem refl (hu : u ∈ A) : PathIn G A u u := ⟨hu, Relation.ReflTransGen.refl⟩

/-- The start of a path lies in the set. [folklore] -/
theorem left_mem (h : PathIn G A u v) : u ∈ A := h.1

/-- The end of a path lies in the set. [folklore] -/
theorem right_mem (h : PathIn G A u v) : v ∈ A := by
  obtain ⟨hu, h⟩ := h
  induction h with
  | refl => exact hu
  | tail _ hbc _ => exact hbc.2

/-- Extending a path by one edge. [folklore] -/
theorem tail (h : PathIn G A u v) (hvw : G.Adj v w) (hw : w ∈ A) : PathIn G A u w :=
  ⟨h.1, h.2.tail ⟨hvw, hw⟩⟩

/-- A one-edge path. [folklore] -/
theorem of_adj (hu : u ∈ A) (hv : v ∈ A) (h : G.Adj u v) : PathIn G A u v :=
  (refl hu).tail h hv

/-- Concatenation of paths. [folklore] -/
theorem trans (h₁ : PathIn G A u v) (h₂ : PathIn G A v w) : PathIn G A u w :=
  ⟨h₁.1, h₁.2.trans h₂.2⟩

/-- Reversal of paths. [folklore] -/
theorem symm (h : PathIn G A u v) : PathIn G A v u := by
  obtain ⟨hu, h⟩ := h
  induction h with
  | refl => exact refl hu
  | @tail b c _ hbc ih =>
    exact (of_adj hbc.2 ih.left_mem hbc.1.symm).trans ih

/-- Paths inside a smaller set are paths inside a larger set. [folklore] -/
theorem mono (hAA' : A ⊆ A') (h : PathIn G A u v) : PathIn G A' u v := by
  obtain ⟨hu, h⟩ := h
  refine ⟨hAA' hu, ?_⟩
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail ⟨hbc.1, hAA' hbc.2⟩

/-- Paths in a subgraph are paths in the larger graph. [folklore] -/
theorem mono_graph {G' : SimpleGraph V} (hGG' : G ≤ G') (h : PathIn G A u v) : PathIn G' A u v := by
  obtain ⟨hu, h⟩ := h
  refine ⟨hu, ?_⟩
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail ⟨hGG' hbc.1, hbc.2⟩

/-- **First exit.** A path inside `A` from a vertex of `R` either stays inside `R`, or it contains
an edge `a ∼ b` with `a ∈ R`, `b ∈ A \ R` such that its initial segment up to `a` lies in
`R ∩ A`. [folklore] -/
theorem exit_or {R : Set V} (h : PathIn G A u v) (hu : u ∈ R) :
    PathIn G (R ∩ A) u v ∨
      ∃ a b, a ∈ R ∧ b ∉ R ∧ b ∈ A ∧ G.Adj a b ∧ PathIn G (R ∩ A) u a := by
  obtain ⟨huA, h⟩ := h
  induction h with
  | refl => exact Or.inl (refl ⟨hu, huA⟩)
  | @tail b c _ hbc ih =>
    rcases ih with ih | ih
    · by_cases hc : c ∈ R
      · exact Or.inl (ih.tail hbc.1 ⟨hc, hbc.2⟩)
      · exact Or.inr ⟨b, c, ih.right_mem.1, hc, hbc.2, hbc.1, ih⟩
    · exact Or.inr ih

/-- **First exit** of a path that does leave `R`. [folklore] -/
theorem exit {R : Set V} (h : PathIn G A u v) (hu : u ∈ R) (hv : v ∉ R) :
    ∃ a b, a ∈ R ∧ b ∉ R ∧ b ∈ A ∧ G.Adj a b ∧ PathIn G (R ∩ A) u a := by
  rcases h.exit_or hu with h' | h'
  · exact absurd h'.right_mem.1 hv
  · exact h'

/-- **Last visit.** A path inside `A` from a vertex of `C` either ends in `C`, or it contains an
edge `a ∼ b` with `a ∈ C ∩ A`, `b ∉ C`, followed by a path inside `A \ C` from `b` to the end
(Duminil-Copin–Tassion 2016, proof of Thm. 1.1: the last vertex of the path in the cluster).
[cite: DuminilCopinTassionCMP2016, Thm. 1.1 (proof, item 1)] -/
theorem last_exit_or {C : Set V} (h : PathIn G A u v) (hu : u ∈ C) :
    v ∈ C ∨ ∃ a b, a ∈ C ∧ a ∈ A ∧ b ∉ C ∧ G.Adj a b ∧ PathIn G (A \ C) b v := by
  obtain ⟨huA, h⟩ := h
  induction h with
  | refl => exact Or.inl hu
  | @tail b c hub hbc ih =>
    by_cases hc : c ∈ C
    · exact Or.inl hc
    · right
      by_cases hb : b ∈ C
      · have hb' : PathIn G A u b := ⟨huA, hub⟩
        exact ⟨b, c, hb, hb'.right_mem, hc, hbc.1, refl ⟨hbc.2, hc⟩⟩
      · rcases ih with ih | ⟨a, b', ha, haA, hb', hab', hp⟩
        · exact absurd ih hb
        · exact ⟨a, b', ha, haA, hb', hab', hp.tail hbc.1 ⟨hbc.2, hc⟩⟩

/-- **Last visit** for a path that ends outside `C`. [cite: DuminilCopinTassionCMP2016, Thm. 1.1 (proof, item 1)] -/
theorem last_exit {C : Set V} (h : PathIn G A u v) (hu : u ∈ C) (hv : v ∉ C) :
    ∃ a b, a ∈ C ∧ a ∈ A ∧ b ∉ C ∧ G.Adj a b ∧ PathIn G (A \ C) b v := by
  rcases h.last_exit_or hu with h' | h'
  · exact absurd h' hv
  · exact h'

end PathIn

end Percolation.Literature
