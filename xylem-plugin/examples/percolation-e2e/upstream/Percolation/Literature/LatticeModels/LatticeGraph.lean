import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.SuccPred
import Mathlib.Analysis.Complex.Basic
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.ZMod.Basic
import Percolation.Util.Linter

/-!
# The hypercubic lattice `ℤ^d` as a simple graph, tori, and finite-volume boundaries

This file provides the shared lattice bookkeeping for the lattice models of this library:

* `zdGraph d`, the nearest-neighbour graph on `ℤ^d`. **Design choice:** this *is* Mathlib's Hasse
  diagram `SimpleGraph.hasse (Fin d → ℤ)` of the product partial order: by `Pi.covBy_iff` and
  `Order.covBy_iff_add_one_eq` (ℤ is a `SuccAddOrder`), `x ⋖ y` in `Fin d → ℤ` iff `y = x + eᵢ` for
  some coordinate vector `eᵢ = Pi.single i 1`. This is proved here (`Site.covBy_iff`,
  `zdGraph_adj_iff`), and the `DecidableRel`/`LocallyFinite` instances rest on that real proof.
* Generic finite-volume boundary operations for a locally finite simple graph `G` and a finite
  vertex set `Λ`: `outerBoundary`, `innerBoundary`, `edgesIn`, `edgesTouching`, `edgeBoundary`,
  with membership lemmas. Conventions follow Friedli–Velenik, *Statistical Mechanics of Lattice
  Systems* (2017), Ch. 3, §3.1 (`∂ᵉˣΛ`, `∂ⁱⁿΛ`, edge sets `ℰ_Λ` and `ℰ_Λ^b`).

Mathlib anchors used rather than re-defined: `SimpleGraph.hasse`, `SimpleGraph.hasse_adj`,
`Pi.covBy_iff_exists_right_eq`, `Order.covBy_iff_add_one_eq`, `SimpleGraph.neighborFinset`,
`SimpleGraph.incidenceFinset`, `SimpleGraph.LocallyFinite`, `SimpleGraph.circulantGraph`
(the torus graph is a circulant graph on the additive group `(ZMod L)^d`), `Equiv.addRight`,
`ZMod`. Mathlib has no vertex/edge boundary of a vertex set in a `SimpleGraph`
(only `SimpleGraph.interedges` between two finsets, as ordered pairs), hence the boundary
definitions below; all of them only assume `[DecidableEq V] [G.LocallyFinite]`.

-/

namespace Percolation.Literature.LatticeModels

open Finset

/-! ### Sites of `ℤ^d` -/

/-- A site of the hypercubic lattice `ℤ^d`, i.e. a function `Fin d → ℤ`. The norm `‖x‖` is the
sup norm inherited from Mathlib's Pi normed group structure.
(Friedli–Velenik 2017, §3.1.) [cite: FriedliVelenikSMLS2017, §3.1] -/
abbrev Site (d : ℕ) : Type := Fin d → ℤ

namespace Site

/-- Translation of `ℤ^d` by the vector `v`, `x ↦ x + v`, as a bijection (Mathlib's
`Equiv.addRight`). (Friedli–Velenik 2017, §3.1, translation invariance.) [cite: FriedliVelenikSMLS2017, §3.1 (translation invariance)] -/
def shift {d : ℕ} (v : Site d) : Site d ≃ Site d := Equiv.addRight v

/-- `Site.shift v x = x + v`. (Friedli–Velenik 2017, §3.1.) [cite: FriedliVelenikSMLS2017, §3.1] -/
@[simp] theorem shift_apply {d : ℕ} (v x : Site d) : shift v x = x + v := rfl

/-- The inverse of translation by `v` is translation by `-v`. (Friedli–Velenik 2017, §3.1.) [cite: FriedliVelenikSMLS2017, §3.1] -/
@[simp] theorem shift_symm_apply {d : ℕ} (v x : Site d) : (shift v).symm x = x - v := by
  simp [shift, sub_eq_add_neg]

variable {d : ℕ}

/-- In the product order on `ℤ^d`, `y` covers `x` iff `y` is obtained from `x` by adding a unit
coordinate vector. This is `Pi.covBy_iff` combined with `Order.covBy_iff_add_one_eq` for `ℤ`.
(Folklore; cf. Friedli–Velenik 2017, §3.1.) [cite: FriedliVelenikSMLS2017, §3.1] -/
theorem covBy_iff {x y : Site d} : x ⋖ y ↔ ∃ i, y = x + Pi.single i 1 := by
  rw [Pi.covBy_iff_exists_right_eq]
  constructor
  · rintro ⟨i, a, h, rfl⟩
    rw [Order.covBy_iff_add_one_eq] at h
    subst h
    refine ⟨i, funext fun j => ?_⟩
    rcases eq_or_ne j i with rfl | hj
    · simp
    · simp [hj]
  · rintro ⟨i, rfl⟩
    refine ⟨i, x i + 1, Order.covBy_iff_add_one_eq.2 rfl, funext fun j => ?_⟩
    rcases eq_or_ne j i with rfl | hj
    · simp
    · simp [hj]

end Site

/-! ### The nearest-neighbour graph on `ℤ^d` -/

variable {d : ℕ}

/-- The nearest-neighbour graph on `ℤ^d`: `x ∼ y` iff `x` and `y` differ by a unit coordinate
vector. Defined as Mathlib's Hasse diagram of the product partial order on `Fin d → ℤ`
(see `zdGraph_adj_iff` for the equivalence). (Friedli–Velenik 2017, §3.1.) [cite: FriedliVelenikSMLS2017, §3.1] -/
noncomputable abbrev zdGraph (d : ℕ) : SimpleGraph (Site d) := SimpleGraph.hasse (Site d)

/-- Adjacency in `ℤ^d`: `x ∼ y` iff `y = x + eᵢ` or `x = y + eᵢ` for some coordinate `i`.
(Friedli–Velenik 2017, §3.1.) [cite: FriedliVelenikSMLS2017, §3.1] -/
theorem zdGraph_adj_iff (x y : Site d) :
    (zdGraph d).Adj x y ↔ ∃ i, y = x + Pi.single i 1 ∨ x = y + Pi.single i 1 := by
  rw [SimpleGraph.hasse_adj, Site.covBy_iff, Site.covBy_iff, ← exists_or]

/-- Adjacency in `ℤ^d` is decidable (via `zdGraph_adj_iff`). (Friedli–Velenik 2017, §3.1.) [cite: FriedliVelenikSMLS2017, §3.1] -/
instance : DecidableRel (zdGraph d).Adj := fun x y =>
  decidable_of_iff _ (zdGraph_adj_iff x y).symm

/-- `ℤ^d` is locally finite: the neighbours of `x` are among the `2d` points `x ± eᵢ`.
(Friedli–Velenik 2017, §3.1.) [cite: FriedliVelenikSMLS2017, §3.1] -/
instance : (zdGraph d).LocallyFinite := fun x =>
  Fintype.ofFinset
    (((univ : Finset (Fin d × Bool)).image fun p =>
        if p.2 then x + Pi.single p.1 1 else x - Pi.single p.1 1).filter
      fun y => (zdGraph d).Adj x y)
    (by
      intro y
      simp only [mem_filter, mem_image, mem_univ, true_and, SimpleGraph.mem_neighborSet,
        and_iff_right_iff_imp]
      intro h
      obtain ⟨i, h | h⟩ := (zdGraph_adj_iff x y).1 h
      · exact ⟨(i, true), by simp [h]⟩
      · exact ⟨(i, false), by simp [h]⟩)

/-- The nearest-neighbour graph is translation invariant. (Friedli–Velenik 2017, §3.1.)
Not a `simp` lemma: `zdGraph` is reducible, so `simp` unfolds adjacency via `SimpleGraph.hasse_adj`
first. [cite: FriedliVelenikSMLS2017, §3.1] -/
theorem zdGraph_adj_shift_iff (v x y : Site d) :
    (zdGraph d).Adj (Site.shift v x) (Site.shift v y) ↔ (zdGraph d).Adj x y := by
  simp only [zdGraph_adj_iff, Site.shift_apply, add_right_comm _ v, add_left_inj]

/-! ### Finite-volume boundaries in a locally finite graph -/

section Boundary

variable {V : Type*} (G : SimpleGraph V)

/-- The outer (exterior) vertex boundary `∂ᵉˣΛ` of a finite vertex set `Λ`: the vertices outside
`Λ` adjacent to some vertex of `Λ`. (Friedli–Velenik 2017, §3.6.3, `∂ᵉˣΔ`, after (3.26).)
[cite: FriedliVelenikSMLS2017, §3.6.3 (exterior boundary, after (3.26))] -/
def outerBoundary [DecidableEq V] [G.LocallyFinite] (Λ : Finset V) : Finset V :=
  (Λ.biUnion fun x => G.neighborFinset x) \ Λ

/-- The inner (interior) vertex boundary `∂ⁱⁿΛ`: the vertices of `Λ` adjacent to some vertex
outside `Λ`. (Friedli–Velenik 2017, §3.2.1, `∂ⁱⁿΛ`, after (3.3).) [cite: FriedliVelenikSMLS2017, §3.2.1 (interior boundary, after (3.3))] -/
def innerBoundary [DecidableEq V] [G.LocallyFinite] (Λ : Finset V) : Finset V :=
  Λ.filter fun x => ∃ y ∈ G.neighborFinset x, y ∉ Λ

/-- The edges of `G` with at least one endpoint in `Λ` (Friedli–Velenik 2017, §3.1, `ℰ_Λ^b`,
used for non-free boundary conditions). [cite: FriedliVelenikSMLS2017, §3.1 (the edge set ℰ_Λ^b)] -/
def edgesTouching [DecidableEq V] [G.LocallyFinite] (Λ : Finset V) : Finset (Sym2 V) :=
  Λ.biUnion fun x => G.incidenceFinset x

/-- The edges of `G` with both endpoints in `Λ` (Friedli–Velenik 2017, §3.1, `ℰ_Λ`, free
boundary condition), as the sub-finset of `edgesTouching G Λ` of edges lying in `Λ.sym2`
(this phrasing keeps the instance requirements at `[DecidableEq V] [G.LocallyFinite]`). [cite: FriedliVelenikSMLS2017, §3.1 (the edge set ℰ_Λ, free boundary condition)] -/
def edgesIn [DecidableEq V] [G.LocallyFinite] (Λ : Finset V) : Finset (Sym2 V) :=
  (edgesTouching G Λ).filter fun e => e ∈ Λ.sym2

/-- The edge boundary of `Λ`: edges of `G` with exactly one endpoint in `Λ`, i.e.
`edgesTouching G Λ \ edgesIn G Λ`. (Friedli–Velenik 2017, §3.1.) [cite: FriedliVelenikSMLS2017, §3.1] -/
def edgeBoundary [DecidableEq V] [G.LocallyFinite] (Λ : Finset V) :
    Finset (Sym2 V) :=
  edgesTouching G Λ \ edgesIn G Λ

variable {G}

/-- Membership in the outer boundary. (Friedli–Velenik 2017, §3.1.) [cite: FriedliVelenikSMLS2017, §3.1] -/
@[simp] theorem mem_outerBoundary_iff [DecidableEq V] [G.LocallyFinite] {Λ : Finset V} {x : V} :
    x ∈ outerBoundary G Λ ↔ x ∉ Λ ∧ ∃ y ∈ Λ, G.Adj x y := by
  simp only [outerBoundary, mem_sdiff, mem_biUnion, SimpleGraph.mem_neighborFinset]
  constructor
  · rintro ⟨⟨y, hy, h⟩, hx⟩
    exact ⟨hx, y, hy, h.symm⟩
  · rintro ⟨hx, y, hy, h⟩
    exact ⟨⟨y, hy, h.symm⟩, hx⟩

/-- Membership in the inner boundary. (Friedli–Velenik 2017, §3.1.) [cite: FriedliVelenikSMLS2017, §3.1] -/
@[simp] theorem mem_innerBoundary_iff [DecidableEq V] [G.LocallyFinite] {Λ : Finset V} {x : V} :
    x ∈ innerBoundary G Λ ↔ x ∈ Λ ∧ ∃ y ∉ Λ, G.Adj x y := by
  simp only [innerBoundary, mem_filter, SimpleGraph.mem_neighborFinset]
  exact and_congr_right fun _ => ⟨fun ⟨y, h, hy⟩ => ⟨y, hy, h⟩, fun ⟨y, hy, h⟩ => ⟨y, h, hy⟩⟩

/-- Membership in `edgesTouching`: an edge of `G` with some endpoint in `Λ`.
(Friedli–Velenik 2017, §3.1.) [cite: FriedliVelenikSMLS2017, §3.1] -/
@[simp] theorem mem_edgesTouching_iff [DecidableEq V] [G.LocallyFinite] {Λ : Finset V} {e : Sym2 V} :
    e ∈ edgesTouching G Λ ↔ e ∈ G.edgeSet ∧ ∃ x ∈ Λ, x ∈ e := by
  simp only [edgesTouching, mem_biUnion, SimpleGraph.mem_incidenceFinset,
    SimpleGraph.incidenceSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, hx, he, hxe⟩
    exact ⟨he, x, hx, hxe⟩
  · rintro ⟨he, x, hx, hxe⟩
    exact ⟨x, hx, he, hxe⟩

/-- Membership in `edgesIn`: an edge of `G` all of whose endpoints lie in `Λ`.
(Friedli–Velenik 2017, §3.1.) [cite: FriedliVelenikSMLS2017, §3.1] -/
@[simp] theorem mem_edgesIn_iff [DecidableEq V] [G.LocallyFinite] {Λ : Finset V} {e : Sym2 V} :
    e ∈ edgesIn G Λ ↔ e ∈ G.edgeSet ∧ ∀ x ∈ e, x ∈ Λ := by
  simp only [edgesIn, mem_filter, mem_edgesTouching_iff, Finset.mem_sym2_iff, and_assoc,
    and_congr_right_iff]
  intro _
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  induction e using Sym2.ind with
  | _ a b => exact ⟨a, h a (Sym2.mem_mk_left a b), Sym2.mem_mk_left a b⟩

/-- Membership in the edge boundary: an edge of `G` with an endpoint in `Λ` and an endpoint
outside `Λ`. (Friedli–Velenik 2017, §3.1.) [cite: FriedliVelenikSMLS2017, §3.1] -/
@[simp] theorem mem_edgeBoundary_iff [DecidableEq V] [G.LocallyFinite]
    {Λ : Finset V} {e : Sym2 V} :
    e ∈ edgeBoundary G Λ ↔ e ∈ G.edgeSet ∧ (∃ x ∈ Λ, x ∈ e) ∧ ∃ x ∉ Λ, x ∈ e := by
  simp only [edgeBoundary, mem_sdiff, mem_edgesTouching_iff, mem_edgesIn_iff, not_and,
    not_forall]
  constructor
  · rintro ⟨⟨he, hx⟩, h⟩
    obtain ⟨y, hy, hyΛ⟩ := h he
    exact ⟨he, hx, y, hyΛ, hy⟩
  · rintro ⟨he, hx, y, hyΛ, hy⟩
    exact ⟨⟨he, hx⟩, fun _ => ⟨y, hy, hyΛ⟩⟩

/-- `ℰ_Λ ⊆ ℰ_Λ^b`: an edge with both endpoints in `Λ` has an endpoint in `Λ`.
(Friedli–Velenik 2017, §3.1.) [cite: FriedliVelenikSMLS2017, §3.1] -/
theorem edgesIn_subset_edgesTouching [DecidableEq V] [G.LocallyFinite]
    (Λ : Finset V) : edgesIn G Λ ⊆ edgesTouching G Λ :=
  Finset.filter_subset _ _

end Boundary

end Percolation.Literature.LatticeModels

