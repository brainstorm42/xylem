import Percolation.Literature.SlabGluingRecovery
import Percolation.Literature.SlabGluingSurgery
import Percolation.Util.Linter

/-!
# DST 2016, §2.3, Fact 2 — the local surgery `ω ↦ ω^{(z)}`: the geometry-free core

Fact 2 (DST 2016, §2.3, pp. 6–7; Newman–Tassion–Wu 2017, §3.2, proof of Thm. 3.9) rests on a
**local surgery**: for `ω ∈ 𝒳` and a point `z ∈ U(ω)`, clear a ball of columns around `z`,
reroute the minimal path `γ = γ_min(ω)` through it, and attach a branch to the `S'_n`-side path
`π` of (P2), producing `ω^{(z)} ∈ C = {S_{3n} ⟷ S'_n}`; then **recover** `z` from `ω^{(z)}`
alone through the statistic "the vertices of `γ_min(ω^{(z)})` joined to `S̄'_n` off
`γ_min(ω^{(z)})`" (p. 7). This file proves everything about one surgery that does not depend
on the shape of the rerouting — the geometry (which columns, which lattice paths) is abstracted
into the data `GlueGeom.Surgery`:

* `GlueGeom.Surgery G k ω` — the data: cleared columns `D ⊆ B_{3n} ∪ B'_n`; the decomposition
  `γ_min(ω) = p₀ ++ E₁ :: mid ++ E₂ :: s₀` at the first and last visits `E₁, E₂` of `D̄`
  (`p₀, s₀ ≠ []` off `D̄`); the rerouted piece `P` (`E₁ :: P ++ [E₂]` a self-avoiding lattice
  chain inside `D̄ ∩ B̄_{3n}`, off `Z̄_n`); the attachment vertex `c ∈ E₁ :: P` and the branch
  `Br` to `w' = Br.last` (inside `D̄`, off the rerouted piece); DST's order condition
  "`(z,v) ≺ (z,w)`" as `key (successor of c) < key (Br.head)`; a key condition over `S_{3n}`
  (structure vertices there do not undercut `γ_0`); and the `S'`-side `ω`-open path `σ` from
  `w'` to `S̄'_n` inside `B̄'_n`, off the columns of `γ`, off `D̄` after its first vertex.
* `Surgery.exists_tail` — proved: **`γ_min(ω^{(z)}) = p₀ ++ E₁ :: P ++ E₂ :: tail`** (DST:
  "`γ_min(ω^{(z)})` and `γ_min(ω)` coincide at least until `u'` … the fact that it contains `u'`
  forces it to go inside … it must contain `z`", p. 7), by the exchange lemma
  `minPath_prefix_of_surgery` (`SlabGluingSurgery.lean`) applied with the prefix `p₀ ++ [E₁]`
  ending AT the first cleared vertex — so that the local forcing at the junction holds (all other
  edges at `E₁` are closed) — and the forced piece `P ++ [E₂]`.
* `Surgery.tail_head`, `tail_props`, `tail_not_D` — proved: the continuation `tail` leaves through
  the old exit edge and stays in the old world: off the structure, off `D̄`, `ω`-joined to
  `S̄_{3n}` (propagation lemma `not_mem_structure_of_pathIn`, `SlabGluingRecovery.lean`).
* `GlueGeom.att` — DST's recovery statistic `Att(ω')` (a function of `ω'` alone), and proved:
  **`c ∈ Att(ω^{(z)})`** (`c_mem_att`: the branch, the stub and `σ`) and
  **`Att(ω^{(z)}) ⊆ D̄`** (`att_subset`: a vertex of `γ_min(ω^{(z)})` off `D̄` is `ω`-joined to
  `S̄_{3n}`, and an `ω^{(z)}`-open path from it to `S̄'_n` avoiding the rest of
  `γ_min(ω^{(z)})` cannot enter the structure, so it is `ω`-open and yields `C(ω)`), together
  with `newConfig_mem_evC` (**`ω^{(z)} ∈ C`**).

What is left for Fact 2 after this file: (i) the ROUTING — producing a `Surgery` with
`D ⊆ z + B_2` for every `z` of (a cofinite-per-`ω` subset of) `U'(ω)` (DST: "three disjoint
self-avoiding paths inside `B̄_{R-1}(z)`", `R = 2` for slabs; NTW Definition 3.7), and (ii) the
bookkeeping of Lemma 7 (`lemma7_bond`, `SlabGluingFact1.lean`) over a separated sub-family of
`U'(ω)`, with injectivity and the recovery window read off `Att`.

## Sources

* H. Duminil-Copin, V. Sidoravicius, V. Tassion, *Absence of infinite cluster for critical
  Bernoulli percolation on slabs*, CPAM 69 (2016), 1397–1411, arXiv:1401.7130: §2.3, proof of
  Fact 2 (pp. 6–7 of the arXiv text: the construction (1)–(3) of `ω^{(z)}`, "the minimality of
  `γ_min(ω)` … implies", "`z` is the only vertex in `γ_min(ω^{(z)})` which is connected to `S'_n`
  in `B'_n ∖ γ_min(ω^{(z)})`").
* C. M. Newman, V. Tassion, W. Wu, *Critical percolation and the minimal spanning tree in
  slabs*, CPAM 70 (2017), 2084–2120, doi:10.1002/cpa.21714: §3.2, proof of Thm. 3.9, steps
  (1)–(3) and the recovery sentence (PDF pp. 13–14 of the held copy) [NewmanTassionWu2017].

## Design choices

* The prefix kept from `γ` ends at `E₁`, the first vertex of `γ` in `D̄` (not at the last
  vertex before `D̄`): all non-structure edges at `E₁` are closed, so the local forcing
  hypothesis of `minPath_prefix_of_surgery` holds at the junction; likewise the kept suffix
  starts at `E₂`. Only the prefix statement is used downstream (the printed "coincide from `v'`
  to the end" is not needed): the continuation `tail` is controlled qualitatively
  (`tail_props`).
* `Att` uses the region `B̄_{3n} ∪ B̄'_n` (that of `C`), and only `Att ⊆ D̄`, `c ∈ Att` are
  proved (not `Att = {c}`): a bounded window around any element of `Att` is all the recovery
  needs.
* No geometry: `D` is any set of columns inside `B_{3n} ∪ B'_n`; `P`, `Br`, `σ` are lists with
  the listed properties. The three stubs are `ω`-open old edges, so `ω^{(z)} ⊆ ω ∪ structEdges`.
-/

noncomputable section

namespace Percolation.Literature

open MeasureTheory LatticeModels SimpleGraph Filter Topology

/-! ## List and edge helpers -/

section Helpers

variable {α : Type*}

/-- In a list without duplicates an element determines its split. [folklore] -/
theorem split_unique {l₁ l₂ r₁ r₂ : List α} {x : α} (h : l₁ ++ x :: r₁ = l₂ ++ x :: r₂)
    (h₁ : x ∉ l₁) (h₂ : x ∉ l₂) : l₁ = l₂ ∧ r₁ = r₂ := by
  rcases List.append_eq_append_iff.1 h with ⟨a', hl₂, hr⟩ | ⟨c', hl₁, hr⟩
  · cases a' with
    | nil => simp only [List.append_nil] at hl₂; simp only [List.nil_append] at hr
             exact ⟨hl₂.symm, (List.cons.inj hr).2⟩
    | cons y a'' =>
      exfalso
      have hy : y = x := (List.cons.inj hr).1.symm
      apply h₂; rw [hl₂, hy]; simp
  · cases c' with
    | nil => simp only [List.append_nil] at hl₁; simp only [List.nil_append] at hr
             exact ⟨hl₁, (List.cons.inj hr).2.symm⟩
    | cons y c'' =>
      exfalso
      have hy : y = x := (List.cons.inj hr).1.symm
      apply h₁; rw [hl₁, hy]; simp

variable {V : Type*}

/-- The set of edges joining consecutive vertices of a list. [folklore] -/
def edgesOf (l : List V) : Set (Sym2 V) :=
  {e | ∃ (a b : V) (l₁ l₂ : List V), l = l₁ ++ a :: b :: l₂ ∧ e = s(a, b)}

/-- Consecutive vertices give an edge of `edgesOf`. [folklore] -/
theorem mem_edgesOf_of_eq {l l₁ l₂ : List V} {a b : V} (h : l = l₁ ++ a :: b :: l₂) :
    s(a, b) ∈ edgesOf l := ⟨a, b, l₁, l₂, h, rfl⟩

/-- Both endpoints of an edge of `edgesOf l` lie in `l`. [folklore] -/
theorem mem_of_mem_edgesOf {l : List V} {x y : V} (h : s(x, y) ∈ edgesOf l) : x ∈ l ∧ y ∈ l := by
  obtain ⟨a, b, l₁, l₂, hl, he⟩ := h
  have ha : a ∈ l := by rw [hl]; simp
  have hb : b ∈ l := by rw [hl]; simp
  rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨ha, hb⟩
  · exact ⟨hb, ha⟩

/-- A chain of adjacent vertices is a chain of `edgesOf`-edges (and of any larger edge set).
[folklore] -/
theorem isChain_of_edgesOf_subset {G : SimpleGraph V} {l : List V} {X : Set (Sym2 V)}
    (hl : l.IsChain (fun a b => G.Adj a b)) (hX : edgesOf l ⊆ X) :
    l.IsChain (fun a b => s(a, b) ∈ X ∧ a ≠ b) := by
  rw [List.isChain_iff_forall_rel_of_append_cons_cons] at hl ⊢
  intro a b l₁ l₂ h
  exact ⟨hX (mem_edgesOf_of_eq h), G.ne_of_adj (hl h)⟩

/-- The edges of a chain of adjacent vertices are edges of the graph. [folklore] -/
theorem edgesOf_subset_edgeSet {G : SimpleGraph V} {l : List V}
    (hl : l.IsChain (fun a b => G.Adj a b)) : edgesOf l ⊆ G.edgeSet := by
  rintro e ⟨a, b, l₁, l₂, h, rfl⟩
  rw [List.isChain_iff_forall_rel_of_append_cons_cons] at hl
  exact (SimpleGraph.mem_edgeSet G).2 (hl h)

/-- In a list without duplicates, an `edgesOf`-edge at `x` leads to the successor or to the
predecessor of `x`. [folklore] -/
theorem next_of_mem_edgesOf {l l₁ r : List V} {x q : V} (hnd : l.Nodup) (hl : l = l₁ ++ x :: r)
    (he : s(x, q) ∈ edgesOf l) : (∃ r', r = q :: r') ∨ ∃ l₁', l₁ = l₁' ++ [q] := by
  obtain ⟨a, b, m₁, m₂, hm, hab⟩ := he
  have hxl₁ : x ∉ l₁ := by
    intro hx
    rw [hl] at hnd
    exact (List.nodup_append.1 hnd).2.2 x hx x (by simp) rfl
  rcases Sym2.eq_iff.1 hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · -- `x = a`, `q = b`: `l = m₁ ++ x :: q :: m₂`
    have hxm₁ : x ∉ m₁ := by
      intro hx
      rw [hm] at hnd
      exact (List.nodup_append.1 hnd).2.2 x hx x (by simp) rfl
    obtain ⟨-, hr⟩ := split_unique (hl.symm.trans hm) hxl₁ hxm₁
    exact Or.inl ⟨m₂, hr⟩
  · -- `x = b`, `q = a`: `l = (m₁ ++ [q]) ++ x :: m₂`
    have hm' : l = (m₁ ++ [q]) ++ x :: m₂ := by rw [hm]; simp
    have hxm₁ : x ∉ m₁ ++ [q] := by
      intro hx
      rw [hm'] at hnd
      exact (List.nodup_append.1 hnd).2.2 x hx x (by simp) rfl
    obtain ⟨hl₁, -⟩ := split_unique (hl.symm.trans hm') hxl₁ hxm₁
    exact Or.inr ⟨m₁, hl₁⟩

/-- The head of a list without duplicates has a single `edgesOf`-edge, to the second element.
[folklore] -/
theorem eq_of_mem_edgesOf_head {c q : V} {l : List V} (hnd : (c :: l).Nodup)
    (he : s(c, q) ∈ edgesOf (c :: l)) : ∃ l', l = q :: l' := by
  rcases next_of_mem_edgesOf (l₁ := []) (r := l) hnd rfl he with h | ⟨l₁', h⟩
  · exact h
  · exact absurd h (by simp)

/-- The last element of a list without duplicates has a single `edgesOf`-edge, to its
predecessor. [folklore] -/
theorem eq_of_mem_edgesOf_last {x q : V} {l₁ : List V} (hnd : (l₁ ++ [x]).Nodup)
    (he : s(x, q) ∈ edgesOf (l₁ ++ [x])) : ∃ l₁', l₁ = l₁' ++ [q] := by
  rcases next_of_mem_edgesOf (r := []) hnd rfl he with ⟨r', h⟩ | h
  · exact absurd h (by simp)
  · exact h

end Helpers

/-! ## The surgery data and the new configuration -/

section SurgeryData

variable (k : ℕ)

/-- The lattice pairs touching the columns over `D` (the edges reset by the surgery).
[cite: DuminilCopinSidoraviciusTassion2016, §2.3, proof of Fact 2 ("Close all edges in `B̄_R(z)`")] -/
def touch (D : Set (ℤ × ℤ)) : Set (Sym2 (slab 3 k)) := {e | ∃ x, x ∈ e ∧ planar k x ∈ D}

variable {k}

/-- Membership of a pair in `touch D`. [folklore] -/
@[simp] theorem mk_mem_touch_iff {D : Set (ℤ × ℤ)} {a b : slab 3 k} :
    s(a, b) ∈ touch k D ↔ planar k a ∈ D ∨ planar k b ∈ D := by
  constructor
  · rintro ⟨x, hx, hxD⟩
    rcases Sym2.mem_iff.1 hx with rfl | rfl
    · exact Or.inl hxD
    · exact Or.inr hxD
  · rintro (h | h)
    · exact ⟨a, Sym2.mem_mk_left _ _, h⟩
    · exact ⟨b, Sym2.mem_mk_right _ _, h⟩

variable (k)

/-- **The data of one local surgery** (DST 2016, §2.3, proof of Fact 2, pp. 6–7; NTW 2017,
§3.2, proof of Thm. 3.9, steps (1)–(3)), in a geometry-free form. For `ω ∈ 𝒳` with
`γ = γ_min(ω) = p₀ ++ E₁ :: mid ++ E₂ :: s₀`: a set `D` of cleared columns (inside
`B_{3n} ∪ B'_n`) met by `γ` first at `E₁` and last at `E₂` (`p₀, s₀` off `D̄`, non-empty);
a rerouted piece `P` (inside `D̄ ∩ B̄_{3n}`, off `Z̄_n`) with `E₁ :: P ++ [E₂]` a self-avoiding
lattice chain; an attachment vertex `c ∈ E₁ :: P` and a branch `Br` (a self-avoiding lattice
chain from a neighbour of `c` to `w' = Br.last`, inside `D̄`, off `E₁ :: P ++ [E₂]`);
DST's condition "`(z,v) ≺ (z,w)`" in the form `key (successor of c) < key (Br.head)`; a key
condition for structure vertices over `S_{3n}` (they must not undercut `γ_0`); and the
`S'`-side path `σ` from `w'` to `S̄'_n` inside `B̄'_n`, `ω`-open, off the columns of `γ`, leaving
`D̄` after its first vertex (the stub edge). [cite: DuminilCopinSidoraviciusTassion2016, §2.3, proof of Fact 2 (pp. 6–7)] [cite: NewmanTassionWu2017, §3.2 (proof of Thm. 3.9, steps (1)–(3))] -/
structure GlueGeom.Surgery (G : GlueGeom) (ω : BondConfig (slab 3 k)) where
  /-- the cleared columns -/
  D : Set (ℤ × ℤ)
  /-- `γ_min(ω)` before its first visit to `D̄` -/
  p₀ : List (slab 3 k)
  /-- the first vertex of `γ_min(ω)` in `D̄` -/
  E₁ : slab 3 k
  /-- `γ_min(ω)` strictly between `E₁` and `E₂` -/
  mid : List (slab 3 k)
  /-- the last vertex of `γ_min(ω)` in `D̄` -/
  E₂ : slab 3 k
  /-- `γ_min(ω)` after its last visit to `D̄` -/
  s₀ : List (slab 3 k)
  /-- the rerouted piece (strictly between `E₁` and `E₂`) -/
  P : List (slab 3 k)
  /-- the attachment vertex -/
  c : slab 3 k
  /-- the branch, from a neighbour of `c` to `w'` -/
  Br : List (slab 3 k)
  /-- the `S'`-side path from `w'` -/
  σ : List (slab 3 k)
  hD : D ⊆ G.big ∪ G.small
  hγ : G.γmin k ω = p₀ ++ E₁ :: (mid ++ E₂ :: s₀)
  hp₀ : p₀ ≠ []
  hs₀ : s₀ ≠ []
  hp₀D : ∀ x ∈ p₀, planar k x ∉ D
  hs₀D : ∀ x ∈ s₀, planar k x ∉ D
  hE₁D : planar k E₁ ∈ D
  hE₂D : planar k E₂ ∈ D
  hPD : ∀ x ∈ P, planar k x ∈ D
  hPbig : ∀ x ∈ P, planar k x ∈ G.big
  hPY : ∀ x ∈ P, planar k x ∉ G.zSeg
  hSPchain : (E₁ :: (P ++ [E₂])).IsChain (fun a b => (slabGraph 3 k).Adj a b)
  hSPnodup : (E₁ :: (P ++ [E₂])).Nodup
  hc : c ∈ E₁ :: P
  hBr : Br ≠ []
  hBrD : ∀ x ∈ Br, planar k x ∈ D
  hBrchain : (c :: Br).IsChain (fun a b => (slabGraph 3 k).Adj a b)
  hBrnodup : (c :: Br).Nodup
  hBrSP : ∀ x ∈ Br, x ∉ E₁ :: (P ++ [E₂])
  hfwd : ∀ (l₁ l₂ : List (slab 3 k)) (y : slab 3 k), E₁ :: (P ++ [E₂]) = l₁ ++ c :: y :: l₂ →
    vKey k y < vKey k (Br.head hBr)
  hsrc : ∀ v ∈ P ++ Br.dropLast, v ∈ slabLift k G.src → v ∉ G.γmin k ω →
    ∀ b ∈ (G.γmin k ω).head?, vKey k b ≤ vKey k v
  hσ : σ.head? = some (Br.getLast hBr)
  hσchain : σ.IsChain (fun a b => s(a, b) ∈ ω ∧ a ≠ b)
  hσsmall : ∀ x ∈ σ, planar k x ∈ G.small
  hσγ : ∀ x ∈ σ, planar k x ∉ G.γcols k ω
  hσD : ∀ x ∈ σ.tail, planar k x ∉ D
  hσsrc' : ∀ h : σ ≠ [], σ.getLast h ∈ slabLift k G.src'

namespace GlueGeom.Surgery

variable {k} {G : GlueGeom} {ω : BondConfig (slab 3 k)} (sg : G.Surgery k ω)

/-- The rerouted structure path `E₁ :: P ++ [E₂]`. [cite: DuminilCopinSidoraviciusTassion2016, §2.3, proof of Fact 2] -/
def SP : List (slab 3 k) := sg.E₁ :: (sg.P ++ [sg.E₂])

/-- The end `w'` of the branch. [cite: DuminilCopinSidoraviciusTassion2016, §2.3, proof of Fact 2] -/
def w' : slab 3 k := sg.Br.getLast sg.hBr

/-- The new (opened) edges: those of the structure path and of the branch. [cite: DuminilCopinSidoraviciusTassion2016, §2.3, proof of Fact 2 ("Open the edges …")] -/
def structEdges : Set (Sym2 (slab 3 k)) := edgesOf sg.SP ∪ edgesOf (sg.c :: sg.Br)

/-- The kept edges entering `D̄`: the edge of `γ` into `E₁`, the edge of `γ` out of `E₂`, and
the first edge of `σ` (out of `w'`). [cite: DuminilCopinSidoraviciusTassion2016, §2.3, proof of Fact 2] -/
def stubs : Set (Sym2 (slab 3 k)) :=
  {s(sg.p₀.getLast sg.hp₀, sg.E₁), s(sg.E₂, sg.s₀.head sg.hs₀)} ∪
    {e | ∃ w₂ ∈ sg.σ.tail.head?, e = s(sg.w', w₂)}

/-- **The new configuration `ω^{(z)}`**: close every edge touching `D̄`, then open the structure
edges and the three stubs. [cite: DuminilCopinSidoraviciusTassion2016, §2.3, proof of Fact 2 (pp. 6–7)] -/
def newConfig : BondConfig (slab 3 k) := (ω \ touch k sg.D) ∪ sg.structEdges ∪ sg.stubs

/-- The structure vertices. [cite: DuminilCopinSidoraviciusTassion2016, §2.3, proof of Fact 2] -/
def Sw : Set (slab 3 k) := {x | x ∈ sg.SP ∨ x ∈ sg.Br}

/-! ### Elementary consequences of the data -/

/-- `σ` is non-empty. [folklore] -/
theorem σ_ne_nil : sg.σ ≠ [] := by
  intro h; have := sg.hσ; rw [h] at this; simp at this

/-- `σ` starts at `w'`. [folklore] -/
theorem σ_head : sg.σ.head sg.σ_ne_nil = sg.w' := by
  have := sg.hσ
  rw [List.head?_eq_some_head sg.σ_ne_nil, Option.some.injEq] at this
  exact this

/-- `w' ∈ Br`. [folklore] -/
theorem w'_mem_Br : sg.w' ∈ sg.Br := List.getLast_mem sg.hBr

/-- `E₁` lies on the structure path. [folklore] -/
theorem E₁_mem_SP : sg.E₁ ∈ sg.SP := by simp [SP]

/-- `E₂` lies on the structure path. [folklore] -/
theorem E₂_mem_SP : sg.E₂ ∈ sg.SP := by simp [SP]

/-- `c` lies on the structure path. [folklore] -/
theorem c_mem_SP : sg.c ∈ sg.SP := by
  rcases List.mem_cons.1 sg.hc with h | h
  · rw [h]; exact sg.E₁_mem_SP
  · simp [SP, h]

/-- Membership in the structure path. [folklore] -/
theorem mem_SP_iff {x : slab 3 k} : x ∈ sg.SP ↔ x = sg.E₁ ∨ x ∈ sg.P ∨ x = sg.E₂ := by
  simp [SP]

/-- The structure path lies in `D̄`. [folklore] -/
theorem SP_D {x : slab 3 k} (hx : x ∈ sg.SP) : planar k x ∈ sg.D := by
  rcases sg.mem_SP_iff.1 hx with rfl | h | rfl
  · exact sg.hE₁D
  · exact sg.hPD x h
  · exact sg.hE₂D

/-- Structure vertices lie in `D̄`. [folklore] -/
theorem Sw_D {x : slab 3 k} (hx : x ∈ sg.Sw) : planar k x ∈ sg.D := by
  rcases hx with h | h
  · exact sg.SP_D h
  · exact sg.hBrD x h

/-- `w'` is a structure vertex. [folklore] -/
theorem w'_mem_Sw : sg.w' ∈ sg.Sw := Or.inr sg.w'_mem_Br

/-- `w'` lies in `D̄`. [folklore] -/
theorem w'_D : planar k sg.w' ∈ sg.D := sg.hBrD _ sg.w'_mem_Br

/-- The attachment vertex is not `E₂`. [folklore] -/
theorem c_ne_E₂ : sg.c ≠ sg.E₂ := by
  intro h
  have hnd := sg.hSPnodup
  rcases List.mem_cons.1 sg.hc with h1 | h1
  · -- `E₁ = E₂`
    rw [h1] at h
    rw [h] at hnd
    exact (List.nodup_cons.1 hnd).1 (by simp)
  · rw [h] at h1
    have := (List.nodup_cons.1 hnd).2
    rw [List.nodup_append] at this
    exact this.2.2 _ h1 _ (by simp) rfl

/-- `E₁ ≠ E₂`. [folklore] -/
theorem E₁_ne_E₂ : sg.E₁ ≠ sg.E₂ := by
  intro h
  have hnd := sg.hSPnodup
  rw [h] at hnd
  exact (List.nodup_cons.1 hnd).1 (by simp)

/-- `w'` is off the structure path. [folklore] -/
theorem w'_not_mem_SP : sg.w' ∉ sg.SP := sg.hBrSP _ sg.w'_mem_Br

/-- The last vertex of `p₀` is off `D̄`. [folklore] -/
theorem p₀_last_not_D : planar k (sg.p₀.getLast sg.hp₀) ∉ sg.D := sg.hp₀D _ (List.getLast_mem _)

/-- The first vertex of `s₀` is off `D̄`. [folklore] -/
theorem s₀_head_not_D : planar k (sg.s₀.head sg.hs₀) ∉ sg.D := sg.hs₀D _ (List.head_mem _)

/-- The new edges join structure vertices. [folklore] -/
theorem structEdges_Sw {a b : slab 3 k} (h : s(a, b) ∈ sg.structEdges) : a ∈ sg.Sw ∧ b ∈ sg.Sw := by
  rcases h with h | h
  · obtain ⟨ha, hb⟩ := mem_of_mem_edgesOf h
    exact ⟨Or.inl ha, Or.inl hb⟩
  · obtain ⟨ha, hb⟩ := mem_of_mem_edgesOf h
    refine ⟨?_, ?_⟩
    · rcases List.mem_cons.1 ha with rfl | ha
      · exact Or.inl sg.c_mem_SP
      · exact Or.inr ha
    · rcases List.mem_cons.1 hb with rfl | hb
      · exact Or.inl sg.c_mem_SP
      · exact Or.inr hb

/-- The stubs are `ω`-open. [folklore] -/
theorem stubs_subset (hA : ω ∈ G.evA k) : sg.stubs ⊆ ω := by
  have hγO := (G.γmin_spec k hA).1
  have hch := hγO.chain
  rw [sg.hγ] at hch
  rintro e (he | ⟨w₂, hw₂, rfl⟩)
  · rcases he with rfl | rfl
    · -- the edge of `γ` into `E₁`
      obtain ⟨q, hq⟩ := List.exists_cons_of_ne_nil sg.hp₀ |>.imp fun _ h => h
      have h1 := List.isChain_append.1 hch
      have := h1.2.2 (sg.p₀.getLast sg.hp₀) (by rw [List.getLast?_eq_some_getLast sg.hp₀]; rfl) sg.E₁ (by simp)
      exact this.1
    · -- the edge of `γ` out of `E₂`
      have h1 := (List.isChain_append.1 hch).2.1
      rw [List.isChain_cons] at h1
      have h2 := h1.2
      have h3 := List.isChain_append.1 (show (sg.mid ++ sg.E₂ :: sg.s₀).IsChain _ from h2)
      have h4 := h3.2.1
      rw [List.isChain_cons] at h4
      have := h4.1 (sg.s₀.head sg.hs₀) (by rw [List.head?_eq_some_head sg.hs₀]; rfl)
      exact this.1
  · -- the first edge of `σ`
    have hσ := sg.hσchain
    have hh := sg.hσ
    rcases hσeq : sg.σ with _ | ⟨x, _ | ⟨y, t⟩⟩
    · rw [hσeq] at hh; simp at hh
    · rw [hσeq] at hw₂; simp at hw₂
    · rw [hσeq] at hh hw₂ hσ
      simp only [List.head?_cons, Option.some.injEq] at hh
      simp only [List.tail_cons, List.head?_cons, Option.mem_def, Option.some.injEq] at hw₂
      subst hh; subst hw₂
      exact (List.isChain_cons_cons.1 hσ).1.1

/-- The endpoints of a stub: one of `E₁, E₂, w'` and its partner outside `D̄`. [folklore] -/
theorem stubs_cases {q x : slab 3 k} (h : s(q, x) ∈ sg.stubs) :
    (x = sg.E₁ ∧ q = sg.p₀.getLast sg.hp₀) ∨ (q = sg.E₁ ∧ x = sg.p₀.getLast sg.hp₀) ∨
    (x = sg.E₂ ∧ q = sg.s₀.head sg.hs₀) ∨ (q = sg.E₂ ∧ x = sg.s₀.head sg.hs₀) ∨
    (x = sg.w' ∧ q ∈ sg.σ.tail.head?) ∨ (q = sg.w' ∧ x ∈ sg.σ.tail.head?) := by
  rcases h with h | ⟨w₂, hw₂, h⟩
  · rcases h with h | h
    · rcases Sym2.eq_iff.1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · rcases Sym2.eq_iff.1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · rcases Sym2.eq_iff.1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hw₂⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hw₂⟩))))

/-- The second vertex of `σ` is off `D̄`. [folklore] -/
theorem σ₂_not_D {w₂ : slab 3 k} (h : w₂ ∈ sg.σ.tail.head?) : planar k w₂ ∉ sg.D :=
  sg.hσD _ (List.mem_of_mem_head? h)

/-- A stub entering a vertex of `D̄` enters `E₁`, `E₂` or `w'`, from its fixed partner. [folklore] -/
theorem stubs_cases_D {q x : slab 3 k} (h : s(q, x) ∈ sg.stubs) (hx : planar k x ∈ sg.D) :
    (x = sg.E₁ ∧ q = sg.p₀.getLast sg.hp₀) ∨ (x = sg.E₂ ∧ q = sg.s₀.head sg.hs₀) ∨
    (x = sg.w' ∧ q ∈ sg.σ.tail.head?) := by
  rcases sg.stubs_cases h with h | ⟨-, rfl⟩ | h | ⟨-, rfl⟩ | h | ⟨-, h⟩
  · exact Or.inl h
  · exact absurd hx sg.p₀_last_not_D
  · exact Or.inr (Or.inl h)
  · exact absurd hx sg.s₀_head_not_D
  · exact Or.inr (Or.inr h)
  · exact absurd hx (sg.σ₂_not_D h)

/-- Stubs touch `D̄`. [folklore] -/
theorem stubs_touch : sg.stubs ⊆ touch k sg.D := by
  intro e he
  induction e using Sym2.ind with
  | h q x =>
    rcases sg.stubs_cases he with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact mk_mem_touch_iff.2 (Or.inr sg.hE₁D)
    · exact mk_mem_touch_iff.2 (Or.inl sg.hE₁D)
    · exact mk_mem_touch_iff.2 (Or.inr sg.hE₂D)
    · exact mk_mem_touch_iff.2 (Or.inl sg.hE₂D)
    · exact mk_mem_touch_iff.2 (Or.inr sg.w'_D)
    · exact mk_mem_touch_iff.2 (Or.inl sg.w'_D)

/-- Structure edges touch `D̄`. [folklore] -/
theorem structEdges_touch : sg.structEdges ⊆ touch k sg.D := by
  intro e he
  induction e using Sym2.ind with
  | h a b => exact mk_mem_touch_iff.2 (Or.inl (sg.Sw_D (sg.structEdges_Sw he).1))

/-- **Locality**: off the pairs touching `D̄`, the new configuration is the old one. [folklore] -/
theorem mem_newConfig_iff_of_not_touch {e : Sym2 (slab 3 k)} (he : e ∉ touch k sg.D) :
    e ∈ sg.newConfig ↔ e ∈ ω := by
  constructor
  · rintro ((h | h) | h)
    · exact h.1
    · exact absurd (sg.structEdges_touch h) he
    · exact absurd (sg.stubs_touch h) he
  · exact fun h => Or.inl (Or.inl ⟨h, he⟩)

/-- `ω' ⊆ ω ∪ Enew`. [folklore] -/
theorem newConfig_subset (hA : ω ∈ G.evA k) : sg.newConfig ⊆ ω ∪ sg.structEdges := by
  rintro e ((h | h) | h)
  · exact Or.inl h.1
  · exact Or.inr h
  · exact Or.inl (sg.stubs_subset hA h)

/-- A new-open pair at a vertex of `D̄` is a structure edge or a stub. [folklore] -/
theorem edge_at_D {q x : slab 3 k} (h : s(q, x) ∈ sg.newConfig) (hx : planar k x ∈ sg.D) :
    s(q, x) ∈ sg.structEdges ∨ s(q, x) ∈ sg.stubs := by
  rcases h with ((h | h) | h)
  · exact absurd (mk_mem_touch_iff.2 (Or.inr hx)) h.2
  · exact Or.inl h
  · exact Or.inr h

/-- **Every new-open edge into `D̄` ends at a structure vertex.** [folklore] -/
theorem mem_Sw_of_edge {q x : slab 3 k} (h : s(q, x) ∈ sg.newConfig) (hx : planar k x ∈ sg.D) :
    x ∈ sg.Sw := by
  rcases sg.edge_at_D h hx with h | h
  · exact (sg.structEdges_Sw h).2
  · rcases sg.stubs_cases_D h hx with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact Or.inl sg.E₁_mem_SP
    · exact Or.inl sg.E₂_mem_SP
    · exact sg.w'_mem_Sw

/-- The protected structure vertices: all but `w'`. [cite: DuminilCopinSidoraviciusTassion2016, §2.3, proof of Fact 2] -/
def Wv : Set (slab 3 k) := sg.Sw \ {sg.w'}

/-- Protected vertices are structure vertices. [folklore] -/
theorem Wv_subset : sg.Wv ⊆ sg.Sw := fun _ h => h.1

/-- New-open edges into protected vertices come from structure vertices, except the two stubs
into `E₁` and `E₂`. [folklore] -/
theorem edge_into_Wv {t x : slab 3 k} (h : s(t, x) ∈ sg.newConfig) (hx : x ∈ sg.Wv) :
    t ∈ sg.Sw ∨ x ∈ ({sg.E₁, sg.E₂} : Set (slab 3 k)) := by
  have hxD := sg.Sw_D hx.1
  rcases sg.edge_at_D h hxD with h | h
  · exact Or.inl (sg.structEdges_Sw h).1
  · rcases sg.stubs_cases_D h hxD with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨h1, -⟩
    · exact Or.inr (by simp)
    · exact Or.inr (by simp)
    · exact absurd h1 hx.2

end GlueGeom.Surgery

end SurgeryData

/-! ## The rerouted path and the exchange argument -/

section Exchange

namespace GlueGeom.Surgery

variable {k : ℕ} {G : GlueGeom} {ω : BondConfig (slab 3 k)} (sg : G.Surgery k ω)

/-- `γ_min(ω)` in decomposed form is an open self-avoiding path. [folklore] -/
theorem γ_isOSAP (hA : ω ∈ G.evA k) :
    IsOSAP k ω (slabLift k G.big) (slabLift k G.src) (slabLift k G.zSeg)
      (sg.p₀ ++ sg.E₁ :: (sg.mid ++ sg.E₂ :: sg.s₀)) := by
  have := (G.γmin_spec k hA).1
  rwa [sg.hγ] at this

/-- `p₀ ⊆ γ`. [folklore] -/
theorem mem_γ_of_mem_p₀ {x : slab 3 k} (hx : x ∈ sg.p₀) : x ∈ G.γmin k ω := by
  rw [sg.hγ]; exact List.mem_append_left _ hx

/-- `s₀ ⊆ γ`. [folklore] -/
theorem mem_γ_of_mem_s₀ {x : slab 3 k} (hx : x ∈ sg.s₀) : x ∈ G.γmin k ω := by
  rw [sg.hγ]; simp [hx]

/-- `E₁ ∈ γ`. [folklore] -/
theorem E₁_mem_γ : sg.E₁ ∈ G.γmin k ω := by rw [sg.hγ]; simp

/-- `E₂ ∈ γ`. [folklore] -/
theorem E₂_mem_γ : sg.E₂ ∈ G.γmin k ω := by rw [sg.hγ]; simp

/-- `p₀` is off the structure. [folklore] -/
theorem p₀_not_Sw {x : slab 3 k} (hx : x ∈ sg.p₀) : x ∉ sg.Sw := fun h => sg.hp₀D x hx (sg.Sw_D h)

/-- `s₀` is off the structure. [folklore] -/
theorem s₀_not_Sw {x : slab 3 k} (hx : x ∈ sg.s₀) : x ∉ sg.Sw := fun h => sg.hs₀D x hx (sg.Sw_D h)

/-- The `γ`-edge into `E₁`. [folklore] -/
theorem γ_rel_p₀_E₁ (hA : ω ∈ G.evA k) :
    s(sg.p₀.getLast sg.hp₀, sg.E₁) ∈ ω ∧ sg.p₀.getLast sg.hp₀ ≠ sg.E₁ := by
  have hch := (sg.γ_isOSAP hA).chain
  exact (List.isChain_append.1 hch).2.2 (sg.p₀.getLast sg.hp₀)
    (by rw [List.getLast?_eq_some_getLast sg.hp₀]; rfl) sg.E₁ (by simp)

/-- The `γ`-edge out of `E₂`. [folklore] -/
theorem γ_rel_E₂_s₀ (hA : ω ∈ G.evA k) :
    s(sg.E₂, sg.s₀.head sg.hs₀) ∈ ω ∧ sg.E₂ ≠ sg.s₀.head sg.hs₀ := by
  have hch := (sg.γ_isOSAP hA).chain
  have h1 := (List.isChain_append.1 hch).2.1
  rw [List.isChain_cons] at h1
  have h3 := (List.isChain_append.1 h1.2).2.1
  rw [List.isChain_cons] at h3
  exact h3.1 (sg.s₀.head sg.hs₀) (by rw [List.head?_eq_some_head sg.hs₀]; rfl)

/-- The chain of `γ` on `s₀`. [folklore] -/
theorem γ_chain_s₀ (hA : ω ∈ G.evA k) : sg.s₀.IsChain (fun a b => s(a, b) ∈ ω ∧ a ≠ b) := by
  have hch := (sg.γ_isOSAP hA).chain
  have h1 := (List.isChain_append.1 hch).2.1
  rw [List.isChain_cons] at h1
  have h3 := (List.isChain_append.1 h1.2).2.1
  rw [List.isChain_cons] at h3
  exact h3.2

/-- The head of `γ` is the head of `p₀`. [folklore] -/
theorem γ_head? : (G.γmin k ω).head? = some (sg.p₀.head sg.hp₀) := by
  rw [sg.hγ, List.head?_append, List.head?_eq_some_head sg.hp₀]; rfl

/-- `γ` starts in `S̄_{3n}`. [folklore] -/
theorem p₀_head_mem_src (hA : ω ∈ G.evA k) : sg.p₀.head sg.hp₀ ∈ slabLift k G.src := by
  have h := (sg.γ_isOSAP hA).head_mem (by simp)
  rwa [List.head_append_of_ne_nil sg.hp₀] at h

/-- `γ` ends in `Z̄_n`. [folklore] -/
theorem s₀_last_mem_Y (hA : ω ∈ G.evA k) : sg.s₀.getLast sg.hs₀ ∈ slabLift k G.zSeg := by
  have h := (sg.γ_isOSAP hA).last_mem (by simp)
  rwa [List.getLast_append_of_ne_nil _ (by simp), List.getLast_cons (by simp),
    List.getLast_append_of_ne_nil _ (by simp), List.getLast_cons sg.hs₀] at h

/-- `γ ⊆ B̄_{3n}`. [folklore] -/
theorem γ_subset_big (hA : ω ∈ G.evA k) {x : slab 3 k} (hx : x ∈ G.γmin k ω) :
    x ∈ slabLift k G.big :=
  (G.γmin_spec k hA).1.subset x hx

/-- An `ω`-open pair with both endpoints off `D̄` stays open. [folklore] -/
theorem mem_newConfig_of_off {a b : slab 3 k} (hab : s(a, b) ∈ ω) (ha : planar k a ∉ sg.D)
    (hb : planar k b ∉ sg.D) : s(a, b) ∈ sg.newConfig :=
  (sg.mem_newConfig_iff_of_not_touch (by simp [ha, hb])).2 hab

/-- Structure edges are new-open. [folklore] -/
theorem structEdges_subset_newConfig : sg.structEdges ⊆ sg.newConfig := fun _ h => Or.inl (Or.inr h)

/-- Stubs are new-open. [folklore] -/
theorem stubs_subset_newConfig : sg.stubs ⊆ sg.newConfig := fun _ h => Or.inr h

/-- The stub into `E₁` is new-open. [folklore] -/
theorem stub₁_mem : s(sg.p₀.getLast sg.hp₀, sg.E₁) ∈ sg.newConfig :=
  sg.stubs_subset_newConfig (Or.inl (by simp))

/-- The stub out of `E₂` is new-open. [folklore] -/
theorem stub₂_mem : s(sg.E₂, sg.s₀.head sg.hs₀) ∈ sg.newConfig :=
  sg.stubs_subset_newConfig (Or.inl (by simp))

/-- The stub out of `w'` is new-open. [folklore] -/
theorem stub₃_mem {w₂ : slab 3 k} (h : w₂ ∈ sg.σ.tail.head?) : s(sg.w', w₂) ∈ sg.newConfig :=
  sg.stubs_subset_newConfig (Or.inr ⟨w₂, h, rfl⟩)

/-- The rerouted path `T = p₀ ++ E₁ :: P ++ E₂ :: s₀`. [cite: DuminilCopinSidoraviciusTassion2016, §2.3, proof of Fact 2] -/
abbrev T : List (slab 3 k) := sg.p₀ ++ (sg.SP ++ sg.s₀)

/-- The structure path ends at `E₂`. [folklore] -/
theorem SP_getLast? : sg.SP.getLast? = some sg.E₂ := by
  simp [SP, List.getLast?_eq_some_getLast]

/-- **`T` is an open self-avoiding path of `ω^{(z)}` from `S̄_{3n}` to `Z̄_n` inside `B̄_{3n}`.**
[cite: DuminilCopinSidoraviciusTassion2016, §2.3, proof of Fact 2] -/
theorem isOSAP_T (hA : ω ∈ G.evA k) :
    IsOSAP k sg.newConfig (slabLift k G.big) (slabLift k G.src) (slabLift k G.zSeg) sg.T := by
  have hγO := sg.γ_isOSAP hA
  have hγnd := hγO.nodup
  rw [List.nodup_append] at hγnd
  obtain ⟨hp₀nd, hrestnd, hp₀rest⟩ := hγnd
  have hs₀nd : sg.s₀.Nodup :=
    (List.nodup_cons.1 (List.nodup_append.1 (List.nodup_cons.1 hrestnd).2).2.1).2
  have hγch := hγO.chain
  refine ⟨?_, ?_, ?_, by simp [T, sg.hp₀], ?_, ?_⟩
  · -- nodup
    rw [List.nodup_append, List.nodup_append]
    refine ⟨hp₀nd, ⟨sg.hSPnodup, hs₀nd, fun a ha b hb hab => ?_⟩, fun a ha b hb hab => ?_⟩
    · exact sg.hs₀D b hb (hab ▸ sg.SP_D ha)
    · rcases List.mem_append.1 hb with hb | hb
      · exact sg.hp₀D a ha (hab ▸ sg.SP_D hb)
      · exact hp₀rest a ha b (by simp [hb]) hab
  · -- chain
    refine List.IsChain.append ?_ (List.IsChain.append ?_ ?_ ?_) ?_
    · exact (List.isChain_append.1 hγch).1.imp_of_mem_imp fun a b ha hb h =>
        ⟨sg.mem_newConfig_of_off h.1 (sg.hp₀D a ha) (sg.hp₀D b hb), h.2⟩
    · exact isChain_of_edgesOf_subset sg.hSPchain
        (fun e he => sg.structEdges_subset_newConfig (Or.inl he))
    · exact (sg.γ_chain_s₀ hA).imp_of_mem_imp fun a b ha hb h =>
        ⟨sg.mem_newConfig_of_off h.1 (sg.hs₀D a ha) (sg.hs₀D b hb), h.2⟩
    · intro x hx y hy
      rw [sg.SP_getLast?, Option.mem_def, Option.some.injEq] at hx
      rw [List.head?_eq_some_head sg.hs₀, Option.mem_def, Option.some.injEq] at hy
      subst hx; subst hy
      exact ⟨sg.stub₂_mem, (sg.γ_rel_E₂_s₀ hA).2⟩
    · intro x hx y hy
      rw [List.getLast?_eq_some_getLast sg.hp₀, Option.mem_def, Option.some.injEq] at hx
      have : y = sg.E₁ := by
        simp only [SP, List.cons_append, List.head?_cons, Option.mem_def, Option.some.injEq] at hy
        exact hy.symm
      subst hx; subst this
      exact ⟨sg.stub₁_mem, (sg.γ_rel_p₀_E₁ hA).2⟩
  · -- inside `B̄_{3n}`
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact γ_subset_big hA (sg.mem_γ_of_mem_p₀ hx)
    rcases List.mem_append.1 hx with hx | hx
    · rcases sg.mem_SP_iff.1 hx with rfl | h | rfl
      · exact γ_subset_big hA sg.E₁_mem_γ
      · exact sg.hPbig x h
      · exact γ_subset_big hA sg.E₂_mem_γ
    · exact γ_subset_big hA (sg.mem_γ_of_mem_s₀ hx)
  · -- starts in `S̄_{3n}`
    intro h
    have : (sg.p₀ ++ (sg.SP ++ sg.s₀)).head h = sg.p₀.head sg.hp₀ :=
      List.head_append_of_ne_nil sg.hp₀
    rw [this]
    exact sg.p₀_head_mem_src hA
  · -- ends in `Z̄_n`
    intro h
    have : (sg.p₀ ++ (sg.SP ++ sg.s₀)).getLast h = sg.s₀.getLast sg.hs₀ := by
      rw [List.getLast_append_of_ne_nil _ (by simp [sg.hs₀]),
        List.getLast_append_of_ne_nil _ sg.hs₀]
    rw [this]
    exact sg.s₀_last_mem_Y hA

/-- `σ = w' :: σ.tail`. [folklore] -/
theorem σ_eq_cons : sg.σ = sg.w' :: sg.σ.tail := by
  conv_lhs => rw [← List.cons_head_tail sg.σ_ne_nil]
  rw [sg.σ_head]

/-- Along `σ`, `w'` is `ω`-joined inside `B̄'_n` to a vertex of `S̄'_n`. [folklore] -/
theorem w'_joined_src' : ∃ s' ∈ slabLift k G.src', ω ∈ openConnIn (slabLift k G.small) sg.w' s' := by
  have hch := sg.hσchain
  rw [sg.σ_eq_cons] at hch
  refine ⟨(sg.w' :: sg.σ.tail).getLast (List.cons_ne_nil _ _), ?_, ?_⟩
  · have := sg.hσsrc' sg.σ_ne_nil
    convert this using 1
    exact (List.getLast_congr _ _ sg.σ_eq_cons).symm
  · exact openConnIn_of_isChain _ _ hch fun x hx => sg.hσsmall x (by rw [sg.σ_eq_cons]; exact hx)

/-- `w'` is not `ω`-joined to `S̄_{3n}` inside `B̄_{3n} ∪ B̄'_n` (else `C(ω)`). [cite: DuminilCopinSidoraviciusTassion2016, §2.3, proof of Fact 2] -/
theorem w'_not_joined (hX : ω ∈ G.evX k) {x : slab 3 k} (hx : x ∈ slabLift k G.src)
    (h : ω ∈ openConnIn (slabLift k (G.big ∪ G.small)) x sg.w') : False := by
  obtain ⟨-, hC⟩ := hX
  obtain ⟨s', hs', hj⟩ := sg.w'_joined_src'
  exact hC ⟨x, hx, s', hs', SlabCriticality.openConnIn_trans h
    (openConnIn_mono (slabLift_mono k Set.subset_union_right) _ _ hj)⟩

/-- `𝒳 ⊆ A`. [folklore] -/
theorem _root_.Percolation.Literature.GlueGeom.evA_of_evX {G : GlueGeom} {k : ℕ} {ω : BondConfig (slab 3 k)}
    (hX : ω ∈ G.evX k) : ω ∈ G.evA k := hX.1.1.1

/-- Membership in `Br` other than at `w'` means membership in `Br.dropLast`. [folklore] -/
theorem mem_dropLast_of_ne {x : slab 3 k} (hx : x ∈ sg.Br) (hne : x ≠ sg.w') : x ∈ sg.Br.dropLast := by
  have := List.dropLast_concat_getLast sg.hBr
  rw [← this] at hx
  rcases List.mem_append.1 hx with h | h
  · exact h
  · simp only [List.mem_singleton] at h
    exact absurd h hne

/-- **The minimal path of `ω^{(z)}` runs through the rerouted piece**: `γ_min(ω^{(z)}) =
p₀ ++ E₁ :: P ++ E₂ :: tail` for some `tail` (DST: "`γ_min(ω^{(z)})` and `γ_min(ω)` coincide at
least until `u'` … forces it to go inside `B̄_R(z)` … it must contain `z`"), by the exchange
lemma `minPath_prefix_of_surgery`. [cite: DuminilCopinSidoraviciusTassion2016, §2.3, proof of Fact 2 (p. 7)] -/
theorem exists_tail (hX : ω ∈ G.evX k) : ∃ tail, G.γmin k sg.newConfig = sg.p₀ ++ (sg.SP ++ tail) := by
  have hA := GlueGeom.evA_of_evX hX
  have hS := G.big_finite k
  have hex : ∃ l, IsOSAP k ω (slabLift k G.big) (slabLift k G.src) (slabLift k G.zSeg) l :=
    (mem_slabConn_iff_exists_isOSAP ω _ _ _).1 hA
  have hγ' : minPath k ω (slabLift k G.big) (slabLift k G.src) (slabLift k G.zSeg) =
      (sg.p₀ ++ [sg.E₁]) ++ (sg.mid ++ sg.E₂ :: sg.s₀) := by
    rw [List.append_assoc]; exact sg.hγ
  have hT : IsOSAP k sg.newConfig (slabLift k G.big) (slabLift k G.src) (slabLift k G.zSeg)
      ((sg.p₀ ++ [sg.E₁]) ++ (sg.P ++ [sg.E₂]) ++ sg.s₀) := by
    have := sg.isOSAP_T hA
    convert this using 1
    simp [T, SP]
  have hγeq : minPath k ω (slabLift k G.big) (slabLift k G.src) (slabLift k G.zSeg) = G.γmin k ω := rfl
  have hpfx : ∀ x ∈ (sg.p₀ ++ [sg.E₁]).dropLast, x ∉ sg.Sw := by
    intro x hx
    rw [List.dropLast_concat] at hx
    exact sg.p₀_not_Sw hx
  have h2 : ∀ q x, s(q, x) ∈ sg.newConfig → x ∈ sg.Wv →
      x ∉ minPath k ω (slabLift k G.big) (slabLift k G.src) (slabLift k G.zSeg) → q ∈ sg.Sw := by
    intro q x hqx hxW hxγ
    rcases sg.edge_into_Wv hqx hxW with h | h
    · exact h
    · exfalso
      rcases h with rfl | rfl
      · exact hxγ sg.E₁_mem_γ
      · exact hxγ sg.E₂_mem_γ
  have h4 : ∀ q ∈ sg.Sw, q ∉ sg.Wv →
      q ∉ minPath k ω (slabLift k G.big) (slabLift k G.src) (slabLift k G.zSeg) →
      ∀ x ∈ slabLift k G.src, ω ∉ openConnIn (slabLift k G.big) x q := by
    intro q hq hqW _ x hx hj
    have hqw : q = sg.w' := by
      by_contra hne
      exact hqW ⟨hq, hne⟩
    subst hqw
    exact sg.w'_not_joined hX hx (openConnIn_mono (slabLift_mono k Set.subset_union_left) _ _ hj)
  have h5 : ∀ v ∈ sg.Wv, v ∈ slabLift k G.src →
      v ∈ minPath k ω (slabLift k G.big) (slabLift k G.src) (slabLift k G.zSeg) ∨
      ∀ b ∈ (minPath k ω (slabLift k G.big) (slabLift k G.src) (slabLift k G.zSeg)).head?,
        vKey k b ≤ vKey k v := by
    intro v hvW hvX
    rw [hγeq]
    by_cases hvγ : v ∈ G.γmin k ω
    · exact Or.inl hvγ
    · right
      obtain ⟨hvSw, hvw⟩ := hvW
      have hv' : v ∈ sg.P ++ sg.Br.dropLast := by
        rcases hvSw with h | h
        · rcases sg.mem_SP_iff.1 h with rfl | h | rfl
          · exact absurd sg.E₁_mem_γ hvγ
          · exact List.mem_append_left _ h
          · exact absurd sg.E₂_mem_γ hvγ
        · exact List.mem_append_right _ (sg.mem_dropLast_of_ne h hvw)
      exact sg.hsrc v hv' hvX hvγ
  have h9 : ∀ x ∈ (sg.P ++ [sg.E₂]).dropLast, x ∉ slabLift k G.zSeg := by
    intro x hx
    rw [List.dropLast_concat] at hx
    exact sg.hPY x hx
  have h6 : ∀ (p₁ : List (slab 3 k)) (x y : slab 3 k) (r : List (slab 3 k)),
      (sg.p₀ ++ [sg.E₁]) ++ (sg.P ++ [sg.E₂]) = p₁ ++ x :: y :: r →
      (sg.p₀ ++ [sg.E₁]).length ≤ p₁.length + 1 →
      ∀ q, s(x, q) ∈ sg.newConfig → q ≠ y → q ∈ p₁ ∨ vKey k y < vKey k q := by
    intro p₁ x y r heq hlen q hxq hqy
    -- `p₁ = p₀ ++ p₁'` and `SP = p₁' ++ x :: y :: r`
    have heq' : sg.p₀ ++ sg.SP = p₁ ++ x :: y :: r := by
      rw [← heq]; simp [SP]
    have hlen' : sg.p₀.length ≤ p₁.length := by simpa using hlen
    obtain ⟨p₁', hp₁, hSP⟩ : ∃ p₁', p₁ = sg.p₀ ++ p₁' ∧ sg.SP = p₁' ++ x :: y :: r := by
      rcases List.append_eq_append_iff.1 heq' with ⟨a', hp₁, hSP⟩ | ⟨c', hp₀, hxyr⟩
      · exact ⟨a', hp₁, hSP⟩
      · -- `p₀ = p₁ ++ c'` forces `c' = []`
        have : c' = [] := by
          have := congrArg List.length hp₀
          simp only [List.length_append] at this
          exact List.eq_nil_of_length_eq_zero (by omega)
        subst this
        simp only [List.append_nil] at hp₀
        simp only [List.nil_append] at hxyr
        exact ⟨[], by simp [hp₀], by simpa using hxyr.symm⟩
    have hxSP : x ∈ sg.SP := by rw [hSP]; simp
    have hxD : planar k x ∈ sg.D := sg.SP_D hxSP
    have hxq' : s(q, x) ∈ sg.newConfig := by rwa [Sym2.eq_swap]
    have hcases : s(x, q) ∈ sg.structEdges ∨ s(x, q) ∈ sg.stubs := by
      have := sg.edge_at_D hxq' hxD
      rwa [Sym2.eq_swap] at this
    rcases hcases with (he | he) | he
    · -- an edge of `SP`: to the predecessor (`∈ p₁`) or the successor (`= y`)
      rcases next_of_mem_edgesOf sg.hSPnodup hSP he with ⟨r', hr'⟩ | ⟨l₁', hl₁'⟩
      · exact absurd (List.cons.inj hr').1.symm hqy
      · left
        rw [hp₁, hl₁']
        simp
    · -- an edge of the branch: `x = c` and `q = Br.head`
      obtain ⟨hxBr, hqBr⟩ := mem_of_mem_edgesOf he
      have hxc : x = sg.c := by
        rcases List.mem_cons.1 hxBr with h | h
        · exact h
        · exact absurd hxSP (sg.hBrSP x h)
      subst hxc
      obtain ⟨l', hl'⟩ := eq_of_mem_edgesOf_head sg.hBrnodup he
      right
      have hq : q = sg.Br.head sg.hBr := by simp [hl']
      rw [hq]
      exact sg.hfwd p₁' r y hSP
    · -- a stub at `x ∈ SP`: only the one into `E₁`, from `p₀.getLast ∈ p₁`
      have he' : s(q, x) ∈ sg.stubs := by rwa [Sym2.eq_swap]
      rcases sg.stubs_cases_D he' hxD with ⟨-, rfl⟩ | ⟨hxE₂, -⟩ | ⟨hxw, -⟩
      · left
        rw [hp₁]
        exact List.mem_append_left _ (List.getLast_mem _)
      · -- `x = E₂` is the last vertex of `SP`, but `y` follows it
        exfalso
        have h1 : sg.SP = (sg.E₁ :: sg.P) ++ sg.E₂ :: [] := by simp [SP]
        rw [hxE₂] at hSP
        have hE₂p : sg.E₂ ∉ p₁' := by
          intro hmem
          have hnd := sg.hSPnodup
          rw [show sg.E₁ :: (sg.P ++ [sg.E₂]) = sg.SP from rfl, hSP] at hnd
          exact (List.nodup_append.1 hnd).2.2 _ hmem _ (by simp) rfl
        have hE₂q : sg.E₂ ∉ sg.E₁ :: sg.P := by
          intro hmem
          have hnd := sg.hSPnodup
          rw [show sg.E₁ :: (sg.P ++ [sg.E₂]) = (sg.E₁ :: sg.P) ++ [sg.E₂] by simp] at hnd
          exact (List.nodup_append.1 hnd).2.2 _ hmem _ (by simp) rfl
        obtain ⟨-, h2⟩ := split_unique (hSP.symm.trans h1) hE₂p hE₂q
        exact List.cons_ne_nil _ _ h2
      · exact absurd hxSP (hxw ▸ sg.w'_not_mem_SP)
  obtain ⟨tail, htail⟩ := minPath_prefix_of_surgery hS hex (sg.p₀ ++ [sg.E₁])
    (sg.mid ++ sg.E₂ :: sg.s₀) (sg.P ++ [sg.E₂]) sg.s₀ hγ' (by simp) (by simp) hT
    sg.structEdges sg.Wv sg.Sw (sg.newConfig_subset hA) (fun a b h => sg.structEdges_Sw h)
    hpfx h2 h4 h5 h6 h9
  refine ⟨tail, ?_⟩
  change minPath k sg.newConfig _ _ _ = _
  rw [htail]; simp [SP]

end GlueGeom.Surgery

end Exchange

/-! ## The continuation of `γ_min(ω^{(z)})` and the recovery of the attachment vertex -/

section Recovery

namespace GlueGeom.Surgery

variable {k : ℕ} {G : GlueGeom} {ω : BondConfig (slab 3 k)} (sg : G.Surgery k ω)

/-- `γ_min(ω^{(z)})` is an open self-avoiding path of `ω^{(z)}`. [folklore] -/
theorem μ_isOSAP (hX : ω ∈ G.evX k) :
    IsOSAP k sg.newConfig (slabLift k G.big) (slabLift k G.src) (slabLift k G.zSeg)
      (G.γmin k sg.newConfig) :=
  (minPath_spec (G.big_finite k) ⟨_, sg.isOSAP_T (GlueGeom.evA_of_evX hX)⟩).1

/-- `S̄_{3n} ∋ p₀.head` is `ω`-joined inside `B̄_{3n} ∪ B̄'_n` to every vertex of `γ`. [folklore] -/
theorem joined_of_mem_γ (hA : ω ∈ G.evA k) {v : slab 3 k} (hv : v ∈ G.γmin k ω) :
    ω ∈ openConnIn (slabLift k (G.big ∪ G.small)) (sg.p₀.head sg.hp₀) v := by
  have hγO := (G.γmin_spec k hA).1
  have h := hγO.openConnIn_of_mem hv
  have hh : (G.γmin k ω).head hγO.ne_nil = sg.p₀.head sg.hp₀ := by
    rw [List.head_eq_iff_head?_eq_some, sg.γ_head?]
  rw [hh] at h
  exact openConnIn_mono (slabLift_mono k Set.subset_union_left) _ _ h

/-- **The continuation starts with the old exit edge**: if `γ_min(ω^{(z)}) = p₀ ++ E₁ :: P ++
E₂ :: tail` with `tail ≠ []`, then `tail.head = s₀.head` (the only open edges at `E₂` are the
structure edge and the stub). [cite: DuminilCopinSidoraviciusTassion2016, §2.3, proof of Fact 2] -/
theorem tail_head (hX : ω ∈ G.evX k) {tail : List (slab 3 k)}
    (hμ : G.γmin k sg.newConfig = sg.p₀ ++ (sg.SP ++ tail)) (ht : tail ≠ []) :
    tail.head ht = sg.s₀.head sg.hs₀ := by
  have hμO := sg.μ_isOSAP hX
  have hch := hμO.chain
  have hnd := hμO.nodup
  rw [hμ] at hch hnd
  set t₁ := tail.head ht with ht₁
  have hrel : s(sg.E₂, t₁) ∈ sg.newConfig ∧ sg.E₂ ≠ t₁ := by
    have h1 := (List.isChain_append.1 hch).2.1
    have h2 := List.IsChain.rel_getLast_head_of_append h1 (by simp [SP]) ht
    have h3 : sg.SP.getLast (by simp [SP]) = sg.E₂ := by simp [SP]
    rwa [h3] at h2
  have ht₁SP : t₁ ∉ sg.SP := by
    intro h
    have := (List.nodup_append.1 (List.nodup_append.1 hnd).2.1).2.2 t₁ h t₁ (List.head_mem ht) rfl
    exact this
  have hrel' : s(t₁, sg.E₂) ∈ sg.newConfig := by rw [Sym2.eq_swap]; exact hrel.1
  rcases sg.edge_at_D hrel' sg.hE₂D with (he | he) | he
  · -- a structure edge of `SP` at its last vertex leads to the predecessor, inside `SP`
    exfalso
    have he' : s(sg.E₂, t₁) ∈ edgesOf ((sg.E₁ :: sg.P) ++ [sg.E₂]) := by
      rw [Sym2.eq_swap]; simpa [SP] using he
    have hnd' : ((sg.E₁ :: sg.P) ++ [sg.E₂]).Nodup := by simpa [SP] using sg.hSPnodup
    obtain ⟨l₁', hl₁'⟩ := eq_of_mem_edgesOf_last hnd' he'
    apply ht₁SP
    have : t₁ ∈ sg.E₁ :: sg.P := by rw [hl₁']; simp
    simp only [SP, List.mem_cons, List.mem_append]
    rcases List.mem_cons.1 this with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · -- a branch edge at `E₂`: impossible, `E₂ ∉ c :: Br`
    exfalso
    obtain ⟨-, hE₂⟩ := mem_of_mem_edgesOf he
    rcases List.mem_cons.1 hE₂ with h | h
    · exact sg.c_ne_E₂ h.symm
    · exact sg.hBrSP _ h sg.E₂_mem_SP
  · rcases sg.stubs_cases_D he sg.hE₂D with ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩
    · exact absurd h.symm sg.E₁_ne_E₂
    · exact h
    · exact absurd sg.E₂_mem_SP (h ▸ sg.w'_not_mem_SP)

/-- **The continuation lives in the old world**: every vertex of `tail` is off the structure and
`ω`-joined to `S̄_{3n}` inside `B̄_{3n} ∪ B̄'_n` (propagation from `s₀.head`).
[cite: DuminilCopinSidoraviciusTassion2016, §2.3, proof of Fact 2] -/
theorem tail_props (hX : ω ∈ G.evX k) {tail : List (slab 3 k)}
    (hμ : G.γmin k sg.newConfig = sg.p₀ ++ (sg.SP ++ tail)) {q : slab 3 k} (hq : q ∈ tail) :
    q ∉ sg.Sw ∧ ω ∈ openConnIn (slabLift k (G.big ∪ G.small)) (sg.p₀.head sg.hp₀) q := by
  have hA := GlueGeom.evA_of_evX hX
  have ht : tail ≠ [] := List.ne_nil_of_mem hq
  have hμO := sg.μ_isOSAP hX
  have hch := hμO.chain
  have hnd := hμO.nodup
  rw [hμ] at hch hnd
  obtain ⟨t₁, tail', htail⟩ := List.exists_cons_of_ne_nil ht
  have ht₁ : t₁ = sg.s₀.head sg.hs₀ := by
    have := sg.tail_head hX hμ ht
    rw [List.head_eq_iff_head?_eq_some, htail] at this
    simpa using this
  -- the open path along `tail` from `t₁` to `q`, inside `A = B̄_{3n} ∖ SP`
  set A : Set (slab 3 k) := slabLift k G.big ∩ {v | v ∉ sg.SP} with hAdef
  have htailch : tail.IsChain (fun a b => s(a, b) ∈ sg.newConfig ∧ a ≠ b) :=
    (List.isChain_append.1 (List.isChain_append.1 hch).2.1).2.1
  have htailA : ∀ x ∈ tail, x ∈ A := by
    intro x hx
    refine ⟨hμO.subset x (by rw [hμ]; simp [hx]), fun hxSP => ?_⟩
    exact (List.nodup_append.1 (List.nodup_append.1 hnd).2.1).2.2 x hxSP x hx rfl
  have hpath : sg.newConfig ∈ openConnIn A t₁ q := by
    rw [htail] at htailch htailA hq
    exact openConnIn_head_of_mem t₁ tail' htailch htailA q hq
  refine not_mem_structure_of_openConnIn (Reg := slabLift k (G.big ∪ G.small))
    (fun x hx => slabLift_mono k Set.subset_union_left hx.1) sg.structEdges sg.Wv sg.Sw
    {sg.E₁, sg.E₂} sg.Wv_subset (sg.p₀.head sg.hp₀) (sg.newConfig_subset hA)
    (fun a b h => sg.structEdges_Sw h) (fun t x h hx => sg.edge_into_Wv h hx) ?_ ?_ hpath ?_ ?_
  · rintro x ⟨-, hx⟩ hK
    exfalso
    rcases hK with rfl | rfl
    · exact hx sg.E₁_mem_SP
    · exact hx sg.E₂_mem_SP
  · intro x hx hxW hj
    have hxw : x = sg.w' := by
      by_contra hne
      exact hxW ⟨hx, hne⟩
    subst hxw
    exact sg.w'_not_joined hX (sg.p₀_head_mem_src hA) hj
  · rw [ht₁]; exact sg.s₀_not_Sw (List.head_mem _)
  · rw [ht₁]; exact sg.joined_of_mem_γ hA (sg.mem_γ_of_mem_s₀ (List.head_mem _))

/-- **The continuation avoids `D̄`.** [cite: DuminilCopinSidoraviciusTassion2016, §2.3, proof of Fact 2] -/
theorem tail_not_D (hX : ω ∈ G.evX k) {tail : List (slab 3 k)}
    (hμ : G.γmin k sg.newConfig = sg.p₀ ++ (sg.SP ++ tail)) {q : slab 3 k} (hq : q ∈ tail) :
    planar k q ∉ sg.D := by
  intro hqD
  have ht : tail ≠ [] := List.ne_nil_of_mem hq
  obtain ⟨t₁, tail', htail⟩ := List.exists_cons_of_ne_nil ht
  have ht₁ : t₁ = sg.s₀.head sg.hs₀ := by
    have := sg.tail_head hX hμ ht
    rw [List.head_eq_iff_head?_eq_some, htail] at this
    simpa using this
  rw [htail] at hq
  rcases List.mem_cons.1 hq with rfl | hq'
  · exact sg.s₀_head_not_D (ht₁ ▸ hqD)
  · -- the edge of `γ_min(ω^{(z)})` into `q` would make `q` a structure vertex
    obtain ⟨u, v, huv⟩ := List.append_of_mem hq'
    have hch := (sg.μ_isOSAP hX).chain
    rw [hμ, htail, huv] at hch
    have h1 : ((sg.p₀ ++ (sg.SP ++ t₁ :: u)) ++ q :: v).IsChain
        (fun a b => s(a, b) ∈ sg.newConfig ∧ a ≠ b) := by
      simpa [List.append_assoc] using hch
    have h2 := List.IsChain.rel_getLast_head_of_append h1 (by simp) (by simp)
    simp only [List.head_cons] at h2
    have hqSw := sg.mem_Sw_of_edge h2.1 hqD
    have hq'' : q ∈ tail := by rw [htail, huv]; simp
    exact (sg.tail_props hX hμ hq'').1 hqSw

end GlueGeom.Surgery

end Recovery

/-! ## The attachment statistic and the conclusions of the surgery -/

section Attachment

variable (k : ℕ)

/-- **DST's recovery statistic**: the vertices `q` of `γ_min(ω')` joined to `S̄'_n` inside
`B̄_{3n} ∪ B̄'_n` by an `ω'`-open path avoiding the other vertices of `γ_min(ω')` ("`z` is the
only vertex in `γ_min(ω^{(z)})` which is connected to `S'_n` in `B'_n ∖ γ_min(ω^{(z)})`",
p. 7; here with the region `B̄_{3n} ∪ B̄'_n`). A function of `ω'` alone.
[cite: DuminilCopinSidoraviciusTassion2016, §2.3, proof of Fact 2 (p. 7)] -/
def GlueGeom.att (G : GlueGeom) (ω' : BondConfig (slab 3 k)) : Set (slab 3 k) :=
  {q | q ∈ G.γmin k ω' ∧ ∃ s' ∈ slabLift k G.src',
    ω' ∈ openConnIn (slabLift k (G.big ∪ G.small) ∩ {v | v ∉ G.γmin k ω' ∨ v = q}) q s'}

namespace GlueGeom.Surgery

variable {k} {G : GlueGeom} {ω : BondConfig (slab 3 k)} (sg : G.Surgery k ω)

/-- The structure path lies in `B̄_{3n} ∪ B̄'_n`. [folklore] -/
theorem SP_subset_Reg {x : slab 3 k} (hx : x ∈ sg.SP) : x ∈ slabLift k (G.big ∪ G.small) :=
  sg.hD (sg.SP_D hx)

/-- The branch lies in `B̄_{3n} ∪ B̄'_n`. [folklore] -/
theorem Br_subset_Reg {x : slab 3 k} (hx : x ∈ sg.Br) : x ∈ slabLift k (G.big ∪ G.small) :=
  sg.hD (sg.hBrD x hx)

/-- Every vertex of `σ` is `ω`-joined inside `B̄'_n` to the end of `σ` (in `S̄'_n`). [folklore] -/
theorem σ_joined {x : slab 3 k} (hx : x ∈ sg.σ) :
    ω ∈ openConnIn (slabLift k G.small) x (sg.σ.getLast sg.σ_ne_nil) := by
  have hch := sg.hσchain
  have hσ := sg.σ_eq_cons
  rw [hσ] at hch
  have hsub : ∀ y ∈ sg.w' :: sg.σ.tail, y ∈ slabLift k G.small :=
    fun y hy => sg.hσsmall y (by rw [hσ]; exact hy)
  have h1 : ω ∈ openConnIn (slabLift k G.small) sg.w' x :=
    openConnIn_head_of_mem _ _ hch hsub x (by rw [hσ] at hx; exact hx)
  have h2 : ω ∈ openConnIn (slabLift k G.small) sg.w' ((sg.w' :: sg.σ.tail).getLast (by simp)) :=
    openConnIn_of_isChain _ _ hch hsub
  have h3 : (sg.w' :: sg.σ.tail).getLast (by simp) = sg.σ.getLast sg.σ_ne_nil :=
    List.getLast_congr _ _ hσ.symm
  rw [h3] at h2
  exact SlabCriticality.openConnIn_trans (openConnIn_reverse h1) h2

/-- A vertex of `σ` is not `ω`-joined to `S̄_{3n}` inside `B̄_{3n} ∪ B̄'_n`. [folklore] -/
theorem σ_not_joined (hX : ω ∈ G.evX k) {x : slab 3 k} (hx : x ∈ sg.σ) {a : slab 3 k}
    (ha : a ∈ slabLift k G.src) (h : ω ∈ openConnIn (slabLift k (G.big ∪ G.small)) a x) : False := by
  obtain ⟨-, hC⟩ := hX
  exact hC ⟨a, ha, _, sg.hσsrc' sg.σ_ne_nil, SlabCriticality.openConnIn_trans h
    (openConnIn_mono (slabLift_mono k Set.subset_union_right) _ _ (sg.σ_joined hx))⟩

/-- **The attachment vertex is recovered**: `c ∈ Att(ω^{(z)})`, via the branch and `σ`.
[cite: DuminilCopinSidoraviciusTassion2016, §2.3, proof of Fact 2 (p. 7)] -/
theorem c_mem_att (hX : ω ∈ G.evX k) : sg.c ∈ G.att k sg.newConfig := by
  have hA := GlueGeom.evA_of_evX hX
  obtain ⟨tail, hμ⟩ := sg.exists_tail hX
  refine ⟨by rw [hμ]; simp [sg.c_mem_SP], sg.σ.getLast sg.σ_ne_nil, sg.hσsrc' _, ?_⟩
  -- the walk `c :: Br ++ σ.tail`
  set A : Set (slab 3 k) :=
    slabLift k (G.big ∪ G.small) ∩ {v | v ∉ G.γmin k sg.newConfig ∨ v = sg.c} with hAdef
  have hσch : (sg.w' :: sg.σ.tail).IsChain (fun a b => s(a, b) ∈ ω ∧ a ≠ b) := by
    have := sg.hσchain; rwa [sg.σ_eq_cons] at this
  have hch : (sg.c :: (sg.Br ++ sg.σ.tail)).IsChain (fun a b => s(a, b) ∈ sg.newConfig ∧ a ≠ b) := by
    rw [← List.cons_append]
    refine List.IsChain.append ?_ ?_ ?_
    · exact isChain_of_edgesOf_subset sg.hBrchain
        fun e he => sg.structEdges_subset_newConfig (Or.inr he)
    · rw [List.isChain_cons] at hσch
      exact hσch.2.imp_of_mem_imp fun a b ha hb h =>
        ⟨sg.mem_newConfig_of_off h.1 (sg.hσD a ha) (sg.hσD b hb), h.2⟩
    · intro x hx y hy
      have hx' : x = sg.w' := by
        rw [List.getLast?_eq_some_getLast (by simp), Option.mem_def, Option.some.injEq] at hx
        rw [← hx, List.getLast_cons sg.hBr]; rfl
      subst hx'
      refine ⟨sg.stub₃_mem hy, ?_⟩
      rw [List.isChain_cons] at hσch
      exact (hσch.1 y hy).2
  have hsub : ∀ x ∈ sg.c :: (sg.Br ++ sg.σ.tail), x ∈ A := by
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨sg.SP_subset_Reg sg.c_mem_SP, Or.inr rfl⟩
    rcases List.mem_append.1 hx with hx | hx
    · refine ⟨sg.Br_subset_Reg hx, Or.inl fun hμx => ?_⟩
      rw [hμ] at hμx
      rcases List.mem_append.1 hμx with h | h
      · exact sg.hp₀D x h (sg.hBrD x hx)
      rcases List.mem_append.1 h with h | h
      · exact sg.hBrSP x hx h
      · exact sg.tail_not_D hX hμ h (sg.hBrD x hx)
    · have hxσ : x ∈ sg.σ := List.mem_of_mem_tail hx
      refine ⟨slabLift_mono k Set.subset_union_right (sg.hσsmall x hxσ), Or.inl fun hμx => ?_⟩
      rw [hμ] at hμx
      rcases List.mem_append.1 hμx with h | h
      · exact sg.hσγ x hxσ ⟨x, sg.mem_γ_of_mem_p₀ h, rfl⟩
      rcases List.mem_append.1 h with h | h
      · exact sg.hσD x hx (sg.SP_D h)
      · exact sg.σ_not_joined hX hxσ (sg.p₀_head_mem_src hA) (sg.tail_props hX hμ h).2
  have hconn := openConnIn_of_isChain _ _ hch hsub
  have hlast : (sg.c :: (sg.Br ++ sg.σ.tail)).getLast (List.cons_ne_nil _ _) =
      sg.σ.getLast sg.σ_ne_nil := by
    have e1 : sg.Br ++ sg.σ.tail = sg.Br.dropLast ++ (sg.w' :: sg.σ.tail) := by
      conv_lhs => rw [← List.dropLast_concat_getLast sg.hBr]
      rw [List.append_assoc]; rfl
    have hne1 : sg.Br ++ sg.σ.tail ≠ [] := by simp [sg.hBr]
    have hne2 : sg.Br.dropLast ++ sg.w' :: sg.σ.tail ≠ [] := by simp
    rw [List.getLast_cons hne1, List.getLast_congr hne1 hne2 e1,
      List.getLast_append_of_ne_nil _ (List.cons_ne_nil _ _), List.getLast_congr _ _ sg.σ_eq_cons]
  rw [hlast] at hconn
  exact hconn

/-- **The statistic localises the surgery**: `Att(ω^{(z)}) ⊆ D̄` — a vertex of
`γ_min(ω^{(z)})` off `D̄` is an old-world vertex `ω`-joined to `S̄_{3n}`, and an `ω^{(z)}`-open
path from it to `S̄'_n` avoiding the rest of `γ_min(ω^{(z)})` cannot enter the structure, so it
would be `ω`-open and give `C(ω)`. [cite: DuminilCopinSidoraviciusTassion2016, §2.3, proof of Fact 2 (p. 7)] -/
theorem att_subset (hX : ω ∈ G.evX k) : G.att k sg.newConfig ⊆ slabLift k sg.D := by
  have hA := GlueGeom.evA_of_evX hX
  obtain ⟨tail, hμ⟩ := sg.exists_tail hX
  rintro q ⟨hqμ, s', hs', hj⟩
  by_contra hqD
  rw [mem_slabLift_iff] at hqD
  have hqSw : q ∉ sg.Sw := fun h => hqD (sg.Sw_D h)
  have hq0 : ω ∈ openConnIn (slabLift k (G.big ∪ G.small)) (sg.p₀.head sg.hp₀) q := by
    rw [hμ] at hqμ
    rcases List.mem_append.1 hqμ with h | h
    · exact sg.joined_of_mem_γ hA (sg.mem_γ_of_mem_p₀ h)
    rcases List.mem_append.1 h with h | h
    · exact absurd (sg.SP_D h) hqD
    · exact (sg.tail_props hX hμ h).2
  have hres := not_mem_structure_of_openConnIn (Reg := slabLift k (G.big ∪ G.small))
    (A := slabLift k (G.big ∪ G.small) ∩ {v | v ∉ G.γmin k sg.newConfig ∨ v = q})
    (fun x hx => hx.1) sg.structEdges sg.Wv sg.Sw {sg.E₁, sg.E₂} sg.Wv_subset
    (sg.p₀.head sg.hp₀) (sg.newConfig_subset hA) (fun a b h => sg.structEdges_Sw h)
    (fun t x h hx => sg.edge_into_Wv h hx) ?_ ?_ hj hqSw hq0
  · obtain ⟨-, hC⟩ := hX
    exact hC ⟨_, sg.p₀_head_mem_src hA, s', hs', hres.2⟩
  · rintro x ⟨-, hx⟩ hK
    exfalso
    have hxSP : x ∈ sg.SP := by
      rcases hK with rfl | rfl
      · exact sg.E₁_mem_SP
      · exact sg.E₂_mem_SP
    rcases hx with hx | rfl
    · exact hx (by rw [hμ]; simp [hxSP])
    · exact hqD (sg.SP_D hxSP)
  · intro x hx hxW hj'
    have hxw : x = sg.w' := by
      by_contra hne
      exact hxW ⟨hx, hne⟩
    subst hxw
    exact sg.w'_not_joined ⟨⟨⟨hA, hX.1.1.2⟩, hX.1.2⟩, hX.2⟩ (sg.p₀_head_mem_src hA) hj'

/-- **The new configuration realises `C`**: `S_{3n} ⟷ S'_n` in `B̄_{3n} ∪ B̄'_n` (along `γ` to
`E₁`, the rerouted piece to `c`, the branch, and `σ`). [cite: DuminilCopinSidoraviciusTassion2016, §2.3, proof of Fact 2 ("By construction, ω^{(z)} is in {S_{3n} ⟷ S'_n}")] -/
theorem newConfig_mem_evC (hX : ω ∈ G.evX k) : sg.newConfig ∈ G.evC k := by
  have hA := GlueGeom.evA_of_evX hX
  obtain ⟨hcμ, s', hs', hj⟩ := sg.c_mem_att hX
  have hμO := sg.μ_isOSAP hX
  have h1 := hμO.openConnIn_of_mem hcμ
  obtain ⟨tail, hμ⟩ := sg.exists_tail hX
  have hh : (G.γmin k sg.newConfig).head hμO.ne_nil = sg.p₀.head sg.hp₀ := by
    rw [List.head_eq_iff_head?_eq_some, hμ, List.head?_append, List.head?_eq_some_head sg.hp₀]
    rfl
  rw [hh] at h1
  exact ⟨_, sg.p₀_head_mem_src hA, s', hs', SlabCriticality.openConnIn_trans
    (openConnIn_mono (slabLift_mono k Set.subset_union_left) _ _ h1)
    (openConnIn_mono (fun x hx => hx.1) _ _ hj)⟩

/-- The attachment statistic of `ω^{(z)}` is non-empty. [folklore] -/
theorem att_nonempty (hX : ω ∈ G.evX k) : (G.att k sg.newConfig).Nonempty := ⟨sg.c, sg.c_mem_att hX⟩

end GlueGeom.Surgery

end Attachment

end Percolation.Literature
