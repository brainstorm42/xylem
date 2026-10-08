import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Percolation.Literature.DecisionTreeWeighted
import Percolation.Literature.GladkovExploration
import Percolation.Literature.GrimmettMarstrand
import Percolation.Literature.LatticeModels.ProdBernoulliBK
import Percolation.Util.Linter

/-!
# The exploration of an open cluster stopped at a target set, and its revealed edge set

A deterministic, adaptive edge-revealing process
("decision tree" in the sense of Gladkov, *Percolation Inequalities and Decision Trees*,
arXiv:2408.08457v2 (2024), §2 Def. 2.4 / Example 2.5 and §6 Algorithm 2, there with the two
targets `b, c`; here with an arbitrary finite TARGET SET `A`): starting from a vertex `o`, reveal,
one at a time, an unrevealed edge of `D` joining the currently reached vertex set to its complement;
an open edge adds its far endpoint; STOP as soon as a vertex of `A` is reached or no such edge is
left.  For configurations `K ⊆ D` of open edges among a finite set `D ⊆ Sym2 V` of edges.

This file (all proved): the objects and the invariant —
* `Inv` / `inv_fin` — the invariant: `o` is reached; revealed edges lie in `D` and touch the reached
  set; open revealed edges have both endpoints reached; reached vertices are joined to `o` by open
  REVEALED edges; at most one target is reached;
Halting, self-determination (`DecisionTree.SelfDetermined (revealedAt D A o)`, so that Gladkov's
swap Lemma 3.1 applies), correctness and the splice facts are in `TargetExplorationRevealed.lean`;
the swap identity and the revealment bound for the gluing defect.

Design as in `GladkovExploration.lean` (explicit reached set, `Classical` choice of the next edge,
fuel); no stack is needed since no depth-first structure is used.
-/

noncomputable section

open Classical

namespace Percolation.Literature

namespace TargetExploration

open Finset DecisionTree

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### States and one step -/

/-- A state of the exploration: the reached vertices and the revealed edges.
[cite: Gladkov2024, §6 Algorithm 2 (the visited set and the revealed edges)] -/
structure St (V : Type*) where
  /-- the vertices reached from the root by open revealed edges -/
  vis : Finset V
  /-- the revealed (queried) edges -/
  rev : Finset (Sym2 V)

section Defs

variable (D : Finset (Sym2 V)) (A : Finset V) (o : V)

/-- The boundary of a state: unrevealed edges of `D` joining a reached vertex to an unreached one.
[cite: Gladkov2024, §2 Example 2.5 (edges with one end in the current cluster)] -/
def bnd (σ : St V) : Finset (Sym2 V) :=
  ((σ.vis ×ˢ (univ \ σ.vis)).image fun q => s(q.1, q.2)) ∩ (D \ σ.rev)

/-- A state is halted when a target is reached or the boundary is empty. [cite: Gladkov2024, §6 Algorithm 2 (stopping rule)] -/
def Halted (σ : St V) : Prop := (σ.vis ∩ A).Nonempty ∨ bnd D σ = ∅

/-- The unreached endpoints of the edge `e` seen from the reached set. [folklore] -/
def newEnds (σ : St V) (e : Sym2 V) : Finset V :=
  (univ \ σ.vis).filter fun v => ∃ u ∈ σ.vis, s(u, v) = e

/-- One step on the configuration `K`: if not halted, reveal a boundary edge; if it is open, add
its far endpoint. [cite: Gladkov2024, §6 Algorithm 2] -/
def step (K : Finset (Sym2 V)) (σ : St V) : St V :=
  if (σ.vis ∩ A).Nonempty then σ
  else
    match Gladkov.pick (bnd D σ) with
    | none => σ
    | some e => if e ∈ K then ⟨σ.vis ∪ newEnds σ e, insert e σ.rev⟩ else ⟨σ.vis, insert e σ.rev⟩

/-- The initial state: only `o` reached, nothing revealed. [folklore] -/
def init : St V := ⟨{o}, ∅⟩

/-- The state after `k` steps on the configuration `K`. [cite: Gladkov2024, §6 Algorithm 2] -/
def run (K : Finset (Sym2 V)) : ℕ → St V
  | 0 => init o
  | k + 1 => step D A K (run K k)

/-- The final state (fuel `#D + 1`, enough by `halted_fin`). [cite: Gladkov2024, §6.2] -/
def fin (K : Finset (Sym2 V)) : St V := run D A o K (D.card + 1)

/-- The revealed edge set of the exploration on `K` — the set `S(C₁)` built by the decision tree.
[cite: Gladkov2024, Def. 2.4] -/
def revealedAt (K : Finset (Sym2 V)) : Finset (Sym2 V) := (fin D A o K).rev

end Defs

/-! ### Basic facts about one step -/

section Basic

variable {D : Finset (Sym2 V)} {A : Finset V} {o : V}

omit [Fintype V] in
/-- `Gladkov.pick` (a `Classical` choice from a finite edge set) is `none` iff the set is empty.
[folklore] -/
theorem pick_eq_none_iff {s : Finset (Sym2 V)} : Gladkov.pick s = none ↔ s = ∅ := by
  constructor
  · intro h
    by_contra hne
    exact Gladkov.pick_ne_none (Finset.nonempty_iff_ne_empty.2 hne) h
  · intro h
    unfold Gladkov.pick
    rw [dif_neg (Finset.not_nonempty_iff_eq_empty.2 h)]

/-- Membership in the boundary. [folklore] -/
theorem mem_bnd {σ : St V} {e : Sym2 V} :
    e ∈ bnd D σ ↔ (∃ u ∈ σ.vis, ∃ v ∉ σ.vis, s(u, v) = e) ∧ e ∈ D ∧ e ∉ σ.rev := by
  simp only [bnd, mem_inter, mem_image, mem_product, mem_sdiff, mem_univ, true_and, Prod.exists]
  constructor
  · rintro ⟨⟨u, v, ⟨hu, hv⟩, rfl⟩, hD, hrev⟩
    exact ⟨⟨u, hu, v, hv, rfl⟩, hD, hrev⟩
  · rintro ⟨⟨u, hu, v, hv, rfl⟩, hD, hrev⟩
    exact ⟨⟨u, v, ⟨hu, hv⟩, rfl⟩, hD, hrev⟩

/-- Membership in `newEnds`. [folklore] -/
theorem mem_newEnds {σ : St V} {e : Sym2 V} {v : V} :
    v ∈ newEnds σ e ↔ v ∉ σ.vis ∧ ∃ u ∈ σ.vis, s(u, v) = e := by
  simp [newEnds]

/-- For a boundary edge `s(u, v)` (`u` reached, `v` not) the new endpoint set is `{v}`. [folklore] -/
theorem newEnds_eq_singleton {σ : St V} {u v : V} (hu : u ∈ σ.vis) (hv : v ∉ σ.vis) :
    newEnds σ s(u, v) = {v} := by
  ext x
  rw [mem_newEnds, mem_singleton]
  constructor
  · rintro ⟨hx, u', hu', he⟩
    rcases Sym2.eq_iff.1 he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h2
    · exact absurd (h1 ▸ hu') hv
  · rintro rfl
    exact ⟨hv, u, hu, rfl⟩

/-- A step at a halted state does nothing. [folklore] -/
theorem step_of_halted {K : Finset (Sym2 V)} {σ : St V} (h : Halted D A σ) : step D A K σ = σ := by
  unfold step
  split_ifs with hA
  · rfl
  · rcases h with h | h
    · exact absurd h hA
    · rw [pick_eq_none_iff.2 h]

/-- A step at a non-halted state reveals the picked boundary edge. [folklore] -/
theorem step_of_not_halted {K : Finset (Sym2 V)} {σ : St V} (h : ¬ Halted D A σ) :
    ∃ e ∈ bnd D σ, Gladkov.pick (bnd D σ) = some e ∧
      step D A K σ = (if e ∈ K then ⟨σ.vis ∪ newEnds σ e, insert e σ.rev⟩ else ⟨σ.vis, insert e σ.rev⟩) := by
  simp only [Halted, not_or] at h
  unfold step
  rw [if_neg h.1]
  cases hp : Gladkov.pick (bnd D σ) with
  | none => exact absurd (pick_eq_none_iff.1 hp) h.2
  | some e => exact ⟨e, Gladkov.mem_of_pick_eq_some hp, rfl, rfl⟩

/-- The revealed set grows by one step. [folklore] -/
theorem rev_subset_step (K : Finset (Sym2 V)) (σ : St V) : σ.rev ⊆ (step D A K σ).rev := by
  by_cases h : Halted D A σ
  · rw [step_of_halted h]
  · obtain ⟨e, -, -, hstep⟩ := step_of_not_halted (K := K) h
    rw [hstep]
    split_ifs <;> exact subset_insert e σ.rev

/-- At a non-halted state the revealed set grows strictly. [folklore] -/
theorem card_rev_step {K : Finset (Sym2 V)} {σ : St V} (h : ¬ Halted D A σ) :
    σ.rev.card + 1 ≤ (step D A K σ).rev.card := by
  obtain ⟨e, he, -, hstep⟩ := step_of_not_halted (K := K) h
  have herev : e ∉ σ.rev := ((mem_bnd.1 he).2).2
  rw [hstep]
  split_ifs <;> simp [card_insert_of_notMem herev]

/-- `run (k+1) = step (run k)`. [folklore] -/
theorem run_succ (K : Finset (Sym2 V)) (k : ℕ) : run D A o K (k + 1) = step D A K (run D A o K k) := rfl

end Basic

/-! ### The invariant -/

/-- The invariant of the exploration of the `K`-open cluster of `o` stopped at `A`.
[cite: Gladkov2024, §6.2 (structure of the revealed set)] -/
structure Inv (D : Finset (Sym2 V)) (A : Finset V) (o : V) (K : Finset (Sym2 V)) (σ : St V) : Prop where
  /-- the root is reached -/
  root : o ∈ σ.vis
  /-- only edges of `D` are revealed -/
  rev_sub : σ.rev ⊆ D
  /-- every revealed edge touches the reached set -/
  touch : ∀ e ∈ σ.rev, ∃ u ∈ σ.vis, u ∈ e
  /-- open revealed edges have both endpoints reached -/
  open_vis : ∀ e ∈ σ.rev, e ∈ K → ∀ v ∈ e, v ∈ σ.vis
  /-- reached vertices are joined to the root by open revealed edges -/
  reach : ∀ v ∈ σ.vis, (openGraph (↑(σ.rev ∩ K) : Set (Sym2 V))).Reachable o v
  /-- at most one target is reached -/
  one : (σ.vis ∩ A).card ≤ 1

section Invariant

variable {D : Finset (Sym2 V)} {A : Finset V} {o : V} {K : Finset (Sym2 V)}

omit [Fintype V] in
/-- The initial state satisfies the invariant. [folklore] -/
theorem inv_init : Inv D A o K (init o) where
  root := mem_singleton_self o
  rev_sub := by simp [init]
  touch := by simp [init]
  open_vis := by simp [init]
  reach := by
    intro v hv
    simp only [init, mem_singleton] at hv
    rw [hv]
  one := by
    refine (card_le_card (inter_subset_left (s₁ := {o}) (s₂ := A))).trans ?_
    simp

/-- **The invariant is preserved by a step.** [folklore] -/
theorem inv_step {σ : St V} (hσ : Inv D A o K σ) : Inv D A o K (step D A K σ) := by
  by_cases h : Halted D A σ
  · rw [step_of_halted h]; exact hσ
  obtain ⟨e, he, -, hstep⟩ := step_of_not_halted (K := K) h
  have hA : σ.vis ∩ A = ∅ := by
    simp only [Halted, not_or] at h
    exact not_nonempty_iff_eq_empty.1 h.1
  obtain ⟨⟨u, hu, v, hv, rfl⟩, heD, herev⟩ := mem_bnd.1 he
  have huv : u ≠ v := fun h => hv (h ▸ hu)
  have hmono : (openGraph (↑(σ.rev ∩ K) : Set (Sym2 V))) ≤
      openGraph (↑(insert s(u, v) σ.rev ∩ K) : Set (Sym2 V)) :=
    openGraph_mono (coe_subset.2 (inter_subset_inter (subset_insert _ _) subset_rfl))
  rw [hstep]
  split_ifs with hK
  · -- the revealed edge is open: the far endpoint `v` is added
    rw [newEnds_eq_singleton hu hv]
    refine ⟨mem_union_left _ hσ.root, insert_subset heD hσ.rev_sub, ?_, ?_, ?_, ?_⟩
    · intro e he'
      rcases mem_insert.1 he' with rfl | he'
      · exact ⟨u, mem_union_left _ hu, Sym2.mem_mk_left u v⟩
      · obtain ⟨w, hw, hwe⟩ := hσ.touch e he'
        exact ⟨w, mem_union_left _ hw, hwe⟩
    · intro e he' heK x hx
      rcases mem_insert.1 he' with rfl | he'
      · rcases Sym2.mem_iff.1 hx with rfl | rfl
        · exact mem_union_left _ hu
        · exact mem_union_right _ (mem_singleton_self _)
      · exact mem_union_left _ (hσ.open_vis e he' heK x hx)
    · intro x hx
      rcases mem_union.1 hx with hx | hx
      · exact (hσ.reach x hx).mono hmono
      · rw [mem_singleton] at hx
        subst hx
        have hadj : (openGraph (↑(insert s(u, x) σ.rev ∩ K) : Set (Sym2 V))).Adj u x := by
          rw [openGraph_adj]
          exact ⟨mem_coe.2 (mem_inter.2 ⟨mem_insert_self _ _, hK⟩), huv⟩
        exact ((hσ.reach u hu).mono hmono).trans hadj.reachable
    · have hsub : (σ.vis ∪ {v}) ∩ A ⊆ {v} := by
        intro x hx
        rw [mem_inter, mem_union] at hx
        rcases hx.1 with hx1 | hx1
        · exact absurd (mem_inter.2 ⟨hx1, hx.2⟩) (hA ▸ notMem_empty x)
        · exact hx1
      exact (card_le_card hsub).trans (card_singleton v).le
  · -- the revealed edge is closed
    refine ⟨hσ.root, insert_subset heD hσ.rev_sub, ?_, ?_, ?_, hσ.one⟩
    · intro e he'
      rcases mem_insert.1 he' with rfl | he'
      · exact ⟨u, hu, Sym2.mem_mk_left u v⟩
      · exact hσ.touch e he'
    · intro e he' heK x hx
      rcases mem_insert.1 he' with rfl | he'
      · exact absurd heK hK
      · exact hσ.open_vis e he' heK x hx
    · intro x hx
      exact (hσ.reach x hx).mono hmono

/-- The invariant holds along the run. [folklore] -/
theorem inv_run (K : Finset (Sym2 V)) : ∀ k, Inv D A o K (run D A o K k)
  | 0 => inv_init
  | k + 1 => inv_step (inv_run K k)

/-- The invariant holds at the final state. [folklore] -/
theorem inv_fin (K : Finset (Sym2 V)) : Inv D A o K (fin D A o K) := inv_run K _

end Invariant

end TargetExploration

end Percolation.Literature

end
