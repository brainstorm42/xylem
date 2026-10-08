import Percolation.Literature.TargetExplorationHK
import Percolation.Util.Linter

/-!
# The full exploration of the open cluster of a vertex SET, its decision tree, and the decision-tree Harris–Kleitman inequality along it ("cluster-conditional Harris" for `C_N`)

Gladkov, *Percolation Inequalities and Decision Trees*,
arXiv:2408.08457v2 (2024), Def. 2.4, Example 2.5 (the exploration of an open cluster as a decision
tree) and Theorem 3.2 (p. 4, decision-tree Harris–Kleitman): for the set `S = S(C₁)` revealed by ANY
decision tree reading `C₁` and up-closed `A, B`, `P(C₁ ∈ A, C₁ →_S C₂ ∈ B) ≥ P(A) P(B)`.

`TargetExploration*.lean` formalise the exploration of the cluster of ONE vertex `o`, stopped at a
target set, revealing only BOUNDARY edges.  The two-source lemma of the conditioned covariance
transfer (used for the additive gluing inequality `AdditiveGluing`, its Lemma (★_N)) needs the exploration of the cluster `C_N` of a vertex SET `N` which reveals EVERY edge of
`D` with at least one reached endpoint (so that, on the explored data, the clusters meeting `N` are
completely determined and the unrevealed edges are exactly the edges of `D` missing `C_N`).  This file
(all proved):

* `bnd`, `step`, `init`, `run`, `fin`, `reached`, `revealedAt` — the exploration from the root set `N`
  among the edges `D`: reveal, one at a time (choice by `Gladkov.pick`), an unrevealed edge of `D` with a
  reached endpoint; an open edge adds its endpoints;
* `Inv`, `inv_fin`, `bnd_fin` — invariant and termination (after `#D + 1` steps nothing is left to reveal);
* `mem_reached_iff` — the reached set is the `K ∩ D`-open cluster of `N`;
  `mem_revealedAt_iff` — the revealed set is the set of edges of `D` meeting that cluster;
* `run_congr`, `selfDetermined_revealedAt` — self-determination (Gladkov Lemma 3.1 applies);

## References
* N. Gladkov, *Percolation Inequalities and Decision Trees*, arXiv:2408.08457v2 (2024), Def. 2.4,
  Example 2.5, Lemma 3.1, Theorem 3.2. [Gladkov2024]
* J. van den Berg, O. Häggström, J. Kahn, *Some conditional correlation inequalities for percolation and
  related processes*, Random Struct. Alg. 29 (2006), eq. (6) (the Markov property at an explored set). [VandenbergHaggstromKahn2005]
-/

noncomputable section

open Classical

namespace Percolation.Literature

namespace SetClusterExploration

open Finset DecisionTree
open TargetExploration (St)

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### The exploration -/

section Defs

variable (D : Finset (Sym2 V)) (N : Finset V)

/-- The endpoints of an edge, as a finset. [folklore] -/
def ends (e : Sym2 V) : Finset V := univ.filter fun v => v ∈ e

/-- The boundary of a state: unrevealed edges of `D` with at least one reached endpoint (internal edges
included, so that the final revealed set is every edge of `D` meeting the cluster).
[cite: Gladkov2024, §2 Example 2.5] -/
def bnd (σ : St V) : Finset (Sym2 V) := (D \ σ.rev).filter fun e => ∃ u ∈ σ.vis, u ∈ e

/-- One step on the configuration `K`: reveal a boundary edge (if any); if it is open, add its endpoints.
[cite: Gladkov2024, §2 Example 2.5] -/
def step (K : Finset (Sym2 V)) (σ : St V) : St V :=
  match Gladkov.pick (bnd D σ) with
  | none => σ
  | some e => if e ∈ K then ⟨σ.vis ∪ ends e, insert e σ.rev⟩ else ⟨σ.vis, insert e σ.rev⟩

/-- The initial state: the root set reached, nothing revealed. [folklore] -/
def init : St V := ⟨N, ∅⟩

/-- The state after `k` steps. [cite: Gladkov2024, §2 Example 2.5] -/
def run (K : Finset (Sym2 V)) : ℕ → St V
  | 0 => init N
  | k + 1 => step D K (run K k)

/-- The final state (fuel `#D + 1`, enough by `bnd_fin`). [folklore] -/
def fin (K : Finset (Sym2 V)) : St V := run D N K (D.card + 1)

/-- The reached set of the full exploration of the cluster of `N`. [folklore] -/
def reached (K : Finset (Sym2 V)) : Finset V := (fin D N K).vis

/-- The revealed edge set `S_N(K)` of the full exploration of the cluster of `N`. [cite: Gladkov2024, Def. 2.4] -/
def revealedAt (K : Finset (Sym2 V)) : Finset (Sym2 V) := (fin D N K).rev

end Defs

/-! ### Basic facts about one step -/

section Basic

variable {D : Finset (Sym2 V)} {N : Finset V}

/-- Membership in `ends`. [folklore] -/
@[simp] private theorem mem_ends {e : Sym2 V} {v : V} : v ∈ ends e ↔ v ∈ e := by
  simp [ends]

omit [Fintype V] in
/-- Membership in the boundary. [cite: Gladkov2024, §2 Example 2.5 (p. 3)] -/
theorem mem_bnd {σ : St V} {e : Sym2 V} :
    e ∈ bnd D σ ↔ (e ∈ D ∧ e ∉ σ.rev) ∧ ∃ u ∈ σ.vis, u ∈ e := by
  simp [bnd, mem_filter, mem_sdiff]

/-- With an empty boundary a step does nothing. [cite: Gladkov2024, §2 Example 2.5 (p. 3)] -/
theorem step_of_bnd_eq_empty {K : Finset (Sym2 V)} {σ : St V} (h : bnd D σ = ∅) : step D K σ = σ := by
  unfold step
  rw [TargetExploration.pick_eq_none_iff.2 h]

/-- With a nonempty boundary a step reveals the picked boundary edge. [cite: Gladkov2024, §2 Example 2.5 (p. 3)] -/
theorem step_of_bnd_ne_empty {K : Finset (Sym2 V)} {σ : St V} (h : bnd D σ ≠ ∅) :
    ∃ e ∈ bnd D σ, Gladkov.pick (bnd D σ) = some e ∧
      step D K σ = (if e ∈ K then ⟨σ.vis ∪ ends e, insert e σ.rev⟩ else ⟨σ.vis, insert e σ.rev⟩) := by
  unfold step
  cases hp : Gladkov.pick (bnd D σ) with
  | none => exact absurd (TargetExploration.pick_eq_none_iff.1 hp) h
  | some e => exact ⟨e, Gladkov.mem_of_pick_eq_some hp, rfl, rfl⟩

/-- The revealed set grows by one step. [cite: Gladkov2024, §2 Example 2.5 (p. 3)] -/
theorem rev_subset_step (K : Finset (Sym2 V)) (σ : St V) : σ.rev ⊆ (step D K σ).rev := by
  by_cases h : bnd D σ = ∅
  · rw [step_of_bnd_eq_empty h]
  · obtain ⟨e, -, -, hstep⟩ := step_of_bnd_ne_empty (K := K) h
    rw [hstep]
    split_ifs <;> exact subset_insert e σ.rev

/-- With a nonempty boundary the revealed set grows strictly. [cite: Gladkov2024, §2 Example 2.5 (p. 3)] -/
theorem card_rev_step {K : Finset (Sym2 V)} {σ : St V} (h : bnd D σ ≠ ∅) :
    σ.rev.card + 1 ≤ (step D K σ).rev.card := by
  obtain ⟨e, he, -, hstep⟩ := step_of_bnd_ne_empty (K := K) h
  have herev : e ∉ σ.rev := ((mem_bnd.1 he).1).2
  rw [hstep]
  split_ifs <;> simp [card_insert_of_notMem herev]

/-- `run (k+1) = step (run k)`. [cite: Gladkov2024, §2 Example 2.5 (p. 3)] -/
theorem run_succ (K : Finset (Sym2 V)) (k : ℕ) : run D N K (k + 1) = step D K (run D N K k) := rfl

end Basic

/-! ### The invariant -/

/-- The invariant of the full exploration of the `K`-open cluster of the set `N` among the edges `D`.
[cite: Gladkov2024, §6.2 (structure of the revealed set)] -/
structure Inv (D : Finset (Sym2 V)) (N : Finset V) (K : Finset (Sym2 V)) (σ : St V) : Prop where
  /-- the root set is reached -/
  root : N ⊆ σ.vis
  /-- only edges of `D` are revealed -/
  rev_sub : σ.rev ⊆ D
  /-- every revealed edge touches the reached set -/
  touch : ∀ e ∈ σ.rev, ∃ u ∈ σ.vis, u ∈ e
  /-- open revealed edges have both endpoints reached -/
  open_vis : ∀ e ∈ σ.rev, e ∈ K → ∀ v ∈ e, v ∈ σ.vis
  /-- reached vertices are joined to the root set by open revealed edges -/
  reach : ∀ v ∈ σ.vis, ∃ s ∈ N, (openGraph (↑(σ.rev ∩ K) : Set (Sym2 V))).Reachable s v

section Invariant

variable {D : Finset (Sym2 V)} {N : Finset V} {K : Finset (Sym2 V)}

omit [Fintype V] in
/-- The initial state satisfies the invariant. [cite: Gladkov2024, §6.2 (structure of the revealed set)] -/
theorem inv_init : Inv D N K (init N) where
  root := by simp [init]
  rev_sub := by simp [init]
  touch := by simp [init]
  open_vis := by simp [init]
  reach := by
    intro v hv
    exact ⟨v, by simpa [init] using hv, SimpleGraph.Reachable.refl _⟩

/-- **The invariant is preserved by a step.** [cite: Gladkov2024, §6.2 (structure of the revealed set)] -/
theorem inv_step {σ : St V} (hσ : Inv D N K σ) : Inv D N K (step D K σ) := by
  by_cases h : bnd D σ = ∅
  · rw [step_of_bnd_eq_empty h]; exact hσ
  obtain ⟨e, he, -, hstep⟩ := step_of_bnd_ne_empty (K := K) h
  obtain ⟨⟨heD, herev⟩, u, hu, hue⟩ := mem_bnd.1 he
  have hmono : (openGraph (↑(σ.rev ∩ K) : Set (Sym2 V))) ≤
      openGraph (↑(insert e σ.rev ∩ K) : Set (Sym2 V)) :=
    openGraph_mono (coe_subset.2 (inter_subset_inter (subset_insert _ _) subset_rfl))
  rw [hstep]
  split_ifs with hK
  · -- the revealed edge is open: its endpoints are added
    refine ⟨hσ.root.trans subset_union_left, insert_subset heD hσ.rev_sub, ?_, ?_, ?_⟩
    · intro e' he'
      rcases mem_insert.1 he' with rfl | he'
      · exact ⟨u, mem_union_left _ hu, hue⟩
      · obtain ⟨w, hw, hwe⟩ := hσ.touch e' he'
        exact ⟨w, mem_union_left _ hw, hwe⟩
    · intro e' he' heK x hx
      rcases mem_insert.1 he' with rfl | he'
      · exact mem_union_right _ (mem_ends.2 hx)
      · exact mem_union_left _ (hσ.open_vis e' he' heK x hx)
    · intro x hx
      rcases mem_union.1 hx with hx | hx
      · obtain ⟨s, hs, hsx⟩ := hσ.reach x hx
        exact ⟨s, hs, hsx.mono hmono⟩
      · rw [mem_ends] at hx
        obtain ⟨s, hs, hsu⟩ := hσ.reach u hu
        refine ⟨s, hs, (hsu.mono hmono).trans ?_⟩
        by_cases hux : u = x
        · subst hux; exact SimpleGraph.Reachable.refl _
        · have hexu : e = s(u, x) := (Sym2.mem_and_mem_iff hux).1 ⟨hue, hx⟩
          have hadj : (openGraph (↑(insert e σ.rev ∩ K) : Set (Sym2 V))).Adj u x := by
            rw [openGraph_adj]
            refine ⟨?_, hux⟩
            rw [← hexu]
            exact mem_coe.2 (mem_inter.2 ⟨mem_insert_self _ _, hK⟩)
          exact hadj.reachable
  · -- the revealed edge is closed
    refine ⟨hσ.root, insert_subset heD hσ.rev_sub, ?_, ?_, ?_⟩
    · intro e' he'
      rcases mem_insert.1 he' with rfl | he'
      · exact ⟨u, hu, hue⟩
      · exact hσ.touch e' he'
    · intro e' he' heK x hx
      rcases mem_insert.1 he' with rfl | he'
      · exact absurd heK hK
      · exact hσ.open_vis e' he' heK x hx
    · intro x hx
      obtain ⟨s, hs, hsx⟩ := hσ.reach x hx
      exact ⟨s, hs, hsx.mono hmono⟩

/-- The invariant holds along the run. [cite: Gladkov2024, §6.2 (structure of the revealed set)] -/
theorem inv_run (K : Finset (Sym2 V)) : ∀ k, Inv D N K (run D N K k)
  | 0 => inv_init
  | k + 1 => inv_step (inv_run K k)

/-- The invariant holds at the final state. [cite: Gladkov2024, §6.2 (structure of the revealed set)] -/
theorem inv_fin (K : Finset (Sym2 V)) : Inv D N K (fin D N K) := inv_run K _

/-! ### Termination -/

/-- Either the boundary is empty by time `k`, or at least `k` edges have been revealed. [cite: Gladkov2024, §6.2 (structure of the revealed set)] -/
theorem bnd_empty_or_le_card (K : Finset (Sym2 V)) :
    ∀ k, bnd D (run D N K k) = ∅ ∨ k ≤ (run D N K k).rev.card
  | 0 => Or.inr (Nat.zero_le _)
  | k + 1 => by
      by_cases h : bnd D (run D N K k) = ∅
      · left; rw [run_succ, step_of_bnd_eq_empty h]; exact h
      · rcases bnd_empty_or_le_card K k with h' | h'
        · exact absurd h' h
        · exact Or.inr (le_trans (Nat.add_le_add_right h' 1) (card_rev_step h))

/-- **The exploration is complete at the final state**: no edge of `D` with a reached endpoint is left
unrevealed. [cite: Gladkov2024, §6.2 (structure of the revealed set)] -/
theorem bnd_fin (K : Finset (Sym2 V)) : bnd D (fin D N K) = ∅ := by
  rcases bnd_empty_or_le_card (D := D) (N := N) K (D.card + 1) with h | h
  · exact h
  · exact absurd ((card_le_card (inv_fin (D := D) (N := N) K).rev_sub).trans_lt
      (Nat.lt_of_succ_le h)) (lt_irrefl _)

/-! ### What the exploration reveals -/

omit [Fintype V] [DecidableEq V] in
/-- A set containing the start of a walk and closed under adjacency along the walk's graph contains its
end. [folklore] -/
private theorem mem_of_walk_closed {G : SimpleGraph V} {S : Set V}
    (hS : ∀ a b, G.Adj a b → a ∈ S → b ∈ S) {u v : V} (p : G.Walk u v) (hu : u ∈ S) : v ∈ S := by
  induction p with
  | nil => exact hu
  | cons hadj _ ih => exact ih (hS _ _ hadj hu)

/-- **The reached set is the open cluster of `N`** (through the edges of `K ∩ D`).
[cite: Gladkov2024, §2 Example 2.5] -/
theorem mem_reached_iff {v : V} :
    v ∈ reached D N K ↔ ∃ s ∈ N, (openGraph (↑(K ∩ D) : Set (Sym2 V))).Reachable s v := by
  have hI := inv_fin (D := D) (N := N) K
  constructor
  · intro hv
    obtain ⟨s, hs, hsv⟩ := hI.reach v hv
    refine ⟨s, hs, hsv.mono (openGraph_mono (coe_subset.2 ?_))⟩
    intro e he
    rw [mem_inter] at he ⊢
    exact ⟨he.2, hI.rev_sub he.1⟩
  · rintro ⟨s, hs, hsv⟩
    obtain ⟨p⟩ := hsv
    have hclosed : ∀ a b, (openGraph (↑(K ∩ D) : Set (Sym2 V))).Adj a b →
        a ∈ (↑(fin D N K).vis : Set V) → b ∈ (↑(fin D N K).vis : Set V) := by
      intro a b hab ha
      rw [openGraph_adj] at hab
      obtain ⟨he, hne⟩ := hab
      rw [mem_coe, mem_inter] at he
      rw [mem_coe] at ha ⊢
      -- the edge `s(a,b)` touches the reached set, so it has been revealed (the final boundary is empty)
      by_contra hb
      by_cases hrev : s(a, b) ∈ (fin D N K).rev
      · exact hb (hI.open_vis _ hrev he.1 b (Sym2.mem_mk_right a b))
      · have hmem : s(a, b) ∈ bnd D (fin D N K) :=
          mem_bnd.2 ⟨⟨he.2, hrev⟩, a, ha, Sym2.mem_mk_left a b⟩
        rw [bnd_fin] at hmem
        exact notMem_empty _ hmem
    have := mem_of_walk_closed hclosed p (mem_coe.2 (hI.root hs))
    exact mem_coe.1 this

/-- **The revealed set is the set of edges of `D` meeting the cluster of `N`.**
[cite: Gladkov2024, §2 Example 2.5] -/
theorem mem_revealedAt_iff {e : Sym2 V} :
    e ∈ revealedAt D N K ↔ e ∈ D ∧ ∃ u ∈ reached D N K, u ∈ e := by
  have hI := inv_fin (D := D) (N := N) K
  constructor
  · intro he
    exact ⟨hI.rev_sub he, hI.touch e he⟩
  · rintro ⟨heD, u, hu, hue⟩
    by_contra hrev
    have hmem : e ∈ bnd D (fin D N K) := mem_bnd.2 ⟨⟨heD, hrev⟩, u, hu, hue⟩
    rw [bnd_fin] at hmem
    exact notMem_empty _ hmem

/-! ### Self-determination -/

/-- A step depends on the configuration only through the edge it reveals. [cite: Gladkov2024, Lemma 3.1] -/
theorem step_congr {K K' : Finset (Sym2 V)} {σ : St V}
    (h : ∀ e ∈ (step D K σ).rev, (e ∈ K ↔ e ∈ K')) : step D K' σ = step D K σ := by
  by_cases hh : bnd D σ = ∅
  · rw [step_of_bnd_eq_empty hh, step_of_bnd_eq_empty hh]
  obtain ⟨e, -, hpick, hstep⟩ := step_of_bnd_ne_empty (K := K) hh
  obtain ⟨e', -, hpick', hstep'⟩ := step_of_bnd_ne_empty (K := K') hh
  rw [hpick, Option.some.injEq] at hpick'
  subst hpick'
  have he : e ∈ (step D K σ).rev := by
    rw [hstep]; split_ifs <;> exact mem_insert_self e σ.rev
  have hiff := h e he
  rw [hstep', hstep]
  by_cases hK : e ∈ K
  · rw [if_pos hK, if_pos (hiff.1 hK)]
  · rw [if_neg hK, if_neg (fun h' => hK (hiff.2 h'))]

/-- The run depends on the configuration only through the revealed edges. [cite: Gladkov2024, Lemma 3.1] -/
theorem run_congr {K K' : Finset (Sym2 V)} :
    ∀ k, (∀ e ∈ (run D N K k).rev, (e ∈ K ↔ e ∈ K')) → run D N K' k = run D N K k
  | 0, _ => rfl
  | k + 1, h => by
      have ih := run_congr k fun e he => h e (rev_subset_step K _ he)
      rw [run_succ, run_succ, ih]
      exact step_congr h

/-- **Self-determination**: a configuration agreeing with `K` on `S_N(K)` ends in the same state.
[cite: Gladkov2024, Lemma 3.1] -/
theorem fin_congr {K K' : Finset (Sym2 V)} (h : ∀ e ∈ revealedAt D N K, (e ∈ K ↔ e ∈ K')) :
    fin D N K' = fin D N K := run_congr _ h

/-- `K ↦ S_N(K)` is self-determined (`DecisionTree.SelfDetermined`). [cite: Gladkov2024, Lemma 3.1] -/
theorem selfDetermined_revealedAt : SelfDetermined (revealedAt D N) :=
  fun _ _ h => congrArg St.rev (fin_congr h)

/-! ### The hybrid `C₁ →_{S_N(C₁)} C₂` -/

/-- The hybrid agrees with `C₁` on the revealed set, hence is explored identically. [cite: Gladkov2024, Lemma 3.1] -/
theorem fin_splice (C₁ C₂ : Finset (Sym2 V)) :
    fin D N (splice (revealedAt D N C₁) C₁ C₂) = fin D N C₁ :=
  fin_congr fun e he => (splice_agree _ C₁ C₂ e he).symm

/-- The hybrid has the same cluster of `N` as `C₁`. [cite: Gladkov2024, Lemma 3.1] -/
theorem reached_splice (C₁ C₂ : Finset (Sym2 V)) :
    reached D N (splice (revealedAt D N C₁) C₁ C₂) = reached D N C₁ :=
  congrArg St.vis (fin_splice C₁ C₂)

end Invariant

/-! ### The decision tree and the Harris–Kleitman inequality along it -/

section Tree

variable (D : Finset (Sym2 V))

/-- The full exploration as a decision tree started at the state `σ` with fuel `n`: query the picked
boundary edge and branch on the answer. [cite: Gladkov2024, Def. 2.4 and Example 2.5] -/
def ttree : ℕ → St V → DTree (Sym2 V)
  | 0, _ => .leaf
  | n + 1, σ =>
      match Gladkov.pick (bnd D σ) with
      | none => .leaf
      | some e => .node e (ttree n ⟨σ.vis ∪ ends e, insert e σ.rev⟩) (ttree n ⟨σ.vis, insert e σ.rev⟩)

variable {D}

/-- **The tree reveals what the exploration reveals.** [cite: Gladkov2024, Def. 2.4 and Example 2.5] -/
theorem rev_iterate_step (K : Finset (Sym2 V)) :
    ∀ (n : ℕ) (σ : St V), ((step D K)^[n] σ).rev = σ.rev ∪ revealed (ttree D n σ) K
  | 0, σ => by simp [ttree, revealed]
  | n + 1, σ => by
      rw [Function.iterate_succ_apply]
      by_cases h : bnd D σ = ∅
      · rw [step_of_bnd_eq_empty h, Function.iterate_fixed (step_of_bnd_eq_empty h)]
        simp [ttree, TargetExploration.pick_eq_none_iff.2 h, revealed]
      · obtain ⟨e, -, hpick, hstep⟩ := step_of_bnd_ne_empty (D := D) (K := K) h
        have htree : ttree D (n + 1) σ =
            .node e (ttree D n ⟨σ.vis ∪ ends e, insert e σ.rev⟩) (ttree D n ⟨σ.vis, insert e σ.rev⟩) := by
          simp only [ttree, hpick]
        rw [hstep, htree]
        by_cases he : e ∈ K
        · rw [if_pos he, rev_iterate_step K n]
          simp only [revealed, if_pos he, Finset.insert_union, Finset.union_insert]
        · rw [if_neg he, rev_iterate_step K n]
          simp only [revealed, if_neg he, Finset.insert_union, Finset.union_insert]

/-- `run` is the iterated `step`. [folklore] -/
private theorem run_eq_iterate (N : Finset V) (K : Finset (Sym2 V)) :
    ∀ k : ℕ, run D N K k = (step D K)^[k] (init N)
  | 0 => rfl
  | k + 1 => by rw [run_succ, Function.iterate_succ_apply', run_eq_iterate N K k]

/-- **The revealed set of the full exploration is the set built by its decision tree.**
[cite: Gladkov2024, Def. 2.4 and Example 2.5] -/
theorem revealedAt_eq_revealed (N : Finset V) (K : Finset (Sym2 V)) :
    revealedAt D N K = revealed (ttree D (D.card + 1) (init N)) K := by
  rw [revealedAt, fin, run_eq_iterate, rev_iterate_step]
  simp [init]

end Tree

end SetClusterExploration

end Percolation.Literature

end
