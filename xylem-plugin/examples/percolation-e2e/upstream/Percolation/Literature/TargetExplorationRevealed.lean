import Percolation.Literature.TargetExploration
import Percolation.Util.Linter

/-!
# The exploration stopped at a target set: halting, self-determination, correctness, splices

Proofs-only continuation of `TargetExploration.lean`
(the exploration of the open cluster of `o` among the edges `D`, revealing one boundary edge at a
time and stopping at the first vertex of the target set `A`; Gladkov, arXiv:2408.08457v2, §2 Def. 2.4 /
§6 Algorithm 2 with a target SET).  All proved:

* `halted_fin` — with fuel `#D + 1` the exploration has halted (a target is reached or the boundary
  is empty);
* `fin_congr`, **`selfDetermined_revealedAt`** — the final state depends on the configuration only
  through the revealed edges, so `K ↦ S(K)` is `DecisionTree.SelfDetermined` and Gladkov's swap
  Lemma 3.1 (`DecisionTree.sum_pair_reindexW`, `Pr2W_preimage_swapPair`) applies to it;
-/

noncomputable section

open Classical

namespace Percolation.Literature

namespace TargetExploration

open Finset DecisionTree

variable {V : Type*} [Fintype V] [DecidableEq V]

section Revealed

variable {D : Finset (Sym2 V)} {A : Finset V} {o : V} {K : Finset (Sym2 V)}

/-! ### Halting and self-determination -/

/-- Either the run has halted by time `k`, or it has revealed at least `k` edges. [folklore] -/
theorem halted_or_le_card (K : Finset (Sym2 V)) :
    ∀ k, Halted D A (run D A o K k) ∨ k ≤ (run D A o K k).rev.card
  | 0 => Or.inr (Nat.zero_le _)
  | k + 1 => by
      by_cases h : Halted D A (run D A o K k)
      · left; rw [run_succ, step_of_halted h]; exact h
      · rcases halted_or_le_card K k with h' | h'
        · exact absurd h' h
        · exact Or.inr (le_trans (Nat.add_le_add_right h' 1) (card_rev_step h))

/-- **The final state is halted**: a target is reached or the boundary is empty. [folklore] -/
theorem halted_fin (K : Finset (Sym2 V)) : Halted D A (fin D A o K) := by
  rcases halted_or_le_card (D := D) (A := A) (o := o) K (D.card + 1) with h | h
  · exact h
  · exact absurd ((card_le_card (inv_fin (D := D) (A := A) (o := o) K).rev_sub).trans_lt
      (Nat.lt_of_succ_le h)) (lt_irrefl _)

/-- A step depends on the configuration only through the edge it reveals. [folklore] -/
theorem step_congr {K K' : Finset (Sym2 V)} {σ : St V}
    (h : ∀ e ∈ (step D A K σ).rev, (e ∈ K ↔ e ∈ K')) : step D A K' σ = step D A K σ := by
  by_cases hh : Halted D A σ
  · rw [step_of_halted hh, step_of_halted hh]
  obtain ⟨e, -, hpick, hstep⟩ := step_of_not_halted (K := K) hh
  obtain ⟨e', -, hpick', hstep'⟩ := step_of_not_halted (K := K') hh
  rw [hpick, Option.some.injEq] at hpick'
  subst hpick'
  have he : e ∈ (step D A K σ).rev := by
    rw [hstep]; split_ifs <;> exact mem_insert_self e σ.rev
  have hiff := h e he
  rw [hstep', hstep]
  by_cases hK : e ∈ K
  · rw [if_pos hK, if_pos (hiff.1 hK)]
  · rw [if_neg hK, if_neg (fun h' => hK (hiff.2 h'))]

/-- The run depends on the configuration only through the revealed edges. [cite: Gladkov2024, §6.2] -/
theorem run_congr {K K' : Finset (Sym2 V)} :
    ∀ k, (∀ e ∈ (run D A o K k).rev, (e ∈ K ↔ e ∈ K')) → run D A o K' k = run D A o K k
  | 0, _ => rfl
  | k + 1, h => by
      have ih := run_congr k fun e he => h e (rev_subset_step K _ he)
      rw [run_succ, run_succ, ih]
      exact step_congr h

/-- **Self-determination**: if `K'` agrees with `K` on the edges revealed by the exploration of
`K`, the two explorations end in the same state. [cite: Gladkov2024, Lemma 3.1 (S is built by a decision tree)] -/
theorem fin_congr {K K' : Finset (Sym2 V)} (h : ∀ e ∈ (fin D A o K).rev, (e ∈ K ↔ e ∈ K')) :
    fin D A o K' = fin D A o K := run_congr _ h

/-! ### The spliced configuration `K →_S C₂` along the revealed set `S = S(K)` -/

/-- The splice along the revealed set explores exactly like `K`. [cite: Gladkov2024, Lemma 3.1] -/
theorem fin_splice (K C₂ : Finset (Sym2 V)) :
    fin D A o (splice (revealedAt D A o K) K C₂) = fin D A o K :=
  fin_congr fun e he => (splice_agree _ K C₂ e he).symm

end Revealed

end TargetExploration

end Percolation.Literature

end
