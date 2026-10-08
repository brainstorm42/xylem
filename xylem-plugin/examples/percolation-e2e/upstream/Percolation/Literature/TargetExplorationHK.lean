import Percolation.Literature.TargetExplorationRevealed
import Percolation.Util.Linter

/-!
# The decision-tree Harris–Kleitman inequality along the stopped target exploration

Gladkov, *Percolation Inequalities and Decision Trees*,
arXiv:2408.08457v2 (2024), Theorem 3.2 (p. 4): "Let `S(C₁, C₂)` be built by some decision tree.  Assume
`A` and `B` are some events in `Ω` closed upward.  Then `P(C₁ ∈ A, C₁ →_S C₂ ∈ B) ≥ P(C₁ ∈ A) P(C₁ →_S C₂ ∈ B)
= μ(A) μ(B)`", for the decision tree of his Example 2.5 / §6 Algorithm 2: the exploration of the open cluster
of a vertex `o` stopped at a target set `A` (`TargetExploration.lean`; with `A = ∅` it reveals the whole
cluster of `o` together with its closed edge boundary).  `DecisionTree.PrW_mul_PrW_le_Pr2W_treeHK`
(`DecisionTreeWeighted.lean`) is Theorem 3.2 for an abstract `DTree`; here (all proved):

* `ttree` — the exploration as a `DTree` (query the picked boundary edge, branch on the answer);
* `rev_iterate_step`, `revealedAt_eq_revealed` — the set it builds on `K` is the revealed set `S(K)` of the
  exploration (`revealedAt`);
* **`PrW_mul_PrW_le_Pr2W_hybrid`** — Theorem 3.2 for this tree: for up-closed `X, Y`,
  `P(X) P(Y) ≤ P⊗P{(C₁, C₂) : C₁ ∈ X, C₁ →_{S(C₁)} C₂ ∈ Y}`.  Since `S(C₁)` determines the explored cluster,
  the hybrid `C₁ →_{S(C₁)} C₂` is "the configuration resampled outside the revealed set": the inequality says
  that the conditional expectations of two increasing events given the exploration σ-field are positively
  correlated ("cluster-conditional Harris"), the tool behind cluster-conditioning arguments for the marker
  dominance inequality behind the additive gluing inequality `AdditiveGluing`.

## References
* N. Gladkov, *Percolation Inequalities and Decision Trees*, arXiv:2408.08457v2 (2024), Def. 2.4, Example 2.5,
  Theorem 3.2. [Gladkov2024]
-/

noncomputable section

open Classical

namespace Percolation.Literature

namespace TargetExploration

open Finset DecisionTree

variable {V : Type*} [Fintype V] [DecidableEq V]

section Tree

variable (D : Finset (Sym2 V)) (A : Finset V)

/-- The stopped target exploration as a decision tree (`DecisionTreeBK.DTree`) started at the state `σ`
with fuel `n`: at a halted state stop; otherwise query the picked boundary edge `e`, branch on the answer
(open: the far endpoint is reached) and continue. [cite: Gladkov2024, Def. 2.4 and Example 2.5] -/
def ttree : ℕ → St V → DTree (Sym2 V)
  | 0, _ => .leaf
  | n + 1, σ =>
      if Halted D A σ then .leaf
      else
        match Gladkov.pick (bnd D σ) with
        | none => .leaf
        | some e => .node e (ttree n ⟨σ.vis ∪ newEnds σ e, insert e σ.rev⟩) (ttree n ⟨σ.vis, insert e σ.rev⟩)

variable {D A}

/-- **The tree reveals what the exploration reveals**: after `n` steps from `σ` on the configuration `K`,
the revealed set is `σ.rev` together with the set built by `ttree n σ` on `K`.
[cite: Gladkov2024, Def. 2.4 and Example 2.5] -/
theorem rev_iterate_step (K : Finset (Sym2 V)) :
    ∀ (n : ℕ) (σ : St V), ((step D A K)^[n] σ).rev = σ.rev ∪ revealed (ttree D A n σ) K
  | 0, σ => by simp [ttree, revealed]
  | n + 1, σ => by
      rw [Function.iterate_succ_apply]
      by_cases h : Halted D A σ
      · rw [step_of_halted h, Function.iterate_fixed (step_of_halted h)]
        simp [ttree, h, revealed]
      · obtain ⟨e, -, hpick, hstep⟩ := step_of_not_halted (D := D) (A := A) (K := K) h
        have htree : ttree D A (n + 1) σ =
            .node e (ttree D A n ⟨σ.vis ∪ newEnds σ e, insert e σ.rev⟩)
              (ttree D A n ⟨σ.vis, insert e σ.rev⟩) := by
          simp only [ttree, if_neg h, hpick]
        rw [hstep, htree]
        by_cases he : e ∈ K
        · rw [if_pos he, rev_iterate_step K n]
          simp only [revealed, if_pos he, Finset.insert_union, Finset.union_insert]
        · rw [if_neg he, rev_iterate_step K n]
          simp only [revealed, if_neg he, Finset.insert_union, Finset.union_insert]

/-- `run` is the iterated `step`. [folklore] -/
private theorem run_eq_iterate (o : V) (K : Finset (Sym2 V)) :
    ∀ k : ℕ, run D A o K k = (step D A K)^[k] (init o)
  | 0 => rfl
  | k + 1 => by rw [run_succ, Function.iterate_succ_apply', run_eq_iterate o K k]

/-- **The revealed set of the exploration is the set built by its decision tree.**
[cite: Gladkov2024, Def. 2.4 and Example 2.5] -/
theorem revealedAt_eq_revealed (o : V) (K : Finset (Sym2 V)) :
    revealedAt D A o K = revealed (ttree D A (D.card + 1) (init o)) K := by
  rw [revealedAt, fin, run_eq_iterate, rev_iterate_step]
  simp [init]

end Tree

section HK

variable (D : Finset (Sym2 V)) (A : Finset V) (o : V) {p : Sym2 V → ℝ}

/-- **Decision-tree Harris–Kleitman inequality for the stopped target exploration** (Gladkov 2024,
Theorem 3.2, for the tree of Example 2.5): for up-closed events `X, Y` of one configuration and
`0 ≤ p ≤ 1`, `P(X) · P(Y) ≤ P⊗P{(C₁, C₂) : C₁ ∈ X, C₁ →_{S(C₁)} C₂ ∈ Y}`, where `S(C₁)` is the revealed set of
the exploration of `C₁` from `o` stopped at `A` and `C₁ →_S C₂` agrees with `C₁` on `S` and with `C₂` off `S`.
[cite: Gladkov2024, Thm. 3.2 (p. 4)] -/
theorem PrW_mul_PrW_le_Pr2W_hybrid (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    {X Y : Set (Finset (Sym2 V))} (hX : IsUpperSet X) (hY : IsUpperSet Y) :
    PrW D p X * PrW D p Y ≤
      Pr2W D p {c | c.1 ∈ X ∧ splice (revealedAt D A o c.1) c.1 c.2 ∈ Y} := by
  have h := PrW_mul_PrW_le_Pr2W_treeHK D hp0 hp1 (ttree D A (D.card + 1) (init o)) hX hY
  have hset : treeHK ∅ (ttree D A (D.card + 1) (init o)) X Y =
      {c | c.1 ∈ X ∧ splice (revealedAt D A o c.1) c.1 c.2 ∈ Y} := by
    ext c
    simp only [treeHK, hkWith, Finset.empty_union, Set.mem_setOf_eq, revealedAt_eq_revealed]
  rwa [hset] at h

end HK

end TargetExploration

end Percolation.Literature

end
