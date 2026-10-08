import Percolation.Literature.TargetExplorationHK
import Percolation.Util.Linter

/-!
# Marker dominance, step P_v: hybrid bookkeeping for the cluster-conditioning lemma

Finitary calculus
`PrW / Pr2W / condSumW` of `DecisionTreeWeighted.lean`; `S(C₁)` a self-determined revealment (e.g. the
revealed set of the stopped target exploration, `TargetExploration.revealedAt`).

* `Pr2W_hybrid_eq_sum_condSumW` — `P⊗P{C₁ ∈ X, C₁ →_S C₂ ∈ B} = Σ_{K} wt(K)·1_X(K)·condSum_S(B)(K)`
  (the hybrid event as a first-configuration average of the conditional sum; [cite: Gladkov2024, §2 and proof of Thm. 5.2] bookkeeping).
* `sum_condSumW_ge` — with Gladkov's decision-tree Harris–Kleitman inequality for the target exploration
  (`TargetExploration.PrW_mul_PrW_le_Pr2W_hybrid`): `Σ_K wt(K) 1_X(K) condSum(F)(K) ≥ P(X)·P(F)` for up-closed `X, F`
  ("cluster-conditional Harris": the conditional expectations of two increasing events given the exploration
  σ-field are positively correlated).
-/

noncomputable section

open Classical

namespace Percolation.Continuity

namespace MarkerDominancePv

open Finset Percolation.Literature Percolation.Literature.DecisionTree
  Percolation.Literature.TargetExploration

variable {ι : Type*} [DecidableEq ι]

/-- **The hybrid event as a first-configuration average of the conditional sum**:
`P⊗P{(C₁,C₂) : C₁ ∈ X, C₁ →_{S(C₁)} C₂ ∈ B} = Σ_{K ⊆ D} wt(K) · 1_X(K) · condSum_S(B)(K)`. [folklore] -/
theorem Pr2W_hybrid_eq_sum_condSumW (D : Finset ι) (p : ι → ℝ) (Fm : Finset ι → Finset ι)
    (X B : Set (Finset ι)) :
    Pr2W D p {c | c.1 ∈ X ∧ splice (Fm c.1) c.1 c.2 ∈ B} =
      ∑ K ∈ D.powerset, wtW D p K * ind X K * condSumW D p Fm B K := by

  have hiter : Pr2W D p {c | c.1 ∈ X ∧ splice (Fm c.1) c.1 c.2 ∈ B} =
      ∑ S ∈ D.powerset, wtW D p S *
        PrW D p {T | (S, T) ∈ {c : Finset ι × Finset ι | c.1 ∈ X ∧ splice (Fm c.1) c.1 c.2 ∈ B}} := by
    unfold Pr2W PrW wt2W
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun T _ => ?_
    by_cases h : (S, T) ∈ {c : Finset ι × Finset ι | c.1 ∈ X ∧ splice (Fm c.1) c.1 c.2 ∈ B}
    · have h' : T ∈ ({T : Finset ι | (S, T) ∈
          {c : Finset ι × Finset ι | c.1 ∈ X ∧ splice (Fm c.1) c.1 c.2 ∈ B}} : Set (Finset ι)) := h
      rw [Set.indicator_of_mem h, Set.indicator_of_mem h']
    · have h' : T ∉ ({T : Finset ι | (S, T) ∈
          {c : Finset ι × Finset ι | c.1 ∈ X ∧ splice (Fm c.1) c.1 c.2 ∈ B}} : Set (Finset ι)) := h
      rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h', mul_zero]
  rw [hiter]
  refine Finset.sum_congr rfl fun K _ => ?_
  by_cases hK : K ∈ X
  · rw [ind_of_mem hK, mul_one]
    congr 1
    unfold PrW condSumW
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [indicator_eq_mul_ind]
    have : ({T : Finset ι | (K, T) ∈ {c : Finset ι × Finset ι | c.1 ∈ X ∧ splice (Fm c.1) c.1 c.2 ∈ B}} :
        Set (Finset ι)) = {T | splice (Fm K) K T ∈ B} := by
      ext T; simp [hK]
    rw [this]
    by_cases hT : splice (Fm K) K T ∈ B
    · rw [ind_of_mem hT, ind_of_mem (show T ∈ {T | splice (Fm K) K T ∈ B} from hT)]
    · rw [ind_of_not_mem hT, ind_of_not_mem (show T ∉ {T | splice (Fm K) K T ∈ B} from hT)]
  · rw [ind_of_not_mem hK, mul_zero, zero_mul]
    have : ({T : Finset ι | (K, T) ∈ {c : Finset ι × Finset ι | c.1 ∈ X ∧ splice (Fm c.1) c.1 c.2 ∈ B}} :
        Set (Finset ι)) = ∅ := by
      ext T; simp [hK]
    rw [this]
    unfold PrW
    simp

end MarkerDominancePv

section Explore

open Finset Percolation.Literature Percolation.Literature.DecisionTree
  Percolation.Literature.TargetExploration MarkerDominancePv

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Cluster-conditional Harris for the stopped target exploration** (Gladkov's Theorem 3.2 in
conditional-sum form): for up-closed `X, F` and weights in `[0,1]`,
`Σ_K wt(K)·1_X(K)·condSum_{S}(F)(K) ≥ P(X)·P(F)`, `S = revealedAt D A o`.
[cite: Gladkov2024, Thm. 3.2 (p. 4) — corollary] -/
theorem MarkerDominancePv.sum_condSumW_ge (D : Finset (Sym2 V)) (A : Finset V) (o : V) {p : Sym2 V → ℝ}
    (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1) {X F : Set (Finset (Sym2 V))} (hX : IsUpperSet X)
    (hF : IsUpperSet F) :
    PrW D p X * PrW D p F ≤
      ∑ K ∈ D.powerset, wtW D p K * ind X K * condSumW D p (revealedAt D A o) F K := by
  rw [← Pr2W_hybrid_eq_sum_condSumW]
  exact PrW_mul_PrW_le_Pr2W_hybrid D A o hp0 hp1 hX hF

end Explore

end Percolation.Continuity

end
