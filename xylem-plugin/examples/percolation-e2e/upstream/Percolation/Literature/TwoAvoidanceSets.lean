import Percolation.Literature.ConditionalPositiveAssociationProofs
import Percolation.Literature.TwoClusterConditionalAssociation
import Percolation.Util.Linter

/-!
# van den Berg–Häggström–Kahn 2006, Theorem 1.1 (two avoidance sets), event form

Bond percolation with arbitrary edge probabilities on a finite vertex type `V` (`μ = prodBernoulli
w`), a vertex `s`, the cluster events `{s ↔ O} := {s ↔ v ∀ v ∈ O}` (increasing, determined by the
open cluster of `s`) and `R_X := {s ↮ X} := {s ↮ x ∀ x ∈ X}`. [VandenbergHaggstromKahn2005, Thm. 1.1
(p. 3, eq. (3))]: "Let `A` and `B` be increasing events determined by the open cluster of `s`. Then
for all `X, Y ⊆ V ∖ {s}`, `Pr(A R_X) Pr(B R_Y) ≤ Pr(A B R_{X∩Y}) Pr(R_{X∪Y})`." The functional form
restricted to a vertex set is proved in `ConditionalPositiveAssociationProofs.lean` (`BHK2006.core`,
from which Thm. 1.3 was derived); this file records the event form for the conjunction events `A =
{s ↔ O₁}`, `B = {s ↔ O₂}` (`BHK2006_twoAvoidanceSets`; `s ∈ X` or `s ∈ Y` is allowed, both sides
then vanish or the statement degenerates harmlessly) and its corollary for the law of the CAPTURED
SET `C(s) ∩ A` of a relay set `A`:

  `P(C∩A = S₁) · P(C∩A = S₂) ≤ P(C∩A = S₁ ∪ S₂) · P(C∩A ⊆ S₁ ∩ S₂)`                          (★)

(`O₁ = S₁, X = A∖S₁`, …): two popular candidate values of the captured set force mass on their union unless a
common sub-value (or `∅`) is popular.  No definition is introduced.

## References
* J. van den Berg, O. Häggström, J. Kahn, *Some conditional correlation inequalities for percolation and related
  processes*, Random Structures Algorithms 29 (2006) 417–435, Thm. 1.1 (pp. 3–5). [VandenbergHaggstromKahn2005]
-/

noncomputable section

open MeasureTheory Set
open Percolation.Literature.LatticeModels (prodBernoulli)

namespace Percolation.Literature

open scoped Classical
open BHK2006 DecisionTree

variable {V : Type*} [Fintype V]

namespace TwoAvoidanceSets

/-- `μ(E) = Σ_ω weight(ω) 1_E(ω)` on the finite configuration space. [folklore] -/
theorem real_eq_sum_ind (w : Sym2 V → unitInterval) (E : Set (Set (Sym2 V))) :
    (prodBernoulli w).real E = ∑ ω, weight (fun e => (w e : ℝ)) ω * ind E ω := by
  rw [← integral_indicator_one MeasurableSet.of_discrete, integral_prodBernoulli_eq_sum]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases hω : ω ∈ E
  · rw [Set.indicator_of_mem hω, ind_of_mem hω, Pi.one_apply]
  · rw [Set.indicator_of_notMem hω, ind_of_not_mem hω, mul_zero]

/-- The increasing function `F_O(W) = 1{every v ∈ O is s or lies on an edge of W}` is monotone. [folklore] -/
theorem monotone_FO (s : V) (O : Finset V) :
    Monotone fun W : Set (Sym2 V) => (if ∀ v ∈ O, v = s ∨ ∃ e ∈ W, v ∈ e then (1 : ℝ) else 0) := by
  intro W W' h
  simp only
  by_cases hW : ∀ v ∈ O, v = s ∨ ∃ e ∈ W, v ∈ e
  · rw [if_pos hW, if_pos (fun v hv => (hW v hv).imp id fun ⟨e, he, hve⟩ => ⟨e, h he, hve⟩)]
  · rw [if_neg hW]; split_ifs <;> norm_num

/-- `F_O(C_s ω) = 1{s ↔ O}(ω)`. [folklore] -/
theorem FO_openEdgeCluster (s : V) (O : Finset V) (ω : BondConfig V) :
    (if ∀ v ∈ O, v = s ∨ ∃ e ∈ openEdgeCluster ω s, v ∈ e then (1 : ℝ) else 0) =
      ind {ω' : BondConfig V | ∀ v ∈ O, ω' ∈ openConn s v} ω := by
  have key : (∀ v ∈ O, v = s ∨ ∃ e ∈ openEdgeCluster ω s, v ∈ e) ↔
      ω ∈ {ω' : BondConfig V | ∀ v ∈ O, ω' ∈ openConn s v} := by
    refine forall₂_congr fun v _ => ?_
    rw [← reachable_iff_exists_mem_openEdgeCluster ω s v]
    rfl
  by_cases h : ∀ v ∈ O, v = s ∨ ∃ e ∈ openEdgeCluster ω s, v ∈ e
  · rw [if_pos h, ind_of_mem (key.1 h)]
  · rw [if_neg h, ind_of_not_mem (fun h' => h (key.2 h'))]

/-- `1_E · 1_D = 1_{E ∩ D}`. [folklore] -/
theorem ind_mul_ind {α : Type*} (E D : Set α) (a : α) : ind E a * ind D a = ind (E ∩ D) a := by
  by_cases hE : a ∈ E <;> by_cases hD : a ∈ D <;>
    simp [ind_of_mem, ind_of_not_mem, hE, hD, Set.mem_inter_iff]

end TwoAvoidanceSets

open TwoAvoidanceSets in
/-- **van den Berg–Häggström–Kahn 2006, Theorem 1.1, event form** (for the conjunction events `{s ↔ O}`):
`μ({s↔O₁} ∩ {s↮X}) · μ({s↔O₂} ∩ {s↮Y}) ≤ μ({s↔O₁∪O₂} ∩ {s↮X∩Y}) · μ({s↮X∪Y})`, proved via
`BHK2006.core`. [cite: VandenbergHaggstromKahn2005, Thm. 1.1 (p. 3) eq. (3)] -/
theorem BHK2006_twoAvoidanceSets (w : Sym2 V → unitInterval) (s : V) (O₁ O₂ : Finset V) (X Y : Set V) :
    (prodBernoulli w).real ({ω | ∀ v ∈ O₁, ω ∈ openConn s v} ∩ {ω | ∀ x ∈ X, ω ∉ openConn s x}) *
        (prodBernoulli w).real ({ω | ∀ v ∈ O₂, ω ∈ openConn s v} ∩ {ω | ∀ y ∈ Y, ω ∉ openConn s y}) ≤
      (prodBernoulli w).real ({ω | ∀ v ∈ O₁ ∪ O₂, ω ∈ openConn s v} ∩
          {ω | ∀ x ∈ X ∩ Y, ω ∉ openConn s x}) *
        (prodBernoulli w).real {ω | ∀ x ∈ X ∪ Y, ω ∉ openConn s x} := by
  set w' : Sym2 V → ℝ := fun e => (w e : ℝ) with hw'
  have hw0 : ∀ e, 0 ≤ w' e := fun e => (w e).2.1
  have hw1 : ∀ e, w' e ≤ 1 := fun e => (w e).2.2
  have hm : ∑ ω, weight w' ω = 1 := by
    have h1 := integral_prodBernoulli_eq_sum w fun _ => (1 : ℝ)
    simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at h1
    exact h1.symm
  -- `U = univ`: restricted cluster / avoidance events are the original ones
  have hE : ∀ ω : Set (Sym2 V), ω ∩ edgesIn (Finset.univ : Finset V) = ω := fun ω => by
    ext e
    simp only [Set.mem_inter_iff, edgesIn, Set.mem_setOf_eq, Finset.mem_univ, imp_true_iff, and_true]
  have hC : ∀ ω, rC Finset.univ s ω = openEdgeCluster ω s := fun ω => by simp only [rC, hE]
  have hDD : ∀ Z : Set V, rD Finset.univ s Z = {ω : BondConfig V | ∀ x ∈ Z, ω ∉ openConn s x} := by
    intro Z; ext ω; simp only [rD, hE, Set.mem_setOf_eq]; rfl
  have hXU : X ⊆ ↑(Finset.univ : Finset V) := by simp
  have hYU : Y ⊆ ↑(Finset.univ : Finset V) := by simp
  have key := core w' hw0 hw1 hm Finset.univ s (Finset.mem_univ s) X Y hXU hYU
    (fun W => if ∀ v ∈ O₁, v = s ∨ ∃ e ∈ W, v ∈ e then (1 : ℝ) else 0)
    (fun W => if ∀ v ∈ O₂, v = s ∨ ∃ e ∈ W, v ∈ e then (1 : ℝ) else 0)
    (monotone_FO s O₁) (monotone_FO s O₂)
    (fun W => by split_ifs <;> norm_num) (fun W => by split_ifs <;> norm_num)
  simp only [hC, hDD, FO_openEdgeCluster, ind_mul_ind] at key
  -- identify the union event: `{s ↔ O₁} ∩ {s ↔ O₂} = {s ↔ O₁ ∪ O₂}`
  have hU : ({ω' : BondConfig V | ∀ v ∈ O₁, ω' ∈ openConn s v} ∩ {ω' | ∀ v ∈ O₂, ω' ∈ openConn s v}) =
      {ω' | ∀ v ∈ O₁ ∪ O₂, ω' ∈ openConn s v} := by
    ext ω'; simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Finset.mem_union]
    exact ⟨fun ⟨h1, h2⟩ v hv => hv.elim (h1 v) (h2 v),
      fun h => ⟨fun v hv => h v (Or.inl hv), fun v hv => h v (Or.inr hv)⟩⟩
  rw [hU] at key
  rw [real_eq_sum_ind, real_eq_sum_ind, real_eq_sum_ind, real_eq_sum_ind]
  have e4 : ∑ ω, weight (fun e => (w e : ℝ)) ω * ind {ω : BondConfig V | ∀ x ∈ X ∪ Y, ω ∉ openConn s x} ω =
      ∑ ω, weight w' ω * ind {ω : BondConfig V | ∀ x ∈ X ∪ Y, ω ∉ openConn s x} ω := rfl
  rw [e4]
  convert key using 2

end Percolation.Literature

end
