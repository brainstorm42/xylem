import Percolation.Continuity.CovTau.A2Anti
import Percolation.Continuity.CovTau.MetaA2
import Percolation.Util.Linter

/-!
# META-A2 and its diagonal modulo the ONE-SOURCE bounds only (the antitonicity of `Y_F` is derived)

Companion of `Continuity/CovTau/MetaA2.lean` (`CovTau.metaA2_of_star`).

`CovTau.metaA2_of_star` proves the generic two-source inequality (META-A2) `E_A(N)·Y_F(N') ≤ M_A(N ∪
N')·X_F(N ∩ N')` for an avoided SET `A` and an arbitrary nonnegative pure world functional `F` under
two hypotheses in every sub-world `U' ⊆ U`: the one-source bound (★^F) and the antitonicity of `N ↦
Y_F(N)`.
* `CovTau.Yw_insert_le` — `Y_F(N ∪ {u}) ≤ Y_F(N)` from the one-source bound `Y_F({u}) ≤ F` in every sub-world, by
  conditioning on the VALUE of the set cluster `C_N` (`CovTau.sum_cond_sC`, the domain Markov property): on `{u ∈ C_N}`
  both sides agree, on `{u ∉ C_N}` the inner sum is `Y_{U ∖ C_N}({u}) ≤ F(U ∖ C_N)`;
* `CovTau.Yw_antitone_of_le` — hence `Y_F` is antitone in the source set (induction on `N' ∖ N`);
Instance "A2^H" (`A = S ∋ x`, `F(U') = Cov_{G[U']}(g(C_x), 1{v ↔ S})`, both one-source bounds proved as
`CovTauStarN.yS_mul_mS_le` / `CovTauStarN.yS_le_bS`): `Continuity/CovTau/A2H.lean`.
[cite: VandenbergHaggstromKahn2005, Thm. 1.1 (pp. 3–5), §1 pp. 7–8] [cite: KozmaNitzan2024, Conj. 1 (p. 3)]
-/

noncomputable section

namespace Percolation.Continuity.CovTau

open Percolation.Literature
open Percolation.Literature.BHK2006
open Percolation.Literature.DecisionTree (ind ind_of_mem ind_of_not_mem ind_nonneg)
open scoped Classical

variable {V : Type*} [Fintype V]

/-- **Adding a source vertex decreases `Y_F`**: if `Y_F({u}) ≤ F` in every sub-world `U' ⊆ U`, then
`Y_F(N ∪ {u}) ≤ Y_F(N)` in `G[U]`.
[cite: VandenbergHaggstromKahn2005, §1 pp. 7–8] -/
theorem Yw_insert_le (w : Sym2 V → ℝ) (hw0 : ∀ e, 0 ≤ w e) (hw1 : ∀ e, w e ≤ 1)
    (hm : ∑ ω, weight w ω = 1) (x : V) (F : Finset V → ℝ) (U : Finset V)
    (hYB : ∀ U' ⊆ U, ∀ u : V, Yw w U' x F {u} ≤ F U') (N : Set V) (u : V) :
    Yw w U x F (insert u N) ≤ Yw w U x F N := by
  -- the integrand of `Y(N ∪ {u})` as a function of `(C_N, ω ∩ E(U ∖ C_N))`
  set Φ : Set V → Set (Sym2 V) → ℝ := fun W η =>
    ind {W : Set V | x ∉ W} W * (if u ∈ W then F (U.filter fun a => a ∉ W) else
      F (rest (U.filter fun a => a ∉ W) ({u} : Set V) η) *
        ind (rD (U.filter fun a => a ∉ W) x ({u} : Set V)) η) with hΦ
  have hxW : ∀ ω : Set (Sym2 V), ind {W : Set V | x ∉ W} (sC U N ω) = ind (rD U x N) ω := by
    intro ω
    by_cases h : x ∈ sC U N ω
    · rw [ind_of_not_mem (show sC U N ω ∉ {W : Set V | x ∉ W} from fun h' => h' h),
        ind_of_not_mem (fun h' => ((not_mem_sC_iff U N ω x).2 h') h)]
    · rw [ind_of_mem (show sC U N ω ∈ {W : Set V | x ∉ W} from h), ind_of_mem ((not_mem_sC_iff U N ω x).1 h)]
  have hint : ∀ ω : Set (Sym2 V), F (rest U (insert u N) ω) * ind (rD U x (insert u N)) ω =
      Φ (sC U N ω) (ω ∩ edgesIn (rest U N ω)) := by
    intro ω
    simp only [hΦ, hxW, ← rest_eq_filter, rest_inter_edgesIn]
    by_cases hu : u ∈ sC U N ω
    · rw [if_pos hu]
      have hC : sC U (insert u N) ω = sC U N ω := sC_insert_of_mem hu
      have hR : rest U (insert u N) ω = rest U N ω := by
        ext a; rw [mem_rest, mem_rest, hC]
      rw [hR]
      by_cases hx : ω ∈ rD U x N
      · have hx' : ω ∈ rD U x (insert u N) := by
          rw [← not_mem_sC_iff] at hx ⊢; rwa [hC]
        rw [ind_of_mem hx, ind_of_mem hx', mul_one, one_mul]
      · have hx' : ω ∉ rD U x (insert u N) := fun h => hx (rD_antitone (Set.subset_insert u N) h)
        rw [ind_of_not_mem hx, ind_of_not_mem hx', mul_zero, zero_mul]
    · rw [if_neg hu, rest_insert_of_not_mem hu]
      by_cases hx : ω ∈ rD U x N
      · rw [ind_of_mem hx, one_mul]
        have hxC : x ∉ sC U N ω := (not_mem_sC_iff U N ω x).2 hx
        have hiff : ω ∈ rD U x (insert u N) ↔ ω ∩ edgesIn (rest U N ω) ∈ rD (rest U N ω) x ({u} : Set V) := by
          rw [mem_rD_inter_edgesIn]
          simp only [rD, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq,
            reach_rest_iff hxC]
          exact ⟨fun h => h.1, fun h => ⟨h, hx⟩⟩
        by_cases hx' : ω ∈ rD U x (insert u N)
        · rw [ind_of_mem hx', ind_of_mem (hiff.1 hx')]
        · rw [ind_of_not_mem hx', ind_of_not_mem fun h => hx' (hiff.2 h)]
      · have hx' : ω ∉ rD U x (insert u N) := fun h => hx (rD_antitone (Set.subset_insert u N) h)
        rw [ind_of_not_mem hx, ind_of_not_mem hx', mul_zero, zero_mul]
  -- condition on `C_N`; inside, the `u ∉ W` branch is `Y_{U∖W}({u}) ≤ F(U∖W)`
  have hdec := sum_cond_sC w hm U N Φ
  unfold Yw
  simp_rw [hint]
  rw [hdec]
  refine Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left ?_ (weight_nonneg hw0 hw1 ω)
  simp only [hΦ, ← rest_eq_filter]
  by_cases hu : u ∈ sC U N ω
  · simp only [if_pos hu]
    rw [← Finset.sum_mul, hm, one_mul, hxW]
    exact (mul_comm _ _).le
  · simp only [if_neg hu, hxW]
    have hsum : ∑ ω', weight w ω' * (ind (rD U x N) ω *
        (F (rest (rest U N ω) ({u} : Set V) (ω' ∩ edgesIn (rest U N ω))) *
          ind (rD (rest U N ω) x ({u} : Set V)) (ω' ∩ edgesIn (rest U N ω)))) =
        ind (rD U x N) ω * Yw w (rest U N ω) x F {u} := by
      unfold Yw
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun ω' _ => ?_
      rw [rest_inter_edgesIn]
      have : ind (rD (rest U N ω) x ({u} : Set V)) (ω' ∩ edgesIn (rest U N ω)) =
          ind (rD (rest U N ω) x ({u} : Set V)) ω' := by
        by_cases h : ω' ∈ rD (rest U N ω) x ({u} : Set V)
        · rw [ind_of_mem h, ind_of_mem ((mem_rD_inter_edgesIn _ _ _ _).2 h)]
        · rw [ind_of_not_mem h, ind_of_not_mem fun h' => h ((mem_rD_inter_edgesIn _ _ _ _).1 h')]
      rw [this]; ring
    rw [hsum, mul_comm (F (rest U N ω))]
    exact mul_le_mul_of_nonneg_left (hYB _ (rest_subset U N ω) u) (ind_nonneg _ _)

/-- **`Y_F` is antitone in the source set** given the one-source bound `Y_F({u}) ≤ F` in every sub-world.
[cite: VandenbergHaggstromKahn2005, §1 pp. 7–8] -/
theorem Yw_antitone_of_le (w : Sym2 V → ℝ) (hw0 : ∀ e, 0 ≤ w e) (hw1 : ∀ e, w e ≤ 1)
    (hm : ∑ ω, weight w ω = 1) (x : V) (F : Finset V → ℝ) (U : Finset V)
    (hYB : ∀ U' ⊆ U, ∀ u : V, Yw w U' x F {u} ≤ F U') {N N' : Set V} (hNN' : N ⊆ N')
    (hN'U : N' ⊆ ↑U) : Yw w U x F N' ≤ Yw w U x F N := by
  -- induction on the finite set `N' ∖ N`
  set D : Finset V := U.filter fun u => u ∈ N' ∧ u ∉ N with hD
  have hN' : N' = N ∪ ↑D := by
    ext u
    simp only [hD, Set.mem_union, Finset.coe_filter, Set.mem_setOf_eq]
    constructor
    · intro hu; by_cases huN : u ∈ N; exacts [Or.inl huN, Or.inr ⟨hN'U hu, hu, huN⟩]
    · rintro (hu | ⟨-, hu, -⟩); exacts [hNN' hu, hu]
  rw [hN']
  clear_value D
  clear hN' hD
  induction D using Finset.induction_on with
  | empty => simp
  | @insert u D _ ih =>
    rw [Finset.coe_insert, Set.union_insert]
    exact (Yw_insert_le w hw0 hw1 hm x F U hYB _ u).trans ih

/-- **META-A2 modulo the one-source bounds** (★^F) `Y_F(N)·M_A(∅) ≤ M_A(N)·F` and `Y_F({u}) ≤ F` in every sub-world
`U' ⊆ U`: for all `N, N' ⊆ U`, `E_A(N)·Y_F(N') ≤ M_A(N ∪ N')·X_F(N ∩ N')`.
[cite: VandenbergHaggstromKahn2005, Thm. 1.1 (pp. 3–5), Thm. 1.3 (p. 6)] -/
theorem metaA2 (w : Sym2 V → ℝ) (hw0 : ∀ e, 0 ≤ w e) (hw1 : ∀ e, w e ≤ 1)
    (hm : ∑ ω, weight w ω = 1) (x o v : V) (A : Set V) {F : Finset V → ℝ}
    (hF0 : ∀ U' : Finset V, 0 ≤ F U') (hFv : ∀ U' : Finset V, v ∉ U' → F U' = 0) (U : Finset V)
    (hstar : ∀ U' ⊆ U, ∀ N : Set V, N ⊆ ↑U' →
      Yw w U' x F N * Mav w U' A v ∅ ≤ Mav w U' A v N * F U')
    (hYB : ∀ U' ⊆ U, ∀ u : V, Yw w U' x F {u} ≤ F U') {N N' : Set V} (hNU : N ⊆ ↑U)
    (hN'U : N' ⊆ ↑U) :
    Eav w U A o v N * Yw w U x F N' ≤ Mav w U A v (N ∪ N') * Xw w U x A o v F (N ∩ N') :=
  metaA2_of_star w hw0 hw1 hm x o v A hF0 hFv U hstar
    (fun U' hU' _ _ hNN' hN'U' => Yw_antitone_of_le w hw0 hw1 hm x F U'
      (fun U'' hU'' => hYB U'' (hU''.trans hU')) hNN' hN'U') N N' hNU hN'U

end Percolation.Continuity.CovTau
