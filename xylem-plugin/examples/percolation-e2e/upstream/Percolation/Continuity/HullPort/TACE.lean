import Percolation.Continuity.HullPort.TAPv
import Percolation.Continuity.LowerTail.MarkerDominancePv
import Percolation.Literature.ClusterConditionalCovariance
import Percolation.Util.Linter

/-!
# Marker dominance with an avoided set: the input (CE) and SL(3,1) unconditionally

The last input of the marker-dominance chain, (CE) "cluster-conditional Harris"
`E[1_U(C_s)] · μ(F) ≤ E[1_U(C_s) · E[1_F | C_v]]`, `F = {s↔y} ∪ {y↔v}`, is Gladkov's decision-tree Harris inequality
(`MarkerDominancePv.sum_condSumW_ge`, from `TargetExploration.PrW_mul_PrW_le_Pr2W_hybrid`) for the
exploration of the cluster of `v` with no targets and all pairs available.  This file identifies that exploration
(`revealedAt univ ∅ v`; reached set / revealed set / cluster of `v` of the splice from
`Percolation.Literature.ClusterConditionalCovariance`): the revealed set contains the closed edge boundary, so off
the cluster of `v` the splice `K →_S K₂` connects like `K₂ − cut_v(K)`; hence `condSum_S(F)(K)` is the explicit kernel `F̂` of `HullPort.PvI_of_CE`, and the finitary sums
`PrW / wtW` over `Finset`-configurations are the `weight`-sums over `Set`-configurations.
[cite: Gladkov2024, Thm. 3.2 (p. 4) — corollary; VandenbergHaggstromKahn2005, Thm. 1.3 (p. 6) — corollary]
-/

noncomputable section

namespace Percolation.Continuity

open MeasureTheory Set Percolation.Literature.LatticeModels Percolation.Literature
open scoped Classical

variable {V : Type*}

namespace HullPort

open LonePortSum LonePortSumGeneral BHK2006 DecisionTree KNPreFKG TargetExploration

section CE

variable [Fintype V]

/-- **`Finset`- vs `Set`-configurations**: `Σ_{K ⊆ univ} wtW(K) φ(↑K) = Σ_ω weight(ω) φ(ω)`. [folklore] -/
theorem sum_powerset_wtW_eq_sum_weight {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℝ) (φ : Set ι → ℝ) :
    ∑ K ∈ (Finset.univ : Finset ι).powerset, wtW Finset.univ p K * φ ↑K = ∑ ω : Set ι, weight p ω * φ ω := by
  refine Finset.sum_nbij' (fun K => (↑K : Set ι)) (fun ω => Finset.univ.filter fun i => i ∈ ω)
    (fun K _ => Finset.mem_univ _) (fun ω _ => Finset.mem_powerset.2 (Finset.subset_univ _))
    (fun K _ => ?_) (fun ω _ => ?_) (fun K _ => ?_)
  · ext i; simp
  · ext i; simp
  · unfold wtW weight
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases hi : i ∈ K
    · rw [if_pos hi, if_pos (Finset.mem_coe.2 hi)]
    · rw [if_neg hi, if_neg fun h => hi (Finset.mem_coe.1 h)]

/-- Revealed pairs touch the cluster of `v`: `S(K) ⊆ cut_v(K)`. [cite: Gladkov2024, §6.2 — corollary] -/
theorem revealedAt_subset_cut (v : V) (K : Finset (Sym2 V)) {e : Sym2 V}
    (he : e ∈ revealedAt (Finset.univ : Finset (Sym2 V)) (∅ : Finset V) v K) : e ∈ cut {v} (↑K : Set (Sym2 V)) := by
  obtain ⟨u, hue, hr⟩ := ClusterConditioning.exists_reachable_of_mem_revealedAt he
  exact ⟨u, hue, v, rfl, hr⟩

/-- Off the cluster of `v`, the splice `K →_{S(K)} K₂` connects like `K₂ − cut_v(K)`: for `v ↮ s` in `K`,
`s ↔ t` in the splice iff `s ↔ t` in `K₂ ∖ cut_v(K)`. [cite: Gladkov2024, Lemma 3.1 — corollary] -/
theorem reachable_splice_iff_sdiff {v s : V} (K K₂ : Finset (Sym2 V))
    (hvs : ¬ (openGraph (↑K : Set (Sym2 V))).Reachable v s) (t : V) :
    (openGraph (↑(splice (revealedAt (Finset.univ : Finset (Sym2 V)) (∅ : Finset V) v K) K K₂) : Set (Sym2 V))).Reachable
        s t ↔ (openGraph ((↑K₂ : Set (Sym2 V)) \ cut {v} (↑K : Set (Sym2 V)))).Reachable s t := by
  have hvs₂ : ¬ (openGraph (↑(splice (revealedAt (Finset.univ : Finset (Sym2 V)) (∅ : Finset V) v K) K K₂) :
      Set (Sym2 V))).Reachable v s := fun h => hvs ((ClusterConditioning.reachable_hybrid_iff v K K₂ s).1 h)
  have hcut : cut {v} (↑(splice (revealedAt (Finset.univ : Finset (Sym2 V)) (∅ : Finset V) v K) K K₂) : Set (Sym2 V)) =
      cut {v} (↑K : Set (Sym2 V)) := by
    ext e
    simp only [cut, Set.mem_setOf_eq, Set.mem_singleton_iff, exists_eq_left, ClusterConditioning.reachable_hybrid_iff]
  have hsd : (↑(splice (revealedAt (Finset.univ : Finset (Sym2 V)) (∅ : Finset V) v K) K K₂) : Set (Sym2 V)) \
        cut {v} (↑(splice (revealedAt (Finset.univ : Finset (Sym2 V)) (∅ : Finset V) v K) K K₂) : Set (Sym2 V)) =
      (↑K₂ : Set (Sym2 V)) \ cut {v} (↑K : Set (Sym2 V)) := by
    rw [hcut]
    ext e
    constructor
    · rintro ⟨he, hc⟩
      exact ⟨Finset.mem_coe.2 ((mem_splice_of_not_mem fun hS => hc (revealedAt_subset_cut v K hS)).1
        (Finset.mem_coe.1 he)), hc⟩
    · rintro ⟨he, hc⟩
      exact ⟨Finset.mem_coe.2 ((mem_splice_of_not_mem fun hS => hc (revealedAt_subset_cut v K hS)).2
        (Finset.mem_coe.1 he)), hc⟩
  rw [← reachable_sdiff_cut_singleton_iff hvs₂ t, hsd]

/-- **The conditional sum of `F = {s↔y} ∪ {y↔v}` given the exploration of `C_v`** is the kernel `F̂`:
`1` if `v↔y`, `0` if `v↮y, v↔s`, and `μ_{K₂}(s↔y in K₂ − cut_v(K))` otherwise.
[cite: Gladkov2024, proof of Thm. 5.2 ((9)) — corollary] -/
theorem condSumW_explore_eq (p : Sym2 V → ℝ) (s y v : V) (K : Finset (Sym2 V)) :
    condSumW Finset.univ p (revealedAt (Finset.univ : Finset (Sym2 V)) (∅ : Finset V) v)
        {T : Finset (Sym2 V) | (openGraph (↑T : Set (Sym2 V))).Reachable s y ∨
          (openGraph (↑T : Set (Sym2 V))).Reachable y v} K =
      if (openGraph (↑K : Set (Sym2 V))).Reachable v y then 1
      else if (openGraph (↑K : Set (Sym2 V))).Reachable v s then 0
      else delE p (cut {v} (↑K : Set (Sym2 V))) (ind (openConn s y : Set (BondConfig V))) := by
  unfold condSumW
  by_cases hvy : (openGraph (↑K : Set (Sym2 V))).Reachable v y
  · rw [if_pos hvy]
    refine Eq.trans (Finset.sum_congr rfl fun K₂ _ => ?_) (sum_wtW Finset.univ p)
    rw [ind_of_mem (show splice (revealedAt Finset.univ ∅ v K) K K₂ ∈ {T : Finset (Sym2 V) |
        (openGraph (↑T : Set (Sym2 V))).Reachable s y ∨ (openGraph (↑T : Set (Sym2 V))).Reachable y v} from
      Or.inr ((ClusterConditioning.reachable_hybrid_iff v K K₂ y).2 hvy).symm), mul_one]
  rw [if_neg hvy]
  by_cases hvs : (openGraph (↑K : Set (Sym2 V))).Reachable v s
  · rw [if_pos hvs]
    refine Finset.sum_eq_zero fun K₂ _ => ?_
    rw [ind_of_not_mem (show splice (revealedAt Finset.univ ∅ v K) K K₂ ∉ {T : Finset (Sym2 V) |
        (openGraph (↑T : Set (Sym2 V))).Reachable s y ∨ (openGraph (↑T : Set (Sym2 V))).Reachable y v} from
      fun h => h.elim
        (fun h => hvy ((ClusterConditioning.reachable_hybrid_iff v K K₂ y).1
          (((ClusterConditioning.reachable_hybrid_iff v K K₂ s).2 hvs).trans h)))
        (fun h => hvy ((ClusterConditioning.reachable_hybrid_iff v K K₂ y).1 h.symm))), mul_zero]
  rw [if_neg hvs, delE, ← sum_powerset_wtW_eq_sum_weight p
    (fun η => ind (openConn s y : Set (BondConfig V)) (η \ cut {v} (↑K : Set (Sym2 V))))]
  refine Finset.sum_congr rfl fun K₂ _ => ?_
  congr 1
  have key : splice (revealedAt Finset.univ ∅ v K) K K₂ ∈ {T : Finset (Sym2 V) |
      (openGraph (↑T : Set (Sym2 V))).Reachable s y ∨ (openGraph (↑T : Set (Sym2 V))).Reachable y v} ↔
      (↑K₂ : Set (Sym2 V)) \ cut {v} (↑K : Set (Sym2 V)) ∈ (openConn s y : Set (BondConfig V)) := by
    constructor
    · intro h
      rcases h with h | h
      · exact (reachable_splice_iff_sdiff K K₂ hvs y).1 h
      · exact absurd ((ClusterConditioning.reachable_hybrid_iff v K K₂ y).1 h.symm) hvy
    · intro h
      exact Or.inl ((reachable_splice_iff_sdiff K K₂ hvs y).2 h)
  by_cases h : splice (revealedAt Finset.univ ∅ v K) K K₂ ∈ {T : Finset (Sym2 V) |
      (openGraph (↑T : Set (Sym2 V))).Reachable s y ∨ (openGraph (↑T : Set (Sym2 V))).Reachable y v}
  · rw [ind_of_mem h, ind_of_mem (key.1 h)]
  · rw [ind_of_not_mem h, ind_of_not_mem fun hh => h (key.2 hh)]

/-- **(CE) — cluster-conditional Harris for `1_U(C_s)` and `F = {s↔y} ∪ {y↔v}`** (Gladkov's decision-tree Harris
inequality for the exploration of `C_v`), in the `weight`-sum shape consumed by `HullPort.PvI_of_CE`.
[cite: Gladkov2024, Thm. 3.2 (p. 4) — corollary] -/
theorem CE_holds (s y : V) (U : Set (Set (Sym2 V))) (hU : IsUpperSet U) (q : Sym2 V → unitInterval) (v : V) :
    (∑ ω, weight (fun e => (q e : ℝ)) ω * ind U (openEdgeCluster ω s)) *
        (∑ ω, weight (fun e => (q e : ℝ)) ω * ind (openConn s y ∪ openConn y v : Set (BondConfig V)) ω) ≤
      ∑ ω, weight (fun e => (q e : ℝ)) ω * (ind U (openEdgeCluster ω s) *
        (if (openGraph ω).Reachable v y then 1 else if (openGraph ω).Reachable v s then 0 else
          delE (fun e => (q e : ℝ)) (cut {v} ω) (ind (openConn s y : Set (BondConfig V))))) := by
  set p : Sym2 V → ℝ := fun e => (q e : ℝ) with hp
  have hp0 : ∀ e, 0 ≤ p e := fun e => (q e).2.1
  have hp1 : ∀ e, p e ≤ 1 := fun e => (q e).2.2
  set X' : Set (Finset (Sym2 V)) := {S | openEdgeCluster (↑S : Set (Sym2 V)) s ∈ U} with hX'
  set F' : Set (Finset (Sym2 V)) := {T | (openGraph (↑T : Set (Sym2 V))).Reachable s y ∨
    (openGraph (↑T : Set (Sym2 V))).Reachable y v} with hF'
  have hXup : IsUpperSet X' := fun S T hST hS =>
    hU (openEdgeCluster_mono (Finset.coe_subset.2 hST) s) hS
  have hFup : IsUpperSet F' := fun S T hST hS =>
    hS.elim (fun h => Or.inl (h.mono (openGraph_le (Finset.coe_subset.2 hST))))
      (fun h => Or.inr (h.mono (openGraph_le (Finset.coe_subset.2 hST))))
  have key := MarkerDominancePv.sum_condSumW_ge (Finset.univ : Finset (Sym2 V)) (∅ : Finset V) v hp0 hp1 hXup hFup
  -- the three translations
  have hindX : ∀ S : Finset (Sym2 V), ind X' S = ind U (openEdgeCluster (↑S : Set (Sym2 V)) s) := by
    intro S
    by_cases h : openEdgeCluster (↑S : Set (Sym2 V)) s ∈ U
    · rw [ind_of_mem h, ind_of_mem (show S ∈ X' from h)]
    · rw [ind_of_not_mem h, ind_of_not_mem (show S ∉ X' from h)]
  have hindF : ∀ S : Finset (Sym2 V), ind F' S = ind (openConn s y ∪ openConn y v : Set (BondConfig V)) ↑S := by
    intro S
    by_cases h : S ∈ F'
    · rw [ind_of_mem h, ind_of_mem (show (↑S : Set (Sym2 V)) ∈ (openConn s y ∪ openConn y v : Set (BondConfig V))
        from h.elim (fun h => Or.inl h) (fun h => Or.inr h))]
    · rw [ind_of_not_mem h, ind_of_not_mem (show (↑S : Set (Sym2 V)) ∉ (openConn s y ∪ openConn y v :
        Set (BondConfig V)) from fun hh => h (hh.elim (fun h => Or.inl h) (fun h => Or.inr h)))]
  have e1 : PrW Finset.univ p X' = ∑ ω, weight p ω * ind U (openEdgeCluster ω s) := by
    rw [PrW_eq_sum_ind, ← sum_powerset_wtW_eq_sum_weight p (fun ω => ind U (openEdgeCluster ω s))]
    exact Finset.sum_congr rfl fun S _ => by rw [hindX]
  have e2 : PrW Finset.univ p F' = ∑ ω, weight p ω * ind (openConn s y ∪ openConn y v : Set (BondConfig V)) ω := by
    rw [PrW_eq_sum_ind, ← sum_powerset_wtW_eq_sum_weight p
      (fun ω => ind (openConn s y ∪ openConn y v : Set (BondConfig V)) ω)]
    exact Finset.sum_congr rfl fun S _ => by rw [hindF]
  have e3 : ∑ K ∈ (Finset.univ : Finset (Sym2 V)).powerset, wtW Finset.univ p K * ind X' K *
      condSumW Finset.univ p (revealedAt Finset.univ ∅ v) F' K =
      ∑ ω, weight p ω * (ind U (openEdgeCluster ω s) *
        (if (openGraph ω).Reachable v y then 1 else if (openGraph ω).Reachable v s then 0 else
          delE p (cut {v} ω) (ind (openConn s y : Set (BondConfig V))))) := by
    rw [← sum_powerset_wtW_eq_sum_weight p (fun ω => ind U (openEdgeCluster ω s) *
      (if (openGraph ω).Reachable v y then 1 else if (openGraph ω).Reachable v s then 0 else
        delE p (cut {v} ω) (ind (openConn s y : Set (BondConfig V)))))]
    refine Finset.sum_congr rfl fun K _ => ?_
    rw [hindX, hF', condSumW_explore_eq p s y v K, mul_assoc]
  rw [e1, e2, e3] at key
  exact key

end CE

end HullPort

end Percolation.Continuity
