import Percolation.Continuity.CovTau.A2Push
import Percolation.Continuity.CovTau.A2Star
import Percolation.Util.Linter

/-!
# `Y` is antitone in the source set — (A2) and P1 ≥ 0 modulo the one-source bounds only

Continues.

* `CovTau.sum_cond_sC` — **conditioning on the value of a set cluster** (the domain Markov property in the
  finite-sum framework, cf. `BHK2006.sum_cond_cluster` for one vertex): for any `Φ`,
  `Σ_ω weight(ω) Φ(C_N(ω), ω ∩ E(U ∖ C_N(ω))) = Σ_ω weight(ω) Σ_ω' weight(ω') Φ(C_N(ω), ω' ∩ E(U ∖ C_N(ω)))`
  — given `C_N = W`, the edges inside `U ∖ W` are fresh. [cite: VandenbergHaggstromKahn2005, §1 pp. 7–8, display (10)]
[cite: VandenbergHaggstromKahn2005, Thm. 1.1 (pp. 3–5), §1 pp. 7–8] [cite: Gladkov2024, Thm. 3.2] [cite: KozmaNitzan2024, Conj. 1 (p. 3)]
-/

noncomputable section

namespace Percolation.Continuity.CovTau

open Percolation.Literature
open Percolation.Literature.BHK2006
open Percolation.Literature.DecisionTree (ind ind_of_mem ind_of_not_mem ind_nonneg)
open scoped Classical

variable {V : Type*}

/-! ### Locality of the value of a set cluster -/

/-- An open path inside `U` starting in a set `W` that is closed under open `U`-edges of `ω` stays in `W`. [folklore] -/
theorem reach_stays {U : Finset V} {ω : Set (Sym2 V)} {W : Set V} {a b : V}
    (hW : ∀ p q : V, p ∈ W → (openGraph (ω ∩ edgesIn U)).Adj p q → q ∈ W)
    (h : (openGraph (ω ∩ edgesIn U)).Reachable a b) (ha : a ∈ W) : b ∈ W := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact ha
  | tail _ hbc ih => exact hW _ _ ih hbc

/-- **Locality of `{C_N = W}`**: if `C^U_N(ω) = W` and `ω'` agrees with `ω` on the pairs meeting `W`, then
`C^U_N(ω') = W`. [folklore] -/
theorem sC_eq_of_agree {U : Finset V} {N : Set V} {ω ω' : Set (Sym2 V)} {W : Set V} (hW : sC U N ω = W)
    (hag : ∀ e : Sym2 V, (∃ u ∈ e, u ∈ W) → (e ∈ ω ↔ e ∈ ω')) : sC U N ω' = W := by
  -- `W` is closed under open `U`-edges of `ω'` and of `ω`
  have hcl : ∀ (ξ : Set (Sym2 V)), (∀ e : Sym2 V, (∃ u ∈ e, u ∈ W) → (e ∈ ξ ↔ e ∈ ω)) →
      ∀ p q : V, p ∈ W → (openGraph (ξ ∩ edgesIn U)).Adj p q → q ∈ W := by
    intro ξ hξ p q hp hpq
    obtain ⟨hξe, hU, hne⟩ := adj_iff.1 hpq
    have hωe : s(p, q) ∈ ω := (hξ _ ⟨p, Sym2.mem_mk_left p q, hp⟩).1 hξe
    rw [← hW] at hp ⊢
    obtain ⟨z, hz, hr⟩ := hp
    exact ⟨z, hz, hr.trans (SimpleGraph.Adj.reachable (adj_iff.2 ⟨hωe, hU, hne⟩))⟩
  have hcl' := hcl ω' fun e he => (hag e he).symm
  have hclω := hcl ω fun _ _ => Iff.rfl
  have hNW : N ⊆ W := by rw [← hW]; exact subset_sC U N ω
  ext u
  constructor
  · rintro ⟨z, hz, hr⟩
    exact reach_stays hcl' hr (hNW hz)
  · intro hu
    rw [← hW] at hu
    obtain ⟨z, hz, hr⟩ := hu
    refine ⟨z, hz, ?_⟩
    -- the `ω`-path from `z` stays in `W`, so its edges meet `W` and are open in `ω'`
    rw [SimpleGraph.reachable_iff_reflTransGen] at hr ⊢
    induction hr with
    | refl => exact Relation.ReflTransGen.refl
    | @tail b c hab hbc ih =>
      refine ih.tail ?_
      obtain ⟨hωe, hU, hne⟩ := adj_iff.1 hbc
      have hb : b ∈ W := reach_stays hclω ((SimpleGraph.reachable_iff_reflTransGen _ _).2 hab) (hNW hz)
      exact adj_iff.2 ⟨(hag _ ⟨b, Sym2.mem_mk_left b c, hb⟩).1 hωe, hU, hne⟩

/-- `{C_N = W}` is decided by the pairs meeting `W`. [folklore] -/
theorem sC_inter_meet_eq_iff (U : Finset V) (N : Set V) (ω : Set (Sym2 V)) (W : Set V) :
    sC U N (ω ∩ {e | ∃ u ∈ e, u ∈ W}) = W ↔ sC U N ω = W :=
  ⟨fun h => sC_eq_of_agree h fun _ he => ⟨fun h' => h'.1, fun h' => ⟨h', he⟩⟩,
    fun h => sC_eq_of_agree h fun _ he => ⟨fun h' => ⟨h', he⟩, fun h' => h'.1⟩⟩

/-- The pairs inside `U ∖ W` do not meet `W`. [folklore] -/
theorem diff_meet_inter_edgesIn (U : Finset V) (W : Set V) (ω : Set (Sym2 V)) :
    (ω \ {e | ∃ u ∈ e, u ∈ W}) ∩ edgesIn (U.filter fun u => u ∉ W) =
      ω ∩ edgesIn (U.filter fun u => u ∉ W) := by
  ext e
  constructor
  · rintro ⟨⟨hω, -⟩, hU⟩; exact ⟨hω, hU⟩
  · rintro ⟨hω, hU⟩
    exact ⟨⟨hω, fun ⟨u, hue, huW⟩ => (Finset.mem_filter.1 (hU u hue)).2 huW⟩, hU⟩

/-- `rest U N ω` is `U` filtered by `∉ C_N(ω)`. [folklore] -/
theorem rest_eq_filter (U : Finset V) (N : Set V) (ω : Set (Sym2 V)) :
    rest U N ω = U.filter fun u => u ∉ sC U N ω := rfl

variable [Fintype V]

/-- **Conditioning on the value of the set cluster** (domain Markov property): for every `Φ`,
`Σ_ω weight(ω) Φ(C_N(ω), ω ∩ E(U ∖ C_N(ω))) = Σ_ω weight(ω) Σ_ω' weight(ω') Φ(C_N(ω), ω' ∩ E(U ∖ C_N(ω)))`.
[cite: VandenbergHaggstromKahn2005, §1 pp. 7–8, display (10)] -/
theorem sum_cond_sC (w : Sym2 V → ℝ) (hm : ∑ ω, weight w ω = 1) (U : Finset V) (N : Set V)
    (Φ : Set V → Set (Sym2 V) → ℝ) :
    ∑ ω, weight w ω * Φ (sC U N ω) (ω ∩ edgesIn (rest U N ω)) =
      ∑ ω, weight w ω * ∑ ω', weight w ω' * Φ (sC U N ω) (ω' ∩ edgesIn (rest U N ω)) := by
  -- fibrewise over the value `W` of the cluster
  have key : ∀ W : Set V,
      ∑ ω, (if sC U N ω = W then weight w ω * Φ W (ω ∩ edgesIn (U.filter fun u => u ∉ W)) else 0) =
      ∑ ω, (if sC U N ω = W then
        weight w ω * ∑ ω', weight w ω' * Φ W (ω' ∩ edgesIn (U.filter fun u => u ∉ W)) else 0) := by
    intro W
    set A : Set (Sym2 V) := {e | ∃ u ∈ e, u ∈ W} with hA
    set Ψ : Set (Sym2 V) → Set (Sym2 V) → ℝ := fun ζ η =>
      if sC U N ζ = W then Φ W (η ∩ edgesIn (U.filter fun u => u ∉ W)) else 0 with hΨ
    have h1 : ∀ ω, (if sC U N ω = W then weight w ω * Φ W (ω ∩ edgesIn (U.filter fun u => u ∉ W)) else 0) =
        weight w ω * Ψ (ω ∩ A) (ω \ A) := by
      intro ω
      simp only [hΨ, hA, sC_inter_meet_eq_iff, diff_meet_inter_edgesIn]
      split_ifs <;> simp
    have h2 : ∀ ω ω', Ψ (ω ∩ A) (ω' \ A) =
        if sC U N ω = W then Φ W (ω' ∩ edgesIn (U.filter fun u => u ∉ W)) else 0 := by
      intro ω ω'
      simp only [hΨ, hA, sC_inter_meet_eq_iff, diff_meet_inter_edgesIn]
    calc ∑ ω, (if sC U N ω = W then weight w ω * Φ W (ω ∩ edgesIn (U.filter fun u => u ∉ W)) else 0)
        = (∑ ω, weight w ω) * ∑ ω, weight w ω * Ψ (ω ∩ A) (ω \ A) := by rw [hm, one_mul]; simp_rw [h1]
      _ = ∑ ω, weight w ω * ∑ ω', weight w ω' * Ψ (ω ∩ A) (ω' \ A) := blockFubini w A Ψ
      _ = _ := by
          refine Finset.sum_congr rfl fun ω _ => ?_
          by_cases hc : sC U N ω = W <;> simp [h2, hc]
  -- combine the fibres
  have lhs : ∑ ω, weight w ω * Φ (sC U N ω) (ω ∩ edgesIn (rest U N ω)) =
      ∑ ω, ∑ W : Set V, (if sC U N ω = W then
        weight w ω * Φ W (ω ∩ edgesIn (U.filter fun u => u ∉ W)) else 0) := by
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [Finset.sum_ite_eq Finset.univ (sC U N ω)]; simp [rest_eq_filter]
  have rhs : ∑ ω, weight w ω * ∑ ω', weight w ω' * Φ (sC U N ω) (ω' ∩ edgesIn (rest U N ω)) =
      ∑ ω, ∑ W : Set V, (if sC U N ω = W then
        weight w ω * ∑ ω', weight w ω' * Φ W (ω' ∩ edgesIn (U.filter fun u => u ∉ W)) else 0) := by
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [Finset.sum_ite_eq Finset.univ (sC U N ω)]; simp [rest_eq_filter]
  rw [lhs, rhs, Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun W _ => key W

/-! ### Adding one source vertex -/

omit [Fintype V] in
/-- Clusters computed from `ω ∩ E(U')` are the clusters of `G[U']`. [folklore] -/
theorem sC_inter_edgesIn (U' : Finset V) (M : Set V) (ω : Set (Sym2 V)) :
    sC U' M (ω ∩ edgesIn U') = sC U' M ω := by
  simp only [sC, Set.inter_assoc, Set.inter_self]

omit [Fintype V] in
/-- Worlds computed from `ω ∩ E(U')` are the worlds of `G[U']`. [folklore] -/
theorem rest_inter_edgesIn (U' : Finset V) (M : Set V) (ω : Set (Sym2 V)) :
    rest U' M (ω ∩ edgesIn U') = rest U' M ω := by
  ext u; rw [mem_rest, mem_rest, sC_inter_edgesIn]

omit [Fintype V] in
/-- Avoidance events computed from `ω ∩ E(U')`. [folklore] -/
theorem mem_rD_inter_edgesIn (U' : Finset V) (s : V) (M : Set V) (ω : Set (Sym2 V)) :
    ω ∩ edgesIn U' ∈ rD U' s M ↔ ω ∈ rD U' s M := by
  simp only [rD, Set.mem_setOf_eq, Set.inter_assoc, Set.inter_self]

omit [Fintype V] in
/-- If `u ∈ C_N` then `C_{N ∪ {u}} = C_N`. [folklore] -/
theorem sC_insert_of_mem {U : Finset V} {N : Set V} {ω : Set (Sym2 V)} {u : V} (hu : u ∈ sC U N ω) :
    sC U (insert u N) ω = sC U N ω := by
  refine Set.Subset.antisymm ?_ (sC_mono_set U (Set.subset_insert u N) ω)
  rintro a ⟨z, rfl | hz, hr⟩
  · obtain ⟨z', hz', hr'⟩ := hu
    exact ⟨z', hz', hr'.trans hr⟩
  · exact ⟨z, hz, hr⟩

omit [Fintype V] in
/-- A `U`-path avoiding the cluster `C_N` is a path of the world `U ∖ C_N`: if `a ∉ C_N(ω)` then
`a ↔ b` in `G[U]` iff `a ↔ b` in `G[U ∖ C_N(ω)]`. [folklore] -/
theorem reach_rest_iff {U : Finset V} {N : Set V} {ω : Set (Sym2 V)} {a b : V} (ha : a ∉ sC U N ω) :
    (openGraph (ω ∩ edgesIn (rest U N ω))).Reachable a b ↔ (openGraph (ω ∩ edgesIn U)).Reachable a b := by
  constructor
  · exact fun h => h.mono (openGraph_le (Set.inter_subset_inter_right _ (edgesIn_mono (rest_subset U N ω))))
  · intro h
    rw [SimpleGraph.reachable_iff_reflTransGen] at h ⊢
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | @tail b c hab hbc ih =>
      obtain ⟨hω, ⟨hbU, hcU⟩, hne⟩ := adj_iff.1 hbc
      -- `b ∉ C_N` (else `a ∈ C_N`), hence `c ∉ C_N`
      have hb : b ∉ sC U N ω := fun ⟨z, hz, hr⟩ =>
        ha ⟨z, hz, hr.trans ((SimpleGraph.reachable_iff_reflTransGen _ _).2 hab).symm⟩
      have hc : c ∉ sC U N ω := fun ⟨z, hz, hr⟩ =>
        hb ⟨z, hz, hr.trans (SimpleGraph.Adj.reachable (adj_iff.2 ⟨by rw [Sym2.eq_swap]; exact hω, ⟨hcU, hbU⟩, hne.symm⟩))⟩
      exact ih.tail (adj_iff.2 ⟨hω, ⟨mem_rest.2 ⟨hbU, hb⟩, mem_rest.2 ⟨hcU, hc⟩⟩, hne⟩)

omit [Fintype V] in
/-- If `u ∉ C_N` then `C_{N ∪ {u}} = C_N ∪ C^{U ∖ C_N}_u`. [folklore] -/
theorem sC_insert_of_not_mem {U : Finset V} {N : Set V} {ω : Set (Sym2 V)} {u : V} (hu : u ∉ sC U N ω) :
    sC U (insert u N) ω = sC U N ω ∪ sC (rest U N ω) ({u} : Set V) ω := by
  ext a
  simp only [Set.mem_union, mem_sC_singleton, reach_rest_iff hu]
  constructor
  · rintro ⟨z, rfl | hz, hr⟩
    · exact Or.inr hr
    · exact Or.inl ⟨z, hz, hr⟩
  · rintro (⟨z, hz, hr⟩ | hr)
    · exact ⟨z, Set.mem_insert_of_mem u hz, hr⟩
    · exact ⟨u, Set.mem_insert u N, hr⟩

omit [Fintype V] in
/-- If `u ∉ C_N` then `U ∖ C_{N ∪ {u}} = (U ∖ C_N) ∖ C^{U∖C_N}_u`. [folklore] -/
theorem rest_insert_of_not_mem {U : Finset V} {N : Set V} {ω : Set (Sym2 V)} {u : V} (hu : u ∉ sC U N ω) :
    rest U (insert u N) ω = rest (rest U N ω) ({u} : Set V) ω := by
  ext a
  rw [mem_rest, mem_rest, mem_rest, sC_insert_of_not_mem hu, Set.mem_union]
  tauto

end Percolation.Continuity.CovTau
