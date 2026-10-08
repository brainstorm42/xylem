import Percolation.Continuity.HullPort.TALayer
import Percolation.Util.Linter

/-!
# Marker dominance with an avoided set: Lemma `P_v` from cluster-conditional Harris

Lemma `P_v` ("conditioning on the cluster of `v` explains at most the
fraction `μ(y↮v | s↮y)` of `Cov(1_U(C_s), 1{s↔y})`") is reduced here, at sum level, to its Gladkov input
(CE) `E[1_U(C_s) · E[1_F | C_v]] ≥ P(U) P(F)`, `F = {s↔y} ∪ {y↔v}` (cluster-conditional Harris for the exploration
of `C_v`; see `MarkerDominancePv.sum_condSumW_ge`), as follows: total covariance over `C_v`
(`HullPort.set_sum_cond_sdiff`), `E[1_Y | C_v] = E[1_F | C_v] − 1{y ∈ C_v, s ∉ C_v}`, and the off-cluster negative
correlation of `1_U(C_s)` and `1{y↔v}` given `{s↮y}` (van den Berg–Häggström–Kahn Thm 1.3;
`setSep_offCluster_negCorrelation`).
* `HullPort.PvI_of_CE` — (CE) ⟹ `P_v` (event form `hPvI` of `Continuity/HullPort/TALayer`);
[cite: VandenbergHaggstromKahn2005, Thm. 1.3 (p. 6) — corollary; Gladkov2024, Thm. 3.2 (the input (CE))]
-/

noncomputable section

namespace Percolation.Continuity

open MeasureTheory Set Percolation.Literature.LatticeModels Percolation.Literature
open scoped Classical

variable {V : Type*}

namespace HullPort

open LonePortSum LonePortSumGeneral BHK2006 DecisionTree KNPreFKG

section TA

variable [Fintype V]

omit [Fintype V] in
/-- Reachability from `v` read off `C_v`. [folklore] -/
theorem reachable_iff_setCl_singleton (ω : Set (Sym2 V)) (v t : V) :
    (openGraph ω).Reachable v t ↔ (t ∈ ({v} : Set V) ∨ ∃ e ∈ setCl ω {v}, t ∈ e) := by
  rw [← setReach_iff]
  simp only [Set.mem_singleton_iff, exists_eq_left]

omit [Fintype V] in
/-- If `v ↮ s`, deleting the cut set of `{v}` does not change the cluster of `s`. [folklore] -/
theorem openEdgeCluster_sdiff_cut_singleton {ω : Set (Sym2 V)} {v s : V} (h : ¬ (openGraph ω).Reachable v s) :
    openEdgeCluster (ω \ cut {v} ω) s = openEdgeCluster ω s := by
  have hT : ∀ t ∈ ({s} : Set V), ¬ (t ∈ ({v} : Set V) ∨ ∃ e ∈ setCl ω {v}, t ∈ e) := by
    intro t ht; rw [Set.mem_singleton_iff] at ht; subst ht
    rw [← reachable_iff_setCl_singleton]; exact h
  have := setCl_eq_sdiff_barOf (rfl : setCl ω {v} = setCl ω {v}) hT
  rw [setCl_singleton, setCl_singleton, ← cut_eq_barOf] at this
  exact this.symm

omit [Fintype V] in
/-- If `v ↮ s`, deleting the cut set of `{v}` does not change the connections of `s`. [folklore] -/
theorem reachable_sdiff_cut_singleton_iff {ω : Set (Sym2 V)} {v s : V} (h : ¬ (openGraph ω).Reachable v s) (t : V) :
    (openGraph (ω \ cut {v} ω)).Reachable s t ↔ (openGraph ω).Reachable s t := by
  rw [reachable_iff_exists_mem_openEdgeCluster, reachable_iff_exists_mem_openEdgeCluster,
    openEdgeCluster_sdiff_cut_singleton h]

omit [Fintype V] in
/-- If `v ↔ y`, then after deleting the cut set of `{v}` the vertex `y` is isolated, so `s ↔ y` fails for `s ≠ y`. [folklore] -/
theorem ind_conn_sdiff_cut_eq_zero {ω : Set (Sym2 V)} {v y : V} (h : (openGraph ω).Reachable v y) (s : V)
    (hsy : s ≠ y) (η : Set (Sym2 V)) : ind (openConn s y : Set (BondConfig V)) (η \ cut {v} ω) = 0 := by
  refine ind_of_not_mem fun hmem => hsy ?_
  have hiso : ∀ e ∈ η \ cut {v} ω, y ∉ e := fun e he hye => he.2 ⟨y, hye, v, rfl, h⟩
  exact eq_of_reachable_of_isolated hiso s ((hmem : (openGraph _).Reachable s y).symm)

/-- **Lemma `P_v` from cluster-conditional Harris (CE)**, event form, sum level.  For `s ≠ y`,
every upper set `U` of clusters, weights `< 1` and every `v`:
`Σ_ω w 1{s↮v} Cov_{G−cut_v}(1_U(C_s), 1{s↔y}) ≤ μ(y↮v | s↮y) · Cov(1_U(C_s), 1{s↔y})`, given
(CE) `E[1_U(C_s) · F̂] ≥ E[1_U(C_s)] · E[1_F]` with `F = {s↔y} ∪ {y↔v}` and
`F̂ = E[1_F | C_v] = (1 if v↔y; 0 if v↮y, v↔s; μ_{G−cut_v}(s↔y) otherwise)`.
[cite: VandenbergHaggstromKahn2005, Thm. 1.3 (p. 6) — corollary; Gladkov2024, Thm. 3.2 (input)] -/
theorem PvI_of_CE (s y : V) (hsy : s ≠ y)
    (hCE : ∀ U : Set (Set (Sym2 V)), IsUpperSet U → ∀ (q : Sym2 V → unitInterval), (∀ e, (q e : ℝ) < 1) → ∀ v : V,
      (∑ ω, weight (fun e => (q e : ℝ)) ω * ind U (openEdgeCluster ω s)) *
          (∑ ω, weight (fun e => (q e : ℝ)) ω * ind (openConn s y ∪ openConn y v : Set (BondConfig V)) ω) ≤
        ∑ ω, weight (fun e => (q e : ℝ)) ω * (ind U (openEdgeCluster ω s) *
          (if (openGraph ω).Reachable v y then 1 else if (openGraph ω).Reachable v s then 0 else
            delE (fun e => (q e : ℝ)) (cut {v} ω) (ind (openConn s y : Set (BondConfig V))))))
    (U : Set (Set (Sym2 V))) (hU : IsUpperSet U) (q : Sym2 V → unitInterval) (hq : ∀ e, (q e : ℝ) < 1) (v : V) :
    taB (fun e => (q e : ℝ)) s y {v} (fun C => ind U C) ≤
      (1 - delE (fun e => (q e : ℝ)) ∅ (ind ((openConn s y : Set (BondConfig V))ᶜ ∩ openConn y v)) /
            delE (fun e => (q e : ℝ)) ∅ (ind (openConn s y : Set (BondConfig V))ᶜ)) *
        (delE (fun e => (q e : ℝ)) ∅ (fun η => (fun C => ind U C) (openEdgeCluster η s) * ind (openConn s y) η) -
          delE (fun e => (q e : ℝ)) ∅ (fun η => (fun C => ind U C) (openEdgeCluster η s)) *
            delE (fun e => (q e : ℝ)) ∅ (ind (openConn s y))) := by
  have hce := hCE U hU q hq v
  -- make the singleton `{v}` opaque (decidability instances in the conditioning kernels)
  generalize hX : ({v} : Set V) = X at hce ⊢
  set ŵ : Sym2 V → ℝ := fun e => (q e : ℝ) with hŵ
  have hw0 : ∀ e, 0 ≤ ŵ e := fun e => (q e).2.1
  have hw1 : ∀ e, ŵ e ≤ 1 := fun e => (q e).2.2
  have hm : ∑ ω, weight ŵ ω = 1 := by
    have h1 := integral_prodBernoulli_eq_sum q fun _ => (1 : ℝ)
    simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at h1
    exact h1.symm
  set Y : Set (BondConfig V) := openConn s y with hY
  set W : Set (BondConfig V) := openConn y v with hW
  -- bookkeeping through `hX`
  have memAv : ∀ ω : Set (Sym2 V), ω ∈ avoidEv s X ↔ ¬ (openGraph ω).Reachable s v := fun ω => by
    rw [← hX]; simp only [avoidEv, Set.mem_setOf_eq, Set.mem_singleton_iff, forall_eq]
  have hreach : ∀ (ω : Set (Sym2 V)) (t : V), (t ∈ X ∨ ∃ e ∈ setCl ω X, t ∈ e) ↔ (openGraph ω).Reachable v t :=
    fun ω t => by rw [← hX]; exact (reachable_iff_setCl_singleton ω v t).symm
  have hclus : ∀ ω : Set (Sym2 V), ¬ (openGraph ω).Reachable v s →
      openEdgeCluster (ω \ cut X ω) s = openEdgeCluster ω s :=
    fun ω h => by rw [← hX]; exact openEdgeCluster_sdiff_cut_singleton h
  have hconn : ∀ ω : Set (Sym2 V), ¬ (openGraph ω).Reachable v s → ∀ t : V,
      (openGraph (ω \ cut X ω)).Reachable s t ↔ (openGraph ω).Reachable s t :=
    fun ω h t => by rw [← hX]; exact reachable_sdiff_cut_singleton_iff h t
  have hzero : ∀ ω : Set (Sym2 V), (openGraph ω).Reachable v y → ∀ η : Set (Sym2 V), ind Y (η \ cut X ω) = 0 :=
    fun ω h η => by rw [← hX]; exact ind_conn_sdiff_cut_eq_zero h s hsy η
  set g : Set (Sym2 V) → ℝ := fun ω => ind U (openEdgeCluster ω s) with hg
  -- shorthand expectations
  set EgY : ℝ := ∑ ω, weight ŵ ω * (g ω * ind Y ω) with hEgY
  set Eg : ℝ := ∑ ω, weight ŵ ω * g ω with hEg
  set EY : ℝ := ∑ ω, weight ŵ ω * ind Y ω with hEY
  set EN : ℝ := ∑ ω, weight ŵ ω * ind Yᶜ ω with hEN
  set EWN : ℝ := ∑ ω, weight ŵ ω * ind (Yᶜ ∩ W) ω with hEWN
  set EgWN : ℝ := ∑ ω, weight ŵ ω * (g ω * ind (Yᶜ ∩ W) ω) with hEgWN
  set EgN : ℝ := ∑ ω, weight ŵ ω * (g ω * ind Yᶜ ω) with hEgN
  -- `delE ∅` is the plain expectation
  have hdel0 : ∀ φ : Set (Sym2 V) → ℝ, delE ŵ ∅ φ = ∑ ω, weight ŵ ω * φ ω := fun φ => by
    simp only [delE, Set.sdiff_empty]
  have hgap : ∀ ω : Set (Sym2 V), ind U (openEdgeCluster ω s) = g ω := fun ω => by simp only [hg]
  have goalE : (1 - delE ŵ ∅ (ind (Yᶜ ∩ W)) / delE ŵ ∅ (ind Yᶜ)) *
      (delE ŵ ∅ (fun η => (fun C => ind U C) (openEdgeCluster η s) * ind Y η) -
        delE ŵ ∅ (fun η => (fun C => ind U C) (openEdgeCluster η s)) * delE ŵ ∅ (ind Y)) =
      (1 - EWN / EN) * (EgY - Eg * EY) := by
    simp only [hdel0, hgap, hEWN, hEN, hEgY, hEg, hEY]
  rw [goalE]
  -- the conditional expectation `F̂ = E[1_F | C_v]`
  set Fh : Set (Sym2 V) → ℝ := fun ω => if (openGraph ω).Reachable v y then 1 else
    if (openGraph ω).Reachable v s then 0 else delE ŵ (cut X ω) (ind Y) with hFh
  -- conditioning identity A: `E[1{s↮v} E_{G−cut_v}[g 1_Y]] = E[1{s↮v} g 1_Y]`
  have idA : ∑ ω, weight ŵ ω * (ind (avoidEv s X) ω * delE ŵ (cut X ω) (fun η => g η * ind Y η)) =
      ∑ ω, weight ŵ ω * (ind (avoidEv s X) ω * (g ω * ind Y ω)) := by
    have key := set_sum_cond_sdiff ŵ hm X (fun Wc ζ =>
      (if (s ∈ X ∨ ∃ e ∈ Wc, s ∈ e) then 0 else 1) * (g ζ * ind Y ζ))
    have lhs : ∀ ω : Set (Sym2 V), weight ŵ ω * ((if (s ∈ X ∨ ∃ e ∈ setCl ω X, s ∈ e) then 0 else 1) *
        (g (ω \ barOf X (setCl ω X)) * ind Y (ω \ barOf X (setCl ω X)))) =
        weight ŵ ω * (ind (avoidEv s X) ω * (g ω * ind Y ω)) := by
      intro ω
      rw [← ind_avoidEv_eq_ite, ← cut_eq_barOf]
      by_cases hω : ω ∈ avoidEv s X
      · have hvs : ¬ (openGraph ω).Reachable v s := fun h => (memAv ω).1 hω h.symm
        have hgω : g (ω \ cut X ω) = g ω := by simp only [hg]; rw [hclus ω hvs]
        have hYY : ind Y (ω \ cut X ω) = ind Y ω := by
          by_cases h1 : (openGraph ω).Reachable s y
          · rw [ind_of_mem (show ω ∈ Y from h1), ind_of_mem (show ω \ cut X ω ∈ Y from (hconn ω hvs y).2 h1)]
          · rw [ind_of_not_mem (show ω ∉ Y from h1),
              ind_of_not_mem (show ω \ cut X ω ∉ Y from fun hh => h1 ((hconn ω hvs y).1 hh))]
        rw [hgω, hYY]
      · rw [ind_of_not_mem hω]; ring
    have rhs : ∀ ω : Set (Sym2 V), weight ŵ ω * ∑ η, weight ŵ η *
        ((if (s ∈ X ∨ ∃ e ∈ setCl ω X, s ∈ e) then 0 else 1) *
          (g (η \ barOf X (setCl ω X)) * ind Y (η \ barOf X (setCl ω X)))) =
        weight ŵ ω * (ind (avoidEv s X) ω * delE ŵ (cut X ω) (fun η => g η * ind Y η)) := by
      intro ω
      rw [← ind_avoidEv_eq_ite, ← cut_eq_barOf]
      simp only [delE, Finset.mul_sum]
      exact Finset.sum_congr rfl fun η _ => by ring
    rw [Finset.sum_congr rfl fun ω _ => (lhs ω).symm, key]
    exact Finset.sum_congr rfl fun ω _ => (rhs ω).symm
  -- conditioning identity B: `E[1{s↮v}1{v↮y} E_{G−cut_v}[g] E_{G−cut_v}[1_Y]] = E[1{s↮v}1{v↮y} g E_{G−cut_v}[1_Y]]`
  have hity : ∀ ω : Set (Sym2 V), (if (y ∈ X ∨ ∃ e ∈ setCl ω X, y ∈ e) then (0 : ℝ) else 1) =
      (if (openGraph ω).Reachable v y then 0 else 1) := fun ω => by
    by_cases h : (openGraph ω).Reachable v y
    · rw [if_pos h, if_pos ((hreach ω y).2 h)]
    · rw [if_neg h, if_neg fun hh => h ((hreach ω y).1 hh)]
  have idB : ∑ ω, weight ŵ ω * (ind (avoidEv s X) ω * ((if (openGraph ω).Reachable v y then 0 else 1) *
      (delE ŵ (cut X ω) g * delE ŵ (cut X ω) (ind Y)))) =
      ∑ ω, weight ŵ ω * (ind (avoidEv s X) ω * ((if (openGraph ω).Reachable v y then 0 else 1) *
      (g ω * delE ŵ (cut X ω) (ind Y)))) := by
    have key := set_sum_cond_sdiff ŵ hm X (fun Wc ζ =>
      (if (s ∈ X ∨ ∃ e ∈ Wc, s ∈ e) then 0 else 1) *
        ((if (y ∈ X ∨ ∃ e ∈ Wc, y ∈ e) then 0 else 1) * (g ζ * delE ŵ (barOf X Wc) (ind Y))))
    have lhs : ∀ ω : Set (Sym2 V), weight ŵ ω * ((if (s ∈ X ∨ ∃ e ∈ setCl ω X, s ∈ e) then 0 else 1) *
        ((if (y ∈ X ∨ ∃ e ∈ setCl ω X, y ∈ e) then 0 else 1) *
          (g (ω \ barOf X (setCl ω X)) * delE ŵ (barOf X (setCl ω X)) (ind Y)))) =
        weight ŵ ω * (ind (avoidEv s X) ω * ((if (openGraph ω).Reachable v y then 0 else 1) *
          (g ω * delE ŵ (cut X ω) (ind Y)))) := by
      intro ω
      rw [← ind_avoidEv_eq_ite, hity ω, ← cut_eq_barOf]
      by_cases hω : ω ∈ avoidEv s X
      · have hvs : ¬ (openGraph ω).Reachable v s := fun h => (memAv ω).1 hω h.symm
        have hgω : g (ω \ cut X ω) = g ω := by simp only [hg]; rw [hclus ω hvs]
        rw [hgω]
      · rw [ind_of_not_mem hω]; ring
    have rhs : ∀ ω : Set (Sym2 V), weight ŵ ω * ∑ η, weight ŵ η *
        ((if (s ∈ X ∨ ∃ e ∈ setCl ω X, s ∈ e) then 0 else 1) *
          ((if (y ∈ X ∨ ∃ e ∈ setCl ω X, y ∈ e) then 0 else 1) *
            (g (η \ barOf X (setCl ω X)) * delE ŵ (barOf X (setCl ω X)) (ind Y)))) =
        weight ŵ ω * (ind (avoidEv s X) ω * ((if (openGraph ω).Reachable v y then 0 else 1) *
          (delE ŵ (cut X ω) g * delE ŵ (cut X ω) (ind Y)))) := by
      intro ω
      rw [← ind_avoidEv_eq_ite, hity ω, ← cut_eq_barOf]
      rw [show delE ŵ (cut X ω) g = ∑ η, weight ŵ η * g (η \ cut X ω) from rfl]
      simp only [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun η _ => by ring
    rw [Finset.sum_congr rfl fun ω _ => (lhs ω).symm, key]
    exact Finset.sum_congr rfl fun ω _ => (rhs ω).symm
  -- taB in terms of the two identities
  have htaB : taB ŵ s y X (fun C => ind U C) =
      ∑ ω, weight ŵ ω * (ind (avoidEv s X) ω * (g ω * ind Y ω)) -
        ∑ ω, weight ŵ ω * (ind (avoidEv s X) ω * ((if (openGraph ω).Reachable v y then 0 else 1) *
          (g ω * delE ŵ (cut X ω) (ind Y)))) := by
    rw [← idA, ← idB, taB, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ω _ => ?_
    simp only [taC]
    by_cases hvy : (openGraph ω).Reachable v y
    · -- `v ↔ y`: `Y` is impossible after deleting `cut_v`
      have h0 : delE ŵ (cut X ω) (ind Y) = 0 :=
        Finset.sum_eq_zero fun η _ => by rw [hzero ω hvy η, mul_zero]
      rw [if_pos hvy, h0]; ring
    · rw [if_neg hvy]
      have : delE ŵ (cut X ω) (fun η => ind U (openEdgeCluster η s)) = delE ŵ (cut X ω) g := rfl
      rw [this]; ring
  -- pointwise: `g F̂ = g 1_W 1_Y + g 1_{W ∩ N} + 1{s↮v} 1{v↮y} g E_{G−cut_v}[1_Y]`
  have hgF : ∀ ω : Set (Sym2 V), g ω * Fh ω = g ω * ind W ω * ind Y ω + g ω * ind (Yᶜ ∩ W) ω +
      ind (avoidEv s X) ω * ((if (openGraph ω).Reachable v y then 0 else 1) * (g ω * delE ŵ (cut X ω) (ind Y))) := by
    intro ω
    simp only [hFh]
    by_cases hvy : (openGraph ω).Reachable v y
    · have hW1 : ω ∈ W := (hvy.symm : (openGraph ω).Reachable y v)
      rw [if_pos hvy, if_pos hvy]
      by_cases hYm : ω ∈ Y
      · rw [ind_of_mem hW1, ind_of_mem hYm, ind_of_not_mem (show ω ∉ Yᶜ ∩ W from fun h => h.1 hYm)]; ring
      · rw [ind_of_mem hW1, ind_of_not_mem hYm, ind_of_mem (show ω ∈ Yᶜ ∩ W from Set.mem_inter hYm hW1)]; ring
    · have hW0 : ω ∉ W := fun h => hvy ((h : (openGraph ω).Reachable y v).symm)
      rw [if_neg hvy, if_neg hvy, ind_of_not_mem hW0, ind_of_not_mem (show ω ∉ Yᶜ ∩ W from fun h => hW0 h.2)]
      by_cases hvs : (openGraph ω).Reachable v s
      · rw [if_pos hvs, ind_of_not_mem (show ω ∉ avoidEv s X from fun h => (memAv ω).1 h hvs.symm)]; ring
      · rw [if_neg hvs, ind_of_mem (show ω ∈ avoidEv s X from (memAv ω).2 fun h => hvs h.symm)]
        ring
  have hsplitY : ∀ ω : Set (Sym2 V), ind (avoidEv s X) ω * (g ω * ind Y ω) + g ω * ind W ω * ind Y ω =
      g ω * ind Y ω := by
    intro ω
    by_cases hYm : ω ∈ Y
    · by_cases hsv : (openGraph ω).Reachable s v
      · have hW1 : ω ∈ W := ((hYm : (openGraph ω).Reachable s y).symm.trans hsv : (openGraph ω).Reachable y v)
        rw [ind_of_not_mem (show ω ∉ avoidEv s X from fun h => (memAv ω).1 h hsv), ind_of_mem hW1]; ring
      · have hW0 : ω ∉ W := fun h => hsv ((hYm : (openGraph ω).Reachable s y).trans h)
        rw [ind_of_mem (show ω ∈ avoidEv s X from (memAv ω).2 hsv), ind_of_not_mem hW0]; ring
    · rw [ind_of_not_mem hYm]; ring
  have hF : ∀ ω : Set (Sym2 V), ind (Y ∪ W) ω = ind Y ω + ind (Yᶜ ∩ W) ω := by
    intro ω
    by_cases hYm : ω ∈ Y
    · rw [ind_of_mem (show ω ∈ Y ∪ W from Or.inl hYm), ind_of_mem hYm,
        ind_of_not_mem (show ω ∉ Yᶜ ∩ W from fun h => h.1 hYm)]; ring
    · by_cases hWm : ω ∈ W
      · rw [ind_of_mem (show ω ∈ Y ∪ W from Or.inr hWm), ind_of_not_mem hYm,
          ind_of_mem (show ω ∈ Yᶜ ∩ W from Set.mem_inter hYm hWm)]; ring
      · rw [ind_of_not_mem (show ω ∉ Y ∪ W from fun h => h.elim hYm hWm), ind_of_not_mem hYm,
          ind_of_not_mem (show ω ∉ Yᶜ ∩ W from fun h => hWm h.2)]; ring
  -- (CE) in shorthand
  have hceF : ∑ ω, weight ŵ ω * ind (Y ∪ W) ω = EY + EWN := by
    rw [hEY, hEWN, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun ω _ => by rw [hF, mul_add]
  have hce' : Eg * (EY + EWN) ≤ ∑ ω, weight ŵ ω * (g ω * Fh ω) := by
    rw [← hceF, hEg]
    simpa only [hg, hFh] using hce
  have hsumF : ∑ ω, weight ŵ ω * (g ω * Fh ω) = (∑ ω, weight ŵ ω * (g ω * ind W ω * ind Y ω)) + EgWN +
      ∑ ω, weight ŵ ω * (ind (avoidEv s X) ω * ((if (openGraph ω).Reachable v y then 0 else 1) *
        (g ω * delE ŵ (cut X ω) (ind Y)))) := by
    rw [hEgWN, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun ω _ => by rw [hgF]; ring
  -- Step 4: taB ≤ Cov(g,Y) + Cov(g, W ∩ N)
  have step4 : taB ŵ s y X (fun C => ind U C) ≤ (EgY - Eg * EY) + (EgWN - Eg * EWN) := by
    rw [htaB]
    have e1 : ∑ ω, weight ŵ ω * (ind (avoidEv s X) ω * (g ω * ind Y ω)) +
        ∑ ω, weight ŵ ω * (g ω * ind W ω * ind Y ω) = EgY := by
      rw [hEgY, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun ω _ => by rw [← mul_add, hsplitY]
    linarith [hce', hsumF, e1]
  -- Step 5: off-cluster negative correlation `E[N] E[g W N] ≤ E[W N] E[g N]`
  have hgmono : Monotone fun C : Set (Sym2 V) => ind U C := by
    intro C C' hCC'
    show ind U C ≤ ind U C'
    by_cases h : C ∈ U
    · rw [ind_of_mem h, ind_of_mem (hU hCC' h)]
    · rw [ind_of_not_mem h]; exact ind_nonneg _ _
  have hWmono : Monotone fun ω : BondConfig V => ind W ω := by
    intro ω ω' hle
    show ind W ω ≤ ind W ω'
    by_cases h : (openGraph ω).Reachable y v
    · rw [ind_of_mem (show ω ∈ W from h), ind_of_mem (show ω' ∈ W from h.mono (openGraph_le hle))]
    · rw [ind_of_not_mem (show ω ∉ W from h)]; exact ind_nonneg _ _
  have hWloc : ∀ ω : BondConfig V, (∀ x ∈ ({y} : Set V), ¬ (openGraph ω).Reachable s x) →
      ind W (ω \ {e | ∃ u ∈ e, u = s ∨ ∃ e' ∈ openEdgeCluster ω s, u ∈ e'}) = ind W ω := by
    intro ω hω
    have hx : ¬ (openGraph ω).Reachable s y := hω y rfl
    by_cases h : (openGraph ω).Reachable y v
    · rw [ind_of_mem (show ω ∈ W from h), ind_of_mem (show ω \ {e | ∃ u ∈ e, u = s ∨
        ∃ e' ∈ openEdgeCluster ω s, u ∈ e'} ∈ W from (reachable_sdiff_bar_iff hx v).2 h)]
    · rw [ind_of_not_mem (show ω ∉ W from h), ind_of_not_mem (show ω \ {e | ∃ u ∈ e, u = s ∨
        ∃ e' ∈ openEdgeCluster ω s, u ∈ e'} ∉ W from fun hh => h ((reachable_sdiff_bar_iff hx v).1 hh))]
  have hoc := setSep_offCluster_negCorrelation q s ({y} : Set V) (fun h => hsy (Set.mem_singleton_iff.1 h))
    (fun C => ind U C) hgmono (fun ω => ind W ω) hWmono hWloc
  have hN : {ω : BondConfig V | ∀ x ∈ ({y} : Set V), ¬ (openGraph ω).Reachable s x} = Yᶜ := by
    ext ω
    rw [hY]
    simp only [openConn, Set.mem_setOf_eq, Set.mem_singleton_iff, forall_eq, Set.mem_compl_iff]
  simp only [hN, measureReal_eq_sum, setIntegral_eq_sum] at hoc
  have o1 : ∑ ω, weight (fun e => (q e : ℝ)) ω * ind Yᶜ ω = EN := by simp only [hEN, hŵ]
  have o2 : ∑ ω, weight (fun e => (q e : ℝ)) ω * (ind U (openEdgeCluster ω s) * ind W ω * ind Yᶜ ω) = EgWN := by
    simp only [hEgWN, hŵ, hg, ind_inter]
    exact Finset.sum_congr rfl fun ω _ => by ring
  have o3 : ∑ ω, weight (fun e => (q e : ℝ)) ω * (ind U (openEdgeCluster ω s) * ind Yᶜ ω) = EgN := by
    simp only [hEgN, hŵ, hg]
  have o4 : ∑ ω, weight (fun e => (q e : ℝ)) ω * (ind W ω * ind Yᶜ ω) = EWN := by
    simp only [hEWN, hŵ, ind_inter]
    exact Finset.sum_congr rfl fun ω _ => by ring
  rw [o1, o2, o3, o4] at hoc
  -- `E[g N] = E[g] − E[g Y]`, `E[Y] + E[N] = 1`, `E[N] > 0`
  have hgN : EgN = Eg - EgY := by
    rw [hEgN, hEg, hEgY, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ω _ => ?_
    have : ind Yᶜ ω = 1 - ind Y ω := by
      by_cases h : ω ∈ Y
      · rw [ind_of_mem h, ind_of_not_mem (show ω ∉ Yᶜ from fun hh => hh h)]; ring
      · rw [ind_of_not_mem h, ind_of_mem (show ω ∈ Yᶜ from h)]; ring
    rw [this]; ring
  have hEYN : EY + EN = 1 := by
    rw [hEY, hEN, ← Finset.sum_add_distrib, ← hm]
    refine Finset.sum_congr rfl fun ω _ => ?_
    by_cases h : ω ∈ Y
    · rw [ind_of_mem h, ind_of_not_mem (show ω ∉ Yᶜ from fun hh => hh h)]; ring
    · rw [ind_of_not_mem h, ind_of_mem (show ω ∈ Yᶜ from h)]; ring
  have hENpos : 0 < EN := by
    have hmem : (∅ : Set (Sym2 V)) ∈ Yᶜ := fun h => hsy ((reachable_empty_iff s y).1 h)
    have h1 : weight ŵ (∅ : Set (Sym2 V)) * ind Yᶜ ∅ ≤ EN :=
      Finset.single_le_sum (f := fun ω => weight ŵ ω * ind Yᶜ ω)
        (fun ω _ => mul_nonneg (weight_nonneg hw0 hw1 ω) (ind_nonneg _ _)) (Finset.mem_univ _)
    rw [ind_of_mem hmem, mul_one] at h1
    exact lt_of_lt_of_le (weight_empty_pos ŵ hq) h1
  -- conclude
  have hoc' : EgWN - Eg * EWN ≤ -(EWN / EN) * (EgY - Eg * EY) := by
    rw [hgN] at hoc
    rw [show -(EWN / EN) * (EgY - Eg * EY) = (EWN * (Eg * EY - EgY)) / EN by ring]
    rw [le_div_iff₀ hENpos]
    linear_combination hoc - (Eg * EWN) * hEYN
  calc taB ŵ s y X (fun C => ind U C) ≤ (EgY - Eg * EY) + (EgWN - Eg * EWN) := step4
    _ ≤ (EgY - Eg * EY) + (-(EWN / EN) * (EgY - Eg * EY)) := by linarith
    _ = (1 - EWN / EN) * (EgY - Eg * EY) := by ring

end TA

end HullPort

end Percolation.Continuity
