import Percolation.Literature.LonePortSumGeneral
import Percolation.Literature.TargetExplorationHK
import Percolation.Util.Linter

/-!
# Cluster conditioning and the two-point covariance: `E[Cov(g(C_s), 1{s ↔ y} | 𝓕(C_v))] ≤ P(y ↮ v | y ↮ s) · Cov(g(C_s), 1{s ↔ y})`

Bernoulli bond percolation on a finite vertex set `V` with
arbitrary edge probabilities `p_e ∈ [0, 1]` (product weights `BHK2006.weight`, configurations `Set (Sym2 V)`),
three vertices `s, y, v`, and an increasing function `g ≥ 0` of van den Berg–Häggström–Kahn's open edge cluster
`C_s = openEdgeCluster ω s`.  Everything in this file is proved; it combines two printed tools:

* N. Gladkov, *Percolation Inequalities and Decision Trees*, arXiv:2408.08457v2 (2024), **Theorem 3.2** (the
  decision-tree Harris–Kleitman inequality) for the decision tree exploring the open cluster of `v`
  (here `TargetExploration.PrW_mul_PrW_le_Pr2W_hybrid` with target set `∅`), together with his **Lemma 3.1**
  (the swap along a self-determined revealed set preserves the product law; here
  `DecisionTree.sum_pair_reindexW`, `TargetExploration.fin_splice`);
* J. van den Berg, O. Häggström, J. Kahn, *Some conditional correlation inequalities for percolation and
  related processes*, Random Structures Algorithms 29 (2006) 417–435, **Theorem 1.3** in the "cluster /
  off-cluster" form of pp. 7–8 (here `setSep_offCluster_negCorrelation`).

Write `E` for the product-weight expectation, `Y = {s ↔ y}`, `N = Yᶜ`, `W_v = {y ↔ v}`, and, for a configuration
`ω`, `cut_v(ω) = {e | e meets the open vertex cluster of v}`; given the cluster of `v`, the configuration off
`cut_v(ω)` is fresh, so the conditional covariance of `g(C_s)` and `1_Y` given the exploration σ-field of `C_v` is,
on `{s ↮ v}`, the covariance `c_v(ω)` of `g(C_s(η ∖ cut_v ω))` and `1_Y(η ∖ cut_v ω)` under a fresh `η` (and `0` on
`{s ↔ v}`).  The results:

* (private plumbing) a finite layer-cake lemma (a linear functional nonnegative on indicators of up-sets is
  nonnegative on monotone nonnegative functions) and the bridge between the finitary calculus
  `DecisionTree.wtW/PrW` on `Finset (Sym2 V)` and the product weights `BHK2006.weight` on `Set (Sym2 V)`;

Proof of the main inequality: with `𝓕 = 𝓕(C_v)` and the increasing event
`F = Y ∪ W_v`, pointwise `1_F = 1_Y + 1_N 1_{W_v}` and `1_N 1_{W_v}` is `𝓕`-measurable, so by Theorem 3.2
`E[g · E[1_Y | 𝓕]] ≥ E g · E 1_Y − Cov(g, 1_N 1_{W_v})`, while `Cov(g, 1_N 1_{W_v}) ≤ −(E[1_N 1_{W_v}]/E[1_N]) Cov(g, 1_Y)`
by the off-cluster negative correlation of `g(C_s)` and `1{y ↔ v}` given `s ↮ y`; and
`E[1{s ↮ v} c_v] = E[g 1_Y] − E[g · E[1_Y | 𝓕]]` by the product law of the hybrid.  Not in print in this form;
derived here from the two printed theorems.

## References
* N. Gladkov, *Percolation Inequalities and Decision Trees*, arXiv:2408.08457v2 (2024), Lemma 3.1, Thm. 3.2,
  Example 2.5. [Gladkov2024]
* J. van den Berg, O. Häggström, J. Kahn, *Some conditional correlation inequalities for percolation and related
  processes*, Random Structures Algorithms 29 (2006) 417–435, Thm. 1.3 and pp. 7–8. [VandenbergHaggstromKahn2005]
-/

noncomputable section

open Classical

namespace Percolation.Literature

namespace ClusterConditioning

open Finset DecisionTree BHK2006 TargetExploration MeasureTheory LonePortSum LonePortSumGeneral
open Percolation.Literature.LatticeModels (prodBernoulli)

/-! ### The exploration of the whole open cluster of `v` (`TargetExploration` with target set `∅`) -/

section Exploration

variable {V : Type*} [Fintype V]

/-- With no target, the final state of the exploration has an empty boundary. [cite: Gladkov2024, Example 2.5 (the algorithm determining C_v)] -/
theorem bnd_fin_eq_empty (v : V) (K : Finset (Sym2 V)) :
    bnd (Finset.univ : Finset (Sym2 V)) (fin Finset.univ (∅ : Finset V) v K) = ∅ := by
  rcases halted_fin (D := (Finset.univ : Finset (Sym2 V))) (A := (∅ : Finset V)) (o := v) K with h | h
  · simp at h
  · exact h

/-- **The exploration with no target reaches exactly the open cluster of `v`.**
[cite: Gladkov2024, Example 2.5 (the algorithm determining C_v)] -/
theorem mem_vis_fin_iff (v : V) (K : Finset (Sym2 V)) (u : V) :
    u ∈ (fin (Finset.univ : Finset (Sym2 V)) (∅ : Finset V) v K).vis ↔
      (openGraph (↑K : Set (Sym2 V))).Reachable v u := by
  constructor
  · intro hu
    exact ((inv_fin K).reach u hu).mono (openGraph_mono (Finset.coe_subset.2 Finset.inter_subset_right))
  · intro hu
    by_contra hnot
    set σ := fin (Finset.univ : Finset (Sym2 V)) (∅ : Finset V) v K with hσ
    have hinv : Inv Finset.univ ∅ v K σ := inv_fin K
    have hbnd : bnd Finset.univ σ = ∅ := bnd_fin_eq_empty v K
    obtain ⟨w⟩ := hu
    obtain ⟨d, -, hd1, hd2⟩ := w.exists_boundary_dart (↑σ.vis) (Finset.mem_coe.2 hinv.root)
      (fun h => hnot (Finset.mem_coe.1 h))
    have hadj := d.adj
    rw [openGraph_adj] at hadj
    obtain ⟨hmem, hne⟩ := hadj
    have hmemK : s(d.toProd.1, d.toProd.2) ∈ K := Finset.mem_coe.1 hmem
    have hnotrev : s(d.toProd.1, d.toProd.2) ∉ σ.rev := fun hrev =>
      hd2 (Finset.mem_coe.2 (hinv.open_vis _ hrev hmemK _ (Sym2.mem_mk_right _ _)))
    have hin : s(d.toProd.1, d.toProd.2) ∈ bnd Finset.univ σ :=
      mem_bnd.2 ⟨⟨d.toProd.1, Finset.mem_coe.1 hd1, d.toProd.2, fun h => hd2 (Finset.mem_coe.2 h), rfl⟩,
        Finset.mem_univ _, hnotrev⟩
    rw [hbnd] at hin
    exact Finset.notMem_empty _ hin

/-- **The exploration reveals only pairs meeting the cluster of `v`.** [cite: Gladkov2024, Example 2.5] -/
theorem exists_reachable_of_mem_revealedAt {v : V} {K : Finset (Sym2 V)} {e : Sym2 V}
    (he : e ∈ revealedAt (Finset.univ : Finset (Sym2 V)) (∅ : Finset V) v K) :
    ∃ u ∈ e, (openGraph (↑K : Set (Sym2 V))).Reachable v u := by
  obtain ⟨u, hu, hue⟩ := (inv_fin K).touch e he
  exact ⟨u, hue, (mem_vis_fin_iff v K u).1 hu⟩

/-- **The hybrid keeps the cluster of `v`**: splicing `K` (on its revealed set) with any `C` (elsewhere) does not
change which vertices are joined to `v`. [cite: Gladkov2024, Lemma 3.1 (S(C₁ →_S C₂) = S(C₁))] -/
theorem reachable_hybrid_iff (v : V) (K C : Finset (Sym2 V)) (u : V) :
    (openGraph (↑(splice (revealedAt (Finset.univ : Finset (Sym2 V)) (∅ : Finset V) v K) K C) :
        Set (Sym2 V))).Reachable v u ↔
      (openGraph (↑K : Set (Sym2 V))).Reachable v u := by
  rw [← mem_vis_fin_iff, ← mem_vis_fin_iff,
    fin_splice (D := (Finset.univ : Finset (Sym2 V))) (A := (∅ : Finset V)) (o := v) K C]

end Exploration

end ClusterConditioning

end Percolation.Literature

end
