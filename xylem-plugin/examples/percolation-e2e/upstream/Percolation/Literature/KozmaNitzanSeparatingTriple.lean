import Percolation.Literature.KozmaNitzanPreFKG
import Percolation.Literature.LatticeModels.ProdBernoulliClusterLocality
import Percolation.Literature.LatticeModels.ProdBernoulliRecolour
import Percolation.Literature.TwoSetConditionalAssociation
import Percolation.Util.Linter

/-!
# Kozma–Nitzan (2024), Theorem 3: the pre-FKG inequality for `|A| = 3` when `A` separates `0` from `b` (with Lemma 4 and its gluing form (9))

Source: G. Kozma, S. Nitzan, *A reduction of the `θ(p_c) = 0` problem to a conjectured
inequality*, arXiv:2401.12397 (2024) [KozmaNitzan2024], §3.1,
pp. 9–12: **Lemma 4**, its reformulation **(9)**, and **Theorem 3**.  Companion of
`KozmaNitzanPreFKG.lean` (Lemma 3, Theorem 1, Lemma 5, Theorem 4, all proved there), whose vocabulary
and whose event forms of the van den Berg–Häggström–Kahn (BHK) inequalities are reused.  Everything in
this file is proved; no unproved statement is introduced.

## Printed statements (arXiv:2401.12397, pp. 3, 5–6, 9–12)

Setting (p. 4): finite graphs with arbitrary edge probabilities; the pre-FKG inequality in the form
**(3)** (p. 3): "`P(0 ↔ b, 0 ↔ A) ≥ min{P(0 ↔ A, a ↔ b) : a ∈ A}`."

* **Lemma 4** (p. 9): "Let `G` be a graph and `a₁, a₂, a₃, b ∈ G`. Then
  `max_{j=1,2} P({a₁,a₂} is pivotal for a_j ↔ b) ≥ P({a₁,a₂} is pivotal for a₃ ↔ b). (8)`"
  (proof: Theorem 1 with `0 := a₃`, `A = {a₁,a₂}`, subtract `P(a₃ ↔ a₂ ↔ b)`, enlarge, add
  `P(a₁ ↔ b, a₂ ↔ a₃, a₁ ↮ a₂)`).  **Remark / (9)** (pp. 9–10): with `G* = G/{a₁,a₂}` the graph with
  `a₁, a₂` glued, "(8) can be reformulated as
  `P_{G*}({a₁,a₂} ↔ b) − P_{G*}(a₃ ↔ b) ≥ min_{j=1,2} P_G(a_j ↔ b) − P_G(a₃ ↔ b). (9)`"
* **Theorem 3** (p. 10): "If `|A| = 3` and `A` separates `0` from `b`, namely, any path in `G` from
  `0` to `b` must pass through a point of `A`, then the pre-FKG inequality in the form (3) holds."
  Proof (pp. 10–12): split `G` along `A` into `B` (the component of `0`, with `A` and the edges inside
  `A`) and `T` (the other components with `A`, without the edges inside `A`); `T^{(jk)} = T/{a_j,a_k}`;
  `q_X = P_T(A(X) ↔ b)`, `q^{(jk)}_X = P_{T^{(jk)}}(A(X) ↔ b)`; with `a₃` minimising `P(a_j ↔ b)`:
  (10)–(11) `0 ≤ P(a₁ ↔ b) − P(a₃ ↔ b) = P_B(a₁↔a₂↮a₃)(q₁₂ − q^{(12)}_3) + P_B(a₁↮a₂↔a₃)(q^{(23)}_1 − q₂₃)
  + P_B(M)(q₁ − q₃)`, `M = {a₁, a₂, a₃ pairwise ↮ in B}`; (12)–(13) from Lemma 3(ii):
  `0 ≤ P_B(a₁↔a₂↮a₃)(q₁₂ − q^{(12)}_3) + P(M)(q₁ − q₃)` (and with `a₁, a₂` swapped); Lemma 4 on `T`
  gives (14) `q₁₂ − q^{(12)}_3 ≥ 0`; then
  `P(0 ↔ b) − P(0 ↔ A, a₃ ↔ b) = α + β₁ + β₂ + γ₁ + γ₂` and two double applications of Lemma 1 in `B`
  ("`α + γ₁ + γ₂ ≥ P_B(0↔a₁|M) L₁ + P_B(0↔a₂|M) L₂`", "`β₁ + δ₁ ≥ 0`", "`β₂ + δ₂ ≥ 0`").

## Transcription (the vocabulary of `KozmaNitzanPreFKG.lean`)

Weights `w : Sym2 V → [0,1]` on a finite vertex type (absent edges = weight `0`), `μ = prodBernoulli w`
on `BondConfig V = Set (Sym2 V)`, `{x ↔ y} = openConn x y`, `{0 ↔ A} = ⋃_{a∈A} {0 ↔ a}`, minima over
`A` as existentials.  "A path in `G`" is a walk in the graph of positive-weight pairs
(`SimpleGraph.fromEdgeSet {e | w e ≠ 0}`); `0, b ∉ A`.  The separation is used through the partition
it induces (`KozmaNitzan2024_thm3_of_parts`): `VB` = the vertices reachable from `0` avoiding `A`
(`KNSep.observerSide`), no positive weight from `VB` to the outside of `VB ∪ A`.  The `B`-side pairs
are the pairs inside `VB ∪ A` (`KNSep.sideB`), the `T`-side pairs those inside `VBᶜ` not inside `A`
(`KNSep.sideT`); `x ↔ y` "in `B`" is an open path through `B`-side pairs (`KNSep.rB`), and gluing
`a_j, a_k` in `T` is realised by a surely-open virtual edge: connectivity in `T^{(F)}` is an open path
through `T`-side pairs and the pairs of `F ⊆ {a₁a₂, a₁a₃, a₂a₃}` (`KNSep.rT`); as percolation models,
`B` has the weights `w·1_{E_B}` (`SepData.wB`) and `T^{(F)}` the weights `1_F + w·1_{E_T}`
(`SepData.uT`), and `P(Φ(↔ in B)) = P_B(Φ(↔))`, `P(Ψ(↔ in T^{(F)})) = P_{T^{(F)}}(Ψ(↔))`
(`SepData.real_rb_eq`, `SepData.real_rt_eq`, locality of `prodBernoulli`).  "Pivotal" in Lemma 4 is
taken in the closed form `{x ↮ b in ω, x ↔ b in ω ∪ {e}}` (for the increasing event `{x ↔ b}` this is
"`e` pivotal and closed"; the state of `e` is independent of pivotality), which is what (9) needs.

## Contents and proof architecture (following the printed proof step by step)

* `KNSep.reachable_insert_iff` (one virtual edge), `KNSep.reachable_inter_iff_cluster` (reading
  restricted connectivity on BHK's open cluster `C_S`), `KNSep.bhk_set_event_pos/neg` (event forms of
  the set version of BHK, `BHK2006_twoSetConditionalAssociation` — the engine of KN's Lemma 1).
* `KozmaNitzan2024_lemma4` — **Lemma 4**, proved from Theorem 1 (`KNPreFKG.preFKG_pair`) exactly as
  printed (`KNSep.lemma4_core` = the displayed chain); `KozmaNitzan2024_lemma4_glued` — **(9)**, proved.
* `KNSep.amalgam` — the combinatorial content of "break according to the connection patterns in `B`":
  for a configuration without open cross pairs, `x ↔ y` (`x, y ∉ VB`) iff `x ↔ y` in `T` glued along the
  pairs of `A` joined in `B`, and `0 ↔ y` iff `0 ↔_B a ↔_{T,glued} y` for some `a ∈ A` (induction along
  the open path); `KNSep.SepData.*`: the five connection patterns of `A` in `B` and their glue sets,
  independence of the two sides (`real_inter_rb_rt`), the product formulas
  `P(x ↔ b, pattern) = P_B(pattern) · q^{(pattern)}_x` (`real_conn_inter_ev`, `real_oconn_inter_ev`),
  **(11)** (`eq11`, `eq11'`), **(13)** (`eq13`, `eq13'`: Lemma 3(ii) of `KozmaNitzanPreFKG.lean` with the
  decreasing cluster event `Q = {a₃ ↮ a₂ in B}` — the reading of "{a₃ ↮ a₂}" under which "(12) broken
  according to the connection patterns in `B`" is (13); with the plain event `{a₃ ↮ a₂}` the identity (13)
  fails, as the pattern `M` then carries extra `T`-terms), **(9) on `T`** (`eq9T`), the decomposition
  `P(0↔b) − P(0↔A, a₃↔b) = α + β₁ + β₂ + γ₁ + γ₂` (`o_decomp`), and the two double applications of
  Lemma 1 in `B` in denominator-free form (`factX`: `x₁₂·P(M) ≥ p₁₂(z₁+z₂)`; `factY1`, `factY2`:
  `z_j p ≥ P(M) y_j`).
* `KNSep.SepData.preFKG_three` — the assembly.  The printed bookkeeping divides by `P(M)`; here it is
  multiplied through, and the case `P(M) = 0` (not discussed in print) is settled separately
  (`m_zero_cases`: then two points of `A` are almost surely joined in `B`, two of the three split
  patterns are null, and (11)/(13) already conclude).  (14) is used in the form "`q₁₂ − q^{(12)}_3 ≥ 0`
  or `P_B(a₁↔a₂↮a₃) = 0`", which is what the printed contradiction argument yields.
* `KozmaNitzan2024_thm3_of_parts` (separation as a partition) and **`KozmaNitzan2024_thm3`** (the
  printed statement: every path from `0` to `b` meets `A`) — **Theorem 3**.

## Context

Theorem 3 is the `|A| = 3` case of the pre-FKG inequality (3) (hence of KN Conjectures 1–2 and of
KN Question 7 at `|A| = 3`) on the configurations where `A` separates the observer from the target;
its proof rests on the factorisation `P = P_B ⋈ P_T` along the separating set.  Lemma 4/(9) is the
printed gluing comparison.
-/

noncomputable section

open MeasureTheory Set
open Percolation.Literature.LatticeModels (prodBernoulli)

namespace Percolation.Literature

variable {V : Type*}

namespace KNSep

/-! ### Graph-theoretic preliminaries: reachability through a sub-family of pairs, virtual edges -/

/-- If every edge of `G` joins two `H`-reachable vertices then `G`-reachability implies
`H`-reachability. [folklore] -/
theorem reachable_of_adj_reachable {G H : SimpleGraph V}
    (h : ∀ u v, G.Adj u v → H.Reachable u v) {x y : V} (hxy : G.Reachable x y) :
    H.Reachable x y := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hxy
  induction hxy with
  | refl => exact SimpleGraph.Reachable.refl x
  | tail _ hadj ih => exact ih.trans (h _ _ hadj)

/-- **One extra edge.** Reachability in the open graph of `insert s(u,v) ω`: either `x ↔ y` already in
`ω`, or `x ↔ u` and `v ↔ y` in `ω`, or `x ↔ v` and `u ↔ y` in `ω` (the extra edge is used, and one may
assume it is used once). [folklore] -/
theorem reachable_insert_iff (ω : BondConfig V) (u v x y : V) :
    (openGraph (insert s(u, v) ω)).Reachable x y ↔
      (openGraph ω).Reachable x y ∨
        ((openGraph ω).Reachable x u ∧ (openGraph ω).Reachable v y) ∨
        ((openGraph ω).Reachable x v ∧ (openGraph ω).Reachable u y) := by
  constructor
  · intro hxy
    rw [SimpleGraph.reachable_iff_reflTransGen] at hxy
    induction hxy with
    | refl => exact Or.inl (SimpleGraph.Reachable.refl x)
    | tail hzz hadj ih =>
      rename_i z z'
      rcases (openGraph_adj _ z z').1 hadj with ⟨hmem, hne⟩
      rcases Set.mem_insert_iff.1 hmem with heq | hω
      · -- the step is along the extra edge `s(u,v)`
        rcases Sym2.eq_iff.1 heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · -- `z = u`, `z' = v`
          rcases ih with h | ⟨h, -⟩ | ⟨h, -⟩
          · exact Or.inr (Or.inl ⟨h, SimpleGraph.Reachable.refl _⟩)
          · exact Or.inr (Or.inl ⟨h, SimpleGraph.Reachable.refl _⟩)
          · exact Or.inl h
        · -- `z = v`, `z' = u`
          rcases ih with h | ⟨h, -⟩ | ⟨h, -⟩
          · exact Or.inr (Or.inr ⟨h, SimpleGraph.Reachable.refl _⟩)
          · exact Or.inl h
          · exact Or.inr (Or.inr ⟨h, SimpleGraph.Reachable.refl _⟩)
      · have hzz' : (openGraph ω).Reachable z z' :=
          SimpleGraph.Adj.reachable ((openGraph_adj ω z z').2 ⟨hω, hne⟩)
        rcases ih with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl (h.trans hzz')
        · exact Or.inr (Or.inl ⟨h1, h2.trans hzz'⟩)
        · exact Or.inr (Or.inr ⟨h1, h2.trans hzz'⟩)
  · have hsub : ω ⊆ insert s(u, v) ω := Set.subset_insert _ _
    have huv : (openGraph (insert s(u, v) ω)).Reachable u v := by
      by_cases h : u = v
      · subst h; exact SimpleGraph.Reachable.refl u
      · exact SimpleGraph.Adj.reachable ((openGraph_adj _ u v).2 ⟨Set.mem_insert _ _, h⟩)
    rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact h.mono (openGraph_mono hsub)
    · exact ((h1.mono (openGraph_mono hsub)).trans huv).trans (h2.mono (openGraph_mono hsub))
    · exact ((h1.mono (openGraph_mono hsub)).trans huv.symm).trans (h2.mono (openGraph_mono hsub))

/-- **Reading reachability off the open cluster.** An open path from `x` using only pairs of `E`
consists of edges of the open edge cluster of `x`; hence for any family of sources `S ∋ x`,
`x ↔ y` through `ω ∩ E` iff `x ↔ y` through `C_S(ω) ∩ E`, `C_S = ⋃_{s ∈ S} C_s`
(BHK's "functions of `C_S`", arXiv:math/0408176 p. 9). [cite: VandenbergHaggstromKahn2005, §2 p. 9 (events defined on C_S)] -/
theorem reachable_inter_iff_cluster (ω : BondConfig V) (E : Set (Sym2 V)) (S : Set V) {x : V}
    (hx : x ∈ S) (y : V) :
    (openGraph (ω ∩ E)).Reachable x y ↔
      (openGraph ((⋃ s ∈ S, openEdgeCluster ω s) ∩ E)).Reachable x y := by
  constructor
  · intro hxy
    rw [SimpleGraph.reachable_iff_reflTransGen] at hxy
    induction hxy with
    | refl => exact SimpleGraph.Reachable.refl x
    | tail hzz hadj ih =>
      rename_i z z'
      rcases (openGraph_adj _ z z').1 hadj with ⟨⟨hω, hE⟩, hne⟩
      have hxz : (openGraph ω).Reachable x z :=
        ih.mono (openGraph_mono (Set.inter_subset_left.trans (Set.iUnion₂_subset fun s _ =>
          openEdgeCluster_subset ω s)))
      have hzz' : (openGraph ω).Adj z z' := (openGraph_adj ω z z').2 ⟨hω, hne⟩
      have hmem : s(z, z') ∈ openEdgeCluster ω x := by
        refine ⟨hω, ?_, ?_⟩
        · rwa [Sym2.mk_isDiag_iff]
        · intro v hv
          rcases Sym2.mem_iff.1 hv with rfl | rfl
          · exact hxz
          · exact hxz.trans hzz'.reachable
      refine ih.trans (SimpleGraph.Adj.reachable ((openGraph_adj _ z z').2 ⟨⟨?_, hE⟩, hne⟩))
      exact Set.mem_iUnion₂.2 ⟨x, hx, hmem⟩
  · exact fun h => h.mono (openGraph_mono (Set.inter_subset_inter_left _
      (Set.iUnion₂_subset fun s _ => openEdgeCluster_subset ω s)))

/-- The case `E = univ`: `x ↔ y` in `ω` iff `x ↔ y` through the edges of `C_S(ω)`, `x ∈ S`.
[cite: VandenbergHaggstromKahn2005, §1 p. 3] -/
theorem reachable_iff_cluster (ω : BondConfig V) (S : Set V) {x : V} (hx : x ∈ S) (y : V) :
    (openGraph ω).Reachable x y ↔ (openGraph (⋃ s ∈ S, openEdgeCluster ω s)).Reachable x y := by
  have h := reachable_inter_iff_cluster ω Set.univ S hx y
  rwa [Set.inter_univ, Set.inter_univ] at h

/-! ### Measure-theoretic preliminaries -/

section Measure

/-- An event of the form `{ω | P (ω ∩ E)}` is determined by the coordinates in `E`. [folklore] -/
theorem determinedBy_setOf_inter (E : Set (Sym2 V)) (P : Set (Sym2 V) → Prop) :
    DeterminedBy {ω : BondConfig V | P (ω ∩ E)} E := by
  rw [determinedBy_iff]
  intro ω ω' h
  simp only [mem_setOf_eq, h]

variable [Fintype V]

/-- **Independence of the two sides.** An event reading only the pairs in `E` and an event reading
only the pairs off `E` are independent under `prodBernoulli w` (Grimmett 1999, §2.2;
`prodBernoulli_real_inter_of_determinedBy`). [cite: GrimmettPercolation1999, §2.2] -/
theorem real_inter_of_determinedBy_compl (w : Sym2 V → unitInterval) (E : Set (Sym2 V))
    {A B : Set (BondConfig V)} (hA : DeterminedBy A E) (hB : DeterminedBy B Eᶜ) :
    (prodBernoulli w).real (A ∩ B) = (prodBernoulli w).real A * (prodBernoulli w).real B := by
  classical
  have hE : (↑E.toFinset : Set (Sym2 V)) = E := Set.coe_toFinset E
  refine Percolation.Literature.LatticeModels.prodBernoulli_real_inter_of_determinedBy w E.toFinset
    (by rwa [hE]) (by rwa [hE]) MeasurableSet.of_discrete MeasurableSet.of_discrete

/-- **Locality.** Two weight functions agreeing on `E` give the same probability to every event reading
only the pairs in `E` (`prodBernoulli_real_eq_of_determinedBy`). [cite: GrimmettPercolation1999, §1.3 p. 11] -/
theorem real_eq_of_agree (w u : Sym2 V → unitInterval) (E : Set (Sym2 V)) (hwu : ∀ e ∈ E, w e = u e)
    {A : Set (BondConfig V)} (hA : DeterminedBy A E) :
    (prodBernoulli w).real A = (prodBernoulli u).real A := by
  classical
  exact Percolation.Literature.LatticeModels.prodBernoulli_real_eq_of_determinedBy w u hwu hA
    MeasurableSet.of_discrete

/-- The configurations in which every weight-`0` pair is closed and every weight-`1` pair is open. [folklore] -/
def sureSet (u : Sym2 V → unitInterval) : Set (BondConfig V) :=
  {ω | ∀ e, (u e = 0 → e ∉ ω) ∧ (u e = 1 → e ∈ ω)}

/-- `sureSet u` has full `prodBernoulli u`-measure. [folklore] -/
theorem measure_compl_sureSet (u : Sym2 V → unitInterval) : prodBernoulli u (sureSet u)ᶜ = 0 := by
  classical
  have hsub : (sureSet u)ᶜ ⊆ ⋃ e : Sym2 V,
      ({ω : BondConfig V | u e = 0 ∧ e ∈ ω} ∪ {ω | u e = 1 ∧ e ∉ ω}) := by
    intro ω hω
    simp only [sureSet, mem_compl_iff, mem_setOf_eq, not_forall] at hω
    obtain ⟨e, he⟩ := hω
    refine mem_iUnion.2 ⟨e, ?_⟩
    by_cases h0 : u e = 0
    · have : ¬ (e ∉ ω) := fun h => he ⟨fun _ => h, fun h1 => absurd (h0 ▸ h1 : (0 : unitInterval) = 1) zero_ne_one⟩
      exact Or.inl ⟨h0, not_not.1 this⟩
    · have : ¬ (u e = 1 → e ∈ ω) := fun h => he ⟨fun h' => absurd h' h0, h⟩
      rcases Classical.not_imp.1 this with ⟨h1, hn⟩
      exact Or.inr ⟨h1, hn⟩
  refine measure_mono_null hsub ((measure_iUnion_null_iff).2 fun e => ?_)
  refine (measure_union_null_iff).2 ⟨?_, ?_⟩
  · by_cases h0 : u e = 0
    · have h := Percolation.Literature.LatticeModels.prodBernoulli_real_setOf_mem u e
      rw [h0] at h
      have : (prodBernoulli u).real {ω : BondConfig V | u e = 0 ∧ e ∈ ω} = 0 := by
        rw [show {ω : BondConfig V | u e = 0 ∧ e ∈ ω} = {ω | e ∈ ω} by ext ω; simp [h0]]
        simpa using h
      exact (measureReal_eq_zero_iff (measure_ne_top _ _)).1 this
    · rw [show {ω : BondConfig V | u e = 0 ∧ e ∈ ω} = ∅ by ext ω; simp [h0]]
      exact measure_empty
  · by_cases h1 : u e = 1
    · have h := Percolation.Literature.LatticeModels.prodBernoulli_real_setOf_notMem u e
      rw [h1] at h
      have : (prodBernoulli u).real {ω : BondConfig V | u e = 1 ∧ e ∉ ω} = 0 := by
        rw [show {ω : BondConfig V | u e = 1 ∧ e ∉ ω} = {ω | e ∉ ω} by ext ω; simp [h1]]
        simpa using h
      exact (measureReal_eq_zero_iff (measure_ne_top _ _)).1 this
    · rw [show {ω : BondConfig V | u e = 1 ∧ e ∉ ω} = ∅ by ext ω; simp [h1]]
      exact measure_empty

/-- Events that agree on `sureSet u` have the same `prodBernoulli u`-probability. [folklore] -/
theorem real_eq_of_inter_sureSet (u : Sym2 V → unitInterval) {S S' : Set (BondConfig V)}
    (h : S ∩ sureSet u = S' ∩ sureSet u) :
    (prodBernoulli u).real S = (prodBernoulli u).real S' := by
  have h1 := measure_inter_conull (μ := prodBernoulli u) (s := S) (measure_compl_sureSet u)
  have h2 := measure_inter_conull (μ := prodBernoulli u) (s := S') (measure_compl_sureSet u)
  simp only [measureReal_def, ← h1, ← h2, h]

open TripodExchange TwoSetConditionalAssociation in
/-- [cite: VandenbergHaggstromKahn2005, Thm. 2.1 (p. 9) at q = 1, Remark 1 (p. 5); KozmaNitzan2024, Lemma 1 (pp. 5–6)] -/
theorem bhk_set_event_pos (w : Sym2 V → unitInterval) (S T : Set V)
    (P Q : Set (Sym2 V) → Set (Sym2 V) → Prop)
    (hP₁ : ∀ D ⦃C C'⦄, C ⊆ C' → P C D → P C' D) (hP₂ : ∀ C ⦃D D'⦄, D ⊆ D' → P C D' → P C D)
    (hQ₁ : ∀ D ⦃C C'⦄, C ⊆ C' → Q C D → Q C' D) (hQ₂ : ∀ C ⦃D D'⦄, D ⊆ D' → Q C D' → Q C D) :
    (prodBernoulli w).real ({ω : BondConfig V | ∀ s ∈ S, ∀ t ∈ T, ¬ (openGraph ω).Reachable s t} ∩
        {ω | P (⋃ s ∈ S, openEdgeCluster ω s) (⋃ t ∈ T, openEdgeCluster ω t)}) *
      (prodBernoulli w).real ({ω : BondConfig V | ∀ s ∈ S, ∀ t ∈ T, ¬ (openGraph ω).Reachable s t} ∩
        {ω | Q (⋃ s ∈ S, openEdgeCluster ω s) (⋃ t ∈ T, openEdgeCluster ω t)}) ≤
    (prodBernoulli w).real {ω : BondConfig V | ∀ s ∈ S, ∀ t ∈ T, ¬ (openGraph ω).Reachable s t} *
      (prodBernoulli w).real ({ω : BondConfig V | ∀ s ∈ S, ∀ t ∈ T, ¬ (openGraph ω).Reachable s t} ∩
        ({ω | P (⋃ s ∈ S, openEdgeCluster ω s) (⋃ t ∈ T, openEdgeCluster ω t)} ∩
         {ω | Q (⋃ s ∈ S, openEdgeCluster ω s) (⋃ t ∈ T, openEdgeCluster ω t)})) := by
  classical
  -- monotonicity of the two-valued gauge under an implication (inlined)
  have hind : ∀ {p q : Prop}, (p → q) → (if p then (1 : ℝ) else 0) ≤ (if q then 1 else 0) :=
    fun {p q} hpq => by
      by_cases hp : p
      · rw [if_pos hp, if_pos (hpq hp)]
      · rw [if_neg hp]; split_ifs <;> norm_num
  have key := BHK2006_twoSetConditionalAssociation w S T
    (fun C D => if P C D then (1 : ℝ) else 0) (fun C D => if Q C D then (1 : ℝ) else 0)
    (fun D _ _ h => hind (hP₁ D h)) (fun C _ _ h => hind (hP₂ C h))
    (fun D _ _ h => hind (hQ₁ D h)) (fun C _ _ h => hind (hQ₂ C h))
  simp only [predIndicator_eq_indicator
      (fun ω => P (⋃ s ∈ S, openEdgeCluster ω s) (⋃ t ∈ T, openEdgeCluster ω t)),
    predIndicator_eq_indicator
      (fun ω => Q (⋃ s ∈ S, openEdgeCluster ω s) (⋃ t ∈ T, openEdgeCluster ω t)),
    TripodExchange.setIntegral_indicator_one_eq, setIntegral_indicator_mul_indicator_eq] at key
  exact key

open TripodExchange TwoSetConditionalAssociation in
/-- **BHK 2006 with vertex sets, event form — negative correlation.** With `D, C_S, C_T` as above,
`P` increasing in `C_S` and decreasing in `C_T`, and `Q` DEcreasing in `C_S` and INcreasing in `C_T`:
`μ(D) μ(D ∩ P ∩ Q) ≤ μ(D ∩ P) μ(D ∩ Q)` ("the inequality is reversed if either `f` or `g` are
decreasing", KN p. 5; BHK Thm. 1.3 last sentence / Thm. 1.4), from the positive form applied to
`(1_P, −1_Q)`. [cite: VandenbergHaggstromKahn2005, Thms. 1.3–1.5 (pp. 6–7) with Remark 1 (p. 5); KozmaNitzan2024, Lemma 1 (pp. 5–6)] -/
theorem bhk_set_event_neg (w : Sym2 V → unitInterval) (S T : Set V)
    (P Q : Set (Sym2 V) → Set (Sym2 V) → Prop)
    (hP₁ : ∀ D ⦃C C'⦄, C ⊆ C' → P C D → P C' D) (hP₂ : ∀ C ⦃D D'⦄, D ⊆ D' → P C D' → P C D)
    (hQ₁ : ∀ D ⦃C C'⦄, C ⊆ C' → Q C' D → Q C D) (hQ₂ : ∀ C ⦃D D'⦄, D ⊆ D' → Q C D → Q C D') :
    (prodBernoulli w).real {ω : BondConfig V | ∀ s ∈ S, ∀ t ∈ T, ¬ (openGraph ω).Reachable s t} *
      (prodBernoulli w).real ({ω : BondConfig V | ∀ s ∈ S, ∀ t ∈ T, ¬ (openGraph ω).Reachable s t} ∩
        ({ω | P (⋃ s ∈ S, openEdgeCluster ω s) (⋃ t ∈ T, openEdgeCluster ω t)} ∩
         {ω | Q (⋃ s ∈ S, openEdgeCluster ω s) (⋃ t ∈ T, openEdgeCluster ω t)})) ≤
    (prodBernoulli w).real ({ω : BondConfig V | ∀ s ∈ S, ∀ t ∈ T, ¬ (openGraph ω).Reachable s t} ∩
        {ω | P (⋃ s ∈ S, openEdgeCluster ω s) (⋃ t ∈ T, openEdgeCluster ω t)}) *
      (prodBernoulli w).real ({ω : BondConfig V | ∀ s ∈ S, ∀ t ∈ T, ¬ (openGraph ω).Reachable s t} ∩
        {ω | Q (⋃ s ∈ S, openEdgeCluster ω s) (⋃ t ∈ T, openEdgeCluster ω t)}) := by
  classical
  -- monotonicity of the two-valued gauge under an implication (inlined)
  have hind : ∀ {p q : Prop}, (p → q) → (if p then (1 : ℝ) else 0) ≤ (if q then 1 else 0) :=
    fun {p q} hpq => by
      by_cases hp : p
      · rw [if_pos hp, if_pos (hpq hp)]
      · rw [if_neg hp]; split_ifs <;> norm_num
  have key := BHK2006_twoSetConditionalAssociation w S T
    (fun C D => if P C D then (1 : ℝ) else 0) (fun C D => -(if Q C D then (1 : ℝ) else 0))
    (fun D _ _ h => hind (hP₁ D h)) (fun C _ _ h => hind (hP₂ C h))
    (fun D _ _ h => neg_le_neg (hind (hQ₁ D h)))
    (fun C _ _ h => neg_le_neg (hind (hQ₂ C h)))
  simp only [predIndicator_eq_indicator
      (fun ω => P (⋃ s ∈ S, openEdgeCluster ω s) (⋃ t ∈ T, openEdgeCluster ω t)),
    predIndicator_eq_indicator
      (fun ω => Q (⋃ s ∈ S, openEdgeCluster ω s) (⋃ t ∈ T, openEdgeCluster ω t)),
    integral_neg, mul_neg, neg_le_neg_iff,
    TripodExchange.setIntegral_indicator_one_eq, setIntegral_indicator_mul_indicator_eq] at key
  exact key

end Measure

/-! ### Kozma–Nitzan, Lemma 4 and its gluing form (9) -/

section Lemma4

variable [Fintype V]

/-- The difference of the probabilities of two nested events. [folklore] -/
theorem real_diff_of_subset (μ : Measure (BondConfig V)) [IsFiniteMeasure μ]
    {A B : Set (BondConfig V)} (h : A ⊆ B) :
    μ.real B - μ.real A = μ.real (B \ A) := by
  classical
  have hBA : B = A ∪ (B \ A) := by rw [Set.union_sdiff_cancel h]
  have hd : Disjoint A (B \ A) := Set.disjoint_sdiff_right
  conv_lhs => rw [hBA, measureReal_union hd MeasurableSet.of_discrete]
  ring

/-- **Core of Lemma 4** (arXiv:2401.12397 p. 9, the displayed chain): if `a₂` minimises
`P(a_j ↔ b, a₃ ↔ {a₁,a₂})` over `j = 1, 2`, then
`P(a₁ ↔ b, a₁ ↮ a₂) ≥ P(a₁ ↔ b, a₂ ↔ a₃, a₁ ↮ a₂) + P(a₂ ↔ b, a₁ ↔ a₃, a₁ ↮ a₂)`.
Proof as printed: Theorem 1 with `0 := a₃`, `A = {a₁, a₂}` ( `KNPreFKG.preFKG_pair`), "subtract
`P(a₃ ↔ a₂ ↔ b)` from both sides", enlarge the left side, "add `P(a₁ ↔ b, a₂ ↔ a₃, a₁ ↮ a₂)` to both
sides". [cite: KozmaNitzan2024, Lemma 4 (p. 9, proof)] -/
theorem lemma4_core (u : Sym2 V → unitInterval) (a₁ a₂ a₃ b : V)
    (hmin : (prodBernoulli u).real ((openConn a₃ a₁ ∪ openConn a₃ a₂) ∩ openConn a₂ b) ≤
      (prodBernoulli u).real ((openConn a₃ a₁ ∪ openConn a₃ a₂) ∩ openConn a₁ b)) :
    (prodBernoulli u).real (openConn a₁ b ∩ openConn a₂ a₃ ∩ (openConn a₁ a₂)ᶜ) +
      (prodBernoulli u).real (openConn a₂ b ∩ openConn a₁ a₃ ∩ (openConn a₁ a₂)ᶜ) ≤
    (prodBernoulli u).real (openConn a₁ b ∩ (openConn a₁ a₂)ᶜ) := by
  classical
  set μ := prodBernoulli u with hμ
  have mem : ∀ (ω : BondConfig V) (x y : V),
      ω ∈ (openConn x y : Set (BondConfig V)) ↔ (openGraph ω).Reachable x y := fun _ _ _ => Iff.rfl
  -- Theorem 1 with `0 := a₃`, `A = {a₁, a₂}`
  have T1 := KNPreFKG.preFKG_pair u a₃ b a₁ a₂
  rw [min_eq_right hmin] at T1
  -- subtract the common event `{a₃ ↔ a₂ ↔ b}`
  set W : Set (BondConfig V) := openConn a₃ a₂ ∩ openConn a₂ b with hW
  have hW1 : W ⊆ openConn a₃ b ∩ (openConn a₃ a₁ ∪ openConn a₃ a₂) := by
    rintro ω ⟨h32, h2b⟩
    exact ⟨(h32.trans h2b : (openGraph ω).Reachable a₃ b), Or.inr h32⟩
  have hW2 : W ⊆ (openConn a₃ a₁ ∪ openConn a₃ a₂) ∩ openConn a₂ b := by
    rintro ω ⟨h32, h2b⟩
    exact ⟨Or.inr h32, h2b⟩
  have e1 : (openConn a₃ b ∩ (openConn a₃ a₁ ∪ openConn a₃ a₂)) \ W =
      (openConn a₁ b ∩ openConn a₁ a₃ ∩ (openConn a₁ a₂)ᶜ : Set (BondConfig V)) := by
    ext ω
    simp only [mem_sdiff, mem_inter_iff, mem_union, mem_compl_iff, mem, hW, not_and]
    constructor
    · rintro ⟨⟨h3b, h31 | h32⟩, hnot⟩
      · refine ⟨⟨h31.symm.trans h3b, h31.symm⟩, fun h12 => hnot (h31.trans h12) ((h31.trans h12).symm.trans h3b)⟩
      · exact absurd (h32.symm.trans h3b) (hnot h32)
    · rintro ⟨⟨h1b, h13⟩, hn12⟩
      exact ⟨⟨h13.symm.trans h1b, Or.inl h13.symm⟩, fun h32 _ => hn12 (h13.trans h32)⟩
  have e2 : ((openConn a₃ a₁ ∪ openConn a₃ a₂) ∩ openConn a₂ b) \ W =
      (openConn a₂ b ∩ openConn a₁ a₃ ∩ (openConn a₁ a₂)ᶜ : Set (BondConfig V)) := by
    ext ω
    simp only [mem_sdiff, mem_inter_iff, mem_union, mem_compl_iff, mem, hW, not_and]
    constructor
    · rintro ⟨⟨h31 | h32, h2b⟩, hnot⟩
      · exact ⟨⟨h2b, h31.symm⟩, fun h12 => hnot (h31.trans h12) h2b⟩
      · exact absurd h2b (hnot h32)
    · rintro ⟨⟨h2b, h13⟩, hn12⟩
      exact ⟨⟨Or.inl h13.symm, h2b⟩, fun h32 _ => hn12 (h13.trans h32)⟩
  have step1 : μ.real (openConn a₂ b ∩ openConn a₁ a₃ ∩ (openConn a₁ a₂)ᶜ) ≤
      μ.real (openConn a₁ b ∩ openConn a₁ a₃ ∩ (openConn a₁ a₂)ᶜ) := by
    rw [← e1, ← e2, ← real_diff_of_subset μ hW1, ← real_diff_of_subset μ hW2]
    linarith [T1]
  -- "Certainly, this implies `P(a₁ ↔ b, a₂ ↮ {a₁, a₃}) ≥ P(a₂ ↔ b, a₁ ↔ a₃, a₁ ↮ a₂)`"
  have step2 : μ.real (openConn a₁ b ∩ openConn a₁ a₃ ∩ (openConn a₁ a₂)ᶜ) ≤
      μ.real (openConn a₁ b ∩ (openConn a₁ a₂)ᶜ ∩ (openConn a₂ a₃)ᶜ) := by
    refine measureReal_mono ?_
    rintro ω ⟨⟨h1b, h13⟩, hn12⟩
    exact ⟨⟨h1b, hn12⟩, fun h23 => hn12 ((h13.trans h23.symm : (openGraph ω).Reachable a₁ a₂))⟩
  -- "We add `P(a₁ ↔ b, a₂ ↔ a₃, a₁ ↮ a₂)` to both sides"
  have split : μ.real (openConn a₁ b ∩ (openConn a₁ a₂)ᶜ) =
      μ.real (openConn a₁ b ∩ (openConn a₁ a₂)ᶜ ∩ (openConn a₂ a₃)ᶜ) +
        μ.real (openConn a₁ b ∩ openConn a₂ a₃ ∩ (openConn a₁ a₂)ᶜ) := by
    rw [← measureReal_union _ MeasurableSet.of_discrete]
    · congr 1
      ext ω
      simp only [mem_inter_iff, mem_compl_iff, mem_union, mem]
      tauto
    · exact Set.disjoint_left.2 fun ω ⟨_, h⟩ ⟨⟨_, h'⟩, _⟩ => h h'
  linarith [step1, step2, split]

/-- **Kozma–Nitzan 2024, Lemma 4** (arXiv:2401.12397 p. 9): "Let `G` be a graph and `a₁, a₂, a₃, b ∈ G`.
Then `max_{j=1,2} P({a₁,a₂} is pivotal for a_j ↔ b) ≥ P({a₁,a₂} is pivotal for a₃ ↔ b). (8)`"
Transcription: for the increasing event `{x ↔ b}` and the pair `e = s(a₁,a₂)`, "`e` is pivotal and
closed" is the event `{x ↮ b in ω, x ↔ b in ω ∪ {e}}` (for `ω ∌ e` this is KN's "`e` is pivotal", p. 5;
the state of `e` itself is independent of pivotality, so (8) for these events is (8) as printed
whenever `u e < 1`, and both sides vanish when `u e = 1`).  Proved, for the percolation measure
`prodBernoulli u` of an arbitrary weight function on a finite vertex type, from Theorem 1
(`lemma4_core` and its mirror image under `a₁ ↔ a₂`).
[cite: KozmaNitzan2024, Lemma 4 (p. 9)] -/
theorem _root_.Percolation.Literature.KozmaNitzan2024_lemma4 (u : Sym2 V → unitInterval)
    (a₁ a₂ a₃ b : V) :
    (prodBernoulli u).real {ω : BondConfig V | ¬ (openGraph ω).Reachable a₃ b ∧
        (openGraph (insert s(a₁, a₂) ω)).Reachable a₃ b} ≤
      max ((prodBernoulli u).real {ω : BondConfig V | ¬ (openGraph ω).Reachable a₁ b ∧
            (openGraph (insert s(a₁, a₂) ω)).Reachable a₁ b})
        ((prodBernoulli u).real {ω : BondConfig V | ¬ (openGraph ω).Reachable a₂ b ∧
            (openGraph (insert s(a₁, a₂) ω)).Reachable a₂ b}) := by
  classical
  set μ := prodBernoulli u with hμ
  have mem : ∀ (ω : BondConfig V) (x y : V),
      ω ∈ (openConn x y : Set (BondConfig V)) ↔ (openGraph ω).Reachable x y := fun _ _ _ => Iff.rfl
  -- the three "pivotal" events in closed form (`reachable_insert_iff`)
  have piv3 : {ω : BondConfig V | ¬ (openGraph ω).Reachable a₃ b ∧
        (openGraph (insert s(a₁, a₂) ω)).Reachable a₃ b} =
      (openConn a₂ b ∩ openConn a₁ a₃ ∩ (openConn a₁ a₂)ᶜ) ∪
        (openConn a₁ b ∩ openConn a₂ a₃ ∩ (openConn a₁ a₂)ᶜ) := by
    ext ω
    simp only [mem_setOf_eq, reachable_insert_iff, mem_union, mem_inter_iff, mem_compl_iff, mem]
    constructor
    · rintro ⟨hn3b, h3b | ⟨h31, h2b⟩ | ⟨h32, h1b⟩⟩
      · exact absurd h3b hn3b
      · exact Or.inl ⟨⟨h2b, h31.symm⟩, fun h12 => hn3b ((h31.trans h12).trans h2b)⟩
      · exact Or.inr ⟨⟨h1b, h32.symm⟩, fun h12 => hn3b ((h32.trans h12.symm).trans h1b)⟩
    · rintro (⟨⟨h2b, h13⟩, hn12⟩ | ⟨⟨h1b, h23⟩, hn12⟩)
      · exact ⟨fun h3b => hn12 ((h13.trans h3b).trans h2b.symm), Or.inr (Or.inl ⟨h13.symm, h2b⟩)⟩
      · exact ⟨fun h3b => hn12 ((h1b.trans h3b.symm).trans h23.symm), Or.inr (Or.inr ⟨h23.symm, h1b⟩)⟩
  have hdisj : Disjoint (openConn a₂ b ∩ openConn a₁ a₃ ∩ (openConn a₁ a₂)ᶜ : Set (BondConfig V))
      (openConn a₁ b ∩ openConn a₂ a₃ ∩ (openConn a₁ a₂)ᶜ) := by
    refine Set.disjoint_left.2 ?_
    rintro ω ⟨⟨h2b, h13⟩, hn12⟩ ⟨⟨h1b, _⟩, _⟩
    exact hn12 ((h1b.trans h2b.symm : (openGraph ω).Reachable a₁ a₂))
  have piv1 : {ω : BondConfig V | ¬ (openGraph ω).Reachable a₁ b ∧
        (openGraph (insert s(a₁, a₂) ω)).Reachable a₁ b} = openConn a₂ b ∩ (openConn a₁ a₂)ᶜ := by
    ext ω
    simp only [mem_setOf_eq, reachable_insert_iff, mem_inter_iff, mem_compl_iff, mem]
    constructor
    · rintro ⟨hn1b, h1b | ⟨_, h2b⟩ | ⟨h12, h1b⟩⟩
      · exact absurd h1b hn1b
      · exact ⟨h2b, fun h12 => hn1b (h12.trans h2b)⟩
      · exact absurd h1b hn1b
    · rintro ⟨h2b, hn12⟩
      exact ⟨fun h1b => hn12 (h1b.trans h2b.symm), Or.inr (Or.inl ⟨SimpleGraph.Reachable.refl _, h2b⟩)⟩
  have piv2 : {ω : BondConfig V | ¬ (openGraph ω).Reachable a₂ b ∧
        (openGraph (insert s(a₁, a₂) ω)).Reachable a₂ b} = openConn a₁ b ∩ (openConn a₁ a₂)ᶜ := by
    ext ω
    simp only [mem_setOf_eq, reachable_insert_iff, mem_inter_iff, mem_compl_iff, mem]
    constructor
    · rintro ⟨hn2b, h2b | ⟨h21, h2b⟩ | ⟨_, h1b⟩⟩
      · exact absurd h2b hn2b
      · exact absurd h2b hn2b
      · exact ⟨h1b, fun h12 => hn2b (h12.symm.trans h1b)⟩
    · rintro ⟨h1b, hn12⟩
      exact ⟨fun h2b => hn12 (h1b.trans h2b.symm), Or.inr (Or.inr ⟨SimpleGraph.Reachable.refl _, h1b⟩)⟩
  rw [piv3, piv1, piv2, measureReal_union hdisj MeasurableSet.of_discrete]
  -- "without loss of generality we may assume that `a₂` is the one that minimises `P(a_j ↔ b, a₃ ↔ {a₁,a₂})`"
  rcases le_total (μ.real ((openConn a₃ a₁ ∪ openConn a₃ a₂) ∩ openConn a₂ b))
      (μ.real ((openConn a₃ a₁ ∪ openConn a₃ a₂) ∩ openConn a₁ b)) with h | h
  · refine le_trans ?_ (le_max_right _ _)
    have := lemma4_core u a₁ a₂ a₃ b h
    linarith
  · refine le_trans ?_ (le_max_left _ _)
    have key := lemma4_core u a₂ a₁ a₃ b (by rwa [Set.union_comm])
    have e12 : (openConn a₂ a₁ : Set (BondConfig V)) = openConn a₁ a₂ := by
      ext ω; exact ⟨fun h => SimpleGraph.Reachable.symm h, fun h => SimpleGraph.Reachable.symm h⟩
    rw [e12] at key
    linarith

/-- **Lemma 4 in the gluing form (9)** (arXiv:2401.12397, Remark on pp. 9–10): "For a graph `G` and an
edge `e` denote by `G/e` the graph one gets by gluing the two vertices of the edge `e` … Denote
`G* = G/{a₁, a₂}`. It is not difficult to see that (8) can be reformulated as
`P_{G*}({a₁,a₂} ↔ b) − P_{G*}(a₃ ↔ b) ≥ min_{j=1,2} P_G(a_j ↔ b) − P_G(a₃ ↔ b). (9)`"
Transcription: gluing `a₁` and `a₂` is realised, for connection events, by giving the pair `s(a₁,a₂)`
the weight `1` (it is then almost surely open): `G*` has the weight function
`Function.update u s(a₁,a₂) 1`, and `{a₁,a₂} ↔ b` in `G*` is `a₁ ↔ b` there.  Proved from Lemma 4:
`P_{G*}(x ↔ b) − P_G(x ↔ b) = P_G(e pivotal and closed for x ↔ b)` (locality of `prodBernoulli` off
`e` and `reachable_insert_iff`). [cite: KozmaNitzan2024, Lemma 4, eq. (9) (pp. 9–10)] -/
theorem _root_.Percolation.Literature.KozmaNitzan2024_lemma4_glued [DecidableEq V]
    (u : Sym2 V → unitInterval) (a₁ a₂ a₃ b : V) :
    min ((prodBernoulli u).real (openConn a₁ b) - (prodBernoulli u).real (openConn a₃ b))
        ((prodBernoulli u).real (openConn a₂ b) - (prodBernoulli u).real (openConn a₃ b)) ≤
      (prodBernoulli (Function.update u s(a₁, a₂) 1)).real (openConn a₁ b) -
        (prodBernoulli (Function.update u s(a₁, a₂) 1)).real (openConn a₃ b) := by
  classical
  set e : Sym2 V := s(a₁, a₂) with he
  set μ := prodBernoulli u with hμ
  set μ' := prodBernoulli (Function.update u e 1) with hμ'
  -- `P_{G*}(x ↔ b) = P_G(x ↔ b in ω ∪ {e})`
  have glue : ∀ x : V, μ'.real (openConn x b) =
      μ.real {ω : BondConfig V | (openGraph (insert e ω)).Reachable x b} := by
    intro x
    have hdet : DeterminedBy {ω : BondConfig V | (openGraph (insert e ω)).Reachable x b} ({e}ᶜ : Set (Sym2 V)) := by
      have : {ω : BondConfig V | (openGraph (insert e ω)).Reachable x b} =
          {ω | (openGraph (insert e (ω ∩ {e}ᶜ))).Reachable x b} := by
        ext ω
        have : insert e (ω ∩ {e}ᶜ) = insert e ω := by
          ext f; by_cases hf : f = e <;> simp [hf]
        simp only [mem_setOf_eq, this]
      rw [this]
      exact determinedBy_setOf_inter _ (fun η => (openGraph (insert e η)).Reachable x b)
    rw [real_eq_of_agree u (Function.update u e 1) ({e}ᶜ : Set (Sym2 V))
      (fun f hf => by rw [Function.update_of_ne (fun h => hf h)]) hdet]
    refine real_eq_of_inter_sureSet (Function.update u e 1) ?_
    ext ω
    simp only [mem_inter_iff, mem_setOf_eq, sureSet]
    constructor
    · rintro ⟨h, hs⟩
      have heω : e ∈ ω := (hs e).2 (by simp)
      rw [Set.insert_eq_of_mem heω]
      exact ⟨h, hs⟩
    · rintro ⟨h, hs⟩
      have heω : e ∈ ω := (hs e).2 (by simp)
      rw [Set.insert_eq_of_mem heω] at h
      exact ⟨h, hs⟩
  -- `P_{G*}(x ↔ b) − P_G(x ↔ b) = P_G(e pivotal and closed for x ↔ b)`
  have diff : ∀ x : V, μ'.real (openConn x b) - μ.real (openConn x b) =
      μ.real {ω : BondConfig V | ¬ (openGraph ω).Reachable x b ∧ (openGraph (insert e ω)).Reachable x b} := by
    intro x
    rw [glue x, real_diff_of_subset μ (show (openConn x b : Set (BondConfig V)) ⊆
      {ω : BondConfig V | (openGraph (insert e ω)).Reachable x b} from
        fun ω h => h.mono (openGraph_mono (Set.subset_insert _ _)))]
    congr 1
    ext ω
    simp only [mem_sdiff, mem_setOf_eq, openConn]
    tauto
  -- in `G*` the vertices `a₁, a₂` are glued: `P_{G*}(a₁ ↔ b) = P_{G*}(a₂ ↔ b)`
  have same : μ'.real (openConn a₁ b) = μ'.real (openConn a₂ b) := by
    rw [glue a₁, glue a₂]
    congr 1
    ext ω
    simp only [mem_setOf_eq]
    have h12 : (openGraph (insert e ω)).Reachable a₁ a₂ := by
      by_cases h : a₁ = a₂
      · rw [h]
      · exact SimpleGraph.Adj.reachable ((openGraph_adj _ a₁ a₂).2 ⟨by rw [he]; exact Set.mem_insert _ _, h⟩)
    exact ⟨fun h => h12.symm.trans h, fun h => h12.trans h⟩
  have L4 := KozmaNitzan2024_lemma4 u a₁ a₂ a₃ b
  rw [← he, ← diff a₁, ← diff a₂, ← diff a₃] at L4
  rcases le_max_iff.1 L4 with h | h
  · refine (min_le_left _ _).trans ?_; linarith
  · refine (min_le_right _ _).trans ?_; linarith

end Lemma4

/-! ### The two sides of a separating set: `B`-connectivity, glued `T`-connectivity, amalgamation -/

section Sides

variable (VB A : Set V)

/-- The pairs of the `B`-side: both endpoints in `VB ∪ A` (KN p. 10: "`B` … the component of `0`, the
vertices of `A` and the edges between them"). [cite: KozmaNitzan2024, proof of Thm. 3 (p. 10)] -/
def sideB : Set (Sym2 V) := {e | ∀ v ∈ e, v ∈ VB ∨ v ∈ A}

/-- The pairs of the `T`-side: both endpoints off `VB` and not both in `A` (KN p. 10: "`T` … the union
of all connected components which do not contain `0`, including the vertices in `A` but not the edges
between them"). [cite: KozmaNitzan2024, proof of Thm. 3 (p. 10)] -/
def sideT : Set (Sym2 V) := {e | (∀ v ∈ e, v ∉ VB) ∧ ¬ (∀ v ∈ e, v ∈ A)}

/-- `B`-connectivity: an open path using only pairs of the `B`-side (KN's `x ↔ y` "in `B`", `P_B`).
[cite: KozmaNitzan2024, proof of Thm. 3 (p. 10)] -/
def rB (ω : BondConfig V) (x y : V) : Prop := (openGraph (ω ∩ sideB VB A)).Reachable x y

/-- The pairs of `A` glued by the `B`-side of `ω`: non-loop pairs inside `A` whose endpoints are
`B`-connected (KN's "connection patterns in `B`", p. 10). [cite: KozmaNitzan2024, proof of Thm. 3 (pp. 10–11)] -/
def glueSet (ω : BondConfig V) : Set (Sym2 V) :=
  {e | (∀ v ∈ e, v ∈ A) ∧ ¬ e.IsDiag ∧ ∀ v ∈ e, ∀ v' ∈ e, rB VB A ω v v'}

/-- Glued `T`-connectivity: an open path using pairs of the `T`-side and the virtual edges `F`
(for `F = {s(a_j,a_k)}` this is connectivity in KN's glued graph `T^{(jk)} = T/{a_j,a_k}`, p. 10).
[cite: KozmaNitzan2024, proof of Thm. 3 (p. 10)] -/
def rT (F : Set (Sym2 V)) (ω : BondConfig V) (x y : V) : Prop :=
  (openGraph (ω ∩ sideT VB A ∪ F)).Reachable x y

/-- A configuration with no open pair joining the interior of the `B`-side to the interior of the
`T`-side. [folklore] -/
def noCross (ω : BondConfig V) : Prop := ∀ e ∈ ω, e ∈ sideB VB A ∨ e ∈ sideT VB A

variable {VB A}

/-- `B`-connectivity is reflexive. [folklore] -/
theorem rB_refl (ω : BondConfig V) (x : V) : rB VB A ω x x := SimpleGraph.Reachable.refl x

/-- `B`-connectivity is symmetric. [folklore] -/
theorem rB.symm {ω : BondConfig V} {x y : V} (h : rB VB A ω x y) : rB VB A ω y x :=
  SimpleGraph.Reachable.symm h

/-- `B`-connectivity is transitive. [folklore] -/
theorem rB.trans {ω : BondConfig V} {x y z : V} (h : rB VB A ω x y) (h' : rB VB A ω y z) :
    rB VB A ω x z := SimpleGraph.Reachable.trans h h'

/-- Glued `T`-connectivity is reflexive. [folklore] -/
theorem rT_refl (F : Set (Sym2 V)) (ω : BondConfig V) (x : V) : rT VB A F ω x x :=
  SimpleGraph.Reachable.refl x

/-- Glued `T`-connectivity is transitive. [folklore] -/
theorem rT.trans {F : Set (Sym2 V)} {ω : BondConfig V} {x y z : V} (h : rT VB A F ω x y)
    (h' : rT VB A F ω y z) : rT VB A F ω x z := SimpleGraph.Reachable.trans h h'

/-- `B`-connectivity implies connectivity. [folklore] -/
theorem rB.reachable {ω : BondConfig V} {x y : V} (h : rB VB A ω x y) : (openGraph ω).Reachable x y :=
  h.mono (openGraph_mono Set.inter_subset_left)

/-- Membership in the glue set of a pair `s(x,y)`. [folklore] -/
theorem mk_mem_glueSet_iff (ω : BondConfig V) (x y : V) :
    s(x, y) ∈ glueSet VB A ω ↔ x ∈ A ∧ y ∈ A ∧ x ≠ y ∧ rB VB A ω x y := by
  simp only [glueSet, mem_setOf_eq, Sym2.mem_iff, Sym2.mk_isDiag_iff]
  constructor
  · rintro ⟨hA, hne, hr⟩
    exact ⟨hA x (Or.inl rfl), hA y (Or.inr rfl), hne, hr x (Or.inl rfl) y (Or.inr rfl)⟩
  · rintro ⟨hx, hy, hne, hr⟩
    refine ⟨?_, hne, ?_⟩
    · rintro v (rfl | rfl) <;> assumption
    · rintro v (rfl | rfl) v' (rfl | rfl)
      exacts [rB_refl ω _, hr, hr.symm, rB_refl ω _]

/-- Two distinct `B`-connected vertices of `A` are adjacent by a virtual edge, hence glued-`T`-connected.
[folklore] -/
theorem rT_of_rB {ω : BondConfig V} {x y : V} (hx : x ∈ A) (hy : y ∈ A) (h : rB VB A ω x y) :
    rT VB A (glueSet VB A ω) ω x y := by
  by_cases hxy : x = y
  · subst hxy; exact rT_refl _ ω x
  · refine SimpleGraph.Adj.reachable ((openGraph_adj _ x y).2 ⟨Or.inr ?_, hxy⟩)
    exact (mk_mem_glueSet_iff ω x y).2 ⟨hx, hy, hxy, h⟩

/-- Glued `T`-connectivity (with the glue set of `ω` itself) implies connectivity. [folklore] -/
theorem rT_glueSet_reachable {ω : BondConfig V} {x y : V} (h : rT VB A (glueSet VB A ω) ω x y) :
    (openGraph ω).Reachable x y := by
  refine reachable_of_adj_reachable (fun u v huv => ?_) h
  rcases (openGraph_adj _ u v).1 huv with ⟨hmem | hmem, hne⟩
  · exact SimpleGraph.Adj.reachable ((openGraph_adj ω u v).2 ⟨hmem.1, hne⟩)
  · exact ((mk_mem_glueSet_iff ω u v).1 hmem).2.2.2.reachable

/-- An open pair of a configuration without cross pairs lies in the `B`-side or in the `T`-side, and
accordingly its endpoints are `B`-connected or glued-`T`-connected. [folklore] -/
theorem step_cases {ω : BondConfig V} (hω : noCross VB A ω) {y z : V} (hyz : (openGraph ω).Adj y z) :
    ((y ∈ VB ∨ y ∈ A) ∧ (z ∈ VB ∨ z ∈ A) ∧ rB VB A ω y z) ∨
      (y ∉ VB ∧ z ∉ VB ∧ ∀ F, rT VB A F ω y z) := by
  rcases (openGraph_adj ω y z).1 hyz with ⟨hmem, hne⟩
  rcases hω _ hmem with hB | hT
  · refine Or.inl ⟨hB y (by simp), hB z (by simp), ?_⟩
    exact SimpleGraph.Adj.reachable ((openGraph_adj _ y z).2 ⟨⟨hmem, hB⟩, hne⟩)
  · refine Or.inr ⟨hT.1 y (by simp), hT.1 z (by simp), fun F => ?_⟩
    exact SimpleGraph.Adj.reachable ((openGraph_adj _ y z).2 ⟨Or.inl ⟨hmem, hT⟩, hne⟩)

/-- **Amalgamation along a separating set** (the combinatorial content of "break according to the
connection patterns in `B`", KN pp. 10–11).  In a configuration without cross pairs write `g` for glued `T`-connectivity with the glue set of `ω`.  Then for every `x, z`:
(1) `x, z ∉ VB`: `x ↔ z` implies `g x z`; (2) `x ∉ VB`, `z ∈ VB`: `x ↔ z` implies `g x a`, `a ↔_B z`
for some `a ∈ A`; (3) `x ∈ VB`, `z ∉ VB`: `x ↔ z` implies `x ↔_B a`, `g a z` for some `a ∈ A`;
(4) `x, z ∈ VB`: `x ↔ z` implies `x ↔_B z` or `x ↔_B a`, `g a a'`, `a' ↔_B z` for some `a, a' ∈ A`.
(Induction along the open path.) [cite: KozmaNitzan2024, proof of Thm. 3 (pp. 10–11)] -/
theorem amalgam {ω : BondConfig V} (hω : noCross VB A ω) {x z : V}
    (hxz : (openGraph ω).Reachable x z) :
    (x ∉ VB → z ∉ VB → rT VB A (glueSet VB A ω) ω x z) ∧
    (x ∉ VB → z ∈ VB → ∃ a ∈ A, rT VB A (glueSet VB A ω) ω x a ∧ rB VB A ω a z) ∧
    (x ∈ VB → z ∉ VB → ∃ a ∈ A, rB VB A ω x a ∧ rT VB A (glueSet VB A ω) ω a z) ∧
    (x ∈ VB → z ∈ VB → rB VB A ω x z ∨
      ∃ a ∈ A, ∃ a' ∈ A, rB VB A ω x a ∧ rT VB A (glueSet VB A ω) ω a a' ∧ rB VB A ω a' z) := by
  set g := rT VB A (glueSet VB A ω) ω with hg
  -- two vertices of `A` that are `B`-connected are `g`-connected
  have gA : ∀ {a a' : V}, a ∈ A → a' ∈ A → rB VB A ω a a' → g a a' := fun ha ha' h => rT_of_rB ha ha' h
  rw [SimpleGraph.reachable_iff_reflTransGen] at hxz
  induction hxz with
  | refl =>
    exact ⟨fun _ _ => rT_refl _ ω x, fun h h' => absurd h' h, fun h h' => absurd h h',
      fun _ _ => Or.inl (rB_refl ω x)⟩
  | tail hxy hadj ih =>
    rename_i y z
    obtain ⟨ih1, ih2, ih3, ih4⟩ := ih
    rcases step_cases hω hadj with ⟨hyBA, hzBA, hByz⟩ | ⟨hyT, hzT, hTyz⟩
    · -- the step `y — z` is inside the `B`-side
      refine ⟨fun hx hz => ?_, fun hx hz => ?_, fun hx hz => ?_, fun hx hz => ?_⟩
      · -- (1) `x, z ∉ VB`, so `z ∈ A`
        have hzA : z ∈ A := hzBA.resolve_left hz
        by_cases hy : y ∈ VB
        · obtain ⟨a, ha, hxa, hay⟩ := ih2 hx hy
          exact hxa.trans (gA ha hzA (hay.trans hByz))
        · have hyA : y ∈ A := hyBA.resolve_left hy
          exact (ih1 hx hy).trans (gA hyA hzA hByz)
      · -- (2) `x ∉ VB`, `z ∈ VB`
        by_cases hy : y ∈ VB
        · obtain ⟨a, ha, hxa, hay⟩ := ih2 hx hy
          exact ⟨a, ha, hxa, hay.trans hByz⟩
        · have hyA : y ∈ A := hyBA.resolve_left hy
          exact ⟨y, hyA, ih1 hx hy, hByz⟩
      · -- (3) `x ∈ VB`, `z ∉ VB`, so `z ∈ A`
        have hzA : z ∈ A := hzBA.resolve_left hz
        by_cases hy : y ∈ VB
        · rcases ih4 hx hy with hxy | ⟨a, ha, a', ha', hxa, haa', ha'y⟩
          · exact ⟨z, hzA, hxy.trans hByz, rT_refl _ ω z⟩
          · exact ⟨a, ha, hxa, haa'.trans (gA ha' hzA (ha'y.trans hByz))⟩
        · have hyA : y ∈ A := hyBA.resolve_left hy
          obtain ⟨a, ha, hxa, hay⟩ := ih3 hx hy
          exact ⟨a, ha, hxa, hay.trans (gA hyA hzA hByz)⟩
      · -- (4) `x, z ∈ VB`
        by_cases hy : y ∈ VB
        · rcases ih4 hx hy with hxy | ⟨a, ha, a', ha', hxa, haa', ha'y⟩
          · exact Or.inl (hxy.trans hByz)
          · exact Or.inr ⟨a, ha, a', ha', hxa, haa', ha'y.trans hByz⟩
        · have hyA : y ∈ A := hyBA.resolve_left hy
          obtain ⟨a, ha, hxa, hay⟩ := ih3 hx hy
          exact Or.inr ⟨a, ha, y, hyA, hxa, hay, hByz⟩
    · -- the step `y — z` is inside the `T`-side: `y, z ∉ VB`
      have hTyz' : g y z := hTyz _
      refine ⟨fun hx _ => (ih1 hx hyT).trans hTyz', fun _ hz => absurd hz hzT,
        fun hx _ => ?_, fun _ hz => absurd hz hzT⟩
      obtain ⟨a, ha, hxa, hay⟩ := ih3 hx hyT
      exact ⟨a, ha, hxa, hay.trans hTyz'⟩

/-- **(R1)** For `x, y` off the interior of the `B`-side, `x ↔ y` in `ω` iff `x ↔ y` in the glued
`T`-side. [cite: KozmaNitzan2024, proof of Thm. 3 (pp. 10–11)] -/
theorem reachable_iff_rT {ω : BondConfig V} (hω : noCross VB A ω) {x y : V}
    (hx : x ∉ VB) (hy : y ∉ VB) :
    (openGraph ω).Reachable x y ↔ rT VB A (glueSet VB A ω) ω x y :=
  ⟨fun h => (amalgam hω h).1 hx hy, rT_glueSet_reachable⟩

/-- **(R2)** For `o` in the interior of the `B`-side and `y` off it, `o ↔ y` in `ω` iff `o ↔_B a` and
`a ↔ y` in the glued `T`-side for some `a ∈ A`. [cite: KozmaNitzan2024, proof of Thm. 3 (p. 11)] -/
theorem reachable_iff_exists_rB_rT {ω : BondConfig V} (hω : noCross VB A ω)
    {o y : V} (ho : o ∈ VB) (hy : y ∉ VB) :
    (openGraph ω).Reachable o y ↔ ∃ a ∈ A, rB VB A ω o a ∧ rT VB A (glueSet VB A ω) ω a y :=
  ⟨fun h => (amalgam hω h).2.2.1 ho hy,
    fun ⟨_, _, hoa, hay⟩ => hoa.reachable.trans (rT_glueSet_reachable hay)⟩

end Sides

/-! ### The data of Theorem 3 and the two auxiliary percolation models `B` and `T^{(F)}` -/

/-- **The setting of the proof of Theorem 3** (KN p. 10): a weight function `w`, the interior `VB` of
the `B`-side containing `0 = o`, the three points `a₁, a₂, a₃` of `A` and the target `b` off `VB`, and
separation: every pair joining `VB` to the complement of `VB ∪ A` has weight `0` ("removing `A`
separates `G` into connected components, and `0` and `b` are in different components").
[cite: KozmaNitzan2024, Thm. 3 and its proof (p. 10)] -/
structure SepData (V : Type*) where
  /-- the edge probabilities -/
  w : Sym2 V → unitInterval
  /-- the interior of the `B`-side (contains `0`, misses `A` and `b`) -/
  VB : Set V
  /-- the observer `0` -/
  o : V
  /-- the target vertex -/
  b : V
  /-- the three points of `A` -/
  a₁ : V
  a₂ : V
  a₃ : V
  ho : o ∈ VB
  hb : b ∉ VB
  ha₁ : a₁ ∉ VB
  ha₂ : a₂ ∉ VB
  ha₃ : a₃ ∉ VB
  h₁₂ : a₁ ≠ a₂
  h₁₃ : a₁ ≠ a₃
  h₂₃ : a₂ ≠ a₃
  hb₁ : b ≠ a₁
  hb₂ : b ≠ a₂
  hb₃ : b ≠ a₃
  /-- separation: no positive weight across -/
  hcut : ∀ e, e ∉ sideB VB ({a₁, a₂, a₃} : Set V) → e ∉ sideT VB ({a₁, a₂, a₃} : Set V) → w e = 0

namespace SepData

variable (S : SepData V)

/-- The separating set `A = {a₁, a₂, a₃}`. [cite: KozmaNitzan2024, Thm. 3 (p. 10)] -/
def A : Set V := {S.a₁, S.a₂, S.a₃}

/-- The `B`-side pairs. [cite: KozmaNitzan2024, proof of Thm. 3 (p. 10)] -/
def EB : Set (Sym2 V) := sideB S.VB S.A

/-- The `T`-side pairs. [cite: KozmaNitzan2024, proof of Thm. 3 (p. 10)] -/
def ET : Set (Sym2 V) := sideT S.VB S.A

/-- `a₁ ∈ A`. [folklore] -/
theorem a₁_mem : S.a₁ ∈ S.A := by simp [A]
/-- `a₂ ∈ A`. [folklore] -/
theorem a₂_mem : S.a₂ ∈ S.A := by simp [A]
/-- `a₃ ∈ A`. [folklore] -/
theorem a₃_mem : S.a₃ ∈ S.A := by simp [A]
/-- `A` misses the interior of the `B`-side. [folklore] -/
theorem notMem_VB_of_mem_A {a : V} (ha : a ∈ S.A) : a ∉ S.VB := by
  simp only [A, mem_insert_iff, mem_singleton_iff] at ha
  rcases ha with rfl | rfl | rfl
  exacts [S.ha₁, S.ha₂, S.ha₃]

/-- The two sides are disjoint families of pairs. [folklore] -/
theorem not_mem_EB_of_mem_ET {e : Sym2 V} (he : e ∈ S.ET) : e ∉ S.EB := by
  intro hB
  refine he.2 fun v hv => ?_
  rcases hB v hv with h | h
  · exact absurd h (he.1 v hv)
  · exact h

/-- The `T`-side pairs lie off the `B`-side pairs. [folklore] -/
theorem ET_subset_compl : S.ET ⊆ S.EBᶜ := fun _ he => S.not_mem_EB_of_mem_ET he

/-- `B`-connectivity of the setting. [cite: KozmaNitzan2024, proof of Thm. 3 (p. 10)] -/
def rb (ω : BondConfig V) (x y : V) : Prop := rB S.VB S.A ω x y

/-- Glued `T`-connectivity of the setting. [cite: KozmaNitzan2024, proof of Thm. 3 (p. 10)] -/
def rt (F : Set (Sym2 V)) (ω : BondConfig V) (x y : V) : Prop := rT S.VB S.A F ω x y

/-- `B`-connectivity reads only the `B`-side pairs. [folklore] -/
theorem rb_eq_of_inter_eq {ω ω' : BondConfig V} (h : ω ∩ S.EB = ω' ∩ S.EB) : S.rb ω = S.rb ω' := by
  funext x y
  simp only [rb, rB]
  rw [show ω ∩ sideB S.VB S.A = ω' ∩ sideB S.VB S.A from h]

/-- Glued `T`-connectivity reads only the `T`-side pairs. [folklore] -/
theorem rt_eq_of_inter_eq {F : Set (Sym2 V)} {ω ω' : BondConfig V} (h : ω ∩ S.ET = ω' ∩ S.ET) :
    S.rt F ω = S.rt F ω' := by
  funext x y
  simp only [rt, rT]
  rw [show ω ∩ sideT S.VB S.A = ω' ∩ sideT S.VB S.A from h]

/-! #### Almost surely there are no cross pairs -/

/-- On `sureSet w` no cross pair is open: cross pairs have weight `0`. [cite: KozmaNitzan2024, proof of Thm. 3 (p. 10: "removing A separates G")] -/
theorem sureSet_subset_noCross : sureSet S.w ⊆ {ω | noCross S.VB S.A ω} := by
  intro ω hω e he
  by_contra h
  rw [not_or] at h
  exact (hω e).1 (S.hcut e h.1 h.2) he

/-! #### Events read on one side -/

/-- An event reading the configuration through `B`-connectivity is determined by the `B`-side pairs. [folklore] -/
theorem determinedBy_rb (Φ : (V → V → Prop) → Prop) : DeterminedBy {ω | Φ (S.rb ω)} S.EB := by
  rw [determinedBy_iff]
  intro ω ω' h
  simp only [mem_setOf_eq, S.rb_eq_of_inter_eq h]

/-- An event reading the configuration through glued `T`-connectivity (with a fixed glue set) is
determined by the complement of the `B`-side pairs. [folklore] -/
theorem determinedBy_rt (F : Set (Sym2 V)) (Ψ : (V → V → Prop) → Prop) :
    DeterminedBy {ω | Ψ (S.rt F ω)} S.EBᶜ := by
  rw [determinedBy_iff]
  intro ω ω' h
  have : ω ∩ S.ET = ω' ∩ S.ET := by
    have h1 : ω ∩ S.ET = (ω ∩ S.EBᶜ) ∩ S.ET := by
      rw [Set.inter_assoc, Set.inter_eq_self_of_subset_right S.ET_subset_compl]
    have h2 : ω' ∩ S.ET = (ω' ∩ S.EBᶜ) ∩ S.ET := by
      rw [Set.inter_assoc, Set.inter_eq_self_of_subset_right S.ET_subset_compl]
    rw [h1, h2, h]
  simp only [mem_setOf_eq, S.rt_eq_of_inter_eq this]

/-- Same, determined by the `T`-side pairs. [folklore] -/
theorem determinedBy_rt' (F : Set (Sym2 V)) (Ψ : (V → V → Prop) → Prop) :
    DeterminedBy {ω | Ψ (S.rt F ω)} S.ET := by
  rw [determinedBy_iff]
  intro ω ω' h
  simp only [mem_setOf_eq, S.rt_eq_of_inter_eq h]

/-! #### The graph `B` and the glued graphs `T^{(F)}` as weight functions -/

open scoped Classical in
/-- The weights of the graph `B`: `w` on the `B`-side pairs, `0` elsewhere. [cite: KozmaNitzan2024, proof of Thm. 3 (p. 10)] -/
def wB : Sym2 V → unitInterval := fun e => if e ∈ S.EB then S.w e else 0

open scoped Classical in
/-- The weights of the glued graph `T^{(F)}`: `1` on the virtual edges `F`, `w` on the `T`-side pairs,
`0` elsewhere. [cite: KozmaNitzan2024, proof of Thm. 3 (p. 10, the graphs T^{(jk)})] -/
def uT (F : Set (Sym2 V)) : Sym2 V → unitInterval :=
  fun e => if e ∈ F then 1 else if e ∈ S.ET then S.w e else 0

variable [Fintype V]

/-- **Independence of the `B`-pattern and the `T`-connections.** [cite: KozmaNitzan2024, proof of Thm. 3 (p. 10: "P_B", "P_T")] -/
theorem real_inter_rb_rt (Φ : (V → V → Prop) → Prop) (F : Set (Sym2 V)) (Ψ : (V → V → Prop) → Prop) :
    (prodBernoulli S.w).real ({ω | Φ (S.rb ω)} ∩ {ω | Ψ (S.rt F ω)}) =
      (prodBernoulli S.w).real {ω | Φ (S.rb ω)} * (prodBernoulli S.w).real {ω | Ψ (S.rt F ω)} :=
  real_inter_of_determinedBy_compl S.w S.EB (S.determinedBy_rb Φ) (S.determinedBy_rt F Ψ)

/-- **`P(Φ(↔_B)) = P_B(Φ(↔))`**: probabilities of `B`-connectivity events are probabilities of plain
connectivity events in the graph `B`. [cite: KozmaNitzan2024, proof of Thm. 3 (p. 10)] -/
theorem real_rb_eq (Φ : (V → V → Prop) → Prop) :
    (prodBernoulli S.w).real {ω | Φ (S.rb ω)} =
      (prodBernoulli S.wB).real {ω | Φ (fun x y => (openGraph ω).Reachable x y)} := by
  classical
  rw [real_eq_of_agree S.w S.wB S.EB (fun e he => by simp [wB, he]) (S.determinedBy_rb Φ)]
  refine real_eq_of_inter_sureSet S.wB ?_
  have key : ∀ ω ∈ sureSet S.wB, ω ∩ S.EB = ω := by
    intro ω hs
    refine Set.inter_eq_self_of_subset_left fun e he => ?_
    by_contra hE
    exact (hs e).1 (by simp [wB, hE]) he
  have key' : ∀ ω ∈ sureSet S.wB, S.rb ω = fun x y => (openGraph ω).Reachable x y := by
    intro ω hs
    funext x y
    simp only [rb, rB]
    rw [show ω ∩ sideB S.VB S.A = ω from key ω hs]
  ext ω
  simp only [mem_inter_iff, mem_setOf_eq]
  constructor
  · rintro ⟨h, hs⟩; rw [key' ω hs] at h; exact ⟨h, hs⟩
  · rintro ⟨h, hs⟩; rw [key' ω hs]; exact ⟨h, hs⟩

/-- **`P(Ψ(↔ in T glued along F)) = P_{T^{(F)}}(Ψ(↔))`** for a glue set `F` of pairs off the `T`-side.
[cite: KozmaNitzan2024, proof of Thm. 3 (p. 10)] -/
theorem real_rt_eq (F : Set (Sym2 V)) (hF : ∀ e ∈ F, e ∉ S.ET) (Ψ : (V → V → Prop) → Prop) :
    (prodBernoulli S.w).real {ω | Ψ (S.rt F ω)} =
      (prodBernoulli (S.uT F)).real {ω | Ψ (fun x y => (openGraph ω).Reachable x y)} := by
  classical
  rw [real_eq_of_agree S.w (S.uT F) S.ET (fun e he => by
      have heF : e ∉ F := fun h => hF e h he
      simp [uT, he, heF]) (S.determinedBy_rt' F Ψ)]
  refine real_eq_of_inter_sureSet (S.uT F) ?_
  have key : ∀ ω ∈ sureSet (S.uT F), ω ∩ sideT S.VB S.A ∪ F = ω := by
    intro ω hs
    ext e
    simp only [mem_union, mem_inter_iff]
    constructor
    · rintro (⟨he, -⟩ | he)
      · exact he
      · exact (hs e).2 (by simp [uT, he])
    · intro he
      by_cases heF : e ∈ F
      · exact Or.inr heF
      · refine Or.inl ⟨he, ?_⟩
        by_contra hT
        exact (hs e).1 (by simp [uT, heF, ET, hT]) he
  have key' : ∀ ω ∈ sureSet (S.uT F), S.rt F ω = fun x y => (openGraph ω).Reachable x y := by
    intro ω hs
    funext x y
    simp only [rt, rT]
    rw [key ω hs]
  ext ω
  simp only [mem_inter_iff, mem_setOf_eq]
  constructor
  · rintro ⟨h, hs⟩; rw [key' ω hs] at h; exact ⟨h, hs⟩
  · rintro ⟨h, hs⟩; rw [key' ω hs]; exact ⟨h, hs⟩

/-! #### The glue set of a configuration: one of `∅`, `{a₁a₂}`, `{a₁a₃}`, `{a₂a₃}`, all three -/

omit [Fintype V] in
/-- Membership in the glue set: a glued pair is one of the three pairs of `A`, with `B`-connected
endpoints. [cite: KozmaNitzan2024, proof of Thm. 3 (p. 10, "connection patterns in B")] -/
theorem mem_glueSet_iff (ω : BondConfig V) (e : Sym2 V) :
    e ∈ glueSet S.VB S.A ω ↔
      (e = s(S.a₁, S.a₂) ∧ S.rb ω S.a₁ S.a₂) ∨ (e = s(S.a₁, S.a₃) ∧ S.rb ω S.a₁ S.a₃) ∨
        (e = s(S.a₂, S.a₃) ∧ S.rb ω S.a₂ S.a₃) := by
  induction e using Sym2.ind with
  | h x y =>
    rw [mk_mem_glueSet_iff]
    constructor
    · rintro ⟨hx, hy, hne, hr⟩
      simp only [A, mem_insert_iff, mem_singleton_iff] at hx hy
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
      all_goals first
        | exact absurd rfl hne
        | exact Or.inl ⟨rfl, hr⟩
        | exact Or.inl ⟨Sym2.eq_swap, rB.symm hr⟩
        | exact Or.inr (Or.inl ⟨rfl, hr⟩)
        | exact Or.inr (Or.inl ⟨Sym2.eq_swap, rB.symm hr⟩)
        | exact Or.inr (Or.inr ⟨rfl, hr⟩)
        | exact Or.inr (Or.inr ⟨Sym2.eq_swap, rB.symm hr⟩)
    · rintro (⟨h, hr⟩ | ⟨h, hr⟩ | ⟨h, hr⟩)
      · rcases Sym2.eq_iff.1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨S.a₁_mem, S.a₂_mem, S.h₁₂, hr⟩
        · exact ⟨S.a₂_mem, S.a₁_mem, S.h₁₂.symm, rB.symm hr⟩
      · rcases Sym2.eq_iff.1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨S.a₁_mem, S.a₃_mem, S.h₁₃, hr⟩
        · exact ⟨S.a₃_mem, S.a₁_mem, S.h₁₃.symm, rB.symm hr⟩
      · rcases Sym2.eq_iff.1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨S.a₂_mem, S.a₃_mem, S.h₂₃, hr⟩
        · exact ⟨S.a₃_mem, S.a₂_mem, S.h₂₃.symm, rB.symm hr⟩

/-- The glue set `{a₁a₂}` (one of the five glue sets). [cite: KozmaNitzan2024, proof of Thm. 3 (p. 10)] -/
def F12 : Set (Sym2 V) := {s(S.a₁, S.a₂)}
/-- The glue set `{a₁a₃}`. [cite: KozmaNitzan2024, proof of Thm. 3 (p. 10)] -/
def F13 : Set (Sym2 V) := {s(S.a₁, S.a₃)}
/-- The glue set `{a₂a₃}`. [cite: KozmaNitzan2024, proof of Thm. 3 (p. 10)] -/
def F23 : Set (Sym2 V) := {s(S.a₂, S.a₃)}
/-- The glue set of all three pairs of `A`. [cite: KozmaNitzan2024, proof of Thm. 3 (p. 10)] -/
def F123 : Set (Sym2 V) := {s(S.a₁, S.a₂), s(S.a₁, S.a₃), s(S.a₂, S.a₃)}

omit [Fintype V] in
/-- A pair inside `A` is not a `T`-side pair. [folklore] -/
theorem mk_notMem_ET {x y : V} (hx : x ∈ S.A) (hy : y ∈ S.A) : s(x, y) ∉ S.ET := by
  intro h
  exact h.2 (by intro v hv; rcases Sym2.mem_iff.1 hv with rfl | rfl <;> assumption)

omit [Fintype V] in
/-- `F12` is off the `T`-side. [folklore] -/
theorem F12_off : ∀ e ∈ S.F12, e ∉ S.ET := by
  intro e he; rw [F12, mem_singleton_iff] at he; subst he; exact S.mk_notMem_ET S.a₁_mem S.a₂_mem
omit [Fintype V] in
/-- The empty glue set is off the `T`-side. [folklore] -/
theorem empty_off : ∀ e ∈ (∅ : Set (Sym2 V)), e ∉ S.ET := by intro e he; exact absurd he (by simp)

omit [Fintype V] in
/-- Pattern `M` (all three separated in `B`): no glued pair. [cite: KozmaNitzan2024, proof of Thm. 3 (p. 10, the event M)] -/
theorem glueSet_M {ω : BondConfig V} (h12 : ¬ S.rb ω S.a₁ S.a₂) (h13 : ¬ S.rb ω S.a₁ S.a₃)
    (h23 : ¬ S.rb ω S.a₂ S.a₃) : glueSet S.VB S.A ω = ∅ := by
  ext e; simp [S.mem_glueSet_iff, h12, h13, h23]

omit [Fintype V] in
/-- Pattern `a₁ ↔ a₂ ↮ a₃` in `B`: the glued pair is `a₁a₂`. [cite: KozmaNitzan2024, proof of Thm. 3 (pp. 10–11)] -/
theorem glueSet_12 {ω : BondConfig V} (h12 : S.rb ω S.a₁ S.a₂) (h13 : ¬ S.rb ω S.a₁ S.a₃) :
    glueSet S.VB S.A ω = S.F12 := by
  have h23 : ¬ S.rb ω S.a₂ S.a₃ := fun h => h13 (rB.trans h12 h)
  ext e; simp [S.mem_glueSet_iff, F12, h12, h13, h23]

omit [Fintype V] in
/-- Pattern `a₁ ↔ a₃ ↮ a₂` in `B`: the glued pair is `a₁a₃`. [cite: KozmaNitzan2024, proof of Thm. 3 (pp. 10–11)] -/
theorem glueSet_13 {ω : BondConfig V} (h12 : ¬ S.rb ω S.a₁ S.a₂) (h13 : S.rb ω S.a₁ S.a₃) :
    glueSet S.VB S.A ω = S.F13 := by
  have h23 : ¬ S.rb ω S.a₂ S.a₃ := fun h => h12 (rB.trans h13 (rB.symm h))
  ext e; simp [S.mem_glueSet_iff, F13, h12, h13, h23]

omit [Fintype V] in
/-- Pattern `a₂ ↔ a₃ ↮ a₁` in `B`: the glued pair is `a₂a₃`. [cite: KozmaNitzan2024, proof of Thm. 3 (pp. 10–11)] -/
theorem glueSet_23 {ω : BondConfig V} (h12 : ¬ S.rb ω S.a₁ S.a₂) (h13 : ¬ S.rb ω S.a₁ S.a₃)
    (h23 : S.rb ω S.a₂ S.a₃) : glueSet S.VB S.A ω = S.F23 := by
  ext e; simp [S.mem_glueSet_iff, F23, h12, h13, h23]

omit [Fintype V] in
/-- Pattern "all of `A` connected in `B`": all three pairs glued. [cite: KozmaNitzan2024, proof of Thm. 3 (pp. 10–11)] -/
theorem glueSet_123 {ω : BondConfig V} (h12 : S.rb ω S.a₁ S.a₂) (h13 : S.rb ω S.a₁ S.a₃) :
    glueSet S.VB S.A ω = S.F123 := by
  have h23 : S.rb ω S.a₂ S.a₃ := rB.trans (rB.symm h12) h13
  ext e; simp [S.mem_glueSet_iff, F123, h12, h13, h23]

/-! #### Reading `G`-connections on a `B`-pattern -/

omit [Fintype V] in
/-- On a configuration without cross pairs in which `o ↔_B a` for some `a ∈ A`: `o ↔ b` iff `a ↔ b`
in the glued `T`-side. [cite: KozmaNitzan2024, proof of Thm. 3 (p. 11, "decompose according to the connections between 0 and the elements of A in B")] -/
theorem reachable_o_iff {ω : BondConfig V} (hω : noCross S.VB S.A ω) {a : V} (ha : a ∈ S.A)
    (hoa : S.rb ω S.o a) :
    (openGraph ω).Reachable S.o S.b ↔ rT S.VB S.A (glueSet S.VB S.A ω) ω a S.b := by
  rw [reachable_iff_exists_rB_rT hω S.ho S.hb]
  constructor
  · rintro ⟨a', ha', hoa', ha'b⟩
    exact (rT_of_rB ha ha' (rB.trans (rB.symm hoa) hoa')).trans ha'b
  · exact fun h => ⟨a, ha, hoa, h⟩

omit [Fintype V] in
/-- On a configuration without cross pairs, `o ↔ A` iff `o ↔_B a` for some `a ∈ A`. [cite: KozmaNitzan2024, proof of Thm. 3 (p. 11)] -/
theorem reachable_oA_iff {ω : BondConfig V} (hω : noCross S.VB S.A ω) :
    (∃ a ∈ S.A, (openGraph ω).Reachable S.o a) ↔ ∃ a ∈ S.A, S.rb ω S.o a := by
  constructor
  · rintro ⟨a, ha, h⟩
    obtain ⟨a', ha', hoa', -⟩ := (reachable_iff_exists_rB_rT hω S.ho (S.notMem_VB_of_mem_A ha)).1 h
    exact ⟨a', ha', hoa'⟩
  · rintro ⟨a, ha, h⟩
    exact ⟨a, ha, rB.reachable h⟩

/-! #### `B`-events, `T`-quantities, and the product formula -/

/-- The event that the `B`-connectivity of `ω` satisfies `Φ`. [folklore] -/
def ev (Φ : (V → V → Prop) → Prop) : Set (BondConfig V) := {ω | Φ (S.rb ω)}

omit [Fintype V] in
/-- Membership in `ev`. [folklore] -/
@[simp] theorem mem_ev (Φ : (V → V → Prop) → Prop) (ω : BondConfig V) : ω ∈ S.ev Φ ↔ Φ (S.rb ω) := Iff.rfl

/-- `P(Φ(↔_B)) = P_B(Φ(↔))`, `ev` form of `real_rb_eq`. [cite: KozmaNitzan2024, proof of Thm. 3 (p. 10)] -/
theorem real_ev_eq (Φ : (V → V → Prop) → Prop) :
    (prodBernoulli S.w).real (S.ev Φ) =
      (prodBernoulli S.wB).real {ω | Φ (fun x y => (openGraph ω).Reachable x y)} :=
  S.real_rb_eq Φ

/-- The event `{0 ↔ A}`. [cite: KozmaNitzan2024, (3) p. 3] -/
def oA : Set (BondConfig V) := openConn S.o S.a₁ ∪ openConn S.o S.a₂ ∪ openConn S.o S.a₃

omit [Fintype V] in
/-- Membership in `{0 ↔ A}`. [folklore] -/
theorem mem_oA_iff (ω : BondConfig V) : ω ∈ S.oA ↔ ∃ a ∈ S.A, (openGraph ω).Reachable S.o a := by
  simp only [oA, A, mem_union, openConn, mem_setOf_eq, mem_insert_iff, mem_singleton_iff,
    exists_eq_or_imp, exists_eq_left, or_assoc]

/-- `q^{(F)}_x = P_{T^{(F)}}(x ↔ b)`, as the probability of glued `T`-connectivity.
[cite: KozmaNitzan2024, proof of Thm. 3 (p. 10, the quantities q_X and q^{(jk)}_X)] -/
def Q (F : Set (Sym2 V)) (x : V) : ℝ := (prodBernoulli S.w).real {ω | S.rt F ω x S.b}

omit [Fintype V] in
/-- Glued vertices have the same `q`. [folklore] -/
theorem Q_eq_of_mem {F : Set (Sym2 V)} {x y : V} (h : s(x, y) ∈ F) : S.Q F x = S.Q F y := by
  simp only [Q]
  congr 1
  ext ω
  simp only [mem_setOf_eq, rt, rT]
  have hxy : (openGraph (ω ∩ sideT S.VB S.A ∪ F)).Reachable x y := by
    by_cases he : x = y
    · rw [he]
    · exact SimpleGraph.Adj.reachable ((openGraph_adj _ x y).2 ⟨Or.inr h, he⟩)
  exact ⟨fun h' => hxy.symm.trans h', fun h' => hxy.trans h'⟩

/-- **Product formula for a vertex off the `B`-interior.** If the `B`-event `Φ` forces the glue set
`F`, then `P(x ↔ b, Φ) = P_B(Φ) · P_{T^{(F)}}(x ↔ b)`. [cite: KozmaNitzan2024, proof of Thm. 3 (pp. 10–11, "break … according to the connection patterns in B")] -/
theorem real_conn_inter_ev {x : V} (hx : x ∉ S.VB) (Φ : (V → V → Prop) → Prop) (F : Set (Sym2 V))
    (hF : ∀ ω, Φ (S.rb ω) → glueSet S.VB S.A ω = F) :
    (prodBernoulli S.w).real (openConn x S.b ∩ S.ev Φ) =
      (prodBernoulli S.w).real (S.ev Φ) * S.Q F x := by
  have step : (prodBernoulli S.w).real (openConn x S.b ∩ S.ev Φ) =
      (prodBernoulli S.w).real (S.ev Φ ∩ {ω | (fun r : V → V → Prop => r x S.b) (S.rt F ω)}) := by
    refine real_eq_of_inter_sureSet S.w ?_
    ext ω
    simp only [mem_inter_iff, mem_ev, mem_setOf_eq, openConn]
    constructor
    · rintro ⟨⟨h, hΦ⟩, hs⟩
      have hω := S.sureSet_subset_noCross hs
      refine ⟨⟨hΦ, ?_⟩, hs⟩
      have := (reachable_iff_rT hω hx S.hb).1 h
      rwa [hF ω hΦ] at this
    · rintro ⟨⟨hΦ, h⟩, hs⟩
      have hω := S.sureSet_subset_noCross hs
      refine ⟨⟨?_, hΦ⟩, hs⟩
      rw [reachable_iff_rT hω hx S.hb, hF ω hΦ]
      exact h
  rw [step]
  exact S.real_inter_rb_rt Φ F (fun r => r x S.b)

/-- **Product formula for the observer.** If the `B`-event `Φ` forces the glue set `F` and
`o ↔_B a` (`a ∈ A`), then `P(0 ↔ b, Φ) = P_B(Φ) · P_{T^{(F)}}(a ↔ b)`. [cite: KozmaNitzan2024, proof of Thm. 3 (p. 11)] -/
theorem real_oconn_inter_ev (Φ : (V → V → Prop) → Prop) (F : Set (Sym2 V))
    (hF : ∀ ω, Φ (S.rb ω) → glueSet S.VB S.A ω = F) {a : V} (ha : a ∈ S.A)
    (hoa : ∀ ω, Φ (S.rb ω) → S.rb ω S.o a) :
    (prodBernoulli S.w).real (openConn S.o S.b ∩ S.ev Φ) =
      (prodBernoulli S.w).real (S.ev Φ) * S.Q F a := by
  have step : (prodBernoulli S.w).real (openConn S.o S.b ∩ S.ev Φ) =
      (prodBernoulli S.w).real (S.ev Φ ∩ {ω | (fun r : V → V → Prop => r a S.b) (S.rt F ω)}) := by
    refine real_eq_of_inter_sureSet S.w ?_
    ext ω
    simp only [mem_inter_iff, mem_ev, mem_setOf_eq, openConn]
    constructor
    · rintro ⟨⟨h, hΦ⟩, hs⟩
      have hω := S.sureSet_subset_noCross hs
      refine ⟨⟨hΦ, ?_⟩, hs⟩
      have := (S.reachable_o_iff hω ha (hoa ω hΦ)).1 h
      rwa [hF ω hΦ] at this
    · rintro ⟨⟨hΦ, h⟩, hs⟩
      have hω := S.sureSet_subset_noCross hs
      refine ⟨⟨?_, hΦ⟩, hs⟩
      rw [S.reachable_o_iff hω ha (hoa ω hΦ), hF ω hΦ]
      exact h
  rw [step]
  exact S.real_inter_rb_rt Φ F (fun r => r a S.b)

/-- **Product formula for `{0 ↔ A, a₃ ↔ b}`.** If the `B`-event `Φ` forces the glue set `F` and
`o ↔_B a` for some `a ∈ A`, then `P(0 ↔ A, a₃ ↔ b, Φ) = P_B(Φ) · P_{T^{(F)}}(a₃ ↔ b)`. [cite: KozmaNitzan2024, proof of Thm. 3 (p. 11)] -/
theorem real_oA_conn_inter_ev (Φ : (V → V → Prop) → Prop) (F : Set (Sym2 V))
    (hF : ∀ ω, Φ (S.rb ω) → glueSet S.VB S.A ω = F) (hoa : ∀ ω, Φ (S.rb ω) → ∃ a ∈ S.A, S.rb ω S.o a) :
    (prodBernoulli S.w).real (S.oA ∩ openConn S.a₃ S.b ∩ S.ev Φ) =
      (prodBernoulli S.w).real (S.ev Φ) * S.Q F S.a₃ := by
  rw [← S.real_conn_inter_ev S.ha₃ Φ F hF]
  refine real_eq_of_inter_sureSet S.w ?_
  ext ω
  simp only [mem_inter_iff, mem_ev]
  constructor
  · rintro ⟨⟨⟨-, h⟩, hΦ⟩, hs⟩; exact ⟨⟨h, hΦ⟩, hs⟩
  · rintro ⟨⟨h, hΦ⟩, hs⟩
    have hω := S.sureSet_subset_noCross hs
    exact ⟨⟨⟨(S.mem_oA_iff ω).2 ((S.reachable_oA_iff hω).2 (hoa ω hΦ)), h⟩, hΦ⟩, hs⟩

/-- **Vanishing cells.** If the `B`-event `Φ` forces `o ↮_B A`, then `P(0 ↔ b, Φ) = 0` and
`P(0 ↔ A, a₃ ↔ b, Φ) = 0`. [cite: KozmaNitzan2024, proof of Thm. 3 (p. 11)] -/
theorem real_zero_of_notConn (Φ : (V → V → Prop) → Prop)
    (hnone : ∀ ω, Φ (S.rb ω) → ∀ a ∈ S.A, ¬ S.rb ω S.o a) :
    (prodBernoulli S.w).real (openConn S.o S.b ∩ S.ev Φ) = 0 ∧
      (prodBernoulli S.w).real (S.oA ∩ openConn S.a₃ S.b ∩ S.ev Φ) = 0 := by
  constructor
  · rw [← measureReal_empty (μ := prodBernoulli S.w)]
    refine real_eq_of_inter_sureSet S.w ?_
    rw [Set.empty_inter, Set.eq_empty_iff_forall_notMem]
    rintro ω ⟨⟨h, hΦ⟩, hs⟩
    have hω := S.sureSet_subset_noCross hs
    obtain ⟨a, ha, hoa, -⟩ := (reachable_iff_exists_rB_rT hω S.ho S.hb).1 h
    exact hnone ω hΦ a ha hoa
  · rw [← measureReal_empty (μ := prodBernoulli S.w)]
    refine real_eq_of_inter_sureSet S.w ?_
    rw [Set.empty_inter, Set.eq_empty_iff_forall_notMem]
    rintro ω ⟨⟨⟨hA, -⟩, hΦ⟩, hs⟩
    have hω := S.sureSet_subset_noCross hs
    obtain ⟨a, ha, hoa⟩ := (S.reachable_oA_iff hω).1 ((S.mem_oA_iff ω).1 hA)
    exact hnone ω hΦ a ha hoa

/-- Splitting an event along a `B`-predicate. [folklore] -/
theorem real_split_ev (X : Set (BondConfig V)) (Φ Ψ : (V → V → Prop) → Prop) :
    (prodBernoulli S.w).real (X ∩ S.ev Φ) =
      (prodBernoulli S.w).real (X ∩ S.ev (fun r => Φ r ∧ Ψ r)) +
        (prodBernoulli S.w).real (X ∩ S.ev (fun r => Φ r ∧ ¬ Ψ r)) := by
  classical
  rw [← measureReal_union _ MeasurableSet.of_discrete]
  · congr 1
    ext ω; simp only [mem_inter_iff, mem_ev, mem_union]; tauto
  · exact Set.disjoint_left.2 fun ω h h' => h'.2.2 h.2.2

/-- **The five connection patterns of `A` in `B`** exhaust the space:
`P(X) = P(X, all joined) + P(X, a₁a₂|a₃) + P(X, a₁a₃|a₂) + P(X, a₂a₃|a₁) + P(X, M)`.
[cite: KozmaNitzan2024, proof of Thm. 3 (pp. 10–11)] -/
theorem five_split (X : Set (BondConfig V)) :
    (prodBernoulli S.w).real X =
      (prodBernoulli S.w).real (X ∩ S.ev fun r => r S.a₁ S.a₂ ∧ r S.a₁ S.a₃) +
      (prodBernoulli S.w).real (X ∩ S.ev fun r => r S.a₁ S.a₂ ∧ ¬ r S.a₁ S.a₃) +
      (prodBernoulli S.w).real (X ∩ S.ev fun r => ¬ r S.a₁ S.a₂ ∧ r S.a₁ S.a₃) +
      (prodBernoulli S.w).real (X ∩ S.ev fun r => ¬ r S.a₁ S.a₂ ∧ ¬ r S.a₁ S.a₃ ∧ r S.a₂ S.a₃) +
      (prodBernoulli S.w).real (X ∩ S.ev fun r => ¬ r S.a₁ S.a₂ ∧ ¬ r S.a₁ S.a₃ ∧ ¬ r S.a₂ S.a₃) := by
  have h0 : (prodBernoulli S.w).real X = (prodBernoulli S.w).real (X ∩ S.ev fun _ => True) := by
    congr 1; ext ω; simp
  rw [h0, S.real_split_ev X (fun _ => True) (fun r => r S.a₁ S.a₂),
    S.real_split_ev X (fun r => True ∧ r S.a₁ S.a₂) (fun r => r S.a₁ S.a₃),
    S.real_split_ev X (fun r => True ∧ ¬ r S.a₁ S.a₂) (fun r => r S.a₁ S.a₃),
    S.real_split_ev X (fun r => (True ∧ ¬ r S.a₁ S.a₂) ∧ ¬ r S.a₁ S.a₃) (fun r => r S.a₂ S.a₃)]
  simp only [true_and, and_assoc]
  ring

/-! #### The five cells as predicates and the decompositions (11), (13) and of the target -/

/-- The cell: all of `A` joined in `B`. [cite: KozmaNitzan2024, proof of Thm. 3 (pp. 10–11)] -/
def c123 (r : V → V → Prop) : Prop := r S.a₁ S.a₂ ∧ r S.a₁ S.a₃
/-- The cell `a₁ ↔ a₂ ↮ a₃` in `B`. [cite: KozmaNitzan2024, proof of Thm. 3, (11) (p. 10)] -/
def c12 (r : V → V → Prop) : Prop := r S.a₁ S.a₂ ∧ ¬ r S.a₁ S.a₃
/-- The cell `a₁ ↔ a₃ ↮ a₂` in `B`. [cite: KozmaNitzan2024, proof of Thm. 3 (pp. 10–11)] -/
def c13 (r : V → V → Prop) : Prop := ¬ r S.a₁ S.a₂ ∧ r S.a₁ S.a₃
/-- The cell `a₂ ↔ a₃ ↮ a₁` in `B`. [cite: KozmaNitzan2024, proof of Thm. 3, (11) (p. 10)] -/
def c23 (r : V → V → Prop) : Prop := ¬ r S.a₁ S.a₂ ∧ ¬ r S.a₁ S.a₃ ∧ r S.a₂ S.a₃
/-- The event `M`: `a₁, a₂, a₃` pairwise separated in `B`. [cite: KozmaNitzan2024, proof of Thm. 3 (p. 10, the event M)] -/
def cM (r : V → V → Prop) : Prop := ¬ r S.a₁ S.a₂ ∧ ¬ r S.a₁ S.a₃ ∧ ¬ r S.a₂ S.a₃

/-- `five_split` with the named cells. [cite: KozmaNitzan2024, proof of Thm. 3 (pp. 10–11)] -/
theorem five_split' (X : Set (BondConfig V)) :
    (prodBernoulli S.w).real X =
      (prodBernoulli S.w).real (X ∩ S.ev S.c123) + (prodBernoulli S.w).real (X ∩ S.ev S.c12) +
      (prodBernoulli S.w).real (X ∩ S.ev S.c13) + (prodBernoulli S.w).real (X ∩ S.ev S.c23) +
      (prodBernoulli S.w).real (X ∩ S.ev S.cM) :=
  S.five_split X

omit [Fintype V] in
/-- Glue set on the cell `c123`. [cite: KozmaNitzan2024, proof of Thm. 3 (pp. 10–11)] -/
theorem glue_c123 : ∀ ω, S.c123 (S.rb ω) → glueSet S.VB S.A ω = S.F123 :=
  fun _ h => S.glueSet_123 h.1 h.2
omit [Fintype V] in
/-- Glue set on the cell `c12`. [cite: KozmaNitzan2024, proof of Thm. 3 (pp. 10–11)] -/
theorem glue_c12 : ∀ ω, S.c12 (S.rb ω) → glueSet S.VB S.A ω = S.F12 :=
  fun _ h => S.glueSet_12 h.1 h.2
omit [Fintype V] in
/-- Glue set on the cell `c13`. [cite: KozmaNitzan2024, proof of Thm. 3 (pp. 10–11)] -/
theorem glue_c13 : ∀ ω, S.c13 (S.rb ω) → glueSet S.VB S.A ω = S.F13 :=
  fun _ h => S.glueSet_13 h.1 h.2
omit [Fintype V] in
/-- Glue set on the cell `c23`. [cite: KozmaNitzan2024, proof of Thm. 3 (pp. 10–11)] -/
theorem glue_c23 : ∀ ω, S.c23 (S.rb ω) → glueSet S.VB S.A ω = S.F23 :=
  fun _ h => S.glueSet_23 h.1 h.2.1 h.2.2
omit [Fintype V] in
/-- Glue set on the cell `M`. [cite: KozmaNitzan2024, proof of Thm. 3 (pp. 10–11)] -/
theorem glue_cM : ∀ ω, S.cM (S.rb ω) → glueSet S.VB S.A ω = ∅ :=
  fun _ h => S.glueSet_M h.1 h.2.1 h.2.2

omit [Fintype V] in
/-- `q^{(123)}_1 = q^{(123)}_3` (glued vertices). [folklore] -/
theorem Q123_13 : S.Q S.F123 S.a₁ = S.Q S.F123 S.a₃ := S.Q_eq_of_mem (by simp [F123])
omit [Fintype V] in
/-- `q^{(13)}_1 = q^{(13)}_3 = q_{13}` (glued vertices). [cite: KozmaNitzan2024, proof of Thm. 3 (p. 10)] -/
theorem Q13_13 : S.Q S.F13 S.a₁ = S.Q S.F13 S.a₃ := S.Q_eq_of_mem (by simp [F13])
omit [Fintype V] in
/-- `q^{(12)}_1 = q^{(12)}_2 = q_{12}` (glued vertices). [cite: KozmaNitzan2024, proof of Thm. 3 (p. 10)] -/
theorem Q12_12 : S.Q S.F12 S.a₁ = S.Q S.F12 S.a₂ := S.Q_eq_of_mem (by simp [F12])
omit [Fintype V] in
/-- `q^{(23)}_2 = q^{(23)}_3 = q_{23}` (glued vertices). [cite: KozmaNitzan2024, proof of Thm. 3 (p. 10)] -/
theorem Q23_23 : S.Q S.F23 S.a₂ = S.Q S.F23 S.a₃ := S.Q_eq_of_mem (by simp [F23])
omit [Fintype V] in
/-- `q^{(123)}_2 = q^{(123)}_3` (glued vertices). [folklore] -/
theorem Q123_23 : S.Q S.F123 S.a₂ = S.Q S.F123 S.a₃ := S.Q_eq_of_mem (by simp [F123])

/-- **Decomposition of `P(x ↔ b)` over the five patterns** (`x ∈ A`):
`P(x ↔ b) = Σ_patterns P_B(pattern) · q^{(pattern)}_x`. [cite: KozmaNitzan2024, proof of Thm. 3 (p. 10, "(10) can be rewritten as (11)")] -/
theorem conn_decomp {x : V} (hx : x ∉ S.VB) :
    (prodBernoulli S.w).real (openConn x S.b) =
      (prodBernoulli S.w).real (S.ev S.c123) * S.Q S.F123 x +
      (prodBernoulli S.w).real (S.ev S.c12) * S.Q S.F12 x +
      (prodBernoulli S.w).real (S.ev S.c13) * S.Q S.F13 x +
      (prodBernoulli S.w).real (S.ev S.c23) * S.Q S.F23 x +
      (prodBernoulli S.w).real (S.ev S.cM) * S.Q ∅ x := by
  rw [S.five_split' (openConn x S.b), S.real_conn_inter_ev hx _ _ S.glue_c123,
    S.real_conn_inter_ev hx _ _ S.glue_c12, S.real_conn_inter_ev hx _ _ S.glue_c13,
    S.real_conn_inter_ev hx _ _ S.glue_c23, S.real_conn_inter_ev hx _ _ S.glue_cM]

/-- **(11)**: `P(a₁ ↔ b) − P(a₃ ↔ b) = P_B(a₁↔a₂↮a₃)(q^{(12)}_1 − q^{(12)}_3) +
P_B(a₁↮a₂↔a₃)(q^{(23)}_1 − q^{(23)}_3) + P_B(M)(q_1 − q_3)`. [cite: KozmaNitzan2024, proof of Thm. 3, eq. (11) (p. 10)] -/
theorem eq11 :
    (prodBernoulli S.w).real (openConn S.a₁ S.b) - (prodBernoulli S.w).real (openConn S.a₃ S.b) =
      (prodBernoulli S.w).real (S.ev S.c12) * (S.Q S.F12 S.a₁ - S.Q S.F12 S.a₃) +
      (prodBernoulli S.w).real (S.ev S.c23) * (S.Q S.F23 S.a₁ - S.Q S.F23 S.a₃) +
      (prodBernoulli S.w).real (S.ev S.cM) * (S.Q ∅ S.a₁ - S.Q ∅ S.a₃) := by
  rw [S.conn_decomp S.ha₁, S.conn_decomp S.ha₃, S.Q123_13, S.Q13_13]
  ring

/-- **(11) with `a₁` and `a₂` swapped**: `P(a₂ ↔ b) − P(a₃ ↔ b) = P_B(a₁↔a₂↮a₃)(q^{(12)}_2 − q^{(12)}_3) +
P_B(a₂↮a₁↔a₃)(q^{(13)}_2 − q^{(13)}_3) + P_B(M)(q_2 − q_3)` ("A similar relation holds also for `a₂`",
p. 10). [cite: KozmaNitzan2024, proof of Thm. 3, after eq. (11) (p. 10)] -/
theorem eq11' :
    (prodBernoulli S.w).real (openConn S.a₂ S.b) - (prodBernoulli S.w).real (openConn S.a₃ S.b) =
      (prodBernoulli S.w).real (S.ev S.c12) * (S.Q S.F12 S.a₁ - S.Q S.F12 S.a₃) +
      (prodBernoulli S.w).real (S.ev S.c13) * (S.Q S.F13 S.a₂ - S.Q S.F13 S.a₃) +
      (prodBernoulli S.w).real (S.ev S.cM) * (S.Q ∅ S.a₂ - S.Q ∅ S.a₃) := by
  rw [S.conn_decomp S.ha₂, S.conn_decomp S.ha₃, S.Q123_23, ← S.Q12_12, S.Q23_23]
  ring

/-- The event of (12): `{x ↔ b} ∩ {a₃ ↮ a₂ in B}` decomposed over the patterns — only `a₁a₂|a₃`,
`a₁a₃|a₂` and `M` are compatible with `a₃ ↮_B a₂`. [cite: KozmaNitzan2024, proof of Thm. 3, (12)–(13) (p. 11)] -/
theorem connQ_decomp {x : V} (hx : x ∉ S.VB) :
    (prodBernoulli S.w).real (openConn x S.b ∩ S.ev fun r => ¬ r S.a₃ S.a₂) =
      (prodBernoulli S.w).real (S.ev S.c12) * S.Q S.F12 x +
      (prodBernoulli S.w).real (S.ev S.c13) * S.Q S.F13 x +
      (prodBernoulli S.w).real (S.ev S.cM) * S.Q ∅ x := by
  have hin : ∀ Φ : (V → V → Prop) → Prop, openConn x S.b ∩ S.ev (fun r => ¬ r S.a₃ S.a₂) ∩ S.ev Φ =
      openConn x S.b ∩ S.ev (fun r => Φ r ∧ ¬ r S.a₃ S.a₂) := by
    intro Φ; ext ω; simp only [mem_inter_iff, mem_ev]; tauto
  rw [S.five_split' (openConn x S.b ∩ _), hin, hin, hin, hin, hin]
  -- the cells `c123` and `c23` are incompatible with `a₃ ↮_B a₂`
  have z123 : S.ev (fun r => S.c123 r ∧ ¬ r S.a₃ S.a₂) = ∅ := by
    ext ω
    simp only [mem_ev, c123, mem_empty_iff_false, iff_false]
    exact fun ⟨⟨h12, h13⟩, hn⟩ => hn (rB.symm (rB.trans (rB.symm h12) h13))
  have z23 : S.ev (fun r => S.c23 r ∧ ¬ r S.a₃ S.a₂) = ∅ := by
    ext ω
    simp only [mem_ev, c23, mem_empty_iff_false, iff_false]
    exact fun ⟨⟨_, _, h23⟩, hn⟩ => hn (rB.symm h23)
  have e12 : S.ev (fun r => S.c12 r ∧ ¬ r S.a₃ S.a₂) = S.ev S.c12 := by
    ext ω
    simp only [mem_ev, c12]
    exact ⟨fun h => h.1, fun ⟨h12, h13⟩ => ⟨⟨h12, h13⟩, fun h32 => h13 (rB.trans h12 (rB.symm h32))⟩⟩
  have e13 : S.ev (fun r => S.c13 r ∧ ¬ r S.a₃ S.a₂) = S.ev S.c13 := by
    ext ω
    simp only [mem_ev, c13]
    exact ⟨fun h => h.1, fun ⟨h12, h13⟩ => ⟨⟨h12, h13⟩, fun h32 => h12 (rB.trans h13 h32)⟩⟩
  have eM : S.ev (fun r => S.cM r ∧ ¬ r S.a₃ S.a₂) = S.ev S.cM := by
    ext ω
    simp only [mem_ev, cM]
    exact ⟨fun h => h.1, fun ⟨h12, h13, h23⟩ => ⟨⟨h12, h13, h23⟩, fun h32 => h23 (rB.symm h32)⟩⟩
  rw [S.real_conn_inter_ev hx (fun r => S.c123 r ∧ ¬ r S.a₃ S.a₂) S.F123 (fun ω h => S.glue_c123 ω h.1),
    S.real_conn_inter_ev hx (fun r => S.c12 r ∧ ¬ r S.a₃ S.a₂) S.F12 (fun ω h => S.glue_c12 ω h.1),
    S.real_conn_inter_ev hx (fun r => S.c13 r ∧ ¬ r S.a₃ S.a₂) S.F13 (fun ω h => S.glue_c13 ω h.1),
    S.real_conn_inter_ev hx (fun r => S.c23 r ∧ ¬ r S.a₃ S.a₂) S.F23 (fun ω h => S.glue_c23 ω h.1),
    S.real_conn_inter_ev hx (fun r => S.cM r ∧ ¬ r S.a₃ S.a₂) ∅ (fun ω h => S.glue_cM ω h.1),
    z123, z23, e12, e13, eM, measureReal_empty]
  ring

/-- **The law of `{0 ↔ b}` and of `{0 ↔ A, a₃ ↔ b}` over the ten cells** (pattern × the block of `A`
joined to `0` in `B`): the two decompositions of p. 11. [cite: KozmaNitzan2024, proof of Thm. 3 (p. 11, the display defining α, β₁, β₂, γ₁, γ₂)] -/
theorem o_decomp :
    (prodBernoulli S.w).real (openConn S.o S.b) -
        (prodBernoulli S.w).real (S.oA ∩ openConn S.a₃ S.b) =
      (prodBernoulli S.w).real (S.ev fun r => S.c12 r ∧ r S.o S.a₁) * (S.Q S.F12 S.a₁ - S.Q S.F12 S.a₃) +
      (prodBernoulli S.w).real (S.ev fun r => S.c23 r ∧ r S.o S.a₁) * (S.Q S.F23 S.a₁ - S.Q S.F23 S.a₃) +
      (prodBernoulli S.w).real (S.ev fun r => S.c13 r ∧ r S.o S.a₂) * (S.Q S.F13 S.a₂ - S.Q S.F13 S.a₃) +
      (prodBernoulli S.w).real (S.ev fun r => S.cM r ∧ r S.o S.a₁) * (S.Q ∅ S.a₁ - S.Q ∅ S.a₃) +
      (prodBernoulli S.w).real (S.ev fun r => S.cM r ∧ r S.o S.a₂) * (S.Q ∅ S.a₂ - S.Q ∅ S.a₃) := by
  -- the ten cells and five empty cells
  have P123 := fun X => S.real_split_ev X S.c123 (fun r => r S.o S.a₁)
  have P12a := fun X => S.real_split_ev X S.c12 (fun r => r S.o S.a₁)
  have P12b := fun X => S.real_split_ev X (fun r => S.c12 r ∧ ¬ r S.o S.a₁) (fun r => r S.o S.a₃)
  have P13a := fun X => S.real_split_ev X S.c13 (fun r => r S.o S.a₁)
  have P13b := fun X => S.real_split_ev X (fun r => S.c13 r ∧ ¬ r S.o S.a₁) (fun r => r S.o S.a₂)
  have P23a := fun X => S.real_split_ev X S.c23 (fun r => r S.o S.a₁)
  have P23b := fun X => S.real_split_ev X (fun r => S.c23 r ∧ ¬ r S.o S.a₁) (fun r => r S.o S.a₂)
  have PM1 := fun X => S.real_split_ev X S.cM (fun r => r S.o S.a₁)
  have PM2 := fun X => S.real_split_ev X (fun r => S.cM r ∧ ¬ r S.o S.a₁) (fun r => r S.o S.a₂)
  have PM3 := fun X => S.real_split_ev X (fun r => (S.cM r ∧ ¬ r S.o S.a₁) ∧ ¬ r S.o S.a₂) (fun r => r S.o S.a₃)
  -- product formulas on the ten cells
  obtain ⟨c123o, c123A⟩ : _ ∧ _ :=
    ⟨S.real_oconn_inter_ev (fun r => S.c123 r ∧ r S.o S.a₁) S.F123 (fun ω h => S.glue_c123 ω h.1)
        S.a₁_mem (fun ω h => h.2),
      S.real_oA_conn_inter_ev (fun r => S.c123 r ∧ r S.o S.a₁) S.F123 (fun ω h => S.glue_c123 ω h.1)
        (fun ω h => ⟨S.a₁, S.a₁_mem, h.2⟩)⟩
  obtain ⟨c12ao, c12aA⟩ : _ ∧ _ :=
    ⟨S.real_oconn_inter_ev (fun r => S.c12 r ∧ r S.o S.a₁) S.F12 (fun ω h => S.glue_c12 ω h.1)
        S.a₁_mem (fun ω h => h.2),
      S.real_oA_conn_inter_ev (fun r => S.c12 r ∧ r S.o S.a₁) S.F12 (fun ω h => S.glue_c12 ω h.1)
        (fun ω h => ⟨S.a₁, S.a₁_mem, h.2⟩)⟩
  obtain ⟨c12bo, c12bA⟩ : _ ∧ _ :=
    ⟨S.real_oconn_inter_ev (fun r => (S.c12 r ∧ ¬ r S.o S.a₁) ∧ r S.o S.a₃) S.F12
        (fun ω h => S.glue_c12 ω h.1.1) S.a₃_mem (fun ω h => h.2),
      S.real_oA_conn_inter_ev (fun r => (S.c12 r ∧ ¬ r S.o S.a₁) ∧ r S.o S.a₃) S.F12
        (fun ω h => S.glue_c12 ω h.1.1) (fun ω h => ⟨S.a₃, S.a₃_mem, h.2⟩)⟩
  obtain ⟨c13ao, c13aA⟩ : _ ∧ _ :=
    ⟨S.real_oconn_inter_ev (fun r => S.c13 r ∧ r S.o S.a₁) S.F13 (fun ω h => S.glue_c13 ω h.1)
        S.a₁_mem (fun ω h => h.2),
      S.real_oA_conn_inter_ev (fun r => S.c13 r ∧ r S.o S.a₁) S.F13 (fun ω h => S.glue_c13 ω h.1)
        (fun ω h => ⟨S.a₁, S.a₁_mem, h.2⟩)⟩
  obtain ⟨c13bo, c13bA⟩ : _ ∧ _ :=
    ⟨S.real_oconn_inter_ev (fun r => (S.c13 r ∧ ¬ r S.o S.a₁) ∧ r S.o S.a₂) S.F13
        (fun ω h => S.glue_c13 ω h.1.1) S.a₂_mem (fun ω h => h.2),
      S.real_oA_conn_inter_ev (fun r => (S.c13 r ∧ ¬ r S.o S.a₁) ∧ r S.o S.a₂) S.F13
        (fun ω h => S.glue_c13 ω h.1.1) (fun ω h => ⟨S.a₂, S.a₂_mem, h.2⟩)⟩
  obtain ⟨c23ao, c23aA⟩ : _ ∧ _ :=
    ⟨S.real_oconn_inter_ev (fun r => S.c23 r ∧ r S.o S.a₁) S.F23 (fun ω h => S.glue_c23 ω h.1)
        S.a₁_mem (fun ω h => h.2),
      S.real_oA_conn_inter_ev (fun r => S.c23 r ∧ r S.o S.a₁) S.F23 (fun ω h => S.glue_c23 ω h.1)
        (fun ω h => ⟨S.a₁, S.a₁_mem, h.2⟩)⟩
  obtain ⟨c23bo, c23bA⟩ : _ ∧ _ :=
    ⟨S.real_oconn_inter_ev (fun r => (S.c23 r ∧ ¬ r S.o S.a₁) ∧ r S.o S.a₂) S.F23
        (fun ω h => S.glue_c23 ω h.1.1) S.a₂_mem (fun ω h => h.2),
      S.real_oA_conn_inter_ev (fun r => (S.c23 r ∧ ¬ r S.o S.a₁) ∧ r S.o S.a₂) S.F23
        (fun ω h => S.glue_c23 ω h.1.1) (fun ω h => ⟨S.a₂, S.a₂_mem, h.2⟩)⟩
  obtain ⟨cM1o, cM1A⟩ : _ ∧ _ :=
    ⟨S.real_oconn_inter_ev (fun r => S.cM r ∧ r S.o S.a₁) ∅ (fun ω h => S.glue_cM ω h.1)
        S.a₁_mem (fun ω h => h.2),
      S.real_oA_conn_inter_ev (fun r => S.cM r ∧ r S.o S.a₁) ∅ (fun ω h => S.glue_cM ω h.1)
        (fun ω h => ⟨S.a₁, S.a₁_mem, h.2⟩)⟩
  obtain ⟨cM2o, cM2A⟩ : _ ∧ _ :=
    ⟨S.real_oconn_inter_ev (fun r => (S.cM r ∧ ¬ r S.o S.a₁) ∧ r S.o S.a₂) ∅
        (fun ω h => S.glue_cM ω h.1.1) S.a₂_mem (fun ω h => h.2),
      S.real_oA_conn_inter_ev (fun r => (S.cM r ∧ ¬ r S.o S.a₁) ∧ r S.o S.a₂) ∅
        (fun ω h => S.glue_cM ω h.1.1) (fun ω h => ⟨S.a₂, S.a₂_mem, h.2⟩)⟩
  obtain ⟨cM3o, cM3A⟩ : _ ∧ _ :=
    ⟨S.real_oconn_inter_ev (fun r => ((S.cM r ∧ ¬ r S.o S.a₁) ∧ ¬ r S.o S.a₂) ∧ r S.o S.a₃) ∅
        (fun ω h => S.glue_cM ω h.1.1.1) S.a₃_mem (fun ω h => h.2),
      S.real_oA_conn_inter_ev (fun r => ((S.cM r ∧ ¬ r S.o S.a₁) ∧ ¬ r S.o S.a₂) ∧ r S.o S.a₃) ∅
        (fun ω h => S.glue_cM ω h.1.1.1) (fun ω h => ⟨S.a₃, S.a₃_mem, h.2⟩)⟩
  -- membership in `A`
  have memA : ∀ a ∈ S.A, a = S.a₁ ∨ a = S.a₂ ∨ a = S.a₃ := fun a ha => by
    simpa only [A, mem_insert_iff, mem_singleton_iff] using ha
  -- the five empty cells
  obtain ⟨z123o, z123A⟩ := S.real_zero_of_notConn (fun r => S.c123 r ∧ ¬ r S.o S.a₁) (by
    rintro ω ⟨⟨h12, h13⟩, hn1⟩ a ha hoa
    rcases memA a ha with rfl | rfl | rfl
    · exact hn1 hoa
    · exact hn1 (rB.trans hoa (rB.symm h12))
    · exact hn1 (rB.trans hoa (rB.symm h13)))
  obtain ⟨z12o, z12A⟩ := S.real_zero_of_notConn (fun r => (S.c12 r ∧ ¬ r S.o S.a₁) ∧ ¬ r S.o S.a₃) (by
    rintro ω ⟨⟨⟨h12, -⟩, hn1⟩, hn3⟩ a ha hoa
    rcases memA a ha with rfl | rfl | rfl
    · exact hn1 hoa
    · exact hn1 (rB.trans hoa (rB.symm h12))
    · exact hn3 hoa)
  obtain ⟨z13o, z13A⟩ := S.real_zero_of_notConn (fun r => (S.c13 r ∧ ¬ r S.o S.a₁) ∧ ¬ r S.o S.a₂) (by
    rintro ω ⟨⟨⟨-, h13⟩, hn1⟩, hn2⟩ a ha hoa
    rcases memA a ha with rfl | rfl | rfl
    · exact hn1 hoa
    · exact hn2 hoa
    · exact hn1 (rB.trans hoa (rB.symm h13)))
  obtain ⟨z23o, z23A⟩ := S.real_zero_of_notConn (fun r => (S.c23 r ∧ ¬ r S.o S.a₁) ∧ ¬ r S.o S.a₂) (by
    rintro ω ⟨⟨⟨-, -, h23⟩, hn1⟩, hn2⟩ a ha hoa
    rcases memA a ha with rfl | rfl | rfl
    · exact hn1 hoa
    · exact hn2 hoa
    · exact hn2 (rB.trans hoa (rB.symm h23)))
  obtain ⟨zMo, zMA⟩ := S.real_zero_of_notConn
    (fun r => ((S.cM r ∧ ¬ r S.o S.a₁) ∧ ¬ r S.o S.a₂) ∧ ¬ r S.o S.a₃) (by
    rintro ω ⟨⟨⟨-, hn1⟩, hn2⟩, hn3⟩ a ha hoa
    rcases memA a ha with rfl | rfl | rfl
    · exact hn1 hoa
    · exact hn2 hoa
    · exact hn3 hoa)
  -- assemble
  rw [S.five_split' (openConn S.o S.b), S.five_split' (S.oA ∩ openConn S.a₃ S.b)]
  rw [P123, P123, P12a, P12a, P12b, P12b, P13a, P13a, P13b, P13b, P23a, P23a, P23b, P23b,
    PM1, PM1, PM2, PM2, PM3, PM3]
  rw [c123o, c123A, c12ao, c12aA, c12bo, c12bA, c13ao, c13aA, c13bo, c13bA, c23ao, c23aA,
    c23bo, c23bA, cM1o, cM1A, cM2o, cM2A, cM3o, cM3A, z123o, z123A, z12o, z12A, z13o, z13A,
    z23o, z23A, zMo, zMA, S.Q123_13, S.Q13_13, S.Q23_23]
  -- two cells simplify: on `c13` and on `M`, `o ↔_B a₂` already forces `o ↮_B a₁`
  have s13 : S.ev (fun r => (S.c13 r ∧ ¬ r S.o S.a₁) ∧ r S.o S.a₂) = S.ev (fun r => S.c13 r ∧ r S.o S.a₂) := by
    ext ω
    simp only [mem_ev, c13]
    exact ⟨fun ⟨⟨h, _⟩, h2⟩ => ⟨h, h2⟩,
      fun ⟨⟨h12, h13⟩, h2⟩ => ⟨⟨⟨h12, h13⟩, fun h1 => h12 (rB.trans (rB.symm h1) h2)⟩, h2⟩⟩
  have sM : S.ev (fun r => (S.cM r ∧ ¬ r S.o S.a₁) ∧ r S.o S.a₂) = S.ev (fun r => S.cM r ∧ r S.o S.a₂) := by
    ext ω
    simp only [mem_ev, cM]
    exact ⟨fun ⟨⟨h, _⟩, h2⟩ => ⟨h, h2⟩,
      fun ⟨⟨h12, h13, h23⟩, h2⟩ => ⟨⟨⟨h12, h13, h23⟩, fun h1 => h12 (rB.trans (rB.symm h1) h2)⟩, h2⟩⟩
  rw [s13, sM]
  ring

/-- The mirror image of `connQ_decomp`: `{x ↔ b} ∩ {a₃ ↮ a₁ in B}` — compatible patterns `a₁a₂|a₃`,
`a₂a₃|a₁`, `M`. [cite: KozmaNitzan2024, proof of Thm. 3, (13) "with a₁ and a₂ swapped" (p. 11)] -/
theorem connQ'_decomp {x : V} (hx : x ∉ S.VB) :
    (prodBernoulli S.w).real (openConn x S.b ∩ S.ev fun r => ¬ r S.a₃ S.a₁) =
      (prodBernoulli S.w).real (S.ev S.c12) * S.Q S.F12 x +
      (prodBernoulli S.w).real (S.ev S.c23) * S.Q S.F23 x +
      (prodBernoulli S.w).real (S.ev S.cM) * S.Q ∅ x := by
  have hin : ∀ Φ : (V → V → Prop) → Prop, openConn x S.b ∩ S.ev (fun r => ¬ r S.a₃ S.a₁) ∩ S.ev Φ =
      openConn x S.b ∩ S.ev (fun r => Φ r ∧ ¬ r S.a₃ S.a₁) := by
    intro Φ; ext ω; simp only [mem_inter_iff, mem_ev]; tauto
  rw [S.five_split' (openConn x S.b ∩ _), hin, hin, hin, hin, hin]
  have z123 : S.ev (fun r => S.c123 r ∧ ¬ r S.a₃ S.a₁) = ∅ := by
    ext ω
    simp only [mem_ev, c123, mem_empty_iff_false, iff_false]
    exact fun ⟨⟨_, h13⟩, hn⟩ => hn (rB.symm h13)
  have z13 : S.ev (fun r => S.c13 r ∧ ¬ r S.a₃ S.a₁) = ∅ := by
    ext ω
    simp only [mem_ev, c13, mem_empty_iff_false, iff_false]
    exact fun ⟨⟨_, h13⟩, hn⟩ => hn (rB.symm h13)
  have e12 : S.ev (fun r => S.c12 r ∧ ¬ r S.a₃ S.a₁) = S.ev S.c12 := by
    ext ω
    simp only [mem_ev, c12]
    exact ⟨fun h => h.1, fun ⟨h12, h13⟩ => ⟨⟨h12, h13⟩, fun h31 => h13 (rB.symm h31)⟩⟩
  have e23 : S.ev (fun r => S.c23 r ∧ ¬ r S.a₃ S.a₁) = S.ev S.c23 := by
    ext ω
    simp only [mem_ev, c23]
    exact ⟨fun h => h.1, fun ⟨h12, h13, h23⟩ => ⟨⟨h12, h13, h23⟩, fun h31 => h13 (rB.symm h31)⟩⟩
  have eM : S.ev (fun r => S.cM r ∧ ¬ r S.a₃ S.a₁) = S.ev S.cM := by
    ext ω
    simp only [mem_ev, cM]
    exact ⟨fun h => h.1, fun ⟨h12, h13, h23⟩ => ⟨⟨h12, h13, h23⟩, fun h31 => h13 (rB.symm h31)⟩⟩
  rw [S.real_conn_inter_ev hx (fun r => S.c123 r ∧ ¬ r S.a₃ S.a₁) S.F123 (fun ω h => S.glue_c123 ω h.1),
    S.real_conn_inter_ev hx (fun r => S.c12 r ∧ ¬ r S.a₃ S.a₁) S.F12 (fun ω h => S.glue_c12 ω h.1),
    S.real_conn_inter_ev hx (fun r => S.c13 r ∧ ¬ r S.a₃ S.a₁) S.F13 (fun ω h => S.glue_c13 ω h.1),
    S.real_conn_inter_ev hx (fun r => S.c23 r ∧ ¬ r S.a₃ S.a₁) S.F23 (fun ω h => S.glue_c23 ω h.1),
    S.real_conn_inter_ev hx (fun r => S.cM r ∧ ¬ r S.a₃ S.a₁) ∅ (fun ω h => S.glue_cM ω h.1),
    z123, z13, e12, e23, eM, measureReal_empty]
  ring

/-! #### The inputs: (12)–(13) from Lemma 3(ii), (9) from Lemma 4 on `T`, Lemma 1 in `B` -/

omit [Fintype V] in
/-- The event `{a₃ ↮ x in B}` is a decreasing event of the open cluster of `a₃` (it reads
`C_{a₃} ∩ E_B`). [cite: KozmaNitzan2024, proof of Thm. 3, (12) (p. 11: "{a₃ ↮ a₂} is a decreasing event in the cluster a₃")] -/
theorem ev_not_rb_eq_cluster (x : V) :
    S.ev (fun r => ¬ r S.a₃ x) =
      {ω | openEdgeCluster ω S.a₃ ∈ {C : Set (Sym2 V) | ¬ (openGraph (C ∩ S.EB)).Reachable S.a₃ x}} := by
  ext ω
  simp only [mem_ev, rb, rB, mem_setOf_eq]
  rw [reachable_inter_iff_cluster ω (sideB S.VB S.A) ({S.a₃} : Set V) (mem_singleton _) x]
  simp only [mem_singleton_iff, iUnion_iUnion_eq_left]
  rfl

/-- **(13)**: `0 ≤ P_B(a₁↔a₂↮a₃)(q^{(12)}_1 − q^{(12)}_3) + P(M)(q_1 − q_3)` — from (12), Lemma 3(ii) with the
decreasing cluster event `Q = {a₃ ↮ a₂ in B}` (this is the reading of "{a₃ ↮ a₂}" under which "(12)
broken according to the connection patterns in `B`" is (13)), decomposed by `connQ_decomp`.
[cite: KozmaNitzan2024, proof of Thm. 3, (12)–(13) (p. 11)] -/
theorem eq13 (h31 : (prodBernoulli S.w).real (openConn S.a₃ S.b) ≤ (prodBernoulli S.w).real (openConn S.a₁ S.b)) :
    0 ≤ (prodBernoulli S.w).real (S.ev S.c12) * (S.Q S.F12 S.a₁ - S.Q S.F12 S.a₃) +
      (prodBernoulli S.w).real (S.ev S.cM) * (S.Q ∅ S.a₁ - S.Q ∅ S.a₃) := by
  have hlow : IsLowerSet {C : Set (Sym2 V) | ¬ (openGraph (C ∩ S.EB)).Reachable S.a₃ S.a₂} :=
    fun C C' hCC' hC h => hC (h.mono (openGraph_mono (Set.inter_subset_inter_left _ hCC')))
  have L3 := KozmaNitzan2024_lemma3_ii S.w S.a₃ S.a₁ S.b le_rfl (by simpa using h31) hlow
  rw [add_zero, ← S.ev_not_rb_eq_cluster S.a₂, S.connQ_decomp S.ha₃, S.connQ_decomp S.ha₁, S.Q13_13] at L3
  linarith

/-- **(13) with `a₁`, `a₂` swapped**: `0 ≤ P_B(a₁↔a₂↮a₃)(q^{(12)}_1 − q^{(12)}_3) + P(M)(q_2 − q_3)`
(Lemma 3(ii) with `Q = {a₃ ↮ a₁ in B}` and `connQ'_decomp`; `q^{(12)}_2 = q^{(12)}_1`).
[cite: KozmaNitzan2024, proof of Thm. 3, after (13) (p. 11)] -/
theorem eq13' (h32 : (prodBernoulli S.w).real (openConn S.a₃ S.b) ≤ (prodBernoulli S.w).real (openConn S.a₂ S.b)) :
    0 ≤ (prodBernoulli S.w).real (S.ev S.c12) * (S.Q S.F12 S.a₁ - S.Q S.F12 S.a₃) +
      (prodBernoulli S.w).real (S.ev S.cM) * (S.Q ∅ S.a₂ - S.Q ∅ S.a₃) := by
  have hlow : IsLowerSet {C : Set (Sym2 V) | ¬ (openGraph (C ∩ S.EB)).Reachable S.a₃ S.a₁} :=
    fun C C' hCC' hC h => hC (h.mono (openGraph_mono (Set.inter_subset_inter_left _ hCC')))
  have L3 := KozmaNitzan2024_lemma3_ii S.w S.a₃ S.a₂ S.b le_rfl (by simpa using h32) hlow
  rw [add_zero, ← S.ev_not_rb_eq_cluster S.a₁, S.connQ'_decomp S.ha₃, S.connQ'_decomp S.ha₂, S.Q23_23,
    ← S.Q12_12] at L3
  linarith

/-- `q^{(F)}_x` is a connection probability of the glued graph `T^{(F)}`. [cite: KozmaNitzan2024, proof of Thm. 3 (p. 10)] -/
theorem Q_eq_uT (F : Set (Sym2 V)) (hF : ∀ e ∈ F, e ∉ S.ET) (x : V) :
    S.Q F x = (prodBernoulli (S.uT F)).real (openConn x S.b) :=
  S.real_rt_eq F hF (fun r => r x S.b)

/-- **(9) for the graph `T`** (Lemma 4 applied "to the graph `T` and the points `a₁, a₂, a₃, b`"):
`q_{12} − q^{(12)}_3 ≥ min_{j=1,2} (q_j − q_3)`, where `q_{12} = q^{(12)}_1`. [cite: KozmaNitzan2024, proof of Thm. 3 (p. 11, "we are in a position to apply lemma 4")] -/
theorem eq9T :
    min (S.Q ∅ S.a₁ - S.Q ∅ S.a₃) (S.Q ∅ S.a₂ - S.Q ∅ S.a₃) ≤ S.Q S.F12 S.a₁ - S.Q S.F12 S.a₃ := by
  classical
  have hupd : Function.update (S.uT ∅) s(S.a₁, S.a₂) 1 = S.uT S.F12 := by
    funext e
    by_cases he : e = s(S.a₁, S.a₂)
    · subst he; simp [uT, F12]
    · rw [Function.update_of_ne he]; simp [uT, F12, he]
  have L4 := KozmaNitzan2024_lemma4_glued (S.uT ∅) S.a₁ S.a₂ S.a₃ S.b
  rw [hupd] at L4
  rwa [S.Q_eq_uT ∅ S.empty_off, S.Q_eq_uT ∅ S.empty_off, S.Q_eq_uT ∅ S.empty_off,
    S.Q_eq_uT S.F12 S.F12_off, S.Q_eq_uT S.F12 S.F12_off]

/-! #### Lemma 1 in the graph `B` -/

omit [Fintype V] in
/-- Reading `{0 ↔ A(X)}` on `C_{A(X)}`: `0 ∈ A(X)` or some edge of `C_{A(X)}` contains `0`.
[cite: KozmaNitzan2024, Lemma 1 (p. 5); VandenbergHaggstromKahn2005, §1 p. 3] -/
theorem conv_o (X : Set V) (ω : BondConfig V) :
    (S.o ∈ X ∨ ∃ e ∈ ⋃ s ∈ X, openEdgeCluster ω s, S.o ∈ e) ↔ ∃ s ∈ X, (openGraph ω).Reachable S.o s := by
  constructor
  · rintro (h | ⟨e, he, hoe⟩)
    · exact ⟨S.o, h, SimpleGraph.Reachable.refl _⟩
    · obtain ⟨s, hs, hes⟩ := mem_iUnion₂.1 he
      exact ⟨s, hs, ((reachable_iff_exists_mem_openEdgeCluster ω s S.o).2 (Or.inr ⟨e, hes, hoe⟩)).symm⟩
  · rintro ⟨s, hs, h⟩
    by_cases hso : S.o = s
    · exact Or.inl (hso ▸ hs)
    · rcases (reachable_iff_exists_mem_openEdgeCluster ω s S.o).1 h.symm with h' | ⟨e, hes, hoe⟩
      · exact absurd h' hso
      · exact Or.inr ⟨e, mem_iUnion₂.2 ⟨s, hs, hes⟩, hoe⟩

/-- **(X) — Lemma 1 twice on `B` with `X = {1,2}`** (p. 11: "`P_B(0 ↔ a₁ ↔ a₂ | a₁ ↔ a₂, A(1,2) ↮ a₃)
≥ P_B(0 ↔ A(1,2) | A(1,2) ↮ a₃) ≥ P_B(0 ↔ A(1,2) | M) = P_B(0 ↔ a₁ | M) + P_B(0 ↔ a₂ | M)`"), in the
denominator-free form `x₁₂ · P(M) ≥ p₁₂ · (z₁ + z₂)` with `x₁₂ = P_B(0 ↔ a₁ ↔ a₂, A(1,2) ↮ a₃)`,
`p₁₂ = P_B(a₁ ↔ a₂ ↮ a₃)`, `z_j = P_B(0 ↔ a_j, M)`. [cite: KozmaNitzan2024, proof of Thm. 3 (p. 11) with Lemma 1 (i),(ii) (pp. 5–6)] -/
theorem factX :
    (prodBernoulli S.w).real (S.ev S.c12) *
        ((prodBernoulli S.w).real (S.ev fun r => S.cM r ∧ r S.o S.a₁) +
          (prodBernoulli S.w).real (S.ev fun r => S.cM r ∧ r S.o S.a₂)) ≤
      (prodBernoulli S.w).real (S.ev fun r => S.c12 r ∧ r S.o S.a₁) *
        (prodBernoulli S.w).real (S.ev S.cM) := by
  classical
  set X : Set V := {S.a₁, S.a₂} with hX
  set Y : Set V := {S.a₃} with hY
  set ν := prodBernoulli S.wB with hν
  -- the events, as `B`-predicates
  set ΦD : (V → V → Prop) → Prop := fun r => ¬ r S.a₁ S.a₃ ∧ ¬ r S.a₂ S.a₃ with hΦD
  have hD : {ω : BondConfig V | ∀ s ∈ X, ∀ t ∈ Y, ¬ (openGraph ω).Reachable s t} =
      {ω | ΦD (fun x y => (openGraph ω).Reachable x y)} := by
    ext ω; simp [hX, hY, hΦD]
  have hP : ∀ ω : BondConfig V, (S.o ∈ X ∨ ∃ e ∈ ⋃ s ∈ X, openEdgeCluster ω s, S.o ∈ e) ↔
      ((openGraph ω).Reachable S.o S.a₁ ∨ (openGraph ω).Reachable S.o S.a₂) := by
    intro ω; rw [S.conv_o X ω]; simp [hX]
  have hQ : ∀ ω : BondConfig V, (openGraph (⋃ s ∈ X, openEdgeCluster ω s)).Reachable S.a₁ S.a₂ ↔
      (openGraph ω).Reachable S.a₁ S.a₂ :=
    fun ω => (reachable_iff_cluster ω X (by simp [hX]) S.a₂).symm
  -- Lemma 1 (i): `Q = {a₁ ↔ a₂}` increasing on `C_{A(1,2)}`
  have key₁ := bhk_set_event_pos S.wB X Y
    (fun C _ => S.o ∈ X ∨ ∃ e ∈ C, S.o ∈ e) (fun C _ => (openGraph C).Reachable S.a₁ S.a₂)
    (fun _ C C' hCC' h => h.imp id fun ⟨e, he, hoe⟩ => ⟨e, hCC' he, hoe⟩) (fun _ _ _ _ h => h)
    (fun _ C C' hCC' h => h.mono (openGraph_mono hCC')) (fun _ _ _ _ h => h)
  -- Lemma 1 (ii): `Q = {a₁ ↮ a₂}` decreasing on `C_{A(1,2)}`
  have key₂ := bhk_set_event_neg S.wB X Y
    (fun C _ => S.o ∈ X ∨ ∃ e ∈ C, S.o ∈ e) (fun C _ => ¬ (openGraph C).Reachable S.a₁ S.a₂)
    (fun _ C C' hCC' h => h.imp id fun ⟨e, he, hoe⟩ => ⟨e, hCC' he, hoe⟩) (fun _ _ _ _ h => h)
    (fun _ C C' hCC' h h' => h (h'.mono (openGraph_mono hCC'))) (fun _ _ _ _ h => h)
  rw [hD] at key₁ key₂
  -- identify the six probabilities
  have e0 : ν.real {ω | ΦD (fun x y => (openGraph ω).Reachable x y)} = (prodBernoulli S.w).real (S.ev ΦD) :=
    (S.real_rb_eq ΦD).symm
  have eP : ν.real ({ω | ΦD (fun x y => (openGraph ω).Reachable x y)} ∩
      {ω | S.o ∈ X ∨ ∃ e ∈ ⋃ s ∈ X, openEdgeCluster ω s, S.o ∈ e}) =
      (prodBernoulli S.w).real (S.ev fun r => ΦD r ∧ (r S.o S.a₁ ∨ r S.o S.a₂)) := by
    rw [S.real_ev_eq]; congr 1; ext ω; simp only [mem_inter_iff, mem_setOf_eq, hP]
  have eQ : ν.real ({ω | ΦD (fun x y => (openGraph ω).Reachable x y)} ∩
      {ω | (openGraph (⋃ s ∈ X, openEdgeCluster ω s)).Reachable S.a₁ S.a₂}) =
      (prodBernoulli S.w).real (S.ev S.c12) := by
    rw [S.real_ev_eq]; congr 1; ext ω
    simp only [mem_inter_iff, mem_setOf_eq, hQ, hΦD, c12]
    constructor
    · rintro ⟨⟨h13, _⟩, h12⟩; exact ⟨h12, h13⟩
    · rintro ⟨h12, h13⟩; exact ⟨⟨h13, fun h23 => h13 (h12.trans h23)⟩, h12⟩
  have ePQ : ν.real ({ω | ΦD (fun x y => (openGraph ω).Reachable x y)} ∩
      ({ω | S.o ∈ X ∨ ∃ e ∈ ⋃ s ∈ X, openEdgeCluster ω s, S.o ∈ e} ∩
        {ω | (openGraph (⋃ s ∈ X, openEdgeCluster ω s)).Reachable S.a₁ S.a₂})) =
      (prodBernoulli S.w).real (S.ev fun r => S.c12 r ∧ r S.o S.a₁) := by
    rw [S.real_ev_eq]; congr 1; ext ω
    simp only [mem_inter_iff, mem_setOf_eq, hP, hQ, hΦD, c12]
    constructor
    · rintro ⟨⟨h13, _⟩, ho, h12⟩
      refine ⟨⟨h12, h13⟩, ho.elim id fun h2 => h2.trans h12.symm⟩
    · rintro ⟨⟨h12, h13⟩, h1⟩
      exact ⟨⟨h13, fun h23 => h13 (h12.trans h23)⟩, Or.inl h1, h12⟩
  have eQ' : ν.real ({ω | ΦD (fun x y => (openGraph ω).Reachable x y)} ∩
      {ω | ¬ (openGraph (⋃ s ∈ X, openEdgeCluster ω s)).Reachable S.a₁ S.a₂}) =
      (prodBernoulli S.w).real (S.ev S.cM) := by
    rw [S.real_ev_eq]; congr 1; ext ω
    simp only [mem_inter_iff, mem_setOf_eq, hQ, hΦD, cM]
    tauto
  have ePQ' : ν.real ({ω | ΦD (fun x y => (openGraph ω).Reachable x y)} ∩
      ({ω | S.o ∈ X ∨ ∃ e ∈ ⋃ s ∈ X, openEdgeCluster ω s, S.o ∈ e} ∩
        {ω | ¬ (openGraph (⋃ s ∈ X, openEdgeCluster ω s)).Reachable S.a₁ S.a₂})) =
      (prodBernoulli S.w).real (S.ev fun r => S.cM r ∧ r S.o S.a₁) +
        (prodBernoulli S.w).real (S.ev fun r => S.cM r ∧ r S.o S.a₂) := by
    have hdisj : Disjoint (S.ev fun r => S.cM r ∧ r S.o S.a₁) (S.ev fun r => S.cM r ∧ r S.o S.a₂) :=
      Set.disjoint_left.2 fun ω ⟨⟨h12, _⟩, h1⟩ ⟨_, h2⟩ => h12 (rB.trans (rB.symm h1) h2)
    have hU : (S.ev fun r => S.cM r ∧ r S.o S.a₁) ∪ (S.ev fun r => S.cM r ∧ r S.o S.a₂) =
        S.ev fun r => S.cM r ∧ (r S.o S.a₁ ∨ r S.o S.a₂) := by
      ext ω; simp only [mem_union, mem_ev]; tauto
    rw [← measureReal_union hdisj MeasurableSet.of_discrete, hU, S.real_ev_eq]
    congr 1; ext ω
    simp only [mem_inter_iff, mem_setOf_eq, hP, hQ, hΦD, cM]
    tauto
  rw [eP, eQ, e0, ePQ] at key₁
  rw [e0, ePQ', eP, eQ'] at key₂
  -- combine: `x₁₂ · P(D) · m ≥ p₁₂ · P(0 ↔ A(1,2), D) · m ≥ p₁₂ · P(D) · (z₁ + z₂)`
  set d := (prodBernoulli S.w).real (S.ev ΦD)
  set pP := (prodBernoulli S.w).real (S.ev fun r => ΦD r ∧ (r S.o S.a₁ ∨ r S.o S.a₂))
  set p12 := (prodBernoulli S.w).real (S.ev S.c12)
  set x12 := (prodBernoulli S.w).real (S.ev fun r => S.c12 r ∧ r S.o S.a₁)
  set m := (prodBernoulli S.w).real (S.ev S.cM)
  set z := (prodBernoulli S.w).real (S.ev fun r => S.cM r ∧ r S.o S.a₁) +
    (prodBernoulli S.w).real (S.ev fun r => S.cM r ∧ r S.o S.a₂)
  have hd : 0 ≤ d := measureReal_nonneg
  have hm : 0 ≤ m := measureReal_nonneg
  have hp12 : 0 ≤ p12 := measureReal_nonneg
  have hp12d : p12 ≤ d := by
    refine measureReal_mono fun ω h => ?_
    simp only [mem_ev, c12, hΦD] at h ⊢
    exact ⟨h.2, fun h23 => h.2 (rB.trans h.1 h23)⟩
  by_cases hd0 : d = 0
  · have : p12 = 0 := le_antisymm (hd0 ▸ hp12d) hp12
    rw [this, zero_mul]
    exact mul_nonneg measureReal_nonneg hm
  · have hdpos : 0 < d := lt_of_le_of_ne hd (Ne.symm hd0)
    -- key₁ : pP * p12 ≤ d * x12 ; key₂ : d * z ≤ pP * m
    nlinarith [key₁, key₂, mul_le_mul_of_nonneg_right key₁ hm, mul_le_mul_of_nonneg_left key₂ hp12]

/-- **(Y₁) — Lemma 1 twice on `B` with `X = {1}`** (p. 12: "`P_B(0 ↔ a₁ | M) ≥ P_B(0 ↔ a₁ | a₁ ↮ A(2,3))
≥ P_B(0 ↔ a₁ | a₂ ↔ a₃, a₁ ↮ A(2,3))`"), in the denominator-free form `z₁ · p₂₃ ≥ P(M) · y₁` with
`y₁ = P_B(0 ↔ a₁, a₂ ↔ a₃, a₁ ↮ A(2,3))`, `p₂₃ = P_B(a₁ ↮ a₂ ↔ a₃)`. [cite: KozmaNitzan2024, proof of Thm. 3 (p. 12) with Lemma 1 (i),(ii) (pp. 5–6)] -/
theorem factY1 :
    (prodBernoulli S.w).real (S.ev S.cM) * (prodBernoulli S.w).real (S.ev fun r => S.c23 r ∧ r S.o S.a₁) ≤
      (prodBernoulli S.w).real (S.ev fun r => S.cM r ∧ r S.o S.a₁) * (prodBernoulli S.w).real (S.ev S.c23) := by
  classical
  set X : Set V := {S.a₁} with hX
  set Y : Set V := {S.a₂, S.a₃} with hY
  set ν := prodBernoulli S.wB with hν
  set ΦD : (V → V → Prop) → Prop := fun r => ¬ r S.a₁ S.a₂ ∧ ¬ r S.a₁ S.a₃ with hΦD
  have hD : {ω : BondConfig V | ∀ s ∈ X, ∀ t ∈ Y, ¬ (openGraph ω).Reachable s t} =
      {ω | ΦD (fun x y => (openGraph ω).Reachable x y)} := by
    ext ω; simp [hX, hY, hΦD]
  have hP : ∀ ω : BondConfig V, (S.o ∈ X ∨ ∃ e ∈ ⋃ s ∈ X, openEdgeCluster ω s, S.o ∈ e) ↔
      (openGraph ω).Reachable S.o S.a₁ := by
    intro ω; rw [S.conv_o X ω]; simp [hX]
  have hQ : ∀ ω : BondConfig V, (openGraph (⋃ s ∈ Y, openEdgeCluster ω s)).Reachable S.a₂ S.a₃ ↔
      (openGraph ω).Reachable S.a₂ S.a₃ :=
    fun ω => (reachable_iff_cluster ω Y (by simp [hY]) S.a₃).symm
  -- Lemma 1 (i): `Q = {a₂ ↮ a₃}` decreasing on `C_{A(2,3)}`
  have key₁ := bhk_set_event_pos S.wB X Y
    (fun C _ => S.o ∈ X ∨ ∃ e ∈ C, S.o ∈ e) (fun _ D => ¬ (openGraph D).Reachable S.a₂ S.a₃)
    (fun _ C C' hCC' h => h.imp id fun ⟨e, he, hoe⟩ => ⟨e, hCC' he, hoe⟩) (fun _ _ _ _ h => h)
    (fun _ _ _ _ h => h) (fun _ D D' hDD' h h' => h (h'.mono (openGraph_mono hDD')))
  -- Lemma 1 (ii): `Q = {a₂ ↔ a₃}` increasing on `C_{A(2,3)}`
  have key₂ := bhk_set_event_neg S.wB X Y
    (fun C _ => S.o ∈ X ∨ ∃ e ∈ C, S.o ∈ e) (fun _ D => (openGraph D).Reachable S.a₂ S.a₃)
    (fun _ C C' hCC' h => h.imp id fun ⟨e, he, hoe⟩ => ⟨e, hCC' he, hoe⟩) (fun _ _ _ _ h => h)
    (fun _ _ _ _ h => h) (fun _ D D' hDD' h => h.mono (openGraph_mono hDD'))
  rw [hD] at key₁ key₂
  have e0 : ν.real {ω | ΦD (fun x y => (openGraph ω).Reachable x y)} = (prodBernoulli S.w).real (S.ev ΦD) :=
    (S.real_rb_eq ΦD).symm
  have eP : ν.real ({ω | ΦD (fun x y => (openGraph ω).Reachable x y)} ∩
      {ω | S.o ∈ X ∨ ∃ e ∈ ⋃ s ∈ X, openEdgeCluster ω s, S.o ∈ e}) =
      (prodBernoulli S.w).real (S.ev fun r => ΦD r ∧ r S.o S.a₁) := by
    rw [S.real_ev_eq]; congr 1; ext ω; simp only [mem_inter_iff, mem_setOf_eq, hP]
  have eQ : ν.real ({ω | ΦD (fun x y => (openGraph ω).Reachable x y)} ∩
      {ω | ¬ (openGraph (⋃ s ∈ Y, openEdgeCluster ω s)).Reachable S.a₂ S.a₃}) =
      (prodBernoulli S.w).real (S.ev S.cM) := by
    rw [S.real_ev_eq]; congr 1; ext ω
    simp only [mem_inter_iff, mem_setOf_eq, hQ, hΦD, cM]
    tauto
  have ePQ : ν.real ({ω | ΦD (fun x y => (openGraph ω).Reachable x y)} ∩
      ({ω | S.o ∈ X ∨ ∃ e ∈ ⋃ s ∈ X, openEdgeCluster ω s, S.o ∈ e} ∩
        {ω | ¬ (openGraph (⋃ s ∈ Y, openEdgeCluster ω s)).Reachable S.a₂ S.a₃})) =
      (prodBernoulli S.w).real (S.ev fun r => S.cM r ∧ r S.o S.a₁) := by
    rw [S.real_ev_eq]; congr 1; ext ω
    simp only [mem_inter_iff, mem_setOf_eq, hP, hQ, hΦD, cM]
    tauto
  have eQ' : ν.real ({ω | ΦD (fun x y => (openGraph ω).Reachable x y)} ∩
      {ω | (openGraph (⋃ s ∈ Y, openEdgeCluster ω s)).Reachable S.a₂ S.a₃}) =
      (prodBernoulli S.w).real (S.ev S.c23) := by
    rw [S.real_ev_eq]; congr 1; ext ω
    simp only [mem_inter_iff, mem_setOf_eq, hQ, hΦD, c23]
    tauto
  have ePQ' : ν.real ({ω | ΦD (fun x y => (openGraph ω).Reachable x y)} ∩
      ({ω | S.o ∈ X ∨ ∃ e ∈ ⋃ s ∈ X, openEdgeCluster ω s, S.o ∈ e} ∩
        {ω | (openGraph (⋃ s ∈ Y, openEdgeCluster ω s)).Reachable S.a₂ S.a₃})) =
      (prodBernoulli S.w).real (S.ev fun r => S.c23 r ∧ r S.o S.a₁) := by
    rw [S.real_ev_eq]; congr 1; ext ω
    simp only [mem_inter_iff, mem_setOf_eq, hP, hQ, hΦD, c23]
    tauto
  rw [eP, eQ, e0, ePQ] at key₁
  rw [e0, ePQ', eP, eQ'] at key₂
  set d := (prodBernoulli S.w).real (S.ev ΦD)
  set pP := (prodBernoulli S.w).real (S.ev fun r => ΦD r ∧ r S.o S.a₁)
  set p23 := (prodBernoulli S.w).real (S.ev S.c23)
  set y1 := (prodBernoulli S.w).real (S.ev fun r => S.c23 r ∧ r S.o S.a₁)
  set m := (prodBernoulli S.w).real (S.ev S.cM)
  set z1 := (prodBernoulli S.w).real (S.ev fun r => S.cM r ∧ r S.o S.a₁)
  have hd : 0 ≤ d := measureReal_nonneg
  have hm : 0 ≤ m := measureReal_nonneg
  have hp23 : 0 ≤ p23 := measureReal_nonneg
  have hy1 : 0 ≤ y1 := measureReal_nonneg
  have hy1p : y1 ≤ p23 := measureReal_mono fun ω h => h.1
  have hp23d : p23 ≤ d := by
    refine measureReal_mono fun ω h => ?_
    simp only [mem_ev, c23, hΦD] at h ⊢
    exact ⟨h.1, h.2.1⟩
  by_cases hd0 : d = 0
  · have hp : p23 = 0 := le_antisymm (hd0 ▸ hp23d) hp23
    have hy : y1 = 0 := le_antisymm (hp ▸ hy1p) hy1
    rw [hy, hp, mul_zero, mul_zero]
  · have hdpos : 0 < d := lt_of_le_of_ne hd (Ne.symm hd0)
    -- key₁ : pP * m ≤ d * z1 ; key₂ : d * y1 ≤ pP * p23
    nlinarith [key₁, key₂, mul_le_mul_of_nonneg_right key₁ hp23, mul_le_mul_of_nonneg_left key₂ hm]

/-- **(Y₂)** — the same with `a₂` in place of `a₁` ("A similar calculation for `P(0 ↔ a₂ | M)`", p. 12):
`z₂ · p₁₃ ≥ P(M) · y₂` with `y₂ = P_B(0 ↔ a₂, a₁ ↔ a₃, a₂ ↮ A(1,3))`, `p₁₃ = P_B(a₂ ↮ a₁ ↔ a₃)`.
[cite: KozmaNitzan2024, proof of Thm. 3 (p. 12) with Lemma 1 (i),(ii) (pp. 5–6)] -/
theorem factY2 :
    (prodBernoulli S.w).real (S.ev S.cM) * (prodBernoulli S.w).real (S.ev fun r => S.c13 r ∧ r S.o S.a₂) ≤
      (prodBernoulli S.w).real (S.ev fun r => S.cM r ∧ r S.o S.a₂) * (prodBernoulli S.w).real (S.ev S.c13) := by
  classical
  set X : Set V := {S.a₂} with hX
  set Y : Set V := {S.a₁, S.a₃} with hY
  set ν := prodBernoulli S.wB with hν
  set ΦD : (V → V → Prop) → Prop := fun r => ¬ r S.a₂ S.a₁ ∧ ¬ r S.a₂ S.a₃ with hΦD
  have hD : {ω : BondConfig V | ∀ s ∈ X, ∀ t ∈ Y, ¬ (openGraph ω).Reachable s t} =
      {ω | ΦD (fun x y => (openGraph ω).Reachable x y)} := by
    ext ω; simp [hX, hY, hΦD]
  have hP : ∀ ω : BondConfig V, (S.o ∈ X ∨ ∃ e ∈ ⋃ s ∈ X, openEdgeCluster ω s, S.o ∈ e) ↔
      (openGraph ω).Reachable S.o S.a₂ := by
    intro ω; rw [S.conv_o X ω]; simp [hX]
  have hQ : ∀ ω : BondConfig V, (openGraph (⋃ s ∈ Y, openEdgeCluster ω s)).Reachable S.a₁ S.a₃ ↔
      (openGraph ω).Reachable S.a₁ S.a₃ :=
    fun ω => (reachable_iff_cluster ω Y (by simp [hY]) S.a₃).symm
  have key₁ := bhk_set_event_pos S.wB X Y
    (fun C _ => S.o ∈ X ∨ ∃ e ∈ C, S.o ∈ e) (fun _ D => ¬ (openGraph D).Reachable S.a₁ S.a₃)
    (fun _ C C' hCC' h => h.imp id fun ⟨e, he, hoe⟩ => ⟨e, hCC' he, hoe⟩) (fun _ _ _ _ h => h)
    (fun _ _ _ _ h => h) (fun _ D D' hDD' h h' => h (h'.mono (openGraph_mono hDD')))
  have key₂ := bhk_set_event_neg S.wB X Y
    (fun C _ => S.o ∈ X ∨ ∃ e ∈ C, S.o ∈ e) (fun _ D => (openGraph D).Reachable S.a₁ S.a₃)
    (fun _ C C' hCC' h => h.imp id fun ⟨e, he, hoe⟩ => ⟨e, hCC' he, hoe⟩) (fun _ _ _ _ h => h)
    (fun _ _ _ _ h => h) (fun _ D D' hDD' h => h.mono (openGraph_mono hDD'))
  rw [hD] at key₁ key₂
  -- the symmetric readings (`r = ↔_B` is symmetric)
  have rs : ∀ (ω : BondConfig V) (x y : V), S.rb ω x y → S.rb ω y x := fun _ _ _ h => rB.symm h
  have e0 : ν.real {ω | ΦD (fun x y => (openGraph ω).Reachable x y)} = (prodBernoulli S.w).real (S.ev ΦD) :=
    (S.real_rb_eq ΦD).symm
  have eP : ν.real ({ω | ΦD (fun x y => (openGraph ω).Reachable x y)} ∩
      {ω | S.o ∈ X ∨ ∃ e ∈ ⋃ s ∈ X, openEdgeCluster ω s, S.o ∈ e}) =
      (prodBernoulli S.w).real (S.ev fun r => ΦD r ∧ r S.o S.a₂) := by
    rw [S.real_ev_eq]; congr 1; ext ω; simp only [mem_inter_iff, mem_setOf_eq, hP]
  have eQ : ν.real ({ω | ΦD (fun x y => (openGraph ω).Reachable x y)} ∩
      {ω | ¬ (openGraph (⋃ s ∈ Y, openEdgeCluster ω s)).Reachable S.a₁ S.a₃}) =
      (prodBernoulli S.w).real (S.ev S.cM) := by
    rw [S.real_ev_eq]; congr 1; ext ω
    simp only [mem_inter_iff, mem_setOf_eq, hQ, hΦD, cM]
    constructor
    · rintro ⟨⟨h21, h23⟩, h13⟩; exact ⟨fun h => h21 h.symm, h13, h23⟩
    · rintro ⟨h12, h13, h23⟩; exact ⟨⟨fun h => h12 h.symm, h23⟩, h13⟩
  have ePQ : ν.real ({ω | ΦD (fun x y => (openGraph ω).Reachable x y)} ∩
      ({ω | S.o ∈ X ∨ ∃ e ∈ ⋃ s ∈ X, openEdgeCluster ω s, S.o ∈ e} ∩
        {ω | ¬ (openGraph (⋃ s ∈ Y, openEdgeCluster ω s)).Reachable S.a₁ S.a₃})) =
      (prodBernoulli S.w).real (S.ev fun r => S.cM r ∧ r S.o S.a₂) := by
    rw [S.real_ev_eq]; congr 1; ext ω
    simp only [mem_inter_iff, mem_setOf_eq, hP, hQ, hΦD, cM]
    constructor
    · rintro ⟨⟨h21, h23⟩, ho, h13⟩; exact ⟨⟨fun h => h21 h.symm, h13, h23⟩, ho⟩
    · rintro ⟨⟨h12, h13, h23⟩, ho⟩; exact ⟨⟨fun h => h12 h.symm, h23⟩, ho, h13⟩
  have eQ' : ν.real ({ω | ΦD (fun x y => (openGraph ω).Reachable x y)} ∩
      {ω | (openGraph (⋃ s ∈ Y, openEdgeCluster ω s)).Reachable S.a₁ S.a₃}) =
      (prodBernoulli S.w).real (S.ev S.c13) := by
    rw [S.real_ev_eq]; congr 1; ext ω
    simp only [mem_inter_iff, mem_setOf_eq, hQ, hΦD, c13]
    constructor
    · rintro ⟨⟨h21, _⟩, h13⟩; exact ⟨fun h => h21 h.symm, h13⟩
    · rintro ⟨h12, h13⟩; exact ⟨⟨fun h => h12 h.symm, fun h23 => h12 (h13.trans h23.symm)⟩, h13⟩
  have ePQ' : ν.real ({ω | ΦD (fun x y => (openGraph ω).Reachable x y)} ∩
      ({ω | S.o ∈ X ∨ ∃ e ∈ ⋃ s ∈ X, openEdgeCluster ω s, S.o ∈ e} ∩
        {ω | (openGraph (⋃ s ∈ Y, openEdgeCluster ω s)).Reachable S.a₁ S.a₃})) =
      (prodBernoulli S.w).real (S.ev fun r => S.c13 r ∧ r S.o S.a₂) := by
    rw [S.real_ev_eq]; congr 1; ext ω
    simp only [mem_inter_iff, mem_setOf_eq, hP, hQ, hΦD, c13]
    constructor
    · rintro ⟨⟨h21, _⟩, ho, h13⟩; exact ⟨⟨fun h => h21 h.symm, h13⟩, ho⟩
    · rintro ⟨⟨h12, h13⟩, ho⟩; exact ⟨⟨fun h => h12 h.symm, fun h23 => h12 (h13.trans h23.symm)⟩, ho, h13⟩
  rw [eP, eQ, e0, ePQ] at key₁
  rw [e0, ePQ', eP, eQ'] at key₂
  set d := (prodBernoulli S.w).real (S.ev ΦD)
  set pP := (prodBernoulli S.w).real (S.ev fun r => ΦD r ∧ r S.o S.a₂)
  set p13 := (prodBernoulli S.w).real (S.ev S.c13)
  set y2 := (prodBernoulli S.w).real (S.ev fun r => S.c13 r ∧ r S.o S.a₂)
  set m := (prodBernoulli S.w).real (S.ev S.cM)
  set z2 := (prodBernoulli S.w).real (S.ev fun r => S.cM r ∧ r S.o S.a₂)
  have hd : 0 ≤ d := measureReal_nonneg
  have hm : 0 ≤ m := measureReal_nonneg
  have hp13 : 0 ≤ p13 := measureReal_nonneg
  have hy2 : 0 ≤ y2 := measureReal_nonneg
  have hy2p : y2 ≤ p13 := measureReal_mono fun ω h => h.1
  have hp13d : p13 ≤ d := by
    refine measureReal_mono fun ω h => ?_
    simp only [mem_ev, c13, hΦD] at h ⊢
    exact ⟨fun h21 => h.1 (rs _ _ _ h21), fun h23 => h.1 (rB.trans h.2 (rB.symm h23))⟩
  by_cases hd0 : d = 0
  · have hp : p13 = 0 := le_antisymm (hd0 ▸ hp13d) hp13
    have hy : y2 = 0 := le_antisymm (hp ▸ hy2p) hy2
    rw [hy, hp, mul_zero, mul_zero]
  · have hdpos : 0 < d := lt_of_le_of_ne hd (Ne.symm hd0)
    nlinarith [key₁, key₂, mul_le_mul_of_nonneg_right key₁ hp13, mul_le_mul_of_nonneg_left key₂ hm]

/-! #### The degenerate case `P(M) = 0` (not treated in print: the printed proof conditions on `M`) -/

/-- [cite: KozmaNitzan2024, proof of Thm. 3 (pp. 11–12)] -/
theorem m_zero_cases (hm : (prodBernoulli S.w).real (S.ev S.cM) = 0) :
    (prodBernoulli S.w).real (S.ev fun r => ¬ r S.a₁ S.a₂) = 0 ∨
      (prodBernoulli S.w).real (S.ev fun r => ¬ r S.a₁ S.a₃) = 0 ∨
      (prodBernoulli S.w).real (S.ev fun r => ¬ r S.a₂ S.a₃) = 0 := by
  classical
  set ω₁ : BondConfig V := {e | S.w e = 1} with hω₁
  -- almost surely the weight-one pairs are open, so `B`-connections of `ω₁` hold almost surely
  have asure : ∀ x y : V, S.rb ω₁ x y → (prodBernoulli S.w).real (S.ev fun r => ¬ r x y) = 0 := by
    intro x y hxy
    rw [← measureReal_empty (μ := prodBernoulli S.w)]
    refine real_eq_of_inter_sureSet S.w ?_
    rw [Set.empty_inter, Set.eq_empty_iff_forall_notMem]
    rintro ω ⟨h, hs⟩
    refine h (hxy.mono (openGraph_mono (Set.inter_subset_inter_left _ fun e he => (hs e).2 he)))
  by_cases hM : S.cM (S.rb ω₁)
  · -- then the cylinder of `ω₁` on the `B`-side lies in `M` and has positive probability
    exfalso
    have hsub : localCylinder (↑S.EB.toFinset : Set (Sym2 V)) ω₁ ⊆ S.ev S.cM := by
      intro ω hω
      have heq : ω ∩ S.EB = ω₁ ∩ S.EB := by
        ext e
        simp only [mem_inter_iff]
        constructor
        · rintro ⟨he, hE⟩; exact ⟨(hω e (by simpa using hE)).1 he, hE⟩
        · rintro ⟨he, hE⟩; exact ⟨(hω e (by simpa using hE)).2 he, hE⟩
      show S.cM (S.rb ω)
      rwa [S.rb_eq_of_inter_eq heq]
    have hpos : 0 < (prodBernoulli S.w).real (localCylinder (↑S.EB.toFinset : Set (Sym2 V)) ω₁) := by
      rw [Percolation.Literature.LatticeModels.prodBernoulli_real_localCylinder S.w S.EB.toFinset ω₁]
      refine mul_pos (Finset.prod_pos fun e he => ?_) (Finset.prod_pos fun e he => ?_)
      · have : S.w e = 1 := (Finset.mem_filter.1 he).2
        rw [this]; norm_num
      · have hne : S.w e ≠ 1 := (Finset.mem_filter.1 he).2
        have hle : (S.w e : ℝ) ≤ 1 := (S.w e).2.2
        have hne' : (S.w e : ℝ) ≠ 1 := fun h => hne (Subtype.ext h)
        linarith [lt_of_le_of_ne hle hne']
    have := measureReal_mono (μ := prodBernoulli S.w) hsub
    linarith
  · simp only [cM, not_and, not_not] at hM
    by_cases h12 : S.rb ω₁ S.a₁ S.a₂
    · exact Or.inl (asure _ _ h12)
    · by_cases h13 : S.rb ω₁ S.a₁ S.a₃
      · exact Or.inr (Or.inl (asure _ _ h13))
      · exact Or.inr (Or.inr (asure _ _ (hM h12 h13)))

/-! #### Conclusion of the proof of Theorem 3 -/

/-- An elementary sign lemma: `0 ≤ x ≤ p` and `0 ≤ p · D` give `0 ≤ x · D`. [folklore] -/
theorem mul_nonneg_of_le {x p D : ℝ} (hx : 0 ≤ x) (hxp : x ≤ p) (hpD : 0 ≤ p * D) : 0 ≤ x * D := by
  by_cases hD : 0 ≤ D
  · exact mul_nonneg hx hD
  · have hD' : D < 0 := lt_of_not_ge hD
    have hp : p ≤ 0 := by nlinarith
    have : x = 0 := le_antisymm (hxp.trans hp) hx
    rw [this, zero_mul]

/-- `P(0 ↔ b, 0 ↔ A) = P(0 ↔ b)`: when `A` separates `0` from `b`, every open path from `0` to `b`
meets `A`. [cite: KozmaNitzan2024, proof of Thm. 3 (p. 10: "we will show … P(0 ↔ b) ≥ P(0 ↔ A, a₃ ↔ b), which will prove the theorem")] -/
theorem real_oconn_inter_oA :
    (prodBernoulli S.w).real (openConn S.o S.b ∩ S.oA) = (prodBernoulli S.w).real (openConn S.o S.b) := by
  refine real_eq_of_inter_sureSet S.w ?_
  ext ω
  simp only [mem_inter_iff]
  constructor
  · rintro ⟨⟨h, -⟩, hs⟩; exact ⟨h, hs⟩
  · rintro ⟨h, hs⟩
    have hω := S.sureSet_subset_noCross hs
    obtain ⟨a, ha, hoa, -⟩ := (reachable_iff_exists_rB_rT hω S.ho S.hb).1 h
    exact ⟨⟨h, (S.mem_oA_iff ω).2 ⟨a, ha, rB.reachable hoa⟩⟩, hs⟩

/-- **Theorem 3 for the setting, with `a₃` minimising `P(a_j ↔ b)`** (p. 10: "We assume without loss
of generality that `a₃` minimises the probability of connection to `b` … We will show that under this
assumption (3) holds for `a₃`, namely `P(0 ↔ b) ≥ P(0 ↔ A, a₃ ↔ b)`").  The proof is the printed one:
(11), (13) and its mirror image, (14) from Lemma 4 on `T`, the decomposition
`P(0 ↔ b) − P(0 ↔ A, a₃ ↔ b) = α + β₁ + β₂ + γ₁ + γ₂`, and the two double applications of Lemma 1
in `B`; the bookkeeping is done without dividing by `P(M)`, and the case `P(M) = 0` is settled by
`m_zero_cases`. [cite: KozmaNitzan2024, Thm. 3, proof (pp. 10–12)] -/
theorem preFKG_three (h31 : (prodBernoulli S.w).real (openConn S.a₃ S.b) ≤ (prodBernoulli S.w).real (openConn S.a₁ S.b))
    (h32 : (prodBernoulli S.w).real (openConn S.a₃ S.b) ≤ (prodBernoulli S.w).real (openConn S.a₂ S.b)) :
    (prodBernoulli S.w).real (S.oA ∩ openConn S.a₃ S.b) ≤
      (prodBernoulli S.w).real (openConn S.o S.b ∩ S.oA) := by
  rw [S.real_oconn_inter_oA, ← sub_nonneg, S.o_decomp]
  -- the quantities
  set p12 := (prodBernoulli S.w).real (S.ev S.c12) with hp12
  set p13 := (prodBernoulli S.w).real (S.ev S.c13) with hp13
  set p23 := (prodBernoulli S.w).real (S.ev S.c23) with hp23
  set m := (prodBernoulli S.w).real (S.ev S.cM) with hm
  set x12 := (prodBernoulli S.w).real (S.ev fun r => S.c12 r ∧ r S.o S.a₁) with hx12
  set y1 := (prodBernoulli S.w).real (S.ev fun r => S.c23 r ∧ r S.o S.a₁) with hy1
  set y2 := (prodBernoulli S.w).real (S.ev fun r => S.c13 r ∧ r S.o S.a₂) with hy2
  set z1 := (prodBernoulli S.w).real (S.ev fun r => S.cM r ∧ r S.o S.a₁) with hz1
  set z2 := (prodBernoulli S.w).real (S.ev fun r => S.cM r ∧ r S.o S.a₂) with hz2
  set D12 := S.Q S.F12 S.a₁ - S.Q S.F12 S.a₃ with hD12
  set D23 := S.Q S.F23 S.a₁ - S.Q S.F23 S.a₃ with hD23
  set D13 := S.Q S.F13 S.a₂ - S.Q S.F13 S.a₃ with hD13
  set E1 := S.Q ∅ S.a₁ - S.Q ∅ S.a₃ with hE1
  set E2 := S.Q ∅ S.a₂ - S.Q ∅ S.a₃ with hE2
  -- the inputs
  have e11 : 0 ≤ p12 * D12 + p23 * D23 + m * E1 := by
    have := S.eq11; rw [← hp12, ← hp23, ← hm, ← hD12, ← hD23, ← hE1] at this; linarith
  have e11' : 0 ≤ p12 * D12 + p13 * D13 + m * E2 := by
    have := S.eq11'; rw [← hp12, ← hp13, ← hm, ← hD12, ← hD13, ← hE2] at this; linarith
  have e13 : 0 ≤ p12 * D12 + m * E1 := S.eq13 h31
  have e13' : 0 ≤ p12 * D12 + m * E2 := S.eq13' h32
  have e9 : min E1 E2 ≤ D12 := S.eq9T
  have fX : p12 * (z1 + z2) ≤ x12 * m := S.factX
  have fY1 : m * y1 ≤ z1 * p23 := S.factY1
  have fY2 : m * y2 ≤ z2 * p13 := S.factY2
  -- nonnegativity and monotonicity of the cells
  have hp12_0 : 0 ≤ p12 := measureReal_nonneg
  have hp13_0 : 0 ≤ p13 := measureReal_nonneg
  have hp23_0 : 0 ≤ p23 := measureReal_nonneg
  have hm_0 : 0 ≤ m := measureReal_nonneg
  have hx12_0 : 0 ≤ x12 := measureReal_nonneg
  have hy1_0 : 0 ≤ y1 := measureReal_nonneg
  have hy2_0 : 0 ≤ y2 := measureReal_nonneg
  have hz1_0 : 0 ≤ z1 := measureReal_nonneg
  have hz2_0 : 0 ≤ z2 := measureReal_nonneg
  have hx12p : x12 ≤ p12 := measureReal_mono fun ω h => h.1
  have hy1p : y1 ≤ p23 := measureReal_mono fun ω h => h.1
  have hy2p : y2 ≤ p13 := measureReal_mono fun ω h => h.1
  have hz1m : z1 ≤ m := measureReal_mono fun ω h => h.1
  have hz2m : z2 ≤ m := measureReal_mono fun ω h => h.1
  -- (14): `q₁₂ − q^{(12)}_3 ≥ 0` "Indeed, if it were negative, so must be `q_j − q_3` leading to a
  -- contradiction to (13)" — precisely: `D12 ≥ 0` unless `p12 = 0`
  have e14 : p12 = 0 ∨ 0 ≤ D12 := by
    by_cases hD : 0 ≤ D12
    · exact Or.inr hD
    · left
      have hD' : D12 < 0 := lt_of_not_ge hD
      have hpD : 0 ≤ p12 * D12 := by
        rcases le_total E1 E2 with hE | hE
        · rw [min_eq_left hE] at e9
          have : m * E1 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hm_0 (by linarith)
          linarith
        · rw [min_eq_right hE] at e9
          have : m * E2 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hm_0 (by linarith)
          linarith
      by_contra hp
      have hp' : 0 < p12 := lt_of_le_of_ne hp12_0 (Ne.symm hp)
      linarith [mul_neg_of_pos_of_neg hp' hD']
  have hxD : 0 ≤ x12 * D12 := by
    rcases e14 with h0 | hD
    · have : x12 = 0 := le_antisymm (h0 ▸ hx12p) hx12_0
      rw [this, zero_mul]
    · exact mul_nonneg hx12_0 hD
  by_cases hm0 : m = 0
  · -- the degenerate case: two points of `A` are a.s. joined in `B`
    have hz1 : z1 = 0 := le_antisymm (hm0 ▸ hz1m) hz1_0
    have hz2 : z2 = 0 := le_antisymm (hm0 ▸ hz2m) hz2_0
    rw [hz1, hz2, zero_mul, zero_mul, add_zero, add_zero]
    rcases S.m_zero_cases hm0 with h | h | h
    · -- `a₁ ↔_B a₂` a.s.: `p13 = p23 = 0`
      have hp13z : p13 = 0 := le_antisymm (le_trans (measureReal_mono fun ω hω => hω.1) h.le) hp13_0
      have hp23z : p23 = 0 := le_antisymm (le_trans (measureReal_mono fun ω hω => hω.1) h.le) hp23_0
      have hy1z : y1 = 0 := le_antisymm (hp23z ▸ hy1p) hy1_0
      have hy2z : y2 = 0 := le_antisymm (hp13z ▸ hy2p) hy2_0
      rw [hy1z, hy2z, zero_mul, zero_mul, add_zero, add_zero]
      exact hxD
    · -- `a₁ ↔_B a₃` a.s.: `p12 = p23 = 0`
      have hp12z : p12 = 0 := le_antisymm (le_trans (measureReal_mono fun ω hω => hω.2) h.le) hp12_0
      have hp23z : p23 = 0 := le_antisymm (le_trans (measureReal_mono fun ω hω => hω.2.1) h.le) hp23_0
      have hx : x12 = 0 := le_antisymm (hp12z ▸ hx12p) hx12_0
      have hy : y1 = 0 := le_antisymm (hp23z ▸ hy1p) hy1_0
      have hpD : 0 ≤ p13 * D13 := by rw [hp12z, hm0] at e11'; linarith
      have : 0 ≤ y2 * D13 := mul_nonneg_of_le hy2_0 hy2p hpD
      rw [hx, hy, zero_mul, zero_mul, zero_add, zero_add]
      exact this
    · -- `a₂ ↔_B a₃` a.s.: `p12 = p13 = 0`
      have hp12z : p12 = 0 := by
        refine le_antisymm (le_trans (measureReal_mono fun ω hω => ?_) h.le) hp12_0
        simp only [mem_ev, c12] at hω ⊢; exact fun h23 => hω.2 (rB.trans hω.1 h23)
      have hp13z : p13 = 0 := by
        refine le_antisymm (le_trans (measureReal_mono fun ω hω => ?_) h.le) hp13_0
        simp only [mem_ev, c13] at hω ⊢; exact fun h23 => hω.1 (rB.trans hω.2 (rB.symm h23))
      have hx : x12 = 0 := le_antisymm (hp12z ▸ hx12p) hx12_0
      have hy : y2 = 0 := le_antisymm (hp13z ▸ hy2p) hy2_0
      have hpD : 0 ≤ p23 * D23 := by rw [hp12z, hm0] at e11; linarith
      have : 0 ≤ y1 * D23 := mul_nonneg_of_le hy1_0 hy1p hpD
      rw [hx, hy, zero_mul, zero_mul, zero_add, add_zero]
      exact this
  · -- the printed chain, multiplied through by `P(M) > 0`
    have hmpos : 0 < m := lt_of_le_of_ne hm_0 (Ne.symm hm0)
    -- `α ≥ (P_B(0↔a₁|M) + P_B(0↔a₂|M)) · p12 · D12`
    have hα : p12 * (z1 + z2) * D12 ≤ m * (x12 * D12) := by
      rcases e14 with h0 | hD
      · have : x12 = 0 := le_antisymm (h0 ▸ hx12p) hx12_0
        rw [h0, this]; ring_nf; exact le_rfl
      · have := mul_le_mul_of_nonneg_right fX hD
        linarith [show x12 * m * D12 = m * (x12 * D12) by ring]
    -- `β₁ + δ₁ ≥ 0` and `β₂ + δ₂ ≥ 0`
    have claim1 : 0 ≤ z1 * (p12 * D12 + m * E1) + m * (y1 * D23) := by
      by_cases hp : p23 = 0
      · have : y1 = 0 := le_antisymm (hp ▸ hy1p) hy1_0
        rw [this, zero_mul, mul_zero, add_zero]
        exact mul_nonneg hz1_0 e13
      · have hppos : 0 < p23 := lt_of_le_of_ne hp23_0 (Ne.symm hp)
        have t1 : m * y1 * (p12 * D12 + m * E1) ≤ z1 * p23 * (p12 * D12 + m * E1) :=
          mul_le_mul_of_nonneg_right fY1 e13
        have t2 : 0 ≤ m * y1 * (p12 * D12 + m * E1 + p23 * D23) :=
          mul_nonneg (mul_nonneg hm_0 hy1_0) (by linarith)
        have key : 0 ≤ p23 * (z1 * (p12 * D12 + m * E1) + m * (y1 * D23)) := by
          have expand : p23 * (z1 * (p12 * D12 + m * E1) + m * (y1 * D23)) =
              z1 * p23 * (p12 * D12 + m * E1) + m * y1 * (p23 * D23) := by ring
          have expand2 : m * y1 * (p12 * D12 + m * E1 + p23 * D23) =
              m * y1 * (p12 * D12 + m * E1) + m * y1 * (p23 * D23) := by ring
          linarith
        exact (mul_nonneg_iff_of_pos_left hppos).1 key
    have claim2 : 0 ≤ z2 * (p12 * D12 + m * E2) + m * (y2 * D13) := by
      by_cases hp : p13 = 0
      · have : y2 = 0 := le_antisymm (hp ▸ hy2p) hy2_0
        rw [this, zero_mul, mul_zero, add_zero]
        exact mul_nonneg hz2_0 e13'
      · have hppos : 0 < p13 := lt_of_le_of_ne hp13_0 (Ne.symm hp)
        have t1 : m * y2 * (p12 * D12 + m * E2) ≤ z2 * p13 * (p12 * D12 + m * E2) :=
          mul_le_mul_of_nonneg_right fY2 e13'
        have t2 : 0 ≤ m * y2 * (p12 * D12 + m * E2 + p13 * D13) :=
          mul_nonneg (mul_nonneg hm_0 hy2_0) (by linarith)
        have key : 0 ≤ p13 * (z2 * (p12 * D12 + m * E2) + m * (y2 * D13)) := by
          have expand : p13 * (z2 * (p12 * D12 + m * E2) + m * (y2 * D13)) =
              z2 * p13 * (p12 * D12 + m * E2) + m * y2 * (p13 * D13) := by ring
          have expand2 : m * y2 * (p12 * D12 + m * E2 + p13 * D13) =
              m * y2 * (p12 * D12 + m * E2) + m * y2 * (p13 * D13) := by ring
          linarith
        exact (mul_nonneg_iff_of_pos_left hppos).1 key
    have total : 0 ≤ m * (x12 * D12 + y1 * D23 + y2 * D13 + z1 * E1 + z2 * E2) := by
      have expand : m * (x12 * D12 + y1 * D23 + y2 * D13 + z1 * E1 + z2 * E2) =
          m * (x12 * D12) + m * (y1 * D23) + m * (y2 * D13) + m * z1 * E1 + m * z2 * E2 := by ring
      have expand2 : z1 * (p12 * D12 + m * E1) + z2 * (p12 * D12 + m * E2) =
          p12 * (z1 + z2) * D12 + m * z1 * E1 + m * z2 * E2 := by ring
      linarith
    exact (mul_nonneg_iff_of_pos_left hmpos).1 total

/-! #### Symmetries of the setting and the choice of the minimiser `a₃` -/

/-- The setting with `a₁` and `a₂` exchanged. [folklore] -/
def swap12 : SepData V where
  w := S.w
  VB := S.VB
  o := S.o
  b := S.b
  a₁ := S.a₂
  a₂ := S.a₁
  a₃ := S.a₃
  ho := S.ho
  hb := S.hb
  ha₁ := S.ha₂
  ha₂ := S.ha₁
  ha₃ := S.ha₃
  h₁₂ := S.h₁₂.symm
  h₁₃ := S.h₂₃
  h₂₃ := S.h₁₃
  hb₁ := S.hb₂
  hb₂ := S.hb₁
  hb₃ := S.hb₃
  hcut := by
    intro e h1 h2
    have hA : ({S.a₂, S.a₁, S.a₃} : Set V) = {S.a₁, S.a₂, S.a₃} := Set.insert_comm _ _ _
    rw [hA] at h1 h2
    exact S.hcut e h1 h2

/-- The setting with `a₂` and `a₃` exchanged. [folklore] -/
def swap23 : SepData V where
  w := S.w
  VB := S.VB
  o := S.o
  b := S.b
  a₁ := S.a₁
  a₂ := S.a₃
  a₃ := S.a₂
  ho := S.ho
  hb := S.hb
  ha₁ := S.ha₁
  ha₂ := S.ha₃
  ha₃ := S.ha₂
  h₁₂ := S.h₁₃
  h₁₃ := S.h₁₂
  h₂₃ := S.h₂₃.symm
  hb₁ := S.hb₁
  hb₂ := S.hb₃
  hb₃ := S.hb₂
  hcut := by
    intro e h1 h2
    have hA : ({S.a₁, S.a₃, S.a₂} : Set V) = {S.a₁, S.a₂, S.a₃} := by
      show insert S.a₁ ({S.a₃, S.a₂} : Set V) = insert S.a₁ {S.a₂, S.a₃}
      rw [Set.pair_comm]
    rw [hA] at h1 h2
    exact S.hcut e h1 h2

omit [Fintype V] in
/-- `{0 ↔ A}` is invariant under exchanging `a₁, a₂`. [folklore] -/
theorem oA_swap12 : S.swap12.oA = S.oA := by
  ext ω; simp only [oA, swap12, mem_union]; tauto

omit [Fintype V] in
/-- `{0 ↔ A}` is invariant under exchanging `a₂, a₃`. [folklore] -/
theorem oA_swap23 : S.swap23.oA = S.oA := by
  ext ω; simp only [oA, swap23, mem_union]; tauto

/-- **Theorem 3 for the setting**: some `a ∈ A` satisfies `P(a ↔ b, 0 ↔ A) ≤ P(0 ↔ b, 0 ↔ A)` — namely a
minimiser of `P(a ↔ b)` (p. 10, "without loss of generality"). [cite: KozmaNitzan2024, Thm. 3 (p. 10)] -/
theorem thm3 : ∃ a ∈ S.A, (prodBernoulli S.w).real (openConn a S.b ∩ S.oA) ≤
    (prodBernoulli S.w).real (openConn S.o S.b ∩ S.oA) := by
  set m₁ := (prodBernoulli S.w).real (openConn S.a₁ S.b)
  set m₂ := (prodBernoulli S.w).real (openConn S.a₂ S.b)
  set m₃ := (prodBernoulli S.w).real (openConn S.a₃ S.b)
  have case3 : m₃ ≤ m₁ → m₃ ≤ m₂ → ∃ a ∈ S.A, (prodBernoulli S.w).real (openConn a S.b ∩ S.oA) ≤
      (prodBernoulli S.w).real (openConn S.o S.b ∩ S.oA) := fun h31 h32 => by
    refine ⟨S.a₃, S.a₃_mem, ?_⟩
    rw [Set.inter_comm]
    exact S.preFKG_three h31 h32
  have case2 : m₂ ≤ m₁ → m₂ ≤ m₃ → ∃ a ∈ S.A, (prodBernoulli S.w).real (openConn a S.b ∩ S.oA) ≤
      (prodBernoulli S.w).real (openConn S.o S.b ∩ S.oA) := fun h21 h23 => by
    refine ⟨S.a₂, S.a₂_mem, ?_⟩
    have key := S.swap23.preFKG_three h21 h23
    rw [oA_swap23] at key
    rw [Set.inter_comm]
    exact key
  have case1 : m₁ ≤ m₂ → m₁ ≤ m₃ → ∃ a ∈ S.A, (prodBernoulli S.w).real (openConn a S.b ∩ S.oA) ≤
      (prodBernoulli S.w).real (openConn S.o S.b ∩ S.oA) := fun h12 h13 => by
    refine ⟨S.a₁, S.a₁_mem, ?_⟩
    have key := S.swap12.swap23.preFKG_three h12 h13
    rw [oA_swap23, oA_swap12] at key
    rw [Set.inter_comm]
    exact key
  rcases le_total m₃ m₁ with h31 | h13
  · rcases le_total m₃ m₂ with h32 | h23
    · exact case3 h31 h32
    · exact case2 (h23.trans h31) h23
  · rcases le_total m₁ m₂ with h12 | h21
    · exact case1 h12 h13
    · exact case2 h21 (h21.trans h13)

end SepData

/-! ### Theorem 3 -/

section Theorem3

variable [Fintype V]

/-- **Kozma–Nitzan 2024, Theorem 3 — separation given as a partition.** Let `w` be edge
probabilities on a finite vertex type, `A` a set of three vertices, `b ∉ A`, and `VB` a set of
vertices containing `0 = o`, disjoint from `A`, not containing `b`, such that every pair joining `VB`
to the outside of `VB ∪ A` has weight `0` (so `A` separates `0` from `b`).  Then the pre-FKG inequality
(3) holds: `P(a ↔ b, 0 ↔ A) ≤ P(0 ↔ b, 0 ↔ A)` for some `a ∈ A` (i.e.
`P(0 ↔ b, 0 ↔ A) ≥ min_{a ∈ A} P(0 ↔ A, a ↔ b)`, `{0 ↔ A} = ⋃_{a ∈ A} {0 ↔ a}`).
[cite: KozmaNitzan2024, Thm. 3 (p. 10), inequality (3) (p. 3)] -/
theorem _root_.Percolation.Literature.KozmaNitzan2024_thm3_of_parts (w : Sym2 V → unitInterval)
    (A : Finset V) (o b : V)
    (VB : Set V) (hA : A.card = 3) (ho : o ∈ VB) (hb : b ∉ VB) (hbA : b ∉ A)
    (hAV : ∀ a ∈ A, a ∉ VB)
    (hcut : ∀ e, e ∉ sideB VB (↑A : Set V) → e ∉ sideT VB (↑A : Set V) → w e = 0) :
    ∃ a ∈ A, (prodBernoulli w).real (openConn a b ∩ ⋃ a' ∈ A, openConn o a') ≤
      (prodBernoulli w).real (openConn o b ∩ ⋃ a' ∈ A, openConn o a') := by
  classical
  obtain ⟨a₁, a₂, a₃, h12, h13, h23, rfl⟩ := Finset.card_eq_three.1 hA
  have hAset : (↑({a₁, a₂, a₃} : Finset V) : Set V) = ({a₁, a₂, a₃} : Set V) := by simp
  set S : SepData V :=
    { w := w, VB := VB, o := o, b := b, a₁ := a₁, a₂ := a₂, a₃ := a₃, ho := ho, hb := hb
      ha₁ := hAV a₁ (by simp), ha₂ := hAV a₂ (by simp), ha₃ := hAV a₃ (by simp)
      h₁₂ := h12, h₁₃ := h13, h₂₃ := h23
      hb₁ := fun h => hbA (by simp [h]), hb₂ := fun h => hbA (by simp [h]), hb₃ := fun h => hbA (by simp [h])
      hcut := fun e h1 h2 => hcut e (by rwa [hAset]) (by rwa [hAset]) } with hS
  have hU : (⋃ a' ∈ ({a₁, a₂, a₃} : Finset V), (openConn o a' : Set (BondConfig V))) = S.oA := by
    ext ω
    simp only [mem_iUnion, exists_prop, Finset.mem_insert, Finset.mem_singleton, SepData.oA, mem_union, hS]
    constructor
    · rintro ⟨a, rfl | rfl | rfl, ha⟩
      · exact Or.inl (Or.inl ha)
      · exact Or.inl (Or.inr ha)
      · exact Or.inr ha
    · rintro ((h | h) | h)
      · exact ⟨a₁, Or.inl rfl, h⟩
      · exact ⟨a₂, Or.inr (Or.inl rfl), h⟩
      · exact ⟨a₃, Or.inr (Or.inr rfl), h⟩
  obtain ⟨a, ha, h⟩ := S.thm3
  refine ⟨a, ?_, ?_⟩
  · simpa [SepData.A, hS] using ha
  · rw [hU]; exact h

/-- The `0`-side of `A`: the vertices reachable from `0` along pairs of positive weight without
passing through `A` (the component of `0` in `G ∖ A`, KN p. 10). [cite: KozmaNitzan2024, proof of Thm. 3 (p. 10)] -/
def observerSide (w : Sym2 V → unitInterval) (A : Finset V) (o : V) : Set V :=
  {x | ∃ p : (SimpleGraph.fromEdgeSet {e : Sym2 V | w e ≠ 0}).Walk o x, ∀ a ∈ A, a ∉ p.support}

/-- **Kozma–Nitzan 2024, Theorem 3** (arXiv:2401.12397, p. 10): "If `|A| = 3` and `A`
separates `0` from `b`, namely, any path in `G` from `0` to `b` must pass through a point of `A`,
then the pre-FKG inequality in the form (3) holds", (3) being
"`P(0 ↔ b, 0 ↔ A) ≥ min{P(0 ↔ A, a ↔ b) : a ∈ A}`" (p. 3).  Transcription (as in
`KozmaNitzanPreFKG.lean`): a finite weighted graph is a weight function `w : Sym2 V → [0,1]` on a
finite vertex type (absent edges = weight `0`), percolation is `prodBernoulli w`, "a path in `G`" is a
walk in the graph of the positive-weight pairs, `b ∉ A` ("`0` and `b` are in different components
[of `G ∖ A`]", p. 10; the case `0 ∈ A` is trivial with `a = 0` and is included), `{0 ↔ A} =
⋃_{a ∈ A} {0 ↔ a}`, and the minimum over `A` is an existential.
Proof: pp. 10–12 as printed (this file), via `KozmaNitzan2024_thm3_of_parts` with `VB` the
`0`-side of `A`. [cite: KozmaNitzan2024, Thm. 3 (p. 10), inequality (3) (p. 3)] -/
theorem _root_.Percolation.Literature.KozmaNitzan2024_thm3 (w : Sym2 V → unitInterval)
    (A : Finset V) (o b : V)
    (hA : A.card = 3) (hbA : b ∉ A)
    (hsep : ∀ p : (SimpleGraph.fromEdgeSet {e : Sym2 V | w e ≠ 0}).Walk o b, ∃ a ∈ A, a ∈ p.support) :
    ∃ a ∈ A, (prodBernoulli w).real (openConn a b ∩ ⋃ a' ∈ A, openConn o a') ≤
      (prodBernoulli w).real (openConn o b ∩ ⋃ a' ∈ A, openConn o a') := by
  classical
  -- if `0 ∈ A` then `a = 0` gives (3) with equality; the printed setting has `0 ∉ A`
  by_cases hoA : o ∈ A
  · exact ⟨o, hoA, le_rfl⟩
  set G := SimpleGraph.fromEdgeSet {e : Sym2 V | w e ≠ 0} with hG
  set VB := observerSide w A o with hVB
  have ho : o ∈ VB := ⟨SimpleGraph.Walk.nil, fun a ha h => hoA (by
    rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at h; exact h ▸ ha)⟩
  have hb : b ∉ VB := fun ⟨p, hp⟩ => by
    obtain ⟨a, ha, hap⟩ := hsep p
    exact hp a ha hap
  have hAV : ∀ a ∈ A, a ∉ VB := fun a ha ⟨p, hp⟩ => hp a ha p.end_mem_support
  refine KozmaNitzan2024_thm3_of_parts w A o b VB hA ho hb hbA hAV fun e h1 h2 => ?_
  -- a pair from `VB` to the outside of `VB ∪ A` has weight `0`
  by_contra hne
  induction e using Sym2.ind with
  | h x y =>
    -- extending an `A`-avoiding walk from `0` by a positive-weight pair stays in `VB`
    have key : ∀ u v : V, s(u, v) = s(x, y) → u ∈ VB → v ∉ VB → v ∉ A → False := by
      rintro u v huv ⟨p, hp⟩ hv hvA
      have hadj : G.Adj u v := by
        rw [hG, SimpleGraph.fromEdgeSet_adj]
        refine ⟨by rw [mem_setOf_eq, huv]; exact hne, ?_⟩
        rintro rfl; exact hv ⟨p, hp⟩
      refine hv ⟨p.concat hadj, fun a ha h => ?_⟩
      rw [SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton] at h
      rcases h with h | rfl
      · exact hp a ha h
      · exact hvA ha
    by_cases hx : x ∈ VB
    · by_cases hy : y ∈ VB
      · exact h1 fun v hv => by
          rcases Sym2.mem_iff.1 hv with rfl | rfl
          · exact Or.inl hx
          · exact Or.inl hy
      · by_cases hyA : y ∈ A
        · exact h1 fun v hv => by
            rcases Sym2.mem_iff.1 hv with rfl | rfl
            · exact Or.inl hx
            · exact Or.inr hyA
        · exact key x y rfl hx hy hyA
    · by_cases hy : y ∈ VB
      · by_cases hxA : x ∈ A
        · exact h1 fun v hv => by
            rcases Sym2.mem_iff.1 hv with rfl | rfl
            · exact Or.inr hxA
            · exact Or.inl hy
        · exact key y x Sym2.eq_swap hy hx hxA
      · refine h2 ⟨fun v hv => ?_, fun hall => h1 fun v hv => Or.inr (hall v hv)⟩
        rcases Sym2.mem_iff.1 hv with rfl | rfl
        · exact hx
        · exact hy

end Theorem3

end KNSep

end Percolation.Literature
