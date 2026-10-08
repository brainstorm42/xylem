import Percolation.Literature.KozmaNitzanPinning
import Percolation.Literature.LatticeModels.ProdBernoulliIndependence
import Percolation.Literature.TwoClusterConditionalAssociationProofs
import Percolation.Util.Linter

/-!
# Kozma–Nitzan's proved cases of the pre-FKG conjecture: Lemma 3(ii), Theorem 1 (`|A| = 2`), Lemma 5, Theorem 4

Source: G. Kozma, S. Nitzan, *A reduction of the `θ(p_c) = 0` problem to a conjectured inequality*,
arXiv:2401.12397 (2024) [KozmaNitzan2024], §2.2 (pp. 5–7: the van den Berg–Häggström–Kahn
inequality and Lemmas 1–3), §3.1 (pp. 7–8: **Theorem 1**), §3.2 (pp. 12–14: **Theorem 4**,
**Lemma 5**). Everything in this file is proved, from the BHK theorems
`BHK2006_clusterConditionalPositiveAssociation_holds` (BHK 2006, Thm. 1.3) and
`BHK2006_twoClusterConditionalAssociation_holds` (BHK 2006, Thm. 1.5).

## Printed statements (arXiv:2401.12397, pp. 3, 5–8, 12–15)

Setting (p. 4): "For a graph `G` and a function `p : E(G) → [0,1]` we will consider the measure
on subsets `ω` of `E(G)` such that for every edge `e` the probability that `e ∈ ω` is `p(e)`, and
these events are independent"; graphs are finite (Conjecture 1, p. 3; BHK is quoted for finite
`G`, p. 5). The pre-FKG conjecture in its "formally stronger" form **(3)** (p. 3):
"`P(0 ↔ b, 0 ↔ A) ≥ min{P(0 ↔ A, a ↔ b) : a ∈ A}`."

* **Lemma 3** (pp. 6–7): "Let `G` be a graph, `a₁, a₂, b ∈ G` and `δ > 0` be such that
  `P(a₁ ↔ b) < P(a₂ ↔ b) + δ`. (i) … (ii) If `Q` is a decreasing event in the cluster of `a₁`
  then we have `P(a₁ ↔ b, Q) < P(a₂ ↔ b, Q) + δ`."  (Proof: Lemma 1 (i),(ii) = BHK given
  `{a₁ ↮ a₂}`.)
* **Theorem 1** (p. 7): "The pre-FKG conjecture (3) holds when `|A| = 2`."  (Proof, pp. 7–8:
  subtract the common event `{0 ↔ a₁ ↔ b}`, "Applying BHK 4 times".)
* **Theorem 4** (pp. 12–13): with `(G, A, 0, b)` *good* meaning
  `P(0 ↔ b) ≥ min_{a∈A} P(a ↔ b) − Σ_{W ∩ A = ∅} P(C(0) = W) min_{a∈A} P_{G∖W}(a ↔ b)` ("A good graph
  satisfies the pre-FKG conjecture (2)", p. 12): "Let `G` be a graph and let `b ∈ G` and `A ⊂ G`. If
  `0` is isolated in `G ∖ A` then `(G, A, 0, b)` is good."  (Proof, pp. 13–14: Lemma 5 for each
  `σ_B`, `B ≠ ∅`, and "Summing over all `B ≠ ∅` gives `P(0 ↔ b) ≥ P(a₀ ↔ b, 0 ↔ A)`".)
* **Lemma 5** (p. 13): "Let `G` be a graph, `0` and `b` some vertices, and `a` and `v` two
  neighbours of `0` with `P_{G∖{0}}(a ↔ b) ≤ P_{G∖{0}}(v ↔ b)`. Let `B` be a set of neighbours of
  `0` such that `v ∈ B` and let `σ := σ_B` be the event that all edges from `0` to vertices of `B`
  are open and all other edges from `0` are closed. Then `P(a ↔ b, σ) ≤ P(0 ↔ b, σ)`."  ("a simple
  corollary of the BHK inequality", p. 13; it is the engine of Thms. 4–5, `0` 'close' to `A`.)

## Transcription (the vocabulary of `KozmaNitzanReduction.lean`)

A finite graph with edge probabilities is a weight function `w : Sym2 V → [0,1]` on the pairs of a
finite vertex type `V` (absent edges = weight `0`), the percolation measure is
`prodBernoulli w` on `BondConfig V = Set (Sym2 V)`, `x ↔ y` is `openConn x y`. "A decreasing
event in the cluster of `a₁`" is, as in BHK 2006 (whose Thms. 1.3/1.5 KN invoke, p. 5), an event
`{ω | C_{a₁}(ω) ∈ 𝒬}` with `𝒬` a lower set of edge sets and `C_s = openEdgeCluster ω s` the open
EDGE cluster (`ConditionalPositiveAssociation.lean`). `P_{G∖{0}}(x ↔ y)`, percolation on the graph
with the vertex `0` deleted, is `(prodBernoulli w).real (openConnIn {0}ᶜ x y)` (an open path
avoiding `0`; the event only reads edges off `0`, whose law is unchanged). The event `σ_B` is
`starEvent 0 B = {ω | ∀ u ≠ 0, s(0,u) ∈ ω ↔ u ∈ B}`. "Neighbours of `0`": in the weighted
complete graph every vertex `≠ 0` is a neighbour (possibly of weight `0`), so the hypotheses kept
are `a ≠ 0`, `v ≠ 0`, `v ∈ B`.

## Contents

* `KNPreFKG.bhk_one_upper_lower`, `….bhk_one_upper_upper`, `….bhk_two_upper_lower`,
  `….bhk_two_upper_upper` — the two BHK facts in EVENT form (indicators of upper/lower families
  of edge sets), denominator-free.
* `KozmaNitzan2024_lemma3_ii` — Lemma 3(ii), proved (non-strict form with slack `δ ≥ 0`; the
  printed strict form follows by shrinking `δ`).
* `KozmaNitzan2024_thm1` — statement of Theorem 1 ((3) for `A = {a₁, a₂}`) and
  `KozmaNitzan2024_thm1_holds` — its proof ("BHK 4 times").
* `KozmaNitzan2024_thm4` — Theorem 4 (pp. 12–14: `0` isolated in `G ∖ A` ⇒ the pre-FKG
  inequality (3), `P(0 ↔ b, 0 ↔ A) ≥ min_{a∈A} P(0 ↔ A, a ↔ b)`), proved from Lemma 5 by summing
  over the stars `σ_B`, `B ⊆ A` (`KNPreFKG.real_eq_sum_inter_starEvent`); the (2)-form
  `P(0 ↔ b) ≥ min_{a∈A} P(0 ↔ A, a ↔ b)` is the corollary `KozmaNitzan2024_thm4_preFKG2`.
* `starEvent`, `KozmaNitzan2024_lemma5` — statement of Lemma 5 and
  `KozmaNitzan2024_lemma5_holds` / `KozmaNitzan2024_lemma5_fintype` — its proof (via Lemma 3(ii) on `G ∖ {0}` with
  `Q = {a ↮ B}`, the restriction coupling `prodBernoulli_map_restrictConfig`, a first/last-visit
  decomposition of open paths through `0` under `σ_B`, and independence of the star of `0` from
  the edges off `0`). The printed proof perturbs the weights at `0` by `ε` and uses Lemma 3(i);
  the argument through Lemma 3(ii) needs no limit.

## Context

Conjecture 3 (p. 15) is `KozmaNitzan2024_conjecture3` (`KozmaNitzanReduction.lean`) and Theorem 6 is
`KozmaNitzan2024_thm6`. The results of this file are the proved `|A| ≤ 2` / "`0` close to `A`" cases
of the pre-FKG inequality (3), which implies Conjecture 1 (by FKG) and hence Conjecture 3.
-/

noncomputable section

open MeasureTheory Set
open Percolation.Literature.LatticeModels (prodBernoulli)

namespace Percolation.Literature

variable {V : Type*}

namespace KNPreFKG

/-! ### Events read off the open edge cluster `C_s` -/

/-- The family of edge sets "seeing" the vertex `a` from `s`: `a = s` or some edge of the set
contains `a`. By `reachable_iff_exists_mem_openEdgeCluster`, `{s ↔ a} = {ω | C_s(ω) ∈ connFamily s a}`.
[cite: VandenbergHaggstromKahn2005, §1 p. 3 ("A simple example of such an event is {s ↔ a}")] -/
def connFamily (s a : V) : Set (Set (Sym2 V)) := {C | a = s ∨ ∃ e ∈ C, a ∈ e}

/-- `connFamily s a` is an upper family. [folklore] -/
theorem isUpperSet_connFamily (s a : V) : IsUpperSet (connFamily s a) := by
  intro C C' hCC' hC
  rcases hC with h | ⟨e, he, hae⟩
  · exact Or.inl h
  · exact Or.inr ⟨e, hCC' he, hae⟩

/-- `{s ↔ a}` is the event that `C_s` lies in `connFamily s a`. [cite: VandenbergHaggstromKahn2005, §1 p. 3] -/
theorem openConn_eq_setOf_connFamily (s a : V) :
    (openConn s a : Set (BondConfig V)) = {ω | openEdgeCluster ω s ∈ connFamily s a} := by
  ext ω
  exact reachable_iff_exists_mem_openEdgeCluster ω s a

/-- The family of edge sets from which no vertex of `B` is seen from `s`:
`{s ↮ B} = {ω | C_s(ω) ∈ disconnFamily s B}`. [cite: VandenbergHaggstromKahn2005, §1 p. 3 (the events R_X = {s ↮ X})] -/
def disconnFamily (s : V) (B : Set V) : Set (Set (Sym2 V)) :=
  {C | ∀ u ∈ B, ¬ (u = s ∨ ∃ e ∈ C, u ∈ e)}

/-- `disconnFamily s B` is a lower family. [folklore] -/
theorem isLowerSet_disconnFamily (s : V) (B : Set V) : IsLowerSet (disconnFamily s B) := by
  intro C C' hCC' hC u hu h
  rcases h with h | ⟨e, he, hue⟩
  · exact hC u hu (Or.inl h)
  · exact hC u hu (Or.inr ⟨e, hCC' he, hue⟩)

/-- `{s ↮ B} = {ω | ∀ u ∈ B, ¬ s ↔ u}` is the event that `C_s` lies in `disconnFamily s B`.
[cite: VandenbergHaggstromKahn2005, §1 p. 3] -/
theorem setOf_forall_not_reachable_eq (s : V) (B : Set V) :
    {ω : BondConfig V | ∀ u ∈ B, ¬ (openGraph ω).Reachable s u} =
      {ω | openEdgeCluster ω s ∈ disconnFamily s B} := by
  ext ω
  simp only [mem_setOf_eq, disconnFamily]
  refine forall₂_congr fun u _ => ?_
  rw [reachable_iff_exists_mem_openEdgeCluster]

/-- The indicator of an upper family is increasing. [folklore] -/
theorem monotone_indicator_one_of_isUpperSet {α : Type*} [Preorder α] {𝒜 : Set α}
    (h : IsUpperSet 𝒜) : Monotone (𝒜.indicator (1 : α → ℝ)) := by
  intro a b hab
  by_cases ha : a ∈ 𝒜
  · rw [indicator_of_mem ha, indicator_of_mem (h hab ha), Pi.one_apply, Pi.one_apply]
  · rw [indicator_of_notMem ha]
    exact indicator_nonneg (fun _ _ => zero_le_one) _

/-- The indicator of a lower family is decreasing. [folklore] -/
theorem antitone_indicator_one_of_isLowerSet {α : Type*} [Preorder α] {𝒬 : Set α}
    (h : IsLowerSet 𝒬) : Antitone (𝒬.indicator (1 : α → ℝ)) := by
  intro a b hab
  by_cases hb : b ∈ 𝒬
  · rw [indicator_of_mem hb, indicator_of_mem (h hab hb), Pi.one_apply, Pi.one_apply]
  · rw [indicator_of_notMem hb]
    exact indicator_nonneg (fun _ _ => zero_le_one) _

/-- Pulling an indicator back along `ω ↦ C_s(ω)`. [folklore] -/
theorem indicator_comp_openEdgeCluster (𝒜 : Set (Set (Sym2 V))) (s : V) :
    (fun ω : BondConfig V => 𝒜.indicator (1 : Set (Sym2 V) → ℝ) (openEdgeCluster ω s)) =
      {ω : BondConfig V | openEdgeCluster ω s ∈ 𝒜}.indicator 1 := by
  funext ω
  by_cases h : openEdgeCluster ω s ∈ 𝒜
  · rw [indicator_of_mem h, indicator_of_mem (show ω ∈ {ω | openEdgeCluster ω s ∈ 𝒜} from h)]
    rfl
  · rw [indicator_of_notMem h, indicator_of_notMem (show ω ∉ {ω | openEdgeCluster ω s ∈ 𝒜} from h)]

/-- Product of two indicators with value one. [folklore] -/
theorem indicator_one_mul_indicator_one (A B : Set (BondConfig V)) :
    (fun ω => A.indicator (1 : BondConfig V → ℝ) ω * B.indicator 1 ω) = (A ∩ B).indicator 1 :=
  funext fun ω => (congrFun (Set.inter_indicator_one (s := A) (t := B) (M₀ := ℝ)) ω).symm

section BHKEvents

variable [Fintype V]

/-- The set integral of the indicator (value one) of an event is the measure of the
intersection. [folklore] -/
theorem setIntegral_indicator_one_eq (μ : Measure (BondConfig V)) [IsFiniteMeasure μ]
    (D A : Set (BondConfig V)) :
    ∫ ω in D, A.indicator (1 : BondConfig V → ℝ) ω ∂μ = μ.real (D ∩ A) := by
  classical
  have hA : MeasurableSet A := MeasurableSet.of_discrete
  rw [setIntegral_indicator hA]
  simp only [Pi.one_apply, setIntegral_const, smul_eq_mul, mul_one]

/-- **BHK 2006, Thm. 1.3, event form (increasing × decreasing).** For `s ∉ X`,
`D = {s ↮ X}`, `𝒜` an upper and `𝒬` a lower family of edge sets,
`μ(D) · μ(D ∩ {C_s ∈ 𝒜} ∩ {C_s ∈ 𝒬}) ≤ μ(D ∩ {C_s ∈ 𝒜}) · μ(D ∩ {C_s ∈ 𝒬})`.
[cite: VandenbergHaggstromKahn2005, Thm. 1.3 (p. 6, last sentence)] -/
theorem bhk_one_upper_lower (w : Sym2 V → unitInterval) (s : V) (X : Set V) (hs : s ∉ X)
    {𝒜 𝒬 : Set (Set (Sym2 V))} (h𝒜 : IsUpperSet 𝒜) (h𝒬 : IsLowerSet 𝒬) :
    (prodBernoulli w).real {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x} *
      (prodBernoulli w).real ({ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x} ∩
        ({ω | openEdgeCluster ω s ∈ 𝒜} ∩ {ω | openEdgeCluster ω s ∈ 𝒬})) ≤
    (prodBernoulli w).real ({ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x} ∩
        {ω | openEdgeCluster ω s ∈ 𝒜}) *
      (prodBernoulli w).real ({ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x} ∩
        {ω | openEdgeCluster ω s ∈ 𝒬}) := by
  have key := BHK2006_clusterConditionalPositiveAssociation_holds.antitone_right V w s X
    (𝒜.indicator 1) (𝒬.indicator 1) (monotone_indicator_one_of_isUpperSet h𝒜)
    (antitone_indicator_one_of_isLowerSet h𝒬) hs
  rw [show (fun ω : BondConfig V => 𝒜.indicator (1 : Set (Sym2 V) → ℝ) (openEdgeCluster ω s) *
      𝒬.indicator 1 (openEdgeCluster ω s)) =
      ({ω : BondConfig V | openEdgeCluster ω s ∈ 𝒜} ∩ {ω | openEdgeCluster ω s ∈ 𝒬}).indicator 1 by
    rw [← indicator_one_mul_indicator_one]
    funext ω
    rw [← indicator_comp_openEdgeCluster, ← indicator_comp_openEdgeCluster],
    indicator_comp_openEdgeCluster, indicator_comp_openEdgeCluster,
    setIntegral_indicator_one_eq, setIntegral_indicator_one_eq, setIntegral_indicator_one_eq] at key
  exact key

/-- **BHK 2006, Thm. 1.3, event form (increasing × increasing).** For `s ∉ X`, `D = {s ↮ X}`,
`𝒜, ℬ` upper families, `μ(D ∩ {C_s ∈ 𝒜}) · μ(D ∩ {C_s ∈ ℬ}) ≤ μ(D) · μ(D ∩ {C_s ∈ 𝒜} ∩ {C_s ∈ ℬ})`.
[cite: VandenbergHaggstromKahn2005, Thm. 1.3 (p. 6)] -/
theorem bhk_one_upper_upper (w : Sym2 V → unitInterval) (s : V) (X : Set V) (hs : s ∉ X)
    {𝒜 ℬ : Set (Set (Sym2 V))} (h𝒜 : IsUpperSet 𝒜) (hℬ : IsUpperSet ℬ) :
    (prodBernoulli w).real ({ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x} ∩
        {ω | openEdgeCluster ω s ∈ 𝒜}) *
      (prodBernoulli w).real ({ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x} ∩
        {ω | openEdgeCluster ω s ∈ ℬ}) ≤
    (prodBernoulli w).real {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x} *
      (prodBernoulli w).real ({ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x} ∩
        ({ω | openEdgeCluster ω s ∈ 𝒜} ∩ {ω | openEdgeCluster ω s ∈ ℬ})) := by
  have key := BHK2006_clusterConditionalPositiveAssociation_holds V w s X
    (𝒜.indicator 1) (ℬ.indicator 1) (monotone_indicator_one_of_isUpperSet h𝒜)
    (monotone_indicator_one_of_isUpperSet hℬ) hs
  rw [show (fun ω : BondConfig V => 𝒜.indicator (1 : Set (Sym2 V) → ℝ) (openEdgeCluster ω s) *
      ℬ.indicator 1 (openEdgeCluster ω s)) =
      ({ω : BondConfig V | openEdgeCluster ω s ∈ 𝒜} ∩ {ω | openEdgeCluster ω s ∈ ℬ}).indicator 1 by
    rw [← indicator_one_mul_indicator_one]
    funext ω
    rw [← indicator_comp_openEdgeCluster, ← indicator_comp_openEdgeCluster],
    indicator_comp_openEdgeCluster, indicator_comp_openEdgeCluster,
    setIntegral_indicator_one_eq, setIntegral_indicator_one_eq, setIntegral_indicator_one_eq] at key
  exact key

/-- **BHK 2006, Thm. 1.5, event form.** For `s ≠ t`, `D = {s ↮ t}`, `𝒜` an upper family read on
`C_s` and `𝒬` a lower family read on `C_t`,
`μ(D ∩ {C_s ∈ 𝒜}) · μ(D ∩ {C_t ∈ 𝒬}) ≤ μ(D) · μ(D ∩ {C_s ∈ 𝒜} ∩ {C_t ∈ 𝒬})`.
[cite: VandenbergHaggstromKahn2005, Thm. 1.5 (p. 7, eq. (9))] -/
theorem bhk_two_upper_lower (w : Sym2 V → unitInterval) (s t : V) (hst : s ≠ t)
    {𝒜 𝒬 : Set (Set (Sym2 V))} (h𝒜 : IsUpperSet 𝒜) (h𝒬 : IsLowerSet 𝒬) :
    (prodBernoulli w).real ({ω : BondConfig V | ¬ (openGraph ω).Reachable s t} ∩
        {ω | openEdgeCluster ω s ∈ 𝒜}) *
      (prodBernoulli w).real ({ω : BondConfig V | ¬ (openGraph ω).Reachable s t} ∩
        {ω | openEdgeCluster ω t ∈ 𝒬}) ≤
    (prodBernoulli w).real {ω : BondConfig V | ¬ (openGraph ω).Reachable s t} *
      (prodBernoulli w).real ({ω : BondConfig V | ¬ (openGraph ω).Reachable s t} ∩
        ({ω | openEdgeCluster ω s ∈ 𝒜} ∩ {ω | openEdgeCluster ω t ∈ 𝒬})) := by
  have key := BHK2006_twoClusterConditionalAssociation_holds V w s t
    (fun C _ => 𝒜.indicator (1 : Set (Sym2 V) → ℝ) C) (fun _ D => 𝒬.indicator (1 : Set (Sym2 V) → ℝ) D)
    (fun _ => monotone_indicator_one_of_isUpperSet h𝒜) (fun _ => antitone_const)
    (fun _ => monotone_const) (fun _ => antitone_indicator_one_of_isLowerSet h𝒬) hst
  rw [show (fun ω : BondConfig V => 𝒜.indicator (1 : Set (Sym2 V) → ℝ) (openEdgeCluster ω s) *
      𝒬.indicator 1 (openEdgeCluster ω t)) =
      ({ω : BondConfig V | openEdgeCluster ω s ∈ 𝒜} ∩ {ω | openEdgeCluster ω t ∈ 𝒬}).indicator 1 by
    rw [← indicator_one_mul_indicator_one]
    funext ω
    rw [← indicator_comp_openEdgeCluster, ← indicator_comp_openEdgeCluster],
    indicator_comp_openEdgeCluster, indicator_comp_openEdgeCluster,
    setIntegral_indicator_one_eq, setIntegral_indicator_one_eq, setIntegral_indicator_one_eq] at key
  exact key

/-- **BHK 2006, Thm. 1.4, event form.** For `s ≠ t`, `D = {s ↮ t}`, `𝒜` an upper family read on
`C_s` and `ℬ` an upper family read on `C_t`,
`μ(D) · μ(D ∩ {C_s ∈ 𝒜} ∩ {C_t ∈ ℬ}) ≤ μ(D ∩ {C_s ∈ 𝒜}) · μ(D ∩ {C_t ∈ ℬ})`.
[cite: VandenbergHaggstromKahn2005, Thm. 1.4 (p. 7)] -/
theorem bhk_two_upper_upper (w : Sym2 V → unitInterval) (s t : V) (hst : s ≠ t)
    {𝒜 ℬ : Set (Set (Sym2 V))} (h𝒜 : IsUpperSet 𝒜) (hℬ : IsUpperSet ℬ) :
    (prodBernoulli w).real {ω : BondConfig V | ¬ (openGraph ω).Reachable s t} *
      (prodBernoulli w).real ({ω : BondConfig V | ¬ (openGraph ω).Reachable s t} ∩
        ({ω | openEdgeCluster ω s ∈ 𝒜} ∩ {ω | openEdgeCluster ω t ∈ ℬ})) ≤
    (prodBernoulli w).real ({ω : BondConfig V | ¬ (openGraph ω).Reachable s t} ∩
        {ω | openEdgeCluster ω s ∈ 𝒜}) *
      (prodBernoulli w).real ({ω : BondConfig V | ¬ (openGraph ω).Reachable s t} ∩
        {ω | openEdgeCluster ω t ∈ ℬ}) := by
  have key := BHK2006_twoClusterConditionalAssociation_holds.negCorrelation V w s t
    (𝒜.indicator 1) (ℬ.indicator 1) (monotone_indicator_one_of_isUpperSet h𝒜)
    (monotone_indicator_one_of_isUpperSet hℬ) hst
  rw [show (fun ω : BondConfig V => 𝒜.indicator (1 : Set (Sym2 V) → ℝ) (openEdgeCluster ω s) *
      ℬ.indicator 1 (openEdgeCluster ω t)) =
      ({ω : BondConfig V | openEdgeCluster ω s ∈ 𝒜} ∩ {ω | openEdgeCluster ω t ∈ ℬ}).indicator 1 by
    rw [← indicator_one_mul_indicator_one]
    funext ω
    rw [← indicator_comp_openEdgeCluster, ← indicator_comp_openEdgeCluster],
    indicator_comp_openEdgeCluster, indicator_comp_openEdgeCluster,
    setIntegral_indicator_one_eq, setIntegral_indicator_one_eq, setIntegral_indicator_one_eq] at key
  exact key

end BHKEvents

end KNPreFKG

/-! ### Kozma–Nitzan, Lemma 3(ii) -/

section Lemma3

open KNPreFKG

variable [Fintype V]

/-- **Kozma–Nitzan 2024, Lemma 3(ii)** (arXiv:2401.12397, pp. 6–7). Printed: "Let `G` be a
graph, `a₁, a₂, b ∈ G` and `δ > 0` be such that `P(a₁ ↔ b) < P(a₂ ↔ b) + δ`. … (ii) If `Q` is a
decreasing event in the cluster of `a₁` then we have `P(a₁ ↔ b, Q) < P(a₂ ↔ b, Q) + δ`." Here in
the non-strict form with slack `δ ≥ 0` (the strict printed form follows by shrinking `δ`), for the
percolation measure `prodBernoulli w` of a finite weighted graph and `Q = {ω | C_{a₁}(ω) ∈ 𝒬}`, `𝒬` a
lower family of edge sets (`C_{a₁}` the open edge cluster, as in BHK 2006).  Proof as printed
(Lemma 1 = BHK given `D = {a₁ ↮ a₂}`): on `Dᶜ` the events `{a₁ ↔ b}` and `{a₂ ↔ b}` coincide; on
`D`, `μ(D) μ(D, a₁↔b, Q) ≤ μ(D, a₁↔b) μ(D, Q)` (BHK Thm. 1.3, increasing × decreasing in `C_{a₁}`),
`μ(D, a₁↔b) ≤ μ(D, a₂↔b) + δ`, and `μ(D, a₂↔b) μ(D, Q) ≤ μ(D) μ(D, a₂↔b, Q)` (BHK Thm. 1.5,
`{a₂ ↔ b}` increasing in `C_{a₂}`, `Q` decreasing in `C_{a₁}`); "multiply both sides of (4) by
`P(a₁ ↮ a₂, Q)` (which is clearly smaller then `P(a₁ ↮ a₂)`)".
[cite: KozmaNitzan2024, Lemma 3(ii) (pp. 6–7)] -/
theorem KozmaNitzan2024_lemma3_ii (w : Sym2 V → unitInterval) (a₁ a₂ b : V) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : (prodBernoulli w).real (openConn a₁ b) ≤ (prodBernoulli w).real (openConn a₂ b) + δ)
    {𝒬 : Set (Set (Sym2 V))} (h𝒬 : IsLowerSet 𝒬) :
    (prodBernoulli w).real (openConn a₁ b ∩ {ω | openEdgeCluster ω a₁ ∈ 𝒬}) ≤
      (prodBernoulli w).real (openConn a₂ b ∩ {ω | openEdgeCluster ω a₁ ∈ 𝒬}) + δ := by
  classical
  set μ := prodBernoulli w with hμ
  set X₁ : Set (BondConfig V) := openConn a₁ b with hX₁
  set X₂ : Set (BondConfig V) := openConn a₂ b with hX₂
  set Q : Set (BondConfig V) := {ω | openEdgeCluster ω a₁ ∈ 𝒬} with hQ
  by_cases h12 : a₁ = a₂
  · subst h12
    linarith [h]
  set D : Set (BondConfig V) := {ω | ¬ (openGraph ω).Reachable a₁ a₂} with hD
  -- on `Dᶜ` the two connection events agree
  have hagree : X₁ ∩ Dᶜ = X₂ ∩ Dᶜ := by
    ext ω
    simp only [mem_inter_iff, mem_compl_iff, mem_setOf_eq, not_not, hX₁, hX₂, hD, openConn]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h2.symm.trans h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h2.trans h1, h2⟩
  -- split every event along `D`
  have hsplit : ∀ A : Set (BondConfig V), μ.real A = μ.real (A ∩ D) + μ.real (A ∩ Dᶜ) := by
    intro A
    rw [← measureReal_inter_add_sdiff (s := A) (MeasurableSet.of_discrete : MeasurableSet D), Set.sdiff_eq]
  -- the hypothesis restricted to `D`
  have hH : μ.real (D ∩ X₁) ≤ μ.real (D ∩ X₂) + δ := by
    have h' := h
    rw [hsplit X₁, hsplit X₂, hagree] at h'
    rw [inter_comm D X₁, inter_comm D X₂]
    linarith
  -- (1) one-cluster BHK: `s = a₁`, `X = {a₂}`, increasing `{a₁ ↔ b}`, decreasing `Q`
  have hD1 : {ω : BondConfig V | ∀ x ∈ ({a₂} : Set V), ¬ (openGraph ω).Reachable a₁ x} = D := by
    ext ω
    simp [hD]
  have h1 := bhk_one_upper_lower w a₁ ({a₂} : Set V) (by simpa using h12)
    (isUpperSet_connFamily a₁ b) h𝒬
  rw [hD1, ← openConn_eq_setOf_connFamily] at h1
  -- (3) two-cluster BHK: `s = a₂`, `t = a₁`, increasing `{a₂ ↔ b}` in `C_{a₂}`, decreasing `Q` in `C_{a₁}`
  have hD2 : {ω : BondConfig V | ¬ (openGraph ω).Reachable a₂ a₁} = D := by
    ext ω
    simp only [mem_setOf_eq, hD]
    exact not_congr ⟨SimpleGraph.Reachable.symm, SimpleGraph.Reachable.symm⟩
  have h3 := bhk_two_upper_lower w a₂ a₁ (Ne.symm h12) (isUpperSet_connFamily a₂ b) h𝒬
  rw [hD2, ← openConn_eq_setOf_connFamily] at h3
  have hQD : μ.real (D ∩ Q) ≤ μ.real D := measureReal_mono inter_subset_left
  -- the inequality on `D`
  have hcore : μ.real (X₁ ∩ Q ∩ D) ≤ μ.real (X₂ ∩ Q ∩ D) + δ := by
    rw [inter_comm (X₁ ∩ Q) D, inter_comm (X₂ ∩ Q) D]
    by_cases hD0 : μ.real D = 0
    · have h0 : μ.real (D ∩ (X₁ ∩ Q)) = 0 :=
        le_antisymm ((measureReal_mono inter_subset_left).trans hD0.le) measureReal_nonneg
      rw [h0]
      exact add_nonneg measureReal_nonneg hδ
    · have hDpos : 0 < μ.real D := lt_of_le_of_ne measureReal_nonneg (Ne.symm hD0)
      have hchain : μ.real D * μ.real (D ∩ (X₁ ∩ Q)) ≤
          μ.real D * (μ.real (D ∩ (X₂ ∩ Q)) + δ) := by
        calc μ.real D * μ.real (D ∩ (X₁ ∩ Q))
            ≤ μ.real (D ∩ X₁) * μ.real (D ∩ Q) := h1
          _ ≤ (μ.real (D ∩ X₂) + δ) * μ.real (D ∩ Q) :=
              mul_le_mul_of_nonneg_right hH measureReal_nonneg
          _ = μ.real (D ∩ X₂) * μ.real (D ∩ Q) + δ * μ.real (D ∩ Q) := by ring
          _ ≤ μ.real D * μ.real (D ∩ (X₂ ∩ Q)) + δ * μ.real D :=
              add_le_add h3 (mul_le_mul_of_nonneg_left hQD hδ)
          _ = μ.real D * (μ.real (D ∩ (X₂ ∩ Q)) + δ) := by ring
      exact le_of_mul_le_mul_left hchain hDpos
  -- conclude by adding the parts on `Dᶜ`, where the events coincide
  have hagreeQ : X₁ ∩ Q ∩ Dᶜ = X₂ ∩ Q ∩ Dᶜ := by
    rw [inter_right_comm, hagree, inter_right_comm]
  calc μ.real (X₁ ∩ Q) = μ.real (X₁ ∩ Q ∩ D) + μ.real (X₁ ∩ Q ∩ Dᶜ) := hsplit _
    _ ≤ μ.real (X₂ ∩ Q ∩ D) + δ + μ.real (X₂ ∩ Q ∩ Dᶜ) := by
        rw [hagreeQ]
        linarith [hcore]
    _ = μ.real (X₂ ∩ Q) + δ := by
        rw [hsplit (X₂ ∩ Q)]
        ring

/-- **Lemma 3(ii) with `δ = 0` and `Q = {a₁ ↮ B}`** (the form used for Lemma 5): if
`P(a₁ ↔ b) ≤ P(a₂ ↔ b)` then `P(a₁ ↔ b, a₁ ↮ B) ≤ P(a₂ ↔ b, a₁ ↮ B)` for every vertex set `B`.
[cite: KozmaNitzan2024, Lemma 3(ii) (pp. 6–7)] -/
theorem KozmaNitzan2024_lemma3_ii_notConn (w : Sym2 V → unitInterval) (a₁ a₂ b : V) (B : Set V)
    (h : (prodBernoulli w).real (openConn a₁ b) ≤ (prodBernoulli w).real (openConn a₂ b)) :
    (prodBernoulli w).real (openConn a₁ b ∩ {ω | ∀ u ∈ B, ¬ (openGraph ω).Reachable a₁ u}) ≤
      (prodBernoulli w).real (openConn a₂ b ∩ {ω | ∀ u ∈ B, ¬ (openGraph ω).Reachable a₁ u}) := by
  have key := KozmaNitzan2024_lemma3_ii w a₁ a₂ b le_rfl (by simpa using h)
    (isLowerSet_disconnFamily a₁ B)
  rw [← setOf_forall_not_reachable_eq, add_zero] at key
  exact key

end Lemma3

/-! ### Kozma–Nitzan, Theorem 1: the pre-FKG inequality (3) for `|A| = 2` -/

namespace KNPreFKG

/-- `{x ↔ y} = {y ↔ x}`. [folklore] -/
theorem openConn_symm (x y : V) : (openConn x y : Set (BondConfig V)) = openConn y x := by
  ext ω
  exact ⟨SimpleGraph.Reachable.symm, SimpleGraph.Reachable.symm⟩

variable [Fintype V]

/-- **Theorem 1 for the pair `{a₁, a₂}`** (the heart of the printed proof): with
`{0 ↔ A} = {0 ↔ a₁} ∪ {0 ↔ a₂}`,
`min(P(0↔A, a₁↔b), P(0↔A, a₂↔b)) ≤ P(0↔b, 0↔A)`.  Printed proof (pp. 7–8): subtracting the
common event `{0 ↔ a₁ ↔ b}`, `P(0↔b↔A) − P(0↔A, a₁↔b) = P(0↔a₂↔b, a₁↮a₂) − P(0↔a₂, a₁↔b, a₁↮a₂)`,
and "Applying BHK 4 times" (Thm. 1.3 for the products inside one cluster, Thm. 1.4 across the
two clusters, given `{a₁ ↮ a₂}`) bounds the two differences below by
`φ(2)(P(a₂↔b, a₁↮a₂) − P(a₁↔b, a₁↮a₂))` and `φ(1)(P(a₁↔b, a₁↮a₂) − P(a₂↔b, a₁↮a₂))`, one of
which is nonnegative (KN combine them with the coefficients (5) instead).
[cite: KozmaNitzan2024, Thm. 1 (pp. 7–8)] -/
theorem preFKG_pair (w : Sym2 V → unitInterval) (o b a₁ a₂ : V) :
    min ((prodBernoulli w).real ((openConn o a₁ ∪ openConn o a₂) ∩ openConn a₁ b))
        ((prodBernoulli w).real ((openConn o a₁ ∪ openConn o a₂) ∩ openConn a₂ b)) ≤
      (prodBernoulli w).real (openConn o b ∩ (openConn o a₁ ∪ openConn o a₂)) := by
  classical
  by_cases h12 : a₁ = a₂
  · -- `A` is a singleton: `{0 ↔ a₁, a₁ ↔ b} ⊆ {0 ↔ b, 0 ↔ A}`
    subst h12
    rw [union_self]
    refine (min_le_left _ _).trans (measureReal_mono ?_)
    rintro ω ⟨hA, hb⟩
    exact ⟨SimpleGraph.Reachable.trans hA hb, hA⟩
  set μ := prodBernoulli w with hμ
  set O₁ : Set (BondConfig V) := openConn o a₁ with hO₁
  set O₂ : Set (BondConfig V) := openConn o a₂ with hO₂
  set Ob : Set (BondConfig V) := openConn o b with hOb
  set B₁ : Set (BondConfig V) := openConn a₁ b with hB₁
  set B₂ : Set (BondConfig V) := openConn a₂ b with hB₂
  set D : Set (BondConfig V) := {ω | ¬ (openGraph ω).Reachable a₁ a₂} with hD
  set E : Set (BondConfig V) := Ob ∩ (O₁ ∪ O₂) with hE
  set F₁ : Set (BondConfig V) := (O₁ ∪ O₂) ∩ B₁ with hF₁
  set F₂ : Set (BondConfig V) := (O₁ ∪ O₂) ∩ B₂ with hF₂
  have hsplit : ∀ A S : Set (BondConfig V), μ.real A = μ.real (A ∩ S) + μ.real (A ∩ Sᶜ) := by
    intro A S
    rw [← measureReal_inter_add_sdiff (s := A) (MeasurableSet.of_discrete : MeasurableSet S), Set.sdiff_eq]
  -- the two "subtract the common event" identities
  have hE1 : E ∩ O₁ = F₁ ∩ O₁ := by
    ext ω
    simp only [mem_inter_iff, mem_union, hE, hF₁, hO₁, hO₂, hOb, hB₁, openConn, mem_setOf_eq]
    constructor
    · rintro ⟨⟨hb, _⟩, h1⟩
      exact ⟨⟨Or.inl h1, h1.symm.trans hb⟩, h1⟩
    · rintro ⟨⟨_, hb⟩, h1⟩
      exact ⟨⟨h1.trans hb, Or.inl h1⟩, h1⟩
  have hE1c : E ∩ O₁ᶜ = O₂ ∩ B₂ ∩ D := by
    ext ω
    simp only [mem_inter_iff, mem_union, mem_compl_iff, hE, hO₁, hO₂, hOb, hB₂, hD, openConn,
      mem_setOf_eq]
    constructor
    · rintro ⟨⟨hb, h1 | h2⟩, hn1⟩
      · exact absurd h1 hn1
      · exact ⟨⟨h2, h2.symm.trans hb⟩, fun h => hn1 (h2.trans h.symm)⟩
    · rintro ⟨⟨h2, hb⟩, hn⟩
      exact ⟨⟨h2.trans hb, Or.inr h2⟩, fun h1 => hn (h1.symm.trans h2)⟩
  have hF1c : F₁ ∩ O₁ᶜ = O₂ ∩ B₁ ∩ D := by
    ext ω
    simp only [mem_inter_iff, mem_union, mem_compl_iff, hF₁, hO₁, hO₂, hB₁, hD, openConn,
      mem_setOf_eq]
    constructor
    · rintro ⟨⟨h1 | h2, hb⟩, hn1⟩
      · exact absurd h1 hn1
      · exact ⟨⟨h2, hb⟩, fun h => hn1 (h2.trans h.symm)⟩
    · rintro ⟨⟨h2, hb⟩, hn⟩
      exact ⟨⟨Or.inr h2, hb⟩, fun h1 => hn (h1.symm.trans h2)⟩
  have hE2 : E ∩ O₂ = F₂ ∩ O₂ := by
    ext ω
    simp only [mem_inter_iff, mem_union, hE, hF₂, hO₁, hO₂, hOb, hB₂, openConn, mem_setOf_eq]
    constructor
    · rintro ⟨⟨hb, _⟩, h2⟩
      exact ⟨⟨Or.inr h2, h2.symm.trans hb⟩, h2⟩
    · rintro ⟨⟨_, hb⟩, h2⟩
      exact ⟨⟨h2.trans hb, Or.inr h2⟩, h2⟩
  have hE2c : E ∩ O₂ᶜ = O₁ ∩ B₁ ∩ D := by
    ext ω
    simp only [mem_inter_iff, mem_union, mem_compl_iff, hE, hO₁, hO₂, hOb, hB₁, hD, openConn,
      mem_setOf_eq]
    constructor
    · rintro ⟨⟨hb, h1 | h2⟩, hn2⟩
      · exact ⟨⟨h1, h1.symm.trans hb⟩, fun h => hn2 (h1.trans h)⟩
      · exact absurd h2 hn2
    · rintro ⟨⟨h1, hb⟩, hn⟩
      exact ⟨⟨h1.trans hb, Or.inl h1⟩, fun h2 => hn (h1.symm.trans h2)⟩
  have hF2c : F₂ ∩ O₂ᶜ = O₁ ∩ B₂ ∩ D := by
    ext ω
    simp only [mem_inter_iff, mem_union, mem_compl_iff, hF₂, hO₁, hO₂, hB₂, hD, openConn,
      mem_setOf_eq]
    constructor
    · rintro ⟨⟨h1 | h2, hb⟩, hn2⟩
      · exact ⟨⟨h1, hb⟩, fun h => hn2 (h1.trans h)⟩
      · exact absurd h2 hn2
    · rintro ⟨⟨h1, hb⟩, hn⟩
      exact ⟨⟨Or.inl h1, hb⟩, fun h2 => hn (h1.symm.trans h2)⟩
  have hdiff1 : μ.real E - μ.real F₁ = μ.real (O₂ ∩ B₂ ∩ D) - μ.real (O₂ ∩ B₁ ∩ D) := by
    rw [hsplit E O₁, hsplit F₁ O₁, hE1, hE1c, hF1c]
    ring
  have hdiff2 : μ.real E - μ.real F₂ = μ.real (O₁ ∩ B₁ ∩ D) - μ.real (O₁ ∩ B₂ ∩ D) := by
    rw [hsplit E O₂, hsplit F₂ O₂, hE2, hE2c, hF2c]
    ring
  -- "Applying BHK 4 times", given `D = {a₁ ↮ a₂}`
  have hD1 : {ω : BondConfig V | ∀ x ∈ ({a₂} : Set V), ¬ (openGraph ω).Reachable a₁ x} = D := by
    ext ω
    simp [hD]
  have hD2 : {ω : BondConfig V | ∀ x ∈ ({a₁} : Set V), ¬ (openGraph ω).Reachable a₂ x} = D := by
    ext ω
    simp only [mem_setOf_eq, mem_singleton_iff, forall_eq, hD]
    exact not_congr ⟨SimpleGraph.Reachable.symm, SimpleGraph.Reachable.symm⟩
  have hD3 : {ω : BondConfig V | ¬ (openGraph ω).Reachable a₂ a₁} = D := by
    ext ω
    simp only [mem_setOf_eq, hD]
    exact not_congr ⟨SimpleGraph.Reachable.symm, SimpleGraph.Reachable.symm⟩
  -- (i) `μ(D, 0↔a₂) μ(D, a₂↔b) ≤ μ(D) μ(D, 0↔a₂, a₂↔b)` (Thm. 1.3 in `C_{a₂}`)
  have h_i := bhk_one_upper_upper w a₂ ({a₁} : Set V) (by simpa using Ne.symm h12)
    (isUpperSet_connFamily a₂ o) (isUpperSet_connFamily a₂ b)
  rw [hD2, ← openConn_eq_setOf_connFamily, ← openConn_eq_setOf_connFamily, openConn_symm a₂ o] at h_i
  -- (ii) `μ(D) μ(D, 0↔a₂, a₁↔b) ≤ μ(D, 0↔a₂) μ(D, a₁↔b)` (Thm. 1.4, `C_{a₂}` and `C_{a₁}`)
  have h_ii := bhk_two_upper_upper w a₂ a₁ (Ne.symm h12) (isUpperSet_connFamily a₂ o)
    (isUpperSet_connFamily a₁ b)
  rw [hD3, ← openConn_eq_setOf_connFamily, ← openConn_eq_setOf_connFamily, openConn_symm a₂ o] at h_ii
  -- (iii) `μ(D, 0↔a₁) μ(D, a₁↔b) ≤ μ(D) μ(D, 0↔a₁, a₁↔b)` (Thm. 1.3 in `C_{a₁}`)
  have h_iii := bhk_one_upper_upper w a₁ ({a₂} : Set V) (by simpa using h12)
    (isUpperSet_connFamily a₁ o) (isUpperSet_connFamily a₁ b)
  rw [hD1, ← openConn_eq_setOf_connFamily, ← openConn_eq_setOf_connFamily, openConn_symm a₁ o] at h_iii
  -- (iv) `μ(D) μ(D, 0↔a₁, a₂↔b) ≤ μ(D, 0↔a₁) μ(D, a₂↔b)` (Thm. 1.4, `C_{a₁}` and `C_{a₂}`)
  have h_iv := bhk_two_upper_upper w a₁ a₂ h12 (isUpperSet_connFamily a₁ o)
    (isUpperSet_connFamily a₂ b)
  rw [← openConn_eq_setOf_connFamily, ← openConn_eq_setOf_connFamily, openConn_symm a₁ o] at h_iv
  -- normalise the intersections
  have e1 : D ∩ (O₂ ∩ B₂) = O₂ ∩ B₂ ∩ D := inter_comm _ _
  have e2 : D ∩ (O₂ ∩ B₁) = O₂ ∩ B₁ ∩ D := inter_comm _ _
  have e3 : D ∩ (O₁ ∩ B₁) = O₁ ∩ B₁ ∩ D := inter_comm _ _
  have e4 : D ∩ (O₁ ∩ B₂) = O₁ ∩ B₂ ∩ D := inter_comm _ _
  simp only [← hD, ← hO₁, ← hO₂, ← hB₁, ← hB₂] at h_i h_ii h_iii h_iv
  rw [e1] at h_i
  rw [e2] at h_ii
  rw [e3] at h_iii
  rw [e4] at h_iv
  -- combine
  by_cases hD0 : μ.real D = 0
  · have hz : ∀ A : Set (BondConfig V), μ.real (A ∩ D) = 0 := fun A =>
      le_antisymm ((measureReal_mono inter_subset_right).trans hD0.le) measureReal_nonneg
    have : μ.real E = μ.real F₁ := by
      have := hdiff1
      rw [hz, hz, sub_self, sub_eq_zero] at this
      exact this
    exact (min_le_left _ _).trans this.symm.le
  · have hDpos : 0 < μ.real D := lt_of_le_of_ne measureReal_nonneg (Ne.symm hD0)
    rcases le_total (μ.real (D ∩ B₁)) (μ.real (D ∩ B₂)) with ht | ht
    · -- `μ(D, a₁↔b) ≤ μ(D, a₂↔b)`: then `μ(E) ≥ μ(F₁)`
      refine (min_le_left _ _).trans ?_
      have key : μ.real D * (μ.real E - μ.real F₁) ≥ 0 := by
        rw [hdiff1, mul_sub]
        have hs2 : 0 ≤ μ.real (D ∩ O₂) := measureReal_nonneg
        nlinarith [h_i, h_ii, mul_le_mul_of_nonneg_left ht hs2]
      nlinarith [key]
    · refine (min_le_right _ _).trans ?_
      have key : μ.real D * (μ.real E - μ.real F₂) ≥ 0 := by
        rw [hdiff2, mul_sub]
        have hs1 : 0 ≤ μ.real (D ∩ O₁) := measureReal_nonneg
        nlinarith [h_iii, h_iv, mul_le_mul_of_nonneg_left ht hs1]
      nlinarith [key]

end KNPreFKG

/-- **Kozma–Nitzan 2024, Theorem 1** (arXiv:2401.12397, p. 7) — a THEOREM in print, proved below
(`KozmaNitzan2024_thm1_holds`): the pre-FKG inequality (3) of p. 3,
"`P(0 ↔ b, 0 ↔ A) ≥ min{P(0 ↔ A, a ↔ b) : a ∈ A}`", "holds when `|A| = 2`", for a finite graph with
arbitrary edge probabilities, vertices `0, b` and a two-element vertex set `A`.  Transcribed for the
percolation measure `prodBernoulli w` of a weight function `w : Sym2 V → [0,1]` on a finite vertex type
(`KozmaNitzanReduction.lean`), `{0 ↔ A} = ⋃_{a ∈ A} {0 ↔ a}`, and the minimum over the finite set `A`
written as an existential.
[cite: KozmaNitzan2024, Thm. 1 (p. 7), inequality (3) (p. 3)] -/
def KozmaNitzan2024_thm1 : Prop :=
  ∀ (V : Type) [Fintype V] (w : Sym2 V → unitInterval) (A : Finset V) (o b : V), A.card = 2 →
    ∃ a ∈ A, (prodBernoulli w).real ((⋃ a' ∈ A, openConn o a') ∩ openConn a b) ≤
      (prodBernoulli w).real (openConn o b ∩ ⋃ a' ∈ A, openConn o a')

/-- **Proof of Kozma–Nitzan's Theorem 1** from the proved BHK facts (`KNPreFKG.preFKG_pair`).
[cite: KozmaNitzan2024, Thm. 1 (pp. 7–8)] -/
theorem KozmaNitzan2024_thm1_holds : KozmaNitzan2024_thm1 := by
  intro V _ w A o b hA
  classical
  obtain ⟨a₁, a₂, h12, rfl⟩ := Finset.card_eq_two.1 hA
  have hU : (⋃ a' ∈ ({a₁, a₂} : Finset V), (openConn o a' : Set (BondConfig V))) =
      openConn o a₁ ∪ openConn o a₂ := by
    ext ω
    simp only [mem_iUnion, exists_prop, Finset.mem_insert, Finset.mem_singleton, mem_union]
    constructor
    · rintro ⟨a, rfl | rfl, ha⟩
      · exact Or.inl ha
      · exact Or.inr ha
    · rintro (h | h)
      · exact ⟨a₁, Or.inl rfl, h⟩
      · exact ⟨a₂, Or.inr rfl, h⟩
  rw [hU]
  have key := KNPreFKG.preFKG_pair w o b a₁ a₂
  rcases min_le_iff.1 key with h | h
  · exact ⟨a₁, by simp, h⟩
  · exact ⟨a₂, by simp, h⟩

/-! ### Kozma–Nitzan, Lemma 5: `P(a ↔ b, σ_B) ≤ P(0 ↔ b, σ_B)` -/

/-- **The event `σ_B` of Kozma–Nitzan's Lemma 5** (arXiv:2401.12397, p. 13): "all edges from `0`
to vertices of `B` are open and all other edges from `0` are closed" — for every `u ≠ 0`, the pair
`s(0, u)` is open iff `u ∈ B` (loops are ignored). [cite: KozmaNitzan2024, Lemma 5 (p. 13)] -/
def starEvent (o : V) (B : Set V) : Set (BondConfig V) :=
  {ω | ∀ u, u ≠ o → (s(o, u) ∈ ω ↔ u ∈ B)}

/-- Unfolding of `starEvent`. [folklore] -/
theorem mem_starEvent_iff (o : V) (B : Set V) (ω : BondConfig V) :
    ω ∈ starEvent o B ↔ ∀ u, u ≠ o → (s(o, u) ∈ ω ↔ u ∈ B) := Iff.rfl

/-- **Kozma–Nitzan 2024, Lemma 5** (arXiv:2401.12397, p. 13; "a simple corollary of the BHK
inequality", the engine of Thms. 4–5): "Let `G` be a graph, `0` and `b` some vertices, and `a` and
`v` two neighbours of `0` with `P_{G∖{0}}(a ↔ b) ≤ P_{G∖{0}}(v ↔ b)`. Let `B` be a set of neighbours
of `0` such that `v ∈ B` and let `σ := σ_B` be the event that all edges from `0` to vertices of `B`
are open and all other edges from `0` are closed. Then `P(a ↔ b, σ) ≤ P(0 ↔ b, σ)`." Transcribed
for the percolation measure `prodBernoulli w` of a weight function on a finite vertex type
(`KozmaNitzanReduction.lean`): `P_{G∖{0}}(x ↔ y)`, percolation on the graph with the vertex `0`
deleted, is the probability of an open path from `x` to `y` avoiding `0` (`openConnIn {0}ᶜ x y`;
the event reads only pairs off `0`, whose joint law is that of `G ∖ {0}`); `σ_B = starEvent 0 B`;
"neighbours of `0`" are vertices `≠ 0` (every pair is an edge of the weighted complete graph,
possibly of weight `0`).  Proved below (`KozmaNitzan2024_lemma5_holds`).
[cite: KozmaNitzan2024, Lemma 5 (p. 13)] -/
def KozmaNitzan2024_lemma5 : Prop :=
  ∀ (V : Type) [Fintype V] (w : Sym2 V → unitInterval) (o b a v : V) (B : Set V),
    a ≠ o → v ≠ o → v ∈ B →
    (prodBernoulli w).real (openConnIn {o}ᶜ a b) ≤ (prodBernoulli w).real (openConnIn {o}ᶜ v b) →
    (prodBernoulli w).real (openConn a b ∩ starEvent o B) ≤
      (prodBernoulli w).real (openConn o b ∩ starEvent o B)

namespace KNPreFKG

/-! #### Open paths avoiding a vertex: the restriction coupling to `G ∖ {0}` -/

/-- For the inclusion of a vertex set `S`, the open graph of the restricted configuration is the
open graph induced on `S`. [folklore] -/
theorem openGraph_restrictConfig_val (ω : BondConfig V) (S : Set V) :
    openGraph (restrictConfig (Subtype.val : S → V) ω) = (openGraph ω).induce S := by
  ext a b
  simp only [openGraph_adj, mem_restrictConfig, Sym2.map_mk, SimpleGraph.induce_adj,
    Subtype.val_injective.ne_iff]

/-- `{x ↔ y in S}` is the pull-back of `{x ↔ y}` on `S` along the restriction. [folklore] -/
theorem preimage_openConn_val (S : Set V) {x y : V} (hx : x ∈ S) (hy : y ∈ S) :
    restrictConfig (Subtype.val : S → V) ⁻¹' (openConn (⟨x, hx⟩ : S) ⟨y, hy⟩) = openConnIn S x y := by
  ext ω
  rw [mem_preimage]
  change (openGraph (restrictConfig Subtype.val ω)).Reachable _ _ ↔ _
  rw [openGraph_restrictConfig_val]
  exact ⟨fun h => ⟨hx, hy, h⟩, fun ⟨_, _, h⟩ => h⟩

/-- Reachability of the restricted configuration is reachability inside `S`. [folklore] -/
theorem reachable_restrictConfig_val_iff (S : Set V) (ω : BondConfig V) (x y : S) :
    (openGraph (restrictConfig (Subtype.val : S → V) ω)).Reachable x y ↔ ω ∈ openConnIn S x y := by
  have h := Set.ext_iff.1 (preimage_openConn_val S x.2 y.2) ω
  rw [mem_preimage] at h
  exact h

/-- `x ↔ x in S` for `x ∈ S`. [folklore] -/
theorem openConnIn_rfl {S : Set V} {x : V} (hx : x ∈ S) (ω : BondConfig V) : ω ∈ openConnIn S x x :=
  ⟨hx, hx, SimpleGraph.Reachable.refl _⟩

/-- Transitivity of `↔ in S`. [folklore] -/
theorem openConnIn_trans {S : Set V} {x y z : V} {ω : BondConfig V} (h : ω ∈ openConnIn S x y)
    (h' : ω ∈ openConnIn S y z) : ω ∈ openConnIn S x z := by
  obtain ⟨hx, hy, hr⟩ := h
  obtain ⟨_, hz, hr'⟩ := h'
  exact ⟨hx, hz, hr.trans hr'⟩

/-- An open pair inside `S` joins its endpoints in `S`. [folklore] -/
theorem openConnIn_of_adj {S : Set V} {x y : V} {ω : BondConfig V} (hx : x ∈ S) (hy : y ∈ S)
    (h : (openGraph ω).Adj x y) : ω ∈ openConnIn S x y :=
  ⟨hx, hy, SimpleGraph.Adj.reachable (show ((openGraph ω).induce S).Adj ⟨x, hx⟩ ⟨y, hy⟩ from h)⟩

/-- `{x ↔ y in S} ⊆ {x ↔ y}`. [folklore] -/
theorem reachable_of_openConnIn {S : Set V} {x y : V} {ω : BondConfig V} (h : ω ∈ openConnIn S x y) :
    (openGraph ω).Reachable x y := by
  obtain ⟨hx, hy, hr⟩ := h
  exact hr.map (SimpleGraph.Embedding.induce S).toHom

/-- [cite: KozmaNitzan2024, Lemma 5 (p. 13, "under σ there is no difference between v ↔ b and 0 ↔ b")] -/
theorem walk_decomp {ω : BondConfig V} {o : V} {B : Set V} (hσ : ω ∈ starEvent o B) {x y : V}
    (p : (openGraph ω).Walk x y) (hy : y ≠ o) :
    (x ≠ o → ω ∈ openConnIn {o}ᶜ x y ∨
      ((∃ u ∈ B, u ≠ o ∧ ω ∈ openConnIn {o}ᶜ x u) ∧ ∃ u' ∈ B, u' ≠ o ∧ ω ∈ openConnIn {o}ᶜ u' y)) ∧
    (x = o → ∃ u' ∈ B, u' ≠ o ∧ ω ∈ openConnIn {o}ᶜ u' y) := by
  induction p with
  | nil =>
    exact ⟨fun hx => Or.inl (openConnIn_rfl (mem_compl_singleton_iff.2 hx) ω), fun hx => absurd hx hy⟩
  | cons hadj p ih =>
    rename_i x z y'
    obtain ⟨IH1, IH2⟩ := ih hy
    have hxz : s(x, z) ∈ ω ∧ x ≠ z := (openGraph_adj ω x z).1 hadj
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · by_cases hz : z = o
      · -- first visit to `0` right after `x`: the pair `s(0, x)` is open, so `x ∈ B`
        have hox : s(o, x) ∈ ω := by
          rw [Sym2.eq_swap, ← hz]
          exact hxz.1
        have hxB : x ∈ B := ((mem_starEvent_iff o B ω).1 hσ x hx).1 hox
        exact Or.inr ⟨⟨x, hxB, hx, openConnIn_rfl (mem_compl_singleton_iff.2 hx) ω⟩, IH2 hz⟩
      · have hRxz : ω ∈ openConnIn {o}ᶜ x z :=
          openConnIn_of_adj (mem_compl_singleton_iff.2 hx) (mem_compl_singleton_iff.2 hz) hadj
        rcases IH1 hz with h | ⟨⟨u, huB, huo, hRzu⟩, h2⟩
        · exact Or.inl (openConnIn_trans hRxz h)
        · exact Or.inr ⟨⟨u, huB, huo, openConnIn_trans hRxz hRzu⟩, h2⟩
    · -- `x = 0`: the first pair `s(0, z)` is open, so `z ∈ B`
      have hzo : z ≠ o := fun h => hxz.2 (hx.trans h.symm)
      have hoz : s(o, z) ∈ ω := hx ▸ hxz.1
      have hzB : z ∈ B := ((mem_starEvent_iff o B ω).1 hσ z hzo).1 hoz
      rcases IH1 hzo with h | ⟨_, h2⟩
      · exact ⟨z, hzB, hzo, h⟩
      · exact h2

section Measure

variable [Fintype V]

/-- **The restriction coupling**: the `prodBernoulli w`-probability of the pull-back of an event
of configurations on `S` is its probability for the restricted weights (`prodBernoulli_map_restrictConfig`).
[cite: GrimmettPercolation1999, §1.3 p. 10 (product measure)] -/
theorem real_preimage_restrictConfig_val (w : Sym2 V → unitInterval) (S : Set V)
    (E : Set (BondConfig S)) :
    (prodBernoulli w).real (restrictConfig (Subtype.val : S → V) ⁻¹' E) =
      (prodBernoulli (w ∘ Sym2.map (Subtype.val : S → V))).real E := by
  classical
  rw [← prodBernoulli_map_restrictConfig w Subtype.val_injective,
    map_measureReal_apply (measurable_restrictConfig _) MeasurableSet.of_discrete]

/-- **The star of `0` is independent of the pairs off `0`**: for an event `E` of configurations on
`{0}ᶜ`, `μ(σ_B ∩ pull-back of E) = μ(σ_B) · μ(pull-back of E)` (product measure; Grimmett 1999,
§2.2). [cite: GrimmettPercolation1999, §2.2] -/
theorem real_starEvent_inter_preimage (w : Sym2 V → unitInterval) (o : V) (B : Set V)
    (E : Set (BondConfig ({o}ᶜ : Set V))) :
    (prodBernoulli w).real (starEvent o B ∩ restrictConfig (Subtype.val : ({o}ᶜ : Set V) → V) ⁻¹' E) =
      (prodBernoulli w).real (starEvent o B) *
        (prodBernoulli w).real (restrictConfig (Subtype.val : ({o}ᶜ : Set V) → V) ⁻¹' E) := by
  classical
  set F : Finset (Sym2 V) := Finset.univ.filter fun e => o ∈ e with hF
  have hσ : DeterminedBy (starEvent o B) (↑F : Set (Sym2 V)) := by
    rw [determinedBy_iff]
    intro ω ω' hωω'
    simp only [mem_starEvent_iff]
    refine forall₂_congr fun u _ => ?_
    have hmem : s(o, u) ∈ (↑F : Set (Sym2 V)) := by
      simp [hF]
    have := Set.ext_iff.1 hωω' s(o, u)
    simp only [mem_inter_iff, hmem, and_true] at this
    rw [this]
  have hE : DeterminedBy (restrictConfig (Subtype.val : ({o}ᶜ : Set V) → V) ⁻¹' E) (↑F : Set (Sym2 V))ᶜ := by
    rw [determinedBy_iff]
    intro ω ω' hωω'
    simp only [mem_preimage]
    suffices h : restrictConfig (Subtype.val : ({o}ᶜ : Set V) → V) ω = restrictConfig Subtype.val ω' by
      rw [h]
    ext e
    simp only [mem_restrictConfig]
    have hmem : e.map (Subtype.val : ({o}ᶜ : Set V) → V) ∈ (↑F : Set (Sym2 V))ᶜ := by
      simp only [hF, Finset.coe_filter, Finset.mem_univ, true_and, mem_compl_iff, mem_setOf_eq,
        Sym2.mem_map, not_exists, not_and]
      rintro ⟨x, hx⟩ _ h
      exact hx h
    have := Set.ext_iff.1 hωω' (e.map Subtype.val)
    simp only [mem_inter_iff, hmem, and_true] at this
    exact this
  exact LatticeModels.prodBernoulli_real_inter_of_determinedBy w F hσ hE MeasurableSet.of_discrete
    MeasurableSet.of_discrete

/-- **The gluing step on `G ∖ {0}`** (from Lemma 3(ii) with `Q = {a ↮ B}`): if
`P(a ↔ b) ≤ P(v ↔ b)` for some `v ∈ B`, then
`P({a ↔ b} ∪ ({a ↔ B} ∩ {B ↔ b})) ≤ P(B ↔ b)` — joining `a` to `b` possibly through the set `B`
glued to a point is at most as likely as joining `B` to `b`. [cite: KozmaNitzan2024, Lemma 5 (p. 13)] -/
theorem real_union_le_of_le (w : Sym2 V → unitInterval) (a v b : V) (B : Set V) (hv : v ∈ B)
    (h : (prodBernoulli w).real (openConn a b) ≤ (prodBernoulli w).real (openConn v b)) :
    (prodBernoulli w).real ((openConn a b : Set (BondConfig V)) ∪
        ({ω | ∃ u ∈ B, (openGraph ω).Reachable a u} ∩ {ω | ∃ u ∈ B, (openGraph ω).Reachable u b})) ≤
      (prodBernoulli w).real {ω : BondConfig V | ∃ u ∈ B, (openGraph ω).Reachable u b} := by
  classical
  set μ := prodBernoulli w with hμ
  set X : Set (BondConfig V) := openConn a b with hX
  set Y : Set (BondConfig V) := {ω | ∃ u ∈ B, (openGraph ω).Reachable a u} with hY
  set Z : Set (BondConfig V) := {ω | ∃ u ∈ B, (openGraph ω).Reachable u b} with hZ
  set N : Set (BondConfig V) := {ω | ∀ u ∈ B, ¬ (openGraph ω).Reachable a u} with hN
  set W : Set (BondConfig V) := X ∪ (Y ∩ Z) with hW
  have L3 := KozmaNitzan2024_lemma3_ii_notConn w a v b B h
  -- `W ∖ Z ⊆ {a ↔ b, a ↮ B}`
  have h1 : W ∩ Zᶜ ⊆ X ∩ N := by
    rintro ω ⟨hw, hz⟩
    have hx : ω ∈ X := by
      rcases hw with hx | ⟨_, hz'⟩
      · exact hx
      · exact absurd hz' hz
    refine ⟨hx, fun u hu hau => hz ⟨u, hu, ?_⟩⟩
    exact hau.symm.trans hx
  -- `{v ↔ b, a ↮ B} ⊆ Z ∖ W`
  have h2 : (openConn v b : Set (BondConfig V)) ∩ N ⊆ Z ∩ Wᶜ := by
    rintro ω ⟨hvb, hn⟩
    refine ⟨⟨v, hv, hvb⟩, ?_⟩
    rintro (hx | ⟨⟨u, hu, hau⟩, _⟩)
    · exact hn v hv (SimpleGraph.Reachable.trans hx hvb.symm)
    · exact hn u hu hau
  have hsplit : ∀ A S : Set (BondConfig V), μ.real A = μ.real (A ∩ S) + μ.real (A ∩ Sᶜ) := by
    intro A S
    rw [← measureReal_inter_add_sdiff (s := A) (MeasurableSet.of_discrete : MeasurableSet S), Set.sdiff_eq]
  calc μ.real W = μ.real (W ∩ Z) + μ.real (W ∩ Zᶜ) := hsplit W Z
    _ ≤ μ.real (Z ∩ W) + μ.real (Z ∩ Wᶜ) := by
        rw [inter_comm W Z]
        refine add_le_add le_rfl ?_
        exact (measureReal_mono h1).trans (L3.trans (measureReal_mono h2))
    _ = μ.real Z := (hsplit Z W).symm

end Measure

end KNPreFKG

open KNPreFKG in
/-- **Kozma–Nitzan's Lemma 5, for every finite vertex type** (universe-polymorphic form of
`KozmaNitzan2024_lemma5`, which is the case `V : Type`). Under `σ_B`, an open path from `a` to `b`
either avoids `0` or passes through `0`, entering and leaving through vertices of `B` (`walk_decomp`);
so `{a ↔ b} ∩ σ_B ⊆ ({a ↔ b off 0} ∪ ({a ↔ B off 0} ∩ {B ↔ b off 0})) ∩ σ_B` and
`{B ↔ b off 0} ∩ σ_B ⊆ {0 ↔ b} ∩ σ_B`. The events "off `0`" are pull-backs from `G ∖ {0}`, independent
of `σ_B` (`real_starEvent_inter_preimage`), and on `G ∖ {0}` the gluing step `real_union_le_of_le`
(Lemma 3(ii) with `Q = {a ↮ B}`, i.e. BHK) compares them. [cite: KozmaNitzan2024, Lemma 5 (p. 13)] -/
theorem KozmaNitzan2024_lemma5_fintype {V : Type*} [Fintype V] (w : Sym2 V → unitInterval)
    (o b a v : V) (B : Set V) (hao : a ≠ o) (hvo : v ≠ o) (hvB : v ∈ B)
    (hyp : (prodBernoulli w).real (openConnIn {o}ᶜ a b) ≤ (prodBernoulli w).real (openConnIn {o}ᶜ v b)) :
    (prodBernoulli w).real (openConn a b ∩ starEvent o B) ≤
      (prodBernoulli w).real (openConn o b ∩ starEvent o B) := by
  classical
  set μ := prodBernoulli w with hμ
  -- the degenerate case `b = 0`
  by_cases hbo : b = o
  · subst hbo
    refine measureReal_mono fun ω hω => ⟨SimpleGraph.Reachable.refl _, hω.2⟩
  -- the graph `G ∖ {0}`
  set S : Set V := {o}ᶜ with hS
  haveI : Fintype S := Fintype.ofFinite S
  set f : S → V := Subtype.val with hf
  set w' : Sym2 S → unitInterval := w ∘ Sym2.map f with hw'
  set μ' := prodBernoulli w' with hμ'
  have haS : a ∈ S := mem_compl_singleton_iff.2 hao
  have hvS : v ∈ S := mem_compl_singleton_iff.2 hvo
  have hbS : b ∈ S := mem_compl_singleton_iff.2 hbo
  set a' : S := ⟨a, haS⟩ with ha'
  set v' : S := ⟨v, hvS⟩ with hv'
  set b' : S := ⟨b, hbS⟩ with hb'
  set B' : Set S := {u | (u : V) ∈ B} with hB'
  have hvB' : v' ∈ B' := hvB
  -- the hypothesis, read on `G ∖ {0}`
  have hyp' : μ'.real (openConn a' b') ≤ μ'.real (openConn v' b') := by
    rw [hμ', hw', hf, ← real_preimage_restrictConfig_val, ← real_preimage_restrictConfig_val,
      preimage_openConn_val, preimage_openConn_val]
    exact hyp
  -- the gluing step on `G ∖ {0}`, pulled back to `G`
  set X : Set (BondConfig S) := openConn a' b' with hX
  set Y : Set (BondConfig S) := {ω | ∃ u ∈ B', (openGraph ω).Reachable a' u} with hY
  set Z : Set (BondConfig S) := {ω | ∃ u ∈ B', (openGraph ω).Reachable u b'} with hZ
  have hWZ : μ.real (restrictConfig f ⁻¹' (X ∪ (Y ∩ Z))) ≤ μ.real (restrictConfig f ⁻¹' Z) := by
    rw [hf, real_preimage_restrictConfig_val, real_preimage_restrictConfig_val]
    exact real_union_le_of_le w' a' v' b' B' hvB' hyp'
  -- `{a ↔ b} ∩ σ ⊆ pull-back of X ∪ (Y ∩ Z)`
  have hsub1 : (openConn a b : Set (BondConfig V)) ∩ starEvent o B ⊆
      starEvent o B ∩ restrictConfig f ⁻¹' (X ∪ (Y ∩ Z)) := by
    rintro ω ⟨hab, hσ⟩
    refine ⟨hσ, ?_⟩
    obtain ⟨p⟩ := (hab : (openGraph ω).Reachable a b)
    rw [mem_preimage]
    rcases (walk_decomp hσ p hbo).1 hao with h | ⟨⟨u, huB, huo, hau⟩, ⟨u', hu'B, hu'o, hu'b⟩⟩
    · left
      change (openGraph (restrictConfig Subtype.val ω)).Reachable a' b'
      exact (reachable_restrictConfig_val_iff S ω a' b').2 h
    · right
      refine ⟨⟨⟨u, mem_compl_singleton_iff.2 huo⟩, huB, ?_⟩, ⟨⟨u', mem_compl_singleton_iff.2 hu'o⟩, hu'B, ?_⟩⟩
      · exact (reachable_restrictConfig_val_iff S ω a' ⟨u, _⟩).2 hau
      · exact (reachable_restrictConfig_val_iff S ω ⟨u', _⟩ b').2 hu'b
  -- `σ ∩ pull-back of Z ⊆ {0 ↔ b} ∩ σ`
  have hsub2 : starEvent o B ∩ restrictConfig f ⁻¹' Z ⊆ (openConn o b : Set (BondConfig V)) ∩ starEvent o B := by
    rintro ω ⟨hσ, hz⟩
    refine ⟨?_, hσ⟩
    obtain ⟨u, huB, hub⟩ := hz
    have hub' : (openGraph ω).Reachable (u : V) b :=
      reachable_of_openConnIn ((reachable_restrictConfig_val_iff S ω u b').1 hub)
    have huo : (u : V) ≠ o := mem_compl_singleton_iff.1 u.2
    have hou : s(o, (u : V)) ∈ ω := ((mem_starEvent_iff o B ω).1 hσ u huo).2 huB
    have hadj : (openGraph ω).Adj o u := (openGraph_adj ω o u).2 ⟨hou, huo.symm⟩
    exact hadj.reachable.trans hub'
  -- assemble with the independence of `σ` from the pairs off `0`
  calc μ.real (openConn a b ∩ starEvent o B)
      ≤ μ.real (starEvent o B ∩ restrictConfig f ⁻¹' (X ∪ (Y ∩ Z))) := measureReal_mono hsub1
    _ = μ.real (starEvent o B) * μ.real (restrictConfig f ⁻¹' (X ∪ (Y ∩ Z))) :=
        real_starEvent_inter_preimage w o B _
    _ ≤ μ.real (starEvent o B) * μ.real (restrictConfig f ⁻¹' Z) :=
        mul_le_mul_of_nonneg_left hWZ measureReal_nonneg
    _ = μ.real (starEvent o B ∩ restrictConfig f ⁻¹' Z) := (real_starEvent_inter_preimage w o B _).symm
    _ ≤ μ.real (openConn o b ∩ starEvent o B) := measureReal_mono hsub2

/-- **Proof of Kozma–Nitzan's Lemma 5** (the named statement, `V : Type`), from the polymorphic
form `KozmaNitzan2024_lemma5_fintype`. [cite: KozmaNitzan2024, Lemma 5 (p. 13)] -/
theorem KozmaNitzan2024_lemma5_holds : KozmaNitzan2024_lemma5 :=
  fun _ _ w o b a v B hao hvo hvB hyp => KozmaNitzan2024_lemma5_fintype w o b a v B hao hvo hvB hyp

/-! ### Kozma–Nitzan, Theorem 4: `0` isolated in `G ∖ A` -/

namespace KNPreFKG

variable [Fintype V]

/-- **The stars of `0` partition the space** when `0` is isolated in `G ∖ A`: if every pair
`s(0, u)` with `u ∉ A`, `u ≠ 0` has weight `0` and `0 ∉ A`, then for every event `E`,
`μ(E) = Σ_{B ⊆ A} μ(E ∩ σ_B)` ("Summing over all `B`", p. 14: off the null event that a weight-`0`
pair at `0` is open, `ω ∈ σ_B` exactly for `B = {u ∈ A | s(0,u) ∈ ω}`).
[cite: KozmaNitzan2024, proof of Thm. 4 (pp. 13–14)] -/
theorem real_eq_sum_inter_starEvent (w : Sym2 V → unitInterval) (A : Finset V) (o : V) (ho : o ∉ A)
    (hiso : ∀ u, u ≠ o → u ∉ A → w s(o, u) = 0) (E : Set (BondConfig V)) :
    (prodBernoulli w).real E = ∑ B ∈ A.powerset, (prodBernoulli w).real (E ∩ starEvent o ↑B) := by
  classical
  set μ := prodBernoulli w with hμ
  -- the null event: some weight-`0` pair at `0` is open
  set N : Set (BondConfig V) :=
    ⋃ u ∈ (Finset.univ.filter fun u : V => u ≠ o ∧ u ∉ A), {ω | s(o, u) ∈ ω} with hN
  have hN0 : μ.real N = 0 := by
    refine le_antisymm ?_ measureReal_nonneg
    refine (measureReal_biUnion_finset_le _ _).trans (Finset.sum_eq_zero fun u hu => ?_).le
    rw [Finset.mem_filter] at hu
    rw [hμ, LatticeModels.prodBernoulli_real_setOf_mem, hiso u hu.2.1 hu.2.2]
    rfl
  -- the stars of `0` with `B ⊆ A` are pairwise disjoint …
  have hdisj : Set.PairwiseDisjoint (↑A.powerset : Set (Finset V)) fun B => E ∩ starEvent o ↑B := by
    intro B hB B' hB' hne
    rw [Function.onFun, Set.disjoint_left]
    rintro ω ⟨-, hσ⟩ ⟨-, hσ'⟩
    refine hne (Finset.ext fun u => ?_)
    have hBA : B ⊆ A := Finset.mem_powerset.1 (Finset.mem_coe.1 hB)
    have hB'A : B' ⊆ A := Finset.mem_powerset.1 (Finset.mem_coe.1 hB')
    by_cases huo : u = o
    · subst huo
      exact ⟨fun h => absurd (hBA h) ho, fun h => absurd (hB'A h) ho⟩
    · have h1 := (mem_starEvent_iff o (↑B) ω).1 hσ u huo
      have h2 := (mem_starEvent_iff o (↑B') ω).1 hσ' u huo
      rw [Finset.mem_coe] at h1 h2
      exact h1.symm.trans h2
  -- … and cover `E` off `N`
  have hcover : E ∩ Nᶜ ⊆ ⋃ B ∈ A.powerset, E ∩ starEvent o ↑B := by
    rintro ω ⟨hE, hNω⟩
    simp only [mem_iUnion, exists_prop]
    refine ⟨A.filter fun u => s(o, u) ∈ ω, Finset.mem_powerset.2 (Finset.filter_subset _ _), hE,
      fun u huo => ?_⟩
    simp only [Finset.coe_filter, mem_setOf_eq]
    refine ⟨fun h => ⟨?_, h⟩, fun h => h.2⟩
    by_contra huA
    exact hNω (mem_iUnion₂.2 ⟨u, Finset.mem_filter.2 ⟨Finset.mem_univ _, huo, huA⟩, h⟩)
  have hsub : (⋃ B ∈ A.powerset, E ∩ starEvent o ↑B) ⊆ E :=
    iUnion₂_subset fun B _ => inter_subset_left
  have hU : μ.real (⋃ B ∈ A.powerset, E ∩ starEvent o ↑B) =
      ∑ B ∈ A.powerset, μ.real (E ∩ starEvent o ↑B) :=
    measureReal_biUnion_finset hdisj fun B _ => MeasurableSet.of_discrete
  rw [← hU]
  refine le_antisymm ?_ (measureReal_mono (h₂ := measure_ne_top _ _) hsub)
  have hEN : μ.real (E ∩ N) = 0 :=
    le_antisymm ((measureReal_mono (h₂ := measure_ne_top _ _) inter_subset_right).trans hN0.le)
      measureReal_nonneg
  calc μ.real E = μ.real (E ∩ N) + μ.real (E \ N) :=
        (measureReal_inter_add_sdiff (s := E) (MeasurableSet.of_discrete : MeasurableSet N)).symm
    _ = μ.real (E ∩ Nᶜ) := by rw [hEN, zero_add, Set.sdiff_eq]
    _ ≤ μ.real (⋃ B ∈ A.powerset, E ∩ starEvent o ↑B) :=
        measureReal_mono (h₂ := measure_ne_top _ _) hcover

omit [Fintype V] in
/-- Under `σ_∅` the vertex `0` is isolated in the open graph: it is joined to no other vertex. [folklore] -/
theorem not_reachable_of_mem_starEvent_empty {ω : BondConfig V} {o : V}
    (hσ : ω ∈ starEvent o (∅ : Set V)) {a : V} (ha : a ≠ o) : ¬ (openGraph ω).Reachable o a := by
  rintro ⟨p⟩
  cases p with
  | nil => exact ha rfl
  | cons hadj q =>
    rename_i z
    have hz : s(o, z) ∈ ω ∧ o ≠ z := (openGraph_adj ω o z).1 hadj
    exact ((mem_starEvent_iff o ∅ ω).1 hσ z hz.2.symm).1 hz.1

end KNPreFKG

open KNPreFKG in
/-- **Kozma–Nitzan 2024, Theorem 4** (arXiv:2401.12397, pp. 12–14), in the form of the
pre-FKG inequality (3) the paper asserts for it (p. 12, §3.2: "In this section we will show that
[the pre-FKG inequality] (3) holds when in the graph `G ∖ A` the vertex `0` is isolated"; (3), p. 3:
"`P(0 ↔ b, 0 ↔ A) ≥ min{P(0 ↔ A, a ↔ b) : a ∈ A}`"; Theorem 4: "Let `G` be a graph and let `b ∈ G`
and `A ⊂ G`. If `0` is isolated in `G ∖ A` then `(G, A, 0, b)` is good"): if every pair `s(0, u)` with
`u ∉ A`, `u ≠ 0` has weight `0` ("`0` is isolated in `G ∖ A`") and `A` is nonempty, then for some
`a ∈ A`, `P(a ↔ b, 0 ↔ A) ≤ P(0 ↔ b, 0 ↔ A)`.  Proof as printed (pp. 13–14): with `a₀ ∈ A`
minimising `P_{G∖{0}}(a ↔ b)`, Lemma 5 gives `P(0 ↔ b, σ_B) ≥ P(a₀ ↔ b, σ_B)` for every nonempty
`B ⊆ A`, and `σ_B ⊆ {0 ↔ A}` for such `B`; "Summing over all `B ≠ ∅`" (`real_eq_sum_inter_starEvent`;
under `σ_∅`, `0 ↮ A`, so the `B = ∅` terms vanish). The degenerate cases `0 ∈ A`, `b = 0` hold
trivially. The (2)-form `P(a ↔ b, 0 ↔ A) ≤ P(0 ↔ b)` is `KozmaNitzan2024_thm4_preFKG2`.
[cite: KozmaNitzan2024, Thm. 4 (pp. 12–14), inequality (3) (p. 3)] -/
theorem KozmaNitzan2024_thm4 {V : Type*} [Fintype V] (w : Sym2 V → unitInterval) (A : Finset V)
    (o b : V) (hA : A.Nonempty) (hiso : ∀ u, u ≠ o → u ∉ A → w s(o, u) = 0) :
    ∃ a ∈ A, (prodBernoulli w).real (openConn a b ∩ ⋃ a' ∈ A, openConn o a') ≤
      (prodBernoulli w).real (openConn o b ∩ ⋃ a' ∈ A, openConn o a') := by
  classical
  set μ := prodBernoulli w with hμ
  by_cases hoA : o ∈ A
  · exact ⟨o, hoA, le_rfl⟩
  by_cases hbo : b = o
  · subst hbo
    obtain ⟨a, ha⟩ := hA
    refine ⟨a, ha, measureReal_mono ?_⟩
    rintro ω ⟨-, hU⟩
    exact ⟨(SimpleGraph.Reachable.refl b : (openGraph ω).Reachable b b), hU⟩
  -- `a₀` minimising `P_{G ∖ {0}}(a ↔ b)` over `A`
  obtain ⟨a₀, ha₀, hmin⟩ := A.exists_min_image (fun a => μ.real (openConnIn {o}ᶜ a b)) hA
  refine ⟨a₀, ha₀, ?_⟩
  have ha₀o : a₀ ≠ o := fun h => hoA (h ▸ ha₀)
  rw [real_eq_sum_inter_starEvent w A o hoA hiso (openConn a₀ b ∩ _),
    real_eq_sum_inter_starEvent w A o hoA hiso (openConn o b ∩ _)]
  refine Finset.sum_le_sum fun B hB => ?_
  have hBA : B ⊆ A := Finset.mem_powerset.1 hB
  rcases B.eq_empty_or_nonempty with rfl | ⟨v, hv⟩
  · -- under `σ_∅`, `0 ↮ A`: the `B = ∅` term vanishes
    have h0 : (openConn a₀ b ∩ ⋃ a' ∈ A, openConn o a') ∩ starEvent o ↑(∅ : Finset V) =
        (∅ : Set (BondConfig V)) := by
      ext ω
      simp only [mem_inter_iff, mem_iUnion, exists_prop, mem_empty_iff_false, iff_false, not_and]
      rintro ⟨-, a', ha', hoa'⟩ hσ
      rw [Finset.coe_empty] at hσ
      exact not_reachable_of_mem_starEvent_empty hσ (fun h => hoA (h ▸ ha')) hoa'
    rw [h0, measureReal_empty]
    exact measureReal_nonneg
  · -- `B ≠ ∅`: Lemma 5 with any `v ∈ B`, and `σ_B ⊆ {0 ↔ v} ⊆ {0 ↔ A}`
    have hvo : v ≠ o := fun h => hoA (h ▸ hBA hv)
    have L5 := KozmaNitzan2024_lemma5_fintype w o b a₀ v (↑B) ha₀o hvo (Finset.mem_coe.2 hv)
      (hmin v (hBA hv))
    have hσU : starEvent o (↑B : Set V) ⊆ ⋃ a' ∈ A, (openConn o a' : Set (BondConfig V)) := by
      intro ω hσ
      have hov : s(o, v) ∈ ω := ((mem_starEvent_iff o (↑B) ω).1 hσ v hvo).2 (Finset.mem_coe.2 hv)
      have hadj : (openGraph ω).Adj o v := (openGraph_adj ω o v).2 ⟨hov, hvo.symm⟩
      exact mem_iUnion₂.2 ⟨v, hBA hv, hadj.reachable⟩
    calc μ.real ((openConn a₀ b ∩ ⋃ a' ∈ A, openConn o a') ∩ starEvent o ↑B)
        ≤ μ.real (openConn a₀ b ∩ starEvent o ↑B) :=
          measureReal_mono fun ω ⟨⟨h1, _⟩, h2⟩ => ⟨h1, h2⟩
      _ ≤ μ.real (openConn o b ∩ starEvent o ↑B) := L5
      _ ≤ μ.real ((openConn o b ∩ ⋃ a' ∈ A, openConn o a') ∩ starEvent o ↑B) :=
          measureReal_mono fun ω ⟨h1, h2⟩ => ⟨⟨h1, hσU h2⟩, h2⟩

/-- **Theorem 4 in the (2)-form** (p. 12: "A good graph satisfies [the pre-FKG inequality] (2)",
(2) being "`P(0 ↔ b) ≥ min{P(0 ↔ A, a ↔ b) : a ∈ A}`", p. 3): under the hypotheses of
`KozmaNitzan2024_thm4`, `P(a ↔ b, 0 ↔ A) ≤ P(0 ↔ b)` for some `a ∈ A`.
[cite: KozmaNitzan2024, Thm. 4 (pp. 12–14), inequality (2) (p. 3)] -/
theorem KozmaNitzan2024_thm4_preFKG2 {V : Type*} [Fintype V] (w : Sym2 V → unitInterval)
    (A : Finset V) (o b : V) (hA : A.Nonempty) (hiso : ∀ u, u ≠ o → u ∉ A → w s(o, u) = 0) :
    ∃ a ∈ A, (prodBernoulli w).real (openConn a b ∩ ⋃ a' ∈ A, openConn o a') ≤
      (prodBernoulli w).real (openConn o b) := by
  obtain ⟨a, ha, h⟩ := KozmaNitzan2024_thm4 w A o b hA hiso
  exact ⟨a, ha, h.trans (measureReal_mono inter_subset_left)⟩

/-! ### Kozma–Nitzan, Lemma 3(i) -/

section Lemma3i

open KNPreFKG

variable [Fintype V]

/-- **Kozma–Nitzan 2024, Lemma 3(i)** (arXiv:2401.12397, pp. 6–7). Printed: "Let `G` be a
graph, `a₁, a₂, b ∈ G` and `δ > 0` be such that `P(a₁ ↔ b) < P(a₂ ↔ b) + δ`. (i) If `Q` is an
increasing event in the cluster of `a₂` then we have `P(a₁ ↔ b | Q) < P(a₂ ↔ b | Q) + δ`." Here in
the non-strict, denominator-free form of the printed CONDITIONAL bound with slack `δ ≥ 0`:
`P(a₁ ↔ b, Q) ≤ P(a₂ ↔ b, Q) + δ·P(Q)` for `Q = {ω | C_{a₂}(ω) ∈ 𝒬}`, `𝒬` an upper family of edge sets
(divide by `P(Q)` for the printed form; the strict version follows by shrinking `δ`).  Proof as printed: on
`Dᶜ`, `D = {a₁ ↮ a₂}`, the events `{a₁ ↔ b}`, `{a₂ ↔ b}` coincide; on `D`, BHK Thm. 1.4 (`{a₁ ↔ b}`
increasing in `C_{a₁}`, `Q` increasing in `C_{a₂}`, negatively correlated given `D`), the hypothesis
restricted to `D`, BHK Thm. 1.3 (`{a₂ ↔ b}`, `Q` both increasing in `C_{a₂}`, positively correlated given
`a₂ ↮ a₁`), and for the slack "since `a₁ ↮ a₂` is a decreasing event and `Q` is an increasing event the FKG
inequality allows to bound the rightmost term": `P(D ∩ Q) ≤ P(D)·P(Q)` (Harris, `prodBernoulli_harris_upper_lower`).
[cite: KozmaNitzan2024, Lemma 3(i) (pp. 6–7)] -/
theorem KozmaNitzan2024_lemma3_i (w : Sym2 V → unitInterval) (a₁ a₂ b : V) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : (prodBernoulli w).real (openConn a₁ b) ≤ (prodBernoulli w).real (openConn a₂ b) + δ)
    {𝒬 : Set (Set (Sym2 V))} (h𝒬 : IsUpperSet 𝒬) :
    (prodBernoulli w).real (openConn a₁ b ∩ {ω | openEdgeCluster ω a₂ ∈ 𝒬}) ≤
      (prodBernoulli w).real (openConn a₂ b ∩ {ω | openEdgeCluster ω a₂ ∈ 𝒬}) +
        δ * (prodBernoulli w).real {ω : BondConfig V | openEdgeCluster ω a₂ ∈ 𝒬} := by
  classical
  set μ := prodBernoulli w with hμ
  set X₁ : Set (BondConfig V) := openConn a₁ b with hX₁
  set X₂ : Set (BondConfig V) := openConn a₂ b with hX₂
  set Q : Set (BondConfig V) := {ω | openEdgeCluster ω a₂ ∈ 𝒬} with hQ
  by_cases h12 : a₁ = a₂
  · subst h12
    exact le_add_of_nonneg_right (mul_nonneg hδ measureReal_nonneg)
  set D : Set (BondConfig V) := {ω | ¬ (openGraph ω).Reachable a₁ a₂} with hD
  -- on `Dᶜ` the two connection events agree
  have hagree : X₁ ∩ Dᶜ = X₂ ∩ Dᶜ := by
    ext ω
    simp only [mem_inter_iff, mem_compl_iff, mem_setOf_eq, not_not, hX₁, hX₂, hD, openConn]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h2.symm.trans h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h2.trans h1, h2⟩
  have hsplit : ∀ A : Set (BondConfig V), μ.real A = μ.real (A ∩ D) + μ.real (A ∩ Dᶜ) := by
    intro A
    rw [← measureReal_inter_add_sdiff (s := A) (MeasurableSet.of_discrete : MeasurableSet D), Set.sdiff_eq]
  -- the hypothesis restricted to `D`
  have hH : μ.real (D ∩ X₁) ≤ μ.real (D ∩ X₂) + δ := by
    have h' := h
    rw [hsplit X₁, hsplit X₂, hagree] at h'
    rw [inter_comm D X₁, inter_comm D X₂]
    linarith
  -- (1) two-cluster BHK (Thm. 1.4): `s = a₁`, `t = a₂`, increasing `{a₁ ↔ b}` in `C_{a₁}`, increasing `Q` in `C_{a₂}`
  have h1 := bhk_two_upper_upper w a₁ a₂ h12 (isUpperSet_connFamily a₁ b) h𝒬
  rw [← openConn_eq_setOf_connFamily] at h1
  -- (2) one-cluster BHK (Thm. 1.3): `s = a₂`, `X = {a₁}`, increasing `{a₂ ↔ b}` and `Q` in `C_{a₂}`
  have hD2 : {ω : BondConfig V | ∀ x ∈ ({a₁} : Set V), ¬ (openGraph ω).Reachable a₂ x} = D := by
    ext ω
    simp only [mem_singleton_iff, forall_eq, mem_setOf_eq, hD]
    exact not_congr ⟨SimpleGraph.Reachable.symm, SimpleGraph.Reachable.symm⟩
  have h2 := bhk_one_upper_upper w a₂ ({a₁} : Set V) (by simpa using Ne.symm h12)
    (isUpperSet_connFamily a₂ b) h𝒬
  rw [hD2, ← openConn_eq_setOf_connFamily] at h2
  -- Harris ("FKG"): `D` decreasing, `Q` increasing ⇒ `μ(D ∩ Q) ≤ μ(D)·μ(Q)`
  have hQup : IsUpperSet Q := fun ω ω' hle hω => h𝒬 (BHK2006.openEdgeCluster_mono hle a₂) hω
  have hDlow : IsLowerSet D := by
    have h' : IsLowerSet (openConn a₁ a₂ : Set (BondConfig V))ᶜ := (isUpperSet_openConn a₁ a₂).compl
    exact h'
  have hQD : μ.real (D ∩ Q) ≤ μ.real D * μ.real Q := by
    rw [inter_comm]
    have h' := Percolation.Literature.LatticeModels.prodBernoulli_harris_upper_lower w hQup hDlow
      MeasurableSet.of_discrete MeasurableSet.of_discrete
    rw [mul_comm]; exact h'
  -- the inequality on `D`
  have hcore : μ.real (X₁ ∩ Q ∩ D) ≤ μ.real (X₂ ∩ Q ∩ D) + δ * μ.real Q := by
    rw [inter_comm (X₁ ∩ Q) D, inter_comm (X₂ ∩ Q) D]
    by_cases hD0 : μ.real D = 0
    · have h0 : μ.real (D ∩ (X₁ ∩ Q)) = 0 :=
        le_antisymm ((measureReal_mono inter_subset_left).trans hD0.le) measureReal_nonneg
      rw [h0]
      exact add_nonneg measureReal_nonneg (mul_nonneg hδ measureReal_nonneg)
    · have hDpos : 0 < μ.real D := lt_of_le_of_ne measureReal_nonneg (Ne.symm hD0)
      have hchain : μ.real D * μ.real (D ∩ (X₁ ∩ Q)) ≤
          μ.real D * (μ.real (D ∩ (X₂ ∩ Q)) + δ * μ.real Q) := by
        calc μ.real D * μ.real (D ∩ (X₁ ∩ Q))
            ≤ μ.real (D ∩ X₁) * μ.real (D ∩ Q) := h1
          _ ≤ (μ.real (D ∩ X₂) + δ) * μ.real (D ∩ Q) :=
              mul_le_mul_of_nonneg_right hH measureReal_nonneg
          _ = μ.real (D ∩ X₂) * μ.real (D ∩ Q) + δ * μ.real (D ∩ Q) := by ring
          _ ≤ μ.real D * μ.real (D ∩ (X₂ ∩ Q)) + δ * (μ.real D * μ.real Q) :=
              add_le_add h2 (mul_le_mul_of_nonneg_left hQD hδ)
          _ = μ.real D * (μ.real (D ∩ (X₂ ∩ Q)) + δ * μ.real Q) := by ring
      exact le_of_mul_le_mul_left hchain hDpos
  have hagreeQ : X₁ ∩ Q ∩ Dᶜ = X₂ ∩ Q ∩ Dᶜ := by
    rw [inter_right_comm, hagree, inter_right_comm]
  calc μ.real (X₁ ∩ Q) = μ.real (X₁ ∩ Q ∩ D) + μ.real (X₁ ∩ Q ∩ Dᶜ) := hsplit _
    _ ≤ μ.real (X₂ ∩ Q ∩ D) + δ * μ.real Q + μ.real (X₂ ∩ Q ∩ Dᶜ) := by
        rw [hagreeQ]
        linarith [hcore]
    _ = μ.real (X₂ ∩ Q) + δ * μ.real Q := by
        rw [hsplit (X₂ ∩ Q)]
        ring

end Lemma3i

end Percolation.Literature

end
