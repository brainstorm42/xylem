import Percolation.Literature.BurtonKeaneCombinatorics
import Percolation.Literature.CerfTwoArms
import Percolation.Literature.Connectivity
import Percolation.Literature.InsertionTolerance
import Percolation.Literature.PercolationProofs
import Percolation.Literature.SiteConnectionTools
import Percolation.Literature.ZeroOneLaw
import Percolation.Util.Linter

/-!
# Uniqueness of the infinite open cluster (Aizenman–Kesten–Newman; Burton–Keane)

Discharge of the named fact
`Percolation.Literature.Grimmett1999_numInfiniteClusters_le_one` (`Connectivity.lean`):
for nearest-neighbour bond percolation on `ℤ^d`, every `d` and every `p`, `P_p`-almost surely there
is at most one infinite open cluster (Aizenman–Kesten–Newman, *Comm. Math. Phys.* 111 (1987), Prop.
1.1; Burton–Keane, *Comm. Math. Phys.* 121 (1989); Grimmett, *Percolation* (1999), Thm. (8.1)).

1. (B–R Lemma 1; `ZeroOneLaw.lean`, `bondPercolation_zero_one_of_relabel_shift`)
   translation-invariant events have probability `0` or `1`.
2. (B–R Lemma 2, Newman–Schulman; `bondPercolation_exactlyTwoInfClusters_eq_zero`)
   `P(`exactly two infinite clusters`) = 0`: otherwise some box `Λ_n` meets both clusters with
   positive probability; opening all edges of `Λ_n` (insertion tolerance,
   `InsertionTolerance.lean`) merges them (`openEdges_edgesIn_mem_exactlyOneInfCluster`), so
   `P(`exactly one`) > 0`; both events are translation invariant, so both would have
   probability `1`.
3. (B–R Thm. 4; `bondPercolation_threeInfClusters_eq_zero`) `P(`at least three infinite
   clusters`) = 0`: otherwise some `Λ_r` meets three of them with positive probability, and
   opening the edges of `Λ_r` produces a *cut-ball* (`IsCutSet`, `cutBall`: all edges of the
   ball open, and deleting the ball leaves at least three infinite branches attached to it) with
   probability `a > 0`, at least `a` at every centre by translation invariance. Place `(2m+1)^d`
   disjoint translates of `Λ_r` in `Λ_n`, `n = (2r+2)m + r`; the expected number of cut-balls
   among them is `≥ a (2m+1)^d`, but deterministically the number of cut-balls inside `Λ_n` is
   at most `|∂ⁱⁿΛ_{n+1}| ≤ 2d(2n+3)^{d-1}` by the counting lemma of
   `BurtonKeaneCombinatorics.lean` (B–R Lemma 3; each cut-ball is a hub of the open graph of
   `Λ_{n+1}` relative to `∂ⁱⁿΛ_{n+1}`, `IsCutSet.isHub`), a contradiction for `m` large.
4. Hence `N ≤ 1` a.s. (`Grimmett1999_numInfiniteClusters_le_one_holds`; `d = 0` and `p = 0`
   are trivial edge cases treated separately).
   (The companion zero–one law for the *existence* of an infinite cluster, Grimmett 1999,
   Thm. (1.11), the named fact `Grimmett1999_prob_exists_percolatesAt` of `Connectivity.lean`,
   is discharged separately in `ConnectivityProofs.lean`.)

Differences from the printed proof (all in the direction of what is proved here being the
printed statement): bond instead of site percolation on the specific graph `ℤ^d`, so the family
`W` of centres is the sublattice `(2r+2)Λ_m` and amenability is the explicit count
`|∂ⁱⁿΛ_{n+1}| ≤ 2d(2n+3)^{d-1}` (`card_innerBoundary_box_le`); Lemma 3 is used in the
uncontracted "hub" form proved in `BurtonKeaneCombinatorics.lean`.

Mathlib / this library anchors: `SimpleGraph.Reachable`, `SimpleGraph.Walk.transfer`/`takeUntil`,
`SimpleGraph.Iso.reachable_iff`, `MeasureTheory.lintegral_finsetSum`,
`ProbabilityTheory.setBernoulli_ae_subset`, `measure_iUnion_null_iff`; `bondPercolation`,
`percolatesAt`, `numInfiniteClusters`, `openCluster_eq_supp`, `measurableSet_openConn_holds`,
`measurableSet_percolatesAt_holds`, `BondConfig.relabel`, `bondPercolation_real_preimage_shift`,
`bondPercolation_zero_one_of_relabel_shift` (`ZeroOneLaw.lean`), `withinGraph`, `openClusterIn`,
`openConnVia`, `percolatesVia`, `openClusterIn_relabel`, `relabel_mem_percolatesVia_iff`,
`measurableSet_openConnVia`, `measurableSet_percolatesVia` (`ConstrainedClusters.lean`: "`ω - K`",
the configuration with the vertices of `K` deleted, is percolation with steps constrained to
`withinGraph ⊤ Kᶜ`), `box`, `innerBoundary`, `outerBoundary`, `edgesIn`, `box_induce_reachable`,
`card_innerBoundary_box_le`, `image_add_box_subset`, `zdShiftIso` (`SiteConnectionTools.lean`),
`shiftedBox`, `mem_shiftedBox_iff`, `shiftedBox_zero` (`CerfTwoArms.lean`), `IsHub`,
`card_add_two_le_card_of_isHub`, `exists_adj_reachable_withinGraph_of_walk`
(`BurtonKeaneCombinatorics.lean`), `openEdges`, `bondPercolation_real_pos_of_openEdges`
(`InsertionTolerance.lean`). No new notion of cluster or configuration is introduced; the new
definitions are the events (`threeInfClusters`, `exactlyTwoInfClusters`, `exactlyOneInfCluster`,
`cutBall`, `threeInBox`, `twoInBox`), the predicate `IsCutSet`, the isomorphism
`openGraphRelabelIso`, and the lattice bookkeeping `centres` (the balls `B_r(c)` of
Bollobás–Riordan are the shifted boxes `shiftedBox c r = c + Λ_r` of `CerfTwoArms.lean`).

## References

* B. Bollobás, O. Riordan, *Percolation*, Cambridge Univ. Press 2006, Ch. 5, §5.1, Lemmas 1–3
  and Thm. 4, printed pp. 117–124. The page numbers `p. 103`–`p. 109` in the in-text cites below
  are those of the held electronic copy (as in `BurtonKeaneCombinatorics.lean`): p. 104 ↔ `I_k`
  and Lemma 1, pp. 105–106 ↔ Lemma 2, p. 106 ↔ Lemma 3, pp. 107–109 ↔ Thm. 4 and its proof
  (printed pp. 121–124). [BollobasRiordanPercolation2006]
* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §8.2, Thm. (8.1), pp. 198–202.
  [GrimmettPercolation1999]
* M. Aizenman, H. Kesten, C. M. Newman, Comm. Math. Phys. 111 (1987) 505–531, Prop. 1.1.
  [AizenmanKestenNewmanCMP1987]
* R. M. Burton, M. Keane, Comm. Math. Phys. 121 (1989) 501–505. [BurtonKeane1989]
-/

noncomputable section

namespace Percolation.Literature

open MeasureTheory ProbabilityTheory SimpleGraph Finset
open Percolation.Literature (shiftedBox mem_shiftedBox_iff shiftedBox_zero)
open scoped ENNReal

variable {V W : Type*}

/-! ### `N ≤ 1` in terms of vertices -/

/-- `N ≤ 1` (at most one infinite open cluster) iff any two vertices with infinite open clusters
are joined by an open path. (Grimmett 1999, §8.2: `N` is the number of infinite open clusters.) [cite: GrimmettPercolation1999, §8.2 p. 198] -/
theorem numInfiniteClusters_le_one_iff (ω : BondConfig V) :
    numInfiniteClusters ω ≤ 1 ↔
      ∀ x y, ω ∈ percolatesAt x → ω ∈ percolatesAt y → (openGraph ω).Reachable x y := by
  rw [numInfiniteClusters, Set.encard_le_one_iff]
  constructor
  · intro h x y hx hy
    have hx' : ((openGraph ω).connectedComponentMk x).supp.Infinite := by
      rw [← Percolation.Literature.openCluster_eq_supp]; exact hx
    have hy' : ((openGraph ω).connectedComponentMk y).supp.Infinite := by
      rw [← Percolation.Literature.openCluster_eq_supp]; exact hy
    exact ConnectedComponent.exact (h _ _ hx' hy')
  · intro h C D hC hD
    induction C using ConnectedComponent.ind with
    | h x =>
      induction D using ConnectedComponent.ind with
      | h y =>
        refine ConnectedComponent.sound (h x y ?_ ?_)
        · change (openCluster ω x).Infinite
          rw [Percolation.Literature.openCluster_eq_supp]; exact hC
        · change (openCluster ω y).Infinite
          rw [Percolation.Literature.openCluster_eq_supp]; exact hD

/-! ### Transport of clusters along a bijection of the vertices -/

/-- A bijection `φ` of the vertices is an isomorphism from the open graph of `ω` onto the open
graph of the relabelled configuration `φ '' ω`. [folklore] -/
def openGraphRelabelIso (φ : V ≃ W) (ω : BondConfig V) :
    openGraph ω ≃g openGraph (BondConfig.relabel (sym2Equiv φ) ω) where
  toEquiv := φ
  map_rel_iff' := fun {a b} => openGraph_relabel_adj_iff φ ω a b

/-- Open paths are transported by relabelling: `φ x ↔ φ y` in `φ '' ω` iff `x ↔ y` in `ω`. [folklore] -/
theorem reachable_relabel_iff (φ : V ≃ W) (ω : BondConfig V) (x y : V) :
    (openGraph (BondConfig.relabel (sym2Equiv φ) ω)).Reachable (φ x) (φ y) ↔
      (openGraph ω).Reachable x y :=
  Iso.reachable_iff (φ := openGraphRelabelIso φ ω)

/-- Unconstrained open clusters are the `⊤`-constrained clusters of `ConstrainedClusters.lean`:
`openClusterIn ⊤ ω x = C_ω(x)`. [folklore] -/
theorem openClusterIn_top (ω : BondConfig V) (x : V) : openClusterIn ⊤ ω x = openCluster ω x := by
  ext y
  rw [mem_openClusterIn_iff, inf_top_eq]
  rfl

/-- `{x ↔ ∞ via ⊤} = {|C(x)| = ∞}`. [folklore] -/
theorem percolatesVia_top (x : V) : percolatesVia (⊤ : SimpleGraph V) x = percolatesAt x := by
  ext ω
  change (openClusterIn ⊤ ω x).Infinite ↔ (openCluster ω x).Infinite
  rw [openClusterIn_top]

/-- `{|C(x)| = ∞}` is transported by relabelling along any bijection `φ : V ≃ W` (the case
`K = K' = ⊤` of `relabel_mem_percolatesVia_iff`, `ConstrainedClusters.lean`; for `φ` a
translation of `ℤ^d` this is `preimage_relabel_shift_percolatesAt` of
`ConnectivityProofs.lean`). [folklore] -/
theorem relabel_mem_percolatesAt_iff (φ : V ≃ W) (ω : BondConfig V) (x : V) :
    BondConfig.relabel (sym2Equiv φ) ω ∈ percolatesAt (φ x) ↔ ω ∈ percolatesAt x := by
  rw [← percolatesVia_top, ← percolatesVia_top]
  exact relabel_mem_percolatesVia_iff φ (K := ⊤) (K' := ⊤)
    (fun u v => by simp only [top_adj, ne_eq, φ.injective.ne_iff]) ω x

/-! ### Deleting a set of vertices: percolation with steps avoiding `K` -/

/-
"`ω - K`" (Bollobás–Riordan 2006, Ch. 5, p. 108: "changing the states of all sites in cut-balls to
closed"; bond version: delete the vertices of `K`) is percolation with steps constrained to the
step graph `withinGraph ⊤ Kᶜ` of all steps avoiding `K`, in the sense of `ConstrainedClusters.lean`
(`openClusterIn`, `openConnVia`, `percolatesVia`): the constrained open graph
`openGraph ω ⊓ withinGraph ⊤ Kᶜ` is the open graph with the vertices of `K` deleted,
`withinGraph (openGraph ω) Kᶜ`.
-/

/-- Constraining the open graph to the steps inside `S` is restricting it to `S`:
`openGraph ω ⊓ withinGraph ⊤ S = withinGraph (openGraph ω) S`. [folklore] -/
theorem openGraph_inf_withinGraph_top (ω : BondConfig V) (S : Set V) :
    openGraph ω ⊓ withinGraph ⊤ S = withinGraph (openGraph ω) S := by
  ext x y
  simp only [inf_adj, withinGraph_adj, top_adj, ne_eq, openGraph_adj]
  tauto

/-- Membership in the cluster constrained to steps inside `S` is reachability in the open graph
restricted to `S`. [folklore] -/
theorem mem_openClusterIn_withinGraph_top_iff {S : Set V} {ω : BondConfig V} {x y : V} :
    y ∈ openClusterIn (withinGraph ⊤ S) ω x ↔ (withinGraph (openGraph ω) S).Reachable x y := by
  rw [mem_openClusterIn_iff, openGraph_inf_withinGraph_top]

/-- Opening edges that are not steps of `K` does not change `K`-constrained clusters. [folklore] -/
theorem openClusterIn_openEdges_of_disjoint {K : SimpleGraph V} {F : Set (Sym2 V)}
    (hF : Disjoint F K.edgeSet) (ω : BondConfig V) (x : V) :
    openClusterIn K (openEdges F ω) x = openClusterIn K ω x := by
  have h : openEdges F ω ∩ K.edgeSet = ω ∩ K.edgeSet := by
    ext e
    simp only [Set.mem_inter_iff, mem_openEdges]
    constructor
    · rintro ⟨h | h, hK⟩
      · exact ⟨h, hK⟩
      · exact absurd hK (Set.disjoint_left.1 hF h)
    · rintro ⟨h, hK⟩
      exact ⟨Or.inl h, hK⟩
  rw [openClusterIn, openClusterIn, h]

/-- The edges of `G` inside `K` are not steps avoiding `K`. [folklore] -/
theorem disjoint_edgesIn_edgeSet_withinGraph_compl [DecidableEq V] {G : SimpleGraph V}
    [G.LocallyFinite] (K : Finset V) :
    Disjoint (↑(LatticeModels.edgesIn G K) : Set (Sym2 V)) (withinGraph ⊤ (↑K : Set V)ᶜ).edgeSet := by
  rw [Set.disjoint_left]
  intro e he he'
  rw [Finset.mem_coe, LatticeModels.mem_edgesIn_iff] at he
  induction e using Sym2.ind with
  | h a b => exact he'.2.1 (he.2 a (Sym2.mem_mk_left a b))

/-! ### The events "at least three", "exactly two", "exactly one" infinite open clusters -/

section Events

variable (V)

/-- The event "there are at least three infinite open clusters": three vertices with infinite
open clusters, no two joined by an open path (Bollobás–Riordan 2006, Ch. 5, proof of Thm. 4:
"the probability that there are at least three (possibly infinitely many) infinite open clusters
is zero"). [cite: BollobasRiordanPercolation2006, Ch. 5, Thm. 4 (proof, p. 107)] -/
def threeInfClusters : Set (BondConfig V) :=
  {ω | ∃ x y z, ω ∈ percolatesAt x ∧ ω ∈ percolatesAt y ∧ ω ∈ percolatesAt z ∧
    ¬ (openGraph ω).Reachable x y ∧ ¬ (openGraph ω).Reachable x z ∧ ¬ (openGraph ω).Reachable y z}

/-- The event `I₂` "there are exactly two infinite open clusters" (Bollobás–Riordan 2006, Ch. 5,
`I_k`, p. 104). [cite: BollobasRiordanPercolation2006, Ch. 5, Lemma 2] -/
def exactlyTwoInfClusters : Set (BondConfig V) :=
  {ω | ∃ x y, ω ∈ percolatesAt x ∧ ω ∈ percolatesAt y ∧ ¬ (openGraph ω).Reachable x y ∧
    ∀ z, ω ∈ percolatesAt z → (openGraph ω).Reachable z x ∨ (openGraph ω).Reachable z y}

/-- The event `I₁` "there is exactly one infinite open cluster" (Bollobás–Riordan 2006, Ch. 5,
`I_k`, p. 104). [cite: BollobasRiordanPercolation2006, Ch. 5, Lemma 2] -/
def exactlyOneInfCluster : Set (BondConfig V) :=
  {ω | (∃ x, ω ∈ percolatesAt x) ∧
    ∀ x y, ω ∈ percolatesAt x → ω ∈ percolatesAt y → (openGraph ω).Reachable x y}

variable {V}

/-- If `N ≤ 1` fails then there are exactly two or at least three infinite open clusters. [folklore] -/
theorem mem_union_of_not_numInfiniteClusters_le_one {ω : BondConfig V}
    (h : ¬ numInfiniteClusters ω ≤ 1) :
    ω ∈ exactlyTwoInfClusters V ∪ threeInfClusters V := by
  rw [numInfiniteClusters_le_one_iff] at h
  push Not at h
  obtain ⟨x, y, hx, hy, hxy⟩ := h
  by_cases h3 : ∃ z, ω ∈ percolatesAt z ∧ ¬ (openGraph ω).Reachable z x ∧
      ¬ (openGraph ω).Reachable z y
  · obtain ⟨z, hz, hzx, hzy⟩ := h3
    exact Or.inr ⟨x, y, z, hx, hy, hz, hxy, fun h => hzx h.symm, fun h => hzy h.symm⟩
  · push Not at h3
    refine Or.inl ⟨x, y, hx, hy, hxy, fun z hz => ?_⟩
    by_cases hzx : (openGraph ω).Reachable z x
    · exact Or.inl hzx
    · exact Or.inr (h3 z hz hzx)

/-- `I₁` and `I₂` are disjoint. [folklore] -/
theorem disjoint_exactlyOne_exactlyTwo :
    Disjoint (exactlyOneInfCluster V) (exactlyTwoInfClusters V) := by
  rw [Set.disjoint_left]
  rintro ω ⟨-, h1⟩ ⟨x, y, hx, hy, hxy, -⟩
  exact hxy (h1 x y hx hy)

/-- The event `{x ↔ y}` is measurable (`measurableSet_openConn`, discharged in
`PercolationProofs.lean`), in set-builder form. [cite: GrimmettPercolation1999, §1.3 p. 10] -/
theorem measurableSet_setOf_reachable [Countable V] (x y : V) :
    MeasurableSet {ω : BondConfig V | (openGraph ω).Reachable x y} :=
  measurableSet_openConn_holds x y

/-- `threeInfClusters` is measurable (countably many measurable conditions). [folklore] -/
theorem measurableSet_threeInfClusters [Countable V] :
    MeasurableSet (threeInfClusters V) := by
  unfold threeInfClusters
  simp only [Set.setOf_exists]
  refine MeasurableSet.iUnion fun x => MeasurableSet.iUnion fun y =>
    MeasurableSet.iUnion fun z => ?_
  simp only [Set.setOf_and]
  exact (measurableSet_percolatesAt_holds x).inter ((measurableSet_percolatesAt_holds y).inter
    ((measurableSet_percolatesAt_holds z).inter ((measurableSet_setOf_reachable x y).compl.inter
    ((measurableSet_setOf_reachable x z).compl.inter (measurableSet_setOf_reachable y z).compl))))

/-- `exactlyTwoInfClusters` is measurable. [folklore] -/
theorem measurableSet_exactlyTwoInfClusters [Countable V] :
    MeasurableSet (exactlyTwoInfClusters V) := by
  unfold exactlyTwoInfClusters
  simp only [Set.setOf_exists]
  refine MeasurableSet.iUnion fun x => MeasurableSet.iUnion fun y => ?_
  simp only [Set.setOf_and, Set.setOf_forall, imp_iff_not_or, Set.setOf_or]
  exact (measurableSet_percolatesAt_holds x).inter ((measurableSet_percolatesAt_holds y).inter
    ((measurableSet_setOf_reachable x y).compl.inter (MeasurableSet.iInter fun z =>
      (measurableSet_percolatesAt_holds z).compl.union
        ((measurableSet_setOf_reachable z x).union (measurableSet_setOf_reachable z y)))))

/-- `exactlyOneInfCluster` is measurable. [folklore] -/
theorem measurableSet_exactlyOneInfCluster [Countable V] :
    MeasurableSet (exactlyOneInfCluster V) := by
  unfold exactlyOneInfCluster
  simp only [Set.setOf_and, Set.setOf_exists, Set.setOf_forall, imp_iff_not_or, Set.setOf_or]
  exact (MeasurableSet.iUnion fun x => measurableSet_percolatesAt_holds x).inter
    (MeasurableSet.iInter fun x => MeasurableSet.iInter fun y =>
      (measurableSet_percolatesAt_holds x).compl.union
        ((measurableSet_percolatesAt_holds y).compl.union (measurableSet_setOf_reachable x y)))

/-- `I₂` is invariant under relabelling along a bijection of the vertices. [cite: BollobasRiordanPercolation2006, Ch. 5, p. 104] -/
theorem preimage_relabel_exactlyTwoInfClusters (φ : V ≃ V) :
    BondConfig.relabel (sym2Equiv φ) ⁻¹' exactlyTwoInfClusters V = exactlyTwoInfClusters V := by
  ext ω
  simp only [Set.mem_preimage, exactlyTwoInfClusters, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, y, hx, hy, hxy, hall⟩
    refine ⟨φ.symm x, φ.symm y, ?_, ?_, ?_, fun z hz => ?_⟩
    · rw [← relabel_mem_percolatesAt_iff φ, φ.apply_symm_apply]; exact hx
    · rw [← relabel_mem_percolatesAt_iff φ, φ.apply_symm_apply]; exact hy
    · rw [← reachable_relabel_iff φ, φ.apply_symm_apply, φ.apply_symm_apply]; exact hxy
    · rw [← reachable_relabel_iff φ, ← reachable_relabel_iff φ ω z, φ.apply_symm_apply,
        φ.apply_symm_apply]
      exact hall (φ z) ((relabel_mem_percolatesAt_iff φ ω z).2 hz)
  · rintro ⟨x, y, hx, hy, hxy, hall⟩
    refine ⟨φ x, φ y, ?_, ?_, ?_, fun z hz => ?_⟩
    · rw [relabel_mem_percolatesAt_iff φ]; exact hx
    · rw [relabel_mem_percolatesAt_iff φ]; exact hy
    · rw [reachable_relabel_iff φ]; exact hxy
    · have hz' : ω ∈ percolatesAt (φ.symm z) := by
        rw [← relabel_mem_percolatesAt_iff φ, φ.apply_symm_apply]; exact hz
      have := hall (φ.symm z) hz'
      rwa [← reachable_relabel_iff φ, ← reachable_relabel_iff φ ω (φ.symm z),
        φ.apply_symm_apply] at this

/-- `I₁` is invariant under relabelling along a bijection of the vertices. [cite: BollobasRiordanPercolation2006, Ch. 5, p. 104] -/
theorem preimage_relabel_exactlyOneInfCluster (φ : V ≃ V) :
    BondConfig.relabel (sym2Equiv φ) ⁻¹' exactlyOneInfCluster V = exactlyOneInfCluster V := by
  ext ω
  simp only [Set.mem_preimage, exactlyOneInfCluster, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨x, hx⟩, hall⟩
    refine ⟨⟨φ.symm x, ?_⟩, fun a b ha hb => ?_⟩
    · rw [← relabel_mem_percolatesAt_iff φ, φ.apply_symm_apply]; exact hx
    · rw [← reachable_relabel_iff φ]
      exact hall _ _ ((relabel_mem_percolatesAt_iff φ ω a).2 ha)
        ((relabel_mem_percolatesAt_iff φ ω b).2 hb)
  · rintro ⟨⟨x, hx⟩, hall⟩
    refine ⟨⟨φ x, (relabel_mem_percolatesAt_iff φ ω x).2 hx⟩, fun a b ha hb => ?_⟩
    have ha' : ω ∈ percolatesAt (φ.symm a) := by
      rw [← relabel_mem_percolatesAt_iff φ, φ.apply_symm_apply]; exact ha
    have hb' : ω ∈ percolatesAt (φ.symm b) := by
      rw [← relabel_mem_percolatesAt_iff φ, φ.apply_symm_apply]; exact hb
    have := hall _ _ ha' hb'
    rwa [← reachable_relabel_iff φ, φ.apply_symm_apply, φ.apply_symm_apply] at this

end Events

/-! ### Opening edges inside a set does not change the clusters that avoid it -/

/-- If `x` is joined in `ω ∪ F` to no endpoint of an edge of `F`, then opening the edges of `F`
does not change the open cluster of `x`: an open path of `ω ∪ F` from `x` cannot use an edge of
`F` without first reaching one of its endpoints. [folklore] -/
theorem openCluster_openEdges_eq [DecidableEq V] {F : Set (Sym2 V)} {ω : BondConfig V} {x : V}
    (h : ∀ e ∈ F, ∀ a ∈ e, ¬ (openGraph (openEdges F ω)).Reachable x a) :
    openCluster (openEdges F ω) x = openCluster ω x := by
  refine Set.Subset.antisymm ?_ (openCluster_mono (subset_openEdges F ω) x)
  rintro u ⟨p⟩
  have hp : ∀ e ∈ p.edges, e ∈ (openGraph ω).edgeSet := by
    intro e he
    have he' := p.edges_subset_edgeSet he
    rw [openGraph, edgeSet_fromEdgeSet] at he' ⊢
    refine ⟨?_, he'.2⟩
    rcases he'.1 with h1 | h1
    · exact h1
    · exfalso
      induction e using Sym2.ind with
      | h a b =>
        exact h _ h1 a (Sym2.mem_mk_left a b) ⟨p.takeUntil a (p.fst_mem_support_of_mem_edges he)⟩
  exact ⟨p.transfer (openGraph ω) hp⟩

/-- Under the same hypothesis, `x` percolates in `ω ∪ F` iff it percolates in `ω`. [folklore] -/
theorem openEdges_mem_percolatesAt_iff [DecidableEq V] {F : Set (Sym2 V)} {ω : BondConfig V}
    {x : V} (h : ∀ e ∈ F, ∀ a ∈ e, ¬ (openGraph (openEdges F ω)).Reachable x a) :
    openEdges F ω ∈ percolatesAt x ↔ ω ∈ percolatesAt x := by
  change (openCluster _ x).Infinite ↔ (openCluster ω x).Infinite
  rw [openCluster_openEdges_eq h]

/-! ### The merge lemma (Bollobás–Riordan 2006, Ch. 5, proof of Lemma 2) -/

/-- If all edges of `G` inside `B` are opened then `B` becomes connected in the open graph, as
soon as `B` is connected in `G` through edges inside `B`. [folklore] -/
theorem reachable_openEdges_edgesIn [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite]
    {B : Finset V} (hB : ∀ x ∈ B, ∀ y ∈ B, (withinGraph G ↑B).Reachable x y)
    (ω : BondConfig V) {x y : V} (hx : x ∈ B) (hy : y ∈ B) :
    (openGraph (openEdges ↑(LatticeModels.edgesIn G B) ω)).Reachable x y := by
  refine (hB x hx y hy).mono ?_
  rintro a b ⟨hab, ha, hb⟩
  rw [openGraph_adj, mem_openEdges]
  refine ⟨Or.inr ?_, hab.ne⟩
  rw [Finset.mem_coe, LatticeModels.mem_edgesIn_iff]
  exact ⟨hab, fun c hc => by rcases Sym2.mem_iff.1 hc with rfl | rfl <;> assumption⟩

/-- **Merge lemma** (Bollobás–Riordan 2006, Ch. 5, proof of Lemma 2, p. 106: "if `ω ∈ T_{n,k,s}`
[each infinite cluster contains a site in `B_n(x₀)`] and `ω'` is the configuration obtained from
`ω` by changing the state of each of the closed sites in `B_n(x₀)` from closed to open, then
`ω' ∈ I₁`"; bond version). Let `B` be a finite vertex set connected in `G` through edges inside
`B`. If `ω` has an infinite open cluster and every infinite open cluster of `ω` meets `B`, then
after opening all edges of `G` inside `B` there is exactly one infinite open cluster. [cite: BollobasRiordanPercolation2006, Ch. 5, proof of Lemma 2 (p. 106)] -/
theorem openEdges_edgesIn_mem_exactlyOneInfCluster [DecidableEq V] {G : SimpleGraph V}
    [G.LocallyFinite] {B : Finset V} (hB : ∀ x ∈ B, ∀ y ∈ B, (withinGraph G ↑B).Reachable x y)
    {ω : BondConfig V} (hex : ∃ x, ω ∈ percolatesAt x)
    (hall : ∀ x, ω ∈ percolatesAt x → ∃ b ∈ B, (openGraph ω).Reachable x b) :
    openEdges ↑(LatticeModels.edgesIn G B) ω ∈ exactlyOneInfCluster V := by
  set F : Set (Sym2 V) := ↑(LatticeModels.edgesIn G B) with hF
  have hle : openGraph ω ≤ openGraph (openEdges F ω) :=
    fromEdgeSet_mono (subset_openEdges F ω)
  -- every vertex percolating in `ω ∪ F` is joined to `B` in `ω ∪ F`
  have key : ∀ x, openEdges F ω ∈ percolatesAt x →
      ∃ b ∈ B, (openGraph (openEdges F ω)).Reachable x b := by
    intro x hx
    by_contra hcon
    push Not at hcon
    have h' : ∀ e ∈ F, ∀ a ∈ e, ¬ (openGraph (openEdges F ω)).Reachable x a := by
      intro e he a ha
      rw [hF, Finset.mem_coe, LatticeModels.mem_edgesIn_iff] at he
      exact hcon a (he.2 a ha)
    rw [openEdges_mem_percolatesAt_iff h'] at hx
    obtain ⟨b, hb, hxb⟩ := hall x hx
    exact hcon b hb (hxb.mono hle)
  refine ⟨?_, fun x y hx hy => ?_⟩
  · obtain ⟨x, hx⟩ := hex
    exact ⟨x, percolatesAt_mono (subset_openEdges F ω) x hx⟩
  · obtain ⟨a, ha, hxa⟩ := key x hx
    obtain ⟨b, hb, hyb⟩ := key y hy
    exact (hxa.trans (reachable_openEdges_edgesIn hB ω ha hb)).trans hyb.symm

/-! ### Cut sets (the bond version of Bollobás–Riordan's cut-balls) -/

/-- `K` is a **cut set** of the configuration `ω` (bond version of the cut-ball event `T_r(x)`
of Bollobás–Riordan 2006, Ch. 5, proof of Thm. 4, p. 107: "every site in `B_r(x)` is open, and
there is an infinite open cluster `O` such that when the states of all the sites in `B_r(x)` are
changed from open to closed, `O` is disconnected into at least three infinite open clusters"):
all edges of `G` inside `K` are open, and there are three vertices outside `K`, each joined to `K`
by an open edge, lying in three distinct infinite open clusters of `ω - K` (open paths with steps
avoiding `K`: the events `openConnVia`/`percolatesVia` of `ConstrainedClusters.lean` for the step
graph `withinGraph ⊤ Kᶜ`). [cite: BollobasRiordanPercolation2006, Ch. 5, proof of Thm. 4 (p. 107, the event T_r(x))] -/
structure IsCutSet [DecidableEq V] (G : SimpleGraph V) [G.LocallyFinite] (K : Finset V)
    (ω : BondConfig V) : Prop where
  /-- all edges of `G` inside `K` are open -/
  open_inside : ↑(LatticeModels.edgesIn G K) ⊆ ω
  /-- three open neighbours of `K` in distinct infinite clusters of `ω - K` -/
  branches : ∃ w : Fin 3 → V, (∀ i, w i ∉ K) ∧ (∀ i, ∃ k ∈ K, (openGraph ω).Adj k (w i)) ∧
      (∀ i j, ω ∈ openConnVia (withinGraph ⊤ (↑K : Set V)ᶜ) (w i) (w j) → i = j) ∧
      (∀ i, ω ∈ percolatesVia (withinGraph ⊤ (↑K : Set V)ᶜ) (w i))

/-- An infinite open cluster meeting the finite set `K` contains, outside `K`, an infinite open
cluster of `ω - K` attached to `K` by an open edge: every vertex of `C(x) ∖ K` is joined in
`ω - K` to the last exit point of an open path from `x`, and there are only finitely many exit
points (`ω ⊆ E(G)`, `G` locally finite). (The observation behind Bollobás–Riordan 2006, Ch. 5,
p. 107: if `B_r(x₀)` meets three infinite clusters then opening it gives `T_r(x₀)`.) [cite: BollobasRiordanPercolation2006, Ch. 5, proof of Thm. 4 (p. 107)] -/
theorem exists_branch_of_percolatesAt [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite]
    (K : Finset V) {ω : BondConfig V} (hωG : ω ⊆ G.edgeSet) {x : V} (hxK : x ∈ K)
    (hx : ω ∈ percolatesAt x) :
    ∃ a, a ∉ K ∧ (∃ k ∈ K, (openGraph ω).Adj k a) ∧ (openGraph ω).Reachable x a ∧
      ω ∈ percolatesVia (withinGraph ⊤ (↑K : Set V)ᶜ) a := by
  classical
  -- the exit points: neighbours of `K` outside `K`, joined to `x`
  set N : Finset V := (LatticeModels.outerBoundary G K).filter fun a =>
    (∃ k ∈ K, (openGraph ω).Adj k a) ∧ (openGraph ω).Reachable x a with hN
  -- every vertex of `C(x) ∖ K` lies in the `(ω - K)`-cluster of an exit point
  have hcover : openCluster ω x \ ↑K ⊆
      ⋃ a ∈ N, openClusterIn (withinGraph ⊤ (↑K : Set V)ᶜ) ω a := by
    rintro u ⟨hu, huK⟩
    obtain ⟨q⟩ := (show (openGraph ω).Reachable x u from hu).symm
    obtain ⟨a, b, ha, hb, hab, -, hr⟩ := exists_adj_reachable_withinGraph_of_walk
      (openGraph ω) q (S := (↑K : Set V)ᶜ) huK ⟨x, q.end_mem_support, fun h => h hxK⟩
    have hb' : b ∈ K := by simpa using hb
    have hGab : G.Adj a b := hωG (by rw [openGraph_adj] at hab; exact hab.1)
    have hxa : (openGraph ω).Reachable x a := hu.trans (hr.mono (withinGraph_le _ _))
    refine Set.mem_biUnion (x := a) ?_ ?_
    · rw [hN, Finset.mem_coe, Finset.mem_filter, LatticeModels.mem_outerBoundary_iff]
      exact ⟨⟨ha, b, hb', hGab⟩, ⟨b, hb', hab.symm⟩, hxa⟩
    · rw [mem_openClusterIn_withinGraph_top_iff]
      exact hr.symm
  -- `C(x) ∖ K` is infinite, so some exit cluster is infinite
  have hinf : (openCluster ω x \ ↑K).Infinite := hx.sdiff K.finite_toSet
  by_contra hcon
  push Not at hcon
  refine hinf ((Set.Finite.biUnion N.finite_toSet fun a ha => ?_).subset hcover)
  rw [hN, Finset.mem_coe, Finset.mem_filter, LatticeModels.mem_outerBoundary_iff] at ha
  exact Set.not_infinite.1 (hcon a ha.1.1 ha.2.1 ha.2.2)

/-- **Three clusters make a cut set** (Bollobás–Riordan 2006, Ch. 5, proof of Thm. 4, p. 107:
"If `ω` is a configuration in which `B_r(x₀)` meets at least three infinite open clusters, and
`ω'` is obtained from `ω` by changing the states of all the sites in `B_r(x₀)` to open, then
`ω' ∈ T_r(x₀)`"; bond version). If three vertices of `K` lie in distinct infinite open clusters
of `ω ⊆ E(G)`, then `K` is a cut set of `ω ∪ E(K)`. [cite: BollobasRiordanPercolation2006, Ch. 5, proof of Thm. 4 (p. 107)] -/
theorem isCutSet_openEdges_of_three [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite]
    {K : Finset V} {ω : BondConfig V} (hωG : ω ⊆ G.edgeSet) {x : Fin 3 → V}
    (hxK : ∀ i, x i ∈ K) (hperc : ∀ i, ω ∈ percolatesAt (x i))
    (hdis : ∀ i j, (openGraph ω).Reachable (x i) (x j) → i = j) :
    IsCutSet G K (openEdges ↑(LatticeModels.edgesIn G K) ω) := by
  choose w hwK hwadj hxw hwperc using
    fun i => exists_branch_of_percolatesAt K hωG (hxK i) (hperc i)
  have hcut : ∀ a, openClusterIn (withinGraph ⊤ (↑K : Set V)ᶜ) (openEdges ↑(LatticeModels.edgesIn G K) ω) a =
      openClusterIn (withinGraph ⊤ (↑K : Set V)ᶜ) ω a :=
    openClusterIn_openEdges_of_disjoint (disjoint_edgesIn_edgeSet_withinGraph_compl K) ω
  refine ⟨subset_openEdges_right _ _, w, hwK, fun i => ?_, fun i j hij => ?_, fun i => ?_⟩
  · obtain ⟨k, hk, hadj⟩ := hwadj i
    exact ⟨k, hk, fromEdgeSet_mono (subset_openEdges _ ω) hadj⟩
  · change w j ∈ openClusterIn _ _ (w i) at hij
    rw [hcut, mem_openClusterIn_withinGraph_top_iff] at hij
    have hij' : (openGraph ω).Reachable (w i) (w j) := hij.mono (withinGraph_le _ _)
    exact hdis i j (((hxw i).trans hij').trans (hxw j).symm)
  · change (openClusterIn _ _ (w i)).Infinite
    rw [hcut]
    exact hwperc i

/-- **A cut set is a hub** of the open graph of `Λ` relative to the inner boundary `∂ⁱⁿΛ`
(Bollobás–Riordan 2006, Ch. 5, p. 109: "the condition that `Cᵢ` is a cut-ball says exactly that
deleting `cᵢ` from `H` disconnects a component into at least three components containing vertices
of `L`" — here uncontracted, with `L = ∂ⁱⁿΛ`: each of the three infinite branches of `ω - K`
leaves the finite set `Λ`, and just before its first exit it passes through `∂ⁱⁿΛ`). Hypotheses:
`ω ⊆ E(G)`; `K ⊆ Λ` together with all its neighbours; `K` is connected in `G` inside `K`. [cite: BollobasRiordanPercolation2006, Ch. 5, proof of Thm. 4 (p. 109)] -/
theorem IsCutSet.isHub [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite] {K Λ : Finset V}
    {ω : BondConfig V} (hcut : IsCutSet G K ω) (hωG : ω ⊆ G.edgeSet) (hKne : K.Nonempty)
    (hKΛ : K ⊆ Λ) (hnb : ∀ k ∈ K, ∀ v, G.Adj k v → v ∈ Λ)
    (hKconn : ∀ x ∈ K, ∀ y ∈ K, (withinGraph G ↑K).Reachable x y) :
    IsHub (withinGraph (openGraph ω) ↑Λ) (LatticeModels.innerBoundary G Λ) K := by
  obtain ⟨w, hwK, hwadj, hwdis, hwperc⟩ := hcut.branches
  -- open edges are edges of `G`
  have hGadj : ∀ {a b : V}, (openGraph ω).Adj a b → G.Adj a b := fun h => by
    rw [openGraph_adj] at h; exact hωG h.1
  have hwΛ : ∀ i, w i ∈ Λ := fun i => by
    obtain ⟨k, hk, hadj⟩ := hwadj i
    exact hnb k hk _ (hGadj hadj)
  refine ⟨hKne, ?_, ?_, w, hwK, ?_, ?_, ?_⟩
  · -- `K` misses the inner boundary of `Λ`
    rw [Finset.disjoint_left]
    intro k hk hkL
    rw [LatticeModels.mem_innerBoundary_iff] at hkL
    obtain ⟨-, y, hy, hky⟩ := hkL
    exact hy (hnb k hk y hky)
  · -- `K` is connected inside `K` in the open graph (all its inner edges are open)
    intro x hx y hy
    rw [withinGraph_withinGraph]
    refine (hKconn x hx y hy).mono ?_
    rintro a b ⟨hab, ha, hb⟩
    refine ⟨?_, ⟨hKΛ ha, ha⟩, ⟨hKΛ hb, hb⟩⟩
    rw [openGraph_adj]
    refine ⟨hcut.open_inside ?_, hab.ne⟩
    rw [Finset.mem_coe, LatticeModels.mem_edgesIn_iff]
    exact ⟨hab, fun c hc => by rcases Sym2.mem_iff.1 hc with rfl | rfl <;> assumption⟩
  · intro i
    obtain ⟨k, hk, hadj⟩ := hwadj i
    exact ⟨k, hk, hadj, hKΛ hk, hwΛ i⟩
  · intro i j hij
    refine hwdis i j ?_
    change w j ∈ openClusterIn _ _ (w i)
    rw [mem_openClusterIn_withinGraph_top_iff]
    exact hij.mono (withinGraph_mono_left (withinGraph_le _ _) _)
  · intro i
    -- the infinite branch of `w i` in `ω - K` leaves `Λ`; stop it at its first exit
    obtain ⟨u, hu, huΛ⟩ := (hwperc i).exists_notMem_finset Λ
    have hu' : (withinGraph (openGraph ω) (↑K)ᶜ).Reachable (w i) u := by
      rwa [mem_openClusterIn_withinGraph_top_iff] at hu
    obtain ⟨q⟩ := hu'
    obtain ⟨a, b, ha, hb, hab, -, hr⟩ := exists_adj_reachable_withinGraph_of_walk
      (withinGraph (openGraph ω) (↑K)ᶜ) q (S := (↑Λ : Set V)) (hwΛ i)
      ⟨u, q.end_mem_support, huΛ⟩
    refine ⟨a, ?_, ?_⟩
    · rw [LatticeModels.mem_innerBoundary_iff]
      exact ⟨ha, b, hb, hGadj hab.1⟩
    · rw [withinGraph_withinGraph] at hr ⊢
      rwa [Set.inter_comm]

/-- Cut sets are transported by graph isomorphisms: if `K` is a cut set of `ω` for `G` then
`φ(K)` is a cut set of `φ '' ω` for `G'`. [folklore] -/
theorem IsCutSet.image [DecidableEq V] [DecidableEq W] {G : SimpleGraph V} {G' : SimpleGraph W}
    [G.LocallyFinite] [G'.LocallyFinite] (φ : G ≃g G') {K : Finset V} {ω : BondConfig V}
    (h : IsCutSet G K ω) :
    IsCutSet G' (K.image φ) (BondConfig.relabel (sym2Equiv φ.toEquiv) ω) := by
  obtain ⟨w, hwK, hwadj, hwdis, hwperc⟩ := h.branches
  -- `φ` carries the step graph avoiding `K` onto the step graph avoiding `φ(K)`
  have hK : ∀ u v, (withinGraph ⊤ (↑(K.image φ) : Set W)ᶜ).Adj (φ.toEquiv u) (φ.toEquiv v) ↔
      (withinGraph ⊤ (↑K : Set V)ᶜ).Adj u v := fun u v => by
    change (withinGraph ⊤ (↑(K.image φ) : Set W)ᶜ).Adj (φ u) (φ v) ↔ _
    simp only [withinGraph_adj, top_adj, ne_eq, Set.mem_compl_iff, Finset.mem_coe,
      φ.injective.eq_iff, Function.Injective.mem_finset_image φ.injective]
  refine ⟨?_, fun i => φ (w i), fun i => ?_, fun i => ?_, fun i j hij => ?_, fun i => ?_⟩
  · intro z hz
    rw [Finset.mem_coe, LatticeModels.mem_edgesIn_iff] at hz
    rw [BondConfig.mem_relabel_iff]
    set z₀ := (sym2Equiv φ.toEquiv).symm z with hz₀
    have hzz : sym2Equiv φ.toEquiv z₀ = z := (sym2Equiv φ.toEquiv).apply_symm_apply z
    apply h.open_inside
    rw [Finset.mem_coe, LatticeModels.mem_edgesIn_iff]
    refine ⟨(sym2Equiv_mem_edgeSet_iff φ z₀).1 (hzz ▸ hz.1), fun x hx => ?_⟩
    have hx' : φ x ∈ z := by
      rw [← hzz, sym2Equiv_apply]; exact Sym2.mem_map.2 ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := Finset.mem_image.1 (hz.2 (φ x) hx')
    rwa [← φ.injective hxy]
  · show φ (w i) ∉ K.image φ
    rw [Function.Injective.mem_finset_image φ.injective]; exact hwK i
  · obtain ⟨k, hk, hadj⟩ := hwadj i
    exact ⟨φ k, Finset.mem_image_of_mem _ hk, (openGraph_relabel_adj_iff φ.toEquiv ω k (w i)).2 hadj⟩
  · refine hwdis i j ?_
    change φ.toEquiv (w j) ∈ openClusterIn _ _ (φ.toEquiv (w i)) at hij
    rw [openClusterIn_relabel φ.toEquiv hK ω (w i), φ.toEquiv.injective.mem_set_image] at hij
    exact hij
  · exact (relabel_mem_percolatesVia_iff φ.toEquiv hK ω (w i)).2 (hwperc i)

/-! ### Shifted boxes (the balls `B_r(c)` of the sup norm) -/

section Lattice

variable {d : ℕ}

/-- Membership in the shifted box `Λ_r(c) = c + Λ_r` (`shiftedBox`, `CerfTwoArms.lean`; this is
Bollobás–Riordan's ball `B_r(c)` of the sup norm), coordinatewise. [folklore] -/
theorem mem_shiftedBox_iff' {c x : LatticeModels.Site d} {r : ℕ} :
    x ∈ shiftedBox c r ↔ ∀ i, -(r : ℤ) ≤ x i - c i ∧ x i - c i ≤ r := by
  rw [mem_shiftedBox_iff, LatticeModels.mem_box]; rfl

/-- The centre belongs to its shifted box. [folklore] -/
theorem self_mem_shiftedBox (c : LatticeModels.Site d) (r : ℕ) : c ∈ shiftedBox c r := by
  rw [mem_shiftedBox_iff, sub_self]; exact LatticeModels.zero_mem_box d r

/-- Translating a shifted box translates its centre. [folklore] -/
theorem shiftedBox_image_add (c v : LatticeModels.Site d) (r : ℕ) :
    (shiftedBox c r).image (· + v) = shiftedBox (c + v) r := by
  ext x
  simp only [Finset.mem_image, mem_shiftedBox_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩; simpa [sub_add_eq_sub_sub_swap, add_comm] using hy
  · intro h; exact ⟨x - v, by simpa [sub_sub, add_comm] using h, sub_add_cancel x v⟩

/-- Neighbours of `Λ_n` lie in `Λ_{n+1}`. [folklore] -/
theorem mem_box_succ_of_adj {n : ℕ} {x y : LatticeModels.Site d} (hx : x ∈ LatticeModels.box d n) (h : (LatticeModels.zdGraph d).Adj x y) :
    y ∈ LatticeModels.box d (n + 1) := by
  rw [LatticeModels.mem_box] at hx ⊢
  intro j
  have hxj := hx j
  obtain ⟨i, h | h⟩ := (LatticeModels.zdGraph_adj_iff x y).1 h
  · have hyj : y j = x j + (Pi.single i (1 : ℤ) : LatticeModels.Site d) j := by rw [h]; rfl
    rcases eq_or_ne j i with rfl | hji
    · simp at hyj; push_cast; omega
    · simp [hji] at hyj; push_cast; omega
  · have hxj' : x j = y j + (Pi.single i (1 : ℤ) : LatticeModels.Site d) j := by rw [h]; rfl
    rcases eq_or_ne j i with rfl | hji
    · simp at hxj'; push_cast; omega
    · simp [hji] at hxj'; push_cast; omega

/-- A shifted box is connected in `ℤ^d` through edges inside it (translate of
`box_induce_reachable`). [folklore] -/
theorem shiftedBox_reachable (c : LatticeModels.Site d) (r : ℕ) {x y : LatticeModels.Site d} (hx : x ∈ shiftedBox c r)
    (hy : y ∈ shiftedBox c r) : (withinGraph (LatticeModels.zdGraph d) ↑(shiftedBox c r)).Reachable x y := by
  rw [mem_shiftedBox_iff] at hx hy
  -- translate the path inside `box d r` by `c`
  let f : (LatticeModels.zdGraph d).induce (↑(LatticeModels.box d r) : Set (LatticeModels.Site d)) →g
      withinGraph (LatticeModels.zdGraph d) ↑(shiftedBox c r) :=
    { toFun := fun z => (z : LatticeModels.Site d) + c
      map_rel' := fun {a b} hab => by
        refine ⟨(LatticeModels.zdGraph_adj_shift_iff c a b).2 hab, ?_, ?_⟩
        · show (a : LatticeModels.Site d) + c ∈ (↑(shiftedBox c r) : Set (LatticeModels.Site d))
          rw [Finset.mem_coe, mem_shiftedBox_iff, add_sub_cancel_right]; exact a.2
        · show (b : LatticeModels.Site d) + c ∈ (↑(shiftedBox c r) : Set (LatticeModels.Site d))
          rw [Finset.mem_coe, mem_shiftedBox_iff, add_sub_cancel_right]; exact b.2 }
  have := (box_induce_reachable r hx hy).map f
  simpa [f] using this

/-- Shifted boxes of radius `r` with distinct centres in `(2r+2) ℤ^d` are disjoint. [folklore] -/
theorem disjoint_shiftedBox_of_ne {r : ℕ} {j j' : LatticeModels.Site d} (h : j ≠ j') :
    Disjoint (shiftedBox ((2 * r + 2 : ℤ) • j) r) (shiftedBox ((2 * r + 2 : ℤ) • j') r) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  apply h
  funext i
  rw [mem_shiftedBox_iff'] at hx hx'
  have h1 := hx i; have h2 := hx' i
  simp only [Pi.smul_apply, smul_eq_mul] at h1 h2
  nlinarith

/-- `c ↦ Λ_r(c)` is injective. [folklore] -/
theorem shiftedBox_injective (r : ℕ) : Function.Injective fun c : LatticeModels.Site d => shiftedBox c r := by
  intro c c' h
  have h1 : c + (fun _ => (r : ℤ)) ∈ shiftedBox c' r := by
    rw [← show shiftedBox c r = shiftedBox c' r from h, mem_shiftedBox_iff']; intro i; simp
  have h2 : c' + (fun _ => (r : ℤ)) ∈ shiftedBox c r := by
    rw [show shiftedBox c r = shiftedBox c' r from h, mem_shiftedBox_iff']; intro i; simp
  rw [mem_shiftedBox_iff'] at h1 h2
  funext i
  have := h1 i; have := h2 i
  simp only [Pi.add_apply] at *
  omega

/-! ### The cut-ball event and its probability -/

/-- The **cut-ball event** `T_r(c)`: `Λ_r(c)` is a cut set of the configuration
(Bollobás–Riordan 2006, Ch. 5, proof of Thm. 4, p. 107; bond version, see `IsCutSet`). [cite: BollobasRiordanPercolation2006, Ch. 5, proof of Thm. 4 (p. 107, the event T_r(x))] -/
def cutBall (c : LatticeModels.Site d) (r : ℕ) : Set (BondConfig (LatticeModels.Site d)) :=
  {ω | IsCutSet (LatticeModels.zdGraph d) (shiftedBox c r) ω}

/-- The cut-ball event is measurable (countably many measurable conditions on the states of
edges, `ω - K` being a measurable function of `ω`). [folklore] -/
theorem measurableSet_cutBall (c : LatticeModels.Site d) (r : ℕ) : MeasurableSet (cutBall c r) := by
  set K := shiftedBox c r with hK
  set S : SimpleGraph (LatticeModels.Site d) := withinGraph ⊤ (↑K : Set (LatticeModels.Site d))ᶜ with hS
  have heq : cutBall c r = {ω | (↑(LatticeModels.edgesIn (LatticeModels.zdGraph d) K) : Set (Sym2 (LatticeModels.Site d))) ⊆ ω} ∩
      ⋃ w : Fin 3 → LatticeModels.Site d, ((⋂ i, {_ω | w i ∉ K}) ∩
        (⋂ i, ⋃ k ∈ K, {ω : BondConfig (LatticeModels.Site d) | s(k, w i) ∈ ω ∧ k ≠ w i}) ∩
        (⋂ i, ⋂ j, {_ω | i = j} ∪ (openConnVia S (w i) (w j))ᶜ) ∩
        (⋂ i, percolatesVia S (w i))) := by
    ext ω
    simp only [cutBall, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iUnion, Set.mem_iInter,
      Set.mem_union, Set.mem_compl_iff, exists_prop]
    constructor
    · rintro ⟨h1, w, h2, h3, h4, h5⟩
      refine ⟨h1, w, ⟨⟨h2, h3⟩, fun i j => ?_⟩, h5⟩
      by_cases hij : i = j
      · exact Or.inl hij
      · exact Or.inr fun h => hij (h4 i j h)
    · rintro ⟨h1, w, ⟨⟨h2, h3⟩, h4⟩, h5⟩
      refine ⟨h1, w, h2, h3, fun i j h => ?_, h5⟩
      rcases h4 i j with hij | hij
      · exact hij
      · exact absurd h hij
  rw [heq]
  refine (measurableSet_setOf_subset (Finset.countable_toSet _)).inter
    (MeasurableSet.iUnion fun w => (((MeasurableSet.iInter fun i => MeasurableSet.const _).inter
      (MeasurableSet.iInter fun i => MeasurableSet.biUnion (Finset.countable_toSet _)
        fun k _ => (measurableSet_mem _).inter (MeasurableSet.const _))).inter
      (MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => (MeasurableSet.const _).union
        (measurableSet_openConnVia S (w i) (w j)).compl)).inter
      (MeasurableSet.iInter fun i => measurableSet_percolatesVia S (w i)))

/-- Translating a configuration by `v` carries the cut-ball event at `c` into the cut-ball
event at `c + v`. [folklore] -/
theorem cutBall_subset_preimage_shift (c v : LatticeModels.Site d) (r : ℕ) :
    cutBall c r ⊆ BondConfig.relabel (sym2Equiv (LatticeModels.Site.shift v)) ⁻¹' cutBall (c + v) r := by
  intro ω hω
  have h := IsCutSet.image (zdShiftIso v) hω
  have hbox : (shiftedBox c r).image (zdShiftIso v) = shiftedBox (c + v) r := by
    rw [← shiftedBox_image_add]; rfl
  rw [hbox] at h
  exact h

/-- **Translation invariance of the cut-ball probability** (Bollobás–Riordan 2006, Ch. 5, (2),
p. 107: "for all sites `x ∈ X₀` we have `P(T_r(x)) = a`"): `P_p(T_r(0)) ≤ P_p(T_r(c))` for every
centre `c` (in fact equality; the inequality is what the counting uses). [cite: BollobasRiordanPercolation2006, Ch. 5, proof of Thm. 4 ((2), p. 107)] -/
theorem real_cutBall_zero_le (p : unitInterval) (c : LatticeModels.Site d) (r : ℕ) :
    (bondPercolation (LatticeModels.zdGraph d) p).real (cutBall 0 r) ≤
      (bondPercolation (LatticeModels.zdGraph d) p).real (cutBall c r) := by
  rw [← bondPercolation_real_preimage_shift c p (cutBall c r)]
  refine measureReal_mono ?_
  simpa using cutBall_subset_preimage_shift (0 : LatticeModels.Site d) c r

end Lattice

/-! ### Counting cut-balls (Bollobás–Riordan 2006, Ch. 5, proof of Thm. 4, pp. 108–109) -/

section Counting

variable {d : ℕ}

/-- The centres `(2r+2) j`, `j ∈ Λ_m`, of the `(2m+1)^d` pairwise disjoint translates of `Λ_r`
used in the counting (Bollobás–Riordan take a maximal `2r`-separated on `ℤ^d` a
sublattice does). [cite: BollobasRiordanPercolation2006, Ch. 5, proof of Thm. 4 (p. 108, the set W)] -/
def centres (r m : ℕ) : Finset (LatticeModels.Site d) := (LatticeModels.box d m).image fun j => (2 * r + 2 : ℤ) • j

/-- There are `(2m+1)^d` centres. [folklore] -/
theorem card_centres (r m : ℕ) : (centres r m : Finset (LatticeModels.Site d)).card = (2 * m + 1) ^ d := by
  rw [centres, Finset.card_image_of_injective _ ?_, LatticeModels.card_box]
  intro j j' h
  funext i
  have := congrFun h i
  simp only [Pi.smul_apply, smul_eq_mul] at this
  have h2 : (2 * r + 2 : ℤ) ≠ 0 := by positivity
  exact mul_left_cancel₀ h2 this

/-- The centres lie in `Λ_{(2r+2)m}`. [folklore] -/
theorem centres_subset_box (r m : ℕ) : (centres r m : Finset (LatticeModels.Site d)) ⊆ LatticeModels.box d ((2 * r + 2) * m) := by
  intro c hc
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hc
  rw [LatticeModels.mem_box] at hj ⊢
  intro i
  obtain ⟨h1, h2⟩ := hj i
  simp only [Pi.smul_apply, smul_eq_mul]
  push_cast
  constructor <;> nlinarith

open Classical in
/-- **Deterministic bound on the number of cut-balls** (Bollobás–Riordan 2006, Ch. 5, pp. 108–109,
"`t = |L| ≥ s + 2`" with `t ≤ |S_{n+1}(x₀)|`): for a configuration `ω ⊆ E(ℤ^d)`, the number of
centres `c ∈ (2r+2)Λ_m` such that `Λ_r(c)` is a cut-ball is at most `|∂ⁱⁿΛ_{n+1}|`,
`n = (2r+2)m + r`: the cut-balls are pairwise disjoint hubs of the open graph of `Λ_{n+1}`
relative to `∂ⁱⁿΛ_{n+1}` (`IsCutSet.isHub`), and the counting lemma
`card_add_two_le_card_of_isHub` applies. [cite: BollobasRiordanPercolation2006, Ch. 5, proof of Thm. 4 (pp. 108–109)] -/
theorem card_filter_cutBall_le (r m : ℕ) {ω : BondConfig (LatticeModels.Site d)} (hωG : ω ⊆ (LatticeModels.zdGraph d).edgeSet) :
    ((centres r m).filter fun c => ω ∈ cutBall c r).card ≤
      (LatticeModels.innerBoundary (LatticeModels.zdGraph d) (LatticeModels.box d ((2 * r + 2) * m + r + 1))).card := by
  classical
  set n := (2 * r + 2) * m + r with hn
  set Wc := (centres r m).filter fun c => ω ∈ cutBall c r with hWc
  set 𝓚 : Finset (Finset (LatticeModels.Site d)) := Wc.image fun c => shiftedBox c r with h𝓚
  have hcard : 𝓚.card = Wc.card := Finset.card_image_of_injective _ (shiftedBox_injective r)
  rcases Wc.eq_empty_or_nonempty with hW | hW
  · rw [hW]; simp
  have hne : 𝓚.Nonempty := by rwa [h𝓚, Finset.image_nonempty]
  rw [← hcard]
  refine le_trans (Nat.le_add_right _ 2) (card_add_two_le_card_of_isHub
    (withinGraph (openGraph ω) ↑(LatticeModels.box d (n + 1))) _ 𝓚 hne ?_ ?_)
  · -- distinct cut-balls are disjoint
    intro K hK K' hK' hKK'
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hK
    obtain ⟨c', hc', rfl⟩ := Finset.mem_image.1 hK'
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_filter.1 hc).1
    obtain ⟨j', -, rfl⟩ := Finset.mem_image.1 (Finset.mem_filter.1 hc').1
    exact disjoint_shiftedBox_of_ne fun h => hKK' (by rw [h])
  · -- each cut-ball is a hub
    intro K hK
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hK
    obtain ⟨hcW, hcut⟩ := Finset.mem_filter.1 hc
    have hcbox : c ∈ LatticeModels.box d ((2 * r + 2) * m) := centres_subset_box r m hcW

    have hKn : shiftedBox c r ⊆ LatticeModels.box d n := fun x hx =>
      image_add_box_subset hcbox (Finset.mem_image.2 ⟨x - c, mem_shiftedBox_iff.1 hx, sub_add_cancel x c⟩)
    refine IsCutSet.isHub hcut hωG ⟨c, self_mem_shiftedBox c r⟩
      (hKn.trans (LatticeModels.box_mono d (Nat.le_succ n))) (fun k hk v hkv => ?_) (fun x hx y hy => ?_)
    · exact mem_box_succ_of_adj (hKn hk) hkv
    · exact shiftedBox_reachable c r hx hy

end Counting

/-! ### `P_p(`at least three infinite clusters`) = 0` (Bollobás–Riordan 2006, Ch. 5, Thm. 4) -/

/-- The empty configuration has no infinite cluster. [folklore] -/
theorem empty_notMem_percolatesAt (x : V) : (∅ : BondConfig V) ∉ percolatesAt x := by
  have h : openCluster (∅ : BondConfig V) x = {x} := by
    ext y
    simp only [openCluster, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro h
      have hbot : openGraph (∅ : BondConfig V) = ⊥ := fromEdgeSet_empty
      rw [hbot, reachable_bot] at h
      exact h.symm
    · rintro rfl; rfl
  simp [percolatesAt, h]

/-- At `p = 0` the configuration is a.s. empty, so events avoiding `∅` are null. [folklore] -/
theorem bondPercolation_eq_zero_of_coe_eq_zero {G : SimpleGraph V} {p : unitInterval}
    (hp : (p : ℝ) = 0) {s : Set (BondConfig V)} (hsm : MeasurableSet s)
    (hs : (∅ : BondConfig V) ∉ s) : bondPercolation G p s = 0 := by
  have hp0 : p = 0 := Subtype.ext hp
  subst hp0
  rw [bondPercolation, setBernoulli_zero, Measure.dirac_apply' _ hsm, Set.indicator_of_notMem hs]

section Three

variable {d : ℕ}

/-- The event "`Λ_r` meets three distinct infinite open clusters" (Bollobás–Riordan 2006, Ch. 5,
p. 107: "there is an `r` such that, with positive probability, `B_r(x₀)` contains sites from
(at least) three infinite open clusters"). [cite: BollobasRiordanPercolation2006, Ch. 5, proof of Thm. 4 (p. 107)] -/
def threeInBox (r : ℕ) : Set (BondConfig (LatticeModels.Site d)) :=
  {ω | ∃ x : Fin 3 → LatticeModels.Site d, (∀ i, x i ∈ LatticeModels.box d r) ∧ (∀ i, ω ∈ percolatesAt (x i)) ∧
    ∀ i j, (openGraph ω).Reachable (x i) (x j) → i = j}

/-- "As the balls `B_r(x₀)` cover `Λ`": three infinite clusters meet some common box. (Bollobás–Riordan
 2006, Ch. 5, p. 107.) [cite: BollobasRiordanPercolation2006, Ch. 5, proof of Thm. 4 (p. 107)]
-/
theorem threeInfClusters_subset_iUnion :
    threeInfClusters (LatticeModels.Site d) ⊆ ⋃ r, threeInBox (d := d) r := by
  have hcov : ∀ v : LatticeModels.Site d, ∃ n, v ∈ LatticeModels.box d n := fun v => by
    have hv : v ∈ ⋃ L : ℕ, ((LatticeModels.box d L : Finset (LatticeModels.Site d)) : Set (LatticeModels.Site d)) := by
      rw [LatticeModels.iUnion_coe_box]; exact Set.mem_univ v
    simpa using hv
  rintro ω ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩
  obtain ⟨n₁, h₁⟩ := hcov x
  obtain ⟨n₂, h₂⟩ := hcov y
  obtain ⟨n₃, h₃⟩ := hcov z
  set n := max n₁ (max n₂ n₃) with hn
  have h₁' : x ∈ LatticeModels.box d n := LatticeModels.box_mono d (le_max_left _ _) h₁
  have h₂' : y ∈ LatticeModels.box d n := LatticeModels.box_mono d ((le_max_left _ _).trans (le_max_right _ _)) h₂
  have h₃' : z ∈ LatticeModels.box d n := LatticeModels.box_mono d ((le_max_right _ _).trans (le_max_right _ _)) h₃
  refine Set.mem_iUnion.2 ⟨n, ![x, y, z], ?_, ?_, ?_⟩
  · intro i; fin_cases i <;> assumption
  · intro i; fin_cases i <;> assumption
  · intro i j h
    fin_cases i <;> fin_cases j <;> simp at h ⊢
    all_goals first
      | exact hxy h | exact hxy h.symm | exact hxz h | exact hxz h.symm | exact hyz h
      | exact hyz h.symm

/-- The sum over the centres of the cut-ball probabilities is at most `|∂ⁱⁿΛ_{n+1}|`: it is the
expected number of cut-balls, which is bounded pointwise (`card_filter_cutBall_le`; a.s.
`ω ⊆ E(ℤ^d)`). (Bollobás–Riordan 2006, Ch. 5, p. 108: "by linearity of expectation the expected
number of cut-balls is `Σ_{w ∈ W} P(T_r(w)) = a|W|`" versus (3)–(4).) [cite: BollobasRiordanPercolation2006, Ch. 5, proof of Thm. 4 (p. 108)] -/
theorem sum_measure_cutBall_le (p : unitInterval) (r m : ℕ) :
    ∑ c ∈ centres r m, bondPercolation (LatticeModels.zdGraph d) p (cutBall c r) ≤
      (LatticeModels.innerBoundary (LatticeModels.zdGraph d) (LatticeModels.box d ((2 * r + 2) * m + r + 1))).card := by
  classical
  set μ := bondPercolation (LatticeModels.zdGraph d) p with hμ
  set L := LatticeModels.innerBoundary (LatticeModels.zdGraph d) (LatticeModels.box d ((2 * r + 2) * m + r + 1)) with hL
  have h1 : ∑ c ∈ centres r m, μ (cutBall c r) =
      ∫⁻ ω, ∑ c ∈ centres r m, (cutBall c r).indicator 1 ω ∂μ := by
    rw [lintegral_finsetSum _ fun c _ => measurable_one.indicator (measurableSet_cutBall c r)]
    exact Finset.sum_congr rfl fun c _ => (lintegral_indicator_one (measurableSet_cutBall c r)).symm
  have hae : ∀ᵐ ω ∂μ, ω ⊆ (LatticeModels.zdGraph d).edgeSet := setBernoulli_ae_subset
  calc ∑ c ∈ centres r m, μ (cutBall c r)
        = ∫⁻ ω, ∑ c ∈ centres r m, (cutBall c r).indicator 1 ω ∂μ := h1
    _ ≤ ∫⁻ _ω, (L.card : ℝ≥0∞) ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [hae] with ω hω
        have hsum : ∑ c ∈ centres r m, (cutBall c r).indicator (1 : BondConfig (LatticeModels.Site d) → ℝ≥0∞) ω =
            (((centres r m).filter fun c => ω ∈ cutBall c r).card : ℝ≥0∞) := by
          simp only [Set.indicator_apply, Pi.one_apply]
          rw [Finset.sum_boole]
        rw [hsum]
        exact_mod_cast card_filter_cutBall_le r m hω
    _ = L.card := by rw [lintegral_const, measure_univ, mul_one]

/-- **`P_p(`there are at least three infinite open clusters`) = 0`** on `ℤ^d`, `d ≥ 1`
(Bollobás–Riordan 2006, Ch. 5, Thm. 4 and its proof, pp. 107–109; Burton–Keane 1989;
Aizenman–Kesten–Newman 1987). If not, some `Λ_r` meets three infinite clusters with positive
probability; opening `Λ_r` (insertion tolerance) makes it a cut-ball, so `a = P_p(T_r(0)) > 0`,
and `P_p(T_r(c)) ≥ a` for every centre `c` (translation invariance). With `(2m+1)^d` disjoint
translates in `Λ_n`, `n = (2r+2)m + r`, the expected number of cut-balls is `≥ a(2m+1)^d`, but it
is `≤ |∂ⁱⁿΛ_{n+1}| ≤ 2d(2r+3)^{d-1}(2m+1)^{d-1}` — false for `m` large. [cite: BollobasRiordanPercolation2006, Ch. 5, Thm. 4 (pp. 107–109)] -/
theorem bondPercolation_threeInfClusters_eq_zero (hd : 1 ≤ d) (p : unitInterval) :
    bondPercolation (LatticeModels.zdGraph d) p (threeInfClusters (LatticeModels.Site d)) = 0 := by
  classical
  set μ := bondPercolation (LatticeModels.zdGraph d) p with hμ
  by_contra h3
  -- `p > 0`
  rcases eq_or_lt_of_le p.2.1 with hp0 | hp
  · refine h3 (bondPercolation_eq_zero_of_coe_eq_zero hp0.symm measurableSet_threeInfClusters ?_)
    rintro ⟨x, -, -, hx, -⟩
    exact empty_notMem_percolatesAt x hx
  -- some box meets three infinite clusters with positive probability
  obtain ⟨r, hr⟩ : ∃ r, μ (threeInBox (d := d) r) ≠ 0 := by
    by_contra hall
    push Not at hall
    exact h3 (measure_mono_null threeInfClusters_subset_iUnion (measure_iUnion_null_iff.2 hall))
  -- opening `Λ_r` on this event produces a cut-ball: `a = P(T_r(0)) > 0`
  set A : Set (BondConfig (LatticeModels.Site d)) := threeInBox r ∩ {ω | ω ⊆ (LatticeModels.zdGraph d).edgeSet} with hA_def
  have hAE : μ {ω : BondConfig (LatticeModels.Site d) | ω ⊆ (LatticeModels.zdGraph d).edgeSet}ᶜ = 0 := by
    rw [Set.compl_setOf]
    exact ae_iff.1 (setBernoulli_ae_subset (u := (LatticeModels.zdGraph d).edgeSet) (p := p))
  have hA : 0 < μ.real A := by
    rw [measureReal_def, ENNReal.toReal_pos_iff]
    refine ⟨pos_iff_ne_zero.2 ?_, measure_lt_top _ _⟩
    rwa [hA_def, measure_inter_conull hAE]
  have hAT : ∀ ω ∈ A, openEdges ↑(LatticeModels.edgesIn (LatticeModels.zdGraph d) (LatticeModels.box d r)) ω ∈ cutBall (0 : LatticeModels.Site d) r := by
    rintro ω ⟨⟨x, hxbox, hperc, hdis⟩, hωG⟩
    change IsCutSet (LatticeModels.zdGraph d) (shiftedBox 0 r) _
    rw [shiftedBox_zero]
    exact isCutSet_openEdges_of_three hωG hxbox hperc hdis
  have ha : 0 < μ.real (cutBall (0 : LatticeModels.Site d) r) :=
    bondPercolation_real_pos_of_openEdges (LatticeModels.zdGraph d) hp (LatticeModels.edgesIn (LatticeModels.zdGraph d) (LatticeModels.box d r))
      (fun e he => (LatticeModels.mem_edgesIn_iff.1 he).1) (measurableSet_cutBall 0 r) hA hAT
  set a := μ.real (cutBall (0 : LatticeModels.Site d) r) with ha_def
  -- choose the number of translates
  set C₀ : ℕ := 2 * d * (2 * r + 3) ^ (d - 1) with hC₀
  obtain ⟨m, hm⟩ := exists_nat_gt ((C₀ : ℝ) / a)
  have hm' : (C₀ : ℝ) < a * (2 * m + 1) := by
    rw [div_lt_iff₀ ha] at hm
    nlinarith
  set n := (2 * r + 2) * m + r with hn
  set L := LatticeModels.innerBoundary (LatticeModels.zdGraph d) (LatticeModels.box d (n + 1)) with hL
  -- lower bound for the expected number of cut-balls
  have hlow : ((2 * m + 1 : ℝ)) ^ d * a ≤ ∑ c ∈ centres r m, μ.real (cutBall c r) := by
    calc ((2 * m + 1 : ℝ)) ^ d * a = ∑ _c ∈ centres (d := d) r m, a := by
          rw [Finset.sum_const, card_centres, nsmul_eq_mul]; push_cast; ring
      _ ≤ ∑ c ∈ centres r m, μ.real (cutBall c r) :=
          Finset.sum_le_sum fun c _ => real_cutBall_zero_le p c r
  -- upper bound
  have hup : ∑ c ∈ centres r m, μ.real (cutBall c r) ≤ (L.card : ℝ) := by
    have h := sum_measure_cutBall_le (d := d) p r m
    have hsum : ∑ c ∈ centres r m, μ.real (cutBall c r) =
        (∑ c ∈ centres r m, μ (cutBall c r)).toReal := by
      rw [ENNReal.toReal_sum fun c _ => measure_ne_top _ _]
      rfl
    rw [hsum]
    have := ENNReal.toReal_mono (ENNReal.natCast_ne_top L.card) h
    simpa using this
  -- the boundary is small
  have hLcard : (L.card : ℝ) ≤ C₀ * (2 * m + 1 : ℝ) ^ (d - 1) := by
    have h1 := card_innerBoundary_box_le (d := d) (n + 1)
    have h2 : 2 * (n + 1) + 1 ≤ (2 * r + 3) * (2 * m + 1) := by
      have : (2 * r + 3) * (2 * m + 1) = 2 * (n + 1) + 1 + 2 * m := by rw [hn]; ring
      omega
    calc (L.card : ℝ) ≤ ((2 * d * (2 * (n + 1) + 1) ^ (d - 1) : ℕ) : ℝ) := by exact_mod_cast h1
      _ ≤ ((2 * d * ((2 * r + 3) * (2 * m + 1)) ^ (d - 1) : ℕ) : ℝ) := by
          exact_mod_cast Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h2 _)
      _ = C₀ * (2 * m + 1 : ℝ) ^ (d - 1) := by rw [hC₀]; push_cast; rw [mul_pow]; ring
  -- combine
  have hpow : (2 * m + 1 : ℝ) ^ d = (2 * m + 1) * (2 * m + 1) ^ (d - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hd, pow_succ]
    ring
  have hchain := hlow.trans (hup.trans hLcard)
  rw [hpow] at hchain
  have hpos : (0 : ℝ) < (2 * m + 1) ^ (d - 1) := by positivity
  have key : (2 * m + 1 : ℝ) * a ≤ C₀ := by
    have h' : ((2 * m + 1 : ℝ) * a) * (2 * m + 1) ^ (d - 1) ≤ (C₀ : ℝ) * (2 * m + 1) ^ (d - 1) := by
      linarith [hchain]
    exact le_of_mul_le_mul_right h' hpos
  linarith [key, hm']

end Three

/-! ### `P_p(`exactly two infinite clusters`) = 0` (Bollobás–Riordan 2006, Ch. 5, Lemma 2) -/

section Two

variable {d : ℕ}

/-- The event `T_{n,2}`: exactly two infinite open clusters, both meeting `Λ_n`
(Bollobás–Riordan 2006, Ch. 5, proof of Lemma 2, p. 105: "`T_{n,k}` the event that `I_k`
holds, and each infinite cluster contains a site in `B_n(x₀)`"). [cite: BollobasRiordanPercolation2006, Ch. 5, proof of Lemma 2 (p. 105)] -/
def twoInBox (n : ℕ) : Set (BondConfig (LatticeModels.Site d)) :=
  {ω | ∃ x y, x ∈ LatticeModels.box d n ∧ y ∈ LatticeModels.box d n ∧ ω ∈ percolatesAt x ∧ ω ∈ percolatesAt y ∧
    ¬ (openGraph ω).Reachable x y ∧
    ∀ z, ω ∈ percolatesAt z → (openGraph ω).Reachable z x ∨ (openGraph ω).Reachable z y}

/-- `I₂ = ⋃ₙ T_{n,2}` ("As the balls `B_n(x₀)` cover `Λ`", Bollobás–Riordan 2006, p. 105). [cite: BollobasRiordanPercolation2006, Ch. 5, proof of Lemma 2 (p. 105)] -/
theorem exactlyTwoInfClusters_subset_iUnion :
    exactlyTwoInfClusters (LatticeModels.Site d) ⊆ ⋃ n, twoInBox (d := d) n := by
  have hcov : ∀ v : LatticeModels.Site d, ∃ n, v ∈ LatticeModels.box d n := fun v => by
    have hv : v ∈ ⋃ L : ℕ, ((LatticeModels.box d L : Finset (LatticeModels.Site d)) : Set (LatticeModels.Site d)) := by
      rw [LatticeModels.iUnion_coe_box]; exact Set.mem_univ v
    simpa using hv
  rintro ω ⟨x, y, hx, hy, hxy, hall⟩
  obtain ⟨n₁, h₁⟩ := hcov x
  obtain ⟨n₂, h₂⟩ := hcov y
  exact Set.mem_iUnion.2 ⟨max n₁ n₂, x, y, LatticeModels.box_mono d (le_max_left _ _) h₁,
    LatticeModels.box_mono d (le_max_right _ _) h₂, hx, hy, hxy, hall⟩

/-- Boxes are connected in `ℤ^d` through edges inside them. [folklore] -/
theorem box_withinGraph_reachable (n : ℕ) {x y : LatticeModels.Site d} (hx : x ∈ LatticeModels.box d n) (hy : y ∈ LatticeModels.box d n) :
    (withinGraph (LatticeModels.zdGraph d) ↑(LatticeModels.box d n)).Reachable x y := by
  rw [← shiftedBox_zero]
  exact shiftedBox_reachable 0 n (by rwa [shiftedBox_zero]) (by rwa [shiftedBox_zero])

/-- A non-zero vector of `ℤ^d`, `d ≥ 1` (for the ergodicity of translations). [folklore] -/
theorem single_ne_zero (hd : 1 ≤ d) : (Pi.single ⟨0, hd⟩ 1 : LatticeModels.Site d) ≠ 0 := by
  intro h
  have := congrFun h ⟨0, hd⟩
  simp at this

/-- **`P_p(`there are exactly two infinite open clusters`) = 0`** on `ℤ^d`, `d ≥ 1`
(Bollobás–Riordan 2006, Ch. 5, Lemma 2 (Newman–Schulman 1981), pp. 105–106, case `k = 2`).
If `P(I₂) > 0` then `P(T_{n,2}) > 0` for some `n`; opening all edges of `Λ_n` on `T_{n,2}` gives
`I₁` (merge lemma), so `P(I₁) > 0` by insertion tolerance; `I₁`, `I₂` are translation
invariant, so both have probability `1` (`ZeroOneLaw.lean`), impossible as they are disjoint. [cite: BollobasRiordanPercolation2006, Ch. 5, Lemma 2 (pp. 105–106)] -/
theorem bondPercolation_exactlyTwoInfClusters_eq_zero (hd : 1 ≤ d) (p : unitInterval) :
    bondPercolation (LatticeModels.zdGraph d) p (exactlyTwoInfClusters (LatticeModels.Site d)) = 0 := by
  classical
  set μ := bondPercolation (LatticeModels.zdGraph d) p with hμ
  by_contra h2
  -- `p > 0`
  rcases eq_or_lt_of_le p.2.1 with hp0 | hp
  · refine h2 (bondPercolation_eq_zero_of_coe_eq_zero hp0.symm measurableSet_exactlyTwoInfClusters ?_)
    rintro ⟨x, -, hx, -⟩
    exact empty_notMem_percolatesAt x hx
  -- some `T_{n,2}` has positive probability
  obtain ⟨n, hn⟩ : ∃ n, μ (twoInBox (d := d) n) ≠ 0 := by
    by_contra hall
    push Not at hall
    exact h2 (measure_mono_null exactlyTwoInfClusters_subset_iUnion (measure_iUnion_null_iff.2 hall))
  set A : Set (BondConfig (LatticeModels.Site d)) := twoInBox n ∩ {ω | ω ⊆ (LatticeModels.zdGraph d).edgeSet} with hA_def
  have hAE : μ {ω : BondConfig (LatticeModels.Site d) | ω ⊆ (LatticeModels.zdGraph d).edgeSet}ᶜ = 0 := by
    rw [Set.compl_setOf]
    exact ae_iff.1 (setBernoulli_ae_subset (u := (LatticeModels.zdGraph d).edgeSet) (p := p))
  have hA : 0 < μ.real A := by
    rw [measureReal_def, ENNReal.toReal_pos_iff]
    refine ⟨pos_iff_ne_zero.2 ?_, measure_lt_top _ _⟩
    rwa [hA_def, measure_inter_conull hAE]
  -- opening `Λ_n` merges the two clusters
  have hAT : ∀ ω ∈ A, openEdges ↑(LatticeModels.edgesIn (LatticeModels.zdGraph d) (LatticeModels.box d n)) ω ∈ exactlyOneInfCluster (LatticeModels.Site d) := by
    rintro ω ⟨⟨x, y, hx, hy, hpx, hpy, -, hall⟩, -⟩
    refine openEdges_edgesIn_mem_exactlyOneInfCluster
      (fun a ha b hb => box_withinGraph_reachable n ha hb) ⟨x, hpx⟩ fun z hz => ?_
    rcases hall z hz with h | h
    · exact ⟨x, hx, h⟩
    · exact ⟨y, hy, h⟩
  have h1 : 0 < μ.real (exactlyOneInfCluster (LatticeModels.Site d)) :=
    bondPercolation_real_pos_of_openEdges (LatticeModels.zdGraph d) hp (LatticeModels.edgesIn (LatticeModels.zdGraph d) (LatticeModels.box d n))
      (fun e he => (LatticeModels.mem_edgesIn_iff.1 he).1) measurableSet_exactlyOneInfCluster hA hAT
  -- ergodicity of a translation
  have hv0 := single_ne_zero hd
  have hI1 : μ (exactlyOneInfCluster (LatticeModels.Site d)) = 1 := by
    rcases bondPercolation_zero_one_of_relabel_shift p hv0 measurableSet_exactlyOneInfCluster
      (preimage_relabel_exactlyOneInfCluster (LatticeModels.Site.shift (Pi.single ⟨0, hd⟩ 1))) with h | h
    · exfalso
      rw [measureReal_def, hμ, h] at h1
      simp at h1
    · exact h
  have hI2 : μ (exactlyTwoInfClusters (LatticeModels.Site d)) = 1 := by
    rcases bondPercolation_zero_one_of_relabel_shift p hv0 measurableSet_exactlyTwoInfClusters
      (preimage_relabel_exactlyTwoInfClusters (LatticeModels.Site.shift (Pi.single ⟨0, hd⟩ 1))) with h | h
    · exact absurd h h2
    · exact h
  have hunion : μ (exactlyOneInfCluster (LatticeModels.Site d) ∪ exactlyTwoInfClusters (LatticeModels.Site d)) = 2 := by
    rw [measure_union disjoint_exactlyOne_exactlyTwo measurableSet_exactlyTwoInfClusters, hI1, hI2,
      one_add_one_eq_two]
  have hle := prob_le_one (μ := μ) (s := exactlyOneInfCluster (LatticeModels.Site d) ∪ exactlyTwoInfClusters (LatticeModels.Site d))
  rw [hunion] at hle
  exact absurd hle (not_le.2 ENNReal.one_lt_two)

end Two

/-! ### Uniqueness of the infinite cluster -/

/-- **Uniqueness of the infinite open cluster** (Aizenman–Kesten–Newman, *Comm. Math. Phys.* 111
(1987), Prop. 1.1; Burton–Keane, *Comm. Math. Phys.* 121 (1989); Grimmett 1999, Thm. (8.1),
p. 198; proof of Bollobás–Riordan 2006, Ch. 5, Lemma 2 + Thm. 4): discharge of the named fact
`Grimmett1999_numInfiniteClusters_le_one` — for every `d` and every `p ∈ [0, 1]`,
`P_p`-almost surely nearest-neighbour bond percolation on `ℤ^d` has at most one infinite open
cluster. If `N ≤ 1` fails there are exactly two or at least three infinite clusters, and both
events are null (`bondPercolation_exactlyTwoInfClusters_eq_zero`,
`bondPercolation_threeInfClusters_eq_zero`); for `d = 0` there is no infinite cluster at all. [cite: BollobasRiordanPercolation2006, Ch. 5, Lemma 2 and Thm. 4 (pp. 105–109)] [cite: GrimmettPercolation1999, Thm. (8.1) p. 198] [cite: AizenmanKestenNewmanCMP1987, Prop. 1.1 p. 507] -/
theorem Grimmett1999_numInfiniteClusters_le_one_holds : Grimmett1999_numInfiniteClusters_le_one := by
  intro d p
  rcases Nat.eq_zero_or_pos d with hd | hd
  · -- `d = 0`: `ℤ⁰` is a single site, no cluster is infinite
    subst hd
    refine Filter.Eventually.of_forall fun ω => ?_
    rw [numInfiniteClusters_le_one_iff]
    intro x y hx
    exact absurd hx (Set.not_infinite.2 (Set.toFinite _))
  · rw [ae_iff]
    refine measure_mono_null (fun ω hω => mem_union_of_not_numInfiniteClusters_le_one hω) ?_
    exact measure_union_null (bondPercolation_exactlyTwoInfClusters_eq_zero hd p)
      (bondPercolation_threeInfClusters_eq_zero hd p)

end Percolation.Literature

end
