import Percolation.Literature.BondPercolationSymmetry
import Percolation.Literature.PercolationEvents
import Percolation.Literature.PercolationProofs
import Percolation.Literature.SubgraphMonotonicity
import Percolation.Util.Linter

/-!
# Open paths confined to a region: "`x ↔ y` in `V`" and "`x ↔ y` in `V*`"

Grimmett, *Percolation*, 2nd ed. (1999), works
throughout Chapter 7 with open paths confined to a vertex set and, in §7.3 (proof of Lemma (7.36),
pp. 164–165), with the starred variant: "For `V ⊆ ℤ³` and `x, y ∈ V`, we write '`x ↔ y` in `V*`'
if there exists an open path in `V` joining `x` and `y` and using no edge joining two vertices in
the boundary of `V`. Similarly, we write '`x ↔ ∞` in `V*`' if such an infinite open path exists
having end vertex `x`." This file sets up these notions for a general graph `G` on a
vertex type `V` (bond configurations `ω : BondConfig V`, `Literature/Basic.lean`):

* `openClusterIn K ω x` — the set of vertices joined to `x` by an open path all of whose steps
  are edges of the "step graph" `K` (`= openCluster (ω ∩ K.edgeSet) x`, so that every statement
  about constrained clusters is a statement about ordinary clusters of the restricted
  configuration `ω ∩ E(K)`); `openGraph_inter_edgeSet : openGraph (ω ∩ E(K)) = openGraph ω ⊓ K`;
* equivariance under a bijection `e : V ≃ V'` carrying `K` to `K'`
  (`openClusterIn_relabel`, `relabel_mem_percolatesVia_iff`), for the translation / reflection
  invariance steps of §7.3;
* the bridge to this library's induced-subgraph convention (`HalfSpace.lean`: `θ_ℍ`, `θ_{S_k}` are
  `theta` of `G.induce R`): `theta_induce_eq_real_percolatesVia`,
  `θ_{G[R]}(x, p) = P_p(x ↔ ∞ in R)` — under `P_p` almost every configuration only opens edges
  of `G`, and then the open cluster of `x` in the induced graph of the restricted configuration is
  the constrained cluster `openClusterIn (withinGraph G R) ω x` (Grimmett 1999, §7.2 p. 148:
  `θ(p, A)`/`p_c(A)` "of bond percolation on the subgraph of `ℤ^d` induced by `A`" versus
  §7.3's paths "in `A`").

## References

* G. Grimmett, *Percolation*, 2nd ed., Grundlehren 321, Springer 1999, §1.3 (`x ↔ y`), §7.2
  p. 148 ("in `A`"), §7.3 pp. 164–165 ("in `V*`").
-/

noncomputable section

namespace Percolation.Literature

open MeasureTheory

variable {V : Type*}

/-! ## Step graphs: paths in `R`, paths in `R*` -/

/-- The graph of steps of `G` inside the vertex set `R`: `u ∼ v` iff `G.Adj u v` and
`u, v ∈ R` (an "open path in `R`" is an open path all of whose steps are of this kind;
Grimmett 1999, §7.2 p. 148). [cite: GrimmettPercolation1999, §7.2 p. 148 (in A)] -/
def withinGraph (G : SimpleGraph V) (R : Set V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ∈ R ∧ v ∈ R
  symm.symm _ _ h := ⟨h.1.symm, h.2.2, h.2.1⟩
  loopless.irrefl _ h := h.1.ne rfl

/-- The graph of steps of `G` inside `R` **using no edge joining two vertices of `B`**
(Grimmett 1999, §7.3 p. 164: "'`x ↔ y` in `V*`' if there exists an open path in `V` joining `x`
and `y` and using no edge joining two vertices in the boundary of `V`"; here `B` is a parameter,
`B = ∂V` in Grimmett's usage). [cite: GrimmettPercolation1999, §7.3 p. 164 (in V*)] -/
def starGraph (G : SimpleGraph V) (R B : Set V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ∈ R ∧ v ∈ R ∧ ¬(u ∈ B ∧ v ∈ B)
  symm.symm _ _ h := ⟨h.1.symm, h.2.2.1, h.2.1, fun h' => h.2.2.2 h'.symm⟩
  loopless.irrefl _ h := h.1.ne rfl

/-- Adjacency in `withinGraph`, unfolded. [folklore] -/
@[simp] theorem withinGraph_adj {G : SimpleGraph V} {R : Set V} {u v : V} :
    (withinGraph G R).Adj u v ↔ G.Adj u v ∧ u ∈ R ∧ v ∈ R := Iff.rfl

/-- Adjacency in `starGraph`, unfolded. [folklore] -/
@[simp] theorem starGraph_adj {G : SimpleGraph V} {R B : Set V} {u v : V} :
    (starGraph G R B).Adj u v ↔ G.Adj u v ∧ u ∈ R ∧ v ∈ R ∧ ¬(u ∈ B ∧ v ∈ B) := Iff.rfl

/-- Paths in `R` are paths of `G`. [folklore] -/
theorem withinGraph_le (G : SimpleGraph V) (R : Set V) : withinGraph G R ≤ G :=
  fun _ _ h => h.1

/-- Paths in `R*` are paths in `R`. [folklore] -/
theorem starGraph_le_withinGraph (G : SimpleGraph V) (R B : Set V) :
    starGraph G R B ≤ withinGraph G R :=
  fun _ _ h => ⟨h.1, h.2.1, h.2.2.1⟩

/-- Paths in `R*` are paths of `G`. [folklore] -/
theorem starGraph_le (G : SimpleGraph V) (R B : Set V) : starGraph G R B ≤ G :=
  fun _ _ h => h.1

/-- `withinGraph` is monotone in the region. [folklore] -/
theorem withinGraph_mono (G : SimpleGraph V) {R R' : Set V} (h : R ⊆ R') :
    withinGraph G R ≤ withinGraph G R' :=
  fun _ _ huv => ⟨huv.1, h huv.2.1, h huv.2.2⟩

/-- `starGraph` is monotone in the region and antitone in the forbidden set. [folklore] -/
theorem starGraph_mono (G : SimpleGraph V) {R R' B B' : Set V} (hR : R ⊆ R') (hB : B' ⊆ B) :
    starGraph G R B ≤ starGraph G R' B' :=
  fun _ _ h => ⟨h.1, hR h.2.1, hR h.2.2.1, fun h' => h.2.2.2 ⟨hB h'.1, hB h'.2⟩⟩

/-- A path in a region `R` disjoint from `B` is a path in `R'*` for every `R' ⊇ R` (e.g. an open
path of the shifted half-space `ℍ + e₃` is an open path of `ℍ*`, Grimmett 1999, p. 165).
[folklore] -/
theorem withinGraph_le_starGraph (G : SimpleGraph V) {R R' B : Set V} (hR : R ⊆ R')
    (hB : Disjoint R B) : withinGraph G R ≤ starGraph G R' B :=
  fun _ _ h => ⟨h.1, hR h.2.1, hR h.2.2, fun h' => hB.le_bot ⟨h.2.1, h'.1⟩⟩

/-- The edges of `withinGraph G R` are edges of `G` with both endpoints in `R`. [folklore] -/
theorem mem_edgeSet_withinGraph {G : SimpleGraph V} {R : Set V} {u v : V} :
    s(u, v) ∈ (withinGraph G R).edgeSet ↔ G.Adj u v ∧ u ∈ R ∧ v ∈ R := Iff.rfl

/-- The edges of `starGraph G R B`. [folklore] -/
theorem mem_edgeSet_starGraph {G : SimpleGraph V} {R B : Set V} {u v : V} :
    s(u, v) ∈ (starGraph G R B).edgeSet ↔ G.Adj u v ∧ u ∈ R ∧ v ∈ R ∧ ¬(u ∈ B ∧ v ∈ B) :=
  Iff.rfl

/-! ## Open clusters with constrained steps -/

/-- The open cluster of `x` **using only steps of `K`**: the vertices joined to `x` by an open
path all of whose edges are edges of the step graph `K` — by definition the ordinary open
cluster of `x` in the restricted configuration `ω ∩ E(K)`. With `K = withinGraph G R` and
`x ∈ R` this is Grimmett's `{y : x ↔ y in R}` (for `x ∉ R` it is `{x}`), with
`K = starGraph G R ∂R` it is `{y : x ↔ y in R*}`.
[cite: GrimmettPercolation1999, §7.3 p. 164 (in V*)] -/
def openClusterIn (K : SimpleGraph V) (ω : BondConfig V) (x : V) : Set V :=
  openCluster (ω ∩ K.edgeSet) x

/-- **Restricting the configuration to `E(K)` restricts the open graph to `K`.** [folklore] -/
theorem openGraph_inter_edgeSet (K : SimpleGraph V) (ω : BondConfig V) :
    openGraph (ω ∩ K.edgeSet) = openGraph ω ⊓ K := by
  ext u v
  simp only [openGraph_adj, Set.mem_inter_iff, SimpleGraph.mem_edgeSet, SimpleGraph.inf_adj]
  constructor
  · rintro ⟨⟨hω, hK⟩, hne⟩
    exact ⟨⟨hω, hne⟩, hK⟩
  · rintro ⟨⟨hω, hne⟩, hK⟩
    exact ⟨⟨hω, hK⟩, hne⟩

/-- Membership in the constrained cluster is reachability in `openGraph ω ⊓ K`. [folklore] -/
theorem mem_openClusterIn_iff {K : SimpleGraph V} {ω : BondConfig V} {x y : V} :
    y ∈ openClusterIn K ω x ↔ (openGraph ω ⊓ K).Reachable x y := by
  rw [openClusterIn, ← openGraph_inter_edgeSet]
  rfl

/-- `x` lies in its own constrained cluster. [folklore] -/
@[simp] theorem self_mem_openClusterIn (K : SimpleGraph V) (ω : BondConfig V) (x : V) :
    x ∈ openClusterIn K ω x :=
  mem_openCluster_self _ x

/-- Constrained clusters grow with the step graph. [folklore] -/
theorem openClusterIn_mono_graph {K K' : SimpleGraph V} (h : K ≤ K') (ω : BondConfig V) (x : V) :
    openClusterIn K ω x ⊆ openClusterIn K' ω x := by
  intro y hy
  rw [mem_openClusterIn_iff] at hy ⊢
  exact hy.mono (inf_le_inf_left _ h)

/-- Constrained clusters grow with the configuration. [folklore] -/
theorem openClusterIn_mono_config (K : SimpleGraph V) {ω ω' : BondConfig V} (h : ω ⊆ ω') (x : V) :
    openClusterIn K ω x ⊆ openClusterIn K ω' x :=
  openCluster_mono (Set.inter_subset_inter_left _ h) x

/-- Constrained clusters are ordinary open clusters of a smaller configuration, hence contained
in the ordinary open cluster. [folklore] -/
theorem openClusterIn_subset_openCluster (K : SimpleGraph V) (ω : BondConfig V) (x : V) :
    openClusterIn K ω x ⊆ openCluster ω x :=
  openCluster_mono Set.inter_subset_left x

/-- The constrained cluster only depends on the edges of `K`: `ω` and `ω ∩ E(K)` have the same
constrained clusters. [folklore] -/
theorem openClusterIn_inter_edgeSet (K : SimpleGraph V) (ω : BondConfig V) (x : V) :
    openClusterIn K (ω ∩ K.edgeSet) x = openClusterIn K ω x := by
  rw [openClusterIn, openClusterIn, Set.inter_assoc, Set.inter_self]

/-- Symmetry / transitivity: a vertex of the constrained cluster of `x` has the same constrained
cluster. [folklore] -/
theorem openClusterIn_eq_of_mem {K : SimpleGraph V} {ω : BondConfig V} {x y : V}
    (hy : y ∈ openClusterIn K ω x) : openClusterIn K ω y = openClusterIn K ω x := by
  ext z
  rw [mem_openClusterIn_iff] at hy
  rw [mem_openClusterIn_iff, mem_openClusterIn_iff]
  exact ⟨fun hz => hy.trans hz, fun hz => hy.symm.trans hz⟩

/-- An extension of an open constrained path by one open step of `K`. [folklore] -/
theorem mem_openClusterIn_of_adj {K : SimpleGraph V} {ω : BondConfig V} {x y z : V}
    (hy : y ∈ openClusterIn K ω x) (hK : K.Adj y z) (hω : s(y, z) ∈ ω) :
    z ∈ openClusterIn K ω x := by
  rw [mem_openClusterIn_iff] at hy ⊢
  refine hy.trans (SimpleGraph.Adj.reachable ?_)
  rw [SimpleGraph.inf_adj, openGraph_adj]
  exact ⟨⟨hω, hK.ne⟩, hK⟩

/-- A vertex of the constrained cluster other than `x` itself is entered by a step of `K`; in
particular the cluster of `x` for `withinGraph G R` stays inside `R` (if `x ∈ R`). [folklore] -/
theorem openClusterIn_withinGraph_subset {G : SimpleGraph V} {R : Set V} {x : V} (hx : x ∈ R)
    (ω : BondConfig V) : openClusterIn (withinGraph G R) ω x ⊆ R := by
  intro y hy
  rw [mem_openClusterIn_iff] at hy
  obtain ⟨p⟩ := hy
  induction p with
  | nil => exact hx
  | cons h _ ih => exact ih h.2.2.2

/-- Likewise for `starGraph G R B`: the constrained cluster stays inside `R`. [folklore] -/
theorem openClusterIn_starGraph_subset {G : SimpleGraph V} {R B : Set V} {x : V} (hx : x ∈ R)
    (ω : BondConfig V) : openClusterIn (starGraph G R B) ω x ⊆ R :=
  (openClusterIn_mono_graph (starGraph_le_withinGraph G R B) ω x).trans
    (openClusterIn_withinGraph_subset hx ω)

/-! ## The events `{x ↔ y via K}` and `{x ↔ ∞ via K}` -/

/-- The event `{x ↔ y via K}`: `y` lies in the `K`-constrained open cluster of `x`
(Grimmett's `{x ↔ y in R}`, `{x ↔ y in R*}`). This generalises this library's `openConnIn S x y`
(`Literature/Basic.lean`): `openConnIn S x y = openConnVia (withinGraph ⊤ S) x y` for `x ∈ S`
(`openConnIn_eq_openConnVia` below); the `K`-parametrised form is needed for the starred regions
and carries `DeterminedBy E(K)`. [cite: GrimmettPercolation1999, §7.3 p. 164 (in V*)] -/
def openConnVia (K : SimpleGraph V) (x y : V) : Set (BondConfig V) :=
  {ω | y ∈ openClusterIn K ω x}

/-- The event `{x ↔ ∞ via K}`: the `K`-constrained open cluster of `x` is infinite
(Grimmett's `{x ↔ ∞ in R}`, `{x ↔ ∞ in R*}`, p. 165, stated there with an infinite open path;
we use the `|C| = ∞` convention of this library's `percolatesAt` (§1.4), which agrees with the path
form on locally finite step graphs such as those of `ℤ³`). [cite: GrimmettPercolation1999, §7.3 p. 165 (x ↔ ∞ in V*)] -/
def percolatesVia (K : SimpleGraph V) (x : V) : Set (BondConfig V) :=
  {ω | (openClusterIn K ω x).Infinite}

/-- `{x ↔ ∞ via K}` is the preimage of `{|C(x)| = ∞}` under restriction to `E(K)`. [folklore] -/
theorem percolatesVia_eq_preimage (K : SimpleGraph V) (x : V) :
    percolatesVia K x = (fun ω : BondConfig V => ω ∩ K.edgeSet) ⁻¹' percolatesAt x := rfl

/-- Restriction of a configuration to a fixed set of edges is measurable. [folklore] -/
theorem measurable_inter_const (E : Set (Sym2 V)) :
    Measurable fun ω : BondConfig V => ω ∩ E :=
  measurable_set_iff.2 fun e => (measurable_set_mem e).and measurable_const

/-- `{x ↔ y via K}` is measurable (`V` countable). [cite: GrimmettPercolation1999, §1.3 p. 10] -/
theorem measurableSet_openConnVia [Countable V] (K : SimpleGraph V) (x y : V) :
    MeasurableSet (openConnVia K x y) :=
  measurableSet_openConn_holds x y |>.preimage (measurable_inter_const _)

/-- `{x ↔ ∞ via K}` is measurable (`V` countable). [cite: GrimmettPercolation1999, §1.4 (1.9)] -/
theorem measurableSet_percolatesVia [Countable V] (K : SimpleGraph V) (x : V) :
    MeasurableSet (percolatesVia K x) :=
  measurableSet_percolatesAt_holds x |>.preimage (measurable_inter_const _)

/-- A preimage under restriction to `E` is determined by the edges in `E`. [folklore] -/
theorem determinedBy_preimage_inter (E : Set (Sym2 V)) (A : Set (BondConfig V)) :
    DeterminedBy ((fun ω : BondConfig V => ω ∩ E) ⁻¹' A) E := by
  rw [determinedBy_iff]
  intro ω ω' h
  simp only [Set.mem_preimage, h]

/-- **`{x ↔ ∞ via K}` is determined by the states of the edges of `K`** (so that events about
disjoint regions are independent, `FiniteEnergy.lean`). [folklore] -/
theorem determinedBy_percolatesVia (K : SimpleGraph V) (x : V) :
    DeterminedBy (percolatesVia K x) K.edgeSet := by
  rw [percolatesVia_eq_preimage]
  exact determinedBy_preimage_inter _ _

/-- `{x ↔ ∞ via K}` grows with `K`. [folklore] -/
theorem percolatesVia_mono_graph {K K' : SimpleGraph V} (h : K ≤ K') (x : V) :
    percolatesVia K x ⊆ percolatesVia K' x :=
  fun ω hω => hω.mono (openClusterIn_mono_graph h ω x)

/-- Vertices of one constrained cluster percolate together. [folklore] -/
theorem mem_percolatesVia_iff_of_mem {K : SimpleGraph V} {ω : BondConfig V} {x y : V}
    (hy : y ∈ openClusterIn K ω x) : ω ∈ percolatesVia K y ↔ ω ∈ percolatesVia K x := by
  simp only [percolatesVia, Set.mem_setOf_eq, openClusterIn_eq_of_mem hy]

/-- If `x ↔ y via K` by one open step and `y ↔ ∞ via K'` with `K' ≤ K`, then `x ↔ ∞ via K`
(path concatenation; e.g. Grimmett 1999, p. 165: the edge `⟨0, (0,0,1)⟩` followed by an infinite
path of `ℍ + (0,0,1)` gives `0 ↔ ∞ in ℍ*`). [cite: GrimmettPercolation1999, §7.3 p. 165] -/
theorem mem_percolatesVia_of_adj {K K' : SimpleGraph V} (hK : K' ≤ K) {ω : BondConfig V} {x y : V}
    (hxy : K.Adj x y) (hω : s(x, y) ∈ ω) (hy : ω ∈ percolatesVia K' y) : ω ∈ percolatesVia K x := by
  have hy' : ω ∈ percolatesVia K y := percolatesVia_mono_graph hK y hy
  have hmem : y ∈ openClusterIn K ω x := mem_openClusterIn_of_adj (self_mem_openClusterIn K ω x) hxy hω
  exact (mem_percolatesVia_iff_of_mem hmem).1 hy'

/-! ## Equivariance under relabelling of the vertices -/

section Relabel

variable {V' : Type*}

/-- **Relabelling vertices carries constrained clusters to constrained clusters**: if the
bijection `e` carries the step graph `K` onto `K'`, then the `K'`-cluster of `e x` in the
relabelled configuration is the image of the `K`-cluster of `x`. (Translation and reflection
invariance of the constructions of Grimmett 1999, §7.3.) [folklore] -/
theorem openClusterIn_relabel (e : V ≃ V') {K : SimpleGraph V} {K' : SimpleGraph V'}
    (hK : ∀ u v, K'.Adj (e u) (e v) ↔ K.Adj u v) (ω : BondConfig V) (x : V) :
    openClusterIn K' (BondConfig.relabel (sym2Equiv e) ω) (e x) = e '' openClusterIn K ω x := by
  -- `e` is an isomorphism between the two constrained open graphs
  let φ : (openGraph ω ⊓ K) ≃g (openGraph (BondConfig.relabel (sym2Equiv e) ω) ⊓ K') :=
    { toEquiv := e
      map_rel_iff' := fun {u v} => by
        simp only [SimpleGraph.inf_adj]
        rw [openGraph_relabel_adj_iff e ω u v, hK u v] }
  ext y'
  simp only [Set.mem_image, mem_openClusterIn_iff]
  constructor
  · intro h
    refine ⟨e.symm y', ?_, e.apply_symm_apply y'⟩
    refine (SimpleGraph.Iso.reachable_iff (φ := φ)).1 ?_
    change (openGraph (BondConfig.relabel (sym2Equiv e) ω) ⊓ K').Reachable (e x) (e (e.symm y'))
    rwa [e.apply_symm_apply]
  · rintro ⟨y, hy, rfl⟩
    exact (SimpleGraph.Iso.reachable_iff (φ := φ)).2 hy

/-- Relabelled configurations percolate via `K'` at `e x` iff the original percolates via `K`
at `x`. [folklore] -/
theorem relabel_mem_percolatesVia_iff (e : V ≃ V') {K : SimpleGraph V} {K' : SimpleGraph V'}
    (hK : ∀ u v, K'.Adj (e u) (e v) ↔ K.Adj u v) (ω : BondConfig V) (x : V) :
    BondConfig.relabel (sym2Equiv e) ω ∈ percolatesVia K' (e x) ↔ ω ∈ percolatesVia K x := by
  simp only [percolatesVia, Set.mem_setOf_eq, openClusterIn_relabel e hK ω x]
  exact Set.infinite_image_iff e.injective.injOn

/-- Preimage form: `(relabel e)⁻¹' {e x ↔ ∞ via K'} = {x ↔ ∞ via K}`. [folklore] -/
theorem relabel_preimage_percolatesVia (e : V ≃ V') {K : SimpleGraph V} {K' : SimpleGraph V'}
    (hK : ∀ u v, K'.Adj (e u) (e v) ↔ K.Adj u v) (x : V) :
    BondConfig.relabel (sym2Equiv e) ⁻¹' percolatesVia K' (e x) = percolatesVia K x := by
  ext ω
  exact relabel_mem_percolatesVia_iff e hK ω x

end Relabel

/-! ## Bridge to percolation on the induced subgraph -/

section Induce

open ProbabilityTheory

variable (G : SimpleGraph V) (R : Set V)

/-- An open path in `R` (steps of `openGraph ω ⊓ withinGraph G R`) between vertices of `R` lifts
to an open path of the induced graph on `R` in the restricted configuration
`restrictConfig Subtype.val ω`. [folklore] -/
theorem reachable_restrictConfig_of_reachable_within {ω : BondConfig V} {x y : V} (hx : x ∈ R)
    (hy : y ∈ R) (h : (openGraph ω ⊓ withinGraph G R).Reachable x y) :
    (openGraph (restrictConfig (Subtype.val : R → V) ω)).Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => rfl
  | @cons u v z huv w ih =>
    have hv : v ∈ R := huv.2.2.2
    have h1 : (openGraph (restrictConfig (Subtype.val : R → V) ω)).Adj ⟨u, hx⟩ ⟨v, hv⟩ := by
      rw [openGraph_adj, mem_restrictConfig, Sym2.map_mk]
      exact ⟨huv.1.1, fun heq => huv.1.2 (congrArg Subtype.val heq)⟩
    exact h1.reachable.trans (ih hv hy)

/-- Conversely, if `ω` only opens edges of `G`, an open path of the induced graph on `R` in the
restricted configuration is an open path in `R`. [folklore] -/
theorem reachable_within_of_reachable_restrictConfig {ω : BondConfig V} (hω : ω ⊆ G.edgeSet)
    {a b : R} (h : (openGraph (restrictConfig (Subtype.val : R → V) ω)).Reachable a b) :
    (openGraph ω ⊓ withinGraph G R).Reachable a.1 b.1 := by
  let φ : openGraph (restrictConfig (Subtype.val : R → V) ω) →g (openGraph ω ⊓ withinGraph G R) :=
    { toFun := Subtype.val
      map_rel' := fun {a b} hab => by
        rw [openGraph_adj, mem_restrictConfig, Sym2.map_mk] at hab
        rw [SimpleGraph.inf_adj, openGraph_adj, withinGraph_adj]
        exact ⟨⟨hab.1, fun heq => hab.2 (Subtype.ext heq)⟩, (SimpleGraph.mem_edgeSet G).1 (hω hab.1),
          a.2, b.2⟩ }
  exact h.map φ

/-- For configurations opening only edges of `G`, the open cluster of `x ∈ R` in the induced graph
(restricted configuration) is, as a subset of `V`, the constrained cluster
`openClusterIn (withinGraph G R) ω x`. [folklore] -/
theorem image_openCluster_restrictConfig {ω : BondConfig V} (hω : ω ⊆ G.edgeSet) {x : V}
    (hx : x ∈ R) :
    Subtype.val '' openCluster (restrictConfig (Subtype.val : R → V) ω) ⟨x, hx⟩ =
      openClusterIn (withinGraph G R) ω x := by
  ext y
  simp only [Set.mem_image, openCluster, Set.mem_setOf_eq, mem_openClusterIn_iff]
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact reachable_within_of_reachable_restrictConfig G R hω hb
  · intro hy
    have hyR : y ∈ R := openClusterIn_withinGraph_subset hx ω (mem_openClusterIn_iff.2 hy)
    exact ⟨⟨y, hyR⟩, reachable_restrictConfig_of_reachable_within G R hx hyR hy, rfl⟩

/-- The induced open graph on `R` is the open graph of the restricted configuration.
[folklore] -/
theorem induce_openGraph_eq (R : Set V) (ω : BondConfig V) :
    (openGraph ω).induce R = openGraph (restrictConfig (Subtype.val : R → V) ω) := by
  ext a b
  simp only [SimpleGraph.comap_adj, Function.Embedding.coe_subtype, openGraph_adj,
    mem_restrictConfig, Sym2.map_mk, ne_eq]
  rw [Subtype.ext_iff]

/-- An open path of the induced graph on `R` is an open path "in `R`" of the ambient vertex type
(no hypothesis on `ω`: the complete step graph `⊤` accepts every open pair). [folklore] -/
theorem reachable_within_top_of_reachable_induce {ω : BondConfig V} {a b : R}
    (h : ((openGraph ω).induce R).Reachable a b) :
    (openGraph ω ⊓ withinGraph ⊤ R).Reachable a.1 b.1 := by
  let φ : (openGraph ω).induce R →g (openGraph ω ⊓ withinGraph ⊤ R) :=
    { toFun := Subtype.val
      map_rel' := fun {a b} hab => by
        rw [SimpleGraph.comap_adj, Function.Embedding.coe_subtype, openGraph_adj] at hab
        rw [SimpleGraph.inf_adj, openGraph_adj, withinGraph_adj, SimpleGraph.top_adj]
        exact ⟨hab, hab.2, a.2, b.2⟩ }
  exact h.map φ

/-- **Bridge to this library's `openConnIn`** (`Literature/Basic.lean`: `{x ↔ y in S}` via the induced
open graph on the subtype `S`): for `x ∈ S`, `openConnIn S x y = openConnVia (withinGraph ⊤ S) x y`
— "joined by an open path using only vertices of `S`" is "joined via steps of the complete graph
inside `S`". (For `x ∉ S` the left side is empty while the right side contains every `ω` when
`y = x`.) [folklore] -/
theorem openConnIn_eq_openConnVia {S : Set V} {x : V} (hx : x ∈ S) (y : V) :
    openConnIn S x y = openConnVia (withinGraph ⊤ S) x y := by
  ext ω
  constructor
  · rintro ⟨hx', hy, h⟩
    exact mem_openClusterIn_iff.2 (reachable_within_top_of_reachable_induce S h)
  · intro h
    have hy : y ∈ S := openClusterIn_withinGraph_subset hx ω h
    refine ⟨hx, hy, ?_⟩
    rw [induce_openGraph_eq]
    exact reachable_restrictConfig_of_reachable_within ⊤ S hx hy (mem_openClusterIn_iff.1 h)

/-- **`θ` of an induced subgraph is the probability of percolating "in `R`"**:
`θ_{G[R]}(x, p) = P_p^G(x ↔ ∞ in R)` for `x ∈ R` (Grimmett 1999, §7.2 p. 148: `θ(p, A)` for "bond
percolation on the subgraph of `ℤ^d` induced by `A`"; §7.3 pp. 164–165: `x ↔ ∞ in V`). This
identifies this library's convention for `θ_ℍ`, `θ_{S_k}` (`HalfSpace.lean`, `theta` of the induced
graph) with events on the ambient configuration space. [cite: GrimmettPercolation1999, §7.2 p. 148 (θ(p, A))] -/
theorem theta_induce_eq_real_percolatesVia [Countable V] (x : V) (hx : x ∈ R) (p : unitInterval) :
    theta (G.induce R) ⟨x, hx⟩ p =
      (bondPercolation G p).real (percolatesVia (withinGraph G R) x) := by
  have h1 : theta (G.induce R) ⟨x, hx⟩ p = (bondPercolation G p).real
      (restrictConfig (Subtype.val : R → V) ⁻¹' percolatesAt (⟨x, hx⟩ : R)) :=
    theta_comap_eq G Subtype.val_injective ⟨x, hx⟩ p
  rw [h1, measureReal_def, measureReal_def]
  congr 1
  refine measure_congr ?_
  -- almost every configuration opens only edges of `G` (`setBernoulli_ae_subset`; this is
  -- `ae_subset_edgeSet` of `RSW.lean`, not imported here)
  have hae : ∀ᵐ ω ∂bondPercolation G p, ω ⊆ G.edgeSet := setBernoulli_ae_subset
  filter_upwards [hae] with ω hω
  refine propext ?_
  change ω ∈ restrictConfig (Subtype.val : R → V) ⁻¹' percolatesAt (⟨x, hx⟩ : R) ↔
    ω ∈ percolatesVia (withinGraph G R) x
  simp only [Set.mem_preimage, percolatesAt, percolatesVia, Set.mem_setOf_eq,
    ← image_openCluster_restrictConfig G R hω hx]
  exact (Set.infinite_image_iff Subtype.val_injective.injOn).symm

end Induce

end Percolation.Literature

end
