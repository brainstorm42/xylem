import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Sym
import Percolation.Literature.Crossings
import Percolation.Util.Linter

/-!
# Planar duality for rectangle crossings of `ℤ²`: discharge of `lrCrossing_xor_dualTBCrossing`

This file proves the planar duality lemma for bond
percolation on the square lattice stated as the named fact
`Percolation.Literature.lrCrossing_xor_dualTBCrossing` in `Crossings.lean`: for every lattice configuration
`ω ⊆ E(ℤ²)`, **exactly one** of "`[0, m] × [0, n]` has an open left-right crossing" and "the dual
rectangle `[½, m - ½] × [-½, n + ½]` has a dual-open top-bottom crossing" holds
(Bollobás–Riordan, *Percolation* (2006), Ch. 3, Lemma 1; Grimmett, *Percolation* (1999), §11.2;
Kesten, *Percolation theory for mathematicians* (1982), §2.2 and Prop. 2.2). In print this is
"obvious from a picture" and proved either through the Jordan curve theorem or, as in
Bollobás–Riordan, by an interface-following (exploration) argument. We give a self-contained
combinatorial proof on `ℤ²`, in two halves.

* **Not both** (a discrete Jordan-curve argument by winding numbers). For a lattice walk `P` and
  a lattice point `u` let `W(P, u)` be the signed number of vertical steps of `P` crossing the
  horizontal half-line from `u + (½, ½)` to the right (`walkWinding`). Moving `u` across an edge not
  used by `P` does not change `W` (`walkWinding_eq_walkWinding_right`, `walkWinding_eq_walkWinding_up`: a flow
  conservation identity), so `W(P, ·)` is constant along lattice walks avoiding `P`
  (`walkWinding_eq_of_walk`) and along walks of faces never separated by an edge of `P`
  (`walkWinding_eq_of_faceWalk`). For a left-right crossing `P` of a rectangle, extended beyond the
  right side and then downwards, `W = 0` at the top and `W = -1` below the bottom; hence every
  top-bottom crossing of the rectangle meets `P` (`exists_mem_support_of_crossing`, the lemma
  "a horizontal and a vertical crossing of a rectangle meet" used in every RSW gluing argument),
  and every top-bottom face walk of the dual rectangle is separated somewhere by an edge of `P`
  (`exists_dart_sepEdge_mem_edges`); since the dual edge joining two adjacent faces is exactly
  the dual of the primal edge separating them (`dualEdge_sepEdge`), an open `P` and a dual-open
  face walk cannot coexist.
* **At least one** (a parity/handshake argument replacing interface following). Colour a vertex
  of the rectangle when it is joined to the left side by an open path of the rectangle. If no
  right-side vertex is coloured, consider the graph on the faces of the dual rectangle in which
  two adjacent faces are joined when the primal edge between them lies in the rectangle and has
  endpoints of different colours (`bichromaticGraph`). Interior faces have even degree (a
  4-cycle has an even number of colour changes), a top face has odd degree iff the top-row edge
  below it is bichromatic, and the number of colour changes along the top row (coloured at the
  left end, uncoloured at the right end) is odd; by the handshake lemma
  (`SimpleGraph.even_card_odd_degree_vertices`) applied to the part of this graph reachable from
  the top faces, some bottom face is joined to a top face (`exists_topReach_dualBottomSide`).
  A bichromatic edge is closed, so its dual edge is dual-open (`mem_dualConfig_of_bichromatic`),
  and the face path is a dual-open top-bottom crossing.

Besides `lrCrossing_xor_dualTBCrossing_holds` the file provides the bridge between the event `{x ↔ y
in S}` and lattice walks (`exists_walk_of_mem_openConnIn`, `mem_openConnIn_of_walk`), the locality
(finite dependence) and measurability of crossing events of finite regions, and the discharge
`crossingProb_add_real_dualTBCrossing_holds` of `P_p(LR) + P_p(TB*) = 1`.

Mathlib anchors: `SimpleGraph.Walk` (`support`, `darts`, `edges`, `append`, `transfer`,
`Walk.induce`, `takeUntil`), `SimpleGraph.even_card_odd_degree_vertices`, `Finset.sym2`,
`MeasureTheory.measureReal_union_add_inter`. Mathlib has no planar duality for lattices and no
discrete Jordan curve theorem.

## References
* B. Bollobás, O. Riordan, *Percolation*, CUP (2006), Ch. 3, Lemma 1 [BollobasRiordanPercolation2006].
* G. Grimmett, *Percolation*, 2nd ed., Springer (1999), §11.2 [GrimmettPercolation1999].
* H. Kesten, *Percolation theory for mathematicians*, Birkhäuser (1982), §2.2 [KestenPTM1982].
-/

namespace Percolation.Literature

open SimpleGraph Finset MeasureTheory

noncomputable section

/-! ### Coordinates on `ℤ²` -/

/-- Points of `ℤ²` are equal iff both coordinates agree. [folklore] -/
theorem _root_.Percolation.Literature.LatticeModels.Site.eq_iff_two {x y : LatticeModels.Site 2} : x = y ↔ x 0 = y 0 ∧ x 1 = y 1 := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · intro h; funext i; fin_cases i
    · exact h.1
    · exact h.2

/-- Coordinates of `e₀`. [folklore] -/
@[simp] theorem single_zero_apply_zero : (Pi.single 0 1 : LatticeModels.Site 2) 0 = 1 := rfl
/-- Coordinates of `e₀`. [folklore] -/
@[simp] theorem single_zero_apply_one : (Pi.single 0 1 : LatticeModels.Site 2) 1 = 0 := rfl
/-- Coordinates of `e₁`. [folklore] -/
@[simp] theorem single_one_apply_zero : (Pi.single 1 1 : LatticeModels.Site 2) 0 = 0 := rfl
/-- Coordinates of `e₁`. [folklore] -/
@[simp] theorem single_one_apply_one : (Pi.single 1 1 : LatticeModels.Site 2) 1 = 1 := rfl

/-- The four kinds of unit steps `x → y` in `ℤ²`, in coordinates. [folklore] -/
inductive StepKind (x y : LatticeModels.Site 2) : Prop
  | right (h0 : y 0 = x 0 + 1) (h1 : y 1 = x 1) : StepKind x y
  | left (h0 : x 0 = y 0 + 1) (h1 : y 1 = x 1) : StepKind x y
  | up (h1 : y 1 = x 1 + 1) (h0 : y 0 = x 0) : StepKind x y
  | down (h1 : x 1 = y 1 + 1) (h0 : y 0 = x 0) : StepKind x y

/-- Adjacency in `ℤ²` in coordinates: the four unit steps. [folklore] -/
theorem stepKind_of_adj {x y : LatticeModels.Site 2} (h : (LatticeModels.zdGraph 2).Adj x y) : StepKind x y := by
  rw [LatticeModels.zdGraph_adj_iff, Fin.exists_fin_two] at h
  simp only [LatticeModels.Site.eq_iff_two, Pi.add_apply, single_zero_apply_zero, single_zero_apply_one,
    single_one_apply_zero, single_one_apply_one, add_zero] at h
  rcases h with (⟨h0, h1⟩ | ⟨h0, h1⟩) | (⟨h0, h1⟩ | ⟨h0, h1⟩)
  · exact .right h0 h1
  · exact .left h0 h1.symm
  · exact .up h1 h0
  · exact .down h1 h0.symm

/-- The four unit steps are adjacencies of `ℤ²`. [folklore] -/
theorem adj_of_stepKind {x y : LatticeModels.Site 2} (h : StepKind x y) : (LatticeModels.zdGraph 2).Adj x y := by
  rw [LatticeModels.zdGraph_adj_iff, Fin.exists_fin_two]
  simp only [LatticeModels.Site.eq_iff_two, Pi.add_apply, single_zero_apply_zero, single_zero_apply_one,
    single_one_apply_zero, single_one_apply_one, add_zero]
  rcases h with ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h1, h0⟩ | ⟨h1, h0⟩ <;> omega

/-- Adjacency in `ℤ²` in coordinates, as a disjunction. [folklore] -/
theorem zdGraph_two_adj_iff (x y : LatticeModels.Site 2) :
    (LatticeModels.zdGraph 2).Adj x y ↔
      (y 0 = x 0 + 1 ∧ y 1 = x 1) ∨ (x 0 = y 0 + 1 ∧ y 1 = x 1) ∨
      (y 1 = x 1 + 1 ∧ y 0 = x 0) ∨ (x 1 = y 1 + 1 ∧ y 0 = x 0) := by
  constructor
  · intro h
    rcases stepKind_of_adj h with ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h1, h0⟩ | ⟨h1, h0⟩
    · exact Or.inl ⟨h0, h1⟩
    · exact Or.inr (Or.inl ⟨h0, h1⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨h1, h0⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h1, h0⟩))
  · rintro (⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h1, h0⟩ | ⟨h1, h0⟩)
    · exact adj_of_stepKind (.right h0 h1)
    · exact adj_of_stepKind (.left h0 h1)
    · exact adj_of_stepKind (.up h1 h0)
    · exact adj_of_stepKind (.down h1 h0)

/-! ### Open paths as lattice walks -/

section Bridge

variable {V : Type*} {G : SimpleGraph V}

/-- The edges of the open graph are open: `E(openGraph ω) ⊆ ω`. [folklore] -/
theorem edgeSet_openGraph_subset (ω : BondConfig V) : (openGraph ω).edgeSet ⊆ ω := by
  intro e he
  rw [openGraph, SimpleGraph.edgeSet_fromEdgeSet] at he
  exact he.1

/-- A walk of `G` inside `S` all of whose edges are open witnesses `{x ↔ y in S}`.
(Grimmett 1999, §1.3, open paths.) [folklore] -/
theorem mem_openConnIn_of_walk {ω : BondConfig V} {S : Set V} {x y : V} (p : G.Walk x y)
    (hS : ∀ z ∈ p.support, z ∈ S) (hω : ∀ e ∈ p.edges, e ∈ ω) : ω ∈ openConnIn S x y := by
  have hp : ∀ e ∈ p.edges, e ∈ (openGraph ω).edgeSet := fun e he => by
    rw [openGraph, SimpleGraph.edgeSet_fromEdgeSet]
    exact ⟨hω e he, SimpleGraph.not_isDiag_of_mem_edgeSet _ (p.edges_subset_edgeSet he)⟩
  have hq : ∀ z ∈ (p.transfer (openGraph ω) hp).support, z ∈ S := by
    rw [Walk.support_transfer]; exact hS
  exact ⟨hS x p.start_mem_support, hS y p.end_mem_support,
    ⟨(p.transfer (openGraph ω) hp).induce S hq⟩⟩

/-- Conversely, for a lattice configuration `ω ⊆ E(G)`, the event `{x ↔ y in S}` is witnessed by
a walk of `G` inside `S` with open edges. (Grimmett 1999, §1.3.) [folklore] -/
theorem exists_walk_of_mem_openConnIn {ω : BondConfig V} (hω : ω ⊆ G.edgeSet) {S : Set V}
    {x y : V} (h : ω ∈ openConnIn S x y) :
    ∃ p : G.Walk x y, (∀ z ∈ p.support, z ∈ S) ∧ ∀ e ∈ p.edges, e ∈ ω := by
  obtain ⟨hx, hy, ⟨q⟩⟩ := h
  set P₁ : (openGraph ω).Walk x y :=
    (q.map (SimpleGraph.Embedding.induce S).toHom).copy rfl rfl with hP₁
  have hq' : ∀ e ∈ P₁.edges, e ∈ G.edgeSet :=
    fun e he => hω (edgeSet_openGraph_subset ω (Walk.edges_subset_edgeSet _ he))
  refine ⟨P₁.transfer G hq', ?_, ?_⟩
  · intro z hz
    rw [Walk.support_transfer, hP₁, Walk.support_copy, Walk.support_map] at hz
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hz
    exact w.2
  · intro e he
    rw [Walk.edges_transfer] at he
    exact edgeSet_openGraph_subset ω (Walk.edges_subset_edgeSet _ he)

/-- `{x ↔ y in S}` is symmetric in `x`, `y`. [folklore] -/
theorem openConnIn_comm (S : Set V) (x y : V) :
    (openConnIn S x y : Set (BondConfig V)) = openConnIn S y x := by
  ext ω
  constructor <;> rintro ⟨hx, hy, h⟩ <;> exact ⟨hy, hx, h.symm⟩

/-- `{x ↔ y in S}` is transitive. [folklore] -/
theorem PlanarDuality.openConnIn_trans {ω : BondConfig V} {S : Set V} {x y z : V} (hxy : ω ∈ openConnIn S x y)
    (hyz : ω ∈ openConnIn S y z) : ω ∈ openConnIn S x z := by
  obtain ⟨hx, _, h⟩ := hxy
  obtain ⟨_, hz, h'⟩ := hyz
  exact ⟨hx, hz, h.trans h'⟩

/-- `{x ↔ x in S}` holds iff `x ∈ S`. [folklore] -/
theorem openConnIn_refl {ω : BondConfig V} {S : Set V} {x : V} (hx : x ∈ S) :
    ω ∈ openConnIn S x x :=
  ⟨hx, hx, Reachable.refl _⟩

/-- An open edge inside `S` joins its endpoints in `S`. [folklore] -/
theorem openConnIn_of_adj {ω : BondConfig V} {S : Set V} {x y : V} (hx : x ∈ S) (hy : y ∈ S)
    (he : s(x, y) ∈ ω) (hne : x ≠ y) : ω ∈ openConnIn S x y := by
  refine ⟨hx, hy, Adj.reachable ?_⟩
  simp [openGraph_adj, he, hne]

/-- If `u` lies on an open walk inside `S` from `x`, then `{x ↔ u in S}`. [folklore] -/
theorem mem_openConnIn_of_mem_support [DecidableEq V] {ω : BondConfig V} {S : Set V} {x y u : V}
    (p : G.Walk x y) (hS : ∀ z ∈ p.support, z ∈ S) (hω : ∀ e ∈ p.edges, e ∈ ω)
    (hu : u ∈ p.support) : ω ∈ openConnIn S x u :=
  mem_openConnIn_of_walk (p.takeUntil u hu)
    (fun z hz => hS z (p.support_takeUntil_subset_support hu hz))
    (fun e he => hω e (p.edges_takeUntil_subset_edges hu he))

end Bridge

/-! ### Locality and measurability of crossing events -/

section Locality

variable {V : Type*}

/-- `{x ↔ y in S}` for a finite `S` depends only on the pairs of vertices of `S`.
(Grimmett 1999, §2.2, cylinder events.) [folklore] -/
theorem PlanarDuality.determinedBy_openConnIn (S : Finset V) (x y : V) :
    DeterminedBy (openConnIn (↑S : Set V) x y : Set (BondConfig V)) ↑S.sym2 := by
  rw [determinedBy_iff]
  intro ω ω' h
  have key : (openGraph ω).induce (↑S : Set V) = (openGraph ω').induce ↑S := by
    ext u v
    simp only [SimpleGraph.comap_adj, Function.Embedding.coe_subtype, openGraph_adj]
    have hmem : s(u.1, v.1) ∈ (↑S.sym2 : Set (Sym2 V)) :=
      Finset.mem_coe.2 (Finset.mem_sym2_iff.2 fun a ha => by
        rcases Sym2.mem_iff.1 ha with rfl | rfl
        · exact u.2
        · exact v.2)
    have hiff : s(u.1, v.1) ∈ ω ↔ s(u.1, v.1) ∈ ω' :=
      ⟨fun h1 => ((Set.ext_iff.1 h _).1 ⟨h1, hmem⟩).1, fun h1 => ((Set.ext_iff.1 h _).2 ⟨h1, hmem⟩).1⟩
    rw [hiff]
  simp only [openConnIn, Set.mem_setOf_eq, key]

/-- Open crossing events of a finite region `S` depend only on the pairs of vertices of `S`.
(Grimmett 1999, §2.2.) [folklore] -/
theorem PlanarDuality.determinedBy_openCrossing (S : Finset V) (A B : Set V) :
    DeterminedBy (openCrossing (↑S : Set V) A B : Set (BondConfig V)) ↑S.sym2 := by
  rw [determinedBy_iff]
  intro ω ω' h
  simp only [mem_openCrossing_iff]
  refine exists_congr fun x => and_congr_right fun _ => exists_congr fun y =>
    and_congr_right fun _ => ?_
  exact (determinedBy_iff _ _).1 (PlanarDuality.determinedBy_openConnIn S x y) ω ω' h

/-- Open crossing events of finite regions are local events. (Grimmett 1999, §2.2.) [folklore] -/
theorem isLocalEvent_openCrossing (S : Finset V) (A B : Set V) :
    IsLocalEvent (openCrossing (↑S : Set V) A B : Set (BondConfig V)) :=
  ⟨S.sym2, PlanarDuality.determinedBy_openCrossing S A B⟩

/-- Open crossing events of finite regions are measurable. (Grimmett 1999, §2.2.) [folklore] -/
theorem measurableSet_openCrossing (S : Finset V) (A B : Set V) :
    MeasurableSet (openCrossing (↑S : Set V) A B : Set (BondConfig V)) :=
  (PlanarDuality.determinedBy_openCrossing S A B).measurableSet_of_finset

end Locality

/-- Left-right crossing events of rectangles are local. (Grimmett 1999, §2.2.) [folklore] -/
theorem isLocalEvent_lrCrossing (m n : ℕ) : IsLocalEvent (lrCrossing m n) :=
  isLocalEvent_openCrossing _ _ _

/-- `dualConfig` is measurable. (Grimmett 1999, §11.2.) [folklore] -/
theorem measurable_dualConfig : Measurable dualConfig := by
  refine measurable_set_iff.2 fun e => ?_
  simp only [dualConfig_eq, Set.mem_setOf_eq]
  exact Measurable.and measurable_const (measurable_set_notMem _)

/-- Dual top-bottom crossing events are measurable. (Grimmett 1999, §11.2.) [folklore] -/
theorem measurableSet_dualTBCrossing (m n : ℕ) : MeasurableSet (dualTBCrossing m n) :=
  measurable_dualConfig (measurableSet_openCrossing _ _ _)

/-! ### The winding number of a lattice walk -/

/-- Indicator of the up-step `(t, u₁) → (t, u₁ + 1)` with `t ≥ u₀ + 1`. [folklore] -/
def upStep (u x y : LatticeModels.Site 2) : ℤ :=
  if y 0 = x 0 ∧ y 1 = x 1 + 1 ∧ x 1 = u 1 ∧ u 0 + 1 ≤ x 0 then 1 else 0

/-- Signed indicator of a vertical unit step `x → y` between heights `u₁` and `u₁ + 1` strictly
to the right of `u`: `+1` for the up-step `(t, u₁) → (t, u₁ + 1)`, `-1` for the down-step
`(t, u₁ + 1) → (t, u₁)`, when `t ≥ u₀ + 1`; `0` otherwise. [folklore] -/
def stepWinding (u x y : LatticeModels.Site 2) : ℤ := upStep u x y - upStep u y x

/-- Horizontal steps do not wind. [folklore] -/
theorem stepWinding_right {u x y : LatticeModels.Site 2} (h0 : y 0 = x 0 + 1) : stepWinding u x y = 0 := by
  unfold stepWinding upStep; split_ifs <;> omega

/-- Horizontal steps do not wind. [folklore] -/
theorem stepWinding_left {u x y : LatticeModels.Site 2} (h0 : x 0 = y 0 + 1) : stepWinding u x y = 0 := by
  unfold stepWinding upStep; split_ifs <;> omega

/-- Winding of an up-step. [folklore] -/
theorem stepWinding_up {u x y : LatticeModels.Site 2} (h1 : y 1 = x 1 + 1) (h0 : y 0 = x 0) :
    stepWinding u x y = if x 1 = u 1 ∧ u 0 + 1 ≤ x 0 then 1 else 0 := by
  unfold stepWinding upStep; split_ifs <;> omega

/-- Winding of a down-step. [folklore] -/
theorem stepWinding_down {u x y : LatticeModels.Site 2} (h1 : x 1 = y 1 + 1) (h0 : y 0 = x 0) :
    stepWinding u x y = -(if y 1 = u 1 ∧ u 0 + 1 ≤ y 0 then 1 else 0) := by
  unfold stepWinding upStep; split_ifs <;> omega

/-- The winding number of the walk `p` around the point `u + (½, ½)`: the signed number of
vertical steps of `p` crossing the horizontal half-line from `u + (½, ½)` to the right
(a lattice version of the winding number of a closed curve; for walks that are not closed it
is the quantity whose jumps encode crossings, Kesten 1982, §2.2). [folklore] -/
def walkWinding {G : SimpleGraph (LatticeModels.Site 2)} {a b : LatticeModels.Site 2} (p : G.Walk a b) (u : LatticeModels.Site 2) : ℤ :=
  (p.darts.map fun d => stepWinding u d.fst d.snd).sum

section WindingBasic

variable {G : SimpleGraph (LatticeModels.Site 2)}

/-- Winding of the trivial walk. [folklore] -/
@[simp] theorem walkWinding_nil (a u : LatticeModels.Site 2) : walkWinding (Walk.nil : G.Walk a a) u = 0 := rfl

/-- Winding of a walk with a first step. [folklore] -/
@[simp] theorem walkWinding_cons {a b c : LatticeModels.Site 2} (h : G.Adj a b) (p : G.Walk b c) (u : LatticeModels.Site 2) :
    walkWinding (Walk.cons h p) u = stepWinding u a b + walkWinding p u := by
  simp [walkWinding]

/-- Winding is additive under concatenation. [folklore] -/
@[simp] theorem walkWinding_append {a b c : LatticeModels.Site 2} (p : G.Walk a b) (q : G.Walk b c) (u : LatticeModels.Site 2) :
    walkWinding (p.append q) u = walkWinding p u + walkWinding q u := by
  simp [walkWinding, Walk.darts_append]

end WindingBasic

/-! ### Flows through a set of vertices -/

section Flow

variable {V : Type*} {G : SimpleGraph V}

/-- Signed indicator that the step `x → y` leaves the set `S`. [folklore] -/
def flowOut (S : Set V) [DecidablePred (· ∈ S)] (x y : V) : ℤ :=
  (if x ∈ S ∧ y ∉ S then 1 else 0) - (if x ∉ S ∧ y ∈ S then 1 else 0)

/-- Conservation of flow: along any walk from `a` to `b`, the number of exits from `S` minus the
number of entries into `S` is `[a ∈ S] - [b ∈ S]`. [folklore] -/
theorem sum_flowOut (S : Set V) [DecidablePred (· ∈ S)] {a b : V} (p : G.Walk a b) :
    (p.darts.map fun d => flowOut S d.fst d.snd).sum =
      (if a ∈ S then 1 else 0) - (if b ∈ S then 1 else 0) := by
  induction p with
  | nil => simp
  | cons h p ih =>
    simp only [Walk.darts_cons, List.map_cons, List.sum_cons, ih]
    unfold flowOut
    split_ifs <;> simp_all

end Flow

/-! ### How the winding number changes across an edge -/

/-- Signed indicator that the step `x → y` traverses the vertical edge `{u + e₀, u + e₀ + e₁}`
(the right side of the unit face with lower-left corner `u`) upwards. [folklore] -/
def vCross (u x y : LatticeModels.Site 2) : ℤ :=
  (if x 0 = u 0 + 1 ∧ x 1 = u 1 ∧ y 0 = u 0 + 1 ∧ y 1 = u 1 + 1 then 1 else 0) -
  (if y 0 = u 0 + 1 ∧ y 1 = u 1 ∧ x 0 = u 0 + 1 ∧ x 1 = u 1 + 1 then 1 else 0)

/-- Signed indicator that the step `x → y` traverses the horizontal edge `{u + e₁, u + e₀ + e₁}`
(the top side of the unit face with lower-left corner `u`) rightwards. [folklore] -/
def hCross (u x y : LatticeModels.Site 2) : ℤ :=
  (if x 0 = u 0 ∧ x 1 = u 1 + 1 ∧ y 0 = u 0 + 1 ∧ y 1 = u 1 + 1 then 1 else 0) -
  (if y 0 = u 0 ∧ y 1 = u 1 + 1 ∧ x 0 = u 0 + 1 ∧ x 1 = u 1 + 1 then 1 else 0)

/-- The half-line `{(t, u₁ + 1) | t ≥ u₀ + 1}` to the right of `u + e₁`. [folklore] -/
def rayAbove (u : LatticeModels.Site 2) : Set (LatticeModels.Site 2) := {z | z 1 = u 1 + 1 ∧ u 0 + 1 ≤ z 0}

/-- Membership in `rayAbove u` is decidable. [folklore] -/
instance (u : LatticeModels.Site 2) : DecidablePred (· ∈ rayAbove u) := fun z => by
  unfold rayAbove; infer_instance

/-- Membership in `rayAbove`. [folklore] -/
@[simp] theorem mem_rayAbove {u z : LatticeModels.Site 2} : z ∈ rayAbove u ↔ z 1 = u 1 + 1 ∧ u 0 + 1 ≤ z 0 :=
  Iff.rfl

/-- Moving the base point one step to the right changes the step winding of a lattice step by
the traversal of the vertical edge in between. [folklore] -/
theorem stepWinding_sub_stepWinding_right {u x y : LatticeModels.Site 2} (hxy : StepKind x y) :
    stepWinding u x y - stepWinding (u + Pi.single 0 1) x y = vCross u x y := by
  rcases hxy with ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h1, h0⟩ | ⟨h1, h0⟩
  · rw [stepWinding_right h0, stepWinding_right h0]
    unfold vCross; split_ifs <;> omega
  · rw [stepWinding_left h0, stepWinding_left h0]
    unfold vCross; split_ifs <;> omega
  · rw [stepWinding_up h1 h0, stepWinding_up h1 h0]
    unfold vCross
    simp only [Pi.add_apply, single_zero_apply_zero, single_zero_apply_one, add_zero]
    split_ifs <;> omega
  · rw [stepWinding_down h1 h0, stepWinding_down h1 h0]
    unfold vCross
    simp only [Pi.add_apply, single_zero_apply_zero, single_zero_apply_one, add_zero]
    split_ifs <;> omega

/-- Moving the base point one step up changes the step winding of a lattice step by the flow
through the half-line `rayAbove u` and the traversal of the horizontal edge in between. [folklore] -/
theorem stepWinding_sub_stepWinding_up {u x y : LatticeModels.Site 2} (hxy : StepKind x y) :
    stepWinding u x y - stepWinding (u + Pi.single 1 1) x y =
      -flowOut (rayAbove u) x y - hCross u x y := by
  rcases hxy with ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h1, h0⟩ | ⟨h1, h0⟩
  · rw [stepWinding_right h0, stepWinding_right h0]
    unfold hCross flowOut
    simp only [mem_rayAbove]
    split_ifs <;> omega
  · rw [stepWinding_left h0, stepWinding_left h0]
    unfold hCross flowOut
    simp only [mem_rayAbove]
    split_ifs <;> omega
  · rw [stepWinding_up h1 h0, stepWinding_up h1 h0]
    unfold hCross flowOut
    simp only [Pi.add_apply, single_one_apply_zero, single_one_apply_one, add_zero, mem_rayAbove]
    split_ifs <;> omega
  · rw [stepWinding_down h1 h0, stepWinding_down h1 h0]
    unfold hCross flowOut
    simp only [Pi.add_apply, single_one_apply_zero, single_one_apply_one, add_zero, mem_rayAbove]
    split_ifs <;> omega

section Lattice

variable {a b : LatticeModels.Site 2}

/-- `vCross u` vanishes on steps other than the vertical edge `{u + e₀, u + e₀ + e₁}`. [folklore] -/
theorem vCross_eq_zero_of_ne {u x y : LatticeModels.Site 2}
    (h : s(x, y) ≠ s(u + Pi.single 0 1, u + Pi.single 0 1 + Pi.single 1 1)) : vCross u x y = 0 := by
  unfold vCross
  have key : ¬(x 0 = u 0 + 1 ∧ x 1 = u 1 ∧ y 0 = u 0 + 1 ∧ y 1 = u 1 + 1) ∧
      ¬(y 0 = u 0 + 1 ∧ y 1 = u 1 ∧ x 0 = u 0 + 1 ∧ x 1 = u 1 + 1) := by
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      apply h
      congr 1 <;> simp [LatticeModels.Site.eq_iff_two, h1, h2, h3, h4]
    · rintro ⟨h1, h2, h3, h4⟩
      apply h
      rw [Sym2.eq_swap]
      congr 1 <;> simp [LatticeModels.Site.eq_iff_two, h1, h2, h3, h4]
  simp [key.1, key.2]

/-- `hCross u` vanishes on steps other than the horizontal edge `{u + e₁, u + e₁ + e₀}`. [folklore] -/
theorem hCross_eq_zero_of_ne {u x y : LatticeModels.Site 2}
    (h : s(x, y) ≠ s(u + Pi.single 1 1, u + Pi.single 1 1 + Pi.single 0 1)) : hCross u x y = 0 := by
  unfold hCross
  have key : ¬(x 0 = u 0 ∧ x 1 = u 1 + 1 ∧ y 0 = u 0 + 1 ∧ y 1 = u 1 + 1) ∧
      ¬(y 0 = u 0 ∧ y 1 = u 1 + 1 ∧ x 0 = u 0 + 1 ∧ x 1 = u 1 + 1) := by
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      apply h
      congr 1 <;> simp [LatticeModels.Site.eq_iff_two, h1, h2, h3, h4]
    · rintro ⟨h1, h2, h3, h4⟩
      apply h
      rw [Sym2.eq_swap]
      congr 1 <;> simp [LatticeModels.Site.eq_iff_two, h1, h2, h3, h4]
  simp [key.1, key.2]

/-- Across the vertical edge `{u + e₀, u + e₀ + e₁}`: the winding numbers of a lattice walk at `u`
and at `u + e₀` differ by the signed number of traversals of that edge. [folklore] -/
theorem walkWinding_sub_walkWinding_right (p : (LatticeModels.zdGraph 2).Walk a b) (u : LatticeModels.Site 2) :
    walkWinding p u - walkWinding p (u + Pi.single 0 1) =
      (p.darts.map fun d => vCross u d.fst d.snd).sum := by
  induction p with
  | nil => simp
  | cons h p ih =>
    simp only [walkWinding_cons, Walk.darts_cons, List.map_cons, List.sum_cons, ← ih,
      ← stepWinding_sub_stepWinding_right (stepKind_of_adj h)]
    ring

/-- Across the horizontal edge `{u + e₁, u + e₀ + e₁}`: the winding numbers of a lattice walk from
`a` to `b` at `u` and at `u + e₁` differ by the signed number of traversals of that edge and by
the boundary term `[a ∈ rayAbove u] - [b ∈ rayAbove u]` (flow conservation through the half-line
`rayAbove u`). [folklore] -/
theorem walkWinding_sub_walkWinding_up (p : (LatticeModels.zdGraph 2).Walk a b) (u : LatticeModels.Site 2) :
    walkWinding p u - walkWinding p (u + Pi.single 1 1) =
      -((if a ∈ rayAbove u then 1 else 0) - (if b ∈ rayAbove u then 1 else 0)) -
        (p.darts.map fun d => hCross u d.fst d.snd).sum := by
  rw [← sum_flowOut (rayAbove u) p]
  induction p with
  | nil => simp
  | cons h p ih =>
    simp only [walkWinding_cons, Walk.darts_cons, List.map_cons, List.sum_cons]
    have := stepWinding_sub_stepWinding_up (u := u) (stepKind_of_adj h)
    linarith

/-- If a lattice walk does not use the vertical edge `{u + e₀, u + e₀ + e₁}`, its winding numbers
at `u` and `u + e₀` agree. [folklore] -/
theorem walkWinding_eq_walkWinding_right {p : (LatticeModels.zdGraph 2).Walk a b} {u : LatticeModels.Site 2}
    (h : s(u + Pi.single 0 1, u + Pi.single 0 1 + Pi.single 1 1) ∉ p.edges) :
    walkWinding p u = walkWinding p (u + Pi.single 0 1) := by
  have hsum : (p.darts.map fun d => vCross u d.fst d.snd).sum = 0 := by
    refine List.sum_eq_zero fun t ht => ?_
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 ht
    refine vCross_eq_zero_of_ne fun heq => h ?_
    rw [← heq]
    exact List.mem_map.2 ⟨d, hd, rfl⟩
  have := walkWinding_sub_walkWinding_right p u
  rw [hsum] at this
  linarith

/-- If a lattice walk from `a` to `b` does not use the horizontal edge `{u + e₁, u + e₀ + e₁}` and
its endpoints are off the half-line `rayAbove u`, its winding numbers at `u` and `u + e₁`
agree. [folklore] -/
theorem walkWinding_eq_walkWinding_up {p : (LatticeModels.zdGraph 2).Walk a b} {u : LatticeModels.Site 2}
    (h : s(u + Pi.single 1 1, u + Pi.single 1 1 + Pi.single 0 1) ∉ p.edges)
    (ha : a ∉ rayAbove u) (hb : b ∉ rayAbove u) :
    walkWinding p u = walkWinding p (u + Pi.single 1 1) := by
  have hsum : (p.darts.map fun d => hCross u d.fst d.snd).sum = 0 := by
    refine List.sum_eq_zero fun t ht => ?_
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 ht
    refine hCross_eq_zero_of_ne fun heq => h ?_
    rw [← heq]
    exact List.mem_map.2 ⟨d, hd, rfl⟩
  have := walkWinding_sub_walkWinding_up p u
  rw [hsum, if_neg ha, if_neg hb] at this
  linarith

/-- The winding number of a lattice walk is constant along lattice steps avoiding the walk (when
the endpoints of the walk are off the relevant half-lines). [folklore] -/
theorem walkWinding_eq_of_stepKind {p : (LatticeModels.zdGraph 2).Walk a b} {v v' : LatticeModels.Site 2} (hvv' : StepKind v v')
    (hv : v ∉ p.support) (hv' : v' ∉ p.support)
    (hav : a ∉ rayAbove v) (hbv : b ∉ rayAbove v) (hav' : a ∉ rayAbove v') (hbv' : b ∉ rayAbove v') :
    walkWinding p v = walkWinding p v' := by
  have notEdge : ∀ {x y : LatticeModels.Site 2}, x ∉ p.support → s(x, y) ∉ p.edges :=
    fun hx he => hx (Walk.fst_mem_support_of_mem_edges p he)
  rcases hvv' with ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h1, h0⟩ | ⟨h1, h0⟩
  · have hv'eq : v' = v + Pi.single 0 1 := by
      simp [LatticeModels.Site.eq_iff_two, h0, h1]
    rw [hv'eq]
    exact walkWinding_eq_walkWinding_right (notEdge (by rwa [← hv'eq]))
  · have hveq : v = v' + Pi.single 0 1 := by
      simp [LatticeModels.Site.eq_iff_two, h0, h1]
    rw [hveq]
    exact (walkWinding_eq_walkWinding_right (notEdge (by rwa [← hveq]))).symm
  · have hv'eq : v' = v + Pi.single 1 1 := by
      simp [LatticeModels.Site.eq_iff_two, h0, h1]
    rw [hv'eq]
    exact walkWinding_eq_walkWinding_up (notEdge (by rwa [← hv'eq])) hav hbv
  · have hveq : v = v' + Pi.single 1 1 := by
      simp [LatticeModels.Site.eq_iff_two, h0, h1]
    rw [hveq]
    exact (walkWinding_eq_walkWinding_up (notEdge (by rwa [← hveq])) hav' hbv').symm

/-- **Constancy along avoiding walks.** If a lattice walk `q` avoids the vertices of the lattice
walk `p` (and the endpoints of `p` are off the half-lines `rayAbove z`, `z ∈ q`), then `p` winds
equally around the two ends of `q`. (Kesten 1982, §2.2, discrete Jordan curve arguments.) [folklore] -/
theorem walkWinding_eq_of_walk (p : (LatticeModels.zdGraph 2).Walk a b) {c d : LatticeModels.Site 2} (q : (LatticeModels.zdGraph 2).Walk c d)
    (hq : ∀ z ∈ q.support, z ∉ p.support)
    (ha : ∀ z ∈ q.support, a ∉ rayAbove z) (hb : ∀ z ∈ q.support, b ∉ rayAbove z) :
    walkWinding p c = walkWinding p d := by
  induction q with
  | nil => rfl
  | cons h q ih =>
    rename_i x y z
    have hx : x ∈ (Walk.cons h q).support := by simp
    have hy : y ∈ (Walk.cons h q).support := by simp
    have htail : ∀ w ∈ q.support, w ∈ (Walk.cons h q).support := fun w hw => by simp [hw]
    rw [walkWinding_eq_of_stepKind (stepKind_of_adj h) (hq x hx) (hq y hy) (ha x hx) (hb x hx)
      (ha y hy) (hb y hy)]
    exact ih (fun w hw => hq w (htail w hw)) (fun w hw => ha w (htail w hw))
      (fun w hw => hb w (htail w hw))

end Lattice

/-! ### Faces and the primal edge separating two adjacent faces

Recall (`Crossings.lean`) that the dual vertex `z : Site 2` stands for the unit face of `ℤ²`
with lower-left corner `z`. Two lattice-adjacent faces `z`, `z'` share the primal edge
`sepEdge z z' = {sepLo z z', sepHi z z'}`. -/

/-- Lower endpoint `z ⊔ z'` of the primal edge separating the adjacent faces `z`, `z'`. [folklore] -/
def sepLo (z z' : LatticeModels.Site 2) : LatticeModels.Site 2 := z ⊔ z'

/-- Upper endpoint of the primal edge separating the adjacent faces `z`, `z'`: `z ⊔ z' + e₁` if the
faces are horizontally adjacent (the edge is vertical), `z ⊔ z' + e₀` if vertically adjacent. [folklore] -/
def sepHi (z z' : LatticeModels.Site 2) : LatticeModels.Site 2 := z ⊔ z' + Pi.single (if z 0 = z' 0 then 0 else 1) 1

/-- The primal edge separating the adjacent faces `z`, `z'` (junk for non-adjacent faces).
(Grimmett 1999, §11.2, "each dual edge crosses a unique primal edge".) [folklore] -/
def sepEdge (z z' : LatticeModels.Site 2) : Sym2 (LatticeModels.Site 2) := s(sepLo z z', sepHi z z')

/-- `sepLo` is symmetric. [folklore] -/
theorem sepLo_comm (z z' : LatticeModels.Site 2) : sepLo z z' = sepLo z' z := sup_comm _ _

/-- `sepHi` is symmetric. [folklore] -/
theorem sepHi_comm (z z' : LatticeModels.Site 2) : sepHi z z' = sepHi z' z := by
  simp only [sepHi, sup_comm, eq_comm]

/-- `sepEdge` is symmetric. [folklore] -/
theorem sepEdge_comm (z z' : LatticeModels.Site 2) : sepEdge z z' = sepEdge z' z := by
  rw [sepEdge, sepEdge, sepLo_comm, sepHi_comm]

section SepLemmas

variable (z : LatticeModels.Site 2)

/-- `z ≤ z + e₀`. [folklore] -/
private theorem le_add_e0 : z ≤ z + Pi.single 0 1 :=
  le_add_of_nonneg_right (Pi.single_nonneg.2 zero_le_one)

/-- `z ≤ z + e₁`. [folklore] -/
private theorem le_add_e1 : z ≤ z + Pi.single 1 1 :=
  le_add_of_nonneg_right (Pi.single_nonneg.2 zero_le_one)

/-- `z - e₀ ≤ z`. [folklore] -/
private theorem sub_e0_le : z - Pi.single 0 1 ≤ z := by simp

/-- `z - e₁ ≤ z`. [folklore] -/
private theorem sub_e1_le : z - Pi.single 1 1 ≤ z := by simp

/-- `sepLo` of the face to the right. [folklore] -/
@[simp] theorem sepLo_add_e0 : sepLo z (z + Pi.single 0 1) = z + Pi.single 0 1 :=
  sup_of_le_right (le_add_e0 z)
/-- `sepLo` of the face to the left. [folklore] -/
@[simp] theorem sepLo_sub_e0 : sepLo z (z - Pi.single 0 1) = z := sup_of_le_left (sub_e0_le z)
/-- `sepLo` of the face above. [folklore] -/
@[simp] theorem sepLo_add_e1 : sepLo z (z + Pi.single 1 1) = z + Pi.single 1 1 :=
  sup_of_le_right (le_add_e1 z)
/-- `sepLo` of the face below. [folklore] -/
@[simp] theorem sepLo_sub_e1 : sepLo z (z - Pi.single 1 1) = z := sup_of_le_left (sub_e1_le z)

/-- `sepHi` of the face to the right. [folklore] -/
@[simp] theorem sepHi_add_e0 :
    sepHi z (z + Pi.single 0 1) = z + Pi.single 0 1 + Pi.single 1 1 := by
  have h : ¬(z 0 = (z + Pi.single 0 1 : LatticeModels.Site 2) 0) := by
    rw [Pi.add_apply, single_zero_apply_zero]; omega
  rw [sepHi, sup_of_le_right (le_add_e0 z), if_neg h]
/-- `sepHi` of the face to the left. [folklore] -/
@[simp] theorem sepHi_sub_e0 : sepHi z (z - Pi.single 0 1) = z + Pi.single 1 1 := by
  have h : ¬(z 0 = (z - Pi.single 0 1 : LatticeModels.Site 2) 0) := by
    rw [Pi.sub_apply, single_zero_apply_zero]; omega
  rw [sepHi, sup_of_le_left (sub_e0_le z), if_neg h]
/-- `sepHi` of the face above. [folklore] -/
@[simp] theorem sepHi_add_e1 :
    sepHi z (z + Pi.single 1 1) = z + Pi.single 1 1 + Pi.single 0 1 := by
  have h : z 0 = (z + Pi.single 1 1 : LatticeModels.Site 2) 0 := by
    rw [Pi.add_apply, single_one_apply_zero, add_zero]
  rw [sepHi, sup_of_le_right (le_add_e1 z), if_pos h]
/-- `sepHi` of the face below. [folklore] -/
@[simp] theorem sepHi_sub_e1 : sepHi z (z - Pi.single 1 1) = z + Pi.single 0 1 := by
  have h : z 0 = (z - Pi.single 1 1 : LatticeModels.Site 2) 0 := by
    rw [Pi.sub_apply, single_one_apply_zero, sub_zero]
  rw [sepHi, sup_of_le_left (sub_e1_le z), if_pos h]

/-- The edge separating a face from the face to its right is its right side. [folklore] -/
theorem sepEdge_right :
    sepEdge z (z + Pi.single 0 1) = s(z + Pi.single 0 1, z + Pi.single 0 1 + Pi.single 1 1) := by
  rw [sepEdge, sepLo_add_e0, sepHi_add_e0]

/-- The edge separating a face from the face above it is its top side. [folklore] -/
theorem sepEdge_up :
    sepEdge z (z + Pi.single 1 1) = s(z + Pi.single 1 1, z + Pi.single 1 1 + Pi.single 0 1) := by
  rw [sepEdge, sepLo_add_e1, sepHi_add_e1]

end SepLemmas

/-- For adjacent faces, `sepHi = sepLo + eᵢ` for some `i`: the separating edge is a lattice
edge. [folklore] -/
theorem sepEdge_mem_edgeSet {z z' : LatticeModels.Site 2} (h : (LatticeModels.zdGraph 2).Adj z z') :
    sepEdge z z' ∈ (LatticeModels.zdGraph 2).edgeSet := by
  rcases stepKind_of_adj h with ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h1, h0⟩ | ⟨h1, h0⟩
  · obtain rfl : z' = z + Pi.single 0 1 := by simp [LatticeModels.Site.eq_iff_two, h0, h1]
    rw [sepEdge_right]; exact single_edge_mem _ 1
  · obtain rfl : z = z' + Pi.single 0 1 := by simp [LatticeModels.Site.eq_iff_two, h0, h1]
    rw [sepEdge_comm, sepEdge_right]; exact single_edge_mem _ 1
  · obtain rfl : z' = z + Pi.single 1 1 := by simp [LatticeModels.Site.eq_iff_two, h0, h1]
    rw [sepEdge_up]; exact single_edge_mem _ 0
  · obtain rfl : z = z' + Pi.single 1 1 := by simp [LatticeModels.Site.eq_iff_two, h0, h1]
    rw [sepEdge_comm, sepEdge_up]; exact single_edge_mem _ 0

/-- **The dual edge joining two adjacent faces is the dual of the primal edge separating them**:
`dualEdge (sepEdge z z') = {z, z'}` (with the lower-left-corner indexing of `Crossings.lean`).
(Grimmett 1999, §11.2; Bollobás–Riordan 2006, Ch. 3, Figure 2.) [folklore] -/
theorem dualEdge_sepEdge {z z' : LatticeModels.Site 2} (h : (LatticeModels.zdGraph 2).Adj z z') :
    dualEdge (sepEdge z z') = s(z, z') := by
  rcases stepKind_of_adj h with ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h1, h0⟩ | ⟨h1, h0⟩
  · obtain rfl : z' = z + Pi.single 0 1 := by simp [LatticeModels.Site.eq_iff_two, h0, h1]
    rw [sepEdge_right, dualEdge_vertical, add_sub_cancel_right]
  · obtain rfl : z = z' + Pi.single 0 1 := by simp [LatticeModels.Site.eq_iff_two, h0, h1]
    rw [sepEdge_comm, sepEdge_right, dualEdge_vertical, add_sub_cancel_right, Sym2.eq_swap]
  · obtain rfl : z' = z + Pi.single 1 1 := by simp [LatticeModels.Site.eq_iff_two, h0, h1]
    rw [sepEdge_up, dualEdge_horizontal, add_sub_cancel_right]
  · obtain rfl : z = z' + Pi.single 1 1 := by simp [LatticeModels.Site.eq_iff_two, h0, h1]
    rw [sepEdge_comm, sepEdge_up, dualEdge_horizontal, add_sub_cancel_right, Sym2.eq_swap]

/-- Both endpoints of the separating edge of adjacent faces `z`, `z'` have first coordinate at
most `max z₀ z'₀ + 1` and at least `max z₀ z'₀`. [folklore] -/
theorem sepEdge_apply_zero_le {z z' w : LatticeModels.Site 2} (hw : w ∈ sepEdge z z') :
    w 0 ≤ max (z 0) (z' 0) + 1 ∧ max (z 0) (z' 0) ≤ w 0 := by
  rw [sepEdge, Sym2.mem_iff] at hw
  rcases hw with rfl | rfl
  · simp [sepLo]
  · simp only [sepHi, Pi.add_apply, Pi.sup_apply]
    split_ifs <;> simp

section FaceWalks

variable {a b : LatticeModels.Site 2}

/-- **Constancy along dual walks.** If `q` is a walk of faces (lattice-adjacent lower-left
corners) such that `p` never traverses the primal edge separating two consecutive faces of `q`
(and the endpoints of `p` are off the half-lines `rayAbove z`, `z ∈ q`), then `p` winds equally
around the two end faces of `q`. (Kesten 1982, §2.2.) [folklore] -/
theorem walkWinding_eq_of_faceWalk (p : (LatticeModels.zdGraph 2).Walk a b) {c d : LatticeModels.Site 2} (q : (LatticeModels.zdGraph 2).Walk c d)
    (hq : ∀ dq ∈ q.darts, sepEdge dq.fst dq.snd ∉ p.edges)
    (ha : ∀ z ∈ q.support, a ∉ rayAbove z) (hb : ∀ z ∈ q.support, b ∉ rayAbove z) :
    walkWinding p c = walkWinding p d := by
  induction q with
  | nil => rfl
  | cons h q ih =>
    rename_i x y z
    have hx : x ∈ (Walk.cons h q).support := by simp
    have hy : y ∈ (Walk.cons h q).support := by simp
    have htail : ∀ w ∈ q.support, w ∈ (Walk.cons h q).support := fun w hw => by simp [hw]
    have hxy : sepEdge x y ∉ p.edges := hq ⟨(x, y), h⟩ (by simp)
    have step : walkWinding p x = walkWinding p y := by
      rcases stepKind_of_adj h with ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h1, h0⟩ | ⟨h1, h0⟩
      · have hyeq : y = x + Pi.single 0 1 := by simp [LatticeModels.Site.eq_iff_two, h0, h1]
        rw [hyeq] at hxy ⊢
        rw [sepEdge_right] at hxy
        exact walkWinding_eq_walkWinding_right hxy
      · have hxeq : x = y + Pi.single 0 1 := by simp [LatticeModels.Site.eq_iff_two, h0, h1]
        rw [hxeq] at hxy ⊢
        rw [sepEdge_comm, sepEdge_right] at hxy
        exact (walkWinding_eq_walkWinding_right hxy).symm
      · have hyeq : y = x + Pi.single 1 1 := by simp [LatticeModels.Site.eq_iff_two, h0, h1]
        rw [hyeq] at hxy ⊢
        rw [sepEdge_up] at hxy
        exact walkWinding_eq_walkWinding_up hxy (ha x hx) (hb x hx)
      · have hxeq : x = y + Pi.single 1 1 := by simp [LatticeModels.Site.eq_iff_two, h0, h1]
        rw [hxeq] at hxy ⊢
        rw [sepEdge_comm, sepEdge_up] at hxy
        exact (walkWinding_eq_walkWinding_up hxy (by simpa [hxeq] using ha y hy)
          (by simpa [hxeq] using hb y hy)).symm
    rw [step]
    exact ih (fun dq hdq => hq dq (by simp [hdq])) (fun w hw => ha w (htail w hw))
      (fun w hw => hb w (htail w hw))

end FaceWalks

/-! ### Winding numbers vanish outside the shadow of the walk -/

section Shadow

variable {a b : LatticeModels.Site 2}

/-- No winding at or above the top of the walk. [folklore] -/
theorem walkWinding_eq_zero_of_le {p : (LatticeModels.zdGraph 2).Walk a b} {u : LatticeModels.Site 2} {N : ℤ}
    (hp : ∀ z ∈ p.support, z 1 ≤ N) (hu : N ≤ u 1) : walkWinding p u = 0 := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    rename_i x y z
    rw [walkWinding_cons, ih fun w hw => hp w (by simp [hw]), add_zero]
    have hx := hp x (by simp)
    have hy := hp y (by simp)
    unfold stepWinding upStep
    split_ifs <;> omega

/-- No winding strictly below the bottom of the walk. [folklore] -/
theorem walkWinding_eq_zero_of_ge {p : (LatticeModels.zdGraph 2).Walk a b} {u : LatticeModels.Site 2} {L : ℤ}
    (hp : ∀ z ∈ p.support, L ≤ z 1) (hu : u 1 + 1 ≤ L) : walkWinding p u = 0 := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    rename_i x y z
    rw [walkWinding_cons, ih fun w hw => hp w (by simp [hw]), add_zero]
    have hx := hp x (by simp)
    have hy := hp y (by simp)
    unfold stepWinding upStep
    split_ifs <;> omega

end Shadow

/-! ### Vertical runs -/

/-- One step down is a lattice step. [folklore] -/
theorem adj_sub_single_one (z : LatticeModels.Site 2) : (LatticeModels.zdGraph 2).Adj z (z - Pi.single 1 1) :=
  adj_of_stepKind (.down (by simp) (by simp))

/-- The straight walk of `k` steps down from `z`. [folklore] -/
def downRun (z : LatticeModels.Site 2) : (k : ℕ) → (LatticeModels.zdGraph 2).Walk z ((fun w : LatticeModels.Site 2 => w - Pi.single 1 1)^[k] z)
  | 0 => Walk.nil
  | k + 1 => Walk.cons (adj_sub_single_one z) (downRun (z - Pi.single 1 1) k)

/-- First coordinate along a vertical run. [folklore] -/
@[simp] theorem iterate_sub_single_apply_zero (z : LatticeModels.Site 2) (k : ℕ) :
    ((fun w : LatticeModels.Site 2 => w - Pi.single 1 1)^[k] z) 0 = z 0 := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, ih]; simp

/-- Second coordinate at the end of a vertical run. [folklore] -/
@[simp] theorem iterate_sub_single_apply_one (z : LatticeModels.Site 2) (k : ℕ) :
    ((fun w : LatticeModels.Site 2 => w - Pi.single 1 1)^[k] z) 1 = z 1 - k := by
  induction k generalizing z with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply, ih]; simp; ring

/-- The vertices of a vertical run. [folklore] -/
theorem mem_support_downRun {z w : LatticeModels.Site 2} {k : ℕ} :
    w ∈ (downRun z k).support ↔ w 0 = z 0 ∧ z 1 - k ≤ w 1 ∧ w 1 ≤ z 1 := by
  induction k generalizing z with
  | zero =>
    show w ∈ (Walk.nil : (LatticeModels.zdGraph 2).Walk z z).support ↔ _
    rw [Walk.support_nil, List.mem_singleton, LatticeModels.Site.eq_iff_two]
    simp only [Nat.cast_zero, sub_zero]
    omega
  | succ k ih =>
    show w ∈ (Walk.cons (adj_sub_single_one z) (downRun (z - Pi.single 1 1) k)).support ↔ _
    rw [Walk.support_cons, List.mem_cons, ih, LatticeModels.Site.eq_iff_two]
    simp only [Pi.sub_apply, single_one_apply_zero, sub_zero, single_one_apply_one, Nat.cast_succ]
    omega

/-- The winding number of a vertical run: `-1` around the points strictly to its left whose level it
passes, `0` elsewhere. [folklore] -/
theorem walkWinding_downRun (z : LatticeModels.Site 2) (k : ℕ) (u : LatticeModels.Site 2) :
    walkWinding (downRun z k) u = -(if u 0 + 1 ≤ z 0 ∧ z 1 - k ≤ u 1 ∧ u 1 + 1 ≤ z 1 then 1 else 0) := by
  induction k generalizing z with
  | zero =>
    show walkWinding (Walk.nil : (LatticeModels.zdGraph 2).Walk z z) u = _
    rw [walkWinding_nil]
    simp only [Nat.cast_zero, sub_zero]
    split_ifs <;> omega
  | succ k ih =>
    show walkWinding (Walk.cons (adj_sub_single_one z) (downRun (z - Pi.single 1 1) k)) u = _
    rw [walkWinding_cons, ih, stepWinding_down (y := z - Pi.single 1 1) (by simp) (by simp)]
    simp only [Pi.sub_apply, single_one_apply_one, single_one_apply_zero, sub_zero, Nat.cast_succ]
    split_ifs <;> omega

/-! ### Crossing walks of a rectangle meet -/

section Meet

variable {a b c d : LatticeModels.Site 2}

/-- The extension of a left-right crossing `P` (ending at `b` on the right side `x₀ = R`) by the
step to `b + e₀` and the vertical run down to height `B - 2`; all box-crossing contradictions are
derived from the winding numbers of this walk. [folklore] -/
def extendRight (P : (LatticeModels.zdGraph 2).Walk a b) (B : ℤ) :
    (LatticeModels.zdGraph 2).Walk a ((fun w : LatticeModels.Site 2 => w - Pi.single 1 1)^[(b 1 - B).toNat + 2] (b + Pi.single 0 1)) :=
  P.append (Walk.cons (adj_of_stepKind (.right (by simp) (by simp)) :
    (LatticeModels.zdGraph 2).Adj b (b + Pi.single 0 1)) (downRun (b + Pi.single 0 1) ((b 1 - B).toNat + 2)))

/-- Vertices of the extended walk: those of `P`, or on the column `x₀ = b₀ + 1` at heights in
`[B - 2, b₁]`. [folklore] -/
theorem mem_support_extendRight {P : (LatticeModels.zdGraph 2).Walk a b} {B : ℤ} (hB : B ≤ b 1) {z : LatticeModels.Site 2}
    (hz : z ∈ (extendRight P B).support) :
    z ∈ P.support ∨ (z 0 = b 0 + 1 ∧ B - 2 ≤ z 1 ∧ z 1 ≤ b 1) := by
  rw [extendRight, Walk.support_append, List.mem_append, Walk.support_cons, List.tail_cons,
    mem_support_downRun] at hz
  rcases hz with hz | hz
  · exact Or.inl hz
  · right
    have hK : (((b 1 - B).toNat + 2 : ℕ) : ℤ) = b 1 - B + 2 := by
      push_cast; rw [Int.toNat_of_nonneg (by omega)]
    simp only [Pi.add_apply, single_zero_apply_zero, single_zero_apply_one, add_zero, hK] at hz
    omega

/-- Edges of the extended walk: those of `P`, or edges with an endpoint on the column
`x₀ = b₀ + 1`. [folklore] -/
theorem mem_edges_extendRight {P : (LatticeModels.zdGraph 2).Walk a b} {B : ℤ} {e : Sym2 (LatticeModels.Site 2)}
    (he : e ∈ (extendRight P B).edges) : e ∈ P.edges ∨ ∃ w ∈ e, w 0 = b 0 + 1 := by
  rw [extendRight, Walk.edges_append, List.mem_append, Walk.edges_cons, List.mem_cons] at he
  rcases he with he | rfl | he
  · exact Or.inl he
  · exact Or.inr ⟨b + Pi.single 0 1, Sym2.mem_mk_right _ _, by simp⟩
  · right
    induction e using Sym2.ind with
    | h x y =>
      refine ⟨x, Sym2.mem_mk_left _ _, ?_⟩
      have := mem_support_downRun.1 (Walk.fst_mem_support_of_mem_edges _ he)
      simpa using this.1

/-- The end of the extended walk is `(b₀ + 1, B - 2)`. [folklore] -/
theorem extendRight_end_apply (b : LatticeModels.Site 2) {B : ℤ} (hB : B ≤ b 1) :
    ((fun w : LatticeModels.Site 2 => w - Pi.single 1 1)^[(b 1 - B).toNat + 2] (b + Pi.single 0 1)) 0 = b 0 + 1 ∧
    ((fun w : LatticeModels.Site 2 => w - Pi.single 1 1)^[(b 1 - B).toNat + 2] (b + Pi.single 0 1)) 1 = B - 2 := by
  rw [iterate_sub_single_apply_zero, iterate_sub_single_apply_one]
  have hK : (((b 1 - B).toNat + 2 : ℕ) : ℤ) = b 1 - B + 2 := by
    push_cast; rw [Int.toNat_of_nonneg (by omega)]
  simp only [Pi.add_apply, single_zero_apply_zero, single_zero_apply_one, add_zero, hK, true_and]
  ring

/-- Winding of the extended walk at a point `u` at the top level `T` (with `u₀ ≤ b₀`): zero.
[folklore] -/
theorem walkWinding_extendRight_top {P : (LatticeModels.zdGraph 2).Walk a b} {B T : ℤ}
    (hP : ∀ z ∈ P.support, B ≤ z 1 ∧ z 1 ≤ T) {u : LatticeModels.Site 2} (hu1 : u 1 = T) :
    walkWinding (extendRight P B) u = 0 := by
  have hb := hP b P.end_mem_support
  rw [extendRight, walkWinding_append, walkWinding_cons, walkWinding_downRun,
    walkWinding_eq_zero_of_le (N := T) (fun z hz => (hP z hz).2) hu1.ge,
    stepWinding_right (by simp)]
  simp only [Pi.add_apply, single_zero_apply_zero, single_zero_apply_one, add_zero]
  split_ifs <;> omega

/-- Winding of the extended walk at a point `u` just below the bottom level (`u₁ = B - 1`) and not
to the right of `b` (`u₀ ≤ b₀`): minus one. [folklore] -/
theorem walkWinding_extendRight_bottom {P : (LatticeModels.zdGraph 2).Walk a b} {B T : ℤ}
    (hP : ∀ z ∈ P.support, B ≤ z 1 ∧ z 1 ≤ T) {u : LatticeModels.Site 2} (hu1 : u 1 = B - 1) (hu0 : u 0 ≤ b 0) :
    walkWinding (extendRight P B) u = -1 := by
  have hb := hP b P.end_mem_support
  have hK : (((b 1 - B).toNat + 2 : ℕ) : ℤ) = b 1 - B + 2 := by
    push_cast; rw [Int.toNat_of_nonneg (by omega)]
  rw [extendRight, walkWinding_append, walkWinding_cons, walkWinding_downRun,
    walkWinding_eq_zero_of_ge (L := B) (fun z hz => (hP z hz).1) (by omega),
    stepWinding_right (by simp)]
  simp only [Pi.add_apply, single_zero_apply_zero, single_zero_apply_one, add_zero, hK]
  split_ifs <;> omega

/-- **A left-right and a top-bottom crossing of a rectangle meet.** If `P` is a lattice walk in
the box `[L, R] × [B, T]` from the left side to the right side and `Q` a lattice walk in the same
box from the bottom side to the top side, then `P` and `Q` have a common vertex. (Discrete form
of the Jordan curve theorem underlying all box-crossing arguments; Kesten 1982, §2.2;
Bollobás–Riordan 2006, Ch. 3, proof of eq. (2), "this path must meet" the horizontal crossing.) [folklore] -/
theorem exists_mem_support_of_crossing {L R B T : ℤ}
    (P : (LatticeModels.zdGraph 2).Walk a b) (Q : (LatticeModels.zdGraph 2).Walk c d)
    (hP : ∀ z ∈ P.support, L ≤ z 0 ∧ z 0 ≤ R ∧ B ≤ z 1 ∧ z 1 ≤ T)
    (hQ : ∀ z ∈ Q.support, L ≤ z 0 ∧ z 0 ≤ R ∧ B ≤ z 1 ∧ z 1 ≤ T)
    (ha : a 0 = L) (hb : b 0 = R) (hc : c 1 = B) (hd : d 1 = T) :
    ∃ z ∈ P.support, z ∈ Q.support := by
  by_contra hdis
  push Not at hdis
  have hbN := hP b (Walk.end_mem_support P)
  have hP' : ∀ z ∈ P.support, B ≤ z 1 ∧ z 1 ≤ T := fun z hz => ⟨(hP z hz).2.2.1, (hP z hz).2.2.2⟩
  -- extend `Q` at the start by one step up from `c - e₁`
  set c' := c - Pi.single 1 1 with hc'
  have hadj' : (LatticeModels.zdGraph 2).Adj c' c := adj_of_stepKind (.up (by simp [hc']) (by simp [hc']))
  have hc0 := hQ c (Walk.start_mem_support Q)
  -- the winding number of the extended `P` at the top end `d` of `Q` is `0`, at `c'` it is `-1`
  have hWd : walkWinding (extendRight P B) d = 0 := walkWinding_extendRight_top hP' hd
  have hWc : walkWinding (extendRight P B) c' = -1 :=
    walkWinding_extendRight_bottom hP' (by simp [hc', hc]) (by simp [hc', hb]; omega)
  -- but the winding number is constant along `c' :: Q`
  have hconst := walkWinding_eq_of_walk (extendRight P B) (Walk.cons hadj' Q) ?_ ?_ ?_
  · rw [hWc, hWd] at hconst; exact absurd hconst (by norm_num)
  · intro z hz hzP
    rw [Walk.support_cons, List.mem_cons] at hz
    rcases mem_support_extendRight hbN.2.2.1 hzP with hzP | hzP
    · rcases hz with rfl | hz
      · have := (hP _ hzP).2.2.1
        simp [hc'] at this
        omega
      · exact hdis z hzP hz
    · rcases hz with rfl | hz
      · simp [hc'] at hzP
        omega
      · have := (hQ z hz).2.1
        omega
  · intro z hz
    simp only [mem_rayAbove, ha, not_and, not_le]
    intro _
    rw [Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · simp only [hc', Pi.sub_apply, single_one_apply_zero, sub_zero]
      omega
    · have := (hQ z hz).1; omega
  · intro z hz
    simp only [mem_rayAbove, not_and]
    intro h1
    exfalso
    rw [(extendRight_end_apply b hbN.2.2.1).2] at h1
    rw [Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · simp [hc', hc] at h1
    · have := (hQ z hz).2.2.1; omega

/-- **A left-right crossing separates the top faces from the bottom faces.** If `P` is a lattice
walk in `[0, M] × [0, N]` from the left side to the right side and `Q` is a walk of faces of the
dual rectangle `[0, M - 1] × [-1, N]` (lower-left corners) from a top face to a bottom face, then
some step of `Q` crosses an edge of `P`. (The "only if" direction of Bollobás–Riordan 2006, Ch. 3,
Lemma 1; Kesten 1982, §2.2.) [folklore] -/
theorem exists_dart_sepEdge_mem_edges {M N : ℕ} {t s : LatticeModels.Site 2}
    (P : (LatticeModels.zdGraph 2).Walk a b) (Q : (LatticeModels.zdGraph 2).Walk t s)
    (hP : ∀ z ∈ P.support, 0 ≤ z 0 ∧ z 0 ≤ M ∧ 0 ≤ z 1 ∧ z 1 ≤ N)
    (hQ : ∀ z ∈ Q.support, 0 ≤ z 0 ∧ z 0 + 1 ≤ M ∧ -1 ≤ z 1 ∧ z 1 ≤ N)
    (ha : a 0 = 0) (hb : b 0 = M) (ht : t 1 = N) (hs : s 1 = -1) :
    ∃ dq ∈ Q.darts, sepEdge dq.fst dq.snd ∈ P.edges := by
  by_contra hdis
  push Not at hdis
  have hbN := hP b (Walk.end_mem_support P)
  have hP' : ∀ z ∈ P.support, (0 : ℤ) ≤ z 1 ∧ z 1 ≤ N := fun z hz => ⟨(hP z hz).2.2.1, (hP z hz).2.2.2⟩
  have hs0 := hQ s (Walk.end_mem_support Q)
  have hWt : walkWinding (extendRight P 0) t = 0 := walkWinding_extendRight_top hP' ht
  have hWs : walkWinding (extendRight P 0) s = -1 :=
    walkWinding_extendRight_bottom hP' (by rw [hs]; ring) (by rw [hb]; omega)
  have hconst := walkWinding_eq_of_faceWalk (extendRight P 0) Q ?_ ?_ ?_
  · rw [hWt, hWs] at hconst; exact absurd hconst (by norm_num)
  · intro dq hdq he
    have hz := hQ _ (Q.dart_fst_mem_support_of_mem_darts hdq)
    have hz' := hQ _ (Q.dart_snd_mem_support_of_mem_darts hdq)
    rcases mem_edges_extendRight he with he | ⟨w, hw, hw0⟩
    · exact hdis dq hdq he
    · have := (sepEdge_apply_zero_le hw).1
      rw [hw0, hb] at this
      have : max (dq.toProd.1 0) (dq.toProd.2 0) + 1 ≤ (M : ℤ) := by
        rcases le_total (dq.toProd.1 0) (dq.toProd.2 0) with h | h
        · rw [max_eq_right h]; exact hz'.2.1
        · rw [max_eq_left h]; exact hz.2.1
      omega
  · intro z hz
    simp only [mem_rayAbove, ha, not_and, not_le]
    intro _
    have := (hQ z hz).1; omega
  · intro z hz
    simp only [mem_rayAbove, not_and]
    intro h1
    exfalso
    rw [(extendRight_end_apply b hbN.2.2.1).2] at h1
    have := (hQ z hz).2.2.1; omega

end Meet

/-! ### The parity lemma: a bichromatic dual crossing exists -/

section Parity

variable (c : LatticeModels.Site 2 → Prop) (m n : ℕ)

/-- The face step `z → z'` crosses an edge of `[0, m] × [0, n]` whose endpoints have different
colours. [folklore] -/
def Bichromatic (z z' : LatticeModels.Site 2) : Prop :=
  sepLo z z' ∈ rectangle m n ∧ sepHi z z' ∈ rectangle m n ∧ (c (sepLo z z') ↔ ¬c (sepHi z z'))

variable {c m n}

/-- `Bichromatic` is symmetric. [folklore] -/
theorem Bichromatic.symm {z z' : LatticeModels.Site 2} (h : Bichromatic c m n z z') : Bichromatic c m n z' z := by
  unfold Bichromatic at h ⊢
  rwa [sepLo_comm, sepHi_comm]

variable (c m n)

/-- The graph on faces of the dual rectangle: adjacent faces separated by a bichromatic edge
of the rectangle. (The combinatorial substitute for the interface of Bollobás–Riordan 2006,
Ch. 3, proof of Lemma 1, Figure 3.) [folklore] -/
def bichromaticGraph : SimpleGraph (LatticeModels.Site 2) where
  Adj z z' := (LatticeModels.zdGraph 2).Adj z z' ∧ z ∈ dualRectangle m n ∧ z' ∈ dualRectangle m n ∧
    Bichromatic c m n z z'
  symm := ⟨fun _ _ ⟨h1, h2, h3, h4⟩ => ⟨h1.symm, h3, h2, h4.symm⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

/-- Faces joined to a top face of the dual rectangle in `bichromaticGraph`. [folklore] -/
def TopReach (z : LatticeModels.Site 2) : Prop := ∃ t ∈ dualTopSide m n, (bichromaticGraph c m n).Reachable t z

/-- `bichromaticGraph` restricted to the faces joined to the top. [folklore] -/
def topGraph : SimpleGraph (LatticeModels.Site 2) where
  Adj z z' := (bichromaticGraph c m n).Adj z z' ∧ TopReach c m n z ∧ TopReach c m n z'
  symm := ⟨fun _ _ ⟨h1, h2, h3⟩ => ⟨h1.symm, h3, h2⟩⟩
  loopless := ⟨fun _ h => h.1.1.ne rfl⟩

variable {c m n}

/-- `TopReach` propagates along `bichromaticGraph`. [folklore] -/
theorem TopReach.of_adj {z z' : LatticeModels.Site 2} (hz : TopReach c m n z)
    (h : (bichromaticGraph c m n).Adj z z') : TopReach c m n z' := by
  obtain ⟨t, ht, htz⟩ := hz
  exact ⟨t, ht, htz.trans h.reachable⟩

/-- On faces joined to the top, `topGraph` and `bichromaticGraph` have the same edges. [folklore] -/
theorem topGraph_adj_iff_of_topReach {z z' : LatticeModels.Site 2} (hz : TopReach c m n z) :
    (topGraph c m n).Adj z z' ↔ (bichromaticGraph c m n).Adj z z' :=
  ⟨fun h => h.1, fun h => ⟨h, hz, hz.of_adj h⟩⟩

/-- The four lattice neighbours of `z`. [folklore] -/
def nbrs (z : LatticeModels.Site 2) : Finset (LatticeModels.Site 2) :=
  {z + Pi.single 0 1, z - Pi.single 0 1, z + Pi.single 1 1, z - Pi.single 1 1}

/-- Lattice neighbours lie in `nbrs`. [folklore] -/
theorem mem_nbrs_of_adj {z z' : LatticeModels.Site 2} (h : (LatticeModels.zdGraph 2).Adj z z') : z' ∈ nbrs z := by
  rw [zdGraph_two_adj_iff] at h
  simp only [nbrs, Finset.mem_insert, Finset.mem_singleton, LatticeModels.Site.eq_iff_two, Pi.add_apply,
    Pi.sub_apply, single_zero_apply_zero, single_zero_apply_one, single_one_apply_zero,
    single_one_apply_one, add_zero, sub_zero]
  omega

/-- The finite type of faces of the dual rectangle. [folklore] -/
abbrev DFace (m n : ℕ) : Type := {z : LatticeModels.Site 2 // z ∈ dualRectangle m n}

variable (c m n) in
/-- `topGraph` as a graph on the finite type of faces of the dual rectangle. [folklore] -/
def topGraphF : SimpleGraph (DFace m n) :=
  (topGraph c m n).comap (Function.Embedding.subtype _)

/-- Degrees in `topGraphF` are numbers of `topGraph`-neighbours among the four lattice
neighbours. [folklore] -/
theorem degree_topGraphF (v : DFace m n) [Fintype ((topGraphF c m n).neighborSet v)]
    [DecidablePred fun z' => (topGraph c m n).Adj v z'] :
    (topGraphF c m n).degree v = #((nbrs (v : LatticeModels.Site 2)).filter fun z' => (topGraph c m n).Adj v z') := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    ← Finset.card_map (Function.Embedding.subtype _)]
  congr 1
  ext z'
  simp only [Finset.mem_map, SimpleGraph.mem_neighborFinset, Function.Embedding.coe_subtype,
    Finset.mem_filter, Subtype.exists, exists_and_right, exists_eq_right]
  constructor
  · rintro ⟨hz', h⟩
    exact ⟨mem_nbrs_of_adj h.1.1, h⟩
  · rintro ⟨-, h⟩
    exact ⟨h.1.2.2.1, h⟩

/-- Sum of four indicators over the four neighbours. [folklore] -/
theorem card_filter_nbrs (z : LatticeModels.Site 2) (p : LatticeModels.Site 2 → Prop) [DecidablePred p] :
    #((nbrs z).filter p) =
      (if p (z + Pi.single 0 1) then 1 else 0) + (if p (z - Pi.single 0 1) then 1 else 0) +
      (if p (z + Pi.single 1 1) then 1 else 0) + (if p (z - Pi.single 1 1) then 1 else 0) := by
  have h1 : z + Pi.single 0 1 ∉ ({z - Pi.single 0 1, z + Pi.single 1 1, z - Pi.single 1 1} :
      Finset (LatticeModels.Site 2)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, LatticeModels.Site.eq_iff_two, Pi.add_apply,
      Pi.sub_apply, single_zero_apply_zero, single_zero_apply_one, single_one_apply_zero,
      single_one_apply_one, add_zero, sub_zero]
    omega
  have h2 : z - Pi.single 0 1 ∉ ({z + Pi.single 1 1, z - Pi.single 1 1} : Finset (LatticeModels.Site 2)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, LatticeModels.Site.eq_iff_two, Pi.add_apply,
      Pi.sub_apply, single_zero_apply_zero, single_zero_apply_one, single_one_apply_zero,
      single_one_apply_one, add_zero, sub_zero]
    omega
  have h3 : z + Pi.single 1 1 ∉ ({z - Pi.single 1 1} : Finset (LatticeModels.Site 2)) := by
    simp only [Finset.mem_singleton, LatticeModels.Site.eq_iff_two, Pi.add_apply,
      Pi.sub_apply, single_one_apply_zero, single_one_apply_one, add_zero, sub_zero]
    omega
  rw [nbrs, Finset.card_filter, Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_insert h3,
    Finset.sum_singleton]
  ring

/-- Parity of the number of bichromatic sides of a face: a 4-cycle of colours changes colour an
even number of times. [folklore] -/
theorem even_four_sides (p q r s : Prop) [Decidable p] [Decidable q] [Decidable r] [Decidable s] :
    Even ((if (q ↔ ¬r) then 1 else 0) + (if (p ↔ ¬s) then 1 else 0) +
      (if (s ↔ ¬r) then 1 else 0) + (if (p ↔ ¬q) then 1 else 0) : ℕ) := by
  by_cases hp : p <;> by_cases hq : q <;> by_cases hr : r <;> by_cases hs : s <;>
    simp [hp, hq, hr, hs] <;> decide

/-- Parity of the number of colour changes along a row: even iff the two ends have the same
colour. [folklore] -/
theorem even_card_changes_iff (f : ℕ → Prop) [DecidablePred f] (k : ℕ) :
    Even #((Finset.range k).filter fun x => (f x ↔ ¬f (x + 1))) ↔ (f 0 ↔ f k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.range_add_one, Finset.filter_insert]
    by_cases hk : (f k ↔ ¬f (k + 1))
    · rw [if_pos hk, Finset.card_insert_of_notMem (by simp), Nat.even_add_one, ih]
      tauto
    · rw [if_neg hk, ih]
      tauto

section RowLemmas

variable {z : LatticeModels.Site 2} (hz : z ∈ dualRectangle m n)
  (hL : ∀ x ∈ leftSide m n, c x) (hR : ∀ x ∈ rightSide m n, ¬c x)

include hz in
/-- Adjacency in `bichromaticGraph` from a face of the dual rectangle, unfolded. [folklore] -/
theorem bichromaticGraph_adj_iff {z' : LatticeModels.Site 2} :
    (bichromaticGraph c m n).Adj z z' ↔ (LatticeModels.zdGraph 2).Adj z z' ∧ z' ∈ dualRectangle m n ∧
      sepLo z z' ∈ rectangle m n ∧ sepHi z z' ∈ rectangle m n ∧
      (c (sepLo z z') ↔ ¬c (sepHi z z')) :=
  ⟨fun h => ⟨h.1, h.2.2.1, h.2.2.2⟩, fun h => ⟨h.1, hz, h.2.1, h.2.2⟩⟩

/-- The face to the right is adjacent. [folklore] -/
private theorem adjR : (LatticeModels.zdGraph 2).Adj z (z + Pi.single 0 1) :=
  (LatticeModels.zdGraph_adj_iff _ _).2 ⟨0, Or.inl rfl⟩
/-- The face to the left is adjacent. [folklore] -/
private theorem adjL : (LatticeModels.zdGraph 2).Adj z (z - Pi.single 0 1) :=
  (LatticeModels.zdGraph_adj_iff _ _).2 ⟨0, Or.inr (by simp)⟩
/-- The face above is adjacent. [folklore] -/
private theorem adjU : (LatticeModels.zdGraph 2).Adj z (z + Pi.single 1 1) :=
  (LatticeModels.zdGraph_adj_iff _ _).2 ⟨1, Or.inl rfl⟩
/-- The face below is adjacent. [folklore] -/
private theorem adjD : (LatticeModels.zdGraph 2).Adj z (z - Pi.single 1 1) :=
  (LatticeModels.zdGraph_adj_iff _ _).2 ⟨1, Or.inr (by simp)⟩

include hL in
/-- Vertices of the left side are coloured. [folklore] -/
private theorem cL {w : LatticeModels.Site 2} (h0 : w 0 = 0) (h1 : 0 ≤ w 1) (h2 : w 1 ≤ n) : c w :=
  hL w (by simp [leftSide, mem_rectangle_iff, h0, h1, h2])

include hR in
/-- Vertices of the right side are not coloured. [folklore] -/
private theorem cR {w : LatticeModels.Site 2} (h0 : w 0 = m) (h1 : 0 ≤ w 1) (h2 : w 1 ≤ n) : ¬c w :=
  hR w (by simp [rightSide, mem_rectangle_iff, h0, h1, h2])

include hz in
/-- Bottom faces have at most the neighbour above, through the bottom edge of the rectangle. [folklore] -/
theorem odd_card_filter_adj_bottom [DecidablePred fun z' => (bichromaticGraph c m n).Adj z z']
    (h1 : z 1 = -1) :
    Odd #((nbrs z).filter fun z' => (bichromaticGraph c m n).Adj z z') ↔
      (c (z + Pi.single 1 1) ↔ ¬c (z + Pi.single 1 1 + Pi.single 0 1)) := by
  classical
  have hzD := mem_dualRectangle_iff.1 hz
  rw [card_filter_nbrs]
  have n0 : ¬(bichromaticGraph c m n).Adj z (z + Pi.single 0 1) := fun h => by
    have := (mem_rectangle_iff.1 h.2.2.2.1).2.2.1
    simp at this; omega
  have n1 : ¬(bichromaticGraph c m n).Adj z (z - Pi.single 0 1) := fun h => by
    have := (mem_rectangle_iff.1 h.2.2.2.1).2.2.1
    simp at this; omega
  have n3 : ¬(bichromaticGraph c m n).Adj z (z - Pi.single 1 1) := fun h => by
    have := (mem_dualRectangle_iff.1 h.2.2.1).2.2.1
    simp at this; omega
  have y2 : (bichromaticGraph c m n).Adj z (z + Pi.single 1 1) ↔
      (c (z + Pi.single 1 1) ↔ ¬c (z + Pi.single 1 1 + Pi.single 0 1)) := by
    have m1 : z + Pi.single 1 1 ∈ dualRectangle m n := by
      simp [mem_dualRectangle_iff]; omega
    have m2 : z + Pi.single 1 1 ∈ rectangle m n := by
      simp [mem_rectangle_iff]; omega
    have m3 : z + Pi.single 1 1 + Pi.single 0 1 ∈ rectangle m n := by
      simp [mem_rectangle_iff]; omega
    simp only [bichromaticGraph_adj_iff hz, sepLo_add_e1, sepHi_add_e1, adjU, m1, m2, m3, true_and]
  simp only [n0, n1, n3, y2, if_false, add_zero, zero_add]
  split_ifs with hc <;> simp [hc]

include hz in
/-- Top faces have at most the neighbour below, through the top edge of the rectangle. [folklore] -/
theorem odd_card_filter_adj_top [DecidablePred fun z' => (bichromaticGraph c m n).Adj z z']
    (h1 : z 1 = n) :
    Odd #((nbrs z).filter fun z' => (bichromaticGraph c m n).Adj z z') ↔
      (c z ↔ ¬c (z + Pi.single 0 1)) := by
  classical
  have hzD := mem_dualRectangle_iff.1 hz
  rw [card_filter_nbrs]
  have n0 : ¬(bichromaticGraph c m n).Adj z (z + Pi.single 0 1) := fun h => by
    have := (mem_rectangle_iff.1 h.2.2.2.2.1).2.2.2
    simp at this; omega
  have n1 : ¬(bichromaticGraph c m n).Adj z (z - Pi.single 0 1) := fun h => by
    have := (mem_rectangle_iff.1 h.2.2.2.2.1).2.2.2
    simp at this; omega
  have n2 : ¬(bichromaticGraph c m n).Adj z (z + Pi.single 1 1) := fun h => by
    have := (mem_dualRectangle_iff.1 h.2.2.1).2.2.2
    simp at this; omega
  have y3 : (bichromaticGraph c m n).Adj z (z - Pi.single 1 1) ↔ (c z ↔ ¬c (z + Pi.single 0 1)) := by
    have m1 : z - Pi.single 1 1 ∈ dualRectangle m n := by
      simp [mem_dualRectangle_iff]; omega
    have m2 : z ∈ rectangle m n := by
      simp [mem_rectangle_iff]; omega
    have m3 : z + Pi.single 0 1 ∈ rectangle m n := by
      simp [mem_rectangle_iff]; omega
    simp only [bichromaticGraph_adj_iff hz, sepLo_sub_e1, sepHi_sub_e1, adjD, m1, m2, m3, true_and]
  simp only [n0, n1, n2, y3, if_false, add_zero, zero_add]
  split_ifs with hc <;> simp [hc]

include hz hL hR in
/-- Interior faces have an even number of bichromatic sides in the rectangle (sides on the left or
right side of the rectangle are monochromatic by `hL`, `hR`). [folklore] -/
theorem even_card_filter_adj_interior [DecidablePred fun z' => (bichromaticGraph c m n).Adj z z']
    (h1 : 0 ≤ z 1) (h1' : z 1 + 1 ≤ n) :
    Even #((nbrs z).filter fun z' => (bichromaticGraph c m n).Adj z z') := by
  classical
  have hzD := mem_dualRectangle_iff.1 hz
  rw [card_filter_nbrs]
  have hcorner : z + Pi.single 1 1 + Pi.single 0 1 = z + Pi.single 0 1 + Pi.single 1 1 :=
    add_right_comm _ _ _
  have mz : z ∈ rectangle m n := by simp [mem_rectangle_iff]; omega
  have m0 : z + Pi.single 0 1 ∈ rectangle m n := by simp [mem_rectangle_iff]; omega
  have m01 : z + Pi.single 0 1 + Pi.single 1 1 ∈ rectangle m n := by
    simp [mem_rectangle_iff]; omega
  have m1 : z + Pi.single 1 1 ∈ rectangle m n := by simp [mem_rectangle_iff]; omega
  have y0 : (bichromaticGraph c m n).Adj z (z + Pi.single 0 1) ↔
      (c (z + Pi.single 0 1) ↔ ¬c (z + Pi.single 0 1 + Pi.single 1 1)) := by
    by_cases hx : z 0 + 1 ≤ (m : ℤ) - 1
    · have hD : z + Pi.single 0 1 ∈ dualRectangle m n := by simp [mem_dualRectangle_iff]; omega
      simp only [bichromaticGraph_adj_iff hz, sepLo_add_e0, sepHi_add_e0, adjR, hD, m0, m01,
        true_and]
    · have hD : z + Pi.single 0 1 ∉ dualRectangle m n := by simp [mem_dualRectangle_iff]; omega
      have c1 : ¬c (z + Pi.single 0 1) :=
        cR hR (by simp; omega) (by simp; omega) (by simp; omega)
      have c2 : ¬c (z + Pi.single 0 1 + Pi.single 1 1) :=
        cR hR (by simp; omega) (by simp; omega) (by simp; omega)
      simp only [bichromaticGraph_adj_iff hz, hD, false_and, and_false, c1, c2,
        not_false_eq_true, iff_true, not_false_eq_true]
  have y1 : (bichromaticGraph c m n).Adj z (z - Pi.single 0 1) ↔ (c z ↔ ¬c (z + Pi.single 1 1)) := by
    by_cases hx : 1 ≤ z 0
    · have hD : z - Pi.single 0 1 ∈ dualRectangle m n := by simp [mem_dualRectangle_iff]; omega
      simp only [bichromaticGraph_adj_iff hz, sepLo_sub_e0, sepHi_sub_e0, adjL, hD, mz, m1,
        true_and]
    · have hD : z - Pi.single 0 1 ∉ dualRectangle m n := by simp [mem_dualRectangle_iff]; omega
      have c1 : c z := cL hL (by omega) (by omega) (by omega)
      have c2 : c (z + Pi.single 1 1) := cL hL (by simp; omega) (by simp; omega) (by simp; omega)
      simp only [bichromaticGraph_adj_iff hz, hD, false_and, and_false, c1, c2,
        not_true_eq_false, iff_false]
  have y2 : (bichromaticGraph c m n).Adj z (z + Pi.single 1 1) ↔
      (c (z + Pi.single 1 1) ↔ ¬c (z + Pi.single 0 1 + Pi.single 1 1)) := by
    have hD : z + Pi.single 1 1 ∈ dualRectangle m n := by simp [mem_dualRectangle_iff]; omega
    simp only [bichromaticGraph_adj_iff hz, sepLo_add_e1, sepHi_add_e1, hcorner, adjU, hD, m1,
      m01, true_and]
  have y3 : (bichromaticGraph c m n).Adj z (z - Pi.single 1 1) ↔ (c z ↔ ¬c (z + Pi.single 0 1)) := by
    have hD : z - Pi.single 1 1 ∈ dualRectangle m n := by simp [mem_dualRectangle_iff]; omega
    simp only [bichromaticGraph_adj_iff hz, sepLo_sub_e1, sepHi_sub_e1, adjD, hD, mz, m0,
      true_and]
  simp only [y0, y1, y2, y3]
  exact even_four_sides (c z) (c (z + Pi.single 0 1)) (c (z + Pi.single 0 1 + Pi.single 1 1))
    (c (z + Pi.single 1 1))

end RowLemmas

/-- Degrees in `topGraphF`: interior faces have even degree; a top face `(x₀, n)` has odd degree
iff the top edge `{(x₀, n), (x₀ + 1, n)}` is bichromatic; a bottom face `(x₀, -1)` has odd
degree iff it is joined to the top and the bottom edge `{(x₀, 0), (x₀ + 1, 0)}` is bichromatic. [folklore] -/
theorem odd_degree_topGraphF_iff (hL : ∀ x ∈ leftSide m n, c x) (hR : ∀ x ∈ rightSide m n, ¬c x)
    (v : DFace m n) [Fintype ((topGraphF c m n).neighborSet v)] :
    Odd ((topGraphF c m n).degree v) ↔
      ((v : LatticeModels.Site 2) 1 = n ∧ (c v ↔ ¬c ((v : LatticeModels.Site 2) + Pi.single 0 1))) ∨
      ((v : LatticeModels.Site 2) 1 = -1 ∧ TopReach c m n v ∧
        (c ((v : LatticeModels.Site 2) + Pi.single 1 1) ↔ ¬c ((v : LatticeModels.Site 2) + Pi.single 1 1 + Pi.single 0 1))) := by
  classical
  obtain ⟨z, hz⟩ := v
  rw [degree_topGraphF]
  simp only
  have hzD := (mem_dualRectangle_iff.1 hz)
  by_cases hreach : TopReach c m n z
  swap
  · -- not joined to the top: isolated, and not a top face
    have h0 : ((nbrs z).filter fun z' => (topGraph c m n).Adj z z') = ∅ :=
      Finset.filter_false_of_mem fun z' _ h => hreach h.2.1
    rw [h0, Finset.card_empty]
    constructor
    · intro h; exact absurd h (by decide)
    · rintro (⟨h1, -⟩ | ⟨-, h, -⟩)
      · exact absurd ⟨z, by simp [dualTopSide, hz, h1], Reachable.refl _⟩ hreach
      · exact absurd h hreach
  have hfilter : ((nbrs z).filter fun z' => (topGraph c m n).Adj z z') =
      (nbrs z).filter fun z' => (bichromaticGraph c m n).Adj z z' :=
    Finset.filter_congr fun z' _ => topGraph_adj_iff_of_topReach hreach
  rw [hfilter]
  simp only [hreach, true_and]
  rcases lt_trichotomy (z 1) (-1) with h | h | h
  · omega
  · rw [odd_card_filter_adj_bottom hz h]
    have : ¬((-1 : ℤ) = n) := by omega
    simp only [this, false_and, false_or, h, true_and]
  · rcases lt_or_ge (z 1) n with h' | h'
    · have hzn : ¬(z 1 = n) := by omega
      have hzm : ¬(z 1 = -1) := by omega
      simp only [hzn, hzm, false_and, or_self, iff_false, Nat.not_odd_iff_even]
      exact even_card_filter_adj_interior hz hL hR (by omega) (by omega)
    · have hzn : z 1 = n := by omega
      rw [odd_card_filter_adj_top hz hzn]
      have : ¬((n : ℤ) = -1) := by omega
      simp only [this, false_and, or_false, hzn, true_and]

/-- The number of top faces with a bichromatic top edge equals the number of colour changes
along the top row of the rectangle. [folklore] -/
theorem card_top_bichromatic [DecidablePred c] :
    #(Finset.univ.filter fun v : DFace m n =>
        (v : LatticeModels.Site 2) 1 = n ∧ (c v ↔ ¬c ((v : LatticeModels.Site 2) + Pi.single 0 1))) =
      #((Finset.range m).filter fun k : ℕ => (c ![(k : ℤ), n] ↔ ¬c ![(k : ℤ) + 1, n])) := by
  symm
  refine Finset.card_bij' (fun k hk => ⟨![(k : ℤ), n], ?_⟩) (fun v _ => ((v : LatticeModels.Site 2) 0).toNat)
    ?_ ?_ ?_ ?_
  · have hk := (Finset.mem_filter.1 hk).1
    rw [Finset.mem_range] at hk
    simp only [mem_dualRectangle_iff, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    omega
  · intro k hk
    obtain ⟨hk, hc⟩ := Finset.mem_filter.1 hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    have he : (![(k : ℤ), n] : LatticeModels.Site 2) + Pi.single 0 1 = ![(k : ℤ) + 1, n] := by
      refine LatticeModels.Site.eq_iff_two.2 ⟨?_, ?_⟩ <;> simp
    rw [he]
    exact hc
  · rintro ⟨v, hv⟩ h
    obtain ⟨-, h1, hc⟩ := Finset.mem_filter.1 h
    have hvD := mem_dualRectangle_iff.1 hv
    simp only at h1 hc
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    have h0 : ((v 0).toNat : ℤ) = v 0 := Int.toNat_of_nonneg hvD.1
    have hv1 : (![((v 0).toNat : ℤ), n] : LatticeModels.Site 2) = v := by
      simp [LatticeModels.Site.eq_iff_two, h0, h1]
    have hv2 : (![((v 0).toNat : ℤ) + 1, n] : LatticeModels.Site 2) = v + Pi.single 0 1 := by
      simp [LatticeModels.Site.eq_iff_two, h0, h1]
    rw [hv1, hv2]
    exact hc
  · intro k hk
    simp
  · rintro ⟨v, hv⟩ h
    obtain ⟨-, h1, -⟩ := Finset.mem_filter.1 h
    have hvD := mem_dualRectangle_iff.1 hv
    simp only at h1
    apply Subtype.ext
    simp [LatticeModels.Site.eq_iff_two, Int.toNat_of_nonneg hvD.1, h1]

/-- **The parity lemma.** If the left side of `[0, m] × [0, n]` is coloured and the right side is
not, then some bottom face of the dual rectangle is joined to a top face by a path of faces each
step of which crosses a bichromatic edge of the rectangle. (Handshake lemma in `topGraphF`; the
combinatorial core of the "if" direction of Bollobás–Riordan 2006, Ch. 3, Lemma 1.) [folklore] -/
theorem exists_topReach_dualBottomSide (hL : ∀ x ∈ leftSide m n, c x)
    (hR : ∀ x ∈ rightSide m n, ¬c x) : ∃ v ∈ dualBottomSide m n, TopReach c m n v := by
  classical
  -- odd number of colour changes along the top row
  have hodd : Odd #((Finset.range m).filter fun k : ℕ => (c ![(k : ℤ), n] ↔ ¬c ![(k : ℤ) + 1, n])) := by
    rw [← Nat.not_even_iff_odd]
    have h := even_card_changes_iff (fun k : ℕ => c ![(k : ℤ), n]) m
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] at h
    rw [h]
    have h0 : c ![(0 : ℤ), n] := hL _ (by simp [leftSide, mem_rectangle_iff])
    have hm : ¬c ![(m : ℤ), n] := hR _ (by simp [rightSide, mem_rectangle_iff])
    tauto
  -- handshake in `topGraphF`
  have hand := (topGraphF c m n).even_card_odd_degree_vertices
  set T := Finset.univ.filter fun v : DFace m n =>
    (v : LatticeModels.Site 2) 1 = n ∧ (c v ↔ ¬c ((v : LatticeModels.Site 2) + Pi.single 0 1)) with hT
  set B := Finset.univ.filter fun v : DFace m n =>
    (v : LatticeModels.Site 2) 1 = -1 ∧ TopReach c m n v ∧
      (c ((v : LatticeModels.Site 2) + Pi.single 1 1) ↔ ¬c ((v : LatticeModels.Site 2) + Pi.single 1 1 + Pi.single 0 1)) with hB
  have hO : (Finset.univ.filter fun v : DFace m n => Odd ((topGraphF c m n).degree v)) = T ∪ B := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, hT, hB]
    exact odd_degree_topGraphF_iff hL hR v
  have hdisj : Disjoint T B := by
    rw [Finset.disjoint_left]
    intro v hvT hvB
    have h1 := (Finset.mem_filter.1 hvT).2.1
    have h2 := (Finset.mem_filter.1 hvB).2.1
    omega
  rw [hO, Finset.card_union_of_disjoint hdisj, hT, card_top_bichromatic] at hand
  have hBodd : Odd #B := by
    rcases Nat.even_or_odd #B with h | h
    · exact absurd hand (Nat.not_even_iff_odd.2 (hodd.add_even h))
    · exact h
  obtain ⟨v, hv⟩ : B.Nonempty := Finset.card_pos.1 hBodd.pos
  obtain ⟨-, h1, hreach, -⟩ := Finset.mem_filter.1 hv
  exact ⟨v, by simp [dualBottomSide, v.2, h1], hreach⟩

end Parity

/-! ### The duality lemma -/

section Duality

variable {m n : ℕ} {ω : BondConfig (LatticeModels.Site 2)}

/-- The colouring used in the proof of the duality lemma: `x` is joined to the left side of
`[0, m] × [0, n]` by an open path of the rectangle. (Bollobás–Riordan 2006, Ch. 3, proof of
Lemma 1: the set of sites joined to the left side.) [folklore] -/
def LeftJoined (m n : ℕ) (ω : BondConfig (LatticeModels.Site 2)) (x : LatticeModels.Site 2) : Prop :=
  ∃ l ∈ leftSide m n, ω ∈ openConnIn (↑(rectangle m n)) l x

/-- An edge of the rectangle whose endpoints differ in `LeftJoined` is closed. [folklore] -/
theorem sepEdge_notMem_of_bichromatic {z z' : LatticeModels.Site 2} (hadj : (LatticeModels.zdGraph 2).Adj z z')
    (hB : Bichromatic (LeftJoined m n ω) m n z z') : sepEdge z z' ∉ ω := by
  intro he
  obtain ⟨hlo, hhi, hc⟩ := hB
  have hne : sepLo z z' ≠ sepHi z z' := ((LatticeModels.zdGraph 2).mem_edgeSet.1 (sepEdge_mem_edgeSet hadj)).ne
  have h1 : ω ∈ openConnIn (↑(rectangle m n)) (sepLo z z') (sepHi z z') :=
    openConnIn_of_adj hlo hhi he hne
  have h2 : ω ∈ openConnIn (↑(rectangle m n)) (sepHi z z') (sepLo z z') := by
    rw [openConnIn_comm]; exact h1
  have : LeftJoined m n ω (sepLo z z') ↔ LeftJoined m n ω (sepHi z z') :=
    ⟨fun ⟨l, hl, h⟩ => ⟨l, hl, PlanarDuality.openConnIn_trans h h1⟩, fun ⟨l, hl, h⟩ => ⟨l, hl, PlanarDuality.openConnIn_trans h h2⟩⟩
  tauto

/-- The dual edge crossing a bichromatic edge is dual-open (for lattice configurations).
(Bollobás–Riordan 2006, Ch. 3, proof of Lemma 1.) [folklore] -/
theorem mem_dualConfig_of_bichromatic (hω : ω ⊆ (LatticeModels.zdGraph 2).edgeSet) {z z' : LatticeModels.Site 2}
    (hadj : (LatticeModels.zdGraph 2).Adj z z') (hB : Bichromatic (LeftJoined m n ω) m n z z') :
    s(z, z') ∈ dualConfig ω := by
  rw [mem_dualConfig_iff]
  refine ⟨hadj, fun e' he' heq => ?_⟩
  rw [← dualEdge_sepEdge hadj] at heq
  have := dualEdge_injOn_holds (hω he') (sepEdge_mem_edgeSet hadj) heq
  exact sepEdge_notMem_of_bichromatic hadj hB (this ▸ he')

/-- A path in `bichromaticGraph` for the colouring `LeftJoined` is a dual-open path of the dual
rectangle. [folklore] -/
theorem dualConfig_mem_openConnIn_of_reachable (hω : ω ⊆ (LatticeModels.zdGraph 2).edgeSet) {t v : LatticeModels.Site 2}
    (ht : t ∈ dualRectangle m n) (h : (bichromaticGraph (LeftJoined m n ω) m n).Reachable t v) :
    dualConfig ω ∈ openConnIn (↑(dualRectangle m n)) t v := by
  obtain ⟨W⟩ := h
  induction W with
  | nil => exact openConnIn_refl ht
  | cons hadj W ih =>
    obtain ⟨hzz', hzD, hz'D, hB⟩ := hadj
    exact PlanarDuality.openConnIn_trans (openConnIn_of_adj hzD hz'D (mem_dualConfig_of_bichromatic hω hzz' hB)
      hzz'.ne) (ih hz'D)

/-- **Discharge of `lrCrossing_xor_dualTBCrossing`** (planar duality lemma; Bollobás–Riordan,
*Percolation* (2006), Ch. 3, Lemma 1; Grimmett, *Percolation* (1999), §11.2; Kesten 1982,
Prop. 2.2). For every lattice configuration `ω ⊆ E(ℤ²)`, exactly one of `LR([0, m] × [0, n])` and
the dual top-bottom crossing `TB*` of `[½, m - ½] × [-½, n + ½]` occurs. "Not both" by the winding
number of the open crossing (`exists_dart_sepEdge_mem_edges` with `dualEdge_sepEdge`); "at least
one" by the parity lemma `exists_topReach_dualBottomSide` for the colouring `LeftJoined`.
[cite: BollobasRiordanPercolation2006, Ch. 3, Lemma 1] [cite: GrimmettPercolation1999, §11.2] -/
theorem lrCrossing_xor_dualTBCrossing_holds : lrCrossing_xor_dualTBCrossing := by
  intro m n ω hω
  by_cases hlr : ω ∈ lrCrossing m n
  · refine Or.inl ⟨hlr, fun hd => ?_⟩
    obtain ⟨x, hx, y, hy, hxy⟩ := hlr
    obtain ⟨P, hPS, hPω⟩ := exists_walk_of_mem_openConnIn hω hxy
    obtain ⟨t, ht, s, hs, hts⟩ := (mem_openCrossing_iff.1 hd :)
    obtain ⟨Q, hQS, hQω⟩ :=
      exists_walk_of_mem_openConnIn (fun _ h => h.1 : dualConfig ω ⊆ (LatticeModels.zdGraph 2).edgeSet) hts
    simp only [Finset.mem_coe, leftSide, rightSide, Finset.mem_filter] at hx hy
    simp only [Finset.mem_coe, dualTopSide, dualBottomSide, Finset.mem_filter] at ht hs
    obtain ⟨dq, hdq, he⟩ := exists_dart_sepEdge_mem_edges (M := m) (N := n) P Q
      (fun z hz => mem_rectangle_iff.1 (hPS z hz))
      (fun z hz => by have := mem_dualRectangle_iff.1 (hQS z hz); omega) hx.2 hy.2 ht.2 hs.2
    have hdual : s(dq.fst, dq.snd) ∈ dualConfig ω := hQω _ (by
      rw [Walk.edges]; exact List.mem_map.2 ⟨dq, hdq, rfl⟩)
    exact (mem_dualConfig_iff.1 hdual).2 _ (hPω _ he) (dualEdge_sepEdge dq.adj)
  · refine Or.inr ⟨?_, hlr⟩
    have hL : ∀ x ∈ leftSide m n, LeftJoined m n ω x := fun x hx =>
      ⟨x, hx, openConnIn_refl (Finset.mem_coe.2 (Finset.mem_filter.1 hx).1)⟩
    have hR : ∀ x ∈ rightSide m n, ¬LeftJoined m n ω x := fun x hx ⟨l, hl, h⟩ =>
      hlr ⟨l, hl, x, hx, h⟩
    obtain ⟨v, hv, t, ht, hreach⟩ := exists_topReach_dualBottomSide hL hR
    have htD : t ∈ dualRectangle m n := (Finset.mem_filter.1 ht).1
    exact ⟨t, ht, v, hv, dualConfig_mem_openConnIn_of_reachable hω htD hreach⟩

/-- **Discharge of `crossingProb_add_real_dualTBCrossing`**: `P_p(LR(m, n)) + P_p(TB*(m, n)) = 1`,
since `P_p`-almost every configuration is a lattice configuration, for which exactly one of the two
events occurs (`lrCrossing_xor_dualTBCrossing_holds`), and both events are measurable.
(Grimmett 1999, §11.2; Bollobás–Riordan 2006, Ch. 3, Cor. 3(i) in the form before the dual event is
rewritten as a crossing of the rotated rectangle.) [cite: GrimmettPercolation1999, §11.2] -/
theorem crossingProb_add_real_dualTBCrossing_holds : crossingProb_add_real_dualTBCrossing := by
  intro p m n
  set μ := bondPercolation (LatticeModels.zdGraph 2) p
  have hae : ∀ᵐ ω ∂μ, ω ⊆ (LatticeModels.zdGraph 2).edgeSet := ProbabilityTheory.setBernoulli_ae_subset
  have hunion : μ.real (lrCrossing m n ∪ dualTBCrossing m n) = 1 := by
    rw [← probReal_univ (μ := μ)]
    refine measureReal_congr (ae_eq_univ.2 ?_)
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hae] with ω hω hn
    rcases lrCrossing_xor_dualTBCrossing_holds m n hω with h | h
    · exact hn (Or.inl h.1)
    · exact hn (Or.inr h.1)
  have hinter : μ.real (lrCrossing m n ∩ dualTBCrossing m n) = 0 := by
    rw [measureReal_def, measure_eq_zero_iff_ae_notMem.2, ENNReal.toReal_zero]
    filter_upwards [hae] with ω hω hn
    rcases lrCrossing_xor_dualTBCrossing_holds m n hω with h | h
    · exact h.2 hn.2
    · exact h.2 hn.1
  have := measureReal_union_add_inter (μ := μ) (s := lrCrossing m n) (measurableSet_dualTBCrossing m n)
  rw [hunion, hinter, add_zero] at this
  rw [crossingProb]
  exact this.symm

end Duality

end

end Percolation.Literature
