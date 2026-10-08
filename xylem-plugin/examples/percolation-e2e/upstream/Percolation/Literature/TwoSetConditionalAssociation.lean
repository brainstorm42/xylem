import Percolation.Literature.KozmaNitzanPinning
import Percolation.Literature.TripodExchange
import Percolation.Util.Linter

/-!
# van den Berg–Häggström–Kahn (2006): Theorem 1.5 with vertex SETS `S, T` (= Theorem 2.1 at `q = 1`, Remark 1 after Theorem 1.2) — proved, with the set forms of the cluster-event / tripod exchange inequalities

Companion of `TwoClusterConditionalAssociation.lean`
(Thm. 1.5 for two VERTICES `s, t`, proved in `TwoClusterConditionalAssociationProofs.lean`) and
of `TripodExchange.lean` (the exchange inequalities (C⁺), (C⁺_gen) for vertices `x, y`).  Bond
percolation with arbitrary edge probabilities `w` on a finite vertex type `V`
(`μ = prodBernoulli w` on `BondConfig V = Set (Sym2 V)`); for a set of vertices `S` write
`C_S = ⋃_{s ∈ S} C_s` (`C_s = openEdgeCluster ω s`; BHK p. 9: "we use `C_S` for the set of edges
belonging to open paths starting at vertices of `S`") and `{S ↮ T} = {∀ s ∈ S, ∀ t ∈ T, s ↮ t}`.

## What is printed, and what is proved here

* [VandenbergHaggstromKahn2005, Remark 1 after Thm. 1.2 (arXiv p. 4 / RSA p. 5)]: "It is easy to
  see that Theorem (1.2) is equivalent to the special case where `|X| = 1`. (To reduce to this,
  simply identify the vertices of `X`, retaining all edges connecting them to `V ∖ X` (edges
  internal to `X` may be deleted, but are anyway irrelevant).) … Similarly, we could replace `s` in
  all results of this section, and `t` in Theorems (1.4) and (1.5), by sets of vertices."
* [VandenbergHaggstromKahn2005, Thm. 2.1 (arXiv p. 6 / RSA p. 9)]: "Consider a distribution (rcdef)
  [the random-cluster measure `φ_{G,p,q}`] with `q ≥ 1`. Let `S` and `T` be disjoint sets of
  vertices, and `f` and `g` bounded, measurable functions of `(C_S, C_T)`, each increasing in `C_S`
  and decreasing in `C_T`. Then on `{S ↛ T}`, `E f g ≥ E f E g`." At `q = 1` the random-cluster
  measure is the product measure, so this is Theorem 1.5 with sets.

`BHK2006_twoSetConditionalAssociation` — Theorem 2.1 at `q = 1` (equivalently Thm. 1.5 with
`s, t` replaced by sets `S, T`), in the same denominator-free form as Thm. 1.5:
`(∫_D f dμ)(∫_D g dμ) ≤ μ(D) · ∫_D f g dμ`, `D = {S ↮ T}`, `f = F(C_S, C_T)`, `g = G(C_S, C_T)` with
`F, G` monotone in the first and antitone in the second argument.  Proved here (no new statement is
introduced); the `q > 1` part of Thm. 2.1 (random-cluster measures) is NOT formalised here.  The
disjointness of `S, T` is not needed in the statement: if `S ∩ T ≠ ∅` then `D = ∅` and both
sides vanish.

## The proof (BHK's reduction, Remark 1)

BHK reduce sets to singletons by identifying the vertices of the set.  On a FIXED configuration
space the same reduction is the following "hub" construction, which keeps the law of the old
edges literally: pass to the vertex type `V ⊕ Bool` with two new vertices, the hubs
`s* = inr true` and `t* = inr false`; give the old pair `e.map inl` the weight `w e`, the hub
edges `{inl u, s*}` (`u ∈ S`) and `{inl u, t*}` (`u ∈ T`) the weight `1`, and every other new pair
the weight `0` (`hubWeight`).  Then

* the law of the hub model is the image of `μ` under `ω ↦ hubConfig ω = (inl″ω) ∪ hub edges`
  (`prodBernoulli_hubWeight_eq_map`: the restriction to the old pairs has law `μ`,
  `prodBernoulli_map_restrictConfig`, and almost surely every weight-`1` pair is open and every
  weight-`0` pair closed), so integrals over events of the hub model are integrals over `μ`
  (`setIntegral_hub`, `measureReal_hub`);
* `{s* ↮ t*}` pulls back to `{S ↮ T}` (`hubConfig_preimage_not_reachable`), and on `{S ↮ T}` the
  clusters of the hubs, read on the old pairs, are `C_S` and `C_T`
  (`restrictConfig_openEdgeCluster_hub`; the point is that an open path from `s*` cannot pass
  through `t*`, so it consists of one hub edge followed by an old open path —
  `hubSide_closed`, a closed-set argument);
* a function of the restricted pair of clusters that is monotone/antitone stays so, hence
  Theorem 1.5 (`BHK2006_twoClusterConditionalAssociation_holds`) for `s*, t*` on `V ⊕ Bool`
  transports to the statement for `S, T` on `V`.

## Corollaries (same file)

* `BHK2006_twoSetConditionalAssociation.negCorrelation` — Thm. 1.4 with sets (the form quoted by
  Kozma–Nitzan, arXiv:2401.12397 §2.2 p. 5, "if `f` and `g` are two increasing functions defined on
  the clusters of `A` and `B` respectively then `E(fg | A ↮ B) ≤ E(f | A ↮ B) E(g | A ↮ B)`");

## References

* J. van den Berg, O. Häggström, J. Kahn, *Some conditional correlation inequalities for
  percolation and related processes*, Random Structures Algorithms 29 (2006) 417–435
  (arXiv:math/0408176): Remark 1 after Thm. 1.2 (p. 5), Thm. 1.5 (p. 7), Thm. 2.1 (p. 9).
  [VandenbergHaggstromKahn2005]
* G. Kozma, S. Nitzan, *A reduction of the θ(p_c) = 0 problem to a conjectured inequality*,
  arXiv:2401.12397 (2024), §2.2 p. 5 (the set form of BHK as used there). [KozmaNitzan2024]
-/

noncomputable section

open MeasureTheory Set
open Percolation.Literature.LatticeModels (prodBernoulli)

namespace Percolation.Literature

variable {V : Type*}

namespace TwoSetConditionalAssociation

/-! ### The hub graph on `V ⊕ Bool` -/

/-- The two blocks as a `Bool`-indexed family: `sides S T true = S`, `sides S T false = T`. [folklore] -/
def sides (S T : Set V) : Bool → Set V := fun b => cond b S T

/-- `sides S T true = S`. [folklore] -/
@[simp] theorem sides_true (S T : Set V) : sides S T true = S := rfl

/-- `sides S T false = T`. [folklore] -/
@[simp] theorem sides_false (S T : Set V) : sides S T false = T := rfl

/-- The hub edges: the pairs `{inl u, inr b}` with `u ∈ side b` (each vertex of the block `side b`
is joined to the hub vertex `inr b`). [folklore] -/
def hubEdges (side : Bool → Set V) : Set (Sym2 (V ⊕ Bool)) :=
  {e' | ∃ (b : Bool) (u : V), u ∈ side b ∧ e' = s(Sum.inl u, Sum.inr b)}

/-- The augmented configuration on `V ⊕ Bool`: the old open edges, pushed forward along `inl`,
together with all hub edges. [folklore] -/
def hubConfig (side : Bool → Set V) (ω : BondConfig V) : BondConfig (V ⊕ Bool) :=
  Sym2.map Sum.inl '' ω ∪ hubEdges side

open Classical in
/-- The augmented weights: `w e` on the old pair `e.map inl`, `1` on hub edges, `0` on every other
pair of `V ⊕ Bool`. [folklore] -/
def hubWeight (w : Sym2 V → unitInterval) (side : Bool → Set V) (e' : Sym2 (V ⊕ Bool)) :
    unitInterval :=
  if h : ∃ e : Sym2 V, Sym2.map Sum.inl e = e' then w h.choose
  else if e' ∈ hubEdges side then 1 else 0

/-- A hub vertex is not an endpoint of (the image of) an old pair. [folklore] -/
theorem inr_not_mem_map_inl (e : Sym2 V) (b : Bool) :
    Sum.inr b ∉ Sym2.map (Sum.inl : V → V ⊕ Bool) e := by
  rw [Sym2.mem_map]
  rintro ⟨v, -, hv⟩
  exact Sum.inl_ne_inr hv

/-- The image of an old pair is not a hub edge. [folklore] -/
theorem map_inl_not_mem_hubEdges (side : Bool → Set V) (e : Sym2 V) :
    Sym2.map Sum.inl e ∉ hubEdges side := by
  rintro ⟨b, u, -, he⟩
  have h : Sum.inr b ∈ Sym2.map (Sum.inl : V → V ⊕ Bool) e := by
    rw [he]; exact Sym2.mem_mk_right _ _
  exact inr_not_mem_map_inl e b h

/-- `hubWeight` restricted to the old pairs is `w`. [folklore] -/
theorem hubWeight_map_inl (w : Sym2 V → unitInterval) (side : Bool → Set V) (e : Sym2 V) :
    hubWeight w side (Sym2.map Sum.inl e) = w e := by
  classical
  unfold hubWeight
  have h : ∃ e₀ : Sym2 V, Sym2.map (Sum.inl : V → V ⊕ Bool) e₀ = Sym2.map Sum.inl e := ⟨e, rfl⟩
  rw [dif_pos h, Sym2.map.injective Sum.inl_injective h.choose_spec]

/-- Hub edges have weight `1`. [folklore] -/
theorem hubWeight_of_mem_hubEdges (w : Sym2 V → unitInterval) {side : Bool → Set V}
    {e' : Sym2 (V ⊕ Bool)} (he' : e' ∈ hubEdges side) : hubWeight w side e' = 1 := by
  classical
  unfold hubWeight
  have h : ¬ ∃ e : Sym2 V, Sym2.map Sum.inl e = e' := by
    rintro ⟨e, rfl⟩
    exact map_inl_not_mem_hubEdges side e he'
  rw [dif_neg h, if_pos he']

/-- The remaining new pairs have weight `0`. [folklore] -/
theorem hubWeight_eq_zero (w : Sym2 V → unitInterval) {side : Bool → Set V}
    {e' : Sym2 (V ⊕ Bool)} (h₁ : ¬ ∃ e : Sym2 V, Sym2.map Sum.inl e = e')
    (h₂ : e' ∉ hubEdges side) : hubWeight w side e' = 0 := by
  classical
  unfold hubWeight
  rw [dif_neg h₁, if_neg h₂]

/-- `hubWeight ∘ Sym2.map inl = w`. [folklore] -/
theorem hubWeight_comp_map_inl (w : Sym2 V → unitInterval) (side : Bool → Set V) :
    hubWeight w side ∘ Sym2.map Sum.inl = w :=
  funext (hubWeight_map_inl w side)

/-! ### The law of the hub configuration -/

/-- Membership in the augmented configuration. [folklore] -/
theorem mem_hubConfig_iff (side : Bool → Set V) (ω : BondConfig V) (e' : Sym2 (V ⊕ Bool)) :
    e' ∈ hubConfig side ω ↔ (∃ e ∈ ω, Sym2.map Sum.inl e = e') ∨ e' ∈ hubEdges side :=
  Iff.rfl

/-- The old pair `e` is open in the augmented configuration iff it is open. [folklore] -/
theorem map_inl_mem_hubConfig_iff (side : Bool → Set V) (ω : BondConfig V) (e : Sym2 V) :
    Sym2.map Sum.inl e ∈ hubConfig side ω ↔ e ∈ ω := by
  constructor
  · rintro (⟨e₀, he₀, hee⟩ | hhub)
    · rwa [← Sym2.map.injective Sum.inl_injective hee]
    · exact absurd hhub (map_inl_not_mem_hubEdges side e)
  · exact fun he => Or.inl ⟨e, he, rfl⟩

/-- **Marginal on the old pairs**: the restriction of `prodBernoulli (hubWeight w side)` along
`inl` has law `prodBernoulli w`. [folklore] -/
theorem map_restrictConfig_prodBernoulli_hubWeight (w : Sym2 V → unitInterval)
    (side : Bool → Set V) :
    (prodBernoulli (hubWeight w side)).map (restrictConfig Sum.inl) = prodBernoulli w := by
  rw [prodBernoulli_map_restrictConfig _ Sum.inl_injective, hubWeight_comp_map_inl]

/-- **Almost surely the new pairs are deterministic**: under `prodBernoulli (hubWeight w side)` the
configuration is (a.s.) the augmentation of its restriction to the old pairs (hub edges have weight
`1`, the other new pairs weight `0`). [folklore] -/
theorem ae_hubConfig_restrictConfig_eq [Fintype V] (w : Sym2 V → unitInterval)
    (side : Bool → Set V) :
    ∀ᵐ ω' ∂(prodBernoulli (hubWeight w side)), hubConfig side (restrictConfig Sum.inl ω') = ω' := by
  have hall : ∀ e' : Sym2 (V ⊕ Bool), ∀ᵐ ω' ∂(prodBernoulli (hubWeight w side)),
      (e' ∈ hubEdges side → e' ∈ ω') ∧
        ((¬ ∃ e : Sym2 V, Sym2.map Sum.inl e = e') → e' ∉ hubEdges side → e' ∉ ω') := by
    intro e'
    by_cases hhub : e' ∈ hubEdges side
    · filter_upwards [prodBernoulli_ae_mem_of_eq_one (hubWeight w side)
        (hubWeight_of_mem_hubEdges w hhub)] with ω' h
      exact ⟨fun _ => h, fun _ h₂ => absurd hhub h₂⟩
    · by_cases himg : ∃ e : Sym2 V, Sym2.map Sum.inl e = e'
      · exact Filter.Eventually.of_forall fun ω' =>
          ⟨fun h => absurd h hhub, fun h => absurd himg h⟩
      · filter_upwards [LatticeModels.prodBernoulli_ae_notMem (hubWeight w side)
          (hubWeight_eq_zero w himg hhub)] with ω' h
        exact ⟨fun h' => absurd h' hhub, fun _ _ => h⟩
  rw [← ae_all_iff] at hall
  filter_upwards [hall] with ω' h
  ext e'
  rw [mem_hubConfig_iff]
  constructor
  · rintro (⟨e, he, rfl⟩ | hhub)
    · exact he
    · exact (h e').1 hhub
  · intro he'
    by_cases hhub : e' ∈ hubEdges side
    · exact Or.inr hhub
    by_cases himg : ∃ e : Sym2 V, Sym2.map Sum.inl e = e'
    · obtain ⟨e, rfl⟩ := himg
      exact Or.inl ⟨e, he', rfl⟩
    · exact absurd he' ((h e').2 himg hhub)

/-- **The law of the hub configuration**: `prodBernoulli (hubWeight w side)` is the image of
`prodBernoulli w` under `ω ↦ hubConfig side ω`. [folklore] -/
theorem prodBernoulli_hubWeight_eq_map [Fintype V] (w : Sym2 V → unitInterval)
    (side : Bool → Set V) :
    prodBernoulli (hubWeight w side) = (prodBernoulli w).map (hubConfig side) := by
  have hres : Measurable (restrictConfig (Sum.inl : V → V ⊕ Bool)) := measurable_restrictConfig _
  have haug : Measurable (hubConfig side : BondConfig V → BondConfig (V ⊕ Bool)) :=
    Measurable.of_discrete
  calc prodBernoulli (hubWeight w side)
      = (prodBernoulli (hubWeight w side)).map id := Measure.map_id.symm
    _ = (prodBernoulli (hubWeight w side)).map (hubConfig side ∘ restrictConfig Sum.inl) :=
        Measure.map_congr (by
          filter_upwards [ae_hubConfig_restrictConfig_eq w side] with ω' h using h.symm)
    _ = ((prodBernoulli (hubWeight w side)).map (restrictConfig Sum.inl)).map (hubConfig side) :=
        (Measure.map_map haug hres).symm
    _ = (prodBernoulli w).map (hubConfig side) := by
        rw [map_restrictConfig_prodBernoulli_hubWeight]

/-- Transport of set integrals to the original space. [folklore] -/
theorem setIntegral_hub [Fintype V] (w : Sym2 V → unitInterval) (side : Bool → Set V)
    (Φ : BondConfig (V ⊕ Bool) → ℝ) (D' : Set (BondConfig (V ⊕ Bool))) :
    ∫ ω' in D', Φ ω' ∂(prodBernoulli (hubWeight w side)) =
      ∫ ω in hubConfig side ⁻¹' D', Φ (hubConfig side ω) ∂(prodBernoulli w) := by
  rw [prodBernoulli_hubWeight_eq_map]
  exact setIntegral_map MeasurableSet.of_discrete
    (Measurable.of_discrete (f := Φ)).aestronglyMeasurable
    (Measurable.of_discrete (f := hubConfig side)).aemeasurable

/-- Transport of probabilities to the original space. [folklore] -/
theorem measureReal_hub [Fintype V] (w : Sym2 V → unitInterval) (side : Bool → Set V)
    (D' : Set (BondConfig (V ⊕ Bool))) :
    (prodBernoulli (hubWeight w side)).real D' = (prodBernoulli w).real (hubConfig side ⁻¹' D') := by
  rw [prodBernoulli_hubWeight_eq_map,
    map_measureReal_apply (Measurable.of_discrete (f := hubConfig side)) MeasurableSet.of_discrete]

/-! ### Reachability in the hub configuration -/

/-- Old open edges stay open edges between the old vertices. [folklore] -/
theorem hubConfig_adj_inl (side : Bool → Set V) {ω : BondConfig V} {u v : V}
    (h : (openGraph ω).Adj u v) :
    (openGraph (hubConfig side ω)).Adj (Sum.inl u) (Sum.inl v) := by
  rw [openGraph_adj] at h ⊢
  have h1 := (map_inl_mem_hubConfig_iff side ω s(u, v)).2 h.1
  rw [Sym2.map_mk] at h1
  exact ⟨h1, fun h' => h.2 (Sum.inl_injective h')⟩

/-- Old open paths stay open paths. [folklore] -/
theorem hubConfig_reachable_inl (side : Bool → Set V) {ω : BondConfig V} {u v : V}
    (h : (openGraph ω).Reachable u v) :
    (openGraph (hubConfig side ω)).Reachable (Sum.inl u) (Sum.inl v) :=
  h.map { toFun := Sum.inl, map_rel' := fun hab => hubConfig_adj_inl side hab }

/-- The hub `inr b` is adjacent to every vertex of its block. [folklore] -/
theorem hubConfig_adj_hub (side : Bool → Set V) (ω : BondConfig V) {b : Bool} {u : V}
    (hu : u ∈ side b) : (openGraph (hubConfig side ω)).Adj (Sum.inr b) (Sum.inl u) := by
  rw [openGraph_adj]
  exact ⟨Or.inr ⟨b, u, hu, Sym2.eq_swap⟩, Sum.inr_ne_inl⟩

/-- A vertex joined to the block `side b` is joined to the hub `inr b`. [folklore] -/
theorem hubConfig_reachable_hub_inl (side : Bool → Set V) (ω : BondConfig V) {b : Bool} {s v : V}
    (hs : s ∈ side b) (h : (openGraph ω).Reachable s v) :
    (openGraph (hubConfig side ω)).Reachable (Sum.inr b) (Sum.inl v) :=
  (hubConfig_adj_hub side ω hs).reachable.trans (hubConfig_reachable_inl side h)

/-- A set of vertices closed under adjacency contains everything reachable from it. [folklore] -/
theorem mem_of_reachable_of_closed {α : Type*} {G : SimpleGraph α} {W : Set α}
    (hW : ∀ ⦃a b : α⦄, a ∈ W → G.Adj a b → b ∈ W) {a b : α} (ha : a ∈ W)
    (h : G.Reachable a b) : b ∈ W := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact ha
  | tail _ hbc ih => exact hW ih hbc

/-- **The hub side is closed.** If no vertex of `side b` is joined to a vertex of `side (!b)`,
then the set `{inl v | v joined to side b} ∪ {inr b}` is closed under adjacency in the hub
configuration (the only edges leaving it would be hub edges at `inr (!b)`, whose old endpoint lies
in `side (!b)`). [folklore] -/
theorem hubSide_closed (side : Bool → Set V) (ω : BondConfig V) (b : Bool)
    (hsep : ∀ s ∈ side b, ∀ t ∈ side (!b), ¬ (openGraph ω).Reachable s t) ⦃x y : V ⊕ Bool⦄
    (hx : x ∈ {x : V ⊕ Bool |
      (∃ v : V, x = Sum.inl v ∧ ∃ s ∈ side b, (openGraph ω).Reachable s v) ∨ x = Sum.inr b})
    (hxy : (openGraph (hubConfig side ω)).Adj x y) :
    y ∈ {x : V ⊕ Bool |
      (∃ v : V, x = Sum.inl v ∧ ∃ s ∈ side b, (openGraph ω).Reachable s v) ∨ x = Sum.inr b} := by
  rw [openGraph_adj, mem_hubConfig_iff] at hxy
  obtain ⟨⟨e, he, hexy⟩ | ⟨b', u, hu, hexy⟩, hne⟩ := hxy
  · -- an old open edge `e = s(u, v)` with `{x, y} = {inl u, inl v}`
    have key : ∀ {u v : V}, s(u, v) ∈ ω → Sum.inl u = x → Sum.inl v = y →
        y ∈ {x : V ⊕ Bool |
          (∃ v : V, x = Sum.inl v ∧ ∃ s ∈ side b, (openGraph ω).Reachable s v) ∨ x = Sum.inr b} := by
      intro u v huv hux hvy
      subst hux hvy
      rcases hx with ⟨v₀, hv₀, s, hs, hsv₀⟩ | hx
      · cases hv₀
        exact Or.inl ⟨v, rfl, s, hs, hsv₀.trans (SimpleGraph.Adj.reachable
          ((openGraph_adj ω _ _).2 ⟨huv, fun h => hne (by rw [h])⟩))⟩
      · exact absurd hx Sum.inl_ne_inr
    induction e using Sym2.ind with
    | h u v =>
      rw [Sym2.map_mk, Sym2.eq_iff] at hexy
      rcases hexy with ⟨hux, hvy⟩ | ⟨huy, hvx⟩
      · exact key he hux hvy
      · exact key (by rw [Sym2.eq_swap]; exact he) hvx huy
  · -- a hub edge `s(inl u, inr b')` with `u ∈ side b'`
    rw [Sym2.eq_iff] at hexy
    by_cases hb : b' = b
    · subst hb
      rcases hexy with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact Or.inr rfl
      · exact Or.inl ⟨u, rfl, u, hu, SimpleGraph.Reachable.refl u⟩
    · have hb' : b' = !b := by
        cases b <;> cases b' <;> first | rfl | exact (hb rfl).elim
      exfalso
      rcases hexy with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · rcases hx with ⟨v₀, hv₀, s, hs, hsv₀⟩ | hx
        · cases hv₀
          exact hsep s hs u (hb' ▸ hu) hsv₀
        · exact Sum.inl_ne_inr hx
      · rcases hx with ⟨v₀, hv₀, -⟩ | hx
        · exact Sum.inr_ne_inl hv₀
        · exact hb (Sum.inr_injective hx)

/-- **No open path between the hubs** when the blocks are not joined. [folklore] -/
theorem not_reachable_hubs (side : Bool → Set V) (ω : BondConfig V) (b : Bool)
    (hsep : ∀ s ∈ side b, ∀ t ∈ side (!b), ¬ (openGraph ω).Reachable s t) :
    ¬ (openGraph (hubConfig side ω)).Reachable (Sum.inr b) (Sum.inr (!b)) := by
  intro h
  rcases mem_of_reachable_of_closed (hubSide_closed side ω b hsep) (Or.inr rfl) h with
    ⟨v, hv, -⟩ | h'
  · exact Sum.inr_ne_inl hv
  · have h'' := Sum.inr_injective h'
    cases b <;> exact Bool.noConfusion h''

/-- **What the hub sees**: when the blocks are not joined, `inr b` is joined to `inl v` only
through its own block. [folklore] -/
theorem exists_reachable_of_hub_reachable (side : Bool → Set V) (ω : BondConfig V) (b : Bool)
    (hsep : ∀ s ∈ side b, ∀ t ∈ side (!b), ¬ (openGraph ω).Reachable s t) {v : V}
    (h : (openGraph (hubConfig side ω)).Reachable (Sum.inr b) (Sum.inl v)) :
    ∃ s ∈ side b, (openGraph ω).Reachable s v := by
  rcases mem_of_reachable_of_closed (hubSide_closed side ω b hsep) (Or.inr rfl) h with
    ⟨v₀, hv₀, hs⟩ | h'
  · cases hv₀
    exact hs
  · exact absurd h' Sum.inl_ne_inr

/-- **`{s* ↮ t*}` pulls back to `{S ↮ T}`.** [folklore] -/
theorem hubConfig_preimage_not_reachable (side : Bool → Set V) :
    hubConfig side ⁻¹'
        {ω' : BondConfig (V ⊕ Bool) | ¬ (openGraph ω').Reachable (Sum.inr true) (Sum.inr false)} =
      {ω : BondConfig V | ∀ s ∈ side true, ∀ t ∈ side false, ¬ (openGraph ω).Reachable s t} := by
  ext ω
  simp only [mem_preimage, mem_setOf_eq]
  constructor
  · intro h s hs t ht hst
    exact h ((hubConfig_reachable_hub_inl side ω hs hst).trans
      (hubConfig_adj_hub side ω ht).reachable.symm)
  · intro h
    exact not_reachable_hubs side ω true h

/-- Membership in the union of the edge clusters of the vertices of `S` ("`C_S`, the set of edges
belonging to open paths starting at vertices of `S`", BHK p. 6): an open non-loop pair both (equivalently,
one) of whose endpoints are joined to `S`. [cite: VandenbergHaggstromKahn2005, §2 p. 6 (definition of C_S)] -/
theorem mem_biUnion_openEdgeCluster_iff (ω : BondConfig V) (S : Set V) (e : Sym2 V) :
    e ∈ (⋃ s ∈ S, openEdgeCluster ω s) ↔
      e ∈ ω ∧ ¬ e.IsDiag ∧ ∀ v ∈ e, ∃ s ∈ S, (openGraph ω).Reachable s v := by
  simp only [mem_iUnion, exists_prop]
  constructor
  · rintro ⟨s, hs, he⟩
    rw [mem_openEdgeCluster_iff] at he
    exact ⟨he.1, he.2.1, fun v hv => ⟨s, hs, he.2.2 v hv⟩⟩
  · rintro ⟨heω, hdiag, hall⟩
    induction e using Sym2.ind with
    | h u v =>
      obtain ⟨s, hs, hsu⟩ := hall u (Sym2.mem_mk_left u v)
      have huv : u ≠ v := fun h => hdiag (Sym2.mk_isDiag_iff.2 h)
      have hsv : (openGraph ω).Reachable s v :=
        hsu.trans (SimpleGraph.Adj.reachable ((openGraph_adj ω u v).2 ⟨heω, huv⟩))
      refine ⟨s, hs, (mem_openEdgeCluster_iff ω s _).2 ⟨heω, hdiag, fun x hx => ?_⟩⟩
      rcases Sym2.mem_iff.1 hx with rfl | rfl
      · exact hsu
      · exact hsv

/-- **The hub's cluster, read on the old pairs, is `C_S`** (when the blocks are not joined).
[folklore] -/
theorem restrictConfig_openEdgeCluster_hub (side : Bool → Set V) (ω : BondConfig V) (b : Bool)
    (hsep : ∀ s ∈ side b, ∀ t ∈ side (!b), ¬ (openGraph ω).Reachable s t) :
    restrictConfig Sum.inl (openEdgeCluster (hubConfig side ω) (Sum.inr b)) =
      ⋃ s ∈ side b, openEdgeCluster ω s := by
  ext e
  rw [mem_restrictConfig, mem_openEdgeCluster_iff, mem_biUnion_openEdgeCluster_iff,
    map_inl_mem_hubConfig_iff, Sym2.isDiag_map Sum.inl_injective]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  constructor
  · intro h v hv
    exact exists_reachable_of_hub_reachable side ω b hsep
      (h (Sum.inl v) (Sym2.mem_map.2 ⟨v, hv, rfl⟩))
  · intro h v' hv'
    obtain ⟨v, hv, rfl⟩ := Sym2.mem_map.1 hv'
    obtain ⟨s, hs, hsv⟩ := h v hv
    exact hubConfig_reachable_hub_inl side ω hs hsv

/-- `restrictConfig f` is monotone. [folklore] -/
theorem restrictConfig_mono' {W : Type*} (f : W → V) {C C' : BondConfig V} (h : C ⊆ C') :
    restrictConfig f C ⊆ restrictConfig f C' := fun _ he => h he

end TwoSetConditionalAssociation

open TwoSetConditionalAssociation in
/-- **van den Berg–Häggström–Kahn (2006), Theorem 1.5 with vertex SETS `S, T` (= Theorem 2.1 at
`q = 1`; Remark 1 after Theorem 1.2: "we could replace `s` in all results of this section, and `t`
in Theorems (1.4) and (1.5), by sets of vertices").** Printed (Thm. 2.1): "Let `S` and `T` be
disjoint sets of vertices, and `f` and `g` bounded, measurable functions of `(C_S, C_T)`, each
increasing in `C_S` and decreasing in `C_T`. Then on `{S ↛ T}`, `E f g ≥ E f E g`" (for every
random-cluster measure with `q ≥ 1`; here `q = 1`, bond percolation with arbitrary edge
probabilities `w` on a finite vertex type).  In this library's vocabulary: `μ = prodBernoulli w`,
`D = {ω | ∀ s ∈ S, ∀ t ∈ T, ¬ (openGraph ω).Reachable s t}` (`= {S ↮ T}`),
`C_S ω = ⋃ s ∈ S, openEdgeCluster ω s`, `f ω = F (C_S ω) (C_T ω)`, `g ω = G (C_S ω) (C_T ω)` with
`F, G` monotone in the first and antitone in the second variable, in the denominator-free form
`(∫_D f dμ)(∫_D g dμ) ≤ μ(D) · ∫_D f g dμ` (for `μ(D) > 0` the printed inequality of conditional
expectations; `S ∩ T ≠ ∅` or `μ(D) = 0` make both sides vanish, so disjointness is not assumed).
proved by BHK's reduction to the one-vertex Theorem 1.5 (hub construction, see the module
docstring); no new statement is introduced.
[cite: VandenbergHaggstromKahn2005, Thm. 2.1 (p. 9) at q = 1; Remark 1 after Thm. 1.2 (p. 5); Thm. 1.5 (p. 7)] -/
theorem BHK2006_twoSetConditionalAssociation [Fintype V] (w : Sym2 V → unitInterval) (S T : Set V)
    (F G : Set (Sym2 V) → Set (Sym2 V) → ℝ)
    (hF₁ : ∀ D, Monotone fun C => F C D) (hF₂ : ∀ C, Antitone fun D => F C D)
    (hG₁ : ∀ D, Monotone fun C => G C D) (hG₂ : ∀ C, Antitone fun D => G C D) :
    (∫ ω in {ω : BondConfig V | ∀ s ∈ S, ∀ t ∈ T, ¬ (openGraph ω).Reachable s t},
        F (⋃ s ∈ S, openEdgeCluster ω s) (⋃ t ∈ T, openEdgeCluster ω t) ∂(prodBernoulli w)) *
      (∫ ω in {ω : BondConfig V | ∀ s ∈ S, ∀ t ∈ T, ¬ (openGraph ω).Reachable s t},
        G (⋃ s ∈ S, openEdgeCluster ω s) (⋃ t ∈ T, openEdgeCluster ω t) ∂(prodBernoulli w)) ≤
    (prodBernoulli w).real {ω : BondConfig V | ∀ s ∈ S, ∀ t ∈ T, ¬ (openGraph ω).Reachable s t} *
      ∫ ω in {ω : BondConfig V | ∀ s ∈ S, ∀ t ∈ T, ¬ (openGraph ω).Reachable s t},
        F (⋃ s ∈ S, openEdgeCluster ω s) (⋃ t ∈ T, openEdgeCluster ω t) *
          G (⋃ s ∈ S, openEdgeCluster ω s) (⋃ t ∈ T, openEdgeCluster ω t) ∂(prodBernoulli w) := by
  classical
  set D : Set (BondConfig V) := {ω | ∀ s ∈ S, ∀ t ∈ T, ¬ (openGraph ω).Reachable s t} with hD
  have hDm : MeasurableSet D := MeasurableSet.of_discrete
  -- Theorem 1.5 on the hub graph `V ⊕ Bool`, `s* = inr true`, `t* = inr false`
  have key := BHK2006_twoClusterConditionalAssociation_holds (V ⊕ Bool) (hubWeight w (sides S T))
    (Sum.inr true) (Sum.inr false)
    (fun C E => F (restrictConfig Sum.inl C) (restrictConfig Sum.inl E))
    (fun C E => G (restrictConfig Sum.inl C) (restrictConfig Sum.inl E))
    (fun E _ _ h => hF₁ _ (restrictConfig_mono' Sum.inl h))
    (fun C _ _ h => hF₂ _ (restrictConfig_mono' Sum.inl h))
    (fun E _ _ h => hG₁ _ (restrictConfig_mono' Sum.inl h))
    (fun C _ _ h => hG₂ _ (restrictConfig_mono' Sum.inl h))
    (by simp)
  simp only [setIntegral_hub, measureReal_hub, hubConfig_preimage_not_reachable, sides_true,
    sides_false] at key
  -- on `D` the hub clusters, read on the old pairs, are `C_S` and `C_T`
  have hC : ∀ ω ∈ D,
      restrictConfig Sum.inl (openEdgeCluster (hubConfig (sides S T) ω) (Sum.inr true)) =
          ⋃ s ∈ S, openEdgeCluster ω s ∧
        restrictConfig Sum.inl (openEdgeCluster (hubConfig (sides S T) ω) (Sum.inr false)) =
          ⋃ t ∈ T, openEdgeCluster ω t := fun ω hω =>
    ⟨restrictConfig_openEdgeCluster_hub (sides S T) ω true (fun s hs t ht => hω s hs t ht),
      restrictConfig_openEdgeCluster_hub (sides S T) ω false
        (fun t ht s hs h => hω s hs t ht h.symm)⟩
  have e1 : ∫ ω in D, F (restrictConfig Sum.inl (openEdgeCluster (hubConfig (sides S T) ω)
        (Sum.inr true))) (restrictConfig Sum.inl (openEdgeCluster (hubConfig (sides S T) ω)
        (Sum.inr false))) ∂(prodBernoulli w) =
      ∫ ω in D, F (⋃ s ∈ S, openEdgeCluster ω s) (⋃ t ∈ T, openEdgeCluster ω t)
        ∂(prodBernoulli w) :=
    setIntegral_congr_fun hDm fun ω hω => by rw [(hC ω hω).1, (hC ω hω).2]
  have e2 : ∫ ω in D, G (restrictConfig Sum.inl (openEdgeCluster (hubConfig (sides S T) ω)
        (Sum.inr true))) (restrictConfig Sum.inl (openEdgeCluster (hubConfig (sides S T) ω)
        (Sum.inr false))) ∂(prodBernoulli w) =
      ∫ ω in D, G (⋃ s ∈ S, openEdgeCluster ω s) (⋃ t ∈ T, openEdgeCluster ω t)
        ∂(prodBernoulli w) :=
    setIntegral_congr_fun hDm fun ω hω => by rw [(hC ω hω).1, (hC ω hω).2]
  have e3 : ∫ ω in D, F (restrictConfig Sum.inl (openEdgeCluster (hubConfig (sides S T) ω)
        (Sum.inr true))) (restrictConfig Sum.inl (openEdgeCluster (hubConfig (sides S T) ω)
        (Sum.inr false))) *
        G (restrictConfig Sum.inl (openEdgeCluster (hubConfig (sides S T) ω)
        (Sum.inr true))) (restrictConfig Sum.inl (openEdgeCluster (hubConfig (sides S T) ω)
        (Sum.inr false))) ∂(prodBernoulli w) =
      ∫ ω in D, F (⋃ s ∈ S, openEdgeCluster ω s) (⋃ t ∈ T, openEdgeCluster ω t) *
        G (⋃ s ∈ S, openEdgeCluster ω s) (⋃ t ∈ T, openEdgeCluster ω t) ∂(prodBernoulli w) :=
    setIntegral_congr_fun hDm fun ω hω => by rw [(hC ω hω).1, (hC ω hω).2]
  rw [e1, e2, e3] at key
  exact key

/-! ### Corollaries: Theorem 1.4 / Theorem 1.3 with sets, and the set forms of the exchange inequalities -/

/-- **Theorem 1.4 with vertex sets** (as quoted by Kozma–Nitzan, §2.2 p. 5: "if `f` and `g` are two
increasing functions defined on the clusters of `A` and `B` respectively then
`E(fg | A ↮ B) ≤ E(f | A ↮ B) E(g | A ↮ B)`"): for `F`, `G` increasing,
`μ(D) · ∫_D F(C_S) G(C_T) dμ ≤ (∫_D F(C_S) dμ)(∫_D G(C_T) dμ)`, `D = {S ↮ T}` — proved from the set
form of Theorem 1.5 applied to `(F, -G)`, exactly as in the one-vertex case.
[cite: VandenbergHaggstromKahn2005, Thm. 1.4 (p. 7) with Remark 1 after Thm. 1.2 (p. 5); KozmaNitzan2024 §2.2 p. 5] -/
theorem BHK2006_twoSetConditionalAssociation.negCorrelation [Fintype V]
    (w : Sym2 V → unitInterval) (S T : Set V) (F G : Set (Sym2 V) → ℝ)
    (hF : Monotone F) (hG : Monotone G) :
    (prodBernoulli w).real {ω : BondConfig V | ∀ s ∈ S, ∀ t ∈ T, ¬ (openGraph ω).Reachable s t} *
      (∫ ω in {ω : BondConfig V | ∀ s ∈ S, ∀ t ∈ T, ¬ (openGraph ω).Reachable s t},
        F (⋃ s ∈ S, openEdgeCluster ω s) * G (⋃ t ∈ T, openEdgeCluster ω t) ∂(prodBernoulli w)) ≤
    (∫ ω in {ω : BondConfig V | ∀ s ∈ S, ∀ t ∈ T, ¬ (openGraph ω).Reachable s t},
        F (⋃ s ∈ S, openEdgeCluster ω s) ∂(prodBernoulli w)) *
      ∫ ω in {ω : BondConfig V | ∀ s ∈ S, ∀ t ∈ T, ¬ (openGraph ω).Reachable s t},
        G (⋃ t ∈ T, openEdgeCluster ω t) ∂(prodBernoulli w) := by
  have key := BHK2006_twoSetConditionalAssociation w S T (fun C _ => F C) (fun _ D => -G D)
    (fun _ => hF) (fun _ => antitone_const) (fun _ => monotone_const)
    (fun _ _ _ hDD' => neg_le_neg (hG hDD'))
  simp only [mul_neg, integral_neg] at key
  linarith

namespace TwoSetConditionalAssociation

/-- Evaluation of a predicate indicator as a set indicator. [folklore] -/
theorem predIndicator_eq_indicator (P : BondConfig V → Prop) [DecidablePred P] (ω : BondConfig V) :
    (if P ω then (1 : ℝ) else 0) = ({ω' : BondConfig V | P ω'}).indicator 1 ω := by
  by_cases h : P ω
  · rw [if_pos h, indicator_of_mem (show ω ∈ {ω' : BondConfig V | P ω'} from h), Pi.one_apply]
  · rw [if_neg h, indicator_of_notMem (show ω ∉ {ω' : BondConfig V | P ω'} from h)]

end TwoSetConditionalAssociation

end Percolation.Literature

end
