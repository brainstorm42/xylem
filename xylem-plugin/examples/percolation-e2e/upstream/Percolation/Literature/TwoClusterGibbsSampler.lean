import Percolation.Literature.LatticeModels.ProdBernoulliIndependence
import Percolation.Literature.TwoClusterConditionalAssociationProofs
import Percolation.Util.Linter

/-!
# The two-cluster Gibbs sampler of van den Berg–Häggström–Kahn (2006), §2.1, at `q = 1`: the conditional law of `(C_S, C_T)` given `{S ↮ T}` is a limit of monotone images of product measures ("UI"), with an explicit rate, and the transfer principle that follows

Companion of `TwoClusterConditionalAssociationProofs.lean`
(BHK Thm. 1.5, proved there along BHK's §1) and `TwoSetConditionalAssociation.lean` (the set forms).
All declarations are definitions with bodies or theorems.  Guiding principle ("one axis"): every
product-measure inequality for monotone functions transfers to the BHK two-cluster conditional law.

## Source, as printed (RSA 29 (2006) 417–435, doi:10.1002/rsa.20102; page numbers of the preprint)

§2.1, p. 9: "we use `C_S` for the set of edges belonging to open paths starting at vertices of `S`.
**Theorem 2.1.** Consider a distribution (11) with `q ≥ 1`. Let `S` and `T` be disjoint sets of
vertices, and `f` and `g` bounded, measurable functions of `(C_S, C_T)`, each increasing in `C_S`
and decreasing in `C_T`. Then on `{S ↮ T}`, `E f g ≥ E f E g`." P. 10: "**Lemma 2.3.** Let
`A ⊂ V` and `F ⊂ E`. The restriction of `φ_{G,q}` to `{0,1}^{E∖F̄}` under conditioning on either of
the events `{C_A = F}`, `{ω_{F̄} ≡ 0}` … is the r.c.m. with parameter `q` on `G − F̄` …
**Lemma 2.4.** If `A, F` are as in Lemma 2.3, `B ⊆ V ∖ V(F)`, and `φ` is (temporarily) `φ_{G,q}`
conditioned on `{A ↮ B}`, then `φ(ω_{E∖F̄} = · | C_A = F) = φ_{G,q}(ω_{E∖F̄} = · | ω_{F̄} ≡ 0) =
φ_{G−F̄,q}(·)`.  We now turn to the proof of Theorem 2.1. We consider a Markov chain with state
space `Ω̂` consisting of pairs `(C_S, C_T)` satisfying `Q := {S ↮ T}` … Initially our chain is in
some fixed state `(C_S^0, C_T^0) ∈ Ω̂`. Given `(C_S^{i−1}, C_T^{i−1})`, the state of the chain at
time `i − 1`, we choose `(C_S^i, C_T^i)` in two steps, first choosing `C_T^i` according to `φ`
conditioned on `{C_S = C_S^{i−1}}` — that is, `Pr(C_T^i = ·) = φ(C_T = · | C_S = C_S^{i−1})` — and
then, similarly, `C_S^i` according to `Pr(C_S^i = ·) = φ(C_S = · | C_T = C_T^i)`.  It is clear
that `φ̂` is stationary for this chain, and that the chain is irreducible and aperiodic; so to
prove Theorem 2.1 it's enough to show **Claim 2.5.** For `f, g` as in the statement of Theorem 2.1
and any `n`, (12) holds for expectation taken with respect to the law of `(C_S^n, C_T^n)`."
(pp. 10–11); p. 12: "**Remark 2.8.** For each `n`, `C_S^n` is increasing in the variables
`X_e^i, Y_e^i`, and `C_T^n` is decreasing in these variables" (`X_e^i = 1{e ∉ C_T^i}`,
`Y_e^i = 1{e ∈ C_S^i}`); p. 13 (Remark after the proof): "introduce independent r.v.'s `X_e^i, Y_e^i`
… It is then not hard to show, again using Lemmas 2.2-2.4, that (for each `n`) `ω^n` is
increasing in the variables `X_e^i, Y_e^i`, so that the Claim follows from Harris' inequality."
Kahn, arXiv:2210.08653, p. 2: "One way to prove PA for `μ` is to realize the `X_i`'s as increasing
functions of independent Bernoullis `Y_1, …, Y_m` and invoke Harris; more generally, `μ` is PA if
it is a limit of measures obtained in this way. Say `μ` is FUI … in the first case, and UI in the
second."

## What is formalized (bond percolation = the case `q = 1`, finite vertex type `V`, arbitrary pair probabilities `w : Sym2 V → [0,1]`, vertex SETS `S, T`)

* `BHK2006.setCl ω S = ⋃_{s ∈ S} C_s` (BHK's `C_S`) and `BHK2006.barOf S W` (the pairs meeting
  `S ∪ V(W)`, BHK's `W̄` plus the pairs at `S`); locality of `{C_S = W}` (`setCl_eq_of_agree`) and
  Lemma 2.4 at `q = 1` pointwise: on `{C_S = W} ∩ {S ↮ T}`, `C_T(ω) = C_T(ω ∖ barOf S W)`
  (`setCl_eq_sdiff_barOf`); summed against the product weight with block Fubini this is the exact
  half-step identity `BHK2006.set_sum_cond_cluster` (the set form of
  `BHK2006.sum_cond_cluster` of `TwoClusterConditionalAssociationProofs.lean`).

Not formalized: `q > 1` (random-cluster measures; the same chain with Lemma 2.2), infinite graphs,
the exact representation of `φ̂` from the last regeneration time.
-/

noncomputable section

open MeasureTheory unitInterval
open Percolation.Literature.LatticeModels (prodBernoulli)

namespace Percolation.Literature

namespace BHK2006

open scoped Classical
open DecisionTree (ind ind_of_mem ind_of_not_mem ind_nonneg)

/-! ### The set clusters `C_S` and the deleted sets `S̄ ∪ V(W)` -/

section Graph

variable {V : Type*}

/-- **`C_S`**, the open edge cluster of a vertex SET: "we use `C_S` for the set of edges belonging
to open paths starting at vertices of `S`" — the union of the clusters `C_s`, `s ∈ S`.
[cite: VandenbergHaggstromKahn2005, §2.1 p. 9 (definition of `C_S`)] -/
def setCl (ω : BondConfig V) (S : Set V) : Set (Sym2 V) := ⋃ s ∈ S, openEdgeCluster ω s

/-- The pairs meeting `S ∪ V(W)`: BHK's `W̄` ("all edges having at least one vertex in common with
some edge of `W`") together with the pairs at `S` (so that `{C_S = W}` is a cylinder event on this
set also for `W = ∅`). [cite: VandenbergHaggstromKahn2005, §1 p. 8 (definition of `W̄`), §2.1 Lemma 2.3 (p. 10)] -/
def barOf (S : Set V) (W : Set (Sym2 V)) : Set (Sym2 V) :=
  {e | ∃ v ∈ e, v ∈ S ∨ ∃ e' ∈ W, v ∈ e'}

/-- Unfolding of membership in `C_S`: `e ∈ C_S` iff `e ∈ C_s` for some `s ∈ S`.
[cite: VandenbergHaggstromKahn2005, §2.1 p. 9 (definition of `C_S`)] -/
theorem mem_setCl_iff (ω : BondConfig V) (S : Set V) (e : Sym2 V) :
    e ∈ setCl ω S ↔ ∃ s ∈ S, e ∈ openEdgeCluster ω s := by
  simp only [setCl, Set.mem_iUnion, exists_prop]

/-- Unfolding of membership in `barOf S W` (the pairs meeting `S ∪ V(W)`).
[cite: VandenbergHaggstromKahn2005, §1 p. 8 (definition of `W̄`)] -/
theorem mem_barOf_iff (S : Set V) (W : Set (Sym2 V)) (e : Sym2 V) :
    e ∈ barOf S W ↔ ∃ v ∈ e, v ∈ S ∨ ∃ e' ∈ W, v ∈ e' := Iff.rfl

/-- `C_S` is increasing in the configuration. [cite: VandenbergHaggstromKahn2005, §1 p. 3] -/
theorem setCl_mono {ω ω' : BondConfig V} (h : ω ⊆ ω') (S : Set V) : setCl ω S ⊆ setCl ω' S := by
  intro e he
  obtain ⟨s, hs, he⟩ := (mem_setCl_iff ω S e).1 he
  exact (mem_setCl_iff ω' S e).2 ⟨s, hs, openEdgeCluster_mono h s he⟩

/-- `barOf S` is increasing in `W`. [cite: VandenbergHaggstromKahn2005, §1 p. 8] -/
theorem barOf_mono (S : Set V) : Monotone (barOf S) := by
  rintro W W' h e ⟨v, hv, hvK⟩
  exact ⟨v, hv, hvK.imp id fun ⟨e', he', hve'⟩ => ⟨e', h he', hve'⟩⟩

/-- **`{S ↔ v}` read off `C_S`**: some vertex of `S` is joined to `v` iff `v ∈ S` or some edge of
`C_S` contains `v`. [cite: VandenbergHaggstromKahn2005, §1 p. 3] -/
theorem setReach_iff (ω : BondConfig V) (S : Set V) (v : V) :
    (∃ s ∈ S, (openGraph ω).Reachable s v) ↔ v ∈ S ∨ ∃ e ∈ setCl ω S, v ∈ e := by
  constructor
  · rintro ⟨s, hs, hsv⟩
    rcases (reachable_iff_exists_mem_openEdgeCluster ω s v).1 hsv with rfl | ⟨e, he, hve⟩
    · exact Or.inl hs
    · exact Or.inr ⟨e, (mem_setCl_iff ω S e).2 ⟨s, hs, he⟩, hve⟩
  · rintro (hv | ⟨e, he, hve⟩)
    · exact ⟨v, hv, SimpleGraph.Reachable.refl v⟩
    · obtain ⟨s, hs, he⟩ := (mem_setCl_iff ω S e).1 he
      exact ⟨s, hs, (reachable_iff_exists_mem_openEdgeCluster ω s v).2 (Or.inr ⟨e, he, hve⟩)⟩

/-- **Locality of `{C_S = W}`** (Lemma 2.3's "`{C_A = F}` is an event on `F̄`"): two configurations
agreeing on the pairs meeting `S ∪ V(W)` lie in `{C_S = W}` together.
[cite: VandenbergHaggstromKahn2005, §2.1 Lemma 2.3 (p. 10); §1 p. 8] -/
theorem setCl_eq_of_agree {S : Set V} {W ω ω' : Set (Sym2 V)}
    (hag : ∀ e ∈ barOf S W, (e ∈ ω ↔ e ∈ ω')) (hW : setCl ω S = W) : setCl ω' S = W := by
  have hK : ∀ v, (∃ s ∈ S, (openGraph ω).Reachable s v) ↔ v ∈ S ∨ ∃ e ∈ W, v ∈ e := fun v => by
    rw [setReach_iff, hW]
  have h1 : ∀ s ∈ S, ∀ v, (openGraph ω').Reachable s v → (openGraph ω).Reachable s v := by
    intro s hs v hv
    rw [SimpleGraph.reachable_iff_reflTransGen] at hv
    induction hv with
    | refl => exact SimpleGraph.Reachable.refl s
    | @tail b c _ hbc ih =>
      obtain ⟨hω', hne⟩ := (openGraph_adj ω' b c).1 hbc
      exact ih.trans (SimpleGraph.Adj.reachable ((openGraph_adj ω b c).2
        ⟨(hag _ ⟨b, Sym2.mem_mk_left b c, (hK b).1 ⟨s, hs, ih⟩⟩).2 hω', hne⟩))
  have h2 : ∀ s ∈ S, ∀ v, (openGraph ω).Reachable s v → (openGraph ω').Reachable s v := by
    intro s hs v hv
    rw [SimpleGraph.reachable_iff_reflTransGen] at hv
    induction hv with
    | refl => exact SimpleGraph.Reachable.refl s
    | @tail b c hab hbc ih =>
      obtain ⟨hω, hne⟩ := (openGraph_adj ω b c).1 hbc
      have hb : (openGraph ω).Reachable s b := (SimpleGraph.reachable_iff_reflTransGen s b).2 hab
      exact ih.trans (SimpleGraph.Adj.reachable ((openGraph_adj ω' b c).2
        ⟨(hag _ ⟨b, Sym2.mem_mk_left b c, (hK b).1 ⟨s, hs, hb⟩⟩).1 hω, hne⟩))
  rw [← hW]
  ext e
  rw [mem_setCl_iff, mem_setCl_iff]
  constructor
  · rintro ⟨s, hs, he⟩
    rw [mem_openEdgeCluster_iff] at he
    obtain ⟨he', hd, hr⟩ := he
    have hr' : ∀ v ∈ e, (openGraph ω).Reachable s v := fun v hv => h1 s hs v (hr v hv)
    refine ⟨s, hs, (mem_openEdgeCluster_iff _ _ _).2 ⟨?_, hd, hr'⟩⟩
    exact (hag e ⟨e.out.1, Sym2.out_fst_mem e,
      (hK _).1 ⟨s, hs, hr' _ (Sym2.out_fst_mem e)⟩⟩).2 he'
  · rintro ⟨s, hs, he⟩
    rw [mem_openEdgeCluster_iff] at he
    obtain ⟨he, hd, hr⟩ := he
    refine ⟨s, hs, (mem_openEdgeCluster_iff _ _ _).2 ⟨?_, hd, fun v hv => h2 s hs v (hr v hv)⟩⟩
    exact (hag e ⟨e.out.1, Sym2.out_fst_mem e,
      (hK _).1 ⟨s, hs, hr _ (Sym2.out_fst_mem e)⟩⟩).1 he

/-- `{C_S = W}` is a cylinder event on `barOf S W` (Lemma 2.3: conditioning on `{C_A = F}` only
involves the variables on `F̄`). [cite: VandenbergHaggstromKahn2005, §2.1 Lemma 2.3 (p. 10)] -/
theorem setCl_inter_barOf_eq_iff (S : Set V) (W ω : Set (Sym2 V)) :
    setCl (ω ∩ barOf S W) S = W ↔ setCl ω S = W :=
  ⟨fun h => setCl_eq_of_agree (ω := ω ∩ barOf S W) (ω' := ω)
      (fun _ he => ⟨fun h' => h'.1, fun h' => ⟨h', he⟩⟩) h,
    fun h => setCl_eq_of_agree (ω := ω) (ω' := ω ∩ barOf S W)
      (fun _ he => ⟨fun h' => ⟨h', he⟩, fun h' => h'.1⟩) h⟩

/-- Deleting the pairs of `B` twice is deleting them once. [folklore] -/
private theorem setCl_sdiff_sdiff (T : Set V) (B η : Set (Sym2 V)) :
    setCl ((η \ B) \ B) T = setCl (η \ B) T := by
  rw [Set.sdiff_sdiff, Set.union_self]

/-- **`C_T` given `C_S = W`** (Lemma 2.4 at `q = 1`): on `{C_S = W}` with no vertex of `T` in
`S ∪ V(W)` (i.e. `S ↮ T`), the open cluster of `T` is the open cluster of `T` in the configuration
with the pairs meeting `S ∪ V(W)` deleted ("the remaining variables are distributed as … on the
graph obtained from `G` by deleting all edges in `F̄`").
[cite: VandenbergHaggstromKahn2005, §2.1 Lemmas 2.3–2.4 (p. 10); §1 p. 8] -/
theorem setCl_eq_sdiff_barOf {S T : Set V} {W ω : Set (Sym2 V)} (hW : setCl ω S = W)
    (hT : ∀ t ∈ T, ¬ (t ∈ S ∨ ∃ e ∈ W, t ∈ e)) :
    setCl ω T = setCl (ω \ barOf S W) T := by
  have hK : ∀ v, (∃ s ∈ S, (openGraph ω).Reachable s v) ↔ v ∈ S ∨ ∃ e ∈ W, v ∈ e := fun v => by
    rw [setReach_iff, hW]
  have hnot : ∀ t ∈ T, ∀ v, (openGraph ω).Reachable t v → ¬ (v ∈ S ∨ ∃ e ∈ W, v ∈ e) := by
    intro t ht v htv hvK
    obtain ⟨s, hs, hsv⟩ := (hK v).2 hvK
    exact hT t ht ((hK t).1 ⟨s, hs, hsv.trans htv.symm⟩)
  have hreach : ∀ t ∈ T, ∀ v, (openGraph ω).Reachable t v →
      (openGraph (ω \ barOf S W)).Reachable t v := by
    intro t ht v hv
    rw [SimpleGraph.reachable_iff_reflTransGen] at hv
    induction hv with
    | refl => exact SimpleGraph.Reachable.refl t
    | @tail b c hab hbc ih =>
      obtain ⟨hω, hne⟩ := (openGraph_adj ω b c).1 hbc
      have hb : (openGraph ω).Reachable t b := (SimpleGraph.reachable_iff_reflTransGen t b).2 hab
      have hbK := hnot t ht b hb
      have hcK := hnot t ht c (hb.trans hbc.reachable)
      refine ih.trans (SimpleGraph.Adj.reachable ((openGraph_adj _ b c).2 ⟨⟨hω, ?_⟩, hne⟩))
      rintro ⟨v, hv, hvK⟩
      rcases Sym2.mem_iff.1 hv with rfl | rfl
      · exact hbK hvK
      · exact hcK hvK
  apply Set.Subset.antisymm
  · intro e he
    obtain ⟨t, ht, he⟩ := (mem_setCl_iff _ _ _).1 he
    rw [mem_openEdgeCluster_iff] at he
    obtain ⟨he, hd, hr⟩ := he
    refine (mem_setCl_iff _ _ _).2 ⟨t, ht, (mem_openEdgeCluster_iff _ _ _).2
      ⟨⟨he, ?_⟩, hd, fun v hv => hreach t ht v (hr v hv)⟩⟩
    rintro ⟨v, hv, hvK⟩
    exact hnot t ht v (hr v hv) hvK
  · exact setCl_mono Set.sdiff_subset T

/-- If no open non-loop pair meets `T`, then `C_T = ∅`. [folklore] -/
private theorem setCl_eq_empty_of_forall {ω : BondConfig V} {T : Set V}
    (h : ∀ e ∈ ω, (∃ v ∈ e, v ∈ T) → e.IsDiag) : setCl ω T = ∅ := by
  refine Set.eq_empty_of_forall_notMem (Sym2.ind fun a b => ?_)
  intro he
  obtain ⟨t, ht, he⟩ := (mem_setCl_iff _ _ _).1 he
  rw [mem_openEdgeCluster_iff] at he
  obtain ⟨-, hd, hr⟩ := he
  -- only `t` itself is joined to `t`: the first edge of an open path from `t` would be an open
  -- non-loop pair at `t`
  have hreach_eq : ∀ v, (openGraph ω).Reachable t v → v = t := by
    intro v hv
    rw [SimpleGraph.reachable_iff_reflTransGen] at hv
    induction hv with
    | refl => rfl
    | @tail b' c _ hbc ih =>
      obtain ⟨hω', hne⟩ := (openGraph_adj ω b' c).1 hbc
      subst ih
      exact absurd (Sym2.mk_isDiag_iff.1 (h _ hω' ⟨_, Sym2.mem_mk_left _ c, ht⟩)) hne
  exact hd (Sym2.mk_isDiag_iff.2 ((hreach_eq a (hr a (Sym2.mem_mk_left a b))).trans
    (hreach_eq b (hr b (Sym2.mem_mk_right a b))).symm))

/-- On `{C_S = W}`, `{S ↮ T}` holds iff no vertex of `T` lies in `S ∪ V(W)` ("If `A, F` are as in
Lemma 2.3, and `B ⊆ V ∖ V(F)`, then `{C_A = F} ⊆ {A ↮ B}`").
[cite: VandenbergHaggstromKahn2005, §2.1 p. 10 (sentence before Lemma 2.4)] -/
theorem notJoined_iff_of_setCl_eq {S T : Set V} {W : Set (Sym2 V)} {ω : BondConfig V}
    (hW : setCl ω S = W) :
    (∀ s ∈ S, ∀ t ∈ T, ¬ (openGraph ω).Reachable s t) ↔ ∀ t ∈ T, ¬ (t ∈ S ∨ ∃ e ∈ W, t ∈ e) := by
  constructor
  · intro h t ht htK
    rw [← hW, ← setReach_iff] at htK
    obtain ⟨s, hs, hst⟩ := htK
    exact h s hs t ht hst
  · intro h s hs t ht hst
    exact h t ht (by rw [← hW, ← setReach_iff]; exact ⟨s, hs, hst⟩)

end Graph

/-! ### Conditioning on `C_S` as a finite-sum identity (Lemma 2.4 at `q = 1`, summed) -/

section Sums

variable {V : Type*} [Fintype V]

/-- **BHK's sampler half-step as an exact identity** (display (10) / Lemma 2.4 at `q = 1`, for
vertex sets): for any `H`,
`E[H(C_S, C_T) 1{S ↮ T}] = Σ_ω w(ω) 1{S ↮ T}(ω) · Σ_η w(η) H(C_S(ω), C_T(η ∖ B(C_S ω)))`, where
`B(W)` is the set of pairs meeting `S ∪ V(W)` and `η` is a fresh configuration: given `C_S = W`
(inside `{S ↮ T}`), `C_T` is distributed as the cluster of `T` for percolation on `G − W̄`.
[cite: VandenbergHaggstromKahn2005, §2.1 Lemma 2.4 (p. 10) and the transition rule `Pr(C_T^i = ·) = φ(C_T = · | C_S = C_S^{i-1})` (pp. 10–11); §1 display (10) (p. 7)] -/
theorem set_sum_cond_cluster (w : Sym2 V → ℝ) (hm : ∑ ω, weight w ω = 1) (S T : Set V)
    (H : Set (Sym2 V) → Set (Sym2 V) → ℝ) {D : Set (Set (Sym2 V))}
    (hD : ∀ ω, ω ∈ D ↔ ∀ s ∈ S, ∀ t ∈ T, ¬ (openGraph ω).Reachable s t) :
    ∑ ω, weight w ω * (H (setCl ω S) (setCl ω T) * ind D ω) =
      ∑ ω, weight w ω * ((∑ η, weight w η *
        H (setCl ω S) (setCl (η \ barOf S (setCl ω S)) T)) * ind D ω) := by
  -- the identity on each event `{C_S = W}`
  have key : ∀ W : Set (Sym2 V),
      ∑ ω, (if setCl ω S = W then weight w ω * (H W (setCl ω T) * ind D ω) else 0) =
      ∑ ω, (if setCl ω S = W then
          weight w ω * ((∑ η, weight w η * H W (setCl (η \ barOf S W) T)) * ind D ω) else 0) := by
    intro W
    by_cases hT : ∀ t ∈ T, ¬ (t ∈ S ∨ ∃ e ∈ W, t ∈ e)
    · -- block Fubini with the block `A = barOf S W`
      set A : Set (Sym2 V) := barOf S W with hA
      set Φ : Set (Sym2 V) → Set (Sym2 V) → ℝ := fun ζ η =>
        if setCl ζ S = W then H W (setCl (η \ A) T) else 0 with hΦ
      have hind : ∀ ω, setCl ω S = W → ind D ω = 1 := fun ω hW =>
        ind_of_mem ((hD ω).2 ((notJoined_iff_of_setCl_eq hW).2 hT))
      have h1 : ∀ ω, (if setCl ω S = W then weight w ω * (H W (setCl ω T) * ind D ω) else 0) =
          weight w ω * Φ (ω ∩ A) (ω \ A) := by
        intro ω
        simp only [hΦ, hA, setCl_inter_barOf_eq_iff, setCl_sdiff_sdiff]
        split_ifs with hW
        · rw [hind ω hW, mul_one, setCl_eq_sdiff_barOf hW hT]
        · rw [mul_zero]
      have h2 : ∀ ω, weight w ω * ∑ ω', weight w ω' * Φ (ω ∩ A) (ω' \ A) =
          (if setCl ω S = W then
            weight w ω * ((∑ η, weight w η * H W (setCl (η \ A) T)) * ind D ω) else 0) := by
        intro ω
        simp only [hΦ, hA, setCl_inter_barOf_eq_iff, setCl_sdiff_sdiff]
        split_ifs with hW
        · rw [hind ω hW, mul_one]
        · simp
      calc ∑ ω, (if setCl ω S = W then weight w ω * (H W (setCl ω T) * ind D ω) else 0)
          = (∑ ω, weight w ω) * ∑ ω, weight w ω * Φ (ω ∩ A) (ω \ A) := by
            rw [hm, one_mul]; exact Finset.sum_congr rfl fun ω _ => h1 ω
        _ = ∑ ω, weight w ω * ∑ ω', weight w ω' * Φ (ω ∩ A) (ω' \ A) := blockFubini w A Φ
        _ = _ := Finset.sum_congr rfl fun ω _ => h2 ω
    · -- some vertex of `T` lies in `S ∪ V(W)`: on `{C_S = W}`, `S ↔ T`, both sides vanish
      refine Finset.sum_congr rfl fun ω _ => ?_
      split_ifs with hW
      · have hωD : ω ∉ D := fun h => hT ((notJoined_iff_of_setCl_eq hW).1 ((hD ω).1 h))
        simp only [ind_of_not_mem hωD, mul_zero]
      · rfl
  -- sum over `W`
  calc ∑ ω, weight w ω * (H (setCl ω S) (setCl ω T) * ind D ω)
      = ∑ ω, ∑ W, (if setCl ω S = W then
          weight w ω * (H W (setCl ω T) * ind D ω) else 0) :=
        Finset.sum_congr rfl fun ω _ => (Fintype.sum_ite_eq (setCl ω S)
          fun W => weight w ω * (H W (setCl ω T) * ind D ω)).symm
    _ = ∑ W, ∑ ω, (if setCl ω S = W then
          weight w ω * (H W (setCl ω T) * ind D ω) else 0) := Finset.sum_comm
    _ = ∑ W, ∑ ω, (if setCl ω S = W then
          weight w ω * ((∑ η, weight w η * H W (setCl (η \ barOf S W) T)) * ind D ω) else 0) :=
        Finset.sum_congr rfl fun W _ => key W
    _ = ∑ ω, ∑ W, (if setCl ω S = W then
          weight w ω * ((∑ η, weight w η * H W (setCl (η \ barOf S W) T)) * ind D ω) else 0) :=
        Finset.sum_comm
    _ = _ :=
        Finset.sum_congr rfl fun ω _ => Fintype.sum_ite_eq (setCl ω S)
          fun W => weight w ω * ((∑ η, weight w η * H W (setCl (η \ barOf S W) T)) * ind D ω)

/-- **The other half-step** (the same identity with the roles of `S` and `T` exchanged):
`E[H(C_S, C_T) 1{S ↮ T}] = Σ_ω w(ω) 1{S ↮ T}(ω) · Σ_η w(η) H(C_S(η ∖ B_T(C_T ω)), C_T(ω))`.
[cite: VandenbergHaggstromKahn2005, §2.1 pp. 10–11 (the transition rule `Pr(C_S^i = ·) = φ(C_S = · | C_T = C_T^i)`)] -/
theorem set_sum_cond_cluster' (w : Sym2 V → ℝ) (hm : ∑ ω, weight w ω = 1) (S T : Set V)
    (H : Set (Sym2 V) → Set (Sym2 V) → ℝ) {D : Set (Set (Sym2 V))}
    (hD : ∀ ω, ω ∈ D ↔ ∀ s ∈ S, ∀ t ∈ T, ¬ (openGraph ω).Reachable s t) :
    ∑ ω, weight w ω * (H (setCl ω S) (setCl ω T) * ind D ω) =
      ∑ ω, weight w ω * ((∑ η, weight w η *
        H (setCl (η \ barOf T (setCl ω T)) S) (setCl ω T)) * ind D ω) := by
  have hD' : ∀ ω, ω ∈ D ↔ ∀ t ∈ T, ∀ s ∈ S, ¬ (openGraph ω).Reachable t s := fun ω => by
    rw [hD]
    exact ⟨fun h t ht s hs hts => h s hs t ht hts.symm, fun h s hs t ht hst => h t ht s hs hst.symm⟩
  exact set_sum_cond_cluster w hm T S (fun B A => H A B) hD'

end Sums

/-! ### The two-cluster Gibbs sampler (BHK §2.1) at `q = 1` -/

section Chain

variable {V : Type*}

/-- **The `T`-half-step of BHK's chain**: given `C_S = A`, the new `C_T` is the cluster of `T` in a
FRESH configuration `η` with the pairs meeting `S ∪ V(A)` deleted
("first choosing `C_T^i` according to `φ` conditioned on `{C_S = C_S^{i-1}}`"; by Lemma 2.4 this is
percolation on `G − F̄`). [cite: VandenbergHaggstromKahn2005, §2.1 pp. 10–11 (definition of the chain), Lemma 2.4 (p. 10)] -/
def halfT (S T : Set V) (A η : Set (Sym2 V)) : Set (Sym2 V) := setCl (η \ barOf S A) T

/-- **The `S`-half-step of BHK's chain**: given `C_T = B`, the new `C_S` is the cluster of `S` in a
fresh configuration with the pairs meeting `T ∪ V(B)` deleted ("and then, similarly, `C_S^i`
according to `Pr(C_S^i = ·) = φ(C_S = · | C_T = C_T^i)`").
[cite: VandenbergHaggstromKahn2005, §2.1 p. 11] -/
def halfS (S T : Set V) (B η : Set (Sym2 V)) : Set (Sym2 V) := setCl (η \ barOf T B) S

/-- **One step of BHK's chain** from the state `x = (C_S^{i-1}, C_T^{i-1})`, driven by the fresh
configurations `(η, η')`: `C_T^i = halfT x.1 η`, `C_S^i = halfS C_T^i η'` (the step does not look at
`C_T^{i-1}`). [cite: VandenbergHaggstromKahn2005, §2.1 pp. 10–11] -/
def gibbsStep (S T : Set V) (x : Set (Sym2 V) × Set (Sym2 V)) (η η' : Set (Sym2 V)) :
    Set (Sym2 V) × Set (Sym2 V) :=
  (halfS S T (halfT S T x.1 η) η', halfT S T x.1 η)

/-- **Regeneration**: the fresh configurations in which every open pair meeting `T` is a loop (no
open edge at `T`). [folklore] -/
def regenT (T : Set V) : Set (Set (Sym2 V)) := {η | ∀ e ∈ η, (∃ v ∈ e, v ∈ T) → e.IsDiag}

/-- `halfT` is decreasing in the conditioning cluster and increasing in the fresh configuration
(Remark 2.8: "`C_S^n` is increasing in the variables `X_e^i, Y_e^i`, and `C_T^n` is decreasing").
[cite: VandenbergHaggstromKahn2005, §2.1 Remark 2.8 (p. 12)] -/
theorem halfT_mono (S T : Set V) {A A' η η' : Set (Sym2 V)} (hA : A ⊆ A') (hη : η' ⊆ η) :
    halfT S T A' η' ⊆ halfT S T A η :=
  setCl_mono (sdiff_le_sdiff hη (barOf_mono S hA)) T

/-- `halfS` is decreasing in the conditioning cluster and increasing in the fresh configuration.
[cite: VandenbergHaggstromKahn2005, §2.1 Remark 2.8 (p. 12)] -/
theorem halfS_mono (S T : Set V) {B B' η η' : Set (Sym2 V)} (hB : B ⊆ B') (hη : η' ⊆ η) :
    halfS S T B' η' ⊆ halfS S T B η :=
  setCl_mono (sdiff_le_sdiff hη (barOf_mono T hB)) S

/-- On the regeneration event the `T`-half-step forgets the past: `C_T^i = ∅` whatever `C_S^{i-1}`
was. [folklore] -/
private theorem halfT_of_mem_regenT (S T : Set V) {η : Set (Sym2 V)} (hη : η ∈ regenT T) (A : Set (Sym2 V)) :
    halfT S T A η = ∅ :=
  setCl_eq_empty_of_forall fun e he hT => hη e he.1 hT

/-- On the regeneration event the whole step forgets the past. [folklore] -/
private theorem gibbsStep_of_mem_regenT (S T : Set V) {η : Set (Sym2 V)} (hη : η ∈ regenT T)
    (x : Set (Sym2 V) × Set (Sym2 V)) (η' : Set (Sym2 V)) :
    gibbsStep S T x η η' = (halfS S T ∅ η', ∅) := by
  simp only [gibbsStep, halfT_of_mem_regenT S T hη]

variable [Fintype V]

/-- **The one-step operator of BHK's chain**: `(E Φ)(x) = Σ_η w(η) Σ_η' w(η') Φ(step x η η')`, the
expectation of `Φ` after one step from `x` (fresh product configurations `η, η'`).
[cite: VandenbergHaggstromKahn2005, §2.1 pp. 10–11] -/
def gibbsE (w : Sym2 V → ℝ) (S T : Set V) (Φ : Set (Sym2 V) × Set (Sym2 V) → ℝ) :
    Set (Sym2 V) × Set (Sym2 V) → ℝ :=
  fun x => ∑ η, weight w η * ∑ η', weight w η' * Φ (gibbsStep S T x η η')

/-- The weight `ε = Σ_η w(η) 1{η ∈ regenT T}` of the regeneration event (`= ∏ (1 - w e)` over the
non-loop pairs `e` meeting `T`, see `regenWeight_eq_prod`). [folklore] -/
def regenWeight (w : Sym2 V → ℝ) (T : Set V) : ℝ := ∑ η, weight w η * ind (regenT T) η

/-- Unfolding of `gibbsE`. [folklore] -/
private theorem gibbsE_apply (w : Sym2 V → ℝ) (S T : Set V) (Φ : Set (Sym2 V) × Set (Sym2 V) → ℝ)
    (x : Set (Sym2 V) × Set (Sym2 V)) :
    gibbsE w S T Φ x = ∑ η, weight w η * ∑ η', weight w η' * Φ (gibbsStep S T x η η') := rfl

/-- **Regeneration contraction**: one step of the chain contracts oscillations by the factor
`1 - ε`, `ε` the weight of the regeneration event (on which the step forgets its starting state).
[folklore] (Doeblin's coupling argument; replaces "the chain is irreducible and aperiodic",
[cite: VandenbergHaggstromKahn2005, §2.1 p. 11]) -/
theorem gibbsE_sub_le {w : Sym2 V → ℝ} (hw0 : ∀ e, 0 ≤ w e) (hw1 : ∀ e, w e ≤ 1)
    (hm : ∑ ω, weight w ω = 1) (S T : Set V) {Φ : Set (Sym2 V) × Set (Sym2 V) → ℝ} {c : ℝ}
    (hΦ : ∀ x y, Φ x - Φ y ≤ c) (x y : Set (Sym2 V) × Set (Sym2 V)) :
    gibbsE w S T Φ x - gibbsE w S T Φ y ≤ (1 - regenWeight w T) * c := by
  have hin : ∀ η, ∑ η', weight w η' * Φ (gibbsStep S T x η η') -
      ∑ η', weight w η' * Φ (gibbsStep S T y η η') ≤ (1 - ind (regenT T) η) * c := by
    intro η
    by_cases hη : η ∈ regenT T
    · simp only [gibbsStep_of_mem_regenT S T hη, sub_self, ind_of_mem hη, zero_mul, le_refl]
    · rw [ind_of_not_mem hη, sub_zero, one_mul, ← Finset.sum_sub_distrib]
      calc ∑ η', (weight w η' * Φ (gibbsStep S T x η η') - weight w η' * Φ (gibbsStep S T y η η'))
          = ∑ η', weight w η' * (Φ (gibbsStep S T x η η') - Φ (gibbsStep S T y η η')) :=
            Finset.sum_congr rfl fun η' _ => by ring
        _ ≤ ∑ η', weight w η' * c := Finset.sum_le_sum fun η' _ =>
            mul_le_mul_of_nonneg_left (hΦ _ _) (weight_nonneg hw0 hw1 η')
        _ = c := by rw [← Finset.sum_mul, hm, one_mul]
  rw [gibbsE_apply, gibbsE_apply, ← Finset.sum_sub_distrib]
  calc ∑ η, (weight w η * ∑ η', weight w η' * Φ (gibbsStep S T x η η') -
        weight w η * ∑ η', weight w η' * Φ (gibbsStep S T y η η'))
      = ∑ η, weight w η * (∑ η', weight w η' * Φ (gibbsStep S T x η η') -
          ∑ η', weight w η' * Φ (gibbsStep S T y η η')) :=
        Finset.sum_congr rfl fun η _ => by ring
    _ ≤ ∑ η, weight w η * ((1 - ind (regenT T) η) * c) := Finset.sum_le_sum fun η _ =>
        mul_le_mul_of_nonneg_left (hin η) (weight_nonneg hw0 hw1 η)
    _ = (1 - regenWeight w T) * c := by
        have : ∀ η, weight w η * ((1 - ind (regenT T) η) * c) =
            c * weight w η - c * (weight w η * ind (regenT T) η) := fun η => by ring
        simp only [this, Finset.sum_sub_distrib, ← Finset.mul_sum, hm, regenWeight]
        ring

/-- **Regeneration contraction, iterated**: `osc(EⁿΦ) ≤ (1 - ε)ⁿ osc(Φ)` — the quantitative form of
"a Markov chain … which converges to a measure (on pairs of clusters) corresponding to (11)".
[folklore] (Doeblin coupling) [cite: VandenbergHaggstromKahn2005, §2.1 p. 9 and p. 11 (convergence of the chain)] -/
theorem gibbsE_iterate_sub_le {w : Sym2 V → ℝ} (hw0 : ∀ e, 0 ≤ w e) (hw1 : ∀ e, w e ≤ 1)
    (hm : ∑ ω, weight w ω = 1) (S T : Set V) (n : ℕ) {Φ : Set (Sym2 V) × Set (Sym2 V) → ℝ}
    {c : ℝ} (hΦ : ∀ x y, Φ x - Φ y ≤ c) (x y : Set (Sym2 V) × Set (Sym2 V)) :
    (gibbsE w S T)^[n] Φ x - (gibbsE w S T)^[n] Φ y ≤ (1 - regenWeight w T) ^ n * c := by
  induction n generalizing Φ c with
  | zero => simpa using hΦ x y
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    calc (gibbsE w S T)^[n] (gibbsE w S T Φ) x - (gibbsE w S T)^[n] (gibbsE w S T Φ) y
        ≤ (1 - regenWeight w T) ^ n * ((1 - regenWeight w T) * c) :=
          ih (gibbsE_sub_le hw0 hw1 hm S T hΦ)
      _ = (1 - regenWeight w T) ^ (n + 1) * c := by ring

end Chain

end BHK2006

/-! ### Measure-level statements for `prodBernoulli w` -/

section MeasureLevel

universe u

variable {V : Type u} [Fintype V]

open scoped Classical
open BHK2006 DecisionTree
open Percolation.Literature.LatticeModels (prodBernoulli_real_forall_notMem)

/-- **The regeneration weight is `∏ (1 - w e)` over the non-loop pairs meeting `T`** (so it is
positive as soon as every such pair has `w e < 1`): the product-measure probability that all pairs of
a finite set are closed. [cite: GrimmettPercolation1999, §1.3 p. 10 (product measure)] -/
theorem BHK2006.regenWeight_eq_prod (w : Sym2 V → unitInterval) (T : Set V) :
    regenWeight (fun e => (w e : ℝ)) T =
      ∏ e ∈ Finset.univ.filter (fun e : Sym2 V => ¬ e.IsDiag ∧ ∃ v ∈ e, v ∈ T),
        (1 - (w e : ℝ)) := by
  classical
  have h1 : regenWeight (fun e => (w e : ℝ)) T = (prodBernoulli w).real (regenT T) := by
    rw [regenWeight, ← integral_indicator_one (MeasurableSet.of_discrete (s := regenT T)),
      integral_prodBernoulli_eq_sum]
    refine Finset.sum_congr rfl fun η _ => ?_
    by_cases hη : η ∈ regenT T
    · rw [Set.indicator_of_mem hη, ind_of_mem hη, Pi.one_apply]
    · rw [Set.indicator_of_notMem hη, ind_of_not_mem hη, mul_zero]
  have h2 : regenT T = {η : Set (Sym2 V) |
      ∀ e ∈ Finset.univ.filter (fun e : Sym2 V => ¬ e.IsDiag ∧ ∃ v ∈ e, v ∈ T), e ∉ η} := by
    ext η
    simp only [regenT, Set.mem_setOf_eq, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro h e ⟨hd, hv⟩ heη
      exact hd (h e heη hv)
    · intro h e he hv
      by_contra hd
      exact h e ⟨hd, hv⟩ he
  rw [h1, h2, prodBernoulli_real_forall_notMem]

end MeasureLevel

end Percolation.Literature
