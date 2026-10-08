import Mathlib.Algebra.BigOperators.Ring.Finset
import Percolation.Literature.ConstrainedClusters
import Percolation.Util.Linter

/-!
# The deterministic counting lemma of the Burton–Keane uniqueness argument

Uniqueness of the infinite open cluster (Aizenman–Kesten–Newman 1987, Burton–Keane 1989): this file contains the graph-theoretic core of
the Burton–Keane proof in the form used by Bollobás–Riordan, *Percolation* (CUP 2006), Ch. 5,
§5.1, proof of Thm. 4 (pp. 106–109): the "cut-ball" counting via their Lemma 3.

* Bollobás–Riordan 2006, Ch. 5, **Lemma 3** (p. 106): "Let `G` be a finite graph with `k`
  components, and let `L` and `C = {c₁, …, c_s}` be disjoint sets of vertices of `G`, with at
  least one `cᵢ` in each component of `G`. Let `m₁, …, m_s` be integers, each at least `2`.
  Suppose that for each `i`, deleting the vertex `cᵢ` disconnects the component containing `cᵢ`
  into smaller components, `mᵢ` of which contain vertices of `L`. Then `|L| ≥ 2k + Σᵢ (mᵢ - 2)`."
  In the proof of Thm. 4 it is applied with `mᵢ ≥ 3` to the graph `H` obtained by contracting
  each cut-ball `Cᵢ` to a vertex `cᵢ`, giving `|L| ≥ s + 2` (p. 109).

  There `L = {ℓ₁, …, ℓ_t}` is the set of vertices of `H` obtained by contracting the INFINITE open
  clusters `L₁, …, L_t` left after closing all cut-balls (p. 108), and the separate step (4),
  `t ≤ |S_{n+1}(x₀)|` ("Each `Lᵢ` contains a site in `S_{n+1}(x₀)`"), bounds `|L|` by the size of
  the boundary sphere.

We prove the consequence `|L| ≥ s + 2` directly for the *uncontracted* graph, with the cut-balls
as **hubs**: pairwise disjoint, internally connected, non-empty finite vertex sets `K`, disjoint
from `L`, such that `G - K` (delete the vertices of `K`) has at least three components adjacent
to `K` and containing vertices of `L` (`IsHub`). Statement: `card_add_two_le_card_of_isHub` — if
`𝓚 ≠ ∅` is such a family of hubs then `|𝓚| + 2 ≤ |L|`; no finiteness of `G` is needed. In the
percolation application (`UniquenessInfiniteCluster.lean`) the lemma is instantiated with `G` the
open graph of the box `Λ_{n+1}` and `L := ∂ⁱⁿΛ_{n+1}` its inner vertex boundary; this merges
Bollobás–Riordan's two steps: each of the (at least three) infinite branches at a cut-ball,
followed inside `Λ_{n+1}` up to its first exit, ends in a distinct component of `G - K` at a
vertex of `∂ⁱⁿΛ_{n+1}`, so a cut-ball is a hub relative to `∂ⁱⁿΛ_{n+1}`, and the conclusion
`s + 2 ≤ |∂ⁱⁿΛ_{n+1}|` is their `s + 2 ≤ t ≤ |S_{n+1}(x₀)|`.

Proof (ours; Bollobás–Riordan argue via a minimal spanning tree instead): induction on `|𝓚|`.
Remove one hub `K` and split `L` and the remaining hubs along the components `Q` of `G - K`
(each remaining hub is connected and misses `K`, so lies in one component). In each component
`Q` containing `s_Q ≥ 1` hubs, the induction hypothesis applied to the hubs in `Q` and to
`L_Q := (L ∩ Q) ∪ {k₀}`, `k₀ ∈ K` a fixed vertex standing in for "the rest of the graph through
`K`", gives `s_Q + 2 ≤ |L ∩ Q| + 1`; the three `L`-carrying branches of `K` lie in three
distinct components, each contributing at least one more vertex of `L` than hubs. Summing over
components, `|L| ≥ (|𝓚| - 1) + 3`.

We add walk lemmas over it: reachability from a support inside `S`, `withinGraph_withinGraph`, and
the first-exit decomposition `exists_adj_reachable_withinGraph_of_walk` — the `Set`-valued,
spanning-graph form of `exists_innerBoundary_reachable_of_walk` (`SiteConnectionTools.lean`, stated
for a `Finset` in a locally finite graph, a walk *ending* outside it, and reachability in the
induced subtype graph): here `S` is any set of vertices (it is used with `S = Kᶜ`, the complement of
a finite hub, and with `S` a box), the walk need only *visit* `Sᶜ`, and the lemma returns the exit
edge `(a, b)` with `b` on the walk.

Mathlib: `SimpleGraph.Reachable`, `SimpleGraph.ConnectedComponent`, `SimpleGraph.Walk.transfer`,
`SimpleGraph.Walk.mapLe`, `Finset.card_eq_sum_card_fiberwise`, `Finset.card_biUnion`,
`Finset.card_eq_sum_ite`.
-/

namespace Percolation.Literature

open SimpleGraph Finset

variable {V : Type*}

/-! ### Walks inside a set of vertices: API over `withinGraph` -/

/-- `withinGraph` is monotone in the graph. [folklore] -/
theorem withinGraph_mono_left {G G' : SimpleGraph V} (h : G ≤ G') (S : Set V) :
    withinGraph G S ≤ withinGraph G' S :=
  fun _ _ hxy => ⟨h hxy.1, hxy.2.1, hxy.2.2⟩

/-- Restricting twice is restricting to the intersection. [folklore] -/
theorem withinGraph_withinGraph (G : SimpleGraph V) (S T : Set V) :
    withinGraph (withinGraph G S) T = withinGraph G (S ∩ T) := by
  ext x y
  simp only [withinGraph_adj, Set.mem_inter_iff]
  tauto

/-- A walk of `G` all of whose vertices lie in `S` joins its endpoints in `withinGraph G S`. [folklore] -/
theorem reachable_withinGraph_of_support_subset (G : SimpleGraph V) {S : Set V} {u v : V}
    (p : G.Walk u v) (hp : ∀ x ∈ p.support, x ∈ S) : (withinGraph G S).Reachable u v := by
  induction p with
  | nil => rfl
  | @cons x y z h p ih =>
    have hx : x ∈ S := hp x (by simp)
    have hp' : ∀ a ∈ p.support, a ∈ S := fun a ha => hp a (by simp [ha])
    have hy : y ∈ S := hp' y p.start_mem_support
    exact (Adj.reachable (show (withinGraph G S).Adj x y from ⟨h, hx, hy⟩)).trans (ih hp')

/-- **First exit decomposition.** A walk of `G` which starts in `S` and visits a vertex outside
`S` has an initial segment inside `S` (a walk of `withinGraph G S`) from its start `u` to a vertex
`a ∈ S` adjacent to a vertex `b ∉ S` of the walk (the first vertex of the walk outside `S`).
`Set`-valued, spanning-graph form of `exists_innerBoundary_reachable_of_walk`
(`SiteConnectionTools.lean`; there `S` is a `Finset` of a locally finite graph, the walk ends
outside `S`, the exit vertex is returned as a member of `innerBoundary G S` and the initial
segment as a walk of the induced subtype graph); this version allows infinite `S` (complements
of finite sets), a walk merely visiting `Sᶜ`, and returns the exit edge `(a, b)` with `b` on the
walk. [folklore] -/
theorem exists_adj_reachable_withinGraph_of_walk (G : SimpleGraph V) {S : Set V} {u v : V}
    (p : G.Walk u v) (hu : u ∈ S) (hx : ∃ x ∈ p.support, x ∉ S) :
    ∃ a b, a ∈ S ∧ b ∉ S ∧ G.Adj a b ∧ b ∈ p.support ∧ (withinGraph G S).Reachable u a := by
  induction p with
  | nil =>
    obtain ⟨x, hx, hxS⟩ := hx
    rw [Walk.support_nil, List.mem_singleton] at hx
    exact absurd (hx ▸ hu) hxS
  | @cons x y z h p ih =>
    by_cases hy : y ∈ S
    · obtain ⟨a, b, ha, hb, hab, hbs, hr⟩ := by
        refine ih hy ?_
        obtain ⟨w, hw, hwS⟩ := hx
        rw [Walk.support_cons, List.mem_cons] at hw
        rcases hw with rfl | hw
        · exact absurd hu hwS
        · exact ⟨w, hw, hwS⟩
      exact ⟨a, b, ha, hb, hab, by simp [hbs],
        (Adj.reachable (show (withinGraph G S).Adj x y from ⟨h, hu, hy⟩)).trans hr⟩
    · exact ⟨x, y, hu, hy, h, by simp, Reachable.refl _⟩

/-! ### Hubs and the counting lemma -/

/-- `K` is a **hub** of `G` relative to the vertex set `L` — the uncontracted form of the
hypothesis "`mᵢ ≥ 3`" of Bollobás–Riordan 2006, Ch. 5, Lemma 3 (as it arises in the proof of
Thm. 4, p. 109: "the condition that `Cᵢ` is a cut-ball says exactly that deleting `cᵢ` from `H`
disconnects a component into at least three components containing vertices of `L`", where in
the source `L = {ℓ₁, …, ℓ_t}` are the contracted infinite clusters left after closing the
cut-balls; in `UniquenessInfiniteCluster.lean`, `L` is the inner boundary of the box, met by
every such infinite cluster): `K` is a non-empty finite vertex set, disjoint from `L`, connected
through edges of `G` inside `K`, and there are three vertices `w 0, w 1, w 2` outside `K`, each
adjacent to a vertex of `K`, no two of them joined in `G - K = withinGraph G Kᶜ`, and each joined
in `G - K` to a vertex of `L`. [cite: BollobasRiordanPercolation2006, Ch. 5, Lemma 3 and proof of Thm. 4 (p. 109)] -/
structure IsHub (G : SimpleGraph V) (L : Finset V) (K : Finset V) : Prop where
  /-- a hub is non-empty -/
  nonempty : K.Nonempty
  /-- a hub contains no vertex of `L` -/
  disjoint : Disjoint K L
  /-- a hub is connected through edges of `G` with both endpoints in the hub -/
  connected : ∀ x ∈ K, ∀ y ∈ K, (withinGraph G ↑K).Reachable x y
  /-- three branches: neighbours of the hub in three distinct components of `G - K`, each
  component containing a vertex of `L` -/
  branches : ∃ w : Fin 3 → V, (∀ i, w i ∉ K) ∧ (∀ i, ∃ k ∈ K, G.Adj k (w i)) ∧
      (∀ i j, (withinGraph G (↑K)ᶜ).Reachable (w i) (w j) → i = j) ∧
      (∀ i, ∃ ℓ ∈ L, (withinGraph G (↑K)ᶜ).Reachable (w i) ℓ)

/-- Changing the target set `L` of a hub `K'` in the presence of another hub-like set `K`
(connected inside, disjoint from `K'`): `K'` is still a hub for any `L'` avoiding `K'` which
contains a vertex `k₀ ∈ K` and every vertex of `L` joined to `K'` in `G - K`. Indeed a branch of
`K'` reaches some `ℓ ∈ L` in `G - K'`; if the joining walk avoids `K` then `ℓ` is joined to `K'`
in `G - K`, hence `ℓ ∈ L'`; otherwise the walk enters `K`, inside which it can be continued to
`k₀ ∈ L'`, still avoiding `K'`. (The step "apply the induction hypothesis inside one component of
`G - K`, with `K` standing in for the rest of the graph" of our proof of the counting lemma.) [cite: BollobasRiordanPercolation2006, Ch. 5, Lemma 3] -/
theorem IsHub.of_reachable {G : SimpleGraph V} {L L' K K' : Finset V} (hK' : IsHub G L K')
    (hKconn : ∀ x ∈ K, ∀ y ∈ K, (withinGraph G ↑K).Reachable x y) (hKK' : Disjoint K K')
    {k₀ : V} (hk₀ : k₀ ∈ K) (hk₀L' : k₀ ∈ L') (hK'L' : Disjoint K' L')
    (hLL' : ∀ ℓ ∈ L, ∀ x ∈ K', (withinGraph G (↑K)ᶜ).Reachable x ℓ → ℓ ∈ L') :
    IsHub G L' K' := by
  obtain ⟨w, hw1, hw2, hw3, hw4⟩ := hK'.branches
  refine ⟨hK'.nonempty, hK'L', hK'.connected, w, hw1, hw2, hw3, fun i => ?_⟩
  -- `K ⊆ (K')ᶜ` and `K' ⊆ Kᶜ`
  have hKsub : (↑K : Set V) ⊆ (↑K' : Set V)ᶜ := fun x hx hx' => Finset.disjoint_left.1 hKK' hx hx'
  obtain ⟨ℓ, hℓL, hreach⟩ := hw4 i
  obtain ⟨π⟩ := hreach
  by_cases hA : ∀ x ∈ π.support, x ∈ (↑K : Set V)ᶜ
  · -- the joining walk avoids `K`: then `ℓ` is joined to `K'` in `G - K`
    refine ⟨ℓ, ?_, ⟨π⟩⟩
    obtain ⟨k, hk, hadj⟩ := hw2 i
    refine hLL' ℓ hℓL k hk ?_
    have hwi : w i ∈ (↑K : Set V)ᶜ := hA _ π.start_mem_support
    have hkK : k ∈ (↑K : Set V)ᶜ := fun hkK => Finset.disjoint_left.1 hKK' hkK hk
    have h1 : (withinGraph G (↑K)ᶜ).Adj k (w i) := ⟨hadj, hkK, hwi⟩
    exact h1.reachable.trans (reachable_withinGraph_of_support_subset G
      (π.mapLe (withinGraph_le G _)) (by simpa only [Walk.support_mapLe_eq_support] using hA))
  · -- the joining walk enters `K`: continue inside `K` to `k₀`
    push Not at hA
    refine ⟨k₀, hk₀L', ?_⟩
    have hin : ∀ b ∈ K, (withinGraph G (↑K')ᶜ).Reachable b k₀ := fun b hb =>
      (hKconn b hb k₀ hk₀).mono (withinGraph_mono G hKsub)
    by_cases hwi : w i ∈ K
    · exact hin _ hwi
    · obtain ⟨a, b, -, hb, hab, -, hr⟩ :=
        exists_adj_reachable_withinGraph_of_walk (withinGraph G (↑K')ᶜ) π
          (S := (↑K : Set V)ᶜ) hwi (by simpa only [Set.mem_compl_iff, not_not] using hA)
      have hb' : b ∈ K := by simpa only [Set.mem_compl_iff, not_not, Finset.mem_coe] using hb
      exact ((hr.mono (withinGraph_le _ _)).trans hab.reachable).trans (hin b hb')

/-- **The counting lemma** (Bollobás–Riordan 2006, Ch. 5, Lemma 3 in the form used on p. 109,
`|L| ≥ s + 2`; uncontracted version with hubs). If `𝓚` is a non-empty finite family of pairwise
disjoint hubs of `G` relative to `L` (`IsHub`: connected inside, avoiding `L`, with three
neighbours in distinct components of `G - K` each containing a vertex of `L`), then
`|𝓚| + 2 ≤ |L|`. Proof by induction on `|𝓚|` (module docstring); Bollobás–Riordan contract the
hubs and pass to a minimal spanning tree instead. [cite: BollobasRiordanPercolation2006, Ch. 5, Lemma 3; proof of Thm. 4 p. 109] -/
theorem card_add_two_le_card_of_isHub (G : SimpleGraph V) (L : Finset V)
    (𝓚 : Finset (Finset V)) (hne : 𝓚.Nonempty)
    (hdisj : ∀ K ∈ 𝓚, ∀ K' ∈ 𝓚, K ≠ K' → Disjoint K K') (hhub : ∀ K ∈ 𝓚, IsHub G L K) :
    𝓚.card + 2 ≤ L.card := by
  classical
  suffices H : ∀ (n : ℕ) (L : Finset V) (𝓚 : Finset (Finset V)), 𝓚.card = n → 𝓚.Nonempty →
      (∀ K ∈ 𝓚, ∀ K' ∈ 𝓚, K ≠ K' → Disjoint K K') → (∀ K ∈ 𝓚, IsHub G L K) →
      𝓚.card + 2 ≤ L.card from H _ L 𝓚 rfl hne hdisj hhub
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro L 𝓚 hn hne hdisj hhub
  obtain ⟨K, hK⟩ := hne
  have hubK := hhub K hK
  obtain ⟨k₀, hk₀⟩ := hubK.nonempty
  obtain ⟨w, hw1, hw2, hw3, hw4⟩ := hubK.branches
  -- `G' = G - K`, its components, and the remaining hubs
  set G' : SimpleGraph V := withinGraph G (↑K : Set V)ᶜ with hG'
  set mk : V → G'.ConnectedComponent := G'.connectedComponentMk with hmk
  set 𝓚' : Finset (Finset V) := 𝓚.erase K with h𝓚'
  set Lc : G'.ConnectedComponent → Finset V := fun c => L.filter fun x => mk x = c with hLc
  set Kc : G'.ConnectedComponent → Finset (Finset V) :=
    fun c => 𝓚'.filter fun K' => ∃ x ∈ K', mk x = c with hKc
  have h𝓚'sub : 𝓚' ⊆ 𝓚 := erase_subset _ _
  have hK'ne : ∀ K' ∈ 𝓚', K' ≠ K := fun K' h => (mem_erase.1 h).1
  have hK'disj : ∀ K' ∈ 𝓚', Disjoint K K' := fun K' h => hdisj K hK K' (h𝓚'sub h) (hK'ne K' h).symm
  -- (1) each remaining hub lies inside one component of `G - K`
  have hF1 : ∀ K' ∈ 𝓚', ∀ x ∈ K', ∀ y ∈ K', mk x = mk y := by
    intro K' hK' x hx y hy
    apply ConnectedComponent.sound
    refine ((hhub K' (h𝓚'sub hK')).connected x hx y hy).mono (withinGraph_mono G ?_)
    exact fun z hz hzK => Finset.disjoint_left.1 (hK'disj K' hK') hzK hz
  -- (2) the induction hypothesis inside each component carrying hubs
  have hF2 : ∀ c, (Kc c).Nonempty → (Kc c).card + 1 ≤ (Lc c).card := by
    intro c hc
    have hlt : (Kc c).card < n :=
      calc (Kc c).card ≤ 𝓚'.card := card_le_card (filter_subset _ _)
        _ < 𝓚.card := card_erase_lt_of_mem hK
        _ = n := hn
    have hk₀L : k₀ ∉ Lc c := fun h => Finset.disjoint_left.1 hubK.disjoint hk₀ (mem_filter.1 h).1
    have key := ih _ hlt (insert k₀ (Lc c)) (Kc c) rfl hc
      (fun K₁ h₁ K₂ h₂ hne => hdisj K₁ (h𝓚'sub (mem_filter.1 h₁).1) K₂ (h𝓚'sub (mem_filter.1 h₂).1) hne)
      ?_
    · rw [card_insert_of_notMem hk₀L] at key
      omega
    · intro K' hK'
      obtain ⟨hK'𝓚', x₀, hx₀, hx₀c⟩ := mem_filter.1 hK'
      have hub' := hhub K' (h𝓚'sub hK'𝓚')
      refine hub'.of_reachable hubK.connected (hK'disj K' hK'𝓚') hk₀ (mem_insert_self _ _) ?_ ?_
      · rw [Finset.disjoint_left]
        rintro z hz hz'
        rcases mem_insert.1 hz' with rfl | hz'
        · exact Finset.disjoint_left.1 (hK'disj K' hK'𝓚') hk₀ hz
        · exact Finset.disjoint_left.1 hub'.disjoint hz (mem_filter.1 hz').1
      · intro ℓ hℓ x hx hr
        refine mem_insert_of_mem (mem_filter.2 ⟨hℓ, ?_⟩)
        rw [← hx₀c, ← hF1 K' hK'𝓚' x hx x₀ hx₀]
        exact (ConnectedComponent.sound hr).symm
  -- (3) the three branches of `K` live in three distinct components, each carrying `L`
  set cw : Fin 3 → G'.ConnectedComponent := fun i => mk (w i) with hcw
  have hcw_inj : Function.Injective cw := fun i j h => hw3 i j (ConnectedComponent.exact h)
  have hLc_pos : ∀ i, 1 ≤ (Lc (cw i)).card := by
    intro i
    obtain ⟨ℓ, hℓ, hr⟩ := hw4 i
    exact card_pos.2 ⟨ℓ, mem_filter.2 ⟨hℓ, (ConnectedComponent.sound hr).symm⟩⟩
  set T : Finset G'.ConnectedComponent := univ.image cw with hT
  have hTcard : T.card = 3 := by
    rw [hT, card_image_of_injective _ hcw_inj]; simp
  -- (4) counting along the components
  set S : Finset G'.ConnectedComponent := L.image mk ∪ 𝓚'.biUnion fun K' => K'.image mk with hS
  have hTS : T ⊆ S := by
    intro c hc
    obtain ⟨i, -, rfl⟩ := mem_image.1 hc
    obtain ⟨ℓ, hℓ, hr⟩ := hw4 i
    exact mem_union_left _ (mem_image.2 ⟨ℓ, hℓ, (ConnectedComponent.sound hr).symm⟩)
  have hLsum : L.card = ∑ c ∈ S, (Lc c).card :=
    card_eq_sum_card_fiberwise fun x hx => mem_union_left _ (mem_image_of_mem _ hx)
  have hKsum : 𝓚'.card = ∑ c ∈ S, (Kc c).card := by
    have hcover : 𝓚' = S.biUnion Kc := by
      ext K'
      simp only [mem_biUnion]
      constructor
      · intro hK'
        obtain ⟨x, hx⟩ := (hhub K' (h𝓚'sub hK')).nonempty
        exact ⟨mk x, mem_union_right _ (mem_biUnion.2 ⟨K', hK', mem_image_of_mem _ hx⟩),
          mem_filter.2 ⟨hK', x, hx, rfl⟩⟩
      · rintro ⟨c, -, hc⟩
        exact (mem_filter.1 hc).1
    rw [hcover, card_biUnion]
    intro c₁ _ c₂ _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro K' hK₁ hK₂
    obtain ⟨hK', x, hx, hx'⟩ := mem_filter.1 hK₁
    obtain ⟨-, y, hy, hy'⟩ := mem_filter.1 hK₂
    exact hne (hx'.symm.trans ((hF1 K' hK' x hx y hy).trans hy'))
  have hpt : ∀ c ∈ S, (Kc c).card + (if c ∈ T then 1 else 0) ≤ (Lc c).card := by
    intro c _
    by_cases hKc : (Kc c).Nonempty
    · have := hF2 c hKc
      split_ifs <;> omega
    · rw [not_nonempty_iff_eq_empty] at hKc
      rw [hKc, card_empty]
      split_ifs with hcT
      · obtain ⟨i, -, rfl⟩ := mem_image.1 hcT
        simpa using hLc_pos i
      · simp
  have hsum := sum_le_sum hpt
  rw [sum_add_distrib, ← hLsum, ← hKsum, ← card_eq_sum_ite hTS, hTcard, h𝓚',
    card_erase_of_mem hK] at hsum
  have h1 : 1 ≤ 𝓚.card := card_pos.2 ⟨K, hK⟩
  omega

end Percolation.Literature
