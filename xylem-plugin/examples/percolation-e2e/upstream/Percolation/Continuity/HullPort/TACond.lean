import Percolation.Continuity.HullPort.DeletedEdges
import Percolation.Continuity.HullPort.TADefs
import Percolation.Util.Linter

/-!
# Marker dominance with an avoided set: conditioning on `C_X` and the step `Δ_N` for `T_A`

Part 3 of the proof of `T_A ≥ 0`, set-`X` form, for the functionals of
`Continuity/HullPort/TADefs.lean`:
* `HullPort.set_sum_cond_sdiff` — conditioning on the open edge cluster `C_X` of a vertex SET: for any kernel `K`,
  `Σ_ω w(ω) K(C_X ω, ω ∖ X̄(C_X ω)) = Σ_ω w(ω) Σ_η w(η) K(C_X ω, η ∖ X̄(C_X ω))` (van den Berg–Häggström–Kahn's Lemma 2.4 /
  display (10): given `C_X`, the configuration off the pairs meeting `X ∪ V(C_X)` is fresh);
* `HullPort.cut_insert_vertex` — `cut_{X∪{v}}(ω) = cut_X(ω) ∪ cut_{{v}}(ω ∖ cut_X ω)`; `HullPort.delE_union`;
* `HullPort.taB_insert_le` — step (II): `B_{X∪{v}} ≤ B_X − A^{(v)}_X` ("adding `v` to the avoided set costs at
  least the `v`-marker term"), from the hypothesis `hPv` = Lemma P_v in every deleted graph (Gladkov's
  decision-tree Harris–Kleitman inequality + BHK Thm 1.3), applied fibrewise in `C_X`.
[cite: VandenbergHaggstromKahn2005, §2.1 Lemma 2.4 (p. 10), §1 display (10) (pp. 7–8) — corollaries]
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
/-- The cut set of `X` is the set of pairs meeting `X ∪ V(C_X)`. [folklore] -/
theorem cut_eq_barOf (X : Set V) (ω : Set (Sym2 V)) : cut X ω = barOf X (setCl ω X) := by
  rw [BHK2006.barOf_setCl_eq]; rfl

/-- **Conditioning on `C_X`** (BHK's Lemma 2.4 / display (10) for a vertex set `X` and an arbitrary kernel): given
`{C_X = W}`, the configuration off `X̄(W)` (the pairs meeting `X ∪ V(W)`) is a fresh product configuration.
[cite: VandenbergHaggstromKahn2005, §2.1 Lemma 2.4 (p. 10); §1 pp. 7–8, display (10) — corollary] -/
theorem set_sum_cond_sdiff (w : Sym2 V → ℝ) (hm : ∑ ω, weight w ω = 1) (S : Set V)
    (K : Set (Sym2 V) → Set (Sym2 V) → ℝ) :
    ∑ ω, weight w ω * K (setCl ω S) (ω \ barOf S (setCl ω S)) =
      ∑ ω, weight w ω * ∑ η, weight w η * K (setCl ω S) (η \ barOf S (setCl ω S)) := by
  classical
  have hsd : ∀ (A ω : Set (Sym2 V)), (ω \ A) \ A = ω \ A := fun A ω => by
    rw [Set.sdiff_sdiff, Set.union_self]
  have key : ∀ W : Set (Sym2 V),
      ∑ ω, (if setCl ω S = W then weight w ω * K W (ω \ barOf S W) else 0) =
      ∑ ω, (if setCl ω S = W then weight w ω * ∑ η, weight w η * K W (η \ barOf S W) else 0) := by
    intro W
    set A : Set (Sym2 V) := barOf S W with hA
    set Φ : Set (Sym2 V) → Set (Sym2 V) → ℝ := fun ζ η => if setCl ζ S = W then K W (η \ A) else 0 with hΦ
    have h1 : ∀ ω, (if setCl ω S = W then weight w ω * K W (ω \ A) else 0) = weight w ω * Φ (ω ∩ A) (ω \ A) := by
      intro ω
      simp only [hΦ, hA, setCl_inter_barOf_eq_iff]
      split_ifs with hW
      · rw [← hA, hsd]
      · rw [mul_zero]
    have h2 : ∀ ω, weight w ω * ∑ ω', weight w ω' * Φ (ω ∩ A) (ω' \ A) =
        (if setCl ω S = W then weight w ω * ∑ η, weight w η * K W (η \ A) else 0) := by
      intro ω
      simp only [hΦ, hA, setCl_inter_barOf_eq_iff]
      split_ifs with hW
      · rw [← hA]
        refine congrArg (weight w ω * ·) (Finset.sum_congr rfl fun η _ => ?_)
        rw [hsd]
      · simp
    calc ∑ ω, (if setCl ω S = W then weight w ω * K W (ω \ A) else 0)
        = (∑ ω, weight w ω) * ∑ ω, weight w ω * Φ (ω ∩ A) (ω \ A) := by
          rw [hm, one_mul]; exact Finset.sum_congr rfl fun ω _ => h1 ω
      _ = ∑ ω, weight w ω * ∑ ω', weight w ω' * Φ (ω ∩ A) (ω' \ A) := blockFubini w A Φ
      _ = _ := Finset.sum_congr rfl fun ω _ => h2 ω
  calc ∑ ω, weight w ω * K (setCl ω S) (ω \ barOf S (setCl ω S))
      = ∑ ω, ∑ W, (if setCl ω S = W then weight w ω * K W (ω \ barOf S W) else 0) :=
        Finset.sum_congr rfl fun ω _ =>
          (Fintype.sum_ite_eq (setCl ω S) fun W => weight w ω * K W (ω \ barOf S W)).symm
    _ = ∑ W, ∑ ω, (if setCl ω S = W then weight w ω * K W (ω \ barOf S W) else 0) := Finset.sum_comm
    _ = ∑ W, ∑ ω, (if setCl ω S = W then weight w ω * ∑ η, weight w η * K W (η \ barOf S W) else 0) :=
        Finset.sum_congr rfl fun W _ => key W
    _ = ∑ ω, ∑ W, (if setCl ω S = W then weight w ω * ∑ η, weight w η * K W (η \ barOf S W) else 0) :=
        Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun ω _ =>
        Fintype.sum_ite_eq (setCl ω S) fun W => weight w ω * ∑ η, weight w η * K W (η \ barOf S W)

omit [Fintype V] in
/-- `C_{X ∪ Y} = C_X ∪ C_Y` (edge clusters of vertex sets). [folklore] -/
theorem setCl_union (ω : BondConfig V) (X Y : Set V) : setCl ω (X ∪ Y) = setCl ω X ∪ setCl ω Y := by
  ext e; simp only [mem_setCl_iff, Set.mem_union]
  constructor
  · rintro ⟨s, hs | hs, he⟩
    · exact Or.inl ⟨s, hs, he⟩
    · exact Or.inr ⟨s, hs, he⟩
  · rintro (⟨s, hs, he⟩ | ⟨s, hs, he⟩)
    · exact ⟨s, Or.inl hs, he⟩
    · exact ⟨s, Or.inr hs, he⟩

omit [Fintype V] in
/-- `(X ∪ Y)‾(W ∪ W') = X̄(W) ∪ Ȳ(W')`. [folklore] -/
theorem barOf_union (X Y : Set V) (W W' : Set (Sym2 V)) :
    barOf (X ∪ Y) (W ∪ W') = barOf X W ∪ barOf Y W' ∪ (barOf X W' ∪ barOf Y W) := by
  ext e
  simp only [mem_barOf_iff, Set.mem_union]
  constructor
  · rintro ⟨u, hu, (hX | hY) | ⟨e', he' | he', hue'⟩⟩
    · exact Or.inl (Or.inl ⟨u, hu, Or.inl hX⟩)
    · exact Or.inl (Or.inr ⟨u, hu, Or.inl hY⟩)
    · exact Or.inl (Or.inl ⟨u, hu, Or.inr ⟨e', he', hue'⟩⟩)
    · exact Or.inl (Or.inr ⟨u, hu, Or.inr ⟨e', he', hue'⟩⟩)
  · rintro ((⟨u, hu, h | ⟨e', he', hue'⟩⟩ | ⟨u, hu, h | ⟨e', he', hue'⟩⟩) | (⟨u, hu, h | ⟨e', he', hue'⟩⟩ | ⟨u, hu, h | ⟨e', he', hue'⟩⟩))
    · exact ⟨u, hu, Or.inl (Or.inl h)⟩
    · exact ⟨u, hu, Or.inr ⟨e', Or.inl he', hue'⟩⟩
    · exact ⟨u, hu, Or.inl (Or.inr h)⟩
    · exact ⟨u, hu, Or.inr ⟨e', Or.inr he', hue'⟩⟩
    · exact ⟨u, hu, Or.inl (Or.inl h)⟩
    · exact ⟨u, hu, Or.inr ⟨e', Or.inr he', hue'⟩⟩
    · exact ⟨u, hu, Or.inl (Or.inr h)⟩
    · exact ⟨u, hu, Or.inr ⟨e', Or.inl he', hue'⟩⟩

omit [Fintype V] in
/-- **Adding a vertex to the avoided set**: the cut set of `X ∪ {v}` is the cut set of `X` together with the cut set of
`{v}` in the configuration with the cut set of `X` deleted. [folklore] -/
theorem cut_insert_vertex (X : Set V) (v : V) (ω : Set (Sym2 V)) :
    cut (insert v X) ω = cut X ω ∪ cut {v} (ω \ cut X ω) := by
  have hins : insert v X = X ∪ {v} := by ext; simp
  by_cases hv : ∃ x ∈ X, (openGraph ω).Reachable x v
  · -- `v` lies in `X ∪ V(C_X)`: both sides are the cut set of `X`
    obtain ⟨x, hx, hxv⟩ := hv
    have h1 : cut (insert v X) ω = cut X ω := by
      apply Set.Subset.antisymm
      · rintro e ⟨u, hu, t, ht, htu⟩
        rcases Set.mem_insert_iff.1 ht with rfl | ht
        · exact ⟨u, hu, x, hx, hxv.trans htu⟩
        · exact ⟨u, hu, t, ht, htu⟩
      · rintro e ⟨u, hu, t, ht, htu⟩
        exact ⟨u, hu, t, Set.mem_insert_of_mem _ ht, htu⟩
    -- `v` is isolated in `ω ∖ cut X ω`
    have hiso : ∀ c, (openGraph (ω \ cut X ω)).Reachable v c → c = v := by
      intro c hvc
      rw [SimpleGraph.reachable_iff_reflTransGen] at hvc
      induction hvc with
      | refl => rfl
      | @tail b c _ hbc ih =>
        subst ih
        obtain ⟨⟨_, hnot⟩, _⟩ := (openGraph_adj _ _ c).1 hbc
        exact absurd ⟨_, Sym2.mem_mk_left _ c, x, hx, hxv⟩ hnot
    have h2 : cut {v} (ω \ cut X ω) ⊆ cut X ω := by
      rintro e ⟨u, hu, t, ht, htu⟩
      rw [Set.mem_singleton_iff] at ht
      subst ht
      have huv : u = t := hiso u htu
      subst huv
      exact ⟨u, hu, x, hx, hxv⟩
    rw [h1]
    exact (Set.union_eq_left.2 h2).symm
  · -- `v ∉ X ∪ V(C_X)`: the cluster of `v` lives in `ω ∖ cut X ω`
    have hvK : ¬ (v ∈ X ∨ ∃ e ∈ setCl ω X, v ∈ e) := fun h => by
      obtain ⟨x, hx, hxv⟩ := (setReach_iff ω X v).2 h
      exact hv ⟨x, hx, hxv⟩
    have hT : ∀ t ∈ ({v} : Set V), ¬ (t ∈ X ∨ ∃ e ∈ setCl ω X, t ∈ e) := by
      intro t ht; rw [Set.mem_singleton_iff] at ht; subst ht; exact hvK
    have hcl : setCl ω {v} = setCl (ω \ barOf X (setCl ω X)) {v} := setCl_eq_sdiff_barOf rfl hT
    have h3 : cut {v} (ω \ cut X ω) = barOf {v} (setCl ω {v}) := by
      rw [cut_eq_barOf, cut_eq_barOf, ← hcl]
    rw [h3, cut_eq_barOf (insert v X), cut_eq_barOf X, hins, setCl_union, barOf_union]
    -- the cross terms are contained in the two main terms
    apply Set.Subset.antisymm
    · refine Set.union_subset (Set.Subset.refl _) (Set.union_subset ?_ ?_)
      · rintro e ⟨u, hu, h | ⟨e', he', hue'⟩⟩
        · exact Or.inl ⟨u, hu, Or.inl h⟩
        · exact Or.inr ⟨u, hu, Or.inr ⟨e', he', hue'⟩⟩
      · rintro e ⟨u, hu, h | ⟨e', he', hue'⟩⟩
        · exact Or.inr ⟨u, hu, Or.inl h⟩
        · exact Or.inl ⟨u, hu, Or.inr ⟨e', he', hue'⟩⟩
    · exact Set.subset_union_left

omit [Fintype V] in
/-- On `{s ↮ X}`: `s ↮ X ∪ {v}` iff `s ↮ v` in the configuration with the cut set of `X` deleted. [folklore] -/
theorem mem_avoidEv_insert_iff (s v : V) (X : Set V) (ω : Set (Sym2 V)) (hω : ω ∈ avoidEv s X) :
    ω ∈ avoidEv s (insert v X) ↔ ω \ cut X ω ∈ avoidEv s {v} := by
  have hsK : ∀ t ∈ ({s} : Set V), ¬ (t ∈ X ∨ ∃ e ∈ setCl ω X, t ∈ e) := by
    intro t ht; rw [Set.mem_singleton_iff] at ht; subst ht
    intro h
    obtain ⟨x, hx, hxs⟩ := (setReach_iff ω X t).2 h
    exact hω x hx hxs.symm
  have hcl : openEdgeCluster ω s = openEdgeCluster (ω \ cut X ω) s := by
    have := setCl_eq_sdiff_barOf (rfl : setCl ω X = setCl ω X) hsK
    rw [setCl_singleton, setCl_singleton, ← cut_eq_barOf] at this
    exact this
  have hreach : ∀ t, (openGraph ω).Reachable s t ↔ (openGraph (ω \ cut X ω)).Reachable s t := fun t => by
    rw [reachable_iff_exists_mem_openEdgeCluster, reachable_iff_exists_mem_openEdgeCluster, hcl]
  constructor
  · intro h t ht
    rw [Set.mem_singleton_iff] at ht; subst ht
    rw [← hreach]; exact h t (Set.mem_insert _ _)
  · intro h t ht
    rcases Set.mem_insert_iff.1 ht with rfl | ht
    · rw [hreach]; exact h t rfl
    · exact hω t ht

/-- **Deleting in two stages**: `E_w[φ(η ∖ (B ∪ B'))] = E_{w_B}[φ(η ∖ B')]` whenever `w_B = w` off `B` and `w_B = 0` on `B`.
[folklore] -/
theorem delE_union (w wB : Sym2 V → ℝ) (B B' : Set (Sym2 V)) (hB : ∀ e ∈ B, wB e = 0) (hoff : ∀ e ∉ B, wB e = w e)
    (φ : Set (Sym2 V) → ℝ) : delE w (B ∪ B') φ = delE wB B' φ := by
  classical
  have hfun : (fun i => if i ∈ B then (0 : ℝ) else w i) = wB := by
    funext i
    by_cases hi : i ∈ B
    · rw [if_pos hi, hB i hi]
    · rw [if_neg hi, hoff i hi]
  simp only [delE]
  have h1 : ∀ η : Set (Sym2 V), η \ (B ∪ B') = (η \ B) \ B' := fun η => by rw [Set.sdiff_sdiff]
  simp only [h1]
  rw [sum_weight_mul_comp_sdiff w B (fun ζ => φ (ζ \ B')), hfun]

/-- `E_w[φ(η ∖ B)] = E_{w_B}[φ]`. [folklore] -/
theorem delE_eq_delE_empty (w wB : Sym2 V → ℝ) (B : Set (Sym2 V)) (hB : ∀ e ∈ B, wB e = 0)
    (hoff : ∀ e ∉ B, wB e = w e) (φ : Set (Sym2 V) → ℝ) : delE w B φ = delE wB ∅ φ := by
  have := delE_union w wB B ∅ hB hoff φ
  rwa [Set.union_empty] at this

omit [Fintype V] in
/-- The cut set of the empty avoided set is empty. [folklore] -/
theorem cut_empty (ω : Set (Sym2 V)) : cut (∅ : Set V) ω = ∅ := by
  ext e; simp [cut]

/-- The functionals at `X ∪ {v}` read in the configuration with `cut_X` deleted: `c`. [folklore] -/
theorem taC_insert_eq (w wB : Sym2 V → ℝ) (s y v : V) (X : Set V) (g : Set (Sym2 V) → ℝ) (ω : Set (Sym2 V))
    (hB : ∀ e ∈ cut X ω, wB e = 0) (hoff : ∀ e ∉ cut X ω, wB e = w e) :
    taC w s y (insert v X) g ω = taC wB s y {v} g (ω \ cut X ω) := by
  simp only [taC, cut_insert_vertex X v ω, delE_union w wB _ _ hB hoff]

/-- The functionals at `X` read in the configuration with `cut_X` deleted (empty avoided set): `c`. [folklore] -/
theorem taC_eq_empty (w wB : Sym2 V → ℝ) (s y : V) (X : Set V) (g : Set (Sym2 V) → ℝ) (ω ζ : Set (Sym2 V))
    (hB : ∀ e ∈ cut X ω, wB e = 0) (hoff : ∀ e ∉ cut X ω, wB e = w e) :
    taC w s y X g ω = taC wB s y ∅ g ζ := by
  simp only [taC, cut_empty, delE_eq_delE_empty w wB _ hB hoff]

/-- Same for `taN`. [folklore] -/
theorem taN_eq_empty (w wB : Sym2 V → ℝ) (s y : V) (X : Set V) (ω ζ : Set (Sym2 V))
    (hB : ∀ e ∈ cut X ω, wB e = 0) (hoff : ∀ e ∉ cut X ω, wB e = w e) :
    taN w s y X ω = taN wB s y ∅ ζ := by
  simp only [taN, cut_empty, delE_eq_delE_empty w wB _ hB hoff]

/-- Same for `taNW`. [folklore] -/
theorem taNW_eq_empty (w wB : Sym2 V → ℝ) (s y z : V) (X : Set V) (ω ζ : Set (Sym2 V))
    (hB : ∀ e ∈ cut X ω, wB e = 0) (hoff : ∀ e ∉ cut X ω, wB e = w e) :
    taNW w s y z X ω = taNW wB s y z ∅ ζ := by
  simp only [taNW, cut_empty, delE_eq_delE_empty w wB _ hB hoff]

/-! ### Step (II): adding `v` to the avoided set, given Lemma `P_v` in every deleted graph -/

/-- `1_{s ↮ X}` read off `C_X`. [folklore] -/
theorem ind_avoidEv_eq_ite (s : V) (X : Set V) (ω : Set (Sym2 V)) :
    ind (avoidEv s X) ω = if (s ∈ X ∨ ∃ e ∈ setCl ω X, s ∈ e) then 0 else 1 := by
  by_cases h : (s ∈ X ∨ ∃ e ∈ setCl ω X, s ∈ e)
  · rw [if_pos h]
    obtain ⟨x, hx, hxs⟩ := (setReach_iff ω X s).2 h
    exact ind_of_not_mem fun hω => hω x hx hxs.symm
  · rw [if_neg h]
    refine ind_of_mem fun x hx hsx => h ((setReach_iff ω X s).1 ⟨x, hx, hsx.symm⟩)

/-- **Step (II)**: `B_{X ∪ {v}} ≤ B_X − A^{(v)}_X`, i.e.
`Σ_ω w 1{s↮X,v} c_{X∪v} ≤ Σ_ω w 1{s↮X} c_X · μ_{G−cut_X}(y ↮ v | s ↮ y)`, given Lemma P_v (hypothesis `hPv`,
"conditioning on the cluster of `v` explains at most the fraction `μ(y↮v | s↮y)` of `Cov(g, 1{s↔y})`") in every graph
with deleted pairs: apply `P_v` in `G − cut_X(ω)` for each `ω` and recombine with `set_sum_cond_sdiff`.
[cite: VandenbergHaggstromKahn2005, §2.1 Lemma 2.4 (p. 10) — corollary] -/
theorem taB_insert_le (w : Sym2 V → unitInterval) (hw : ∀ e, (w e : ℝ) < 1) (s y v : V) (X : Set V)
    (g : Set (Sym2 V) → ℝ)
    (hPv : ∀ (q : Sym2 V → unitInterval), (∀ e, (q e : ℝ) < 1) → ∀ v' : V,
      taB (fun e => (q e : ℝ)) s y {v'} g ≤
        (1 - delE (fun e => (q e : ℝ)) ∅ (ind ((openConn s y : Set (BondConfig V))ᶜ ∩ openConn y v')) /
              delE (fun e => (q e : ℝ)) ∅ (ind (openConn s y : Set (BondConfig V))ᶜ)) *
          (delE (fun e => (q e : ℝ)) ∅ (fun η => g (openEdgeCluster η s) * ind (openConn s y) η) -
            delE (fun e => (q e : ℝ)) ∅ (fun η => g (openEdgeCluster η s)) *
              delE (fun e => (q e : ℝ)) ∅ (ind (openConn s y)))) :
    taB (fun e => (w e : ℝ)) s y (insert v X) g ≤
      taB (fun e => (w e : ℝ)) s y X g - taA (fun e => (w e : ℝ)) s y v X g := by
  classical
  set ŵ : Sym2 V → ℝ := fun e => (w e : ℝ) with hŵ
  have hw0 : ∀ e, 0 ≤ ŵ e := fun e => (w e).2.1
  have hw1 : ∀ e, ŵ e ≤ 1 := fun e => (w e).2.2
  have hm : ∑ ω, weight ŵ ω = 1 := by
    have h1 := integral_prodBernoulli_eq_sum w fun _ => (1 : ℝ)
    simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at h1
    exact h1.symm
  -- the zeroed weights `w_B`, `B = X̄(W)`
  set qB : Set (Sym2 V) → Sym2 V → unitInterval := fun W e => if e ∈ barOf X W then 0 else w e with hqB
  set wB : Set (Sym2 V) → Sym2 V → ℝ := fun W e => (qB W e : ℝ) with hwB
  have hB : ∀ (ω : Set (Sym2 V)), ∀ e ∈ cut X ω, wB (setCl ω X) e = 0 := by
    intro ω e he
    rw [cut_eq_barOf] at he
    simp only [hwB, hqB, if_pos he]; rfl
  have hoff : ∀ (ω : Set (Sym2 V)), ∀ e ∉ cut X ω, wB (setCl ω X) e = ŵ e := by
    intro ω e he
    rw [cut_eq_barOf] at he
    simp only [hwB, hqB, if_neg he, hŵ]
  have hqlt : ∀ (W : Set (Sym2 V)) (e : Sym2 V), (qB W e : ℝ) < 1 := by
    intro W e
    simp only [hqB]
    split_ifs
    · norm_num
    · exact hw e
  -- the kernel expressing `1{s ↮ X, v} c_{X∪v}` through `(C_X, configuration off X̄(C_X))`
  set KK : Set (Sym2 V) → Set (Sym2 V) → ℝ := fun W ζ =>
    (if (s ∈ X ∨ ∃ e ∈ W, s ∈ e) then 0 else 1) *
      (ind (avoidEv s {v}) ζ * taC (wB W) s y {v} g ζ) with hKK
  have lhs : taB ŵ s y (insert v X) g = ∑ ω, weight ŵ ω * KK (setCl ω X) (ω \ barOf X (setCl ω X)) := by
    refine Finset.sum_congr rfl fun ω _ => ?_
    simp only [hKK]
    rw [← ind_avoidEv_eq_ite, ← cut_eq_barOf]
    by_cases hω : ω ∈ avoidEv s X
    · have h1 : ind (avoidEv s (insert v X)) ω = ind (avoidEv s X) ω * ind (avoidEv s {v}) (ω \ cut X ω) := by
        rw [ind_of_mem hω, one_mul]
        by_cases h' : ω ∈ avoidEv s (insert v X)
        · rw [ind_of_mem h', ind_of_mem ((mem_avoidEv_insert_iff s v X ω hω).1 h')]
        · rw [ind_of_not_mem h', ind_of_not_mem fun hh => h' ((mem_avoidEv_insert_iff s v X ω hω).2 hh)]
      rw [h1, taC_insert_eq ŵ (wB (setCl ω X)) s y v X g ω (hB ω) (hoff ω)]
      ring
    · have h' : ω ∉ avoidEv s (insert v X) := fun hh => hω fun x hx => hh x (Set.mem_insert_of_mem _ hx)
      rw [ind_of_not_mem h', ind_of_not_mem hω]; ring
  rw [lhs, set_sum_cond_sdiff ŵ hm X KK]
  -- the right-hand side, configuration by configuration
  have rhs : taB ŵ s y X g - taA ŵ s y v X g =
      ∑ ω, weight ŵ ω * (ind (avoidEv s X) ω *
        ((1 - taNW ŵ s y v X ω / taN ŵ s y X ω) * taC ŵ s y X g ω)) := by
    simp only [taB, taA, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ω _ => ?_
    ring
  rw [rhs]
  refine Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left ?_ (weight_nonneg hw0 hw1 ω)
  simp only [hKK]
  rw [← ind_avoidEv_eq_ite]
  by_cases hω : ω ∈ avoidEv s X
  swap
  · rw [ind_of_not_mem hω]; simp
  rw [ind_of_mem hω, one_mul]
  -- in `G − cut_X(ω)`: the inner sum is `taB (w_B) s y {v} g`, the right side is `P_v`'s right side
  have inner : ∑ η, weight ŵ η * (1 * (ind (avoidEv s {v}) (η \ barOf X (setCl ω X)) *
      taC (wB (setCl ω X)) s y {v} g (η \ barOf X (setCl ω X)))) = taB (wB (setCl ω X)) s y {v} g := by
    simp only [one_mul, taB]
    rw [← cut_eq_barOf]
    rw [sum_weight_mul_comp_sdiff ŵ (cut X ω)
      (fun ζ => ind (avoidEv s {v}) ζ * taC (wB (setCl ω X)) s y {v} g ζ)]
    refine Finset.sum_congr rfl fun η _ => ?_
    congr 2
    funext e
    by_cases he : e ∈ cut X ω
    · rw [if_pos he, hB ω e he]
    · rw [if_neg he, hoff ω e he]
  rw [inner]
  have e1 := taC_eq_empty ŵ (wB (setCl ω X)) s y X g ω ∅ (hB ω) (hoff ω)
  have e2 := taN_eq_empty ŵ (wB (setCl ω X)) s y X ω ∅ (hB ω) (hoff ω)
  have e3 := taNW_eq_empty ŵ (wB (setCl ω X)) s y v X ω ∅ (hB ω) (hoff ω)
  rw [e1, e2, e3]
  have key := hPv (qB (setCl ω X)) (hqlt (setCl ω X)) v
  simp only [taC, taN, taNW, cut_empty] at key ⊢
  exact key

end TA

end HullPort

end Percolation.Continuity
