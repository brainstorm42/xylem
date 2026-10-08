import Percolation.Literature.HalfSpaceHighDimBounded
import Percolation.Util.Linter

/-!
# Many level-`h` vertices are joined to the seed `b(0)` in `S_h*`, in `ℤ^d`: step (7.41) of Lemma (7.36)

Third step of the bottom-up proof, in every dimension
`d`, of the finite-size criterion of the Barsky–Grimmett–Newman theorem (Grimmett, *Percolation*,
2nd ed. (1999), §7.3, Lemma (7.36) = Barsky–Grimmett–Newman 1991, Prop. 2.1), after its `d = 3`
model `HalfSpaceSlab.lean`. With `b(0) = b_d(m)` the central square and `S_h = ℤ^{d-1} × [0, h]`
the slab, Grimmett (pp. 165–166) sets

> `U(h) = |{x : x_3 = h, b(0) ↔ x in S_h*}|`. As in (7.15)–(7.16) with `B(m)` replaced by `b(0)`,
> `P_{p_c}(U(h) < 2N₂) ≤ a_h + ε²` by (7.37), for some `a_h` satisfying `a_h → 0` as `h → ∞`.
> (We have used (7.38) surreptitiously here.) We pick `H₀` large enough that `a_h ≤ ε²` for
> `h ≥ H₀`, and deduce that (7.41) `P_{p_c}(U(h) ≥ 2N₂) ≥ 1 - 2ε²` for `h ≥ H₀`,

where (7.38) is "no percolation in slabs at `p_c`". In the coordinates of `HalfSpace.lean`
(vertical axis `0`) we prove the same for bond percolation `P_p` on `ℤ^d`, at EVERY `0 < p < 1`,
with (7.38) replaced by the slab-free statement of `HalfSpaceHighDimBounded.lean` (an infinite
`ℍ*`-cluster has unbounded height almost surely; this is how Barsky–Grimmett–Newman 1991,
Lemma 2.3, dispense with slabs at a general density):

* `BGNd.exits x` — the upward edge and the `2(d-1)` horizontal edges at `x` (the edges closed in
  the finite-energy step), `BGNd.slabStar d h` — the step graph of `S_h*`, `BGNd.slabLevelSet` —
  Grimmett's set behind `U(h)`, `BGNd.starCluster` — the `ℍ*`-cluster of `b(0)`,
  `BGNd.maxHeightEvent` — "the `ℍ*`-cluster of `b(0)` has maximal height exactly `h`" (pairwise
  disjoint in `h`, so of probability `→ 0`);
* the geometric heart `BGNd.openClusterIn_halfSpaceStar_subset_slabStar`: if every level-`h`
  vertex of the `S_h*`-cluster of `y ∈ b(0)` has its exit edges closed, the `ℍ*`-cluster of `y`
  is its `S_h*`-cluster (`h ≥ 2`);
* `BGNd.prob_iUnion_boundedCluster_eq_zero` — the replacement of (7.38): if `U(h) = ∅`, an
  infinite `ℍ*`-cluster of `b(0)` would be an infinite `ℍ*`-cluster of height `≤ h`, a null event;
* `BGNd.finiteEnergy_slabLevelSet` — `(1-p)^{2d(n-1)} P_p(1 ≤ U(h) < n) ≤ P_p(maxHeightEvent)`;
* `BGNd.tendsto_prob_centralSquarePercolates_inter_slabLevelLT` (`a_h → 0`) and
  `BGNd.exists_prob_slabLevelLT_lt` — **(7.41)**: if `P_p(b(0) ↔ ∞ in ℍ*) > 1 - δ` then for all
  large `h`, `P_p(U(h) < n) < 2δ`.

## References

* G. Grimmett, *Percolation*, 2nd ed., Grundlehren 321, Springer 1999, §7.3, proof of
  Lemma (7.36), pp. 165–166, (7.38)–(7.41); §7.2, (7.15)–(7.16), p. 151.
* D. J. Barsky, G. R. Grimmett, C. M. Newman, *Percolation in half-spaces: equality of critical
  densities and continuity of the percolation probability*, Probab. Theory Related Fields 90
  (1991) 111–148, §2, Lemmas 2.2–2.3.
-/

noncomputable section

namespace Percolation.Literature

open _root_.MeasureTheory _root_.ProbabilityTheory _root_.Filter LatticeModels unitInterval
open scoped _root_.ENNReal _root_.Topology

namespace BGNd

variable {d : ℕ}

/-! ## Unit vectors and the exit edges of a vertex -/

/-- The unit vector `e_i` of `ℤ^d`. [folklore] -/
def unitVec (i : Fin d) : Site d := Pi.single i 1

/-- Coordinates of `e_i`. [folklore] -/
@[simp] theorem unitVec_apply_same (i : Fin d) : unitVec i i = 1 := by simp [unitVec]

/-- Coordinates of `e_i`. [folklore] -/
theorem unitVec_apply_of_ne {i j : Fin d} (h : j ≠ i) : unitVec i j = 0 := by simp [unitVec, h]

/-- The neighbours of a vertex of `ℤ^d` are `u ± e_i`. [folklore] -/
theorem zdGraph_adj_cases' {u v : Site d} (h : (zdGraph d).Adj u v) :
    ∃ i, v = u + unitVec i ∨ v = u - unitVec i := by
  obtain ⟨i, h | h⟩ := (zdGraph_adj_iff u v).1 h
  · exact ⟨i, Or.inl h⟩
  · exact ⟨i, Or.inr (eq_sub_of_add_eq h.symm)⟩

/-- The **exit edges** at `x`: the edges `⟨x, x + e_i⟩` (`i` arbitrary) and `⟨x, x - e_i⟩`
(`i ≠ 0`), i.e. all lattice edges at `x` except the downward one (the edges closed in the
finite-energy step of (7.16)/(7.41)). [cite: GrimmettPercolation1999, §7.2 (7.16) p. 151] -/
def exits [NeZero d] (x : Site d) : Finset (Sym2 (Site d)) :=
  (Finset.univ.image fun i : Fin d => s(x, x + unitVec i)) ∪
    ((Finset.univ.filter fun i : Fin d => i ≠ 0).image fun i => s(x, x - unitVec i))

/-- At most `2d` exit edges per vertex. [folklore] -/
theorem card_exits_le [NeZero d] (x : Site d) : (exits x).card ≤ 2 * d := by
  unfold exits
  calc _ ≤ (Finset.univ.image fun i : Fin d => s(x, x + unitVec i)).card +
        ((Finset.univ.filter fun i : Fin d => i ≠ 0).image fun i => s(x, x - unitVec i)).card :=
        Finset.card_union_le _ _
    _ ≤ d + d := by
        gcongr
        · exact Finset.card_image_le.trans (by simp)
        · exact Finset.card_image_le.trans ((Finset.card_filter_le _ _).trans (by simp))
    _ = 2 * d := by ring

/-- The upward-type exits. [folklore] -/
theorem add_mem_exits [NeZero d] (x : Site d) (i : Fin d) : s(x, x + unitVec i) ∈ exits x :=
  Finset.mem_union_left _ (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)

/-- The horizontal backward exits. [folklore] -/
theorem sub_mem_exits [NeZero d] (x : Site d) {i : Fin d} (hi : i ≠ 0) : s(x, x - unitVec i) ∈ exits x :=
  Finset.mem_union_right _ (Finset.mem_image.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩, rfl⟩)

/-- Membership in `exits`. [folklore] -/
theorem mem_exits_iff [NeZero d] {x : Site d} {e : Sym2 (Site d)} :
    e ∈ exits x ↔ (∃ i, e = s(x, x + unitVec i)) ∨ ∃ i, i ≠ 0 ∧ e = s(x, x - unitVec i) := by
  simp only [exits, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_filter]
  constructor
  · rintro (⟨i, hi⟩ | ⟨i, hi0, hi⟩)
    exacts [Or.inl ⟨i, hi.symm⟩, Or.inr ⟨i, hi0, hi.symm⟩]
  · rintro (⟨i, hi⟩ | ⟨i, hi0, hi⟩)
    exacts [Or.inl ⟨i, hi.symm⟩, Or.inr ⟨i, hi0, hi.symm⟩]

/-- Heights of the endpoints of exit edges: the other endpoint has height `x 0` or `x 0 + 1`.
[folklore] -/
theorem apply_zero_of_mem_exits [NeZero d] {x : Site d} {e : Sym2 (Site d)} (he : e ∈ exits x) :
    ∃ v, e = s(x, v) ∧ (v 0 = x 0 ∨ v 0 = x 0 + 1) := by
  rcases mem_exits_iff.1 he with ⟨i, rfl⟩ | ⟨i, hi0, rfl⟩
  · refine ⟨_, rfl, ?_⟩
    by_cases hi : i = 0
    · subst hi; right; simp [unitVec]
    · left; simp [unitVec, Pi.single_eq_of_ne (Ne.symm hi)]
  · refine ⟨_, rfl, Or.inl ?_⟩
    simp [unitVec, Pi.single_eq_of_ne (Ne.symm hi0)]

/-! ## The slab `S_h*`, the level set `U(h)` and the `ℍ*`-cluster of `b(0)` -/

/-- The step graph of **`S_h*`**: nearest-neighbour steps inside the slab `S_h` joining no two
vertices of its boundary `∂S_h = {x 0 = 0} ∪ {x 0 = h}` (Grimmett 1999, p. 165, `U(h)`).
[cite: GrimmettPercolation1999, §7.3 p. 165 (S_h*)] -/
def slabStar (d : ℕ) [NeZero d] (h : ℕ) : SimpleGraph (Site d) :=
  starGraph (zdGraph d) (slab d h) (plane 0 ∪ plane h)

/-- `S_h*`-paths are `ℍ*`-paths. [folklore] -/
theorem slabStar_le_halfSpaceStar [NeZero d] (h : ℕ) : slabStar d h ≤ halfSpaceStar d :=
  starGraph_mono (zdGraph d) (fun _ hx => mem_halfSpace_iff.2 (mem_slab_iff.1 hx).1)
    Set.subset_union_left

/-- **Grimmett's `U(h)`, as a set**: the vertices `x` at height `h` with `b(0) ↔ x in S_h*`
(`U(h)` is its cardinality). [cite: GrimmettPercolation1999, §7.3 p. 165 (U(h))] -/
def slabLevelSet (d : ℕ) [NeZero d] (m h : ℕ) (ω : BondConfig (Site d)) : Set (Site d) :=
  {x | x 0 = h ∧ ∃ y ∈ centralSquare d m, x ∈ openClusterIn (slabStar d h) ω y}

/-- The `ℍ*`-cluster of the central square `b(0)`. [cite: GrimmettPercolation1999, §7.3 p. 165] -/
def starCluster (d : ℕ) [NeZero d] (m : ℕ) (ω : BondConfig (Site d)) : Set (Site d) :=
  ⋃ y ∈ centralSquare d m, openClusterIn (halfSpaceStar d) ω y

/-- Membership in the `ℍ*`-cluster of `b(0)`. [folklore] -/
theorem mem_starCluster_iff [NeZero d] {m : ℕ} {ω : BondConfig (Site d)} {x : Site d} :
    x ∈ starCluster d m ω ↔ ∃ y ∈ centralSquare d m, x ∈ openClusterIn (halfSpaceStar d) ω y := by
  simp only [starCluster, Set.mem_iUnion, exists_prop]

/-- The level set lies in the `ℍ*`-cluster of `b(0)`. [folklore] -/
theorem slabLevelSet_subset_starCluster [NeZero d] (m h : ℕ) (ω : BondConfig (Site d)) :
    slabLevelSet d m h ω ⊆ starCluster d m ω := by
  rintro x ⟨-, y, hy, hx⟩
  exact mem_starCluster_iff.2 ⟨y, hy, openClusterIn_mono_graph (slabStar_le_halfSpaceStar h) ω y hx⟩

/-- The level set only depends on the edges of `S_h*`. [folklore] -/
theorem slabLevelSet_inter_edgeSet [NeZero d] (m h : ℕ) (ω : BondConfig (Site d)) :
    slabLevelSet d m h (ω ∩ (slabStar d h).edgeSet) = slabLevelSet d m h ω := by
  simp only [slabLevelSet, openClusterIn_inter_edgeSet]

/-- **The event "the `ℍ*`-cluster of `b(0)` has maximal height exactly `h`"** (the analogue of
Grimmett's `{U(n+1) = ∅, U(n) ≠ ∅}` in (7.16)). [cite: GrimmettPercolation1999, §7.2 (7.16) p. 151] -/
def maxHeightEvent (d : ℕ) [NeZero d] (m h : ℕ) : Set (BondConfig (Site d)) :=
  {ω | starCluster d m ω ⊆ {x | x 0 ≤ h} ∧ (starCluster d m ω ∩ plane h).Nonempty}

/-- The maximal-height events are pairwise disjoint. [folklore] -/
theorem pairwise_disjoint_maxHeightEvent [NeZero d] (m : ℕ) :
    Pairwise (Function.onFun Disjoint (maxHeightEvent d m)) := by
  intro h h' hne
  rw [Function.onFun, Set.disjoint_left]
  rintro ω ⟨hle, x, hx, hxh⟩ ⟨hle', x', hx', hxh'⟩
  rw [mem_plane_iff] at hxh hxh'
  have h1 : (h : ℤ) ≤ h' := hxh ▸ hle' hx
  have h2 : (h' : ℤ) ≤ h := hxh' ▸ hle hx'
  exact hne (by exact_mod_cast le_antisymm h1 h2)

/-! ### Measurability -/

/-- `{x ∈ ℍ*-cluster of b(0)}` is measurable. [folklore] -/
theorem measurableSet_mem_starCluster [NeZero d] (m : ℕ) (x : Site d) :
    MeasurableSet {ω : BondConfig (Site d) | x ∈ starCluster d m ω} := by
  have : {ω : BondConfig (Site d) | x ∈ starCluster d m ω} =
      ⋃ y ∈ centralSquare d m, openConnVia (halfSpaceStar d) y x := by
    ext ω
    simp only [Set.mem_setOf_eq, mem_starCluster_iff, Set.mem_iUnion, exists_prop, openConnVia]
  rw [this]
  exact MeasurableSet.biUnion (Set.to_countable _) fun y _ => measurableSet_openConnVia _ y x

/-- `{x ∈ U(h)-set}` is measurable. [folklore] -/
theorem measurableSet_mem_slabLevelSet [NeZero d] (m h : ℕ) (x : Site d) :
    MeasurableSet {ω : BondConfig (Site d) | x ∈ slabLevelSet d m h ω} := by
  have : {ω : BondConfig (Site d) | x ∈ slabLevelSet d m h ω} =
      {_ω | x 0 = h} ∩ ⋃ y ∈ centralSquare d m, openConnVia (slabStar d h) y x := by
    ext ω
    simp only [slabLevelSet, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iUnion, exists_prop,
      openConnVia]
  rw [this]
  exact (MeasurableSet.const _).inter
    (MeasurableSet.biUnion (Set.to_countable _) fun y _ => measurableSet_openConnVia _ y x)

/-- `{U(h)-set = W}` is measurable. [folklore] -/
theorem measurableSet_slabLevelSet_eq [NeZero d] (m h : ℕ) (W : Set (Site d)) :
    MeasurableSet {ω : BondConfig (Site d) | slabLevelSet d m h ω = W} := by
  have : {ω : BondConfig (Site d) | slabLevelSet d m h ω = W} =
      (⋂ x ∈ W, {ω | x ∈ slabLevelSet d m h ω}) ∩ ⋂ x ∈ Wᶜ, {ω | x ∈ slabLevelSet d m h ω}ᶜ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff]
    constructor
    · rintro rfl
      exact ⟨fun x hx => hx, fun x hx hx' => hx hx'⟩
    · rintro ⟨h1, h2⟩
      ext x
      exact ⟨fun hx => by_contra fun hxW => h2 x hxW hx, fun hx => h1 x hx⟩
  rw [this]
  exact (MeasurableSet.biInter (Set.to_countable _) fun x _ => measurableSet_mem_slabLevelSet m h x).inter
    (MeasurableSet.biInter (Set.to_countable _) fun x _ => (measurableSet_mem_slabLevelSet m h x).compl)

/-- The maximal-height event is measurable. [folklore] -/
theorem measurableSet_maxHeightEvent [NeZero d] (m h : ℕ) : MeasurableSet (maxHeightEvent d m h) := by
  have h1 : {ω : BondConfig (Site d) | starCluster d m ω ⊆ {x | x 0 ≤ h}} =
      ⋂ x ∈ {x : Site d | ¬(x 0 ≤ h)}, {ω | x ∈ starCluster d m ω}ᶜ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_compl_iff]
    exact ⟨fun hs x hx hxs => hx (hs hxs), fun hs x hxs => by_contra fun hx => hs x hx hxs⟩
  have h2 : {ω : BondConfig (Site d) | (starCluster d m ω ∩ plane h).Nonempty} =
      ⋃ x ∈ plane (d := d) (h : ℤ), {ω | x ∈ starCluster d m ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop, Set.Nonempty, Set.mem_inter_iff]
    exact ⟨fun ⟨x, hx, hxp⟩ => ⟨x, hxp, hx⟩, fun ⟨x, hxp, hx⟩ => ⟨x, hx, hxp⟩⟩
  have : maxHeightEvent d m h = {ω | starCluster d m ω ⊆ {x | x 0 ≤ h}} ∩
      {ω | (starCluster d m ω ∩ plane h).Nonempty} := rfl
  rw [this, h1, h2]
  exact (MeasurableSet.biInter (Set.to_countable _) fun x _ => (measurableSet_mem_starCluster m x).compl).inter
    (MeasurableSet.biUnion (Set.to_countable _) fun x _ => measurableSet_mem_starCluster m x)

/-- **`P_p(maxHeightEvent m h) → 0` as `h → ∞`** (disjoint events; the "`→ 0 as n → ∞`" of
(7.16)). [cite: GrimmettPercolation1999, §7.2 (7.16) p. 151] -/
theorem tendsto_prob_maxHeightEvent [NeZero d] (m : ℕ) (p : unitInterval) :
    Tendsto (fun h => (bondPercolation (zdGraph d) p).real (maxHeightEvent d m h)) atTop (𝓝 0) :=
  tendsto_measureReal_of_pairwise_disjoint _ (measurableSet_maxHeightEvent m)
    (pairwise_disjoint_maxHeightEvent m)

/-! ## The geometric heart: closing the exits of `U(h)` confines the `ℍ*`-cluster to the slab -/

/-- **Closing the exits of the level set confines `ℍ*`-paths to the slab.** Let `h ≥ 2`,
`y ∈ b(0)`, and suppose that at every level-`h` vertex of the `S_h*`-cluster of `y` the upward
edge and the `2(d-1)` horizontal edges are closed. Then the `ℍ*`-cluster of `y` is its
`S_h*`-cluster. (This is "`U(n+1) = ∅` if every edge exiting `∂B(n)` from `U(n)` is closed",
Grimmett 1999, p. 151, in the slab geometry of p. 165: an `ℍ*`-path from `b(0)` leaving `S_h`
must do so through an upward or horizontal edge at a level-`h` vertex previously reached inside
`S_h*`.) [cite: GrimmettPercolation1999, §7.2 (7.16) p. 151; §7.3 p. 165] -/
theorem openClusterIn_halfSpaceStar_subset_slabStar [NeZero d] {m h : ℕ} (hh : 2 ≤ h)
    {ω : BondConfig (Site d)} {y : Site d} (hy : y ∈ centralSquare d m)
    (hclosed : ∀ x ∈ openClusterIn (slabStar d h) ω y, x 0 = h → ∀ e ∈ exits x, e ∉ ω) :
    openClusterIn (halfSpaceStar d) ω y ⊆ openClusterIn (slabStar d h) ω y := by
  have hy0 : y 0 = 0 := (mem_centralSquare_iff.1 hy).1
  have hyslab : y ∈ slab d h := mem_slab_iff.2 ⟨by omega, by omega⟩
  refine BGN.openClusterIn_subset_of_closed (self_mem_openClusterIn _ ω y) fun u hu v huv => ?_
  have huslab : u ∈ slab d h := openClusterIn_starGraph_subset hyslab ω hu
  rw [mem_slab_iff] at huslab
  rw [SimpleGraph.inf_adj, openGraph_adj] at huv
  obtain ⟨⟨hωuv, -⟩, hzd, -, hvH, hnot0⟩ := huv
  rw [mem_halfSpace_iff] at hvH
  simp only [mem_plane_iff] at hnot0
  have hv0 := zdGraph_adj_apply_zero hzd
  -- the step `u → v` is a step of `S_h*`, unless it is a closed exit edge
  have key : (slabStar d h).Adj u v := by
    rcases eq_or_lt_of_le huslab.2 with hutop | hult
    · -- `u` at level `h`: only the downward edge is available
      have hcl := hclosed u hu hutop
      obtain ⟨i, rfl | rfl⟩ := zdGraph_adj_cases' hzd
      · exact absurd hωuv (hcl _ (add_mem_exits u i))
      · by_cases hi : i = 0
        · subst hi
          have h0 : (u - unitVec (0 : Fin d)) 0 = u 0 - 1 := by simp [unitVec]
          refine ⟨hzd, mem_slab_iff.2 huslab, mem_slab_iff.2 ⟨?_, ?_⟩, ?_⟩
          · rw [h0]; omega
          · rw [h0]; omega
          · simp only [Set.mem_union, mem_plane_iff, h0]
            omega
        · exact absurd hωuv (hcl _ (sub_mem_exits u hi))
    · -- `u` below level `h`: `v` stays in the slab and the edge is not within `∂S_h`
      refine ⟨hzd, mem_slab_iff.2 huslab, mem_slab_iff.2 ⟨hvH, by omega⟩, ?_⟩
      simp only [Set.mem_union, mem_plane_iff]
      omega
  exact mem_openClusterIn_of_adj hu key hωuv

/-- **If `U(h) = 0`, an infinite `ℍ*`-cluster of `b(0)` is an infinite `ℍ*`-cluster of height
`≤ h`** (this replaces "we have used (7.38) surreptitiously here", Grimmett 1999, p. 166, by the
case analysis of BGN 1991, Lemma 2.3): for `h ≥ 2`,
`{b(0) ↔ ∞ in ℍ*} ∩ {U(h) = ∅} ⊆ ⋃_{y ∈ b(0)} {y ↔ ∞ in ℍ*, all heights ≤ h}`.
[cite: GrimmettPercolation1999, §7.3 pp. 165–166] [cite: BarskyGrimmettNewman1991, Lemma 2.3 p. 123] -/
theorem centralSquarePercolates_inter_slabLevelSet_empty_subset [NeZero d] {m h : ℕ} (hh : 2 ≤ h) :
    centralSquarePercolates d m ∩ {ω | slabLevelSet d m h ω = ∅} ⊆
      ⋃ y ∈ centralSquare d m, (percolatesVia (halfSpaceStar d) y ∩
        {ω | ∀ z ∈ openClusterIn (halfSpaceStar d) ω y, z 0 ≤ h}) := by
  rintro ω ⟨hperc, hempty⟩
  obtain ⟨y, hy, hωy⟩ := mem_centralSquarePercolates_iff.1 hperc
  simp only [Set.mem_iUnion, exists_prop]
  refine ⟨y, hy, hωy, fun z hz => ?_⟩
  have hsub : openClusterIn (halfSpaceStar d) ω y ⊆ openClusterIn (slabStar d h) ω y := by
    refine openClusterIn_halfSpaceStar_subset_slabStar hh hy fun x hx hx0 => ?_
    have : x ∈ slabLevelSet d m h ω := ⟨hx0, y, hy, hx⟩
    rw [hempty] at this
    exact absurd this (Set.notMem_empty x)
  have hyslab : y ∈ slab d h :=
    mem_slab_iff.2 ⟨by rw [(mem_centralSquare_iff.1 hy).1], by rw [(mem_centralSquare_iff.1 hy).1]; positivity⟩
  exact (mem_slab_iff.1 (openClusterIn_starGraph_subset hyslab ω (hsub hz))).2

/-- **If `1 ≤ U(h)` and all exit edges of the level set are closed, the `ℍ*`-cluster of `b(0)` has
maximal height exactly `h`.** [cite: GrimmettPercolation1999, §7.2 (7.16) p. 151; §7.3 p. 165] -/
theorem mem_maxHeightEvent_of_exits_closed [NeZero d] {m h : ℕ} (hh : 2 ≤ h) {ω : BondConfig (Site d)}
    (hne : (slabLevelSet d m h ω).Nonempty)
    (hclosed : ∀ x ∈ slabLevelSet d m h ω, ∀ e ∈ exits x, e ∉ ω) : ω ∈ maxHeightEvent d m h := by
  constructor
  · intro z hz
    obtain ⟨y, hy, hz⟩ := mem_starCluster_iff.1 hz
    have hsub := openClusterIn_halfSpaceStar_subset_slabStar hh hy
      (fun x hx hx0 => hclosed x ⟨hx0, y, hy, hx⟩)
    have hyslab : y ∈ slab d h :=
      mem_slab_iff.2 ⟨by rw [(mem_centralSquare_iff.1 hy).1], by rw [(mem_centralSquare_iff.1 hy).1]; positivity⟩
    exact (mem_slab_iff.1 (openClusterIn_starGraph_subset hyslab ω (hsub hz))).2
  · obtain ⟨x, hx⟩ := hne
    exact ⟨x, slabLevelSet_subset_starCluster m h ω hx, hx.1⟩

/-! ## The replacement of (7.38): bounded infinite `ℍ*`-clusters are null -/

/-- `P_p(⋃_{y ∈ b(0)} {y ↔ ∞ in ℍ*, all heights ≤ h}) = 0` for `p > 0`
(`HalfSpaceHighDimBounded.lean`). [cite: BarskyGrimmettNewman1991, Lemma 2.3 p. 123] -/
theorem prob_iUnion_boundedCluster_eq_zero [NeZero d] (p : unitInterval) (hp : 0 < (p : ℝ)) (m h : ℕ) :
    bondPercolation (zdGraph d) p (⋃ y ∈ centralSquare d m, (percolatesVia (halfSpaceStar d) y ∩
        {ω | ∀ z ∈ openClusterIn (halfSpaceStar d) ω y, z 0 ≤ h})) = 0 :=
  (measure_biUnion_null_iff (Set.to_countable _)).2 fun y _ =>
    measure_percolatesVia_inter_heightLE_eq_zero p hp y h

/-! ## The finite-energy step -/

/-- The event `{1 ≤ U(h) < n}` (with `U(h)` finite). [cite: GrimmettPercolation1999, §7.3 p. 165] -/
def slabLevelSmall (d : ℕ) [NeZero d] (m h n : ℕ) : Set (BondConfig (Site d)) :=
  {ω | ∃ hf : (slabLevelSet d m h ω).Finite, 1 ≤ hf.toFinset.card ∧ hf.toFinset.card < n}

open Classical in
/-- The level set as a `Finset` (empty if infinite): the statistic `Ψ` of the finite-energy
lemma. [folklore] -/
def slabLevelFinset (d : ℕ) [NeZero d] (m h : ℕ) (ω : BondConfig (Site d)) : Finset (Site d) :=
  if hf : (slabLevelSet d m h ω).Finite then hf.toFinset else ∅

/-- The exit edges of a finite set of vertices. [folklore] -/
def exitsOf [NeZero d] (W : Finset (Site d)) : Finset (Sym2 (Site d)) := W.biUnion exits

/-- At most `2d |W|` exit edges. [folklore] -/
theorem card_exitsOf_le [NeZero d] (W : Finset (Site d)) : (exitsOf W).card ≤ 2 * d * W.card := by
  calc (exitsOf W).card ≤ ∑ x ∈ W, (exits x).card := Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ W, 2 * d := Finset.sum_le_sum fun x _ => card_exits_le x
    _ = 2 * d * W.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- On `{1 ≤ U(h) < n}` the statistic `Ψ` is the level set. [folklore] -/
theorem coe_slabLevelFinset [NeZero d] {m h n : ℕ} {ω : BondConfig (Site d)}
    (hω : ω ∈ slabLevelSmall d m h n) :
    (↑(slabLevelFinset d m h ω) : Set (Site d)) = slabLevelSet d m h ω := by
  obtain ⟨hf, -, -⟩ := hω
  simp [slabLevelFinset, hf]

/-- The pieces `{1 ≤ U(h) < n} ∩ {Ψ = W}` are level-set events. [folklore] -/
theorem slabLevelSmall_inter_preimage [NeZero d] (m h n : ℕ) (W : Finset (Site d)) :
    slabLevelSmall d m h n ∩ slabLevelFinset d m h ⁻¹' {W} =
      {ω | slabLevelSet d m h ω = ↑W} ∩ {_ω | 1 ≤ W.card ∧ W.card < n} := by
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨hf, h1, h2⟩, hW⟩
    have hW' : hf.toFinset = W := by simpa [slabLevelFinset, hf] using hW
    refine ⟨?_, ?_, ?_⟩
    · rw [← hW', Set.Finite.coe_toFinset]
    · rwa [← hW']
    · rwa [← hW']
  · rintro ⟨hW, h1, h2⟩
    have hf : (slabLevelSet d m h ω).Finite := by rw [hW]; exact W.finite_toSet
    have hW' : hf.toFinset = W := by
      apply Finset.coe_injective
      rw [Set.Finite.coe_toFinset, hW]
    refine ⟨⟨hf, ?_, ?_⟩, ?_⟩
    · rwa [hW']
    · rwa [hW']
    · simp [slabLevelFinset, hf, hW']

/-- The pieces are determined by the edges of `S_h*`. [folklore] -/
theorem determinedBy_slabLevelSmall_inter [NeZero d] (m h n : ℕ) (W : Finset (Site d)) :
    DeterminedBy (slabLevelSmall d m h n ∩ slabLevelFinset d m h ⁻¹' {W}) (slabStar d h).edgeSet := by
  rw [slabLevelSmall_inter_preimage]
  have : {ω : BondConfig (Site d) | slabLevelSet d m h ω = ↑W} ∩ {_ω | 1 ≤ W.card ∧ W.card < n} =
      (fun ω : BondConfig (Site d) => ω ∩ (slabStar d h).edgeSet) ⁻¹'
        ({ω | slabLevelSet d m h ω = ↑W} ∩ {_ω | 1 ≤ W.card ∧ W.card < n}) := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage, slabLevelSet_inter_edgeSet]
  rw [this]
  exact determinedBy_preimage_inter _ _

/-- The pieces are measurable. [folklore] -/
theorem measurableSet_slabLevelSmall_inter [NeZero d] (m h n : ℕ) (W : Finset (Site d)) :
    MeasurableSet (slabLevelSmall d m h n ∩ slabLevelFinset d m h ⁻¹' {W}) := by
  rw [slabLevelSmall_inter_preimage]
  exact (measurableSet_slabLevelSet_eq m h _).inter (MeasurableSet.const _)

/-- The exit edges of level-`h` vertices are not edges of `S_h*` (`h ≥ 1`). [folklore] -/
theorem exits_disjoint_edgeSet_slabStar [NeZero d] {h : ℕ} {x : Site d} (hx : x 0 = h) :
    Disjoint (↑(exits x) : Set (Sym2 (Site d))) (slabStar d h).edgeSet := by
  rw [Set.disjoint_left]
  intro e he heE
  obtain ⟨v, rfl, hv⟩ := apply_zero_of_mem_exits (Finset.mem_coe.1 he)
  rw [slabStar, mem_edgeSet_starGraph] at heE
  obtain ⟨-, -, hvs, hB⟩ := heE
  rcases hv with hv | hv
  · exact hB ⟨Or.inr (mem_plane_iff.2 hx), Or.inr (mem_plane_iff.2 (by rw [hv, hx]))⟩
  · have := (mem_slab_iff.1 hvs).2
    rw [hv, hx] at this
    omega

/-- **Finite energy for the level set** ((7.16) in the slab geometry of p. 165): for `h ≥ 2`,
`(1 - p)^{2d(n-1)} · P_p(1 ≤ U(h) < n) ≤ P_p(the ℍ*-cluster of b(0) has maximal height h)`.
[cite: GrimmettPercolation1999, §7.2 (7.16) p. 151; §7.3 p. 165] -/
theorem finiteEnergy_slabLevelSet [NeZero d] {m h : ℕ} (hh : 2 ≤ h) (n : ℕ) (p : unitInterval) :
    (1 - (p : ℝ)) ^ (2 * d * (n - 1)) * (bondPercolation (zdGraph d) p).real (slabLevelSmall d m h n) ≤
      (bondPercolation (zdGraph d) p).real (maxHeightEvent d m h) := by
  have hfe := bondPercolation_real_finiteEnergy (zdGraph d) p (A := slabLevelSmall d m h n)
    (slabStar d h).edgeSet (slabLevelFinset d m h) exitsOf (2 * d * (n - 1))
    (determinedBy_slabLevelSmall_inter m h n) (measurableSet_slabLevelSmall_inter m h n)
    (fun ω hω => by
      rw [exitsOf, Finset.coe_biUnion]
      refine Set.disjoint_iUnion₂_left.2 fun x hx => exits_disjoint_edgeSet_slabStar ?_
      have hx' : x ∈ slabLevelSet d m h ω := by rw [← coe_slabLevelFinset hω]; exact hx
      exact hx'.1)
    (fun ω hω => by
      obtain ⟨hf, -, hlt⟩ := hω
      calc (exitsOf (slabLevelFinset d m h ω)).card ≤ 2 * d * (slabLevelFinset d m h ω).card :=
            card_exitsOf_le _
        _ ≤ 2 * d * (n - 1) := by
            apply Nat.mul_le_mul_left
            have : (slabLevelFinset d m h ω).card = hf.toFinset.card := by simp [slabLevelFinset, hf]
            omega)
  refine hfe.trans (measureReal_mono ?_)
  rintro ω ⟨hω, hcl⟩
  have hcoe := coe_slabLevelFinset hω
  refine mem_maxHeightEvent_of_exits_closed hh ?_ fun x hx e he => hcl e ?_
  · obtain ⟨hf, h1, -⟩ := hω
    obtain ⟨x, hx⟩ := Finset.card_pos.1 h1
    exact ⟨x, hf.mem_toFinset.1 hx⟩
  · rw [exitsOf, Finset.mem_biUnion]
    refine ⟨x, ?_, he⟩
    rw [← Finset.mem_coe, hcoe]
    exact hx

/-! ## (7.41): `U(h)` is large with high probability -/

/-- The event `{U(h) < n}` (the level set is finite with fewer than `n` elements).
[cite: GrimmettPercolation1999, §7.3 p. 165 (U(h) < 2N₂)] -/
def slabLevelLT (d : ℕ) [NeZero d] (m h n : ℕ) : Set (BondConfig (Site d)) :=
  {ω | ∃ hf : (slabLevelSet d m h ω).Finite, hf.toFinset.card < n}

/-- `{U(h) < n}` as a union of level-set events. [folklore] -/
theorem slabLevelLT_eq_iUnion [NeZero d] (m h n : ℕ) :
    slabLevelLT d m h n = ⋃ W : Finset (Site d), {ω | slabLevelSet d m h ω = ↑W} ∩ {_ω | W.card < n} := by
  ext ω
  simp only [slabLevelLT, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
  constructor
  · rintro ⟨hf, hlt⟩
    exact ⟨hf.toFinset, by rw [Set.Finite.coe_toFinset], hlt⟩
  · rintro ⟨W, hW, hlt⟩
    have hf : (slabLevelSet d m h ω).Finite := by rw [hW]; exact W.finite_toSet
    have hW' : hf.toFinset = W := by
      apply Finset.coe_injective
      rw [Set.Finite.coe_toFinset, hW]
    exact ⟨hf, by rwa [hW']⟩

/-- `{U(h) < n}` is measurable. [folklore] -/
theorem measurableSet_slabLevelLT [NeZero d] (m h n : ℕ) : MeasurableSet (slabLevelLT d m h n) := by
  rw [slabLevelLT_eq_iUnion]
  exact MeasurableSet.iUnion fun W => (measurableSet_slabLevelSet_eq m h _).inter (MeasurableSet.const _)

/-- `{b(0) ↔ ∞ in ℍ*} ∩ {U(h) < n} ⊆ (⋃_{y ∈ b(0)} {y ↔ ∞ in ℍ*, heights ≤ h}) ∪ {1 ≤ U(h) < n}`
for `h ≥ 2`. [cite: GrimmettPercolation1999, §7.3 pp. 165–166] -/
theorem centralSquarePercolates_inter_slabLevelLT_subset [NeZero d] {m h : ℕ} (hh : 2 ≤ h) (n : ℕ) :
    centralSquarePercolates d m ∩ slabLevelLT d m h n ⊆
      (⋃ y ∈ centralSquare d m, (percolatesVia (halfSpaceStar d) y ∩
        {ω | ∀ z ∈ openClusterIn (halfSpaceStar d) ω y, z 0 ≤ h})) ∪
        slabLevelSmall d m h n := by
  rintro ω ⟨hperc, hf, hlt⟩
  by_cases hemp : slabLevelSet d m h ω = ∅
  · exact Or.inl (centralSquarePercolates_inter_slabLevelSet_empty_subset hh ⟨hperc, hemp⟩)
  · refine Or.inr ⟨hf, ?_, hlt⟩
    rw [Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero, ← Finset.coe_eq_empty,
      Set.Finite.coe_toFinset]
    exact hemp

/-- **`a_h`-bound**: for `h ≥ 2` and `p > 0`,
`(1 - p)^{2d(n-1)} P_p(b(0) ↔ ∞ in ℍ*, U(h) < n) ≤ P_p(maxHeightEvent m h)`.
[cite: GrimmettPercolation1999, §7.3 pp. 165–166 ((7.16)-type bound)] -/
theorem prob_centralSquarePercolates_inter_slabLevelLT_le [NeZero d] {m h : ℕ} (hh : 2 ≤ h) (n : ℕ)
    (p : unitInterval) (hp : 0 < (p : ℝ)) :
    (1 - (p : ℝ)) ^ (2 * d * (n - 1)) *
        (bondPercolation (zdGraph d) p).real (centralSquarePercolates d m ∩ slabLevelLT d m h n) ≤
      (bondPercolation (zdGraph d) p).real (maxHeightEvent d m h) := by
  have hle : (bondPercolation (zdGraph d) p).real (centralSquarePercolates d m ∩ slabLevelLT d m h n) ≤
      (bondPercolation (zdGraph d) p).real (slabLevelSmall d m h n) := by
    calc (bondPercolation (zdGraph d) p).real (centralSquarePercolates d m ∩ slabLevelLT d m h n)
        ≤ (bondPercolation (zdGraph d) p).real
            ((⋃ y ∈ centralSquare d m, (percolatesVia (halfSpaceStar d) y ∩
              {ω | ∀ z ∈ openClusterIn (halfSpaceStar d) ω y, z 0 ≤ h})) ∪
              slabLevelSmall d m h n) :=
          measureReal_mono (centralSquarePercolates_inter_slabLevelLT_subset hh n)
      _ ≤ (bondPercolation (zdGraph d) p).real
            (⋃ y ∈ centralSquare d m, (percolatesVia (halfSpaceStar d) y ∩
              {ω | ∀ z ∈ openClusterIn (halfSpaceStar d) ω y, z 0 ≤ h})) +
            (bondPercolation (zdGraph d) p).real (slabLevelSmall d m h n) := measureReal_union_le _ _
      _ = (bondPercolation (zdGraph d) p).real (slabLevelSmall d m h n) := by
          rw [measureReal_def, prob_iUnion_boundedCluster_eq_zero p hp m h, ENNReal.toReal_zero,
            zero_add]
  calc (1 - (p : ℝ)) ^ (2 * d * (n - 1)) *
        (bondPercolation (zdGraph d) p).real (centralSquarePercolates d m ∩ slabLevelLT d m h n)
      ≤ (1 - (p : ℝ)) ^ (2 * d * (n - 1)) * (bondPercolation (zdGraph d) p).real (slabLevelSmall d m h n) :=
        mul_le_mul_of_nonneg_left hle (pow_nonneg (sub_nonneg.2 p.2.2) _)
    _ ≤ (bondPercolation (zdGraph d) p).real (maxHeightEvent d m h) := finiteEnergy_slabLevelSet hh n p

/-- **`a_h → 0`**: for `0 < p < 1`, `P_p(b(0) ↔ ∞ in ℍ*, U(h) < n) → 0` as `h → ∞` (Grimmett 1999,
pp. 165–166: "`P(U(h) < 2N₂) ≤ a_h + ε²` … for some `a_h` satisfying `a_h → 0` as `h → ∞`").
[cite: GrimmettPercolation1999, §7.3 pp. 165–166 (a_h → 0)] -/
theorem tendsto_prob_centralSquarePercolates_inter_slabLevelLT [NeZero d] (m n : ℕ) (p : unitInterval)
    (hp0 : 0 < (p : ℝ)) (hp : (p : ℝ) < 1) :
    Tendsto (fun h => (bondPercolation (zdGraph d) p).real (centralSquarePercolates d m ∩ slabLevelLT d m h n))
      atTop (𝓝 0) := by
  set c : ℝ := (1 - (p : ℝ)) ^ (2 * d * (n - 1)) with hc
  have hcpos : 0 < c := pow_pos (by linarith) _
  have hbound : ∀ᶠ h in atTop,
      (bondPercolation (zdGraph d) p).real (centralSquarePercolates d m ∩ slabLevelLT d m h n) ≤
        c⁻¹ * (bondPercolation (zdGraph d) p).real (maxHeightEvent d m h) := by
    filter_upwards [eventually_ge_atTop 2] with h hh
    rw [le_inv_mul_iff₀ hcpos]
    exact prob_centralSquarePercolates_inter_slabLevelLT_le hh n p hp0
  have hlim : Tendsto (fun h => c⁻¹ * (bondPercolation (zdGraph d) p).real (maxHeightEvent d m h))
      atTop (𝓝 0) := by
    simpa using (tendsto_prob_maxHeightEvent m p).const_mul c⁻¹
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun h => measureReal_nonneg) hbound

/-- **(7.41)**: for `0 < p < 1`, if `P_p(b(0) ↔ ∞ in ℍ*) > 1 - δ` (cf. (7.37)) then there is `H₀`
such that `P_p(U(h) < n) < 2δ` for all `h ≥ H₀` (Grimmett 1999, p. 166: "We pick `H₀` large
enough that `a_h ≤ ε²` for `h ≥ H₀`, and deduce that (7.41) `P_{p_c}(U(h) ≥ 2N₂) ≥ 1 - 2ε²` for
`h ≥ H₀`", with `δ = ε²`, `n = 2N₂`). [cite: GrimmettPercolation1999, §7.3 p. 166 (7.41)] -/
theorem exists_prob_slabLevelLT_lt [NeZero d] (m n : ℕ) (p : unitInterval) (hp0 : 0 < (p : ℝ))
    (hp : (p : ℝ) < 1) {δ : ℝ} (hδ : 0 < δ)
    (hm : 1 - δ < (bondPercolation (zdGraph d) p).real (centralSquarePercolates d m)) :
    ∃ H₀ : ℕ, ∀ h, H₀ ≤ h → (bondPercolation (zdGraph d) p).real (slabLevelLT d m h n) < 2 * δ := by
  have hev := (tendsto_prob_centralSquarePercolates_inter_slabLevelLT (d := d) m n p hp0 hp).eventually
    (Iio_mem_nhds hδ)
  obtain ⟨H₀, hH₀⟩ := eventually_atTop.1 hev
  refine ⟨H₀, fun h hh => ?_⟩
  have h1 : (bondPercolation (zdGraph d) p).real (centralSquarePercolates d m ∩ slabLevelLT d m h n) < δ :=
    hH₀ h hh
  set P := bondPercolation (zdGraph d) p with hP
  have hsplit : P.real (slabLevelLT d m h n) =
      P.real (slabLevelLT d m h n ∩ centralSquarePercolates d m) +
        P.real (slabLevelLT d m h n \ centralSquarePercolates d m) :=
    (measureReal_inter_add_sdiff (measurableSet_centralSquarePercolates (d := d) m)).symm
  have h2 : P.real (centralSquarePercolates d m) +
      P.real (slabLevelLT d m h n \ centralSquarePercolates d m) ≤ 1 := by
    rw [← measureReal_union (μ := P) Set.disjoint_sdiff_right
      ((measurableSet_slabLevelLT m h n).diff (measurableSet_centralSquarePercolates (d := d) m))]
    exact measureReal_le_one
  rw [hsplit, Set.inter_comm]
  linarith

end BGNd

end Percolation.Literature

end
