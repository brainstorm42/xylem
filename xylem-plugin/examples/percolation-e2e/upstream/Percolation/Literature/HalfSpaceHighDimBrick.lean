import Percolation.Literature.HalfSpaceHighDimSlab
import Percolation.Util.Linter

/-!
# Bricks `B(l,h)*` in `ℤ^d`: the counts `U(l,h)`, `V(l,h)`, (7.42), and no percolation in a column

Fourth step of the bottom-up proof, in every dimension
`d`, of the finite-size criterion of the Barsky–Grimmett–Newman theorem (Grimmett, *Percolation*,
2nd ed. (1999), §7.3, Lemma (7.36) = Barsky–Grimmett–Newman 1991, Prop. 2.1), after its `d = 3`
model. Grimmett introduces, for the brick `B(l,h) = [-l,l]^{d-1} × [0,h]` with top `T(l,h)` and
sides `S(l,h)` (`HalfSpaceHighDim.lean`),

> `U(l,h) = |{x ∈ T(l,h) : b(0) ↔ x in B(l,h)*}|`. Since `U(l,h) → U(h)` as `l → ∞`, there
> exists `L₀ = L₀(h)` such that (7.42) [`P_{p_c}(U(l, H₀) ≥ 2N₂) ≥ 1 - 2ε` for `l ≥ L₀`] … The
> sequence `a(h) = P_{p_c}(U(l,h) ≥ N₂)` satisfies … `a(h) ≤ P_{p_c}(b(0) ↔ T(l,h) in B(l,h))
> → P_{p_c}(b(0) ↔ ∞ in B(l,∞)) = 0` as `h → ∞`. The last probability equals `0` since `B(l,∞)`
> is topologically one-dimensional. … `V(l,h) = |{x ∈ S(l,h) : b(0) ↔ x in B(l,h)*}|`,

where "`x ↔ y in B(l,h)*`" means joined by an open path of the brick using no edge joining two
vertices of `∂B(l,h) = U ∪ T ∪ S` (p. 164). In the coordinates of `HalfSpace.lean` (vertical
axis `0`) this file provides:

* `BGNd.brickBoundary`, `BGNd.brickStar d l h` (the step graph of `B(l,h)*`), `BGNd.topLinked`
  and `BGNd.sideLinked` (the sets behind `U(l,h)`, `V(l,h)`), with measurability, dependence on
  the edges of `B(l,h)*` only, and the geometric facts `brickStar_mono` (in `l`),
  `brickStar_le_slabStar`, `topLinked_notMem_rim` (a vertex of `T(l,h)` joined to `b(0)` in
  `B(l,h)*` is not on the rim `|x_j| = l`);
* **`U(l,h) ↑ U(h)`**: `topLinked_mono`, `iUnion_topLinked`, and the probability form **(7.42)**
  `tendsto_prob_topCountGE`: `P_p(U(l,h) ≥ N) → P_p(U(h) ≥ N)` as `l → ∞`;
* **the column `B(l,∞)` does not percolate**: `prob_topCountGE_le_pow`,
  `P_p(U(l,h) ≥ 1) ≤ (1 - (1-p)^{c(l)})^h` with `c(l)` the number of vertical edges of the column
  per level (if all vertical edges of the column between heights `k` and `k+1` are closed, no
  open path of the column climbs above `k`; these `h` events are independent), whence
  `tendsto_prob_topCountGE_height`: `P_p(U(l,h) ≥ N) → 0` as `h → ∞` for `p < 1`, `N ≥ 1`.

## References

* G. Grimmett, *Percolation*, 2nd ed., Grundlehren 321, Springer 1999, §7.3, proof of
  Lemma (7.36), pp. 164 (`B(L,H)`, `V*`), 166 ((7.42)–(7.44), `U(l,h)`, `V(l,h)`).
* D. J. Barsky, G. R. Grimmett, C. M. Newman, Probab. Theory Related Fields 90 (1991) 111–148,
  §2 (Prop. 2.1, Lemmas 2.4–2.5).
-/

noncomputable section

namespace Percolation.Literature

open _root_.MeasureTheory _root_.ProbabilityTheory _root_.Filter LatticeModels unitInterval
open scoped _root_.ENNReal _root_.Topology

namespace BGNd

variable {d : ℕ}

/-! ## The brick `B(l,h)*` -/

/-- The boundary `∂B(l,h) = U ∪ T ∪ S` of the brick (underside, top and sides).
[cite: GrimmettPercolation1999, §7.3 p. 164] -/
def brickBoundary (d : ℕ) [NeZero d] (l h : ℕ) : Set (Site d) :=
  underside d l h ∪ top d l h ∪ sides d l h

/-- Membership in the boundary of the brick. [folklore] -/
theorem mem_brickBoundary_iff [NeZero d] {l h : ℕ} {x : Site d} :
    x ∈ brickBoundary d l h ↔
      x ∈ brick d l h ∧ (x 0 = 0 ∨ x 0 = h ∨ ∃ j : Fin d, j ≠ 0 ∧ |x j| = l) := by
  simp only [brickBoundary, underside, top, sides, Set.mem_union, Set.mem_setOf_eq]
  tauto

/-- The step graph of **`B(l,h)*`**: nearest-neighbour steps inside the brick joining no two
vertices of its boundary (Grimmett 1999, p. 164, "`x ↔ y in V*`" with `V = B(l,h)`).
[cite: GrimmettPercolation1999, §7.3 p. 164 (B(l,h)*)] -/
def brickStar (d : ℕ) [NeZero d] (l h : ℕ) : SimpleGraph (Site d) :=
  starGraph (zdGraph d) (brick d l h) (brickBoundary d l h)

/-- The brick lies in the slab of the same height. [folklore] -/
theorem brick_subset_slab [NeZero d] (l h : ℕ) : brick d l h ⊆ slab d h :=
  fun _ hx => mem_slab_iff.2 hx.1

/-- `B(l,h)*`-paths are `S_h*`-paths. [folklore] -/
theorem brickStar_le_slabStar [NeZero d] (l h : ℕ) : brickStar d l h ≤ slabStar d h := by
  intro u v huv
  refine ⟨huv.1, brick_subset_slab l h huv.2.1, brick_subset_slab l h huv.2.2.1, fun hB => huv.2.2.2 ?_⟩
  simp only [Set.mem_union, mem_plane_iff] at hB
  refine ⟨mem_brickBoundary_iff.2 ⟨huv.2.1, ?_⟩, mem_brickBoundary_iff.2 ⟨huv.2.2.1, ?_⟩⟩
  · rcases hB.1 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
  · rcases hB.2 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)

/-- `B(l,h)*`-paths are `ℍ*`-paths. [folklore] -/
theorem brickStar_le_halfSpaceStar [NeZero d] (l h : ℕ) : brickStar d l h ≤ halfSpaceStar d :=
  (brickStar_le_slabStar l h).trans (slabStar_le_halfSpaceStar h)

/-- A smaller brick lies in a larger one. [folklore] -/
theorem brick_mono [NeZero d] (h : ℕ) {l l' : ℕ} (hl : l ≤ l') : brick d l h ⊆ brick d l' h := by
  intro u hu
  rw [mem_brick] at hu ⊢
  exact ⟨hu.1, fun j hj => (hu.2 j hj).trans (by exact_mod_cast hl)⟩

/-- **`B(l,h)* ≤ B(l',h)*` for `l ≤ l'`**: a step of the smaller brick joining two boundary
vertices of the larger brick joins two vertices of `U ∪ T`, hence of the smaller boundary.
[cite: GrimmettPercolation1999, §7.3 p. 166 (U(l,h) → U(h))] -/
theorem brickStar_mono [NeZero d] (h : ℕ) {l l' : ℕ} (hl : l ≤ l') : brickStar d l h ≤ brickStar d l' h := by
  intro u v huv
  obtain ⟨hzd, hu, hv, hB⟩ := huv
  refine ⟨hzd, brick_mono h hl hu, brick_mono h hl hv, fun hB' => hB ?_⟩
  rw [mem_brickBoundary_iff, mem_brickBoundary_iff] at hB' ⊢
  rw [mem_brick] at hu hv
  rcases eq_or_lt_of_le hl with rfl | hlt
  · exact hB'
  · -- `l < l'`: neither endpoint is on the rim of the larger brick, so both are in `U' ∪ T'`
    have hl' : (l : ℤ) < l' := by exact_mod_cast hlt
    have key : ∀ w : Site d, (∀ j : Fin d, j ≠ 0 → |w j| ≤ l) →
        (w 0 = 0 ∨ w 0 = h ∨ ∃ j : Fin d, j ≠ 0 ∧ |w j| = l') → (w 0 = 0 ∨ w 0 = h) := by
      rintro w hw (h1 | h1 | ⟨j, hj, hjl⟩)
      · exact Or.inl h1
      · exact Or.inr h1
      · exfalso; have := hw j hj; omega
    have hu0 := key u hu.2 hB'.1.2
    have hv0 := key v hv.2 hB'.2.2
    refine ⟨⟨mem_brick.2 hu, ?_⟩, ⟨mem_brick.2 hv, ?_⟩⟩
    · rcases hu0 with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
    · rcases hv0 with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)

/-! ## `U(l,h)` and `V(l,h)` as sets -/

/-- **Grimmett's `U(l,h)`, as a set**: the vertices of the top `T(l,h)` joined to `b(0)` in
`B(l,h)*` (`U(l,h)` is its cardinality). [cite: GrimmettPercolation1999, §7.3 p. 166 (U(l,h))] -/
def topLinked (d : ℕ) [NeZero d] (m l h : ℕ) (ω : BondConfig (Site d)) : Set (Site d) :=
  {x | x ∈ top d l h ∧ ∃ y ∈ centralSquare d m, x ∈ openClusterIn (brickStar d l h) ω y}

/-- **Grimmett's `V(l,h)`, as a set**: the vertices of the sides `S(l,h)` joined to `b(0)` in
`B(l,h)*`. [cite: GrimmettPercolation1999, §7.3 p. 166 (V(l,h))] -/
def sideLinked (d : ℕ) [NeZero d] (m l h : ℕ) (ω : BondConfig (Site d)) : Set (Site d) :=
  {x | x ∈ sides d l h ∧ ∃ y ∈ centralSquare d m, x ∈ openClusterIn (brickStar d l h) ω y}

/-- The brick is finite (it lies in a box). [folklore] -/
theorem brick_finite [NeZero d] (l h : ℕ) : (brick d l h).Finite :=
  (box d (l + h + 0)).finite_toSet.subset (brick_subset_box 0 l h)

/-- `U(l,h)`'s set is finite. [folklore] -/
theorem topLinked_finite [NeZero d] (m l h : ℕ) (ω : BondConfig (Site d)) : (topLinked d m l h ω).Finite :=
  (brick_finite l h).subset fun _ hx => hx.1.1

/-- `V(l,h)`'s set is finite. [folklore] -/
theorem sideLinked_finite [NeZero d] (m l h : ℕ) (ω : BondConfig (Site d)) : (sideLinked d m l h ω).Finite :=
  (brick_finite l h).subset fun _ hx => hx.1.1

/-- `U(l,h)` only depends on the edges of `B(l,h)*`. [folklore] -/
theorem topLinked_inter_edgeSet [NeZero d] (m l h : ℕ) (ω : BondConfig (Site d)) :
    topLinked d m l h (ω ∩ (brickStar d l h).edgeSet) = topLinked d m l h ω := by
  simp only [topLinked, openClusterIn_inter_edgeSet]

/-- `V(l,h)` only depends on the edges of `B(l,h)*`. [folklore] -/
theorem sideLinked_inter_edgeSet [NeZero d] (m l h : ℕ) (ω : BondConfig (Site d)) :
    sideLinked d m l h (ω ∩ (brickStar d l h).edgeSet) = sideLinked d m l h ω := by
  simp only [sideLinked, openClusterIn_inter_edgeSet]

/-- `{x ∈ U(l,h)-set}` is measurable. [folklore] -/
theorem measurableSet_mem_topLinked [NeZero d] (m l h : ℕ) (x : Site d) :
    MeasurableSet {ω : BondConfig (Site d) | x ∈ topLinked d m l h ω} := by
  have : {ω : BondConfig (Site d) | x ∈ topLinked d m l h ω} =
      {_ω | x ∈ top d l h} ∩ ⋃ y ∈ centralSquare d m, openConnVia (brickStar d l h) y x := by
    ext ω
    simp only [topLinked, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iUnion, exists_prop, openConnVia]
  rw [this]
  exact (MeasurableSet.const _).inter
    (MeasurableSet.biUnion (Set.to_countable _) fun y _ => measurableSet_openConnVia _ y x)

/-- `{x ∈ V(l,h)-set}` is measurable. [folklore] -/
theorem measurableSet_mem_sideLinked [NeZero d] (m l h : ℕ) (x : Site d) :
    MeasurableSet {ω : BondConfig (Site d) | x ∈ sideLinked d m l h ω} := by
  have : {ω : BondConfig (Site d) | x ∈ sideLinked d m l h ω} =
      {_ω | x ∈ sides d l h} ∩ ⋃ y ∈ centralSquare d m, openConnVia (brickStar d l h) y x := by
    ext ω
    simp only [sideLinked, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iUnion, exists_prop, openConnVia]
  rw [this]
  exact (MeasurableSet.const _).inter
    (MeasurableSet.biUnion (Set.to_countable _) fun y _ => measurableSet_openConnVia _ y x)

/-- **Events defined through a finite-set-valued statistic are measurable**: if `Φ ω ⊆ V` is always
 finite and each `{x ∈ Φ ω}` is measurable (`V` countable), then `{ω | Φ ω ∈ 𝒮}` is measurable for
 every of sets. [folklore]
-/
theorem measurableSet_setStat {V : Type*} [Countable V] {Φ : BondConfig (Site d) → Set V}
    (hΦ : ∀ x, MeasurableSet {ω | x ∈ Φ ω}) (hfin : ∀ ω, (Φ ω).Finite) (𝒮 : Set (Set V)) :
    MeasurableSet {ω | Φ ω ∈ 𝒮} := by
  classical
  have heq : ∀ W : Finset V, MeasurableSet {ω | Φ ω = ↑W} := by
    intro W
    have : {ω | Φ ω = ↑W} = (⋂ x ∈ (↑W : Set V), {ω | x ∈ Φ ω}) ∩ ⋂ x ∈ (↑W : Set V)ᶜ, {ω | x ∈ Φ ω}ᶜ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff]
      constructor
      · rintro h
        exact ⟨fun x hx => h ▸ hx, fun x hx hx' => hx (h ▸ hx')⟩
      · rintro ⟨h1, h2⟩
        ext x
        exact ⟨fun hx => by_contra fun hxW => h2 x hxW hx, fun hx => h1 x hx⟩
    rw [this]
    exact (MeasurableSet.biInter (Set.to_countable _) fun x _ => hΦ x).inter
      (MeasurableSet.biInter (Set.to_countable _) fun x _ => (hΦ x).compl)
  have : {ω | Φ ω ∈ 𝒮} = ⋃ W ∈ {W : Finset V | (↑W : Set V) ∈ 𝒮}, {ω | Φ ω = ↑W} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    constructor
    · intro h
      exact ⟨(hfin ω).toFinset, by simpa using h, by simp⟩
    · rintro ⟨W, hW, hωW⟩
      rwa [hωW]
  rw [this]
  exact MeasurableSet.biUnion (Set.to_countable _) fun W _ => heq W

/-! ## Geometry of `B(l,h)*`-clusters -/

/-- Coordinates of `u ± e_i` off the axis `i`. [folklore] -/
theorem add_unitVec_apply_of_ne {i j : Fin d} (u : Site d) (h : j ≠ i) : (u + unitVec i) j = u j := by
  simp [unitVec_apply_of_ne h]

/-- Coordinates of `u ± e_i` off the axis `i`. [folklore] -/
theorem sub_unitVec_apply_of_ne {i j : Fin d} (u : Site d) (h : j ≠ i) : (u - unitVec i) j = u j := by
  simp [unitVec_apply_of_ne h]

/-- Coordinates of `u + e_i` on the axis `i`. [folklore] -/
@[simp] theorem add_unitVec_apply_same (i : Fin d) (u : Site d) : (u + unitVec i) i = u i + 1 := by
  simp

/-- Coordinates of `u - e_i` on the axis `i`. [folklore] -/
@[simp] theorem sub_unitVec_apply_same (i : Fin d) (u : Site d) : (u - unitVec i) i = u i - 1 := by
  simp

/-- A step of `ℤ^d` changing the height is vertical: all horizontal coordinates agree. [folklore] -/
theorem apply_eq_of_adj_of_apply_zero_ne [NeZero d] {u v : Site d} (h : (zdGraph d).Adj u v)
    (h0 : v 0 ≠ u 0) {j : Fin d} (hj : j ≠ 0) : v j = u j := by
  obtain ⟨i, rfl | rfl⟩ := zdGraph_adj_cases' h
  · by_cases hi : i = 0
    · subst hi; exact add_unitVec_apply_of_ne u hj
    · exact absurd (add_unitVec_apply_of_ne u (Ne.symm hi)) h0
  · by_cases hi : i = 0
    · subst hi; exact sub_unitVec_apply_of_ne u hj
    · exact absurd (sub_unitVec_apply_of_ne u (Ne.symm hi)) h0

/-- **A vertex of the top joined to `b(0)` in `B(l,h)*` is not on the rim** (`h ≥ 1`): the last
step of such a path enters `x ∈ T(l,h) ⊆ ∂B` from a vertex which is not in `∂B`, hence from the
vertex `x - e₀` directly below, which is interior. [cite: GrimmettPercolation1999, §7.3 p. 166] -/
theorem topLinked_notMem_rim [NeZero d] {m l h : ℕ} (hh : 1 ≤ h) {ω : BondConfig (Site d)} {x : Site d}
    (hx : x ∈ topLinked d m l h ω) : ∀ j : Fin d, j ≠ 0 → |x j| < l := by
  obtain ⟨hxtop, y, hy, hxy⟩ := hx
  have hy0 : y 0 = 0 := (mem_centralSquare_iff.1 hy).1
  -- the set of vertices which, if at height `h`, are off the rim, is closed under `B(l,h)*`-steps
  have hcl := BGN.openClusterIn_subset_of_closed (K := brickStar d l h) (ω := ω) (x := y)
    (S := {z : Site d | z 0 = h → ∀ j : Fin d, j ≠ 0 → |z j| < l}) (fun h0 => by rw [hy0] at h0; omega)
    (fun u _ v huv hv0 => by
      rw [SimpleGraph.inf_adj] at huv
      obtain ⟨-, hzd, hu, hv, hB⟩ := huv
      rw [mem_brickBoundary_iff, mem_brickBoundary_iff] at hB
      rw [mem_brick] at hu hv
      have huB : ¬(u 0 = 0 ∨ u 0 = ↑h ∨ ∃ j : Fin d, j ≠ 0 ∧ |u j| = ↑l) := fun h' =>
        hB ⟨⟨mem_brick.2 hu, h'⟩, ⟨mem_brick.2 hv, Or.inr (Or.inl hv0)⟩⟩
      push Not at huB
      intro j hj
      have hvu0 : v 0 ≠ u 0 := by rw [hv0]; exact Ne.symm huB.2.1
      rw [apply_eq_of_adj_of_apply_zero_ne hzd hvu0 hj]
      exact lt_of_le_of_ne (hu.2 j hj) (huB.2.2 j hj))
  exact hcl hxy hxtop.2

/-- `U(l,h)`'s set is contained in `U(h)`'s set. [folklore] -/
theorem topLinked_subset_slabLevelSet [NeZero d] (m l h : ℕ) (ω : BondConfig (Site d)) :
    topLinked d m l h ω ⊆ slabLevelSet d m h ω := by
  rintro x ⟨hxtop, y, hy, hxy⟩
  exact ⟨hxtop.2, y, hy, openClusterIn_mono_graph (brickStar_le_slabStar l h) ω y hxy⟩

/-- `U(l,h)`'s set increases with `l`. [cite: GrimmettPercolation1999, §7.3 p. 166] -/
theorem topLinked_mono [NeZero d] (h m : ℕ) {l l' : ℕ} (hl : l ≤ l') (ω : BondConfig (Site d)) :
    topLinked d m l h ω ⊆ topLinked d m l' h ω := by
  rintro x ⟨hxtop, y, hy, hxy⟩
  exact ⟨⟨brick_mono h hl hxtop.1, hxtop.2⟩, y, hy, openClusterIn_mono_graph (brickStar_mono h hl) ω y hxy⟩

/-- A uniform bound on all coordinates of the vertices of a walk. [folklore] -/
theorem exists_bound_support {G : SimpleGraph (Site d)} {u v : Site d} (w : G.Walk u v) :
    ∃ R : ℕ, ∀ z ∈ w.support, ∀ i, |z i| ≤ R := by
  classical
  obtain ⟨R, hR⟩ := exists_subset_box w.support.toFinset
  refine ⟨R, fun z hz i => ?_⟩
  exact (mem_box_iff_abs.1 (hR (List.mem_toFinset.2 hz))) i

/-- **`U(l,h) ↑ U(h)`**: every vertex at height `h` joined to `b(0)` in `S_h*` is joined to
`b(0)` in `B(l,h)*` for `l` large — an open path is finite, so it lies inside a brick whose rim
it does not touch (Grimmett 1999, p. 166: "Since `U(l,h) → U(h)` as `l → ∞`").
[cite: GrimmettPercolation1999, §7.3 p. 166 (U(l,h) → U(h))] -/
theorem iUnion_topLinked [NeZero d] (m h : ℕ) (ω : BondConfig (Site d)) :
    ⋃ l : ℕ, topLinked d m l h ω = slabLevelSet d m h ω := by
  classical
  refine Set.Subset.antisymm (Set.iUnion_subset fun l => topLinked_subset_slabLevelSet m l h ω) ?_
  rintro x ⟨hx0, y, hy, hxy⟩
  rw [mem_openClusterIn_iff] at hxy
  obtain ⟨w⟩ := hxy
  -- a bound on the coordinates along the walk
  obtain ⟨R, hR⟩ := exists_bound_support w
  have hbound : ∀ v ∈ w.support, ∀ j, |v j| < (R + 1 : ℕ) := by
    intro v hv j
    have := hR v hv j
    push_cast
    omega
  have hslab : ∀ v ∈ w.support, 0 ≤ v 0 ∧ v 0 ≤ h := by
    intro v hv
    have hyslab : y ∈ slab d h := mem_slab_iff.2 ⟨by rw [(mem_centralSquare_iff.1 hy).1],
      by rw [(mem_centralSquare_iff.1 hy).1]; positivity⟩
    have : v ∈ openClusterIn (slabStar d h) ω y := mem_openClusterIn_iff.2 ⟨w.takeUntil v hv⟩
    exact mem_slab_iff.1 (openClusterIn_starGraph_subset hyslab ω this)
  have hbrick : ∀ v ∈ w.support, v ∈ brick d (R + 1) h := fun v hv =>
    mem_brick.2 ⟨hslab v hv, fun j _ => (hbound v hv j).le⟩
  refine Set.mem_iUnion.2 ⟨R + 1, ⟨⟨hbrick x w.end_mem_support, hx0⟩, y, hy, ?_⟩⟩
  rw [mem_openClusterIn_iff]
  refine ⟨w.transfer (openGraph ω ⊓ brickStar d (R + 1) h) fun e he => ?_⟩
  induction e using Sym2.ind with
  | h u v =>
    have hadj := w.adj_of_mem_edges he
    have hu := w.fst_mem_support_of_mem_edges he
    have hv := w.snd_mem_support_of_mem_edges he
    rw [SimpleGraph.inf_adj] at hadj
    obtain ⟨hopen, hzd, -, -, hB⟩ := hadj
    rw [SimpleGraph.mem_edgeSet, SimpleGraph.inf_adj]
    refine ⟨hopen, hzd, hbrick u hu, hbrick v hv, fun hB' => hB ?_⟩
    rw [mem_brickBoundary_iff, mem_brickBoundary_iff] at hB'
    simp only [Set.mem_union, mem_plane_iff]
    have key : ∀ z ∈ w.support, (z 0 = 0 ∨ z 0 = h ∨ ∃ j : Fin d, j ≠ 0 ∧ |z j| = (R + 1 : ℕ)) →
        z 0 = 0 ∨ z 0 = h := by
      rintro z hz (h1 | h1 | ⟨j, -, hj⟩)
      · exact Or.inl h1
      · exact Or.inr h1
      · exact absurd hj (hbound z hz j).ne
    exact ⟨key u hu hB'.1.2, key v hv hB'.2.2⟩

/-! ## (7.42): `P(U(l,h) ≥ N) → P(U(h) ≥ N)` as `l → ∞` -/

/-- The event `{U(l,h) ≥ N}`. [cite: GrimmettPercolation1999, §7.3 p. 166 (7.42)] -/
def topCountGE (d : ℕ) [NeZero d] (m l h N : ℕ) : Set (BondConfig (Site d)) :=
  {ω | (N : ℕ∞) ≤ (topLinked d m l h ω).encard}

/-- The event `{U(h) ≥ N}` (Grimmett's `U(h)`, possibly infinite).
[cite: GrimmettPercolation1999, §7.3 p. 166 (7.41)] -/
def slabCountGE (d : ℕ) [NeZero d] (m h N : ℕ) : Set (BondConfig (Site d)) :=
  {ω | (N : ℕ∞) ≤ (slabLevelSet d m h ω).encard}

/-- `{U(l,h) ≥ N}` is measurable. [folklore] -/
theorem measurableSet_topCountGE [NeZero d] (m l h N : ℕ) : MeasurableSet (topCountGE d m l h N) :=
  measurableSet_setStat (measurableSet_mem_topLinked m l h) (topLinked_finite m l h)
    {W | (N : ℕ∞) ≤ W.encard}

/-- `{U(h) ≥ N}` is the complement of `{U(h) < N}` (`HalfSpaceHighDimSlab.lean`). [folklore] -/
theorem compl_slabCountGE [NeZero d] (m h N : ℕ) : (slabCountGE d m h N)ᶜ = slabLevelLT d m h N := by
  ext ω
  simp only [slabCountGE, slabLevelLT, Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
  constructor
  · intro hlt
    have hfin : (slabLevelSet d m h ω).Finite := by
      by_contra hinf
      rw [Set.Infinite.encard_eq hinf] at hlt
      exact not_top_lt hlt
    refine ⟨hfin, ?_⟩
    have := hfin.encard_eq_coe_toFinset_card
    rw [this] at hlt
    exact_mod_cast hlt
  · rintro ⟨hf, hlt⟩
    rw [hf.encard_eq_coe_toFinset_card]
    exact_mod_cast hlt

/-- `{U(l,h) ≥ N}` increases with `l`. [cite: GrimmettPercolation1999, §7.3 p. 166] -/
theorem topCountGE_mono [NeZero d] (h m N : ℕ) : Monotone fun l => topCountGE d m l h N :=
  fun _ _ hl _ hω => hω.trans (Set.encard_le_encard (topLinked_mono h m hl _))

/-- `⋃_l {U(l,h) ≥ N} = {U(h) ≥ N}`. [cite: GrimmettPercolation1999, §7.3 p. 166] -/
theorem iUnion_topCountGE [NeZero d] (h m N : ℕ) :
    ⋃ l : ℕ, topCountGE d m l h N = slabCountGE d m h N := by
  ext ω
  simp only [Set.mem_iUnion, topCountGE, slabCountGE, Set.mem_setOf_eq]
  constructor
  · rintro ⟨l, hl⟩
    exact hl.trans (Set.encard_le_encard (topLinked_subset_slabLevelSet m l h ω))
  · intro hN
    obtain ⟨T, hTsub, hTcard⟩ := Set.exists_subset_encard_eq hN
    have hTfin : T.Finite := Set.finite_of_encard_eq_coe hTcard
    rw [← iUnion_topLinked m h ω] at hTsub
    obtain ⟨Iset, hIfin, hTI⟩ := Set.finite_subset_iUnion hTfin hTsub
    set l₀ : ℕ := hIfin.toFinset.sup id
    refine ⟨l₀, ?_⟩
    rw [← hTcard]
    refine Set.encard_le_encard (hTI.trans (Set.iUnion₂_subset fun i hi => ?_))
    exact topLinked_mono h m (Finset.le_sup (f := id) (hIfin.mem_toFinset.2 hi)) ω

/-- **(7.42)**: `P_p(U(l,h) ≥ N) → P_p(U(h) ≥ N)` as `l → ∞` (continuity of measure
along `{U(l,h) ≥ N} ↑ {U(h) ≥ N}`; Grimmett 1999, p. 166: "Since `U(l,h) → U(h)` as `l → ∞`,
there exists `L₀ = L₀(h)` such that (7.42) holds"). [cite: GrimmettPercolation1999, §7.3 p. 166 (7.42)] -/
theorem tendsto_prob_topCountGE [NeZero d] (h m N : ℕ) (p : unitInterval) :
    Tendsto (fun l => (bondPercolation (zdGraph d) p).real (topCountGE d m l h N)) atTop
      (𝓝 ((bondPercolation (zdGraph d) p).real (slabCountGE d m h N))) := by
  have h1 : Tendsto (fun l => bondPercolation (zdGraph d) p (topCountGE d m l h N)) atTop
      (𝓝 (bondPercolation (zdGraph d) p (⋃ l : ℕ, topCountGE d m l h N))) :=
    tendsto_measure_iUnion_atTop (topCountGE_mono h m N)
  rw [iUnion_topCountGE] at h1
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h1

/-- (7.42) in `ε`-form: if `P_p(U(h) ≥ N) > c` then `P_p(U(l,h) ≥ N) > c` for all large `l`.
[cite: GrimmettPercolation1999, §7.3 p. 166 (7.42)] -/
theorem exists_prob_topCountGE_gt [NeZero d] (h m N : ℕ) (p : unitInterval) {c : ℝ}
    (hc : c < (bondPercolation (zdGraph d) p).real (slabCountGE d m h N)) :
    ∃ L₀ : ℕ, ∀ l, L₀ ≤ l → c < (bondPercolation (zdGraph d) p).real (topCountGE d m l h N) := by
  have hev := (tendsto_prob_topCountGE h m N p).eventually (Ioi_mem_nhds hc)
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.1 hev
  exact ⟨L₀, hL₀⟩

/-! ## The column `B(l,∞)` does not percolate: `P(U(l,h) ≥ 1) → 0` as `h → ∞` -/

/-- The column `B(l,∞) = [-l,l]^{d-1} × [0,∞)`. [cite: GrimmettPercolation1999, §7.3 p. 166 (B(l,∞))] -/
def column (d : ℕ) [NeZero d] (l : ℕ) : Set (Site d) := {x | 0 ≤ x 0 ∧ ∀ j : Fin d, j ≠ 0 → |x j| ≤ l}

/-- Membership in the column. [folklore] -/
@[simp] theorem mem_column_iff [NeZero d] {l : ℕ} {x : Site d} :
    x ∈ column d l ↔ 0 ≤ x 0 ∧ ∀ j : Fin d, j ≠ 0 → |x j| ≤ l :=
  Iff.rfl

/-- The brick lies in the column. [folklore] -/
theorem brick_subset_column [NeZero d] (l h : ℕ) : brick d l h ⊆ column d l :=
  fun _ hx => ⟨hx.1.1, hx.2⟩

/-- `B(l,h)*`-paths are paths of the column. [folklore] -/
theorem brickStar_le_withinGraph_column [NeZero d] (l h : ℕ) :
    brickStar d l h ≤ withinGraph (zdGraph d) (column d l) :=
  (starGraph_le_withinGraph _ _ _).trans (withinGraph_mono _ (brick_subset_column l h))

/-- The sites of the base `[-l,l]^{d-1} × {0}` of the column, as a `Finset`. [folklore] -/
def baseSites (d : ℕ) [NeZero d] (l : ℕ) : Finset (Site d) := (box d l).filter fun z => z 0 = 0

/-- The height of `z + k • up`. [folklore] -/
@[simp] theorem add_zsmul_up_apply_zero [NeZero d] (z : Site d) (k : ℤ) : (z + k • (up : Site d)) 0 = z 0 + k := by
  simp [up]

/-- The horizontal coordinates of `z + k • up`. [folklore] -/
theorem add_zsmul_up_apply_of_ne [NeZero d] (z : Site d) (k : ℤ) {j : Fin d} (hj : j ≠ 0) :
    (z + k • (up : Site d)) j = z j := by
  simp [up, Pi.single_eq_of_ne hj]

/-- The vertical edges of the column between heights `k` and `k + 1`.
[cite: GrimmettPercolation1999, §7.3 p. 166 (B(l,∞) one-dimensional)] -/
def levelVerticalEdges (d : ℕ) [NeZero d] (l k : ℕ) : Finset (Sym2 (Site d)) :=
  (baseSites d l).image fun z => s(z + (k : ℤ) • up, z + (k : ℤ) • up + up)

/-- There are at most `|baseSites|` such edges. [folklore] -/
theorem card_levelVerticalEdges_le [NeZero d] (l k : ℕ) :
    (levelVerticalEdges d l k).card ≤ (baseSites d l).card :=
  Finset.card_image_le

/-- The vertical edge above a column vertex at height `k` is one of them. [folklore] -/
theorem mem_levelVerticalEdges [NeZero d] {l k : ℕ} {z : Site d} (hz : z ∈ column d l) (hz0 : z 0 = k) :
    s(z, z + up) ∈ levelVerticalEdges d l k := by
  rw [levelVerticalEdges, Finset.mem_image]
  rw [mem_column_iff] at hz
  refine ⟨z + (-(k : ℤ)) • up, ?_, ?_⟩
  · simp only [baseSites, Finset.mem_filter, mem_box, add_zsmul_up_apply_zero, hz0, add_neg_cancel,
      and_true]
    intro i
    by_cases hi : i = 0
    · subst hi; rw [add_zsmul_up_apply_zero, hz0]; omega
    · rw [add_zsmul_up_apply_of_ne z _ hi]; exact abs_le.1 (hz.2 i hi)
  · have : z + (-(k : ℤ)) • (up : Site d) + (k : ℤ) • up = z := by rw [add_assoc, ← add_smul]; simp
    rw [this]

/-- The event `C_k`: all vertical edges of the column between heights `k` and `k+1` are closed.
[cite: GrimmettPercolation1999, §7.3 p. 166] -/
def levelCut (d : ℕ) [NeZero d] (l k : ℕ) : Set (BondConfig (Site d)) :=
  {ω | ∀ e ∈ levelVerticalEdges d l k, e ∉ ω}

/-- On `C_k`, an open path of the column started at height `≤ k` never climbs above `k`.
[cite: GrimmettPercolation1999, §7.3 p. 166] -/
theorem openClusterIn_column_subset_of_levelCut [NeZero d] {l k : ℕ} {ω : BondConfig (Site d)}
    (hω : ω ∈ levelCut d l k) {y : Site d} (hy0 : y 0 ≤ k) :
    openClusterIn (withinGraph (zdGraph d) (column d l)) ω y ⊆ {x | x 0 ≤ k} := by
  refine BGN.openClusterIn_subset_of_closed (S := {x : Site d | x 0 ≤ k}) hy0 fun u hu v huv => ?_
  rw [SimpleGraph.inf_adj, openGraph_adj, withinGraph_adj] at huv
  obtain ⟨⟨hopen, -⟩, hzd, hucol, -⟩ := huv
  simp only [Set.mem_setOf_eq] at hu ⊢
  have h0 := zdGraph_adj_apply_zero hzd
  rcases eq_or_lt_of_le hu with heq | hlt
  · -- `u` at height `k`: the upward edge is closed
    by_contra hv
    have hv' : v 0 = u 0 + 1 := by omega
    have := eq_add_up_of_adj hzd hv'
    subst this
    exact hω _ (mem_levelVerticalEdges hucol heq) hopen
  · omega

/-- **If `U(l,h) ≥ 1` then no level below `h` is cut**: `{U(l,h)-set ≠ ∅} ⊆ ⋂_{k<h} C_kᶜ`.
[cite: GrimmettPercolation1999, §7.3 p. 166] -/
theorem topLinked_nonempty_subset_iInter [NeZero d] (m l h : ℕ) :
    {ω | (topLinked d m l h ω).Nonempty} ⊆ ⋂ k ∈ Finset.range h, (levelCut d l k)ᶜ := by
  intro ω hω
  obtain ⟨x, hxtop, y, hy, hxy⟩ := hω
  simp only [Set.mem_iInter, Set.mem_compl_iff, Finset.mem_range]
  intro k hk hcut
  have hy0 : y 0 = 0 := (mem_centralSquare_iff.1 hy).1
  have hxcol : x ∈ openClusterIn (withinGraph (zdGraph d) (column d l)) ω y :=
    openClusterIn_mono_graph (brickStar_le_withinGraph_column l h) ω y hxy
  have := openClusterIn_column_subset_of_levelCut hcut (y := y) (by rw [hy0]; positivity) hxcol
  simp only [Set.mem_setOf_eq] at this
  rw [hxtop.2] at this
  exact absurd this (by omega)

/-- `C_k` has probability at least `(1-p)^{|baseSites|}`. [folklore] -/
theorem le_prob_levelCut [NeZero d] (l k : ℕ) (p : unitInterval) :
    (1 - (p : ℝ)) ^ (baseSites d l).card ≤ (bondPercolation (zdGraph d) p).real (levelCut d l k) :=
  (pow_le_pow_of_le_one (sub_nonneg.2 p.2.2) (sub_le_self _ p.2.1) (card_levelVerticalEdges_le l k)).trans
    (le_bondPercolation_real_forall_notMem (zdGraph d) p (levelVerticalEdges d l k))

/-- Vertical edges at different levels are different. [folklore] -/
theorem disjoint_levelVerticalEdges [NeZero d] {l k k' : ℕ} (hk : k ≠ k') :
    Disjoint (↑(levelVerticalEdges d l k) : Set (Sym2 (Site d))) ↑(levelVerticalEdges d l k') := by
  rw [Set.disjoint_left]
  intro e he he'
  rw [Finset.mem_coe, levelVerticalEdges, Finset.mem_image] at he he'
  obtain ⟨z, hz, rfl⟩ := he
  obtain ⟨z', hz', hzz⟩ := he'
  simp only [baseSites, Finset.mem_filter] at hz hz'
  rw [Sym2.eq_iff] at hzz
  rcases hzz with ⟨h1, -⟩ | ⟨h1, h2⟩
  · have := congrFun h1 0
    simp only [add_zsmul_up_apply_zero, hz.2, hz'.2] at this
    omega
  · have h1' := congrFun h1 0
    have h2' := congrFun h2 0
    simp only [add_zsmul_up_apply_zero, add_up_apply_zero, hz.2, hz'.2] at h1' h2'
    omega

/-- `C_kᶜ` is determined by the level-`k` vertical edges. [folklore] -/
theorem determinedBy_levelCut_compl [NeZero d] (l k : ℕ) :
    DeterminedBy (levelCut d l k)ᶜ (↑(levelVerticalEdges d l k) : Set (Sym2 (Site d))) :=
  (determinedBy_forall_notMem _).compl

/-- **The levels are cut independently**: `P_p(⋂_{k<h} C_kᶜ) ≤ (1 - (1-p)^{|baseSites|})^h`
("`B(l,∞)` is topologically one-dimensional", Grimmett 1999, p. 166).
[cite: GrimmettPercolation1999, §7.3 p. 166 (P(b(0) ↔ ∞ in B(l,∞)) = 0)] -/
theorem prob_iInter_levelCut_compl_le [NeZero d] (l h : ℕ) (p : unitInterval) :
    (bondPercolation (zdGraph d) p).real (⋂ k ∈ Finset.range h, (levelCut d l k)ᶜ) ≤
      (1 - (1 - (p : ℝ)) ^ (baseSites d l).card) ^ h := by
  set r : ℝ := 1 - (1 - (p : ℝ)) ^ (baseSites d l).card with hr
  -- the events `D_h = ⋂_{k<h} C_kᶜ`, their determining sets, measurability
  have hmeasC : ∀ k, MeasurableSet (levelCut d l k) := fun k => measurableSet_forall_notMem _
  have hmeasD : ∀ h, MeasurableSet (⋂ k ∈ Finset.range h, (levelCut d l k)ᶜ) := fun h =>
    MeasurableSet.biInter (Set.to_countable _) fun k _ => (hmeasC k).compl
  have hdetD : ∀ h, DeterminedBy (⋂ k ∈ Finset.range h, (levelCut d l k)ᶜ)
      (⋃ k ∈ Finset.range h, (↑(levelVerticalEdges d l k) : Set (Sym2 (Site d)))) := by
    intro h
    induction h with
    | zero => simpa using determinedBy_univ _
    | succ n ih =>
      have hsplit : (⋂ k ∈ Finset.range (n + 1), (levelCut d l k)ᶜ) =
          (⋂ k ∈ Finset.range n, (levelCut d l k)ᶜ) ∩ (levelCut d l n)ᶜ := by
        rw [Finset.range_add_one, Finset.set_biInter_insert, Set.inter_comm]
      rw [hsplit]
      refine DeterminedBy.inter (ih.mono ?_) ((determinedBy_levelCut_compl l n).mono ?_)
      · exact Set.biUnion_subset_biUnion_left fun k hk => by
          simp only [Finset.coe_range, Set.mem_Iio] at hk ⊢; omega
      · exact Set.subset_biUnion_of_mem (u := fun k => (↑(levelVerticalEdges d l k) : Set (Sym2 (Site d))))
          (by simp)
  have hr0 : 0 ≤ r := by
    rw [hr, sub_nonneg]
    exact pow_le_one₀ (sub_nonneg.2 p.2.2) (sub_le_self _ p.2.1)
  have hrC : ∀ k, (bondPercolation (zdGraph d) p).real (levelCut d l k)ᶜ ≤ r := by
    intro k
    rw [probReal_compl_eq_one_sub (hmeasC k), hr]
    linarith [le_prob_levelCut (d := d) l k p]
  induction h with
  | zero => simp
  | succ n ih =>
    have hsplit : (⋂ k ∈ Finset.range (n + 1), (levelCut d l k)ᶜ) =
        (⋂ k ∈ Finset.range n, (levelCut d l k)ᶜ) ∩ (levelCut d l n)ᶜ := by
      rw [Finset.range_add_one, Finset.set_biInter_insert, Set.inter_comm]
    have hdisj : Disjoint (⋃ k ∈ Finset.range n, (↑(levelVerticalEdges d l k) : Set (Sym2 (Site d))))
        ↑(levelVerticalEdges d l n) := by
      rw [Set.disjoint_iUnion₂_left]
      intro k hk
      exact disjoint_levelVerticalEdges (by simp at hk; omega)
    rw [hsplit, bondPercolation_real_inter_of_disjoint (zdGraph d) p hdisj (hdetD n)
      (determinedBy_levelCut_compl l n) (hmeasD n) (hmeasC n).compl, pow_succ]
    exact mul_le_mul ih (hrC n) measureReal_nonneg (pow_nonneg hr0 n)

/-- **`P_p(U(l,h) ≥ N) ≤ (1 - (1-p)^{|baseSites|})^h`** for `N ≥ 1`.
[cite: GrimmettPercolation1999, §7.3 p. 166 (a(h) → 0)] -/
theorem prob_topCountGE_le_pow [NeZero d] (m l h : ℕ) {N : ℕ} (hN : 1 ≤ N) (p : unitInterval) :
    (bondPercolation (zdGraph d) p).real (topCountGE d m l h N) ≤
      (1 - (1 - (p : ℝ)) ^ (baseSites d l).card) ^ h := by
  refine (measureReal_mono ?_).trans (prob_iInter_levelCut_compl_le l h p)
  refine Set.Subset.trans (fun ω hω => ?_) (topLinked_nonempty_subset_iInter m l h)
  simp only [topCountGE, Set.mem_setOf_eq] at hω ⊢
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  rw [hne, Set.encard_empty] at hω
  exact absurd hω (by exact_mod_cast Nat.not_succ_le_zero _ ∘ fun h => hN.trans h)

/-- **`a(h) → 0`**: `P_p(U(l,h) ≥ N) → 0` as `h → ∞`, for `p < 1`, `N ≥ 1` (Grimmett
1999, p. 166: "`a(h) ≤ P(b(0) ↔ T(l,h) in B(l,h)) → P(b(0) ↔ ∞ in B(l,∞)) = 0` as `h → ∞`. The
last probability equals `0` since `B(l,∞)` is topologically one-dimensional").
[cite: GrimmettPercolation1999, §7.3 p. 166 (a(h) → 0)] -/
theorem tendsto_prob_topCountGE_height [NeZero d] (m l : ℕ) {N : ℕ} (hN : 1 ≤ N)
    (p : unitInterval) (hp : (p : ℝ) < 1) :
    Tendsto (fun h => (bondPercolation (zdGraph d) p).real (topCountGE d m l h N)) atTop (𝓝 0) := by
  set r : ℝ := 1 - (1 - (p : ℝ)) ^ (baseSites d l).card with hr
  have hr0 : 0 ≤ r := by
    rw [hr, sub_nonneg]
    exact pow_le_one₀ (sub_nonneg.2 p.2.2) (sub_le_self _ p.2.1)
  have hr1 : r < 1 := by
    rw [hr, sub_lt_self_iff]
    exact pow_pos (by linarith) _
  have hlim : Tendsto (fun h : ℕ => r ^ h) atTop (𝓝 0) := tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun h => measureReal_nonneg)
    (Eventually.of_forall fun h => prob_topCountGE_le_pow m l h hN p)

end BGNd

end Percolation.Literature

end
