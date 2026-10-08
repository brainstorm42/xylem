import Percolation.Literature.HalfSpaceBrickSymmetry
import Percolation.Literature.HalfSpaceHighDimBrick
import Percolation.Util.Linter

/-!
# The vertical-edge step (7.45)–(7.46) and the exits of the brick ((7.16)-type bound) in `ℤ^d`

Fifth step of the bottom-up proof, in every dimension
`d`, of the finite-size criterion of the Barsky–Grimmett–Newman theorem (Grimmett, *Percolation*,
2nd ed. (1999), §7.3, Lemma (7.36) = Barsky–Grimmett–Newman 1991, Prop. 2.1), after its `d = 3`
models `HalfSpaceBrickUp.lean` (second half) and. Grimmett, p. 167:

> "given `N₂` points `z` in `T(l, H₁(l) - 1)`, there is by (7.40) at least probability `1 - ε`
> that `M` or more of the edges `⟨z, z + (0,0,1)⟩` are open (note that this last event is
> conditionally independent of the states of all edges in `B(l, H₁(l) - 1)`). Therefore, the
> conditional probability in (7.45) is at least `1 - ε`, whence (7.46) … It is a consequence
> of (7.44) that the bricks `B(l, H₁(l))` satisfy `B(l, H₁(l)) ↑ ℍ` as `l → ∞`. As in
> (7.15)–(7.16) with `U(n)` replaced by `U(l, H₁(l)) + V(l, H₁(l))` and `B(m)` replaced by
> `b(0)`, `P_{p_c}(U + V < M + N₂) ≤ a_l + ε²` for some `a_l → 0` … It follows by the FKG
> inequality that `P(U < N₂) P(V < M) ≤ P(U + V < M + N₂)`."

* `BGNd.prob_topCountGE_succ_ge` — **(7.45)–(7.46)**:
  `P_p(U(l,h+1) ≥ M) ≥ (1 - M(1-p)^g) · P_p(U(l,h) ≥ M g)` (`h ≥ 1`), via
  `BGNd.up_mem_topLinked` (an open vertical edge above a linked top vertex lifts it one level)
  and the conditional-independence decomposition `bondPercolation_real_inter_memDep_ge`;
* `BGNd.boundaryLinked` (the set behind `U + V`), `BGNd.bExits` (the at most `2d` edges at a
  boundary vertex leading out of the brick or along its boundary), the geometric heart
  `BGNd.openClusterIn_halfSpaceStar_subset_brickStar` (closed exits at all linked top/side
  vertices confine the `ℍ*`-cluster of `b(0)` to its `B(l,h)*`-cluster; `h ≥ 2`, `m ≤ l`),
  `BGNd.confined` with the finite-energy bound `finiteEnergy_boundaryLinked` and
  `tendsto_prob_confined` (**`a_l → 0`**: every configuration is confined in `B(l, H l)` for only
  finitely many `l` when `H l → ∞`);
* the FKG step for the decreasing events `{U < N}`, `{V^a < M}` (`V^a` the linked vertices of
  the two facets `|x_a| = l`, `a` a horizontal axis): `BGNd.prob_mul_prod_le_boundaryCountLT`,
  `P(U < N) ∏_a P(V^a < M) ≤ P(U + V < N + (d-1) M)` (`harris_fkg_lower`).

## References

* G. Grimmett, *Percolation*, 2nd ed., Grundlehren 321, Springer 1999, §7.3, proof of
  Lemma (7.36), pp. 166–167, (7.45)–(7.47); §7.2, (7.15)–(7.16), p. 151.
* D. J. Barsky, G. R. Grimmett, C. M. Newman, Probab. Theory Related Fields 90 (1991) 111–148,
  §2 (Lemmas 2.4–2.6).
-/

noncomputable section

namespace Percolation.Literature

open _root_.MeasureTheory _root_.ProbabilityTheory _root_.Filter LatticeModels unitInterval
open scoped _root_.ENNReal _root_.Topology

namespace BGNd

variable {d : ℕ}

/-! ## (7.45)–(7.46): from `U(l,h) ≥ M g` to `U(l,h+1) ≥ M` -/

/-- `B(l,h)* ≤ B(l,h+1)*`: a step of the lower brick joining two boundary vertices of the
higher brick joins two vertices of `U ∪ S`, hence of the lower boundary. [folklore] -/
theorem brickStar_le_succ [NeZero d] (l h : ℕ) : brickStar d l h ≤ brickStar d l (h + 1) := by
  intro u v huv
  obtain ⟨hzd, hu, hv, hB⟩ := huv
  rw [mem_brick] at hu hv
  have hu' : u ∈ brick d l (h + 1) := mem_brick.2 ⟨⟨hu.1.1, by push_cast; linarith [hu.1.2]⟩, hu.2⟩
  have hv' : v ∈ brick d l (h + 1) := mem_brick.2 ⟨⟨hv.1.1, by push_cast; linarith [hv.1.2]⟩, hv.2⟩
  refine ⟨hzd, hu', hv', fun hB' => hB ?_⟩
  rw [mem_brickBoundary_iff, mem_brickBoundary_iff] at hB' ⊢
  refine ⟨⟨mem_brick.2 hu, ?_⟩, ⟨mem_brick.2 hv, ?_⟩⟩
  · rcases hB'.1.2 with h1 | h1 | h1
    · exact Or.inl h1
    · exfalso; push_cast at h1; linarith [hu.1.2]
    · exact Or.inr (Or.inr h1)
  · rcases hB'.2.2 with h1 | h1 | h1
    · exact Or.inl h1
    · exfalso; push_cast at h1; linarith [hv.1.2]
    · exact Or.inr (Or.inr h1)

/-- **An open vertical edge lifts a linked top vertex one level** (Grimmett 1999, p. 167): if
`z ∈ T(l,h)` is joined to `b(0)` in `B(l,h)*` (`h ≥ 1`) and the edge `⟨z, z + e₀⟩` is open,
then `z + e₀ ∈ T(l,h+1)` is joined to `b(0)` in `B(l,h+1)*`. [cite: GrimmettPercolation1999, §7.3 p. 167 (7.45)] -/
theorem up_mem_topLinked [NeZero d] {m l h : ℕ} (hh : 1 ≤ h) {ω : BondConfig (Site d)} {z : Site d}
    (hz : z ∈ topLinked d m l h ω) (hopen : s(z, z + up) ∈ ω) : z + up ∈ topLinked d m l (h + 1) ω := by
  have hrim := topLinked_notMem_rim hh hz
  obtain ⟨hztop, y, hy, hzy⟩ := hz
  have hzb := hztop.1
  rw [mem_brick] at hzb
  have hz0 := hztop.2
  have hz1 : z ∈ brick d l (h + 1) :=
    mem_brick.2 ⟨⟨hzb.1.1, by rw [hz0]; push_cast; linarith⟩, hzb.2⟩
  have hzup0 : (z + (up : Site d)) 0 = (h + 1 : ℕ) := by rw [add_up_apply_zero, hz0]; push_cast; ring
  have hzupj : ∀ j : Fin d, j ≠ 0 → (z + (up : Site d)) j = z j := fun j hj => by
    simp [up, Pi.single_eq_of_ne hj]
  have hzup : z + up ∈ brick d l (h + 1) := by
    refine mem_brick.2 ⟨⟨by rw [hzup0]; positivity, by rw [hzup0]⟩, fun j hj => ?_⟩
    rw [hzupj j hj]; exact hzb.2 j hj
  have hadj : (brickStar d l (h + 1)).Adj z (z + up) := by
    refine ⟨(zdGraph_adj_iff z (z + up)).2 ⟨0, Or.inl rfl⟩, hz1, hzup, fun hB => ?_⟩
    have hzB := (mem_brickBoundary_iff.1 hB.1).2
    rw [hz0] at hzB
    push_cast at hzB
    rcases hzB with h1 | h1 | ⟨j, hj, hjl⟩
    · omega
    · linarith
    · exact absurd hjl (hrim j hj).ne
  refine ⟨⟨hzup, hzup0⟩, y, hy, ?_⟩
  exact mem_openClusterIn_of_adj (openClusterIn_mono_graph (brickStar_le_succ l h) ω y hzy) hadj hopen

/-- The vertical edges above the top of `B(l,h)` are not edges of `B(l,h)*`. [folklore] -/
theorem upEdges_disjoint_edgeSet_brickStar [NeZero d] {l h : ℕ} {W : Finset (Site d)} (hW : ∀ z ∈ W, z 0 = h) :
    Disjoint (brickStar d l h).edgeSet (↑(upEdges W) : Set (Sym2 (Site d))) := by
  rw [Set.disjoint_right]
  intro e he heE
  rw [Finset.mem_coe, upEdges, Finset.mem_image] at he
  obtain ⟨z, hz, rfl⟩ := he
  rw [brickStar, mem_edgeSet_starGraph] at heE
  have := (mem_brick.1 heE.2.2.1).1.2
  rw [add_up_apply_zero, hW z hz] at this
  linarith

/-- The level set of `B(l,h)*` as a `Finset` (the statistic `Ψ`). [folklore] -/
def topLinkedFinset (d : ℕ) [NeZero d] (m l h : ℕ) (ω : BondConfig (Site d)) : Finset (Site d) :=
  (topLinked_finite m l h ω).toFinset

/-- `↑(topLinkedFinset) = topLinked`. [folklore] -/
@[simp] theorem coe_topLinkedFinset [NeZero d] (m l h : ℕ) (ω : BondConfig (Site d)) :
    (↑(topLinkedFinset d m l h ω) : Set (Site d)) = topLinked d m l h ω :=
  Set.Finite.coe_toFinset _

/-- The event `{U(l,h) ≥ N}` in terms of the `Finset` statistic. [folklore] -/
theorem mem_topCountGE_iff [NeZero d] {m l h N : ℕ} {ω : BondConfig (Site d)} :
    ω ∈ topCountGE d m l h N ↔ N ≤ (topLinkedFinset d m l h ω).card := by
  simp only [topCountGE, Set.mem_setOf_eq, topLinkedFinset,
    (topLinked_finite m l h ω).encard_eq_coe_toFinset_card, Nat.cast_le]

/-- **(7.45)–(7.46): the vertical-edge step.** For `h ≥ 1` and all `M, g`,
`P_p(U(l,h+1) ≥ M) ≥ (1 - M(1-p)^g) · P_p(U(l,h) ≥ M g)`: given the configuration inside
`B(l,h)*` with at least `M g` linked top vertices, the vertical edges above them are independent
of it, at least `M` of them are open with probability `≥ 1 - M(1-p)^g`
(`BGN.le_prob_atLeastOpen`), and each open one produces a distinct vertex of `T(l,h+1)` linked in
`B(l,h+1)*` (`up_mem_topLinked`). [cite: GrimmettPercolation1999, §7.3 p. 167 (7.45)–(7.46)] -/
theorem prob_topCountGE_succ_ge [NeZero d] {m l h : ℕ} (hh : 1 ≤ h) (M g : ℕ) (p : unitInterval) :
    (1 - M * (1 - (p : ℝ)) ^ g) * (bondPercolation (zdGraph d) p).real (topCountGE d m l h (M * g)) ≤
      (bondPercolation (zdGraph d) p).real (topCountGE d m l (h + 1) M) := by
  classical
  set A := topCountGE d m l h (M * g) with hA
  set Ψ := topLinkedFinset d m l h with hΨ
  set E : Finset (Site d) → Set (BondConfig (Site d)) := fun W => BGN.atLeastOpen (upEdges W) M with hE
  have hpiece : ∀ W : Finset (Site d), A ∩ Ψ ⁻¹' {W} =
      {ω | topLinked d m l h ω = ↑W} ∩ {_ω | M * g ≤ W.card} := by
    intro W
    ext ω
    simp only [hA, hΨ, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq,
      mem_topCountGE_iff]
    constructor
    · rintro ⟨hM, hW⟩
      exact ⟨by rw [← hW, coe_topLinkedFinset], hW ▸ hM⟩
    · rintro ⟨hW, hM⟩
      have hW' : topLinkedFinset d m l h ω = W := Finset.coe_injective (by rw [coe_topLinkedFinset, hW])
      exact ⟨by rw [hW']; exact hM, hW'⟩
  have hdet : ∀ W, DeterminedBy (A ∩ Ψ ⁻¹' {W}) (brickStar d l h).edgeSet := by
    intro W
    rw [hpiece]
    have : {ω : BondConfig (Site d) | topLinked d m l h ω = ↑W} ∩ {_ω | M * g ≤ W.card} =
        (fun ω : BondConfig (Site d) => ω ∩ (brickStar d l h).edgeSet) ⁻¹'
          ({ω | topLinked d m l h ω = ↑W} ∩ {_ω | M * g ≤ W.card}) := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage, topLinked_inter_edgeSet]
    rw [this]
    exact determinedBy_preimage_inter _ _
  have hmeas : ∀ W, MeasurableSet (A ∩ Ψ ⁻¹' {W}) := by
    intro W
    rw [hpiece]
    exact (measurableSet_setStat (measurableSet_mem_topLinked m l h) (topLinked_finite m l h) {S : Set (Site d) | S = ↑W}).inter
      (MeasurableSet.const _)
  have hEdet : ∀ W, DeterminedBy (E W) ↑(upEdges W) := fun W => BGN.determinedBy_atLeastOpen _ _
  have hEm : ∀ W, MeasurableSet (E W) := fun W => BGN.measurableSet_atLeastOpen _ _
  have hdisj : ∀ ω ∈ A, Disjoint (brickStar d l h).edgeSet (↑(upEdges (Ψ ω)) : Set (Sym2 (Site d))) := by
    intro ω _
    refine upEdges_disjoint_edgeSet_brickStar fun z hz => ?_
    rw [hΨ, ← Finset.mem_coe, coe_topLinkedFinset] at hz
    exact hz.1.2
  have hq : ∀ ω ∈ A, 1 - M * (1 - (p : ℝ)) ^ g ≤ (bondPercolation (zdGraph d) p).real (E (Ψ ω)) := by
    intro ω hω
    refine BGN.le_prob_atLeastOpen (zdGraph d) p (upEdges_subset_edgeSet _) ?_
    rw [card_upEdges]
    exact mem_topCountGE_iff.1 hω
  by_cases hq0 : 0 ≤ 1 - M * (1 - (p : ℝ)) ^ g
  · have hge := bondPercolation_real_inter_memDep_ge (zdGraph d) p (A := A)
      (fun _ => (brickStar d l h).edgeSet) (fun W => ↑(upEdges W)) Ψ E hdet hmeas hEdet hEm hdisj hq0 hq
    refine hge.trans (measureReal_mono ?_)
    rintro ω ⟨hωA, hωE⟩
    obtain ⟨Z, hZsub, hZcard, hZopen⟩ := hωE
    rw [mem_topCountGE_iff]
    have hlift : ∀ e ∈ Z, ∃ z ∈ topLinked d m l h ω, e = s(z, z + up) ∧ z + up ∈ topLinked d m l (h + 1) ω := by
      intro e he
      have he' := hZsub he
      rw [upEdges, Finset.mem_image] at he'
      obtain ⟨z, hz, rfl⟩ := he'
      rw [hΨ, ← Finset.mem_coe, coe_topLinkedFinset] at hz
      exact ⟨z, hz, rfl, up_mem_topLinked hh hz (hZopen (Finset.mem_coe.2 he))⟩
    choose f hf hfe hfup using hlift
    have hinj : Set.InjOn (fun e : {e // e ∈ Z} => f e.1 e.2 + up) Set.univ := by
      rintro ⟨e, he⟩ - ⟨e', he'⟩ - hff
      simp only at hff
      have : f e he = f e' he' := add_right_cancel hff
      apply Subtype.ext
      show e = e'
      rw [hfe e he, hfe e' he', this]
    calc M ≤ Z.card := hZcard
      _ = (Finset.univ : Finset {e // e ∈ Z}).card := by simp
      _ = ((Finset.univ : Finset {e // e ∈ Z}).image fun e => f e.1 e.2 + up).card := by
          rw [Finset.card_image_of_injOn (by simpa using hinj)]
      _ ≤ (topLinkedFinset d m l (h + 1) ω).card := by
          refine Finset.card_le_card fun x hx => ?_
          rw [Finset.mem_image] at hx
          obtain ⟨e, -, rfl⟩ := hx
          rw [topLinkedFinset, Set.Finite.mem_toFinset]
          exact hfup e.1 e.2
  · push Not at hq0
    exact (mul_nonpos_of_nonpos_of_nonneg hq0.le measureReal_nonneg).trans measureReal_nonneg

/-! ## `U + V`: linked vertices of the top and sides -/

/-- **The set behind `U(l,h) + V(l,h)`**: vertices of `T(l,h) ∪ S(l,h)` joined to `b(0)` in
`B(l,h)*`. [cite: GrimmettPercolation1999, §7.3 p. 167 (U + V)] -/
def boundaryLinked (d : ℕ) [NeZero d] (m l h : ℕ) (ω : BondConfig (Site d)) : Set (Site d) :=
  {x | x ∈ top d l h ∪ sides d l h ∧ ∃ y ∈ centralSquare d m, x ∈ openClusterIn (brickStar d l h) ω y}

/-- `U + V`'s set is the union of `U`'s and `V`'s. [folklore] -/
theorem boundaryLinked_eq_union [NeZero d] (m l h : ℕ) (ω : BondConfig (Site d)) :
    boundaryLinked d m l h ω = topLinked d m l h ω ∪ sideLinked d m l h ω := by
  ext x
  simp only [boundaryLinked, topLinked, sideLinked, Set.mem_union, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hx | hx, hy⟩
    exacts [Or.inl ⟨hx, hy⟩, Or.inr ⟨hx, hy⟩]
  · rintro (⟨hx, hy⟩ | ⟨hx, hy⟩)
    exacts [⟨Or.inl hx, hy⟩, ⟨Or.inr hx, hy⟩]

/-- `U + V`'s set is finite. [folklore] -/
theorem boundaryLinked_finite [NeZero d] (m l h : ℕ) (ω : BondConfig (Site d)) : (boundaryLinked d m l h ω).Finite := by
  rw [boundaryLinked_eq_union]
  exact (topLinked_finite m l h ω).union (sideLinked_finite m l h ω)

/-- `U + V` only depends on the edges of `B(l,h)*`. [folklore] -/
theorem boundaryLinked_inter_edgeSet [NeZero d] (m l h : ℕ) (ω : BondConfig (Site d)) :
    boundaryLinked d m l h (ω ∩ (brickStar d l h).edgeSet) = boundaryLinked d m l h ω := by
  simp only [boundaryLinked, openClusterIn_inter_edgeSet]

/-- `{x ∈ (U+V)-set}` is measurable. [folklore] -/
theorem measurableSet_mem_boundaryLinked [NeZero d] (m l h : ℕ) (x : Site d) :
    MeasurableSet {ω : BondConfig (Site d) | x ∈ boundaryLinked d m l h ω} := by
  have : {ω : BondConfig (Site d) | x ∈ boundaryLinked d m l h ω} =
      {ω | x ∈ topLinked d m l h ω} ∪ {ω | x ∈ sideLinked d m l h ω} := by
    ext ω; simp [boundaryLinked_eq_union]
  rw [this]
  exact (measurableSet_mem_topLinked m l h x).union (measurableSet_mem_sideLinked m l h x)

/-- Linked boundary vertices lie in the `ℍ*`-cluster of `b(0)`. [folklore] -/
theorem boundaryLinked_subset_starCluster [NeZero d] (m l h : ℕ) (ω : BondConfig (Site d)) :
    boundaryLinked d m l h ω ⊆ starCluster d m ω := by
  rintro x ⟨-, y, hy, hxy⟩
  exact mem_starCluster_iff.2 ⟨y, hy, openClusterIn_mono_graph (brickStar_le_halfSpaceStar l h) ω y hxy⟩

/-- The `B(l,h)*`-cluster of `b(0)`. [cite: GrimmettPercolation1999, §7.3 p. 167] -/
def brickCluster (d : ℕ) [NeZero d] (m l h : ℕ) (ω : BondConfig (Site d)) : Set (Site d) :=
  ⋃ y ∈ centralSquare d m, openClusterIn (brickStar d l h) ω y

/-- The central square lies in the brick when `m ≤ l`. [folklore] -/
theorem centralSquare_subset_brick [NeZero d] {m l : ℕ} (hml : m ≤ l) (h : ℕ) :
    centralSquare d m ⊆ brick d l h := by
  intro y hy
  rw [mem_centralSquare_iff] at hy
  refine mem_brick.2 ⟨⟨by rw [hy.1], by rw [hy.1]; positivity⟩, fun j hj => ?_⟩
  exact (hy.2 j hj).trans (by exact_mod_cast hml)

/-- The `B(l,h)*`-cluster of `b(0)` lies in the brick (`m ≤ l`). [folklore] -/
theorem brickCluster_subset_brick [NeZero d] {m l : ℕ} (hml : m ≤ l) (h : ℕ) (ω : BondConfig (Site d)) :
    brickCluster d m l h ω ⊆ brick d l h := by
  intro x hx
  simp only [brickCluster, Set.mem_iUnion, exists_prop] at hx
  obtain ⟨y, hy, hxy⟩ := hx
  exact openClusterIn_starGraph_subset (centralSquare_subset_brick hml h hy) ω hxy

/-! ## Exit edges at boundary vertices -/

/-- The `2d` lattice neighbours of a vertex of `ℤ^d`, as a `Finset`. [folklore] -/
def nbrs (w : Site d) : Finset (Site d) :=
  (Finset.univ.image fun i : Fin d => w + unitVec i) ∪ (Finset.univ.image fun i : Fin d => w - unitVec i)

/-- Every neighbour is in the set. [folklore] -/
theorem mem_nbrs_of_adj {w v : Site d} (h : (zdGraph d).Adj w v) : v ∈ nbrs w := by
  obtain ⟨i, rfl | rfl⟩ := zdGraph_adj_cases' h
  · exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)
  · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)

/-- At most `2d` neighbours. [folklore] -/
theorem card_nbrs_le (w : Site d) : (nbrs w).card ≤ 2 * d := by
  unfold nbrs
  calc _ ≤ (Finset.univ.image fun i : Fin d => w + unitVec i).card +
        (Finset.univ.image fun i : Fin d => w - unitVec i).card := Finset.card_union_le _ _
    _ ≤ d + d := by
        gcongr <;> exact Finset.card_image_le.trans (by simp)
    _ = 2 * d := by ring

open Classical in
/-- The **exit edges** at a boundary vertex `w` of the brick: the edges from `w` to neighbours
which are outside the brick or on its boundary (the edges closed in the finite-energy step;
Grimmett 1999, p. 151/167, "every edge exiting `∂B(n)` from `U(n)`", here together with the
boundary-internal edges since the paths of `B(l,h)*` avoid those). [cite: GrimmettPercolation1999, §7.2 (7.16) p. 151; §7.3 p. 167] -/
def bExits (d : ℕ) [NeZero d] (l h : ℕ) (w : Site d) : Finset (Sym2 (Site d)) :=
  ((nbrs w).filter fun v => ¬(v ∈ brick d l h ∧ v ∉ brickBoundary d l h)).image fun v => s(w, v)

/-- At most `2d` exit edges per vertex. [folklore] -/
theorem card_bExits_le [NeZero d] (l h : ℕ) (w : Site d) : (bExits d l h w).card ≤ 2 * d := by
  classical
  unfold bExits
  exact Finset.card_image_le.trans ((Finset.card_filter_le _ _).trans (card_nbrs_le w))

/-- Membership in `bExits`. [folklore] -/
theorem mem_bExits_iff [NeZero d] {l h : ℕ} {w : Site d} {e : Sym2 (Site d)} :
    e ∈ bExits d l h w ↔ ∃ v ∈ nbrs w, ¬(v ∈ brick d l h ∧ v ∉ brickBoundary d l h) ∧ e = s(w, v) := by
  classical
  simp only [bExits, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨v, ⟨hv, hnot⟩, rfl⟩
    exact ⟨v, hv, hnot, rfl⟩
  · rintro ⟨v, hv, hnot, rfl⟩
    exact ⟨v, ⟨hv, hnot⟩, rfl⟩

/-- Top and sides lie in the boundary. [folklore] -/
theorem top_union_sides_subset_brickBoundary [NeZero d] (l h : ℕ) :
    top d l h ∪ sides d l h ⊆ brickBoundary d l h := by
  rintro x (hx | hx)
  · exact Or.inl (Or.inr hx)
  · exact Or.inr hx

/-- The exit edges at a boundary vertex are not edges of `B(l,h)*`. [folklore] -/
theorem bExits_disjoint_edgeSet [NeZero d] {l h : ℕ} {w : Site d} (hw : w ∈ brickBoundary d l h) :
    Disjoint (↑(bExits d l h w) : Set (Sym2 (Site d))) (brickStar d l h).edgeSet := by
  rw [Set.disjoint_left]
  intro e he heE
  rw [Finset.mem_coe, mem_bExits_iff] at he
  obtain ⟨v, -, hnot, rfl⟩ := he
  rw [brickStar, mem_edgeSet_starGraph] at heE
  exact hnot ⟨heE.2.2.1, fun hvB => heE.2.2.2 ⟨hw, hvB⟩⟩

/-! ## The geometric heart: closed exits confine the `ℍ*`-cluster to the brick -/

/-- The coordinates of a neighbour differ by at most one. [folklore] -/
theorem abs_sub_le_one_of_adj {u v : Site d} (h : (zdGraph d).Adj u v) (j : Fin d) :
    v j ≤ u j + 1 ∧ u j ≤ v j + 1 := by
  obtain ⟨i, rfl | rfl⟩ := zdGraph_adj_cases' h
  · by_cases hj : j = i
    · subst hj; rw [add_unitVec_apply_same]; omega
    · rw [add_unitVec_apply_of_ne u hj]; omega
  · by_cases hj : j = i
    · subst hj; rw [sub_unitVec_apply_same]; omega
    · rw [sub_unitVec_apply_of_ne u hj]; omega

/-- **Closing the exits of the linked boundary vertices confines `ℍ*`-paths to `B(l,h)*`.** Let
`h ≥ 2`, `m ≤ l`, and suppose that at every vertex of `T ∪ S` joined to `b(0)` in `B(l,h)*` all
exit edges are closed. Then for every `y ∈ b(0)` the `ℍ*`-cluster of `y` is its
`B(l,h)*`-cluster ("`U(n+1) = ∅` if every edge exiting `∂B(n)` from `U(n)` is closed",
Grimmett 1999, p. 151, in the brick geometry of p. 167). [cite: GrimmettPercolation1999, §7.2 (7.16) p. 151; §7.3 p. 167] -/
theorem openClusterIn_halfSpaceStar_subset_brickStar [NeZero d] {m l h : ℕ} (hh : 2 ≤ h) (hml : m ≤ l)
    {ω : BondConfig (Site d)} {y : Site d} (hy : y ∈ centralSquare d m)
    (hclosed : ∀ w ∈ boundaryLinked d m l h ω, ∀ e ∈ bExits d l h w, e ∉ ω) :
    openClusterIn (halfSpaceStar d) ω y ⊆ openClusterIn (brickStar d l h) ω y := by
  have hybrick : y ∈ brick d l h := centralSquare_subset_brick hml h hy
  refine BGN.openClusterIn_subset_of_closed (self_mem_openClusterIn _ ω y) fun u hu v huv => ?_
  have hubrick : u ∈ brick d l h := openClusterIn_starGraph_subset hybrick ω hu
  rw [SimpleGraph.inf_adj, openGraph_adj] at huv
  obtain ⟨⟨hωuv, -⟩, hzd, -, hvH, hnot0⟩ := huv
  rw [mem_halfSpace_iff] at hvH
  simp only [mem_plane_iff] at hnot0
  have hub := mem_brick.1 hubrick
  have key : (brickStar d l h).Adj u v := by
    by_cases huTS : u ∈ top d l h ∪ sides d l h
    · -- `u` linked on the top or sides: all its exits are closed, so `v` is an interior vertex
      have hcl := hclosed u ⟨huTS, y, hy, hu⟩
      have hv : v ∈ brick d l h ∧ v ∉ brickBoundary d l h := by
        by_contra hnot
        exact hcl _ (mem_bExits_iff.2 ⟨v, mem_nbrs_of_adj hzd, hnot, rfl⟩) hωuv
      exact ⟨hzd, hubrick, hv.1, fun hB => hv.2 hB.2⟩
    · -- `u` not on the top or sides: `u 0 < h`, `|u j| < l`
      simp only [Set.mem_union, top, sides, Set.mem_setOf_eq, not_or, not_and, not_exists] at huTS
      have hu0 : u 0 < h := lt_of_le_of_ne hub.1.2 (huTS.1 hubrick)
      have huj : ∀ j : Fin d, j ≠ 0 → |u j| < l := fun j hj =>
        lt_of_le_of_ne (hub.2 j hj) (huTS.2 hubrick j hj)
      have hv0 := zdGraph_adj_apply_zero hzd
      -- `v` lies in the brick
      have hvb : v ∈ brick d l h := by
        rw [mem_brick]
        refine ⟨⟨hvH, by omega⟩, fun j hj => ?_⟩
        have h1 := abs_sub_le_one_of_adj hzd j
        have h2 := abs_lt.1 (huj j hj)
        exact abs_le.2 ⟨by omega, by omega⟩
      refine ⟨hzd, hubrick, hvb, fun hB => ?_⟩
      -- both endpoints in `∂B`: then `u` is on the underside …
      have huB := (mem_brickBoundary_iff.1 hB.1).2
      have hvB := (mem_brickBoundary_iff.1 hB.2).2
      have hu00 : u 0 = 0 := by
        rcases huB with h1 | h1 | ⟨j, hj, hjl⟩
        · exact h1
        · exfalso; rw [h1] at hu0; exact lt_irrefl _ hu0
        · exact absurd hjl (huj j hj).ne
      -- … and `v` is above `u` (a horizontal step stays on the underside, a downward one leaves `ℍ`)
      rcases hvB with h1 | h1 | ⟨j, hj, hjl⟩
      · exact hnot0 ⟨hu00, h1⟩
      · omega
      · have hne : v 0 ≠ u 0 := by
          intro heq
          exact hnot0 ⟨hu00, by rw [heq, hu00]⟩
        rw [apply_eq_of_adj_of_apply_zero_ne hzd hne hj] at hjl
        exact absurd hjl (huj j hj).ne
  exact mem_openClusterIn_of_adj hu key hωuv

/-- Hence closed exits give `starCluster ⊆ brickCluster`. [cite: GrimmettPercolation1999, §7.3 p. 167] -/
theorem starCluster_subset_brickCluster [NeZero d] {m l h : ℕ} (hh : 2 ≤ h) (hml : m ≤ l)
    {ω : BondConfig (Site d)} (hclosed : ∀ w ∈ boundaryLinked d m l h ω, ∀ e ∈ bExits d l h w, e ∉ ω) :
    starCluster d m ω ⊆ brickCluster d m l h ω := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := mem_starCluster_iff.1 hx
  simp only [brickCluster, Set.mem_iUnion, exists_prop]
  exact ⟨y, hy, openClusterIn_halfSpaceStar_subset_brickStar hh hml hy hclosed hxy⟩

/-- **If `U + V = 0` then `b(0) ↮ ∞ in ℍ*`** (`h ≥ 2`, `m ≤ l`). [cite: GrimmettPercolation1999, §7.3 p. 167] -/
theorem centralSquarePercolates_inter_boundaryLinked_empty [NeZero d] {m l h : ℕ} (hh : 2 ≤ h) (hml : m ≤ l) :
    centralSquarePercolates d m ∩ {ω | boundaryLinked d m l h ω = ∅} = ∅ := by
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro hperc hempty
  obtain ⟨y, hy, hωy⟩ := mem_centralSquarePercolates_iff.1 hperc
  have hsub := openClusterIn_halfSpaceStar_subset_brickStar hh hml hy (ω := ω)
    (fun w hw => by rw [hempty] at hw; exact absurd hw (Set.notMem_empty w))
  exact hωy ((brick_finite l h).subset ((hsub.trans
    (openClusterIn_starGraph_subset (centralSquare_subset_brick hml h hy) ω))))

/-! ## The confinement event and the finite-energy bound -/

/-- **The event "the `ℍ*`-cluster of `b(0)` lies in `B(l,h)` and meets `T(l,h) ∪ S(l,h)`"** (the
brick analogue of `{U(n+1) = ∅, U(n) ≠ ∅}` in (7.16)). [cite: GrimmettPercolation1999, §7.2 (7.16) p. 151; §7.3 p. 167] -/
def confined (d : ℕ) [NeZero d] (m l h : ℕ) : Set (BondConfig (Site d)) :=
  {ω | starCluster d m ω ⊆ brick d l h ∧ (starCluster d m ω ∩ (top d l h ∪ sides d l h)).Nonempty}

/-- `confined` is measurable. [folklore] -/
theorem measurableSet_confined [NeZero d] (m l h : ℕ) : MeasurableSet (confined d m l h) := by
  have h1 : {ω : BondConfig (Site d) | starCluster d m ω ⊆ brick d l h} =
      ⋂ x ∈ (brick d l h)ᶜ, {ω | x ∈ starCluster d m ω}ᶜ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_compl_iff]
    exact ⟨fun hs x hx hxs => hx (hs hxs), fun hs x hxs => by_contra fun hx => hs x hx hxs⟩
  have h2 : {ω : BondConfig (Site d) | (starCluster d m ω ∩ (top d l h ∪ sides d l h)).Nonempty} =
      ⋃ x ∈ top d l h ∪ sides d l h, {ω | x ∈ starCluster d m ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop, Set.Nonempty, Set.mem_inter_iff]
    exact ⟨fun ⟨x, hx, hxp⟩ => ⟨x, hxp, hx⟩, fun ⟨x, hxp, hx⟩ => ⟨x, hx, hxp⟩⟩
  have : confined d m l h = {ω | starCluster d m ω ⊆ brick d l h} ∩
      {ω | (starCluster d m ω ∩ (top d l h ∪ sides d l h)).Nonempty} := rfl
  rw [this, h1, h2]
  exact (MeasurableSet.biInter (Set.to_countable _) fun x _ => (measurableSet_mem_starCluster m x).compl).inter
    (MeasurableSet.biUnion (Set.to_countable _) fun x _ => measurableSet_mem_starCluster m x)

/-- **Closed exits and `U + V ≥ 1` give the confinement event.** [cite: GrimmettPercolation1999, §7.3 p. 167] -/
theorem mem_confined_of_exits_closed [NeZero d] {m l h : ℕ} (hh : 2 ≤ h) (hml : m ≤ l) {ω : BondConfig (Site d)}
    (hne : (boundaryLinked d m l h ω).Nonempty)
    (hclosed : ∀ w ∈ boundaryLinked d m l h ω, ∀ e ∈ bExits d l h w, e ∉ ω) : ω ∈ confined d m l h := by
  refine ⟨(starCluster_subset_brickCluster hh hml hclosed).trans (brickCluster_subset_brick hml h ω), ?_⟩
  obtain ⟨x, hx⟩ := hne
  exact ⟨x, boundaryLinked_subset_starCluster m l h ω hx, hx.1⟩

/-- The event `{1 ≤ U + V < K}`. [cite: GrimmettPercolation1999, §7.3 p. 167] -/
def boundarySmall (d : ℕ) [NeZero d] (m l h K : ℕ) : Set (BondConfig (Site d)) :=
  {ω | 1 ≤ (boundaryLinked_finite m l h ω).toFinset.card ∧ (boundaryLinked_finite m l h ω).toFinset.card < K}

/-- The event `{U + V < K}`. [cite: GrimmettPercolation1999, §7.3 p. 167] -/
def boundaryCountLT (d : ℕ) [NeZero d] (m l h K : ℕ) : Set (BondConfig (Site d)) :=
  {ω | (boundaryLinked_finite m l h ω).toFinset.card < K}

/-- The `Finset` statistic `Ψ = (U+V)`-set. [folklore] -/
def boundaryLinkedFinset (d : ℕ) [NeZero d] (m l h : ℕ) (ω : BondConfig (Site d)) : Finset (Site d) :=
  (boundaryLinked_finite m l h ω).toFinset

/-- `↑Ψ = (U+V)`-set. [folklore] -/
@[simp] theorem coe_boundaryLinkedFinset [NeZero d] (m l h : ℕ) (ω : BondConfig (Site d)) :
    (↑(boundaryLinkedFinset d m l h ω) : Set (Site d)) = boundaryLinked d m l h ω :=
  Set.Finite.coe_toFinset _

/-- The union of the exit edges of a finite set of vertices. [folklore] -/
def bExitsOf (d : ℕ) [NeZero d] (l h : ℕ) (W : Finset (Site d)) : Finset (Sym2 (Site d)) :=
  W.biUnion (bExits d l h)

/-- The pieces `{1 ≤ U+V < K} ∩ {Ψ = W}`. [folklore] -/
theorem boundarySmall_inter_preimage [NeZero d] (m l h K : ℕ) (W : Finset (Site d)) :
    boundarySmall d m l h K ∩ boundaryLinkedFinset d m l h ⁻¹' {W} =
      {ω | boundaryLinked d m l h ω = ↑W} ∩ {_ω | 1 ≤ W.card ∧ W.card < K} := by
  ext ω
  simp only [boundarySmall, boundaryLinkedFinset, Set.mem_inter_iff, Set.mem_preimage,
    Set.mem_singleton_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨h1, h2⟩, hW⟩
    refine ⟨by rw [← hW, Set.Finite.coe_toFinset], ?_, ?_⟩ <;> rwa [← hW]
  · rintro ⟨hW, h1, h2⟩
    have hW' : (boundaryLinked_finite m l h ω).toFinset = W :=
      Finset.coe_injective (by rw [Set.Finite.coe_toFinset, hW])
    exact ⟨⟨by rwa [hW'], by rwa [hW']⟩, hW'⟩

/-- **Finite energy for `U + V`** ((7.16) in the brick geometry of p. 167): for `h ≥ 2`,
`m ≤ l`, `(1 - p)^{2d(K-1)} · P_p(1 ≤ U+V < K) ≤ P_p(confined)`.
[cite: GrimmettPercolation1999, §7.2 (7.16) p. 151; §7.3 p. 167] -/
theorem finiteEnergy_boundaryLinked [NeZero d] {m l h : ℕ} (hh : 2 ≤ h) (hml : m ≤ l) (K : ℕ) (p : unitInterval) :
    (1 - (p : ℝ)) ^ (2 * d * (K - 1)) * (bondPercolation (zdGraph d) p).real (boundarySmall d m l h K) ≤
      (bondPercolation (zdGraph d) p).real (confined d m l h) := by
  have hfe := bondPercolation_real_finiteEnergy (zdGraph d) p (A := boundarySmall d m l h K)
    (brickStar d l h).edgeSet (boundaryLinkedFinset d m l h) (bExitsOf d l h) (2 * d * (K - 1))
    (fun W => by
      rw [boundarySmall_inter_preimage]
      have : {ω : BondConfig (Site d) | boundaryLinked d m l h ω = ↑W} ∩ {_ω | 1 ≤ W.card ∧ W.card < K} =
          (fun ω : BondConfig (Site d) => ω ∩ (brickStar d l h).edgeSet) ⁻¹'
            ({ω | boundaryLinked d m l h ω = ↑W} ∩ {_ω | 1 ≤ W.card ∧ W.card < K}) := by
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage, boundaryLinked_inter_edgeSet]
      rw [this]
      exact determinedBy_preimage_inter _ _)
    (fun W => by
      rw [boundarySmall_inter_preimage]
      exact (measurableSet_setStat (measurableSet_mem_boundaryLinked m l h) (boundaryLinked_finite m l h)
        {S : Set (Site d) | S = ↑W}).inter (MeasurableSet.const _))
    (fun ω hω => by
      rw [bExitsOf, Finset.coe_biUnion]
      refine Set.disjoint_iUnion₂_left.2 fun x hx => bExits_disjoint_edgeSet ?_
      rw [coe_boundaryLinkedFinset] at hx
      exact top_union_sides_subset_brickBoundary l h hx.1)
    (fun ω hω => by
      obtain ⟨-, hlt⟩ := hω
      calc (bExitsOf d l h (boundaryLinkedFinset d m l h ω)).card
          ≤ ∑ x ∈ boundaryLinkedFinset d m l h ω, (bExits d l h x).card := Finset.card_biUnion_le
        _ ≤ ∑ _x ∈ boundaryLinkedFinset d m l h ω, 2 * d := Finset.sum_le_sum fun x _ => card_bExits_le l h x
        _ = 2 * d * (boundaryLinkedFinset d m l h ω).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ 2 * d * (K - 1) := by
            apply Nat.mul_le_mul_left
            have : (boundaryLinkedFinset d m l h ω).card < K := hlt
            omega)
  refine hfe.trans (measureReal_mono ?_)
  rintro ω ⟨hω, hcl⟩
  refine mem_confined_of_exits_closed hh hml ?_ fun w hw e he => hcl e ?_
  · obtain ⟨h1, -⟩ := hω
    obtain ⟨x, hx⟩ := Finset.card_pos.1 h1
    exact ⟨x, (boundaryLinked_finite m l h ω).mem_toFinset.1 hx⟩
  · rw [bExitsOf, Finset.mem_biUnion]
    refine ⟨w, ?_, he⟩
    rw [← Finset.mem_coe, coe_boundaryLinkedFinset]
    exact hw

/-- `{U + V < K}` is measurable. [folklore] -/
theorem measurableSet_boundaryCountLT [NeZero d] (m l h K : ℕ) : MeasurableSet (boundaryCountLT d m l h K) := by
  have : boundaryCountLT d m l h K =
      {ω | boundaryLinked d m l h ω ∈ {S : Set (Site d) | S.ncard < K}} := by
    ext ω
    simp only [boundaryCountLT, Set.mem_setOf_eq, Set.ncard_eq_toFinset_card _ (boundaryLinked_finite m l h ω)]
  rw [this]
  exact measurableSet_setStat (measurableSet_mem_boundaryLinked m l h) (boundaryLinked_finite m l h) _

/-- `{b(0) ↔ ∞ in ℍ*} ∩ {U + V < K} ⊆ {1 ≤ U + V < K}` for `h ≥ 2`, `m ≤ l`. [cite: GrimmettPercolation1999, §7.3 p. 167] -/
theorem centralSquarePercolates_inter_boundaryCountLT_subset [NeZero d] {m l h : ℕ} (hh : 2 ≤ h) (hml : m ≤ l)
    (K : ℕ) : centralSquarePercolates d m ∩ boundaryCountLT d m l h K ⊆ boundarySmall d m l h K := by
  rintro ω ⟨hperc, hlt⟩
  refine ⟨?_, hlt⟩
  rw [Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero, ← Finset.coe_eq_empty, Set.Finite.coe_toFinset]
  intro hempty
  have : ω ∈ centralSquarePercolates d m ∩ {ω | boundaryLinked d m l h ω = ∅} := ⟨hperc, hempty⟩
  rw [centralSquarePercolates_inter_boundaryLinked_empty hh hml] at this
  exact this

/-- **`P_p(b(0) ↔ ∞ in ℍ*, U + V < K) ≤ (1-p)^{-2d(K-1)} P_p(confined)`** (`h ≥ 2`, `m ≤ l`).
[cite: GrimmettPercolation1999, §7.3 p. 167 ((7.16)-type bound)] -/
theorem prob_centralSquarePercolates_inter_boundaryCountLT_le [NeZero d] {m l h : ℕ} (hh : 2 ≤ h)
    (hml : m ≤ l) (K : ℕ) (p : unitInterval) :
    (1 - (p : ℝ)) ^ (2 * d * (K - 1)) *
        (bondPercolation (zdGraph d) p).real (centralSquarePercolates d m ∩ boundaryCountLT d m l h K) ≤
      (bondPercolation (zdGraph d) p).real (confined d m l h) :=
  (mul_le_mul_of_nonneg_left (measureReal_mono (centralSquarePercolates_inter_boundaryCountLT_subset hh hml K))
    (pow_nonneg (sub_nonneg.2 p.2.2) _)).trans (finiteEnergy_boundaryLinked hh hml K p)

/-! ## `a_l → 0`: escape to infinity of the bricks `B(l, H(l))` -/

/-- **Every configuration is confined in `B(l, H l)` for only finitely many `l`** when
`H l → ∞`: an infinite `ℍ*`-cluster of `b(0)` is never confined, a finite one has bounded
coordinates and eventually meets neither the sides `|x_j| = l` nor the top at height `H l`.
(Grimmett 1999, p. 167: "the bricks `B(l, H₁(l)) ↑ ℍ` as `l → ∞`".) [cite: GrimmettPercolation1999, §7.3 p. 167] -/
theorem eventually_notMem_confined [NeZero d] (m : ℕ) {H : ℕ → ℕ} (hH : Tendsto H atTop atTop)
    (ω : BondConfig (Site d)) : ∀ᶠ l in atTop, ω ∉ confined d m l (H l) := by
  classical
  by_cases hfin : (starCluster d m ω).Finite
  · -- bounded coordinates
    obtain ⟨R, hR⟩ : ∃ R : ℕ, ∀ x ∈ starCluster d m ω, ∀ i, |x i| < R := by
      obtain ⟨R, hR⟩ := exists_subset_box hfin.toFinset
      refine ⟨R + 1, fun x hx i => ?_⟩
      have := (mem_box_iff_abs.1 (hR (hfin.mem_toFinset.2 hx))) i
      push_cast
      omega
    filter_upwards [eventually_ge_atTop R, hH.eventually (eventually_ge_atTop R)] with l hl hHl
    rintro ⟨-, x, hx, hxTS⟩
    rcases hxTS with hxT | hxS
    · have h0 := hR x hx 0
      rw [hxT.2, abs_of_nonneg (by positivity)] at h0
      exact absurd h0 (by omega)
    · obtain ⟨j, -, hj⟩ := hxS.2
      have h1 := hR x hx j
      rw [hj] at h1
      exact absurd h1 (by omega)
  · exact Eventually.of_forall fun l hl => hfin ((brick_finite l (H l)).subset hl.1)

/-- **`P_p(confined m l (H l)) → 0` as `l → ∞`** when `H l → ∞` (continuity from above along
the decreasing tails `⋃_{l ≥ N} confined_l ↓ ∅`). [cite: GrimmettPercolation1999, §7.3 p. 167 (a_l → 0)] -/
theorem tendsto_prob_confined [NeZero d] (m : ℕ) {H : ℕ → ℕ} (hH : Tendsto H atTop atTop) (p : unitInterval) :
    Tendsto (fun l => (bondPercolation (zdGraph d) p).real (confined d m l (H l))) atTop (𝓝 0) := by
  set T : ℕ → Set (BondConfig (Site d)) := fun N => ⋃ l ∈ {l | N ≤ l}, confined d m l (H l) with hT
  have hTanti : Antitone T := by
    intro N N' hNN' ω hω
    simp only [hT, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at hω ⊢
    obtain ⟨l, hl, hωl⟩ := hω
    exact ⟨l, hNN'.trans hl, hωl⟩
  have hTmeas : ∀ N, MeasurableSet (T N) := fun N =>
    MeasurableSet.biUnion (Set.to_countable _) fun l _ => measurableSet_confined m l (H l)
  have hTinter : ⋂ N, T N = ∅ := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false, not_forall, hT, Set.mem_iUnion,
      Set.mem_setOf_eq, exists_prop, not_exists, not_and]
    obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_notMem_confined m hH ω)
    exact ⟨N, fun l hl => hN l hl⟩
  have hlim : Tendsto (fun N => bondPercolation (zdGraph d) p (T N)) atTop (𝓝 0) := by
    have := tendsto_measure_iInter_atTop (μ := bondPercolation (zdGraph d) p)
      (fun N => (hTmeas N).nullMeasurableSet) hTanti ⟨0, measure_ne_top _ _⟩
    rwa [hTinter, measure_empty] at this
  have hlim' : Tendsto (fun N => (bondPercolation (zdGraph d) p).real (T N)) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim
    rwa [ENNReal.toReal_zero] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim'
    (Eventually.of_forall fun l => measureReal_nonneg) (Eventually.of_forall fun l => ?_)
  exact measureReal_mono
    (Set.subset_biUnion_of_mem (u := fun l => confined d m l (H l)) (show l ∈ {l' | l ≤ l'} from le_refl l))
    (measure_ne_top _ _)

/-- **`a_l → 0` for the fine-tuned bricks**: `P_p(b(0) ↔ ∞ in ℍ*, U + V < K) → 0` along
`h = H l → ∞` (`p < 1`). [cite: GrimmettPercolation1999, §7.3 p. 167 (a_l → 0)] -/
theorem tendsto_prob_centralSquarePercolates_inter_boundaryCountLT [NeZero d] (m K : ℕ) {H : ℕ → ℕ}
    (hH : Tendsto H atTop atTop) (p : unitInterval) (hp : (p : ℝ) < 1) :
    Tendsto (fun l => (bondPercolation (zdGraph d) p).real
      (centralSquarePercolates d m ∩ boundaryCountLT d m l (H l) K)) atTop (𝓝 0) := by
  set c : ℝ := (1 - (p : ℝ)) ^ (2 * d * (K - 1)) with hc
  have hcpos : 0 < c := pow_pos (by linarith) _
  have hbound : ∀ᶠ l in atTop,
      (bondPercolation (zdGraph d) p).real (centralSquarePercolates d m ∩ boundaryCountLT d m l (H l) K) ≤
        c⁻¹ * (bondPercolation (zdGraph d) p).real (confined d m l (H l)) := by
    filter_upwards [eventually_ge_atTop m, hH.eventually (eventually_ge_atTop 2)] with l hml hHl
    rw [le_inv_mul_iff₀ hcpos]
    exact prob_centralSquarePercolates_inter_boundaryCountLT_le hHl hml K p
  have hlim : Tendsto (fun l => c⁻¹ * (bondPercolation (zdGraph d) p).real (confined d m l (H l)))
      atTop (𝓝 0) := by
    simpa using (tendsto_prob_confined m hH p).const_mul c⁻¹
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun l => measureReal_nonneg) hbound

/-! ## The FKG step -/

/-- The linked vertices of the two facets `|x_a| = l` (`a` a horizontal axis): the set behind
`V^a` (`V ≤ Σ_a V^a`). [cite: GrimmettPercolation1999, §7.3 p. 167 (V(l,h))] -/
def facetLinked (d : ℕ) [NeZero d] (a : Fin d) (m l h : ℕ) (ω : BondConfig (Site d)) : Set (Site d) :=
  {x | x ∈ sideLinked d m l h ω ∧ |x a| = l}

/-- `V^a`'s set is finite. [folklore] -/
theorem facetLinked_finite [NeZero d] (a : Fin d) (m l h : ℕ) (ω : BondConfig (Site d)) :
    (facetLinked d a m l h ω).Finite :=
  (sideLinked_finite m l h ω).subset fun _ hx => hx.1

/-- The event `{V^a < M}`. [cite: GrimmettPercolation1999, §7.3 p. 167] -/
def facetCountLT (d : ℕ) [NeZero d] (a : Fin d) (m l h M : ℕ) : Set (BondConfig (Site d)) :=
  {ω | (facetLinked_finite a m l h ω).toFinset.card < M}

/-- The event `{U < N}` (fewer than `N` linked top vertices). [cite: GrimmettPercolation1999, §7.3 p. 167] -/
def topCountLT (d : ℕ) [NeZero d] (m l h N : ℕ) : Set (BondConfig (Site d)) :=
  {ω | (topLinked_finite m l h ω).toFinset.card < N}

/-- `{U < N}` is the complement of `{U ≥ N}`. [folklore] -/
theorem topCountLT_eq_compl [NeZero d] (m l h N : ℕ) : topCountLT d m l h N = (topCountGE d m l h N)ᶜ := by
  ext ω
  simp only [topCountLT, topCountGE, Set.mem_setOf_eq, Set.mem_compl_iff, not_le,
    (topLinked_finite m l h ω).encard_eq_coe_toFinset_card, Nat.cast_lt]

/-- `{x ∈ V^a-set}` is measurable. [folklore] -/
theorem measurableSet_mem_facetLinked [NeZero d] (a : Fin d) (m l h : ℕ) (x : Site d) :
    MeasurableSet {ω : BondConfig (Site d) | x ∈ facetLinked d a m l h ω} := by
  have : {ω : BondConfig (Site d) | x ∈ facetLinked d a m l h ω} =
      {ω | x ∈ sideLinked d m l h ω} ∩ {_ω | |x a| = l} := by
    ext ω; simp [facetLinked]
  rw [this]
  exact (measurableSet_mem_sideLinked m l h x).inter (MeasurableSet.const _)

/-- `{V^a < M}` is measurable. [folklore] -/
theorem measurableSet_facetCountLT [NeZero d] (a : Fin d) (m l h M : ℕ) :
    MeasurableSet (facetCountLT d a m l h M) := by
  have : facetCountLT d a m l h M = {ω | facetLinked d a m l h ω ∈ {S : Set (Site d) | S.ncard < M}} := by
    ext ω
    simp only [facetCountLT, Set.mem_setOf_eq, Set.ncard_eq_toFinset_card _ (facetLinked_finite a m l h ω)]
  rw [this]
  exact measurableSet_setStat (measurableSet_mem_facetLinked a m l h) (facetLinked_finite a m l h) _

/-- `{U < N}` is measurable. [folklore] -/
theorem measurableSet_topCountLT [NeZero d] (m l h N : ℕ) : MeasurableSet (topCountLT d m l h N) := by
  rw [topCountLT_eq_compl]
  exact (measurableSet_topCountGE m l h N).compl

/-- `{V^a < M}` is a decreasing event. [folklore] -/
theorem isLowerSet_facetCountLT [NeZero d] (a : Fin d) (m l h M : ℕ) : IsLowerSet (facetCountLT d a m l h M) := by
  intro ω ω' hle hω
  simp only [facetCountLT, Set.mem_setOf_eq] at hω ⊢
  refine lt_of_le_of_lt (Finset.card_le_card fun x hx => ?_) hω
  rw [Set.Finite.mem_toFinset] at hx ⊢
  exact ⟨⟨hx.1.1, hx.1.2.imp fun y hy => ⟨hy.1, openClusterIn_mono_config _ hle y hy.2⟩⟩, hx.2⟩

/-- `{U < N}` is a decreasing event. [folklore] -/
theorem isLowerSet_topCountLT [NeZero d] (m l h N : ℕ) : IsLowerSet (topCountLT d m l h N) := by
  intro ω ω' hle hω
  simp only [topCountLT, Set.mem_setOf_eq] at hω ⊢
  refine lt_of_le_of_lt (Finset.card_le_card fun x hx => ?_) hω
  rw [Set.Finite.mem_toFinset] at hx ⊢
  exact ⟨hx.1, hx.2.imp fun y hy => ⟨hy.1, openClusterIn_mono_config _ hle y hy.2⟩⟩

/-- The horizontal axes as a `Finset` of `Fin d`. [folklore] -/
def hAxes (d : ℕ) [NeZero d] : Finset (Fin d) := Finset.univ.filter fun a => a ≠ 0

/-- Membership in `hAxes`. [folklore] -/
@[simp] theorem mem_hAxes [NeZero d] {a : Fin d} : a ∈ hAxes d ↔ a ≠ 0 := by simp [hAxes]

/-- `U + V ≤ U + Σ_a V^a`: `{U < N} ∩ ⋂_a {V^a < M} ⊆ {U + V < N + |hAxes| M}`. [folklore] -/
theorem topCountLT_inter_facetCountLT_subset [NeZero d] (m l h N M : ℕ) :
    topCountLT d m l h N ∩ (⋂ a ∈ hAxes d, facetCountLT d a m l h M) ⊆
      boundaryCountLT d m l h (N + (hAxes d).card * M) := by
  classical
  rintro ω ⟨hU, hV⟩
  simp only [Set.mem_iInter] at hV
  simp only [topCountLT, facetCountLT, boundaryCountLT, Set.mem_setOf_eq] at hU hV ⊢
  have hcover : (boundaryLinked_finite m l h ω).toFinset ⊆ (topLinked_finite m l h ω).toFinset ∪
      (hAxes d).biUnion fun a => (facetLinked_finite a m l h ω).toFinset := by
    intro x hx
    simp only [Finset.mem_union, Set.Finite.mem_toFinset, Finset.mem_biUnion, mem_hAxes] at hx ⊢
    rw [boundaryLinked_eq_union] at hx
    rcases hx with hx | hx
    · exact Or.inl hx
    · obtain ⟨j, hj, hjl⟩ := hx.1.2
      exact Or.inr ⟨j, hj, hx, hjl⟩
  calc (boundaryLinked_finite m l h ω).toFinset.card
      ≤ ((topLinked_finite m l h ω).toFinset ∪
          (hAxes d).biUnion fun a => (facetLinked_finite a m l h ω).toFinset).card :=
        Finset.card_le_card hcover
    _ ≤ (topLinked_finite m l h ω).toFinset.card +
          ∑ a ∈ hAxes d, (facetLinked_finite a m l h ω).toFinset.card :=
        (Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_biUnion_le _)
    _ < N + (hAxes d).card * M := by
        refine add_lt_add_of_lt_of_le hU ?_
        calc ∑ a ∈ hAxes d, (facetLinked_finite a m l h ω).toFinset.card ≤ ∑ _a ∈ hAxes d, M :=
              Finset.sum_le_sum fun a ha => (hV a ha).le
          _ = (hAxes d).card * M := by rw [Finset.sum_const, smul_eq_mul]

/-- **The FKG step** (Grimmett 1999, p. 167: "It follows by the FKG inequality that
`P(U < N₂) P(V < M) ≤ P(U + V < M + N₂)`", here with the sides split into the `d - 1` facet
families): `P(U < N) · ∏_a P(V^a < M) ≤ P(U + V < N + (d-1)M)`, since all the events are
decreasing (`harris_fkg_lower`, `prob_biInter_ge_prod_of_isLowerSet`).
[cite: GrimmettPercolation1999, §7.3 p. 167 (FKG)] -/
theorem prob_mul_prod_le_boundaryCountLT [NeZero d] (m l h N M : ℕ) (p : unitInterval) :
    (bondPercolation (zdGraph d) p).real (topCountLT d m l h N) *
        ∏ a ∈ hAxes d, (bondPercolation (zdGraph d) p).real (facetCountLT d a m l h M) ≤
      (bondPercolation (zdGraph d) p).real (boundaryCountLT d m l h (N + (hAxes d).card * M)) := by
  have hI : IsLowerSet (⋂ a ∈ hAxes d, facetCountLT d a m l h M) :=
    isLowerSet_iInter₂ fun a _ => isLowerSet_facetCountLT a m l h M
  have hIm : MeasurableSet (⋂ a ∈ hAxes d, facetCountLT d a m l h M) :=
    MeasurableSet.biInter (Set.to_countable _) fun a _ => measurableSet_facetCountLT a m l h M
  have h1 := prob_biInter_ge_prod_of_isLowerSet (zdGraph d) p (hAxes d) (fun a => facetCountLT d a m l h M)
    (fun a _ => isLowerSet_facetCountLT a m l h M) (fun a _ => measurableSet_facetCountLT a m l h M)
  have h2 := harris_fkg_lower (zdGraph d) p (isLowerSet_topCountLT m l h N) hI
    (measurableSet_topCountLT m l h N) hIm
  calc _ ≤ (bondPercolation (zdGraph d) p).real (topCountLT d m l h N) *
        (bondPercolation (zdGraph d) p).real (⋂ a ∈ hAxes d, facetCountLT d a m l h M) :=
        mul_le_mul_of_nonneg_left h1 measureReal_nonneg
    _ ≤ (bondPercolation (zdGraph d) p).real (topCountLT d m l h N ∩ ⋂ a ∈ hAxes d, facetCountLT d a m l h M) := h2
    _ ≤ _ := measureReal_mono (topCountLT_inter_facetCountLT_subset m l h N M)

end BGNd

end Percolation.Literature

end
