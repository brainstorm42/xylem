import Percolation.Literature.HalfSpaceHighDimClean
import Percolation.Util.Linter

/-!
# Placed clean bricks in `ℤ^d`: supports, boxes and exits

The `ℤ^d` version of `PlacedBricks.lean`: the geometric
interface between the clean good events `goodC d m L H`, `topGoodC d m L H` of
`HalfSpaceHighDimClean.lean` (Grimmett, *Percolation*, 2nd ed. (1999), §7.3, the brick `B(L,H)` of
Lemma (7.36) with the seeds placed just outside its faces) and the block construction of Lemma (7.52)
(Grimmett pp. 169–176, "rotated translates of `B(L,H)`", (A) top stacking, (B) side stacking, (C)
"the intersection of a new brick with the region considered so far must be limited to a subset of
its underside"). proved here:

* `BGNd.Exitable`, `BGNd.linked_exitable` — a vertex of `T ∪ S` joined to `b(0)` in `B(L,H)*` is
  off the rim of the top, at height `≥ 1`, and on exactly one side face;
* `BGNd.dmid e = u + v` (the doubled midpoint of `e = {u,v}`) and the **support box**
  `stdBox L H = [1, 2H+2] × [-(2L+2), 2L+2]^{d-1}` with `dmid_mem_stdBox_of_mem_suppC`
  (`L ≥ m + 1`, `H ≥ 2m + 2`): the underside hyperplane (doubled height `0`) is excluded, so that a
  brick stacked on a clean seed examines edges disjoint from those of its parent;
* open squares are internally connected (`reachable_of_isSeed_square`);

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §7.3 pp. 163–176.
-/

noncomputable section

namespace Percolation.Literature

open _root_.MeasureTheory _root_.ProbabilityTheory LatticeModels unitInterval
open scoped _root_.ENNReal

namespace BGNd

variable {d : ℕ} [NeZero d] {m L H : ℕ}

/-! ## Exitable vertices -/

/-- A vertex of the top or sides through which `B(L,H)*`-paths from `b(0)` can leave: off the rim
of the top, and (on the sides) at height `≥ 1` and on exactly one side face. [folklore] -/
def Exitable (L H : ℕ) (x : Site d) : Prop :=
  (x 0 = H → ∀ j : Fin d, j ≠ 0 → |x j| < L) ∧
    (x 0 ≠ H → 1 ≤ x 0 ∧ ∀ j j' : Fin d, j ≠ 0 → j' ≠ 0 → |x j| = L → |x j'| = L → j = j')

/-- **Linked vertices of `T ∪ S` are exitable** (`H ≥ 1`, `m < L`): the last step of a
`B(L,H)*`-path into a boundary vertex comes from an interior vertex.
[cite: GrimmettPercolation1999, §7.3 p. 166] -/
theorem linked_exitable (hH : 1 ≤ H) (hmL : m < L) {x : Site d} (hx : x ∈ top d L H ∪ sides d L H)
    {ω : BondConfig (Site d)} (hl : Linked d m L H x ω) : Exitable L H x := by
  obtain ⟨y, hy, hxy⟩ := hl
  obtain ⟨hy0, hyj⟩ := mem_centralSquare_iff.1 hy
  set S : Set (Site d) := {z | (z 0 = H → ∀ j : Fin d, j ≠ 0 → |z j| < L) ∧
    ((∃ j : Fin d, j ≠ 0 ∧ |z j| = L) → z 0 ≠ H →
      1 ≤ z 0 ∧ ∀ j j' : Fin d, j ≠ 0 → j' ≠ 0 → |z j| = L → |z j'| = L → j = j')} with hS
  have hyS : y ∈ S := by
    refine ⟨fun h => by rw [hy0] at h; omega, fun h _ => ?_⟩
    exfalso
    obtain ⟨j, hj, hjl⟩ := h
    have := hyj j hj
    omega
  have hcl := BGN.openClusterIn_subset_of_closed (K := brickStar d L H) (ω := ω) (x := y) (S := S) hyS
    (fun u _ v huv => by
      rw [SimpleGraph.inf_adj] at huv
      obtain ⟨-, hzd, hu, hv, hB⟩ := huv
      rw [mem_brickBoundary_iff, mem_brickBoundary_iff] at hB
      rw [mem_brick] at hu hv
      -- if `v` is a boundary vertex then `u` is interior
      have hint : (v 0 = 0 ∨ v 0 = H ∨ ∃ j : Fin d, j ≠ 0 ∧ |v j| = L) →
          ¬(u 0 = 0 ∨ u 0 = H ∨ ∃ j : Fin d, j ≠ 0 ∧ |u j| = L) :=
        fun hvB huB => hB ⟨⟨mem_brick.2 hu, huB⟩, ⟨mem_brick.2 hv, hvB⟩⟩
      obtain ⟨i, hi⟩ := zdGraph_adj_cases' hzd
      -- coordinates of `v` in terms of `u`
      have hvi : ∀ j : Fin d, j ≠ i → v j = u j := by
        intro j hj
        rcases hi with rfl | rfl
        · exact add_unitVec_apply_of_ne u hj
        · exact sub_unitVec_apply_of_ne u hj
      refine ⟨fun hv0 j hj => ?_, fun hvs hv0 => ?_⟩
      · have huB := hint (Or.inr (Or.inl hv0))
        push Not at huB
        have hi0 : i = 0 := by
          by_contra hi0
          have := hvi 0 (Ne.symm hi0)
          exact huB.2.1 (this ▸ hv0)
        rw [hvi j (hi0 ▸ hj)]
        exact lt_of_le_of_ne (hu.2 j hj) (huB.2.2 j hj)
      · have huB := hint (Or.inr (Or.inr hvs))
        push Not at huB
        obtain ⟨j₀, hj₀, hj₀l⟩ := hvs
        -- the changed coordinate is `j₀`
        have hij : i = j₀ := by
          by_contra hij
          have := hvi j₀ (Ne.symm hij)
          exact huB.2.2 j₀ hj₀ (this ▸ hj₀l)
        refine ⟨?_, fun j j' hj hj' hjl hj'l => ?_⟩
        · have h00 : v 0 = u 0 := hvi 0 (by rw [hij]; exact Ne.symm hj₀)
          rw [h00]
          have := huB.1
          omega
        · have hj1 : j = i := by
            by_contra hne
            exact huB.2.2 j hj ((hvi j hne) ▸ hjl)
          have hj2 : j' = i := by
            by_contra hne
            exact huB.2.2 j' hj' ((hvi j' hne) ▸ hj'l)
          rw [hj1, hj2])
  have hxS := hcl hxy
  refine ⟨hxS.1, fun hx0 => hxS.2 ?_ hx0⟩
  rcases hx with hx | hx
  · exact absurd hx.2 hx0
  · exact hx.2

/-- Exitable vertices of `T ∪ S`: the possible exits. [folklore] -/
def exitSet (L H : ℕ) : Set (Site d) := {x | x ∈ top d L H ∪ sides d L H ∧ Exitable L H x}

/-- The top subfacets lie in `T ∪ S`. [folklore] -/
theorem topSubfacet_subset_top_union_sides (L H : ℕ) (ρ : HAxis d → Bool) :
    topSubfacet d L H ρ ⊆ top d L H ∪ sides d L H :=
  fun _ hx => Or.inl (topSubfacet_subset_top L H ρ hx)

/-- The side subfacets lie in `T ∪ S`. [folklore] -/
theorem sideSubfacet_subset_top_union_sides (L H : ℕ) (a : HAxis d) (τ : HAxis d → Bool) :
    sideSubfacet d L H a τ ⊆ top d L H ∪ sides d L H :=
  fun _ hx => Or.inr (sideSubfacet_subset_sides L H a τ hx)

/-! ## The support of `goodC` -/

/-- The edges `goodC m L H` depends on: the edges of `B(L,H)*` and the clean edges of the exitable
vertices. [cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
def suppC (d m L H : ℕ) [NeZero d] : Set (Sym2 (Site d)) :=
  (brickStar d L H).edgeSet ∪ ⋃ x ∈ exitSet (d := d) L H, (↑(cleanEdges d m L H x) : Set (Sym2 (Site d)))

/-- `Linked` only depends on the edges of `B(L,H)*`. [folklore] -/
theorem linked_iff_of_agree {ω ω' : BondConfig (Site d)} (h : ∀ e ∈ (brickStar d L H).edgeSet, e ∈ ω ↔ e ∈ ω')
    (x : Site d) : Linked d m L H x ω ↔ Linked d m L H x ω' := by
  have heq : ω ∩ (brickStar d L H).edgeSet = ω' ∩ (brickStar d L H).edgeSet := by
    ext e; constructor
    · rintro ⟨he, hK⟩; exact ⟨(h e hK).1 he, hK⟩
    · rintro ⟨he, hK⟩; exact ⟨(h e hK).2 he, hK⟩
  simp only [Linked, ← openClusterIn_inter_edgeSet (brickStar d L H) ω,
    ← openClusterIn_inter_edgeSet (brickStar d L H) ω', heq]

/-- The transfer of `okEventR F` (`F ⊆ T ∪ S`) between configurations agreeing on the support. [folklore] -/
theorem okEventR_of_agree (hH : 1 ≤ H) (hmL : m < L) {F : Set (Site d)} (hF : F ⊆ top d L H ∪ sides d L H)
    {ω ω' : BondConfig (Site d)} (hag : ω ∩ suppC d m L H = ω' ∩ suppC d m L H)
    (hω : ω ∈ okEventR d m L H (cleanEdges d m L H) F) : ω' ∈ okEventR d m L H (cleanEdges d m L H) F := by
  have hag' : ∀ e ∈ suppC d m L H, e ∈ ω ↔ e ∈ ω' := fun e he => by
    constructor
    · intro h; exact ((Set.ext_iff.1 hag e).1 ⟨h, he⟩).1
    · intro h; exact ((Set.ext_iff.1 hag e).2 ⟨h, he⟩).1
  obtain ⟨x, hxF, hl, ho⟩ := hω
  have hxe : x ∈ exitSet L H := ⟨hF hxF, linked_exitable hH hmL (hF hxF) hl⟩
  refine ⟨x, hxF, (linked_iff_of_agree (fun e he => hag' e (Or.inl he)) x).1 hl, fun e he => ?_⟩
  exact (hag' e (Or.inr (Set.mem_biUnion hxe he))).1 (ho he)

/-- **`goodC` is determined by its support** (`H ≥ 1`, `m < L`). [cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
theorem determinedBy_goodC (hH : 1 ≤ H) (hmL : m < L) : DeterminedBy (goodC d m L H) (suppC d m L H) := by
  rw [determinedBy_iff]
  have hT := topSubfacet_subset_top_union_sides (d := d) L H
  have hS := sideSubfacet_subset_top_union_sides (d := d) L H
  intro ω ω' hag
  simp only [goodC, goodR, Set.mem_inter_iff, Set.mem_iInter]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun ρ => okEventR_of_agree hH hmL (hT ρ) hag (h1 ρ), fun aτ => okEventR_of_agree hH hmL (hS aτ.1 aτ.2) hag (h2 aτ)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun ρ => okEventR_of_agree hH hmL (hT ρ) hag.symm (h1 ρ),
      fun aτ => okEventR_of_agree hH hmL (hS aτ.1 aτ.2) hag.symm (h2 aτ)⟩

/-! ## Doubled midpoints and the support box -/

omit [NeZero d] in
/-- The doubled midpoint `u + v` of the edge `{u, v}`. [folklore] -/
def dmid : Sym2 (Site d) → Site d := Sym2.lift ⟨fun u v => u + v, fun u v => add_comm u v⟩

omit [NeZero d] in
/-- `dmid {u,v} = u + v`. [folklore] -/
@[simp] theorem dmid_mk (u v : Site d) : dmid s(u, v) = u + v := rfl

/-- The support box of the standard brick in doubled coordinates:
`[1, 2H+2] × [-(2L+2), 2L+2]^{d-1}` (underside hyperplane excluded). [cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
def stdBox (L H : ℕ) : Set (Site d) :=
  {z | (1 ≤ z 0 ∧ z 0 ≤ 2 * (H : ℤ) + 2) ∧ ∀ j : Fin d, j ≠ 0 → |z j| ≤ 2 * (L : ℤ) + 2}

/-- Membership in the support box. [folklore] -/
@[simp] theorem mem_stdBox {z : Site d} :
    z ∈ stdBox L H ↔ (1 ≤ z 0 ∧ z 0 ≤ 2 * (H : ℤ) + 2) ∧ ∀ j : Fin d, j ≠ 0 → |z j| ≤ 2 * (L : ℤ) + 2 := Iff.rfl

/-- Edges of `B(L,H)*` have doubled midpoints in `[1, 2H-1] × [-(2L-1), 2L-1]^{d-1}`. [folklore] -/
theorem dmid_mem_of_mem_edgeSet_brickStar {e : Sym2 (Site d)} (he : e ∈ (brickStar d L H).edgeSet) :
    (1 ≤ dmid e 0 ∧ dmid e 0 ≤ 2 * (H : ℤ) - 1) ∧ ∀ j : Fin d, j ≠ 0 → |dmid e j| ≤ 2 * (L : ℤ) - 1 := by
  induction e using Sym2.ind with
  | _ u v =>
    rw [SimpleGraph.mem_edgeSet, brickStar, starGraph_adj] at he
    obtain ⟨hzd, hu, hv, hB⟩ := he
    rw [mem_brickBoundary_iff, mem_brickBoundary_iff] at hB
    rw [mem_brick] at hu hv
    have hB' : ¬((u 0 = 0 ∨ u 0 = H ∨ ∃ j : Fin d, j ≠ 0 ∧ |u j| = L) ∧
        (v 0 = 0 ∨ v 0 = H ∨ ∃ j : Fin d, j ≠ 0 ∧ |v j| = L)) :=
      fun h => hB ⟨⟨mem_brick.2 hu, h.1⟩, ⟨mem_brick.2 hv, h.2⟩⟩
    have h0 := zdGraph_adj_apply_zero hzd
    simp only [dmid_mk, Pi.add_apply]
    refine ⟨⟨?_, ?_⟩, fun j hj => ?_⟩
    · by_contra hlt
      exact hB' ⟨Or.inl (by omega), Or.inl (by omega)⟩
    · by_contra hlt
      exact hB' ⟨Or.inr (Or.inl (by omega)), Or.inr (Or.inl (by omega))⟩
    · have huj := abs_le.1 (hu.2 j hj)
      have hvj := abs_le.1 (hv.2 j hj)
      have hstep := abs_sub_le_one_of_adj hzd j
      rw [abs_le]
      by_contra hout
      have hcase : (u j = L ∧ v j = L) ∨ (u j = -(L : ℤ) ∧ v j = -(L : ℤ)) := by omega
      refine hB' ⟨Or.inr (Or.inr ⟨j, hj, ?_⟩), Or.inr (Or.inr ⟨j, hj, ?_⟩)⟩ <;>
        rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]

/-- Coordinate bounds of an exitable vertex (`H ≥ 1`). [folklore] -/
theorem exitSet_bounds (hH : 1 ≤ H) {x : Site d} (hx : x ∈ exitSet L H) :
    1 ≤ x 0 ∧ x 0 ≤ H ∧ (∀ j : Fin d, j ≠ 0 → |x j| ≤ L) ∧
      (x 0 = H → ∀ j : Fin d, j ≠ 0 → |x j| ≤ (L : ℤ) - 1) ∧
      (x 0 ≠ H → ∀ j : Fin d, j ≠ 0 → j ≠ seedAxis d L H x → |x j| ≤ (L : ℤ) - 1) := by
  obtain ⟨hxts, htop, hside⟩ := hx
  have hb := mem_brick.1 (mem_brick_of_mem_top_union_sides hxts)
  by_cases h0 : x 0 = H
  · refine ⟨by rw [h0]; exact_mod_cast hH, hb.1.2, hb.2, fun _ j hj => ?_, fun h => absurd h0 h⟩
    have := htop h0 j hj
    omega
  · obtain ⟨h1, huniq⟩ := hside h0
    have hs : ∃ j : Fin d, j ≠ 0 ∧ |x j| = L := by
      rcases hxts with h | h
      · exact absurd h.2 h0
      · exact h.2
    obtain ⟨hk, hkl⟩ := seedAxis_of_side (L := L) (H := H) h0 hs
    refine ⟨h1, hb.1.2, hb.2, fun h => absurd h h0, fun _ j hj hjk => ?_⟩
    have hne : |x j| ≠ L := fun h => hjk (huniq j _ hj hk h hkl)
    have := hb.2 j hj
    omega

/-- Coordinates of the doubled midpoint of the connecting edge. [folklore] -/
theorem dmid_cleanConn_apply (L H : ℕ) (x : Site d) (i : Fin d) :
    dmid (cleanConn d L H x) i = 2 * x i + (if i = seedAxis d L H x then normalSign d L H x else 0) := by
  rw [cleanConn, dmid_mk, Pi.add_apply, add_cleanNormal_apply]
  split_ifs <;> ring

/-- The clean edges of an exitable vertex have doubled midpoints in the support box
(`L ≥ m + 1`, `H ≥ 2m + 2`). [cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
theorem dmid_mem_stdBox_of_mem_cleanEdges (hL : m + 1 ≤ L) (hH : 2 * m + 2 ≤ H) {x : Site d} (hx : x ∈ exitSet L H)
    {e : Sym2 (Site d)} (he : e ∈ cleanEdges d m L H x) : dmid e ∈ stdBox L H := by
  obtain ⟨h1, h0H, hxj, htop, hside⟩ := exitSet_bounds (by omega) hx
  have hL1 : 1 ≤ L := by omega
  obtain ⟨hs, hcase⟩ := normalSign_spec hL1 hx.1
  rw [cleanEdges, Finset.mem_insert] at he
  rcases he with rfl | he
  · -- the connecting edge: `dmid = 2x + n e_k`
    have e := dmid_cleanConn_apply L H x
    rw [mem_stdBox, e 0]
    refine ⟨?_, fun j hj => ?_⟩
    · rcases hcase with ⟨hk, h0, hs1⟩ | ⟨hk, h0, -, -⟩
      · rw [if_pos hk.symm, h0, hs1]; constructor <;> omega
      · rw [if_neg (Ne.symm hk)]; constructor <;> omega
    · rw [e j]
      have := abs_le.1 (hxj j hj)
      rw [abs_le]
      split_ifs
      · rcases hs with h | h <;> rw [h] <;> constructor <;> omega
      · constructor <;> omega
  · -- an edge of the clean square: both endpoints within `m` of the centre
    rw [mem_sqEdges_iff] at he
    obtain ⟨u, hu, v, hv, -, rfl⟩ := he
    have hu' := fun i => abs_le.1 (abs_sub_le_of_mem_square hu i)
    have hv' := fun i => abs_le.1 (abs_sub_le_of_mem_square hv i)
    have hck : cleanCenter d m L H x (seedAxis d L H x) = x (seedAxis d L H x) + normalSign d L H x :=
      cleanCenter_apply_seedAxis m L H x
    have huk : u (seedAxis d L H x) = cleanCenter d m L H x (seedAxis d L H x) := (mem_square.1 hu).1
    have hvk : v (seedAxis d L H x) = cleanCenter d m L H x (seedAxis d L H x) := (mem_square.1 hv).1
    rw [dmid_mk, mem_stdBox]
    simp only [Pi.add_apply]
    rcases hcase with ⟨hk, h0, hs1⟩ | ⟨hk, h0, habs, hval⟩
    · -- top: the square lies in the hyperplane `H + 1`, transversally within `L - 1`
      rw [hk, h0, hs1] at hck
      rw [hk, hck] at huk hvk
      refine ⟨⟨by omega, by omega⟩, fun j hj => ?_⟩
      have huj := hu' j; have hvj := hv' j
      rw [cleanCenter_apply_of_ne m L H (by rw [hk]; exact hj) hj] at huj hvj
      have hc := BGN.clampZ_mem (lo := -((L : ℤ) - m - 1)) (hi := (L : ℤ) - m - 1) (by omega) (x j)
      rw [abs_le]; constructor <;> omega
    · have hu0 := hu' 0; have hv0 := hv' 0
      rw [cleanCenter_apply_zero_of_ne m L H hk] at hu0 hv0
      have hcH := BGN.clampZ_mem (lo := (m : ℤ) + 1) (hi := (H : ℤ) - m - 1) (by omega) (x 0)
      refine ⟨⟨by omega, by omega⟩, fun j hj => ?_⟩
      have huj := hu' j; have hvj := hv' j
      by_cases hjk : j = seedAxis d L H x
      · rw [hjk, huk, hvk, hck, hval]
        rcases hs with h | h <;> rw [h, abs_le] <;> constructor <;> omega
      · rw [cleanCenter_apply_of_ne m L H hjk hj] at huj hvj
        have hc := BGN.clampZ_mem (lo := -((L : ℤ) - m - 1)) (hi := (L : ℤ) - m - 1) (by omega) (x j)
        rw [abs_le]; constructor <;> omega

/-- **Every support edge of `goodC` has its doubled midpoint in the support box.**
[cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
theorem dmid_mem_stdBox_of_mem_suppC (hL : m + 1 ≤ L) (hH : 2 * m + 2 ≤ H) {e : Sym2 (Site d)}
    (he : e ∈ suppC d m L H) : dmid e ∈ stdBox L H := by
  rcases he with he | he
  · obtain ⟨⟨h1, h2⟩, h3⟩ := dmid_mem_of_mem_edgeSet_brickStar he
    exact ⟨⟨h1, by omega⟩, fun j hj => (h3 j hj).trans (by omega)⟩
  · rw [Set.mem_iUnion₂] at he
    obtain ⟨x, hx, he⟩ := he
    exact dmid_mem_stdBox_of_mem_cleanEdges hL hH hx he

/-- The support of `goodC` as a finite set of edges. [folklore] -/
def suppCF (d m L H : ℕ) [NeZero d] : Finset (Sym2 (Site d)) := by
  classical
  exact (sqEdges (brick d L H) (brick_finite L H)).filter (· ∈ (brickStar d L H).edgeSet) ∪
    ((box d (L + H + 0)).filter (· ∈ exitSet (d := d) L H)).biUnion (cleanEdges d m L H)

/-- `suppCF` and `suppC` are the same set of edges. [folklore] -/
theorem coe_suppCF (m L H : ℕ) : (↑(suppCF d m L H) : Set (Sym2 (Site d))) = suppC d m L H := by
  classical
  ext e
  simp only [suppCF, Finset.coe_union, Finset.coe_filter, Finset.coe_biUnion, Set.mem_union, Set.mem_setOf_eq,
    Set.mem_iUnion, Finset.mem_coe, suppC, exists_prop]
  constructor
  · rintro (⟨-, he⟩ | ⟨x, ⟨-, hx⟩, he⟩)
    · exact Or.inl he
    · exact Or.inr ⟨x, hx, he⟩
  · rintro (he | ⟨x, hx, he⟩)
    · refine Or.inl ⟨?_, he⟩
      induction e using Sym2.ind with
      | _ u v =>
        have h := he
        rw [SimpleGraph.mem_edgeSet, brickStar, starGraph_adj] at h
        exact mem_sqEdges_iff.2 ⟨u, h.2.1, v, h.2.2.1, h.1, rfl⟩
    · exact Or.inr ⟨x, ⟨brick_subset_box 0 L H (mem_brick_of_mem_top_union_sides hx.1), hx⟩, he⟩

/-! ## Placements -/

/-- A **placement** of the brick: the axis `a` and direction `s` of its height, and the centre `b`
of its underside (so that its entry square is `square a m b`). (Grimmett 1999, p. 170: "rotated
translates of `B(L,H)`".) [cite: GrimmettPercolation1999, §7.3 pp. 170, 173] -/
structure BrickPos (d : ℕ) where
  /-- the axis along which the brick's height runs -/
  a : Fin d
  /-- the direction of the height along that axis -/
  s : ℤˣ
  /-- the centre of the underside -/
  b : Site d
  deriving DecidableEq

namespace BrickPos

omit [NeZero d] in
/-- Placements form a countable type (they inject into `Fin d × ℤˣ × ℤ^d`). [folklore] -/
instance instCountable : Countable (BrickPos d) := by
  refine Function.Injective.countable (f := fun β : BrickPos d => (β.a, β.s, β.b)) ?_
  rintro ⟨a, s, b⟩ ⟨a', s', b'⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  rfl

variable (β : BrickPos d)

omit [NeZero d] in
/-- The signs of the canonical frame: `s` on the axis, `+1` elsewhere. [folklore] -/
def eps : Fin d → ℤˣ := Function.update 1 β.a β.s

/-- The coordinate permutation of the canonical frame: the transposition `(0 a)`. [folklore] -/
def perm : Equiv.Perm (Fin d) := Equiv.swap 0 β.a

/-- The linear part of the canonical frame. [folklore] -/
def lin : Site d ≃ Site d := Site.signedPerm β.perm β.eps

/-- **The canonical frame** of the placement: the lattice automorphism
`z ↦ signedPerm (0 a) ε z + b` carrying the standard brick onto the placed one.
[cite: GrimmettPercolation1999, §7.3 p. 170 (rotated translates)] -/
def frame : zdGraph d ≃g zdGraph d := (zdSignedPermIso β.perm β.eps).trans (zdShiftIso β.b)

/-- `frame z = lin z + b`. [folklore] -/
theorem frame_apply (z : Site d) : β.frame z = β.lin z + β.b := rfl

omit [NeZero d] in
/-- `eps a = s`. [folklore] -/
@[simp] theorem eps_self : β.eps β.a = β.s := by simp [eps]

omit [NeZero d] in
/-- `eps i = 1` off the axis. [folklore] -/
theorem eps_of_ne {i : Fin d} (hi : i ≠ β.a) : β.eps i = 1 := by simp [eps, hi]

/-- Coordinates of the linear part: `lin z i = eps i * z (swap 0 a i)`. [folklore] -/
theorem lin_apply (z : Site d) (i : Fin d) : β.lin z i = (β.eps i : ℤ) * z (Equiv.swap 0 β.a i) := by
  rw [lin, Site.signedPerm_apply, perm, Equiv.symm_swap]

/-- The axis coordinate: `lin z a = s * z 0`. [folklore] -/
theorem lin_apply_axis (z : Site d) : β.lin z β.a = (β.s : ℤ) * z 0 := by
  rw [lin_apply, eps_self, Equiv.swap_apply_right]

/-- Off-axis coordinates: `lin z i = z (swap 0 a i)` with `swap 0 a i ≠ 0`. [folklore] -/
theorem lin_apply_of_ne (z : Site d) {i : Fin d} (hi : i ≠ β.a) :
    β.lin z i = z (Equiv.swap 0 β.a i) ∧ Equiv.swap 0 β.a i ≠ 0 := by
  rw [lin_apply, eps_of_ne β hi, Units.val_one, one_mul]
  refine ⟨rfl, fun h => ?_⟩
  by_cases hi0 : i = 0
  · subst hi0; rw [Equiv.swap_apply_left] at h; exact hi h.symm
  · rw [Equiv.swap_apply_of_ne_of_ne hi0 hi] at h; exact hi0 h

/-- `lin` is additive. [folklore] -/
theorem lin_add (u v : Site d) : β.lin (u + v) = β.lin u + β.lin v := Site.signedPerm_add _ _ u v

/-- Doubled midpoints transform affinely: `dmid (frame e) = lin (dmid e) + 2b`. [folklore] -/
theorem dmid_sym2Equiv_frame (e : Sym2 (Site d)) :
    dmid (sym2Equiv β.frame.toEquiv e) = β.lin (dmid e) + (β.b + β.b) := by
  induction e using Sym2.ind with
  | _ u v =>
    rw [sym2Equiv_mk, dmid_mk, dmid_mk, lin_add]
    change (β.lin u + β.b) + (β.lin v + β.b) = _
    abel

/-- `perm 0 = a`. [folklore] -/
theorem perm_apply_zero : β.perm 0 = β.a := by
  rw [BrickPos.perm, Equiv.swap_apply_left]

/-- `frame 0 = b`. [folklore] -/
theorem frame_zero : β.frame 0 = β.b := by
  rw [β.frame_apply, BrickPos.lin, Site.signedPerm_zero, zero_add]

/-- The axis coordinate of the frame: `frame z a = b a + s z₀`. [folklore] -/
theorem frame_apply_axis (z : Site d) : β.frame z β.a = β.b β.a + (β.s : ℤ) * z 0 := by
  rw [β.frame_apply, Pi.add_apply, β.lin_apply_axis, add_comm]

/-- Off-axis frame coordinates: `frame z i = b i + z (swap 0 a i)` with `swap 0 a i ≠ 0`. [folklore] -/
theorem frame_apply_of_ne (z : Site d) {i : Fin d} (hi : i ≠ β.a) :
    β.frame z i = β.b i + z (Equiv.swap 0 β.a i) ∧ Equiv.swap 0 β.a i ≠ 0 := by
  obtain ⟨hl, hj⟩ := β.lin_apply_of_ne z hi
  exact ⟨by rw [β.frame_apply, Pi.add_apply, hl, add_comm], hj⟩

/-- The frame coordinate carrying the standard coordinate `k ≠ 0`:
`frame z (swap 0 a k) = b (swap 0 a k) + z k`. [folklore] -/
theorem frame_apply_swap (z : Site d) {k : Fin d} (hk : k ≠ 0) :
    β.frame z (Equiv.swap 0 β.a k) = β.b (Equiv.swap 0 β.a k) + z k ∧ Equiv.swap 0 β.a k ≠ β.a := by
  have hne : Equiv.swap 0 β.a k ≠ β.a := by
    intro h
    by_cases hak : β.a = k
    · rw [hak, Equiv.swap_apply_right] at h; exact hk h.symm
    · rw [Equiv.swap_apply_of_ne_of_ne hk (Ne.symm hak)] at h; exact hak h.symm
  refine ⟨?_, hne⟩
  rw [(β.frame_apply_of_ne z hne).1, Equiv.swap_apply_self]

end BrickPos

/-- **The support box of a placed brick** in doubled coordinates: along the axis
`1 ≤ s (w_a - 2 b_a) ≤ 2H + 2`, transversally `|w_i - 2 b_i| ≤ 2L + 2`.
[cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
def boxOf (L H : ℕ) (β : BrickPos d) : Set (Site d) :=
  {w | (1 ≤ (β.s : ℤ) * (w β.a - 2 * β.b β.a) ∧ (β.s : ℤ) * (w β.a - 2 * β.b β.a) ≤ 2 * (H : ℤ) + 2) ∧
    ∀ i, i ≠ β.a → |w i - 2 * β.b i| ≤ 2 * (L : ℤ) + 2}

omit [NeZero d] in
/-- Membership in the box of a placed brick. [folklore] -/
theorem mem_boxOf {β : BrickPos d} {w : Site d} :
    w ∈ boxOf L H β ↔ (1 ≤ (β.s : ℤ) * (w β.a - 2 * β.b β.a) ∧ (β.s : ℤ) * (w β.a - 2 * β.b β.a) ≤ 2 * (H : ℤ) + 2) ∧
      ∀ i, i ≠ β.a → |w i - 2 * β.b i| ≤ 2 * (L : ℤ) + 2 := Iff.rfl

/-- The frame carries the standard box into the box of the placement. [folklore] -/
theorem lin_add_mem_boxOf {β : BrickPos d} {z : Site d} (hz : z ∈ stdBox L H) : β.lin z + (β.b + β.b) ∈ boxOf L H β := by
  obtain ⟨⟨h0, h0'⟩, hj⟩ := mem_stdBox.1 hz
  rw [mem_boxOf]
  simp only [Pi.add_apply]
  refine ⟨?_, fun i hi => ?_⟩
  · rw [β.lin_apply_axis]
    have e : (β.s : ℤ) * ((β.s : ℤ) * z 0 + (β.b β.a + β.b β.a) - 2 * β.b β.a) = ((β.s : ℤ) * β.s) * z 0 := by ring
    rw [e, BGN.units_mul_self, one_mul]
    exact ⟨h0, h0'⟩
  · obtain ⟨hl, hj0⟩ := β.lin_apply_of_ne z hi
    rw [hl, show z (Equiv.swap 0 β.a i) + (β.b i + β.b i) - 2 * β.b i = z (Equiv.swap 0 β.a i) by ring]
    exact hj _ hj0

/-- **The placed clean good event**: the configuration seen from the brick's own frame is in
`goodC`. [cite: GrimmettPercolation1999, §7.3 p. 172 (A)] -/
def placedC (m L H : ℕ) (β : BrickPos d) : Set (BondConfig (Site d)) :=
  BondConfig.relabel (sym2Equiv β.frame.symm.toEquiv) ⁻¹' goodC d m L H

/-- **The placed clean top-good event** (for bricks used for top stacking only).
[cite: GrimmettPercolation1999, §7.3 p. 172 (A)] -/
def placedT (m L H : ℕ) (β : BrickPos d) : Set (BondConfig (Site d)) :=
  BondConfig.relabel (sym2Equiv β.frame.symm.toEquiv) ⁻¹' topGoodC d m L H

/-- `placedC ⊆ placedT`. [folklore] -/
theorem placedC_subset_placedT (m L H : ℕ) (β : BrickPos d) : placedC m L H β ⊆ placedT m L H β :=
  Set.preimage_mono (goodR_subset_topGoodR m L H _)

/-- Edges seen from the frame: `z ∈ (frame⁻¹ · ω) ↔ frame z ∈ ω`. [folklore] -/
theorem mem_relabel_frame_symm_iff (β : BrickPos d) (ω : BondConfig (Site d)) (z : Sym2 (Site d)) :
    z ∈ BondConfig.relabel (sym2Equiv β.frame.symm.toEquiv) ω ↔ sym2Equiv β.frame.toEquiv z ∈ ω := by
  rw [BondConfig.mem_relabel_iff, sym2Equiv_symm]
  rfl

/-- **`P_p` is invariant**: a placed brick is clean-good with the probability of the standard one.
[cite: GrimmettPercolation1999, §7.3 p. 172 (A) ("there is conditional probability π that … is good")] -/
theorem prob_placedC (m L H : ℕ) (β : BrickPos d) (p : unitInterval) :
    (bondPercolation (zdGraph d) p).real (placedC m L H β) = (bondPercolation (zdGraph d) p).real (goodC d m L H) :=
  bondPercolation_real_preimage_relabel_iso β.frame.symm p _

/-- The support of a placed brick: the image of `suppCF` under the frame. [folklore] -/
def suppP (m L H : ℕ) (β : BrickPos d) : Finset (Sym2 (Site d)) :=
  (suppCF d m L H).map (sym2Equiv β.frame.toEquiv).toEmbedding

omit [NeZero d] in
/-- Pulling back a determined event along a relabelling. [folklore] -/
theorem determinedBy_preimage_relabel_bond (e : Sym2 (Site d) ≃ Sym2 (Site d)) {A : Set (BondConfig (Site d))}
    {F : Set (Sym2 (Site d))} (hA : DeterminedBy A F) : DeterminedBy (BondConfig.relabel e ⁻¹' A) (e ⁻¹' F) := by
  rw [determinedBy_iff] at hA ⊢
  intro ω ω' h
  simp only [Set.mem_preimage]
  apply hA
  ext z
  simp only [Set.mem_inter_iff, BondConfig.relabel_apply, Set.mem_image]
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, hz⟩
    have : y ∈ ω' ∩ e ⁻¹' F := by rw [← h]; exact ⟨hy, hz⟩
    exact ⟨⟨y, this.1, rfl⟩, hz⟩
  · rintro ⟨⟨y, hy, rfl⟩, hz⟩
    have : y ∈ ω ∩ e ⁻¹' F := by rw [h]; exact ⟨hy, hz⟩
    exact ⟨⟨y, this.1, rfl⟩, hz⟩

/-- Transport of a support statement along the frame. [folklore] -/
theorem determinedBy_preimage_frame_suppP {A : Set (BondConfig (Site d))} (hA : DeterminedBy A (suppC d m L H))
    (β : BrickPos d) : DeterminedBy (BondConfig.relabel (sym2Equiv β.frame.symm.toEquiv) ⁻¹' A) ↑(suppP m L H β) := by
  have h := determinedBy_preimage_relabel_bond (sym2Equiv β.frame.symm.toEquiv) hA
  refine h.mono fun z hz => ?_
  rw [Set.mem_preimage, ← coe_suppCF] at hz
  rw [suppP, Finset.coe_map, Equiv.coe_toEmbedding]
  refine ⟨_, hz, ?_⟩
  change sym2Equiv β.frame.toEquiv ((sym2Equiv β.frame.toEquiv).symm z) = z
  exact Equiv.apply_symm_apply _ _

/-- **A placed brick's event is determined by its support.** [cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
theorem determinedBy_placedC_suppP (hH : 1 ≤ H) (hmL : m < L) (β : BrickPos d) :
    DeterminedBy (placedC m L H β) ↑(suppP m L H β) :=
  determinedBy_preimage_frame_suppP (determinedBy_goodC hH hmL) β

/-- **Every support edge of a placed brick has its doubled midpoint in the brick's box**
(`L ≥ m + 1`, `H ≥ 2m + 2`). [cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
theorem dmid_mem_boxOf_of_mem_suppP (hL : m + 1 ≤ L) (hH : 2 * m + 2 ≤ H) (β : BrickPos d) {z : Sym2 (Site d)}
    (hz : z ∈ suppP m L H β) : dmid z ∈ boxOf L H β := by
  rw [suppP, Finset.mem_map] at hz
  obtain ⟨e, he, rfl⟩ := hz
  rw [Equiv.coe_toEmbedding, β.dmid_sym2Equiv_frame]
  refine lin_add_mem_boxOf (dmid_mem_stdBox_of_mem_suppC hL hH ?_)
  rw [← coe_suppCF]; exact he

/-- **Disjoint boxes give disjoint supports.** [cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
theorem disjoint_suppP_of_disjoint_boxOf (hL : m + 1 ≤ L) (hH : 2 * m + 2 ≤ H) {L' H' : ℕ} (hL' : m + 1 ≤ L')
    (hH' : 2 * m + 2 ≤ H') {β β' : BrickPos d} (h : Disjoint (boxOf L H β) (boxOf L' H' β')) :
    Disjoint (suppP m L H β) (suppP m L' H' β') := by
  rw [Finset.disjoint_left]
  intro z hz hz'
  exact Set.disjoint_left.1 h (dmid_mem_boxOf_of_mem_suppP hL hH β hz) (dmid_mem_boxOf_of_mem_suppP hL' hH' β' hz')

/-- The placed event is measurable. [folklore] -/
theorem measurableSet_placedC (hH : 1 ≤ H) (hmL : m < L) (β : BrickPos d) : MeasurableSet (placedC m L H β) :=
  measurableSet_of_isLocalEvent_holds ⟨_, determinedBy_placedC_suppP hH hmL β⟩

/-! ## Open squares are connected -/

omit [NeZero d] in
/-- One lattice step inside an open square is an open edge. [folklore] -/
theorem reachable_step_of_isSeed {ω : BondConfig (Site d)} {Q : Set (Site d)} (hQ : IsSeed ω Q) {w : Site d} (j : Fin d)
    (hw : w ∈ Q) (hw' : w + Pi.single j 1 ∈ Q) : (openGraph ω).Reachable w (w + Pi.single j 1) := by
  have hadj : (zdGraph d).Adj w (w + Pi.single j 1) := (zdGraph_adj_iff _ _).2 ⟨j, Or.inl rfl⟩
  refine SimpleGraph.Adj.reachable ?_
  rw [openGraph_adj]
  exact ⟨hQ hw hw' hadj, hadj.ne⟩

omit [NeZero d] in
/-- Moving `n` steps along an in-plane axis inside an open square. [folklore] -/
theorem reachable_line_of_isSeed {ω : BondConfig (Site d)} {k : Fin d} {m : ℕ} {c : Site d} (hQ : IsSeed ω (square k m c))
    {j : Fin d} (hj : j ≠ k) : ∀ (n : ℕ) (w : Site d), w ∈ square k m c → w + (n : ℤ) • (Pi.single j 1 : Site d) ∈ square k m c →
      (openGraph ω).Reachable w (w + (n : ℤ) • (Pi.single j 1 : Site d))
  | 0, w, _, _ => by simp
  | n + 1, w, hw, hw' => by
    have hmid : w + (n : ℤ) • (Pi.single j 1 : Site d) ∈ square k m c := by
      rw [mem_square] at hw hw' ⊢
      refine ⟨?_, fun i hi => ?_⟩
      · simp only [Pi.add_apply, Pi.smul_apply, Pi.single_apply, if_neg (Ne.symm hj), smul_zero, add_zero]; exact hw.1
      · by_cases hij : i = j
        · subst hij
          have h1 := abs_le.1 (hw.2 i hi); have h2 := abs_le.1 (hw'.2 i hi)
          simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, Nat.cast_succ] at h2 ⊢
          rw [abs_le]; constructor <;> linarith
        · have := hw.2 i hi
          simpa [Pi.single_apply, hij] using this
    have heq : w + ((n + 1 : ℕ) : ℤ) • (Pi.single j 1 : Site d) = (w + (n : ℤ) • (Pi.single j 1 : Site d)) + Pi.single j 1 := by
      simp only [Nat.cast_succ, add_smul, one_smul, add_assoc]
    have h1 := reachable_line_of_isSeed hQ hj n w hw hmid
    have h2 := reachable_step_of_isSeed hQ j hmid (by rw [← heq]; exact hw')
    rw [heq]
    exact h1.trans h2

omit [NeZero d] in
/-- Moving by any integer displacement along an in-plane axis inside an open square. [folklore] -/
theorem reachable_zline_of_isSeed {ω : BondConfig (Site d)} {k : Fin d} {m : ℕ} {c : Site d} (hQ : IsSeed ω (square k m c))
    {j : Fin d} (hj : j ≠ k) (t : ℤ) {w : Site d} (hw : w ∈ square k m c) (hw' : w + t • (Pi.single j 1 : Site d) ∈ square k m c) :
    (openGraph ω).Reachable w (w + t • (Pi.single j 1 : Site d)) := by
  rcases le_or_gt 0 t with ht | ht
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le ht
    exact reachable_line_of_isSeed hQ hj n w hw hw'
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ -t by omega)
    have h := reachable_line_of_isSeed hQ hj n (w + t • (Pi.single j 1 : Site d)) hw' (by
      rw [← hn, add_assoc, ← add_smul, add_neg_cancel, zero_smul, add_zero]; exact hw)
    rw [← hn, add_assoc, ← add_smul, add_neg_cancel, zero_smul, add_zero] at h
    exact h.symm

omit [NeZero d] in
/-- **An open square is internally connected**: all its vertices are joined by open paths
(adjusting the in-plane coordinates one at a time, by induction on a list of axes).
[cite: GrimmettPercolation1999, §7.3 p. 163 (seed)] -/
theorem reachable_of_isSeed_square {ω : BondConfig (Site d)} {k : Fin d} {m : ℕ} {c : Site d} (hQ : IsSeed ω (square k m c))
    {u v : Site d} (hu : u ∈ square k m c) (hv : v ∈ square k m c) : (openGraph ω).Reachable u v := by
  classical
  -- adjust the coordinates in a finite set `s` of axes: reach the point agreeing with `v` on `s`
  suffices h : ∀ s : Finset (Fin d), k ∉ s →
      (fun i => if i ∈ s then v i else u i) ∈ square k m c ∧ (openGraph ω).Reachable u (fun i => if i ∈ s then v i else u i) by
    obtain ⟨-, hreach⟩ := h (Finset.univ.erase k) (Finset.notMem_erase k _)
    have hv' : (fun i => if i ∈ Finset.univ.erase k then v i else u i) = v := by
      funext i
      by_cases hi : i = k
      · subst hi; simp only [Finset.mem_erase, ne_eq, not_true_eq_false, false_and, ↓reduceIte]
        rw [(mem_square.1 hu).1, (mem_square.1 hv).1]
      · simp [hi]
    rwa [hv'] at hreach
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro _
    have : (fun i => if i ∈ (∅ : Finset (Fin d)) then v i else u i) = u := by funext i; simp
    rw [this]
    exact ⟨hu, SimpleGraph.Reachable.refl u⟩
  | insert j s hj ih =>
    intro hk
    rw [Finset.mem_insert, not_or] at hk
    obtain ⟨hmem, hreach⟩ := ih hk.2
    set w : Site d := fun i => if i ∈ s then v i else u i with hw
    have hwj : w j = u j := by simp [hw, hj]
    set w' : Site d := fun i => if i ∈ insert j s then v i else u i with hw'
    have hw'eq : w' = w + (v j - u j) • (Pi.single j 1 : Site d) := by
      funext i
      simp only [hw', hw, Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, Finset.mem_insert]
      by_cases hij : i = j
      · subst hij; simp [hj]
      · simp [hij]
    have hw'mem : w' ∈ square k m c := by
      rw [mem_square] at hu hv ⊢
      refine ⟨?_, fun i hi => ?_⟩
      · simp only [hw', Finset.mem_insert]
        rw [if_neg (by push Not; exact hk)]; exact hu.1
      · simp only [hw']
        split_ifs
        · exact hv.2 i hi
        · exact hu.2 i hi
    refine ⟨hw'mem, hreach.trans ?_⟩
    have := reachable_zline_of_isSeed hQ (fun h => hk.1 h.symm) (v j - u j) hmem (by rw [← hw'eq]; exact hw'mem)
    rwa [← hw'eq] at this

/-! ## Transport along the frame -/

omit [NeZero d] in
/-- Open paths seen from the frame are open paths: reachability in `frame⁻¹·ω` transports to `ω`.
[folklore] -/
theorem reachable_of_reachable_relabel_symm (φ : zdGraph d ≃g zdGraph d) {ω : BondConfig (Site d)} {x y : Site d}
    (h : (openGraph (BondConfig.relabel (sym2Equiv φ.symm.toEquiv) ω)).Reachable x y) :
    (openGraph ω).Reachable (φ x) (φ y) := by
  let ψ : openGraph ω ≃g openGraph (BondConfig.relabel (sym2Equiv φ.symm.toEquiv) ω) :=
    { toEquiv := φ.symm.toEquiv
      map_rel_iff' := fun {a b} => openGraph_relabel_adj_iff φ.symm.toEquiv ω a b }
  exact (SimpleGraph.Iso.reachable_iff (φ := ψ.symm)).2 h

omit [NeZero d] in
/-- An image set all of whose lattice edges are open (seen from the frame) is a seed. [folklore] -/
theorem isSeed_image_of_forall (φ : zdGraph d ≃g zdGraph d) {ω : BondConfig (Site d)} {Q : Set (Site d)}
    (h : ∀ u ∈ Q, ∀ v ∈ Q, (zdGraph d).Adj u v → s(φ u, φ v) ∈ ω) : IsSeed ω (φ '' Q) := by
  rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ hadj
  exact h u hu v hv (φ.map_rel_iff'.1 hadj)

omit [NeZero d] in
/-- Translates of squares. [folklore] -/
theorem image_add_square (k : Fin d) (m : ℕ) (c b : Site d) : (fun z => z + b) '' square k m c = square k m (c + b) := by
  ext y
  simp only [Set.mem_image, mem_square, Pi.add_apply]
  constructor
  · rintro ⟨z, ⟨hz1, hz2⟩, rfl⟩
    refine ⟨by simp [hz1], fun j hj => ?_⟩
    rw [Pi.add_apply, show z j + b j - (c j + b j) = z j - c j by ring]; exact hz2 j hj
  · rintro ⟨hy1, hy2⟩
    refine ⟨y - b, ⟨by simp [hy1], fun j hj => ?_⟩, by simp⟩
    rw [Pi.sub_apply, show y j - b j - c j = y j - (c j + b j) by ring]; exact hy2 j hj

/-- **The frame carries squares to squares**: `frame '' (c + b_k(m)) = frame c + b_{perm k}(m)`. [folklore] -/
theorem BrickPos.image_frame_square (β : BrickPos d) (k : Fin d) (m : ℕ) (c : Site d) :
    β.frame '' square k m c = square (β.perm k) m (β.frame c) := by
  have h1 : β.frame '' square k m c = (fun z => z + β.b) '' (β.lin '' square k m c) := by
    rw [Set.image_image]; rfl
  rw [h1, BrickPos.lin, image_square_signedPerm, image_add_square]
  rfl

/-- The entry square of a placement is the image of `b(0)`. [folklore] -/
theorem BrickPos.image_frame_centralSquare (β : BrickPos d) (m : ℕ) : β.frame '' centralSquare d m = square β.a m β.b := by
  rw [centralSquare, β.image_frame_square, β.perm_apply_zero, β.frame_zero]

/-! ## Exits -/

/-- For an exitable vertex the neighbour `x + n` across the face lies in the clean square
(`L ≥ m + 1`, `H ≥ 2m + 2`). [folklore] -/
theorem add_cleanNormal_mem_cleanSquare (hL : m + 1 ≤ L) (hH : 2 * m + 2 ≤ H) {x : Site d} (hx : x ∈ exitSet L H) :
    x + cleanNormal d L H x ∈ cleanSquare d m L H x := by
  obtain ⟨h1, h0H, hxj, htop, hside⟩ := exitSet_bounds (by omega) hx
  have hL1 : 1 ≤ L := by omega
  obtain ⟨hs, hcase⟩ := normalSign_spec hL1 hx.1
  rw [cleanSquare, mem_square]
  refine ⟨by rw [add_cleanNormal_apply, if_pos rfl, cleanCenter_apply_seedAxis], fun j hj => ?_⟩
  rw [add_cleanNormal_apply, if_neg hj]
  by_cases hj0 : j = 0
  · subst hj0
    rw [cleanCenter_apply_zero_of_ne m L H (Ne.symm hj), abs_sub_comm]
    rcases hcase with ⟨hk, -, -⟩ | ⟨hk, h0, -, -⟩
    · exact absurd hk.symm hj
    · exact BGN.abs_clampZ_sub_le (by omega) (by positivity) (by omega) (by omega)
  · rw [cleanCenter_apply_of_ne m L H hj hj0, abs_sub_comm]
    have hxj' : |x j| ≤ (L : ℤ) - 1 := by
      rcases hcase with ⟨hk, h0, -⟩ | ⟨hk, h0, -, -⟩
      · exact htop h0 j hj0
      · exact hside h0 j hj0 hj
    have := abs_le.1 hxj'
    exact BGN.abs_clampZ_sub_le (by omega) (by positivity) (by omega) (by omega)

/-- **The exit through a subfacet.** On a placed event containing `okEventR F` (`F ⊆ T ∪ S`) in
the brick's frame, there is an exitable `x ∈ F` whose clean square, placed by the frame, is an
open seed square `square (perm k) m (frame c)` joined to the entry square of `β` by an open path.
[cite: GrimmettPercolation1999, §7.3 p. 172 (A)–(B)] -/
theorem exists_exit_of_okEventR' (hL : m + 1 ≤ L) (hH : 2 * m + 2 ≤ H) {β : BrickPos d} {ω : BondConfig (Site d)}
    {F : Set (Site d)} (hF : F ⊆ top d L H ∪ sides d L H)
    (hok : BondConfig.relabel (sym2Equiv β.frame.symm.toEquiv) ω ∈ okEventR d m L H (cleanEdges d m L H) F) :
    ∃ x ∈ F, x ∈ exitSet L H ∧
      IsSeed ω (square (β.perm (seedAxis d L H x)) m (β.frame (cleanCenter d m L H x))) ∧
      ∃ y ∈ square β.a m β.b, (openGraph ω).Reachable y (β.frame (cleanCenter d m L H x)) := by
  obtain ⟨x, hxF, hl, ho⟩ := hok
  have hxe : x ∈ exitSet L H := ⟨hF hxF, linked_exitable (by omega) (by omega) (hF hxF) hl⟩
  obtain ⟨y, hy, hxy⟩ := hl
  have hyx : (openGraph ω).Reachable (β.frame y) (β.frame x) :=
    reachable_of_reachable_relabel_symm β.frame (openClusterIn_subset_openCluster _ _ _ hxy)
  have hfy : β.frame y ∈ square β.a m β.b := by
    rw [← β.image_frame_centralSquare m]; exact ⟨y, hy, rfl⟩
  have hopen : ∀ e ∈ cleanEdges d m L H x, sym2Equiv β.frame.toEquiv e ∈ ω := fun e he =>
    (mem_relabel_frame_symm_iff β ω e).1 (ho (Finset.mem_coe.2 he))
  have hsq : IsSeed ω (square (β.perm (seedAxis d L H x)) m (β.frame (cleanCenter d m L H x))) := by
    rw [← β.image_frame_square]
    refine isSeed_image_of_forall β.frame fun u hu v hv hadj => ?_
    have := hopen _ (Finset.mem_insert_of_mem (mem_sqEdges_iff.2 ⟨u, hu, v, hv, hadj, rfl⟩))
    rwa [sym2Equiv_mk] at this
  have hconn : (openGraph ω).Reachable (β.frame x) (β.frame (x + cleanNormal d L H x)) := by
    have he := hopen _ (Finset.mem_insert_self _ _)
    rw [cleanConn, sym2Equiv_mk] at he
    refine SimpleGraph.Adj.reachable ?_
    rw [openGraph_adj]
    exact ⟨he, (β.frame.map_rel_iff'.2 (adj_add_cleanNormal (by omega) (hF hxF))).ne⟩
  have hin : (openGraph ω).Reachable (β.frame (x + cleanNormal d L H x)) (β.frame (cleanCenter d m L H x)) := by
    refine reachable_of_isSeed_square hsq ?_ ?_
    · rw [← β.image_frame_square]; exact ⟨_, add_cleanNormal_mem_cleanSquare hL hH hxe, rfl⟩
    · rw [← β.image_frame_square]; exact ⟨_, self_mem_square _ _ _, rfl⟩
  exact ⟨x, hxF, hxe, hsq, β.frame y, hfy, hyx.trans (hconn.trans hin)⟩

/-- The `HAxis` version of `swap 0 a i` for `i ≠ a`. [folklore] -/
def BrickPos.std (β : BrickPos d) (i : Fin d) (hi : i ≠ β.a) : HAxis d :=
  ⟨Equiv.swap 0 β.a i, (β.lin_apply_of_ne 0 hi).2⟩

/-- **Top stacking** (Grimmett 1999, p. 172 (A)). On the placed top-good event, for every requested
sign pattern `sg` there is an open seed square `square a m b'` one level beyond the top
(`b'_a = b_a + s(H+1)`), transversally within `L - m - 1` of `b` with offsets of the requested
signs, joined to the entry square by an open path. [cite: GrimmettPercolation1999, §7.3 p. 172 (A)] -/
theorem exists_top_exit' (hL : m + 1 ≤ L) (hH : 2 * m + 2 ≤ H) {β : BrickPos d} {ω : BondConfig (Site d)}
    (hgood : ω ∈ placedT m L H β) (sg : Fin d → Bool) :
    ∃ b' : Site d, b' β.a = β.b β.a + (β.s : ℤ) * ((H : ℤ) + 1) ∧
      (∀ i, i ≠ β.a → |b' i - β.b i| ≤ (L : ℤ) - m - 1 ∧
        (sg i = true → 0 ≤ b' i - β.b i) ∧ (sg i = false → b' i - β.b i ≤ 0)) ∧
      IsSeed ω (square β.a m b') ∧ ∃ y ∈ square β.a m β.b, (openGraph ω).Reachable y b' := by
  -- the standard top subfacet realising `sg`: `ρ j = sg (swap 0 a j)`
  set ρ : HAxis d → Bool := fun j => sg (Equiv.swap 0 β.a j.1) with hρ
  have hok := (Set.mem_iInter.1 hgood) ρ
  obtain ⟨x, hxF, hxe, hsq, hreach⟩ := exists_exit_of_okEventR' hL hH (topSubfacet_subset_top_union_sides L H ρ) hok
  obtain ⟨hx0, hxρ⟩ := hxF
  have hk : seedAxis d L H x = 0 := seedAxis_of_top hx0
  have hs : normalSign d L H x = 1 := by simp [normalSign, hx0]
  rw [hk, β.perm_apply_zero] at hsq
  refine ⟨β.frame (cleanCenter d m L H x), ?_, fun i hi => ?_, hsq, hreach⟩
  · rw [β.frame_apply_axis]
    have : cleanCenter d m L H x 0 = x 0 + normalSign d L H x := by
      have := cleanCenter_apply_seedAxis m L H x; rwa [hk] at this
    rw [this, hx0, hs]
  · obtain ⟨hfi, hsw⟩ := β.frame_apply_of_ne (cleanCenter d m L H x) hi
    rw [hfi, add_sub_cancel_left, cleanCenter_apply_of_ne m L H (by rw [hk]; exact hsw) hsw]
    have hmem := BGN.clampZ_mem (lo := -((L : ℤ) - m - 1)) (hi := (L : ℤ) - m - 1) (by omega) (x (Equiv.swap 0 β.a i))
    have hsign := BGN.clampZ_nonneg_iff (a := (L : ℤ) - m - 1) (by omega) (x (Equiv.swap 0 β.a i))
    have hρi : ρ (β.std i hi) = sg i := by
      simp only [hρ, BrickPos.std, Equiv.swap_apply_self]
    have hrange := hxρ (β.std i hi)
    rw [hρi] at hrange
    change HalfRange L (sg i) (x (Equiv.swap 0 β.a i)) at hrange
    refine ⟨abs_le.2 ⟨by linarith [hmem.1], hmem.2⟩, fun h1 => hsign.1 ?_, fun h2 => hsign.2 ?_⟩
    · rw [h1] at hrange; simp only [HalfRange, ↓reduceIte] at hrange; exact hrange.1
    · rw [h2] at hrange; simp only [HalfRange, Bool.false_eq_true, ↓reduceIte] at hrange; exact hrange.2

/-- **Side stacking** (Grimmett 1999, pp. 172–173 (B)). On the placed good event, for every
transverse global axis `i ≠ a`, outward sign `u` and requested sign pattern `sg` of the remaining
coordinates, there is an open seed square orthogonal to `i`, one step outside the face
(`b'_i = b_i + u(L+1)`), at longitudinal position `s(b'_a - b_a) ∈ [m+1, H-m-1]`, with the other
offsets of size `≤ L-m-1` and of the requested signs, joined to the entry square by an open path.
[cite: GrimmettPercolation1999, §7.3 pp. 172–173 (B)] -/
theorem exists_side_exit' (hL : m + 1 ≤ L) (hH : 2 * m + 2 ≤ H) {β : BrickPos d} {ω : BondConfig (Site d)}
    (hgood : ω ∈ placedC m L H β) {i : Fin d} (hi : i ≠ β.a) (u : ℤˣ) (sg : Fin d → Bool) :
    ∃ b' : Site d, b' i = β.b i + (u : ℤ) * ((L : ℤ) + 1) ∧
      ((m : ℤ) + 1 ≤ (β.s : ℤ) * (b' β.a - β.b β.a) ∧ (β.s : ℤ) * (b' β.a - β.b β.a) ≤ (H : ℤ) - m - 1) ∧
      (∀ j, j ≠ β.a → j ≠ i → |b' j - β.b j| ≤ (L : ℤ) - m - 1 ∧
        (sg j = true → 0 ≤ b' j - β.b j) ∧ (sg j = false → b' j - β.b j ≤ 0)) ∧
      IsSeed ω (square i m b') ∧ ∃ y ∈ square β.a m β.b, (openGraph ω).Reachable y b' := by
  have hL0 : (0 : ℤ) < L := by exact_mod_cast (show 0 < L by omega)
  -- the standard side subfacet realising the request
  set a' : HAxis d := β.std i hi with ha'
  set τ : HAxis d → Bool := fun j => if j = a' then decide (u = 1) else sg (Equiv.swap 0 β.a j.1) with hτ
  have hok := (Set.mem_iInter.1 hgood.2) (a', τ)
  obtain ⟨x, hxF, hxe, hsq, hreach⟩ := exists_exit_of_okEventR' hL hH (sideSubfacet_subset_top_union_sides L H a' τ) hok
  obtain ⟨hx0, hface, hother⟩ := hxF
  obtain ⟨h1, h0H, hxj, htop, hside⟩ := exitSet_bounds (by omega) hxe
  -- `x a' = u L`, `x ∉ T`, the seed axis is `a'`, the sign is `u`
  have hxa : x a'.1 = (u : ℤ) * L := by
    rw [hface]
    simp only [hτ, ↓reduceIte]
    rcases Int.units_eq_one_or u with rfl | rfl
    · simp
    · simp
  have habs : |x a'.1| = L := by rw [hxa, BGN.abs_units_mul]; simp
  have hxn0 : x 0 ≠ H := by
    intro h0
    have := htop h0 a'.1 a'.2
    omega
  have hk : seedAxis d L H x = a'.1 :=
    seedAxis_eq_of_unique hxn0 a'.2 habs fun j hj hjl => (hxe.2.2 hxn0).2 j a'.1 hj a'.2 hjl habs
  have hs : normalSign d L H x = (u : ℤ) := by
    simp only [normalSign, hxn0, ↓reduceIte, hk, hxa, BGN.sign_units_mul, Int.sign_eq_one_of_pos hL0, mul_one]
  have ha'val : a'.1 = Equiv.swap 0 β.a i := rfl
  have hperm : β.perm (seedAxis d L H x) = i := by
    rw [hk, ha'val, BrickPos.perm, Equiv.swap_apply_self]
  rw [hperm] at hsq
  refine ⟨β.frame (cleanCenter d m L H x), ?_, ?_, fun j hja hji => ?_, hsq, hreach⟩
  · have := (β.frame_apply_swap (cleanCenter d m L H x) a'.2).1
    rw [ha'val, Equiv.swap_apply_self] at this
    rw [this, ← ha'val, ← hk, cleanCenter_apply_seedAxis, hk, hs, hxa]; ring
  · rw [β.frame_apply_axis, add_sub_cancel_left, ← mul_assoc, BGN.units_mul_self, one_mul,
      cleanCenter_apply_zero_of_ne m L H (by rw [hk]; exact a'.2)]
    exact BGN.clampZ_mem (lo := (m : ℤ) + 1) (hi := (H : ℤ) - m - 1) (by omega) (x 0)
  · obtain ⟨hfj, hsw⟩ := β.frame_apply_of_ne (cleanCenter d m L H x) hja
    have hne : Equiv.swap 0 β.a j ≠ a'.1 := by
      rw [ha'val]; intro h; exact hji ((Equiv.swap 0 β.a).injective h)
    rw [hfj, add_sub_cancel_left, cleanCenter_apply_of_ne m L H (by rw [hk]; exact hne) hsw]
    have hmem := BGN.clampZ_mem (lo := -((L : ℤ) - m - 1)) (hi := (L : ℤ) - m - 1) (by omega) (x (Equiv.swap 0 β.a j))
    have hsign := BGN.clampZ_nonneg_iff (a := (L : ℤ) - m - 1) (by omega) (x (Equiv.swap 0 β.a j))
    have hstd : β.std j hja ≠ a' := fun h => hne (congrArg Subtype.val h)
    have hτj : τ (β.std j hja) = sg j := by
      rw [hτ]
      dsimp only
      rw [if_neg hstd]
      simp only [BrickPos.std, Equiv.swap_apply_self]
    have hrange := hother (β.std j hja) hstd
    rw [hτj] at hrange
    change HalfRange L (sg j) (x (Equiv.swap 0 β.a j)) at hrange
    refine ⟨abs_le.2 ⟨by linarith [hmem.1], hmem.2⟩, fun ht => hsign.1 ?_, fun hf => hsign.2 ?_⟩
    · rw [ht] at hrange; simp only [HalfRange, ↓reduceIte] at hrange; exact hrange.1
    · rw [hf] at hrange; simp only [HalfRange, Bool.false_eq_true, ↓reduceIte] at hrange; exact hrange.2

end BGNd

end Percolation.Literature

end
