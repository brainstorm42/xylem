import Percolation.Literature.TallZone
import Percolation.Util.Linter

/-!
# The tall gait, XV: the initial structure

The initial open set `U₀` of the block construction
(Grimmett, *Percolation*, 2nd ed. (1999), §7.3 p. 171: "we begin by finding a suitably large open
cluster near the origin"): four seed squares at the four exit ports of the origin cell, joined to the
origin by lattice paths (three straight segments each: up to the layer, sideways to the lane, forward
to the port). We define straight segments of edges (`segEdges`) with their basic properties (lattice
edges; open segments connect their ends; doubled midpoints), the initial ports `initPos`, the initial
tokens, `U₀`, and prove: `U₀` consists of lattice edges, and when `U₀` is open the initial seeds are
open and joined to the origin.

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §7.3 pp. 170–171.
-/

noncomputable section

namespace Percolation.Literature

open LatticeModels Contour
open scoped Classical

namespace BGNd

variable {d : ℕ} [NeZero d]

/-! ## Straight segments -/

/-- The point `x + t e_i`. [folklore] -/
def shift (x : Site d) (i : Fin d) (t : ℤ) : Site d := x + Pi.single i t

omit [NeZero d] in
/-- Auxiliary fact `shift_apply_self`. [folklore] -/
@[simp] theorem shift_apply_self (x : Site d) (i : Fin d) (t : ℤ) : shift x i t i = x i + t := by
  simp [shift]

omit [NeZero d] in
/-- Auxiliary fact `shift_apply_of_ne`. [folklore] -/
theorem shift_apply_of_ne (x : Site d) {i j : Fin d} (h : j ≠ i) (t : ℤ) : shift x i t j = x j := by
  simp [shift, Pi.single_eq_of_ne h]

omit [NeZero d] in
/-- Auxiliary fact `shift_zero`. [folklore] -/
@[simp] theorem shift_zero (x : Site d) (i : Fin d) : shift x i 0 = x := by
  ext j; by_cases h : j = i
  · subst h; simp
  · rw [shift_apply_of_ne x h]

omit [NeZero d] in
/-- Auxiliary fact `shift_add_one`. [folklore] -/
theorem shift_add_one (x : Site d) (i : Fin d) (t : ℤ) : shift x i (t + 1) = shift x i t + Pi.single i 1 := by
  ext j; by_cases h : j = i
  · subst h; simp [shift]; ring
  · simp [shift, Pi.single_eq_of_ne h]

omit [NeZero d] in
/-- Consecutive points of a segment are adjacent. [folklore] -/
theorem adj_shift_succ (x : Site d) (i : Fin d) (t : ℤ) : (zdGraph d).Adj (shift x i t) (shift x i (t + 1)) := by
  rw [zdGraph_adj_iff]; exact ⟨i, Or.inl (shift_add_one x i t)⟩

/-- **The edges of the straight segment** from `x` to `x + σ n e_i` (`σ = ±1` according to `pos`). [folklore] -/
def segEdges (x : Site d) (i : Fin d) (n : ℕ) (pos : Bool) : Finset (Sym2 (Site d)) :=
  (Finset.range n).image fun k : ℕ =>
    if pos then s(shift x i (k : ℤ), shift x i ((k : ℤ) + 1)) else s(shift x i (-(k : ℤ) - 1), shift x i (-(k : ℤ)))

omit [NeZero d] in
/-- Segment edges are lattice edges. [folklore] -/
theorem segEdges_subset_edgeSet (x : Site d) (i : Fin d) (n : ℕ) (pos : Bool) :
    (↑(segEdges x i n pos) : Set (Sym2 (Site d))) ⊆ (zdGraph d).edgeSet := by
  intro z hz
  rw [Finset.mem_coe, segEdges, Finset.mem_image] at hz
  obtain ⟨k, -, rfl⟩ := hz
  split_ifs
  · exact (SimpleGraph.mem_edgeSet _).2 (adj_shift_succ x i k)
  · rw [SimpleGraph.mem_edgeSet]
    have := adj_shift_succ x i (-(k : ℤ) - 1)
    rwa [sub_add_cancel] at this

omit [NeZero d] in
/-- **An open segment joins its ends.** [folklore] -/
theorem reachable_of_segEdges_subset {ω : BondConfig (Site d)} {x : Site d} {i : Fin d} {n : ℕ} {pos : Bool}
    (h : (↑(segEdges x i n pos) : Set (Sym2 (Site d))) ⊆ ω) :
    (openGraph ω).Reachable x (shift x i (if pos then (n : ℤ) else -(n : ℤ))) := by
  induction n with
  | zero => cases pos <;> simp
  | succ n ih =>
    have hsub : (↑(segEdges x i n pos) : Set (Sym2 (Site d))) ⊆ ω := by
      intro z hz; apply h
      rw [Finset.mem_coe, segEdges, Finset.mem_image] at hz ⊢
      obtain ⟨k, hk, rfl⟩ := hz
      exact ⟨k, Finset.mem_range.2 (by have := Finset.mem_range.1 hk; omega), rfl⟩
    have hlast : (if pos then s(shift x i n, shift x i (n + 1)) else s(shift x i (-(n : ℤ) - 1), shift x i (-(n : ℤ)))) ∈ ω := by
      apply h; rw [Finset.mem_coe, segEdges, Finset.mem_image]
      exact ⟨n, Finset.mem_range.2 (Nat.lt_succ_self n), rfl⟩
    refine (ih hsub).trans ?_
    cases pos
    · simp only [Bool.false_eq_true, ↓reduceIte] at hlast ⊢
      refine SimpleGraph.Adj.reachable ?_
      rw [openGraph_adj]
      have hadj := adj_shift_succ x i (-(n : ℤ) - 1)
      rw [sub_add_cancel] at hadj
      push_cast
      rw [show -((n : ℤ) + 1) = -(n : ℤ) - 1 by ring]
      exact ⟨by rw [Sym2.eq_swap]; exact hlast, hadj.symm.ne⟩
    · simp only [↓reduceIte] at hlast ⊢
      refine SimpleGraph.Adj.reachable ?_
      rw [openGraph_adj]
      push_cast
      exact ⟨hlast, (adj_shift_succ x i n).ne⟩

omit [NeZero d] in
/-- The doubled midpoints of segment edges: on the segment's line, strictly between the ends (doubled). [folklore] -/
theorem dmid_of_mem_segEdges {x : Site d} {i : Fin d} {n : ℕ} {pos : Bool} {z : Sym2 (Site d)} (hz : z ∈ segEdges x i n pos) :
    (∀ j, j ≠ i → dmid z j = 2 * x j) ∧ 1 ≤ (if pos then (1 : ℤ) else -1) * (dmid z i - 2 * x i) ∧
      (if pos then (1 : ℤ) else -1) * (dmid z i - 2 * x i) ≤ 2 * n - 1 := by
  rw [segEdges, Finset.mem_image] at hz
  obtain ⟨k, hk, rfl⟩ := hz
  have hk' := Finset.mem_range.1 hk
  cases pos
  · simp only [Bool.false_eq_true, ↓reduceIte, dmid_mk, Pi.add_apply]
    refine ⟨fun j hj => by rw [shift_apply_of_ne x hj, shift_apply_of_ne x hj]; ring, ?_, ?_⟩ <;>
      rw [shift_apply_self, shift_apply_self] <;> nlinarith
  · simp only [↓reduceIte, dmid_mk, Pi.add_apply]
    refine ⟨fun j hj => by rw [shift_apply_of_ne x hj, shift_apply_of_ne x hj]; ring, ?_, ?_⟩ <;>
      rw [shift_apply_self, shift_apply_self] <;> nlinarith

/-! ## Open squares -/

/-- The edges of the square `b_k(m)` at `c`. [folklore] -/
def sqEdgesAt (k : Fin d) (m : ℕ) (c : Site d) : Finset (Sym2 (Site d)) := sqEdges (square k m c) (square_finite k m c)

omit [NeZero d] in
/-- If the edges of a square are open, the square is a seed. [folklore] -/
theorem isSeed_of_sqEdgesAt_subset {ω : BondConfig (Site d)} {k : Fin d} {m : ℕ} {c : Site d}
    (h : (↑(sqEdgesAt k m c) : Set (Sym2 (Site d))) ⊆ ω) : IsSeed ω (square k m c) := by
  intro u hu v hv hadj
  apply h
  rw [Finset.mem_coe, sqEdgesAt, mem_sqEdges_iff]
  exact ⟨u, hu, v, hv, hadj, rfl⟩

omit [NeZero d] in
/-- Square edges are lattice edges. [folklore] -/
theorem sqEdgesAt_subset_edgeSet (k : Fin d) (m : ℕ) (c : Site d) :
    (↑(sqEdgesAt k m c) : Set (Sym2 (Site d))) ⊆ (zdGraph d).edgeSet := by
  intro z hz
  rw [Finset.mem_coe, sqEdgesAt, mem_sqEdges_iff] at hz
  obtain ⟨u, -, v, -, hadj, rfl⟩ := hz
  exact (SimpleGraph.mem_edgeSet _).2 hadj

omit [NeZero d] in
/-- The doubled midpoints of square edges: in the square's plane, within `2m` of twice the centre. [folklore] -/
theorem dmid_of_mem_sqEdgesAt {k : Fin d} {m : ℕ} {c : Site d} {z : Sym2 (Site d)} (hz : z ∈ sqEdgesAt k m c) :
    dmid z k = 2 * c k ∧ ∀ j, j ≠ k → |dmid z j - 2 * c j| ≤ 2 * m := by
  rw [sqEdgesAt, mem_sqEdges_iff] at hz
  obtain ⟨u, hu, v, hv, -, rfl⟩ := hz
  rw [mem_square] at hu hv
  rw [dmid_mk]
  refine ⟨by rw [Pi.add_apply, hu.1, hv.1]; ring, fun j hj => ?_⟩
  have h1 := abs_le.1 (hu.2 j hj); have h2 := abs_le.1 (hv.2 j hj)
  rw [Pi.add_apply, abs_le]; constructor <;> linarith

/-! ## The initial ports and `U₀` -/

section Init

variable (Y : TallLayout) (hd : 3 ≤ d)

/-- **The initial port** of the origin cell towards `e`: forward at `s (D/2 - ℓ)`, on the lane of `e`,
at the height of the layer of `e`. [cite: GrimmettPercolation1999, §7.3 p. 171] -/
def initPos (e : MDir) : Site d := fun i =>
  if i = axOf hd e then (sgOf e : ℤ) * (Y.Dh - Y.ell) else if i = latOf hd e then Y.lane 0 e else if i = ax0 hd then Y.zOf (rev e) else 0

/-- The initial token towards `e`: at the port of the origin cell, on the layer of `rev e`, with the
nominal provenance `rev e` ("as if it had arrived from behind"; the kit reports no provenance for it,
see `TallKitDef`). This keeps the initial entry legs off the layers used inside the origin cell by
attempts aimed at it. [folklore] -/
def initTok (e : MDir) : TTok d := ⟨initPos Y hd e, axOf hd e, some (rev e)⟩

/-- The corner points of the initial path towards `e`: above the origin, and on the lane. [folklore] -/
def initP1 (e : MDir) : Site d := shift 0 (ax0 hd) (Y.zOf (rev e))
/-- The second corner. [folklore] -/
def initP2 (e : MDir) : Site d := shift (initP1 Y hd e) (latOf hd e) (Y.lane 0 e)

/-- The edges of the initial path towards `e`: up, sideways, forward. [folklore] -/
def initPath (e : MDir) : Finset (Sym2 (Site d)) :=
  segEdges 0 (ax0 hd) (Y.zOf (rev e)).toNat true ∪
    segEdges (initP1 Y hd e) (latOf hd e) (Y.lane 0 e).natAbs (decide (0 ≤ Y.lane 0 e)) ∪
    segEdges (initP2 Y hd e) (axOf hd e) (Y.Dh - Y.ell).toNat e.2

/-- **The initial open set `U₀`**: the four initial seed squares and the four paths. [cite: GrimmettPercolation1999, §7.3 p. 171] -/
def U0 : Finset (Sym2 (Site d)) :=
  Finset.univ.biUnion fun e : MDir => sqEdgesAt (axOf hd e) Y.m (initPos Y hd e) ∪ initPath Y hd e

omit [NeZero d] in
/-- `U₀` consists of lattice edges. [folklore] -/
theorem U0_subset_edgeSet : (↑(U0 Y hd) : Set (Sym2 (Site d))) ⊆ (zdGraph d).edgeSet := by
  intro z hz
  rw [Finset.mem_coe, U0, Finset.mem_biUnion] at hz
  obtain ⟨e, -, hz⟩ := hz
  rw [Finset.mem_union] at hz
  rcases hz with hz | hz
  · exact sqEdgesAt_subset_edgeSet _ _ _ hz
  · rw [initPath, Finset.mem_union, Finset.mem_union] at hz
    rcases hz with (hz | hz) | hz <;> exact segEdges_subset_edgeSet _ _ _ _ hz

omit [NeZero d] in
/-- The end of the initial path is the initial port (the layers and `D/2 - ℓ` being nonnegative). [folklore] -/
theorem initPath_end (hY : Y.OK) (e : MDir) :
    shift (initP2 Y hd e) (axOf hd e) (if e.2 then (((Y.Dh - Y.ell).toNat : ℕ) : ℤ) else -(((Y.Dh - Y.ell).toNat : ℕ) : ℤ)) =
      initPos Y hd e := by
  obtain ⟨-, -, -, hell, hmH, -, -, -, -, -, -, -, -, hWl, hDh, -, hPe, hP2, hP3, -, -, hP64, -⟩ := hY.facts
  have hD : 0 ≤ Y.Dh - Y.ell := by linarith only [hDh, hP3, hP2, hPe, hP64, hell, hmH]
  rw [Int.toNat_of_nonneg hD]
  ext j
  unfold initPos initP2 initP1
  by_cases h1 : j = axOf hd e
  · subst h1
    rw [shift_apply_self, shift_apply_of_ne _ (latOf_ne_axOf hd e).symm, shift_apply_of_ne _ (axOf_ne_ax0 hd e), if_pos rfl]
    simp only [Pi.zero_apply, zero_add]
    unfold sgOf; cases e.2 <;> simp
  by_cases h2 : j = latOf hd e
  · subst h2
    rw [shift_apply_of_ne _ (latOf_ne_axOf hd e), shift_apply_self, shift_apply_of_ne _ (latOf_ne_ax0 hd e), if_neg h1, if_pos rfl]
    simp
  by_cases h3 : j = ax0 hd
  · subst h3
    rw [shift_apply_of_ne _ (axOf_ne_ax0 hd e).symm, shift_apply_of_ne _ (latOf_ne_ax0 hd e).symm, shift_apply_self, if_neg h1,
      if_neg h2, if_pos rfl]
    simp
  · rw [shift_apply_of_ne _ h1, shift_apply_of_ne _ h2, shift_apply_of_ne _ h3, if_neg h1, if_neg h2, if_neg h3]; simp

omit [NeZero d] in
/-- **When `U₀` is open, the initial seeds are open and joined to the origin.** [cite: GrimmettPercolation1999, §7.3 p. 171] -/
theorem init_conn (hY : Y.OK) {ω : BondConfig (Site d)} (hω : (↑(U0 Y hd) : Set (Sym2 (Site d))) ⊆ ω) (e : MDir) :
    IsSeed ω (square (axOf hd e) Y.m (initPos Y hd e)) ∧ (openGraph ω).Reachable 0 (initPos Y hd e) := by
  have hsub : ∀ z, z ∈ sqEdgesAt (axOf hd e) Y.m (initPos Y hd e) ∪ initPath Y hd e → z ∈ ω := fun z hz =>
    hω (by rw [Finset.mem_coe, U0, Finset.mem_biUnion]; exact ⟨e, Finset.mem_univ _, hz⟩)
  refine ⟨isSeed_of_sqEdgesAt_subset fun z hz => hsub z (Finset.mem_union_left _ hz), ?_⟩
  have h1 : (openGraph ω).Reachable 0 (initP1 Y hd e) := by
    have := reachable_of_segEdges_subset (ω := ω) (x := (0 : Site d)) (i := ax0 hd) (n := (Y.zOf (rev e)).toNat) (pos := true)
      fun z hz => hsub z (by rw [initPath]; exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_union_left _ hz)))
    simp only [↓reduceIte] at this
    have hz0 : 0 ≤ Y.zOf (rev e) := by
      unfold TallLayout.zOf
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hWl, -⟩ := hY.facts
      have : 0 ≤ Y.Wl := by rw [hWl]; positivity
      positivity
    rwa [Int.toNat_of_nonneg hz0] at this
  have h2 : (openGraph ω).Reachable (initP1 Y hd e) (initP2 Y hd e) := by
    have := reachable_of_segEdges_subset (ω := ω) (x := initP1 Y hd e) (i := latOf hd e) (n := (Y.lane 0 e).natAbs)
      (pos := decide (0 ≤ Y.lane 0 e))
      fun z hz => hsub z (by rw [initPath]; exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_union_right _ hz)))
    unfold initP2
    by_cases h : 0 ≤ Y.lane 0 e
    · simp only [h, decide_true, ↓reduceIte] at this
      rwa [Int.natAbs_of_nonneg h] at this
    · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte] at this
      push Not at h
      rwa [Int.ofNat_natAbs_of_nonpos h.le, neg_neg] at this
  have h3 : (openGraph ω).Reachable (initP2 Y hd e) (initPos Y hd e) := by
    have := reachable_of_segEdges_subset (ω := ω) (x := initP2 Y hd e) (i := axOf hd e) (n := (Y.Dh - Y.ell).toNat) (pos := e.2)
      fun z hz => hsub z (by rw [initPath]; exact Finset.mem_union_right _ (Finset.mem_union_right _ hz))
    rwa [initPath_end Y hd hY e] at this
  exact h1.trans (h2.trans h3)

end Init

end BGNd

end Percolation.Literature

end
