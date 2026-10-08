import Percolation.Literature.LatticeSymmetry
import Percolation.Literature.PlanarDuality
import Percolation.Util.Linter

/-!
# The region below the lowest crossing: conditioning without conditioning

Infrastructure for the Russo–Seymour–Welsh step
(Bollobás–Riordan, *Percolation* (2006), Ch. 3, Lemma 4; Grimmett, *Percolation* (1999),
Lemma 11.73; Kesten, *Percolation theory for mathematicians* (1982), Prop. 2.3), which
conditions on the *lowest* (or left-most) open crossing of a square. We replace the lowest open
left-right crossing of `S = [0, j] × [0, j]` by the random set of faces lying below it:

* `dualBelow j ω`: the faces of the dual rectangle `S* = [½, j - ½] × [-½, j + ½]` (indexed by
  lower-left corners, `dualRectangle j j`) joined to its bottom side by a dual-open path of `S*`
  (dual-open = crossing a closed primal edge, `dualConfig`). By planar duality
  (`lrCrossing_xor_dualTBCrossing_holds`), `S` has an open left-right crossing iff
  `dualBelow j ω` contains no top face (`not_mem_dualBelow_of_lrCrossing`).
* `squareEdges g`, `belowEdges D₀`: the four primal edges bounding the face `g`, and their
  union over `g ∈ D₀`. The event `{dualBelow j ω = D₀}` is determined by the states of the edges
  in `belowEdges D₀` (`determinedBy_dualBelow_eq`): "the event `{LV(S) = P₁}` does not depend on
  the states of bonds of `S` to the right of `P₁`" (Bollobás–Riordan, proof of Lemma 4).
* `IsBdryEdge D₀ j e`: `e` separates a face of `D₀` from a face of `S* \ D₀`. On
  `{dualBelow j ω = D₀}` every such edge is open (`mem_of_isBdryEdge`), and if the bottom side of
  `S*` lies in `D₀` and the top side avoids it, the boundary edges contain a left-right crossing
  of `S` (`exists_bdryWalk`, from the parity lemma `exists_topReach_dualBottomSide` of
  `PlanarDuality.lean` transposed and dualised): this walk *is* the lowest open crossing, obtained
  here without ordering crossings.

Mathlib anchors: `SimpleGraph.Walk` (`map`, `darts`, `support`), `Finset.biUnion`,
`Finset.filter`; tree anchors: `dualEdge`, `dualConfig`, `dualRectangle`, `dualEdgeEquiv`,
`dualConfig_eq` (`Crossings.lean`), `sepLo`, `sepHi`, `dualEdge_sepEdge`, `Bichromatic`,
`bichromaticGraph`, `exists_topReach_dualBottomSide`, `exists_walk_of_mem_openConnIn`,
`determinedBy_iff` users (`PlanarDuality.lean`), `transposeIso` (`LatticeSymmetry.lean`).

## References
* B. Bollobás, O. Riordan, *Percolation*, CUP (2006), Ch. 3, Lemma 1 (remark on the top-most
  crossing) and Lemma 4 [BollobasRiordanPercolation2006].
* H. Kesten, *Percolation theory for mathematicians*, Birkhäuser (1982), §2.3, Prop. 2.3
  [KestenPTM1982].
* G. Grimmett, *Percolation*, 2nd ed., Springer (1999), Lemma 11.73 [GrimmettPercolation1999].
-/

namespace Percolation.Literature

open SimpleGraph Finset

noncomputable section

/-! ### The parity lemma, transposed: bottom coloured, top uncoloured -/

section TransposedParity

/-- The transposition as a graph homomorphism `bichromaticGraph (c ∘ T) n m →g ℤ²`. [folklore] -/
def transposeBichromaticHom (c : LatticeModels.Site 2 → Prop) (m n : ℕ) :
    bichromaticGraph (fun z => c (transposeIso z)) n m →g LatticeModels.zdGraph 2 where
  toFun z := transposeIso z
  map_rel' h := transposeIso.map_adj_iff.2 h.1

/-- Transposition commutes with `sepLo`. [folklore] -/
theorem transposeIso_sepLo (z z' : LatticeModels.Site 2) :
    transposeIso (sepLo z z') = sepLo (transposeIso z) (transposeIso z') := by
  rw [LatticeModels.Site.eq_iff_two]
  simp [sepLo]

/-- Transposition commutes with `sepHi` on adjacent faces. [folklore] -/
theorem transposeIso_sepHi {z z' : LatticeModels.Site 2} (h : (LatticeModels.zdGraph 2).Adj z z') :
    transposeIso (sepHi z z') = sepHi (transposeIso z) (transposeIso z') := by
  have hxor : z 0 = z' 0 ↔ ¬ z 1 = z' 1 := by
    rcases stepKind_of_adj h with ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h1, h0⟩ | ⟨h1, h0⟩ <;> omega
  rw [LatticeModels.Site.eq_iff_two]
  simp only [sepHi, transposeIso_apply_zero, transposeIso_apply_one, Pi.add_apply, Pi.sup_apply]
  by_cases h0 : z 0 = z' 0
  · have h1 : ¬ z 1 = z' 1 := hxor.1 h0
    simp [h0, h1]
  · have h1 : z 1 = z' 1 := by tauto
    simp [h0, h1]

/-- Transposition carries `Bichromatic (c ∘ T) n m` steps to `Bichromatic c m n` steps. [folklore] -/
theorem Bichromatic.transpose {c : LatticeModels.Site 2 → Prop} {m n : ℕ} {z z' : LatticeModels.Site 2}
    (hadj : (LatticeModels.zdGraph 2).Adj z z') (h : Bichromatic (fun z => c (transposeIso z)) n m z z') :
    Bichromatic c m n (transposeIso z) (transposeIso z') := by
  obtain ⟨hlo, hhi, hc⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [← transposeIso_sepLo, ← Finset.mem_coe, ← Set.mem_preimage, preimage_transpose_rectangle,
      Finset.mem_coe]
    exact hlo
  · rw [← transposeIso_sepHi hadj, ← Finset.mem_coe, ← Set.mem_preimage,
      preimage_transpose_rectangle, Finset.mem_coe]
    exact hhi
  · rwa [← transposeIso_sepLo, ← transposeIso_sepHi hadj]

/-- The vertices of a walk in `bichromaticGraph c m n` starting in the dual rectangle lie in the
dual rectangle. [folklore] -/
theorem support_subset_dualRectangle_of_walk {c : LatticeModels.Site 2 → Prop} {m n : ℕ} {t v : LatticeModels.Site 2}
    (W : (bichromaticGraph c m n).Walk t v) (ht : t ∈ dualRectangle m n) :
    ∀ w ∈ W.support, w ∈ dualRectangle m n := by
  induction W with
  | nil => intro w hw; rw [Walk.support_nil, List.mem_singleton] at hw; rw [hw]; exact ht
  | cons hadj W' ih =>
    intro w hw
    rw [Walk.support_cons, List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact ht
    · exact ih hadj.2.2.1 w hw

/-- **The parity lemma, transposed.** If the bottom side of `[0, m] × [0, n]` is coloured and the
top side is not, then there is a walk of faces of the vertical dual `[-1, m] × [0, n - 1]`
(lower-left corners) from a face of its right column to a face of its left column, each step of
which crosses a bichromatic edge of the rectangle. (`exists_topReach_dualBottomSide` for the
transposed colouring.) [folklore] -/
theorem exists_faceWalk_of_bottom_top (c : LatticeModels.Site 2 → Prop) (m n : ℕ)
    (hB : ∀ x ∈ bottomSide m n, c x) (hT : ∀ x ∈ topSide m n, ¬c x) :
    ∃ u v : LatticeModels.Site 2, u 0 = m ∧ v 0 = -1 ∧ ∃ q : (LatticeModels.zdGraph 2).Walk u v,
      (∀ z ∈ q.support, -1 ≤ z 0 ∧ z 0 ≤ m ∧ 0 ≤ z 1 ∧ z 1 + 1 ≤ n) ∧
      ∀ d ∈ q.darts, Bichromatic c m n d.fst d.snd := by
  have hL : ∀ x ∈ leftSide n m, (fun z => c (transposeIso z)) x := by
    intro x hx
    apply hB
    simp only [leftSide, bottomSide, Finset.mem_filter, mem_rectangle_iff,
      transposeIso_apply_zero, transposeIso_apply_one] at hx ⊢
    omega
  have hR : ∀ x ∈ rightSide n m, ¬(fun z => c (transposeIso z)) x := by
    intro x hx
    apply hT
    simp only [rightSide, topSide, Finset.mem_filter, mem_rectangle_iff,
      transposeIso_apply_zero, transposeIso_apply_one] at hx ⊢
    omega
  obtain ⟨v, hv, t, ht, ⟨W⟩⟩ := exists_topReach_dualBottomSide hL hR
  have htD : t ∈ dualRectangle n m := (Finset.mem_filter.1 ht).1
  refine ⟨transposeBichromaticHom c m n t, transposeBichromaticHom c m n v, ?_, ?_,
    W.map (transposeBichromaticHom c m n), ?_, ?_⟩
  · simp only [dualTopSide, Finset.mem_filter] at ht
    show (transposeIso t) 0 = m
    rw [transposeIso_apply_zero, ht.2]
  · simp only [dualBottomSide, Finset.mem_filter] at hv
    show (transposeIso v) 0 = -1
    rw [transposeIso_apply_zero, hv.2]
  · intro z hz
    rw [Walk.support_map, List.mem_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    have hwD := support_subset_dualRectangle_of_walk W htD w hw
    show -1 ≤ (transposeIso w) 0 ∧ (transposeIso w) 0 ≤ m ∧ 0 ≤ (transposeIso w) 1 ∧
      (transposeIso w) 1 + 1 ≤ n
    rw [mem_dualRectangle_iff] at hwD
    simp only [transposeIso_apply_zero, transposeIso_apply_one]
    omega
  · intro d hd
    rw [Walk.darts_map, List.mem_map] at hd
    obtain ⟨d', hd', rfl⟩ := hd
    have hadj := d'.adj
    exact Bichromatic.transpose hadj.1 hadj.2.2.2

end TransposedParity

/-! ### Boundary edges of a set of faces and the boundary crossing -/

section Boundary

/-- The dual of a primal step translated by `e₀`, in terms of the endpoints of the edge separating
the corresponding faces: `dualEdge {w + e₀, w' + e₀} = {sepLo w w' - e₁, sepHi w w' - e₁}` for
adjacent `w`, `w'` (double duality: the faces of the lattice of faces are the primal vertices,
shifted by `(1, 1)`, cf. `dualEdge_dualEdge`). [folklore] -/
theorem dualEdge_mk_add_single_zero {w w' : LatticeModels.Site 2} (h : (LatticeModels.zdGraph 2).Adj w w') :
    dualEdge s(w + Pi.single 0 1, w' + Pi.single 0 1) =
      s(sepLo w w' - Pi.single 1 1, sepHi w w' - Pi.single 1 1) := by
  rcases stepKind_of_adj h with ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h1, h0⟩ | ⟨h1, h0⟩
  · obtain rfl : w' = w + Pi.single 0 1 := by simp [LatticeModels.Site.eq_iff_two, h0, h1]
    rw [dualEdge_horizontal, sepLo_add_e0, sepHi_add_e0, add_sub_cancel_right]
  · obtain rfl : w = w' + Pi.single 0 1 := by simp [LatticeModels.Site.eq_iff_two, h0, h1]
    rw [Sym2.eq_swap, dualEdge_horizontal, sepLo_comm, sepHi_comm, sepLo_add_e0, sepHi_add_e0,
      add_sub_cancel_right]
  · obtain rfl : w' = w + Pi.single 1 1 := by simp [LatticeModels.Site.eq_iff_two, h0, h1]
    rw [add_right_comm w, dualEdge_vertical, sepLo_add_e1, sepHi_add_e1, add_sub_cancel_right,
      add_sub_cancel_right, add_right_comm w, add_sub_cancel_right]
  · obtain rfl : w = w' + Pi.single 1 1 := by simp [LatticeModels.Site.eq_iff_two, h0, h1]
    rw [Sym2.eq_swap, add_right_comm w', dualEdge_vertical, sepLo_comm, sepHi_comm, sepLo_add_e1,
      sepHi_add_e1, add_sub_cancel_right, add_sub_cancel_right, add_right_comm w',
      add_sub_cancel_right]

variable (D₀ : Finset (LatticeModels.Site 2)) (j : ℕ)

/-- `e` is a *boundary edge* of the set of faces `D₀` in the dual square `S* = dualRectangle j j`:
its dual edge joins a face of `D₀` to a face of `S*` outside `D₀`. (For `D₀` the region below
the lowest open crossing these are the edges of that crossing together with the closed edges
hanging below it; Kesten 1982, §2.3.) Junk value: since `dualEdge` is the identity on pairs
that are not lattice edges, `IsBdryEdge D₀ j e` may hold for such a pair `e` (e.g.
`e = s((0,-1), (0,1))`, `D₀ = {(0,-1)}`, `j = 1`); all uses supply `e ∈ (zdGraph 2).edgeSet`
separately. [folklore] -/
def IsBdryEdge (e : Sym2 (LatticeModels.Site 2)) : Prop :=
  ∃ g g' : LatticeModels.Site 2, dualEdge e = s(g, g') ∧ g ∈ dualRectangle j j ∧ g' ∈ dualRectangle j j ∧
    g ∈ D₀ ∧ g' ∉ D₀

variable {D₀ j}

/-- **The boundary crossing.** If every bottom face of `S* = [½, j - ½] × [-½, j + ½]` lies in
`D₀` and no top face does, then there is a lattice walk in `S = [0, j] × [0, j]` from its left
side to its right side all of whose edges are boundary edges of `D₀`. (The parity lemma
`exists_faceWalk_of_bottom_top` applied to the faces of `S*`, coloured by membership in `D₀`;
for `D₀ = dualBelow j ω` this walk is the lowest open left-right crossing of `S`, cf.
Bollobás–Riordan 2006, Ch. 3, remark after Lemma 1, and Kesten 1982, Prop. 2.3.) [folklore] -/
theorem exists_bdryWalk (hbot : ∀ f ∈ dualBottomSide j j, f ∈ D₀)
    (htop : ∀ f ∈ dualTopSide j j, f ∉ D₀) :
    ∃ a b : LatticeModels.Site 2, a 0 = 0 ∧ b 0 = j ∧ ∃ π : (LatticeModels.zdGraph 2).Walk a b,
      (∀ z ∈ π.support, z ∈ rectangle j j) ∧ ∀ d ∈ π.darts, IsBdryEdge D₀ j d.edge := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · refine ⟨0, 0, rfl, by simp, Walk.nil, ?_, ?_⟩
    · intro z hz
      rw [Walk.support_nil, List.mem_singleton] at hz
      subst hz
      simp [mem_rectangle_iff]
    · intro d hd; simp at hd
  set c : LatticeModels.Site 2 → Prop := fun z => z - Pi.single 1 1 ∈ D₀ with hc
  have hB : ∀ x ∈ bottomSide (j - 1) (j + 1), c x := by
    intro x hx
    simp only [bottomSide, Finset.mem_filter, mem_rectangle_iff] at hx
    apply hbot
    simp only [dualBottomSide, Finset.mem_filter, mem_dualRectangle_iff, Pi.sub_apply,
      single_one_apply_zero, single_one_apply_one]
    omega
  have hT : ∀ x ∈ topSide (j - 1) (j + 1), ¬c x := by
    intro x hx
    simp only [topSide, Finset.mem_filter, mem_rectangle_iff] at hx
    apply htop
    simp only [dualTopSide, Finset.mem_filter, mem_dualRectangle_iff, Pi.sub_apply,
      single_one_apply_zero, single_one_apply_one]
    omega
  obtain ⟨u, v, hu, hv, q, hq, hd⟩ := exists_faceWalk_of_bottom_top c (j - 1) (j + 1) hB hT
  refine ⟨(zdShiftIso (Pi.single 0 1 : LatticeModels.Site 2)).toEmbedding.toHom v,
    (zdShiftIso (Pi.single 0 1 : LatticeModels.Site 2)).toEmbedding.toHom u, ?_, ?_,
    q.reverse.map (zdShiftIso (Pi.single 0 1 : LatticeModels.Site 2)).toEmbedding.toHom, ?_, ?_⟩
  · show (v + Pi.single 0 1 : LatticeModels.Site 2) 0 = 0
    simp [hv]
  · show (u + Pi.single 0 1 : LatticeModels.Site 2) 0 = j
    simp only [Pi.add_apply, single_zero_apply_zero, hu]
    omega
  · intro z hz
    rw [Walk.support_map, List.mem_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    rw [Walk.support_reverse, List.mem_reverse] at hw
    have := hq w hw
    show w + Pi.single 0 1 ∈ rectangle j j
    simp only [mem_rectangle_iff, Pi.add_apply, single_zero_apply_zero, single_zero_apply_one]
    omega
  · intro d hd'
    rw [Walk.darts_map, List.mem_map] at hd'
    obtain ⟨d₁, hd₁, rfl⟩ := hd'
    rw [Walk.darts_reverse, List.mem_reverse, List.mem_map] at hd₁
    obtain ⟨d₀, hd₀, rfl⟩ := hd₁
    obtain ⟨hlo, hhi, hcol⟩ := hd d₀ hd₀
    have hedge : ((zdShiftIso (Pi.single 0 1 : LatticeModels.Site 2)).toEmbedding.toHom.mapDart d₀.symm).edge =
        s(d₀.fst + Pi.single 0 1, d₀.snd + Pi.single 0 1) := by
      rw [Sym2.eq_swap]; rfl
    rw [hedge]
    simp only [mem_rectangle_iff] at hlo hhi
    have hgD : sepLo d₀.fst d₀.snd - Pi.single 1 1 ∈ dualRectangle j j := by
      simp only [mem_dualRectangle_iff, Pi.sub_apply, single_one_apply_zero, single_one_apply_one]
      omega
    have hg'D : sepHi d₀.fst d₀.snd - Pi.single 1 1 ∈ dualRectangle j j := by
      simp only [mem_dualRectangle_iff, Pi.sub_apply, single_one_apply_zero, single_one_apply_one]
      omega
    by_cases hg : sepLo d₀.fst d₀.snd - Pi.single 1 1 ∈ D₀
    · exact ⟨_, _, dualEdge_mk_add_single_zero d₀.adj, hgD, hg'D, hg, hcol.1 hg⟩
    · refine ⟨_, _, ?_, hg'D, hgD, ?_, hg⟩
      · rw [dualEdge_mk_add_single_zero d₀.adj, Sym2.eq_swap]
      · by_contra h'
        exact hg (hcol.2 h')

end Boundary

/-! ### The faces below the lowest crossing -/

section Below

variable {j : ℕ} {ω : BondConfig (LatticeModels.Site 2)} {f f' : LatticeModels.Site 2}

open Classical in
/-- The random set of faces of the dual square `S* = dualRectangle j j` joined to its bottom side
by a dual-open path of `S*` — the faces "below the lowest open left-right crossing" of
`S = [0, j] × [0, j]` when there is one, all faces reachable from below otherwise.
(Kesten 1982, §2.3; Bollobás–Riordan 2006, Ch. 3, proof of Lemma 4, `LV(S)`.) [folklore] -/
def dualBelow (j : ℕ) (ω : BondConfig (LatticeModels.Site 2)) : Finset (LatticeModels.Site 2) :=
  (dualRectangle j j).filter fun f => ∃ b ∈ dualBottomSide j j,
    dualConfig ω ∈ openConnIn (↑(dualRectangle j j) : Set (LatticeModels.Site 2)) b f

/-- Membership in `dualBelow`. [folklore] -/
theorem mem_dualBelow_iff : f ∈ dualBelow j ω ↔ f ∈ dualRectangle j j ∧
    ∃ b ∈ dualBottomSide j j, dualConfig ω ∈ openConnIn (↑(dualRectangle j j) : Set (LatticeModels.Site 2)) b f := by
  classical
  simp [dualBelow]

/-- `dualBelow j ω ⊆ S*`. [folklore] -/
theorem dualBelow_subset : dualBelow j ω ⊆ dualRectangle j j := fun _ h => (mem_dualBelow_iff.1 h).1

/-- The bottom faces lie in `dualBelow`. [folklore] -/
theorem mem_dualBelow_of_mem_dualBottomSide (hf : f ∈ dualBottomSide j j) : f ∈ dualBelow j ω := by
  have hfD : f ∈ dualRectangle j j := (Finset.mem_filter.1 hf).1
  exact mem_dualBelow_iff.2 ⟨hfD, f, hf, openConnIn_refl (Finset.mem_coe.2 hfD)⟩

/-- `dualBelow` is closed under dual-open steps inside `S*`. [folklore] -/
theorem mem_dualBelow_of_adj (hf : f ∈ dualBelow j ω) (hf' : f' ∈ dualRectangle j j)
    (he : s(f, f') ∈ dualConfig ω) : f' ∈ dualBelow j ω := by
  obtain ⟨hfD, b, hb, hconn⟩ := mem_dualBelow_iff.1 hf
  have hne : f ≠ f' := ((LatticeModels.zdGraph 2).mem_edgeSet.1 (mem_dualConfig_iff.1 he).1).ne
  exact mem_dualBelow_iff.2 ⟨hf', b, hb, PlanarDuality.openConnIn_trans hconn
    (openConnIn_of_adj (Finset.mem_coe.2 hfD) (Finset.mem_coe.2 hf') he hne)⟩

/-- Every face of `dualBelow j ω` is joined to the bottom side by a dual-open path *inside*
`dualBelow j ω`. [folklore] -/
theorem exists_openConnIn_dualBelow (hf : f ∈ dualBelow j ω) :
    ∃ b ∈ dualBottomSide j j, dualConfig ω ∈ openConnIn (↑(dualBelow j ω) : Set (LatticeModels.Site 2)) b f := by
  classical
  obtain ⟨-, b, hb, hconn⟩ := mem_dualBelow_iff.1 hf
  obtain ⟨W, hWS, hWω⟩ :=
    exists_walk_of_mem_openConnIn (fun _ h => h.1 : dualConfig ω ⊆ (LatticeModels.zdGraph 2).edgeSet) hconn
  refine ⟨b, hb, mem_openConnIn_of_walk W (fun z hz => ?_) hWω⟩
  exact Finset.mem_coe.2 (mem_dualBelow_iff.2
    ⟨hWS z hz, b, hb, mem_openConnIn_of_mem_support W hWS hWω hz⟩)

/-- If `S` has an open left-right crossing then no top face lies below: `dualBelow j ω` misses
the top side of `S*` (planar duality, "not both"). [folklore] -/
theorem not_mem_dualBelow_of_lrCrossing (hω : ω ⊆ (LatticeModels.zdGraph 2).edgeSet) (h : ω ∈ lrCrossing j j)
    (hf : f ∈ dualTopSide j j) : f ∉ dualBelow j ω := by
  intro hfD
  obtain ⟨-, b, hb, hconn⟩ := mem_dualBelow_iff.1 hfD
  have hdual : ω ∈ dualTBCrossing j j :=
    ⟨f, Finset.mem_coe.2 hf, b, Finset.mem_coe.2 hb, by rw [openConnIn_comm]; exact hconn⟩
  rcases lrCrossing_xor_dualTBCrossing_holds j j hω with ⟨-, hn⟩ | ⟨-, hn⟩
  · exact hn hdual
  · exact hn h

/-! ### Locality of `{dualBelow = D₀}` -/

/-- The four primal edges bounding the face with lower-left corner `g`. [folklore] -/
def squareEdges (g : LatticeModels.Site 2) : Finset (Sym2 (LatticeModels.Site 2)) :=
  {s(g, g + Pi.single 0 1), s(g, g + Pi.single 1 1),
    s(g + Pi.single 1 1, g + Pi.single 1 1 + Pi.single 0 1),
    s(g + Pi.single 0 1, g + Pi.single 0 1 + Pi.single 1 1)}

/-- A lattice edge whose dual has the face `g` as an endpoint bounds the face `g`. [folklore] -/
theorem mem_squareEdges_of_mem_dualEdge {e : Sym2 (LatticeModels.Site 2)} (he : e ∈ (LatticeModels.zdGraph 2).edgeSet)
    {g : LatticeModels.Site 2} (hg : g ∈ dualEdge e) : e ∈ squareEdges g := by
  obtain ⟨u, hi⟩ := mem_edgeSet_zdGraph_iff.1 he
  rcases Fin.exists_fin_two.1 hi with rfl | rfl
  · rw [dualEdge_horizontal, Sym2.mem_iff] at hg
    rcases hg with rfl | rfl
    · simp [squareEdges, sub_add_cancel]
    · simp [squareEdges]
  · rw [dualEdge_vertical, Sym2.mem_iff] at hg
    rcases hg with rfl | rfl
    · simp [squareEdges, sub_add_cancel]
    · simp [squareEdges]

/-- Conversely, the face `g` is an endpoint of the dual of each of its four bounding edges. [folklore] -/
theorem mem_dualEdge_of_mem_squareEdges {e : Sym2 (LatticeModels.Site 2)} {g : LatticeModels.Site 2} (hg : e ∈ squareEdges g) :
    g ∈ dualEdge e := by
  simp only [squareEdges, Finset.mem_insert, Finset.mem_singleton] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · rw [dualEdge_horizontal]; exact Sym2.mem_mk_right _ _
  · rw [dualEdge_vertical]; exact Sym2.mem_mk_right _ _
  · rw [dualEdge_horizontal, add_sub_cancel_right]; exact Sym2.mem_mk_left _ _
  · rw [dualEdge_vertical, add_sub_cancel_right]; exact Sym2.mem_mk_left _ _

/-- The primal edges bounding some face of `D₀`: the edges examined by the event
`{dualBelow j ω = D₀}`. [folklore] -/
def belowEdges (D₀ : Finset (LatticeModels.Site 2)) : Finset (Sym2 (LatticeModels.Site 2)) := D₀.biUnion squareEdges

/-- A lattice edge whose dual meets `D₀` lies in `belowEdges D₀`. [folklore] -/
theorem mem_belowEdges {D₀ : Finset (LatticeModels.Site 2)} {e : Sym2 (LatticeModels.Site 2)} (he : e ∈ (LatticeModels.zdGraph 2).edgeSet)
    {g : LatticeModels.Site 2} (hgD : g ∈ D₀) (hg : g ∈ dualEdge e) : e ∈ belowEdges D₀ :=
  Finset.mem_biUnion.2 ⟨g, hgD, mem_squareEdges_of_mem_dualEdge he hg⟩

/-- The state of a dual edge with an endpoint in `D₀` is the same in two configurations agreeing
on `belowEdges D₀`. [folklore] -/
theorem mem_dualConfig_iff_of_inter_eq {D₀ : Finset (LatticeModels.Site 2)} {ω ω' : BondConfig (LatticeModels.Site 2)}
    (h : ω ∩ ↑(belowEdges D₀) = ω' ∩ ↑(belowEdges D₀)) {g g' : LatticeModels.Site 2} (hg : g ∈ D₀)
    (hE : s(g, g') ∈ (LatticeModels.zdGraph 2).edgeSet) :
    s(g, g') ∈ dualConfig ω ↔ s(g, g') ∈ dualConfig ω' := by
  set e := dualEdgeEquiv.symm s(g, g') with he
  have hde : dualEdge e = s(g, g') := by
    rw [← dualEdgeEquiv_apply, he, Equiv.apply_symm_apply]
  have heE : e ∈ (LatticeModels.zdGraph 2).edgeSet := (dualEdge_mem_edgeSet_iff e).1 (hde ▸ hE)
  have heF : e ∈ belowEdges D₀ := mem_belowEdges heE hg (by rw [hde]; exact Sym2.mem_mk_left _ _)
  have hiff : e ∈ ω ↔ e ∈ ω' :=
    ⟨fun h1 => ((Set.ext_iff.1 h e).1 ⟨h1, heF⟩).1, fun h1 => ((Set.ext_iff.1 h e).2 ⟨h1, heF⟩).1⟩
  rw [dualConfig_eq, dualConfig_eq, Set.mem_setOf_eq, Set.mem_setOf_eq, ← he, hiff]

/-- One direction of the locality of `{dualBelow = D₀}`. [folklore] -/
theorem dualBelow_eq_of_inter_eq {D₀ : Finset (LatticeModels.Site 2)} {ω ω' : BondConfig (LatticeModels.Site 2)}
    (h : ω ∩ ↑(belowEdges D₀) = ω' ∩ ↑(belowEdges D₀)) (hD : dualBelow j ω = D₀) :
    dualBelow j ω' = D₀ := by
  classical
  have hDR : D₀ ⊆ dualRectangle j j := hD ▸ dualBelow_subset
  apply Finset.Subset.antisymm
  · -- a face joined to the bottom in `ω'` but not in `D₀` gives a dual-open exit step from `D₀`
    intro f hf
    by_contra hfD
    obtain ⟨hfR, b, hb, hconn⟩ := mem_dualBelow_iff.1 hf
    have hbD : b ∈ D₀ := hD ▸ mem_dualBelow_of_mem_dualBottomSide hb
    obtain ⟨W, hWS, hWω⟩ :=
      exists_walk_of_mem_openConnIn (fun _ h => h.1 : dualConfig ω' ⊆ (LatticeModels.zdGraph 2).edgeSet) hconn
    obtain ⟨d, hd, hd1, hd2⟩ :=
      W.exists_boundary_dart (↑D₀ : Set (LatticeModels.Site 2)) (Finset.mem_coe.2 hbD) (by simpa using hfD)
    have hopen' : s(d.fst, d.snd) ∈ dualConfig ω' :=
      hWω _ (by rw [Walk.edges]; exact List.mem_map.2 ⟨d, hd, rfl⟩)
    have hopen : s(d.fst, d.snd) ∈ dualConfig ω :=
      (mem_dualConfig_iff_of_inter_eq h (Finset.mem_coe.1 hd1) (hopen'.1)).2 hopen'
    have := mem_dualBelow_of_adj (hD.symm ▸ Finset.mem_coe.1 hd1 : d.fst ∈ dualBelow j ω)
      (hWS _ (W.dart_snd_mem_support_of_mem_darts hd)) hopen
    rw [hD] at this
    exact hd2 (Finset.mem_coe.2 this)
  · -- a face of `D₀` is joined to the bottom inside `D₀`, by dual edges with the same states
    intro f hf
    have hf' : f ∈ dualBelow j ω := hD.symm ▸ hf
    obtain ⟨b, hb, hconn⟩ := exists_openConnIn_dualBelow hf'
    rw [hD] at hconn
    obtain ⟨W, hWS, hWω⟩ :=
      exists_walk_of_mem_openConnIn (fun _ h => h.1 : dualConfig ω ⊆ (LatticeModels.zdGraph 2).edgeSet) hconn
    have hWω' : ∀ e ∈ W.edges, e ∈ dualConfig ω' := by
      intro e he
      rw [Walk.edges, List.mem_map] at he
      obtain ⟨d, hd, rfl⟩ := he
      have hopen : s(d.fst, d.snd) ∈ dualConfig ω :=
        hWω _ (by rw [Walk.edges]; exact List.mem_map.2 ⟨d, hd, rfl⟩)
      exact (mem_dualConfig_iff_of_inter_eq h
        (Finset.mem_coe.1 (hWS _ (W.dart_fst_mem_support_of_mem_darts hd))) hopen.1).1 hopen
    have := mem_openConnIn_of_walk W (fun z hz => (hDR (Finset.mem_coe.1 (hWS z hz)) :
      z ∈ dualRectangle j j)) hWω'
    exact mem_dualBelow_iff.2 ⟨hDR hf, b, hb, this⟩

/-- **Locality of the region below the lowest crossing**: the event `{dualBelow j ω = D₀}` is
determined by the states of the edges bounding the faces of `D₀` ("the event `{LV(S) = P₁}`
does not depend on the states of bonds of `S` to the right of `P₁`", Bollobás–Riordan 2006,
Ch. 3, proof of Lemma 4; Kesten 1982, Prop. 2.3). [cite: BollobasRiordanPercolation2006, Ch. 3, proof of Lemma 4] -/
theorem determinedBy_dualBelow_eq (j : ℕ) (D₀ : Finset (LatticeModels.Site 2)) :
    DeterminedBy {ω : BondConfig (LatticeModels.Site 2) | dualBelow j ω = D₀} ↑(belowEdges D₀) := by
  rw [determinedBy_iff]
  intro ω ω' h
  exact ⟨dualBelow_eq_of_inter_eq h, dualBelow_eq_of_inter_eq h.symm⟩

/-- **Boundary edges are open**: on `{dualBelow j ω = D₀}` every lattice edge separating a face
of `D₀` from a face of `S* \ D₀` is open (otherwise its dual edge would be a dual-open step out
of `D₀`). In particular the boundary crossing of `exists_bdryWalk` is open: it is the lowest
open left-right crossing of `S`. [folklore] -/
theorem mem_of_isBdryEdge {D₀ : Finset (LatticeModels.Site 2)} (hD : dualBelow j ω = D₀) {e : Sym2 (LatticeModels.Site 2)}
    (he : e ∈ (LatticeModels.zdGraph 2).edgeSet) (hb : IsBdryEdge D₀ j e) : e ∈ ω := by
  by_contra hne
  obtain ⟨g, g', hde, -, hg', hgD, hg'D⟩ := hb
  have hdual : s(g, g') ∈ dualConfig ω := by
    rw [mem_dualConfig_iff, ← hde]
    refine ⟨dualEdge_mem_edgeSet_holds he, fun e'' he'' heq => ?_⟩
    have he''E : e'' ∈ (LatticeModels.zdGraph 2).edgeSet :=
      (dualEdge_mem_edgeSet_iff e'').1 (heq ▸ dualEdge_mem_edgeSet_holds he)
    exact hne (dualEdge_injOn_holds he''E he heq ▸ he'')
  have := mem_dualBelow_of_adj (hD.symm ▸ hgD : g ∈ dualBelow j ω) hg' hdual
  rw [hD] at this
  exact hg'D this

end Below

end

end Percolation.Literature
