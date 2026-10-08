import Percolation.Literature.HalfSpaceBrickUp
import Percolation.Literature.HalfSpaceHighDimStar
import Percolation.Util.Linter

/-!
# An infinite `ℍ*`-cluster has unbounded height: the slab-free form of Grimmett's (7.38) / BGN Lemma 2.3

In the printed proof of Lemma (7.36) the level counts `U(h)` are shown to be large via (Grimmett, p.
166) "`P_{p_c}(U(h) < 2N₂) ≤ a_h + ε²` … (We have used (7.38) surreptitiously here.)", where (7.38)
is `P_{p_c}(b(0) ↔ ∞ in S_h) = 0`, "which is to say that there is no percolation in slabs at `p_c`"
— obtained in the book from `p_c(S_h) > p_c` (Theorem 3.16 / Aizenman–Grimmett), in this library (for `d
= 3` only) from Duminil-Copin–Sidoravicius–Tassion (`HalfSpaceSlab.lean`). Barsky, Grimmett and
Newman (1991, proof of Prop. 2.1, Lemma 2.3, pp. 121–123) work at a general density `p` with `θ_ℍ(p)
> 0` and split into the cases "no slab percolates" / "some slab percolates", treating the second by
a dynamic exploration with fresh vertical columns ("every time that the 'cluster of `b_d`' reaches
the boundary of a new box `B_n`, it has at least probability `p^h` of being connected … to the
overhead site", p. 123).

This file PROVES a statement which makes both the slab input and the case split unnecessary,
in every dimension and at every density `p > 0`:

> **the `ℍ*`-cluster of a vertex is almost surely not both infinite and of bounded height**

(`BGNd.measure_percolatesVia_inter_heightLE_eq_zero`). The only place where (7.38) enters the
printed proof is the implication "`U(h) = 0` and `b(0) ↔ ∞ in ℍ*` ⇒ `b(0) ↔ ∞ in S_h`"; the
event on the left says that the `ℍ*`-cluster of `b(0)` is infinite and never reaches height
`h`, so it is null by the present result, with no hypothesis on slabs (`HalfSpaceHighDimSlab.lean`).

The proof is static (no stopping times). Let `T_j` be the graph of `ℍ*`-steps with both
endpoints at height `≤ j` (`BGNd.lowerStar d j`) and call a configuration *trapped at `(j, x)`*
if the `T_j`-cluster `K` of `x` is infinite while only finitely many of its height-`j` vertices
have an open upward edge (`BGNd.trapped`), and *top-trapped* if moreover `K` has infinitely
many height-`j` vertices (`BGNd.topTrapped`).

* `BGNd.measure_topTrapped_eq_zero` — top-trapped is null: conditionally on the `T_j`-edges,
  the upward edges over the (infinitely many) height-`j` vertices of `K` are independent and
  open with probability `p`; formally, the value-dependent conditional-independence
  decomposition `bondPercolation_real_inter_memDep_le` (`FiniteEnergy.lean`) applied to the
  finite statistic "height-`j` vertices of `K` in the box `box d R`" and the grouping bound
  `BGN.prob_compl_atLeastOpen_le` (`HalfSpaceBrickUp.lean`), followed by `R → ∞`.
* `BGNd.trapped_succ_subset` — the combinatorial heart: trapped at `(j+1, x)` implies
  top-trapped at `(j+1, x)` or trapped at `(j, z)` for some `z`. Indeed, if `K` (the
  `T_{j+1}`-cluster of `x`) has finitely many top vertices, its lower part is a disjoint union
  of `T_j`-clusters; an infinite one with infinitely many open upward edges would give
  infinitely many top vertices of `K`; and if all of them are finite there are infinitely many
  of them, each not containing `x` being entered from above through an open upward edge at a
  distinct height-`j` vertex (`BGNd.exists_entry_from_above`, the first boundary dart of an open
  `T_{j+1}`-walk from `x`), again giving infinitely many top vertices.

## References

* G. Grimmett, *Percolation*, 2nd ed., Grundlehren 321, Springer 1999, §7.3, pp. 165–166,
  (7.38), (7.41).
* D. J. Barsky, G. R. Grimmett, C. M. Newman, Percolation in half-spaces: equality of critical
  densities and continuity of the percolation probability, Probab. Theory Related Fields 90
  (1991) 111–148, §2, Lemmas 2.2–2.3, pp. 121–123.
-/

noncomputable section

namespace Percolation.Literature

open MeasureTheory ProbabilityTheory Filter LatticeModels
open scoped ENNReal Topology

namespace BGNd

variable {d : ℕ}

/-! ## The truncated graphs `T_j` -/

/-- Membership in the slab `S_j = {0 ≤ x 0 ≤ j}`. [folklore] -/
theorem mem_slab_iff [NeZero d] {j : ℕ} {x : Site d} : x ∈ slab d j ↔ 0 ≤ x 0 ∧ x 0 ≤ j := Iff.rfl

/-- **`T_j`**: the graph of `ℍ*`-steps with both endpoints at height `≤ j` (steps of `ℤ^d` inside
the slab `S_j` not joining two vertices of the hyperplane `L = {x 0 = 0}`; unlike `S_j*`, steps
inside the top hyperplane `{x 0 = j}` are allowed). [cite: GrimmettPercolation1999, §7.3 pp. 164–165 (ℍ*, S_h)] -/
def lowerStar (d : ℕ) [NeZero d] (j : ℕ) : SimpleGraph (Site d) :=
  starGraph (zdGraph d) (slab d j) (plane 0)

/-- Adjacency in `T_j`: an `ℍ*`-step with both endpoints at height `≤ j`. [folklore] -/
theorem lowerStar_adj_iff [NeZero d] {j : ℕ} {u v : Site d} :
    (lowerStar d j).Adj u v ↔ (halfSpaceStar d).Adj u v ∧ u 0 ≤ j ∧ v 0 ≤ j := by
  simp only [lowerStar, halfSpaceStar, starGraph_adj, mem_slab_iff, mem_halfSpace_iff]
  tauto

/-- `T_j ≤ ℍ*`. [folklore] -/
theorem lowerStar_le_halfSpaceStar [NeZero d] (j : ℕ) : lowerStar d j ≤ halfSpaceStar d :=
  fun _ _ h => (lowerStar_adj_iff.1 h).1

/-- `T_j` increases with `j`. [folklore] -/
theorem lowerStar_mono [NeZero d] {j j' : ℕ} (h : j ≤ j') : lowerStar d j ≤ lowerStar d j' := by
  intro u v huv
  rw [lowerStar_adj_iff] at huv ⊢
  exact ⟨huv.1, huv.2.1.trans (by exact_mod_cast h), huv.2.2.trans (by exact_mod_cast h)⟩

/-- `T_0` has no edges (both endpoints would lie in `L`). [folklore] -/
theorem not_lowerStar_zero_adj [NeZero d] (u v : Site d) : ¬(lowerStar d 0).Adj u v := by
  rintro ⟨-, hu, hv, hB⟩
  rw [mem_slab_iff] at hu hv
  push_cast at hu hv
  exact hB ⟨mem_plane_iff.2 (le_antisymm hu.2 hu.1), mem_plane_iff.2 (le_antisymm hv.2 hv.1)⟩

/-- The `T_j`-cluster of a vertex of `S_j` stays in `S_j`. [folklore] -/
theorem openClusterIn_lowerStar_subset_slab [NeZero d] {j : ℕ} {x : Site d} (hx : x ∈ slab d j)
    (ω : BondConfig (Site d)) : openClusterIn (lowerStar d j) ω x ⊆ slab d j :=
  openClusterIn_starGraph_subset hx ω

/-- The `T_j`-cluster of a vertex outside `S_j` is a singleton. [folklore] -/
theorem openClusterIn_lowerStar_of_notMem [NeZero d] {j : ℕ} {x : Site d} (hx : x ∉ slab d j)
    (ω : BondConfig (Site d)) : openClusterIn (lowerStar d j) ω x = {x} := by
  refine Set.Subset.antisymm (fun y hy => ?_) ?_
  · obtain ⟨w⟩ := mem_openClusterIn_iff.1 hy
    cases w with
    | nil => rfl
    | cons h _ => exact absurd h.2.2.1 hx
  · rintro y rfl
    exact self_mem_openClusterIn _ ω _

/-- The `T_0`-cluster of any vertex is a singleton. [folklore] -/
theorem openClusterIn_lowerStar_zero [NeZero d] (x : Site d) (ω : BondConfig (Site d)) :
    openClusterIn (lowerStar d 0) ω x = {x} := by
  refine Set.Subset.antisymm (fun y hy => ?_) ?_
  · obtain ⟨w⟩ := mem_openClusterIn_iff.1 hy
    cases w with
    | nil => rfl
    | cons h _ => exact absurd h.2 (not_lowerStar_zero_adj _ _)
  · rintro y rfl
    exact self_mem_openClusterIn _ ω _

/-- Heights in a `T_j`-cluster are at most `j` (when the source is in `S_j`, by the previous
lemmas; in general the cluster is `{x}` otherwise). [folklore] -/
theorem apply_zero_le_of_mem_openClusterIn_lowerStar [NeZero d] {j : ℕ} {x y : Site d}
    {ω : BondConfig (Site d)} (hy : y ∈ openClusterIn (lowerStar d j) ω x) (hne : y ≠ x) :
    0 ≤ y 0 ∧ y 0 ≤ j := by
  by_cases hx : x ∈ slab d j
  · exact mem_slab_iff.1 (openClusterIn_lowerStar_subset_slab hx ω hy)
  · rw [openClusterIn_lowerStar_of_notMem hx ω, Set.mem_singleton_iff] at hy
    exact absurd hy hne

/-! ## Vertical steps -/

/-- A step of `ℤ^d` which raises the height by one is the upward step. [folklore] -/
theorem eq_add_up_of_adj [NeZero d] {u v : Site d} (h : (zdGraph d).Adj u v) (h0 : v 0 = u 0 + 1) :
    v = u + up := by
  obtain ⟨i, h | h⟩ := (zdGraph_adj_iff u v).1 h
  · by_cases hi : i = 0
    · subst hi
      exact h
    · have h0' : (0 : Fin d) ≠ i := fun h' => hi h'.symm
      have := congrFun h 0
      simp only [Pi.add_apply, Pi.single_eq_of_ne h0', add_zero] at this
      omega
  · exfalso
    have := congrFun h 0
    by_cases hi : i = 0
    · subst hi
      simp only [Pi.add_apply, Pi.single_eq_same] at this
      omega
    · have h0' : (0 : Fin d) ≠ i := fun h' => hi h'.symm
      simp only [Pi.add_apply, Pi.single_eq_of_ne h0', add_zero] at this
      omega

/-- The height of `z + up`. [folklore] -/
@[simp] theorem add_up_apply_zero [NeZero d] (z : Site d) : (z + (up : Site d)) 0 = z 0 + 1 := by
  simp

/-- The height of `z - up`. [folklore] -/
@[simp] theorem sub_up_apply_zero [NeZero d] (z : Site d) : (z - (up : Site d)) 0 = z 0 - 1 := by
  simp

/-- The upward edge at a vertex of `ℍ` is a step of `ℍ*`. [cite: GrimmettPercolation1999, §7.3 p. 165] -/
theorem halfSpaceStar_adj_add_up [NeZero d] {z : Site d} (hz : 0 ≤ z 0) :
    (halfSpaceStar d).Adj z (z + up) := by
  refine ⟨(zdGraph_adj_iff _ _).2 ⟨0, Or.inl rfl⟩, mem_halfSpace_iff.2 hz,
    mem_halfSpace_iff.2 (by rw [add_up_apply_zero]; omega), ?_⟩
  rintro ⟨h1, h2⟩
  rw [mem_plane_iff] at h1 h2
  rw [add_up_apply_zero] at h2
  omega

/-- The upward edge at a vertex of height `< j` in `ℍ` is a step of `T_j`. [folklore] -/
theorem lowerStar_adj_add_up [NeZero d] {j : ℕ} {z : Site d} (hz : 0 ≤ z 0) (hzj : z 0 + 1 ≤ j) :
    (lowerStar d j).Adj z (z + up) :=
  lowerStar_adj_iff.2 ⟨halfSpaceStar_adj_add_up hz, by omega, by rw [add_up_apply_zero]; omega⟩

/-- The upward edges are edges of `ℤ^d`. [folklore] -/
theorem upEdge_mem_edgeSet [NeZero d] (z : Site d) : s(z, z + up) ∈ (zdGraph d).edgeSet :=
  (SimpleGraph.mem_edgeSet _).2 ((zdGraph_adj_iff _ _).2 ⟨0, Or.inl rfl⟩)

/-- `z ↦ ⟨z, z + up⟩` is injective. [folklore] -/
theorem upEdge_injective [NeZero d] : Function.Injective fun z : Site d => s(z, z + (up : Site d)) := by
  intro z z' h
  have h' := Sym2.eq_iff.1 h
  rcases h' with ⟨h1, -⟩ | ⟨h1, h2⟩
  · exact h1
  · exfalso
    have e1 := congrFun h1 0
    have e2 := congrFun h2 0
    rw [add_up_apply_zero] at e1 e2
    omega

/-! ## Sub-clusters and entry from above -/

/-- A `T_j`-cluster of a vertex of the `T_{j+1}`-cluster `K` of `x` lies in `K`. [folklore] -/
theorem openClusterIn_lowerStar_subset_of_mem [NeZero d] {j : ℕ} {ω : BondConfig (Site d)}
    {x z : Site d} (hz : z ∈ openClusterIn (lowerStar d (j + 1)) ω x) :
    openClusterIn (lowerStar d j) ω z ⊆ openClusterIn (lowerStar d (j + 1)) ω x := by
  rw [← openClusterIn_eq_of_mem hz]
  exact openClusterIn_mono_graph (lowerStar_mono (Nat.le_succ j)) ω z

/-- An open upward edge at a height-`j` vertex `z'` of the `T_{j+1}`-cluster `K` of `x` puts
`z' + up` in `K`. [folklore] -/
theorem add_up_mem_openClusterIn_lowerStar_succ [NeZero d] {j : ℕ} {ω : BondConfig (Site d)}
    {x z' : Site d} (hz' : z' ∈ openClusterIn (lowerStar d (j + 1)) ω x) (h0 : 0 ≤ z' 0)
    (hj : z' 0 = j) (hopen : s(z', z' + up) ∈ ω) :
    z' + up ∈ openClusterIn (lowerStar d (j + 1)) ω x :=
  mem_openClusterIn_of_adj hz' (lowerStar_adj_add_up h0 (by push_cast; omega)) hopen

/-- **Entry from above.** Let `K` be the `T_{j+1}`-cluster of `x`, `z ∈ K` a vertex of height
`≤ j`, and suppose that `x` is not in the `T_j`-cluster `K'` of `z`. Then `K'` is entered from
above: some height-`j` vertex `z'` of `K'` has its upward edge open and `z' + up ∈ K` (consider
the first dart of an open `T_{j+1}`-walk from `z` to `x` leaving `K'`: it cannot be a `T_j`-step,
so it is the upward step at a height-`j` vertex). [cite: GrimmettPercolation1999, §7.3 p. 166] [cite: BarskyGrimmettNewman1991, Lemma 2.3 p. 123] -/
theorem exists_entry_from_above [NeZero d] {j : ℕ} {ω : BondConfig (Site d)} {x z : Site d}
    (hz : z ∈ openClusterIn (lowerStar d (j + 1)) ω x) (hzs : z ∈ slab d j)
    (hx : x ∉ openClusterIn (lowerStar d j) ω z) :
    ∃ z' ∈ openClusterIn (lowerStar d j) ω z, z' 0 = j ∧ s(z', z' + up) ∈ ω ∧
      z' + up ∈ openClusterIn (lowerStar d (j + 1)) ω x := by
  classical
  obtain ⟨w⟩ := (mem_openClusterIn_iff.1 hz).symm
  set S : Set (Site d) := openClusterIn (lowerStar d j) ω z with hS
  obtain ⟨e, he, heS, heS'⟩ := w.exists_boundary_dart S (self_mem_openClusterIn _ ω z) hx
  have hadj : (openGraph ω ⊓ lowerStar d (j + 1)).Adj e.fst e.snd := e.adj
  rw [SimpleGraph.inf_adj, openGraph_adj] at hadj
  obtain ⟨⟨hopen, -⟩, hT⟩ := hadj
  have hT' := lowerStar_adj_iff.1 hT
  -- heights: `e.fst ∈ S ⊆ S_j`, `e.snd` at height `≤ j + 1`
  have hfst : 0 ≤ e.fst 0 ∧ e.fst 0 ≤ j := mem_slab_iff.1 (openClusterIn_lowerStar_subset_slab hzs ω heS)
  have hsnd_le : e.snd 0 ≤ (j : ℤ) + 1 := by have := hT'.2.2; push_cast at this; exact this
  -- `e.snd` is not at height `≤ j`, else the dart is an open `T_j`-step inside `S`
  have hsnd_gt : (j : ℤ) < e.snd 0 := by
    by_contra hle
    push Not at hle
    exact heS' (mem_openClusterIn_of_adj heS (lowerStar_adj_iff.2 ⟨hT'.1, hfst.2, hle⟩) hopen)
  have hstep := zdGraph_adj_apply_zero hT'.1.1
  have hsnd_eq : e.snd 0 = e.fst 0 + 1 := by omega
  have hfst_j : e.fst 0 = j := by omega
  have hsnd : e.snd = e.fst + up := eq_add_up_of_adj hT'.1.1 hsnd_eq
  -- `e.snd` lies on the walk, hence in `K`
  have hmem : e.snd ∈ w.support := w.dart_snd_mem_support_of_mem_darts he
  have hK : e.snd ∈ openClusterIn (lowerStar d (j + 1)) ω x :=
    mem_openClusterIn_iff.2 ((mem_openClusterIn_iff.1 hz).trans ⟨w.takeUntil _ hmem⟩)
  refine ⟨e.fst, heS, hfst_j, ?_, ?_⟩
  · rw [← hsnd]; exact hopen
  · rw [← hsnd]; exact hK

/-! ## Trapped configurations -/

/-- The height-`j` vertices of the `T_j`-cluster of `x` with an open upward edge. [folklore] -/
def openUp (d : ℕ) [NeZero d] (j : ℕ) (x : Site d) (ω : BondConfig (Site d)) : Set (Site d) :=
  {z | z ∈ openClusterIn (lowerStar d j) ω x ∧ z 0 = j ∧ s(z, z + up) ∈ ω}

/-- The height-`j` vertices of the `T_j`-cluster of `x`. [folklore] -/
def topOf (d : ℕ) [NeZero d] (j : ℕ) (x : Site d) (ω : BondConfig (Site d)) : Set (Site d) :=
  {z | z ∈ openClusterIn (lowerStar d j) ω x ∧ z 0 = j}

/-- **Trapped at `(j, x)`**: the `T_j`-cluster of `x` is infinite but only finitely many of its
height-`j` vertices have an open upward edge. [folklore] -/
def trapped (d : ℕ) [NeZero d] (j : ℕ) (x : Site d) : Set (BondConfig (Site d)) :=
  {ω | (openClusterIn (lowerStar d j) ω x).Infinite ∧ (openUp d j x ω).Finite}

/-- **Top-trapped at `(j, x)`**: the `T_j`-cluster of `x` has infinitely many height-`j` vertices
but only finitely many of them have an open upward edge. [folklore] -/
def topTrapped (d : ℕ) [NeZero d] (j : ℕ) (x : Site d) : Set (BondConfig (Site d)) :=
  {ω | (topOf d j x ω).Infinite ∧ (openUp d j x ω).Finite}

/-- Nothing is trapped at height `0` (`T_0`-clusters are singletons). [folklore] -/
theorem trapped_zero [NeZero d] (x : Site d) : trapped d 0 x = ∅ := by
  ext ω
  simp only [trapped, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro h
  rw [openClusterIn_lowerStar_zero] at h
  exact absurd (Set.finite_singleton x) h

/-- **The combinatorial heart**: trapped at `(j+1, x)` implies top-trapped at `(j+1, x)` or
trapped at `(j, z)` for some vertex `z`. [cite: GrimmettPercolation1999, §7.3 p. 166] [cite: BarskyGrimmettNewman1991, Lemma 2.3 p. 123] -/
theorem trapped_succ_subset [NeZero d] (j : ℕ) (x : Site d) :
    trapped d (j + 1) x ⊆ topTrapped d (j + 1) x ∪ ⋃ z : Site d, trapped d j z := by
  intro ω hω
  obtain ⟨hKinf, hUfin⟩ := hω
  by_cases htop : (topOf d (j + 1) x ω).Infinite
  · exact Or.inl ⟨htop, hUfin⟩
  right
  rw [Set.not_infinite] at htop
  simp only [Set.mem_iUnion]
  by_contra hnone
  push Not at hnone
  -- notation
  set K : Set (Site d) := openClusterIn (lowerStar d (j + 1)) ω x with hK
  have hxs : x ∈ slab d (j + 1) := by
    by_contra hxs
    rw [hK, openClusterIn_lowerStar_of_notMem hxs ω] at hKinf
    exact hKinf (Set.finite_singleton x)
  have hKslab : K ⊆ slab d (j + 1) := openClusterIn_lowerStar_subset_slab hxs ω
  -- every `T_j`-cluster of a vertex of `K` is finite
  have hfin : ∀ z ∈ K, (openClusterIn (lowerStar d j) ω z).Finite := by
    intro z hz
    by_contra hinf
    have hz' : ω ∉ trapped d j z := hnone z
    simp only [trapped, Set.mem_setOf_eq, not_and] at hz'
    have hUinf : (openUp d j z ω).Infinite := hz' hinf
    -- the open upward edges over the `T_j`-cluster of `z` give infinitely many top vertices of `K`
    apply htop.not_infinite
    have himage : ((fun z' : Site d => z' + up) '' openUp d j z ω).Infinite :=
      hUinf.image fun a _ b _ h => add_right_cancel h
    refine himage.mono ?_
    rintro _ ⟨z', ⟨hz'S, hz'j, hz'open⟩, rfl⟩
    have hz'K : z' ∈ K := openClusterIn_lowerStar_subset_of_mem hz hz'S
    have hz'0 : 0 ≤ z' 0 := (mem_slab_iff.1 (hKslab hz'K)).1
    refine ⟨add_up_mem_openClusterIn_lowerStar_succ hz'K hz'0 hz'j hz'open, ?_⟩
    show (z' + (up : Site d)) 0 = ((j + 1 : ℕ) : ℤ)
    rw [add_up_apply_zero, hz'j]
    push_cast
    ring
  -- the lower part of `K` is covered by finitely many finite `T_j`-clusters
  set Low : Set (Site d) := {z | z ∈ K ∧ z 0 ≤ j} with hLow
  have hcover : Low ⊆ openClusterIn (lowerStar d j) ω x ∪
      ⋃ w ∈ topOf d (j + 1) x ω, {y | w - up ∈ K ∧ y ∈ openClusterIn (lowerStar d j) ω (w - up)} := by
    rintro z ⟨hzK, hzj⟩
    have hzs : z ∈ slab d j := mem_slab_iff.2 ⟨(mem_slab_iff.1 (hKslab hzK)).1, hzj⟩
    by_cases hxz : x ∈ openClusterIn (lowerStar d j) ω z
    · left
      rw [openClusterIn_eq_of_mem hxz]
      exact self_mem_openClusterIn _ ω z
    · right
      obtain ⟨z', hz'S, hz'j, -, hz'K⟩ := exists_entry_from_above hzK hzs hxz
      simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
      refine ⟨z' + up, ⟨hz'K, by rw [add_up_apply_zero, hz'j]; push_cast; ring⟩, ?_, ?_⟩
      · rw [add_sub_cancel_right]
        exact openClusterIn_lowerStar_subset_of_mem hzK hz'S
      · rw [add_sub_cancel_right, openClusterIn_eq_of_mem hz'S]
        exact self_mem_openClusterIn _ ω z
  have hLowfin : Low.Finite := by
    refine Set.Finite.subset ?_ hcover
    refine (hfin x (self_mem_openClusterIn _ ω x)).union (Set.Finite.biUnion htop fun w _ => ?_)
    by_cases hw : w - up ∈ K
    · exact (hfin _ hw).subset fun y hy => hy.2
    · exact Set.finite_empty.subset fun y hy => absurd hy.1 hw
  -- hence `K` is finite: contradiction
  apply hKinf
  refine (htop.union hLowfin).subset fun z hzK => ?_
  have hz := mem_slab_iff.1 (hKslab hzK)
  rcases eq_or_lt_of_le hz.2 with h | h
  · exact Or.inl ⟨hzK, h⟩
  · refine Or.inr ⟨hzK, ?_⟩
    push_cast at h
    omega

/-! ## Top-trapped configurations are null -/

section TopTrapped

/-- Membership in the box `box d R` of `ThermodynamicLimit.lean` in the form `|z i| ≤ R`. [folklore] -/
theorem mem_box_iff_abs {R : ℕ} {z : Site d} : z ∈ box d R ↔ ∀ i, |z i| ≤ R := by
  simp only [mem_box, abs_le]

/-- Every finite set of vertices lies in some box. [folklore] -/
theorem exists_subset_box (t : Finset (Site d)) : ∃ R : ℕ, t ⊆ box d R := by
  refine ⟨t.sup fun z => Finset.univ.sup fun i => (z i).natAbs, fun z hz => mem_box_iff_abs.2 fun i => ?_⟩
  have h1 : (z i).natAbs ≤ Finset.univ.sup fun i => (z i).natAbs :=
    Finset.le_sup (f := fun i => (z i).natAbs) (Finset.mem_univ i)
  have h2 : (Finset.univ.sup fun i => (z i).natAbs) ≤ t.sup fun z => Finset.univ.sup fun i => (z i).natAbs :=
    Finset.le_sup (f := fun z : Site d => Finset.univ.sup fun i => (z i).natAbs) hz
  calc |z i| = ((z i).natAbs : ℤ) := (Int.natCast_natAbs (z i)).symm
    _ ≤ _ := by exact_mod_cast h1.trans h2

variable [NeZero d]

open Classical in
/-- The statistic of the nullity argument: the height-`j` vertices of the `T_j`-cluster of `x`
inside the box of radius `R`. [folklore] -/
def topBox (j : ℕ) (x : Site d) (R : ℕ) (ω : BondConfig (Site d)) : Finset (Site d) :=
  (box d R).filter fun z => z ∈ openClusterIn (lowerStar d j) ω x ∧ z 0 = j

/-- Membership in the statistic. [folklore] -/
theorem mem_topBox_iff {j : ℕ} {x : Site d} {R : ℕ} {ω : BondConfig (Site d)} {z : Site d} :
    z ∈ topBox j x R ω ↔ z ∈ box d R ∧ z ∈ openClusterIn (lowerStar d j) ω x ∧ z 0 = j := by
  classical
  simp only [topBox, Finset.mem_filter]

/-- The statistic only depends on the edges of `T_j`. [folklore] -/
theorem topBox_inter_edgeSet (j : ℕ) (x : Site d) (R : ℕ) (ω : BondConfig (Site d)) :
    topBox j x R (ω ∩ (lowerStar d j).edgeSet) = topBox j x R ω := by
  ext z
  simp only [mem_topBox_iff, openClusterIn_inter_edgeSet]

/-- `{z ∈ T_j-cluster of x}` is measurable. [folklore] -/
theorem measurableSet_mem_openClusterIn_lowerStar (j : ℕ) (x z : Site d) :
    MeasurableSet {ω : BondConfig (Site d) | z ∈ openClusterIn (lowerStar d j) ω x} :=
  measurableSet_openConnVia (lowerStar d j) x z

/-- The level sets of the statistic are measurable. [folklore] -/
theorem measurableSet_topBox_eq (j : ℕ) (x : Site d) (R : ℕ) (W : Finset (Site d)) :
    MeasurableSet {ω : BondConfig (Site d) | topBox j x R ω = W} := by
  have : {ω : BondConfig (Site d) | topBox j x R ω = W} =
      ⋂ z : Site d, {ω | z ∈ topBox j x R ω ↔ z ∈ W} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Finset.ext_iff]
  rw [this]
  refine MeasurableSet.iInter fun z => ?_
  by_cases hzW : z ∈ W
  · by_cases hc : z ∈ box d R ∧ z 0 = j
    · have : {ω : BondConfig (Site d) | z ∈ topBox j x R ω ↔ z ∈ W} =
          {ω | z ∈ openClusterIn (lowerStar d j) ω x} := by
        ext ω; simp [mem_topBox_iff, hzW, hc.1, hc.2]
      rw [this]
      exact measurableSet_mem_openClusterIn_lowerStar j x z
    · have : {ω : BondConfig (Site d) | z ∈ topBox j x R ω ↔ z ∈ W} = ∅ := by
        ext ω
        simp only [mem_topBox_iff, hzW, iff_true, Set.mem_setOf_eq, Set.mem_empty_iff_false,
          iff_false, not_and]
        intro h1 _ h3
        exact hc ⟨h1, h3⟩
      rw [this]
      exact MeasurableSet.empty
  · by_cases hc : z ∈ box d R ∧ z 0 = j
    · have : {ω : BondConfig (Site d) | z ∈ topBox j x R ω ↔ z ∈ W} =
          {ω | z ∈ openClusterIn (lowerStar d j) ω x}ᶜ := by
        ext ω; simp [mem_topBox_iff, hzW, hc.1, hc.2]
      rw [this]
      exact (measurableSet_mem_openClusterIn_lowerStar j x z).compl
    · have : {ω : BondConfig (Site d) | z ∈ topBox j x R ω ↔ z ∈ W} = Set.univ := by
        ext ω
        simp only [mem_topBox_iff, hzW, iff_false, not_and, Set.mem_setOf_eq, Set.mem_univ,
          iff_true]
        intro h1 _ h3
        exact hc ⟨h1, h3⟩
      rw [this]
      exact MeasurableSet.univ

/-- The upward edges over a finite set of vertices. [folklore] -/
def upEdges (W : Finset (Site d)) : Finset (Sym2 (Site d)) := W.image fun z => s(z, z + up)

/-- `|upEdges W| = |W|`. [folklore] -/
theorem card_upEdges (W : Finset (Site d)) : (upEdges W).card = W.card :=
  Finset.card_image_of_injective _ upEdge_injective

/-- The upward edges are edges of `ℤ^d`. [folklore] -/
theorem upEdges_subset_edgeSet (W : Finset (Site d)) :
    (↑(upEdges W) : Set (Sym2 (Site d))) ⊆ (zdGraph d).edgeSet := by
  intro e he
  rw [Finset.mem_coe, upEdges, Finset.mem_image] at he
  obtain ⟨z, -, rfl⟩ := he
  exact upEdge_mem_edgeSet z

/-- Upward edges at height-`j` vertices are not edges of `T_j`. [folklore] -/
theorem upEdges_disjoint_edgeSet_lowerStar {j : ℕ} {W : Finset (Site d)} (hW : ∀ z ∈ W, z 0 = j) :
    Disjoint (lowerStar d j).edgeSet (↑(upEdges W) : Set (Sym2 (Site d))) := by
  rw [Set.disjoint_right]
  intro e he heT
  rw [Finset.mem_coe, upEdges, Finset.mem_image] at he
  obtain ⟨z, hz, rfl⟩ := he
  have h := (lowerStar_adj_iff.1 ((SimpleGraph.mem_edgeSet _).1 heT)).2.2
  rw [add_up_apply_zero, hW z hz] at h
  omega

/-- "Fewer than `k + 1` of the upward edges over `W` are open". [folklore] -/
def fewOpenUp (k : ℕ) (W : Finset (Site d)) : Set (BondConfig (Site d)) :=
  (BGN.atLeastOpen (upEdges W) (k + 1))ᶜ

/-- `fewOpenUp k W` is determined by the upward edges over `W`. [folklore] -/
theorem determinedBy_fewOpenUp (k : ℕ) (W : Finset (Site d)) :
    DeterminedBy (fewOpenUp k W) (↑(upEdges W) : Set (Sym2 (Site d))) := by
  have h := BGN.determinedBy_atLeastOpen (upEdges W) (k + 1)
  rw [determinedBy_iff] at h ⊢
  intro ω ω' hω
  rw [fewOpenUp, Set.mem_compl_iff, Set.mem_compl_iff, h ω ω' hω]

/-- `fewOpenUp k W` is measurable. [folklore] -/
theorem measurableSet_fewOpenUp (k : ℕ) (W : Finset (Site d)) : MeasurableSet (fewOpenUp k W) :=
  (BGN.measurableSet_atLeastOpen _ _).compl

/-- `P_p(fewOpenUp k W) ≤ (k+1)(1-p)^g` when `|W| ≥ (k+1) g` (grouping bound,
`HalfSpaceBrickUp.lean`). [cite: GrimmettPercolation1999, §7.3 p. 165 (7.40)] -/
theorem prob_fewOpenUp_le (p : unitInterval) (k g : ℕ) {W : Finset (Site d)}
    (hW : (k + 1) * g ≤ W.card) :
    (bondPercolation (zdGraph d) p).real (fewOpenUp k W) ≤ ((k + 1 : ℕ) : ℝ) * (1 - (p : ℝ)) ^ g := by
  have h := BGN.prob_compl_atLeastOpen_le (zdGraph d) p (upEdges_subset_edgeSet W) (M := k + 1) (g := g)
    (by rw [card_upEdges]; exact hW)
  simpa [fewOpenUp] using h

/-- The events `G_R = {|topBox R| ≥ n} ∩ {fewOpenUp k (topBox R)}` of the nullity argument.
[folklore] -/
def boxEvent (j : ℕ) (x : Site d) (k n R : ℕ) : Set (BondConfig (Site d)) :=
  {ω | n ≤ (topBox j x R ω).card} ∩ {ω | ω ∈ fewOpenUp k (topBox j x R ω)}

/-- **`P_p(G_R) ≤ (k+1)(1-p)^g`** for `n = (k+1) g`: conditionally on the `T_j`-edges (which
determine the statistic), the upward edges over its value are independent of them
(`bondPercolation_real_inter_memDep_le`). [cite: GrimmettPercolation1999, §7.3 p. 167 (conditional independence)] -/
theorem prob_boxEvent_le (p : unitInterval) (j : ℕ) (x : Site d) (k g R : ℕ) :
    (bondPercolation (zdGraph d) p).real (boxEvent j x k ((k + 1) * g) R) ≤
      ((k + 1 : ℕ) : ℝ) * (1 - (p : ℝ)) ^ g := by
  set n := (k + 1) * g with hn
  set A : Set (BondConfig (Site d)) := {ω | n ≤ (topBox j x R ω).card} with hA
  have hdet : ∀ W, DeterminedBy (A ∩ topBox j x R ⁻¹' {W}) (lowerStar d j).edgeSet := by
    intro W
    have : A ∩ topBox j x R ⁻¹' {W} = (fun ω : BondConfig (Site d) => ω ∩ (lowerStar d j).edgeSet) ⁻¹'
        (A ∩ topBox j x R ⁻¹' {W}) := by
      ext ω
      simp only [hA, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff,
        topBox_inter_edgeSet]
    rw [this]
    exact determinedBy_preimage_inter _ _
  have hmeas : ∀ W, MeasurableSet (A ∩ topBox j x R ⁻¹' {W}) := by
    intro W
    have : A ∩ topBox j x R ⁻¹' {W} = {ω | topBox j x R ω = W} ∩ {_ω | n ≤ W.card} := by
      ext ω
      simp only [hA, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · rintro ⟨h1, rfl⟩
        exact ⟨rfl, h1⟩
      · rintro ⟨rfl, h1⟩
        exact ⟨h1, rfl⟩
    rw [this]
    exact (measurableSet_topBox_eq j x R W).inter (MeasurableSet.const _)
  have hdisj : ∀ ω ∈ A, Disjoint (lowerStar d j).edgeSet (↑(upEdges (topBox j x R ω)) : Set (Sym2 (Site d))) :=
    fun ω _ => upEdges_disjoint_edgeSet_lowerStar fun z hz => (mem_topBox_iff.1 hz).2.2
  have hq : ∀ ω ∈ A, (bondPercolation (zdGraph d) p).real (fewOpenUp k (topBox j x R ω)) ≤
      ((k + 1 : ℕ) : ℝ) * (1 - (p : ℝ)) ^ g := fun ω hω => prob_fewOpenUp_le p k g hω
  have h := bondPercolation_real_inter_memDep_le (zdGraph d) p (A := A)
    (fun _ => (lowerStar d j).edgeSet) (fun W => (↑(upEdges W) : Set (Sym2 (Site d))))
    (topBox j x R) (fun W => fewOpenUp k W) hdet hmeas (fun W => determinedBy_fewOpenUp k W)
    (fun W => measurableSet_fewOpenUp k W) hdisj hq
  have hA1 : (bondPercolation (zdGraph d) p).real A ≤ 1 := measureReal_le_one
  have hc : 0 ≤ ((k + 1 : ℕ) : ℝ) * (1 - (p : ℝ)) ^ g :=
    mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (sub_nonneg.2 p.2.2) _)
  calc (bondPercolation (zdGraph d) p).real (boxEvent j x k n R)
      = (bondPercolation (zdGraph d) p).real (A ∩ {ω | ω ∈ fewOpenUp k (topBox j x R ω)}) := rfl
    _ ≤ ((k + 1 : ℕ) : ℝ) * (1 - (p : ℝ)) ^ g * (bondPercolation (zdGraph d) p).real A := h
    _ ≤ ((k + 1 : ℕ) : ℝ) * (1 - (p : ℝ)) ^ g * 1 := mul_le_mul_of_nonneg_left hA1 hc
    _ = _ := mul_one _

/-- Top-trapped with at most `k` open upward edges. [folklore] -/
def topTrappedLE (j : ℕ) (x : Site d) (k : ℕ) : Set (BondConfig (Site d)) :=
  {ω | (topOf d j x ω).Infinite ∧ ∃ hf : (openUp d j x ω).Finite, hf.toFinset.card ≤ k}

/-- A top-trapped configuration with at most `k` open upward edges lies in `G_R` for all large
`R` (every `n`). [folklore] -/
theorem topTrappedLE_subset_liminf (j : ℕ) (x : Site d) (k n : ℕ) :
    topTrappedLE j x k ⊆ ⋃ R₀ : ℕ, ⋂ R ∈ Set.Ici R₀, boxEvent j x k n R := by
  rintro ω ⟨hinf, hf, hk⟩
  -- `n` top vertices, and a box containing them
  obtain ⟨t, ht, htn⟩ := hinf.exists_subset_card_eq n
  obtain ⟨R₀, hR₀⟩ := exists_subset_box t
  simp only [Set.mem_iUnion, Set.mem_iInter, Set.mem_Ici]
  refine ⟨R₀, fun R hR => ⟨?_, ?_⟩⟩
  · -- `n ≤ |topBox R|`
    rw [Set.mem_setOf_eq, ← htn]
    refine Finset.card_le_card fun z hz => mem_topBox_iff.2 ⟨box_mono d hR (hR₀ hz), ?_⟩
    exact ht (Finset.mem_coe.2 hz)
  · -- fewer than `k + 1` open upward edges over `topBox R`
    rintro ⟨Z, hZ, hZcard, hZω⟩
    -- the open edges `Z` come from distinct vertices of `openUp`
    classical
    set Z' : Finset (Site d) := (topBox j x R ω).filter fun z => s(z, z + (up : Site d)) ∈ Z with hZ'
    have hZeq : Z = Z'.image fun z => s(z, z + (up : Site d)) := by
      ext e
      constructor
      · intro he
        have he' := hZ he
        rw [upEdges, Finset.mem_image] at he'
        obtain ⟨z, hz, rfl⟩ := he'
        exact Finset.mem_image.2 ⟨z, Finset.mem_filter.2 ⟨hz, he⟩, rfl⟩
      · intro he
        rw [Finset.mem_image] at he
        obtain ⟨z, hz, rfl⟩ := he
        exact (Finset.mem_filter.1 hz).2
    have hZ'sub : Z' ⊆ hf.toFinset := fun z hz => by
      rw [Set.Finite.mem_toFinset]
      obtain ⟨hz1, hz2⟩ := Finset.mem_filter.1 hz
      exact ⟨(mem_topBox_iff.1 hz1).2.1, (mem_topBox_iff.1 hz1).2.2, hZω (Finset.mem_coe.2 hz2)⟩
    have hle : Z.card ≤ hf.toFinset.card := by
      rw [hZeq]
      exact Finset.card_image_le.trans (Finset.card_le_card hZ'sub)
    omega

/-- The sets `⋂_{R ≥ R₀} G_R` increase with `R₀`. [folklore] -/
theorem monotone_biInter_boxEvent (j : ℕ) (x : Site d) (k n : ℕ) :
    Monotone fun R₀ : ℕ => ⋂ R ∈ Set.Ici R₀, boxEvent j x k n R := by
  intro R₀ R₀' h ω hω
  simp only [Set.mem_iInter, Set.mem_Ici] at hω ⊢
  exact fun R hR => hω R (h.trans hR)

/-- **`P_p(topTrappedLE j x k) = 0`** for `p > 0`. [cite: GrimmettPercolation1999, §7.3 p. 166] [cite: BarskyGrimmettNewman1991, Lemma 2.3 p. 123] -/
theorem measure_topTrappedLE_eq_zero (p : unitInterval) (hp : 0 < (p : ℝ)) (j : ℕ) (x : Site d) (k : ℕ) :
    bondPercolation (zdGraph d) p (topTrappedLE j x k) = 0 := by
  set P := bondPercolation (zdGraph d) p with hP
  -- for every `g`: `P(topTrappedLE) ≤ (k+1)(1-p)^g`
  have hbound : ∀ g : ℕ, P (topTrappedLE j x k) ≤ ENNReal.ofReal (((k + 1 : ℕ) : ℝ) * (1 - (p : ℝ)) ^ g) := by
    intro g
    set n := (k + 1) * g with hn
    set D : ℕ → Set (BondConfig (Site d)) := fun R₀ => ⋂ R ∈ Set.Ici R₀, boxEvent j x k n R with hD
    have hlim : Tendsto (fun R₀ => P (D R₀)) atTop (𝓝 (P (⋃ R₀, D R₀))) :=
      tendsto_measure_iUnion_atTop (monotone_biInter_boxEvent j x k n)
    have hDle : ∀ R₀, P (D R₀) ≤ ENNReal.ofReal (((k + 1 : ℕ) : ℝ) * (1 - (p : ℝ)) ^ g) := by
      intro R₀
      calc P (D R₀) ≤ P (boxEvent j x k n R₀) :=
            measure_mono fun ω hω => (Set.mem_iInter₂.1 hω) R₀ (Set.mem_Ici.2 le_rfl)
        _ = ENNReal.ofReal (P.real (boxEvent j x k n R₀)) := (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
        _ ≤ _ := ENNReal.ofReal_le_ofReal (prob_boxEvent_le p j x k g R₀)
    calc P (topTrappedLE j x k) ≤ P (⋃ R₀, D R₀) := measure_mono (topTrappedLE_subset_liminf j x k n)
      _ ≤ _ := le_of_tendsto' hlim hDle
  -- let `g → ∞`
  have hq1 : 1 - (p : ℝ) < 1 := by linarith
  have hq0 : 0 ≤ 1 - (p : ℝ) := sub_nonneg.2 p.2.2
  have htend : Tendsto (fun g : ℕ => ENNReal.ofReal (((k + 1 : ℕ) : ℝ) * (1 - (p : ℝ)) ^ g)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun g : ℕ => ((k + 1 : ℕ) : ℝ) * (1 - (p : ℝ)) ^ g) atTop (𝓝 (((k + 1 : ℕ) : ℝ) * 0)) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul _
    rw [mul_zero] at h1
    have h2 := ENNReal.tendsto_ofReal h1
    rwa [ENNReal.ofReal_zero] at h2
  exact le_antisymm (ge_of_tendsto' htend hbound) bot_le

/-- **Top-trapped is null**: `P_p(topTrapped d j x) = 0` for `p > 0`.
[cite: GrimmettPercolation1999, §7.3 p. 166] [cite: BarskyGrimmettNewman1991, Lemma 2.3 p. 123] -/
theorem measure_topTrapped_eq_zero (p : unitInterval) (hp : 0 < (p : ℝ)) (j : ℕ) (x : Site d) :
    bondPercolation (zdGraph d) p (topTrapped d j x) = 0 := by
  have hsub : topTrapped d j x ⊆ ⋃ k : ℕ, topTrappedLE j x k := by
    rintro ω ⟨hinf, hf⟩
    exact Set.mem_iUnion.2 ⟨hf.toFinset.card, hinf, hf, le_rfl⟩
  exact measure_mono_null hsub (measure_iUnion_null fun k => measure_topTrappedLE_eq_zero p hp j x k)

end TopTrapped

/-! ## Trapped configurations are null; bounded height -/

/-- **Trapped is null**: `P_p(trapped d j x) = 0` for `p > 0`, every `j` and `x` (induction on
`j` using `trapped_succ_subset`). [cite: GrimmettPercolation1999, §7.3 p. 166] [cite: BarskyGrimmettNewman1991, Lemma 2.3 p. 123] -/
theorem measure_trapped_eq_zero [NeZero d] (p : unitInterval) (hp : 0 < (p : ℝ)) :
    ∀ (j : ℕ) (x : Site d), bondPercolation (zdGraph d) p (trapped d j x) = 0 := by
  intro j
  induction j with
  | zero => intro x; rw [trapped_zero, measure_empty]
  | succ j ih =>
    intro x
    exact measure_mono_null (trapped_succ_subset j x)
      (measure_union_null (measure_topTrapped_eq_zero p hp (j + 1) x) (measure_iUnion_null fun z => ih z))

/-- An `ℍ*`-cluster of height `≤ t` is the `T_t`-cluster of its source. [folklore] -/
theorem openClusterIn_halfSpaceStar_subset_lowerStar [NeZero d] {t : ℕ} {ω : BondConfig (Site d)}
    {y : Site d} (hle : ∀ z ∈ openClusterIn (halfSpaceStar d) ω y, z 0 ≤ t) :
    openClusterIn (halfSpaceStar d) ω y ⊆ openClusterIn (lowerStar d t) ω y := by
  refine BGN.openClusterIn_subset_of_closed (self_mem_openClusterIn _ ω y) fun u hu v huv => ?_
  rw [SimpleGraph.inf_adj, openGraph_adj] at huv
  obtain ⟨⟨hωuv, -⟩, hH⟩ := huv
  have hu' : u ∈ openClusterIn (halfSpaceStar d) ω y :=
    openClusterIn_mono_graph (lowerStar_le_halfSpaceStar t) ω y hu
  have hv' : v ∈ openClusterIn (halfSpaceStar d) ω y := mem_openClusterIn_of_adj hu' hH hωuv
  exact mem_openClusterIn_of_adj hu (lowerStar_adj_iff.2 ⟨hH, hle u hu', hle v hv'⟩) hωuv

/-- **An infinite `ℍ*`-cluster has unbounded height**: for `p > 0`, every vertex `y` and every
`t`, `P_p(y ↔ ∞ in ℍ* and every vertex of the ℍ*-cluster of y has height ≤ t) = 0`. This is the
slab-free replacement for Grimmett's use of (7.38) in the proof of Lemma (7.36) and for the case
analysis of BGN 1991, Lemma 2.3. [cite: GrimmettPercolation1999, §7.3 pp. 165–166 (7.38)] [cite: BarskyGrimmettNewman1991, Lemma 2.3 p. 123] -/
theorem measure_percolatesVia_inter_heightLE_eq_zero [NeZero d] (p : unitInterval) (hp : 0 < (p : ℝ))
    (y : Site d) (t : ℕ) :
    bondPercolation (zdGraph d) p
      (percolatesVia (halfSpaceStar d) y ∩ {ω | ∀ z ∈ openClusterIn (halfSpaceStar d) ω y, z 0 ≤ t}) = 0 := by
  refine measure_mono_null ?_ (measure_trapped_eq_zero p hp t y)
  rintro ω ⟨hinf, hle⟩
  have hsub := openClusterIn_halfSpaceStar_subset_lowerStar hle
  refine ⟨hinf.mono hsub, Set.finite_empty.subset ?_⟩
  rintro z ⟨hz, hzt, hopen⟩
  have hzH : z ∈ openClusterIn (halfSpaceStar d) ω y :=
    openClusterIn_mono_graph (lowerStar_le_halfSpaceStar t) ω y hz
  have hz0 : 0 ≤ z 0 := by
    rcases eq_or_ne z y with rfl | hne
    · -- `y ∈ ℍ`, else its cluster is `{y}`
      by_contra hy
      apply hinf
      have : openClusterIn (halfSpaceStar d) ω z = {z} := by
        refine Set.Subset.antisymm (fun w hw => ?_) (by rintro w rfl; exact self_mem_openClusterIn _ ω _)
        obtain ⟨wk⟩ := mem_openClusterIn_iff.1 hw
        cases wk with
        | nil => rfl
        | cons h _ => exact absurd (mem_halfSpace_iff.1 h.2.2.1) hy
      rw [this]
      exact Set.finite_singleton z
    · exact (apply_zero_le_of_mem_openClusterIn_lowerStar hz hne).1
  have hup : z + up ∈ openClusterIn (halfSpaceStar d) ω y :=
    mem_openClusterIn_of_adj hzH (halfSpaceStar_adj_add_up hz0) hopen
  have := hle _ hup
  rw [add_up_apply_zero, hzt] at this
  omega

end BGNd

end Percolation.Literature

end
