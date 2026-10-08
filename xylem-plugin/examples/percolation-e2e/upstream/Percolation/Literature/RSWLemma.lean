import Percolation.Literature.FiniteEnergy
import Percolation.Literature.LowestCrossing
import Percolation.Literature.RSWProofs
import Percolation.Util.Linter

/-!
# The Russo–Seymour–Welsh step: Bollobás–Riordan's Lemma 4 and Corollary 5

This file discharges the named facts
`Percolation.Literature.BollobasRiordan2006_cor5` (`h(3n, 2n) ≥ 2⁻⁷` at `p = 1/2`) and hence
`Percolation.Literature.rsw_lowerBound` (`h(kn, n) ≥ h_k > 0`) of `RSW.lean`, following Bollobás–Riordan,
*Percolation* (2006), Ch. 3, Lemma 4 and Corollary 5 (the argument of Bollobás–Riordan,
*A short proof of the Harris–Kesten theorem*, Bull. LMS 38 (2006)), with rows and columns
exchanged so that the "left-most vertical crossing" of the book becomes the *lowest horizontal
crossing*, which we handle through the region `dualBelow` below it (`LowestCrossing.lean`).

Setting (`crossingProb` indices, `n = j + 1`). `S = [0, j]²` is the bottom-left square of
`R = [0, 2j + 1] × [0, M]`, `M ≥ j`; `ρ` (`reflX (2j + 1)`) is the reflection of `R` in its
vertical axis `x₀ = j + ½`. `X = stdJoinedCrossing j M` is the event that an open left-right crossing of `S`
is joined inside `R` by an open path to the top side of `R` (in cluster form: some `a` on the
left side of `S` is joined in `S` to the right side of `S` and in `R` to the top side of `R`).

* **Lemma 4** (`BollobasRiordan2006_lemma4_holds`): `P_p(X) ≥ P_p(V(R)) · P_p(H(S)) / 2`.
  Proof. For a lattice configuration with `H(S)`, let `D = dualBelow j ω` be the set of faces of
  `S*` dual-joined to the bottom; `H(S)` holds iff `D` misses the top faces, `{D = D₀}` depends
  only on the edges bounding faces of `D₀` (`determinedBy_dualBelow_eq`), and the boundary of
  `D₀` contains a left-right crossing `π = π(D₀)` of `S` (`exists_bdryWalk`) which is open on
  `{D = D₀}` — the lowest crossing. Let `P = π ∪ {b, b + e₀} ∪ ρπ` (`symWalk`), a horizontal
  crossing of the strip `[0, 2j + 1] × [0, j]`, and let `Y(π)` (`pathToCrossing`) be the event that some
  open path of `R` descends from the top side of `R` to a vertex of `π` with all earlier
  vertices off `P`; `Y'(π) = ρ Y(π)` (`pathToReflCrossing`). Then
  - every open vertical crossing of `R` meets `P` (`exists_mem_support_of_crossing`), and its
    part above the first meeting witnesses `Y(π)` or `Y'(π)`; by reflection invariance
    `P(Y(π)) = P(Y'(π))`, so `P(Y(π)) ≥ P(V(R))/2` (`mem_pathToCrossing_or_mem_pathToReflCrossing`, `real_pathToReflCrossing_eq`);
  - `Y(π)` depends only on edges of `R` *not* bounding a face of `D₀` (`determinedBy_pathToCrossing`): the
    winding number of the extended path `P̂` (`PlanarDuality.lean`) is `0` at the top of `R`,
    constant along the witnessing path (which avoids `P̂`), equal on the faces around its
    vertices, but `-1` on every face of `D₀` (these are dual-joined to the bottom without
    crossing `P̂`, `walkWinding_symExt_of_mem`);
  - hence `{D = D₀}` and `Y(π)` are independent (`bondPercolation_real_inter_of_disjoint`,
    `FiniteEnergy.lean`), `{D = D₀} ∩ Y(π) ⊆ X`, and summing
    `P({D = D₀} ∩ X) ≥ P(D = D₀) P(V(R))/2` over the achieved values `D₀` gives the lemma.
* **Corollary 5** (`BollobasRiordan2006_cor5_general`, `BollobasRiordan2006_cor5_holds`): with the
  `2n × 2n` squares `R⁺ = [0, 2j+1] × [j+1, 3j+2]`, `R⁻ = [0, 2j+1]²` and `S = [0, j] × [j+1, 2j+1]`,
  the events `X⁺` (Lemma 4 in `R⁺`, translated), `X⁻` (Lemma 4 in `R⁻`, reflected in
  `x₁ = j + ½`) and `V(S)` are increasing and local; if all three hold, the vertical crossing of
  `S` meets both horizontal crossings and `[0, 2j+1] × [0, 3j+2]` is crossed vertically
  (`tbCrossing_of_upperJoinedCrossing_lowerJoinedCrossing_midTBCrossing`). By Harris's lemma and the symmetries of `P_p`,
  `h(3j+2, 2j+1) ≥ (h(2j+1, 2j+1) h(j, j)/2)² h(j, j)`, which is `≥ 2⁻⁷` at `p = 1/2` by
  `h(N, N) ≥ 1/2` (Cor. 3(iii)).
* `rsw_lowerBound_holds`: `rsw_lowerBound_of_glue` (`RSW.lean`) fed with Corollary 5, the gluing
  inequality `crossingProb_glue_holds` and `crossingProb_half_succ_self_holds` (`RSWProofs.lean`).
* `rsw_half_holds`: the box-crossing property `rsw_half` (`BoxCrossing.lean`) itself, by
  `rsw_half_of_lowerBound` (`RSW.lean`) from `rsw_lowerBound_holds` and the duality of crossing
  probabilities `crossingProb_add_crossingProb_symm_holds` (`RSWProofs.lean`; Bollobás–Riordan
  Ch. 3, eq. (3) with Corollary 3(i); Grimmett 1999, §11.7).

Mathlib anchors: `measureReal_biUnion_finset`, `SimpleGraph.Walk` (`map`, `append`,
`reverse`, `copy`, `firstDart`, `takeUntil` via `mem_openConnIn_of_mem_support`); tree anchors:
`bondPercolation_real_inter_of_disjoint` (`FiniteEnergy.lean`), `walkWinding`, `extendRight`,
`walkWinding_eq_of_faceWalk`, `walkWinding_eq_of_stepKind`, `exists_mem_support_of_crossing`
(`PlanarDuality.lean`), `dualBelow`, `belowEdges`, `IsBdryEdge`, `exists_bdryWalk`,
`determinedBy_dualBelow_eq`, `mem_of_isBdryEdge` (`LowestCrossing.lean`), `reflectIso`,
`zdShiftIso`, `bondPercolation_real_preimage_relabel_iso`, `real_tbCrossing`
(`LatticeSymmetry.lean`, `BondPercolationSymmetry.lean`), `harris_fkg_local` (`HarrisLocal.lean`),
`rsw_lowerBound_of_glue`, `half_le_crossingProb_self` (`RSW.lean`).

## References
* B. Bollobás, O. Riordan, *Percolation*, CUP (2006), Ch. 3, Lemma 4, Corollary 5, eq. (3)
  [BollobasRiordanPercolation2006].
* G. Grimmett, *Percolation*, 2nd ed., Springer (1999), §11.7, Lemma 11.73 [GrimmettPercolation1999].
* H. Kesten, *Percolation theory for mathematicians*, Birkhäuser (1982), §2.3 [KestenPTM1982].
-/

namespace Percolation.Literature

open MeasureTheory ProbabilityTheory SimpleGraph Finset unitInterval

noncomputable section

/-! ### Walk utilities -/

section WalkLemmas

variable {V : Type*} {G : SimpleGraph V}

/-- The prefix of a walk up to its first vertex in `O`: if a walk meets `O`, it has an initial
segment ending in `O` all of whose earlier vertices (the sources of its steps) avoid `O`.
[folklore] -/
theorem exists_prefix_first_mem {O : Set V} {a b : V} (p : G.Walk a b)
    (h : ∃ z ∈ p.support, z ∈ O) :
    ∃ v ∈ O, ∃ q : G.Walk a v, (∀ z ∈ q.support, z ∈ p.support) ∧
      (∀ e ∈ q.edges, e ∈ p.edges) ∧ ∀ d ∈ q.darts, d.fst ∉ O := by
  classical
  induction p with
  | nil =>
    rename_i a
    obtain ⟨z, hz, hzO⟩ := h
    rw [Walk.support_nil, List.mem_singleton] at hz
    subst hz
    exact ⟨z, hzO, Walk.nil, by simp, by simp, by simp⟩
  | cons hadj p ih =>
    rename_i x y b
    by_cases hx : x ∈ O
    · exact ⟨x, hx, Walk.nil, by simp, by simp, by simp⟩
    · have h' : ∃ z ∈ p.support, z ∈ O := by
        obtain ⟨z, hz, hzO⟩ := h
        rw [Walk.support_cons, List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact absurd hzO hx
        · exact ⟨z, hz, hzO⟩
      obtain ⟨v, hv, q, hqs, hqe, hqd⟩ := ih h'
      refine ⟨v, hv, Walk.cons hadj q, ?_, ?_, ?_⟩
      · intro z hz
        rw [Walk.support_cons, List.mem_cons] at hz ⊢
        rcases hz with rfl | hz
        · exact Or.inl rfl
        · exact Or.inr (hqs z hz)
      · intro e he
        rw [Walk.edges_cons, List.mem_cons] at he ⊢
        rcases he with rfl | he
        · exact Or.inl rfl
        · exact Or.inr (hqe e he)
      · intro d hd
        rw [Walk.darts_cons, List.mem_cons] at hd
        rcases hd with rfl | hd
        · exact hx
        · exact hqd d hd

end WalkLemmas

section LatticeWalks

/-- Discrete intermediate value property along a lattice walk: a walk of `ℤ²` from a vertex with
`x i ≤ c` to a vertex with `c ≤ y i` visits the hyperplane `{z i = c}`. [folklore] -/
theorem exists_mem_support_apply_eq {x y : LatticeModels.Site 2} (p : (LatticeModels.zdGraph 2).Walk x y) (i : Fin 2) (c : ℤ)
    (hx : x i ≤ c) (hy : c ≤ y i) : ∃ z ∈ p.support, z i = c := by
  induction p with
  | nil => rename_i x; exact ⟨x, by simp, le_antisymm hx hy⟩
  | cons hadj p ih =>
    rename_i x w y
    rcases hx.eq_or_lt with hxc | hxc
    · exact ⟨x, by simp, hxc⟩
    · have hw : w i ≤ c := by have := (zdGraph_adj_apply_le hadj i).1; omega
      obtain ⟨z, hz, hzc⟩ := ih hw hy
      exact ⟨z, by simp [hz], hzc⟩

/-- A lattice walk starting at height `≤ c` none of whose step sources lies at height `c` stays at
height `≤ c`. [folklore] -/
theorem apply_le_of_darts {x y : LatticeModels.Site 2} (p : (LatticeModels.zdGraph 2).Walk x y) (i : Fin 2) (c : ℤ)
    (hx : x i ≤ c) (h : ∀ d ∈ p.darts, d.fst i ≠ c) : ∀ z ∈ p.support, z i ≤ c := by
  induction p with
  | nil => intro z hz; rw [Walk.support_nil, List.mem_singleton] at hz; rw [hz]; exact hx
  | cons hadj p ih =>
    rename_i x w y
    have hxc : x i ≠ c := h ⟨(x, w), hadj⟩ (by simp)
    have hw : w i ≤ c := by have := (zdGraph_adj_apply_le hadj i).1; omega
    intro z hz
    rw [Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact hx
    · exact ih hw (fun d hd => h d (by simp [hd])) z hz

end LatticeWalks

/-! ### The reflection of `ℤ²` in a vertical axis -/

section Reflection

/-- The reflection `(x₀, x₁) ↦ (c - x₀, x₁)` of `ℤ²` in the vertical line `x₀ = c/2`, an
automorphism of the square lattice: the coordinate reflection `reflectIso 0` followed by the
translation `zdShiftIso (c, 0)`. (Bollobás–Riordan 2006, Ch. 3, proof of Lemma 4: reflection in
the symmetry axis of `R`; Grimmett 1999, proof of Lemma 11.73, `ρ`.) [folklore] -/
def reflX (c : ℤ) : LatticeModels.zdGraph 2 ≃g LatticeModels.zdGraph 2 := (reflectIso 0).trans (zdShiftIso ![c, 0])

/-- First coordinate of the reflection. [folklore] -/
@[simp] theorem reflX_apply_zero (c : ℤ) (x : LatticeModels.Site 2) : reflX c x 0 = c - x 0 := by
  have h1 : ((1 : Equiv.Perm (Fin 2)).symm : Equiv.Perm (Fin 2)) = 1 := rfl
  simp [reflX, RelIso.trans_apply, h1]; ring

/-- Second coordinate of the reflection. [folklore] -/
@[simp] theorem reflX_apply_one (c : ℤ) (x : LatticeModels.Site 2) : reflX c x 1 = x 1 := by
  have h1 : ((1 : Equiv.Perm (Fin 2)).symm : Equiv.Perm (Fin 2)) = 1 := rfl
  simp [reflX, RelIso.trans_apply, h1]

/-- The reflection is an involution. [folklore] -/
@[simp] theorem reflX_reflX (c : ℤ) (x : LatticeModels.Site 2) : reflX c (reflX c x) = x := by
  rw [LatticeModels.Site.eq_iff_two]; simp

/-- The inverse of the reflection is itself. [folklore] -/
@[simp] theorem reflX_symm_apply (c : ℤ) (x : LatticeModels.Site 2) : (reflX c).symm x = reflX c x := by
  rw [RelIso.symm_apply_eq, reflX_reflX]

/-- Images under the reflection. [folklore] -/
theorem mem_image_reflX_iff (c : ℤ) (S : Set (LatticeModels.Site 2)) (z : LatticeModels.Site 2) :
    z ∈ reflX c '' S ↔ reflX c z ∈ S := by
  constructor
  · rintro ⟨w, hw, rfl⟩; rwa [reflX_reflX]
  · intro h; exact ⟨reflX c z, h, reflX_reflX c z⟩

/-- Images under the inverse reflection. [folklore] -/
theorem image_reflX_symm (c : ℤ) (S : Set (LatticeModels.Site 2)) : (reflX c).symm '' S = reflX c '' S := by
  ext z
  simp only [Set.mem_image, reflX_symm_apply]

end Reflection

/-! ### The symmetric crossing `P = π ∪ e ∪ ρπ` and its winding numbers -/

section SymWalk

variable {j : ℕ} {a b : LatticeModels.Site 2}

/-- The reflection in the axis `x₀ = j + ½` maps the right side `x₀ = j` of `[0, j]²` to the
column `x₀ = j + 1`: `ρ b = b + e₀`. [folklore] -/
theorem reflX_eq_add_single (hb : b 0 = j) : reflX (2 * j + 1) b = b + Pi.single 0 1 := by
  rw [LatticeModels.Site.eq_iff_two]
  simp only [reflX_apply_zero, reflX_apply_one, Pi.add_apply, single_zero_apply_zero,
    single_zero_apply_one, add_zero, hb]
  exact ⟨by omega, trivial⟩

/-- One step to the right is a lattice step. [folklore] -/
theorem adj_add_single_zero (z : LatticeModels.Site 2) : (LatticeModels.zdGraph 2).Adj z (z + Pi.single 0 1) :=
  adj_of_stepKind (.right (by simp) (by simp))

/-- **The symmetric crossing.** For a walk `π` from `a` to `b` with `b₀ = j`, the walk
`π`, then the bond `{b, b + e₀}`, then the reflection `ρπ` of `π` in the axis `x₀ = j + ½`
traversed backwards, from `a` to `ρ a`. For `π` a left-right crossing of `[0, j]²` this is a
left-right crossing of `[0, 2j + 1] × [0, j]` symmetric under `ρ` (the path `P = P₁ ∪ P₁'` plus
one bond of Bollobás–Riordan 2006, Ch. 3, proof of Lemma 4, Figure 5, transposed). [folklore] -/
def symWalk (j : ℕ) (π : (LatticeModels.zdGraph 2).Walk a b) (hb : b 0 = j) :
    (LatticeModels.zdGraph 2).Walk a (reflX (2 * j + 1) a) :=
  π.append (Walk.cons (adj_add_single_zero b)
    (((π.map (reflX (2 * j + 1)).toEmbedding.toHom).reverse).copy (reflX_eq_add_single hb) rfl))

/-- Vertices of the symmetric crossing: those of `π` and their reflections. [folklore] -/
theorem mem_support_symWalk_iff (π : (LatticeModels.zdGraph 2).Walk a b) (hb : b 0 = j) {z : LatticeModels.Site 2} :
    z ∈ (symWalk j π hb).support ↔ z ∈ π.support ∨ reflX (2 * j + 1) z ∈ π.support := by
  rw [symWalk, Walk.support_append, List.mem_append, Walk.support_cons, List.tail_cons,
    Walk.support_copy, Walk.support_reverse, List.mem_reverse, Walk.support_map, List.mem_map]
  refine or_congr_right ⟨?_, fun h => ⟨_, h, by simp⟩⟩
  rintro ⟨w, hw, rfl⟩
  simpa using hw

/-- Edges of the symmetric crossing: those of `π`, the middle bond, and reflected edges of `π`.
[folklore] -/
theorem mem_edges_symWalk (π : (LatticeModels.zdGraph 2).Walk a b) (hb : b 0 = j) {e : Sym2 (LatticeModels.Site 2)}
    (he : e ∈ (symWalk j π hb).edges) :
    e ∈ π.edges ∨ e = s(b, b + Pi.single 0 1) ∨ ∃ e₀ ∈ π.edges, e = e₀.map (reflX (2 * j + 1)) := by
  rw [symWalk, Walk.edges_append, List.mem_append, Walk.edges_cons, List.mem_cons,
    Walk.edges_copy, Walk.edges_reverse, List.mem_reverse, Walk.edges_map, List.mem_map] at he
  rcases he with he | rfl | ⟨e₀, he₀, rfl⟩
  · exact Or.inl he
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr ⟨e₀, he₀, rfl⟩)

/-- The hypotheses on a left-right crossing `π` of `S = [0, j]²` used throughout: `π` lies in the
square, starts on the left side and ends on the right side (a horizontal crossing `H(S)`,
Bollobás–Riordan 2006, Ch. 3). [folklore] -/
structure IsSquareCrossing (j : ℕ) (π : (LatticeModels.zdGraph 2).Walk a b) : Prop where
  /-- The walk lies in `[0, j]²`. -/
  subset : ∀ z ∈ π.support, z ∈ rectangle j j
  /-- The walk starts on the left side `x₀ = 0`. -/
  start : a 0 = 0
  /-- The walk ends on the right side `x₀ = j`. -/
  finish : b 0 = j

namespace IsSquareCrossing

variable {π : (LatticeModels.zdGraph 2).Walk a b} (h : IsSquareCrossing j π)
include h

/-- The start of a square crossing has height `≥ 0`. [folklore] -/
theorem start_one_nonneg : 0 ≤ a 1 := (mem_rectangle_iff.1 (h.subset a π.start_mem_support)).2.2.1

/-- The start of a square crossing has height `≤ j`. [folklore] -/
theorem start_one_le : a 1 ≤ j := (mem_rectangle_iff.1 (h.subset a π.start_mem_support)).2.2.2

/-- The symmetric crossing lies in the strip `[0, 2j + 1] × [0, j]`. [folklore] -/
theorem support_symWalk_bounds {z : LatticeModels.Site 2} (hz : z ∈ (symWalk j π h.finish).support) :
    0 ≤ z 0 ∧ z 0 ≤ 2 * j + 1 ∧ 0 ≤ z 1 ∧ z 1 ≤ j := by
  rcases (mem_support_symWalk_iff π h.finish).1 hz with hz | hz
  · have := mem_rectangle_iff.1 (h.subset z hz); omega
  · have := mem_rectangle_iff.1 (h.subset _ hz)
    simp only [reflX_apply_zero, reflX_apply_one] at this
    omega

/-- The start of `P̂` is off every half-line `rayAbove z` with `z₀ ≥ 0`. [folklore] -/
theorem start_notMem_rayAbove {z : LatticeModels.Site 2} (hz : 0 ≤ z 0) : a ∉ rayAbove z := by
  have := h.start
  simp only [mem_rayAbove, not_and, not_le]; intro; omega

/-- The end of `P̂ = extendRight (symWalk j π _) 0` is `(2j + 2, -2)`. [folklore] -/
theorem symExt_end_apply :
    ((fun w : LatticeModels.Site 2 => w - Pi.single 1 1)^[((reflX (2 * j + 1) a) 1 - 0).toNat + 2]
        (reflX (2 * j + 1) a + Pi.single 0 1)) 0 = 2 * j + 2 ∧
    ((fun w : LatticeModels.Site 2 => w - Pi.single 1 1)^[((reflX (2 * j + 1) a) 1 - 0).toNat + 2]
        (reflX (2 * j + 1) a + Pi.single 0 1)) 1 = -2 := by
  have h' := extendRight_end_apply (reflX (2 * j + 1) a) (B := 0) (by simpa using h.start_one_nonneg)
  rw [h'.1, h'.2, reflX_apply_zero, h.start]
  constructor <;> ring

/-- The end of `P̂` is off every half-line `rayAbove z` with `z₁ ≥ -2`. [folklore] -/
theorem end_notMem_rayAbove {z : LatticeModels.Site 2} (hz : -2 ≤ z 1) :
    ((fun w : LatticeModels.Site 2 => w - Pi.single 1 1)^[((reflX (2 * j + 1) a) 1 - 0).toNat + 2]
        (reflX (2 * j + 1) a + Pi.single 0 1)) ∉ rayAbove z := by
  simp only [mem_rayAbove, not_and]
  intro h1
  rw [h.symExt_end_apply.2] at h1
  omega

/-- Vertices of `P̂`: those of the symmetric crossing, or on the column `x₀ = 2j + 2`. [folklore] -/
theorem mem_support_symExt {z : LatticeModels.Site 2} (hz : z ∈ (extendRight (symWalk j π h.finish) 0).support) :
    z ∈ (symWalk j π h.finish).support ∨ z 0 = 2 * j + 2 := by
  rcases mem_support_extendRight (P := symWalk j π h.finish) (B := 0)
    (by simpa using h.start_one_nonneg) hz with hz | hz
  · exact Or.inl hz
  · right; rw [hz.1, reflX_apply_zero, h.start]; ring

/-- A vertex of `[0, 2j + 1] × ℤ` off the symmetric crossing is off `P̂`. [folklore] -/
theorem notMem_support_symExt {v : LatticeModels.Site 2} (hv : v ∉ (symWalk j π h.finish).support)
    (hv0 : v 0 ≤ 2 * j + 1) : v ∉ (extendRight (symWalk j π h.finish) 0).support := fun h' => by
  rcases h.mem_support_symExt h' with h' | h'
  · exact hv h'
  · omega

/-- **Above `P`**: `P̂` does not wind around points at height `≥ j`. [folklore] -/
theorem walkWinding_symExt_eq_zero {u : LatticeModels.Site 2} (hu : (j : ℤ) ≤ u 1) :
    walkWinding (extendRight (symWalk j π h.finish) 0) u = 0 := by
  refine walkWinding_eq_zero_of_le (N := j) (fun z hz => ?_) hu
  rcases mem_support_extendRight (P := symWalk j π h.finish) (B := 0)
    (by simpa using h.start_one_nonneg) hz with hz | hz
  · exact (h.support_symWalk_bounds hz).2.2.2
  · have : (reflX (2 * j + 1) a) 1 ≤ j := by rw [reflX_apply_one]; exact h.start_one_le
    omega

/-- **Below `P`**: `P̂` winds `-1` times around the faces just below the strip. [folklore] -/
theorem walkWinding_symExt_eq_neg_one {u : LatticeModels.Site 2} (hu1 : u 1 = -1) (hu0 : u 0 ≤ 2 * j + 1) :
    walkWinding (extendRight (symWalk j π h.finish) 0) u = -1 :=
  walkWinding_extendRight_bottom (T := j) (fun z hz => (h.support_symWalk_bounds hz).2.2)
    (by rw [hu1]; ring) (by rw [reflX_apply_zero, h.start]; omega)

/-- **The faces of `D₀` lie below `P`.** If the edges of `π` are boundary edges of `D₀` and
`D₀ = dualBelow j ω₀` is an achieved value, then `P̂` winds `-1` times around every face of
`D₀`: each such face is joined to a bottom face by a dual walk inside `D₀` that is dual-open in
`ω₀`, hence never crosses an edge of `π` (these are open in `ω₀`), nor the other edges of `P̂`
(which lie in the columns `x₀ ≥ j`). [folklore] -/
theorem walkWinding_symExt_of_mem {D₀ : Finset (LatticeModels.Site 2)} {ω₀ : BondConfig (LatticeModels.Site 2)}
    (hbdry : ∀ d ∈ π.darts, IsBdryEdge D₀ j d.edge) (hach : dualBelow j ω₀ = D₀) {f : LatticeModels.Site 2}
    (hf : f ∈ D₀) : walkWinding (extendRight (symWalk j π h.finish) 0) f = -1 := by
  classical
  have hf' : f ∈ dualBelow j ω₀ := hach.symm ▸ hf
  obtain ⟨b₀, hb₀, hconn⟩ := exists_openConnIn_dualBelow hf'
  obtain ⟨q, hqS, hqω⟩ :=
    exists_walk_of_mem_openConnIn (fun _ h => h.1 : dualConfig ω₀ ⊆ (LatticeModels.zdGraph 2).edgeSet) hconn
  have hqD : ∀ z ∈ q.support, z ∈ dualRectangle j j := fun z hz =>
    dualBelow_subset (Finset.mem_coe.1 (hqS z hz))
  have hb₀D := mem_dualRectangle_iff.1 (Finset.mem_filter.1 hb₀).1
  rw [← h.walkWinding_symExt_eq_neg_one (u := b₀) (Finset.mem_filter.1 hb₀).2 (by omega)]
  symm
  refine walkWinding_eq_of_faceWalk _ q (fun dq hdq hmem => ?_)
    (fun z hz => h.start_notMem_rayAbove (mem_dualRectangle_iff.1 (hqD z hz)).1)
    (fun z hz => h.end_notMem_rayAbove (by have := (mem_dualRectangle_iff.1 (hqD z hz)).2.2.1; omega))
  -- the dual step `dq` is dual-open in `ω₀`
  have hdual : s(dq.fst, dq.snd) ∈ dualConfig ω₀ :=
    hqω _ (by rw [Walk.edges]; exact List.mem_map.2 ⟨dq, hdq, rfl⟩)
  have hg := mem_dualRectangle_iff.1 (hqD _ (q.dart_fst_mem_support_of_mem_darts hdq))
  have hg' := mem_dualRectangle_iff.1 (hqD _ (q.dart_snd_mem_support_of_mem_darts hdq))
  -- endpoints of the separating edge have first coordinate `≤ j`
  have hsep : ∀ w ∈ sepEdge dq.fst dq.snd, w 0 ≤ j := fun w hw => by
    have := (sepEdge_apply_zero_le hw).1
    have hmax : max (dq.fst 0) (dq.snd 0) ≤ (j : ℤ) - 1 := max_le hg.2.1 hg'.2.1
    omega
  rcases mem_edges_extendRight hmem with hsw | ⟨w, hw, hw0⟩
  · rcases mem_edges_symWalk π h.finish hsw with hπ | hbe | ⟨e₀, he₀, heq⟩
    · -- an edge of `π`: open in `ω₀`, so its dual is not dual-open
      obtain ⟨d, hd, hde⟩ : ∃ d ∈ π.darts, d.edge = sepEdge dq.fst dq.snd := by
        rw [Walk.edges] at hπ; exact List.mem_map.1 hπ
      have hopen : sepEdge dq.fst dq.snd ∈ ω₀ :=
        mem_of_isBdryEdge hach (π.edges_subset_edgeSet hπ) (hde ▸ hbdry d hd)
      exact (mem_dualConfig_iff.1 hdual).2 _ hopen (dualEdge_sepEdge dq.adj)
    · -- the middle bond `{b, b + e₀}` reaches the column `j + 1`
      have := hsep (b + Pi.single 0 1) (by rw [hbe]; exact Sym2.mem_mk_right _ _)
      simp only [Pi.add_apply, single_zero_apply_zero, h.finish] at this
      omega
    · -- a reflected edge lies in the columns `≥ j + 1`
      induction e₀ using Sym2.ind with
      | h x y =>
        have hx := mem_rectangle_iff.1 (h.subset x (π.fst_mem_support_of_mem_edges he₀))
        have := hsep (reflX (2 * j + 1) x)
          (by rw [heq, Sym2.map_mk]; exact Sym2.mem_mk_left _ _)
        rw [reflX_apply_zero] at this
        omega
  · have := hsep w hw
    rw [reflX_apply_zero, h.start] at hw0
    omega

/-- **The four faces around a vertex off `P`.** If `v ∈ [0, 2j + 1] × [0, ∞)` is not on the
symmetric crossing, then `P̂` winds equally around `v + (½, ½)` and around both faces adjacent to
any lattice edge at `v` (all four faces around `v` are separated only by edges at `v`, none of
which is on `P̂`). [folklore] -/
theorem walkWinding_symExt_eq_of_mem_dualEdge {v : LatticeModels.Site 2}
    (hv : v ∉ (symWalk j π h.finish).support) (hv0 : 0 ≤ v 0) (hv0' : v 0 ≤ 2 * j + 1)
    (hv1 : 0 ≤ v 1) {e : Sym2 (LatticeModels.Site 2)} (he : e ∈ (LatticeModels.zdGraph 2).edgeSet) (hve : v ∈ e) {g : LatticeModels.Site 2}
    (hg : g ∈ dualEdge e) :
    walkWinding (extendRight (symWalk j π h.finish) 0) g =
      walkWinding (extendRight (symWalk j π h.finish) 0) v := by
  set P := extendRight (symWalk j π h.finish) 0 with hP
  have hvP : v ∉ P.support := h.notMem_support_symExt hv hv0'
  have hne1 : ∀ w, s(v, w) ∉ P.edges := fun w h' => hvP (P.fst_mem_support_of_mem_edges h')
  have hne2 : ∀ w, s(w, v) ∉ P.edges := fun w h' => hvP (P.snd_mem_support_of_mem_edges h')
  -- the three other faces around `v`
  have h0 : walkWinding P (v - Pi.single 0 1) = walkWinding P v := by
    have := walkWinding_eq_walkWinding_right (p := P) (u := v - Pi.single 0 1)
      (by rw [sub_add_cancel]; exact hne1 _)
    rwa [sub_add_cancel] at this
  have h1 : walkWinding P (v - Pi.single 1 1) = walkWinding P v := by
    have := walkWinding_eq_walkWinding_up (p := P) (u := v - Pi.single 1 1)
      (by rw [sub_add_cancel]; exact hne1 _)
      (by
        have := h.start
        simp only [mem_rayAbove, Pi.sub_apply, single_one_apply_zero, not_and, not_le]
        intro; omega)
      (by
        simp only [mem_rayAbove, Pi.sub_apply, single_one_apply_one, sub_add_cancel, not_and]
        intro h'; rw [h.symExt_end_apply.2] at h'; omega)
    rwa [sub_add_cancel] at this
  have h01 : walkWinding P (v - Pi.single 0 1 - Pi.single 1 1) = walkWinding P v := by
    rw [← h0]
    have := walkWinding_eq_walkWinding_up (p := P) (u := v - Pi.single 0 1 - Pi.single 1 1)
      (by rw [sub_add_cancel, sub_add_cancel]; exact hne2 _)
      (by
        simp only [mem_rayAbove, Pi.sub_apply, single_one_apply_zero, single_zero_apply_zero,
          single_one_apply_one, single_zero_apply_one, sub_add_cancel, not_and, not_le]
        intro h1'
        by_contra h0'
        push Not at h0'
        have hva : v = a := by
          have := h.start
          rw [LatticeModels.Site.eq_iff_two]; constructor <;> omega
        exact hv ((mem_support_symWalk_iff π h.finish).2 (Or.inl (hva ▸ π.start_mem_support))))
      (by
        simp only [mem_rayAbove, Pi.sub_apply, single_one_apply_one, single_zero_apply_one,
          sub_add_cancel, not_and]
        intro h'; rw [h.symExt_end_apply.2] at h'; omega)
    rwa [sub_add_cancel] at this
  -- the edge `e` at `v` and its two faces
  obtain ⟨u, hi⟩ := mem_edgeSet_zdGraph_iff.1 he
  rcases Fin.exists_fin_two.1 hi with rfl | rfl
  · rw [dualEdge_horizontal] at hg
    rcases Sym2.mem_iff.1 hve with rfl | rfl
    · rcases Sym2.mem_iff.1 hg with rfl | rfl
      · exact h1
      · rfl
    · rcases Sym2.mem_iff.1 hg with rfl | rfl
      · rw [← h01, add_sub_cancel_right]
      · rw [← h0, add_sub_cancel_right]
  · rw [dualEdge_vertical] at hg
    rcases Sym2.mem_iff.1 hve with rfl | rfl
    · rcases Sym2.mem_iff.1 hg with rfl | rfl
      · exact h0
      · rfl
    · rcases Sym2.mem_iff.1 hg with rfl | rfl
      · rw [← h01, sub_right_comm, add_sub_cancel_right]
      · rw [← h1, add_sub_cancel_right]

end IsSquareCrossing

end SymWalk

/-! ### The events `X` (crossing joined to the top) and `Y` (path above `P` from the top) -/

section Events

variable {ω : BondConfig (LatticeModels.Site 2)}

/-- The event `X(S; R, T)` of Bollobás–Riordan 2006, Ch. 3, Lemma 4 (transposed, in cluster
form): some `a ∈ A` is joined inside `S` to some `b ∈ B` (an open crossing of `S` when `A`, `B`
are opposite sides of `S`) and inside `R` to some `t ∈ T`. [folklore] -/
def joinedCrossing (S R A B T : Set (LatticeModels.Site 2)) : Set (BondConfig (LatticeModels.Site 2)) :=
  {ω | ∃ a ∈ A, ∃ b ∈ B, ∃ t ∈ T, ω ∈ openConnIn S a b ∧ ω ∈ openConnIn R a t}

/-- `joinedCrossing` is increasing. [folklore] -/
theorem isUpperSet_joinedCrossing (S R A B T : Set (LatticeModels.Site 2)) : IsUpperSet (joinedCrossing S R A B T) := by
  rintro ω ω' hle ⟨a, ha, b, hb, t, ht, h1, h2⟩
  exact ⟨a, ha, b, hb, t, ht, isUpperSet_openConnIn S a b hle h1, isUpperSet_openConnIn R a t hle h2⟩

/-- Transport of `joinedCrossing` along a lattice automorphism. [folklore] -/
theorem relabel_mem_joinedCrossing (φ : LatticeModels.zdGraph 2 ≃g LatticeModels.zdGraph 2) {S R A B T : Set (LatticeModels.Site 2)}
    (h : ω ∈ joinedCrossing S R A B T) :
    BondConfig.relabel (sym2Equiv φ.toEquiv) ω ∈ joinedCrossing (φ '' S) (φ '' R) (φ '' A) (φ '' B) (φ '' T) := by
  obtain ⟨a, ha, b, hb, t, ht, h1, h2⟩ := h
  exact ⟨φ a, Set.mem_image_of_mem _ ha, φ b, Set.mem_image_of_mem _ hb, φ t,
    Set.mem_image_of_mem _ ht, relabel_mem_openConnIn φ.toEquiv h1, relabel_mem_openConnIn φ.toEquiv h2⟩

/-- `joinedCrossing` of the image sets pulls back to `joinedCrossing`. [folklore] -/
theorem preimage_relabel_joinedCrossing (φ : LatticeModels.zdGraph 2 ≃g LatticeModels.zdGraph 2) (S R A B T : Set (LatticeModels.Site 2)) :
    BondConfig.relabel (sym2Equiv φ.toEquiv) ⁻¹' joinedCrossing (φ '' S) (φ '' R) (φ '' A) (φ '' B) (φ '' T) =
      joinedCrossing S R A B T := by
  ext ω
  constructor
  · intro h
    have h' := relabel_mem_joinedCrossing φ.symm h
    have hs : ∀ U : Set (LatticeModels.Site 2), φ.symm '' (φ '' U) = U := fun U =>
      Equiv.symm_image_image φ.toEquiv U
    simp only [hs] at h'
    rwa [show φ.symm.toEquiv = φ.toEquiv.symm from rfl, relabel_symm_relabel] at h'
  · exact relabel_mem_joinedCrossing φ

/-- Transported `joinedCrossing` events are equiprobable. [folklore] -/
theorem real_joinedCrossing_image (φ : LatticeModels.zdGraph 2 ≃g LatticeModels.zdGraph 2) (p : unitInterval) (S R A B T : Set (LatticeModels.Site 2)) :
    (bondPercolation (LatticeModels.zdGraph 2) p).real (joinedCrossing (φ '' S) (φ '' R) (φ '' A) (φ '' B) (φ '' T)) =
      (bondPercolation (LatticeModels.zdGraph 2) p).real (joinedCrossing S R A B T) := by
  rw [← bondPercolation_real_preimage_relabel_iso φ p, preimage_relabel_joinedCrossing]

/-- `joinedCrossing` of finite regions is determined by the pairs of their vertices. [folklore] -/
theorem determinedBy_joinedCrossing (S R : Finset (LatticeModels.Site 2)) (A B T : Set (LatticeModels.Site 2)) :
    DeterminedBy (joinedCrossing ↑S ↑R A B T) ↑(S.sym2 ∪ R.sym2) := by
  rw [determinedBy_iff]
  intro ω ω' h
  have hS := fun x y => (determinedBy_iff _ _).1
    ((PlanarDuality.determinedBy_openConnIn S x y).mono (by simp)) ω ω' h
  have hR := fun x y => (determinedBy_iff _ _).1
    ((PlanarDuality.determinedBy_openConnIn R x y).mono (by simp)) ω ω' h
  simp only [joinedCrossing, Set.mem_setOf_eq, hS, hR]

/-- `joinedCrossing` of finite regions is a local event. [folklore] -/
theorem isLocalEvent_joinedCrossing (S R : Finset (LatticeModels.Site 2)) (A B T : Set (LatticeModels.Site 2)) :
    IsLocalEvent (joinedCrossing ↑S ↑R A B T) :=
  ⟨_, determinedBy_joinedCrossing S R A B T⟩

/-- `joinedCrossing` of finite regions is measurable. [folklore] -/
theorem measurableSet_joinedCrossing (S R : Finset (LatticeModels.Site 2)) (A B T : Set (LatticeModels.Site 2)) :
    MeasurableSet (joinedCrossing ↑S ↑R A B T) :=
  (determinedBy_joinedCrossing S R A B T).measurableSet_of_finset

/-- The event `Y` of Bollobás–Riordan 2006, Ch. 3, proof of Lemma 4 (transposed): an open
lattice walk inside `Rs` from a vertex of `T` to a vertex of `A`, all of whose vertices before
the last avoid the obstacle `O` (in the application: a path *above* the symmetric crossing `P`
from the top side of `R` to a vertex of `π`). [folklore] -/
def avoidingPath (Rs O A T : Set (LatticeModels.Site 2)) : Set (BondConfig (LatticeModels.Site 2)) :=
  {ω | ∃ t ∈ T, ∃ v ∈ A, ∃ γ : (LatticeModels.zdGraph 2).Walk t v, (∀ z ∈ γ.support, z ∈ Rs) ∧
    (∀ d ∈ γ.darts, d.fst ∉ O) ∧ ∀ e ∈ γ.edges, e ∈ ω}

/-- Transport of `avoidingPath` along a lattice automorphism. [folklore] -/
theorem relabel_mem_avoidingPath (φ : LatticeModels.zdGraph 2 ≃g LatticeModels.zdGraph 2) {Rs O A T : Set (LatticeModels.Site 2)}
    (h : ω ∈ avoidingPath Rs O A T) :
    BondConfig.relabel (sym2Equiv φ.toEquiv) ω ∈ avoidingPath (φ '' Rs) (φ '' O) (φ '' A) (φ '' T) := by
  obtain ⟨t, ht, v, hv, γ, hγR, hγO, hγω⟩ := h
  refine ⟨φ.toEmbedding.toHom t, Set.mem_image_of_mem _ ht, φ.toEmbedding.toHom v,
    Set.mem_image_of_mem _ hv, γ.map φ.toEmbedding.toHom, ?_, ?_, ?_⟩
  · intro z hz
    rw [Walk.support_map, List.mem_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact Set.mem_image_of_mem _ (hγR w hw)
  · intro d hd
    rw [Walk.darts_map, List.mem_map] at hd
    obtain ⟨d₀, hd₀, rfl⟩ := hd
    intro hO
    obtain ⟨w, hw, hweq⟩ := hO
    have : w = d₀.fst := φ.injective hweq
    exact hγO d₀ hd₀ (this ▸ hw)
  · intro e he
    rw [Walk.edges_map, List.mem_map] at he
    obtain ⟨e₀, he₀, rfl⟩ := he
    rw [BondConfig.relabel_apply]
    exact ⟨e₀, hγω e₀ he₀, rfl⟩

end Events

/-! ### The key step: `P(Y) ≥ P(V(R))/2` and independence from `{dualBelow = D₀}` -/

section KeyStep

variable {j M : ℕ} {a b : LatticeModels.Site 2} {π : (LatticeModels.zdGraph 2).Walk a b}

/-- The standard position of the event `X`: an open left-right crossing of `S = [0, j]²` joined
inside `R = [0, 2j + 1] × [0, M]` to the top side of `R`. [folklore] -/
def stdJoinedCrossing (j M : ℕ) : Set (BondConfig (LatticeModels.Site 2)) :=
  joinedCrossing ↑(rectangle j j) ↑(rectangle (2 * j + 1) M) ↑(leftSide j j) ↑(rightSide j j)
    ↑(topSide (2 * j + 1) M)

/-- The obstacle: the vertices of the symmetric crossing. [folklore] -/
def symObstacle (j : ℕ) (π : (LatticeModels.zdGraph 2).Walk a b) (hb : b 0 = j) : Set (LatticeModels.Site 2) :=
  {z | z ∈ (symWalk j π hb).support}

/-- The event `Y(π)` (Bollobás–Riordan 2006, Ch. 3, proof of Lemma 4, `Y(P₁)`, transposed): an open
path of `R` from the top side to a vertex of `π`, all of whose earlier vertices are off `P`. [folklore] -/
def pathToCrossing (j M : ℕ) (π : (LatticeModels.zdGraph 2).Walk a b) (hb : b 0 = j) : Set (BondConfig (LatticeModels.Site 2)) :=
  avoidingPath ↑(rectangle (2 * j + 1) M) (symObstacle j π hb) {z | z ∈ π.support} ↑(topSide (2 * j + 1) M)

/-- The mirror event `Y'(π) = ρ Y(π)`: an open path of `R` from the top side to a vertex of
`ρπ`, all of whose earlier vertices are off `P`. [folklore] -/
def pathToReflCrossing (j M : ℕ) (π : (LatticeModels.zdGraph 2).Walk a b) (hb : b 0 = j) : Set (BondConfig (LatticeModels.Site 2)) :=
  avoidingPath ↑(rectangle (2 * j + 1) M) (symObstacle j π hb) {z | reflX (2 * j + 1) z ∈ π.support}
    ↑(topSide (2 * j + 1) M)

namespace IsSquareCrossing

variable (h : IsSquareCrossing j π)
include h

/-- Along a lattice step inside `R` between vertices off the symmetric crossing, the winding
number of `P̂` does not change. [folklore] -/
theorem walkWinding_symExt_eq_of_adj {x y : LatticeModels.Site 2} (hxy : (LatticeModels.zdGraph 2).Adj x y)
    (hx : x ∉ (symWalk j π h.finish).support) (hy : y ∉ (symWalk j π h.finish).support)
    (hxR : x ∈ rectangle (2 * j + 1) M) (hyR : y ∈ rectangle (2 * j + 1) M) :
    walkWinding (extendRight (symWalk j π h.finish) 0) x =
      walkWinding (extendRight (symWalk j π h.finish) 0) y := by
  rw [mem_rectangle_iff] at hxR hyR
  push_cast at hxR hyR
  exact walkWinding_eq_of_stepKind (stepKind_of_adj hxy)
    (h.notMem_support_symExt hx hxR.2.1) (h.notMem_support_symExt hy hyR.2.1)
    (h.start_notMem_rayAbove hxR.1) (h.end_notMem_rayAbove (by omega))
    (h.start_notMem_rayAbove hyR.1) (h.end_notMem_rayAbove (by omega))

/-- Along a walk of `R` whose step sources avoid the symmetric crossing and which starts with
winding number `0`, every step source has winding number `0`. [folklore] -/
theorem walkWinding_eq_zero_of_darts {x y : LatticeModels.Site 2} (γ : (LatticeModels.zdGraph 2).Walk x y)
    (hγR : ∀ z ∈ γ.support, z ∈ rectangle (2 * j + 1) M)
    (hγO : ∀ d ∈ γ.darts, d.fst ∉ (symWalk j π h.finish).support)
    (hx : γ.darts ≠ [] → walkWinding (extendRight (symWalk j π h.finish) 0) x = 0) :
    ∀ d ∈ γ.darts, walkWinding (extendRight (symWalk j π h.finish) 0) d.fst = 0 := by
  induction γ with
  | nil => intro d hd; simp at hd
  | cons hadj γ ih =>
    rename_i x y z
    have hx0 : walkWinding (extendRight (symWalk j π h.finish) 0) x = 0 := hx (by simp)
    have hxO : x ∉ (symWalk j π h.finish).support := hγO ⟨(x, y), hadj⟩ (by simp)
    intro d hd
    rw [Walk.darts_cons, List.mem_cons] at hd
    rcases hd with rfl | hd
    · exact hx0
    · refine ih (fun w hw => hγR w (by simp [hw])) (fun d' hd' => hγO d' (by simp [hd'])) ?_ d hd
      intro hne
      have hyO : y ∉ (symWalk j π h.finish).support :=
        hγO (γ.firstDart (Walk.darts_eq_nil.not.mp hne))
          (by simp [Walk.firstDart_mem_darts (Walk.darts_eq_nil.not.mp hne)])
      rw [← h.walkWinding_symExt_eq_of_adj hadj hxO hyO (hγR x (by simp)) (hγR y (by simp))]
      exact hx0

/-- **`Y(π)` depends only on the edges of `R` above `P`**: it is determined by the pairs of
vertices of `R` not bounding a face of `D₀` ("`Y(P₁)` depends only on the states of bonds to the
right of `P`", Bollobás–Riordan 2006, Ch. 3, proof of Lemma 4). Indeed a witnessing walk starts on
the top side (winding number `0`) and its step sources avoid `P̂`, so all faces around them have
winding number `0`, whereas the faces of `D₀` have winding number `-1`. [cite: BollobasRiordanPercolation2006, Ch. 3, proof of Lemma 4] -/
theorem determinedBy_pathToCrossing (hM : j ≤ M) {D₀ : Finset (LatticeModels.Site 2)} {ω₀ : BondConfig (LatticeModels.Site 2)}
    (hbdry : ∀ d ∈ π.darts, IsBdryEdge D₀ j d.edge) (hach : dualBelow j ω₀ = D₀) :
    DeterminedBy (pathToCrossing j M π h.finish) ↑((rectangle (2 * j + 1) M).sym2 \ belowEdges D₀) := by
  classical
  set R := rectangle (2 * j + 1) M with hR
  set F := R.sym2 \ belowEdges D₀ with hF
  suffices key : ∀ ω ω' : BondConfig (LatticeModels.Site 2), ω ∩ ↑F = ω' ∩ ↑F →
      ω ∈ pathToCrossing j M π h.finish → ω' ∈ pathToCrossing j M π h.finish by
    rw [determinedBy_iff]
    exact fun ω ω' hωω' => ⟨key ω ω' hωω', key ω' ω hωω'.symm⟩
  rintro ω ω' hωω' ⟨t, ht, v, hv, γ, hγR, hγO, hγω⟩
  refine ⟨t, ht, v, hv, γ, hγR, hγO, fun e he => ?_⟩
  -- every edge of `γ` lies in `F`
  suffices heF : e ∈ F from ((Set.ext_iff.1 hωω' e).1 ⟨hγω e he, heF⟩).1
  rw [Walk.edges, List.mem_map] at he
  obtain ⟨d, hd, rfl⟩ := he
  have hdR := hγR _ (γ.dart_fst_mem_support_of_mem_darts hd)
  have hdR' := hγR _ (γ.dart_snd_mem_support_of_mem_darts hd)
  rw [hF, Finset.mem_sdiff]
  refine ⟨Finset.mk_mem_sym2_iff.2 ⟨hdR, hdR'⟩, fun hbelow => ?_⟩
  obtain ⟨g, hgD, hge⟩ := Finset.mem_biUnion.1 hbelow
  -- the face `g ∈ D₀` adjacent to the edge `d.edge` at `d.fst ∉ P`
  have hE : d.edge ∈ (LatticeModels.zdGraph 2).edgeSet := γ.edges_subset_edgeSet
    (by rw [Walk.edges]; exact List.mem_map.2 ⟨d, hd, rfl⟩)
  have hgd : g ∈ dualEdge d.edge := mem_dualEdge_of_mem_squareEdges hge
  have hW1 : walkWinding (extendRight (symWalk j π h.finish) 0) g = -1 :=
    h.walkWinding_symExt_of_mem hbdry hach hgD
  have hvR := mem_rectangle_iff.1 hdR
  have hW2 := h.walkWinding_symExt_eq_of_mem_dualEdge (hγO d hd) hvR.1 (by exact_mod_cast hvR.2.1)
    hvR.2.2.1 hE (Sym2.mem_mk_left _ _) hgd
  have hW3 : walkWinding (extendRight (symWalk j π h.finish) 0) d.fst = 0 := by
    refine h.walkWinding_eq_zero_of_darts γ hγR hγO (fun _ => ?_) d hd
    exact h.walkWinding_symExt_eq_zero (by
      have := (Finset.mem_filter.1 ht).2; rw [this]; exact_mod_cast hM)
  rw [hW2, hW3] at hW1
  exact absurd hW1 (by norm_num)

/-- **Every vertical crossing of `R` meets `P`, first on `π` or first on `ρπ`**: for a lattice
configuration with an open top-bottom crossing of `R = [0, 2j + 1] × [0, M]` (`M ≥ j`), the part
of the crossing below its first visit to height `j` (from the bottom) crosses the strip
`[0, 2j + 1] × [0, j]` vertically and therefore meets the symmetric crossing `P`
(`exists_mem_support_of_crossing`); the initial segment from the top down to the first vertex of
`P` witnesses `Y(π)` or `Y'(π)` ("this path must meet `P`. By symmetry ...", Bollobás–Riordan
2006, Ch. 3, proof of Lemma 4). [cite: BollobasRiordanPercolation2006, Ch. 3, proof of Lemma 4] -/
theorem mem_pathToCrossing_or_mem_pathToReflCrossing (hM : j ≤ M) {ω : BondConfig (LatticeModels.Site 2)} (hω : ω ⊆ (LatticeModels.zdGraph 2).edgeSet)
    (hV : ω ∈ tbCrossing (2 * j + 1) M) : ω ∈ pathToCrossing j M π h.finish ∨ ω ∈ pathToReflCrossing j M π h.finish := by
  classical
  obtain ⟨x, hx, t, ht, hxt⟩ := hV
  obtain ⟨Q, hQR, hQω⟩ := exists_walk_of_mem_openConnIn hω hxt
  simp only [Finset.mem_coe, bottomSide, topSide, Finset.mem_filter, mem_rectangle_iff] at hx ht
  -- the part of `Q` from the bottom up to its first visit to height `j`
  obtain ⟨z, hzj, γ₀, hγ₀s, -, hγ₀d⟩ := exists_prefix_first_mem (O := {z : LatticeModels.Site 2 | z 1 = j}) Q
    (exists_mem_support_apply_eq Q 1 j (by rw [hx.2]; positivity) (by rw [ht.2]; exact_mod_cast hM))
  have hγ₀le : ∀ w ∈ γ₀.support, w 1 ≤ j :=
    apply_le_of_darts γ₀ 1 j (by rw [hx.2]; positivity) (fun d hd => hγ₀d d hd)
  -- it meets the symmetric crossing
  obtain ⟨w, hwP, hwγ₀⟩ := exists_mem_support_of_crossing (L := 0) (R := 2 * j + 1) (B := 0) (T := j)
    (symWalk j π h.finish) γ₀ (fun w hw => by have := h.support_symWalk_bounds hw; omega)
    (fun w hw => by
      have := mem_rectangle_iff.1 (hQR w (hγ₀s w hw)); have := hγ₀le w hw; omega)
    h.start (by rw [reflX_apply_zero, h.start]; ring) hx.2 hzj
  -- the initial segment of `Q` reversed (from the top) down to its first vertex on `P`
  obtain ⟨v, hvO, γ, hγs, hγe, hγd⟩ := exists_prefix_first_mem (O := symObstacle j π h.finish) Q.reverse
    ⟨w, by rw [Walk.support_reverse, List.mem_reverse]; exact hγ₀s w hwγ₀, hwP⟩
  have hγR : ∀ z ∈ γ.support, z ∈ (↑(rectangle (2 * j + 1) M) : Set (LatticeModels.Site 2)) := fun z hz =>
    hQR z (by have := hγs z hz; rwa [Walk.support_reverse, List.mem_reverse] at this)
  have hγω : ∀ e ∈ γ.edges, e ∈ ω := fun e he =>
    hQω e (by have := hγe e he; rwa [Walk.edges_reverse, List.mem_reverse] at this)
  have htT : t ∈ (↑(topSide (2 * j + 1) M) : Set (LatticeModels.Site 2)) := by
    simp only [Finset.mem_coe, topSide, Finset.mem_filter, mem_rectangle_iff]; exact ht
  rcases (mem_support_symWalk_iff π h.finish).1 hvO with hv | hv
  · exact Or.inl ⟨t, htT, v, hv, γ, hγR, hγd, hγω⟩
  · exact Or.inr ⟨t, htT, v, hv, γ, hγR, hγd, hγω⟩

/-- **Reflection symmetry**: `P(Y'(π)) = P(Y(π))`, the reflection `ρ` in the axis `x₀ = j + ½`
preserving `R`, its top side and `P`, and exchanging `π` and `ρπ`. [folklore] -/
theorem real_pathToReflCrossing_eq (p : unitInterval) :
    (bondPercolation (LatticeModels.zdGraph 2) p).real (pathToReflCrossing j M π h.finish) =
      (bondPercolation (LatticeModels.zdGraph 2) p).real (pathToCrossing j M π h.finish) := by
  set ρ := reflX (2 * (j : ℤ) + 1) with hρ
  have hR : ρ '' (↑(rectangle (2 * j + 1) M) : Set (LatticeModels.Site 2)) = ↑(rectangle (2 * j + 1) M) := by
    ext z; rw [mem_image_reflX_iff, Finset.mem_coe, Finset.mem_coe, mem_rectangle_iff,
      mem_rectangle_iff, reflX_apply_zero, reflX_apply_one]; push_cast; omega
  have hT : ρ '' (↑(topSide (2 * j + 1) M) : Set (LatticeModels.Site 2)) = ↑(topSide (2 * j + 1) M) := by
    ext z
    rw [mem_image_reflX_iff]
    simp only [Finset.mem_coe, topSide, Finset.mem_filter, mem_rectangle_iff, reflX_apply_zero,
      reflX_apply_one]
    push_cast; omega
  have hO : ρ '' symObstacle j π h.finish = symObstacle j π h.finish := by
    ext z
    rw [mem_image_reflX_iff]
    simp only [symObstacle, Set.mem_setOf_eq, mem_support_symWalk_iff, reflX_reflX]
    tauto
  have hA : ρ '' {z : LatticeModels.Site 2 | z ∈ π.support} = {z | reflX (2 * j + 1) z ∈ π.support} := by
    ext z; rw [mem_image_reflX_iff]; rfl
  have hA' : ρ '' {z : LatticeModels.Site 2 | reflX (2 * j + 1) z ∈ π.support} = {z | z ∈ π.support} := by
    ext z; rw [mem_image_reflX_iff, Set.mem_setOf_eq, Set.mem_setOf_eq, reflX_reflX]
  have hpre : BondConfig.relabel (sym2Equiv ρ.toEquiv) ⁻¹' pathToReflCrossing j M π h.finish = pathToCrossing j M π h.finish := by
    ext ω
    constructor
    · intro hω
      have h' := relabel_mem_avoidingPath ρ.symm hω
      rw [show ρ.symm.toEquiv = ρ.toEquiv.symm from rfl, relabel_symm_relabel] at h'
      have hs : ∀ U : Set (LatticeModels.Site 2), ρ.symm '' U = ρ '' U := fun U => image_reflX_symm _ U
      simp only [hs] at h'
      rw [hR, hT, hO, hA'] at h'
      exact h'
    · intro hω
      have h' := relabel_mem_avoidingPath ρ hω
      rw [hR, hT, hO, hA] at h'
      exact h'
  rw [← hpre, bondPercolation_real_preimage_relabel_iso]

/-- On `{dualBelow = D₀} ∩ Y(π)` the event `X` occurs: `π` is an open crossing of `S` (its edges
are boundary edges of `D₀`, `mem_of_isBdryEdge`) and the open path of `Y(π)` joins it to the top
side inside `R`. ("If `Y(P₁)` holds and `LV(S) = P₁`, then `X(R)` holds", Bollobás–Riordan 2006,
Ch. 3, proof of Lemma 4.) [folklore] -/
theorem inter_pathToCrossing_subset_stdJoinedCrossing (hM : j ≤ M) {D₀ : Finset (LatticeModels.Site 2)}
    (hbdry : ∀ d ∈ π.darts, IsBdryEdge D₀ j d.edge) :
    {ω | dualBelow j ω = D₀} ∩ pathToCrossing j M π h.finish ⊆ stdJoinedCrossing j M := by
  classical
  rintro ω ⟨hD, t, ht, v, hv, γ, hγR, -, hγω⟩
  have hπω : ∀ e ∈ π.edges, e ∈ ω := by
    intro e he
    obtain ⟨d, hd, rfl⟩ : ∃ d ∈ π.darts, d.edge = e := by rw [Walk.edges] at he; exact List.mem_map.1 he
    exact mem_of_isBdryEdge hD (π.edges_subset_edgeSet he) (hbdry d hd)
  have hπS : ∀ z ∈ π.support, z ∈ (↑(rectangle j j) : Set (LatticeModels.Site 2)) := fun z hz => h.subset z hz
  have hSR : (↑(rectangle j j) : Set (LatticeModels.Site 2)) ⊆ ↑(rectangle (2 * j + 1) M) := by
    intro z hz
    rw [Finset.mem_coe, mem_rectangle_iff] at hz ⊢
    push_cast; omega
  refine ⟨a, ?_, b, ?_, t, ht, mem_openConnIn_of_walk π hπS hπω, ?_⟩
  · simp only [Finset.mem_coe, leftSide, Finset.mem_filter]
    exact ⟨h.subset a π.start_mem_support, h.start⟩
  · simp only [Finset.mem_coe, rightSide, Finset.mem_filter]
    exact ⟨h.subset b π.end_mem_support, h.finish⟩
  · have hav : ω ∈ openConnIn ↑(rectangle (2 * j + 1) M) a v :=
      openConnIn_mono hSR _ _ (mem_openConnIn_of_mem_support π hπS hπω hv)
    have hvt : ω ∈ openConnIn ↑(rectangle (2 * j + 1) M) v t := by
      rw [openConnIn_comm]; exact mem_openConnIn_of_walk γ hγR hγω
    exact PlanarDuality.openConnIn_trans hav hvt

/-- `Y(π)` is measurable (a local event). [folklore] -/
theorem measurableSet_pathToCrossing (hM : j ≤ M) {D₀ : Finset (LatticeModels.Site 2)} {ω₀ : BondConfig (LatticeModels.Site 2)}
    (hbdry : ∀ d ∈ π.darts, IsBdryEdge D₀ j d.edge) (hach : dualBelow j ω₀ = D₀) :
    MeasurableSet (pathToCrossing j M π h.finish) :=
  (h.determinedBy_pathToCrossing hM hbdry hach).measurableSet_of_finset

/-- **The conditional step of Lemma 4** (Bollobás–Riordan 2006, Ch. 3, proof of Lemma 4,
transposed): for an achieved value `D₀` of `dualBelow j` and its boundary crossing `π`,
`P_p({dualBelow = D₀} ∩ X) ≥ P_p(dualBelow = D₀) · P_p(V(R))/2`. Proof:
`{dualBelow = D₀} ∩ Y(π) ⊆ X`; the two events on the left are determined by disjoint sets of edges,
hence independent; and `2 P_p(Y(π)) = P_p(Y(π)) + P_p(Y'(π)) ≥ P_p(V(R))`. [cite: BollobasRiordanPercolation2006, Ch. 3, Lemma 4] -/
theorem le_real_inter_stdJoinedCrossing (p : unitInterval) (hM : j ≤ M) {D₀ : Finset (LatticeModels.Site 2)} {ω₀ : BondConfig (LatticeModels.Site 2)}
    (hbdry : ∀ d ∈ π.darts, IsBdryEdge D₀ j d.edge) (hach : dualBelow j ω₀ = D₀) :
    (bondPercolation (LatticeModels.zdGraph 2) p).real {ω | dualBelow j ω = D₀} *
        ((bondPercolation (LatticeModels.zdGraph 2) p).real (tbCrossing (2 * j + 1) M) / 2) ≤
      (bondPercolation (LatticeModels.zdGraph 2) p).real ({ω | dualBelow j ω = D₀} ∩ stdJoinedCrossing j M) := by
  classical
  set μ := bondPercolation (LatticeModels.zdGraph 2) p with hμ
  set E₀ : Set (BondConfig (LatticeModels.Site 2)) := {ω | dualBelow j ω = D₀} with hE₀
  set Y := pathToCrossing j M π h.finish
  set Y' := pathToReflCrossing j M π h.finish
  have hind : μ.real (E₀ ∩ Y) = μ.real E₀ * μ.real Y :=
    bondPercolation_real_inter_of_disjoint (LatticeModels.zdGraph 2) p
      (Finset.disjoint_coe.2 Finset.disjoint_sdiff) (determinedBy_dualBelow_eq j D₀)
      (h.determinedBy_pathToCrossing hM hbdry hach)
      (determinedBy_dualBelow_eq j D₀).measurableSet_of_finset
      (h.measurableSet_pathToCrossing hM hbdry hach)
  have hV : μ.real (tbCrossing (2 * j + 1) M) ≤ μ.real Y + μ.real Y' := by
    refine le_trans ?_ (measureReal_union_le Y Y')
    refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_)
    filter_upwards [ae_subset_edgeSet (LatticeModels.zdGraph 2) p] with ω hω hVω
    exact h.mem_pathToCrossing_or_mem_pathToReflCrossing hM hω hVω
  have hY' : μ.real Y' = μ.real Y := h.real_pathToReflCrossing_eq p
  have hmono : μ.real (E₀ ∩ Y) ≤ μ.real (E₀ ∩ stdJoinedCrossing j M) :=
    measureReal_mono (Set.subset_inter Set.inter_subset_left (h.inter_pathToCrossing_subset_stdJoinedCrossing hM hbdry))
  calc μ.real E₀ * (μ.real (tbCrossing (2 * j + 1) M) / 2)
      ≤ μ.real E₀ * μ.real Y := mul_le_mul_of_nonneg_left (by linarith) measureReal_nonneg
    _ = μ.real (E₀ ∩ Y) := hind.symm
    _ ≤ μ.real (E₀ ∩ stdJoinedCrossing j M) := hmono

end IsSquareCrossing

end KeyStep

/-! ### Lemma 4 (transposed): summing over the values of `dualBelow` -/

section Lemma4

/-- **Bollobás–Riordan 2006, Ch. 3, Lemma 4** (transposed: rows and columns exchanged, in
`crossingProb` indices, cluster form of the event `X`). Let `S = [0, j]²` be the bottom-left
square of `R = [0, 2j + 1] × [0, M]`, `M ≥ j`, and let `X` be the event that some open
left-right crossing of `S` is joined by an open path of `R` to the top side of `R` (`stdJoinedCrossing j M`).
Then `P_p(X) ≥ P_p(V(R)) P_p(H(S)) / 2`, where `V(R)` is the vertical crossing of `R`
(`tbCrossing (2j + 1) M`) and `P_p(H(S)) = crossingProb p j j`. [cite: BollobasRiordanPercolation2006, Ch. 3, Lemma 4] -/
def BollobasRiordan2006_lemma4 : Prop :=
  ∀ (p : unitInterval) (j M : ℕ), j ≤ M →
    (bondPercolation (LatticeModels.zdGraph 2) p).real (tbCrossing (2 * j + 1) M) * crossingProb p j j / 2 ≤
      (bondPercolation (LatticeModels.zdGraph 2) p).real (stdJoinedCrossing j M)

/-- **Discharge of `BollobasRiordan2006_lemma4`** (Bollobás–Riordan 2006, Ch. 3, proof of
Lemma 4, with the left-most crossing replaced by the region `dualBelow` below the lowest
crossing): `H(S)` is (a.e.) the disjoint union over the achieved values `D₀` of `dualBelow j`
missing the top faces of the events `{dualBelow = D₀}`; on each, the boundary crossing `π(D₀)` is
an open crossing of `S` and `P({dualBelow = D₀} ∩ X) ≥ P(dualBelow = D₀) P(V(R))/2`
(`IsSquareCrossing.le_real_inter_stdJoinedCrossing`); summing gives the claim. [cite: BollobasRiordanPercolation2006, Ch. 3, Lemma 4] -/
theorem BollobasRiordan2006_lemma4_holds : BollobasRiordan2006_lemma4 := by
  classical
  intro p j M hM
  set μ := bondPercolation (LatticeModels.zdGraph 2) p with hμ
  set 𝒟 : Finset (Finset (LatticeModels.Site 2)) := (dualRectangle j j).powerset.filter fun D₀ =>
    (∃ ω₀ : BondConfig (LatticeModels.Site 2), dualBelow j ω₀ = D₀) ∧ ∀ f ∈ dualTopSide j j, f ∉ D₀ with h𝒟
  set E₀ : Finset (LatticeModels.Site 2) → Set (BondConfig (LatticeModels.Site 2)) := fun D₀ => {ω | dualBelow j ω = D₀} with hE₀
  -- each term
  have hkey : ∀ D₀ ∈ 𝒟, μ.real (E₀ D₀) * (μ.real (tbCrossing (2 * j + 1) M) / 2) ≤
      μ.real (E₀ D₀ ∩ stdJoinedCrossing j M) := by
    intro D₀ hD₀
    obtain ⟨-, ⟨ω₀, hω₀⟩, htop⟩ := Finset.mem_filter.1 hD₀
    have hbot : ∀ f ∈ dualBottomSide j j, f ∈ D₀ := fun f hf =>
      hω₀ ▸ mem_dualBelow_of_mem_dualBottomSide hf
    obtain ⟨a, b, ha, hb, π, hπS, hπd⟩ := exists_bdryWalk hbot htop
    exact IsSquareCrossing.le_real_inter_stdJoinedCrossing ⟨hπS, ha, hb⟩ p hM hπd hω₀
  -- disjointness and measurability
  have hdisj : (↑𝒟 : Set (Finset (LatticeModels.Site 2))).PairwiseDisjoint fun D₀ => E₀ D₀ ∩ stdJoinedCrossing j M := by
    intro D₁ _ D₂ _ hne
    rw [Function.onFun, Set.disjoint_left]
    rintro ω ⟨h1, -⟩ ⟨h2, -⟩
    exact hne (h1.symm.trans h2)
  have hmeas : ∀ D₀ ∈ 𝒟, MeasurableSet (E₀ D₀ ∩ stdJoinedCrossing j M) := fun D₀ _ =>
    ((determinedBy_dualBelow_eq j D₀).measurableSet_of_finset).inter (measurableSet_joinedCrossing _ _ _ _ _)
  -- the sum is at most `P(X)`
  have hup : ∑ D₀ ∈ 𝒟, μ.real (E₀ D₀ ∩ stdJoinedCrossing j M) ≤ μ.real (stdJoinedCrossing j M) := by
    rw [← measureReal_biUnion_finset hdisj hmeas]
    exact measureReal_mono (Set.iUnion₂_subset fun D₀ _ => Set.inter_subset_right)
  -- `P(H(S))` is at most the sum of the `P(dualBelow = D₀)`
  have hlow : crossingProb p j j ≤ ∑ D₀ ∈ 𝒟, μ.real (E₀ D₀) := by
    refine le_trans ?_ (measureReal_biUnion_finset_le 𝒟 E₀)
    rw [crossingProb]
    refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_)
    filter_upwards [ae_subset_edgeSet (LatticeModels.zdGraph 2) p] with ω hω hlr
    refine Set.mem_iUnion₂.2 ⟨dualBelow j ω, ?_, rfl⟩
    exact Finset.mem_filter.2 ⟨Finset.mem_powerset.2 dualBelow_subset, ⟨ω, rfl⟩,
      fun f hf => not_mem_dualBelow_of_lrCrossing hω hlr hf⟩
  have h0 : 0 ≤ μ.real (tbCrossing (2 * j + 1) M) / 2 := by
    have := measureReal_nonneg (μ := μ) (s := tbCrossing (2 * j + 1) M); linarith
  calc μ.real (tbCrossing (2 * j + 1) M) * crossingProb p j j / 2
      = crossingProb p j j * (μ.real (tbCrossing (2 * j + 1) M) / 2) := by ring
    _ ≤ (∑ D₀ ∈ 𝒟, μ.real (E₀ D₀)) * (μ.real (tbCrossing (2 * j + 1) M) / 2) :=
      mul_le_mul_of_nonneg_right hlow h0
    _ = ∑ D₀ ∈ 𝒟, μ.real (E₀ D₀) * (μ.real (tbCrossing (2 * j + 1) M) / 2) := Finset.sum_mul _ _ _
    _ ≤ ∑ D₀ ∈ 𝒟, μ.real (E₀ D₀ ∩ stdJoinedCrossing j M) := Finset.sum_le_sum hkey
    _ ≤ μ.real (stdJoinedCrossing j M) := hup

end Lemma4

/-! ### Corollary 5 (transposed): two stacked squares and the square between them -/

section Cor5

/-- The reflection `(x₀, x₁) ↦ (x₀, c - x₁)` of `ℤ²` in the horizontal line `x₁ = c/2`:
`reflectIso 1` followed by `zdShiftIso (0, c)`. (Bollobás–Riordan 2006, Ch. 3, proof of Cor. 5:
"`X'(R')` ... reflected".) [folklore] -/
def reflY (c : ℤ) : LatticeModels.zdGraph 2 ≃g LatticeModels.zdGraph 2 := (reflectIso 1).trans (zdShiftIso ![0, c])

/-- First coordinate of the reflection. [folklore] -/
@[simp] theorem reflY_apply_zero (c : ℤ) (x : LatticeModels.Site 2) : reflY c x 0 = x 0 := by
  have h1 : ((1 : Equiv.Perm (Fin 2)).symm : Equiv.Perm (Fin 2)) = 1 := rfl
  simp [reflY, RelIso.trans_apply, h1]

/-- Second coordinate of the reflection. [folklore] -/
@[simp] theorem reflY_apply_one (c : ℤ) (x : LatticeModels.Site 2) : reflY c x 1 = c - x 1 := by
  have h1 : ((1 : Equiv.Perm (Fin 2)).symm : Equiv.Perm (Fin 2)) = 1 := rfl
  simp [reflY, RelIso.trans_apply, h1]; ring

/-- The reflection is an involution. [folklore] -/
@[simp] theorem reflY_reflY (c : ℤ) (x : LatticeModels.Site 2) : reflY c (reflY c x) = x := by
  rw [LatticeModels.Site.eq_iff_two]; simp

/-- Images under the reflection. [folklore] -/
theorem mem_image_reflY_iff (c : ℤ) (S : Set (LatticeModels.Site 2)) (z : LatticeModels.Site 2) :
    z ∈ reflY c '' S ↔ reflY c z ∈ S := by
  constructor
  · rintro ⟨w, hw, rfl⟩; rwa [reflY_reflY]
  · intro h; exact ⟨reflY c z, h, reflY_reflY c z⟩

/-- Images under a translation, as images under `· + v`. [folklore] -/
theorem image_zdShiftIso (v : LatticeModels.Site 2) (U : Set (LatticeModels.Site 2)) : zdShiftIso v '' U = (· + v) '' U := rfl

variable (j : ℕ)

/-- The translation by `(0, j + 1)`. [folklore] -/
def upShift : LatticeModels.Site 2 := ![0, (j : ℤ) + 1]

/-- Coordinates of `upShift`. [folklore] -/
@[simp] theorem upShift_apply_zero : upShift j 0 = 0 := rfl
/-- Coordinates of `upShift`. [folklore] -/
@[simp] theorem upShift_apply_one : upShift j 1 = (j : ℤ) + 1 := rfl

/-- `X` for the upper square `R⁺ = [0, 2j + 1] × [j + 1, 3j + 2]` with `S = [0, j] × [j + 1, 2j + 1]`
at its bottom-left, joined to the top side of `R⁺`. [folklore] -/
def upperJoinedCrossing : Set (BondConfig (LatticeModels.Site 2)) :=
  joinedCrossing (zdShiftIso (upShift j) '' ↑(rectangle j j))
    (zdShiftIso (upShift j) '' ↑(rectangle (2 * j + 1) (2 * j + 1)))
    (zdShiftIso (upShift j) '' ↑(leftSide j j)) (zdShiftIso (upShift j) '' ↑(rightSide j j))
    (zdShiftIso (upShift j) '' ↑(topSide (2 * j + 1) (2 * j + 1)))

/-- `X'` for the lower square `R⁻ = [0, 2j + 1] × [0, 2j + 1]` with the same `S` at its top-left,
joined to the bottom side of `R⁻` (the reflection of the standard position in `x₁ = j + ½`). [folklore] -/
def lowerJoinedCrossing : Set (BondConfig (LatticeModels.Site 2)) :=
  joinedCrossing (reflY (2 * j + 1) '' ↑(rectangle j j)) (reflY (2 * j + 1) '' ↑(rectangle (2 * j + 1) (2 * j + 1)))
    (reflY (2 * j + 1) '' ↑(leftSide j j)) (reflY (2 * j + 1) '' ↑(rightSide j j))
    (reflY (2 * j + 1) '' ↑(topSide (2 * j + 1) (2 * j + 1)))

/-- The vertical crossing of the middle square `S = [0, j] × [j + 1, 2j + 1]`. [folklore] -/
def midTBCrossing : Set (BondConfig (LatticeModels.Site 2)) :=
  openCrossing (zdShiftIso (upShift j) '' ↑(rectangle j j))
    (zdShiftIso (upShift j) '' ↑(bottomSide j j)) (zdShiftIso (upShift j) '' ↑(topSide j j))

variable {j}

/-- Membership in the reflected square: `ρ '' [0, j]² = [0, j] × [j + 1, 2j + 1]`. [folklore] -/
theorem mem_image_reflY_rectangle_iff {z : LatticeModels.Site 2} :
    z ∈ reflY (2 * j + 1) '' (↑(rectangle j j) : Set (LatticeModels.Site 2)) ↔
      0 ≤ z 0 ∧ z 0 ≤ j ∧ (j : ℤ) + 1 ≤ z 1 ∧ z 1 ≤ 2 * j + 1 := by
  rw [mem_image_reflY_iff, Finset.mem_coe, mem_rectangle_iff, reflY_apply_zero, reflY_apply_one]
  omega

/-- Membership in the shifted square: `[0, j]² + (0, j + 1) = [0, j] × [j + 1, 2j + 1]`. [folklore] -/
theorem mem_image_shift_rectangle_iff {z : LatticeModels.Site 2} :
    z ∈ zdShiftIso (upShift j) '' (↑(rectangle j j) : Set (LatticeModels.Site 2)) ↔
      0 ≤ z 0 ∧ z 0 ≤ j ∧ (j : ℤ) + 1 ≤ z 1 ∧ z 1 ≤ 2 * j + 1 := by
  rw [image_zdShiftIso, mem_image_add_rectangle, upShift_apply_zero, upShift_apply_one]
  omega

/-- The two descriptions of the middle square agree. [folklore] -/
theorem image_reflY_rectangle_eq :
    reflY (2 * j + 1) '' (↑(rectangle j j) : Set (LatticeModels.Site 2)) = zdShiftIso (upShift j) '' ↑(rectangle j j) := by
  ext z; rw [mem_image_reflY_rectangle_iff, mem_image_shift_rectangle_iff]

/-- **Gluing for Corollary 5** (Bollobás–Riordan 2006, Ch. 3, proof of Cor. 5, Figure 6,
transposed): if `X⁺`, `X⁻` and `V(S)` occur (for a lattice configuration), the open vertical
crossing of `S` meets both horizontal crossings of `S`, which are joined to the top of `R⁺` and to
the bottom of `R⁻`; hence `R⁺ ∪ R⁻ = [0, 2j + 1] × [0, 3j + 2]` has an open vertical crossing.
[cite: BollobasRiordanPercolation2006, Ch. 3, proof of Corollary 5] -/
theorem tbCrossing_of_upperJoinedCrossing_lowerJoinedCrossing_midTBCrossing {ω : BondConfig (LatticeModels.Site 2)} (hω : ω ⊆ (LatticeModels.zdGraph 2).edgeSet)
    (hup : ω ∈ upperJoinedCrossing j) (hlow : ω ∈ lowerJoinedCrossing j) (hV : ω ∈ midTBCrossing j) :
    ω ∈ tbCrossing (2 * j + 1) (3 * j + 2) := by
  classical
  set S' : Set (LatticeModels.Site 2) := zdShiftIso (upShift j) '' ↑(rectangle j j) with hS'
  set Big : Set (LatticeModels.Site 2) := ↑(rectangle (2 * j + 1) (3 * j + 2)) with hBig
  have hmemS' : ∀ z : LatticeModels.Site 2, z ∈ S' ↔ 0 ≤ z 0 ∧ z 0 ≤ j ∧ (j : ℤ) + 1 ≤ z 1 ∧ z 1 ≤ 2 * j + 1 :=
    fun z => mem_image_shift_rectangle_iff
  have hmemBig : ∀ z : LatticeModels.Site 2, z ∈ Big ↔ 0 ≤ z 0 ∧ z 0 ≤ 2 * j + 1 ∧ 0 ≤ z 1 ∧ z 1 ≤ 3 * j + 2 := by
    intro z; rw [hBig, Finset.mem_coe, mem_rectangle_iff]; push_cast; tauto
  have hS'Big : S' ⊆ Big := fun z hz => by rw [hmemS'] at hz; rw [hmemBig]; omega
  have hRupBig : zdShiftIso (upShift j) '' (↑(rectangle (2 * j + 1) (2 * j + 1)) : Set (LatticeModels.Site 2)) ⊆ Big := by
    intro z hz
    rw [image_zdShiftIso, mem_image_add_rectangle, upShift_apply_zero, upShift_apply_one] at hz
    rw [hmemBig]; omega
  have hRlowBig : reflY (2 * j + 1) '' (↑(rectangle (2 * j + 1) (2 * j + 1)) : Set (LatticeModels.Site 2)) ⊆ Big := by
    intro z hz
    rw [mem_image_reflY_iff, Finset.mem_coe, mem_rectangle_iff, reflY_apply_zero, reflY_apply_one] at hz
    rw [hmemBig]; omega
  -- unpack the three events
  obtain ⟨a₁, ha₁, b₁, hb₁, t₁, ht₁, hab₁, hat₁⟩ := hup
  obtain ⟨a₂, ha₂, b₂, hb₂, t₂, ht₂, hab₂, hat₂⟩ := hlow
  obtain ⟨c, hc, d, hd, hcd⟩ := hV
  rw [image_zdShiftIso, mem_image_add_leftSide, upShift_apply_zero, upShift_apply_one] at ha₁
  rw [image_zdShiftIso, mem_image_add_rightSide, upShift_apply_zero, upShift_apply_one] at hb₁
  rw [image_zdShiftIso, mem_image_add_topSide, upShift_apply_zero, upShift_apply_one] at ht₁
  rw [image_zdShiftIso, mem_image_add_bottomSide, upShift_apply_zero, upShift_apply_one] at hc
  rw [image_zdShiftIso, mem_image_add_topSide, upShift_apply_zero, upShift_apply_one] at hd
  simp only [mem_image_reflY_iff, Finset.mem_coe, leftSide, rightSide, topSide, Finset.mem_filter,
    mem_rectangle_iff, reflY_apply_zero, reflY_apply_one] at ha₂ hb₂ ht₂
  rw [image_reflY_rectangle_eq] at hab₂
  -- walks
  obtain ⟨π₁, hπ₁S, hπ₁ω⟩ := exists_walk_of_mem_openConnIn hω hab₁
  obtain ⟨π₂, hπ₂S, hπ₂ω⟩ := exists_walk_of_mem_openConnIn hω hab₂
  obtain ⟨Q, hQS, hQω⟩ := exists_walk_of_mem_openConnIn hω hcd
  have hbox : ∀ {x y : LatticeModels.Site 2} (P : (LatticeModels.zdGraph 2).Walk x y), (∀ z ∈ P.support, z ∈ S') →
      ∀ z ∈ P.support, (0 : ℤ) ≤ z 0 ∧ z 0 ≤ j ∧ (j : ℤ) + 1 ≤ z 1 ∧ z 1 ≤ 2 * j + 1 :=
    fun P hP z hz => (hmemS' z).1 (hP z hz)
  obtain ⟨w₁, hw₁π, hw₁Q⟩ := exists_mem_support_of_crossing (L := 0) (R := j) (B := (j : ℤ) + 1)
    (T := 2 * j + 1) π₁ Q (hbox π₁ hπ₁S) (hbox Q hQS) ha₁.2 (by rw [hb₁.2]; ring) hc.2
    (by rw [hd.2]; ring)
  obtain ⟨w₂, hw₂π, hw₂Q⟩ := exists_mem_support_of_crossing (L := 0) (R := j) (B := (j : ℤ) + 1)
    (T := 2 * j + 1) π₂ Q (hbox π₂ hπ₂S) (hbox Q hQS) ha₂.2 hb₂.2 hc.2 (by rw [hd.2]; ring)
  -- the chain `t₂ ↔ a₂ ↔ w₂ ↔ w₁ ↔ a₁ ↔ t₁` inside the big rectangle
  have c1 : ω ∈ openConnIn Big t₂ a₂ := openConnIn_mono hRlowBig _ _ (by rw [openConnIn_comm]; exact hat₂)
  have c2 : ω ∈ openConnIn Big a₂ w₂ :=
    openConnIn_mono hS'Big _ _ (mem_openConnIn_of_mem_support π₂ hπ₂S hπ₂ω hw₂π)
  have c3 : ω ∈ openConnIn Big w₂ w₁ :=
    openConnIn_mono hS'Big _ _ (PlanarDuality.openConnIn_trans
      (by rw [openConnIn_comm]; exact mem_openConnIn_of_mem_support Q hQS hQω hw₂Q)
      (mem_openConnIn_of_mem_support Q hQS hQω hw₁Q))
  have c4 : ω ∈ openConnIn Big w₁ a₁ :=
    openConnIn_mono hS'Big _ _ (by rw [openConnIn_comm]; exact mem_openConnIn_of_mem_support π₁ hπ₁S hπ₁ω hw₁π)
  have c5 : ω ∈ openConnIn Big a₁ t₁ := openConnIn_mono hRupBig _ _ hat₁
  refine ⟨t₂, ?_, t₁, ?_, PlanarDuality.openConnIn_trans (PlanarDuality.openConnIn_trans (PlanarDuality.openConnIn_trans
    (PlanarDuality.openConnIn_trans c1 c2) c3) c4) c5⟩
  · simp only [Finset.mem_coe, bottomSide, Finset.mem_filter, mem_rectangle_iff]
    push_cast; omega
  · simp only [Finset.mem_coe, topSide, Finset.mem_filter, mem_rectangle_iff]
    push_cast at ht₁ ⊢; omega

/-- `P(X⁺) = P(X)` (translation invariance). [folklore] -/
theorem real_upperJoinedCrossing (p : unitInterval) :
    (bondPercolation (LatticeModels.zdGraph 2) p).real (upperJoinedCrossing j) =
      (bondPercolation (LatticeModels.zdGraph 2) p).real (stdJoinedCrossing j (2 * j + 1)) :=
  real_joinedCrossing_image (zdShiftIso (upShift j)) p _ _ _ _ _

/-- `P(X⁻) = P(X)` (reflection invariance). [folklore] -/
theorem real_lowerJoinedCrossing (p : unitInterval) :
    (bondPercolation (LatticeModels.zdGraph 2) p).real (lowerJoinedCrossing j) =
      (bondPercolation (LatticeModels.zdGraph 2) p).real (stdJoinedCrossing j (2 * j + 1)) :=
  real_joinedCrossing_image (reflY (2 * j + 1)) p _ _ _ _ _

/-- `P(V(S)) = crossingProb p j j` (translation invariance and transposition). [folklore] -/
theorem real_midTBCrossing (p : unitInterval) :
    (bondPercolation (LatticeModels.zdGraph 2) p).real (midTBCrossing j) = crossingProb p j j := by
  rw [midTBCrossing, bondPercolation_real_image (zdShiftIso (upShift j)) p]
  exact real_tbCrossing p j j

/-- `X⁺` is a local increasing event. [folklore] -/
theorem isLocalEvent_upperJoinedCrossing : IsLocalEvent (upperJoinedCrossing j) := by
  rw [upperJoinedCrossing, ← Finset.coe_image, ← Finset.coe_image]; exact isLocalEvent_joinedCrossing _ _ _ _ _

/-- `X⁻` is a local increasing event. [folklore] -/
theorem isLocalEvent_lowerJoinedCrossing : IsLocalEvent (lowerJoinedCrossing j) := by
  rw [lowerJoinedCrossing, ← Finset.coe_image, ← Finset.coe_image]; exact isLocalEvent_joinedCrossing _ _ _ _ _

/-- `V(S)` is a local increasing event. [folklore] -/
theorem isLocalEvent_midTBCrossing : IsLocalEvent (midTBCrossing j) := by
  rw [midTBCrossing, ← Finset.coe_image]; exact isLocalEvent_openCrossing _ _ _

/-- **Bollobás–Riordan 2006, Ch. 3, Corollary 5, before specialising to `p = 1/2`** (transposed
and in `crossingProb` indices): with `h = crossingProb p`,
`(h(2j+1, 2j+1) · h(j, j) / 2)² · h(j, j) ≤ h(3j+2, 2j+1)`, i.e.
`P(H(3n × 2n)) ≥ P(X)² P(V(S)) ≥ (P(H(R)) P(V(S))/2)² P(H(S))` for the `2n × 2n` squares
`R⁺`, `R⁻` and the `n × n` square `S` between them (Harris's lemma twice, Lemma 4 twice, and the
symmetries of `P_p`). [cite: BollobasRiordanPercolation2006, Ch. 3, Corollary 5] -/
theorem BollobasRiordan2006_cor5_general (p : unitInterval) (j : ℕ) :
    (crossingProb p (2 * j + 1) (2 * j + 1) * crossingProb p j j / 2) ^ 2 * crossingProb p j j ≤
      crossingProb p (3 * j + 2) (2 * j + 1) := by
  classical
  have hX : crossingProb p (2 * j + 1) (2 * j + 1) * crossingProb p j j / 2 ≤
      (bondPercolation (LatticeModels.zdGraph 2) p).real (stdJoinedCrossing j (2 * j + 1)) := by
    have := BollobasRiordan2006_lemma4_holds p j (2 * j + 1) (by omega)
    rwa [real_tbCrossing] at this
  have h0 : ∀ a b : ℕ, (0 : ℝ) ≤ crossingProb p a b := fun a b => (crossingProb_mem_Icc _ _ _).1
  -- Harris twice
  have h12 : (bondPercolation (LatticeModels.zdGraph 2) p).real (upperJoinedCrossing j) * (bondPercolation (LatticeModels.zdGraph 2) p).real (lowerJoinedCrossing j) ≤ (bondPercolation (LatticeModels.zdGraph 2) p).real (upperJoinedCrossing j ∩ lowerJoinedCrossing j) :=
    Percolation.Literature.harris_fkg_local (LatticeModels.zdGraph 2) p (isUpperSet_joinedCrossing _ _ _ _ _) (isUpperSet_joinedCrossing _ _ _ _ _)
      isLocalEvent_upperJoinedCrossing isLocalEvent_lowerJoinedCrossing
  have h123 : (bondPercolation (LatticeModels.zdGraph 2) p).real (upperJoinedCrossing j ∩ lowerJoinedCrossing j) * (bondPercolation (LatticeModels.zdGraph 2) p).real (midTBCrossing j) ≤ (bondPercolation (LatticeModels.zdGraph 2) p).real (upperJoinedCrossing j ∩ lowerJoinedCrossing j ∩ midTBCrossing j) :=
    Percolation.Literature.harris_fkg_local (LatticeModels.zdGraph 2) p ((isUpperSet_joinedCrossing _ _ _ _ _).inter (isUpperSet_joinedCrossing _ _ _ _ _))
      (isUpperSet_openCrossing _ _ _) (isLocalEvent_upperJoinedCrossing.inter isLocalEvent_lowerJoinedCrossing) isLocalEvent_midTBCrossing
  have hsub : (bondPercolation (LatticeModels.zdGraph 2) p).real (upperJoinedCrossing j ∩ lowerJoinedCrossing j ∩ midTBCrossing j) ≤ crossingProb p (3 * j + 2) (2 * j + 1) := by
    rw [← real_tbCrossing p (3 * j + 2) (2 * j + 1)]
    refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_)
    filter_upwards [ae_subset_edgeSet (LatticeModels.zdGraph 2) p] with ω hω hmem
    exact tbCrossing_of_upperJoinedCrossing_lowerJoinedCrossing_midTBCrossing hω hmem.1.1 hmem.1.2 hmem.2
  have hXX : (crossingProb p (2 * j + 1) (2 * j + 1) * crossingProb p j j / 2) ^ 2 ≤
      (bondPercolation (LatticeModels.zdGraph 2) p).real (upperJoinedCrossing j) * (bondPercolation (LatticeModels.zdGraph 2) p).real (lowerJoinedCrossing j) := by
    rw [real_upperJoinedCrossing, real_lowerJoinedCrossing, ← sq]
    exact pow_le_pow_left₀ (div_nonneg (mul_nonneg (h0 _ _) (h0 _ _)) (by norm_num)) hX 2
  calc (crossingProb p (2 * j + 1) (2 * j + 1) * crossingProb p j j / 2) ^ 2 * crossingProb p j j
      ≤ (bondPercolation (LatticeModels.zdGraph 2) p).real (upperJoinedCrossing j) * (bondPercolation (LatticeModels.zdGraph 2) p).real (lowerJoinedCrossing j) * (bondPercolation (LatticeModels.zdGraph 2) p).real (midTBCrossing j) := by
        rw [real_midTBCrossing]; exact mul_le_mul_of_nonneg_right hXX (h0 j j)
    _ ≤ (bondPercolation (LatticeModels.zdGraph 2) p).real (upperJoinedCrossing j ∩ lowerJoinedCrossing j) * (bondPercolation (LatticeModels.zdGraph 2) p).real (midTBCrossing j) := mul_le_mul_of_nonneg_right h12 measureReal_nonneg
    _ ≤ (bondPercolation (LatticeModels.zdGraph 2) p).real (upperJoinedCrossing j ∩ lowerJoinedCrossing j ∩ midTBCrossing j) := h123
    _ ≤ crossingProb p (3 * j + 2) (2 * j + 1) := hsub

end Cor5

end

end Percolation.Literature

/-! ### Discharge of `BollobasRiordan2006_cor5`, of `rsw_lowerBound` and of `rsw_half` -/

namespace Percolation.Literature

open MeasureTheory LatticeModels PlanarDuality

noncomputable section

/-- **Discharge of `BollobasRiordan2006_cor5`** (Bollobás–Riordan, *Percolation* (2006), Ch. 3,
Corollary 5): `h(3n, 2n) ≥ 2⁻⁷` at `p = 1/2` for all `n ≥ 1`, i.e.
`crossingProb ½ (3j + 2) (2j + 1) ≥ 2⁻⁷`; from `BollobasRiordan2006_cor5_general` and
`h(N, N) ≥ 1/2` (Cor. 3(iii), `half_le_crossingProb_self` with `crossingProb_half_succ_self_holds`):
`((1/2)(1/2)/2)² (1/2) = 2⁻⁷`. [cite: BollobasRiordanPercolation2006, Ch. 3, Corollary 5] -/
theorem BollobasRiordan2006_cor5_holds : BollobasRiordan2006_cor5 := by
  intro j
  have h := BollobasRiordan2006_cor5_general half j
  have h1 : 1 / 2 ≤ crossingProb half (2 * j + 1) (2 * j + 1) :=
    half_le_crossingProb_self crossingProb_half_succ_self_holds _
  have h2 : 1 / 2 ≤ crossingProb half j j :=
    half_le_crossingProb_self crossingProb_half_succ_self_holds _
  have h3 : (1 / 2 : ℝ) * (1 / 2) / 2 ≤ crossingProb half (2 * j + 1) (2 * j + 1) * crossingProb half j j / 2 := by
    have := mul_le_mul h1 h2 (by norm_num) (by linarith)
    linarith
  calc (2 : ℝ)⁻¹ ^ 7 = ((1 / 2) * (1 / 2) / 2) ^ 2 * (1 / 2) := by norm_num
    _ ≤ (crossingProb half (2 * j + 1) (2 * j + 1) * crossingProb half j j / 2) ^ 2 *
          crossingProb half j j :=
        mul_le_mul (pow_le_pow_left₀ (by norm_num) h3 2) h2 (by norm_num) (sq_nonneg _)
    _ ≤ crossingProb half (3 * j + 2) (2 * j + 1) := h

/-- **Discharge of `rsw_lowerBound`** (Bollobás–Riordan 2006, Ch. 3, eq. (3); Grimmett 1999,
§11.7): `h(kn, n) ≥ h_k > 0` at `p = 1/2`, from Corollary 5, the gluing inequality (2) and
Corollary 3(ii) (`rsw_lowerBound_of_glue` of `RSW.lean` fed with the three discharges). [cite: BollobasRiordanPercolation2006, Ch. 3, eq. (3)] -/
theorem rsw_lowerBound_holds : rsw_lowerBound :=
  rsw_lowerBound_of_glue BollobasRiordan2006_cor5_holds crossingProb_glue_holds
    crossingProb_half_succ_self_holds

/-- [cite: GrimmettPercolation1999, §11.7, Thm (11.70)] [cite: BollobasRiordanPercolation2006, Ch. 3, eq. (3) and Corollary 3(i)] -/
theorem rsw_half_holds : rsw_half :=
  rsw_half_of_lowerBound rsw_lowerBound_holds crossingProb_add_crossingProb_symm_holds

end

end Percolation.Literature
