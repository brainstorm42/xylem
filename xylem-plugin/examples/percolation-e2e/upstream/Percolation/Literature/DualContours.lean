import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.ZMod.Basic
import Percolation.Literature.Basic
import Percolation.Literature.Crossings
import Percolation.Util.Linter

/-!
# Dual contours around finite clusters of bond percolation on `ℤ²` (Peierls' argument)

This file supplies
the planar combinatorics behind the upper bound `p_c(2) < 1` in Grimmett, *Percolation* (2nd ed.,
1999), §1.4, Theorem (1.10) — the step that Grimmett describes but does not prove ("It is somewhat
tedious to formulate and prove such a statement with complete rigour", p. 17, deferring to
Kesten 1982, p. 386): **if the open cluster of the origin is finite, then the origin is surrounded
by a closed circuit of the dual lattice**, in the quantitative form consumed by the Peierls
estimate (1.17)–(1.18): the circuit has some length `n ≥ 1`, passes through a dual vertex
`(k + ½, ½)` with `0 ≤ k < n`, and consists of `n` distinct closed edges
(`Percolation.Literature.Contour.exists_dualCircuit`). Everything here is proved.

## Vocabulary

* `stepVec`, `wordPos`: the `2d` unit steps `± eᵢ` of `ℤ^d` and the displacement of a step word
  `w : Fin n → Fin d × Bool` (also used for path counting on `ℤ^d`).
* `Contour.IsEven Z`: every plaquette has an even number of sides in the finite edge set `Z`
  (a dual `𝔽₂`-cycle); the edge boundary `edgeBoundary (zdGraph 2) hC.toFinset` of a finite
  vertex set `C` (`LatticeGraph.lean`: the edges with exactly one endpoint in `C`) is even
  (`isEven_bdry`).
* `Contour.rowPar`, `rightPar`, `leftPar`: parities (in `ZMod 2`, as `finsum`s) of the numbers of
  horizontal `Z`-edges in a row, resp. on the two halves of row `0`.

## The argument (an `𝔽₂` version of "finite cluster ⇒ surrounding dual circuit")

1. Row lemma (`IsEven.rowPar_eq_zero`): summing the plaquette relations along a row shows that
   consecutive rows of an even set carry equally many horizontal edges mod 2; far rows carry
   none, so every row is even. Hence an even set crossing the positive `x`-axis an odd number of
   times also crosses the negative `x`-axis (`IsEven.leftPar_eq`).
2. The boundary of a finite `C ∋ 0` crosses the positive `x`-axis an odd number of times
   (`rightPar_bdry`, telescoping of the coboundary along the axis).
3. Cycle extraction (`exists_isSimpleClosed`): inside an even set one can walk on the dual
   lattice without ever reversing (each plaquette has an even number, hence `≠ 1`, of usable
   sides); the walk stays in a finite set of plaquettes, so it revisits one, and the first
   revisit closes a non-backtracking simple dual cycle, whose edge set is again even
   (`IsSimpleClosed.isEven`: a plaquette on the cycle has exactly its outgoing and reversed
   incoming sides in it) and has exactly `n` edges (`IsSimpleClosed.card_cycEdges`).
4. Induction on the number of edges (`exists_cycle_rightPar`): peel off cycles; parities are
   additive, so some peeled cycle crosses the positive axis an odd number of times.
5. That cycle crosses the axis at some `{(t,0),(t+1,0)}`, `t ≥ 0`, and (by 1) at some
   `{(s,0),(s+1,0)}`, `s < 0`; a dual walk moves the first coordinate by at most one per step,
   so `t < t - s ≤ n` (`exists_dualCircuit`).

## References

* G. Grimmett, *Percolation*, 2nd ed., Grundlehren 321, Springer 1999: §1.4, Theorem (1.10) and
  its proof pp. 15–18 (dual lattice p. 16, Fig. 1.5–1.6, the counting bound (1.17)
  `ρ(n) ≤ n σ(n-1)`, the Peierls sum (1.18)).
* H. Kesten, *Percolation Theory for Mathematicians*, Birkhäuser 1982, p. 386 (the rigorous
  circuit lemma Grimmett cites; not followed here — the `𝔽₂` argument above replaces it).
-/

noncomputable section

namespace Percolation.Literature

open LatticeModels

variable {d : ℕ}

/-! ### Step words on `ℤ^d` -/

/-- The unit step of `ℤ^d` in coordinate direction `a.1`, forwards if `a.2 = true` and backwards
otherwise (the `2d` steps `± eᵢ` of the nearest-neighbour lattice; Grimmett 1999, §1.4 p. 15,
"each new step … has at most `2d - 1` choices"). [cite: GrimmettPercolation1999, §1.4 p. 15] -/
def stepVec (a : Fin d × Bool) : Site d :=
  if a.2 then Pi.single a.1 1 else -Pi.single a.1 1

/-- Adjacency in `ℤ^d` iff the two sites differ by one of the `2d` unit steps.
[cite: GrimmettPercolation1999, §1.4 p. 15] -/
theorem zdGraph_adj_iff_stepVec (x y : Site d) :
    (zdGraph d).Adj x y ↔ ∃ a : Fin d × Bool, y = x + stepVec a := by
  rw [zdGraph_adj_iff]
  constructor
  · rintro ⟨i, h | h⟩
    · exact ⟨(i, true), by simpa [stepVec] using h⟩
    · exact ⟨(i, false), by simp [stepVec, h]⟩
  · rintro ⟨⟨i, b⟩, h⟩
    cases b
    · exact ⟨i, Or.inr (by simp [stepVec, h])⟩
    · exact ⟨i, Or.inl (by simpa [stepVec] using h)⟩

/-- The displacement after the first `k` steps of the word `w ∈ ({1,…,d} × {±})ⁿ` (constant after
`n` steps): a path or self-avoiding walk of `𝕃^d` from the origin is coded by such a word
(Grimmett 1999, §1.4 p. 15, `σ(n) ≤ 2d(2d-1)^{n-1}`). [cite: GrimmettPercolation1999, §1.4 p. 15] -/
def wordPos {n : ℕ} (w : Fin n → Fin d × Bool) (k : ℕ) : Site d :=
  ∑ i ∈ Finset.range k, if h : i < n then stepVec (w ⟨i, h⟩) else 0

/-- No steps, no displacement. [folklore] -/
@[simp] theorem wordPos_zero {n : ℕ} (w : Fin n → Fin d × Bool) : wordPos w 0 = 0 := by
  simp [wordPos]

/-- One more step adds its unit vector. [folklore] -/
theorem wordPos_succ {n : ℕ} (w : Fin n → Fin d × Bool) {k : ℕ} (hk : k < n) :
    wordPos w (k + 1) = wordPos w k + stepVec (w ⟨k, hk⟩) := by
  simp [wordPos, Finset.sum_range_succ, hk]

/-! ### The dual lattice of `𝕃²` -/

/-- The dual lattice of `𝕃²` (Grimmett 1999, §1.4 p. 16 and Fig. 1.5): its vertices are the
plaquettes (unit squares) of `ℤ²`, the plaquette with lower-left corner `a` standing for the dual
vertex `a + (½, ½)`; two plaquettes sharing an edge of `𝕃²` are joined by the dual edge crossing
it. `crossedEdge a dir` is the edge of `𝕃²` crossed by the dual step from plaquette `a` in
direction `dir`: for the step `+eᵢ` it is the side `{a + eᵢ, a + eᵢ + eᵢ'}` and for `-eᵢ` the side
`{a, a + eᵢ'}` (`i' ≠ i` the other axis). [cite: GrimmettPercolation1999, §1.4 p. 16] -/
def crossedEdge (a : Site 2) (dir : Fin 2 × Bool) : Sym2 (Site 2) :=
  s((if dir.2 then a + Pi.single dir.1 1 else a),
    (if dir.2 then a + Pi.single dir.1 1 else a) + Pi.single dir.1.rev 1)

/-- Every crossed edge is an edge of `𝕃²`. [cite: GrimmettPercolation1999, §1.4 p. 16 ("one-one
correspondence between the edges of `𝕃²` and the edges of the dual")] -/
theorem crossedEdge_mem_edgeSet (a : Site 2) (dir : Fin 2 × Bool) :
    crossedEdge a dir ∈ (zdGraph 2).edgeSet := by
  rw [crossedEdge, SimpleGraph.mem_edgeSet, zdGraph_adj_iff]
  exact ⟨dir.1.rev, Or.inl rfl⟩

/-- The edges of `𝕃²` crossed by the dual walk that starts at plaquette `a` and follows the word
`w` (its `k`-th step goes from plaquette `a + wordPos w k` in direction `w k`).
[cite: GrimmettPercolation1999, §1.4 p. 17 (circuits of the dual)] -/
def dualEdges {n : ℕ} (a : Site 2) (w : Fin n → Fin 2 × Bool) : Finset (Sym2 (Site 2)) :=
  Finset.univ.image fun k : Fin n => crossedEdge (a + wordPos w k) (w k)

/-- The crossed edges of a dual walk are edges of `𝕃²`. [cite: GrimmettPercolation1999, §1.4 p. 16] -/
theorem dualEdges_subset_edgeSet {n : ℕ} (a : Site 2) (w : Fin n → Fin 2 × Bool) :
    (↑(dualEdges a w) : Set (Sym2 (Site 2))) ⊆ (zdGraph 2).edgeSet := by
  intro e he
  simp only [dualEdges, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at he
  obtain ⟨k, rfl⟩ := he
  exact crossedEdge_mem_edgeSet _ _

namespace Contour

/-! ### Coordinates on `ℤ²` -/

/-- The unit vector `e₀ = (1, 0)`. [folklore] -/
def ex : Site 2 := Pi.single 0 1
/-- The unit vector `e₁ = (0, 1)`. [folklore] -/
def ey : Site 2 := Pi.single 1 1

/-- The site `(i, j)`. [folklore] -/
def mk (i j : ℤ) : Site 2 := ![i, j]

/-- First coordinate of `mk`. [folklore] -/
@[simp] theorem mk_apply_zero (i j : ℤ) : mk i j 0 = i := rfl
/-- Second coordinate of `mk`. [folklore] -/
@[simp] theorem mk_apply_one (i j : ℤ) : mk i j 1 = j := rfl
/-- Coordinates of `e₀`. [folklore] -/
@[simp] theorem ex_apply_zero : ex 0 = 1 := rfl
/-- Coordinates of `e₀`. [folklore] -/
@[simp] theorem ex_apply_one : ex 1 = 0 := rfl
/-- Coordinates of `e₁`. [folklore] -/
@[simp] theorem ey_apply_zero : ey 0 = 0 := rfl
/-- Coordinates of `e₁`. [folklore] -/
@[simp] theorem ey_apply_one : ey 1 = 1 := rfl

/-- Sites of `ℤ²` are determined by their two coordinates. [folklore] -/
theorem site_ext {a b : Site 2} (h0 : a 0 = b 0) (h1 : a 1 = b 1) : a = b := by
  funext i; fin_cases i <;> assumption

/-- Translation by `e₀` in coordinates. [folklore] -/
@[simp] theorem mk_add_ex (i j : ℤ) : mk i j + ex = mk (i + 1) j := site_ext (by simp) (by simp)
/-- Translation by `e₁` in coordinates. [folklore] -/
@[simp] theorem mk_add_ey (i j : ℤ) : mk i j + ey = mk i (j + 1) := site_ext (by simp) (by simp)
/-- Translation by `-e₀` in coordinates. [folklore] -/
@[simp] theorem mk_sub_ex (i j : ℤ) : mk i j - ex = mk (i - 1) j := site_ext (by simp) (by simp)
/-- Translation by `-e₁` in coordinates. [folklore] -/
@[simp] theorem mk_sub_ey (i j : ℤ) : mk i j - ey = mk i (j - 1) := site_ext (by simp) (by simp)
/-- Translation by `-e₀` in coordinates. [folklore] -/
@[simp] theorem mk_add_neg_ex (i j : ℤ) : mk i j + -ex = mk (i - 1) j :=
  site_ext (by simp; ring) (by simp)
/-- Translation by `-e₁` in coordinates. [folklore] -/
@[simp] theorem mk_add_neg_ey (i j : ℤ) : mk i j + -ey = mk i (j - 1) :=
  site_ext (by simp) (by simp; ring)
/-- `mk` is injective. [folklore] -/
theorem mk_inj {i j i' j' : ℤ} : mk i j = mk i' j' ↔ i = i' ∧ j = j' :=
  ⟨fun h => ⟨by simpa using congrFun h 0, by simpa using congrFun h 1⟩,
    fun ⟨h0, h1⟩ => by rw [h0, h1]⟩

/-- The origin. [folklore] -/
@[simp] theorem mk_zero_zero : mk 0 0 = 0 := site_ext rfl rfl

/-- The step `+e₀`. [folklore] -/
@[simp] theorem stepVec_zero_true : stepVec ((0 : Fin 2), true) = ex := rfl
/-- The step `-e₀`. [folklore] -/
@[simp] theorem stepVec_zero_false : stepVec ((0 : Fin 2), false) = -ex := rfl
/-- The step `+e₁`. [folklore] -/
@[simp] theorem stepVec_one_true : stepVec ((1 : Fin 2), true) = ey := rfl
/-- The step `-e₁`. [folklore] -/
@[simp] theorem stepVec_one_false : stepVec ((1 : Fin 2), false) = -ey := rfl

/-- Each step changes the first coordinate by at most one. [folklore] -/
theorem abs_stepVec_apply_zero_le (dir : Fin 2 × Bool) : |stepVec dir 0| ≤ 1 := by
  obtain ⟨i, b⟩ := dir
  fin_cases i <;> cases b <;> simp

/-- Unit steps are non-zero. [folklore] -/
theorem stepVec_ne_zero (dir : Fin 2 × Bool) : stepVec dir ≠ 0 := by
  obtain ⟨i, b⟩ := dir
  intro h
  fin_cases i <;> cases b
  · simpa using congrFun h 0
  · simpa using congrFun h 0
  · simpa using congrFun h 1
  · simpa using congrFun h 1

/-- Reversal of a step direction. [folklore] -/
def rev (dir : Fin 2 × Bool) : Fin 2 × Bool := (dir.1, !dir.2)

/-- Reversal is an involution. [folklore] -/
@[simp] theorem rev_rev (dir : Fin 2 × Bool) : rev (rev dir) = dir := by
  simp [rev]

/-- Reversal has no fixed point. [folklore] -/
theorem rev_ne_self (dir : Fin 2 × Bool) : rev dir ≠ dir := by
  obtain ⟨i, b⟩ := dir; cases b <;> simp [rev]

/-- The reversed step is the opposite vector. [folklore] -/
@[simp] theorem stepVec_rev (dir : Fin 2 × Bool) : stepVec (rev dir) = -stepVec dir := by
  obtain ⟨i, b⟩ := dir
  fin_cases i <;> cases b <;> simp [rev]

/-! ### Horizontal and vertical edges -/

/-- The horizontal edge with left endpoint `a`. [folklore] -/
def hEdge (a : Site 2) : Sym2 (Site 2) := s(a, a + ex)
/-- The vertical edge with lower endpoint `a`. [folklore] -/
def vEdge (a : Site 2) : Sym2 (Site 2) := s(a, a + ey)

/-- A horizontal edge determines its left endpoint. [folklore] -/
@[simp] theorem hEdge_inj {a b : Site 2} : hEdge a = hEdge b ↔ a = b := by
  constructor
  · intro h
    rw [hEdge, hEdge, Sym2.eq_iff] at h
    rcases h with ⟨h, -⟩ | ⟨h1, h2⟩
    · exact h
    · exfalso
      have := congrFun h2 0
      rw [h1] at this
      simp at this
      omega
  · rintro rfl; rfl

/-- A vertical edge determines its lower endpoint. [folklore] -/
@[simp] theorem vEdge_inj {a b : Site 2} : vEdge a = vEdge b ↔ a = b := by
  constructor
  · intro h
    rw [vEdge, vEdge, Sym2.eq_iff] at h
    rcases h with ⟨h, -⟩ | ⟨h1, h2⟩
    · exact h
    · exfalso
      have := congrFun h2 1
      rw [h1] at this
      simp at this
      omega
  · rintro rfl; rfl

/-- Horizontal and vertical edges differ. [folklore] -/
theorem hEdge_ne_vEdge (a b : Site 2) : hEdge a ≠ vEdge b := by
  intro h
  rw [hEdge, vEdge, Sym2.eq_iff] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have := congrFun h2 0
    rw [h1] at this
    simp at this
  · have := congrFun h2 0
    rw [h1] at this
    simp at this

/-- The edge crossed by the dual step `+e₀`: the right side of the plaquette. [folklore] -/
@[simp] theorem crossedEdge_zero_true (a : Site 2) : crossedEdge a (0, true) = vEdge (a + ex) := rfl
/-- The edge crossed by the dual step `-e₀`: the left side of the plaquette. [folklore] -/
@[simp] theorem crossedEdge_zero_false (a : Site 2) : crossedEdge a (0, false) = vEdge a := rfl
/-- The edge crossed by the dual step `+e₁`: the top side of the plaquette. [folklore] -/
@[simp] theorem crossedEdge_one_true (a : Site 2) : crossedEdge a (1, true) = hEdge (a + ey) := rfl
/-- The edge crossed by the dual step `-e₁`: the bottom side of the plaquette. [folklore] -/
@[simp] theorem crossedEdge_one_false (a : Site 2) : crossedEdge a (1, false) = hEdge a := rfl

/-- The edge crossed from `a` in direction `dir` is the edge crossed back from the neighbouring
plaquette. [folklore] -/
theorem crossedEdge_step_rev (a : Site 2) (dir : Fin 2 × Bool) :
    crossedEdge (a + stepVec dir) (rev dir) = crossedEdge a dir := by
  obtain ⟨i, b⟩ := dir
  fin_cases i <;> cases b <;> simp [rev]

/-- **Two plaquettes per edge**: the dual steps crossing a given edge of `𝕃²` are exactly a step
and its reversal. [folklore] -/
theorem crossedEdge_eq_iff {a a' : Site 2} {dir dir' : Fin 2 × Bool} :
    crossedEdge a dir = crossedEdge a' dir' ↔
      (a' = a ∧ dir' = dir) ∨ (a' = a + stepVec dir ∧ dir' = rev dir) := by
  constructor
  · intro h
    obtain ⟨i, b⟩ := dir
    obtain ⟨i', b'⟩ := dir'
    fin_cases i <;> fin_cases i' <;> cases b <;> cases b' <;>
      simp only [crossedEdge_zero_true, crossedEdge_zero_false, crossedEdge_one_true,
        crossedEdge_one_false, hEdge_inj, vEdge_inj, add_left_inj, Fin.zero_eta, Fin.mk_one,
        hEdge_ne_vEdge, (hEdge_ne_vEdge _ _).symm] at h <;>
      simp [rev, h]
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact (crossedEdge_step_rev a dir).symm

/-- The sum over the four sides of plaquette `a` of a function of edges. [folklore] -/
theorem sum_dirs (f : Sym2 (Site 2) → ZMod 2) (a : Site 2) :
    ∑ dir : Fin 2 × Bool, f (crossedEdge a dir) =
      f (hEdge a) + f (hEdge (a + ey)) + f (vEdge a) + f (vEdge (a + ex)) := by
  rw [Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool, Fintype.sum_bool]
  simp only [crossedEdge_zero_true, crossedEdge_zero_false, crossedEdge_one_true,
    crossedEdge_one_false]
  ring

/-! ### Parity bookkeeping in `ZMod 2` -/

/-- `x + x = 0` in `ZMod 2`. [folklore] -/
theorem zmod2_add_self : ∀ x : ZMod 2, x + x = 0 := by
  decide

/-- `ZMod 2 = {0, 1}`. [folklore] -/
theorem zmod2_eq_zero_or_one : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by
  decide

/-- Indicator (in `ZMod 2`) of membership of an edge in `Z`. [folklore] -/
def ind (Z : Finset (Sym2 (Site 2))) (e : Sym2 (Site 2)) : ZMod 2 := if e ∈ Z then 1 else 0

/-- Indicators are additive along `Z ⊆ E ↦ E \\ Z` in characteristic two. [folklore] -/
theorem ind_sdiff {E Z : Finset (Sym2 (Site 2))} (h : Z ⊆ E) (e : Sym2 (Site 2)) :
    ind (E \ Z) e = ind E e + ind Z e := by
  unfold ind
  by_cases hZ : e ∈ Z
  · have hE : e ∈ E := h hZ
    simp [hZ, hE, zmod2_add_self]
  · by_cases hE : e ∈ E <;> simp [hZ, hE]

/-- A finite edge set is *even* if every plaquette has an even number of sides in it (it is a
cycle of the dual lattice in the `𝔽₂` sense). [folklore] -/
def IsEven (Z : Finset (Sym2 (Site 2))) : Prop :=
  ∀ a : Site 2,
    ind Z (hEdge a) + ind Z (hEdge (a + ey)) + ind Z (vEdge a) + ind Z (vEdge (a + ex)) = 0

/-- Removing an even subset from an even set leaves an even set. [folklore] -/
theorem IsEven.sdiff {E Z : Finset (Sym2 (Site 2))} (hE : IsEven E) (hZ : IsEven Z) (h : Z ⊆ E) :
    IsEven (E \ Z) := by
  intro a
  have h1 := hE a
  have h2 := hZ a
  simp only [ind_sdiff h]
  linear_combination h1 + h2

/-- Evenness in terms of the number of sides of a plaquette lying in `Z`. [folklore] -/
theorem IsEven.natCast_card_filter {Z : Finset (Sym2 (Site 2))} (hZ : IsEven Z) (a : Site 2) :
    ((Finset.univ.filter fun dir => crossedEdge a dir ∈ Z).card : ZMod 2) = 0 := by
  rw [Finset.natCast_card_filter, sum_dirs (fun e => if e ∈ Z then 1 else 0) a]
  exact hZ a

/-- An even set meets every plaquette in an even number of sides. [folklore] -/
theorem IsEven.even_card_filter {Z : Finset (Sym2 (Site 2))} (hZ : IsEven Z) (a : Site 2) :
    Even (Finset.univ.filter fun dir => crossedEdge a dir ∈ Z).card :=
  (ZMod.natCast_eq_zero_iff_even).1 (hZ.natCast_card_filter a)

/-- Evenness from side counts. [folklore] -/
theorem isEven_of_card {Z : Finset (Sym2 (Site 2))}
    (h : ∀ a, ((Finset.univ.filter fun dir => crossedEdge a dir ∈ Z).card : ZMod 2) = 0) :
    IsEven Z := by
  intro a
  have := h a
  rwa [Finset.natCast_card_filter, sum_dirs (fun e => if e ∈ Z then 1 else 0) a] at this

/-! ### Row parities -/

/-- The parity of the number of horizontal `Z`-edges in row `j`. [folklore] -/
def rowPar (Z : Finset (Sym2 (Site 2))) (j : ℤ) : ZMod 2 := ∑ᶠ s : ℤ, ind Z (hEdge (mk s j))

/-- Preimages of a finite edge set under an injective parametrisation are finite. [folklore] -/
theorem finite_setOf_mem (Z : Finset (Sym2 (Site 2))) {g : ℤ → Sym2 (Site 2)}
    (hg : Function.Injective g) : {s | g s ∈ Z}.Finite :=
  Set.Finite.preimage hg.injOn Z.finite_toSet

/-- Indicators of a finite edge set along an injective parametrisation have finite support.
[folklore] -/
theorem hasFiniteSupport_ind (Z : Finset (Sym2 (Site 2))) {g : ℤ → Sym2 (Site 2)}
    (hg : Function.Injective g) : Function.HasFiniteSupport fun s => ind Z (g s) := by
  refine (finite_setOf_mem Z hg).subset ?_
  intro s hs
  by_contra h
  simp [ind, if_neg (show g s ∉ Z from h)] at hs

/-- Horizontal edges of a row are parametrised injectively by their column. [folklore] -/
theorem hEdge_mk_injective_left (j : ℤ) : Function.Injective fun s : ℤ => hEdge (mk s j) := by
  intro s t h; simpa [mk_inj] using h

/-- Vertical edges of a row are parametrised injectively by their column. [folklore] -/
theorem vEdge_mk_injective_left (j : ℤ) : Function.Injective fun s : ℤ => vEdge (mk s j) := by
  intro s t h; simpa [mk_inj] using h

/-- Consecutive rows have equal parity for an even edge set. [folklore] -/
theorem IsEven.rowPar_succ {Z : Finset (Sym2 (Site 2))} (hZ : IsEven Z) (j : ℤ) :
    rowPar Z (j + 1) = rowPar Z j := by
  have h1 : Function.HasFiniteSupport fun s : ℤ => ind Z (hEdge (mk s j)) :=
    hasFiniteSupport_ind Z (hEdge_mk_injective_left j)
  have h2 : Function.HasFiniteSupport fun s : ℤ => ind Z (hEdge (mk s (j + 1))) :=
    hasFiniteSupport_ind Z (hEdge_mk_injective_left (j + 1))
  have h3 : Function.HasFiniteSupport fun s : ℤ => ind Z (vEdge (mk s j)) :=
    hasFiniteSupport_ind Z (vEdge_mk_injective_left j)
  have h4 : Function.HasFiniteSupport fun s : ℤ => ind Z (vEdge (mk (s + 1) j)) :=
    hasFiniteSupport_ind Z
      ((vEdge_mk_injective_left j).comp fun s t (h : s + 1 = t + 1) => by omega)
  have key : ∑ᶠ s : ℤ, (ind Z (hEdge (mk s j)) + ind Z (hEdge (mk s (j + 1))) +
      ind Z (vEdge (mk s j)) + ind Z (vEdge (mk (s + 1) j))) = 0 := by
    apply finsum_eq_zero_of_forall_eq_zero
    intro s
    have := hZ (mk s j)
    simpa using this
  have e3 : ∑ᶠ s : ℤ, (ind Z (hEdge (mk s j)) + ind Z (hEdge (mk s (j + 1))) +
      ind Z (vEdge (mk s j)) + ind Z (vEdge (mk (s + 1) j))) =
      ∑ᶠ s : ℤ, (ind Z (hEdge (mk s j)) + ind Z (hEdge (mk s (j + 1))) + ind Z (vEdge (mk s j))) +
        ∑ᶠ s : ℤ, ind Z (vEdge (mk (s + 1) j)) :=
    finsum_add_distrib
      (f := fun s =>
        ind Z (hEdge (mk s j)) + ind Z (hEdge (mk s (j + 1))) + ind Z (vEdge (mk s j)))
      ((h1.add h2).add h3) h4
  have e2 :
      ∑ᶠ s : ℤ, (ind Z (hEdge (mk s j)) + ind Z (hEdge (mk s (j + 1))) + ind Z (vEdge (mk s j))) =
      ∑ᶠ s : ℤ, (ind Z (hEdge (mk s j)) + ind Z (hEdge (mk s (j + 1)))) +
        ∑ᶠ s : ℤ, ind Z (vEdge (mk s j)) :=
    finsum_add_distrib (f := fun s => ind Z (hEdge (mk s j)) + ind Z (hEdge (mk s (j + 1))))
      (h1.add h2) h3
  have e1 : ∑ᶠ s : ℤ, (ind Z (hEdge (mk s j)) + ind Z (hEdge (mk s (j + 1)))) =
      ∑ᶠ s : ℤ, ind Z (hEdge (mk s j)) + ∑ᶠ s : ℤ, ind Z (hEdge (mk s (j + 1))) :=
    finsum_add_distrib h1 h2
  have hshift : ∑ᶠ s : ℤ, ind Z (vEdge (mk (s + 1) j)) = ∑ᶠ s : ℤ, ind Z (vEdge (mk s j)) :=
    finsum_comp_equiv (Equiv.addRight (1 : ℤ)) (f := fun s => ind Z (vEdge (mk s j)))
  rw [e3, e2, e1, hshift, add_assoc, zmod2_add_self, add_zero] at key
  -- key : rowPar j + rowPar (j+1) = 0
  have : rowPar Z j + rowPar Z (j + 1) = 0 := key
  calc rowPar Z (j + 1) = rowPar Z (j + 1) + (rowPar Z j + rowPar Z j) := by
        rw [zmod2_add_self, add_zero]
    _ = rowPar Z j + (rowPar Z j + rowPar Z (j + 1)) := by ring
    _ = rowPar Z j := by rw [this, add_zero]

/-- Some row carries no horizontal `Z`-edge. [folklore] -/
theorem exists_rowPar_eq_zero (Z : Finset (Sym2 (Site 2))) : ∃ j, rowPar Z j = 0 := by
  classical
  have hS : {p : ℤ × ℤ | hEdge (mk p.1 p.2) ∈ Z}.Finite := by
    refine Set.Finite.preimage (f := fun p : ℤ × ℤ => hEdge (mk p.1 p.2)) ?_ Z.finite_toSet
    rintro ⟨s, j⟩ - ⟨s', j'⟩ - h
    simpa [mk_inj, Prod.ext_iff] using h
  have hfin : {j : ℤ | ∃ s, hEdge (mk s j) ∈ Z}.Finite := by
    refine (hS.image Prod.snd).subset ?_
    rintro j ⟨s, hs⟩
    exact ⟨(s, j), hs, rfl⟩
  obtain ⟨j, hj⟩ := Infinite.exists_notMem_finset hfin.toFinset
  refine ⟨j, finsum_eq_zero_of_forall_eq_zero fun s => ?_⟩
  rw [Set.Finite.mem_toFinset] at hj
  have : hEdge (mk s j) ∉ Z := fun h => hj ⟨s, h⟩
  simp [ind, this]

/-- **Row lemma**: every row carries an even number of horizontal edges of an even edge set.
[folklore] -/
theorem IsEven.rowPar_eq_zero {Z : Finset (Sym2 (Site 2))} (hZ : IsEven Z) (j : ℤ) :
    rowPar Z j = 0 := by
  obtain ⟨j₀, hj₀⟩ := exists_rowPar_eq_zero Z
  have hup : ∀ n : ℕ, rowPar Z (j₀ + n) = rowPar Z j₀ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.cast_succ, ← add_assoc, hZ.rowPar_succ, ih]
  have hdown : ∀ n : ℕ, rowPar Z (j₀ - n) = rowPar Z j₀ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [← ih, Nat.cast_succ, ← hZ.rowPar_succ (j₀ - (n + 1))]
      congr 1; ring
  rcases le_or_gt j₀ j with h | h
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.2 h)
    have : j = j₀ + n := by omega
    rw [this, hup, hj₀]
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.2 h.le)
    have : j = j₀ - n := by omega
    rw [this, hdown, hj₀]

/-! ### The two half-rays of row `0` -/

/-- Parity of the number of horizontal `Z`-edges `{(s,0),(s+1,0)}` with `s ≥ 0` (crossings of the
positive `x`-axis of the dual picture). [folklore] -/
def rightPar (Z : Finset (Sym2 (Site 2))) : ZMod 2 :=
  ∑ᶠ s : ℤ, if 0 ≤ s then ind Z (hEdge (mk s 0)) else 0

/-- Parity of the number of horizontal `Z`-edges `{(s,0),(s+1,0)}` with `s < 0`. [folklore] -/
def leftPar (Z : Finset (Sym2 (Site 2))) : ZMod 2 :=
  ∑ᶠ s : ℤ, if s < 0 then ind Z (hEdge (mk s 0)) else 0

/-- Restricted row indicators have finite support. [folklore] -/
theorem hasFiniteSupport_ite (Z : Finset (Sym2 (Site 2))) (p : ℤ → Prop) [DecidablePred p] :
    Function.HasFiniteSupport fun s : ℤ => if p s then ind Z (hEdge (mk s 0)) else 0 := by
  refine (hasFiniteSupport_ind Z (hEdge_mk_injective_left 0)).subset ?_
  intro s hs
  simp only [Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp] at hs
  exact hs.2

/-- Row `0` splits into the two half-axes. [folklore] -/
theorem rowPar_zero_eq (Z : Finset (Sym2 (Site 2))) : rowPar Z 0 = rightPar Z + leftPar Z := by
  rw [rightPar, leftPar, ← finsum_add_distrib (hasFiniteSupport_ite Z _) (hasFiniteSupport_ite Z _)]
  refine finsum_congr fun s => ?_
  by_cases h : 0 ≤ s
  · simp [h, not_lt.2 h]
  · simp [h, not_le.1 h]

/-- The right parity is additive along `Z ⊆ E ↦ E \\ Z`. [folklore] -/
theorem rightPar_sdiff {E Z : Finset (Sym2 (Site 2))} (h : Z ⊆ E) :
    rightPar (E \ Z) = rightPar E + rightPar Z := by
  rw [rightPar, rightPar, rightPar,
    ← finsum_add_distrib (hasFiniteSupport_ite E _) (hasFiniteSupport_ite Z _)]
  refine finsum_congr fun s => ?_
  by_cases hs : 0 ≤ s
  · simp [hs, ind_sdiff h]
  · simp [hs]

/-- Odd right parity produces a horizontal edge on the non-negative axis. [folklore] -/
theorem exists_right_of_rightPar_ne_zero {Z : Finset (Sym2 (Site 2))} (h : rightPar Z ≠ 0) :
    ∃ s : ℤ, 0 ≤ s ∧ hEdge (mk s 0) ∈ Z := by
  by_contra hne
  push Not at hne
  refine h (finsum_eq_zero_of_forall_eq_zero fun s => ?_)
  by_cases hs : 0 ≤ s
  · simp [hs, ind, hne s hs]
  · simp [hs]

/-- Odd left parity produces a horizontal edge on the negative axis. [folklore] -/
theorem exists_left_of_leftPar_ne_zero {Z : Finset (Sym2 (Site 2))} (h : leftPar Z ≠ 0) :
    ∃ s : ℤ, s < 0 ∧ hEdge (mk s 0) ∈ Z := by
  by_contra hne
  push Not at hne
  refine h (finsum_eq_zero_of_forall_eq_zero fun s => ?_)
  by_cases hs : s < 0
  · simp [hs, ind, hne s hs]
  · simp [hs]

/-- An even edge set crossing the positive `x`-axis an odd number of times also crosses the
negative `x`-axis. [folklore] -/
theorem IsEven.leftPar_eq {Z : Finset (Sym2 (Site 2))} (hZ : IsEven Z) :
    leftPar Z = rightPar Z := by
  have h := rowPar_zero_eq Z
  rw [hZ.rowPar_eq_zero] at h
  calc leftPar Z = leftPar Z + (rightPar Z + rightPar Z) := by rw [zmod2_add_self, add_zero]
    _ = rightPar Z + (rightPar Z + leftPar Z) := by ring
    _ = rightPar Z := by rw [← h, add_zero]

/-! ### The edge boundary of a finite cluster -/

section Boundary

variable {C : Set (Site 2)} {hC : C.Finite}

/-- The boundary of the finite set `C` used below is this library's edge boundary
`edgeBoundary (zdGraph 2) hC.toFinset` (`LatticeGraph.lean`): the edges of `𝕃²` with exactly one
endpoint in `C` (the "necklace of closed edges" around a finite open cluster, Grimmett 1999, §1.4
p. 17). Membership of a concrete pair, unfolded. [cite: GrimmettPercolation1999, §1.4 p. 17] -/
theorem mk_mem_bdry_iff {x y : Site 2} :
    s(x, y) ∈ edgeBoundary (zdGraph 2) hC.toFinset ↔ (zdGraph 2).Adj x y ∧ Xor (x ∈ C) (y ∈ C) := by
  simp only [mem_edgeBoundary_iff, SimpleGraph.mem_edgeSet, Set.Finite.mem_toFinset,
    Sym2.mem_iff]
  constructor
  · rintro ⟨hadj, ⟨a, haC, ha⟩, ⟨b, hbC, hb⟩⟩
    refine ⟨hadj, ?_⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd haC hbC
    · exact Or.inl ⟨haC, hbC⟩
    · exact Or.inr ⟨haC, hbC⟩
    · exact absurd haC hbC
  · rintro ⟨hadj, ⟨hxC, hyC⟩ | ⟨hyC, hxC⟩⟩
    · exact ⟨hadj, ⟨x, hxC, Or.inl rfl⟩, ⟨y, hyC, Or.inr rfl⟩⟩
    · exact ⟨hadj, ⟨y, hyC, Or.inr rfl⟩, ⟨x, hxC, Or.inl rfl⟩⟩

/-- Indicator of `C` in `ZMod 2`. [folklore] -/
def cind (C : Set (Site 2)) (a : Site 2) : ZMod 2 := by
  classical exact if a ∈ C then 1 else 0

/-- The indicator of the edge boundary is the coboundary of the indicator of `C`. [folklore] -/
theorem ind_bdry_mk {x y : Site 2} (hadj : (zdGraph 2).Adj x y) :
    ind (edgeBoundary (zdGraph 2) hC.toFinset) s(x, y) = cind C x + cind C y := by
  classical
  unfold ind cind
  simp only [mk_mem_bdry_iff, hadj, true_and]
  by_cases hx : x ∈ C <;> by_cases hy : y ∈ C <;> (simp [Xor, hx, hy]; try decide)

/-- Boundary indicator of a horizontal edge. [folklore] -/
theorem ind_bdry_hEdge (a : Site 2) :
    ind (edgeBoundary (zdGraph 2) hC.toFinset) (hEdge a) = cind C a + cind C (a + ex) :=
  ind_bdry_mk ((zdGraph_adj_iff _ _).2 ⟨0, Or.inl rfl⟩)

/-- Boundary indicator of a vertical edge. [folklore] -/
theorem ind_bdry_vEdge (a : Site 2) :
    ind (edgeBoundary (zdGraph 2) hC.toFinset) (vEdge a) = cind C a + cind C (a + ey) :=
  ind_bdry_mk ((zdGraph_adj_iff _ _).2 ⟨1, Or.inl rfl⟩)

/-- The edge boundary of a finite set is even (it is a dual `𝔽₂`-cycle). [folklore] -/
theorem isEven_bdry : IsEven (edgeBoundary (zdGraph 2) hC.toFinset) := by
  intro a
  rw [ind_bdry_hEdge, ind_bdry_hEdge, ind_bdry_vEdge, ind_bdry_vEdge, add_right_comm a ey ex]
  have h2 : (2 : ZMod 2) = 0 := by decide
  linear_combination (cind C a + cind C (a + ex) + cind C (a + ey) + cind C (a + ex + ey)) * h2

/-- Boundary edges of an open cluster are closed. [cite: GrimmettPercolation1999, §1.4 p. 17] -/
theorem not_mem_of_mem_bdry_openCluster {ω : BondConfig (Site 2)} {x₀ : Site 2}
    (hC : (openCluster ω x₀).Finite) {e : Sym2 (Site 2)}
    (he : e ∈ edgeBoundary (zdGraph 2) hC.toFinset) : e ∉ ω := by
  induction e using Sym2.ind with
  | _ x y =>
    intro hω
    obtain ⟨hadj, hx⟩ := mk_mem_bdry_iff.1 he
    have hopen : (openGraph ω).Adj x y := (openGraph_adj ω x y).2 ⟨hω, hadj.ne⟩
    have hiff : x ∈ openCluster ω x₀ ↔ y ∈ openCluster ω x₀ :=
      ⟨fun h => SimpleGraph.Reachable.trans h hopen.reachable,
        fun h => SimpleGraph.Reachable.trans h hopen.symm.reachable⟩
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h2 (hiff.1 h1)
    · exact h2 (hiff.2 h1)

/-- Telescoping in characteristic two. [folklore] -/
theorem sum_range_telescope (g : ℕ → ZMod 2) (N : ℕ) :
    ∑ m ∈ Finset.range N, (g m + g (m + 1)) = g 0 + g N := by
  induction N with
  | zero => simp [zmod2_add_self]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    have h2 : (2 : ZMod 2) = 0 := by decide
    linear_combination (g N) * h2

/-- The boundary of a finite set containing the origin crosses the positive `x`-axis an odd number
of times. [folklore] -/
theorem rightPar_bdry (h0 : (0 : Site 2) ∈ C) :
    rightPar (edgeBoundary (zdGraph 2) hC.toFinset) = 1 := by
  classical
  -- a column bound for `C`
  obtain ⟨M, hM⟩ := (hC.image fun x : Site 2 => x 0).bddAbove
  have hMC : ∀ x ∈ C, x 0 ≤ M := fun x hx => hM ⟨x, hx, rfl⟩
  set N : ℕ := M.toNat + 1 with hN
  have hout : ∀ s : ℤ, (N : ℤ) ≤ s → mk s 0 ∉ C := by
    intro s hs hsC
    have := hMC _ hsC
    simp at this
    omega
  set f : ℤ → ZMod 2 := fun s =>
    if 0 ≤ s then ind (edgeBoundary (zdGraph 2) hC.toFinset) (hEdge (mk s 0)) else 0 with hf
  have hsupp : Function.support f ⊆ ((Finset.range N).map Nat.castEmbedding : Finset ℤ) := by
    intro s hs
    rw [Function.mem_support] at hs
    simp only [Finset.coe_map, Nat.castEmbedding_apply, Set.mem_image, Finset.mem_coe,
      Finset.mem_range]
    by_cases hs0 : 0 ≤ s
    · refine ⟨s.toNat, ?_, by simp; omega⟩
      by_contra hlt
      push Not at hlt
      apply hs
      simp only [hf, hs0, if_true, ind_bdry_hEdge, mk_add_ex]
      have h1 : mk s 0 ∉ C := hout s (by omega)
      have h2 : mk (s + 1) 0 ∉ C := hout (s + 1) (by omega)
      simp [cind, h1, h2]
    · exact absurd (by simp [hf, hs0]) hs
  rw [rightPar, finsum_eq_sum_of_support_subset f hsupp, Finset.sum_map]
  have hterm : ∀ m ∈ Finset.range N, f (Nat.castEmbedding m) =
      cind C (mk m 0) + cind C (mk (↑(m + 1)) 0) := by
    intro m _
    simp only [hf, Nat.castEmbedding_apply, Nat.cast_nonneg, if_true, ind_bdry_hEdge, mk_add_ex,
      Nat.cast_succ]
  rw [Finset.sum_congr rfl hterm, sum_range_telescope (fun m : ℕ => cind C (mk m 0)) N]
  have h1 : cind C (mk (0 : ℕ) 0) = 1 := by simp [cind, h0]
  have h2 : cind C (mk N 0) = 0 := by simp [cind, hout N le_rfl]
  rw [h1, h2, add_zero]

end Boundary

/-! ### Abstract closed non-backtracking simple dual walks -/

section Cycle

variable {n : ℕ} {P : ℕ → Site 2} {dd : ℕ → Fin 2 × Bool}

/-- The edges crossed by the dual walk `(P m, dd m)_{m < n}`. [folklore] -/
def cycEdges (n : ℕ) (P : ℕ → Site 2) (dd : ℕ → Fin 2 × Bool) : Finset (Sym2 (Site 2)) :=
  (Finset.range n).image fun m => crossedEdge (P m) (dd m)

/-- The hypotheses: a closed dual walk of length `n ≥ 1` visiting distinct plaquettes and never
reversing a step. [folklore] -/
structure IsSimpleClosed (n : ℕ) (P : ℕ → Site 2) (dd : ℕ → Fin 2 × Bool) : Prop where
  /-- the walk has at least one step -/
  pos : 0 < n
  /-- consecutive plaquettes differ by the step taken -/
  step : ∀ m < n, P (m + 1) = P m + stepVec (dd m)
  /-- the walk is closed -/
  closed : P n = P 0
  /-- the plaquettes `P 0, …, P (n-1)` are distinct -/
  inj : ∀ m l, m < n → l < n → P m = P l → m = l
  /-- no step reverses the previous one -/
  noback : ∀ m, m + 1 < n → dd (m + 1) ≠ rev (dd m)

/-- Membership in the crossed edges of a dual walk. [folklore] -/
theorem IsSimpleClosed.mem_cycEdges_iff {e : Sym2 (Site 2)} :
    e ∈ cycEdges n P dd ↔ ∃ m < n, crossedEdge (P m) (dd m) = e := by
  simp [cycEdges]

/-- The index of the plaquette before `m` on a closed walk of length `n`. [folklore] -/
def cycPred (n m : ℕ) : ℕ := if m = 0 then n - 1 else m - 1

/-- `cycPred` stays below `n`. [folklore] -/
theorem IsSimpleClosed.cycPred_lt (m : ℕ) (hm : m < n) : cycPred n m < n := by
  unfold cycPred; split_ifs <;> omega

variable (h : IsSimpleClosed n P dd)
include h

/-- A closed non-backtracking simple dual walk crosses each edge at most once. [folklore] -/
theorem IsSimpleClosed.edge_inj {m l : ℕ} (hm : m < n) (hl : l < n)
    (he : crossedEdge (P m) (dd m) = crossedEdge (P l) (dd l)) : m = l := by
  wlog hml : m ≤ l generalizing m l
  · exact (this hl hm he.symm (le_of_not_ge hml)).symm
  rcases crossedEdge_eq_iff.1 he with ⟨h1, -⟩ | ⟨h1, h2⟩
  · exact h.inj m l hm hl h1.symm
  · rw [← h.step m hm] at h1
    by_cases hm1 : m + 1 < n
    · exfalso
      have := h.inj _ _ hl hm1 h1
      subst this
      exact h.noback m hm1 h2
    · omega

/-- Such a walk of length `n` crosses exactly `n` edges. [folklore] -/
theorem IsSimpleClosed.card_cycEdges : (cycEdges n P dd).card = n := by
  rw [cycEdges, Finset.card_image_of_injOn, Finset.card_range]
  intro m hm l hl he
  exact h.edge_inj (by simpa using hm) (by simpa using hl) he

/-- The predecessor plaquette steps to the current one. [folklore] -/
theorem IsSimpleClosed.P_cycPred_succ {m : ℕ} (hm : m < n) : P (cycPred n m + 1) = P m := by
  unfold cycPred
  split_ifs with h0
  · subst h0
    rw [Nat.sub_add_cancel h.pos, h.closed]
  · congr 1; omega

/-- On the walk, exactly the outgoing step and the reversed incoming step cross cycle edges.
[folklore] -/
theorem IsSimpleClosed.filter_eq_pair {m₀ : ℕ} (hm₀ : m₀ < n) :
    (Finset.univ.filter fun dir => crossedEdge (P m₀) dir ∈ cycEdges n P dd) =
      {dd m₀, rev (dd (cycPred n m₀))} := by
  ext dir
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton, IsSimpleClosed.mem_cycEdges_iff]
  constructor
  · rintro ⟨m, hm, he⟩
    rcases crossedEdge_eq_iff.1 he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      have := h.inj _ _ hm₀ hm h1
      subst this
      exact h2
    · right
      rw [← h.step m hm] at h1
      have hpm : cycPred n m₀ = m := by
        by_cases hm1 : m + 1 < n
        · have := h.inj _ _ hm₀ hm1 h1
          subst this
          simp [cycPred]
        · have hmn : m + 1 = n := by omega
          rw [hmn, h.closed] at h1
          have := h.inj _ _ hm₀ h.pos h1
          subst this
          simp [cycPred]; omega
      rw [hpm]; exact h2
  · rintro (rfl | rfl)
    · exact ⟨m₀, hm₀, rfl⟩
    · refine ⟨cycPred n m₀, IsSimpleClosed.cycPred_lt m₀ hm₀, ?_⟩
      rw [← crossedEdge_step_rev, ← h.step _ (IsSimpleClosed.cycPred_lt m₀ hm₀),
        h.P_cycPred_succ hm₀]

/-- The outgoing step at a plaquette of the walk is not the reversal of the incoming one (also
across the closing point). [folklore] -/
theorem IsSimpleClosed.dd_ne_rev_cycPred {m₀ : ℕ} (hm₀ : m₀ < n) :
    dd m₀ ≠ rev (dd (cycPred n m₀)) := by
  intro heq
  by_cases h0 : m₀ = 0
  · subst h0
    simp only [cycPred, if_true] at heq
    -- the last edge equals the first edge
    have hlast : crossedEdge (P (n - 1)) (dd (n - 1)) = crossedEdge (P 0) (dd 0) := by
      rw [heq, ← crossedEdge_step_rev, ← h.step _ (by have := h.pos; omega),
        Nat.sub_add_cancel h.pos, h.closed]
    have hn1 : n - 1 = 0 := h.edge_inj (by have := h.pos; omega) h.pos hlast
    have hn : n = 1 := by have := h.pos; omega
    have := h.step 0 h.pos
    rw [zero_add, show (1 : ℕ) = n from hn.symm, h.closed] at this
    exact stepVec_ne_zero (dd 0) (by simpa using this.symm)
  · simp only [cycPred, h0, if_false] at heq
    have := h.noback (m₀ - 1) (by omega)
    rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 h0)] at this
    exact this heq

/-- Off the walk, no side of the plaquette is a cycle edge. [folklore] -/
theorem IsSimpleClosed.filter_eq_empty {a : Site 2} (ha : ∀ m < n, P m ≠ a) :
    (Finset.univ.filter fun dir => crossedEdge a dir ∈ cycEdges n P dd) = ∅ := by
  ext dir
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
    IsSimpleClosed.mem_cycEdges_iff, not_exists, not_and]
  intro m hm he
  rcases crossedEdge_eq_iff.1 he with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact ha m hm h1.symm
  · rw [← h.step m hm] at h1
    by_cases hm1 : m + 1 < n
    · exact ha _ hm1 h1.symm
    · have hmn : m + 1 = n := by omega
      rw [hmn, h.closed] at h1
      exact ha 0 h.pos h1.symm

/-- The edge set of a closed non-backtracking simple dual walk is even. [folklore] -/
theorem IsSimpleClosed.isEven : IsEven (cycEdges n P dd) := by
  classical
  refine isEven_of_card fun a => ?_
  by_cases ha : ∃ m < n, P m = a
  · obtain ⟨m₀, hm₀, rfl⟩ := ha
    rw [h.filter_eq_pair hm₀, Finset.card_pair (h.dd_ne_rev_cycPred hm₀)]
    decide
  · push Not at ha
    rw [h.filter_eq_empty ha, Finset.card_empty, Nat.cast_zero]

end Cycle

/-! ### Walking without backtracking inside an even edge set -/

section WalkSeq

variable {E : Finset (Sym2 (Site 2))}

/-- A state of the dual walk: the current plaquette and the direction of arrival (so that the
edge just crossed, `crossedEdge a (rev din)`, lies in `E`). [folklore] -/
structure WState (E : Finset (Sym2 (Site 2))) where
  /-- current plaquette -/
  a : Site 2
  /-- direction of the last step -/
  din : Fin 2 × Bool
  /-- the edge just crossed lies in `E` -/
  mem : crossedEdge a (rev din) ∈ E

/-- In an even edge set one can always leave a plaquette by an edge other than the arrival edge.
[folklore] -/
theorem exists_next (hE : IsEven E) (s : WState E) :
    ∃ dir, dir ≠ rev s.din ∧ crossedEdge s.a dir ∈ E := by
  classical
  set D := Finset.univ.filter fun dir => crossedEdge s.a dir ∈ E with hD
  have hmem : rev s.din ∈ D := by simp [hD, s.mem]
  have h1 : 1 < D.card := by
    have hpos : 0 < D.card := Finset.card_pos.2 ⟨_, hmem⟩
    have hev : Even D.card := hE.even_card_filter s.a
    obtain ⟨r, hr⟩ := hev
    omega
  obtain ⟨dir, hdir, hne⟩ := Finset.exists_mem_ne h1 (rev s.din)
  exact ⟨dir, hne, (Finset.mem_filter.1 hdir).2⟩

/-- The next state. [folklore] -/
def wnext (hE : IsEven E) (s : WState E) : WState E :=
  ⟨s.a + stepVec (Classical.choose (exists_next hE s)), Classical.choose (exists_next hE s), by
    rw [crossedEdge_step_rev]; exact (Classical.choose_spec (exists_next hE s)).2⟩

/-- The walk. [folklore] -/
def wseq (hE : IsEven E) (s₀ : WState E) : ℕ → WState E
  | 0 => s₀
  | k + 1 => wnext hE (wseq hE s₀ k)

variable (hE : IsEven E) (s₀ : WState E)

/-- Plaquette visited at time `k`. [folklore] -/
def wpos (k : ℕ) : Site 2 := (wseq hE s₀ k).a
/-- Step taken at time `k`. [folklore] -/
def wdir (k : ℕ) : Fin 2 × Bool := (wseq hE s₀ (k + 1)).din

/-- One step of the walk. [folklore] -/
theorem wpos_succ (k : ℕ) : wpos hE s₀ (k + 1) = wpos hE s₀ k + stepVec (wdir hE s₀ k) := rfl

/-- The walk only crosses edges of `E`. [folklore] -/
theorem wedge_mem (k : ℕ) : crossedEdge (wpos hE s₀ k) (wdir hE s₀ k) ∈ E :=
  (Classical.choose_spec (exists_next hE (wseq hE s₀ k))).2

/-- The walk never backtracks. [folklore] -/
theorem wdir_noback (k : ℕ) : wdir hE s₀ (k + 1) ≠ rev (wdir hE s₀ k) :=
  (Classical.choose_spec (exists_next hE (wseq hE s₀ (k + 1)))).1

/-- The plaquettes having a side in `E`: a finite set containing the whole walk. [folklore] -/
theorem finite_touch (E : Finset (Sym2 (Site 2))) :
    {a : Site 2 | ∃ dir, crossedEdge a dir ∈ E}.Finite := by
  have : {a : Site 2 | ∃ dir, crossedEdge a dir ∈ E} ⊆
      ⋃ e ∈ (E : Set (Sym2 (Site 2))), ⋃ dir : Fin 2 × Bool, {a | crossedEdge a dir = e} := by
    rintro a ⟨dir, ha⟩
    exact Set.mem_biUnion ha (Set.mem_iUnion.2 ⟨dir, rfl⟩)
  refine Set.Finite.subset (Set.Finite.biUnion E.finite_toSet fun e _ =>
    Set.finite_iUnion fun dir => Set.Subsingleton.finite ?_) this
  intro a ha a' ha'
  have := crossedEdge_eq_iff.1 (ha.trans ha'.symm)
  rcases this with ⟨h, -⟩ | ⟨-, h⟩
  · exact h.symm
  · exact absurd h (rev_ne_self dir).symm

/-- The walk stays on plaquettes having a side in `E`. [folklore] -/
theorem wpos_mem_touch (k : ℕ) : wpos hE s₀ k ∈ {a : Site 2 | ∃ dir, crossedEdge a dir ∈ E} :=
  ⟨rev (wseq hE s₀ k).din, (wseq hE s₀ k).mem⟩

/-- **Cycle extraction**: the walk closes up into a closed non-backtracking simple dual walk whose
edges lie in `E`. [folklore] -/
theorem exists_isSimpleClosed :
    ∃ n i₀ : ℕ, IsSimpleClosed n (fun m => wpos hE s₀ (i₀ + m)) (fun m => wdir hE s₀ (i₀ + m)) := by
  classical
  obtain ⟨i, -, j, -, hij, heq⟩ := Set.infinite_univ.exists_ne_map_eq_of_mapsTo
    (fun k _ => wpos_mem_touch hE s₀ k) (finite_touch E)
  have hrep : ∃ j, ∃ i < j, wpos hE s₀ i = wpos hE s₀ j := by
    rcases lt_or_gt_of_ne hij with h | h
    · exact ⟨j, i, h, heq⟩
    · exact ⟨i, j, h, heq.symm⟩
  set j₀ := Nat.find hrep with hj₀
  obtain ⟨i₀, hi₀, heq₀⟩ : ∃ i < j₀, wpos hE s₀ i = wpos hE s₀ j₀ := Nat.find_spec hrep
  have hmin : ∀ i i', i < i' → i' < j₀ → wpos hE s₀ i ≠ wpos hE s₀ i' := by
    intro i i' hii' hi' h
    exact Nat.find_min hrep hi' ⟨i, hii', h⟩
  refine ⟨j₀ - i₀, i₀, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · intro m _; exact wpos_succ hE s₀ (i₀ + m)
  · simp only [add_zero]
    rw [Nat.add_sub_cancel' hi₀.le, heq₀]
  · intro m l hm hl h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact hmin (i₀ + m) (i₀ + l) (by omega) (by omega) h
    · exact hmin (i₀ + l) (i₀ + m) (by omega) (by omega) h.symm
  · intro m _
    rw [show i₀ + (m + 1) = i₀ + m + 1 by ring]
    exact wdir_noback hE s₀ (i₀ + m)

end WalkSeq

/-! ### Extracting a cycle around the origin -/

/-- **Key combinatorial lemma**: an even set of edges of `𝕃²` crossing the positive `x`-axis an
odd number of times contains the edge set of a closed non-backtracking simple dual walk which
itself crosses the positive `x`-axis an odd number of times. [folklore] -/
theorem exists_cycle_rightPar (E : Finset (Sym2 (Site 2))) (hE : IsEven E)
    (hr : rightPar E = 1) :
    ∃ (n : ℕ) (P : ℕ → Site 2) (dd : ℕ → Fin 2 × Bool), IsSimpleClosed n P dd ∧
      cycEdges n P dd ⊆ E ∧ rightPar (cycEdges n P dd) = 1 := by
  induction hN : E.card using Nat.strong_induction_on generalizing E with
  | _ N ih =>
    -- a starting edge on the positive axis
    obtain ⟨t, -, ht⟩ := exists_right_of_rightPar_ne_zero (Z := E) (by rw [hr]; exact one_ne_zero)
    let s₀ : WState E := ⟨mk t 0 + stepVec ((1 : Fin 2), false), (1, false), by
      rw [crossedEdge_step_rev]; exact ht⟩
    obtain ⟨n, i₀, hsc⟩ := exists_isSimpleClosed hE s₀
    set P : ℕ → Site 2 := fun m => wpos hE s₀ (i₀ + m) with hP
    set dd : ℕ → Fin 2 × Bool := fun m => wdir hE s₀ (i₀ + m) with hdd
    have hsub : cycEdges n P dd ⊆ E := by
      intro e he
      obtain ⟨m, -, rfl⟩ := (IsSimpleClosed.mem_cycEdges_iff).1 he
      exact wedge_mem hE s₀ (i₀ + m)
    by_cases h1 : rightPar (cycEdges n P dd) = 1
    · exact ⟨n, P, dd, hsc, hsub, h1⟩
    · have h0 : rightPar (cycEdges n P dd) = 0 :=
        (zmod2_eq_zero_or_one _).resolve_right h1
      have hne : (cycEdges n P dd).Nonempty := by
        rw [← Finset.card_pos, hsc.card_cycEdges]; exact hsc.pos
      have hlt : (E \ cycEdges n P dd).card < N := by
        rw [← hN]; exact Finset.card_lt_card (Finset.sdiff_ssubset hsub hne)
      obtain ⟨n', P', dd', hsc', hsub', hr'⟩ := ih _ hlt (E \ cycEdges n P dd)
        (hE.sdiff hsc.isEven hsub) (by rw [rightPar_sdiff hsub, hr, h0, add_zero]) rfl
      exact ⟨n', P', dd', hsc', hsub'.trans Finset.sdiff_subset, hr'⟩

/-- A cycle edge is a side of a visited plaquette. [folklore] -/
theorem IsSimpleClosed.exists_eq_of_mem {n : ℕ} {P : ℕ → Site 2} {dd : ℕ → Fin 2 × Bool}
    (h : IsSimpleClosed n P dd) {a : Site 2} {dir : Fin 2 × Bool}
    (he : crossedEdge a dir ∈ cycEdges n P dd) : ∃ m ≤ n, P m = a := by
  obtain ⟨m, hm, he⟩ := (IsSimpleClosed.mem_cycEdges_iff).1 he
  rcases crossedEdge_eq_iff.1 he with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact ⟨m, hm.le, h1.symm⟩
  · rw [← h.step m hm] at h1
    exact ⟨m + 1, hm, h1.symm⟩

/-- Along a dual walk the first coordinate moves by at most one per step. [folklore] -/
theorem IsSimpleClosed.abs_sub_le {n : ℕ} {P : ℕ → Site 2} {dd : ℕ → Fin 2 × Bool}
    (h : IsSimpleClosed n P dd) {m l : ℕ} (hml : m ≤ l) (hl : l ≤ n) :
    |P l 0 - P m 0| ≤ (l : ℤ) - m := by
  induction l, hml using Nat.le_induction with
  | base => simp
  | succ l hml ih =>
    have h1 := ih (Nat.le_of_succ_le hl)
    have h2 : |P (l + 1) 0 - P l 0| ≤ 1 := by
      rw [h.step l hl]; simpa using abs_stepVec_apply_zero_le (dd l)
    calc |P (l + 1) 0 - P m 0| = |(P (l + 1) 0 - P l 0) + (P l 0 - P m 0)| := by ring_nf
      _ ≤ |P (l + 1) 0 - P l 0| + |P l 0 - P m 0| := abs_add_le _ _
      _ ≤ 1 + ((l : ℤ) - m) := add_le_add h2 h1
      _ = ((l + 1 : ℕ) : ℤ) - m := by push_cast; ring

/-- The word of a dual walk reproduces its positions. [folklore] -/
theorem IsSimpleClosed.wordPos_eq {n : ℕ} {P : ℕ → Site 2} {dd : ℕ → Fin 2 × Bool}
    (h : IsSimpleClosed n P dd) {m : ℕ} (hm : m ≤ n) :
    P 0 + wordPos (fun k : Fin n => dd k) m = P m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [wordPos_succ _ hm, ← add_assoc, ih (Nat.le_of_succ_le hm), h.step m hm]

/-- The crossed edges of the word of a dual walk are its cycle edges. [folklore] -/
theorem IsSimpleClosed.dualEdges_eq {n : ℕ} {P : ℕ → Site 2} {dd : ℕ → Fin 2 × Bool}
    (h : IsSimpleClosed n P dd) : dualEdges (P 0) (fun k : Fin n => dd k) = cycEdges n P dd := by
  ext e
  simp only [dualEdges, cycEdges, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_range]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, k.2, by rw [h.wordPos_eq k.2.le]⟩
  · rintro ⟨m, hm, rfl⟩
    exact ⟨⟨m, hm⟩, by rw [h.wordPos_eq hm.le]⟩

/-- **The dual circuit around a finite open cluster** (Grimmett 1999, §1.4 pp. 17–18 with (1.17);
Kesten 1982, p. 386): if the open cluster of the origin is finite then some closed dual walk of
length `n ≥ 1`, passing through a plaquette `(k, 0)` with `0 ≤ k < n`, crosses `n` distinct
edges of `𝕃²`, all closed; moreover the walk is self-avoiding (its `n` plaquettes are distinct)
and non-backtracking, as in Grimmett's count `ρ(n) ≤ n σ(n-1)` of (1.17) (the Peierls estimate
for `p_c(2) < 1` only uses the cruder count of all `4ⁿ` words).
[cite: GrimmettPercolation1999, §1.4 pp. 17–18, (1.17)] -/
theorem exists_dualCircuit (ω : BondConfig (Site 2)) (hC : (openCluster ω 0).Finite) :
    ∃ n k : ℕ, k < n ∧ ∃ (a : Site 2) (w : Fin n → Fin 2 × Bool),
      wordPos w n = 0 ∧ (∃ m ≤ n, a + wordPos w m = Pi.single 0 (k : ℤ)) ∧
      (dualEdges a w).card = n ∧ Disjoint (↑(dualEdges a w) : Set (Sym2 (Site 2))) ω ∧
      Set.InjOn (wordPos w) (Set.Iio n) ∧
      (∀ i j : Fin n, (j : ℕ) = i + 1 → w j ≠ rev (w i)) := by
  set C := openCluster ω 0
  have h0 : (0 : Site 2) ∈ C := mem_openCluster_self ω 0
  obtain ⟨n, P, dd, hsc, hsub, hr⟩ :=
    exists_cycle_rightPar (edgeBoundary (zdGraph 2) hC.toFinset) isEven_bdry (rightPar_bdry h0)
  -- the walk visits the positive and the negative axis
  obtain ⟨t, ht0, ht⟩ := exists_right_of_rightPar_ne_zero (Z := cycEdges n P dd)
    (by rw [hr]; exact one_ne_zero)
  obtain ⟨s, hs0, hs⟩ := exists_left_of_leftPar_ne_zero (Z := cycEdges n P dd)
    (by rw [hsc.isEven.leftPar_eq, hr]; exact one_ne_zero)
  rw [show hEdge (mk t 0) = crossedEdge (mk t 0) (1, false) from rfl] at ht
  rw [show hEdge (mk s 0) = crossedEdge (mk s 0) (1, false) from rfl] at hs
  obtain ⟨m', hm', hPm'⟩ := hsc.exists_eq_of_mem ht
  obtain ⟨m'', hm'', hPm''⟩ := hsc.exists_eq_of_mem hs
  have hdist : t - s ≤ n := by
    rcases le_total m'' m' with hle | hle
    · have := hsc.abs_sub_le hle hm'
      rw [hPm', hPm''] at this
      simp only [mk_apply_zero] at this
      have := (le_abs_self _).trans this
      omega
    · have := hsc.abs_sub_le hle hm''
      rw [hPm', hPm''] at this
      simp only [mk_apply_zero] at this
      have := (neg_le_abs _).trans this
      omega
  refine ⟨n, t.toNat, by omega, P 0, fun k => dd k, ?_, ⟨m', hm', ?_⟩, ?_, ?_, ?_, ?_⟩
  · have := hsc.wordPos_eq le_rfl
    rw [hsc.closed] at this
    simpa using this
  · rw [hsc.wordPos_eq hm', hPm']
    exact site_ext (by simp; omega) (by simp)
  · rw [hsc.dualEdges_eq, hsc.card_cycEdges]
  · rw [hsc.dualEdges_eq, Set.disjoint_left]
    intro e he
    exact not_mem_of_mem_bdry_openCluster hC (hsub he)
  · intro i hi j hj hij
    have h := congrArg (P 0 + ·) hij
    simp only [hsc.wordPos_eq (le_of_lt hi), hsc.wordPos_eq (le_of_lt hj)] at h
    exact hsc.inj i j hi hj h
  · intro i j hj
    show dd j ≠ rev (dd i)
    rw [hj]
    exact hsc.noback i (hj ▸ j.2)

end Contour

end Percolation.Literature
