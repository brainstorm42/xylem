import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.Convex.Segment
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Pi.Interval
import Mathlib.Order.UpperLower.Basic
import Mathlib.Probability.Distributions.SetBernoulli
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Percolation.Literature.Basic
import Percolation.Literature.LatticeModels.LatticeGraph
import Percolation.Literature.PercolationEvents
import Percolation.Util.Linter

/-!
# Rectangle crossings, planar duality on `ℤ²`, conformal-rectangle crossing events

Bond percolation on the square lattice `ℤ² = Site 2` (Grimmett, *Percolation*, 2nd ed. (1999),
§§1.6, 9.7, 11.2–11.3; Bollobás–Riordan, *Percolation* (2006), Ch. 3, Lemma 1; Smirnov,
*Critical percolation in the plane*, C. R. Acad. Sci. Paris 333 (2001), §2):

* `openCrossing S A B`: the event that some vertex of `A` is joined to some vertex of `B` by an
  open path inside `S` (general vertex type); it is increasing (`isUpperSet_openCrossing`).
* `rectangle m n = [0, m] × [0, n] ∩ ℤ²` (a `Finset`, Mathlib's order interval `Finset.Icc` for
  the product order on `Fin 2 → ℤ`), its four sides, and the left-right / top-bottom open
  crossing events `lrCrossing m n`, `tbCrossing m n`; `crossingProb p m n = P_p(LR(m, n))`.

Design choices.
* Probabilities are `μ.real _`; increasing events are Mathlib's `IsUpperSet`.
* For `m = 0` the left and right sides of `rectangle 0 n` coincide, so `lrCrossing 0 n` is the sure
  event and `crossingProb p 0 n = 1`; correspondingly `dualRectangle 0 n = ∅`. RSW-type statements
  therefore quantify over `1 ≤ m`.
* `dualEdge` is the identity on pairs that are not edges of `ℤ²` (documented junk value); it is
  defined through `Sym2.lift` using the lattice operations `⊓`, `⊔` on `Site 2`, which makes the
  symmetry in the two endpoints definitional.

Mathlib anchors used rather than re-defined: `Finset.Icc` on `Fin 2 → ℤ` (`Mathlib.Data.Pi.Interval`),
`Finset.filter`, `IsUpperSet`, `Sym2.lift`, `Sym2.map`, `SimpleGraph.edgeSet`,
`SimpleGraph.Reachable`, `SimpleGraph.induce`, `MeasureTheory.Measure.map`,
`MeasureTheory.Measure.real`, `unitInterval.symm`. Mathlib has no rectangle-crossing events, no
planar lattice duality and no percolation crossing probabilities.
-/

namespace Percolation.Literature

open MeasureTheory

noncomputable section

/-! ### General open crossing events -/

section General

variable {V : Type*}

/-- The open crossing event from `A` to `B` inside `S`: some `x ∈ A` is joined to some `y ∈ B` by
an open path all of whose vertices lie in `S`. (Grimmett 1999, §1.6 and §11.3, crossings of
boxes.) [cite: GrimmettPercolation1999, §1.6 and §11.3 crossings of boxes] -/
def openCrossing (S A B : Set V) : Set (BondConfig V) :=
  {ω | ∃ x ∈ A, ∃ y ∈ B, ω ∈ openConnIn S x y}

/-- Membership in an open crossing event, unfolded. (Grimmett 1999, §11.3.) [cite: GrimmettPercolation1999, §11.3] -/
@[simp] theorem mem_openCrossing_iff {S A B : Set V} {ω : BondConfig V} :
    ω ∈ openCrossing S A B ↔ ∃ x ∈ A, ∃ y ∈ B, ω ∈ openConnIn S x y :=
  Iff.rfl

/-- The restricted connection event `{x ↔ y in S}` is increasing. (Grimmett 1999, §2.1.) [cite: GrimmettPercolation1999, §2.1] -/
theorem isUpperSet_openConnIn (S : Set V) (x y : V) :
    IsUpperSet (openConnIn S x y : Set (BondConfig V)) := by
  rintro ω ω' h ⟨hx, hy, hr⟩
  refine ⟨hx, hy, hr.mono ?_⟩
  exact SimpleGraph.comap_monotone _ (openGraph_mono h)

/-- Open crossing events are increasing. (Grimmett 1999, §2.1.) [cite: GrimmettPercolation1999, §2.1] -/
theorem isUpperSet_openCrossing (S A B : Set V) :
    IsUpperSet (openCrossing S A B : Set (BondConfig V)) := by
  rintro ω ω' h ⟨x, hx, y, hy, hω⟩
  exact ⟨x, hx, y, hy, isUpperSet_openConnIn S x y h hω⟩

end General

/-! ### Rectangles in `ℤ²` and their crossings -/

/-- The lattice rectangle `[0, m] × [0, n] ∩ ℤ²`, as the order interval `Icc 0 (m, n)` of the
product order on `Site 2 = Fin 2 → ℤ`. (Grimmett 1999, §11.3, `B(m, n)`-type rectangles.) [cite: GrimmettPercolation1999, §11.3   B(m n] -/
def rectangle (m n : ℕ) : Finset (LatticeModels.Site 2) := Finset.Icc 0 ![(m : ℤ), n]

/-- Membership in `rectangle m n`: `0 ≤ x₀ ≤ m` and `0 ≤ x₁ ≤ n`. (Grimmett 1999, §11.3.) [cite: GrimmettPercolation1999, §11.3] -/
@[simp] theorem mem_rectangle_iff {m n : ℕ} {x : LatticeModels.Site 2} :
    x ∈ rectangle m n ↔ 0 ≤ x 0 ∧ x 0 ≤ m ∧ 0 ≤ x 1 ∧ x 1 ≤ n := by
  simp only [rectangle, Finset.mem_Icc, Pi.le_def, Fin.forall_fin_two, Pi.zero_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  tauto

/-- The left side `{x ∈ [0, m] × [0, n] | x₀ = 0}` of the rectangle. (Grimmett 1999, §11.3.) [cite: GrimmettPercolation1999, §11.3] -/
def leftSide (m n : ℕ) : Finset (LatticeModels.Site 2) := (rectangle m n).filter fun x => x 0 = 0

/-- The right side `{x ∈ [0, m] × [0, n] | x₀ = m}` of the rectangle. (Grimmett 1999, §11.3.) [cite: GrimmettPercolation1999, §11.3] -/
def rightSide (m n : ℕ) : Finset (LatticeModels.Site 2) := (rectangle m n).filter fun x => x 0 = m

/-- The bottom side `{x ∈ [0, m] × [0, n] | x₁ = 0}` of the rectangle. (Grimmett 1999, §11.3.) [cite: GrimmettPercolation1999, §11.3] -/
def bottomSide (m n : ℕ) : Finset (LatticeModels.Site 2) := (rectangle m n).filter fun x => x 1 = 0

/-- The top side `{x ∈ [0, m] × [0, n] | x₁ = n}` of the rectangle. (Grimmett 1999, §11.3.) [cite: GrimmettPercolation1999, §11.3] -/
def topSide (m n : ℕ) : Finset (LatticeModels.Site 2) := (rectangle m n).filter fun x => x 1 = n

/-- The left-right open crossing event `LR(m, n)` of `[0, m] × [0, n]`: an open path inside the
rectangle from its left side to its right side. For `m = 0` the two sides coincide and this is
the sure event. (Grimmett 1999, §11.3; Bollobás–Riordan 2006, Ch. 3.) [cite: GrimmettPercolation1999, §11.3] -/
def lrCrossing (m n : ℕ) : Set (BondConfig (LatticeModels.Site 2)) :=
  openCrossing ↑(rectangle m n) ↑(leftSide m n) ↑(rightSide m n)

/-- The top-bottom open crossing event `TB(m, n)` of `[0, m] × [0, n]`: an open path inside the
rectangle from its bottom side to its top side. (Grimmett 1999, §11.3.) [cite: GrimmettPercolation1999, §11.3] -/
def tbCrossing (m n : ℕ) : Set (BondConfig (LatticeModels.Site 2)) :=
  openCrossing ↑(rectangle m n) ↑(bottomSide m n) ↑(topSide m n)

/-- Left-right crossing events are increasing. (Grimmett 1999, §2.1.) [cite: GrimmettPercolation1999, §2.1] -/
theorem isUpperSet_lrCrossing (m n : ℕ) : IsUpperSet (lrCrossing m n) :=
  isUpperSet_openCrossing _ _ _

/-- The crossing probability `P_p(LR(m, n))` of the rectangle `[0, m] × [0, n]` under bond
percolation on `ℤ²`. Warning: for `m = 0` the left and right sides coincide and
`crossingProb p 0 n = 1`; RSW-type statements quantify over `1 ≤ m`.
(Grimmett 1999, §11.3; Bollobás–Riordan 2006, Ch. 3.) [cite: GrimmettPercolation1999, §11.3] -/
noncomputable def crossingProb (p : unitInterval) (m n : ℕ) : ℝ :=
  (bondPercolation (LatticeModels.zdGraph 2) p).real (lrCrossing m n)

/-! ### Planar duality on `ℤ²` -/

/-- The dual edge of an edge of `ℤ²`, with dual vertices indexed by `Site 2` via
"dual vertex `x` = face with lower-left corner `x`" (the point `x + (½, ½)`): the horizontal
edge `{u, u + e₀}` is crossed by the dual edge `{u - e₁, u}` and the vertical edge `{u, u + e₁}`
by the dual edge `{u - e₀, u}`. Here `u = x ⊓ y` is the lower-left endpoint of the edge
`{x, y}`. On pairs that are not edges of `ℤ²` the map is the identity (junk value).
(Grimmett 1999, §11.2, planar duality; Bollobás–Riordan 2006, Ch. 3.) [cite: GrimmettPercolation1999, §11.2 planar duality] -/
def dualEdge : Sym2 (LatticeModels.Site 2) → Sym2 (LatticeModels.Site 2) :=
  Sym2.lift ⟨fun x y =>
    if x ⊔ y = x ⊓ y + Pi.single 0 1 then s(x ⊓ y - Pi.single 1 1, x ⊓ y)
    else if x ⊔ y = x ⊓ y + Pi.single 1 1 then s(x ⊓ y - Pi.single 0 1, x ⊓ y)
    else s(x, y),
    fun x y => by simp only [sup_comm, inf_comm, Sym2.eq_swap]⟩

/-- `dualEdge` on a horizontal edge `{x, x + e₀}` is the vertical dual edge `{x - e₁, x}`.
(Grimmett 1999, §11.2.) [cite: GrimmettPercolation1999, §11.2] -/
theorem dualEdge_horizontal (x : LatticeModels.Site 2) :
    dualEdge s(x, x + Pi.single 0 1) = s(x - Pi.single 1 1, x) := by
  have hle : x ≤ x + Pi.single 0 1 := le_add_of_nonneg_right (Pi.single_nonneg.2 zero_le_one)
  simp [dualEdge, Sym2.lift_mk, hle]

/-- `dualEdge` on a vertical edge `{x, x + e₁}` is the horizontal dual edge `{x - e₀, x}`.
(Grimmett 1999, §11.2.) [cite: GrimmettPercolation1999, §11.2] -/
theorem dualEdge_vertical (x : LatticeModels.Site 2) :
    dualEdge s(x, x + Pi.single 1 1) = s(x - Pi.single 0 1, x) := by
  have hle : x ≤ x + Pi.single 1 1 := le_add_of_nonneg_right (Pi.single_nonneg.2 zero_le_one)
  have hne : x + Pi.single 1 1 ≠ x + Pi.single 0 1 := by
    intro h
    have := congr_fun (add_left_cancel h) 0
    simp at this
  simp [dualEdge, Sym2.lift_mk, hle, hne]

/-- `dualEdge` maps edges of `ℤ²` to edges of `ℤ²` (the dual lattice being indexed by `Site 2`).
(Grimmett 1999, §11.2.) [cite: GrimmettPercolation1999, §11.2] -/
def dualEdge_mem_edgeSet : Prop :=
  ∀ {e : Sym2 (LatticeModels.Site 2)} (he : e ∈ (LatticeModels.zdGraph 2).edgeSet),
    dualEdge e ∈ (LatticeModels.zdGraph 2).edgeSet

/-- `dualEdge` is injective on the edges of `ℤ²`. (Grimmett 1999, §11.2.) [cite: GrimmettPercolation1999, §11.2] -/
def dualEdge_injOn : Prop :=
  Set.InjOn dualEdge (LatticeModels.zdGraph 2).edgeSet

/-- Double duality: with the lower-left-corner identification the dual of the dual lattice is
`ℤ² + (1, 1)`, so on lattice edges `dualEdge (dualEdge e)` is `e` translated by `-(1, 1)`.
(Grimmett 1999, §11.2.) [cite: GrimmettPercolation1999, §11.2] -/
def dualEdge_dualEdge : Prop :=
  ∀ {e : Sym2 (LatticeModels.Site 2)} (he : e ∈ (LatticeModels.zdGraph 2).edgeSet),
    dualEdge (dualEdge e) = e.map fun x => x - 1

/-- The dual configuration of `ω`: a dual edge (an edge of `ℤ²` in dual coordinates) is open iff
the primal edge it crosses is *closed*, i.e. `dualConfig ω = E(ℤ²) \ dualEdge '' ω`.
(Grimmett 1999, §11.2, "open dual edges cross closed primal edges".) [cite: GrimmettPercolation1999, §11.2  "open dual edges cross closed pri] -/
def dualConfig (ω : BondConfig (LatticeModels.Site 2)) : BondConfig (LatticeModels.Site 2) :=
  (LatticeModels.zdGraph 2).edgeSet \ dualEdge '' ω

/-- Membership in the dual configuration, unfolded. (Grimmett 1999, §11.2.) [cite: GrimmettPercolation1999, §11.2] -/
@[simp] theorem mem_dualConfig_iff {ω : BondConfig (LatticeModels.Site 2)} {e : Sym2 (LatticeModels.Site 2)} :
    e ∈ dualConfig ω ↔ e ∈ (LatticeModels.zdGraph 2).edgeSet ∧ ∀ e' ∈ ω, dualEdge e' ≠ e := by
  simp [dualConfig]

/-- The dual rectangle of `[0, m] × [0, n]` in dual coordinates: the dual vertices
`[0, m - 1] × [-1, n]`, i.e. the points `[½, m - ½] × [-½, n + ½]` of `ℤ² + (½, ½)`
(Bollobás–Riordan 2006, Ch. 3, Lemma 1, the "horizontal dual" `R^h`). Empty for `m = 0`. [cite: BollobasRiordanPercolation2006, Ch. 3 Lemma 1  the "horizontal dual"  R] -/
def dualRectangle (m n : ℕ) : Finset (LatticeModels.Site 2) := Finset.Icc ![0, -1] ![(m : ℤ) - 1, n]

/-- Membership in `dualRectangle m n`: `0 ≤ x₀ ≤ m - 1` and `-1 ≤ x₁ ≤ n`.
(Bollobás–Riordan 2006, Ch. 3, Lemma 1.) [cite: BollobasRiordanPercolation2006, Ch. 3 Lemma 1] -/
@[simp] theorem mem_dualRectangle_iff {m n : ℕ} {x : LatticeModels.Site 2} :
    x ∈ dualRectangle m n ↔ 0 ≤ x 0 ∧ x 0 ≤ m - 1 ∧ -1 ≤ x 1 ∧ x 1 ≤ n := by
  simp only [dualRectangle, Finset.mem_Icc, Pi.le_def, Fin.forall_fin_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  tauto

/-- The top side `{x₁ = n}` of the dual rectangle (dual vertices just above the top side of
`[0, m] × [0, n]`). (Bollobás–Riordan 2006, Ch. 3, Lemma 1.) [cite: BollobasRiordanPercolation2006, Ch. 3 Lemma 1] -/
def dualTopSide (m n : ℕ) : Finset (LatticeModels.Site 2) := (dualRectangle m n).filter fun x => x 1 = n

/-- The bottom side `{x₁ = -1}` of the dual rectangle (dual vertices just below the bottom side
of `[0, m] × [0, n]`). (Bollobás–Riordan 2006, Ch. 3, Lemma 1.) [cite: BollobasRiordanPercolation2006, Ch. 3 Lemma 1] -/
def dualBottomSide (m n : ℕ) : Finset (LatticeModels.Site 2) := (dualRectangle m n).filter fun x => x 1 = -1

/-- The dual top-bottom crossing event `TB*(m, n)`: the dual configuration contains a dual-open
path inside the dual rectangle from its top side to its bottom side.
(Grimmett 1999, §11.2; Bollobás–Riordan 2006, Ch. 3, Lemma 1.) [cite: GrimmettPercolation1999, §11.2] -/
def dualTBCrossing (m n : ℕ) : Set (BondConfig (LatticeModels.Site 2)) :=
  dualConfig ⁻¹' openCrossing ↑(dualRectangle m n) ↑(dualTopSide m n) ↑(dualBottomSide m n)

/-- [cite: GrimmettPercolation1999, §11.2–11.3] -/
def lrCrossing_xor_dualTBCrossing : Prop :=
  ∀ (m n : ℕ) {ω : BondConfig (LatticeModels.Site 2)} (hω : ω ⊆ (LatticeModels.zdGraph 2).edgeSet),
    Xor (ω ∈ lrCrossing m n) (ω ∈ dualTBCrossing m n)

/-- The law of the dual configuration under `P_p` is `P_{1-p}`: dual edges are open independently
with probability `1 - p`. (Grimmett 1999, §11.2.) [cite: GrimmettPercolation1999, §11.2] -/
def bondPercolation_map_dualConfig : Prop :=
  ∀ (p : unitInterval),
    (bondPercolation (LatticeModels.zdGraph 2) p).map dualConfig =
      bondPercolation (LatticeModels.zdGraph 2) (unitInterval.symm p)

/-- `LR(m, n)` and `TB*(m, n)` have complementary probabilities:
`P_p(LR(m, n)) + P_p(TB*(m, n)) = 1`. (Grimmett 1999, §11.2; consequence of
`lrCrossing_xor_dualTBCrossing` since `P_p` is carried by `{ω ⊆ E(ℤ²)}`.) [cite: GrimmettPercolation1999, §11.2] -/
def crossingProb_add_real_dualTBCrossing : Prop :=
  ∀ (p : unitInterval) (m n : ℕ),
    crossingProb p m n + (bondPercolation (LatticeModels.zdGraph 2) p).real (dualTBCrossing m n) = 1

/-- Self-duality at `p = 1/2`: the `(n+1) × n` rectangle `[0, n + 1] × [0, n]` is crossed from
left to right with probability exactly `1/2`, since its dual rectangle is a rotated copy of
itself and `P_{1/2}` is self-dual. (Grimmett 1999, Lemma 11.21; Bollobás–Riordan 2006, Ch. 3,
Corollary 3.) [cite: GrimmettPercolation1999, Lemma 11.21] -/
def crossingProb_half_succ_self : Prop :=
  ∀ (n : ℕ),
    crossingProb half (n + 1) n = 1 / 2

/-! ### Crossings of conformal rectangles -/

/-! ### Planar duality: discharges of `dualEdge_mem_edgeSet`, `dualEdge_injOn`,
`dualEdge_dualEdge`, `bondPercolation_map_dualConfig` -/

section DualityProofs

open ProbabilityTheory unitInterval

/-- The edges of `ℤ^d` are exactly the pairs `{u, u + eᵢ}`. (Friedli–Velenik 2017, §3.1.) [folklore] -/
theorem mem_edgeSet_zdGraph_iff {d : ℕ} {e : Sym2 (LatticeModels.Site d)} :
    e ∈ (LatticeModels.zdGraph d).edgeSet ↔ ∃ u i, e = s(u, u + Pi.single i 1) := by
  induction e using Sym2.ind with
  | h x y =>
    rw [SimpleGraph.mem_edgeSet, LatticeModels.zdGraph_adj_iff]
    constructor
    · rintro ⟨i, h | h⟩
      · exact ⟨x, i, by rw [h]⟩
      · exact ⟨y, i, by rw [h, Sym2.eq_swap]⟩
    · rintro ⟨u, i, h⟩
      rw [Sym2.eq_iff] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨i, Or.inl rfl⟩
      · exact ⟨i, Or.inr rfl⟩

/-- `{u, u + eᵢ}` is an edge of `ℤ²`. [folklore] -/
theorem single_edge_mem (u : LatticeModels.Site 2) (i : Fin 2) : s(u, u + Pi.single i 1) ∈ (LatticeModels.zdGraph 2).edgeSet :=
  mem_edgeSet_zdGraph_iff.2 ⟨u, i, rfl⟩

/-- In `ℤ²`, `x ⊔ y = x ⊓ y + eᵢ` iff `{x, y}` is the lattice edge `{x ⊓ y, x ⊓ y + eᵢ}`, i.e. iff
`y = x + eᵢ` or `x = y + eᵢ` (the case distinction underlying `dualEdge`). [folklore] -/
theorem sup_eq_inf_add_single_iff (x y : LatticeModels.Site 2) (i : Fin 2) :
    x ⊔ y = x ⊓ y + Pi.single i 1 ↔ (y = x + Pi.single i 1 ∨ x = y + Pi.single i 1) := by
  constructor
  · intro h
    have h0 := congr_fun h 0
    have h1 := congr_fun h 1
    simp only [Pi.sup_apply, Pi.inf_apply, Pi.add_apply] at h0 h1
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Pi.single_eq_same, ne_eq, one_ne_zero,
        not_false_eq_true, Pi.single_eq_of_ne] at h0 h1
      rcases le_total (x 0) (y 0) with hle | hle
      · left; funext j; fin_cases j <;> simp <;> omega
      · right; funext j; fin_cases j <;> simp <;> omega
    · simp only [Fin.mk_one, Fin.isValue, ne_eq, zero_ne_one, not_false_eq_true,
        Pi.single_eq_of_ne, Pi.single_eq_same] at h0 h1
      rcases le_total (x 1) (y 1) with hle | hle
      · left; funext j; fin_cases j <;> simp <;> omega
      · right; funext j; fin_cases j <;> simp <;> omega
  · have hnn : (0 : LatticeModels.Site 2) ≤ Pi.single i 1 := Pi.single_nonneg.2 zero_le_one
    rintro (rfl | rfl)
    · rw [sup_of_le_right (le_add_of_nonneg_right hnn), inf_of_le_left (le_add_of_nonneg_right hnn)]
    · rw [sup_of_le_left (le_add_of_nonneg_right hnn), inf_of_le_right (le_add_of_nonneg_right hnn)]

/-- `dualEdge` is the identity off the edge set (its documented junk value). [folklore] -/
theorem dualEdge_of_not_mem {e : Sym2 (LatticeModels.Site 2)} (he : e ∉ (LatticeModels.zdGraph 2).edgeSet) : dualEdge e = e := by
  induction e using Sym2.ind with
  | h x y =>
    rw [SimpleGraph.mem_edgeSet, LatticeModels.zdGraph_adj_iff, not_exists] at he
    have h0 : ¬ x ⊔ y = x ⊓ y + Pi.single 0 1 := fun h => he 0 ((sup_eq_inf_add_single_iff x y 0).1 h)
    have h1 : ¬ x ⊔ y = x ⊓ y + Pi.single 1 1 := fun h => he 1 ((sup_eq_inf_add_single_iff x y 1).1 h)
    simp [dualEdge, Sym2.lift_mk, h0, h1]

/-- `dualEdge` of a horizontal edge, written as a vertical lattice edge `{v, v + e₁}`.
(Grimmett 1999, §11.2.) [folklore] -/
theorem dualEdge_horizontal' (u : LatticeModels.Site 2) :
    dualEdge s(u, u + Pi.single 0 1) = s(u - Pi.single 1 1, (u - Pi.single 1 1) + Pi.single 1 1) := by
  rw [dualEdge_horizontal, sub_add_cancel]

/-- `dualEdge` of a vertical edge, written as a horizontal lattice edge `{v, v + e₀}`.
(Grimmett 1999, §11.2.) [folklore] -/
theorem dualEdge_vertical' (u : LatticeModels.Site 2) :
    dualEdge s(u, u + Pi.single 1 1) = s(u - Pi.single 0 1, (u - Pi.single 0 1) + Pi.single 0 1) := by
  rw [dualEdge_vertical, sub_add_cancel]

/-- Discharge of `dualEdge_mem_edgeSet`: dual edges of lattice edges are lattice edges (in dual
coordinates). (Grimmett 1999, §11.2.) [cite: GrimmettPercolation1999, §11.2] -/
theorem dualEdge_mem_edgeSet_holds : dualEdge_mem_edgeSet := by
  intro e he
  obtain ⟨u, i, rfl⟩ := mem_edgeSet_zdGraph_iff.1 he
  fin_cases i
  · simp only [Fin.zero_eta]; rw [dualEdge_horizontal']; exact single_edge_mem _ 1
  · simp only [Fin.mk_one]; rw [dualEdge_vertical']; exact single_edge_mem _ 0

/-- `dualEdge e` is a lattice edge iff `e` is. (Grimmett 1999, §11.2.) [folklore] -/
theorem dualEdge_mem_edgeSet_iff (e : Sym2 (LatticeModels.Site 2)) :
    dualEdge e ∈ (LatticeModels.zdGraph 2).edgeSet ↔ e ∈ (LatticeModels.zdGraph 2).edgeSet := by
  refine ⟨fun h => ?_, dualEdge_mem_edgeSet_holds⟩
  by_contra he
  rw [dualEdge_of_not_mem he] at h
  exact he h

/-- The all-ones vector of `ℤ²` is `(1, 1) = e₀ + e₁`. [folklore] -/
theorem one_eq_single_add_single : (1 : LatticeModels.Site 2) = Pi.single 0 1 + Pi.single 1 1 := by
  funext j; fin_cases j <;> simp

/-- Discharge of `dualEdge_dualEdge`: with the lower-left-corner indexing of dual vertices,
`dualEdge (dualEdge e) = e - (1, 1)` on lattice edges. (Grimmett 1999, §11.2.) [cite: GrimmettPercolation1999, §11.2] -/
theorem dualEdge_dualEdge_holds : dualEdge_dualEdge := by
  intro e he
  obtain ⟨u, i, rfl⟩ := mem_edgeSet_zdGraph_iff.1 he
  fin_cases i
  · simp only [Fin.zero_eta]
    rw [dualEdge_horizontal', dualEdge_vertical', Sym2.map_mk, Sym2.eq_iff]
    left; constructor
    · rw [one_eq_single_add_single]; abel
    · rw [one_eq_single_add_single]; abel
  · simp only [Fin.mk_one]
    rw [dualEdge_vertical', dualEdge_horizontal', Sym2.map_mk, Sym2.eq_iff]
    left; constructor
    · rw [one_eq_single_add_single]; abel
    · rw [one_eq_single_add_single]; abel

/-- Discharge of `dualEdge_injOn`: `dualEdge` is injective on lattice edges (it has the left
inverse `e ↦ dualEdge e + (1, 1)`). (Grimmett 1999, §11.2.) [cite: GrimmettPercolation1999, §11.2] -/
theorem dualEdge_injOn_holds : dualEdge_injOn := by
  intro e he e' he' h
  have := congr_arg dualEdge h
  rw [dualEdge_dualEdge_holds he, dualEdge_dualEdge_holds he'] at this
  have hinj : Function.Injective (Sym2.map fun x : LatticeModels.Site 2 => x - 1) :=
    Sym2.map.injective (sub_left_injective)
  exact hinj this

/-- `dualEdge` maps the lattice edges onto the lattice edges: every edge `e` is the dual of
`dualEdge (e + (1, 1))`. (Grimmett 1999, §11.2.) [folklore] -/
theorem exists_dualEdge_eq {e : Sym2 (LatticeModels.Site 2)} (he : e ∈ (LatticeModels.zdGraph 2).edgeSet) :
    ∃ e' ∈ (LatticeModels.zdGraph 2).edgeSet, dualEdge e' = e := by
  refine ⟨dualEdge (e.map fun x => x + 1), dualEdge_mem_edgeSet_holds ?_, ?_⟩
  · obtain ⟨u, i, rfl⟩ := mem_edgeSet_zdGraph_iff.1 he
    rw [Sym2.map_mk, add_right_comm]
    exact single_edge_mem _ _
  · have hmem : e.map (fun x => x + 1) ∈ (LatticeModels.zdGraph 2).edgeSet := by
      obtain ⟨u, i, rfl⟩ := mem_edgeSet_zdGraph_iff.1 he
      rw [Sym2.map_mk, add_right_comm]
      exact single_edge_mem _ _
    have hcomp : ((fun x : LatticeModels.Site 2 => x - 1) ∘ fun x => x + 1) = id := by funext x; simp
    rw [dualEdge_dualEdge_holds hmem, Sym2.map_map, hcomp, Sym2.map_id, id]

/-- `dualEdge` is a permutation of `Sym2 (Site 2)`: a bijection of the lattice edges onto
themselves and the identity elsewhere. (Grimmett 1999, §11.2, the primal–dual edge bijection.) [folklore] -/
theorem dualEdge_bijective : Function.Bijective dualEdge := by
  constructor
  · intro e e' h
    by_cases he : e ∈ (LatticeModels.zdGraph 2).edgeSet
    · by_cases he' : e' ∈ (LatticeModels.zdGraph 2).edgeSet
      · exact dualEdge_injOn_holds he he' h
      · rw [dualEdge_of_not_mem he'] at h
        exact absurd (h ▸ dualEdge_mem_edgeSet_holds he) he'
    · by_cases he' : e' ∈ (LatticeModels.zdGraph 2).edgeSet
      · rw [dualEdge_of_not_mem he] at h
        exact absurd (h.symm ▸ dualEdge_mem_edgeSet_holds he') he
      · rwa [dualEdge_of_not_mem he, dualEdge_of_not_mem he'] at h
  · intro e
    by_cases he : e ∈ (LatticeModels.zdGraph 2).edgeSet
    · obtain ⟨e', -, h⟩ := exists_dualEdge_eq he
      exact ⟨e', h⟩
    · exact ⟨e, dualEdge_of_not_mem he⟩

/-- `dualEdge` as a permutation of `Sym2 (Site 2)` (`Equiv.ofBijective`). (Grimmett 1999, §11.2.) [folklore] -/
def dualEdgeEquiv : Sym2 (LatticeModels.Site 2) ≃ Sym2 (LatticeModels.Site 2) := Equiv.ofBijective dualEdge dualEdge_bijective

/-- `dualEdgeEquiv` acts as `dualEdge`. [folklore] -/
@[simp] theorem dualEdgeEquiv_apply (e : Sym2 (LatticeModels.Site 2)) : dualEdgeEquiv e = dualEdge e := rfl

/-- The dual configuration in terms of the edge bijection: a lattice pair `e` is dual-open iff
the primal edge `dualEdge⁻¹ e` that it crosses is closed. (Grimmett 1999, §11.2.) [folklore] -/
theorem dualConfig_eq (ω : BondConfig (LatticeModels.Site 2)) :
    dualConfig ω = {e | e ∈ (LatticeModels.zdGraph 2).edgeSet ∧ dualEdgeEquiv.symm e ∉ ω} := by
  ext e
  simp only [dualConfig, Set.mem_sdiff, Set.mem_image, not_exists, not_and, Set.mem_setOf_eq]
  refine and_congr_right fun _ => ⟨fun h hm => h _ hm (by simp [← dualEdgeEquiv_apply]), ?_⟩
  rintro h e' he' rfl
  exact h (by simpa [← dualEdgeEquiv_apply] using he')

/-- **Discharge of `bondPercolation_map_dualConfig`**: the law of the dual configuration under
`P_p` is `P_{1-p}`. Proof: `dualConfig = (E ∖ ·) ∘ (dualEdgeEquiv⁻¹)⁻¹`, the reindexing by the
permutation `dualEdgeEquiv` (which preserves the edge set) preserves the product measure
(Mathlib's `Measure.infinitePi_map_piCongrLeft`), and complementation inside `E` maps each
one-edge law `p δ_{e ∈ E} + (1-p) δ_⊥` to `(1-p) δ_{e ∈ E} + p δ_⊥` (`Measure.infinitePi_map_pi`).
(Grimmett 1999, §11.2, "each edge of the dual is open with probability `1 - p` independently
of all other edges".) [cite: GrimmettPercolation1999, §11.2] -/
theorem bondPercolation_map_dualConfig_holds : bondPercolation_map_dualConfig := by
  intro p
  set E := (LatticeModels.zdGraph 2).edgeSet
  set ψ := dualEdgeEquiv
  set ν : Sym2 (LatticeModels.Site 2) → Measure Prop :=
    fun i => toNNReal p • Measure.dirac (i ∈ E) + toNNReal (σ p) • Measure.dirac False
  set ν' : Sym2 (LatticeModels.Site 2) → Measure Prop :=
    fun i => toNNReal (σ p) • Measure.dirac (i ∈ E) + toNNReal (σ (σ p)) • Measure.dirac False
  set f : (i : Sym2 (LatticeModels.Site 2)) → Prop → Prop := fun i P => i ∈ E ∧ ¬ P
  have hν : (fun a => ν (ψ a)) = ν := by
    funext a
    simp only [ν, ψ, dualEdgeEquiv_apply]
    rw [show (dualEdge a ∈ E) = (a ∈ E) from propext (dualEdge_mem_edgeSet_iff a)]
  have hν' : (fun i => (ν i).map (f i)) = ν' := by
    funext i
    simp only [ν, ν', f]
    rw [Measure.map_add _ _ (Measurable.of_discrete), Measure.map_smul, Measure.map_smul,
      Measure.map_dirac' Measurable.of_discrete, Measure.map_dirac' Measurable.of_discrete,
      add_comm, unitInterval.symm_symm]
    congr 3
    · exact propext ⟨fun h => h.1, fun h => ⟨h, not_false⟩⟩
    · exact propext ⟨fun h => h.2 h.1, fun h => h.elim⟩
  have hcomm : dualConfig ∘ (fun q : Sym2 (LatticeModels.Site 2) → Prop => {i | q i}) =
      (fun q : Sym2 (LatticeModels.Site 2) → Prop => {i | q i}) ∘ (fun x i => f i (x i)) ∘
        (MeasurableEquiv.piCongrLeft (fun _ => Prop) ψ) := by
    funext q
    rw [Function.comp_apply, dualConfig_eq]
    ext e
    simp only [Set.mem_setOf_eq, Function.comp_apply, MeasurableEquiv.coe_piCongrLeft,
      Equiv.piCongrLeft_apply, eq_rec_constant, f]
    rfl
  have hmeas : Measurable dualConfig := by
    refine measurable_set_iff.2 fun e => ?_
    simp only [dualConfig_eq, Set.mem_setOf_eq]
    exact Measurable.and measurable_const (measurable_set_notMem _)
  have hmf : Measurable (fun (x : Sym2 (LatticeModels.Site 2) → Prop) i => f i (x i)) :=
    measurable_pi_lambda _ fun i => (Measurable.of_discrete : Measurable (f i)).comp
      (measurable_pi_apply i)
  rw [bondPercolation, bondPercolation, setBernoulli_eq_map, setBernoulli_eq_map,
    Measure.map_map hmeas measurable_setOf, hcomm, ← Measure.map_map, ← Measure.map_map,
    show (fun i => toNNReal p • Measure.dirac (i ∈ (LatticeModels.zdGraph 2).edgeSet) +
      toNNReal (σ p) • Measure.dirac False) = fun a => ν (ψ a) from hν.symm,
    Measure.infinitePi_map_piCongrLeft, Measure.infinitePi_map_pi, hν']
  · exact fun i => Measurable.of_discrete
  · exact hmf
  · exact MeasurableEquiv.measurable _
  · exact measurable_setOf
  · exact hmf.comp (MeasurableEquiv.measurable _)

end DualityProofs

end

end Percolation.Literature
