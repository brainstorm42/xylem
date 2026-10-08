import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Data.Pi.Interval
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Separation.Hausdorff
import Percolation.Literature.LatticeModels.LatticeGraph
import Percolation.Util.Linter

/-!
# Boxes in `ℤ^d` and thermodynamic (infinite-volume) limits

This file provides the finite-volume bookkeeping used by the infinite-volume statements of the
lattice models of this library:

* `box d L = {-L, …, L}^d ⊆ ℤ^d`, the centred cube of side `2L+1` (Friedli–Velenik 2017, §3.2,
  `B(n)`), with `card_box`, `box_mono`, `zero_mem_box`, `iUnion_coe_box`; the half-open cube
  `halfOpenBox d L = {0, …, L-1}^d`; the cubic annulus `annulus d r R = box d R \ box d r`.

Design choices. Both the box limit (a `Tendsto` along
`atTop : Filter ℕ`) and a genuine van Hove filter are provided; infinite-volume *values* are
`limUnder` (junk if the limit does not exist, always accompanied by an existence theorem where it
is used). `box` is defined through `Fintype.piFinset`; it coincides with
Mathlib's `Finset.Icc (-L) L` for the product locally finite order on `Fin d → ℤ`
(`Pi.Icc_eq`, see `box_eq_Icc`).

Mathlib anchors used rather than re-defined: `Fintype.piFinset`, `Fintype.card_piFinset_const`,
`Int.card_Icc`, `Pi.Icc_eq`, `Filter.atTop`, `Filter.limUnder`, `Filter.Tendsto.limUnder_eq`,
`nhds`. Mathlib's `Finset.box n` is the *hollow* shell `Icc (-n) n \ Icc (-(n-1)) (n-1)` of a
locally finite ordered ring, not the full cube, and there is no van Hove filter in Mathlib; hence
the definitions below.
-/

namespace Percolation.Literature.LatticeModels

open Finset Filter Topology

variable {d : ℕ}

/-! ### Boxes -/

/-- The centred cube `box d L = {-L, …, L}^d ⊆ ℤ^d` of side length `2L+1`
(Friedli–Velenik 2017, §3.2.1, `B(n) = {-n,…,n}^d`, after eq. (3.3)). [cite: FriedliVelenikSMLS2017, §3.2.1 (the boxes B(n), after eq. (3.3))] -/
noncomputable def box (d L : ℕ) : Finset (Site d) :=
  Fintype.piFinset fun _ => Finset.Icc (-(L : ℤ)) L

/-- Membership in `box d L`: every coordinate lies in `[-L, L]`. (Friedli–Velenik 2017, §3.2.) [cite: FriedliVelenikSMLS2017, §3.2] -/
@[simp] theorem mem_box {L : ℕ} {x : Site d} : x ∈ box d L ↔ ∀ i, -(L : ℤ) ≤ x i ∧ x i ≤ L := by
  simp [box, Fintype.mem_piFinset]

/-- `box d L` is Mathlib's order interval `Icc (-L) L` for the product order on `Fin d → ℤ`
(`Pi.Icc_eq`). (Friedli–Velenik 2017, §3.2.) [cite: FriedliVelenikSMLS2017, §3.2] -/
theorem box_eq_Icc (d L : ℕ) : box d L = Finset.Icc (-(L : Site d)) (L : Site d) := by
  rw [Pi.Icc_eq]; rfl

/-- `|box d L| = (2L+1)^d`. (Friedli–Velenik 2017, §3.2.) [cite: FriedliVelenikSMLS2017, §3.2] -/
theorem card_box (d L : ℕ) : #(box d L) = (2 * L + 1) ^ d := by
  rw [box, Fintype.card_piFinset_const, Int.card_Icc]
  congr 1
  omega

/-- Boxes are increasing in `L`. (Friedli–Velenik 2017, §3.2.) [cite: FriedliVelenikSMLS2017, §3.2] -/
theorem box_mono (d : ℕ) : Monotone (box d) := by
  intro L L' h x hx
  rw [mem_box] at hx ⊢
  intro i
  obtain ⟨h₁, h₂⟩ := hx i
  constructor <;> omega

/-- The origin belongs to every box. (Friedli–Velenik 2017, §3.2.) [cite: FriedliVelenikSMLS2017, §3.2] -/
theorem zero_mem_box (d L : ℕ) : (0 : Site d) ∈ box d L := by
  simp

/-- `box d L` is nonempty. (Friedli–Velenik 2017, §3.2.) [cite: FriedliVelenikSMLS2017, §3.2] -/
theorem box_nonempty (d L : ℕ) : (box d L).Nonempty := ⟨0, zero_mem_box d L⟩

/-- The boxes exhaust `ℤ^d`: `⋃_L box d L = ℤ^d`. (Friedli–Velenik 2017, §3.2.) [cite: FriedliVelenikSMLS2017, §3.2] -/
theorem iUnion_coe_box (d : ℕ) :
    ⋃ L : ℕ, ((box d L : Finset (Site d)) : Set (Site d)) = Set.univ := by
  refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ?_
  classical
  refine ⟨Finset.univ.sup fun i => (x i).natAbs, ?_⟩
  rw [Finset.mem_coe, mem_box]
  intro i
  have h : (x i).natAbs ≤ Finset.univ.sup fun i => (x i).natAbs :=
    Finset.le_sup (f := fun i => (x i).natAbs) (Finset.mem_univ i)
  omega

/-- The cubic annulus `box d R \ box d r = {x | r < ‖x‖_∞ ≤ R}` (empty unless `r < R`).
(Cf. Friedli–Velenik 2017, §3.7; percolation arm events, Grimmett 1999, §9.) [cite: FriedliVelenikSMLS2017, §3.7] -/
noncomputable def annulus (d r R : ℕ) : Finset (Site d) := box d R \ box d r

/-- Membership in the annulus. (Friedli–Velenik 2017, §3.7.) [cite: FriedliVelenikSMLS2017, §3.7] -/
@[simp] theorem mem_annulus {r R : ℕ} {x : Site d} :
    x ∈ annulus d r R ↔ x ∈ box d R ∧ x ∉ box d r := mem_sdiff

end Percolation.Literature.LatticeModels
