import Mathlib.Data.Set.Card
import Mathlib.Logic.Function.DependsOn
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Order.UpperLower.Basic
import Percolation.Literature.Basic
import Percolation.Util.Linter

/-!
# Increasing events, finite dependence, pivotality and disjoint occurrence

Configurations are random subsets `ω : Set ι` of an index type `ι` (edges for bond percolation,
vertices for site percolation); events are `A : Set (Set ι)`.
Source: Grimmett, *Percolation*, 2nd ed. (1999), §§2.2–2.4.

* **Increasing / decreasing events** are Mathlib's `IsUpperSet A` / `IsLowerSet A` for the
  inclusion order on `Set ι` (with `IsUpperSet.inter`, `IsUpperSet.union`, `isUpperSet_compl`
  from `Mathlib/Order/UpperLower/Basic.lean`); increasing random variables are
  `Monotone (f : Set ι → ℝ)`. We do NOT re-wrap these (Grimmett 1999, §2.1).
* `DeterminedBy A F`: the event `A` depends only on the states of the coordinates in `F`,
  phrased through Mathlib's `DependsOn` applied to indicator functions `χ : ι → Prop`;
  `determinedBy_iff` is the set-theoretic characterisation. `IsLocalEvent A`: `A` is a
  cylinder (finite-dimensional) event (Grimmett 1999, §2.2).

Mathlib anchors used: `IsUpperSet`, `DependsOn`, `Xor`, `Set.encard`, `Set.instMeasurableSpace` (the
product σ-algebra on `Set ι`, under which `setBernoulli` lives). Mathlib has no notion of pivotality
or disjoint occurrence.

-/

namespace Percolation.Literature

variable {ι : Type*}

/-! ### Finite dependence -/

/-- The event `A ⊆ Set ι` is *determined by* the coordinates in `F ⊆ ι`: whether `ω ∈ A`
depends only on `ω ∩ F`. Defined via Mathlib's `DependsOn` for the indicator function
`χ : ι → Prop` of `ω`. (Grimmett 1999, §2.2, events "defined in terms of the states of
finitely many edges".) [cite: GrimmettPercolation1999, §2.2 (events defined in terms of finitely many edges)] -/
def DeterminedBy (A : Set (Set ι)) (F : Set ι) : Prop :=
  DependsOn (fun χ : ι → Prop => {i | χ i} ∈ A) F

/-- Set-theoretic form of `DeterminedBy`: configurations agreeing on `F` agree on `A`.
(Grimmett 1999, §2.2.) [cite: GrimmettPercolation1999, §2.2] -/
theorem determinedBy_iff (A : Set (Set ι)) (F : Set ι) :
    DeterminedBy A F ↔ ∀ ω ω' : Set ι, ω ∩ F = ω' ∩ F → (ω ∈ A ↔ ω' ∈ A) := by
  constructor
  · intro h ω ω' hF
    have key : ∀ i ∈ F, (i ∈ ω) = (i ∈ ω') := fun i hi =>
      propext ⟨fun hω => ((Set.ext_iff.1 hF i).1 ⟨hω, hi⟩).1,
        fun hω' => ((Set.ext_iff.1 hF i).2 ⟨hω', hi⟩).1⟩
    have := h (x := fun i => i ∈ ω) (y := fun i => i ∈ ω') key
    simpa using this
  · intro h χ χ' hF
    refine propext (h {i | χ i} {i | χ' i} ?_)
    ext i
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    exact ⟨fun ⟨hχ, hi⟩ => ⟨(hF i hi) ▸ hχ, hi⟩, fun ⟨hχ, hi⟩ => ⟨(hF i hi) ▸ hχ, hi⟩⟩

/-- `A` is a *local* (cylinder, finite-dimensional) event: it is determined by finitely many
coordinates. (Grimmett 1999, §2.2.) [cite: GrimmettPercolation1999, §2.2] -/
def IsLocalEvent (A : Set (Set ι)) : Prop :=
  ∃ F : Finset ι, DeterminedBy A (↑F : Set ι)

/-- A local event is measurable for the product σ-algebra on `Set ι`
(`Set.instMeasurableSpace`): it is a finite union of finite-dimensional cylinders.
(Grimmett 1999, §2.2.) [cite: GrimmettPercolation1999, §2.2] -/
def measurableSet_of_isLocalEvent : Prop :=
  ∀ {A : Set (Set ι)} (hA : IsLocalEvent A),
    MeasurableSet A

/-! ### Pivotality -/

/-- The coordinate `i` is *pivotal* for the event `A` in the configuration `ω` if exactly one
of the two configurations `ω ∪ {i}`, `ω \ {i}` (which agree with `ω` off `i`) lies in `A`.
(Grimmett 1999, §2.4, before Thm. (2.25).) [cite: GrimmettPercolation1999, §2.4 (before Thm. (2.25))] -/
def IsPivotal (A : Set (Set ι)) (i : ι) (ω : Set ι) : Prop :=
  Xor (insert i ω ∈ A) (ω \ {i} ∈ A)

/-- The set of coordinates pivotal for `A` in `ω`. (Grimmett 1999, §2.4.) [cite: GrimmettPercolation1999, §2.4] -/
def pivotals (A : Set (Set ι)) (ω : Set ι) : Set ι := {i | IsPivotal A i ω}

/-- Membership in `pivotals`. (Grimmett 1999, §2.4.) [cite: GrimmettPercolation1999, §2.4] -/
@[simp] theorem mem_pivotals (A : Set (Set ι)) (ω : Set ι) (i : ι) :
    i ∈ pivotals A ω ↔ IsPivotal A i ω := Iff.rfl

/-! ### Disjoint occurrence -/

/-- The cylinder of configurations agreeing with `ω` on `K`: `[ω]_K = {ω' | ω'(i) = ω(i) for all i ∈
 K}`. (Grimmett 1999, §2.3.) [cite: GrimmettPercolation1999, §2.3]
-/
def localCylinder (K ω : Set ι) : Set (Set ι) := {ω' | ∀ i ∈ K, i ∈ ω' ↔ i ∈ ω}

/-- `ω` lies in its own cylinder. (Grimmett 1999, §2.3.) [cite: GrimmettPercolation1999, §2.3] -/
@[simp] theorem mem_localCylinder_self (K ω : Set ι) : ω ∈ localCylinder K ω :=
  fun _ _ => Iff.rfl

/-! ### Connection events are increasing -/

section Bond

variable {V : Type*}

/-- Adding open edges preserves open paths: `openGraph` is monotone.
(Grimmett 1999, §2.1.) [cite: GrimmettPercolation1999, §2.1] -/
theorem openGraph_mono : Monotone (openGraph (V := V)) :=
  fun _ _ h => SimpleGraph.fromEdgeSet_mono h

/-- The connection event `{x ↔ y}` is increasing. (Grimmett 1999, §2.1, examples of increasing
events.) [cite: GrimmettPercolation1999, §2.1 (examples of increasing events)] -/
theorem isUpperSet_openConn (x y : V) : IsUpperSet (openConn x y : Set (BondConfig V)) :=
  fun _ _ h hω => hω.mono (openGraph_mono h)

/-- The event `{|C(x)| = ∞}` is increasing. (Grimmett 1999, §2.1.) [cite: GrimmettPercolation1999, §2.1] -/
theorem isUpperSet_percolatesAt (x : V) : IsUpperSet (percolatesAt x : Set (BondConfig V)) :=
  fun _ _ h hω => Set.Infinite.mono (fun _ hy => SimpleGraph.Reachable.mono (openGraph_mono h) hy) hω

end Bond

/-! ### Local events are measurable (discharge of `measurableSet_of_isLocalEvent`) -/

section LocalMeasurable

/-- `DeterminedBy` is monotone in the index set: an event determined by `F` is determined by any
`F' ⊇ F`. (Grimmett 1999, §2.2.) [folklore] -/
theorem DeterminedBy.mono {A : Set (Set ι)} {F F' : Set ι} (h : DeterminedBy A F) (hF : F ⊆ F') :
    DeterminedBy A F' := by
  rw [determinedBy_iff] at h ⊢
  intro ω ω' hω
  refine h ω ω' ?_
  rw [← Set.inter_eq_self_of_subset_left hF, Set.inter_comm F F', ← Set.inter_assoc,
    ← Set.inter_assoc, hω]

/-- The intersection of two events determined by `K` is determined by `K`.
(Grimmett 1999, §2.2.) [folklore] -/
theorem DeterminedBy.inter {A B : Set (Set ι)} {K : Set ι} (hA : DeterminedBy A K)
    (hB : DeterminedBy B K) : DeterminedBy (A ∩ B) K := by
  rw [determinedBy_iff] at hA hB ⊢
  intro ω ω' h
  rw [Set.mem_inter_iff, Set.mem_inter_iff, hA ω ω' h, hB ω ω' h]

/-- The sure event is determined by any index set. [folklore] -/
theorem determinedBy_univ (K : Set ι) : DeterminedBy (Set.univ : Set (Set ι)) K := by
  rw [determinedBy_iff]; simp

/-- Cylinders `[ω]_K` over a countable index set `K` are measurable for the product σ-algebra
`Set.instMeasurableSpace` (countable intersections of the coordinate events `{i ∈ ω'}` or their
complements). (Grimmett 1999, §2.2.) [folklore] -/
theorem measurableSet_localCylinder {K : Set ι} (hK : K.Countable) (ω : Set ι) :
    MeasurableSet (localCylinder K ω) := by
  have : localCylinder K ω = ⋂ i ∈ K, {ω' : Set ι | i ∈ ω' ↔ i ∈ ω} := by
    ext ω'; simp [localCylinder]
  rw [this]
  refine MeasurableSet.biInter hK fun i _ => ?_
  by_cases hi : i ∈ ω
  · simpa [hi] using measurableSet_mem i
  · simpa [hi] using measurableSet_notMem i

open Classical in
/-- An event determined by the finite set `F` is the finite union of the cylinders `[T]_F` over
the `T ⊆ F` with `T ∈ A`. (Grimmett 1999, §2.2, "cylinder events".) [folklore] -/
theorem DeterminedBy.eq_biUnion_localCylinder {A : Set (Set ι)} {F : Finset ι}
    (h : DeterminedBy A (↑F : Set ι)) :
    A = ⋃ T ∈ F.powerset.filter (fun T : Finset ι => (↑T : Set ι) ∈ A),
      localCylinder (↑F : Set ι) (↑T : Set ι) := by
  rw [determinedBy_iff] at h
  ext ω
  simp only [Set.mem_iUnion, Finset.mem_filter, Finset.mem_powerset, exists_prop]
  constructor
  · intro hω
    refine ⟨F.filter (· ∈ ω), ⟨Finset.filter_subset _ _, ?_⟩, ?_⟩
    · refine (h _ ω ?_).2 hω
      ext i
      simp only [Finset.coe_filter, Set.mem_inter_iff, Set.mem_setOf_eq, Finset.mem_coe]
      tauto
    · intro i hi
      simp [Finset.mem_coe.1 hi]
  · rintro ⟨T, ⟨-, hTA⟩, hω⟩
    refine (h ω ↑T ?_).2 hTA
    ext i
    simp only [Set.mem_inter_iff, Finset.mem_coe]
    constructor
    · rintro ⟨hiω, hiF⟩; exact ⟨(hω i hiF).1 hiω, hiF⟩
    · rintro ⟨hiT, hiF⟩; exact ⟨(hω i hiF).2 hiT, hiF⟩

/-- An event determined by a finite set of coordinates is measurable. (Grimmett 1999, §2.2.) [folklore] -/
theorem DeterminedBy.measurableSet_of_finset {A : Set (Set ι)} {F : Finset ι}
    (h : DeterminedBy A (↑F : Set ι)) : MeasurableSet A := by
  classical
  rw [h.eq_biUnion_localCylinder]
  exact Finset.measurableSet_biUnion _ fun T _ =>
    measurableSet_localCylinder (F.finite_toSet.countable) _

/-- Discharge of `measurableSet_of_isLocalEvent`: local (cylinder) events are measurable for the
product σ-algebra on `Set ι`, being finite unions of finite-dimensional cylinders.
(Grimmett 1999, §2.2.) [cite: GrimmettPercolation1999, §2.2] -/
theorem measurableSet_of_isLocalEvent_holds : measurableSet_of_isLocalEvent (ι := ι) := by
  intro A ⟨F, hF⟩
  exact hF.measurableSet_of_finset

end LocalMeasurable

end Percolation.Literature
