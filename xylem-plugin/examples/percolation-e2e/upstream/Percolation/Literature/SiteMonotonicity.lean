import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Combinatorics.SimpleGraph.Dart
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Percolation.Literature.SiteConnectionTools
import Percolation.Literature.SitePercolationMeasure
import Percolation.Util.Linter

/-!
# Monotonicity in `p` of site percolation: local increasing events and `θ`

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999: §1.4 (1.11) and p. 14 (`θ` non-decreasing,
  `θ = lim P(0 ⟷ ∂B(n))`), Thm. 2.1 (monotonicity of increasing events), §2.4 (2.28).
* H. Kesten, *Percolation theory for mathematicians*, Birkhäuser 1982, §3.4 (3.62).

## Mathlib / this library

Mathlib: `MeasureTheory.tendsto_measure_iInter_le` (continuity from above along `⋂_{j ≤ i}`),
`exists_surjective_nat` (enumeration of a countable type). No percolation in Mathlib.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology

namespace Percolation.Literature

variable {V : Type*}

/-! ### `DeterminedBy` under unions and intersections -/

/-- An arbitrary intersection of events determined by `K` is determined by `K`. [folklore] -/
theorem DeterminedBy.iInter {ι : Sort*} {A : ι → Set (Set V)} {K : Set V}
    (h : ∀ i, DeterminedBy (A i) K) : DeterminedBy (⋂ i, A i) K := by
  rw [determinedBy_iff]
  intro ω ω' hω
  simp only [Set.mem_iInter]
  exact forall_congr' fun i => (determinedBy_iff _ _).1 (h i) ω ω' hω

/-- An arbitrary union of events determined by `K` is determined by `K`. [folklore] -/
theorem DeterminedBy.iUnion {ι : Sort*} {A : ι → Set (Set V)} {K : Set V}
    (h : ∀ i, DeterminedBy (A i) K) : DeterminedBy (⋃ i, A i) K := by
  rw [determinedBy_iff]
  intro ω ω' hω
  simp only [Set.mem_iUnion]
  exact exists_congr fun i => (determinedBy_iff _ _).1 (h i) ω ω' hω

/-- The complement of an event determined by `K` is determined by `K`. [folklore] -/
theorem DeterminedBy.compl {A : Set (Set V)} {K : Set V} (h : DeterminedBy A K) :
    DeterminedBy Aᶜ K := by
  rw [determinedBy_iff] at h ⊢
  intro ω ω' hω
  rw [Set.mem_compl_iff, Set.mem_compl_iff, h ω ω' hω]

/-- The event `{v open}` is determined by the site `v`. [folklore] -/
theorem determinedBy_mem (v : V) : DeterminedBy {ω : SiteConfig V | v ∈ ω} ({v} : Set V) := by
  rw [determinedBy_iff]
  intro ω ω' h
  have := Set.ext_iff.1 h v
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff, and_true] at this
  exact this

end Percolation.Literature
