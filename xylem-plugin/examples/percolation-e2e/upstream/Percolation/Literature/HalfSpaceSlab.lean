import Percolation.Literature.ConstrainedClusters
import Percolation.Literature.FiniteEnergy
import Percolation.Literature.HalfSpaceBGN
import Percolation.Literature.ZeroOneLaw
import Percolation.Util.Linter

/-!
# A constrained open cluster stays inside a region closed under open steps (from the slab step (7.41) of Grimmett's Lemma (7.36))

One geometric lemma used in the block construction of the Barsky–Grimmett–Newman half-space theorem (Grimmett,
*Percolation*, 2nd ed. (1999), §7.3, proof of Lemma (7.36), pp. 165–166): `openClusterIn_subset_of_closed` — the open cluster
of `x` computed inside a step graph `K` is contained in any set that contains `x` and is closed under `K`-steps along open
edges. (In Grimmett's argument this confines the `ℍ*`-cluster of the seed to the slab `S_h` once the exits at level `h` are
closed.)
[cite: GrimmettPercolation1999, §7.3, proof of Lemma (7.36), pp. 165–166]
-/

noncomputable section

namespace Percolation.Literature

open MeasureTheory ProbabilityTheory Filter LatticeModels unitInterval
open scoped ENNReal Topology

namespace BGN

/-! ## The geometric heart: closing the exits of `U(h)` confines the `ℍ*`-cluster to the slab -/

/-- A constrained cluster stays inside any set containing its source and closed under open
steps of the step graph. [folklore] -/
theorem openClusterIn_subset_of_closed {V : Type*} {K : SimpleGraph V} {ω : BondConfig V} {x : V}
    {S : Set V} (hx : x ∈ S) (hS : ∀ u ∈ S, ∀ v, (openGraph ω ⊓ K).Adj u v → v ∈ S) :
    openClusterIn K ω x ⊆ S := by
  intro y hy
  rw [mem_openClusterIn_iff] at hy
  obtain ⟨w⟩ := hy
  induction w with
  | nil => exact hx
  | cons huv _ ih => exact ih (hS _ hx _ huv)

end BGN

end Percolation.Literature

end
