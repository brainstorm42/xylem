import Mathlib.MeasureTheory.MeasurableSpace.NCard
import Percolation.Literature.ConstrainedClusters
import Percolation.Literature.HalfSpace
import Percolation.Util.Linter

/-!
# The half-space cluster of the origin, its footprint on `∂ℍ`, and floor-pinned `w`-pairs

Definitions used to state the *low-point identity* `τ_p(0, w) = E_p[N_w(U) / |U ∩ ∂ℍ|]` (`p ≤ p_c`,
bond percolation on `ℤ³`), over the existing notions of `Literature/Basic.lean` (`openConnIn`, `openGraph`)
and `HalfSpace.lean` (`halfSpace d = {x | 0 ≤ x₀}`). Everything is stated for `ℤ^d`, `d ≥ 1`
(`[NeZero d]`, as in `HalfSpace.lean`); the case of interest is `d = 3`, where
`ω : BondConfig (Site 3)` fixes `d` by unification.

## Content

* Sanity check `w = 0`: `halfSpacePinnedPairs ω 0 = U(ω) ∩ ∂ℍ`, so
  `halfSpacePinnedPairCount ω 0 = halfSpaceFootprint ω` (the identity then reads `τ_p(0,0) = 1`).

## Sources

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999: §7.2 p. 148 (paths/percolation "in `A`"),
  §7.3 p. 162 (`ℍ`, `0 ↔ ∞ in ℍ`), Thm. (7.35) p. 163 (`θ_ℍ(p_c) = 0`, which makes `U` a.s. finite at
  `p ≤ p_c`; stated as `BarskyGrimmettNewman1991` in `HalfSpace.lean`, not used here).
* The pinned-pair count `N_w(U)` and the footprint normalisation are an elementary combinatorial
  device (mass transport over the floor `∂ℍ ≅ ℤ^{d-1}`); no published source defines them, hence
  `[folklore]` tags on those declarations.

## Design choices / not here

* `ℕ∞`-valued counts via `Set.encard` (no finiteness is assumed; at `p ≤ p_c` finiteness holds a.s.
  by the Barsky–Grimmett–Newman theorem). Real values for the integrand can be taken via
  `ENat.toENNReal` then `ENNReal.toReal`, or `ENat.toNat`.
* No measure appears here: the identity itself (with `bondPercolation (zdGraph 3) p`, `tau`) is not
  stated in this file.
* The floor `{x | x₀ = 0}` and the raised half-space `{x | 1 ≤ x₀}` are written inline.
-/

noncomputable section

namespace Percolation.Literature

open LatticeModels

variable {d : ℕ} [NeZero d]

/-! ## `{x ↔ y in S}` is measurable for arbitrary `S` -/

omit [NeZero d] in
/-- The event `{x ↔ y in S}` (`openConnIn S x y`) is measurable for every vertex set `S` of a
countable vertex type: for `x ∈ S` it is `{x ↔ y via withinGraph ⊤ S}` (`openConnIn_eq_openConnVia`,
`measurableSet_openConnVia`), and for `x ∉ S` it is empty. (Grimmett 1999, §1.3 / §7.2 p. 148.)
[cite: GrimmettPercolation1999, §7.2 p. 148 (in A)] -/
theorem measurableSet_openConnIn_of_countable {V : Type*} [Countable V] (S : Set V) (x y : V) :
    MeasurableSet (openConnIn S x y : Set (BondConfig V)) := by
  by_cases hx : x ∈ S
  · rw [openConnIn_eq_openConnVia hx]
    exact measurableSet_openConnVia _ x y
  · have h : openConnIn S x y = (∅ : Set (BondConfig V)) :=
      Set.subset_empty_iff.1 fun ω hω => (hx hω.1).elim
    rw [h]
    exact MeasurableSet.empty

/-! ## Measurability in `ω` -/

/-! ## Covariance under horizontal translations (re-rooting at a floor point)

The shift `ω ↦ ω + s` of configurations is `BondConfig.relabel (sym2Equiv (Site.shift s)) ω`. For a
floor point `c ∈ U(ω) ∩ ∂ℍ`, shifting by `-c` moves `c` to the origin, carries `U(ω)` to `U(ω) - c`
(root invariance + translation), and leaves `N_w` and the footprint unchanged — the two invariances
behind the weight `1/|U ∩ ∂ℍ|` in the mass-transport step.
-/

end Percolation.Literature

end
