import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Order.Interval.Set.ProjIcc
import Mathlib.Probability.Distributions.SetBernoulli
import Mathlib.Probability.ProductMeasure
import Percolation.Literature.Crossings
import Percolation.Util.Linter

/-!
# Inhomogeneous product Bernoulli measures

`prodBernoulli p`, for a family of parameters `p : ι → [0,1]`, is the probability measure on `Set ι` under which each
index `i` belongs to the random set independently with probability `p i` — bond percolation with arbitrary edge
probabilities when `ι = Sym2 V`. It is built exactly like Mathlib's `ProbabilityTheory.setBernoulli` (the pullback along
`s ↦ (i ↦ i ∈ s)` of the infinite product of the two-point measures `p i • δ_True + (1 - p i) • δ_False`), of which it
is the inhomogeneous generalisation: with the parameter `p` on `u` and `0` off `u` it is `setBer(u, p)`
(`prodBernoulli_indicator`, proved in `LatticeModels/ProdBernoulliProofs.lean`).

This is the measure in which the gluing statements `Percolation.Continuity.Statements.NearOneGluing` /
`AdditiveGluing` and Kozma–Nitzan's Conjecture 3 (`Percolation.Literature.KozmaNitzan2024_conjecture3`) are stated.
Independence over disjoint index sets, cylinder probabilities, couplings and continuity in the parameters are in the
sibling files `ProdBernoulliIndependence.lean`, `ProdBernoulliAtomExpansion.lean`, `ProdBernoulliCoupling.lean`,
`ProdBernoulliWeightContinuity.lean`, `ProdBernoulliClusterLocality.lean`, `ProdBernoulliBK.lean`.

Reference: G. Grimmett, *Percolation*, 2nd ed. (1999), §1.3 (the product measure `∏_e μ_e`). [cite: GrimmettPercolation1999, §1.3]
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Percolation.Literature.LatticeModels

/-! ### Inhomogeneous product Bernoulli measures -/

section ProdBernoulli

variable {ι : Type*}

/-- The product of Bernoulli measures with parameters `p i` on `Set ι`: each `i` belongs to
the random set independently with probability `p i`. Built exactly like Mathlib's
`ProbabilityTheory.setBernoulli` (which is the special case `p = Set.indicator u (const p)`):
the pullback along `s ↦ (i ↦ i ∈ s)` of the infinite product of the two-point measures
`p i • δ_True + (1 - p i) • δ_False` on `Prop`.
(Grimmett 1999, §1.3, product measure `∏_e μ_e`.) [cite: GrimmettPercolation1999, §1.3 (product measure ∏_e μ_e)] -/
def prodBernoulli (p : ι → unitInterval) : Measure (Set ι) :=
  .comap (fun s i => i ∈ s) <| Measure.infinitePi fun i : ι =>
    unitInterval.toNNReal (p i) • Measure.dirac True +
      unitInterval.toNNReal (unitInterval.symm (p i)) • Measure.dirac False

/-- `prodBernoulli p` is a probability measure (same proof as Mathlib's instance for
`setBernoulli`: `s ↦ (i ↦ i ∈ s)` is the measurable equivalence `MeasurableEquiv.setOf.symm`).
(Grimmett 1999, §1.3.) [cite: GrimmettPercolation1999, §1.3] -/
instance instIsProbabilityMeasureProdBernoulli (p : ι → unitInterval) :
    IsProbabilityMeasure (prodBernoulli p) :=
  MeasurableEquiv.setOf.symm.measurableEmbedding.isProbabilityMeasure_comap <|
    .of_forall fun P => ⟨{i | P i}, rfl⟩

/-- `prodBernoulli` as a pushforward along the measurable equivalence `(ι → Prop) ≃ Set ι`.
(Bookkeeping; cf. Mathlib `setBernoulli_eq_map`.) [folklore] -/
theorem prodBernoulli_eq_map (p : ι → unitInterval) :
    prodBernoulli p = .map (fun q : ι → Prop => {i | q i})
      (Measure.infinitePi fun i : ι =>
        unitInterval.toNNReal (p i) • Measure.dirac True +
          unitInterval.toNNReal (unitInterval.symm (p i)) • Measure.dirac False) :=
  MeasurableEquiv.setOf.comap_symm

/-- With the parameter `p` on `u` and `0` off `u`, `prodBernoulli` is Mathlib's `setBer(u, p)`.
(Grimmett 1999, §1.3.) [cite: GrimmettPercolation1999, §1.3] -/
def prodBernoulli_indicator : Prop :=
  ∀ (u : Set ι) [DecidablePred (· ∈ u)] (p : unitInterval),
    prodBernoulli (fun i => if i ∈ u then p else 0) = setBer(u, p)

end ProdBernoulli

end Percolation.Literature.LatticeModels
