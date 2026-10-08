import Percolation.Literature.HalfSpace
import Percolation.Literature.PercolationEvents
import Percolation.Literature.SubgraphMonotonicity
import Percolation.Util.Linter

/-!
# The Barsky–Grimmett–Newman block argument for `θ_ℍ(p_c) = 0` (Grimmett 1999, §7.3)

## Coordinates

`HalfSpace.lean` takes `ℍ = {x ∈ ℤ³ | 0 ≤ x₀}` (first coordinate), Grimmett takes
`ℍ = ℤ² × ℤ₊` (third coordinate). Throughout this file Grimmett's coordinates `(x_1, x_2, x_3)`
are written `(x 1, x 2, x 0)`: the vertical direction is the coordinate `0 : Fin 3`. So
`B(L,H) = [-L,L]² × [0,H]` becomes `{x | 0 ≤ x 0 ≤ H, |x 1| ≤ L, |x 2| ≤ L}` and Grimmett's
`b_3(m)` (horizontal square) is `square 0 m`, `b_1(m)`, `b_2(m)` are `square 1 m`, `square 2 m`.

## Design choices

* `P_p` in Lemmas (7.36), (7.52) is bond percolation on all of `ℤ³`
  (`bondPercolation (zdGraph 3) p`): the event `{B(L,H) is good}` involves seeds `b(x)`, `x ∈ S`,
  which stick out of `B(L,H)` and below height `0` (p. 168: "the squares `b(x)` … do not
  intersect the interior of `B(L,H)`"). `θ_ℍ` is, as in `HalfSpace.lean`, `theta` of the induced
  half-space graph at the origin.

## References

* G. Grimmett, *Percolation*, 2nd ed., Grundlehren 321, Springer 1999, §7.3: Thm. (7.35) p. 163,
  definitions pp. 163–164, Lemma (7.36) p. 164, Lemma (7.52) p. 169, proof of (7.35) p. 169, sketch of
  the proof of (7.52) pp. 169–173.
* D. J. Barsky, G. R. Grimmett, C. M. Newman, *Percolation in half-spaces: equality of critical
  densities and continuity of the percolation probability*, Probab. Theory Related Fields 90
  (1991) 111–148 (and its companion "Dynamic renormalization and continuity of the percolation
  transition in orthants", 1991).
-/

noncomputable section

namespace Percolation.Literature

open MeasureTheory ProbabilityTheory LatticeModels unitInterval
open scoped ProbabilityTheory ENNReal

/-! ## Continuity of `p ↦ P_p(A)` for events depending on finitely many edges -/

section Continuity

variable {V : Type*}

/-- The `P_p`-probability of a finite-dimensional cylinder `[T]_F` (configurations agreeing with
`T` on the finite edge set `F`) is a continuous function of `p ∈ [0,1]`: it is the finite product
`∏_{e ∈ F} μ_e({e ∈ T})` of one-edge Bernoulli masses, each affine in `p` (Grimmett 1999, §7.3
p. 162: "`P_p(A)` is a finite polynomial in `p`, since `B` is finite").
[cite: GrimmettPercolation1999, §7.3 p. 162] -/
theorem continuous_bondPercolation_real_localCylinder (G : SimpleGraph V) (F : Finset (Sym2 V))
    (T : Set (Sym2 V)) :
    Continuous fun p : unitInterval =>
      (bondPercolation G p).real (localCylinder (↑F : Set (Sym2 V)) T) := by
  classical
  have hpre : (fun q : Sym2 V → Prop => {i | q i}) ⁻¹' localCylinder (↑F : Set (Sym2 V)) T =
      Set.pi (↑F : Set (Sym2 V)) (fun e => {r : Prop | r ↔ e ∈ T}) := by
    ext q
    simp [localCylinder, Set.mem_pi]
  have key : ∀ p : unitInterval,
      (bondPercolation G p).real (localCylinder (↑F : Set (Sym2 V)) T) =
        ∏ e ∈ F, ((toNNReal p • Measure.dirac (e ∈ G.edgeSet) +
          toNNReal (σ p) • Measure.dirac False : Measure Prop) {r : Prop | r ↔ e ∈ T}).toReal := by
    intro p
    rw [measureReal_def, bondPercolation, setBernoulli_apply', hpre,
      Measure.infinitePi_pi _ (fun _ _ => MeasurableSet.of_discrete), ENNReal.toReal_prod]
  simp_rw [key]
  refine continuous_finsetProd _ fun e _ => ?_
  have hval : ∀ p : unitInterval,
      ((toNNReal p • Measure.dirac (e ∈ G.edgeSet) +
          toNNReal (σ p) • Measure.dirac False : Measure Prop) {r : Prop | r ↔ e ∈ T}).toReal =
        (p : ℝ) * (Measure.dirac (e ∈ G.edgeSet) {r : Prop | r ↔ e ∈ T}).toReal +
          (1 - (p : ℝ)) * (Measure.dirac False {r : Prop | r ↔ e ∈ T}).toReal := by
    intro p
    rw [Measure.coe_add, Pi.add_apply, Measure.coe_nnreal_smul_apply,
      Measure.coe_nnreal_smul_apply, ENNReal.toReal_add (by finiteness) (by finiteness),
      ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.coe_toReal,
      coe_toNNReal, coe_toNNReal, coe_symm_eq]
  simp_rw [hval]
  fun_prop

/-- **`P_p(A)` is continuous in `p` for a finite-dimensional event `A`** (Grimmett 1999, §7.3,
p. 162: "`P_p(A)` is a finite polynomial in `p`, since `B` is finite. Therefore `P_p(A)` is a
continuous function of `p`"; p. 169: "The event `{B(L,H) is good}` depends on the states of a
finite set of edges only, whence `P_p(B(L,H) is good)` is a continuous function of `p`"). If
`A` is determined by the states of the edges in a finite set `F`, then
`p ↦ P_p(A)` is continuous on `[0,1]`: `A` is the disjoint union of the cylinders `[T]_F`,
`T ⊆ F`, `T ∈ A`. [cite: GrimmettPercolation1999, §7.3 p. 162 and p. 169] -/
theorem continuous_bondPercolation_real_of_determinedBy (G : SimpleGraph V)
    {A : Set (BondConfig V)} {F : Finset (Sym2 V)} (hA : DeterminedBy A (↑F : Set (Sym2 V))) :
    Continuous fun p : unitInterval => (bondPercolation G p).real A := by
  classical
  have hdisj : (↑(F.powerset.filter fun T : Finset (Sym2 V) => (↑T : Set (Sym2 V)) ∈ A) :
      Set (Finset (Sym2 V))).PairwiseDisjoint
        fun T : Finset (Sym2 V) => localCylinder (↑F : Set (Sym2 V)) (↑T : Set (Sym2 V)) := by
    intro T hT T' hT' hne
    simp only [Finset.coe_filter, Finset.mem_powerset, Set.mem_setOf_eq] at hT hT'
    rw [Function.onFun, Set.disjoint_left]
    intro ω hω hω'
    apply hne
    ext e
    constructor
    · intro he
      exact (hω' e (hT.1 he)).1 ((hω e (hT.1 he)).2 he)
    · intro he
      exact (hω e (hT'.1 he)).1 ((hω' e (hT'.1 he)).2 he)
  have hsum : ∀ p : unitInterval, (bondPercolation G p).real A =
      ∑ T ∈ F.powerset.filter (fun T : Finset (Sym2 V) => (↑T : Set (Sym2 V)) ∈ A),
        (bondPercolation G p).real (localCylinder (↑F : Set (Sym2 V)) (↑T : Set (Sym2 V))) := by
    intro p
    conv_lhs => rw [DeterminedBy.eq_biUnion_localCylinder hA]
    exact measureReal_biUnion_finset hdisj
      (fun T _ => measurableSet_localCylinder F.finite_toSet.countable _)
  simp_rw [hsum]
  exact continuous_finsetSum _ fun T _ => continuous_bondPercolation_real_localCylinder G F _

/-- Corollary: `p ↦ P_p(A)` is continuous for every local (cylinder) event `A`.
[cite: GrimmettPercolation1999, §7.3 p. 162] -/
theorem continuous_bondPercolation_real_of_isLocalEvent (G : SimpleGraph V)
    {A : Set (BondConfig V)} (hA : IsLocalEvent A) :
    Continuous fun p : unitInterval => (bondPercolation G p).real A := by
  obtain ⟨F, hF⟩ := hA
  exact continuous_bondPercolation_real_of_determinedBy G hF

end Continuity

end Percolation.Literature

end
