import Percolation.Literature.HalfSpaceBrickSeeds
import Percolation.Literature.SiteConnectionTools
import Percolation.Util.Linter

/-!
# Symmetry between the subfacets: (7.51) and the "square-root trick" step of Lemma (7.36)

Seventh step of the proof of Lemma (7.36) of Grimmett, *Percolation*, 2nd ed. (1999), §7.3,
pp. 168–169 (finite-size criterion of the Barsky–Grimmett–Newman theorem `θ_ℍ(p_c) = 0`),
proved here:

> "Inequalities (7.49)–(7.50) are not quite good enough for our purpose, since the property of
> being good requires seeds in every 'subfacet' `S_i` of `S` and `T_j` of `T`. This we shall obtain
> by further applications of the FKG inequality. Let `X_j = |{x ∈ T_j : b(0) ↔ x in B(L,H)*,
> b(x) is a seed}|`, `Y_i = …`. By symmetry, the `X_j` (respectively `Y_i`) have the same
> distribution … Therefore, `P(X_1 = 0)⁴ = ∏_j P(X_j = 0) ≤ P(X_j = 0 for all j) ≤ P(X = 0)`
> by the FKG inequality and (7.49) … Similarly, (7.51)."

Contents (coordinates of `HalfSpace.lean`, vertical axis `0`):

* the FKG product step `prob_biInter_ge_prod_of_isLowerSet` (Harris for finitely many decreasing
  events, from `harris_fkg_lower`);

## References

* G. Grimmett, *Percolation*, 2nd ed., Grundlehren 321, Springer 1999, §7.3, proof of
  Lemma (7.36), pp. 168–169, (7.51).
-/

noncomputable section

namespace Percolation.Literature

open MeasureTheory ProbabilityTheory Filter LatticeModels unitInterval
open scoped ENNReal Topology

/-! ## Harris for finitely many decreasing events -/

/-- **`∏_i P_p(D_i) ≤ P_p(⋂_i D_i)` for decreasing measurable events** (Grimmett 1999, Thm. (2.4)
and (2.7); iteration of `harris_fkg_lower`). [cite: GrimmettPercolation1999, Thm. 2.4] -/
theorem prob_biInter_ge_prod_of_isLowerSet {V ι : Type*} (G : SimpleGraph V) (p : unitInterval)
    (s : Finset ι) (D : ι → Set (BondConfig V)) (hD : ∀ i ∈ s, IsLowerSet (D i))
    (hDm : ∀ i ∈ s, MeasurableSet (D i)) :
    ∏ i ∈ s, (bondPercolation G p).real (D i) ≤ (bondPercolation G p).real (⋂ i ∈ s, D i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.set_biInter_insert]
    have hD' : ∀ i ∈ s, IsLowerSet (D i) := fun i hi => hD i (Finset.mem_insert_of_mem hi)
    have hDm' : ∀ i ∈ s, MeasurableSet (D i) := fun i hi => hDm i (Finset.mem_insert_of_mem hi)
    have hI : IsLowerSet (⋂ i ∈ s, D i) := isLowerSet_iInter₂ hD'
    have hIm : MeasurableSet (⋂ i ∈ s, D i) := MeasurableSet.biInter s.countable_toSet hDm'
    calc (bondPercolation G p).real (D j) * ∏ i ∈ s, (bondPercolation G p).real (D i)
        ≤ (bondPercolation G p).real (D j) * (bondPercolation G p).real (⋂ i ∈ s, D i) :=
          mul_le_mul_of_nonneg_left (ih hD' hDm') measureReal_nonneg
      _ ≤ _ := harris_fkg_lower G p (hD j (Finset.mem_insert_self j s)) hI (hDm j (Finset.mem_insert_self j s)) hIm

/-- Hence, if `n` decreasing events have the same probability, `P(D_{i₀})^n ≤ P(⋂ D_i)`.
[cite: GrimmettPercolation1999, §7.3 p. 168 (P(X_1 = 0)^4 ≤ P(X = 0))] -/
theorem prob_pow_le_biInter_of_isLowerSet {V ι : Type*} (G : SimpleGraph V) (p : unitInterval)
    (s : Finset ι) (D : ι → Set (BondConfig V)) (hD : ∀ i ∈ s, IsLowerSet (D i))
    (hDm : ∀ i ∈ s, MeasurableSet (D i)) {c : ℝ} (hc : ∀ i ∈ s, (bondPercolation G p).real (D i) = c) :
    c ^ s.card ≤ (bondPercolation G p).real (⋂ i ∈ s, D i) := by
  rw [← Finset.prod_const, ← Finset.prod_congr rfl hc]
  exact prob_biInter_ge_prod_of_isLowerSet G p s D hD hDm

namespace BGN

/-! ## Signed permutations fixing the vertical axis -/

/-- `|ε| = 1` for a unit `ε` of `ℤ`. [folklore] -/
theorem abs_units_coe (u : ℤˣ) : |(u : ℤ)| = 1 := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> simp

/-- `|ε a| = |a|` for a unit `ε` of `ℤ`. [folklore] -/
theorem abs_units_mul (u : ℤˣ) (a : ℤ) : |(u : ℤ) * a| = |a| := by
  rw [abs_mul, abs_units_coe, one_mul]

end BGN

end Percolation.Literature

end
