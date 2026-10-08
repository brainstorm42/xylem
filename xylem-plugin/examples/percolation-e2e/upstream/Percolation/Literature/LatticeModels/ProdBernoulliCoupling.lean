import Percolation.Literature.LatticeModels.ProdBernoulli
import Percolation.Util.Linter

/-!
# The monotone coupling of inhomogeneous product Bernoulli measures

This is Grimmett's coupling (1999, §1.3 p. 11, around (1.4); Thm. (2.1) p. 32 with proof p. 33:
"`P_{p₁}(A) ≤ P_{p₂}(A)` for `A` increasing, `p₁ ≤ p₂`"), written for parameters depending on the
coordinate; the constant-parameter case for `bondPercolation` is
`Percolation.Literature.map_configOfLabels_holds` / `theta_mono_holds`
(`Percolation/PercolationProofs`), whose proof is followed line by line.

## Contents

* `map_threshold_volume_restrict_Icc p` — under `U ∼ U[0, 1]`, the indicator `[U ≤ p]` has law
  `p δ_True + (1 - p) δ_False`;
* `prodBernoulli_eq_map_labels p` — `prodBernoulli p` is the law of `η_p = {i | U_i ≤ p_i}` under
  the infinite product of `Leb|[0,1]`;
* `prodBernoulli_mono_of_isUpperSet`, `prodBernoulli_real_mono_of_isUpperSet` — monotonicity in
  the parameters on increasing measurable events (in `ℝ≥0∞` and in `ℝ`).

## References

* G. R. Grimmett, *Percolation*, 2nd ed., Springer (1999), §1.3 (p. 11) and Thm. (2.1) (pp. 32–33).
-/

noncomputable section

namespace Percolation.Literature.LatticeModels

open MeasureTheory Measure ProbabilityTheory
open scoped ENNReal

section ProdBernoulliCoupling

variable {ι : Type*}

/-- The law of one thresholded uniform label: for `p ∈ [0, 1]`, under `U ∼ U[0, 1]` the
indicator `[U ≤ p]` has law `p δ_True + (1 - p) δ_False` — the one-coordinate factor of
`prodBernoulli`. (Grimmett 1999, §1.3, p. 11: "`P(η_p(e) = 0) = 1 - p`, `P(η_p(e) = 1) = p`".)
[cite: GrimmettPercolation1999, §1.3 p. 11] -/
theorem map_threshold_volume_restrict_Icc (p : unitInterval) :
    ((volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1)).map (fun t : ℝ => (t ≤ (p : ℝ))) =
      unitInterval.toNNReal p • Measure.dirac True +
        unitInterval.toNNReal (unitInterval.symm p) • Measure.dirac False := by
  have hp0 : (0 : ℝ) ≤ p := p.2.1
  have hp1 : (p : ℝ) ≤ 1 := p.2.2
  have hmeas : Measurable fun t : ℝ => (t ≤ (p : ℝ)) := measurableSet_setOf.1 measurableSet_Iic
  refine Measure.ext_of_singleton fun a => ?_
  rw [Measure.map_apply hmeas (measurableSet_singleton a),
    Measure.restrict_apply (hmeas (measurableSet_singleton a))]
  rcases Classical.em a with ha | ha
  · obtain rfl : a = True := eq_true ha
    -- `{t ∈ [0,1] | t ≤ p} = [0, p]`, of Lebesgue measure `p`
    have hpre : (fun t : ℝ => (t ≤ (p : ℝ))) ⁻¹' {True} ∩ Set.Icc 0 1 = Set.Icc 0 (p : ℝ) := by
      ext t
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, eq_iff_iff, iff_true,
        Set.mem_Icc]
      constructor
      · rintro ⟨h1, h2, -⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1, h2.trans hp1⟩
    rw [hpre, Real.volume_Icc, sub_zero]
    simp [ENNReal.ofReal_eq_coe_nnreal hp0]
    rfl
  · obtain rfl : a = False := eq_false ha
    -- `{t ∈ [0,1] | ¬ t ≤ p} = (p, 1]`, of Lebesgue measure `1 - p`
    have hpre : (fun t : ℝ => (t ≤ (p : ℝ))) ⁻¹' {False} ∩ Set.Icc 0 1 = Set.Ioc (p : ℝ) 1 := by
      ext t
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, eq_iff_iff, iff_false,
        not_le, Set.mem_Icc, Set.mem_Ioc]
      constructor
      · rintro ⟨h1, -, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, hp0.trans h1.le, h2⟩
    rw [hpre, Real.volume_Ioc]
    simp [ENNReal.ofReal_eq_coe_nnreal (sub_nonneg.2 hp1)]
    rfl

/-- **The monotone coupling has the right marginals.** Under i.i.d. uniform `[0, 1]` labels
`(U_i)_{i ∈ ι}` (the infinite product of `Leb|[0,1]`), the random set `η_p = {i | U_i ≤ p_i}`
has law `prodBernoulli p`. Proof: `η_p = setOf ∘ (U ↦ (i ↦ [U_i ≤ p_i]))`; the push-forward of
the product measure under this coordinatewise map is the product of the one-coordinate
push-forwards (Mathlib's `Measure.infinitePi_map_pi`), and each factor is
`p_i δ_True + (1 - p_i) δ_False` (`map_threshold_volume_restrict_Icc`), the factor of
`prodBernoulli p` (`prodBernoulli_eq_map`). (Grimmett 1999, §1.3, p. 11, coupling around (1.4),
here with coordinate-dependent levels.) [cite: GrimmettPercolation1999, §1.3 p. 11 (coupling around (1.4))] -/
theorem prodBernoulli_eq_map_labels (p : ι → unitInterval) :
    prodBernoulli p =
      (Measure.infinitePi fun _ : ι => (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1)).map
        (fun U : ι → ℝ => {i | U i ≤ (p i : ℝ)}) := by
  have : IsProbabilityMeasure ((volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1)) :=
    ⟨by simp [Real.volume_Icc]⟩
  have hmeas : ∀ i : ι, Measurable fun t : ℝ => (t ≤ (p i : ℝ)) := fun i =>
    measurableSet_setOf.1 measurableSet_Iic
  have hf : (fun U : ι → ℝ => {i | U i ≤ (p i : ℝ)}) =
      (fun q : ι → Prop => {i | q i}) ∘ fun (U : ι → ℝ) (i : ι) => (U i ≤ (p i : ℝ)) := rfl
  rw [prodBernoulli_eq_map, hf,
    ← Measure.map_map (g := fun q : ι → Prop => {i | q i})
      (f := fun (U : ι → ℝ) (i : ι) => (U i ≤ (p i : ℝ)))
      measurable_setOf (measurable_pi_lambda _ fun i => (hmeas i).comp (measurable_pi_apply i)),
    Measure.infinitePi_map_pi _ hmeas]
  congrm Measure.map _ (Measure.infinitePi fun i => ?_)
  exact (map_threshold_volume_restrict_Icc (p i)).symm

/-- **Monotonicity of `prodBernoulli` in the parameters on increasing events**: if `p ≤ q`
pointwise and `A` is an increasing measurable event, then `prodBernoulli p A ≤ prodBernoulli q A`.
Proof as printed (Grimmett 1999, Thm. (2.1), p. 33): realise both measures as laws of `η_p`,
`η_q` (`prodBernoulli_eq_map_labels`); `η_p ⊆ η_q` pointwise since `U_i ≤ p_i ≤ q_i`, and `A`
is increasing. [cite: GrimmettPercolation1999, Thm. (2.1) (2.3) pp. 32–33] -/
theorem prodBernoulli_mono_of_isUpperSet {p q : ι → unitInterval} (hpq : p ≤ q)
    {A : Set (Set ι)} (hA : IsUpperSet A) (hAm : MeasurableSet A) :
    prodBernoulli p A ≤ prodBernoulli q A := by
  have hmeas : ∀ r : ι → unitInterval, Measurable fun U : ι → ℝ => {i | U i ≤ (r i : ℝ)} :=
    fun r => measurable_set_iff.2 fun i =>
      (show Measurable fun t : ℝ => (t ≤ (r i : ℝ)) from
        measurableSet_setOf.1 measurableSet_Iic).comp (measurable_pi_apply i)
  rw [prodBernoulli_eq_map_labels p, prodBernoulli_eq_map_labels q,
    Measure.map_apply (hmeas p) hAm, Measure.map_apply (hmeas q) hAm]
  refine measure_mono fun U hU => ?_
  exact hA (fun i (hi : U i ≤ (p i : ℝ)) => hi.trans (Subtype.coe_le_coe.2 (hpq i))) hU

/-- Real-valued form of `prodBernoulli_mono_of_isUpperSet`: `(prodBernoulli p).real A ≤
(prodBernoulli q).real A` for `p ≤ q` and `A` increasing and measurable.
[cite: GrimmettPercolation1999, Thm. (2.1) (2.3) pp. 32–33] -/
theorem prodBernoulli_real_mono_of_isUpperSet {p q : ι → unitInterval} (hpq : p ≤ q)
    {A : Set (Set ι)} (hA : IsUpperSet A) (hAm : MeasurableSet A) :
    (prodBernoulli p).real A ≤ (prodBernoulli q).real A :=
  ENNReal.toReal_mono (measure_ne_top _ _) (prodBernoulli_mono_of_isUpperSet hpq hA hAm)

end ProdBernoulliCoupling

end Percolation.Literature.LatticeModels

end
