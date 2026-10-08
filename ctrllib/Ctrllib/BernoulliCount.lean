import Ctrllib.BinomialConfidence

/-!
Bernoulli count-law bridge (atlas obligation R3).

Independent Bernoulli indicators indexed by `Fin n` form a random subset of
the finite index set.  Their subset law is the finite product Bernoulli law;
the cardinality map therefore has the binomial law.  The final corollary
feeds this proved count law into the existing exact binomial confidence-set
coverage theorem.

This module assumes one complete episode per indicator.  It proves no
independence, sensor, controller, plant, or episode-model fact from physical
data, and introduces no probability approximation.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology unitInterval

namespace Ctrllib

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The cardinality of an independent finite family of Bernoulli indicators
has the binomial law.  The indicator family is represented by propositions;
`I i ω` means that trial `i` is a success. -/
theorem hasLaw_fin_indicator_count
    (n : ℕ) (p : I) (ind : Fin n → Ω → Prop)
    (_h_meas : ∀ i, Measurable (ind i))
    (h_law : ∀ i, HasLaw (ind i) (Ber(True, False, p)) P)
    (h_indep : iIndepFun ind P) :
    HasLaw (fun ω => Set.ncard {i | ind i ω}) (Bin(n, p)) P := by
  classical
  let μ : (i : Fin n) → Measure Prop := fun _ => Ber(True, False, p)
  have hpi : HasLaw (fun ω i => ind i ω) (Measure.pi μ) P := by
    simpa [μ] using h_indep.hasLaw_pi h_law
  have hset : HasLaw (fun ω => {i | ind i ω})
      (setBer((Set.univ : Set (Fin n)), p)) P := by
    rw [setBernoulli_eq_map, Measure.infinitePi_eq_pi]
    let f : (Fin n → Prop) → Set (Fin n) := fun q => {i | q i}
    have hf : HasLaw f ((Measure.pi μ).map f) (Measure.pi μ) :=
      { aemeasurable := by fun_prop
        map_eq := rfl }
    simpa [f, μ, Function.comp_def] using hf.fun_comp hpi
  have hcard : HasLaw Set.ncard
      ((setBer((Set.univ : Set (Fin n)), p)).map Set.ncard)
      (setBer((Set.univ : Set (Fin n)), p)) :=
    { aemeasurable := by fun_prop
      map_eq := rfl }
  have hcount : HasLaw (fun ω => Set.ncard {i | ind i ω})
      ((setBer((Set.univ : Set (Fin n)), p)).map Set.ncard) P := by
    simpa [Function.comp_def] using hcard.fun_comp hset
  have hbin : (setBer((Set.univ : Set (Fin n)), p)).map Set.ncard = Bin(n, p) := by
    apply Measure.ext_of_singleton
    intro k
    rw [map_ncard_setBernoulli_singleton (u := (Set.univ : Set (Fin n))) Set.finite_univ,
      binomial_singleton]
    simp
  rw [← hbin]
  exact hcount

/-- Exact binomial confidence-set coverage for the count of an independent
finite Bernoulli indicator family. -/
theorem binomial_upper_confidence_set_coverage_of_fin_indicators
    (n : ℕ) (p : I) {δ : ℝ} (hδ : 0 ≤ δ) (ind : Fin n → Ω → Prop)
    (h_meas : ∀ i, Measurable (ind i))
    (h_law : ∀ i, HasLaw (ind i) (Ber(True, False, p)) P)
    (h_indep : iIndepFun ind P) :
    P.real {ω | p ∉ binomialUpperConfidenceSet n
      (Set.ncard {i | ind i ω}) δ} ≤ δ := by
  apply binomial_upper_confidence_set_coverage_of_hasLaw n p hδ
  exact hasLaw_fin_indicator_count n p ind h_meas h_law h_indep

end Ctrllib

#print axioms Ctrllib.hasLaw_fin_indicator_count
#print axioms Ctrllib.binomial_upper_confidence_set_coverage_of_fin_indicators
