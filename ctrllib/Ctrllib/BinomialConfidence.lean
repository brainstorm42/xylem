/-
Exact binomial lower-tail confidence for an iid episode-violation count.

`binomialLowerTail n r p` is the finite polynomial
`P_p{Bin(n,p) ≤ r}`.  The count `r` is deliberately allowed to be any
natural number; the `min r n` cap makes the polynomial agree with the
binomial law even outside its support.  The adaptive rejection theorem is
proved from the finite support and monotonicity of the CDF.  It therefore
handles the data-dependent rejection cutoff instead of assuming a fixed
cutoff in advance.

The confidence-set theorem is the exact inversion of that test: for a
realized count `r`, retain a candidate probability `p` when its binomial
lower tail is larger than `δ`.  Coverage is over the count drawn from the
true `Bin(n,p)` law.  It does not turn a nominal-model count law into a
physical guarantee for an unmodelled controller or plant.
-/
import Mathlib.Probability.Distributions.Binomial

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology unitInterval

namespace Ctrllib

noncomputable def binomialLowerTail (n r : ℕ) (p : I) : ℝ :=
  ∑ k ∈ Finset.Iic (min r n), (n.choose k : ℝ) * (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (n - k)

lemma binomialLowerTail_of_le {n r : ℕ} (hr : r ≤ n) (p : I) :
    binomialLowerTail n r p =
      ∑ k ∈ Finset.Iic r, (n.choose k : ℝ) * (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (n - k) := by
  simp [binomialLowerTail, Nat.min_eq_left hr]

lemma binomial_real_Iic (n r : ℕ) (p : I) :
    (Bin(n, p)).real (Set.Iic r) = binomialLowerTail n r p := by
  classical
  rw [ProbabilityTheory.binomial_eq_sum_dirac]
  simp only [Measure.real, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply' _ measurableSet_Iic, smul_eq_mul]
  rw [ENNReal.toReal_sum]
  · have hterm (x : ℕ) :
        (ENNReal.ofReal ((n.choose x : ℝ) * (p : ℝ) ^ x * (1 - (p : ℝ)) ^ (n - x)) *
            (Set.Iic r).indicator 1 x).toReal =
        if x ≤ r then (n.choose x : ℝ) * (p : ℝ) ^ x * (1 - (p : ℝ)) ^ (n - x)
        else 0 := by
      by_cases hx : x ≤ r <;> simp [Set.indicator, hx,
        ENNReal.toReal_ofReal (ProbabilityTheory.binomial_nonneg :
          (0 : ℝ) ≤ (n.choose x : ℝ) * (p : ℝ) ^ x * (1 - (p : ℝ)) ^ (n - x))]
    simp_rw [hterm]
    rw [← Finset.sum_filter]
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_Iic]
    omega
  · intro a ha
    by_cases h : a ≤ r <;> simp [Set.indicator, h]

lemma binomialLowerTail_of_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℕ} (n r : ℕ) (p : I)
    (hX : HasLaw X (Bin(n, p)) P) :
    P.real {ω | X ω ≤ r} = binomialLowerTail n r p := by
  rw [hX.measureReal_eq (p := fun x : ℕ ↦ x ≤ r) measurableSet_Iic]
  change (Bin(n, p)).real (Set.Iic r) = binomialLowerTail n r p
  exact binomial_real_Iic n r p

lemma binomialLowerTail_mono (n r s : ℕ) (p : I) (hrs : r ≤ s) :
    binomialLowerTail n r p ≤ binomialLowerTail n s p := by
  rw [← binomial_real_Iic n r p, ← binomial_real_Iic n s p]
  exact measureReal_mono (Set.Iic_subset_Iic.2 hrs)

/-- The exact upper confidence set obtained by inverting the binomial lower tail. -/
def binomialUpperConfidenceSet (n r : ℕ) (δ : ℝ) : Set I :=
  {p | δ < binomialLowerTail n r p}

theorem binomial_lower_tail_adaptive_rejection (n : ℕ) (p : I) {δ : ℝ}
    (hδ : 0 ≤ δ) :
    (Bin(n, p)).real {r | binomialLowerTail n r p ≤ δ} ≤ δ := by
  classical
  let A : Set ℕ := {r | binomialLowerTail n r p ≤ δ}
  let S : Finset ℕ := (Finset.Iic n).filter (fun r => r ∈ A)
  change (Bin(n, p)).real A ≤ δ
  have hsupport : ∀ᵐ x ∂Bin(n, p), x ≤ n :=
    ProbabilityTheory.ae_le_of_hasLaw_binomial (ProbabilityTheory.HasLaw.id)
  have hAae : A =ᵐ[Bin(n, p)] (Set.inter A (Set.Iic n)) := by
    filter_upwards [hsupport] with x hx
    apply propext
    change (x ∈ A) ↔ (x ∈ A ∧ x ≤ n)
    constructor
    · intro hA
      exact ⟨hA, hx⟩
    · exact And.left
  have hAeq : (Bin(n, p)).real A = (Bin(n, p)).real (Set.inter A (Set.Iic n)) := by
    simp only [Measure.real, MeasureTheory.measure_congr hAae]
  by_cases hS : S.Nonempty
  · let c : ℕ := S.max' hS
    have hcS : c ∈ S := Finset.max'_mem S hS
    have hFc : binomialLowerTail n c p ≤ δ := by
      exact (Finset.mem_filter.1 hcS).2
    have hsub : Set.inter A (Set.Iic n) ⊆ Set.Iic c := by
      intro x hx
      have hxS : x ∈ S := by
        exact Finset.mem_filter.2 ⟨by simpa using hx.2, hx.1⟩
      exact Finset.le_max' S x hxS
    calc
      (Bin(n, p)).real A = (Bin(n, p)).real (Set.inter A (Set.Iic n)) := hAeq
      _ ≤ (Bin(n, p)).real (Set.Iic c) := measureReal_mono hsub
      _ = binomialLowerTail n c p := binomial_real_Iic n c p
      _ ≤ δ := hFc
  · have hAempty : Set.inter A (Set.Iic n) = ∅ := by
      ext x
      constructor
      · intro hx
        exfalso
        have hxS : x ∈ S := Finset.mem_filter.2 ⟨by simpa using hx.2, hx.1⟩
        exact hS ⟨x, hxS⟩
      · simp
    calc
      (Bin(n, p)).real A = (Bin(n, p)).real (Set.inter A (Set.Iic n)) := hAeq
      _ = 0 := by rw [hAempty, measureReal_empty]
      _ ≤ δ := hδ

/-- Exact coverage of the inverted binomial upper confidence set. -/
theorem binomial_upper_confidence_set_coverage (n : ℕ) (p : I) {δ : ℝ}
    (hδ : 0 ≤ δ) :
    (Bin(n, p)).real {r | p ∉ binomialUpperConfidenceSet n r δ} ≤ δ := by
  simpa [binomialUpperConfidenceSet, not_lt] using
    (binomial_lower_tail_adaptive_rejection n p hδ)

/-- The exact confidence-set coverage transported through an arbitrary binomial count. -/
theorem binomial_upper_confidence_set_coverage_of_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℕ}
    (n : ℕ) (p : I) {δ : ℝ} (hδ : 0 ≤ δ)
    (hX : HasLaw X (Bin(n, p)) P) :
    P.real {ω | p ∉ binomialUpperConfidenceSet n (X ω) δ} ≤ δ := by
  rw [hX.measureReal_eq (p := fun r : ℕ ↦ p ∉ binomialUpperConfidenceSet n r δ)
    (MeasurableSet.of_discrete)]
  exact binomial_upper_confidence_set_coverage n p hδ

end Ctrllib

#print axioms Ctrllib.binomialLowerTail_of_le
#print axioms Ctrllib.binomial_real_Iic
#print axioms Ctrllib.binomialLowerTail_of_hasLaw
#print axioms Ctrllib.binomialLowerTail_mono
#print axioms Ctrllib.binomial_lower_tail_adaptive_rejection
#print axioms Ctrllib.binomial_upper_confidence_set_coverage
#print axioms Ctrllib.binomial_upper_confidence_set_coverage_of_hasLaw
