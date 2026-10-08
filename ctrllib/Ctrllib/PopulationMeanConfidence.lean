/-
Population mean lower-tail confidence for a fixed iid holdout loss.

The public theorem starts from independence of the original episode losses.  It derives
independence of centered negated losses by measurable composition, then transports the bounded
sub-Gaussian estimate through negation.  The event is therefore the lower deviation needed for
an upper confidence bound on the population mean; it is not the upper empirical-minus-population
direction exposed by `HoeffdingViewLoss`.

The common-mean premise is the explicit iid-law interface used here.  A controller-level iid
holdout map must supply the original `iIndepFun`, the a.e. finite envelope, and
`∀ i, μ[loss i] = m` before this theorem is applied.
-/
import Ctrllib.HoeffdingViewLoss

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace Ctrllib

section PopulationMeanConfidence

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Independence of centered negated losses follows by composing the original independent
family first with coordinatewise centering and then with negation. -/
theorem centered_neg_iIndepFun_of_iIndepFun
    {loss : ℕ → Ω → ℝ} (h_indep : iIndepFun loss μ) :
    iIndepFun (fun i ω ↦ -(loss i ω - μ[loss i])) μ := by
  have h_centered : iIndepFun (fun i ω ↦ loss i ω - μ[loss i]) μ := by
    have h := h_indep.comp (fun (i : ℕ) (x : ℝ) ↦ x - μ[loss i])
      (fun _ ↦ by fun_prop)
    simpa [Function.comp_def] using h
  have h_neg := h_centered.comp (fun (_ : ℕ) (x : ℝ) ↦ -x) (fun _ ↦ by fun_prop)
  simpa [Function.comp_def] using h_neg

/-- One-sided upper confidence event for the population mean of bounded losses.

The event is `m - empiricalMean ≥ ε`, with the direction needed to upper-bound the population
mean by the observed mean plus a radius.  The proof derives the centered-negated independence
premise rather than assuming it as a theorem input. -/
theorem bounded_view_loss_population_mean_lower_tail
    {loss : ℕ → Ω → ℝ} {a b m ε : ℝ} {n : ℕ} [IsProbabilityMeasure μ]
    (h_indep : iIndepFun loss μ)
    (h_meas : ∀ i, AEMeasurable (loss i) μ)
    (h_bounded : ∀ i, ∀ᵐ ω ∂μ, loss i ω ∈ Set.Icc a b)
    (h_mean : ∀ i, μ[loss i] = m)
    (hn : 0 < n)
    (hε : 0 ≤ ε) :
    μ.real {ω | m - (∑ i ∈ Finset.range n, loss i ω) / n ≥ ε} ≤
      Real.exp (-((n : ℝ) * ε) ^ 2 /
        (2 * (n : ℝ) * ((‖b - a‖₊ / 2) ^ 2))) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h_centered_neg := centered_neg_iIndepFun_of_iIndepFun h_indep
  have h_subG : ∀ i < n,
      HasSubgaussianMGF (fun ω ↦ -(loss i ω - μ[loss i]))
        ((‖b - a‖₊ / 2) ^ 2) μ := by
    intro i hi
    have h := centered_view_loss_hasSubgaussianMGF_of_mem_Icc
      (h_meas i) (h_bounded i)
    convert h.neg using 1
  have h_tail := HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun
    h_centered_neg h_subG (mul_nonneg hn'.le hε)
  have hsum_mean :
      (∑ i ∈ Finset.range n, μ[loss i]) = (n : ℝ) * m := by
    simp_rw [h_mean]
    simp
  have hsum (ω : Ω) :
      (∑ i ∈ Finset.range n, -(loss i ω - μ[loss i])) =
        -(∑ i ∈ Finset.range n, loss i ω) + (n : ℝ) * m := by
    rw [Finset.sum_neg_distrib, Finset.sum_sub_distrib, hsum_mean]
    ring
  have hset :
      {ω | m - (∑ i ∈ Finset.range n, loss i ω) / n ≥ ε} =
        {ω | (n : ℝ) * ε ≤ ∑ i ∈ Finset.range n, -(loss i ω - μ[loss i])} := by
    ext ω
    change (m - (∑ i ∈ Finset.range n, loss i ω) / n ≥ ε) ↔
      ((n : ℝ) * ε ≤ ∑ i ∈ Finset.range n, -(loss i ω - μ[loss i]))
    rw [ge_iff_le]
    have hsum' := hsum ω
    constructor
    · intro h
      have hdiv : (∑ i ∈ Finset.range n, loss i ω) / n ≤ m - ε := by
        linarith
      have hmul : (∑ i ∈ Finset.range n, loss i ω) ≤ (m - ε) * (n : ℝ) :=
        (div_le_iff₀ hn').mp hdiv
      rw [hsum']
      linarith
    · intro h
      have hmul : (∑ i ∈ Finset.range n, loss i ω) ≤ (m - ε) * (n : ℝ) := by
        rw [hsum'] at h
        linarith
      have hdiv : (∑ i ∈ Finset.range n, loss i ω) / n ≤ m - ε :=
        (div_le_iff₀ hn').mpr hmul
      linarith
  rw [hset]
  exact h_tail

end PopulationMeanConfidence

end Ctrllib

#print axioms Ctrllib.centered_neg_iIndepFun_of_iIndepFun
#print axioms Ctrllib.bounded_view_loss_population_mean_lower_tail
