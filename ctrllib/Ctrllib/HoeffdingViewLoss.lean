/-
Hoeffding empirical-mean interface for the bounded view-loss — the reachable half of risk
obligation A6.

This skeleton isolates the mean-concentration route only.  The quantile/DKW half remains a
DOCUMENTED WALL and is not stated or proved here.

Sources:
* the corresponding local note (named by the brief, but absent from this payload at assembly);
* the corresponding local note (A6 scope and the quantile boundary);
* `Mathlib.Probability.Moments.SubGaussian`, copied at
  `the corresponding source note (not bundled).lean:780-784` (`measure_sum_ge_le_of_iIndepFun`),
  `:787-789` (the range specialization), and `:860-866`
  (`hasSubgaussianMGF_of_mem_Icc`).

The public theorem deliberately asks for independence of the *centered* samples, exactly the
family consumed by Mathlib's sum theorem.

Both bodies are proved.  The bounded-RV leg is exactly Mathlib's
`hasSubgaussianMGF_of_mem_Icc`.  The tail leg rides
`HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun`: since `0 < n`, the empirical-mean
event `{ε ≤ (∑ i ∈ range n, X i) / n}` is the same set as `{n * ε ≤ ∑ i ∈ range n, X i}`, so
the sum theorem applies at threshold `n * ε` and returns the stated bound directly.  The
`0 < n` hypothesis is load-bearing for exactly that set rewrite, not decoration.
-/
import Mathlib.Probability.Moments.SubGaussian

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace Ctrllib

/-! ### Bounded view-loss Hoeffding route -/

section HoeffdingViewLoss

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The bounded-RV leg of the route: center a loss in an a.e. interval and obtain Mathlib's
sub-Gaussian parameter.  This is the shape of
`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc`. -/
theorem centered_view_loss_hasSubgaussianMGF_of_mem_Icc
    {loss : Ω → ℝ} {a b : ℝ} [IsProbabilityMeasure μ]
    (h_meas : AEMeasurable loss μ)
    (h_bounded : ∀ᵐ ω ∂μ, loss ω ∈ Set.Icc a b) :
    HasSubgaussianMGF (fun ω ↦ loss ω - μ[loss]) ((‖b - a‖₊ / 2) ^ 2) μ :=
  hasSubgaussianMGF_of_mem_Icc h_meas h_bounded

/-- Upper-tail concentration for the empirical mean of bounded view losses.

The interval and measurability hypotheses feed the bounded-RV lemma above; the independent
centered family feeds `ProbabilityTheory.measure_sum_range_ge_le_of_iIndepFun`.  No identical-
distribution hypothesis is used. -/
theorem bounded_view_loss_empirical_mean_upper_tail
    {loss : ℕ → Ω → ℝ} {a b ε : ℝ} {n : ℕ} [IsProbabilityMeasure μ]
    (h_indep : iIndepFun (fun i ω ↦ loss i ω - μ[loss i]) μ)
    (h_meas : ∀ i, AEMeasurable (loss i) μ)
    (h_bounded : ∀ i, ∀ᵐ ω ∂μ, loss i ω ∈ Set.Icc a b)
    (hn : 0 < n)
    (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ (∑ i ∈ Finset.range n, (loss i ω - μ[loss i])) / n} ≤
      Real.exp (-((n : ℝ) * ε) ^ 2 /
        (2 * (n : ℝ) * ((‖b - a‖₊ / 2) ^ 2))) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h_subG : ∀ i < n,
      HasSubgaussianMGF (fun ω ↦ loss i ω - μ[loss i]) ((‖b - a‖₊ / 2) ^ 2) μ :=
    fun i _ ↦ centered_view_loss_hasSubgaussianMGF_of_mem_Icc (h_meas i) (h_bounded i)
  have h := HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun h_indep h_subG
    (mul_nonneg hn'.le hε)
  push_cast at h
  have hset : {ω | ε ≤ (∑ i ∈ Finset.range n, (loss i ω - μ[loss i])) / n}
      = {ω | (n : ℝ) * ε ≤ ∑ i ∈ Finset.range n, (loss i ω - μ[loss i])} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    rw [le_div_iff₀ hn', mul_comm]
  rw [hset]
  exact h

end HoeffdingViewLoss

end Ctrllib

#print axioms Ctrllib.centered_view_loss_hasSubgaussianMGF_of_mem_Icc
#print axioms Ctrllib.bounded_view_loss_empirical_mean_upper_tail
