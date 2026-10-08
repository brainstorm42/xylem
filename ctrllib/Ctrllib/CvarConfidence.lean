import Ctrllib.CvarPopulation
import Ctrllib.CvarInfForm
import Ctrllib.PopulationMeanConfidence
import Mathlib.Probability.IdentDistrib

/-!
# Population CVaR certificates from independent validation losses

The threshold is fixed before validation, or selected from a fixed finite
family with a simultaneous union bound. This is a Hoeffding validation route,
not the unproved DKW/order-statistic bound for the unrestricted empirical
CVaR minimizer. The sample losses have the same law as the population loss;
independence is across complete episodes, not time points within an episode.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace Ctrllib

/-- Empirical hinge objective plus a confidence radius in mean-hinge units. -/
noncomputable def cvarValidationUpper (α τ ε : ℝ) (loss : ℕ → ℝ) (n : ℕ) : ℝ :=
  τ + (1 / (1 - α)) * ((∑ i ∈ Finset.range n, max (loss i - τ) 0) / n + ε)

/-- The validation expression uses the existing equal-weight finite objective. -/
theorem cvarValidationUpper_eq_cvarObj {α τ ε : ℝ} {loss : ℕ → ℝ} {n : ℕ}
    (hn : 0 < n) (hα : α < 1) :
    cvarValidationUpper α τ ε loss n =
      cvarObj α (fun i : Fin n => loss i) τ + ε / (1 - α) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hα' : (1 - α : ℝ) ≠ 0 := by linarith
  unfold cvarValidationUpper cvarObj
  rw [Fin.sum_univ_eq_sum_range (fun i => max (loss i - τ) 0)]
  field_simp
  ring

section Confidence

variable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
  {μ : Measure Ω} {ν : Measure Ξ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- Any fixed threshold at or above the lower support bound yields an upper
population CVaR certificate, with an explicit failure-probability bound. -/
theorem cvarPop_fixed_threshold_failure_le
    {loss : ℕ → Ω → ℝ} {Z : Ξ → ℝ} {a b α τ ε : ℝ} {n : ℕ}
    (hZ : Integrable Z ν) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hab : a ≤ b) (hτ : a ≤ τ) (hε : 0 ≤ ε) (hn : 0 < n)
    (h_indep : iIndepFun loss μ)
    (h_law : ∀ i, IdentDistrib (loss i) Z μ ν)
    (h_bounded : ∀ᵐ ξ ∂ν, Z ξ ∈ Set.Icc a b) :
    μ.real {ω | cvarPop α ν Z > cvarValidationUpper α τ ε (fun i => loss i ω) n} ≤
      Real.exp (-((n : ℝ) * ε) ^ 2 /
        (2 * (n : ℝ) * ((‖b - a‖₊ / 2) ^ 2))) := by
  let hinge : ℝ → ℝ := fun z => max (z - τ) 0
  have hhinge : Measurable hinge := by fun_prop
  have hlaws (i : ℕ) : IdentDistrib (fun ω => hinge (loss i ω)) (fun ξ => hinge (Z ξ)) μ ν := by
    simpa [Function.comp_def] using (h_law i).comp hhinge
  have hind : iIndepFun (fun i ω => hinge (loss i ω)) μ := by
    simpa [Function.comp_def] using h_indep.comp (fun _ => hinge) (fun _ => hhinge)
  have hb (i : ℕ) : ∀ᵐ ω ∂μ, hinge (loss i ω) ∈ Set.Icc 0 (b - a) := by
    have hs := (h_law i).symm.ae_mem_snd measurableSet_Icc h_bounded
    filter_upwards [hs] with ω hω
    refine ⟨le_max_right _ _, max_le ?_ (sub_nonneg.mpr hab)⟩
    linarith [hω.2]
  have hm (i : ℕ) : (∫ ω, hinge (loss i ω) ∂μ) = ∫ ξ, hinge (Z ξ) ∂ν :=
    (hlaws i).integral_eq
  have htail := bounded_view_loss_population_mean_lower_tail hind
    (fun i => (hlaws i).aemeasurable_fst) hb hm hn hε
  have hpop := cvarPop_le_obj hZ hα0 hα1 τ
  have hρ : 0 < 1 / (1 - α) := div_pos zero_lt_one (by linarith)
  have hsubset :
      {ω | cvarPop α ν Z > cvarValidationUpper α τ ε (fun i => loss i ω) n} ⊆
      {ω | (∫ ξ, hinge (Z ξ) ∂ν) -
        (∑ i ∈ Finset.range n, hinge (loss i ω)) / n ≥ ε} := by
    intro ω hω
    change cvarPop α ν Z > τ + (1 / (1 - α)) *
      ((∑ i ∈ Finset.range n, hinge (loss i ω)) / n + ε) at hω
    change cvarPop α ν Z ≤ τ + (1 / (1 - α)) * (∫ ξ, hinge (Z ξ) ∂ν) at hpop
    change ε ≤ (∫ ξ, hinge (Z ξ) ∂ν) -
      (∑ i ∈ Finset.range n, hinge (loss i ω)) / n
    by_contra hh
    have hle : (∫ ξ, hinge (Z ξ) ∂ν) ≤
        (∑ i ∈ Finset.range n, hinge (loss i ω)) / n + ε := by linarith
    have hscaled := mul_le_mul_of_nonneg_left hle hρ.le
    linarith
  have hmeasure := measureReal_mono (μ := μ) hsubset
  exact hmeasure.trans (by simpa using htail)

/-- A finite predetermined family permits data-dependent threshold selection.
The union bound accounts for every candidate, including the one selected after
observing the sample. Candidates and their radii are fixed parameters. -/
theorem cvarPop_finite_threshold_selection_failure_le
    {I : Type*} [Fintype I]
    {loss : ℕ → Ω → ℝ} {Z : Ξ → ℝ} {a b α : ℝ} {n : ℕ}
    (τ ε : I → ℝ) (select : Ω → I)
    (hZ : Integrable Z ν) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hab : a ≤ b) (hτ : ∀ i, a ≤ τ i) (hε : ∀ i, 0 ≤ ε i) (hn : 0 < n)
    (h_indep : iIndepFun loss μ)
    (h_law : ∀ i, IdentDistrib (loss i) Z μ ν)
    (h_bounded : ∀ᵐ ξ ∂ν, Z ξ ∈ Set.Icc a b) :
    μ.real {ω | cvarPop α ν Z >
      cvarValidationUpper α (τ (select ω)) (ε (select ω)) (fun i => loss i ω) n} ≤
      ∑ j : I, Real.exp (-((n : ℝ) * ε j) ^ 2 /
        (2 * (n : ℝ) * ((‖b - a‖₊ / 2) ^ 2))) := by
  let bad (j : I) : Set Ω :=
    {ω | cvarPop α ν Z > cvarValidationUpper α (τ j) (ε j) (fun i => loss i ω) n}
  have hsubset :
      {ω | cvarPop α ν Z >
        cvarValidationUpper α (τ (select ω)) (ε (select ω)) (fun i => loss i ω) n} ⊆
      ⋃ j, bad j := by
    intro ω hω
    exact Set.mem_iUnion.mpr ⟨select ω, hω⟩
  calc
    _ ≤ μ.real (⋃ j, bad j) := measureReal_mono hsubset
    _ ≤ ∑ j : I, μ.real (bad j) := measureReal_iUnion_fintype_le bad
    _ ≤ _ := Finset.sum_le_sum (fun j _ =>
      cvarPop_fixed_threshold_failure_le hZ hα0 hα1 hab (hτ j) (hε j) hn
        h_indep h_law h_bounded)

/-- Combine validation of reconstructed losses with an independently justified
almost-sure upper error on the true loss. The sampling radius and estimation
error remain separate additive terms. -/
theorem cvarPop_finite_threshold_failure_le_of_loss_error
    {I : Type*} [Fintype I]
    {loss : ℕ → Ω → ℝ} {Z Y : Ξ → ℝ} {a b α η : ℝ} {n : ℕ}
    (τ ε : I → ℝ) (select : Ω → I)
    (hZ : Integrable Z ν) (hY : Integrable Y ν)
    (herror : ∀ᵐ ξ ∂ν, Z ξ ≤ Y ξ + η)
    (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hab : a ≤ b) (hτ : ∀ i, a ≤ τ i) (hε : ∀ i, 0 ≤ ε i) (hn : 0 < n)
    (h_indep : iIndepFun loss μ)
    (h_law : ∀ i, IdentDistrib (loss i) Y μ ν)
    (h_bounded : ∀ᵐ ξ ∂ν, Y ξ ∈ Set.Icc a b) :
    μ.real {ω | cvarPop α ν Z >
      cvarValidationUpper α (τ (select ω)) (ε (select ω)) (fun i => loss i ω) n + η} ≤
      ∑ j : I, Real.exp (-((n : ℝ) * ε j) ^ 2 /
        (2 * (n : ℝ) * ((‖b - a‖₊ / 2) ^ 2))) := by
  have htransfer := cvarPop_le_of_ae_le_add hZ hY hα0 hα1 herror
  have hsubset :
      {ω | cvarPop α ν Z >
        cvarValidationUpper α (τ (select ω)) (ε (select ω)) (fun i => loss i ω) n + η} ⊆
      {ω | cvarPop α ν Y >
        cvarValidationUpper α (τ (select ω)) (ε (select ω)) (fun i => loss i ω) n} := by
    intro ω hω
    change cvarPop α ν Z > _ at hω
    change cvarPop α ν Y > _
    linarith
  exact (measureReal_mono hsubset).trans
    (cvarPop_finite_threshold_selection_failure_le τ ε select hY hα0 hα1
      hab hτ hε hn h_indep h_law h_bounded)

end Confidence

end Ctrllib

#print axioms Ctrllib.cvarValidationUpper_eq_cvarObj
#print axioms Ctrllib.cvarPop_fixed_threshold_failure_le
#print axioms Ctrllib.cvarPop_finite_threshold_selection_failure_le
#print axioms Ctrllib.cvarPop_finite_threshold_failure_le_of_loss_error
