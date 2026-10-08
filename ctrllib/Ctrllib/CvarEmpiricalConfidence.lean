import Ctrllib.CvarConfidence
import Ctrllib.CvarGridApproximation

/-!
# Population confidence for unrestricted empirical CVaR

This module composes two existing results.  The finite-family Hoeffding theorem
controls the population CVaR at a threshold selected from a predetermined finite
grid.  The finite-grid approximation theorem then pays `h / (1 - α)` to replace
that grid objective by the unrestricted empirical infimum.  The sample is only
assumed to lie in `[a,b]` almost surely; the algebra below is therefore stated as
an almost-everywhere implication before taking measures.

The result is a confidence statement for a fixed population law and iid episode
losses.  It does not establish that a physical loss map has the stated law,
independence, integrability, support bound, or covering-grid property.  The
failure event uses the strict direction `population CVaR > empirical CVaR + radius`.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace Ctrllib

section EmpiricalConfidence

variable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
  {μ : Measure Ω} {ν : Measure Ξ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

private noncomputable def gridMinIndex (G : Finset ℝ) (hG : G.Nonempty)
    (α : ℝ) {q : ℕ} (Z : Fin q → ℝ) : {g : ℝ // g ∈ G} := by
  classical
  exact ⟨Classical.choose (Finset.exists_min_image G (fun g => cvarObj α Z g) hG),
    (Classical.choose_spec (Finset.exists_min_image G (fun g => cvarObj α Z g) hG)).1⟩

private lemma gridMinIndex_min (G : Finset ℝ) (hG : G.Nonempty)
    (α : ℝ) {q : ℕ} (Z : Fin q → ℝ) (g : {g : ℝ // g ∈ G}) :
    cvarObj α Z (gridMinIndex G hG α Z).1 ≤ cvarObj α Z g.1 := by
  classical
  exact (Classical.choose_spec (Finset.exists_min_image G (fun x => cvarObj α Z x) hG)).2
    g.1 g.2

/-- Raw finite-family form of the population-to-empirical CVaR confidence bridge.

The right-hand side retains the concentration radius emitted by the existing
bounded-mean theorem.  The selected threshold is the minimum of the empirical
objective over `G`; it depends on the sample, while `G` and the common allowance
`η` are fixed before validation.
-/
theorem cvarPop_empirical_cvar_failure_le_raw
    {loss : ℕ → Ω → ℝ} {Z : Ξ → ℝ} {a b α h η : ℝ} {n : ℕ}
    (G : Finset ℝ) (hG : G.Nonempty)
    (hZ : Integrable Z ν) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hab : a ≤ b) (hGsub : ∀ g ∈ G, g ∈ Set.Icc a b)
    (hh : 0 ≤ h) (hη : 0 ≤ η) (hn : 0 < n)
    (hcover : ∀ t ∈ Set.Icc a b, ∃ g ∈ G, |t - g| ≤ h)
    (h_indep : iIndepFun loss μ)
    (h_law : ∀ i, IdentDistrib (loss i) Z μ ν)
    (h_bounded : ∀ᵐ ξ ∂ν, Z ξ ∈ Set.Icc a b) :
    μ.real {ω | cvarPop α ν Z >
      cvarSAA α (fun i : Fin n => loss i ω) + (η + h) / (1 - α)} ≤
      ∑ _g : {g : ℝ // g ∈ G},
        Real.exp (-((n : ℝ) * η) ^ 2 /
          (2 * (n : ℝ) * ((‖b - a‖₊ / 2) ^ 2))) := by
  classical
  let I := {g : ℝ // g ∈ G}
  let τ : I → ℝ := fun g => g.1
  let ε : I → ℝ := fun _ => η
  let select : Ω → I := fun ω =>
    gridMinIndex G hG α (fun i : Fin n => loss i ω)
  have hτ : ∀ i : I, a ≤ τ i := by
    intro i
    exact (hGsub i.1 i.2).1
  have hε : ∀ i : I, 0 ≤ ε i := by
    intro i
    exact hη
  have hfinite := cvarPop_finite_threshold_selection_failure_le
    (τ := τ) (ε := ε) (select := select) hZ hα0 hα1 hab hτ hε hn
    h_indep h_law h_bounded
  have hsample : ∀ᵐ ω ∂μ, ∀ i : Fin n, loss i ω ∈ Set.Icc a b := by
    apply (ae_all_iff).2
    intro i
    exact (h_law i).symm.ae_mem_snd measurableSet_Icc h_bounded
  have hbridge :
      {ω | cvarPop α ν Z >
        cvarSAA α (fun i : Fin n => loss i ω) + (η + h) / (1 - α)} ≤ᵐ[μ]
      {ω | cvarPop α ν Z >
        cvarValidationUpper α (τ (select ω)) (ε (select ω))
          (fun i => loss i ω) n} := by
    filter_upwards [hsample] with ω hω hbad
    let sample : Fin n → ℝ := fun i => loss i ω
    have hgrid := cvarGrid_approximation α sample G a b h hn hα0 hα1
      (fun i => hω i) hG hcover hh
    have hsel : cvarObj α sample (select ω).1 ≤
        G.inf' hG (fun g => cvarObj α sample g) := by
      apply Finset.le_inf' hG
      intro g hg
      exact gridMinIndex_min G hG α sample ⟨g, hg⟩
    have hsel' : G.inf' hG (fun g => cvarObj α sample g) ≤
        cvarObj α sample (select ω).1 := by
      exact Finset.inf'_le (fun g => cvarObj α sample g) (select ω).2
    have hsel_eq : cvarObj α sample (select ω).1 =
        G.inf' hG (fun g => cvarObj α sample g) := le_antisymm hsel hsel'
    have hgrid_upper : cvarObj α sample (select ω).1 ≤
        cvarSAA α sample + h / (1 - α) := by
      rw [hsel_eq]
      linarith [hgrid.2]
    have hval := cvarValidationUpper_eq_cvarObj hn hα1
      (α := α) (τ := (select ω).1) (ε := η) (loss := fun i => loss i ω)
    change cvarPop α ν Z > cvarSAA α sample + (η + h) / (1 - α) at hbad
    change cvarPop α ν Z > cvarValidationUpper α (τ (select ω)) (ε (select ω))
      (fun i => loss i ω) n
    dsimp [sample] at hbad
    dsimp [sample, τ, ε] at hgrid_upper hval ⊢
    rw [hval]
    have hadd : (η + h) / (1 - α) = η / (1 - α) + h / (1 - α) := by ring
    rw [hadd] at hbad
    linarith [hgrid_upper]
  have hmeasure := measure_mono_ae hbridge
  have hmeasure_real :
      μ.real {ω | cvarPop α ν Z >
        cvarSAA α (fun i : Fin n => loss i ω) + (η + h) / (1 - α)} ≤
      μ.real {ω | cvarPop α ν Z >
        cvarValidationUpper α (τ (select ω)) (ε (select ω))
          (fun i => loss i ω) n} :=
    ENNReal.toReal_mono (measure_ne_top μ _) hmeasure
  exact hmeasure_real.trans hfinite

/-- The finite-family bridge in the usual bounded-loss form.

When `a < b`, the raw radius simplifies to Hoeffding's
`2 n η² / (b - a)²`, and the finite-family sum is the grid cardinality times
one common exponential term.  Thus the unrestricted empirical CVaR is an
upper confidence certificate for the population CVaR with total additive cost
`(η + h) / (1 - α)`.
-/
theorem cvarPop_empirical_cvar_failure_le
    {loss : ℕ → Ω → ℝ} {Z : Ξ → ℝ} {a b α h η : ℝ} {n : ℕ}
    (G : Finset ℝ) (hG : G.Nonempty)
    (hZ : Integrable Z ν) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hab : a < b) (hGsub : ∀ g ∈ G, g ∈ Set.Icc a b)
    (hh : 0 ≤ h) (hη : 0 ≤ η) (hn : 0 < n)
    (hcover : ∀ t ∈ Set.Icc a b, ∃ g ∈ G, |t - g| ≤ h)
    (h_indep : iIndepFun loss μ)
    (h_law : ∀ i, IdentDistrib (loss i) Z μ ν)
    (h_bounded : ∀ᵐ ξ ∂ν, Z ξ ∈ Set.Icc a b) :
    μ.real {ω | cvarPop α ν Z >
      cvarSAA α (fun i : Fin n => loss i ω) + (η + h) / (1 - α)} ≤
      (G.card : ℝ) * Real.exp (-2 * (n : ℝ) * η ^ 2 / (b - a) ^ 2) := by
  have hraw := cvarPop_empirical_cvar_failure_le_raw G hG hZ hα0 hα1
    hab.le hGsub hh hη hn hcover h_indep h_law h_bounded
  have hnorm : ‖b - a‖₊ = Real.toNNReal (b - a) := by
    rw [Real.nnnorm_of_nonneg (sub_pos.mpr hab).le,
      Real.toNNReal_of_nonneg (sub_pos.mpr hab).le]
  have hexp : -((n : ℝ) * η) ^ 2 /
        (2 * (n : ℝ) * ((‖b - a‖₊ / 2) ^ 2)) =
      -2 * (n : ℝ) * η ^ 2 / (b - a) ^ 2 := by
    rw [hnorm, Real.coe_toNNReal (b - a) (sub_pos.mpr hab).le]
    field_simp
  have hsum :
      (∑ g : {g : ℝ // g ∈ G}, Real.exp (-((n : ℝ) * η) ^ 2 /
        (2 * (n : ℝ) * ((‖b - a‖₊ / 2) ^ 2)))) =
        (G.card : ℝ) * Real.exp (-2 * (n : ℝ) * η ^ 2 / (b - a) ^ 2) := by
    rw [hexp]
    simp [nsmul_eq_mul]
  rw [hsum] at hraw
  exact hraw

end EmpiricalConfidence

end Ctrllib

#print axioms Ctrllib.cvarPop_empirical_cvar_failure_le_raw
#print axioms Ctrllib.cvarPop_empirical_cvar_failure_le
