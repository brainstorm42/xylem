import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Tactic

/-!
# Population CVaR and deterministic loss error

The Rockafellar–Uryasev population infimum is defined for an integrable real
loss on a probability space. Confidence level `α` has upper-tail mass `1 - α`.
The results derive lower boundedness, comparison with each auxiliary objective,
and the transfer from an almost-sure one-sided loss error to a CVaR error.
They do not assume a density, identify a conditional tail mean, or establish
sampling concentration. Integrability is an explicit premise at each endpoint.
-/

open MeasureTheory

namespace Ctrllib

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The population auxiliary objective, with confidence level `α`. -/
noncomputable def cvarPopObj (α : ℝ) (μ : Measure Ω) (Z : Ω → ℝ) (τ : ℝ) : ℝ :=
  τ + (1 / (1 - α)) * ∫ ω, max (Z ω - τ) 0 ∂μ

/-- Population CVaR, defined by the infimum of the auxiliary objective. -/
noncomputable def cvarPop (α : ℝ) (μ : Measure Ω) (Z : Ω → ℝ) : ℝ :=
  ⨅ τ : ℝ, cvarPopObj α μ Z τ

/-- Integrable loss gives an integrable hinge at every real threshold. -/
theorem integrable_cvar_hinge [IsFiniteMeasure μ] {Z : Ω → ℝ}
    (hZ : Integrable Z μ) (τ : ℝ) :
    Integrable (fun ω => max (Z ω - τ) 0) μ :=
  (hZ.sub (integrable_const τ)).sup (integrable_const 0)

/-- Every auxiliary objective is bounded below by the population mean. -/
theorem integral_le_cvarPopObj [IsProbabilityMeasure μ] {Z : Ω → ℝ}
    (hZ : Integrable Z μ) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (τ : ℝ) :
    (∫ ω, Z ω ∂μ) ≤ cvarPopObj α μ Z τ := by
  have hρ : 0 < 1 - α := by linarith
  have hc0 : 0 ≤ 1 / (1 - α) := (div_pos zero_lt_one hρ).le
  have hc1 : 1 ≤ 1 / (1 - α) := by
    apply (le_div_iff₀ hρ).2
    linarith
  have hhinge := integrable_cvar_hinge hZ τ
  have hnonneg : 0 ≤ ∫ ω, max (Z ω - τ) 0 ∂μ :=
    integral_nonneg (fun _ => le_max_right _ _)
  have hmean : (∫ ω, Z ω ∂μ) - τ ≤ ∫ ω, max (Z ω - τ) 0 ∂μ := by
    have h := integral_mono_ae (hZ.sub (integrable_const τ)) hhinge
      (Filter.Eventually.of_forall (fun ω => le_max_left (Z ω - τ) 0))
    simpa [integral_sub hZ (integrable_const τ)] using h
  unfold cvarPopObj
  by_cases hτ : (∫ ω, Z ω ∂μ) ≤ τ
  · exact hτ.trans (le_add_of_nonneg_right (mul_nonneg hc0 hnonneg))
  · have hgap : 0 ≤ (∫ ω, Z ω ∂μ) - τ := by linarith
    have hscaled := mul_le_mul_of_nonneg_left hmean hc0
    have hgain := mul_le_mul_of_nonneg_right hc1 hgap
    nlinarith

/-- The real infimum is not evaluated on a range unbounded below. -/
theorem cvarPopObj_bddBelow [IsProbabilityMeasure μ] {Z : Ω → ℝ}
    (hZ : Integrable Z μ) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) :
    BddBelow (Set.range (cvarPopObj α μ Z)) :=
  ⟨∫ ω, Z ω ∂μ, by
    rintro _ ⟨τ, rfl⟩
    exact integral_le_cvarPopObj hZ hα0 hα1 τ⟩

/-- Any chosen threshold supplies a population CVaR upper bound. -/
theorem cvarPop_le_obj [IsProbabilityMeasure μ] {Z : Ω → ℝ}
    (hZ : Integrable Z μ) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (τ : ℝ) :
    cvarPop α μ Z ≤ cvarPopObj α μ Z τ :=
  ciInf_le (cvarPopObj_bddBelow hZ hα0 hα1) τ

/-- Population CVaR is at least the population mean under the stated convention. -/
theorem integral_le_cvarPop [IsProbabilityMeasure μ] {Z : Ω → ℝ}
    (hZ : Integrable Z μ) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) :
    (∫ ω, Z ω ∂μ) ≤ cvarPop α μ Z :=
  le_ciInf (integral_le_cvarPopObj hZ hα0 hα1)

/-- An almost-sure additive upper error on loss gives the same additive upper
error on population CVaR. The threshold shifts with the error, avoiding a
spurious factor `1 / (1 - α)` on a uniform loss error. -/
theorem cvarPop_le_of_ae_le_add [IsProbabilityMeasure μ] {Z Y : Ω → ℝ}
    (hZ : Integrable Z μ) (hY : Integrable Y μ)
    {α η : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hZY : ∀ᵐ ω ∂μ, Z ω ≤ Y ω + η) :
    cvarPop α μ Z ≤ cvarPop α μ Y + η := by
  have hρ : 0 < 1 - α := by linarith
  have hc : 0 ≤ 1 / (1 - α) := (div_pos zero_lt_one hρ).le
  have hobj : ∀ τ, cvarPopObj α μ Z (τ + η) ≤ cvarPopObj α μ Y τ + η := by
    intro τ
    have hh : (∫ ω, max (Z ω - (τ + η)) 0 ∂μ) ≤
        ∫ ω, max (Y ω - τ) 0 ∂μ := by
      apply integral_mono_ae (integrable_cvar_hinge hZ _) (integrable_cvar_hinge hY _)
      filter_upwards [hZY] with ω hω
      apply max_le_max _ le_rfl
      linarith
    have hs := mul_le_mul_of_nonneg_left hh hc
    unfold cvarPopObj
    linarith
  have hbound : cvarPop α μ Z - η ≤ cvarPop α μ Y := by
    apply le_ciInf
    intro τ
    have ht := (cvarPop_le_obj hZ hα0 hα1 (τ + η)).trans (hobj τ)
    linarith
  linarith

/-- Monotonicity for integrable losses, including distributions with atoms. -/
theorem cvarPop_mono [IsProbabilityMeasure μ] {Z Y : Ω → ℝ}
    (hZ : Integrable Z μ) (hY : Integrable Y μ)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hZY : ∀ᵐ ω ∂μ, Z ω ≤ Y ω) :
    cvarPop α μ Z ≤ cvarPop α μ Y := by
  simpa using cvarPop_le_of_ae_le_add hZ hY hα0 hα1 (η := 0) (by simpa using hZY)

/-- A uniform two-sided loss error bounds the absolute population CVaR error. -/
theorem abs_cvarPop_sub_le_of_ae_abs_sub_le [IsProbabilityMeasure μ] {Z Y : Ω → ℝ}
    (hZ : Integrable Z μ) (hY : Integrable Y μ)
    {α η : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hZY : ∀ᵐ ω ∂μ, |Z ω - Y ω| ≤ η) :
    |cvarPop α μ Z - cvarPop α μ Y| ≤ η := by
  have hupper := cvarPop_le_of_ae_le_add hZ hY hα0 hα1 (by
    filter_upwards [hZY] with ω hω
    have hu := (abs_le.mp hω).2
    linarith)
  have hlower := cvarPop_le_of_ae_le_add hY hZ hα0 hα1 (by
    filter_upwards [hZY] with ω hω
    have hl := (abs_le.mp hω).1
    linarith)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end Ctrllib

#print axioms Ctrllib.integrable_cvar_hinge
#print axioms Ctrllib.integral_le_cvarPopObj
#print axioms Ctrllib.cvarPopObj_bddBelow
#print axioms Ctrllib.cvarPop_le_obj
#print axioms Ctrllib.integral_le_cvarPop
#print axioms Ctrllib.cvarPop_le_of_ae_le_add
#print axioms Ctrllib.cvarPop_mono
#print axioms Ctrllib.abs_cvarPop_sub_le_of_ae_abs_sub_le
