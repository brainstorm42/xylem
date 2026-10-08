import Ctrllib.EstimationError

namespace Ctrllib

open MeasureTheory

/-! # Generic inspection-margin interfaces

These declarations separate a geometric sufficient condition from any particular
robot, controller, coordinate conversion, or physical-unit interpretation.
Conventional derivation: the corresponding derivation record's
the corresponding local note.
-/

/-- Pairwise distance cannot decrease by more than the two pointwise
    displacements.  The ambient space need only be a pseudometric space. -/
theorem dist_actual_ge_dist_nominal_sub
    {X : Type*} [PseudoMetricSpace X]
    (p₀ p q₀ q : X) {εp εq : ℝ}
    (hp : dist p p₀ ≤ εp) (hq : dist q q₀ ≤ εq) :
    dist p₀ q₀ - εp - εq ≤ dist p q := by
  have hleft : dist p₀ q₀ ≤ dist p₀ p + dist p q₀ :=
    dist_triangle _ _ _
  have hright : dist p q₀ ≤ dist p q + dist q q₀ :=
    dist_triangle _ _ _
  have hchain : dist p₀ q₀ ≤ dist p₀ p + dist p q + dist q q₀ := by
    have h := le_trans hleft (add_le_add_right hright (dist p₀ p))
    simpa [add_assoc] using h
  rw [dist_comm p₀ p] at hchain
  linarith

/-- Uniform all-pairs nominal separation and pointwise displacement bounds give
    a uniform lower bound on every actual pair.  The index types are arbitrary;
    no finite sampling or enumeration assumption is present. -/
theorem all_pair_clearance_lower_bound
    {I J X : Type*} [PseudoMetricSpace X]
    {p₀ : I → X} {p : I → X} {q₀ : J → X} {q : J → X}
    {δ εp εq : ℝ}
    (hp : ∀ i, dist (p i) (p₀ i) ≤ εp)
    (hq : ∀ j, dist (q j) (q₀ j) ≤ εq)
    (hsep : ∀ i j, δ ≤ dist (p₀ i) (q₀ j)) :
    ∀ i j, δ - εp - εq ≤ dist (p i) (q j) := by
  intro i j
  have herode := dist_actual_ge_dist_nominal_sub
    (p₀ i) (p i) (q₀ j) (q j) (hp i) (hq j)
  linarith [hsep i j, herode]

/-- State error erodes all represented point-pair clearances through proved
Lipschitz geometry maps. Physical coverage of the index types remains explicit. -/
theorem all_pair_clearance_of_state_error
    {I J S X : Type*} [PseudoMetricSpace S] [PseudoMetricSpace X]
    {p : I → S → X} {q : J → S → X} {Kp Kq : NNReal}
    (hp : ∀ i, LipschitzWith Kp (p i)) (hq : ∀ j, LipschitzWith Kq (q j))
    {x xhat : S} {ε δ : ℝ} (herr : dist x xhat ≤ ε)
    (hsep : ∀ i j, δ ≤ dist (p i xhat) (q j xhat)) :
    ∀ i j, δ - ((Kp : ℝ) + (Kq : ℝ)) * ε ≤ dist (p i x) (q j x) := by
  have hp' : ∀ i, dist (p i x) (p i xhat) ≤ (Kp : ℝ) * ε := fun i ↦
    ((hp i).dist_le_mul x xhat).trans (mul_le_mul_of_nonneg_left herr Kp.coe_nonneg)
  have hq' : ∀ j, dist (q j x) (q j xhat) ≤ (Kq : ℝ) * ε := fun j ↦
    ((hq j).dist_le_mul x xhat).trans (mul_le_mul_of_nonneg_left herr Kq.coe_nonneg)
  intro i j
  have h := all_pair_clearance_lower_bound hp' hq' hsep i j
  linarith

/-- A scalar margin can fall by at most its Lipschitz constant times state error. -/
theorem margin_lower_bound_of_state_error
    {S : Type*} [PseudoMetricSpace S] {m : S → ℝ} {K : NNReal}
    (hm : LipschitzWith K m) {x xhat : S} {ε : ℝ} (herr : dist x xhat ≤ ε) :
    m xhat - (K : ℝ) * ε ≤ m x := by
  have h := hm.le_add_mul xhat x
  rw [dist_comm xhat x] at h
  have hmul := mul_le_mul_of_nonneg_left herr K.coe_nonneg
  linarith

/-- The signed loss associated with an abstract scalar inspection margin. -/
def populationMarginLoss {S Ω : Type*} (m : S → ℝ) (x : Ω → S) : Ω → ℝ :=
  fun ω => -(m (x ω))

/-- A Lipschitz inspection margin induces the same two-sided population-CVaR
    transfer bound after changing its sign.  Integrability and the almost-sure
    state error are explicit hypotheses; the CVaR result is delegated to the
    existing estimation-error theorem. -/
theorem abs_cvarPop_sub_le_of_margin_error
    {Ω S : Type*} [MeasurableSpace Ω] [NormedAddCommGroup S]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m : S → ℝ} {K : NNReal} {x xhat : Ω → S}
    (hMargin : LipschitzWith K m)
    (hx : Integrable (populationMarginLoss m x) μ)
    (hhat : Integrable (populationMarginLoss m xhat) μ)
    {α ε : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (herr : ∀ᵐ ω ∂μ, ‖x ω - xhat ω‖ ≤ ε) :
    |cvarPop α μ (populationMarginLoss m x) -
        cvarPop α μ (populationMarginLoss m xhat)| ≤ (K : ℝ) * ε := by
  have hNeg : LipschitzWith K (fun s : S => -(m s)) := hMargin.neg
  exact abs_cvarPop_sub_le_of_estimation_error
    hNeg hx hhat hα0 hα1 herr

end Ctrllib

#print axioms Ctrllib.dist_actual_ge_dist_nominal_sub
#print axioms Ctrllib.all_pair_clearance_lower_bound
#print axioms Ctrllib.all_pair_clearance_of_state_error
#print axioms Ctrllib.margin_lower_bound_of_state_error
#print axioms Ctrllib.abs_cvarPop_sub_le_of_margin_error
