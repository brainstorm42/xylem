/-
Allocation perturbation and realization-error interfaces.

The statements use continuous linear maps so every operator norm is the
induced norm of an explicitly typed map.  They are algebraic and metric
interfaces; no plant, controller implementation, or actuator model is
assumed.
-/
import Ctrllib.InspectionMargin

/-! # Allocation perturbation and realization-error interfaces

The module uses explicitly typed continuous linear maps and induced operator
norms to separate model, solve, demand, and actuator-realization errors. -/

namespace Ctrllib

/-! The spaces below are deliberately abstract.  An application must provide
the physical scaling and the correspondence from its allocation coordinates
to these normed spaces. -/

/--
The difference between two linear allocations is bounded by operator error
times the perturbed demand plus nominal operator norm times demand error.
-/
theorem allocation_perturbation_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Khat K : E →L[ℝ] F} {bhat b : E} {η εb : ℝ}
    (hK : ‖Khat - K‖ ≤ η) (hDemand : ‖bhat - b‖ ≤ εb) :
    ‖Khat bhat - K b‖ ≤ η * ‖bhat‖ + ‖K‖ * εb := by
  have hdecomp : Khat bhat - K b = (Khat - K) bhat + K (bhat - b) := by
    simp only [sub_apply, map_sub]
    abel
  rw [hdecomp]
  calc
    ‖(Khat - K) bhat + K (bhat - b)‖ ≤
        ‖(Khat - K) bhat‖ + ‖K (bhat - b)‖ := norm_add_le _ _
    _ ≤ ‖Khat - K‖ * ‖bhat‖ + ‖K‖ * ‖bhat - b‖ := by
      gcongr
      · exact ContinuousLinearMap.le_opNorm _ _
      · exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ η * ‖bhat‖ + ‖K‖ * εb := by
      gcongr

/-- A scalar budget form of `allocation_perturbation_bound`. -/
theorem allocation_perturbation_budget
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Khat K : E →L[ℝ] F} {bhat b : E}
    {η Bhat εb Kbound : ℝ}
    (hη : 0 ≤ η) (_hBhat : 0 ≤ Bhat) (hεb : 0 ≤ εb) (_hKbound : 0 ≤ Kbound)
    (hK : ‖Khat - K‖ ≤ η) (hBhatNorm : ‖bhat‖ ≤ Bhat)
    (hDemand : ‖bhat - b‖ ≤ εb) (hKnorm : ‖K‖ ≤ Kbound) :
    ‖Khat bhat - K b‖ ≤ η * Bhat + Kbound * εb := by
  have hraw := allocation_perturbation_bound hK hDemand
  have hηmul : η * ‖bhat‖ ≤ η * Bhat :=
    mul_le_mul_of_nonneg_left hBhatNorm hη
  have hKmul : ‖K‖ * εb ≤ Kbound * εb :=
    mul_le_mul_of_nonneg_right hKnorm hεb
  linarith

/--
The norm budget after additive realization error in the allocation output
space.  Here `eReal : F` bounds the discrepancy between the computed output
`Khat bhat` and the resultant realized allocation vector.
-/
theorem allocation_actual_realization_budget
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Khat K : E →L[ℝ] F} {bhat b : E} {eReal : F}
    {η Bhat εb Kbound εS : ℝ}
    (hη : 0 ≤ η) (_hBhat : 0 ≤ Bhat) (hεb : 0 ≤ εb) (_hKbound : 0 ≤ Kbound)
    (_hεS : 0 ≤ εS) (hK : ‖Khat - K‖ ≤ η) (hBhatNorm : ‖bhat‖ ≤ Bhat)
    (hDemand : ‖bhat - b‖ ≤ εb) (hKnorm : ‖K‖ ≤ Kbound)
    (hReal : ‖eReal‖ ≤ εS) :
    ‖(Khat bhat + eReal) - K b‖ ≤ η * Bhat + Kbound * εb + εS := by
  have hAlloc : ‖Khat bhat - K b‖ ≤ η * Bhat + Kbound * εb :=
    allocation_perturbation_budget hη _hBhat hεb _hKbound hK hBhatNorm hDemand hKnorm
  calc
    ‖(Khat bhat + eReal) - K b‖ = ‖(Khat bhat - K b) + eReal‖ := by
      congr 1
      abel
    _ ≤ ‖Khat bhat - K b‖ + ‖eReal‖ := norm_add_le _ _
    _ ≤ η * Bhat + Kbound * εb + εS := by linarith

/--
Expanding an actually realized allocation separates model, solve, demand, and
actuator-realization residuals.  The vector `eS` is an additive realization
error, so the actual effort is `Shat + eS`.
-/
theorem allocation_equality_residual_identity
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {A Ahat : E →L[ℝ] F} {Shat eS : E} {b bhat : F} :
    A (Shat + eS) - b =
      (A - Ahat) Shat + (Ahat Shat - bhat) + (bhat - b) + A eS := by
  simp only [map_add, sub_apply]
  abel

/--
The equality residual is bounded by model perturbation, numerical solve
residual, demand perturbation, and actuator realization error.
-/
theorem allocation_equality_residual_budget
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {A Ahat : E →L[ℝ] F} {Shat eS : E} {b bhat : F}
    {η BhatS rsolve εb εS Abound : ℝ}
    (hη : 0 ≤ η) (_hBhatS : 0 ≤ BhatS) (_hrsolve : 0 ≤ rsolve)
    (_hεb : 0 ≤ εb) (_hεS : 0 ≤ εS) (hAbound : 0 ≤ Abound)
    (hA : ‖A - Ahat‖ ≤ η) (hShat : ‖Shat‖ ≤ BhatS)
    (hsolve : ‖Ahat Shat - bhat‖ ≤ rsolve)
    (hdemand : ‖bhat - b‖ ≤ εb) (hreal : ‖eS‖ ≤ εS)
    (hAnorm : ‖A‖ ≤ Abound) :
    ‖A (Shat + eS) - b‖ ≤ η * BhatS + rsolve + εb + Abound * εS := by
  rw [allocation_equality_residual_identity]
  calc
    ‖(A - Ahat) Shat + (Ahat Shat - bhat) + (bhat - b) + A eS‖ ≤
        ‖(A - Ahat) Shat‖ + ‖Ahat Shat - bhat‖ + ‖bhat - b‖ + ‖A eS‖ := by
      calc
        ‖(A - Ahat) Shat + (Ahat Shat - bhat) + (bhat - b) + A eS‖ ≤
            ‖(A - Ahat) Shat + (Ahat Shat - bhat) + (bhat - b)‖ + ‖A eS‖ :=
          norm_add_le _ _
        _ ≤ (‖(A - Ahat) Shat + (Ahat Shat - bhat)‖ + ‖bhat - b‖) +
              ‖A eS‖ := by
          gcongr
          exact norm_add_le _ _
        _ ≤ (‖(A - Ahat) Shat‖ + ‖Ahat Shat - bhat‖) + ‖bhat - b‖ +
              ‖A eS‖ := by
          gcongr
          exact norm_add_le _ _
    _ ≤ η * BhatS + rsolve + εb + Abound * εS := by
      have hmodel : ‖(A - Ahat) Shat‖ ≤ η * BhatS := by
        calc
          ‖(A - Ahat) Shat‖ ≤ ‖A - Ahat‖ * ‖Shat‖ :=
            ContinuousLinearMap.le_opNorm _ _
          _ ≤ η * BhatS := by
            gcongr
      have hact : ‖A eS‖ ≤ Abound * εS := by
        calc
          ‖A eS‖ ≤ ‖A‖ * ‖eS‖ := ContinuousLinearMap.le_opNorm _ _
          _ ≤ Abound * εS := by
            gcongr
      linarith

/--
A Lipschitz scalar constraint preserves a nominal negative slack after an
allocation perturbation, with the perturbation budget supplied by
`allocation_perturbation_budget`.
-/
theorem allocation_constraint_slack_budget
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Khat K : E →L[ℝ] F} {bhat b : E} {g : F → ℝ} {Kg η Bhat εb Kbound margin : ℝ}
    (hKg : 0 ≤ Kg) (hη : 0 ≤ η) (_hBhat : 0 ≤ Bhat) (hεb : 0 ≤ εb)
    (_hKbound : 0 ≤ Kbound) (_hmargin : 0 ≤ margin)
    (hg : LipschitzWith ⟨Kg, hKg⟩ g)
    (hK : ‖Khat - K‖ ≤ η) (hBhatNorm : ‖bhat‖ ≤ Bhat)
    (hDemand : ‖bhat - b‖ ≤ εb) (hKnorm : ‖K‖ ≤ Kbound)
    (hNominal : g (K b) ≤ -margin) :
    g (Khat bhat) ≤ -margin + Kg * (η * Bhat + Kbound * εb) := by
  have hS : ‖Khat bhat - K b‖ ≤ η * Bhat + Kbound * εb :=
    allocation_perturbation_budget hη _hBhat hεb _hKbound hK hBhatNorm hDemand hKnorm
  have hg' := hg.le_add_mul (Khat bhat) (K b)
  have hdist : dist (Khat bhat) (K b) = ‖Khat bhat - K b‖ := by
    rw [dist_eq_norm]
  rw [hdist] at hg'
  change g (Khat bhat) ≤ g (K b) + Kg * ‖Khat bhat - K b‖ at hg'
  have hmul := mul_le_mul_of_nonneg_left hS hKg
  calc
    g (Khat bhat) ≤ g (K b) + Kg * ‖Khat bhat - K b‖ := by linarith [hg']
    _ ≤ -margin + Kg * (η * Bhat + Kbound * εb) := by
      linarith [hNominal, hmul]

/--
The scalar constraint-slack bound for the actual realized allocation output.
The realization error is in the output space `F`; in a weighted allocation this
space may include both contact-wrench and actuator-effort coordinates.  The
bound does not assert that contact wrenches are directly commanded.
-/
theorem allocation_actual_constraint_slack_budget
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Khat K : E →L[ℝ] F} {bhat b : E} {eReal : F} {g : F → ℝ}
    {Kg η Bhat εb Kbound εS margin : ℝ}
    (hKg : 0 ≤ Kg) (hη : 0 ≤ η) (_hBhat : 0 ≤ Bhat) (hεb : 0 ≤ εb)
    (_hKbound : 0 ≤ Kbound) (_hmargin : 0 ≤ margin) (hεS : 0 ≤ εS)
    (hg : LipschitzWith ⟨Kg, hKg⟩ g)
    (hK : ‖Khat - K‖ ≤ η) (hBhatNorm : ‖bhat‖ ≤ Bhat)
    (hDemand : ‖bhat - b‖ ≤ εb) (hKnorm : ‖K‖ ≤ Kbound)
    (hReal : ‖eReal‖ ≤ εS) (hNominal : g (K b) ≤ -margin) :
    g (Khat bhat + eReal) ≤
      -margin + Kg * (η * Bhat + Kbound * εb + εS) := by
  have hS : ‖(Khat bhat + eReal) - K b‖ ≤ η * Bhat + Kbound * εb + εS :=
    allocation_actual_realization_budget hη _hBhat hεb _hKbound hεS
      hK hBhatNorm hDemand hKnorm hReal
  have hg' := hg.le_add_mul (Khat bhat + eReal) (K b)
  have hdist : dist (Khat bhat + eReal) (K b) = ‖(Khat bhat + eReal) - K b‖ := by
    rw [dist_eq_norm]
  rw [hdist] at hg'
  change g (Khat bhat + eReal) ≤ g (K b) + Kg * ‖(Khat bhat + eReal) - K b‖ at hg'
  have hmul := mul_le_mul_of_nonneg_left hS hKg
  calc
    g (Khat bhat + eReal) ≤
        g (K b) + Kg * ‖(Khat bhat + eReal) - K b‖ := by linarith [hg']
    _ ≤ -margin + Kg * (η * Bhat + Kbound * εb + εS) := by
      linarith [hNominal, hmul]

end Ctrllib

#print axioms Ctrllib.allocation_perturbation_bound
#print axioms Ctrllib.allocation_perturbation_budget
#print axioms Ctrllib.allocation_actual_realization_budget
#print axioms Ctrllib.allocation_equality_residual_identity
#print axioms Ctrllib.allocation_equality_residual_budget
#print axioms Ctrllib.allocation_constraint_slack_budget
#print axioms Ctrllib.allocation_actual_constraint_slack_budget
