import Ctrllib.ReferencePhase
import Ctrllib.ReferenceAdmissibility
import Ctrllib.TrackingDissipation
import Ctrllib.TrackingForcingInterface
import Ctrllib.TrackingStorageDerivative

/-!
# Reference delivery and tracking

The selected FFSM ideal field uses Coriolis on velocity error and retains a
moving-frame kinematic residual. These results connect the analytic reference
to that error and account exactly for delivered velocity/acceleration mismatch.
The combined theorem proves the local storage derivative from supplied path
derivatives. It does not establish the configuration lift or physical plant
equations. Conventional account: the corresponding derivation record's FFSM contract companion
the corresponding local note in `the corresponding local note`.
-/
namespace Ctrllib
section Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {p p₁ p₂ : ℝ → E} {rate u₀ t P₁ P₂ : ℝ}

/-- Analytic phase specialization, in the explicitly selected norm on `E`. -/
theorem referencePhase_derivatives_and_bounds
    (hrate : 0 < rate) (hu₀ : 0 ≤ u₀) (hu₀1 : u₀ < 1) (ht : 0 ≤ t)
    (hp : HasDerivAt p (p₁ (referencePhase rate u₀ t)) (referencePhase rate u₀ t))
    (hp₁ : HasDerivAt p₁ (p₂ (referencePhase rate u₀ t)) (referencePhase rate u₀ t))
    (hP₁ : ‖p₁ (referencePhase rate u₀ t)‖ ≤ P₁)
    (hP₂ : ‖p₂ (referencePhase rate u₀ t)‖ ≤ P₂) :
    HasDerivAt (fun τ ↦ p (referencePhase rate u₀ τ))
        (referenceSpeed rate u₀ t • p₁ (referencePhase rate u₀ t)) t ∧
    HasDerivAt (fun τ ↦ referenceSpeed rate u₀ τ • p₁ (referencePhase rate u₀ τ))
        ((referenceSpeed rate u₀ t)^2 • p₂ (referencePhase rate u₀ t) +
          (-(rate * referenceSpeed rate u₀ t)) • p₁ (referencePhase rate u₀ t)) t ∧
    ‖referenceSpeed rate u₀ t • p₁ (referencePhase rate u₀ t)‖ ≤ P₁ * rate ∧
    ‖(referenceSpeed rate u₀ t)^2 • p₂ (referencePhase rate u₀ t) +
      (-(rate * referenceSpeed rate u₀ t)) • p₁ (referencePhase rate u₀ t)‖ ≤
      P₂ * rate^2 + P₁ * rate^2 := by
  have hs : HasDerivAt (fun u : ℝ ↦ rate * (1 - u)) (-rate)
      (referencePhase rate u₀ t) := by
    simpa using ((hasDerivAt_const (referencePhase rate u₀ t) (1 : ℝ)).sub
      (hasDerivAt_id (referencePhase rate u₀ t))).const_mul rate
  have hspeed := referenceSpeed_bounds hrate hu₀ hu₀1 ht
  have h := reference_derivatives_and_bounds
    (u := referencePhase rate u₀) (s := fun u ↦ rate * (1 - u)) (s₁ := fun _ ↦ -rate)
    (hasDerivAt_referencePhase rate u₀ t) hp hs hp₁
    (by change |referenceSpeed rate u₀ t| ≤ rate
        simpa only [abs_of_nonneg hspeed.1] using hspeed.2)
    (by simpa only [referenceSpeed, neg_mul] using
      referenceAcceleration_abs_le hrate hu₀ hu₀1 ht)
    hP₁ hP₂ hrate.le (sq_nonneg rate)
  simpa only [referenceSpeed, neg_mul] using h

/-- A phase-indexed generalized velocity is differentiated as its own map;
it is not identified with the coordinate derivative of a configuration lift. -/
theorem hasDerivAt_reference_tracking_error {v vd : ℝ → E} {vd₁ vdot : E}
    (hv : HasDerivAt v vdot t)
    (hvd : HasDerivAt vd vd₁ (referencePhase rate u₀ t)) :
    HasDerivAt (fun τ ↦ v τ - vd (referencePhase rate u₀ τ))
      (vdot - referenceSpeed rate u₀ t • vd₁) t := by
  have hd := hasDerivAt_reference_comp
    (s := fun u ↦ rate * (1 - u)) (p₁ := fun _ ↦ vd₁)
    (hasDerivAt_referencePhase rate u₀ t) hvd
  exact hv.sub hd
end Calculus

open Matrix
section Delivery
variable {n m : Type*} [Fintype n] [Fintype m]
variable {M Mdot C D : Matrix n n ℝ} {K : Matrix m m ℝ} {J : Matrix m n ℝ}
variable {v vd vhat vdot ad ahat F : n → ℝ} {x xdot r : m → ℝ}

/-- Exact error equation for delivered reference values, with their signs retained. -/
theorem reference_delivery_error_equation
    (hdyn : M *ᵥ vdot = -(C *ᵥ (v - vhat)) - D *ᵥ (v - vhat) -
      Jᵀ *ᵥ (K *ᵥ x) - F + M *ᵥ ahat) :
    M *ᵥ (vdot - ad) = -(C *ᵥ (v - vd)) - D *ᵥ (v - vd) -
      Jᵀ *ᵥ (K *ᵥ x) - (F - (C + D) *ᵥ (vhat - vd) - M *ᵥ (ahat - ad)) := by
  rw [mulVec_sub, hdyn]
  simp only [mulVec_sub, add_mulVec]
  abel

/-- Selected error dynamics plus the moving-frame residual imply the exact rate.
This is pointwise algebra; actual storage calculus has separate hypotheses. -/
theorem tracking_rate_reference_delivery (hK : Kᵀ = K) (hM : Mdot = C + Cᵀ)
    (hdyn : M *ᵥ vdot = -(C *ᵥ (v - vhat)) - D *ᵥ (v - vhat) -
      Jᵀ *ᵥ (K *ᵥ x) - F + M *ᵥ ahat)
    (hkin : xdot = J *ᵥ (v - vd) + r) :
    trackingRate M Mdot K (v - vd) (vdot - ad) x xdot =
      -((v - vd) ⬝ᵥ D *ᵥ (v - vd)) -
        (v - vd) ⬝ᵥ (F - (C + D) *ᵥ (vhat - vd) - M *ᵥ (ahat - ad)) +
        x ⬝ᵥ K *ᵥ r := by
  have he := reference_delivery_error_equation (vd := vd) (ad := ad) hdyn
  have hb := passivity_bracket hM (v - vd)
  unfold trackingRate
  rw [he, hkin, mulVec_add, dotProduct_add]
  simp only [dotProduct_sub, dotProduct_neg]
  rw [stiffness_cross_symm hK]
  linarith

/-- Delivered-reference budgets become an Euclidean forcing budget when the two
matrix actions satisfy the stated gains. All gains use the same coordinates. -/
theorem reference_delivery_forcing_bound {f cGain mGain εv εa : ℝ}
    (hF : Real.sqrt (F ⬝ᵥ F) ≤ f)
    (hC : ∀ w, Real.sqrt (((C + D) *ᵥ w) ⬝ᵥ ((C + D) *ᵥ w)) ≤
      cGain * Real.sqrt (w ⬝ᵥ w))
    (hM : ∀ w, Real.sqrt ((M *ᵥ w) ⬝ᵥ (M *ᵥ w)) ≤
      mGain * Real.sqrt (w ⬝ᵥ w))
    (hc : 0 ≤ cGain) (hm : 0 ≤ mGain)
    (hv : Real.sqrt ((vhat - vd) ⬝ᵥ (vhat - vd)) ≤ εv)
    (ha : Real.sqrt ((ahat - ad) ⬝ᵥ (ahat - ad)) ≤ εa) :
    let Fe := F - (C + D) *ᵥ (vhat - vd) - M *ᵥ (ahat - ad)
    Real.sqrt (Fe ⬝ᵥ Fe) ≤ f + cGain * εv + mGain * εa := by
  dsimp only
  apply forcing_combined_bound (F_est := F)
    (F_act := -((C + D) *ᵥ (vhat - vd))) (F_model := -(M *ᵥ (ahat - ad))) hF
  · simpa only [neg_dotProduct, dotProduct_neg, neg_neg] using
      (hC (vhat - vd)).trans (mul_le_mul_of_nonneg_left hv hc)
  · simpa only [neg_dotProduct, dotProduct_neg, neg_neg] using
      (hM (ahat - ad)).trans (mul_le_mul_of_nonneg_left ha hm)
  · abel
end Delivery

/-- Actual local derivative of storage for a phase reference and delivered values.
The path derivatives, controller equation, passivity and residual kinematics are
explicit premises. This establishes no trajectory existence or domain retention. -/
theorem reference_tracking_storage_hasDerivAt
    {n m : Type*} [Fintype n] [Fintype m]
    {M : ℝ → Matrix n n ℝ} {Mdot C D : Matrix n n ℝ}
    {K : Matrix m m ℝ} {J : Matrix m n ℝ}
    {v vd : ℝ → (n → ℝ)} {x : ℝ → (m → ℝ)}
    {vd₁ vdot vhat ahat F : n → ℝ} {xdot r : m → ℝ} {rate u₀ t : ℝ}
    (hMt : HasDerivAt M Mdot t) (hv : HasDerivAt v vdot t)
    (hvd : HasDerivAt vd vd₁ (referencePhase rate u₀ t))
    (hx : HasDerivAt x xdot t) (hMsym : (M t)ᵀ = M t) (hK : Kᵀ = K)
    (hpass : Mdot = C + Cᵀ)
    (hdyn : M t *ᵥ vdot = -(C *ᵥ (v t - vhat)) - D *ᵥ (v t - vhat) -
      Jᵀ *ᵥ (K *ᵥ x t) - F + M t *ᵥ ahat)
    (hkin : xdot = J *ᵥ (v t - vd (referencePhase rate u₀ t)) + r) :
    let e := v t - vd (referencePhase rate u₀ t)
    let ad := referenceSpeed rate u₀ t • vd₁
    let Fe := F - (C + D) *ᵥ (vhat - vd (referencePhase rate u₀ t)) -
      M t *ᵥ (ahat - ad)
    HasDerivAt
      (fun τ ↦ blockLyap (M τ) K (v τ - vd (referencePhase rate u₀ τ)) (x τ))
      (-(e ⬝ᵥ D *ᵥ e) - e ⬝ᵥ Fe + x t ⬝ᵥ K *ᵥ r) t := by
  dsimp only
  have he := hasDerivAt_reference_tracking_error hv hvd
  have h := blockLyap_hasDerivAt hMt he hx hMsym hK
  rw [tracking_rate_reference_delivery hK hpass hdyn hkin] at h
  exact h
end Ctrllib

#print axioms Ctrllib.referencePhase_derivatives_and_bounds
#print axioms Ctrllib.hasDerivAt_reference_tracking_error
#print axioms Ctrllib.reference_delivery_error_equation
#print axioms Ctrllib.tracking_rate_reference_delivery
#print axioms Ctrllib.reference_delivery_forcing_bound
#print axioms Ctrllib.reference_tracking_storage_hasDerivAt
