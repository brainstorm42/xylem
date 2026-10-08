import Ctrllib.RoverSampledClearance

/-! Pose-to-point and pose-to-body clearance interfaces in `Point3`. -/

namespace Ctrllib

abbrev Point3 := EuclideanSpace ℝ (Fin 3)

/-- Translation error plus operator-norm orientation error times body radius. -/
theorem rigid_point_error_le
    {tActual tNom : Point3}
    {RActual RNom : Point3 →L[ℝ] Point3}
    {b : Point3} {ρ κt κR : ℝ}
    (hb : ‖b‖ ≤ ρ) (ht : ‖tActual - tNom‖ ≤ κt)
    (hR : ‖RActual - RNom‖ ≤ κR) (hκR : 0 ≤ κR) :
    ‖(tActual + RActual b) - (tNom + RNom b)‖ ≤ κt + κR * ρ := by
  rw [add_sub_add_comm, ← sub_apply]
  calc
    ‖(tActual - tNom) + (RActual - RNom) b‖ ≤
        ‖tActual - tNom‖ + ‖(RActual - RNom) b‖ := norm_add_le _ _
    _ ≤ ‖tActual - tNom‖ + ‖RActual - RNom‖ * ‖b‖ := by
      gcongr
      exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ κt + κR * ρ := by gcongr

/-- A rigid isometry preserves a body-coordinate sample-cover radius. -/
theorem rigid_cover_transport
    {I : Type*} {B : Set Point3} {samples : I → Point3}
    {t : Point3} {R : Point3 →L[ℝ] Point3} {ρ : ℝ}
    (hcover : ∀ b, b ∈ B → ∃ i, ‖b - samples i‖ ≤ ρ)
    (hisom : ∀ x y : Point3, ‖R x - R y‖ = ‖x - y‖) :
    ∀ b, b ∈ B → ∃ i, ‖(t + R b) - (t + R (samples i))‖ ≤ ρ := by
  intro b hb
  obtain ⟨i, hi⟩ := hcover b hb
  refine ⟨i, ?_⟩
  rw [add_sub_add_left_eq_sub]
  exact hisom b (samples i) ▸ hi

/-- Translation/orientation time bounds give a material-point motion bound. -/
theorem time_lipschitz_point_error
    {S : Set ℝ}
    {tActual : ℝ → Point3} {RActual : ℝ → (Point3 →L[ℝ] Point3)}
    {b : Point3} {ρ Lt LR : ℝ}
    (hb : ‖b‖ ≤ ρ) (hLR : 0 ≤ LR)
    (ht : ∀ s ∈ S, ∀ u ∈ S,
      ‖tActual s - tActual u‖ ≤ Lt * |s - u|)
    (hR : ∀ s ∈ S, ∀ u ∈ S,
      ‖RActual s - RActual u‖ ≤ LR * |s - u|) :
    ∀ s ∈ S, ∀ u ∈ S,
      ‖(tActual s + RActual s b) - (tActual u + RActual u b)‖ ≤
        (Lt + LR * ρ) * |s - u| := by
  intro s hs u hu
  have hd : 0 ≤ |s - u| := abs_nonneg _
  have hpoint := rigid_point_error_le hb (ht s hs u hu)
    (hR s hs u hu) (mul_nonneg hLR hd)
  calc
    ‖(tActual s + RActual s b) - (tActual u + RActual u b)‖ ≤
        Lt * |s - u| + (LR * |s - u|) * ρ := hpoint
    _ = (Lt + LR * ρ) * |s - u| := by ring

/-- Pose errors, temporal bounds, and body-coordinate covers compose into a
whole-body target-time clearance bound. `rP,rQ` bound material-point radii
and `rhoP,rhoQ` are independent cover radii. -/
theorem rover_pose_body_clearance
    {S : Set ℝ} {I J : Type*} {Bp Bq BodyP BodyQ : Set Point3}
    {p : I → ℝ → Point3} {q : J → ℝ → Point3}
    {sampleP : I → Point3} {sampleQ : J → Point3}
    {tP tQ : ℝ → Point3}
    {RP : ℝ → (Point3 →L[ℝ] Point3)} {RQ : ℝ → (Point3 →L[ℝ] Point3)}
    {tPdel tQdel : Point3} {RPdel RQdel : Point3 →L[ℝ] Point3}
    {pDelivered : I → Point3} {qDelivered : J → Point3}
    {eps_tP eps_tQ eps_RP eps_RQ delta h t tau rP rQ rhoP rhoQ LtP LtQ LRP LRQ : ℝ}
    (hage : |t - tau| ≤ h)
    (hrP : 0 ≤ rP) (hrQ : 0 ≤ rQ)
    (hLtP : 0 ≤ LtP) (hLtQ : 0 ≤ LtQ)
    (htau : tau ∈ S) (htarget : t ∈ S)
    (hpPose : ∀ i s, s ∈ S → p i s = tP s + RP s (sampleP i))
    (hqPose : ∀ j s, s ∈ S → q j s = tQ s + RQ s (sampleQ j))
    (hpDel : ∀ i, pDelivered i = tPdel + RPdel (sampleP i))
    (hqDel : ∀ j, qDelivered j = tQdel + RQdel (sampleQ j))
    (hbodyP : ∀ i, ‖sampleP i‖ ≤ rP) (hbodyQ : ∀ j, ‖sampleQ j‖ ≤ rQ)
    (htransP : ‖tPdel - tP tau‖ ≤ eps_tP) (htransQ : ‖tQdel - tQ tau‖ ≤ eps_tQ)
    (hrotP : ‖RPdel - RP tau‖ ≤ eps_RP) (hrotQ : ‖RQdel - RQ tau‖ ≤ eps_RQ)
    (hεP : 0 ≤ eps_RP) (hεQ : 0 ≤ eps_RQ)
    (htimeP : ∀ s ∈ S, ∀ u ∈ S, ‖tP s - tP u‖ ≤ LtP * |s - u|)
    (htimeQ : ∀ s ∈ S, ∀ u ∈ S, ‖tQ s - tQ u‖ ≤ LtQ * |s - u|)
    (hrotTimeP : ∀ s ∈ S, ∀ u ∈ S, ‖RP s - RP u‖ ≤ LRP * |s - u|)
    (hrotTimeQ : ∀ s ∈ S, ∀ u ∈ S, ‖RQ s - RQ u‖ ≤ LRQ * |s - u|)
    (hLRP : 0 ≤ LRP) (hLRQ : 0 ≤ LRQ)
    (hpCover : ∀ b ∈ BodyP, ∃ i, ‖b - sampleP i‖ ≤ rhoP)
    (hqCover : ∀ b ∈ BodyQ, ∃ j, ‖b - sampleQ j‖ ≤ rhoQ)
    (hBp : ∀ x ∈ Bp, ∃ b ∈ BodyP, x = tP t + RP t b)
    (hBq : ∀ y ∈ Bq, ∃ b ∈ BodyQ, y = tQ t + RQ t b)
    (hisoP : ∀ x y, ‖RP t x - RP t y‖ = ‖x - y‖)
    (hisoQ : ∀ x y, ‖RQ t x - RQ t y‖ = ‖x - y‖)
    (hsep : ∀ i j, delta ≤ dist (pDelivered i) (qDelivered j)) :
    ∀ x ∈ Bp, ∀ y ∈ Bq,
      delta - (eps_tP + eps_RP*rP) - (eps_tQ + eps_RQ*rQ)
        - ((LtP + LRP*rP) + (LtQ + LRQ*rQ))*h - rhoP-rhoQ ≤ dist x y := by
  have hpDelivered : ∀ i, dist (pDelivered i) (p i tau) ≤ eps_tP + eps_RP*rP := by
    intro i
    rw [hpDel i, hpPose i tau htau, dist_eq_norm]
    exact rigid_point_error_le (hbodyP i) htransP hrotP hεP
  have hqDelivered : ∀ j, dist (qDelivered j) (q j tau) ≤ eps_tQ + eps_RQ*rQ := by
    intro j
    rw [hqDel j, hqPose j tau htau, dist_eq_norm]
    exact rigid_point_error_le (hbodyQ j) htransQ hrotQ hεQ
  have hpTarget : ∀ i, dist (pDelivered i) (p i t) ≤
      eps_tP + eps_RP*rP + (LtP + LRP*rP)*h := by
    intro i
    have hm := time_lipschitz_point_error (S := S) (hbodyP i) hLRP
      htimeP hrotTimeP t htarget tau htau
    have hd : dist (p i tau) (p i t) ≤ (LtP + LRP*rP)*h := by
      rw [dist_eq_norm, hpPose i tau htau, hpPose i t htarget]
      have hm' : ‖tP tau + RP tau (sampleP i) - (tP t + RP t (sampleP i))‖ ≤
          (LtP + LRP*rP) * |t-tau| := by
        simpa only [norm_sub_rev] using hm
      exact le_trans hm' (mul_le_mul_of_nonneg_left hage (by positivity))
    have htri := dist_triangle (pDelivered i) (p i tau) (p i t)
    linarith [hpDelivered i, hd]
  have hqTarget : ∀ j, dist (qDelivered j) (q j t) ≤
      eps_tQ + eps_RQ*rQ + (LtQ + LRQ*rQ)*h := by
    intro j
    have hm := time_lipschitz_point_error (S := S) (hbodyQ j) hLRQ
      htimeQ hrotTimeQ t htarget tau htau
    have hd : dist (q j tau) (q j t) ≤ (LtQ + LRQ*rQ)*h := by
      rw [dist_eq_norm, hqPose j tau htau, hqPose j t htarget]
      have hm' : ‖tQ tau + RQ tau (sampleQ j) - (tQ t + RQ t (sampleQ j))‖ ≤
          (LtQ + LRQ*rQ) * |t-tau| := by
        simpa only [norm_sub_rev] using hm
      exact le_trans hm' (mul_le_mul_of_nonneg_left hage (by positivity))
    have htri := dist_triangle (qDelivered j) (q j tau) (q j t)
    linarith [hqDelivered j, hd]
  have hsepTarget : ∀ i j, delta - (eps_tP + eps_RP*rP) - (eps_tQ + eps_RQ*rQ)
      - ((LtP + LRP*rP) + (LtQ + LRQ*rQ))*h ≤ dist (p i t) (q j t) := by
    intro i j
    have he := dist_actual_ge_dist_nominal_sub (pDelivered i) (p i t) (qDelivered j) (q j t)
      (by simpa [dist_comm] using hpTarget i) (by simpa [dist_comm] using hqTarget j)
    linarith [hsep i j]
  have hpcover : ∀ x ∈ Bp, ∃ i, dist x (p i t) ≤ rhoP := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := hBp x hx
    obtain ⟨i, hi⟩ := rigid_cover_transport (t := tP t) (R := RP t) hpCover hisoP b hb
    refine ⟨i, ?_⟩
    rw [hpPose i t htarget, dist_eq_norm]
    exact hi
  have hqcover : ∀ y ∈ Bq, ∃ j, dist y (q j t) ≤ rhoQ := by
    intro y hy
    obtain ⟨b, hb, rfl⟩ := hBq y hy
    obtain ⟨j, hj⟩ := rigid_cover_transport (t := tQ t) (R := RQ t) hqCover hisoQ b hb
    refine ⟨j, ?_⟩
    rw [hqPose j t htarget, dist_eq_norm]
    exact hj
  exact rover_body_clearance_of_sample_cover hpcover hqcover hsepTarget

end Ctrllib

#print axioms Ctrllib.rigid_point_error_le
#print axioms Ctrllib.rigid_cover_transport
#print axioms Ctrllib.time_lipschitz_point_error
#print axioms Ctrllib.rover_pose_body_clearance
