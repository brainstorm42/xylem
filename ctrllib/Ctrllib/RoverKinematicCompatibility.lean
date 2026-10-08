/-
Copyright (c) 2026 Antonia Hoffman. All rights reserved.
Authors: Antonia Hoffman
-/
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Kinematic compatibility

These lemmas express the calculus interface between an attachment Jacobian,
generalized velocity, and a desired attachment twist.  They do not assert
existence of a robot trajectory, rank of a Jacobian, or correspondence with a
particular controller.
-/

namespace Ctrllib

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Product rule for a time-varying continuous linear map applied to a path. -/
theorem hasDerivAt_kinematic_product
    {J : ℝ → E →L[ℝ] F} {v : ℝ → E}
    {Jdot : ℝ → E →L[ℝ] F} {a : ℝ → E} {t : ℝ}
    (hJ : HasDerivAt J (Jdot t) t) (hv : HasDerivAt v (a t) t) :
    HasDerivAt (fun s => J s (v s))
      (Jdot t (v t) + J t (a t)) t := by
  exact hJ.clm_apply hv

/--
If the acceleration-level compatibility residual vanishes on an interval, an
initially matching attachment twist remains matching throughout the interval.

The hypotheses deliberately separate the actual integrated velocity `v` from
the acceleration `a`: `hv` states that `a` is the derivative of `v`.  The
conclusion is therefore not obtained by independently assigning a new
velocity optimum at each time.
-/
theorem kinematic_compatibility_on_Icc
    {t₀ t₁ : ℝ} {J : ℝ → E →L[ℝ] F} {v : ℝ → E} {Vd : ℝ → F}
    {Jdot : ℝ → E →L[ℝ] F} {a : ℝ → E} {Ad : ℝ → F}
    (hJ_cont : ContinuousOn J (Set.Icc t₀ t₁))
    (hv_cont : ContinuousOn v (Set.Icc t₀ t₁))
    (hVd_cont : ContinuousOn Vd (Set.Icc t₀ t₁))
    (hJ : ∀ t ∈ Set.Ico t₀ t₁, HasDerivAt J (Jdot t) t)
    (hv : ∀ t ∈ Set.Ico t₀ t₁, HasDerivAt v (a t) t)
    (hVd : ∀ t ∈ Set.Ico t₀ t₁, HasDerivAt Vd (Ad t) t)
    (hres : ∀ t ∈ Set.Ico t₀ t₁,
      Jdot t (v t) + J t (a t) - Ad t = 0)
    (h₀ : J t₀ (v t₀) = Vd t₀) (ht : t ∈ Set.Icc t₀ t₁) :
    J t (v t) = Vd t := by
  have hprod_cont : ContinuousOn (fun s => J s (v s)) (Set.Icc t₀ t₁) :=
    hJ_cont.clm_apply hv_cont
  have herr_cont : ContinuousOn (fun s => J s (v s) - Vd s) (Set.Icc t₀ t₁) :=
    hprod_cont.sub hVd_cont
  have hdiff : ∀ s ∈ Set.Ico t₀ t₁,
      HasDerivWithinAt (fun r => J r (v r) - Vd r) 0 (Set.Ici s) s := by
    intro s hs
    have hprod := hasDerivAt_kinematic_product (hJ s hs) (hv s hs)
    have hsub := hprod.sub (hVd s hs)
    have hz : Jdot s (v s) + J s (a s) - Ad s = 0 := hres s hs
    have hzero : Jdot s (v s) + J s (a s) - Ad s = (0 : F) := hz
    exact (hsub.congr_deriv hzero).hasDerivWithinAt
  have hconst := constant_of_has_deriv_right_zero herr_cont hdiff
  have hzero : J t₀ (v t₀) - Vd t₀ = 0 := sub_eq_zero.mpr h₀
  have herror : J t (v t) - Vd t = 0 := by
    rw [← hzero]
    exact hconst t ht
  exact sub_eq_zero.mp herror

/--
Uniformly bounded acceleration-level compatibility defect gives linear growth
of the attachment-twist error from its initial value.

The bound is derived from the operator product rule and the normed mean-value
estimate; the defect is not supplied as a zero residual.  The nonnegativity
hypothesis on `ε` records its operational interpretation as an error budget.
-/
theorem kinematic_compatibility_error_bound_on_Icc
    {t₀ t₁ : ℝ} {J : ℝ → E →L[ℝ] F} {v : ℝ → E} {Vd : ℝ → F}
    {Jdot : ℝ → E →L[ℝ] F} {a : ℝ → E} {Ad : ℝ → F} {ε : ℝ}
    (hJ_cont : ContinuousOn J (Set.Icc t₀ t₁))
    (hv_cont : ContinuousOn v (Set.Icc t₀ t₁))
    (hVd_cont : ContinuousOn Vd (Set.Icc t₀ t₁))
    (hJ : ∀ t ∈ Set.Ico t₀ t₁, HasDerivAt J (Jdot t) t)
    (hv : ∀ t ∈ Set.Ico t₀ t₁, HasDerivAt v (a t) t)
    (hVd : ∀ t ∈ Set.Ico t₀ t₁, HasDerivAt Vd (Ad t) t)
    (_hε : 0 ≤ ε)
    (hres : ∀ t ∈ Set.Ico t₀ t₁,
      ‖Jdot t (v t) + J t (a t) - Ad t‖ ≤ ε)
    (ht : t ∈ Set.Icc t₀ t₁) :
    ‖J t (v t) - Vd t‖ ≤
      ‖J t₀ (v t₀) - Vd t₀‖ + ε * (t - t₀) := by
  have hprod_cont : ContinuousOn (fun s => J s (v s)) (Set.Icc t₀ t₁) :=
    hJ_cont.clm_apply hv_cont
  have herr_cont : ContinuousOn (fun s => J s (v s) - Vd s) (Set.Icc t₀ t₁) :=
    hprod_cont.sub hVd_cont
  have hdiff : ∀ s ∈ Set.Ico t₀ t₁,
      HasDerivWithinAt (fun r => J r (v r) - Vd r)
        (Jdot s (v s) + J s (a s) - Ad s) (Set.Ici s) s := by
    intro s hs
    have hprod := hasDerivAt_kinematic_product (hJ s hs) (hv s hs)
    exact (hprod.sub (hVd s hs)).hasDerivWithinAt
  have hstep : ‖(J t (v t) - Vd t) -
      (J t₀ (v t₀) - Vd t₀)‖ ≤ ε * (t - t₀) :=
    norm_image_sub_le_of_norm_deriv_right_le_segment herr_cont hdiff hres t ht
  have hadd : ‖J t (v t) - Vd t‖ ≤
      ‖(J t (v t) - Vd t) - (J t₀ (v t₀) - Vd t₀)‖ +
        ‖J t₀ (v t₀) - Vd t₀‖ := by
    convert norm_add_le
      ((J t (v t) - Vd t) - (J t₀ (v t₀) - Vd t₀))
      (J t₀ (v t₀) - Vd t₀) using 1 <;> abel
  calc
    ‖J t (v t) - Vd t‖ ≤
        ‖(J t (v t) - Vd t) - (J t₀ (v t₀) - Vd t₀)‖ +
          ‖J t₀ (v t₀) - Vd t₀‖ := hadd
    _ ≤ ε * (t - t₀) + ‖J t₀ (v t₀) - Vd t₀‖ :=
      by simpa [add_comm] using
        (add_le_add_right hstep ‖J t₀ (v t₀) - Vd t₀‖)
    _ = ‖J t₀ (v t₀) - Vd t₀‖ + ε * (t - t₀) := by rw [add_comm]

end Ctrllib

#print axioms Ctrllib.hasDerivAt_kinematic_product
#print axioms Ctrllib.kinematic_compatibility_on_Icc
#print axioms Ctrllib.kinematic_compatibility_error_bound_on_Icc
