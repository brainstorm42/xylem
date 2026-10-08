import Ctrllib.TrackingStrictBound
import Mathlib.Analysis.Real.Sqrt

/-!
# Uncertainty-to-forcing norm interface

The theorems below are deliberately Euclidean and pointwise.  They turn
square-root-of-dot-product bounds into the `hFe` and `hFg` premises consumed by
`Ctrllib.strict_rate_dominated_forced`.  They do not identify an FFSM forcing
term, or assert that an estimator, actuator, or model discrepancy realizes the
premises.
Conventional derivation: the corresponding derivation record's
the corresponding local note.
-/

open Matrix

namespace Ctrllib

variable {n : Type*} [Fintype n]

theorem forcing_state_dot_bound {e F : n → ℝ} {f : ℝ}
    (hF : Real.sqrt (F ⬝ᵥ F) ≤ f) :
    -(e ⬝ᵥ F) ≤ f * Real.sqrt (e ⬝ᵥ e) := by
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset n) e (fun i => -F i)
  have hcs' : -(e ⬝ᵥ F) ≤ Real.sqrt (e ⬝ᵥ e) * Real.sqrt (F ⬝ᵥ F) := by
    simpa [dotProduct, neg_mul, sq] using hcs
  have he : 0 ≤ Real.sqrt (e ⬝ᵥ e) := Real.sqrt_nonneg _
  calc
    -(e ⬝ᵥ F) ≤ Real.sqrt (e ⬝ᵥ e) * Real.sqrt (F ⬝ᵥ F) := hcs'
    _ ≤ Real.sqrt (e ⬝ᵥ e) * f := mul_le_mul_of_nonneg_left hF he
    _ = f * Real.sqrt (e ⬝ᵥ e) := by ring

theorem forcing_stiffness_dot_bound {m : Type*} [Fintype m]
    {g F : n → ℝ} {γ f : ℝ} {x : m → ℝ}
    (hf : 0 ≤ f)
    (hg : Real.sqrt (g ⬝ᵥ g) ≤ γ * Real.sqrt (x ⬝ᵥ x))
    (hF : Real.sqrt (F ⬝ᵥ F) ≤ f) :
    -(g ⬝ᵥ F) ≤ γ * f * Real.sqrt (x ⬝ᵥ x) := by
  have hdot := forcing_state_dot_bound (e := g) (F := F) hF
  calc
    -(g ⬝ᵥ F) ≤ f * Real.sqrt (g ⬝ᵥ g) := hdot
    _ ≤ f * (γ * Real.sqrt (x ⬝ᵥ x)) := mul_le_mul_of_nonneg_left hg hf
    _ = γ * f * Real.sqrt (x ⬝ᵥ x) := by ring

private theorem sqrt_dot_add_le {u v : n → ℝ} :
    Real.sqrt ((u + v) ⬝ᵥ (u + v)) ≤
      Real.sqrt (u ⬝ᵥ u) + Real.sqrt (v ⬝ᵥ v) := by
  have huv := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset n) u v
  have huv' : u ⬝ᵥ v ≤ Real.sqrt (u ⬝ᵥ u) * Real.sqrt (v ⬝ᵥ v) := by
    simpa [dotProduct, sq] using huv
  have hquad : (u + v) ⬝ᵥ (u + v) ≤
      (Real.sqrt (u ⬝ᵥ u) + Real.sqrt (v ⬝ᵥ v)) ^ 2 := by
    have huu : 0 ≤ u ⬝ᵥ u := dotProduct_self_nonneg' u
    have hvv : 0 ≤ v ⬝ᵥ v := dotProduct_self_nonneg' v
    have hsu := Real.sq_sqrt huu
    have hsv := Real.sq_sqrt hvv
    have hexpand : (u + v) ⬝ᵥ (u + v) =
        u ⬝ᵥ u + 2 * (u ⬝ᵥ v) + v ⬝ᵥ v := by
      simp [dotProduct, add_mul, mul_add, Finset.sum_add_distrib]
      have hcomm : (∑ i, v i * u i) = ∑ i, u i * v i := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      rw [hcomm]
      ring
    rw [hexpand]
    nlinarith [huv', Real.sqrt_nonneg (u ⬝ᵥ u), Real.sqrt_nonneg (v ⬝ᵥ v)]
  exact (Real.sqrt_le_iff.mpr ⟨by positivity, hquad⟩)

theorem forcing_combined_bound {F F_est F_act F_model : n → ℝ}
    {f_est f_act f_model : ℝ}
    (hest : Real.sqrt (F_est ⬝ᵥ F_est) ≤ f_est)
    (hact : Real.sqrt (F_act ⬝ᵥ F_act) ≤ f_act)
    (hmodel : Real.sqrt (F_model ⬝ᵥ F_model) ≤ f_model)
    (hparts : F = F_est + F_act + F_model) :
    Real.sqrt (F ⬝ᵥ F) ≤ f_est + f_act + f_model := by
  rw [hparts]
  calc
    Real.sqrt ((F_est + F_act + F_model) ⬝ᵥ (F_est + F_act + F_model))
        ≤ Real.sqrt ((F_est + F_act) ⬝ᵥ (F_est + F_act)) +
          Real.sqrt (F_model ⬝ᵥ F_model) := sqrt_dot_add_le
    _ ≤ (Real.sqrt (F_est ⬝ᵥ F_est) + Real.sqrt (F_act ⬝ᵥ F_act)) +
          Real.sqrt (F_model ⬝ᵥ F_model) := by
      gcongr
      exact sqrt_dot_add_le
    _ ≤ f_est + f_act + f_model := by linarith

#print axioms Ctrllib.forcing_state_dot_bound
#print axioms Ctrllib.forcing_stiffness_dot_bound
#print axioms Ctrllib.forcing_combined_bound

end Ctrllib
