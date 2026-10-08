import Ctrllib.EstimationError

/-!
Uniform eventual observer threshold (atlas obligation E1).

A family of error sequences with one shared contraction factor, disturbance
ceiling, and initial-error bound has one threshold that works for every family
member.  The proof uses the finite-time estimate
`norm_error_le_contraction_bound` with a common scalar majorant before taking
the geometric-power limit.  No probability, measurability, or observer-model
assumption is introduced here; those belong to later observer-to-risk
composition interfaces.
-/

open Filter
open scoped Topology

namespace Ctrllib

variable {Theta E : Type*} [NormedAddCommGroup E]

/-- **Uniform eventual contraction radius (atlas E1).**  For a family of
error sequences sharing `0 ≤ r < 1`, `b ≥ 0`, and `M ≥ 0`, a common initial
bound `‖e θ 0‖ ≤ M` and a common one-step recursion imply that one natural
number `N` works for every `θ` and every `k ≥ N`.  The initial and disturbance
nonnegativity premises are retained as the intended observer interface; the
scalar convergence argument itself only uses the shared initial inequality and
the contraction condition. -/
theorem norm_error_family_eventually_le_contraction_radius
    (e : Theta → ℕ → E) {r b M : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (_hb : 0 ≤ b) (_hM : 0 ≤ M)
    (hinit : ∀ θ, ‖e θ 0‖ ≤ M)
    (hstep : ∀ θ k, ‖e θ (k + 1)‖ ≤ r * ‖e θ k‖ + b) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ (θ : Theta) (k : ℕ), N ≤ k →
      ‖e θ k‖ ≤ b / (1 - r) + ε := by
  intro ε hε
  have hp : Tendsto (fun k : ℕ ↦ r ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (𝕜 := ℝ) hr0 hr1
  have hfirst : Tendsto (fun k : ℕ ↦ r ^ k * M) atTop (𝓝 0) := by
    simpa using hp.mul_const M
  have hnum : Tendsto (fun k : ℕ ↦ 1 - r ^ k) atTop (𝓝 (1 - 0)) := by
    simpa using tendsto_const_nhds.sub hp
  have hquot : Tendsto (fun k : ℕ ↦ (1 - r ^ k) / (1 - r)) atTop
      (𝓝 ((1 - 0) / (1 - r))) := by
    simpa using hnum.div_const (1 - r)
  have hsecond : Tendsto (fun k : ℕ ↦ b * ((1 - r ^ k) / (1 - r))) atTop
      (𝓝 (b * ((1 - 0) / (1 - r)))) := by
    simpa using hquot.const_mul b
  have hmajorant : Tendsto
      (fun k : ℕ ↦ r ^ k * M + b * ((1 - r ^ k) / (1 - r))) atTop
      (𝓝 (b / (1 - r))) := by
    simpa [div_eq_mul_inv] using hfirst.add hsecond
  have hev := hmajorant.eventually
    (Iio_mem_nhds (lt_add_of_pos_right (b / (1 - r)) hε))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨N, ?_⟩
  intro θ k hk
  have hfinite := norm_error_le_contraction_bound hr0 hr1 (hstep θ) k
  have hinitial : r ^ k * ‖e θ 0‖ ≤ r ^ k * M :=
    mul_le_mul_of_nonneg_left (hinit θ) (pow_nonneg hr0 k)
  have hmajorant_k : ‖e θ k‖ ≤ r ^ k * M + b * ((1 - r ^ k) / (1 - r)) :=
    hfinite.trans (add_le_add hinitial le_rfl)
  exact le_of_lt (hmajorant_k.trans_lt (hN k hk))

end Ctrllib

#print axioms Ctrllib.norm_error_family_eventually_le_contraction_radius
