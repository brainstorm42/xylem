import Ctrllib.EstimationError

open Filter
open scoped Topology

namespace Ctrllib

/-- A nonnegative strict contraction with a bounded additive term eventually stays within
the contraction radius plus any prescribed positive tolerance. -/
theorem norm_error_eventually_le_contraction_radius
    (E : Type*) [NormedAddCommGroup E] (e : ℕ → E) (r b : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (_hb : 0 ≤ b)
    (hstep : ∀ k : ℕ, ‖e (k + 1)‖ ≤ r * ‖e k‖ + b) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ k : ℕ, N ≤ k → ‖e k‖ ≤ b / (1 - r) + ε := by
  intro ε hε
  have hp : Tendsto (fun k : ℕ => r ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (𝕜 := ℝ) hr0 hr1
  have hfirst : Tendsto (fun k : ℕ => r ^ k * ‖e 0‖) atTop (𝓝 0) := by
    simpa using hp.mul_const ‖e 0‖
  have hnum : Tendsto (fun k : ℕ => 1 - r ^ k) atTop (𝓝 (1 - 0)) := by
    simpa using tendsto_const_nhds.sub hp
  have hquot : Tendsto (fun k : ℕ => (1 - r ^ k) / (1 - r)) atTop
      (𝓝 ((1 - 0) / (1 - r))) := by
    simpa using hnum.div_const (1 - r)
  have hsecond : Tendsto (fun k : ℕ => b * ((1 - r ^ k) / (1 - r))) atTop
      (𝓝 (b * ((1 - 0) / (1 - r)))) := by
    simpa using hquot.const_mul b
  have hlim := hfirst.add hsecond
  have hev := hlim.eventually (Iio_mem_nhds (lt_add_of_pos_right _ hε))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨N, ?_⟩
  intro k hk
  have hfin := norm_error_le_contraction_bound hr0 hr1 hstep k
  exact le_of_lt (lt_of_le_of_lt hfin (by simpa [div_eq_mul_inv, mul_assoc] using hN k hk))

end Ctrllib

#print axioms Ctrllib.norm_error_eventually_le_contraction_radius
