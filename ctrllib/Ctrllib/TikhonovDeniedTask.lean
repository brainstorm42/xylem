import Ctrllib.TikhonovRealizedTask

open Matrix

namespace Ctrllib

/-- A singular-label floor bounds the denied-task operator and every denied
task vector. Taking `s` to be the least nonnegative singular label gives the
usual minimum-singular-value estimate. -/
theorem tikhonov_denied_task_bound
    {n : Type*} [Fintype n] [DecidableEq n]
    (Γ : Matrix n n ℝ) (σ : n → ℝ) (lam s : ℝ)
    (hlam : 0 < lam) (hs : 0 ≤ s) (hfloor : ∀ i, s ≤ σ i)
    (hsvd : ∃ U V : Matrix n n ℝ,
      Uᵀ * U = (1 : Matrix n n ℝ) ∧ U * Uᵀ = 1 ∧
      Vᵀ * V = 1 ∧ V * Vᵀ = 1 ∧ Γ = U * diagonal σ * Vᵀ) :
    ‖toEuclideanCLM (𝕜 := ℝ) ((1 : Matrix n n ℝ) - tikhonovRealizedTask Γ lam)‖ ≤
      lam / (s ^ 2 + lam) ∧
    ∀ x : EuclideanSpace ℝ n,
      ‖toEuclideanCLM (𝕜 := ℝ) ((1 : Matrix n n ℝ) - tikhonovRealizedTask Γ lam) x‖ ≤
        lam / (s ^ 2 + lam) * ‖x‖ := by
  obtain ⟨U, V, hUtU, hUUt, hVtV, hVVt, hΓ⟩ := hsvd
  have hsden : 0 < s ^ 2 + lam := by positivity
  have hfactor := tikhonov_denied_task_factorization
    Γ σ lam hlam hUtU hUUt hVtV hVVt hΓ
  have hnorm :
      ‖toEuclideanCLM (𝕜 := ℝ) ((1 : Matrix n n ℝ) - tikhonovRealizedTask Γ lam)‖ ≤
        lam / (s ^ 2 + lam) := by
    refine euclideanCLM_norm_le_of_conj_diagonal
      hUtU hUUt hfactor (div_nonneg hlam.le hsden.le) ?_
    intro i
    have hden : 0 < σ i ^ 2 + lam := by positivity
    have hsq : s ^ 2 ≤ σ i ^ 2 := by
      nlinarith [hfloor i]
    rw [abs_of_nonneg (div_nonneg hlam.le hden.le)]
    apply (div_le_div_iff₀ hden hsden).2
    exact mul_le_mul_of_nonneg_left (by linarith : s ^ 2 + lam ≤ σ i ^ 2 + lam) hlam.le
  refine ⟨hnorm, ?_⟩
  intro x
  exact (ContinuousLinearMap.le_opNorm _ x).trans
    (mul_le_mul_of_nonneg_right hnorm (norm_nonneg x))

end Ctrllib

#print axioms Ctrllib.tikhonov_denied_task_bound
