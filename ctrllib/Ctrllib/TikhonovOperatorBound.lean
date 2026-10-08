/-
Universal Euclidean operator-norm bound for the normal-equations Tikhonov map.

The theorem below is the matrix lift of `Ctrllib.tikhonov_uniform_bound`.  It
uses the generic indexed square SVD from `TikhonovSVD` and the orthogonal
diagonal operator-norm bridge from `EuclideanNormBridge`; no spectral floor,
schedule, application map, or dimension-specific premise is introduced.
-/
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Positivity
import Ctrllib.TikhonovSVD
import Ctrllib.TikhonovUniformBound
import Ctrllib.EuclideanNormBridge

open Matrix

namespace Ctrllib

variable {n : Type*} [Fintype n] [DecidableEq n]

/--
**Universal Tikhonov operator bound.**  For an indexed square SVD
`Γ = U · diagonal σ · Vᵀ` with nonnegative singular-value labels, the
Euclidean induced norm of the regularized normal-equations map is bounded by
`1 / (2 * √lam)` whenever `lam > 0`:

`‖toEuclideanCLM ((Alam Γ lam)⁻¹ * Γᵀ)‖ ≤ 1 / (2 * Real.sqrt lam)`.

The only matrix premises are the displayed orthogonal SVD identities.  The
positivity of `lam` supplies every denominator and the scalar universal cap;
no scheduled floor or `IsUnit (Alam Γ lam)` premise is needed.
-/
theorem tikhonov_operator_norm_bound
    (Γ : Matrix n n ℝ) (σ : n → ℝ) (lam : ℝ)
    (hσ : ∀ i, 0 ≤ σ i)
    (hlam : 0 < lam)
    (hsvd : ∃ U V : Matrix n n ℝ,
      Uᵀ * U = (1 : Matrix n n ℝ) ∧
      U * Uᵀ = 1 ∧
      Vᵀ * V = 1 ∧
      V * Vᵀ = 1 ∧
      Γ = U * diagonal σ * Vᵀ) :
    ‖toEuclideanCLM (𝕜 := ℝ) ((Alam Γ lam)⁻¹ * Γᵀ)‖ ≤
      1 / (2 * Real.sqrt lam) := by
  obtain ⟨U, V, hUtU, hUUt, hVtV, hVVt, hΓ⟩ := hsvd
  have hden : ∀ i, 0 < σ i ^ 2 + lam := by
    intro i
    nlinarith [sq_nonneg (σ i)]
  have hinv :=
    alam_inv_eq Γ σ lam hUtU hVtV hVVt hΓ (fun i => (hden i).ne')
  have hΓt : Γᵀ = V * diagonal σ * Uᵀ := by
    rw [hΓ, transpose_mul, transpose_mul, transpose_transpose,
      diagonal_transpose, mul_assoc]
  have hfactor :
      (Alam Γ lam)⁻¹ * Γᵀ =
        V * diagonal (fun i => σ i / (σ i ^ 2 + lam)) * Uᵀ := by
    rw [hinv, hΓt]
    calc
      V * diagonal (fun i => (σ i ^ 2 + lam)⁻¹) * Vᵀ *
          (V * diagonal σ * Uᵀ) =
        V * (diagonal (fun i => (σ i ^ 2 + lam)⁻¹) *
          (Vᵀ * V) * diagonal σ) * Uᵀ := by
            simp only [Matrix.mul_assoc]
      _ = V * diagonal (fun i => σ i / (σ i ^ 2 + lam)) * Uᵀ := by
        rw [hVtV, Matrix.mul_one, diagonal_mul_diagonal]
        congr 2
        funext i
        simp [div_eq_inv_mul]
  refine euclideanCLM_norm_le_of_conj_diagonal hVtV hUUt hfactor ?_ ?_
  · positivity
  · intro i
    rw [abs_of_nonneg (tikhonov_uniform_bound (hσ i) hlam).1]
    exact (tikhonov_uniform_bound (hσ i) hlam).2

end Ctrllib

#print axioms Ctrllib.tikhonov_operator_norm_bound
