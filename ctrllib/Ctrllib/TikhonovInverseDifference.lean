/-
Matrix lift of the scalar Tikhonov inverse-difference bound (research Phase 2, lane P,
task P2.2 "matrix/SVD residual interface").

`TikhonovSVD.tikhonov_inverse_difference_scalar_bound` proves, for one singular value,
`|σ⁻¹ - σ / (σ² + lam)| ≤ lam / δ³` whenever `0 < δ ≤ σ` and `0 ≤ lam`.  This module
states the same fact for a square real matrix `Γ` with an indexed orthogonal SVD
`Γ = U · diagonal σ · Vᵀ`:

  `Γ⁻¹ - (Alam Γ lam)⁻¹ * Γᵀ = V · diagonal (σ⁻¹ - σ/(σ² + lam)) · Uᵀ`
  (`tikhonov_inverse_difference_factor`), and hence
  `‖toEuclideanCLM (Γ⁻¹ - (Alam Γ lam)⁻¹ * Γᵀ)‖ ≤ lam / δ³`
  (`tikhonov_inverse_difference_norm_bound`).

Here `Γ⁻¹` is the exact inverse (the runtime's exact tier) and
`(Alam Γ lam)⁻¹ * Γᵀ = (ΓᵀΓ + lam·1)⁻¹ Γᵀ` is the normal-equations Tikhonov inverse
(the runtime's damped tier); their difference is the object the research reports call
`Δ_B` and bound by `lambda_Gamma / s_min_G³`.  The bound is uniform over every square
`Γ` whose singular values all lie at or above `δ`; nothing here says which `Γ`, `δ`,
or `lam` the implementation attains — that correspondence is the written interface in
the corresponding local note (P2.2), not a
theorem.

Scope honesty: square `Γ` only (the `TikhonovSVD` convention), the Euclidean operator
norm via `EuclideanNormBridge.euclideanCLM_norm_le_of_conj_diagonal`, and the Lean
`lam` is the quantity added to `σ²` in the denominator (the runtime adds
`lamda ** 2`; see the P2.2 interface).
-/
import Ctrllib.TikhonovSVD
import Ctrllib.EuclideanNormBridge

open Matrix

namespace Ctrllib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The exact inverse of an indexed orthogonal SVD with nonvanishing singular values. -/
theorem inv_eq_of_svd (Γ : Matrix n n ℝ) (σ : n → ℝ)
    {U V : Matrix n n ℝ} (hUUt : U * Uᵀ = (1 : Matrix n n ℝ))
    (hVtV : Vᵀ * V = (1 : Matrix n n ℝ))
    (hΓ : Γ = U * diagonal σ * Vᵀ) (hne : ∀ i, σ i ≠ 0) :
    Γ⁻¹ = V * diagonal (fun i => (σ i)⁻¹) * Uᵀ := by
  refine Matrix.inv_eq_right_inv ?_
  rw [hΓ]
  calc U * diagonal σ * Vᵀ * (V * diagonal (fun i => (σ i)⁻¹) * Uᵀ)
      = U * (diagonal σ * (Vᵀ * V) * diagonal (fun i => (σ i)⁻¹)) * Uᵀ := by
        simp only [Matrix.mul_assoc]
  _ = 1 := by
        rw [hVtV, Matrix.mul_one, diagonal_mul_diagonal]
        have hone : (fun i => σ i * (σ i)⁻¹) = (1 : n → ℝ) := by
          funext i
          simp [mul_inv_cancel₀ (hne i)]
        rw [hone]
        simp [hUUt]

/-- The normal-equations Tikhonov inverse `(ΓᵀΓ + lam·1)⁻¹ Γᵀ` of an indexed orthogonal
SVD, in factored form with the named factors (the existential of
`tikhonov_plus_singular_values` is unpacked here so the difference below can be taken
with the same `U`, `V`). -/
theorem tikhonov_inverse_eq_of_svd (Γ : Matrix n n ℝ) (σ : n → ℝ) (lam : ℝ)
    {U V : Matrix n n ℝ} (hUtU : Uᵀ * U = (1 : Matrix n n ℝ))
    (hVtV : Vᵀ * V = (1 : Matrix n n ℝ)) (hVVt : V * Vᵀ = 1)
    (hΓ : Γ = U * diagonal σ * Vᵀ) (hne : ∀ i, σ i ^ 2 + lam ≠ 0) :
    (Alam Γ lam)⁻¹ * Γᵀ = V * diagonal (fun i => σ i / (σ i ^ 2 + lam)) * Uᵀ := by
  have hinv := alam_inv_eq Γ σ lam hUtU hVtV hVVt hΓ hne
  have hΓt : Γᵀ = V * diagonal σ * Uᵀ := by
    rw [hΓ, transpose_mul, transpose_mul, transpose_transpose, diagonal_transpose, mul_assoc]
  rw [hinv, hΓt]
  calc V * diagonal (fun i => (σ i ^ 2 + lam)⁻¹) * Vᵀ * (V * diagonal σ * Uᵀ)
      = V * (diagonal (fun i => (σ i ^ 2 + lam)⁻¹) * (Vᵀ * V) * diagonal σ) * Uᵀ := by
        simp only [Matrix.mul_assoc]
  _ = V * diagonal (fun i => σ i / (σ i ^ 2 + lam)) * Uᵀ := by
        rw [hVtV, Matrix.mul_one, diagonal_mul_diagonal]
        congr 2
        funext i
        simp [div_eq_inv_mul]

/-- **Factored inverse difference.**  Exact inverse minus Tikhonov inverse is the
orthogonal conjugate of the diagonal of scalar differences
`σ i⁻¹ - σ i / (σ i ^ 2 + lam)` — the matrix whose entries
`tikhonov_inverse_difference_scalar_bound` controls one at a time. -/
theorem tikhonov_inverse_difference_factor (Γ : Matrix n n ℝ) (σ : n → ℝ) (lam : ℝ)
    {U V : Matrix n n ℝ} (hUtU : Uᵀ * U = (1 : Matrix n n ℝ)) (hUUt : U * Uᵀ = 1)
    (hVtV : Vᵀ * V = (1 : Matrix n n ℝ)) (hVVt : V * Vᵀ = 1)
    (hΓ : Γ = U * diagonal σ * Vᵀ)
    (hσne : ∀ i, σ i ≠ 0) (hne : ∀ i, σ i ^ 2 + lam ≠ 0) :
    Γ⁻¹ - (Alam Γ lam)⁻¹ * Γᵀ
      = V * diagonal (fun i => (σ i)⁻¹ - σ i / (σ i ^ 2 + lam)) * Uᵀ := by
  rw [inv_eq_of_svd Γ σ hUUt hVtV hΓ hσne,
    tikhonov_inverse_eq_of_svd Γ σ lam hUtU hVtV hVVt hΓ hne,
    ← Matrix.sub_mul, ← Matrix.mul_sub, ← diagonal_sub]

/-- **Matrix Tikhonov inverse-difference bound.**  If every singular value of the
square `Γ` is at least `δ > 0` and `0 ≤ lam`, then the Euclidean operator norm of
`Γ⁻¹ - (ΓᵀΓ + lam·1)⁻¹ Γᵀ` is at most `lam / δ ^ 3`.  This is the matrix form of
`tikhonov_inverse_difference_scalar_bound`; it is uniform in `Γ` over the stated
singular-value floor and says nothing about which floor a trajectory attains. -/
theorem tikhonov_inverse_difference_norm_bound
    (Γ : Matrix n n ℝ) (σ : n → ℝ) (δ lam : ℝ)
    (hδ : 0 < δ) (hlam : 0 ≤ lam) (hσ : ∀ i, δ ≤ σ i)
    (hsvd : ∃ U V : Matrix n n ℝ,
      Uᵀ * U = (1 : Matrix n n ℝ) ∧
      U * Uᵀ = 1 ∧
      Vᵀ * V = 1 ∧
      V * Vᵀ = 1 ∧
      Γ = U * diagonal σ * Vᵀ) :
    ‖toEuclideanCLM (𝕜 := ℝ) (Γ⁻¹ - (Alam Γ lam)⁻¹ * Γᵀ)‖ ≤ lam / δ ^ 3 := by
  obtain ⟨U, V, hUtU, hUUt, hVtV, hVVt, hΓ⟩ := hsvd
  have hσpos : ∀ i, 0 < σ i := fun i => lt_of_lt_of_le hδ (hσ i)
  have hσne : ∀ i, σ i ≠ 0 := fun i => (hσpos i).ne'
  have hne : ∀ i, σ i ^ 2 + lam ≠ 0 := by
    intro i
    have : 0 < σ i ^ 2 + lam := by nlinarith [hσpos i]
    exact this.ne'
  have hfactor := tikhonov_inverse_difference_factor Γ σ lam hUtU hUUt hVtV hVVt hΓ hσne hne
  refine euclideanCLM_norm_le_of_conj_diagonal hVtV hUUt hfactor ?_ ?_
  · positivity
  · intro i
    exact tikhonov_inverse_difference_scalar_bound hδ hlam (hσ i)

end Ctrllib

#print axioms Ctrllib.inv_eq_of_svd
#print axioms Ctrllib.tikhonov_inverse_eq_of_svd
#print axioms Ctrllib.tikhonov_inverse_difference_factor
#print axioms Ctrllib.tikhonov_inverse_difference_norm_bound
