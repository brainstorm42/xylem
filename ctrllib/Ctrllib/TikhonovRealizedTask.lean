/-
Realized-task map for the square indexed Tikhonov lane.

For `P = Γ * ((ΓᵀΓ + lam I)⁻¹ Γᵀ)`, an indexed orthogonal SVD of `Γ`
gives the modal factorization with coefficients `σ²/(σ²+lam)`.  The
positive-shift assumption makes those coefficients nonnegative and at most
one, which yields a symmetric positive-semidefinite map and the Euclidean
nonexpansive bound.  No strict uniform contraction factor is asserted.
-/
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Positivity
import Ctrllib.TikhonovSVD
import Ctrllib.EuclideanNormBridge

open Matrix

namespace Ctrllib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The realized task map `P_lam = Γ * J_lam^dagger` in the square lane. -/
noncomputable def tikhonovRealizedTask (Γ : Matrix n n ℝ) (lam : ℝ) : Matrix n n ℝ :=
  Γ * ((Alam Γ lam)⁻¹ * Γᵀ)

/--
The modal factorization of the realized task map.  Under the indexed square
SVD `Γ = U * diagonal σ * Vᵀ`, a positive shift gives

`P_lam = U * diagonal (fun i => σ i ^ 2 / (σ i ^ 2 + lam)) * Uᵀ`.

Only the identities needed for this multiplication are assumed here; the full
orthogonal SVD hypotheses are supplied by the properties theorem below.
-/
theorem tikhonov_realized_task_factorization
    (Γ : Matrix n n ℝ) (σ : n → ℝ) (lam : ℝ)
    (hlam : 0 < lam)
    {U V : Matrix n n ℝ}
    (hUtU : Uᵀ * U = (1 : Matrix n n ℝ))
    (hVtV : Vᵀ * V = (1 : Matrix n n ℝ))
    (hVVt : V * Vᵀ = 1)
    (hΓ : Γ = U * diagonal σ * Vᵀ) :
    tikhonovRealizedTask Γ lam =
      U * diagonal (fun i => σ i ^ 2 / (σ i ^ 2 + lam)) * Uᵀ := by
  have hden : ∀ i, 0 < σ i ^ 2 + lam := by
    intro i
    nlinarith [sq_nonneg (σ i)]
  have hinv :=
    alam_inv_eq Γ σ lam hUtU hVtV hVVt hΓ (fun i => (hden i).ne')
  have hΓt : Γᵀ = V * diagonal σ * Uᵀ := by
    rw [hΓ, transpose_mul, transpose_mul, transpose_transpose,
      diagonal_transpose, mul_assoc]
  rw [tikhonovRealizedTask, hinv, hΓt, hΓ]
  calc
    U * diagonal σ * Vᵀ *
        (V * diagonal (fun i => (σ i ^ 2 + lam)⁻¹) * Vᵀ *
          (V * diagonal σ * Uᵀ)) =
      U * (diagonal σ * (Vᵀ * V) *
        diagonal (fun i => (σ i ^ 2 + lam)⁻¹) *
        (Vᵀ * V) * diagonal σ) * Uᵀ := by
          simp only [Matrix.mul_assoc]
    _ = U * diagonal (fun i => σ i ^ 2 / (σ i ^ 2 + lam)) * Uᵀ := by
      rw [hVtV, Matrix.mul_one, Matrix.mul_one,
        diagonal_mul_diagonal, diagonal_mul_diagonal]
      congr 2
      funext i
      field_simp [ne_of_gt (hden i)]

/--
The denied-task complement has the complementary modal factorization

`I - P_lam = U * diagonal (fun i => lam / (σ i ^ 2 + lam)) * Uᵀ`.

This helper exposes the factorization separately so later denied-task bounds
can reuse it without repeating the matrix algebra.
-/
theorem tikhonov_denied_task_factorization
    (Γ : Matrix n n ℝ) (σ : n → ℝ) (lam : ℝ)
    (hlam : 0 < lam)
    {U V : Matrix n n ℝ}
    (hUtU : Uᵀ * U = (1 : Matrix n n ℝ))
    (hUUt : U * Uᵀ = 1)
    (hVtV : Vᵀ * V = (1 : Matrix n n ℝ))
    (hVVt : V * Vᵀ = 1)
    (hΓ : Γ = U * diagonal σ * Vᵀ) :
    (1 : Matrix n n ℝ) - tikhonovRealizedTask Γ lam =
      U * diagonal (fun i => lam / (σ i ^ 2 + lam)) * Uᵀ := by
  have hden : ∀ i, 0 < σ i ^ 2 + lam := by
    intro i
    nlinarith [sq_nonneg (σ i)]
  have hfactor :=
    tikhonov_realized_task_factorization Γ σ lam hlam hUtU hVtV hVVt hΓ
  have hdiag_sub :
      (1 : Matrix n n ℝ) -
          diagonal (fun i => σ i ^ 2 / (σ i ^ 2 + lam)) =
        diagonal (fun i => lam / (σ i ^ 2 + lam)) := by
    rw [← diagonal_one, diagonal_sub]
    congr 1
    funext i
    field_simp [ne_of_gt (hden i)]
    ring
  rw [hfactor, ← hUUt]
  calc
    U * Uᵀ -
        U * diagonal (fun i => σ i ^ 2 / (σ i ^ 2 + lam)) * Uᵀ =
        U * ((1 : Matrix n n ℝ) -
          diagonal (fun i => σ i ^ 2 / (σ i ^ 2 + lam))) * Uᵀ := by
            rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
    _ = U * diagonal (fun i => lam / (σ i ^ 2 + lam)) * Uᵀ := by
      rw [hdiag_sub]

/--
Complete square-lane properties for the realized task map.  The existential
returns the SVD witness together with the modal factorization, positive
semidefiniteness (hence symmetry), and the Euclidean nonexpansive estimate in
both operator-norm and pointwise forms.

The conclusion uses `≤ 1`; it deliberately does not claim a uniform strict
contraction factor, even though each displayed modal coefficient is strictly
below one when `lam > 0`.
-/
theorem tikhonov_realized_task_properties
    (Γ : Matrix n n ℝ) (σ : n → ℝ) (lam : ℝ)
    (hlam : 0 < lam)
    (hsvd : ∃ U V : Matrix n n ℝ,
      Uᵀ * U = (1 : Matrix n n ℝ) ∧
      U * Uᵀ = 1 ∧
      Vᵀ * V = 1 ∧
      V * Vᵀ = 1 ∧
      Γ = U * diagonal σ * Vᵀ) :
    ∃ U V : Matrix n n ℝ,
      Uᵀ * U = (1 : Matrix n n ℝ) ∧
      U * Uᵀ = 1 ∧
      Vᵀ * V = 1 ∧
      V * Vᵀ = 1 ∧
      Γ = U * diagonal σ * Vᵀ ∧
      tikhonovRealizedTask Γ lam =
        U * diagonal (fun i => σ i ^ 2 / (σ i ^ 2 + lam)) * Uᵀ ∧
      (∀ i, 0 ≤ σ i ^ 2 / (σ i ^ 2 + lam) ∧
        σ i ^ 2 / (σ i ^ 2 + lam) < 1) ∧
      (tikhonovRealizedTask Γ lam).PosSemidef ∧
      ((1 : Matrix n n ℝ) - tikhonovRealizedTask Γ lam).PosSemidef ∧
      (tikhonovRealizedTask Γ lam).IsHermitian ∧
      ‖toEuclideanCLM (𝕜 := ℝ) (tikhonovRealizedTask Γ lam)‖ ≤ 1 ∧
      ∀ x : EuclideanSpace ℝ n,
        ‖toEuclideanCLM (𝕜 := ℝ) (tikhonovRealizedTask Γ lam) x‖ ≤ ‖x‖ := by
  obtain ⟨U, V, hUtU, hUUt, hVtV, hVVt, hΓ⟩ := hsvd
  have hden : ∀ i, 0 < σ i ^ 2 + lam := by
    intro i
    nlinarith [sq_nonneg (σ i)]
  have hfactor :=
    tikhonov_realized_task_factorization Γ σ lam hlam hUtU hVtV hVVt hΓ
  have hq0 : ∀ i, 0 ≤ σ i ^ 2 / (σ i ^ 2 + lam) := by
    intro i
    exact div_nonneg (sq_nonneg (σ i)) (hden i).le
  have hq1 : ∀ i, σ i ^ 2 / (σ i ^ 2 + lam) ≤ 1 := by
    intro i
    apply (div_le_iff₀ (hden i)).2
    nlinarith
  have hq_lt : ∀ i, σ i ^ 2 / (σ i ^ 2 + lam) < 1 := by
    intro i
    apply (div_lt_iff₀ (hden i)).2
    nlinarith
  have hcomp0 : ∀ i, 0 ≤ lam / (σ i ^ 2 + lam) := by
    intro i
    exact div_nonneg hlam.le (hden i).le
  have hdiag :
      (diagonal (fun i => σ i ^ 2 / (σ i ^ 2 + lam))).PosSemidef := by
    exact (Matrix.posSemidef_diagonal_iff).2 hq0
  have hpsd : (tikhonovRealizedTask Γ lam).PosSemidef := by
    rw [hfactor]
    simpa only [conjTranspose_eq_transpose_of_trivial] using
      hdiag.mul_mul_conjTranspose_same U
  have hcompfactor :=
    tikhonov_denied_task_factorization Γ σ lam hlam hUtU hUUt hVtV hVVt hΓ
  have hdiag_sub_psd :
      (diagonal (fun i => lam / (σ i ^ 2 + lam))).PosSemidef := by
    exact (Matrix.posSemidef_diagonal_iff).2 hcomp0
  have hcomp_psd :
      ((1 : Matrix n n ℝ) - tikhonovRealizedTask Γ lam).PosSemidef := by
    rw [hcompfactor]
    simpa only [conjTranspose_eq_transpose_of_trivial] using
      hdiag_sub_psd.mul_mul_conjTranspose_same U
  have hnorm :
      ‖toEuclideanCLM (𝕜 := ℝ) (tikhonovRealizedTask Γ lam)‖ ≤ 1 := by
    refine euclideanCLM_norm_le_of_conj_diagonal
      (M := tikhonovRealizedTask Γ lam) (U := U) (V := U)
      hUtU hUUt hfactor (by norm_num) ?_
    intro i
    rw [abs_of_nonneg (hq0 i)]
    exact hq1 i
  have hpoint : ∀ x : EuclideanSpace ℝ n,
      ‖toEuclideanCLM (𝕜 := ℝ) (tikhonovRealizedTask Γ lam) x‖ ≤ ‖x‖ := by
    intro x
    calc
      ‖toEuclideanCLM (𝕜 := ℝ) (tikhonovRealizedTask Γ lam) x‖ ≤
          ‖toEuclideanCLM (𝕜 := ℝ) (tikhonovRealizedTask Γ lam)‖ * ‖x‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg x)
      _ = ‖x‖ := one_mul _
  exact ⟨U, V, hUtU, hUUt, hVtV, hVVt, hΓ, hfactor,
    fun i => ⟨hq0 i, hq_lt i⟩, hpsd, hcomp_psd, hpsd.isHermitian,
    hnorm, hpoint⟩

end Ctrllib

#print axioms Ctrllib.tikhonov_realized_task_factorization
#print axioms Ctrllib.tikhonov_denied_task_factorization
#print axioms Ctrllib.tikhonov_realized_task_properties
