/-
Weighted right inverses for a finite real rectangular map.

For `A : Matrix m n ℝ` and an SPD weight `W : Matrix n n ℝ`, the controller
formula is

  B = W⁻¹ Aᵀ (A W⁻¹ Aᵀ)⁻¹.

The source interface is the rectangular map in the rectangular source interface: `A` has
six output rows and `n + 3` decision columns.  The same algebra is reusable for
any equality-constrained weighted allocation map once its constraint matrix is
typed.  The theorem below keeps the full-row-rank premise explicit as
surjectivity of `A.mulVec`; no square or unrestricted inverse is claimed.
-/
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef

open Matrix

namespace Ctrllib

section

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-! ### Full-row-rank bridge -/

omit [DecidableEq m] [DecidableEq n] in
/-- A surjective real rectangular map has an injective transpose map.

This is the finite-dimensional full-row-rank bridge needed to make the left
Gramian positive definite.  The proof uses only the Euclidean dot product:
if `Aᵀ d = 0`, surjectivity makes every output a value `A v`, hence it is
orthogonal to `d`; taking the output to be `d` gives `d = 0`.
-/
theorem mulVec_transpose_injective_of_surjective {A : Matrix m n ℝ}
    (hA : Function.Surjective A.mulVec) :
    Function.Injective Aᵀ.mulVec := by
  intro x y hxy
  let d : m → ℝ := x - y
  have hd : Aᵀ *ᵥ d = 0 := by
    dsimp [d]
    rw [mulVec_sub, hxy, sub_self]
  have hdot : ∀ z : m → ℝ, z ⬝ᵥ d = 0 := by
    intro z
    obtain ⟨v, hv⟩ := hA z
    calc
      z ⬝ᵥ d = (A *ᵥ v) ⬝ᵥ d := by rw [hv]
      _ = d ⬝ᵥ (A *ᵥ v) := dotProduct_comm _ _
      _ = (d ᵥ* A) ⬝ᵥ v := by rw [dotProduct_mulVec]
      _ = (Aᵀ *ᵥ d) ⬝ᵥ v := by rw [← mulVec_transpose]
      _ = 0 := by rw [hd, zero_dotProduct]
  have hd0 : d = 0 := dotProduct_self_eq_zero.mp (hdot d)
  exact sub_eq_zero.mp (by simpa [d] using hd0)

/-! ### Weighted Gramian -/

omit [DecidableEq m] in
/-- The weighted left Gramian is positive definite under SPD `W` and
full-row-rank `A`.

`W⁻¹` is SPD by the matrix inverse theorem, and the preceding transpose
bridge supplies the injectivity needed by the congruence theorem. -/
theorem weighted_gram_posDef {A : Matrix m n ℝ} {W : Matrix n n ℝ}
    (hW : W.PosDef) (hA : Function.Surjective A.mulVec) :
    (A * W⁻¹ * Aᵀ).PosDef := by
  have hAT : Function.Injective Aᵀ.mulVec :=
    mulVec_transpose_injective_of_surjective hA
  have h := (hW.inv).conjTranspose_mul_mul_same hAT
  rwa [conjTranspose_eq_transpose_of_trivial, transpose_transpose] at h

/-- The Gramian is a unit, so its nonsingular inverse is a genuine inverse. -/
theorem weighted_gram_isUnit {A : Matrix m n ℝ} {W : Matrix n n ℝ}
    (hW : W.PosDef) (hA : Function.Surjective A.mulVec) :
    IsUnit (A * W⁻¹ * Aᵀ) :=
  (weighted_gram_posDef hW hA).isUnit

/-! ### Right inverse -/

/-- The finite real weighted right inverse used by equality-constrained allocation
and by the generic equality-constrained quadratic problem. -/
noncomputable def weightedRightInverse (W : Matrix n n ℝ) (A : Matrix m n ℝ) : Matrix n m ℝ :=
  W⁻¹ * Aᵀ * (A * W⁻¹ * Aᵀ)⁻¹

/-- The closed form is a right inverse whenever the displayed Gramian is a
unit.  This algebraic interface makes the exact missing premise visible to
callers that do not want to derive it from SPD and surjectivity. -/
theorem weighted_right_inverse_mul_of_gram_isUnit {A : Matrix m n ℝ}
    {W : Matrix n n ℝ} (hG : IsUnit (A * W⁻¹ * Aᵀ)) :
    A * weightedRightInverse W A = 1 := by
  have hGdet : IsUnit (A * W⁻¹ * Aᵀ).det :=
    (isUnit_iff_isUnit_det _).mp hG
  calc
    A * weightedRightInverse W A =
        (A * W⁻¹ * Aᵀ) * (A * W⁻¹ * Aᵀ)⁻¹ := by
      simp only [weightedRightInverse]
      calc
        A * (W⁻¹ * Aᵀ * (A * W⁻¹ * Aᵀ)⁻¹) =
            (A * (W⁻¹ * Aᵀ)) * (A * W⁻¹ * Aᵀ)⁻¹ :=
          (Matrix.mul_assoc A (W⁻¹ * Aᵀ) (A * W⁻¹ * Aᵀ)⁻¹).symm
        _ = (A * W⁻¹ * Aᵀ) * (A * W⁻¹ * Aᵀ)⁻¹ := by
          rw [← Matrix.mul_assoc A W⁻¹ Aᵀ]
    _ = 1 := Matrix.mul_nonsing_inv _ hGdet

/-- Under the conventional SPD and full-row-rank premises, the weighted
right inverse is exact. -/
theorem weighted_right_inverse_mul {A : Matrix m n ℝ} {W : Matrix n n ℝ}
    (hW : W.PosDef) (hA : Function.Surjective A.mulVec) :
    A * weightedRightInverse W A = 1 :=
  weighted_right_inverse_mul_of_gram_isUnit (weighted_gram_isUnit hW hA)

/-- Feasibility of the minimum-norm command `B b` for every target `b`. -/
theorem weighted_right_inverse_feasible {A : Matrix m n ℝ} {W : Matrix n n ℝ}
    (hW : W.PosDef) (hA : Function.Surjective A.mulVec) (b : m → ℝ) :
    A *ᵥ (weightedRightInverse W A *ᵥ b) = b := by
  calc
    A *ᵥ (weightedRightInverse W A *ᵥ b) =
        (A * weightedRightInverse W A) *ᵥ b := by
      rw [mulVec_mulVec]
    _ = (1 : Matrix m m ℝ) *ᵥ b := by rw [weighted_right_inverse_mul hW hA]
    _ = b := one_mulVec b

end

end Ctrllib

#print axioms Ctrllib.mulVec_transpose_injective_of_surjective
#print axioms Ctrllib.weighted_gram_posDef
#print axioms Ctrllib.weighted_gram_isUnit
#print axioms Ctrllib.weighted_right_inverse_mul_of_gram_isUnit
#print axioms Ctrllib.weighted_right_inverse_mul
#print axioms Ctrllib.weighted_right_inverse_feasible
