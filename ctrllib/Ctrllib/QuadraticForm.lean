/-
Reusable weighted bilinear-form algebra for the isolated controls pilot.

The contract corresponds to the mathematical content of NASALib's
`def_matrix_weighted_inner_prod.smat_ip_sym`: a symmetric matrix makes the
matrix-weighted bilinear form symmetric. The Lean statement exposes the
matrix and finite index type directly; it does not copy the PVS list/matrix
representation or its subtype encoding of semidefiniteness.
-/
import Mathlib.Data.Matrix.Mul
import Mathlib.Basic.Real.Basic

open Matrix

namespace Ctrllib

variable {n : Type*} [Fintype n]

/- The PSD premise carried by PVS's `spos_defn?` is not needed for this
   algebraic identity, so the reusable contract keeps only its symmetry
   projection. -/
theorem dotProduct_mulVec_symm_of_transpose_eq {A : Matrix n n ℝ}
    (hA : Aᵀ = A) (u v : n → ℝ) :
    u ⬝ᵥ A *ᵥ v = v ⬝ᵥ A *ᵥ u := by
  rw [dotProduct_mulVec u A v, ← mulVec_transpose, hA, dotProduct_comm]

#print axioms Ctrllib.dotProduct_mulVec_symm_of_transpose_eq

end Ctrllib
