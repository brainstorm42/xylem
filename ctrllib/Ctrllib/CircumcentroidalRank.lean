import Ctrllib.CircumcentroidalCorrection
import Mathlib.LinearAlgebra.Matrix.Rank

namespace Ctrllib

/-- The change made by a factored correction has rank at most its inner
dimension. This bounds the update, not the rank of the corrected matrix. -/
theorem correctedJacobian_update_rank_le
    {m n r : Type*} [Fintype m] [Fintype n] [Fintype r]
    (J : Matrix m n ℝ) (U : Matrix m r ℝ) (V : Matrix r n ℝ) :
    (J - correctedJacobian J U V).rank ≤ Fintype.card r := by
  have hupdate : J - correctedJacobian J U V = U * V := by
    simp [correctedJacobian]
  rw [hupdate]
  exact (Matrix.rank_mul_le_left U V).trans (Matrix.rank_le_card_width U)

/-- The six-by-three correction changes the Jacobian by rank at most three;
no full-rank condition on either correction factor is assumed. -/
theorem circumcentroidal_update_rank_le_three
    (J : Matrix (Fin 6) (Fin 6) ℝ)
    (U : Matrix (Fin 6) (Fin 3) ℝ)
    (V : Matrix (Fin 3) (Fin 6) ℝ) :
    (J - circumcentroidalJacobian J U V).rank ≤ 3 := by
  simpa [circumcentroidalJacobian] using correctedJacobian_update_rank_le J U V

end Ctrllib

#print axioms Ctrllib.correctedJacobian_update_rank_le
#print axioms Ctrllib.circumcentroidal_update_rank_le_three
