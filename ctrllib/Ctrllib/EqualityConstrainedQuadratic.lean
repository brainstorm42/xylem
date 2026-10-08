/-
Equality-constrained weighted quadratic allocation.

For a full-row-rank rectangular map `A : Matrix m n ℝ` and an SPD weight
`W : Matrix n n ℝ`, the feasible command selected by

  1/2 xᵀ W x  subject to  A x = b

is the weighted right-inverse command

  x⋆ = W⁻¹ Aᵀ (A W⁻¹ Aᵀ)⁻¹ b.

The proof is finite-dimensional and keeps the exact SPD and surjectivity
premises explicit.  It establishes feasibility, the quadratic comparison,
and strictness away from `x⋆`; it does not add an actuator-limit or physical
frame theorem to the generic weighted-allocation source interface.
-/
import Ctrllib.WeightedRightInverse

open Matrix

namespace Ctrllib

section

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The weighted quadratic cost, with the conventional factor `1/2`. -/
noncomputable def weightedQuadratic (W : Matrix n n ℝ) (x : n → ℝ) : ℝ :=
  ((1 : ℝ) / 2) * (x ⬝ᵥ (W *ᵥ x))

omit [Fintype n] [DecidableEq n] in
/-- Real SPD matrices are symmetric in the transpose notation used by the
quadratic-form calculations. -/
theorem posDef_transpose_eq {W : Matrix n n ℝ} (hW : W.PosDef) : Wᵀ = W := by
  exact hW.isHermitian.eq

/-- Applying `W` to the weighted right-inverse command cancels `W⁻¹` and
leaves the transpose constraint map.  This is the stationarity identity. -/
theorem weighted_right_inverse_stationarity {A : Matrix m n ℝ}
    {W : Matrix n n ℝ} (hW : W.PosDef) (b : m → ℝ) :
    W *ᵥ (weightedRightInverse W A *ᵥ b) =
      Aᵀ *ᵥ ((A * W⁻¹ * Aᵀ)⁻¹ *ᵥ b) := by
  have hWdet : IsUnit W.det := (isUnit_iff_isUnit_det _).mp hW.isUnit
  calc
    W *ᵥ (weightedRightInverse W A *ᵥ b) =
        (W * weightedRightInverse W A) *ᵥ b := by rw [mulVec_mulVec]
    _ = (Aᵀ * (A * W⁻¹ * Aᵀ)⁻¹) *ᵥ b := by
      rw [weightedRightInverse]
      congr 1
      calc
        W * (W⁻¹ * Aᵀ * (A * W⁻¹ * Aᵀ)⁻¹) =
            (W * W⁻¹) * Aᵀ * (A * W⁻¹ * Aᵀ)⁻¹ := by
          rw [← Matrix.mul_assoc W (W⁻¹ * Aᵀ) (A * W⁻¹ * Aᵀ)⁻¹,
            ← Matrix.mul_assoc W W⁻¹ Aᵀ]
        _ = Aᵀ * (A * W⁻¹ * Aᵀ)⁻¹ := by
          rw [W.mul_nonsing_inv hWdet, Matrix.one_mul]
    _ = Aᵀ *ᵥ ((A * W⁻¹ * Aᵀ)⁻¹ *ᵥ b) := by rw [mulVec_mulVec]

/-- The weighted right-inverse command is orthogonal, in the `W` inner
product, to every feasible homogeneous displacement. -/
theorem weighted_right_inverse_cross_term_zero {A : Matrix m n ℝ}
    {W : Matrix n n ℝ} (hW : W.PosDef)
    (b : m → ℝ)
    {d : n → ℝ} (hd : A *ᵥ d = 0) :
    (weightedRightInverse W A *ᵥ b) ⬝ᵥ (W *ᵥ d) = 0 := by
  have hWsymm : Wᵀ = W := posDef_transpose_eq hW
  calc
    (weightedRightInverse W A *ᵥ b) ⬝ᵥ (W *ᵥ d) =
        (W *ᵥ (weightedRightInverse W A *ᵥ b)) ⬝ᵥ d := by
      rw [dotProduct_mulVec, ← mulVec_transpose, hWsymm]
    _ = (Aᵀ *ᵥ ((A * W⁻¹ * Aᵀ)⁻¹ *ᵥ b)) ⬝ᵥ d := by
      rw [weighted_right_inverse_stationarity hW b]
    _ = d ⬝ᵥ (Aᵀ *ᵥ ((A * W⁻¹ * Aᵀ)⁻¹ *ᵥ b)) := dotProduct_comm _ _
    _ = (d ᵥ* Aᵀ) ⬝ᵥ ((A * W⁻¹ * Aᵀ)⁻¹ *ᵥ b) := by
      rw [dotProduct_mulVec]
    _ = (A *ᵥ d) ⬝ᵥ ((A * W⁻¹ * Aᵀ)⁻¹ *ᵥ b) := by
      rw [← mulVec_transpose, transpose_transpose]
    _ = 0 := by rw [hd, zero_dotProduct]

omit [DecidableEq n] in
/-- Additive expansion of the weighted quadratic form.  Symmetry of `W`
identifies the two cross terms, leaving exactly one bilinear cross term. -/
theorem weightedQuadratic_add {W : Matrix n n ℝ} (hWsymm : Wᵀ = W)
    (u v : n → ℝ) :
    weightedQuadratic W (u + v) =
      weightedQuadratic W u + weightedQuadratic W v + u ⬝ᵥ (W *ᵥ v) := by
  have hcross : v ⬝ᵥ (W *ᵥ u) = u ⬝ᵥ (W *ᵥ v) := by
    calc
      v ⬝ᵥ (W *ᵥ u) = (v ᵥ* W) ⬝ᵥ u := by rw [dotProduct_mulVec]
      _ = (Wᵀ *ᵥ v) ⬝ᵥ u := by rw [← mulVec_transpose]
      _ = (W *ᵥ v) ⬝ᵥ u := by rw [hWsymm]
      _ = u ⬝ᵥ (W *ᵥ v) := dotProduct_comm _ _
  simp only [weightedQuadratic, mulVec_add, add_dotProduct, dotProduct_add]
  rw [hcross]
  ring

/-- The weighted right-inverse command is feasible for the equality target. -/
theorem weighted_quadratic_feasible {A : Matrix m n ℝ} {W : Matrix n n ℝ}
    (hW : W.PosDef) (hA : Function.Surjective A.mulVec) (b : m → ℝ) :
    A *ᵥ (weightedRightInverse W A *ᵥ b) = b :=
  weighted_right_inverse_feasible hW hA b

/-- The weighted right-inverse command minimizes the quadratic cost on the
affine equality set. -/
theorem weighted_quadratic_minimizer_le {A : Matrix m n ℝ}
    {W : Matrix n n ℝ} (hW : W.PosDef) (hA : Function.Surjective A.mulVec)
    (b : m → ℝ) {x : n → ℝ} (hx : A *ᵥ x = b) :
    weightedQuadratic W (weightedRightInverse W A *ᵥ b) ≤
      weightedQuadratic W x := by
  let xstar : n → ℝ := weightedRightInverse W A *ᵥ b
  let d : n → ℝ := x - xstar
  have hxstar : A *ᵥ xstar = b := by
    exact weighted_quadratic_feasible hW hA b
  have hd : A *ᵥ d = 0 := by
    dsimp [d]
    rw [mulVec_sub, hx, hxstar, sub_self]
  have hcross : xstar ⬝ᵥ (W *ᵥ d) = 0 :=
    weighted_right_inverse_cross_term_zero hW b hd
  have hdecomp : x = xstar + d := by
    dsimp [d]
    abel
  have hqd : 0 ≤ weightedQuadratic W d := by
    change 0 ≤ ((1 : ℝ) / 2) * (d ⬝ᵥ (W *ᵥ d))
    exact mul_nonneg (by norm_num) (hW.posSemidef.dotProduct_mulVec_nonneg d)
  rw [hdecomp, weightedQuadratic_add (posDef_transpose_eq hW), hcross]
  have hgoal : weightedQuadratic W xstar ≤
      weightedQuadratic W xstar + weightedQuadratic W d := by
    linarith
  simpa [xstar, add_assoc] using hgoal

/-- Strictness of the comparison: a feasible point different from the
weighted right-inverse command has strictly larger cost. -/
theorem weighted_quadratic_minimizer_lt {A : Matrix m n ℝ}
    {W : Matrix n n ℝ} (hW : W.PosDef) (hA : Function.Surjective A.mulVec)
    (b : m → ℝ) {x : n → ℝ} (hx : A *ᵥ x = b)
    (hne : x ≠ weightedRightInverse W A *ᵥ b) :
    weightedQuadratic W (weightedRightInverse W A *ᵥ b) <
      weightedQuadratic W x := by
  let xstar : n → ℝ := weightedRightInverse W A *ᵥ b
  let d : n → ℝ := x - xstar
  have hxstar : A *ᵥ xstar = b := by
    exact weighted_quadratic_feasible hW hA b
  have hd : A *ᵥ d = 0 := by
    dsimp [d]
    rw [mulVec_sub, hx, hxstar, sub_self]
  have hcross : xstar ⬝ᵥ (W *ᵥ d) = 0 :=
    weighted_right_inverse_cross_term_zero hW b hd
  have hdecomp : x = xstar + d := by
    dsimp [d]
    abel
  have hdne : d ≠ 0 := by
    intro hd0
    apply hne
    dsimp [d] at hd0
    exact sub_eq_zero.mp hd0
  have hqpos : 0 < weightedQuadratic W d := by
    change 0 < ((1 : ℝ) / 2) * (d ⬝ᵥ (W *ᵥ d))
    exact mul_pos (by norm_num) (hW.dotProduct_mulVec_pos hdne)
  rw [hdecomp, weightedQuadratic_add (posDef_transpose_eq hW), hcross]
  have hgoal : weightedQuadratic W xstar <
      weightedQuadratic W xstar + weightedQuadratic W d := by
    linarith
  simpa [xstar, add_assoc] using hgoal

/-- Equality characterizes the unique feasible minimizer. -/
theorem weighted_quadratic_minimizer_eq_iff {A : Matrix m n ℝ}
    {W : Matrix n n ℝ} (hW : W.PosDef) (hA : Function.Surjective A.mulVec)
    (b : m → ℝ) {x : n → ℝ} (hx : A *ᵥ x = b) :
    weightedQuadratic W x = weightedQuadratic W (weightedRightInverse W A *ᵥ b) ↔
      x = weightedRightInverse W A *ᵥ b := by
  constructor
  · intro heq
    by_contra hne
    have hlt := weighted_quadratic_minimizer_lt hW hA b hx hne
    linarith
  · intro h
    rw [h]

end

end Ctrllib

#print axioms Ctrllib.weightedQuadratic
#print axioms Ctrllib.posDef_transpose_eq
#print axioms Ctrllib.weighted_right_inverse_stationarity
#print axioms Ctrllib.weighted_right_inverse_cross_term_zero
#print axioms Ctrllib.weightedQuadratic_add
#print axioms Ctrllib.weighted_quadratic_feasible
#print axioms Ctrllib.weighted_quadratic_minimizer_le
#print axioms Ctrllib.weighted_quadratic_minimizer_lt
#print axioms Ctrllib.weighted_quadratic_minimizer_eq_iff
