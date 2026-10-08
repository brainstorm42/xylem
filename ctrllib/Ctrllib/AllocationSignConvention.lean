/-
Contact-wrench sign reversal for weighted equality allocation.

The decision coordinates are split as `q ⊕ u`, where `q` contains contact
wrench coordinates and `u` contains effort coordinates.  The involution
`signDiagonal q u` negates the contact block and fixes the effort block.  The
generic transport theorem below applies the corresponding involutions to the
decision and output spaces.  Its proof uses the existing equality-constrained
weighted quadratic minimizer and does not assume a candidate solution as a
premise.

This is an algebraic sign-convention result.  It does not establish the
controller/source correspondence, contact feasibility, actuator limits, or
physical validity of a particular rover model.
-/
import Ctrllib.EqualityConstrainedQuadratic
import Mathlib.Data.Matrix.Block

open Matrix

namespace Ctrllib

section SignDiagonal

variable {q u : Type*} [Fintype q] [Fintype u] [DecidableEq q] [DecidableEq u]

/-- The block sign involution `diag(-I_q, I_u)` on `q ⊕ u`. -/
def signDiagonal (q u : Type*) [DecidableEq q] [DecidableEq u] :
    Matrix (q ⊕ u) (q ⊕ u) ℝ :=
  Matrix.diagonal (Sum.elim (fun _ : q ↦ (-1 : ℝ)) (fun _ : u ↦ (1 : ℝ)))

omit [Fintype q] [Fintype u] in
/-- The contact/effort sign involution is symmetric. -/
theorem signDiagonal_transpose : (signDiagonal q u)ᵀ = signDiagonal q u := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [signDiagonal, Matrix.transpose_apply, Matrix.diagonal_apply, eq_comm]

/-- Applying the contact/effort sign involution twice is the identity. -/
theorem signDiagonal_mul_self : signDiagonal q u * signDiagonal q u = 1 := by
  change Matrix.diagonal _ * Matrix.diagonal _ = 1
  rw [Matrix.diagonal_mul_diagonal]
  funext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.diagonal_apply, Matrix.one_apply, eq_comm]

/-- A block-diagonal weight is unchanged by contact sign reversal. -/
theorem signDiagonal_conj_invariant_of_isTwoBlockDiagonal
    {W : Matrix (q ⊕ u) (q ⊕ u) ℝ}
    (hW : Matrix.IsTwoBlockDiagonal W) :
    (signDiagonal q u)ᵀ * W * signDiagonal q u = W := by
  have hW12 : ∀ i : q, ∀ j : u, W (Sum.inl i) (Sum.inr j) = 0 := by
    intro i j
    have h := congrFun (congrFun hW.1 i) j
    simpa [Matrix.toBlocks₁₂] using h
  have hW21 : ∀ i : u, ∀ j : q, W (Sum.inr i) (Sum.inl j) = 0 := by
    intro i j
    have h := congrFun (congrFun hW.2 i) j
    simpa [Matrix.toBlocks₂₁] using h
  rw [signDiagonal_transpose]
  funext i j
  rcases i with i | i <;> rcases j with j | j
  · simp only [signDiagonal, Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp
  · simp only [signDiagonal, Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp [hW12 i j]
  · simp only [signDiagonal, Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp [hW21 i j]
  · simp only [signDiagonal, Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp

/-- The contact coordinates of a sign-transformed vector are negated. -/
theorem signDiagonal_mulVec_inl (x : q ⊕ u → ℝ) (i : q) :
    (signDiagonal q u *ᵥ x) (Sum.inl i) = -x (Sum.inl i) := by
  rw [show signDiagonal q u = Matrix.diagonal
      (Sum.elim (fun _ : q ↦ (-1 : ℝ)) (fun _ : u ↦ (1 : ℝ))) from rfl]
  simp [Matrix.mulVec_diagonal]

/-- The effort coordinates of a sign-transformed vector are unchanged. -/
theorem signDiagonal_mulVec_inr (x : q ⊕ u → ℝ) (i : u) :
    (signDiagonal q u *ᵥ x) (Sum.inr i) = x (Sum.inr i) := by
  rw [show signDiagonal q u = Matrix.diagonal
      (Sum.elim (fun _ : q ↦ (-1 : ℝ)) (fun _ : u ↦ (1 : ℝ))) from rfl]
  simp [Matrix.mulVec_diagonal]

end SignDiagonal

section Transport

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- A two-sided involutive sign change preserves full row rank. -/
theorem sign_transform_surjective {A : Matrix m n ℝ} {T : Matrix n n ℝ}
    {R : Matrix m m ℝ} (hA : Function.Surjective A.mulVec)
    (hT : T * T = 1) (hR : R * R = 1) :
    Function.Surjective (R * A * T).mulVec := by
  intro z
  obtain ⟨x, hx⟩ := hA (R *ᵥ z)
  refine ⟨T *ᵥ x, ?_⟩
  calc
    (R * A * T) *ᵥ (T *ᵥ x) = ((R * A * T) * T) *ᵥ x := by
      rw [Matrix.mulVec_mulVec]
    _ = (R * A) *ᵥ x := by simp [Matrix.mul_assoc, hT]
    _ = R *ᵥ (A *ᵥ x) := by rw [Matrix.mulVec_mulVec]
    _ = R *ᵥ (R *ᵥ z) := by rw [hx]
    _ = z := by
      simp [hR]

/-- A feasible point maps to a feasible point under the sign convention. -/
theorem sign_transform_feasible {A : Matrix m n ℝ} {T : Matrix n n ℝ}
    {R : Matrix m m ℝ} {b : m → ℝ} {x : n → ℝ}
    (hT : T * T = 1) (_hR : R * R = 1) (hx : A *ᵥ x = b) :
    (R * A * T) *ᵥ (T *ᵥ x) = R *ᵥ b := by
  calc
    (R * A * T) *ᵥ (T *ᵥ x) = ((R * A * T) * T) *ᵥ x := by
      rw [Matrix.mulVec_mulVec]
    _ = (R * A) *ᵥ x := by simp [Matrix.mul_assoc, hT]
    _ = R *ᵥ (A *ᵥ x) := by rw [Matrix.mulVec_mulVec]
    _ = R *ᵥ b := by rw [hx]

omit [DecidableEq n] in
/-- The weighted quadratic cost is invariant under a `W`-isometric involution. -/
theorem weightedQuadratic_sign_invariant {W : Matrix n n ℝ}
    {T : Matrix n n ℝ} (hW : W.PosDef)
    (hWT : Tᵀ * W * T = W) (x : n → ℝ) :
    weightedQuadratic W (T *ᵥ x) = weightedQuadratic W x := by
  have hWsymm : Wᵀ = W := posDef_transpose_eq hW
  have hinner : (T *ᵥ x) ⬝ᵥ (W *ᵥ (T *ᵥ x)) =
      x ⬝ᵥ ((Tᵀ * W * T) *ᵥ x) := by
    calc
      (T *ᵥ x) ⬝ᵥ (W *ᵥ (T *ᵥ x)) =
          ((T *ᵥ x) ᵥ* W) ⬝ᵥ (T *ᵥ x) := by rw [dotProduct_mulVec]
      _ = (Wᵀ *ᵥ (T *ᵥ x)) ⬝ᵥ (T *ᵥ x) := by rw [← mulVec_transpose]
      _ = (W *ᵥ (T *ᵥ x)) ⬝ᵥ (T *ᵥ x) := by rw [hWsymm]
      _ = ((W * T) *ᵥ x) ⬝ᵥ (T *ᵥ x) := by rw [Matrix.mulVec_mulVec]
      _ = (T *ᵥ x) ⬝ᵥ ((W * T) *ᵥ x) := dotProduct_comm _ _
      _ = ((Tᵀ * (W * T)) *ᵥ x) ⬝ᵥ x := by
        rw [dotProduct_mulVec, ← mulVec_transpose, transpose_mul, hWsymm]
        rw [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = x ⬝ᵥ ((Tᵀ * W * T) *ᵥ x) := by
        rw [dotProduct_comm]
        congr 1
        rw [Matrix.mul_assoc]
  unfold weightedQuadratic
  rw [hinner, hWT]

end Transport

section TransportMinimizer

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/--
The unique SPD-weighted equality minimizer transports under an involutive
contact/effort sign change.  Set `T = diag(-I_q,I_u)` for decision variables
and `R` to the corresponding output sign involution.  The transformed system
is `A' = R A T`, `b' = R b`; its minimizer is exactly `T x⋆`.
-/
theorem weighted_quadratic_sign_transport {A : Matrix m n ℝ} {W : Matrix n n ℝ}
    {T : Matrix n n ℝ} {R : Matrix m m ℝ} (hW : W.PosDef)
    (hA : Function.Surjective A.mulVec) (hT : T * T = 1) (hR : R * R = 1)
    (hWT : Tᵀ * W * T = W) (b : m → ℝ) :
    weightedRightInverse W (R * A * T) *ᵥ (R *ᵥ b) =
      T *ᵥ (weightedRightInverse W A *ᵥ b) := by
  let A' : Matrix m n ℝ := R * A * T
  let b' : m → ℝ := R *ᵥ b
  let xstar : n → ℝ := weightedRightInverse W A *ᵥ b
  let ystar : n → ℝ := weightedRightInverse W A' *ᵥ b'
  have hA' : Function.Surjective A'.mulVec := by
    exact sign_transform_surjective hA hT hR
  have hxstar : A *ᵥ xstar = b := by
    exact weighted_quadratic_feasible hW hA b
  have hystar : A' *ᵥ ystar = b' := by
    exact weighted_quadratic_feasible hW hA' b'
  have hystar' : (R * A * T) *ᵥ ystar = R *ᵥ b := by
    simpa [A', b'] using hystar
  have hforward : A' *ᵥ (T *ᵥ xstar) = b' := by
    exact sign_transform_feasible hT hR hxstar
  have hAT : A * T = R * (R * A * T) := by
    calc
      A * T = (1 : Matrix m m ℝ) * (A * T) := by rw [Matrix.one_mul]
      _ = (R * R) * (A * T) := by rw [hR]
      _ = R * (R * (A * T)) := by rw [Matrix.mul_assoc]
      _ = R * (R * A * T) := by simp only [Matrix.mul_assoc]
  have hback : A *ᵥ (T *ᵥ ystar) = b := by
    calc
      A *ᵥ (T *ᵥ ystar) = (A * T) *ᵥ ystar := by rw [Matrix.mulVec_mulVec]
      _ = (R * (R * A * T)) *ᵥ ystar := by rw [hAT]
      _ = R *ᵥ ((R * A * T) *ᵥ ystar) := by
        exact (Matrix.mulVec_mulVec ystar R (R * A * T)).symm
      _ = R *ᵥ (R *ᵥ b) := by rw [hystar']
      _ = (R * R) *ᵥ b := by exact Matrix.mulVec_mulVec b R R
      _ = b := by rw [hR]; exact Matrix.one_mulVec b
  have hy_le : weightedQuadratic W ystar ≤ weightedQuadratic W (T *ᵥ xstar) := by
    exact weighted_quadratic_minimizer_le hW hA' b' hforward
  have hx_le : weightedQuadratic W xstar ≤ weightedQuadratic W (T *ᵥ ystar) := by
    exact weighted_quadratic_minimizer_le hW hA b hback
  have hcandidate_le : weightedQuadratic W (T *ᵥ xstar) ≤ weightedQuadratic W ystar := by
    rw [weightedQuadratic_sign_invariant hW hWT ystar] at hx_le
    rw [weightedQuadratic_sign_invariant hW hWT xstar]
    exact hx_le
  have hcost : weightedQuadratic W (T *ᵥ xstar) = weightedQuadratic W ystar :=
    le_antisymm hcandidate_le hy_le
  have heq : T *ᵥ xstar = ystar :=
    (weighted_quadratic_minimizer_eq_iff hW hA' b' hforward).mp hcost
  exact heq.symm

end TransportMinimizer

end Ctrllib

#print axioms Ctrllib.signDiagonal_mul_self
#print axioms Ctrllib.signDiagonal_conj_invariant_of_isTwoBlockDiagonal
#print axioms Ctrllib.sign_transform_surjective
#print axioms Ctrllib.weightedQuadratic_sign_invariant
#print axioms Ctrllib.weighted_quadratic_sign_transport
