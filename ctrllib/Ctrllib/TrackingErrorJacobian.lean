/-
Tracking error-rate Jacobian with the body-frame transport block (research
the corresponding algebra note) — the block-triangular structure of the IMPLEMENTED
end-effector error-rate Jacobian, and why the stiffness-residual finish
(StiffnessResidual.lean) survives it unchanged.

THE STEP (the source model note eq 4.1a; `the implemented error-rate Jacobian`, `J_12 = cross(e_p)`).
The live 6-DOF controller expresses the end-effector position error in the
rotating end-effector frame, so its error-rate Jacobian carries a transport
block that Giordano 2019 eq 24 prints as zero:

    J_x̃_e = [ E     [p]^∧              ]        (code, eq 4.1a)
            [ 0   −η E + [ε]^∧          ]

    J_x̃_e = [ E     0                  ]        (printed, Giordano eq 24)
            [ 0   −η E + [ε]^∧          ]

Both are block upper-triangular with the same diagonal blocks. The stacked
error-rate Jacobian is J_x̃ = blkdiag(J_x̃_b, J_x̃_e).

WHAT IS PROVEN (over any commutative ring unless stated):
  `det_trackingErrorJacobian`      — det [1 P; 0 Q] = det Q for EVERY transport
                                     block P.
  `isUnit_trackingErrorJacobian_iff` — [1 P; 0 Q] is nonsingular iff Q is.
  `isUnit_trackingErrorJacobian_transport_free` — two such Jacobians differing
                                     only in P are nonsingular together: the
                                     printed and the implemented J_x̃_e share
                                     their singular set exactly.
  `isUnit_trackingJacobian_iff`    — the stacked J_x̃ = blkdiag(Jb, [1 P; 0 Q]) is
                                     nonsingular iff Jb and Q are.
  `tracking_stiffness_residual_injective` (ℝ) — with K̆ ≻ 0 and Q nonsingular,
                                     the eq-31/34b residual J_x̃_eᵀ K̆ x̃ = 0 forces
                                     x̃ = 0 for the IMPLEMENTED Jacobian, by the
                                     sealed `stiffness_residual_injective`.
  `tracking_stiffness_residual_injective_stacked` (ℝ) — the same for the stacked
                                     J_x̃ with Jb nonsingular.

SYMPY-PINNED (the corresponding project check (not bundled).py):
  (A) det J_x̃_e = det Q for generic P and for P = [p]^∧;
  (B),(C) det J_x̃ = det J_x̃_b · det Q, no p-dependence;
  (D) det(−ηE + [ε]^∧) = −η(η² + |ε|²) = −η on the unit quaternion, so the
      singular set is η = 0 for both the printed and the implemented Jacobian;
  (E) FALSIFICATION of "the transport block is harmless everywhere": the residual
      VECTOR J_x̃_eᵀ K̆ x̃ does depend on P; only nonsingularity, and hence the
      x̃ = 0 conclusion, is P-free. Any argument that manipulates the residual
      vector (CruiseLag.lean) must carry P.

INTERFACE BOUNDARY (honest). This module is finite-dimensional algebra about
the Jacobian's block shape. It does not derive eq 4.1a from kinematics (that
derivation is in the source model note §4.1 and its SymPy check), and it does not
assert which Jacobian the source paper intended. Nonsingularity of Q (η ≠ 0)
remains the operating-region premise, as in StiffnessResidual.lean pin (D).
-/
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Ctrllib.StiffnessResidual

open Matrix

namespace Ctrllib

section Ring

variable {R : Type*} [CommRing R]
variable {l m n : Type*} [Fintype l] [Fintype m] [Fintype n]
variable [DecidableEq l] [DecidableEq m] [DecidableEq n]

/-- **Transport block does not enter the determinant** (eq 4.1a vs Giordano eq 24).
For the block upper-triangular error-rate Jacobian `[1 P; 0 Q]`,
`det = det Q`, whatever the transport block `P` is. -/
theorem det_trackingErrorJacobian (P : Matrix m n R) (Q : Matrix n n R) :
    (fromBlocks (1 : Matrix m m R) P 0 Q).det = Q.det := by
  rw [det_fromBlocks_zero₂₁, det_one, one_mul]

/-- **Nonsingularity is decided by the rotational block alone.** -/
theorem isUnit_trackingErrorJacobian_iff (P : Matrix m n R) (Q : Matrix n n R) :
    IsUnit (fromBlocks (1 : Matrix m m R) P 0 Q) ↔ IsUnit Q := by
  rw [isUnit_fromBlocks_zero₂₁]
  exact ⟨fun h => h.2, fun h => ⟨isUnit_one, h⟩⟩

/-- **Printed and implemented Jacobians share their singular set.** Two error-rate
Jacobians that differ only in the transport block are nonsingular together; in
particular the code's `[1 [p]^∧; 0 Q]` and the paper's `[1 0; 0 Q]`. -/
theorem isUnit_trackingErrorJacobian_transport_free
    (P P' : Matrix m n R) (Q : Matrix n n R) :
    IsUnit (fromBlocks (1 : Matrix m m R) P 0 Q) ↔
      IsUnit (fromBlocks (1 : Matrix m m R) P' 0 Q) := by
  rw [isUnit_trackingErrorJacobian_iff, isUnit_trackingErrorJacobian_iff]

/-- **Stacked error-rate Jacobian** `J_x̃ = blkdiag(J_x̃_b, J_x̃_e)` with the
implemented `J_x̃_e = [1 P; 0 Q]`: nonsingular iff `J_x̃_b` and `Q` are. -/
theorem isUnit_trackingJacobian_iff (Jb : Matrix l l R) (P : Matrix m n R)
    (Q : Matrix n n R) :
    IsUnit (fromBlocks Jb 0 0 (fromBlocks (1 : Matrix m m R) P 0 Q)) ↔
      IsUnit Jb ∧ IsUnit Q := by
  rw [isUnit_fromBlocks_zero₂₁, isUnit_trackingErrorJacobian_iff]

end Ring

section Real

variable {l m n : Type*} [Fintype l] [Fintype m] [Fintype n]
variable [DecidableEq l] [DecidableEq m] [DecidableEq n]

/-- **Stiffness-residual finish for the implemented Jacobian** (eq 31/34b with
eq 4.1a). With `K̆ ≻ 0` and the rotational block `Q` nonsingular, the residual
`J_x̃_eᵀ K̆ x̃ = 0` forces `x̃ = 0` — the transport block `P` is arbitrary. This is
`stiffness_residual_injective` applied to `J = [1 P; 0 Q]`. -/
theorem tracking_stiffness_residual_injective
    {K : Matrix (m ⊕ n) (m ⊕ n) ℝ} (hK : K.PosDef)
    {P : Matrix m n ℝ} {Q : Matrix n n ℝ} (hQ : IsUnit Q)
    {x : m ⊕ n → ℝ}
    (hres : ((fromBlocks (1 : Matrix m m ℝ) P 0 Q)ᵀ * K) *ᵥ x = 0) : x = 0 :=
  stiffness_residual_injective hK
    (mulVec_injective_iff_isUnit.mpr ((isUnit_trackingErrorJacobian_iff P Q).mpr hQ))
    hres

/-- The same finish for the stacked `J_x̃ = blkdiag(J_x̃_b, [1 P; 0 Q])`, with the
base block `J_x̃_b` nonsingular as well. -/
theorem tracking_stiffness_residual_injective_stacked
    {K : Matrix (l ⊕ (m ⊕ n)) (l ⊕ (m ⊕ n)) ℝ} (hK : K.PosDef)
    {Jb : Matrix l l ℝ} (hJb : IsUnit Jb)
    {P : Matrix m n ℝ} {Q : Matrix n n ℝ} (hQ : IsUnit Q)
    {x : l ⊕ (m ⊕ n) → ℝ}
    (hres : ((fromBlocks Jb 0 0 (fromBlocks (1 : Matrix m m ℝ) P 0 Q))ᵀ * K) *ᵥ x = 0) :
    x = 0 :=
  stiffness_residual_injective hK
    (mulVec_injective_iff_isUnit.mpr ((isUnit_trackingJacobian_iff Jb P Q).mpr ⟨hJb, hQ⟩))
    hres

end Real

end Ctrllib

#print axioms Ctrllib.det_trackingErrorJacobian
#print axioms Ctrllib.isUnit_trackingErrorJacobian_iff
#print axioms Ctrllib.isUnit_trackingErrorJacobian_transport_free
#print axioms Ctrllib.isUnit_trackingJacobian_iff
#print axioms Ctrllib.tracking_stiffness_residual_injective
#print axioms Ctrllib.tracking_stiffness_residual_injective_stacked
