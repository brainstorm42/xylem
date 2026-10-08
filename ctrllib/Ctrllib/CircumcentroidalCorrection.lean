/-
Wave-1 workbench for the six-joint circumcentroidal Jacobian correction

  J_oplus = J_nu_e - R_eb0 * Jv_bar.

The generic core treats the correction as `J - U * V`, where `U * V` has
rank at most the inner dimension.  The FFSM specialization has dimensions
6x6 - (6x3)(3x6).  This file proves algebraic identities only; it does not
identify the supplied matrices with a robot model or a Pinocchio frame.
-/
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic.Abel

open Matrix

namespace Ctrllib

section GenericCorrection

variable {R : Type*} [CommRing R]
variable {m n r : Type*}
variable [Fintype m] [Fintype n] [Fintype r]
variable [DecidableEq m] [DecidableEq n] [DecidableEq r]

/-- A dimension-generic low-rank correction `J - U * V`. -/
def correctedJacobian (J : Matrix m n R) (U : Matrix m r R) (V : Matrix r n R) :
    Matrix m n R :=
  J - U * V

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [DecidableEq r] in
/-- Transposition reverses the two correction factors. -/
theorem correctedJacobian_transpose (J : Matrix m n R) (U : Matrix m r R)
    (V : Matrix r n R) :
    (correctedJacobian J U V)ᵀ = Jᵀ - Vᵀ * Uᵀ := by
  simp [correctedJacobian, Matrix.transpose_sub, Matrix.transpose_mul]

omit [Fintype m] [DecidableEq m] [DecidableEq n] [DecidableEq r] in
/-- Applying the corrected Jacobian first applies `V`, then `U`, and subtracts
the resulting task-space correction from the bare Jacobian action. -/
theorem correctedJacobian_mulVec (J : Matrix m n R) (U : Matrix m r R)
    (V : Matrix r n R) (x : n → R) :
    correctedJacobian J U V *ᵥ x = J *ᵥ x - U *ᵥ (V *ᵥ x) := by
  rw [correctedJacobian, Matrix.sub_mulVec, Matrix.mulVec_mulVec]

omit [Fintype m] [DecidableEq m] [DecidableEq n] [DecidableEq r] in
/-- The correction is invisible on the kernel of its right factor. -/
theorem correctedJacobian_eq_on_correction_kernel (J : Matrix m n R)
    (U : Matrix m r R) (V : Matrix r n R) (x : n → R)
    (hV : V *ᵥ x = 0) :
    correctedJacobian J U V *ᵥ x = J *ᵥ x := by
  rw [correctedJacobian_mulVec, hV, Matrix.mulVec_zero, sub_zero]

omit [Fintype m] [DecidableEq m] [DecidableEq n] [DecidableEq r] in
/-- A vector killed by both the bare Jacobian and the correction's right
factor remains in the kernel after the update. -/
theorem correctedJacobian_kernel_of_common_kernel (J : Matrix m n R)
    (U : Matrix m r R) (V : Matrix r n R) (x : n → R)
    (hJ : J *ᵥ x = 0) (hV : V *ᵥ x = 0) :
    correctedJacobian J U V *ᵥ x = 0 := by
  rw [correctedJacobian_eq_on_correction_kernel J U V x hV, hJ]

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [DecidableEq r] in
/-- The update is unchanged by the simultaneous signed-basis replacement
`(U,V) -> (-U,-V)`. -/
theorem correctedJacobian_neg_neg (J : Matrix m n R) (U : Matrix m r R)
    (V : Matrix r n R) :
    correctedJacobian J (-U) (-V) = correctedJacobian J U V := by
  simp [correctedJacobian]

omit [Fintype n] [DecidableEq m] [DecidableEq n] [DecidableEq r] in
/-- Exact Gram expansion for a low-rank corrected Jacobian.

For the FFSM correction, substitute `U = R_eb0` and `V = Jv_bar`. -/
theorem correctedJacobian_gram (J : Matrix m n R) (U : Matrix m r R)
    (V : Matrix r n R) :
    (correctedJacobian J U V)ᵀ * correctedJacobian J U V =
      Jᵀ * J - Jᵀ * U * V - Vᵀ * Uᵀ * J + Vᵀ * Uᵀ * U * V := by
  simp only [correctedJacobian, Matrix.transpose_sub, Matrix.transpose_mul]
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
  simp only [Matrix.mul_assoc]
  abel

/-- A global block determinant identity for the correction.  It requires no
invertibility premise: the determinant of the augmented block matrix equals
the determinant of its Schur complement `J - U * V`. -/
theorem det_fromBlocks_eq_det_correctedJacobian (J : Matrix n n R)
    (U : Matrix n r R) (V : Matrix r n R) :
    (Matrix.fromBlocks J U V 1).det = (correctedJacobian J U V).det := by
  change (Matrix.fromBlocks J U V 1).det = (J - U * V).det
  exact Matrix.det_fromBlocks_one₂₂ J U V

/-- Determinant update formula on the nonsingular region.  The smaller
determinant has the correction dimension `r`; in the FFSM instance it is 3x3. -/
theorem det_correctedJacobian (J : Matrix n n R) (U : Matrix n r R)
    (V : Matrix r n R) (hJ : IsUnit J.det) :
    (correctedJacobian J U V).det =
      J.det * (1 - V * J⁻¹ * U).det := by
  simpa [correctedJacobian, sub_eq_add_neg, Matrix.neg_mul, Matrix.mul_neg,
    Matrix.mul_assoc] using Matrix.det_add_mul (-U) V hJ

end GenericCorrection

section EuclideanGainPerturbation

open scoped Matrix.Norms.L2Operator

variable {𝕜 : Type*} [RCLike 𝕜]
variable {m n r : Type*}
variable [Fintype m] [Fintype n] [Fintype r]
variable [DecidableEq m] [DecidableEq n] [DecidableEq r]

omit [Fintype m] [DecidableEq m] [DecidableEq r] in
/-- Applying the corrected matrix as a Euclidean linear map subtracts the
Euclidean action of the correction matrix. -/
theorem correctedJacobian_toEuclideanLin_apply
    (J : Matrix m n 𝕜) (U : Matrix m r 𝕜) (V : Matrix r n 𝕜)
    (x : EuclideanSpace 𝕜 n) :
    Matrix.toEuclideanLin (correctedJacobian J U V) x =
      Matrix.toEuclideanLin J x - Matrix.toEuclideanLin (U * V) x := by
  simp [correctedJacobian]

omit [DecidableEq m] [DecidableEq r] in
/-- Pointwise lower perturbation bound in Euclidean vector norm and the
induced Euclidean (`L2Operator`) matrix norm. -/
theorem correctedJacobian_euclidean_norm_lower
    (J : Matrix m n 𝕜) (U : Matrix m r 𝕜) (V : Matrix r n 𝕜)
    (x : EuclideanSpace 𝕜 n) :
    ‖Matrix.toEuclideanLin J x‖ - ‖U * V‖ * ‖x‖ ≤
      ‖Matrix.toEuclideanLin (correctedJacobian J U V) x‖ := by
  rw [correctedJacobian_toEuclideanLin_apply]
  calc
    ‖Matrix.toEuclideanLin J x‖ - ‖U * V‖ * ‖x‖ ≤
        ‖Matrix.toEuclideanLin J x‖ - ‖Matrix.toEuclideanLin (U * V) x‖ := by
      exact sub_le_sub_left (Matrix.l2_opNorm_mulVec (U * V) x) _
    _ ≤ ‖Matrix.toEuclideanLin J x - Matrix.toEuclideanLin (U * V) x‖ :=
      norm_sub_norm_le _ _

omit [DecidableEq m] [DecidableEq r] in
/-- Pointwise upper perturbation bound in Euclidean vector norm and the
induced Euclidean (`L2Operator`) matrix norm. -/
theorem correctedJacobian_euclidean_norm_upper
    (J : Matrix m n 𝕜) (U : Matrix m r 𝕜) (V : Matrix r n 𝕜)
    (x : EuclideanSpace 𝕜 n) :
    ‖Matrix.toEuclideanLin (correctedJacobian J U V) x‖ ≤
      ‖Matrix.toEuclideanLin J x‖ + ‖U * V‖ * ‖x‖ := by
  rw [correctedJacobian_toEuclideanLin_apply]
  calc
    ‖Matrix.toEuclideanLin J x - Matrix.toEuclideanLin (U * V) x‖ ≤
        ‖Matrix.toEuclideanLin J x‖ + ‖Matrix.toEuclideanLin (U * V) x‖ :=
      norm_sub_le _ _
    _ ≤ ‖Matrix.toEuclideanLin J x‖ + ‖U * V‖ * ‖x‖ := by
      exact add_le_add_right (Matrix.l2_opNorm_mulVec (U * V) x) _

omit [DecidableEq m] [DecidableEq r] in
/-- The pointwise gain changes by at most the Euclidean operator norm of the
correction, scaled by the input norm. -/
theorem abs_euclidean_norm_correctedJacobian_sub_norm_le
    (J : Matrix m n 𝕜) (U : Matrix m r 𝕜) (V : Matrix r n 𝕜)
    (x : EuclideanSpace 𝕜 n) :
    |‖Matrix.toEuclideanLin (correctedJacobian J U V) x‖ -
        ‖Matrix.toEuclideanLin J x‖| ≤ ‖U * V‖ * ‖x‖ := by
  rw [correctedJacobian_toEuclideanLin_apply]
  calc
    |‖Matrix.toEuclideanLin J x - Matrix.toEuclideanLin (U * V) x‖ -
        ‖Matrix.toEuclideanLin J x‖| ≤
        ‖(Matrix.toEuclideanLin J x - Matrix.toEuclideanLin (U * V) x) -
          Matrix.toEuclideanLin J x‖ := abs_norm_sub_norm_le _ _
    _ = ‖Matrix.toEuclideanLin (U * V) x‖ := by simp
    _ ≤ ‖U * V‖ * ‖x‖ := Matrix.l2_opNorm_mulVec (U * V) x

/-- `s` is a lower bound for the gain of `A` on the Euclidean unit sphere.
This is the order-theoretic interface needed before choosing a concrete
definition of smallest singular value. -/
def IsUnitSphereGainLowerBound (A : Matrix m n 𝕜) (s : ℝ) : Prop :=
  ∀ x : EuclideanSpace 𝕜 n, ‖x‖ = 1 → s ≤ ‖Matrix.toEuclideanLin A x‖

/-- The set of output gains attained by `A` on the Euclidean unit sphere. -/
def EuclideanUnitSphereGains (A : Matrix m n 𝕜) : Set ℝ :=
  {y | ∃ x : EuclideanSpace 𝕜 n, ‖x‖ = 1 ∧
      y = ‖Matrix.toEuclideanLin A x‖}

/-- The variational smallest gain: the infimum of the output norm over the
Euclidean unit sphere.  This definition is meaningful for rectangular maps;
for a map with a nontrivial kernel it is zero. -/
noncomputable def euclideanSmallestGain (A : Matrix m n 𝕜) : ℝ :=
  sInf (EuclideanUnitSphereGains A)

omit [DecidableEq m] [DecidableEq r] in
/-- A nonempty finite-dimensional domain has a nonempty Euclidean unit sphere,
so its gain set is nonempty for every matrix. -/
theorem euclideanUnitSphereGains_nonempty [Nonempty n] (A : Matrix m n 𝕜) :
    (EuclideanUnitSphereGains A).Nonempty := by
  classical
  let i : n := Classical.arbitrary n
  refine ⟨‖Matrix.toEuclideanLin A (EuclideanSpace.single i 1)‖, ?_⟩
  refine ⟨EuclideanSpace.single i 1, ?_, rfl⟩
  simp

omit [DecidableEq m] [DecidableEq r] in
/-- Unit-sphere gains are bounded below by zero. -/
theorem euclideanUnitSphereGains_bddBelow (A : Matrix m n 𝕜) :
    BddBelow (EuclideanUnitSphereGains A) := by
  refine ⟨0, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  exact norm_nonneg _

omit [DecidableEq m] [DecidableEq r] in
/-- A real number is a unit-sphere gain lower bound exactly when it lies below
the variational smallest gain. -/
theorem isUnitSphereGainLowerBound_iff_le_euclideanSmallestGain [Nonempty n]
    (A : Matrix m n 𝕜) (s : ℝ) :
    IsUnitSphereGainLowerBound A s ↔ s ≤ euclideanSmallestGain A := by
  constructor
  · intro hs
    refine le_csInf (euclideanUnitSphereGains_nonempty A) ?_
    rintro y ⟨x, hx, rfl⟩
    exact hs x hx
  · intro hs x hx
    refine hs.trans ?_
    exact csInf_le (euclideanUnitSphereGains_bddBelow A) ⟨x, hx, rfl⟩

omit [DecidableEq m] [DecidableEq r] in
/-- The variational smallest gain is nonnegative. -/
theorem euclideanSmallestGain_nonneg [Nonempty n] (A : Matrix m n 𝕜) :
    0 ≤ euclideanSmallestGain A := by
  rw [← isUnitSphereGainLowerBound_iff_le_euclideanSmallestGain]
  intro x hx
  exact norm_nonneg _

omit [DecidableEq m] [DecidableEq r] in
/-- Every unit-sphere gain lower bound decreases by at most `‖U * V‖` under
the correction.  Instantiating `s` with the infimum unit-sphere gain yields
the lower half of the standard smallest-gain perturbation estimate. -/
theorem correctedJacobian_isUnitSphereGainLowerBound
    (J : Matrix m n 𝕜) (U : Matrix m r 𝕜) (V : Matrix r n 𝕜) (s : ℝ)
    (hJ : IsUnitSphereGainLowerBound J s) :
    IsUnitSphereGainLowerBound (correctedJacobian J U V) (s - ‖U * V‖) := by
  intro x hx
  calc
    s - ‖U * V‖ ≤ ‖Matrix.toEuclideanLin J x‖ - ‖U * V‖ :=
      sub_le_sub_right (hJ x hx) _
    _ = ‖Matrix.toEuclideanLin J x‖ - ‖U * V‖ * ‖x‖ := by rw [hx, mul_one]
    _ ≤ ‖Matrix.toEuclideanLin (correctedJacobian J U V) x‖ :=
      correctedJacobian_euclidean_norm_lower J U V x

omit [DecidableEq m] [DecidableEq r] in
/-- On a Euclidean unit vector, the absolute pointwise gain change is at most
the Euclidean operator norm `‖U * V‖`. -/
theorem abs_euclidean_unit_gain_correctedJacobian_sub_gain_le
    (J : Matrix m n 𝕜) (U : Matrix m r 𝕜) (V : Matrix r n 𝕜)
    (x : EuclideanSpace 𝕜 n) (hx : ‖x‖ = 1) :
    |‖Matrix.toEuclideanLin (correctedJacobian J U V) x‖ -
        ‖Matrix.toEuclideanLin J x‖| ≤ ‖U * V‖ := by
  simpa [hx] using abs_euclidean_norm_correctedJacobian_sub_norm_le J U V x

omit [DecidableEq m] [DecidableEq r] in
/-- Conversely, a unit-sphere gain lower bound for the corrected matrix gives
one for the bare matrix after the same `‖U * V‖` loss.  Together with
`correctedJacobian_isUnitSphereGainLowerBound`, this is the lower-bound form of
the two-sided smallest-gain perturbation estimate. -/
theorem correctedJacobian_reverse_isUnitSphereGainLowerBound
    (J : Matrix m n 𝕜) (U : Matrix m r 𝕜) (V : Matrix r n 𝕜) (s : ℝ)
    (hCorrected : IsUnitSphereGainLowerBound (correctedJacobian J U V) s) :
    IsUnitSphereGainLowerBound J (s - ‖U * V‖) := by
  intro x hx
  have hAbs := abs_euclidean_unit_gain_correctedJacobian_sub_gain_le J U V x hx
  have hDiff :
      ‖Matrix.toEuclideanLin (correctedJacobian J U V) x‖ -
          ‖Matrix.toEuclideanLin J x‖ ≤ ‖U * V‖ :=
    le_trans (le_abs_self _) hAbs
  have hGain' :
      ‖Matrix.toEuclideanLin (correctedJacobian J U V) x‖ ≤
        ‖U * V‖ + ‖Matrix.toEuclideanLin J x‖ :=
    (sub_le_iff_le_add).mp hDiff
  have hGain :
      ‖Matrix.toEuclideanLin (correctedJacobian J U V) x‖ ≤
        ‖Matrix.toEuclideanLin J x‖ + ‖U * V‖ :=
    by simpa [add_comm] using hGain'
  calc
    s - ‖U * V‖ ≤
        ‖Matrix.toEuclideanLin (correctedJacobian J U V) x‖ - ‖U * V‖ :=
      sub_le_sub_right (hCorrected x hx) _
    _ ≤ ‖Matrix.toEuclideanLin J x‖ := (sub_le_iff_le_add).mpr hGain

omit [DecidableEq m] [DecidableEq r] in
/-- The variational smallest gain changes by at most the Euclidean operator
norm of the low-rank correction. -/
theorem abs_euclideanSmallestGain_correctedJacobian_sub_le [Nonempty n]
    (J : Matrix m n 𝕜) (U : Matrix m r 𝕜) (V : Matrix r n 𝕜) :
    |euclideanSmallestGain (correctedJacobian J U V) -
        euclideanSmallestGain J| ≤ ‖U * V‖ := by
  have hForward :
      euclideanSmallestGain J - ‖U * V‖ ≤
        euclideanSmallestGain (correctedJacobian J U V) := by
    rw [← isUnitSphereGainLowerBound_iff_le_euclideanSmallestGain]
    exact correctedJacobian_isUnitSphereGainLowerBound J U V
      (euclideanSmallestGain J)
      ((isUnitSphereGainLowerBound_iff_le_euclideanSmallestGain J
        (euclideanSmallestGain J)).2 le_rfl)
  have hReverse :
      euclideanSmallestGain (correctedJacobian J U V) - ‖U * V‖ ≤
        euclideanSmallestGain J := by
    rw [← isUnitSphereGainLowerBound_iff_le_euclideanSmallestGain]
    exact correctedJacobian_reverse_isUnitSphereGainLowerBound J U V
      (euclideanSmallestGain (correctedJacobian J U V))
      ((isUnitSphereGainLowerBound_iff_le_euclideanSmallestGain
        (correctedJacobian J U V)
        (euclideanSmallestGain (correctedJacobian J U V))).2 le_rfl)
  rw [abs_le]
  constructor <;> linarith

omit [DecidableEq m] [DecidableEq r] in
/-- Two-sided perturbation bounds with the nonnegative lower bound made
explicit. -/
theorem euclideanSmallestGain_correctedJacobian_bounds [Nonempty n]
    (J : Matrix m n 𝕜) (U : Matrix m r 𝕜) (V : Matrix r n 𝕜) :
    max 0 (euclideanSmallestGain J - ‖U * V‖) ≤
        euclideanSmallestGain (correctedJacobian J U V) ∧
      euclideanSmallestGain (correctedJacobian J U V) ≤
        euclideanSmallestGain J + ‖U * V‖ := by
  have hAbs := abs_euclideanSmallestGain_correctedJacobian_sub_le J U V
  rw [abs_le] at hAbs
  constructor
  · rw [max_le_iff]
    constructor
    · exact euclideanSmallestGain_nonneg _
    · linarith [hAbs.1]
  · linarith [hAbs.2]

end EuclideanGainPerturbation

section CircumcentroidalSixJoint

open scoped Matrix.Norms.L2Operator

variable {R : Type*} [CommRing R]

/-- The six-joint circumcentroidal correction with its physical block sizes:
`J_nu_e` is 6x6, `R_eb0` is 6x3, and `Jv_bar` is 3x6. -/
def circumcentroidalJacobian
    (JnuE : Matrix (Fin 6) (Fin 6) R)
    (Reb0 : Matrix (Fin 6) (Fin 3) R)
    (JvBar : Matrix (Fin 3) (Fin 6) R) :
    Matrix (Fin 6) (Fin 6) R :=
  correctedJacobian JnuE Reb0 JvBar

/-- The concrete 6x6-by-rank-three Gram expansion used by the FFSM model. -/
theorem circumcentroidalJacobian_gram
    (JnuE : Matrix (Fin 6) (Fin 6) R)
    (Reb0 : Matrix (Fin 6) (Fin 3) R)
    (JvBar : Matrix (Fin 3) (Fin 6) R) :
    (circumcentroidalJacobian JnuE Reb0 JvBar)ᵀ *
        circumcentroidalJacobian JnuE Reb0 JvBar =
      JnuEᵀ * JnuE - JnuEᵀ * Reb0 * JvBar -
        JvBarᵀ * Reb0ᵀ * JnuE + JvBarᵀ * Reb0ᵀ * Reb0 * JvBar := by
  exact correctedJacobian_gram JnuE Reb0 JvBar

/-- The concrete smaller 3x3 determinant update when the bare Jacobian is
nonsingular. -/
theorem det_circumcentroidalJacobian
    (JnuE : Matrix (Fin 6) (Fin 6) R)
    (Reb0 : Matrix (Fin 6) (Fin 3) R)
    (JvBar : Matrix (Fin 3) (Fin 6) R)
    (hJ : IsUnit JnuE.det) :
    (circumcentroidalJacobian JnuE Reb0 JvBar).det =
      JnuE.det * (1 - JvBar * JnuE⁻¹ * Reb0).det := by
  exact det_correctedJacobian JnuE Reb0 JvBar hJ

/-- Fixed six-joint specialization of the variational perturbation bound. -/
theorem abs_euclideanSmallestGain_circumcentroidalJacobian_sub_le
    (JnuE : Matrix (Fin 6) (Fin 6) ℝ)
    (Reb0 : Matrix (Fin 6) (Fin 3) ℝ)
    (JvBar : Matrix (Fin 3) (Fin 6) ℝ) :
    |euclideanSmallestGain (circumcentroidalJacobian JnuE Reb0 JvBar) -
        euclideanSmallestGain JnuE| ≤ ‖Reb0 * JvBar‖ := by
  exact abs_euclideanSmallestGain_correctedJacobian_sub_le JnuE Reb0 JvBar

end CircumcentroidalSixJoint

section VariationalInterfaceChecks

open scoped Matrix.Norms.L2Operator

/-- A narrow interface check with a non-unit bare scaling (`2`) and correction
factors (`3` and `1/2`).  This is an elaboration check, not a numerical
evaluation of the infimum. -/
example :
    let J : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ ↦ 2
    let U : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ ↦ 3
    let V : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ ↦ (1 / 2 : ℝ)
    |euclideanSmallestGain (correctedJacobian J U V) -
        euclideanSmallestGain J| ≤ ‖U * V‖ := by
  dsimp only
  exact abs_euclideanSmallestGain_correctedJacobian_sub_le _ _ _

/-- The max-form lower bound and additive upper bound elaborate on the same
non-unit one-dimensional fixture. -/
example :
    let J : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ ↦ 2
    let U : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ ↦ 3
    let V : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ ↦ (1 / 2 : ℝ)
    max 0 (euclideanSmallestGain J - ‖U * V‖) ≤
        euclideanSmallestGain (correctedJacobian J U V) ∧
      euclideanSmallestGain (correctedJacobian J U V) ≤
        euclideanSmallestGain J + ‖U * V‖ := by
  dsimp only
  exact euclideanSmallestGain_correctedJacobian_bounds _ _ _

end VariationalInterfaceChecks

end Ctrllib

#print axioms Ctrllib.correctedJacobian_transpose
#print axioms Ctrllib.correctedJacobian_mulVec
#print axioms Ctrllib.correctedJacobian_eq_on_correction_kernel
#print axioms Ctrllib.correctedJacobian_kernel_of_common_kernel
#print axioms Ctrllib.correctedJacobian_neg_neg
#print axioms Ctrllib.correctedJacobian_gram
#print axioms Ctrllib.det_fromBlocks_eq_det_correctedJacobian
#print axioms Ctrllib.det_correctedJacobian
#print axioms Ctrllib.correctedJacobian_toEuclideanLin_apply
#print axioms Ctrllib.correctedJacobian_euclidean_norm_lower
#print axioms Ctrllib.correctedJacobian_euclidean_norm_upper
#print axioms Ctrllib.abs_euclidean_norm_correctedJacobian_sub_norm_le
#print axioms Ctrllib.IsUnitSphereGainLowerBound
#print axioms Ctrllib.EuclideanUnitSphereGains
#print axioms Ctrllib.euclideanSmallestGain
#print axioms Ctrllib.euclideanUnitSphereGains_nonempty
#print axioms Ctrllib.euclideanUnitSphereGains_bddBelow
#print axioms Ctrllib.isUnitSphereGainLowerBound_iff_le_euclideanSmallestGain
#print axioms Ctrllib.euclideanSmallestGain_nonneg
#print axioms Ctrllib.correctedJacobian_isUnitSphereGainLowerBound
#print axioms Ctrllib.abs_euclidean_unit_gain_correctedJacobian_sub_gain_le
#print axioms Ctrllib.correctedJacobian_reverse_isUnitSphereGainLowerBound
#print axioms Ctrllib.abs_euclideanSmallestGain_correctedJacobian_sub_le
#print axioms Ctrllib.euclideanSmallestGain_correctedJacobian_bounds
#print axioms Ctrllib.circumcentroidalJacobian_gram
#print axioms Ctrllib.det_circumcentroidalJacobian
#print axioms Ctrllib.abs_euclideanSmallestGain_circumcentroidalJacobian_sub_le
