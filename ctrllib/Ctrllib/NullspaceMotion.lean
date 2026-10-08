import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.PosDef

open Matrix

namespace Ctrllib

section Ring

variable {R : Type*} [CommRing R]
variable {m n : Type*} [Fintype m] [Fintype n]

/-- The rank-one projector determined by a kernel vector `k` and a
normalizing covector `z`. -/
def rankOneProjector (k z : n → R) : Matrix n n R :=
  fun i j => k i * z j

theorem rankOneProjector_mulVec (k z x : n → R) :
    rankOneProjector k z *ᵥ x = (z ⬝ᵥ x) • k := by
  ext i
  simp only [rankOneProjector, Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem rankOneProjector_idempotent (k z : n → R) (hzk : z ⬝ᵥ k = 1) :
    rankOneProjector k z * rankOneProjector k z = rankOneProjector k z := by
  ext i j
  change (∑ x, (k i * z x) * (k x * z j)) = k i * z j
  change (∑ x, z x * k x) = 1 at hzk
  calc
    (∑ x, (k i * z x) * (k x * z j))
        = k i * (∑ x, z x * k x) * z j := by
            rw [Finset.mul_sum, Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro x _
            ring
    _ = k i * z j := by rw [hzk, mul_one]

-- The projector does not depend on the sign chosen for the one-dimensional
-- kernel basis.
omit [Fintype n] in
theorem rankOneProjector_neg_neg (k z : n → R) :
    rankOneProjector (-k) (-z) = rankOneProjector k z := by
  ext i j
  simp [rankOneProjector]

omit [Fintype m] in
theorem task_annihilates_rankOneProjector (J : Matrix m n R) (k z : n → R)
    (hk : J *ᵥ k = 0) :
    J * rankOneProjector k z = 0 := by
  ext i j
  have hki : (∑ x, J i x * k x) = 0 := by
    simpa [Matrix.mulVec, dotProduct] using congrFun hk i
  change (∑ x, J i x * (k x * z j)) = 0
  calc
    (∑ x, J i x * (k x * z j))
        = (∑ x, J i x * k x) * z j := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro x _
            ring
    _ = 0 := by rw [hki, zero_mul]

-- Every projected velocity lies in the task kernel.
omit [Fintype m] in
theorem task_annihilates_projected_velocity (J : Matrix m n R) (k z x : n → R)
    (hk : J *ᵥ k = 0) :
    J *ᵥ (rankOneProjector k z *ᵥ x) = 0 := by
  rw [rankOneProjector_mulVec]
  ext i
  have hki : (∑ j, J i j * k j) = 0 := by
    simpa [Matrix.mulVec, dotProduct] using congrFun hk i
  change (∑ j, J i j * ((z ⬝ᵥ x) * k j)) = 0
  calc
    (∑ j, J i j * ((z ⬝ᵥ x) * k j))
        = (z ⬝ᵥ x) * (∑ j, J i j * k j) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
    _ = 0 := by rw [hki, mul_zero]

/-- A task wrench does zero virtual work along a task-null velocity. -/
theorem taskWrench_dot_null_eq_zero (J : Matrix m n R) (k : n → R) (w : m → R)
    (hk : J *ᵥ k = 0) :
    k ⬝ᵥ (Jᵀ *ᵥ w) = 0 := by
  rw [dotProduct_comm, mulVec_transpose, ← dotProduct_mulVec, hk, dotProduct_zero]

end Ring

section RealInertia

variable {m n : Type*} [Fintype m] [Fintype n]

/-- The kinetic-energy coefficient along `k`. This definition is algebraic: a
positive-definite interpretation is supplied separately by
`inertiaDenominator_pos`. -/
def inertiaDenominator (M : Matrix n n ℝ) (k : n → ℝ) : ℝ :=
  k ⬝ᵥ (M *ᵥ k)

/-- The inertia-weighted covector normalized to read one on `k` whenever the
inertia denominator is nonzero. -/
noncomputable def inertiaWeightedCovector (M : Matrix n n ℝ) (k : n → ℝ) : n → ℝ :=
  (inertiaDenominator M k)⁻¹ • (M *ᵥ k)

/-- The rank-one inertia-weighted projector onto the line spanned by `k`. -/
noncomputable def inertiaProjector (M : Matrix n n ℝ) (k : n → ℝ) : Matrix n n ℝ :=
  rankOneProjector k (inertiaWeightedCovector M k)

theorem inertiaDenominator_pos {M : Matrix n n ℝ} {k : n → ℝ}
    (hM : M.PosDef) (hk : k ≠ 0) :
    0 < inertiaDenominator M k := by
  simpa [inertiaDenominator] using hM.dotProduct_mulVec_pos hk

theorem inertiaWeightedCovector_dot_kernel {M : Matrix n n ℝ} {k : n → ℝ}
    (hden : inertiaDenominator M k ≠ 0) :
    inertiaWeightedCovector M k ⬝ᵥ k = 1 := by
  rw [inertiaWeightedCovector, smul_dotProduct, dotProduct_comm]
  exact inv_mul_cancel₀ hden

theorem inertiaProjector_idempotent {M : Matrix n n ℝ} {k : n → ℝ}
    (hden : inertiaDenominator M k ≠ 0) :
    inertiaProjector M k * inertiaProjector M k = inertiaProjector M k := by
  exact rankOneProjector_idempotent k (inertiaWeightedCovector M k)
    (inertiaWeightedCovector_dot_kernel hden)

omit [Fintype m] in
theorem task_annihilates_inertiaProjector (J : Matrix m n ℝ) (M : Matrix n n ℝ)
    (k : n → ℝ) (hk : J *ᵥ k = 0) :
    J * inertiaProjector M k = 0 := by
  exact task_annihilates_rankOneProjector J k (inertiaWeightedCovector M k) hk

theorem inertiaDenominator_neg (M : Matrix n n ℝ) (k : n → ℝ) :
    inertiaDenominator M (-k) = inertiaDenominator M k := by
  rw [inertiaDenominator, inertiaDenominator, Matrix.mulVec_neg,
    neg_dotProduct_neg]

theorem inertiaWeightedCovector_neg (M : Matrix n n ℝ) (k : n → ℝ) :
    inertiaWeightedCovector M (-k) = -inertiaWeightedCovector M k := by
  rw [inertiaWeightedCovector, inertiaWeightedCovector, inertiaDenominator_neg,
    Matrix.mulVec_neg, smul_neg]

theorem inertiaProjector_neg (M : Matrix n n ℝ) (k : n → ℝ) :
    inertiaProjector M (-k) = inertiaProjector M k := by
  rw [inertiaProjector, inertiaProjector, inertiaWeightedCovector_neg]
  exact rankOneProjector_neg_neg k (inertiaWeightedCovector M k)

/-- A basis-orientation-independent descent velocity along the line spanned by
`k`, weighted by its inertia denominator. No claim is made here that `gradient`
is the gradient of a concrete robot objective. -/
noncomputable def inertiaProjectedDescentVelocity
    (M : Matrix n n ℝ) (k gradient : n → ℝ)
    (gain : ℝ) : n → ℝ :=
  (-gain * (inertiaDenominator M k)⁻¹ * (k ⬝ᵥ gradient)) • k

theorem gradient_dot_inertiaProjectedDescentVelocity
    (M : Matrix n n ℝ) (k gradient : n → ℝ) (gain : ℝ) :
    gradient ⬝ᵥ inertiaProjectedDescentVelocity M k gradient gain
      = (-gain * (k ⬝ᵥ gradient) ^ 2) / inertiaDenominator M k := by
  simp [inertiaProjectedDescentVelocity, dotProduct_smul, dotProduct_comm, div_eq_mul_inv]
  ring

omit [Fintype m] in
theorem task_annihilates_inertiaProjectedDescentVelocity
    (J : Matrix m n ℝ) (M : Matrix n n ℝ) (k gradient : n → ℝ) (gain : ℝ)
    (hk : J *ᵥ k = 0) :
    J *ᵥ inertiaProjectedDescentVelocity M k gradient gain = 0 := by
  rw [inertiaProjectedDescentVelocity, mulVec_smul, hk, smul_zero]

theorem gradient_dot_inertiaProjectedDescentVelocity_nonpos
    {M : Matrix n n ℝ} {k gradient : n → ℝ} {gain : ℝ}
    (hgain : 0 ≤ gain) (hden : 0 < inertiaDenominator M k) :
    gradient ⬝ᵥ inertiaProjectedDescentVelocity M k gradient gain ≤ 0 := by
  rw [gradient_dot_inertiaProjectedDescentVelocity]
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hgain) (sq_nonneg _)) hden.le

theorem inertiaProjectedDescentVelocity_neg_basis
    (M : Matrix n n ℝ) (k gradient : n → ℝ) (gain : ℝ) :
    inertiaProjectedDescentVelocity M (-k) gradient gain
      = inertiaProjectedDescentVelocity M k gradient gain := by
  ext i
  simp [inertiaProjectedDescentVelocity, inertiaDenominator_neg, dotProduct]

end RealInertia

end Ctrllib

#print axioms Ctrllib.rankOneProjector_mulVec
#print axioms Ctrllib.rankOneProjector_idempotent
#print axioms Ctrllib.rankOneProjector_neg_neg
#print axioms Ctrllib.task_annihilates_rankOneProjector
#print axioms Ctrllib.task_annihilates_projected_velocity
#print axioms Ctrllib.taskWrench_dot_null_eq_zero
#print axioms Ctrllib.inertiaDenominator_pos
#print axioms Ctrllib.inertiaWeightedCovector_dot_kernel
#print axioms Ctrllib.inertiaProjector_idempotent
#print axioms Ctrllib.task_annihilates_inertiaProjector
#print axioms Ctrllib.inertiaDenominator_neg
#print axioms Ctrllib.inertiaWeightedCovector_neg
#print axioms Ctrllib.inertiaProjector_neg
#print axioms Ctrllib.gradient_dot_inertiaProjectedDescentVelocity
#print axioms Ctrllib.task_annihilates_inertiaProjectedDescentVelocity
#print axioms Ctrllib.gradient_dot_inertiaProjectedDescentVelocity_nonpos
#print axioms Ctrllib.inertiaProjectedDescentVelocity_neg_basis
