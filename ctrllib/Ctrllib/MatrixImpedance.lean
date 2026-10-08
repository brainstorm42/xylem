/-
Constant matrix impedance in a finite Euclidean task space.

The state is `(v,e)` and the unforced equation is
`M v' + D v + K e = 0`, `e' = v`. Symmetric positive-definite constant
matrices give a global operator-exponential flow, Lyapunov stability and convergence.
This is an ideal task equation, not an identification with a rover plant.
-/
import Ctrllib.LinearOperatorFlow
import Ctrllib.ComLaSalleMatrix
import Ctrllib.BlockPrecompact
import Ctrllib.KhalilStability

set_option maxSynthPendingDepth 3

open Matrix Set Filter Topology
open scoped InnerProductSpace

namespace Ctrllib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Matrix impedance state, velocity first and task error second. -/
abbrev MatrixImpedanceState (n : Type*) := EuclideanSpace ℝ n × EuclideanSpace ℝ n

/-- The unforced impedance field as a continuous linear operator. -/
noncomputable def matrixImpedanceCLM (M D K : Matrix n n ℝ) :
    MatrixImpedanceState n →L[ℝ] MatrixImpedanceState n :=
  (-((toEuclideanCLM (𝕜 := ℝ) M⁻¹).comp
      ((toEuclideanCLM (𝕜 := ℝ) D).comp (ContinuousLinearMap.fst ℝ _ _) +
       (toEuclideanCLM (𝕜 := ℝ) K).comp (ContinuousLinearMap.snd ℝ _ _)))).prod
    (ContinuousLinearMap.fst ℝ _ _)

/-- Exact match with the existing CoM field interface. -/
theorem matrixImpedanceCLM_apply (M D K : Matrix n n ℝ) (z : MatrixImpedanceState n) :
    matrixImpedanceCLM M D K z =
      comField (toEuclideanCLM (𝕜 := ℝ) D) (toEuclideanCLM (𝕜 := ℝ) K)
        (toEuclideanCLM (𝕜 := ℝ) M⁻¹) z := by
  simp [matrixImpedanceCLM, comField]

/-- The ideal equation has an explicit global flow for every matrix triple;
positivity is needed for stability, not for this linear flow construction. -/
noncomputable def matrixImpedanceFlow (M D K : Matrix n n ℝ) :
    Flow ℝ (MatrixImpedanceState n) :=
  linearOperatorFlow (matrixImpedanceCLM M D K)

/-- The global flow solves the explicit field with `M⁻¹`. Under SPD `M`,
this is equivalent to the implicit equation `M v' + D v + K e = 0`. -/
theorem matrixImpedance_isSolutionTo (M D K : Matrix n n ℝ) :
    IsSolutionTo (matrixImpedanceFlow M D K)
      (comField (toEuclideanCLM (𝕜 := ℝ) D) (toEuclideanCLM (𝕜 := ℝ) K)
        (toEuclideanCLM (𝕜 := ℝ) M⁻¹)) := by
  intro z t
  simpa only [matrixImpedanceFlow, matrixImpedanceCLM_apply] using
    linearOperatorFlow_hasDerivAt (matrixImpedanceCLM M D K) z t

/-- Mechanical energy in the operator representation already used by LaSalle. -/
noncomputable def matrixImpedanceEnergy (M K : Matrix n n ℝ) :
    MatrixImpedanceState n → ℝ :=
  comEnergy (toEuclideanCLM (𝕜 := ℝ) M) (toEuclideanCLM (𝕜 := ℝ) K)

/-- The operator energy is exactly the existing sum of matrix quadratic forms. -/
theorem matrixImpedanceEnergy_eq_blockLyap (M K : Matrix n n ℝ)
    (z : MatrixImpedanceState n) :
    matrixImpedanceEnergy M K z = blockLyap M K z.1 z.2 := by
  simp [matrixImpedanceEnergy, comEnergy, blockLyap, inner_toEuclideanCLM]

private theorem matrixImpedanceEnergy_decrease (M D K : Matrix n n ℝ)
    (hM : M.PosDef) (hD : D.PosDef) (hK : K.PosDef) :
    ∀ z, fderiv ℝ (matrixImpedanceEnergy M K) z
      (comField (toEuclideanCLM (𝕜 := ℝ) D) (toEuclideanCLM (𝕜 := ℝ) K)
        (toEuclideanCLM (𝕜 := ℝ) M⁻¹) z) ≤ 0 :=
  com_decrease (euclideanCLM_self_adjoint hM.isHermitian)
    (euclideanCLM_self_adjoint hK.isHermitian) (euclideanCLM_inv hM)
    (euclideanCLM_dotProduct_nonneg hD)

/-- Energy is nonincreasing along the explicit flow. -/
theorem matrixImpedanceEnergy_antitone (M D K : Matrix n n ℝ)
    (hM : M.PosDef) (hD : D.PosDef) (hK : K.PosDef) (z : MatrixImpedanceState n) :
    Antitone (fun t : ℝ => matrixImpedanceEnergy M K (matrixImpedanceFlow M D K t z)) := by
  have hsol := matrixImpedance_isSolutionTo M D K
  have hdiff : Differentiable ℝ (matrixImpedanceEnergy M K) := comEnergy_differentiable
  apply antitone_of_deriv_nonpos
  · exact fun t => (hsol.hasDerivAt_comp hdiff z t).differentiableAt
  · intro t
    rw [(hsol.hasDerivAt_comp hdiff z t).deriv]
    exact matrixImpedanceEnergy_decrease M D K hM hD hK _

variable [Nonempty n]

/-- Coercivity supplies strict positivity off the origin in any nonempty
finite task dimension. -/
theorem matrixImpedanceEnergy_pos (M K : Matrix n n ℝ)
    (hM : M.PosDef) (hK : K.PosDef) (z : MatrixImpedanceState n) (hz : z ≠ 0) :
    0 < matrixImpedanceEnergy M K z := by
  obtain ⟨c, hc, hb⟩ := blockLyap_norm_coercive hM hK
  rw [matrixImpedanceEnergy_eq_blockLyap]
  exact (mul_pos hc (sq_pos_of_pos (norm_pos_iff.mpr hz))).trans_le (hb z)

/-- Lyapunov stability of the origin for constant SPD matrix impedance. -/
theorem matrixImpedance_lyapStable (M D K : Matrix n n ℝ)
    (hM : M.PosDef) (hD : D.PosDef) (hK : K.PosDef) :
    LyapStable (matrixImpedanceFlow M D K) := by
  refine lyapunov_stable (ϕ := matrixImpedanceFlow M D K)
    (f := comField (toEuclideanCLM (𝕜 := ℝ) D) (toEuclideanCLM (𝕜 := ℝ) K)
      (toEuclideanCLM (𝕜 := ℝ) M⁻¹)) (V := matrixImpedanceEnergy M K)
    (matrixImpedance_isSolutionTo M D K) comEnergy_differentiable ?_ ?_ ?_
  · simp [matrixImpedanceEnergy, comEnergy]
  · exact matrixImpedanceEnergy_pos M K hM hK
  · exact matrixImpedanceEnergy_decrease M D K hM hD hK

/-- Every initial state converges; flow existence and forward precompactness
are discharged here rather than assumed by the caller. -/
theorem matrixImpedance_tendsto_zero (M D K : Matrix n n ℝ)
    (hM : M.PosDef) (hD : D.PosDef) (hK : K.PosDef) (z : MatrixImpedanceState n) :
    Tendsto (fun t : ℝ => matrixImpedanceFlow M D K t z) atTop (𝓝 0) := by
  apply com_attractive_matrix M D K hM hD hK _ (matrixImpedance_isSolutionTo M D K) z
  apply forwardPrecompact_blockLyap hM hK
  intro t ht
  have h := matrixImpedanceEnergy_antitone M D K hM hD hK z ht
  simpa only [Flow.map_zero_apply, matrixImpedanceEnergy_eq_blockLyap] using h

/-- Stability and global convergence of the ideal constant matrix equation. -/
theorem matrixImpedance_globally_asymptotically_stable (M D K : Matrix n n ℝ)
    (hM : M.PosDef) (hD : D.PosDef) (hK : K.PosDef) :
    LyapStable (matrixImpedanceFlow M D K) ∧
      ∀ z, Tendsto (fun t : ℝ => matrixImpedanceFlow M D K t z) atTop (𝓝 0) :=
  ⟨matrixImpedance_lyapStable M D K hM hD hK,
    matrixImpedance_tendsto_zero M D K hM hD hK⟩

end Ctrllib

#print axioms Ctrllib.matrixImpedanceCLM_apply
#print axioms Ctrllib.matrixImpedance_isSolutionTo
#print axioms Ctrllib.matrixImpedanceEnergy_eq_blockLyap
#print axioms Ctrllib.matrixImpedanceEnergy_antitone
#print axioms Ctrllib.matrixImpedanceEnergy_pos
#print axioms Ctrllib.matrixImpedance_lyapStable
#print axioms Ctrllib.matrixImpedance_tendsto_zero
#print axioms Ctrllib.matrixImpedance_globally_asymptotically_stable
