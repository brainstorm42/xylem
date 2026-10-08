/-
Forced constant-matrix impedance power balance.

For a finite Euclidean task space, this module keeps the input port explicit:

    M v' + D v + K e = f,    e' = v.

The storage is `1/2 vᵀ M v + 1/2 eᵀ K e`.  Symmetry of `M` and `K` gives the
pointwise balance

    dV/dt = vᵀ f - vᵀ D v.

The trajectory is supplied with actual `HasDerivAt` witnesses.  No ODE
existence theorem is assumed here; the result is a local calculus identity for
any trajectory satisfying the displayed equation at the time in question.
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Matrix.PosDef
import Ctrllib.BlockLyapunov
import Ctrllib.ComLaSalleMatrix

open Matrix
open scoped InnerProductSpace

namespace Ctrllib

variable {n : Type*} [Fintype n] [DecidableEq n]

abbrev ForcedImpedanceCoord (n : Type*) := EuclideanSpace ℝ n

/- The storage is written through the matrix-to-Euclidean operator bridge so
   that the calculus proof can use the inner-product derivative lemmas. -/
noncomputable def forcedImpedanceEnergy (M K : Matrix n n ℝ)
    (v e : ForcedImpedanceCoord n) : ℝ :=
  (1 / 2 : ℝ) * ⟪v, toEuclideanCLM (𝕜 := ℝ) M v⟫_ℝ +
    (1 / 2 : ℝ) * ⟪e, toEuclideanCLM (𝕜 := ℝ) K e⟫_ℝ

theorem forcedImpedanceEnergy_eq_blockLyap (M K : Matrix n n ℝ)
    (v e : ForcedImpedanceCoord n) :
    forcedImpedanceEnergy M K v e =
      blockLyap M K (WithLp.ofLp v) (WithLp.ofLp e) := by
  simp [forcedImpedanceEnergy, blockLyap, inner_toEuclideanCLM]

omit [DecidableEq n] in
private lemma real_inner_eq_dotProduct (x y : ForcedImpedanceCoord n) :
    ⟪x, y⟫_ℝ = WithLp.ofLp x ⬝ᵥ WithLp.ofLp y := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct_comm]

/-- General path derivative for the quadratic storage before imposing the
impedance equation.  This is public so coupled extensions can reuse the
calculus step without reproving the quadratic derivative. -/
theorem forcedImpedance_energy_path_hasDerivAt
    (M K : Matrix n n ℝ) (hM : M.IsHermitian) (hK : K.IsHermitian)
    {v e : ℝ → ForcedImpedanceCoord n}
    {a b : ForcedImpedanceCoord n} {t : ℝ}
    (hv : HasDerivAt v a t) (he : HasDerivAt e b t) :
    HasDerivAt (fun s => forcedImpedanceEnergy M K (v s) (e s))
      (⟪v t, toEuclideanCLM (𝕜 := ℝ) M a⟫_ℝ +
        ⟪e t, toEuclideanCLM (𝕜 := ℝ) K b⟫_ℝ) t := by
  have hMv : HasDerivAt (fun s => toEuclideanCLM (𝕜 := ℝ) M (v s))
      (toEuclideanCLM (𝕜 := ℝ) M a) t := by
    simpa using (hasDerivAt_const t (toEuclideanCLM (𝕜 := ℝ) M)).clm_apply hv
  have hKe : HasDerivAt (fun s => toEuclideanCLM (𝕜 := ℝ) K (e s))
      (toEuclideanCLM (𝕜 := ℝ) K b) t := by
    simpa using (hasDerivAt_const t (toEuclideanCLM (𝕜 := ℝ) K)).clm_apply he
  have hkin := (hv.inner ℝ hMv).const_mul (1 / 2 : ℝ)
  have hpot := (he.inner ℝ hKe).const_mul (1 / 2 : ℝ)
  have hMsymm :
      ⟪a, toEuclideanCLM (𝕜 := ℝ) M (v t)⟫_ℝ =
        ⟪v t, toEuclideanCLM (𝕜 := ℝ) M a⟫_ℝ := by
    rw [real_inner_comm, euclideanCLM_self_adjoint hM]
  have hKsymm :
      ⟪b, toEuclideanCLM (𝕜 := ℝ) K (e t)⟫_ℝ =
        ⟪e t, toEuclideanCLM (𝕜 := ℝ) K b⟫_ℝ := by
    rw [real_inner_comm, euclideanCLM_self_adjoint hK]
  have hsum : HasDerivAt (fun s => forcedImpedanceEnergy M K (v s) (e s))
      ((1 / 2 : ℝ) *
          (⟪v t, toEuclideanCLM (𝕜 := ℝ) M a⟫_ℝ +
            ⟪a, toEuclideanCLM (𝕜 := ℝ) M (v t)⟫_ℝ) +
        (1 / 2 : ℝ) *
          (⟪e t, toEuclideanCLM (𝕜 := ℝ) K b⟫_ℝ +
            ⟪b, toEuclideanCLM (𝕜 := ℝ) K (e t)⟫_ℝ)) t := by
    have hsum0 := hkin.add hpot
    apply hsum0.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun s => rfl)
  apply hsum.congr_deriv
  rw [hMsymm, hKsymm]
  ring

/-- Exact instantaneous power balance for a forced constant-matrix impedance
trajectory.  The hypotheses are local derivative witnesses and the equation
`M v' + D v + K e = f` at the selected time. -/
theorem forcedImpedance_energy_hasDerivAt
    (M D K : Matrix n n ℝ) (hM : M.IsHermitian) (hK : K.IsHermitian)
    {v e f : ℝ → ForcedImpedanceCoord n}
    {a : ForcedImpedanceCoord n} {t : ℝ}
    (hv : HasDerivAt v a t) (he : HasDerivAt e (v t) t)
    (heq : toEuclideanCLM (𝕜 := ℝ) M a +
        toEuclideanCLM (𝕜 := ℝ) D (v t) +
        toEuclideanCLM (𝕜 := ℝ) K (e t) = f t) :
    HasDerivAt (fun s => forcedImpedanceEnergy M K (v s) (e s))
      (WithLp.ofLp (v t) ⬝ᵥ WithLp.ofLp (f t) -
        WithLp.ofLp (v t) ⬝ᵥ D *ᵥ WithLp.ofLp (v t)) t := by
  have hraw := forcedImpedance_energy_path_hasDerivAt M K hM hK hv he
  have hbal :
      ⟪v t, toEuclideanCLM (𝕜 := ℝ) M a⟫_ℝ +
          ⟪v t, toEuclideanCLM (𝕜 := ℝ) K (e t)⟫_ℝ =
        ⟪v t, f t⟫_ℝ -
          ⟪v t, toEuclideanCLM (𝕜 := ℝ) D (v t)⟫_ℝ := by
    have hinner := congrArg (fun x : ForcedImpedanceCoord n => ⟪v t, x⟫_ℝ) heq
    rw [inner_add_right, inner_add_right] at hinner
    linarith
  have hKcross :
      ⟪e t, toEuclideanCLM (𝕜 := ℝ) K (v t)⟫_ℝ =
        ⟪v t, toEuclideanCLM (𝕜 := ℝ) K (e t)⟫_ℝ := by
    rw [real_inner_comm, euclideanCLM_self_adjoint hK]
  apply hraw.congr_deriv
  rw [hKcross, hbal, real_inner_eq_dotProduct, real_inner_eq_dotProduct]
  rw [ofLp_toEuclideanCLM]

/- The storage value is nonnegative under the weak matrix assumptions used for
   a storage function. -/
theorem forcedImpedanceEnergy_nonneg
    (M K : Matrix n n ℝ) (hM : M.PosSemidef) (hK : K.PosSemidef)
    (v e : ForcedImpedanceCoord n) :
    0 ≤ forcedImpedanceEnergy M K v e := by
  rw [forcedImpedanceEnergy, inner_toEuclideanCLM, inner_toEuclideanCLM]
  have hMv := hM.dotProduct_mulVec_nonneg (WithLp.ofLp v)
  have hKe := hK.dotProduct_mulVec_nonneg (WithLp.ofLp e)
  simpa using add_nonneg (mul_nonneg (by norm_num) hMv) (mul_nonneg (by norm_num) hKe)

/-- Pointwise differential dissipation/passivity inequality.  The derivative
exists by the exact balance theorem, and PSD damping makes the dissipated power
nonnegative. -/
theorem forcedImpedance_energy_deriv_le_power
    (M D K : Matrix n n ℝ) (hM : M.IsHermitian) (hK : K.IsHermitian)
    (hD : D.PosSemidef)
    {v e f : ℝ → ForcedImpedanceCoord n}
    {a : ForcedImpedanceCoord n} {t : ℝ}
    (hv : HasDerivAt v a t) (he : HasDerivAt e (v t) t)
    (heq : toEuclideanCLM (𝕜 := ℝ) M a +
        toEuclideanCLM (𝕜 := ℝ) D (v t) +
        toEuclideanCLM (𝕜 := ℝ) K (e t) = f t) :
    deriv (fun s => forcedImpedanceEnergy M K (v s) (e s)) t ≤
      WithLp.ofLp (v t) ⬝ᵥ WithLp.ofLp (f t) := by
  have hderiv := forcedImpedance_energy_hasDerivAt M D K hM hK hv he heq
  rw [hderiv.deriv]
  have hDnonneg := hD.dotProduct_mulVec_nonneg (WithLp.ofLp (v t))
  have hDnonneg' : 0 ≤ WithLp.ofLp (v t) ⬝ᵥ D *ᵥ WithLp.ofLp (v t) := by
    simpa using hDnonneg
  linarith

end Ctrllib

#print axioms Ctrllib.forcedImpedanceEnergy_eq_blockLyap
#print axioms Ctrllib.forcedImpedance_energy_path_hasDerivAt
#print axioms Ctrllib.forcedImpedance_energy_hasDerivAt
#print axioms Ctrllib.forcedImpedanceEnergy_nonneg
#print axioms Ctrllib.forcedImpedance_energy_deriv_le_power
