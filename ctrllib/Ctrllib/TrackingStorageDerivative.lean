/-
Calculus bridge for the time-varying tracking storage.

This theorem differentiates the displayed quadratic storage under supplied
path derivatives.  It does not supply an ODE realization or any source/model
correspondence for those derivatives.
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Data.Matrix.Mul
import Ctrllib.BlockLyapunov
import Ctrllib.MatrixPathDerivative
import Ctrllib.QuadraticForm
import Ctrllib.TrackingDissipation

open Matrix
open scoped BigOperators

namespace Ctrllib

variable {n m : Type*} [Fintype n] [Fintype m]

/-- Derivative of the tracking storage under supplied path derivatives.

The symmetry assumptions are exactly what identifies the two product-rule
cross terms with the single terms in `trackingRate`.  The theorem is a local
calculus identity: it does not assert that `M`, `e`, or `x` arise from a
particular plant, controller, or ODE.
-/
theorem blockLyap_hasDerivAt
    {M : ℝ → Matrix n n ℝ} {Mdot : Matrix n n ℝ}
    {K : Matrix m m ℝ}
    {e : ℝ → (n → ℝ)} {edot : n → ℝ}
    {x : ℝ → (m → ℝ)} {xdot : m → ℝ} {t : ℝ}
    (hM : HasDerivAt M Mdot t)
    (he : HasDerivAt e edot t)
    (hx : HasDerivAt x xdot t)
    (hMsym : (M t)ᵀ = M t)
    (hKsym : Kᵀ = K) :
    HasDerivAt (fun s => blockLyap (M s) K (e s) (x s))
      (trackingRate (M t) Mdot K (e t) edot (x t) xdot) t := by
  have hMe := hasDerivAt_matrix_mulVec hM he
  have hMx := hasDerivAt_const_matrix_mulVec (p := m) (q := m) (A := K) hx
  have heq := hasDerivAt_dotProduct he hMe
  have hxq := hasDerivAt_dotProduct hx hMx
  have hMcross : edot ⬝ᵥ M t *ᵥ e t = e t ⬝ᵥ M t *ᵥ edot := by
    exact dotProduct_mulVec_symm_of_transpose_eq hMsym _ _
  have hKcross : xdot ⬝ᵥ K *ᵥ x t = x t ⬝ᵥ K *ᵥ xdot := by
    exact dotProduct_mulVec_symm_of_transpose_eq hKsym _ _
  have hsum :
      HasDerivAt
        (fun s => blockLyap (M s) K (e s) (x s))
        ((1 / 2 : ℝ) *
            (edot ⬝ᵥ M t *ᵥ e t +
              e t ⬝ᵥ (Mdot *ᵥ e t + M t *ᵥ edot)) +
          (1 / 2 : ℝ) *
            (xdot ⬝ᵥ K *ᵥ x t + x t ⬝ᵥ (0 *ᵥ x t + K *ᵥ xdot))) t := by
    have h1 := (heq.const_mul (1 / 2 : ℝ))
    have h2 := (hxq.const_mul (1 / 2 : ℝ))
    have hadd := h1.add h2
    convert hadd using 1
    · funext s
      simp [blockLyap]
    · simp
  apply hsum.congr_deriv
  rw [hMcross, hKcross]
  simp only [zero_mulVec]
  unfold trackingRate
  rw [dotProduct_add]
  ring_nf

end Ctrllib

#print axioms Ctrllib.blockLyap_hasDerivAt
