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
import Ctrllib.TrackingDissipation

open Matrix
open scoped BigOperators

namespace Ctrllib

variable {n m : Type*} [Fintype n] [Fintype m]

private lemma hasDerivAt_dotProduct
    {x y : ℝ → (n → ℝ)} {xd yd : n → ℝ} {t : ℝ}
    (hx : HasDerivAt x xd t) (hy : HasDerivAt y yd t) :
    HasDerivAt (fun s => x s ⬝ᵥ y s)
      (xd ⬝ᵥ y t + x t ⬝ᵥ yd) t := by
  classical
  have hxi : ∀ i : n, HasDerivAt (fun s => x s i) (xd i) t := by
    intro i
    simpa using (hasDerivAt_const t (ContinuousLinearMap.proj i)).clm_apply hx
  have hyi : ∀ i : n, HasDerivAt (fun s => y s i) (yd i) t := by
    intro i
    simpa using (hasDerivAt_const t (ContinuousLinearMap.proj i)).clm_apply hy
  have hsum : HasDerivAt (fun s => ∑ i : n, x s i * y s i)
      (∑ i : n, (xd i * y t i + x t i * yd i)) t := by
    apply HasDerivAt.fun_sum
    intro i hi
    exact (hxi i).mul (hyi i)
  simpa [dotProduct, Finset.sum_add_distrib] using hsum

private lemma hasDerivAt_matrix_mulVec
    {A : ℝ → Matrix n n ℝ} {x : ℝ → (n → ℝ)}
    {Ad : Matrix n n ℝ} {xd : n → ℝ} {t : ℝ}
    (hA : HasDerivAt A Ad t) (hx : HasDerivAt x xd t) :
    HasDerivAt (fun s => A s *ᵥ x s)
      (Ad *ᵥ x t + A t *ᵥ xd) t := by
  classical
  have hAi : ∀ i : n, HasDerivAt (fun s => A s i) (Ad i) t := by
    intro i
    have h := (hasDerivAt_const t
      (ContinuousLinearMap.proj i : (Matrix n n ℝ) →L[ℝ] (n → ℝ))).clm_apply hA
    have hfun :
        (fun s =>
            (ContinuousLinearMap.proj i : (Matrix n n ℝ) →L[ℝ] (n → ℝ)) (A s)) =
          (fun s => A s i) := by
      funext s
      rfl
    rw [hfun] at h
    have hderiv :
        ((0 : (Matrix n n ℝ) →L[ℝ] (n → ℝ)) (A t) +
          (ContinuousLinearMap.proj i : (Matrix n n ℝ) →L[ℝ] (n → ℝ)) Ad) = Ad i := by
      change (0 : n → ℝ) + Ad i = Ad i
      simp
    exact h.congr_deriv hderiv
  have hAij : ∀ i j : n, HasDerivAt (fun s => A s i j) (Ad i j) t := by
    intro i j
    simpa [ContinuousLinearMap.proj_apply] using
      (hasDerivAt_const t
        (ContinuousLinearMap.proj j : (n → ℝ) →L[ℝ] ℝ)).clm_apply (hAi i)
  have hxi : ∀ j : n, HasDerivAt (fun s => x s j) (xd j) t := by
    intro j
    simpa [ContinuousLinearMap.proj_apply] using
      (hasDerivAt_const t
        (ContinuousLinearMap.proj j : (n → ℝ) →L[ℝ] ℝ)).clm_apply hx
  apply hasDerivAt_pi.mpr
  intro i
  have hsum : HasDerivAt (fun s => ∑ j : n, A s i j * x s j)
      (∑ j : n, (Ad i j * x t j + A t i j * xd j)) t := by
    apply HasDerivAt.fun_sum
    intro j hj
    exact (hAij i j).mul (hxi j)
  simpa [Matrix.mulVec, dotProduct, Pi.add_apply, Finset.sum_add_distrib] using hsum

private lemma hasDerivAt_const_matrix_mulVec
    {A : Matrix n n ℝ} {x : ℝ → (n → ℝ)}
    {xd : n → ℝ} {t : ℝ} (hx : HasDerivAt x xd t) :
    HasDerivAt (fun s => A *ᵥ x s) (A *ᵥ xd) t := by
  classical
  have hxi : ∀ j : n, HasDerivAt (fun s => x s j) (xd j) t := by
    intro j
    simpa [ContinuousLinearMap.proj_apply] using
      (hasDerivAt_const t
        (ContinuousLinearMap.proj j : (n → ℝ) →L[ℝ] ℝ)).clm_apply hx
  apply hasDerivAt_pi.mpr
  intro i
  have hsum : HasDerivAt (fun s => ∑ j : n, A i j * x s j)
      (∑ j : n, A i j * xd j) t := by
    apply HasDerivAt.fun_sum
    intro j hj
    convert (hasDerivAt_const t (A i j)).mul (hxi j) using 1
    simp
  simpa [Matrix.mulVec, dotProduct] using hsum

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
  have hMx := hasDerivAt_const_matrix_mulVec (n := m) (A := K) hx
  have heq := hasDerivAt_dotProduct he hMe
  have hxq := hasDerivAt_dotProduct hx hMx
  have hMcross : edot ⬝ᵥ M t *ᵥ e t = e t ⬝ᵥ M t *ᵥ edot := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hMsym, dotProduct_comm]
  have hKcross : xdot ⬝ᵥ K *ᵥ x t = x t ⬝ᵥ K *ᵥ xdot := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hKsym, dotProduct_comm]
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
