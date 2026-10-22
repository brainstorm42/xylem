/-
Finite-dimensional matrix/path derivative bridges.

These lemmas expose only coordinatewise calculus for finite matrix and vector
paths. They do not supply an ODE realization or any source/model
correspondence.
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Data.Matrix.Mul
import Mathlib.Topology.Instances.Matrix

open Matrix
open scoped BigOperators

namespace Ctrllib

lemma hasDerivAt_dotProduct
    {p : Type*} [Fintype p]
    {x y : ℝ → (p → ℝ)} {xd yd : p → ℝ} {t : ℝ}
    (hx : HasDerivAt x xd t) (hy : HasDerivAt y yd t) :
    HasDerivAt (fun s => x s ⬝ᵥ y s)
      (xd ⬝ᵥ y t + x t ⬝ᵥ yd) t := by
  classical
  have hxi : ∀ i : p, HasDerivAt (fun s => x s i) (xd i) t := by
    intro i
    simpa using (hasDerivAt_const t (ContinuousLinearMap.proj i)).clm_apply hx
  have hyi : ∀ i : p, HasDerivAt (fun s => y s i) (yd i) t := by
    intro i
    simpa using (hasDerivAt_const t (ContinuousLinearMap.proj i)).clm_apply hy
  have hsum : HasDerivAt (fun s => ∑ i : p, x s i * y s i)
      (∑ i : p, (xd i * y t i + x t i * yd i)) t := by
    apply HasDerivAt.fun_sum
    intro i hi
    exact (hxi i).mul (hyi i)
  simpa [dotProduct, Finset.sum_add_distrib] using hsum

set_option linter.unusedFintypeInType false in
lemma hasDerivAt_matrix_mulVec
    {p q : Type*} [Fintype p] [Fintype q]
    {A : ℝ → Matrix p q ℝ} {x : ℝ → (q → ℝ)}
    {Ad : Matrix p q ℝ} {xd : q → ℝ} {t : ℝ}
    (hA : HasDerivAt A Ad t) (hx : HasDerivAt x xd t) :
    HasDerivAt (fun s => A s *ᵥ x s)
      (Ad *ᵥ x t + A t *ᵥ xd) t := by
  classical
  have hAi : ∀ i : p, HasDerivAt (fun s => A s i) (Ad i) t := by
    intro i
    have h := (hasDerivAt_const t
      (ContinuousLinearMap.proj i : (Matrix p q ℝ) →L[ℝ] (q → ℝ))).clm_apply hA
    have hfun :
        (fun s =>
            (ContinuousLinearMap.proj i : (Matrix p q ℝ) →L[ℝ] (q → ℝ)) (A s)) =
          (fun s => A s i) := by
      funext s
      rfl
    rw [hfun] at h
    have hderiv :
        ((0 : (Matrix p q ℝ) →L[ℝ] (q → ℝ)) (A t) +
          (ContinuousLinearMap.proj i : (Matrix p q ℝ) →L[ℝ] (q → ℝ)) Ad) = Ad i := by
      change (0 : q → ℝ) + Ad i = Ad i
      simp
    exact h.congr_deriv hderiv
  have hAij : ∀ i j, HasDerivAt (fun s => A s i j) (Ad i j) t := by
    intro i j
    simpa [ContinuousLinearMap.proj_apply] using
      (hasDerivAt_const t
        (ContinuousLinearMap.proj j : (q → ℝ) →L[ℝ] ℝ)).clm_apply (hAi i)
  have hxi : ∀ j : q, HasDerivAt (fun s => x s j) (xd j) t := by
    intro j
    simpa [ContinuousLinearMap.proj_apply] using
      (hasDerivAt_const t
        (ContinuousLinearMap.proj j : (q → ℝ) →L[ℝ] ℝ)).clm_apply hx
  apply hasDerivAt_pi.mpr
  intro i
  have hsum : HasDerivAt (fun s => ∑ j : q, A s i j * x s j)
      (∑ j : q, (Ad i j * x t j + A t i j * xd j)) t := by
    apply HasDerivAt.fun_sum
    intro j hj
    exact (hAij i j).mul (hxi j)
  simpa [Matrix.mulVec, dotProduct, Pi.add_apply, Finset.sum_add_distrib] using hsum

set_option linter.unusedFintypeInType false in
lemma hasDerivAt_const_matrix_mulVec
    {p q : Type*} [Fintype p] [Fintype q]
    {A : Matrix p q ℝ} {x : ℝ → (q → ℝ)}
    {xd : q → ℝ} {t : ℝ} (hx : HasDerivAt x xd t) :
    HasDerivAt (fun s => A *ᵥ x s) (A *ᵥ xd) t := by
  classical
  have hxi : ∀ j : q, HasDerivAt (fun s => x s j) (xd j) t := by
    intro j
    simpa [ContinuousLinearMap.proj_apply] using
      (hasDerivAt_const t
        (ContinuousLinearMap.proj j : (q → ℝ) →L[ℝ] ℝ)).clm_apply hx
  apply hasDerivAt_pi.mpr
  intro i
  have hsum : HasDerivAt (fun s => ∑ j : q, A i j * x s j)
      (∑ j : q, A i j * xd j) t := by
    apply HasDerivAt.fun_sum
    intro j hj
    convert (hasDerivAt_const t (A i j)).mul (hxi j) using 1
    simp
  simpa [Matrix.mulVec, dotProduct] using hsum

end Ctrllib
