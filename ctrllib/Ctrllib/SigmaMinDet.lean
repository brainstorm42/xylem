/-
σ_min(J⊕) > 0 ⟺ det J⊕ ≠ 0 — the discharge of the `hsvd` interface hypothesis of
`gamma_isUnit_iff_sigmaMin_pos` (GammaInvertible.lean, TARGET 3).

`gamma_isUnit_iff_sigmaMin_pos` takes `sigmaMin : Matrix (Fin 6) (Fin 6) ℝ → ℝ`
as a BARE function parameter and `hsvd : 0 < sigmaMin J ↔ J.det ≠ 0` as a NAMED
interface hypothesis, precisely because Mathlib's `LinearMap.singularValues` lives
on linear maps between inner-product spaces, not on matrices, and no single library
lemma packages `σ_min(matrix) > 0 ↔ det ≠ 0`. This module discharges that interface
the same way the concrete-SPD operator hypotheses were discharged for `com_attractive`
(ComLaSalleMatrix.lean): define a concrete σ_min, prove the SVD fact for it as a
theorem, and feed it in to obtain an interface-free corollary.

`sigmaMinEuclid J` is the genuine smallest singular value of the 6×6 real matrix `J`
(smallest of the `finrank`-many = index 5, since `singularValues` is antitone and
zero-indexed): the √-eigenvalues of `Jᵀ J` reached through `Matrix.toEuclideanLin`.
So the discharge is faithful, not a weaker substitute.

Discharge route (every named lemma read in the v4.31.0 .lake source):
  0 < sv 5                                  -- `sigmaMinEuclid`
    ↔ Function.Injective (toEuclideanLin J) -- `injective_iff_forall_lt_finrank_singularValues_pos`
                                            --   collapsed to index 5 by `singularValues_antitone`
    ↔ (∀ v, J *ᵥ v = 0 → v = 0)             -- transported through `ofLp`/`toLp`
    ↔ J.det ≠ 0                             -- `exists_mulVec_eq_zero_iff` (contrapositive)

SymPy pin: the corresponding local note
-/
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Ctrllib.GammaInvertible

open Matrix Module Function WithLp LinearMap

namespace Ctrllib

/-- **Concrete smallest singular value** of a 6×6 real matrix. The singular values
of `Matrix.toEuclideanLin J` are zero-indexed and antitone, so the smallest of the
`finrank = 6`-many sits at index `5`. This is a genuine σ_min (the √-eigenvalues of
`Jᵀ J`), the concrete witness that discharges the `hsvd` interface. -/
noncomputable def sigmaMinEuclid (J : Matrix (Fin 6) (Fin 6) ℝ) : ℝ :=
  (Matrix.toEuclideanLin J).singularValues 5

/-- **The discharged SVD fact** (was the interface hypothesis `hsvd`). For a 6×6
real matrix, its smallest singular value is positive exactly when it is nonsingular.
Proved outright through the `LinearMap.singularValues` API: positivity of the
smallest singular value ⟺ injectivity of the Euclidean operator ⟺ `det ≠ 0`. -/
theorem sigmaMinEuclid_pos_iff_det_ne_zero (J : Matrix (Fin 6) (Fin 6) ℝ) :
    0 < sigmaMinEuclid J ↔ J.det ≠ 0 := by
  rw [sigmaMinEuclid]
  have hfr : finrank ℝ (EuclideanSpace ℝ (Fin 6)) = 6 := finrank_euclideanSpace_fin
  -- Step 1: positivity of the smallest singular value ⟺ injectivity of the operator.
  have hinj : 0 < (Matrix.toEuclideanLin J).singularValues 5
      ↔ Function.Injective (Matrix.toEuclideanLin J) := by
    rw [injective_iff_forall_lt_finrank_singularValues_pos, hfr]
    constructor
    · intro h i hi
      exact lt_of_lt_of_le h
        ((Matrix.toEuclideanLin J).singularValues_antitone (by omega))
    · intro h
      exact h 5 (by norm_num)
  rw [hinj, injective_iff_map_eq_zero]
  -- Step 2: operator injectivity ⟺ det ≠ 0, transported through `ofLp`/`toLp`.
  rw [ne_eq, ← exists_mulVec_eq_zero_iff (M := J)]
  constructor
  · intro h
    rintro ⟨v, hv, hJv⟩
    apply hv
    have h0 : Matrix.toEuclideanLin J (toLp _ v) = 0 := by
      rw [toLpLin_apply]; simp [hJv]
    simpa using h (toLp _ v) h0
  · intro h a ha
    by_contra hane
    exact h ⟨ofLp a, by simpa using hane,
      by rw [toLpLin_apply] at ha; simpa using ha⟩

/-- **Ω-region ⟺ Γ invertible, interface-free.** Feeding the discharged fact
`sigmaMinEuclid_pos_iff_det_ne_zero` into `gamma_isUnit_iff_sigmaMin_pos` removes
the `hsvd` hypothesis entirely: with the genuine smallest singular value of the
circumcentroidal block `J⊕`, the singularity-free region Ω = {σ_min(J⊕) > 0} is
exactly the set of configurations at which the coordinated transform Γ is invertible. -/
theorem gamma_isUnit_iff_sigmaMinEuclid_pos
    (Rot : Matrix (Fin 3) (Fin 3) ℝ)
    (hRot : Rot ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (T : Matrix (Fin 3) ((Fin 3) ⊕ (Fin 6)) ℝ)
    (G : Matrix (Fin 6) (Fin 3) ℝ) (J : Matrix (Fin 6) (Fin 6) ℝ) :
    0 < sigmaMinEuclid J
      ↔ IsUnit (fromBlocks Rot T 0 (fromBlocks (1 : Matrix (Fin 3) (Fin 3) ℝ) 0 G J)) :=
  gamma_isUnit_iff_sigmaMin_pos sigmaMinEuclid Rot hRot T G J
    (sigmaMinEuclid_pos_iff_det_ne_zero J)

end Ctrllib

#print axioms Ctrllib.sigmaMinEuclid_pos_iff_det_ne_zero
#print axioms Ctrllib.gamma_isUnit_iff_sigmaMinEuclid_pos
