/-
Euclidean induced-norm bridges for the square real-matrix lane.

The lower-bound input is deliberately the already-proved Rayleigh API rather
than a new eigenvalue/norm theorem (`Rayleigh.le_dotProduct_mulVec`).  The matrix
operator is `toEuclideanCLM`, matching the synced operator vocabulary and its
`ofLp_toEuclideanCLM` transport (CoupledCollapseMatrix).
The singular-value index below is Mathlib's `Fin (finrank ...)` index, not the
fixed `Fin 6` witness in SigmaMinDet; this avoids importing a fixed-dimensional
sigma-min convention.  The Tikhonov/SVD identities that produce the bound live
in TikhonovSVD and are intentionally not redrafted here.

Human derivation: the corresponding derivation record (not bundled)
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.CStarAlgebra.Matrix
import Ctrllib.Rayleigh

open Matrix
open scoped InnerProductSpace

namespace Ctrllib

variable {n : Type*} [Fintype n] [DecidableEq n]

/--
Matrix multiplication is composition after transporting through
`toEuclideanCLM`.  This is the algebraic half of the requested operator-norm
bridge; the `mulVec` transport is the same one used by the synced concrete
operator proofs (`CoupledCollapseMatrix.lean:80-84`; `Rayleigh.lean:39-41`).
-/
theorem euclideanCLM_mul (A B : Matrix n n ℝ) :
    toEuclideanCLM (𝕜 := ℝ) (A * B) =
      (toEuclideanCLM (𝕜 := ℝ) A).comp
        (toEuclideanCLM (𝕜 := ℝ) B) := by
  ext x i
  -- `ofLp_toEuclideanCLM` and `mulVec_mulVec` are simp lemmas; componentwise
  -- both sides reduce to `((A * B) *ᵥ x.ofLp) i`.
  simp [ContinuousLinearMap.comp_apply]

/--
Submultiplicativity of the Euclidean operator norm, written at matrix level.
This is the fact needed by the Prop-3 norm estimates (TikhonovProp3).
-/
theorem euclideanCLM_norm_mul_le (A B : Matrix n n ℝ) :
    ‖toEuclideanCLM (𝕜 := ℝ) (A * B)‖ ≤
      ‖toEuclideanCLM (𝕜 := ℝ) A‖ * ‖toEuclideanCLM (𝕜 := ℝ) B‖ := by
  rw [euclideanCLM_mul]
  -- MATHLIB: `ContinuousLinearMap.opNorm_comp_le` (exists).
  exact ContinuousLinearMap.opNorm_comp_le _ _

/--
Transpose preserves the Euclidean induced operator norm.  The raw inner
product identity is the calculation already present in the synced house style
(`CoupledCollapseMatrix.lean:61-66`); the remaining step is the adjoint/norm
packaging.
-/
theorem euclideanCLM_transpose_norm_eq (M : Matrix n n ℝ) :
    ‖toEuclideanCLM (𝕜 := ℝ) Mᵀ‖ =
      ‖toEuclideanCLM (𝕜 := ℝ) M‖ := by
  rw [Matrix.l2_opNorm_toEuclideanCLM (𝕜 := ℝ) Mᵀ,
    Matrix.l2_opNorm_toEuclideanCLM (𝕜 := ℝ) M]
  simpa only [conjTranspose_eq_transpose_of_trivial] using
    (Matrix.l2_opNorm_conjTranspose (𝕜 := ℝ) M)

/--
If a real symmetric matrix has all eigenvalues at least `c^2`, its inverse
Euclidean operator norm is at most `1 / c^2`.  The proof lifts
`le_dotProduct_mulVec` (`Rayleigh.lean:82-87`) to a pointwise norm estimate,
uses the unit-matrix inverse identity, and closes with the continuous-linear-map
operator-norm bound.  The hypotheses and conclusion are exactly the API the
Tikhonov lane consumes.
-/
theorem euclideanCLM_inv_norm_le_of_isHermitian_eigenvalue_floor
    {K : Matrix n n ℝ} (hK : K.IsHermitian) (hKunit : IsUnit K)
    {c : ℝ} (hc : 0 < c)
    (hfloor : ∀ i, c ^ 2 ≤ hK.eigenvalues i) :
    ‖toEuclideanCLM (𝕜 := ℝ) K⁻¹‖ ≤ 1 / c ^ 2 := by
  have hquad (x : EuclideanSpace ℝ n) :
      c ^ 2 * ‖x‖ ^ 2 ≤
        ⟪x, toEuclideanCLM (𝕜 := ℝ) K x⟫_ℝ := by
    -- MATHLIB: `le_dotProduct_mulVec` is the synced theorem, not a
    -- re-proved spectral assertion (`Rayleigh.lean:82-87`).
    have h := le_dotProduct_mulVec hK hfloor (WithLp.ofLp x)
    -- MATHLIB: `real_inner_self_eq_norm_sq`,
    -- `EuclideanSpace.inner_eq_star_dotProduct`, and `star_trivial` (exists;
    -- the same rewrite is used by `Rayleigh.lean:119-120`).
    have hnorm : ‖x‖ ^ 2 =
        WithLp.ofLp x ⬝ᵥ WithLp.ofLp x := by
      rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct,
        star_trivial]
    calc
      c ^ 2 * ‖x‖ ^ 2 =
          c ^ 2 * (WithLp.ofLp x ⬝ᵥ WithLp.ofLp x) := by rw [hnorm]
      _ ≤ WithLp.ofLp x ⬝ᵥ K *ᵥ WithLp.ofLp x := h
      _ = ⟪x, toEuclideanCLM (𝕜 := ℝ) K x⟫_ℝ :=
        (inner_toEuclideanCLM K x x).symm
  have hKM : K * K⁻¹ = (1 : Matrix n n ℝ) :=
    Matrix.mul_nonsing_inv K ((Matrix.isUnit_iff_isUnit_det K).mp hKunit)
  have hpoint (x : EuclideanSpace ℝ n) :
      ‖toEuclideanCLM (𝕜 := ℝ) K⁻¹ x‖ ≤ (1 / c ^ 2) * ‖x‖ := by
    let y : EuclideanSpace ℝ n := toEuclideanCLM (𝕜 := ℝ) K⁻¹ x
    change ‖y‖ ≤ (1 / c ^ 2) * ‖x‖
    have hxy : toEuclideanCLM (𝕜 := ℝ) K y = x := by
      -- MATHLIB: `WithLp.ofLp_injective` (exists; used by
      -- `CoupledCollapseMatrix.lean:80-84`).
      apply WithLp.ofLp_injective
      rw [ofLp_toEuclideanCLM, ofLp_toEuclideanCLM, mulVec_mulVec,
        hKM, one_mulVec]
    have hquad_y : c ^ 2 * ‖y‖ ^ 2 ≤ ⟪y, x⟫_ℝ := by
      calc
        c ^ 2 * ‖y‖ ^ 2 ≤
            ⟪y, toEuclideanCLM (𝕜 := ℝ) K y⟫_ℝ := hquad y
        _ = ⟪y, x⟫_ℝ := by rw [hxy]
    -- MATHLIB: `real_inner_le_norm` (exists).
    have hcs : ⟪y, x⟫_ℝ ≤ ‖y‖ * ‖x‖ :=
      real_inner_le_norm _ _
    by_cases hy : ‖y‖ = 0
    · rw [hy]
      positivity
    -- MATHLIB: `norm_nonneg` and `lt_of_le_of_ne` (exists).
    have hypos : 0 < ‖y‖ :=
      lt_of_le_of_ne (norm_nonneg y) (Ne.symm hy)
    have hcancel : c ^ 2 * ‖y‖ ≤ ‖x‖ := by
      have h2 : ‖y‖ * (c ^ 2 * ‖y‖) ≤ ‖y‖ * ‖x‖ := by
        calc
          ‖y‖ * (c ^ 2 * ‖y‖) = c ^ 2 * ‖y‖ ^ 2 := by ring
          _ ≤ ⟪y, x⟫_ℝ := hquad_y
          _ ≤ ‖y‖ * ‖x‖ := hcs
      exact le_of_mul_le_mul_left h2 hypos
    -- MATHLIB: `sq_pos_of_pos` and `le_div_iff₀` (exists).
    calc
      ‖y‖ ≤ ‖x‖ / c ^ 2 := by
        apply (le_div_iff₀ (sq_pos_of_pos hc)).2
        simpa [mul_comm] using hcancel
      _ = (1 / c ^ 2) * ‖x‖ := by ring
  -- MATHLIB: `ContinuousLinearMap.opNorm_le_bound` (exists).
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) ?_
  intro x
  simpa [mul_comm] using hpoint x

/--
Lift a uniform bound on a named singular-value list to the Euclidean operator
norm of a square real matrix.  Mathlib's singular values are indexed by
`Fin (Module.finrank ℝ (EuclideanSpace ℝ n))`; `hσ` identifies the caller's `σ` with
that list, and `hbound` is the requested `∀ i, σ i ≤ b`.  The nonempty index
assumption is intentional: it is used for the finite spectrum, and it prevents a
vacuous bound with a negative `b`.
-/
theorem euclideanCLM_norm_le_of_singular_value_bound
    [Nonempty n] (M : Matrix n n ℝ)
    (σ : Fin (Module.finrank ℝ (EuclideanSpace ℝ n)) → ℝ) (b : ℝ)
    (hσ : ∀ i, σ i = (Matrix.toEuclideanLin M).singularValues i)
    (hbound : ∀ i, σ i ≤ b) :
    ‖toEuclideanCLM (𝕜 := ℝ) M‖ ≤ b := by
  have hbound' : ∀ i : Fin (Module.finrank ℝ (EuclideanSpace ℝ n)),
      (Matrix.toEuclideanLin M).singularValues i ≤ b := by
    intro i
    rw [← hσ i]
    exact hbound i
  -- Route: `‖T x‖² = ⟪x, (T† ∘ T) x⟫` (`LinearMap.adjoint_inner_right`), the Gram
  -- operator `T† ∘ T` is symmetric (`LinearMap.isSymmetric_adjoint_comp_self`,
  -- `Mathlib/Analysis/InnerProductSpace/Adjoint.lean:735`), its eigenvalues are the
  -- squared singular values (`LinearMap.sq_singularValues_fin`,
  -- `Mathlib/Analysis/InnerProductSpace/SingularValues.lean:127-129`), and the
  -- eigenvector orthonormal basis diagonalizes the quadratic form
  -- (`LinearMap.IsSymmetric.eigenvectorBasis_apply_self_apply`,
  -- `Mathlib/Analysis/InnerProductSpace/Spectrum.lean:332-335`).  Mathlib has no
  -- single largest-singular-value/operator-norm declaration; this assembles one.
  set T := Matrix.toEuclideanLin (𝕜 := ℝ) M with hTdef
  have hpos : 0 < Module.finrank ℝ (EuclideanSpace ℝ n) := by
    rw [finrank_euclideanSpace]
    exact Fintype.card_pos
  have hb : 0 ≤ b := le_trans (T.singularValues_nonneg _) (hbound' ⟨0, hpos⟩)
  have hSsym : (LinearMap.adjoint T ∘ₗ T).IsSymmetric := T.isSymmetric_adjoint_comp_self
  have hlam : ∀ i : Fin (Module.finrank ℝ (EuclideanSpace ℝ n)),
      hSsym.eigenvalues rfl i ≤ b ^ 2 := by
    intro i
    rw [← T.sq_singularValues_fin rfl i]
    nlinarith [T.singularValues_nonneg (i : ℕ), hbound' i]
  set e := hSsym.eigenvectorBasis (n := Module.finrank ℝ (EuclideanSpace ℝ n)) rfl with hedef
  have key : ∀ x : EuclideanSpace ℝ n, ‖T x‖ ^ 2 ≤ b ^ 2 * ‖x‖ ^ 2 := by
    intro x
    have hTT : ‖T x‖ ^ 2 = ⟪x, (LinearMap.adjoint T ∘ₗ T) x⟫_ℝ := by
      rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]
    have hinner : ⟪x, (LinearMap.adjoint T ∘ₗ T) x⟫_ℝ
        = ∑ i, hSsym.eigenvalues rfl i * (e.repr x i) ^ 2 := by
      rw [← e.repr.inner_map_map x ((LinearMap.adjoint T ∘ₗ T) x)]
      simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hedef, LinearMap.IsSymmetric.eigenvectorBasis_apply_self_apply]
      simp only [RCLike.ofReal_real_eq_id, id_eq]
      ring
    have hnormx : ‖x‖ ^ 2 = ∑ i, (e.repr x i) ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, ← e.repr.inner_map_map x x]
      simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
      exact Finset.sum_congr rfl fun i _ => (sq _).symm
    rw [hTT, hinner, hnormx, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (hlam i) (sq_nonneg _)
  refine ContinuousLinearMap.opNorm_le_bound _ hb fun x => ?_
  have hcoe : toEuclideanCLM (𝕜 := ℝ) M x = T x := rfl
  rw [hcoe]
  nlinarith [key x, norm_nonneg (T x), mul_nonneg hb (norm_nonneg x)]

/--
**Operator-norm bound from an indexed orthogonal SVD.**  If `M = U · diagonal d · Vᵀ`
with `Uᵀ U = 1` and `V Vᵀ = 1`, and every `|d i|` is at most `b`, then the Euclidean
operator norm of `M` is at most `b`.

This is the companion of `euclideanCLM_norm_le_of_singular_value_bound` for the
`n`-indexed SVD interface, and it is the one the Tikhonov transports feed:
`tikhonov_plus_singular_values` and `tikhonov_squared_transpose_singular_values`
(`TikhonovSVD.lean`) produce exactly this factored shape, whereas Mathlib's
`LinearMap.singularValues` is a sorted `ℕ`-indexed list with no pointwise link to an
arbitrary `Fintype` index.  Without this theorem the two APIs do not compose.
-/
theorem euclideanCLM_norm_le_of_conj_diagonal
    {M U V : Matrix n n ℝ} {d : n → ℝ} {b : ℝ}
    (hUtU : Uᵀ * U = (1 : Matrix n n ℝ)) (hVVt : V * Vᵀ = 1)
    (hM : M = U * diagonal d * Vᵀ) (hb : 0 ≤ b) (hd : ∀ i, |d i| ≤ b) :
    ‖toEuclideanCLM (𝕜 := ℝ) M‖ ≤ b := by
  -- An orthogonal factor preserves the dot-product square.
  have horth : ∀ P : Matrix n n ℝ, Pᵀ * P = 1 →
      ∀ w : n → ℝ, (P *ᵥ w) ⬝ᵥ (P *ᵥ w) = w ⬝ᵥ w := by
    intro P hP w
    rw [dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, hP, one_mulVec]
  have hnormsq : ∀ w : EuclideanSpace ℝ n,
      ‖w‖ ^ 2 = WithLp.ofLp w ⬝ᵥ WithLp.ofLp w := by
    intro w
    rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  refine ContinuousLinearMap.opNorm_le_bound _ hb fun x => ?_
  set z : n → ℝ := WithLp.ofLp x with hz
  set y : n → ℝ := Vᵀ *ᵥ z with hy
  have hMz : M *ᵥ z = U *ᵥ (diagonal d *ᵥ y) := by
    rw [hM, hy, mulVec_mulVec, mulVec_mulVec]
  have hsq : ‖toEuclideanCLM (𝕜 := ℝ) M x‖ ^ 2 ≤ b ^ 2 * ‖x‖ ^ 2 := by
    have hlhs : ‖toEuclideanCLM (𝕜 := ℝ) M x‖ ^ 2 = (M *ᵥ z) ⬝ᵥ (M *ᵥ z) := by
      rw [hnormsq, ofLp_toEuclideanCLM]
    have hyy : y ⬝ᵥ y = z ⬝ᵥ z := by
      have := horth Vᵀ (by rw [transpose_transpose]; exact hVVt) z
      rw [hy]
      exact this
    have hdiag : (diagonal d *ᵥ y) ⬝ᵥ (diagonal d *ᵥ y) ≤ b ^ 2 * (y ⬝ᵥ y) := by
      simp only [dotProduct, mulVec_diagonal, Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      have hdi : d i ^ 2 ≤ b ^ 2 := by
        have := hd i
        nlinarith [abs_nonneg (d i), sq_abs (d i)]
      nlinarith [hdi, mul_self_nonneg (y i)]
    rw [hlhs, hMz, horth U hUtU, hnormsq x, ← hz, ← hyy]
    exact hdiag
  nlinarith [hsq, norm_nonneg (toEuclideanCLM (𝕜 := ℝ) M x),
    mul_nonneg hb (norm_nonneg x)]

end Ctrllib

#print axioms Ctrllib.euclideanCLM_mul
#print axioms Ctrllib.euclideanCLM_norm_mul_le
#print axioms Ctrllib.euclideanCLM_transpose_norm_eq
#print axioms Ctrllib.euclideanCLM_inv_norm_le_of_isHermitian_eigenvalue_floor
#print axioms Ctrllib.euclideanCLM_norm_le_of_singular_value_bound
#print axioms Ctrllib.euclideanCLM_norm_le_of_conj_diagonal
