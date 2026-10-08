/-
Generic square-matrix Tikhonov/SVD API for a general finite index.

The square scope and the three displayed Tikhonov expressions follow
the corresponding local note and the corresponding local note.  `Alam` and `Blam` retain the
notation of the corresponding local note.  The scalar floor uses the direct
inequality required by the corresponding local note and checked in
the corresponding local note, not a branch split.

The SVD hypotheses below use an indexed real square SVD (orthogonal factors and
an `n`-indexed nonnegative diagonal).  This avoids pretending that the
Nat-indexed, antitone `LinearMap.singularValues` API is pointwise aligned with
an arbitrary `Fintype` index; that API is the one actually used in
`SigmaMinDet.lean:37-59`.  The `toEuclideanCLM` norm bridges are intentionally
not duplicated: the prior lane marks them as a sibling API at
the corresponding local note, and the corresponding local note says to treat them
as available by name.
-/
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Ctrllib.Rayleigh

open Matrix

namespace Ctrllib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The regularized right Gram matrix from the corresponding local note. -/
def Alam (Γ : Matrix n n ℝ) (lam : ℝ) : Matrix n n ℝ :=
  Γᵀ * Γ + lam • (1 : Matrix n n ℝ)

/-- The regularized left Gram matrix from the corresponding local note. -/
def Blam (Γ : Matrix n n ℝ) (lam : ℝ) : Matrix n n ℝ :=
  Γ * Γᵀ + lam • (1 : Matrix n n ℝ)

omit [DecidableEq n] in
/-- Conjugating a quadratic form by a square matrix is the change of variables
`x ↦ Pᵀ x`.  Pure ring identity, no orthogonality (the public counterpart of the
private `quad_conj` in `Rayleigh.lean:38-40`). -/
theorem dotProduct_conj_mulVec (P M : Matrix n n ℝ) (x : n → ℝ) :
    x ⬝ᵥ (P * M * Pᵀ) *ᵥ x = (Pᵀ *ᵥ x) ⬝ᵥ M *ᵥ (Pᵀ *ᵥ x) := by
  rw [mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose]

/-- **Converse Rayleigh floor.**  A uniform quadratic-form floor forces a uniform
eigenvalue floor.  This is the direction `Rayleigh.lean:82-87` does not supply:
`le_dotProduct_mulVec` goes from eigenvalues to the form, this goes back.  The
proof evaluates the form at the orthonormal eigenvector
(`Matrix.IsHermitian.mulVec_eigenvectorBasis`, `Analysis/Matrix/Spectrum.lean:73-78`). -/
theorem le_eigenvalues_of_le_dotProduct_mulVec {K : Matrix n n ℝ} (hK : K.IsHermitian)
    {c : ℝ} (h : ∀ x : n → ℝ, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ K *ᵥ x) (i : n) :
    c ≤ hK.eigenvalues i := by
  set v : n → ℝ := ⇑(hK.eigenvectorBasis i) with hv
  have hvv : v ⬝ᵥ v = 1 := by
    have hn1 : ‖(hK.eigenvectorBasis i : EuclideanSpace ℝ n)‖ = 1 :=
      hK.eigenvectorBasis.orthonormal.1 i
    have hsq : ‖(hK.eigenvectorBasis i : EuclideanSpace ℝ n)‖ ^ 2 = v ⬝ᵥ v := by
      rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
    rw [← hsq, hn1, one_pow]
  have hKv : K *ᵥ v = hK.eigenvalues i • v := hK.mulVec_eigenvectorBasis i
  have hle := h v
  rw [hKv, dotProduct_smul, hvv, smul_eq_mul, mul_one, mul_one] at hle
  exact hle

/-- **Orthogonal-conjugate eigenvalue floor.**  If a Hermitian `K` is presented as
`P · diagonal d · Pᵀ` with `P Pᵀ = 1` and every `d i` is at least `c`, then every
eigenvalue of `K` is at least `c`.  This is the Gram-spectrum transport the two
holes below need, stated once for both Grams. -/
theorem le_eigenvalues_of_conj_diagonal
    {K P : Matrix n n ℝ} {d : n → ℝ} {c : ℝ} (hK : K.IsHermitian)
    (hPPt : P * Pᵀ = 1) (hKeq : K = P * diagonal d * Pᵀ)
    (hd : ∀ i, c ≤ d i) (i : n) :
    c ≤ hK.eigenvalues i := by
  refine le_eigenvalues_of_le_dotProduct_mulVec hK (fun x => ?_) i
  have hxx : x ⬝ᵥ x = (Pᵀ *ᵥ x) ⬝ᵥ (Pᵀ *ᵥ x) := by
    have h1 := dotProduct_conj_mulVec P 1 x
    rw [mul_one, hPPt, one_mulVec, one_mulVec] at h1
    exact h1
  rw [hKeq, dotProduct_conj_mulVec, hxx]
  set y : n → ℝ := Pᵀ *ᵥ x with hy
  simp only [dotProduct, mulVec_diagonal, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  nlinarith [hd j, mul_self_nonneg (y j)]

/-- The regularized right Gram matrix of an indexed square SVD is the orthogonal
conjugate of `diagonal (σ² + lam)` by the right factor `V`. -/
theorem alam_conj_eq (Γ : Matrix n n ℝ) (σ : n → ℝ) (lam : ℝ)
    {U V : Matrix n n ℝ} (hUtU : Uᵀ * U = (1 : Matrix n n ℝ)) (hVVt : V * Vᵀ = 1)
    (hΓ : Γ = U * diagonal σ * Vᵀ) :
    Alam Γ lam = V * diagonal (fun i => σ i ^ 2 + lam) * Vᵀ := by
  have hsplit : diagonal (fun i => σ i ^ 2 + lam)
      = diagonal σ * diagonal σ + lam • (1 : Matrix n n ℝ) := by
    rw [diagonal_mul_diagonal]
    ext i j
    rcases eq_or_ne i j with h | h
    · subst h; simp [sq]
    · simp [diagonal_apply_ne _ h, Matrix.one_apply_ne h]
  have hΓt : Γᵀ = V * diagonal σ * Uᵀ := by
    rw [hΓ, transpose_mul, transpose_mul, transpose_transpose, diagonal_transpose, mul_assoc]
  rw [Alam, hΓt, hΓ, hsplit, Matrix.mul_add, Matrix.add_mul]
  congr 1
  · calc V * diagonal σ * Uᵀ * (U * diagonal σ * Vᵀ)
        = V * diagonal σ * (Uᵀ * U) * diagonal σ * Vᵀ := by
          simp only [Matrix.mul_assoc]
    _ = V * (diagonal σ * diagonal σ) * Vᵀ := by
          rw [hUtU, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
  · rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hVVt]

/-- The regularized left Gram matrix of an indexed square SVD is the orthogonal
conjugate of `diagonal (σ² + lam)` by the left factor `U`. -/
theorem blam_conj_eq (Γ : Matrix n n ℝ) (σ : n → ℝ) (lam : ℝ)
    {U V : Matrix n n ℝ} (hVtV : Vᵀ * V = (1 : Matrix n n ℝ)) (hUUt : U * Uᵀ = 1)
    (hΓ : Γ = U * diagonal σ * Vᵀ) :
    Blam Γ lam = U * diagonal (fun i => σ i ^ 2 + lam) * Uᵀ := by
  have hΓt : Γᵀ = V * diagonal σ * Uᵀ := by
    rw [hΓ, transpose_mul, transpose_mul, transpose_transpose, diagonal_transpose, mul_assoc]
  have hrewrite : Blam Γ lam = Alam Γᵀ lam := by
    rw [Alam, Blam, transpose_transpose]
  rw [hrewrite]
  exact alam_conj_eq Γᵀ σ lam hVtV hUUt (by rw [hΓt])

/-- The inverse of the regularized right Gram matrix, in closed form.  The
nonvanishing hypothesis `hne` is exactly what the eigenvalue floor supplies, so
`IsUnit (Alam Γ lam)` is not needed as an input: invertibility is a conclusion. -/
theorem alam_inv_eq (Γ : Matrix n n ℝ) (σ : n → ℝ) (lam : ℝ)
    {U V : Matrix n n ℝ} (hUtU : Uᵀ * U = (1 : Matrix n n ℝ))
    (hVtV : Vᵀ * V = (1 : Matrix n n ℝ)) (hVVt : V * Vᵀ = 1)
    (hΓ : Γ = U * diagonal σ * Vᵀ) (hne : ∀ i, σ i ^ 2 + lam ≠ 0) :
    (Alam Γ lam)⁻¹ = V * diagonal (fun i => (σ i ^ 2 + lam)⁻¹) * Vᵀ := by
  refine Matrix.inv_eq_right_inv ?_
  rw [alam_conj_eq Γ σ lam hUtU hVVt hΓ]
  calc V * diagonal (fun i => σ i ^ 2 + lam) * Vᵀ
        * (V * diagonal (fun i => (σ i ^ 2 + lam)⁻¹) * Vᵀ)
      = V * (diagonal (fun i => σ i ^ 2 + lam) * (Vᵀ * V)
          * diagonal (fun i => (σ i ^ 2 + lam)⁻¹)) * Vᵀ := by
        simp only [Matrix.mul_assoc]
  _ = 1 := by
        rw [hVtV, Matrix.mul_one, diagonal_mul_diagonal]
        have hone : (fun i => (σ i ^ 2 + lam) * (σ i ^ 2 + lam)⁻¹) = (1 : n → ℝ) := by
          funext i
          simp [mul_inv_cancel₀ (hne i)]
        rw [hone]
        simp [hVVt]

/--
**Tikhonov Gram eigenvalue floor.**  If `lambda` is the scheduled maximum and
`σG` is a nonnegative lower bound for every nonnegative singular-value label,
then every labeled denominator is at least `s^2`; the last two conjuncts are
the corresponding eigenvalue floors for `Alam` and `Blam`.

The scalar part is proved by
`σ i ^ 2 + lam ≥ σ i ^ 2 + s ^ 2 - sigmaG ^ 2 ≥ s ^ 2`, as required by
the corresponding local note and the corresponding local note.  The explicit indexed SVD
argument is the generic replacement for the fixed `Fin 6` interface described
in `GammaInvertible.lean:86-95` and `SigmaMinDet.lean:37-49`.
-/
theorem tikhonov_gram_eigenvalue_floor
    (Γ : Matrix n n ℝ) (σ : n → ℝ)
    (β s sigmaG lam : ℝ)
    (hlam : lam = max (β ^ 2) (s ^ 2 - sigmaG ^ 2))
    (hσG : 0 ≤ sigmaG)
    (hσ : ∀ i, 0 ≤ σ i)
    (hσG_le : ∀ i, sigmaG ≤ σ i)
    (hsvd : ∃ U V : Matrix n n ℝ,
      Uᵀ * U = (1 : Matrix n n ℝ) ∧
      U * Uᵀ = 1 ∧
      Vᵀ * V = 1 ∧
      V * Vᵀ = 1 ∧
      Γ = U * diagonal σ * Vᵀ)
    (hA : (Alam Γ lam).IsHermitian)
    (hB : (Blam Γ lam).IsHermitian) :
    (∀ i, s ^ 2 ≤ σ i ^ 2 + lam) ∧
      (∀ i, s ^ 2 ≤ hA.eigenvalues i) ∧
      (∀ i, s ^ 2 ≤ hB.eigenvalues i) := by
  have hlam_floor : s ^ 2 - sigmaG ^ 2 ≤ lam := by
    rw [hlam]
    exact le_max_right _ _
  have hfloor : ∀ i, s ^ 2 ≤ σ i ^ 2 + lam := by
    intro i
    have hsq : sigmaG ^ 2 ≤ σ i ^ 2 := by
      have hdiff : 0 ≤ σ i - sigmaG := sub_nonneg.mpr (hσG_le i)
      have hsum : 0 ≤ σ i + sigmaG := by
        nlinarith [hσ i, hσG]
      have hprod : 0 ≤ (σ i - sigmaG) * (σ i + sigmaG) :=
        mul_nonneg hdiff hsum
      nlinarith [hprod]
    -- The requested direct estimate, with no two-regime split.
    nlinarith [hlam_floor, hsq]
  refine ⟨hfloor, ?_⟩
  obtain ⟨U, V, hUtU, hUUt, hVtV, hVVt, hΓ⟩ := hsvd
  constructor
  · -- Right Gram: `Alam Γ lam = V · diagonal (σ² + lam) · Vᵀ`, then the
    -- orthogonal-conjugate eigenvalue floor.
    exact fun i =>
      le_eigenvalues_of_conj_diagonal hA hVVt
        (alam_conj_eq Γ σ lam hUtU hVVt hΓ) hfloor i
  · -- Left Gram: the same statement conjugated by `U` instead of `V`.
    exact fun i =>
      le_eigenvalues_of_conj_diagonal hB hUUt
        (blam_conj_eq Γ σ lam hVtV hUUt hΓ) hfloor i

/--
**Tikhonov plus singular values.**  Under an indexed square SVD of `Γ`, the
matrix `(Alam Γ lam)⁻¹ * Γᵀ` has the same orthogonal-factor form with diagonal
entries `σ i / (σ i ^ 2 + lam)`.  The first conjunct records their
nonnegativity, so the existential is an actual SVD labeling rather than an
unsigned diagonalization.  This is the generic-`Fintype` version of the
missing API identified at the corresponding local note; the fixed `Fin 6`
`sigmaMinEuclid` witness is deliberately not reused (`SigmaMinDet.lean:37-49`).
-/
theorem tikhonov_plus_singular_values
    (Γ : Matrix n n ℝ) (σ : n → ℝ) (s lam : ℝ)
    (hs : 0 < s)
    (hσ : ∀ i, 0 ≤ σ i)
    (hfloor : ∀ i, s ^ 2 ≤ σ i ^ 2 + lam)
    (hsvd : ∃ U V : Matrix n n ℝ,
      Uᵀ * U = (1 : Matrix n n ℝ) ∧
      U * Uᵀ = 1 ∧
      Vᵀ * V = 1 ∧
      V * Vᵀ = 1 ∧
      Γ = U * diagonal σ * Vᵀ)
    (hAunit : IsUnit (Alam Γ lam)) :
    (∀ i, 0 ≤ σ i / (σ i ^ 2 + lam)) ∧
      ∃ U V : Matrix n n ℝ,
        Uᵀ * U = (1 : Matrix n n ℝ) ∧
        U * Uᵀ = 1 ∧
        Vᵀ * V = 1 ∧
        V * Vᵀ = 1 ∧
        (Alam Γ lam)⁻¹ * Γᵀ =
          U * diagonal (fun i => σ i / (σ i ^ 2 + lam)) * Vᵀ := by
  have hden : ∀ i, 0 < σ i ^ 2 + lam := by
    intro i
    exact lt_of_lt_of_le (sq_pos_of_pos hs) (hfloor i)
  have hnonneg : ∀ i, 0 ≤ σ i / (σ i ^ 2 + lam) := by
    intro i
    exact div_nonneg (hσ i) (le_of_lt (hden i))
  refine ⟨hnonneg, ?_⟩
  obtain ⟨U, V, hUtU, hUUt, hVtV, hVVt, hΓ⟩ := hsvd
  have hinv := alam_inv_eq Γ σ lam hUtU hVtV hVVt hΓ (fun i => (hden i).ne')
  have hΓt : Γᵀ = V * diagonal σ * Uᵀ := by
    rw [hΓ, transpose_mul, transpose_mul, transpose_transpose, diagonal_transpose, mul_assoc]
  refine ⟨V, U, hVtV, hVVt, hUtU, hUUt, ?_⟩
  rw [hinv, hΓt]
  calc V * diagonal (fun i => (σ i ^ 2 + lam)⁻¹) * Vᵀ * (V * diagonal σ * Uᵀ)
      = V * (diagonal (fun i => (σ i ^ 2 + lam)⁻¹) * (Vᵀ * V) * diagonal σ) * Uᵀ := by
        simp only [Matrix.mul_assoc]
  _ = V * diagonal (fun i => σ i / (σ i ^ 2 + lam)) * Uᵀ := by
        rw [hVtV, Matrix.mul_one, diagonal_mul_diagonal]
        congr 2
        funext i
        simp [div_eq_inv_mul]

/--
**Tikhonov squared-transpose singular values.**  Under the same generic square
SVD interface, `(Alam Γ lam)⁻¹ * (Alam Γ lam)⁻¹ * Γᵀ` has diagonal entries
`σ i / (σ i ^ 2 + lam) ^ 2`.  The statement is the matrix-level SVD interface
that the scalar squared bound and the sibling `toEuclideanCLM` norm bridge
consume; its missing transport is the item-3 hole at
the corresponding local note.
-/
theorem tikhonov_squared_transpose_singular_values
    (Γ : Matrix n n ℝ) (σ : n → ℝ) (s lam : ℝ)
    (hs : 0 < s)
    (hσ : ∀ i, 0 ≤ σ i)
    (hfloor : ∀ i, s ^ 2 ≤ σ i ^ 2 + lam)
    (hsvd : ∃ U V : Matrix n n ℝ,
      Uᵀ * U = (1 : Matrix n n ℝ) ∧
      U * Uᵀ = 1 ∧
      Vᵀ * V = 1 ∧
      V * Vᵀ = 1 ∧
      Γ = U * diagonal σ * Vᵀ)
    (hAunit : IsUnit (Alam Γ lam)) :
    (∀ i, 0 ≤ σ i / (σ i ^ 2 + lam) ^ 2) ∧
      ∃ U V : Matrix n n ℝ,
        Uᵀ * U = (1 : Matrix n n ℝ) ∧
        U * Uᵀ = 1 ∧
        Vᵀ * V = 1 ∧
        V * Vᵀ = 1 ∧
        (Alam Γ lam)⁻¹ * (Alam Γ lam)⁻¹ * Γᵀ =
          U * diagonal (fun i => σ i / (σ i ^ 2 + lam) ^ 2) * Vᵀ := by
  have hden : ∀ i, 0 < σ i ^ 2 + lam := by
    intro i
    exact lt_of_lt_of_le (sq_pos_of_pos hs) (hfloor i)
  have hnonneg : ∀ i, 0 ≤ σ i / (σ i ^ 2 + lam) ^ 2 := by
    intro i
    exact div_nonneg (hσ i) (sq_nonneg (σ i ^ 2 + lam))
  refine ⟨hnonneg, ?_⟩
  obtain ⟨U, V, hUtU, hUUt, hVtV, hVVt, hΓ⟩ := hsvd
  have hinv := alam_inv_eq Γ σ lam hUtU hVtV hVVt hΓ (fun i => (hden i).ne')
  have hΓt : Γᵀ = V * diagonal σ * Uᵀ := by
    rw [hΓ, transpose_mul, transpose_mul, transpose_transpose, diagonal_transpose, mul_assoc]
  refine ⟨V, U, hVtV, hVVt, hUtU, hUUt, ?_⟩
  rw [hinv, hΓt]
  calc V * diagonal (fun i => (σ i ^ 2 + lam)⁻¹) * Vᵀ
        * (V * diagonal (fun i => (σ i ^ 2 + lam)⁻¹) * Vᵀ) * (V * diagonal σ * Uᵀ)
      = V * (diagonal (fun i => (σ i ^ 2 + lam)⁻¹) * (Vᵀ * V)
          * diagonal (fun i => (σ i ^ 2 + lam)⁻¹) * (Vᵀ * V) * diagonal σ) * Uᵀ := by
        simp only [Matrix.mul_assoc]
  _ = V * diagonal (fun i => σ i / (σ i ^ 2 + lam) ^ 2) * Uᵀ := by
        rw [hVtV, Matrix.mul_one, Matrix.mul_one, diagonal_mul_diagonal, diagonal_mul_diagonal]
        congr 2
        funext i
        field_simp

/--
**Scalar plus bound.**  If `0 < s`, `0 ≤ σ`, `0 ≤ lam`, and
`s ^ 2 ≤ σ ^ 2 + lam`, then `σ / (σ ^ 2 + lam) ≤ 1 / s`.  The extra `0 ≤ lam` is
mathematically necessary and is supplied by the max schedule; see
the corresponding local note and the counterexample recorded in this
lane's FLAGS.
-/
theorem tikhonov_plus_scalar_bound
    {s σ lam : ℝ}
    (hs : 0 < s) (hlam : 0 ≤ lam) (hσ : 0 ≤ σ)
    (hfloor : s ^ 2 ≤ σ ^ 2 + lam) :
    σ / (σ ^ 2 + lam) ≤ 1 / s := by
  have hden : 0 < σ ^ 2 + lam :=
    lt_of_lt_of_le (sq_pos_of_pos hs) hfloor
  -- MATHLIB: exists: ordered-field cross multiplication, exposed as
  -- `div_le_div_iff₀`; the remaining steps are polynomial inequalities.
  apply (div_le_div_iff₀ hden hs).2
  rcases le_total s σ with hss | hσs
  · have hprod : 0 ≤ σ * (σ - s) :=
      mul_nonneg hσ (sub_nonneg.mpr hss)
    nlinarith [hprod, hlam]
  · have hprod : 0 ≤ (s - σ) * s :=
      mul_nonneg (sub_nonneg.mpr hσs) (le_of_lt hs)
    nlinarith [hprod, hfloor]

/--
**Scalar squared-transpose bound.**  If `0 < s`, `0 ≤ σ`, `0 ≤ lam`, and
`s ^ 2 ≤ σ ^ 2 + lam`, then `σ / (σ ^ 2 + lam) ^ 2 ≤ 1 / s ^ 3`.  The proof
uses exactly the requested cases `s ≤ σ` and `σ < s`; no SVD or norm fact is
hidden in this scalar lemma (the corresponding local note).
-/
theorem tikhonov_squared_transpose_scalar_bound
    {s σ lam : ℝ}
    (hs : 0 < s) (hlam : 0 ≤ lam) (hσ : 0 ≤ σ)
    (hfloor : s ^ 2 ≤ σ ^ 2 + lam) :
    σ / (σ ^ 2 + lam) ^ 2 ≤ 1 / s ^ 3 := by
  have hden : 0 < σ ^ 2 + lam :=
    lt_of_lt_of_le (sq_pos_of_pos hs) hfloor
  have hs3 : 0 < s ^ 3 := by positivity
  apply (div_le_div_iff₀ (sq_pos_of_pos hden) hs3).2
  rcases le_total s σ with hss | hσs
  · have hsum : 0 ≤ σ ^ 2 + σ * s + s ^ 2 := by
      nlinarith [sq_nonneg σ, sq_nonneg s,
        mul_nonneg hσ (le_of_lt hs)]
    have hcube_factor :
        0 ≤ (σ - s) * (σ ^ 2 + σ * s + s ^ 2) :=
      mul_nonneg (sub_nonneg.mpr hss) hsum
    have hcube : s ^ 3 ≤ σ ^ 3 := by
      nlinarith [hcube_factor]
    have hleft : σ * s ^ 3 ≤ σ ^ 4 := by
      have hmul := mul_le_mul_of_nonneg_left hcube hσ
      nlinarith [hmul]
    have hlamfactor : 0 ≤ lam * (2 * σ ^ 2 + lam) := by
      apply mul_nonneg hlam
      nlinarith [sq_nonneg σ]
    have hright : σ ^ 4 ≤ (σ ^ 2 + lam) ^ 2 := by
      nlinarith [hlamfactor]
    nlinarith [hleft, hright]
  · have hσle : σ ≤ s := hσs
    have hleft : σ * s ^ 3 ≤ s ^ 4 := by
      have hmul := mul_le_mul_of_nonneg_right hσle (le_of_lt hs3)
      nlinarith [hmul]
    have hsum : 0 ≤ (σ ^ 2 + lam) + s ^ 2 := by
      nlinarith [hden, sq_nonneg s]
    have hfactor :
        0 ≤ ((σ ^ 2 + lam) - s ^ 2) * ((σ ^ 2 + lam) + s ^ 2) :=
      mul_nonneg (sub_nonneg.mpr hfloor) hsum
    have hright : s ^ 4 ≤ (σ ^ 2 + lam) ^ 2 := by
      nlinarith [hfactor]
    nlinarith [hleft, hright]

/--
The scalar diagonal entry of the exact inverse minus the normal-equations
Tikhonov inverse is
`1 / σ - σ / (σ ^ 2 + lam) = lam / (σ * (σ ^ 2 + lam))`.
The lower singular-value floor makes its magnitude at most `lam / δ ^ 3`.
-/
theorem tikhonov_inverse_difference_scalar_bound
    {δ σ lam : ℝ}
    (hδ : 0 < δ) (hlam : 0 ≤ lam) (hσ : δ ≤ σ) :
    |σ⁻¹ - σ / (σ ^ 2 + lam)| ≤ lam / δ ^ 3 := by
  have hσpos : 0 < σ := lt_of_lt_of_le hδ hσ
  have hδsq : 0 < δ ^ 2 := sq_pos_of_pos hδ
  have hden : 0 < σ ^ 2 + lam := by
    nlinarith [sq_nonneg σ]
  have hdiff : σ⁻¹ - σ / (σ ^ 2 + lam) = lam / (σ * (σ ^ 2 + lam)) := by
    field_simp
    ring
  have hden_lower : δ ^ 3 ≤ σ * (σ ^ 2 + lam) := by
    have hσ_sq : δ ^ 2 ≤ σ ^ 2 := by
      nlinarith [sq_nonneg (σ - δ)]
    have hsum : δ ^ 2 ≤ σ ^ 2 + lam := by
      nlinarith
    have hprod : δ * δ ^ 2 ≤ σ * (σ ^ 2 + lam) := by
      exact mul_le_mul hσ hsum (le_of_lt hδsq) (le_of_lt hσpos)
    nlinarith [hprod]
  rw [hdiff, abs_of_nonneg]
  · exact div_le_div_of_nonneg_left hlam (by positivity) hden_lower
  · positivity

end Ctrllib

#print axioms Ctrllib.tikhonov_gram_eigenvalue_floor
#print axioms Ctrllib.tikhonov_plus_singular_values
#print axioms Ctrllib.tikhonov_squared_transpose_singular_values
#print axioms Ctrllib.tikhonov_plus_scalar_bound
#print axioms Ctrllib.tikhonov_squared_transpose_scalar_bound
#print axioms Ctrllib.tikhonov_inverse_difference_scalar_bound
