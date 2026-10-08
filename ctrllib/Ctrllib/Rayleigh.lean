/-
The Rayleigh sandwich (TARGET 4 of the ctrllib stream) — the ENABLER that
discharges the `QuadSandwich` predicate assumed in `Lyapunov.lean`.

For a real symmetric matrix `K` (`K.IsHermitian`; positive-definiteness is NOT
needed for the sandwich, only for `c₁ > 0`) and any vector `x`,

    c₁ * (x ⬝ᵥ x)  ≤  x ⬝ᵥ K *ᵥ x  ≤  c₂ * (x ⬝ᵥ x)

whenever `c₁ ≤ λᵢ(K) ≤ c₂` for every eigenvalue. The tightest constants are
`c₁ = λ_min`, `c₂ = λ_max` (Horn–Johnson, *Matrix Analysis* Thm 4.2.2 / Khalil,
*Nonlinear Systems* Lemma-level Rayleigh–Ritz bound). `rayleigh_sandwich` states
exactly the `λ_min … λ_max` form.

Proof route: the Mathlib spectral theorem `K = U · diag(λ) · Uᵀ` with `U`
orthogonal (`IsHermitian.eigenvectorUnitary`), change of variables `w = Uᵀx`,
so `x ⬝ᵥ K *ᵥ x = Σ λᵢ wᵢ²` and `x ⬝ᵥ x = Σ wᵢ²`, then a termwise comparison.
The load-bearing algebraic step (`quad_conj`) is a pure ring identity with NO
orthogonality — orthogonality enters only to preserve the norm (`Σ wᵢ² = x⬝ᵥx`).

SymPy pin (all three facts): the corresponding symbolic check (not bundled).py.
Human derivation: the corresponding derivation record (not bundled)
-/
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.InnerProductSpace.PiL2
import Ctrllib.Lyapunov

open Matrix

namespace Ctrllib

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Matrix n n ℝ}

omit [DecidableEq n] in
/-- Pure ring identity (no orthogonality): conjugating a quadratic form by any
square matrix `U` is a change of variables `x ↦ Uᵀx`. This is what turns the
spectral decomposition into a diagonal quadratic form. -/
private theorem quad_conj (U M : Matrix n n ℝ) (x : n → ℝ) :
    x ⬝ᵥ (U * M * Uᵀ) *ᵥ x = (Uᵀ *ᵥ x) ⬝ᵥ M *ᵥ (Uᵀ *ᵥ x) := by
  rw [mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose]

/-- The spectral theorem over `ℝ`, packaged as `K = U · diag(eigenvalues) · Uᵀ`
with `U := hK.eigenvectorUnitary` (orthogonal). Peels the `conjStarAlgAut`,
`RCLike.ofReal`, and `star = ᵀ` (trivial star on `ℝ`) wrappers of the library
statement. -/
private theorem spectral_conj (hK : K.IsHermitian) :
    K = (hK.eigenvectorUnitary : Matrix n n ℝ) * diagonal hK.eigenvalues
          * (hK.eigenvectorUnitary : Matrix n n ℝ)ᵀ := by
  conv_lhs => rw [hK.spectral_theorem, Unitary.conjStarAlgAut_apply]
  simp only [RCLike.ofReal_real_eq_id, Function.id_comp,
    Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]

/-- Diagonalized quadratic form and norm, in the eigenvector coordinates
`w = Uᵀx`: `x ⬝ᵥ K *ᵥ x = Σ λᵢ wᵢ²` and `x ⬝ᵥ x = Σ wᵢ²`. -/
private theorem rayleigh_sums (hK : K.IsHermitian) (x : n → ℝ) :
    x ⬝ᵥ K *ᵥ x
        = ∑ i, hK.eigenvalues i * (((hK.eigenvectorUnitary : Matrix n n ℝ)ᵀ *ᵥ x) i) ^ 2
      ∧ x ⬝ᵥ x
        = ∑ i, (((hK.eigenvectorUnitary : Matrix n n ℝ)ᵀ *ᵥ x) i) ^ 2 := by
  have hstar : star (hK.eigenvectorUnitary : Matrix n n ℝ)
      = (hK.eigenvectorUnitary : Matrix n n ℝ)ᵀ := by
    rw [Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  refine ⟨?_, ?_⟩
  · conv_lhs => rw [spectral_conj hK]
    rw [quad_conj]
    simp only [dotProduct, mulVec_diagonal]
    exact Finset.sum_congr rfl fun i _ => by ring
  · have huni : (hK.eigenvectorUnitary : Matrix n n ℝ) * 1
          * (hK.eigenvectorUnitary : Matrix n n ℝ)ᵀ = 1 := by
      rw [mul_one, ← hstar]
      exact Unitary.coe_mul_star_self _
    calc x ⬝ᵥ x
        = x ⬝ᵥ ((hK.eigenvectorUnitary : Matrix n n ℝ) * 1
            * (hK.eigenvectorUnitary : Matrix n n ℝ)ᵀ) *ᵥ x := by rw [huni, one_mulVec]
      _ = _ := by
          rw [quad_conj]
          simp only [dotProduct, one_mulVec, pow_two]

/-- **Rayleigh lower bound.** If every eigenvalue of a symmetric `K` is at least
`c₁`, then `c₁ ‖x‖² ≤ xᵀ K x` (stated as `c₁ * (x ⬝ᵥ x) ≤ x ⬝ᵥ K *ᵥ x`; over
`EuclideanSpace ℝ n`, `x ⬝ᵥ x = ‖x‖²`). Positive-definiteness lets `c₁ > 0`. -/
theorem le_dotProduct_mulVec (hK : K.IsHermitian) {c₁ : ℝ}
    (h : ∀ i, c₁ ≤ hK.eigenvalues i) (x : n → ℝ) :
    c₁ * (x ⬝ᵥ x) ≤ x ⬝ᵥ K *ᵥ x := by
  obtain ⟨hKx, hxx⟩ := rayleigh_sums hK x
  rw [hKx, hxx, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (h i) (sq_nonneg _)

/-- **Rayleigh upper bound.** If every eigenvalue of a symmetric `K` is at most
`c₂`, then `xᵀ K x ≤ c₂ ‖x‖²`. -/
theorem dotProduct_mulVec_le (hK : K.IsHermitian) {c₂ : ℝ}
    (h : ∀ i, hK.eigenvalues i ≤ c₂) (x : n → ℝ) :
    x ⬝ᵥ K *ᵥ x ≤ c₂ * (x ⬝ᵥ x) := by
  obtain ⟨hKx, hxx⟩ := rayleigh_sums hK x
  rw [hKx, hxx, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (h i) (sq_nonneg _)

/-- **Rayleigh–Ritz sandwich**, tightest form: `λ_min · (x⬝ᵥx) ≤ xᵀ K x ≤
λ_max · (x⬝ᵥx)`, with `λ_min`/`λ_max` the extreme eigenvalues (over a nonempty
index). -/
theorem rayleigh_sandwich [Nonempty n] (hK : K.IsHermitian) (x : n → ℝ) :
    (Finset.univ.inf' Finset.univ_nonempty hK.eigenvalues) * (x ⬝ᵥ x) ≤ x ⬝ᵥ K *ᵥ x
      ∧ x ⬝ᵥ K *ᵥ x ≤ (Finset.univ.sup' Finset.univ_nonempty hK.eigenvalues) * (x ⬝ᵥ x) :=
  ⟨le_dotProduct_mulVec hK (fun i => Finset.inf'_le _ (Finset.mem_univ i)) x,
   dotProduct_mulVec_le hK (fun i => Finset.le_sup' _ (Finset.mem_univ i)) x⟩

/-- **`QuadSandwich` producer.** The matrix quadratic form `V y = yᵀ K y` on
`EuclideanSpace ℝ n` satisfies the `QuadSandwich` predicate of `Lyapunov.lean`
with constants any uniform eigenvalue bounds `c₁ ≤ λᵢ(K) ≤ c₂`. This is the
stone `lyapunov_norm_sq_exp_decay` consumes: with `K` the stiffness/inertia
matrix (giordano2019coordinated eq 37) and `c₁ = λ_min`, `c₂ = λ_max`, its
`QuadSandwich` hypothesis falls out. -/
theorem quadSandwich_matrix (hK : K.IsHermitian) {c₁ c₂ : ℝ}
    (h₁ : ∀ i, c₁ ≤ hK.eigenvalues i) (h₂ : ∀ i, hK.eigenvalues i ≤ c₂) :
    QuadSandwich (fun y : EuclideanSpace ℝ n => WithLp.ofLp y ⬝ᵥ K *ᵥ WithLp.ofLp y) c₁ c₂ := by
  intro y
  have hnorm : ‖y‖ ^ 2 = WithLp.ofLp y ⬝ᵥ WithLp.ofLp y := by
    rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  rw [hnorm]
  exact ⟨le_dotProduct_mulVec hK h₁ _, dotProduct_mulVec_le hK h₂ _⟩

end Ctrllib

#print axioms Ctrllib.le_dotProduct_mulVec
#print axioms Ctrllib.dotProduct_mulVec_le
#print axioms Ctrllib.rayleigh_sandwich
#print axioms Ctrllib.quadSandwich_matrix
