import Ctrllib.TikhonovSVD
import Ctrllib.EuclideanNormBridge

open Matrix

namespace Ctrllib

variable {n : Type*} [Fintype n] [DecidableEq n]

/--
Seals Proposition 3, item 1 (the corresponding local note).  The
square domain is carried by `Matrix n n`, with `Alam` and `Blam` defined at
`ctrllib/TikhonovSVD.lean:31-35`; the schedule floor and both Gram floors are
supplied by `ctrllib/TikhonovSVD.lean:159-176`, and the two inverse norm
transports are `ctrllib/EuclideanNormBridge.lean:75-79`.
-/
theorem prop3_item1
    (Γ : Matrix n n ℝ) (σ : n → ℝ)
    (beta s sigmaG lam : ℝ)
    (hlam : lam = max (beta ^ 2) (s ^ 2 - sigmaG ^ 2))
    (hbeta : 0 < beta) (hbeta_le : beta ≤ s) (hs : 0 < s)
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
    (hB : (Blam Γ lam).IsHermitian)
    (hAunit : IsUnit (Alam Γ lam))
    (hBunit : IsUnit (Blam Γ lam)) :
    ‖toEuclideanCLM (𝕜 := ℝ) (Alam Γ lam)⁻¹‖ ≤ 1 / s ^ 2 ∧
      ‖toEuclideanCLM (𝕜 := ℝ) (Blam Γ lam)⁻¹‖ ≤ 1 / s ^ 2 := by
  have hfloor :=
    tikhonov_gram_eigenvalue_floor Γ σ beta s sigmaG lam hlam hσG hσ
      hσG_le hsvd hA hB
  constructor
  · exact
      euclideanCLM_inv_norm_le_of_isHermitian_eigenvalue_floor
        hA hAunit hs hfloor.2.1
  · exact
      euclideanCLM_inv_norm_le_of_isHermitian_eigenvalue_floor
        hB hBunit hs hfloor.2.2

/--
Seals Proposition 3, item 2 (the corresponding local note).  The
indexed orthogonal factorization is the sealed API at
`ctrllib/TikhonovSVD.lean:213-232`; its scalar bound is at
`ctrllib/TikhonovSVD.lean:314-318`, and the indexed diagonal norm bridge is at
`ctrllib/EuclideanNormBridge.lean:220-224`.
-/
theorem prop3_item2
    (Γ : Matrix n n ℝ) (σ : n → ℝ)
    (beta s sigmaG lam : ℝ)
    (hlam : lam = max (beta ^ 2) (s ^ 2 - sigmaG ^ 2))
    (hbeta : 0 < beta) (hbeta_le : beta ≤ s) (hs : 0 < s)
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
    (hB : (Blam Γ lam).IsHermitian)
    (hAunit : IsUnit (Alam Γ lam)) :
    ‖toEuclideanCLM (𝕜 := ℝ)
        ((Alam Γ lam)⁻¹ * Γᵀ)‖ ≤ 1 / s := by
  have hfloor :=
    tikhonov_gram_eigenvalue_floor Γ σ beta s sigmaG lam hlam hσG hσ
      hσG_le hsvd hA hB
  have hlam_nonneg : 0 ≤ lam := by
    rw [hlam]
    exact le_trans (sq_nonneg beta) (le_max_left _ _)
  obtain ⟨hσratio, U, V, hUtU, hUUt, hVtV, hVVt, hfactor⟩ :=
    tikhonov_plus_singular_values Γ σ s lam hs hσ hfloor.1 hsvd hAunit
  refine euclideanCLM_norm_le_of_conj_diagonal hUtU hVVt hfactor ?_ ?_
  · positivity
  · intro i
    rw [abs_of_nonneg (hσratio i)]
    exact tikhonov_plus_scalar_bound hs hlam_nonneg (hσ i) (hfloor.1 i)

/--
Seals Proposition 3, item 3 (the corresponding local note).  The
squared-transpose factorization is the sealed API at
`ctrllib/TikhonovSVD.lean:263-282`; its scalar bound is at
`ctrllib/TikhonovSVD.lean:338-342`, and the same indexed diagonal norm bridge
is `ctrllib/EuclideanNormBridge.lean:220-224`.
-/
theorem prop3_item3
    (Γ : Matrix n n ℝ) (σ : n → ℝ)
    (beta s sigmaG lam : ℝ)
    (hlam : lam = max (beta ^ 2) (s ^ 2 - sigmaG ^ 2))
    (hbeta : 0 < beta) (hbeta_le : beta ≤ s) (hs : 0 < s)
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
    (hB : (Blam Γ lam).IsHermitian)
    (hAunit : IsUnit (Alam Γ lam)) :
    ‖toEuclideanCLM (𝕜 := ℝ)
        ((Alam Γ lam)⁻¹ * (Alam Γ lam)⁻¹ * Γᵀ)‖ ≤ 1 / s ^ 3 := by
  have hfloor :=
    tikhonov_gram_eigenvalue_floor Γ σ beta s sigmaG lam hlam hσG hσ
      hσG_le hsvd hA hB
  have hlam_nonneg : 0 ≤ lam := by
    rw [hlam]
    exact le_trans (sq_nonneg beta) (le_max_left _ _)
  obtain ⟨hσratio, U, V, hUtU, hUUt, hVtV, hVVt, hfactor⟩ :=
    tikhonov_squared_transpose_singular_values Γ σ s lam hs hσ hfloor.1
      hsvd hAunit
  refine euclideanCLM_norm_le_of_conj_diagonal hUtU hVVt hfactor ?_ ?_
  · positivity
  · intro i
    rw [abs_of_nonneg (hσratio i)]
    exact
      tikhonov_squared_transpose_scalar_bound hs hlam_nonneg (hσ i)
        (hfloor.1 i)

end Ctrllib
