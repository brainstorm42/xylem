import Ctrllib.TrackingCascade
import Ctrllib.ComparisonUltimateBound

/-!
# Eventual tracking storage and norm floors

This module applies the existing tracking cascade majorant to a bounded upstream
signal.  With `a = κ / (2 * c_hi)` and
`B = c' ^ 2 * c_hi / (2 * κ) * (Mx + ρ) ^ 2`, it proves that the realized
storage eventually lies below `B / a + ε`, and then transfers that floor through
the lower storage sandwich to the tracking norm.

The flow, storage, derivative, sandwich, forced-rate inequality, and upstream
bound remain explicit hypotheses.  This is an application corollary for a
realized trajectory; it does not derive those premises from a controller or
claim the open C4 model-realization theorem.
-/

open Set Filter Topology

namespace Ctrllib

section UltimateBound

variable {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedAddCommGroup E₂]
  {x₁ : ℝ → E₁} {x₂ : ℝ → E₂} {W W' : ℝ → ℝ}
  {c_lo c_hi κ c' ρ : ℝ}

private lemma tracking_storage_forcing_le
    (hchi : 0 < c_hi) (hκ : 0 < κ) (hcp : 0 < c') (hρ : 0 ≤ ρ)
    {Mx : ℝ} (hMx : 0 ≤ Mx)
    (hx2M : ∀ t ∈ Ici (0 : ℝ), ‖x₂ t‖ ≤ Mx)
    (hWnn : ∀ t ∈ Ici (0 : ℝ), 0 ≤ W t)
    (hdi : ∀ t ∈ Ici (0 : ℝ),
      W' t ≤ -(κ / c_hi) * W t + c' * (‖x₂ t‖ + ρ) * Real.sqrt (W t)) :
    ∀ t ∈ Ici (0 : ℝ),
      W' t ≤ -(κ / (2 * c_hi)) * W t
        + c' ^ 2 * c_hi / (2 * κ) * (Mx + ρ) ^ 2 := by
  have hmaj := tracking_forced_rate_majorant (x₂ := x₂) (ρ := ρ)
    hchi hκ hcp hρ hWnn hdi
  intro t ht
  have hnn2 : (0 : ℝ) ≤ ‖x₂ t‖ := norm_nonneg _
  have hle : ‖x₂ t‖ + ρ ≤ Mx + ρ := by
    linarith [hx2M t ht]
  have hle2 : (‖x₂ t‖ + ρ) ^ 2 ≤ (Mx + ρ) ^ 2 :=
    sq_le_sq' (by linarith) hle
  have hKnn : (0 : ℝ) ≤ c' ^ 2 * c_hi / (2 * κ) := by positivity
  have hforcing : c' ^ 2 * c_hi / (2 * κ) * (‖x₂ t‖ + ρ) ^ 2 ≤
      c' ^ 2 * c_hi / (2 * κ) * (Mx + ρ) ^ 2 :=
    mul_le_mul_of_nonneg_left hle2 hKnn
  exact le_trans (hmaj t ht) (by linarith [hforcing])

/-- Eventual storage floor for a bounded upstream coupling.

For every positive `ε`, the realized storage eventually satisfies
`W t ≤ B / a + ε`, where
`a = κ / (2 * c_hi)` and
`B = c' ^ 2 * c_hi / (2 * κ) * (Mx + ρ) ^ 2`. -/
theorem tracking_storage_eventual_floor
    (hchi : 0 < c_hi) (hκ : 0 < κ) (hcp : 0 < c') (hρ : 0 ≤ ρ)
    {Mx : ℝ} (hMx : 0 ≤ Mx)
    (hWc : ContinuousOn W (Ici 0))
    (hWderiv : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt W (W' t) (Ici t) t)
    (hdi : ∀ t ∈ Ici (0 : ℝ),
      W' t ≤ -(κ / c_hi) * W t + c' * (‖x₂ t‖ + ρ) * Real.sqrt (W t))
    (hx2M : ∀ t ∈ Ici (0 : ℝ), ‖x₂ t‖ ≤ Mx)
    (hWnn : ∀ t ∈ Ici (0 : ℝ), 0 ≤ W t) :
    ∀ ε > 0, ∃ T ≥ 0, ∀ t ≥ T,
      W t ≤
        (c' ^ 2 * c_hi / (2 * κ) * (Mx + ρ) ^ 2) / (κ / (2 * c_hi)) + ε := by
  have ha : (0 : ℝ) < κ / (2 * c_hi) := by positivity
  have hB : (0 : ℝ) ≤ c' ^ 2 * c_hi / (2 * κ) * (Mx + ρ) ^ 2 := by
    positivity
  have hbound := tracking_storage_forcing_le (x₂ := x₂) (W := W) (W' := W')
    hchi hκ hcp hρ hMx hx2M hWnn hdi
  exact comparison_eventual_floor ha hB hWc hWderiv hbound

/-- Eventual tracking norm floor obtained from the lower storage sandwich.

For every positive `ε`, there is `T ≥ 0` such that, for all `t ≥ T`,

`‖x₁ t‖ ≤ sqrt ((B / a + ε) / c_lo)`,

with the exact constants `a = κ / (2 * c_hi)` and
`B = c' ^ 2 * c_hi / (2 * κ) * (Mx + ρ) ^ 2`. -/
theorem tracking_norm_eventual_floor
    (hclo : 0 < c_lo) (hchi : 0 < c_hi) (hκ : 0 < κ) (hcp : 0 < c')
    (hρ : 0 ≤ ρ) {Mx : ℝ} (hMx : 0 ≤ Mx)
    (hsand_lo : ∀ t ∈ Ici (0 : ℝ), c_lo * ‖x₁ t‖ ^ 2 ≤ W t)
    (hWc : ContinuousOn W (Ici 0))
    (hWderiv : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt W (W' t) (Ici t) t)
    (hdi : ∀ t ∈ Ici (0 : ℝ),
      W' t ≤ -(κ / c_hi) * W t + c' * (‖x₂ t‖ + ρ) * Real.sqrt (W t))
    (hx2M : ∀ t ∈ Ici (0 : ℝ), ‖x₂ t‖ ≤ Mx) :
    ∀ ε > 0, ∃ T ≥ 0, ∀ t ≥ T,
      ‖x₁ t‖ ≤ Real.sqrt ((
        (c' ^ 2 * c_hi / (2 * κ) * (Mx + ρ) ^ 2) / (κ / (2 * c_hi)) + ε) / c_lo) := by
  have hWnn : ∀ t ∈ Ici (0 : ℝ), 0 ≤ W t := fun t ht =>
    le_trans (mul_nonneg hclo.le (sq_nonneg _)) (hsand_lo t ht)
  intro ε hε
  obtain ⟨T, hT0, hT⟩ := tracking_storage_eventual_floor
    (x₂ := x₂) (W := W) (W' := W') hchi hκ hcp hρ hMx hWc hWderiv hdi hx2M hWnn ε hε
  refine ⟨T, hT0, ?_⟩
  intro t ht
  have hstorage := hT t ht
  have hsq : ‖x₁ t‖ ^ 2 ≤
      ((c' ^ 2 * c_hi / (2 * κ) * (Mx + ρ) ^ 2) / (κ / (2 * c_hi)) + ε) / c_lo := by
    rw [le_div_iff₀ hclo]
    have hsand := hsand_lo t (mem_Ici.mpr (le_trans hT0 ht))
    simpa [mul_comm] using hsand.trans hstorage
  have hnorm : ‖x₁ t‖ = Real.sqrt (‖x₁ t‖ ^ 2) :=
    (Real.sqrt_sq (norm_nonneg _)).symm
  rw [hnorm]
  exact Real.sqrt_le_sqrt hsq

end UltimateBound

end Ctrllib

#print axioms Ctrllib.tracking_storage_eventual_floor
#print axioms Ctrllib.tracking_norm_eventual_floor
