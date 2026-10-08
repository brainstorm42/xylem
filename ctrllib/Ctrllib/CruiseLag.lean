/-
Cruise-lag steady-state relation (the corresponding design note, gap 3) — the source model note
eq 4.14 (final.tex eq x_ss) as a checked declaration under an explicit
invertibility premise.

THE STEP (the source model note §4.5). At steady state of the working control equation
(eq 4.12) the velocity error and its rate vanish, and what survives is a balance
among the proportional term, the cruising Coriolis force and the CoM coupling:

    0 = −C̆ v̆_d − J_x̃ᵀ K̆ x̃_ss − (C_c + D̆ Ğ_vc) ẋ̃_c
    ⇒ x̃_ss = −(J_x̃ᵀ K̆)⁻¹ [ C̆ v̆_d + (C_c + D̆ Ğ_vc) ẋ̃_c ].         (eq 4.14)

The Coriolis-only limit (perfect CoM tracking, ẋ̃_c = 0) is the special case
x̃_ss = −(J_x̃ᵀ K̆)⁻¹ C̆ v̆_d used in the corresponding local note.

WHAT IS PROVEN (finite-dimensional linear algebra over ℝ):
  `cruise_lag_unique`      — for A nonsingular, 0 = −b − A x forces x = −A⁻¹ b.
  `cruise_lag_iff`         — and conversely; the steady state is unique.
  `cruise_lag`             — eq 4.14 literally, with A = J_x̃ᵀ K̆ and
                             b = C̆ v̆_d + F, F the CoM-coupling forcing.
  `cruise_lag_coriolis_only` — the F = 0 limit.
  `isUnit_transpose_mul_of_posDef` — the premise reduces to the same
                             "J_x̃ nonsingular" as StiffnessResidual.lean:
                             K̆ ≻ 0 and J_x̃ nonsingular ⇒ J_x̃ᵀ K̆ nonsingular.
  `cruise_lag_of_posDef`   — eq 4.14 under (K̆ ≻ 0, J_x̃ nonsingular) directly.

SYMPY-PINNED (the corresponding project check (not bundled).py):
  (A) unique solution for det A ≠ 0; (B) F = 0 limit by substitution;
  (C) FALSIFICATION: for singular A the balance has no solution or an affine
      family — the invertibility premise is load-bearing and is therefore a
      hypothesis here, not a conclusion; (D) det(JᵀK) = det J · det K.

INTERFACE BOUNDARY (honest). "Steady state" (ẋ̃ = 0, v̆ = v̆_d, v̇̆ = v̇̆_d) is a
hypothesis package: this module does not derive from the flow that such a state
is reached, nor that ẋ̃ = 0 implies v̆ = v̆_d (the open check named in
the corresponding local note). It records that IF the balance holds with the stated
matrices, THEN the lag is the displayed vector and no other. The frame,
derivative convention and whether v̆_d is analytic or finite-difference are
inputs to the matrices, not to this algebra. The transport block of the
implemented J_x̃ (TrackingErrorJacobian.lean) enters through J_x̃ᵀ and must be
carried when the relation is evaluated numerically.
-/
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open Matrix

namespace Ctrllib

-- `DecidableEq` is used by the inverse in the *statements* (`A⁻¹`), so it is
-- genuinely in-type here; no linter option needed.
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Unique steady state.** If `A` is nonsingular and `0 = −b − A x`, then
`x = −A⁻¹ b`. -/
theorem cruise_lag_unique {A : Matrix n n ℝ} (hA : IsUnit A) {x b : n → ℝ}
    (h : 0 = -b - A *ᵥ x) : x = -(A⁻¹ *ᵥ b) := by
  have hdet : IsUnit A.det := (isUnit_iff_isUnit_det A).mp hA
  have hAx : A *ᵥ x = -b := by
    have := congrArg (fun y => y + A *ᵥ x) h
    simpa using this
  calc x = (A⁻¹ * A) *ᵥ x := by rw [nonsing_inv_mul A hdet, one_mulVec]
    _ = A⁻¹ *ᵥ (A *ᵥ x) := by rw [← mulVec_mulVec]
    _ = A⁻¹ *ᵥ (-b) := by rw [hAx]
    _ = -(A⁻¹ *ᵥ b) := by rw [mulVec_neg]

/-- **Characterization.** For nonsingular `A`, the balance `0 = −b − A x` holds
iff `x = −A⁻¹ b`. -/
theorem cruise_lag_iff {A : Matrix n n ℝ} (hA : IsUnit A) {x b : n → ℝ} :
    0 = -b - A *ᵥ x ↔ x = -(A⁻¹ *ᵥ b) := by
  refine ⟨cruise_lag_unique hA, fun hx => ?_⟩
  have hdet : IsUnit A.det := (isUnit_iff_isUnit_det A).mp hA
  subst hx
  rw [mulVec_neg, mulVec_mulVec, mul_nonsing_inv A hdet, one_mulVec]
  simp

/-- **Cruise-lag relation, eq 4.14.** With `A = J_x̃ᵀ K̆` nonsingular and the
steady-state balance `0 = −C̆ v̆_d − (J_x̃ᵀ K̆) x̃ − F` (`F` the CoM-coupling forcing
`(C_c + D̆ Ğ_vc) ẋ̃_c`), the lag is
`x̃_ss = −(J_x̃ᵀ K̆)⁻¹ (C̆ v̆_d + F)`. -/
theorem cruise_lag {J K C : Matrix n n ℝ} (hJK : IsUnit (Jᵀ * K))
    {x vd F : n → ℝ}
    (hss : 0 = -(C *ᵥ vd) - (Jᵀ * K) *ᵥ x - F) :
    x = -((Jᵀ * K)⁻¹ *ᵥ (C *ᵥ vd + F)) := by
  apply cruise_lag_unique hJK
  rw [hss]
  simp [sub_eq_add_neg, add_comm, add_assoc]

/-- **Coriolis-only limit** (perfect CoM tracking, `F = 0`):
`x̃_ss = −(J_x̃ᵀ K̆)⁻¹ C̆ v̆_d`. -/
theorem cruise_lag_coriolis_only {J K C : Matrix n n ℝ} (hJK : IsUnit (Jᵀ * K))
    {x vd : n → ℝ}
    (hss : 0 = -(C *ᵥ vd) - (Jᵀ * K) *ᵥ x) :
    x = -((Jᵀ * K)⁻¹ *ᵥ (C *ᵥ vd)) := by
  have h := cruise_lag hJK (F := 0) (by simpa using hss)
  simpa using h

/-- **The premise reduces to `J_x̃` nonsingular.** `K̆ ≻ 0` and `J_x̃` nonsingular
give `J_x̃ᵀ K̆` nonsingular (same reasoning as `stiffness_residual_injective`). -/
theorem isUnit_transpose_mul_of_posDef {J K : Matrix n n ℝ} (hK : K.PosDef)
    (hJ : IsUnit J) : IsUnit (Jᵀ * K) := by
  have hJT : IsUnit Jᵀ := by
    rw [isUnit_iff_isUnit_det, det_transpose, ← isUnit_iff_isUnit_det]; exact hJ
  exact hJT.mul hK.isUnit

/-- Eq 4.14 under the physical premises `K̆ ≻ 0`, `J_x̃` nonsingular. -/
theorem cruise_lag_of_posDef {J K C : Matrix n n ℝ} (hK : K.PosDef) (hJ : IsUnit J)
    {x vd F : n → ℝ}
    (hss : 0 = -(C *ᵥ vd) - (Jᵀ * K) *ᵥ x - F) :
    x = -((Jᵀ * K)⁻¹ *ᵥ (C *ᵥ vd + F)) :=
  cruise_lag (isUnit_transpose_mul_of_posDef hK hJ) hss

end Ctrllib

#print axioms Ctrllib.cruise_lag_unique
#print axioms Ctrllib.cruise_lag_iff
#print axioms Ctrllib.cruise_lag
#print axioms Ctrllib.cruise_lag_coriolis_only
#print axioms Ctrllib.isUnit_transpose_mul_of_posDef
#print axioms Ctrllib.cruise_lag_of_posDef
