/-
Stiffness-residual injectivity (TARGET 5 / L4b of the ctrllib stream) — the
algebraic heart of Prop IV.1's closing step "v̆ ≡ 0 implies x̃ = 0", the content
of the `hzero` interface named in the sealed `propIV1_tendsto` (Reduction.lean).

THE STEP (giordano2019coordinated §IV.D). On the ω-limit set LaSalle isolates,
`v̆ ≡ 0`, so `v̇̆ ≡ 0`; substituting into the driven dynamics (eq 34b)

    M̆ v̇̆ + C̆ v̆ + D̆ v̆ + J_x̃ᵀ K̆ x̃ = −(…)ẋ̃_c ,   ẋ̃_c = 0 on Γ₂

collapses every velocity term and leaves the STIFFNESS RESIDUAL

    J_x̃ᵀ K̆ x̃ = 0 .                                     (eq 31 / 34b)

From the clean source (eq 24–26, 31): `x̃ = [x̃_b; x̃_e] ∈ ℝ⁹`, the block stiffness
`K̆ = blkdiag(K_b, K_e) ∈ ℝ⁹ˣ⁹` is symmetric positive definite, and the
representation Jacobian `J_x̃ = blkdiag(J_x̃_b, J_x̃_e) ∈ ℝ⁹ˣ⁹` is SQUARE (eq 26:
`ẋ̃ = J_x̃ v̆`, mapping ℝ⁹ → ℝ⁹). "`J_x̃` full column rank on Ω" therefore means
`J_x̃` is NONSINGULAR — for a square matrix full column rank ⟺ `J_x̃.mulVec`
injective ⟺ invertible.

WHAT IS PROVEN (real content, non-vacuous):
  `stiffness_residual_injective`  — K̆ ≻ 0 and J_x̃ full column rank (square ⇒
    nonsingular) force `J_x̃ᵀ K̆ x̃ = 0 → x̃ = 0`. This is the "v̆ ≡ 0 ⇒ x̃ = 0"
    step made precise: `Jᵀ K` is a product of two nonsingular matrices, hence its
    `mulVec` is injective.
  `stiffness_residual_injective'` — the same in the physical grouping
    `Jᵀ (K x̃) = 0 → x̃ = 0`.
  `stiffness_gram_posDef` — the sign-definiteness behind it: for the (possibly
    rectangular) full-column-rank J and K ≻ 0, the congruence `Jᵀ K J` is itself
    positive definite (⇒ injective). Recorded because it is the rank-robust reason
    the residual map is injective.

SYMPY-PINNED (the corresponding symbolic check (not bundled).py), before formalizing:
  (A) the SQUARE claim above holds — det(JᵀK)=det(J)det(K), 5000 random 9×9;
  (B) the RECTANGULAR reduced form is FALSE — a 3×2 full-column-rank J and K=I
      give a nonzero x with JᵀK x = 0 (nullspace `[0,0,1]`). So the Lean statement
      MUST require J square/nonsingular; a rectangular "J^T K x=0 ⇒ x=0" would be a
      false seal. This resolves the the corresponding local note §7 wording flag.
  (C) the Gram form JᵀKJ ≻ 0 for full-column-rank J (rectangular ok);
  (D) det(J_x̃_b) = det(−η E + [ε]ˣ) = −η on the unit quaternion, so J_x̃ is
      nonsingular exactly when each quaternion scalar part η ≠ 0 — automatic near
      the target x̃ = 0 (η = ±1). This is the concrete meaning of "nonsingular on Ω".

INTERFACE BOUNDARY (honest). This module seals the finite-dimensional ALGEBRA of
the hzero step only. Wiring it into `propIV1_tendsto.hzero`
(`{y | fderiv V y (f y) = 0} ⊆ Γ₁`) additionally needs the coordinate-level
closed-loop field `g₂` (eq 34b) to turn the abstract `fderiv V y (f y) = 0` into
`v̆ = 0` (via D̆ ≻ 0, the sealed Rayleigh machinery) and then into the residual
`Jᵀ K x̃ = 0`. That field is deliberately un-formalized in this campaign — the same
`IsSolutionTo` interface precedent used throughout L3/L4a — so the coordinate
wiring stays applier-side; this lemma is its final, machine-checked link.

Human derivation: the corresponding derivation record (not bundled)
-/
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open Matrix

namespace Ctrllib

-- `DecidableEq` is needed by the invertibility lemmas in the *proofs*
-- (`PosDef.isUnit`, `mulVec_injective_of_isUnit`); it does not surface in the
-- statements, so silence the in-type linter rather than drop a used instance
-- (same pattern as `BlockLyapunov`).
set_option linter.unusedDecidableInType false

variable {n : Type*} [Fintype n] [DecidableEq n] {K J : Matrix n n ℝ}

/-- **Stiffness-residual injectivity** (Prop IV.1 closing step, eq 31/34b). With
`K̆ = K` symmetric positive definite and the square representation Jacobian
`J_x̃ = J` of full column rank (`J.mulVec` injective ⟺ `J` nonsingular), the
stiffness residual vanishes only at the origin:

    `Jᵀ K x̃ = 0  →  x̃ = 0`.

Proof: `K` is a unit (`PosDef.isUnit`); `J` is a unit (square full-column-rank);
so `Jᵀ` is a unit and `Jᵀ * K` is a unit, whence `(Jᵀ * K).mulVec` is injective. -/
theorem stiffness_residual_injective (hK : K.PosDef)
    (hJ : Function.Injective J.mulVec) {x : n → ℝ}
    (hres : (Jᵀ * K) *ᵥ x = 0) : x = 0 := by
  have hJu : IsUnit J := mulVec_injective_iff_isUnit.mp hJ
  have hKu : IsUnit K := hK.isUnit
  have hJTu : IsUnit Jᵀ := by
    rw [isUnit_iff_isUnit_det, det_transpose, ← isUnit_iff_isUnit_det]; exact hJu
  have hinj : Function.Injective (Jᵀ * K).mulVec :=
    mulVec_injective_of_isUnit (hJTu.mul hKu)
  refine hinj ?_
  rw [mulVec_zero]
  exact hres

/-- Same fact in the physical grouping `Jᵀ (K x̃)` (transpose Jacobian applied to
the elastic wrench `K x̃`), matching eq 31 as written. -/
theorem stiffness_residual_injective' (hK : K.PosDef)
    (hJ : Function.Injective J.mulVec) {x : n → ℝ}
    (hres : Jᵀ *ᵥ (K *ᵥ x) = 0) : x = 0 := by
  refine stiffness_residual_injective hK hJ ?_
  rw [← mulVec_mulVec]
  exact hres

omit [DecidableEq n] in
/-- **The sign-definiteness behind the injectivity** (rank-robust form). For `K`
positive definite and `J` of full column rank (`J.mulVec` injective — valid for
rectangular `J` too), the congruence `Jᵀ K J` is positive definite. This is the
Rayleigh–Ritz reason the stiffness map is injective: `x̃ᵀ(Jᵀ K J)x̃ = (Jx̃)ᵀK(Jx̃) > 0`
off the origin. Recorded for the derivation; the eq-34b residual itself is the
square specialization above. -/
theorem stiffness_gram_posDef {m : Type*} [Fintype m]
    {K : Matrix n n ℝ} {J : Matrix n m ℝ}
    (hK : K.PosDef) (hJ : Function.Injective J.mulVec) :
    (Jᵀ * K * J).PosDef := by
  have h := hK.conjTranspose_mul_mul_same hJ
  rwa [conjTranspose_eq_transpose_of_trivial] at h

end Ctrllib

#print axioms Ctrllib.stiffness_residual_injective
#print axioms Ctrllib.stiffness_residual_injective'
#print axioms Ctrllib.stiffness_gram_posDef
