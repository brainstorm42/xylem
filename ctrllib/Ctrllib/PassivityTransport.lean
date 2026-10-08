/-
TARGET 7 — the Christoffel choice makes passivity automatic (ctrllib).

Giordano 2019 asserts eq 23 "automatically holds" from the transformation
machinery, without exhibiting the construction. The sealed `Passivity.lean`
proves eq 23 GIVEN the factorization `Ṁ = C + Cᵀ`, but leaves that factorization
as a consumed hypothesis. This module PRODUCES it for the transformed dynamics:
Giordano's transported inertia/Coriolis (the source model note §3 eqs 3.1–3.2) inherit the
factorization from the original system, so "eq 23 holds automatically" becomes a
theorem instead of an assertion.

The content is the CONGRUENCE TRANSPORT of the Christoffel factorization. Let
`P` (= Γ⁻¹) be an invertible time-varying transform. the source model note eqs 3.1–3.2 give

    M̂  = Pᵀ M P                                   (eq 3.1)
    Ĉ  = Pᵀ (C P + M Ṗ)                            (eq 3.2, the −MΓ⁻¹Γ̇ correction)

and the product rule gives  M̂̇ = Ṗᵀ M P + Pᵀ Ṁ P + Pᵀ M Ṗ.  The theorem:
if `M` is SYMMETRIC (inertia) and `Ṁ = C + Cᵀ` (Christoffel choice in the
original coordinates), then `M̂̇ = Ĉ + Ĉᵀ` — the transported factorization.
Composed with the sealed Passivity lemmas, the transformed `M̂̇ − 2Ĉ` is
skew and Giordano eq 23 holds for the transformed dynamics.

SymPy-pinned (the corresponding symbolic check (not bundled).py) BEFORE formalizing:
  (A) the identity holds — symbolic n=3, all entries free, + 20000 random 5×5;
  (B) `M` symmetric is NECESSARY — dropping it leaves residual `Ṗᵀ(M−Mᵀ)P ≠ 0`;
  (C) `P = Γ⁻¹` makes `Ĉ` equal the house eq-3.2 form `Γ⁻ᵀ(C − MΓ⁻¹Γ̇)Γ⁻¹`.

INTERFACE BOUNDARY (honest). This seals the finite-dimensional ALGEBRA: the
product-rule form of `M̂̇` and the transport `P = Γ⁻¹` are supplied at the
statement level (the LHS of `congruence_transport` is literally the product-rule
derivative; the P↔Γ⁻¹ identification is pin (C)). What is deliberately NOT here:
the Mathlib-calculus derivation of `M̂̇` from a time-varying `Γ(t)`, and the
9×9 block extraction picking `M̆,C̆` out of the 12×12 `M̂,Ĉ`. Both are the same
`IsSolutionTo`-style applier-side scaffolding used throughout L3/L4 — see the .

Human derivation: the corresponding derivation record (not bundled)
-/
import Ctrllib.Passivity
import Mathlib.Tactic.NoncommRing

open Matrix

namespace Ctrllib

-- `DecidableEq` is needed in the *proof* (`noncomm_ring` uses the
-- `Ring (Matrix n n R)` instance, whose identity matrix needs it); it does not
-- surface in the statements, so silence the in-type linter rather than drop a
-- used instance (same pattern as `BlockLyapunov`/`StiffnessResidual`).
set_option linter.unusedDecidableInType false

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Congruence transport of the Christoffel factorization** (the source model note
eqs 3.1–3.2). Over any commutative ring: if the inertia `M` is symmetric and the
original system obeys the Christoffel choice `Ṁ = C + Cᵀ`, then the transported
inertia `M̂ = Pᵀ M P` and Coriolis `Ĉ = Pᵀ(C P + M Ṗ)` again factor as
`M̂̇ = Ĉ + Ĉᵀ`, where `M̂̇ = Ṗᵀ M P + Pᵀ Ṁ P + Pᵀ M Ṗ` is the product-rule
derivative. This is the algebra behind Giordano's "eq 23 automatically holds":
the transformation transports the factorization the passivity property needs.

The symmetry `Mᵀ = M` is load-bearing (SymPy pin (B): the obstruction to the
identity is exactly `Ṗᵀ(M − Mᵀ)P`). Only additive/multiplicative ring structure
is used, so this holds over any `CommRing`. -/
theorem congruence_transport {R : Type*} [CommRing R]
    {M C P Pdot Mdot : Matrix n n R}
    (hMsymm : Mᵀ = M) (hfact : Mdot = C + Cᵀ) :
    Pdotᵀ * M * P + Pᵀ * Mdot * P + Pᵀ * M * Pdot
      = Pᵀ * (C * P + M * Pdot) + (Pᵀ * (C * P + M * Pdot))ᵀ := by
  subst hfact
  simp only [transpose_mul, transpose_add, transpose_transpose, hMsymm]
  noncomm_ring

/-- The transported `M̂̇ − 2Ĉ` is skew-symmetric — feeding the sealed
`mdot_sub_two_coriolis_skew` with the transported factorization. This is the
exact hypothesis `Passivity.lean` consumed, now discharged by construction. -/
theorem transported_skew {R : Type*} [CommRing R] {M C P Pdot : Matrix n n R}
    (hMsymm : Mᵀ = M) :
    ((Pdotᵀ * M * P + Pᵀ * (C + Cᵀ) * P + Pᵀ * M * Pdot)
        - 2 • (Pᵀ * (C * P + M * Pdot)))ᵀ
      = -((Pdotᵀ * M * P + Pᵀ * (C + Cᵀ) * P + Pᵀ * M * Pdot)
        - 2 • (Pᵀ * (C * P + M * Pdot))) :=
  mdot_sub_two_coriolis_skew (congruence_transport hMsymm rfl)

/-- **Giordano eq 23 for the transformed dynamics, automatically.** The velocity
quadratic form of the transported `M̂̇ − 2Ĉ` vanishes for every `v̆` — no longer
assumed, but produced from the original Christoffel factorization via the
congruence. Composes `congruence_transport` into the sealed `passivity_identity`. -/
theorem transported_passivity_identity {M C P Pdot : Matrix n n ℝ}
    (hMsymm : Mᵀ = M) (v : n → ℝ) :
    v ⬝ᵥ ((Pdotᵀ * M * P + Pᵀ * (C + Cᵀ) * P + Pᵀ * M * Pdot)
        - 2 • (Pᵀ * (C * P + M * Pdot))) *ᵥ v = 0 :=
  passivity_identity (congruence_transport hMsymm rfl) v

end Ctrllib

#print axioms Ctrllib.congruence_transport
#print axioms Ctrllib.transported_skew
#print axioms Ctrllib.transported_passivity_identity
