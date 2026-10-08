/-
The CONCRETE circumcentroidal passivity instance — Giordano eq 23 in its own
printed 9-dimensional shape (ctrllib).

`PassivityTransport.lean` seals the ABSTRACT congruence transport: for a free
index type `n` and free matrices `P, Ṗ`, the transported residual `M̂̇ − 2Ĉ` has
a vanishing quadratic form. The staged evidence pack records that this is not yet
the concrete physical instance — "product-rule calculus, the identification
`P = Γ⁻¹`, and block extraction remain outside the Lean statement"
(the corresponding local note, discrepancy 4). This module supplies the concrete
instance for the paper's own case.

CONCRETE CASE. giordano2019coordinated eq 19 stacks the transformed velocity as
`[v_c ; ω_b ; ν_e^⊕]` with block sizes (3, 3, 6), so the coordinate index is

    CircumCoord = Fin 3 ⊕ (Fin 3 ⊕ Fin 6),   ReducedCoord = Fin 3 ⊕ Fin 6,

12-dimensional with the 9-dimensional attitude/end-effector block `(ω_b, ν_e^⊕)`
sitting in the second summand. `gammaCircum` is eq 19's transform itself, in the
same block form the sealed `DetGamma`/`GammaInvertible` modules use.

WHAT IS NEW HERE (over the abstract module):
  * `gammaCircum`             — eq 19's concrete 12×12 transform as a named target.
  * `circum_gamma_inv_mul`    — `Γ⁻¹Γ = E` exactly on the paper's Ω side-condition
                                (nonsingular `J_{ν_e}^⊕`), via sealed `DetGamma`.
                                This is what licenses writing `Γ⁻¹` at all.
  * `circum_coriolis_house_form` — the transported Coriolis at `P = Γ⁻¹` equals the
                                house eq-3.2 form `Γ⁻ᵀ(C − MΓ⁻¹Γ̇)Γ⁻¹` (SymPy pin (C)
                                of `the corresponding private check`, now kernel-checked).
  * `dotProduct_mulVec_toBlocks₂₂` — the BLOCK EXTRACTION: the quadratic form of a
                                `(α ⊕ β)`-indexed matrix, restricted to vectors
                                supported on `β`, is the quadratic form of the `₂₂`
                                sub-block. This is the 12×12 → 9×9 step the evidence
                                pack names as missing.
  * `circum_passivity_identity_full` — eq 23's quadratic form at the concrete index
                                type, with `P = Γ⁻¹` and `Ṗ = −Γ⁻¹Γ̇Γ⁻¹` substituted.
  * `circum_passivity_identity` — HEADLINE. eq 23 as the paper prints it:
                                `[ω_bᵀ ν_e^⊕ᵀ](M̆̇ − 2C̆)[ω_b ; ν_e^⊕] = 0` for every
                                `v̆ ∈ ℝ⁹`, with `M̆̇ − 2C̆` the reduced 9×9 block of the
                                12×12 transported residual.

WHY THE ₂₂ BLOCK IS `M̆̇ − 2C̆`. Eq 21 reads the transformed system as
`M̂ = blockdiag(mE₃, M̆)` and `Ĉ` with lower-right block `C̆`; entrywise
differentiation commutes with block selection, so `(M̂̇ − 2Ĉ)₂₂ = M̆̇ − 2C̆`. The
Lean statement therefore proves eq 23 for the reduced block, given eq 21's block
reading of `M̂, Ĉ` — which is a reading of the source, not a Lean claim.

INTERFACE BOUNDARY (honest, unchanged from the abstract module). `Ṗ` appears here
in its closed form `−Γ⁻¹Γ̇Γ⁻¹` rather than as a free matrix, but the Mathlib-calculus
derivation that this IS `d/dt(Γ(t)⁻¹)` along a trajectory is still not in the
statement; `circum_gamma_inv_mul` supplies the `Γ⁻¹Γ = E` that the standard
differentiate-and-solve step needs, and `SevenDof.inv_deriv_eq` seals that step.
Likewise `M̂̇` is the product-rule expression at the value level, not a derivative
of a time-varying `Γ(t)`.

Human derivation: the corresponding local note (transport algebra),
the corresponding local note (the application correspondence).
-/
import Ctrllib.PassivityTransport
import Ctrllib.GammaInvertible

open Matrix

namespace Ctrllib

set_option linter.unusedDecidableInType false

/-! ## The concrete circumcentroidal coordinate index (eq 19) -/

/-- The reduced 9-dimensional attitude/end-effector index `(ω_b, ν_e^⊕)`, block
sizes (3, 6) per giordano2019coordinated eq 22b. -/
abbrev ReducedCoord := Fin 3 ⊕ Fin 6

/-- The full 12-dimensional circumcentroidal coordinate index `(v_c, (ω_b, ν_e^⊕))`,
block sizes (3, 3, 6) per giordano2019coordinated eq 19. The centre-of-mass block
is the FIRST summand, so the coupled 9×9 attitude/end-effector system is the
second — the `₂₂` block of any `CircumCoord`-indexed matrix. -/
abbrev CircumCoord := Fin 3 ⊕ ReducedCoord

/-- **giordano2019coordinated eq 19** — the coordinated transform Γ, in the block
form the sealed `DetGamma`/`GammaInvertible` modules already carry:

    Γ = [ R_cb   -R_cb[p_bc]^×   R_cb J̄_v ]     (top row abbreviated as `T`)
        [ 0       E              0        ]
        [ 0       G_ωb           J_{ν_e}^⊕ ]

`Rot` is `R_cb`, `T` the top-right pair, `G` is `G_ωb`, and `J` is the
circumcentroidal Jacobian `J_{ν_e}^⊕` (square because the arm is nonredundant,
`n = 6`, eq 19's standing assumption). -/
def gammaCircum (Rot : Matrix (Fin 3) (Fin 3) ℝ) (T : Matrix (Fin 3) ReducedCoord ℝ)
    (G : Matrix (Fin 6) (Fin 3) ℝ) (J : Matrix (Fin 6) (Fin 6) ℝ) :
    Matrix CircumCoord CircumCoord ℝ :=
  fromBlocks Rot T 0 (fromBlocks 1 0 G J)

/-- `det Γ = det J_{ν_e}^⊕` at the concrete index type — the sealed `DetGamma`
identity, read off `gammaCircum`. -/
theorem gammaCircum_det {Rot : Matrix (Fin 3) (Fin 3) ℝ}
    (hRot : Rot ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (T : Matrix (Fin 3) ReducedCoord ℝ) (G : Matrix (Fin 6) (Fin 3) ℝ)
    (J : Matrix (Fin 6) (Fin 6) ℝ) :
    (gammaCircum Rot T G J).det = J.det := by
  simp only [gammaCircum]
  exact det_gamma_eq_det_J_oplus Rot hRot T G J

/-- **Γ is genuinely invertible on Ω.** With `R_cb ∈ SO(3)` and the circumcentroidal
Jacobian nonsingular — eq 19's stated side-condition, the region Ω of Section IV.D —
the Moore-style `Γ⁻¹` really is a left inverse. This is what licenses the
substitution `P = Γ⁻¹` below: off Ω, `Matrix.inv` returns a junk value and the
identification is void. -/
theorem circum_gamma_inv_mul {Rot : Matrix (Fin 3) (Fin 3) ℝ}
    (hRot : Rot ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (T : Matrix (Fin 3) ReducedCoord ℝ) (G : Matrix (Fin 6) (Fin 3) ℝ)
    {J : Matrix (Fin 6) (Fin 6) ℝ} (hJ : IsUnit J.det) :
    (gammaCircum Rot T G J)⁻¹ * gammaCircum Rot T G J = 1 :=
  nonsing_inv_mul _ (by rw [gammaCircum_det hRot T G J]; exact hJ)

/-! ## Block extraction: 12×12 → the reduced 9×9 -/

/-- **Block extraction of a quadratic form.** For a matrix indexed by `α ⊕ β`, the
quadratic form evaluated on a vector supported on the `β` summand is the quadratic
form of the `₂₂` sub-block. This is the 12×12 → 9×9 step: putting `v_c = 0` in the
full circumcentroidal identity reads off the reduced attitude/end-effector block. -/
theorem dotProduct_mulVec_toBlocks₂₂ {α β : Type*} [Fintype α] [Fintype β]
    (A : Matrix (α ⊕ β) (α ⊕ β) ℝ) (w : β → ℝ) :
    Sum.elim (0 : α → ℝ) w ⬝ᵥ A *ᵥ Sum.elim (0 : α → ℝ) w = w ⬝ᵥ A.toBlocks₂₂ *ᵥ w := by
  simp [dotProduct, mulVec, Fintype.sum_sum_type, toBlocks₂₂]

/-! ## The concrete transported residual at `P = Γ⁻¹` -/

/-- **The transported passivity residual `M̂̇ − 2Ĉ` at `P = Γ⁻¹`**, at the concrete
12-dimensional circumcentroidal index. `M̂̇ = Ṗᵀ M P + Pᵀ Ṁ P + Pᵀ M Ṗ` is the
product-rule derivative (the source model note eq 3.1) with `Ṁ = C + Cᵀ` substituted, and
`Ĉ = Pᵀ(C P + M Ṗ)` is the transported Coriolis (the source model note eq 3.2). The
inverse's rate is written in its closed form `Ṗ = −Γ⁻¹ Γ̇ Γ⁻¹`, which is the
inverse-derivative step sealed as `SevenDof.inv_deriv_eq` and licensed here by
`circum_gamma_inv_mul`. -/
noncomputable def circumResidual (M C Gam Gamdot : Matrix CircumCoord CircumCoord ℝ) :
    Matrix CircumCoord CircumCoord ℝ :=
  ((-(Gam⁻¹ * Gamdot * Gam⁻¹))ᵀ * M * Gam⁻¹ + (Gam⁻¹)ᵀ * (C + Cᵀ) * Gam⁻¹
      + (Gam⁻¹)ᵀ * M * (-(Gam⁻¹ * Gamdot * Gam⁻¹)))
    - 2 • ((Gam⁻¹)ᵀ * (C * Gam⁻¹ + M * (-(Gam⁻¹ * Gamdot * Gam⁻¹))))

/-- **SymPy pin (C), kernel-checked.** At `P = Γ⁻¹` the transported Coriolis
`Ĉ = Pᵀ(C P + M Ṗ)` is exactly the house eq-3.2 form `Γ⁻ᵀ(C − M Γ⁻¹ Γ̇)Γ⁻¹` — the
`−MΓ⁻¹Γ̇` correction. Pure ring algebra; no invertibility or symmetry used. -/
theorem circum_coriolis_house_form (M C Gam Gamdot : Matrix CircumCoord CircumCoord ℝ) :
    (Gam⁻¹)ᵀ * (C - M * (Gam⁻¹ * Gamdot)) * Gam⁻¹
      = (Gam⁻¹)ᵀ * (C * Gam⁻¹ + M * (-(Gam⁻¹ * Gamdot * Gam⁻¹))) := by
  noncomm_ring

/-- **eq 23 at the concrete 12-dimensional index, `P = Γ⁻¹`.** The full
circumcentroidal quadratic form of `M̂̇ − 2Ĉ` vanishes for every
`[v_c ; ω_b ; ν_e^⊕] ∈ ℝ¹²`. Instantiation of the sealed
`transported_passivity_identity` at `CircumCoord`, `P = Γ⁻¹`, `Ṗ = −Γ⁻¹Γ̇Γ⁻¹`. -/
theorem circum_passivity_identity_full {M C Gam Gamdot : Matrix CircumCoord CircumCoord ℝ}
    (hMsymm : Mᵀ = M) (v : CircumCoord → ℝ) :
    v ⬝ᵥ circumResidual M C Gam Gamdot *ᵥ v = 0 := by
  simp only [circumResidual]
  exact transported_passivity_identity hMsymm v

/-- **giordano2019coordinated eq 23, as printed.**

    [ω_bᵀ  ν_e^⊕ᵀ] (M̆̇ − 2C̆) [ω_b ; ν_e^⊕] = 0    ∀ (ω_b, ν_e^⊕) ∈ ℝ⁹,

with `M̆̇ − 2C̆` the reduced 9×9 attitude/end-effector block of the 12×12
transported residual (eq 21's `₂₂` block). Proved by restricting the full
circumcentroidal identity to `v_c = 0` and extracting the block — the paper's
"this automatically holds", now a theorem about the concrete transform.

The one modelling input is `hMsymm`: symmetry of the original-coordinate inertia.
The Christoffel factorization `Ṁ = C + Cᵀ` is not a hypothesis here — it is
substituted into `circumResidual` at the statement level. -/
theorem circum_passivity_identity {M C Gam Gamdot : Matrix CircumCoord CircumCoord ℝ}
    (hMsymm : Mᵀ = M) (vred : ReducedCoord → ℝ) :
    vred ⬝ᵥ (circumResidual M C Gam Gamdot).toBlocks₂₂ *ᵥ vred = 0 := by
  rw [← dotProduct_mulVec_toBlocks₂₂]
  exact circum_passivity_identity_full hMsymm _

end Ctrllib

#print axioms Ctrllib.gammaCircum_det
#print axioms Ctrllib.circum_gamma_inv_mul
#print axioms Ctrllib.dotProduct_mulVec_toBlocks₂₂
#print axioms Ctrllib.circum_coriolis_house_form
#print axioms Ctrllib.circum_passivity_identity_full
#print axioms Ctrllib.circum_passivity_identity
