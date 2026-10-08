/-
Machine-checked witnesses for two internal algebraic inconsistencies in
Giordano, Ott, and Albu-Schäffer (2019), DOI 10.1109/LRA.2019.2899433.

The published source prints:

* equations (29) and (30) with negative stiffness and damping, but equation
  (31), which is stated to stack them, with positive stiffness and damping;
* equation (16) as `ν_e^⊕ = G_ωb ω_b + J_νe^⊕ q̇`, while equation (34d)
  applies the selector `[E, -G_ωb]` to
  `v̆ = [ω_b; ν_e^⊕]`. The conforming selector is `[-G_ωb, E]`.

These theorems certify concrete algebraic witnesses only. They support the
classification "verified internal inconsistencies consistent with typographical
errors"; they do not establish authorial intent.
-/
import Mathlib

namespace Ctrllib

/-- Scalar form of the two negative-feedback component laws (29) and (30). -/
def eq31FromComponentLaws (stiffness damping : ℝ) : ℝ :=
  -stiffness - damping

/-- Scalar form of the positive signs printed in the stacked equation (31). -/
def eq31AsPrinted (stiffness damping : ℝ) : ℝ :=
  stiffness + damping

/-- With unit stiffness and damping contributions, the printed equation (31)
returns `2`, whereas the component laws (29) and (30) return `-2`. -/
theorem eq31_printed_sign_counterexample :
    eq31AsPrinted 1 1 ≠ eq31FromComponentLaws 1 1 := by
  norm_num [eq31AsPrinted, eq31FromComponentLaws]

/-- Scalar proxy for the block-conforming recovery obtained by solving (16):
`q̇ = J⁻¹(ν_e^⊕ - G_ωb ω_b)`. -/
def eq34dConformingOrder (g omega nu : ℝ) : ℝ :=
  -g * omega + nu

/-- Scalar proxy for applying the printed order `[E, -G_ωb]` positionally to
the declared stack `[ω_b; ν_e^⊕]`. -/
def eq34dPrintedOrder (g omega nu : ℝ) : ℝ :=
  omega - g * nu

/-- For `G_ωb = 2`, `ω_b = 1`, and `ν_e^⊕ = 3`, solving equation (16) gives
`1`; the printed positional order in (34d) gives `-5`. -/
theorem eq34d_printed_block_order_counterexample :
    eq34dConformingOrder 2 1 3 ≠ eq34dPrintedOrder 2 1 3 := by
  norm_num [eq34dConformingOrder, eq34dPrintedOrder]

/-- The two declared blocks of `v̆ = [ω_b; ν_e^⊕]` have different widths.
This arithmetic fact records why `[E₆, -G₆×₃]` cannot conform to a
`[3; 6]` partition without swapping the blocks. -/
theorem eq34d_declared_block_widths_differ : (3 : ℕ) ≠ 6 := by
  norm_num

/-! ### Dimension-typed witness for equation (34d)

The proxies above are scalars.  A scalar has no block structure, so it can
record the positional error numerically but cannot record it as a *dimension*
error.  The declarations below carry the published dimensions instead.

Equation (16) reads `ν_e^⊕ = G_ωb ω_b + J_νe^⊕ q̇` with `ω_b ∈ ℝ³` and
`ν_e^⊕ ∈ ℝ⁶`; hence `G_ωb ∈ ℝ^{6×3}`, and the identity block `E` that acts on
`ν_e^⊕` is `ℝ^{6×6}`.  Equation (27) declares the stack `v̆ = [ω_b; ν_e^⊕]`,
whose index type is therefore `Fin 3 ⊕ Fin 6`. -/

open scoped Matrix

/-- The input stack declared in equation (27), `v̆ = [ω_b; ν_e^⊕]`, indexed by
`Fin 3 ⊕ Fin 6`. -/
def eq34dDeclaredStack (omega : Fin 3 → ℝ) (nu : Fin 6 → ℝ) :
    Fin 3 ⊕ Fin 6 → ℝ :=
  Sum.elim omega nu

/-- The conforming selector `[-G_ωb, E] ∈ ℝ^{6×9}` obtained by solving (16).
Its column index is `Fin 3 ⊕ Fin 6`: the same partition as the declared
stack. -/
def eq34dConformingSelector (G : Matrix (Fin 6) (Fin 3) ℝ) :
    Matrix (Fin 6) (Fin 3 ⊕ Fin 6) ℝ :=
  Matrix.fromCols (-G) (1 : Matrix (Fin 6) (Fin 6) ℝ)

/-- The selector as printed in equation (34d), identity block first.  Its
column index is `Fin 6 ⊕ Fin 3`: the reversed partition. -/
def eq34dPrintedSelector (G : Matrix (Fin 6) (Fin 3) ℝ) :
    Matrix (Fin 6) (Fin 6 ⊕ Fin 3) ℝ :=
  Matrix.fromCols (1 : Matrix (Fin 6) (Fin 6) ℝ) (-G)

/-- Positive control, and the seal on the replacement rather than the defect:
the conforming selector does apply to the declared stack, and the product is
the recovery obtained by solving equation (16), `ν_e^⊕ - G_ωb ω_b`. -/
theorem eq34dConformingSelector_mulVec_declaredStack
    (G : Matrix (Fin 6) (Fin 3) ℝ) (omega : Fin 3 → ℝ) (nu : Fin 6 → ℝ) :
    eq34dConformingSelector G *ᵥ eq34dDeclaredStack omega nu = nu - G *ᵥ omega := by
  rw [eq34dConformingSelector, eq34dDeclaredStack, Matrix.fromCols_mulVec_sumElim,
    Matrix.neg_mulVec, Matrix.one_mulVec]
  abel

/-! #### The type-level witness

Applying the printed selector to the declared stack does not elaborate:
`Matrix.mulVec` forces the matrix column index and the vector index to be the
same type, and here they are `Fin 6 ⊕ Fin 3` against `Fin 3 ⊕ Fin 6`.

`#check_failure` fails the build if this expression ever starts to elaborate;
`#guard_msgs` fails the build if it stops failing for this particular reason.
The pinned text is the type checker's verbatim rejection.  Nothing is added to
the environment, so this witness carries no axiom footprint — the `sorry` in
the echoed term is the elaborator's error placeholder for the rejected
argument, not an admitted proof. -/

/--
info: Application type mismatch: The argument
  eq34dDeclaredStack omega nu
has type
  Fin 3 ⊕ Fin 6 → ℝ
but is expected to have type
  Fin 6 ⊕ Fin 3 → ℝ
in the application
  eq34dPrintedSelector G *ᵥ eq34dDeclaredStack omega nu
---
info: fun G omega nu ↦ eq34dPrintedSelector G *ᵥ sorry : Matrix (Fin 6) (Fin 3) ℝ → (Fin 3 → ℝ) → (Fin 6 → ℝ) → Fin 6 → ℝ
-/
#guard_msgs in
#check_failure fun (G : Matrix (Fin 6) (Fin 3) ℝ) (omega : Fin 3 → ℝ)
    (nu : Fin 6 → ℝ) => eq34dPrintedSelector G *ᵥ eq34dDeclaredStack omega nu

end Ctrllib

#print axioms Ctrllib.eq31_printed_sign_counterexample
#print axioms Ctrllib.eq34d_printed_block_order_counterexample
#print axioms Ctrllib.eq34d_declared_block_widths_differ
#print axioms Ctrllib.eq34dConformingSelector_mulVec_declaredStack
