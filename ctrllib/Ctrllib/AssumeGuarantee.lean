/-!
# Relational assume–guarantee interfaces

A small non-temporal composition rule for mathematical components. Inputs and
outputs may themselves be trajectories or random variables, but this module
supplies no temporal logic, deadlines, flow existence, or probabilistic law.
The conventional argument and application obligations are in the corresponding derivation record's
the corresponding local note.
-/

namespace Ctrllib.AssumeGuarantee

universe u v w z

structure Contract (X : Type u) (Y : Type v) where
  assumption : X → Prop
  guarantee : X → Y → Prop

variable {X : Type u} {Y : Type v} {U : Type w} {Z : Type z}

/-- Every permitted implementation output meets the guarantee on admissible inputs.
This is partial correctness; it does not assert an output exists. -/
def Satisfies (R : X → Y → Prop) (C : Contract X Y) : Prop :=
  ∀ x y, C.assumption x → R x y → C.guarantee x y

/-- Existence of an implementation output is a separate obligation. -/
def Enabled (R : X → Y → Prop) (A : X → Prop) : Prop :=
  ∀ x, A x → ∃ y, R x y

/-- Wiring includes the mathematical conversion between interfaces. -/
def connected (R : X → Y → Prop) (S : U → Z → Prop) (wire : Y → U) : X → Z → Prop :=
  fun x z ↦ ∃ y, R x y ∧ S (wire y) z

/-- The composite assumption retains downstream compatibility for every output
allowed by the upstream contract, including nondeterministic outputs. -/
def sequential (C : Contract X Y) (D : Contract U Z) (wire : Y → U) : Contract X Z where
  assumption x := C.assumption x ∧ ∀ y, C.guarantee x y → D.assumption (wire y)
  guarantee x z := ∃ y, C.guarantee x y ∧ D.guarantee (wire y) z

theorem satisfies_sequential {R : X → Y → Prop} {S : U → Z → Prop}
    {C : Contract X Y} {D : Contract U Z} (wire : Y → U)
    (hR : Satisfies R C) (hS : Satisfies S D) :
    Satisfies (connected R S wire) (sequential C D wire) := by
  intro x z hx ⟨y, hxy, hyz⟩
  have hy := hR x y hx.1 hxy
  exact ⟨y, hy, hS (wire y) z (hx.2 y hy) hyz⟩

theorem enabled_sequential {R : X → Y → Prop} {S : U → Z → Prop}
    {C : Contract X Y} {D : Contract U Z} (wire : Y → U)
    (hR : Satisfies R C) (eR : Enabled R C.assumption) (eS : Enabled S D.assumption) :
    Enabled (connected R S wire) (sequential C D wire).assumption := by
  intro x hx
  obtain ⟨y, hy⟩ := eR x hx.1
  obtain ⟨z, hz⟩ := eS (wire y) (hx.2 y (hR x y hx.1 hy))
  exact ⟨z, y, hy, hz⟩

/-- External premises are discharged explicitly; none disappears on composition. -/
theorem sequential_assumption_of_environment {C : Contract X Y} {D : Contract U Z}
    (wire : Y → U) (E : X → Prop)
    (hC : ∀ x, E x → C.assumption x)
    (hwire : ∀ x y, E x → C.guarantee x y → D.assumption (wire y)) :
    ∀ x, E x → (sequential C D wire).assumption x := by
  intro x hx
  exact ⟨hC x hx, fun y hy ↦ hwire x y hx hy⟩

/-- Replacement accepts every old admissible input and meets its guarantees
there. Stronger assumptions are not a valid general replacement. -/
def Refines (replacement original : Contract X Y) : Prop :=
  (∀ x, original.assumption x → replacement.assumption x) ∧
  ∀ x y, original.assumption x → replacement.guarantee x y → original.guarantee x y

theorem satisfies_of_refines {R : X → Y → Prop} {C D : Contract X Y}
    (h : Refines D C) (hR : Satisfies R D) : Satisfies R C := by
  intro x y hx hxy
  exact h.2 x y hx (hR x y (h.1 x hx) hxy)

/-- Mutually supporting implications alone establish neither claim. -/
theorem circular_implications_insufficient :
    ¬ (∀ P Q : Prop, (P → Q) → (Q → P) → P) := by
  intro h
  exact h False False (fun h ↦ h) (fun h ↦ h)

end Ctrllib.AssumeGuarantee

#print axioms Ctrllib.AssumeGuarantee.satisfies_sequential
#print axioms Ctrllib.AssumeGuarantee.enabled_sequential
#print axioms Ctrllib.AssumeGuarantee.sequential_assumption_of_environment
#print axioms Ctrllib.AssumeGuarantee.satisfies_of_refines
#print axioms Ctrllib.AssumeGuarantee.circular_implications_insufficient
