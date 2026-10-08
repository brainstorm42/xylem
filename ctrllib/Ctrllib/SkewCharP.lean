/-
TARGET 21 (FILLER) — the skew quadratic form vanishes over any field of
characteristic != 2.

Generalizes the sealed `Ctrllib.dotProduct_mulVec_self_of_skew`
(Passivity.lean, over ℝ) to an arbitrary field `F` with `ringChar F ≠ 2`.
The sealed ℝ proof used only "a scalar equal to its own negative is zero";
over a field that fact is exactly `Ring.eq_self_iff_eq_zero_of_char_ne_two`
(a domain of char != 2 has `-a = a ↔ a = 0`). Everything else is the same
transpose/dot-product algebra, which already lives over any commutative ring.

The `char != 2` hypothesis is necessary: over GF(2), skew = symmetric, so
`A = diag(1)` is skew yet `x ⬝ᵥ A *ᵥ x = 1 ≠ 0` at `x = (1)`. See the SymPy
pin `the corresponding private check` and the derivation the corresponding local note.

Human derivation: the corresponding derivation record (not bundled)
-/
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.Field.Basic

open Matrix

namespace Ctrllib

variable {n : Type*}

/-- The quadratic form of a skew-symmetric matrix vanishes over any field of
characteristic `≠ 2`. Char-`≠ 2` generalization of the ℝ-only sealed
`Ctrllib.dotProduct_mulVec_self_of_skew`; the only characteristic-sensitive
step is `-s = s ⟹ s = 0`, supplied by `Ring.eq_self_iff_eq_zero_of_char_ne_two`. -/
theorem dotProduct_mulVec_self_of_skew_of_charP
    {F : Type*} [Field F] (hF : ringChar F ≠ 2) [Fintype n]
    {A : Matrix n n F} (hA : Aᵀ = -A) (x : n → F) : x ⬝ᵥ A *ᵥ x = 0 := by
  have h1 : x ⬝ᵥ A *ᵥ x = (x ᵥ* A) ⬝ᵥ x := dotProduct_mulVec x A x
  have h2 : x ᵥ* A = -(A *ᵥ x) := by
    rw [← mulVec_transpose, hA, neg_mulVec]
  have h3 : x ⬝ᵥ A *ᵥ x = -((A *ᵥ x) ⬝ᵥ x) := by
    rw [h1, h2, neg_dotProduct]
  have h4 : (A *ᵥ x) ⬝ᵥ x = x ⬝ᵥ A *ᵥ x := dotProduct_comm _ _
  rw [h4] at h3
  exact (Ring.eq_self_iff_eq_zero_of_char_ne_two hF).mp h3.symm

end Ctrllib

#print axioms Ctrllib.dotProduct_mulVec_self_of_skew_of_charP
