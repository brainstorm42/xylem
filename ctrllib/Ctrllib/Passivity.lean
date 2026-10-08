/-
The passivity identity (giordano2019coordinated eq 23) as matrix lemmas
(L3 sub-phase iii of the ctrllib stream).

The framing paper states eq 23 in quadratic-form shape — v̆ᵀ(Ṁ̆ − 2C̆)v̆ = 0
for all v̆ — and asserts it "automatically holds" from the transformation
machinery, without exhibiting the construction. The construction anchor in
the corpus is ott2008cartesian Lemma 3.2: skew symmetry of Λ̇ − 2μ follows
from the equality Ṁ = C + Cᵀ (its Property 2.6 + Lemma A.22 — equivalently,
the Christoffel-symbol choice of the Coriolis matrix).

Formalized at matrix-value level: at any instant, if the inertia-rate value
Ṁ equals C + Cᵀ, then Ṁ − 2C is skew-symmetric, and the quadratic form of a
skew-symmetric matrix vanishes — together, eq 23.

Human derivation: the corresponding derivation record (not bundled)
-/
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

open Matrix

namespace Ctrllib

variable {n : Type*}

/-- ott2008cartesian Lemma 3.2 shape: if `Ṁ = C + Cᵀ` (the Christoffel-symbol
choice of the Coriolis matrix), then `Ṁ − 2C` is skew-symmetric. Over any
commutative ring; symmetry of `Ṁ` is not assumed — it follows from the
hypothesis. -/
theorem mdot_sub_two_coriolis_skew {R : Type*} [CommRing R]
    {Mdot C : Matrix n n R} (hM : Mdot = C + Cᵀ) :
    (Mdot - 2 • C)ᵀ = -(Mdot - 2 • C) := by
  subst hM
  ext i j
  simp [two_smul]

/-- The quadratic form of a skew-symmetric real matrix vanishes. -/
theorem dotProduct_mulVec_self_of_skew [Fintype n] {A : Matrix n n ℝ}
    (hA : Aᵀ = -A) (x : n → ℝ) : x ⬝ᵥ A *ᵥ x = 0 := by
  have h1 : x ⬝ᵥ A *ᵥ x = (x ᵥ* A) ⬝ᵥ x := dotProduct_mulVec x A x
  have h2 : x ᵥ* A = -(A *ᵥ x) := by
    rw [← mulVec_transpose, hA, neg_mulVec]
  have h3 : x ⬝ᵥ A *ᵥ x = -((A *ᵥ x) ⬝ᵥ x) := by
    rw [h1, h2, neg_dotProduct]
  have h4 : (A *ᵥ x) ⬝ᵥ x = x ⬝ᵥ A *ᵥ x := dotProduct_comm _ _
  linarith [h3, h4]

/-- giordano2019coordinated eq 23: with the Christoffel-consistent Coriolis
matrix, the velocity quadratic form of `Ṁ − 2C` vanishes identically. -/
theorem passivity_identity [Fintype n] {Mdot C : Matrix n n ℝ} (hM : Mdot = C + Cᵀ)
    (v : n → ℝ) : v ⬝ᵥ (Mdot - 2 • C) *ᵥ v = 0 :=
  dotProduct_mulVec_self_of_skew (mdot_sub_two_coriolis_skew hM) v

end Ctrllib

#print axioms Ctrllib.mdot_sub_two_coriolis_skew
#print axioms Ctrllib.dotProduct_mulVec_self_of_skew
#print axioms Ctrllib.passivity_identity
