/-
Γ invertibility ⟺ J⊕ invertibility (TARGET 3, difficulty S).

det Γ ≠ 0 ↔ det J⊕ ≠ 0  and  IsUnit Γ ↔ IsUnit J⊕ — the singularity biconditional.
Composes the L1 determinant identity `det_gamma_eq_det_J_oplus` (DetGamma.lean)
with `Matrix.isUnit_iff_isUnit_det`. Grounds the standing Ω-region side-condition
every downstream theorem assumes: the 12×12 coordinated transform Γ loses rank
exactly when its 6×6 circumcentroidal block J⊕ does.

Ω = {σ_min(J⊕) > 0} is the singularity-free region (the source model note eq 2.4 §4.6,
Giordano 2019 RA-L eq 19 / eq 36). The SVD fact σ_min(M) > 0 ↔ det M ≠ 0 is
INTERFACED as a named hypothesis `hsvd` in `gamma_isUnit_iff_sigmaMin_pos`:
Mathlib's `LinearMap.singularValues` lives on linear maps, not matrices, and no
library lemma packages `σ_min(matrix) > 0 ↔ det ≠ 0`. Building that bridge is the
singular-value machinery this determinant lemma deliberately does not invent. The
determinant / IsUnit biconditionals themselves are proved outright.

SymPy pin (biconditional teeth): the corresponding local note
Human derivation: the corresponding derivation record (not bundled)

Built in the lake workspace ~/lean/ctrllib (this file is the tracked mirror;
the build copy lives at Ctrllib/GammaInvertible.lean there).
-/
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Ctrllib.DetGamma

open Matrix

namespace Ctrllib

/-- **Abstract IsUnit biconditional.** Over any commutative ring, the coordinated
transform `fromBlocks Rot T 0 (fromBlocks 1 0 G J)` (with `det Rot = 1`) is a unit
iff its lower-right block `J` is. Composes `det_coordinated_transform` (L1) with
`Matrix.isUnit_iff_isUnit_det`. -/
theorem isUnit_coordinated_transform {R : Type*} [CommRing R]
    {l m n : Type*} [Fintype l] [Fintype m] [Fintype n]
    [DecidableEq l] [DecidableEq m] [DecidableEq n]
    (Rot : Matrix l l R) (hRot : Rot.det = 1)
    (T : Matrix l (m ⊕ n) R) (G : Matrix n m R) (J : Matrix n n R) :
    IsUnit (fromBlocks Rot T 0 (fromBlocks (1 : Matrix m m R) 0 G J)) ↔ IsUnit J := by
  rw [isUnit_iff_isUnit_det, isUnit_iff_isUnit_det J,
    det_coordinated_transform Rot hRot T G J]

/-- **Abstract nonsingularity biconditional.** The transform has nonzero
determinant iff its lower-right block does — an immediate consequence of the L1
determinant identity. -/
theorem det_ne_zero_coordinated_transform {R : Type*} [CommRing R]
    {l m n : Type*} [Fintype l] [Fintype m] [Fintype n]
    [DecidableEq l] [DecidableEq m] [DecidableEq n]
    (Rot : Matrix l l R) (hRot : Rot.det = 1)
    (T : Matrix l (m ⊕ n) R) (G : Matrix n m R) (J : Matrix n n R) :
    (fromBlocks Rot T 0 (fromBlocks (1 : Matrix m m R) 0 G J)).det ≠ 0 ↔ J.det ≠ 0 := by
  rw [det_coordinated_transform Rot hRot T G J]

/-- **Γ nonsingular ⟺ J⊕ nonsingular** (thesis shape: 12×12 over ℝ, `Rot ∈ SO(3)`).
The full coordinated transform is nonsingular exactly where the circumcentroidal
Jacobian is. -/
theorem gamma_nonsingular_iff
    (Rot : Matrix (Fin 3) (Fin 3) ℝ)
    (hRot : Rot ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (T : Matrix (Fin 3) ((Fin 3) ⊕ (Fin 6)) ℝ)
    (G : Matrix (Fin 6) (Fin 3) ℝ) (J : Matrix (Fin 6) (Fin 6) ℝ) :
    (fromBlocks Rot T 0 (fromBlocks (1 : Matrix (Fin 3) (Fin 3) ℝ) 0 G J)).det ≠ 0 ↔ J.det ≠ 0 := by
  rw [det_gamma_eq_det_J_oplus Rot hRot T G J]

/-- **Γ invertible ⟺ J⊕ invertible** (thesis shape). This is the standing Ω
side-condition of every downstream theorem, stated at matrix level: the controller
can invert Γ exactly where the circumcentroidal Jacobian is nonsingular. -/
theorem gamma_isUnit_iff
    (Rot : Matrix (Fin 3) (Fin 3) ℝ)
    (hRot : Rot ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (T : Matrix (Fin 3) ((Fin 3) ⊕ (Fin 6)) ℝ)
    (G : Matrix (Fin 6) (Fin 3) ℝ) (J : Matrix (Fin 6) (Fin 6) ℝ) :
    IsUnit (fromBlocks Rot T 0 (fromBlocks (1 : Matrix (Fin 3) (Fin 3) ℝ) 0 G J)) ↔ IsUnit J := by
  rw [isUnit_iff_isUnit_det, isUnit_iff_isUnit_det J, det_gamma_eq_det_J_oplus Rot hRot T G J]

/-- **Ω-region ⟺ Γ invertible.** With `sigmaMin` any candidate smallest-singular-
value map and `hsvd` the standard SVD fact (σ_min > 0 ⟺ nonsingular) supplied as a
NAMED INTERFACE hypothesis, the singularity-free region Ω = {σ_min(J⊕) > 0} is
exactly the set of configurations at which the coordinated transform Γ is invertible.

`hsvd` is interfaced, not proved: Mathlib's `LinearMap.singularValues` lives on
linear maps, and no library lemma packages `σ_min(matrix) > 0 ↔ det ≠ 0`; that is
the singular-value machinery this determinant lemma deliberately does not invent.
Everything downstream of `hsvd` — the reduction of the Ω condition to Γ — is proved. -/
theorem gamma_isUnit_iff_sigmaMin_pos
    (sigmaMin : Matrix (Fin 6) (Fin 6) ℝ → ℝ)
    (Rot : Matrix (Fin 3) (Fin 3) ℝ)
    (hRot : Rot ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (T : Matrix (Fin 3) ((Fin 3) ⊕ (Fin 6)) ℝ)
    (G : Matrix (Fin 6) (Fin 3) ℝ) (J : Matrix (Fin 6) (Fin 6) ℝ)
    (hsvd : 0 < sigmaMin J ↔ J.det ≠ 0) :
    0 < sigmaMin J
      ↔ IsUnit (fromBlocks Rot T 0 (fromBlocks (1 : Matrix (Fin 3) (Fin 3) ℝ) 0 G J)) := by
  rw [hsvd, gamma_isUnit_iff Rot hRot T G J, isUnit_iff_isUnit_det J, isUnit_iff_ne_zero]

end Ctrllib

#print axioms Ctrllib.isUnit_coordinated_transform
#print axioms Ctrllib.det_ne_zero_coordinated_transform
#print axioms Ctrllib.gamma_nonsingular_iff
#print axioms Ctrllib.gamma_isUnit_iff
#print axioms Ctrllib.gamma_isUnit_iff_sigmaMin_pos
