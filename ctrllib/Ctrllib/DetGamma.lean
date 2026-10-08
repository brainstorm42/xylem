/-
det Γ = det J⊕ — the coordinated-transform determinant identity (L1 pilot).

Γ per the corresponding local note source model note eq 2.4 (Giordano 2019 RA-L eq 19),
block rows/cols of sizes (3, 3, 6):

    Γ = [ R_cb   -R_cb·p_bc^×   R_cb·J̄_v ]
        [ 0       E              0        ]
        [ 0       G_ωb           J⊕       ]

Claim: det Γ = det J⊕. Only the zero blocks, det R_cb = 1, and E = 1 matter;
the top-right blocks and G_ωb are arbitrary. Human derivation:
the corresponding derivation record (not bundled)

Built in the lake workspace ~/lean/ctrllib (this file is the tracked mirror;
the build copy lives at Ctrllib/DetGamma.lean there).
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Data.Real.Basic

open Matrix

namespace Ctrllib

/-- Abstract shape of the coordinated transform: over any commutative ring,
`fromBlocks Rot T 0 (fromBlocks 1 0 G J)` with `det Rot = 1` has determinant
`det J`. The blocks `T` (top-right) and `G` (coupling) are arbitrary. -/
theorem det_coordinated_transform {R : Type*} [CommRing R]
    {l m n : Type*} [Fintype l] [Fintype m] [Fintype n]
    [DecidableEq l] [DecidableEq m] [DecidableEq n]
    (Rot : Matrix l l R) (hRot : Rot.det = 1)
    (T : Matrix l (m ⊕ n) R) (G : Matrix n m R) (J : Matrix n n R) :
    (fromBlocks Rot T 0 (fromBlocks 1 0 G J)).det = J.det := by
  rw [det_fromBlocks_zero₂₁]
  rw [det_fromBlocks_zero₁₂]
  rw [hRot]
  rw [det_one]
  rw [one_mul]
  rw [one_mul]

/-- Thesis instantiation: the 12×12 coordinated transform over ℝ (block sizes
3, 3, 6) with the base-to-CoM rotation an element of SO(3). -/
theorem det_gamma_eq_det_J_oplus
    (Rot : Matrix (Fin 3) (Fin 3) ℝ)
    (hRot : Rot ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (T : Matrix (Fin 3) ((Fin 3) ⊕ (Fin 6)) ℝ)
    (G : Matrix (Fin 6) (Fin 3) ℝ) (J : Matrix (Fin 6) (Fin 6) ℝ) :
    (fromBlocks Rot T 0 (fromBlocks 1 0 G J)).det = J.det :=
  det_coordinated_transform Rot (mem_specialOrthogonalGroup_iff.mp hRot).2 T G J

end Ctrllib

#print axioms Ctrllib.det_coordinated_transform
#print axioms Ctrllib.det_gamma_eq_det_J_oplus
