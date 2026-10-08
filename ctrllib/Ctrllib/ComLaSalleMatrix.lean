/-
CoM loop attractivity for a CONCRETE symmetric-positive-definite model (G1 sub-item b) —
the matrix corollary that discharges `com_attractive`'s six operator hypotheses.

`com_attractive` (ComLaSalle.lean) is stated abstractly over an inner-product space `H`
with the inertia/damping/stiffness carried as continuous linear operators
`M, D, K : H →L[ℝ] H` plus their defining identities as NAMED hypotheses
(`hMsa/hKsa` symmetry, `hMinv` inverse, `hDnn/hDdef` damping sign, `hKdef`
stiffness injectivity). For the actual thesis model those operators are concrete
symmetric positive-definite MATRICES (the source model note §4.3, the CoM block
`m x'' + D x' + K x = 0`), so the six hypotheses are not assumptions but
theorems. This module proves exactly that, via `Matrix.toEuclideanCLM` (the
matrix → operator bridge) and the sealed Rayleigh / PosDef stones, and wires
them into `com_attractive` to give `com_attractive_matrix`.

Defense line (ratified G1 bar): kernel-proved for every system with the stated
structure (`com_attractive`); our model verifiably has it (`com_attractive_matrix`, the six
`euclideanCLM_*` discharges, SymPy-pinned on the 3×3 CoM block).

DISCHARGE ROUTES (the corresponding local note "concrete-SPD operator hypotheses" rows):
  hMsa/hKsa  ← `euclideanCLM_self_adjoint`  (Matrix.IsHermitian, real → Aᵀ = A)
  hMinv      ← `euclideanCLM_inv`           (Matrix.mul_nonsing_inv)
  hDnn       ← `euclideanCLM_dotProduct_nonneg`  (sealed `le_dotProduct_mulVec`, c₁ = 0)
  hDdef      ← `euclideanCLM_dotProduct_def`     (Matrix.PosDef.dotProduct_mulVec_pos)
  hKdef      ← `euclideanCLM_injective`          (PosDef.isUnit + mulVec_injective_of_isUnit)

STILL INTERFACED (unchanged, by design — the (c) refactor / flow existence):
  `IsSolutionTo ϕ (comField …)` and `hcpt` (orbit precompactness) stay
  applier-side, exactly as in `com_attractive`; this corollary discharges ONLY the
  operator algebra.

SymPy pin: the corresponding symbolic check (not bundled).py.
Human derivation: the corresponding derivation record (not bundled)
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.PosDef
import Ctrllib.ComLaSalle
import Ctrllib.Rayleigh

open Set Filter Topology Matrix
open scoped InnerProductSpace

namespace Ctrllib

-- The eigenvalue / inverse machinery needs `DecidableEq` in the *proofs*; it does
-- not surface in the statements (same pattern as BlockLyapunov / StiffnessResidual).
set_option linter.unusedDecidableInType false

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}

omit [DecidableEq n] in
/-- Symmetric quadratic-form symmetry: for a real Hermitian `A`, the bilinear
form is symmetric, `a ⬝ᵥ A *ᵥ b = b ⬝ᵥ A *ᵥ a` (`Aᵀ = A` over `ℝ`). -/
private lemma quad_symm (hA : A.IsHermitian) (a b : n → ℝ) :
    a ⬝ᵥ A *ᵥ b = b ⬝ᵥ A *ᵥ a := by
  have hAT : Aᵀ = A := by
    rw [← conjTranspose_eq_transpose_of_trivial]; exact hA.eq
  rw [dotProduct_mulVec b A a, dotProduct_comm (b ᵥ* A) a, ← mulVec_transpose A b, hAT]

/-- **`hMsa`/`hKsa` discharge.** For a real symmetric matrix `A`, its Euclidean
operator `toEuclideanCLM A` is self-adjoint: `⟪A x, y⟫ = ⟪x, A y⟫`. -/
theorem euclideanCLM_self_adjoint (hA : A.IsHermitian) (a b : EuclideanSpace ℝ n) :
    ⟪toEuclideanCLM (𝕜 := ℝ) A a, b⟫_ℝ = ⟪a, toEuclideanCLM (𝕜 := ℝ) A b⟫_ℝ := by
  rw [inner_toEuclideanCLM, real_inner_comm, inner_toEuclideanCLM]
  exact quad_symm hA b a

/-- **`hMinv` discharge.** For positive-definite `A`, `toEuclideanCLM A⁻¹` is a
right inverse of `toEuclideanCLM A`: `A (A⁻¹ w) = w`. -/
theorem euclideanCLM_inv (hA : A.PosDef) (w : EuclideanSpace ℝ n) :
    toEuclideanCLM (𝕜 := ℝ) A (toEuclideanCLM (𝕜 := ℝ) A⁻¹ w) = w := by
  have hdet : IsUnit A.det := (isUnit_iff_isUnit_det _).mp hA.isUnit
  apply WithLp.ofLp_injective
  rw [ofLp_toEuclideanCLM, ofLp_toEuclideanCLM, mulVec_mulVec, mul_nonsing_inv A hdet, one_mulVec]

/-- **`hDnn` discharge.** For positive-definite `A`, the damping form is
nonnegative: `0 ≤ ⟪v, A v⟫` (sealed Rayleigh lower bound with `c₁ = 0`). -/
theorem euclideanCLM_dotProduct_nonneg (hA : A.PosDef) (v : EuclideanSpace ℝ n) :
    0 ≤ ⟪v, toEuclideanCLM (𝕜 := ℝ) A v⟫_ℝ := by
  rw [inner_toEuclideanCLM]
  have h := le_dotProduct_mulVec hA.isHermitian (c₁ := 0)
    (fun i => (hA.eigenvalues_pos i).le) v
  simpa using h

/-- **`hDdef` discharge.** For positive-definite `A`, the damping form is
definite: `⟪v, A v⟫ = 0 → v = 0`. -/
theorem euclideanCLM_dotProduct_def (hA : A.PosDef) (v : EuclideanSpace ℝ n) :
    ⟪v, toEuclideanCLM (𝕜 := ℝ) A v⟫_ℝ = 0 → v = 0 := by
  rw [inner_toEuclideanCLM]
  intro h
  by_contra hv
  have hv' : WithLp.ofLp v ≠ 0 := by simpa using hv
  have hpos := hA.dotProduct_mulVec_pos (x := WithLp.ofLp v) hv'
  rw [star_trivial] at hpos
  linarith

/-- **`hKdef` discharge.** For positive-definite `A`, the stiffness operator is
injective at the origin: `A x = 0 → x = 0` (PosDef ⇒ unit ⇒ `mulVec` injective). -/
theorem euclideanCLM_injective (hA : A.PosDef) (x : EuclideanSpace ℝ n) :
    toEuclideanCLM (𝕜 := ℝ) A x = 0 → x = 0 := by
  intro h
  have hz : A *ᵥ WithLp.ofLp x = 0 := by rw [← ofLp_toEuclideanCLM, h]; simp
  have hx : WithLp.ofLp x = 0 := by
    apply mulVec_injective_of_isUnit hA.isUnit
    rw [mulVec_zero]; exact hz
  simpa using hx

/-- **CoM-loop attractivity for a concrete SPD model** (G1 sub-item b headline).
Given concrete symmetric positive-definite inertia, damping and stiffness matrices
`Mm, Dm, Km`, every forward-precompact orbit of the closed-loop CoM field converges
to the origin — attractivity of forward-precompact trajectories, not ε–δ stability
(see `KhalilStability.AsympStable`; formerly named `com_gas_matrix`). All six operator
hypotheses of `com_attractive` are discharged here as theorems (`euclideanCLM_*`); only
flow existence (`IsSolutionTo`) and orbit precompactness (`hcpt`) remain applier-side,
exactly as in `com_attractive`. -/
theorem com_attractive_matrix (Mm Dm Km : Matrix n n ℝ)
    (hM : Mm.PosDef) (hD : Dm.PosDef) (hK : Km.PosDef)
    (ϕ : Flow ℝ (ComState (EuclideanSpace ℝ n)))
    (hϕ : IsSolutionTo ϕ (comField (toEuclideanCLM (𝕜 := ℝ) Dm)
      (toEuclideanCLM (𝕜 := ℝ) Km) (toEuclideanCLM (𝕜 := ℝ) Mm⁻¹)))
    (z₀ : ComState (EuclideanSpace ℝ n))
    (hcpt : ForwardPrecompact ϕ z₀) :
    Tendsto (fun t : ℝ => ϕ t z₀) atTop (𝓝 0) :=
  com_attractive ϕ hϕ
    (euclideanCLM_self_adjoint hM.isHermitian)
    (euclideanCLM_self_adjoint hK.isHermitian)
    (euclideanCLM_inv hM)
    (euclideanCLM_dotProduct_nonneg hD)
    (euclideanCLM_dotProduct_def hD)
    (euclideanCLM_injective hK)
    z₀ hcpt

@[deprecated com_attractive_matrix (since := "2026-08-15")]
alias com_gas_matrix := com_attractive_matrix

end Ctrllib

#print axioms Ctrllib.euclideanCLM_self_adjoint
#print axioms Ctrllib.euclideanCLM_inv
#print axioms Ctrllib.euclideanCLM_dotProduct_nonneg
#print axioms Ctrllib.euclideanCLM_dotProduct_def
#print axioms Ctrllib.euclideanCLM_injective
#print axioms Ctrllib.com_attractive_matrix
