/-
Coupled-block attractivity for a CONCRETE SPD model + the 6-DOF Γ rank fact (G1 sub-item d)
— the matrix corollary that discharges `coupled_attractive`'s operator hypotheses (the
hzero step on the concrete `g2Field`), and the Ω-region full-rank fact for the
circumcentroidal Jacobian.

`coupled_attractive` (CoupledCollapse.lean) is Prop IV.1's convergence for the driven
attitude+EE block, assembled through the INVARIANCE route (rung-2's honest
finding: the pointwise `hzero` is FALSE — the Lyapunov-derivative zero set is the
whole subspace `{v̆ = 0}`, not `{0}` — so the origin is reached only via LaSalle
invariance `v̆ ≡ 0 ⇒ v̇̆ ≡ 0 ⇒ J_x̃ᵀ K̆ x̃ = 0 ⇒ x̃ = 0`). Its eight operator
hypotheses (symmetry, inverse, adjoint, passivity, D̆ sign, stiffness-residual
injectivity) are, for the concrete SPD model, theorems. This module proves them
via `Matrix.toEuclideanCLM` and the sealed stones, and wires them into
`coupled_attractive` to give `coupled_attractive_matrix` — the concrete-model witness of the
LaSalle-route hzero collapse on `g2Field`.

DISCHARGE ROUTES (the corresponding local note "concrete-SPD operator hypotheses" rows):
  hMsa/hKsa ← `euclideanCLM_self_adjoint`            (reused from ComLaSalleMatrix)
  hMinv     ← `euclideanCLM_inv`                     (reused)
  hDnn      ← `euclideanCLM_dotProduct_nonneg`       (reused)
  hDdef     ← `euclideanCLM_dotProduct_def`          (reused)
  hJadj     ← `euclideanCLM_adjoint`                 (toEuclideanCLM Jᵀ is the adjoint)
  hpass     ← `euclideanCLM_passivity`               (from Ṁ̆ = C̆ + C̆ᵀ, the Christoffel relation)
  (`hMinj` is derived inside `coupled_attractive` from `hMinv`;
   `euclideanCLM_injective_of_isUnit` remains available for `coupled_collapse`.)
  hJKinj    ← `euclideanCLM_stiffness_injective`     (sealed `stiffness_residual_injective'`)

STILL INTERFACED (unchanged, by design — the moving-metric bracket + flow):
  `hϕ` (IsSolutionTo), `hV` (Differentiable V), `hreal`/`hfield` (the true field's
  Fréchet-derivative / velocity component — the deferred analytic step), and
  `hcpt` (orbit precompactness) stay applier-side, exactly as in `coupled_attractive`.

Γ RANK (d, first half): `gamma_jacobian_mulVec_injective` — where Γ is invertible
(the singularity-free region Ω, GammaInvertible.gamma_isUnit_iff), the 6×6
circumcentroidal Jacobian J⊕ has full column rank (`mulVec` injective). The
concrete meaning of the source model note's "J full-rank on Ω".

SymPy pin: the corresponding symbolic check (not bundled).py.
Human derivation:
the corresponding derivation record (not bundled)
-/
import Ctrllib.CoupledCollapse
import Ctrllib.ComLaSalleMatrix
import Ctrllib.StiffnessResidual
import Ctrllib.GammaInvertible

open Set Filter Topology Matrix
open scoped InnerProductSpace

namespace Ctrllib

set_option linter.unusedDecidableInType false

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- The transpose quadratic form equals the untransposed one: `v ⬝ᵥ Cᵀ v = v ⬝ᵥ C v`. -/
private lemma dp_transpose_self (C : Matrix n n ℝ) (v : n → ℝ) :
    v ⬝ᵥ Cᵀ *ᵥ v = v ⬝ᵥ C *ᵥ v := by
  rw [mulVec_transpose, dotProduct_comm v (v ᵥ* C), ← dotProduct_mulVec]

/-- **`hJadj` discharge.** For any real matrix `J`, the Euclidean operator of its
transpose is the adjoint of `toEuclideanCLM J`: `⟪J a, b⟫ = ⟪a, Jᵀ b⟫`. -/
theorem euclideanCLM_adjoint (J : Matrix n n ℝ) (a b : EuclideanSpace ℝ n) :
    ⟪toEuclideanCLM (𝕜 := ℝ) J a, b⟫_ℝ = ⟪a, toEuclideanCLM (𝕜 := ℝ) Jᵀ b⟫_ℝ := by
  rw [inner_toEuclideanCLM, real_inner_comm, inner_toEuclideanCLM,
    mulVec_transpose, dotProduct_comm a (b ᵥ* J), ← dotProduct_mulVec]

/-- **`hpass` discharge.** From the Christoffel relation `Ṁ̆ = C̆ + C̆ᵀ` (the sealed
passivity content), the quadratic passivity identity `⟪v, Ṁ̆ v⟫ = 2⟪v, C̆ v⟫`. -/
theorem euclideanCLM_passivity {C Mdot : Matrix n n ℝ} (hchris : Mdot = C + Cᵀ)
    (v : EuclideanSpace ℝ n) :
    ⟪v, toEuclideanCLM (𝕜 := ℝ) Mdot v⟫_ℝ = 2 * ⟪v, toEuclideanCLM (𝕜 := ℝ) C v⟫_ℝ := by
  rw [inner_toEuclideanCLM, inner_toEuclideanCLM, hchris, add_mulVec, dotProduct_add,
    dp_transpose_self]
  ring

/-- **`hMinj` discharge** (for `coupled_collapse`; `coupled_attractive` derives `hMinj` from
`hMinv`). For a unit matrix `A`, its Euclidean operator is
injective (used for `Minv = toEuclideanCLM M̆⁻¹`, a unit since `M̆` is). -/
theorem euclideanCLM_injective_of_isUnit {A : Matrix n n ℝ} (hA : IsUnit A) :
    Function.Injective (toEuclideanCLM (𝕜 := ℝ) A) := by
  intro a b hab
  apply WithLp.ofLp_injective
  apply mulVec_injective_of_isUnit hA
  rw [← ofLp_toEuclideanCLM, ← ofLp_toEuclideanCLM, hab]

/-- **`hJKinj` discharge.** For `K̆` positive-definite and the representation
Jacobian `J` full column rank (`mulVec` injective — StiffnessResidual pin D:
nonsingular on Ω), the stiffness residual is injective at the origin:
`Jᵀ (K̆ x̃) = 0 → x̃ = 0`. The operator transcription of the sealed
`stiffness_residual_injective'`. -/
theorem euclideanCLM_stiffness_injective {K J : Matrix n n ℝ} (hK : K.PosDef)
    (hJ : Function.Injective J.mulVec) (x : EuclideanSpace ℝ n) :
    toEuclideanCLM (𝕜 := ℝ) Jᵀ (toEuclideanCLM (𝕜 := ℝ) K x) = 0 → x = 0 := by
  intro h
  have hz : Jᵀ *ᵥ (K *ᵥ WithLp.ofLp x) = 0 := by
    rw [← ofLp_toEuclideanCLM, ← ofLp_toEuclideanCLM, h]; simp
  have hx : WithLp.ofLp x = 0 := stiffness_residual_injective' hK hJ hz
  simpa using hx

/-- **Circumcentroidal Jacobian full rank on Ω** (G1 sub-item d, Γ half). Where the
12×12 coordinated transform Γ is invertible — the singularity-free region Ω,
GammaInvertible.gamma_isUnit_iff — the 6×6 circumcentroidal Jacobian J⊕ has full
column rank (`mulVec` injective). The concrete content of "J full-rank on Ω". -/
theorem gamma_jacobian_mulVec_injective
    (Rot : Matrix (Fin 3) (Fin 3) ℝ)
    (hRot : Rot ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (T : Matrix (Fin 3) ((Fin 3) ⊕ (Fin 6)) ℝ)
    (G : Matrix (Fin 6) (Fin 3) ℝ) (J : Matrix (Fin 6) (Fin 6) ℝ)
    (hΓ : IsUnit (fromBlocks Rot T 0 (fromBlocks (1 : Matrix (Fin 3) (Fin 3) ℝ) 0 G J))) :
    Function.Injective J.mulVec :=
  mulVec_injective_of_isUnit ((gamma_isUnit_iff Rot hRot T G J).mp hΓ)

/-- **Coupled-block attractivity for a concrete SPD model** (G1 sub-item d
headline — the hzero step on the concrete `g2Field`; attractivity of
forward-precompact trajectories, not ε–δ stability, see `KhalilStability.AsympStable`;
formerly named `coupled_gas_matrix`). Given concrete
symmetric positive-definite reduced inertia `Mm`, damping `Dm`, stiffness `Km`,
the Christoffel matrix `Cm` with `Ṁ̆ = Cm + Cmᵀ`, and a nonsingular representation
Jacobian `Jm` (full rank on Ω), every precompact orbit of the coupled closed-loop
block converges to the origin. All eight operator hypotheses of `coupled_attractive` are
discharged here as theorems; only flow existence (`hϕ`), differentiability
(`hV`), the moving-metric bracket (`hreal`/`hfield`) and orbit precompactness
(`hcpt`) remain applier-side, exactly as in `coupled_attractive`. Scope of the
bracket: `hreal`/`hfield` pin `DV[f]` and the velocity field to the CONSTANT
matrices `Mm Cm Dm Km Jm Mdotm` at every state, so this is the concrete witness
that the LaSalle-route collapse (NOT the false pointwise hzero) holds for the
constant-operator SPD model; the configuration-dependent M̆(q) system with
`Ṁ̆ ≠ 0` is not an instance of this statement. -/
theorem coupled_attractive_matrix (Mm Cm Dm Km Jm Mdotm : Matrix n n ℝ)
    (hM : Mm.PosDef) (hD : Dm.PosDef) (hK : Km.PosDef)
    (hJ : IsUnit Jm) (hchris : Mdotm = Cm + Cmᵀ)
    (ϕ : Flow ℝ (CoupledState (EuclideanSpace ℝ n)))
    {V : CoupledState (EuclideanSpace ℝ n) → ℝ}
    {f : CoupledState (EuclideanSpace ℝ n) → CoupledState (EuclideanSpace ℝ n)}
    (hϕ : IsSolutionTo ϕ f) (hV : Differentiable ℝ V)
    (hreal : ∀ y, fderiv ℝ V y (f y) = coupledLyapRate
      (toEuclideanCLM (𝕜 := ℝ) Mm) (toEuclideanCLM (𝕜 := ℝ) Cm) (toEuclideanCLM (𝕜 := ℝ) Dm)
      (toEuclideanCLM (𝕜 := ℝ) Km) (toEuclideanCLM (𝕜 := ℝ) Jm) (toEuclideanCLM (𝕜 := ℝ) Mm⁻¹)
      (toEuclideanCLM (𝕜 := ℝ) Jmᵀ) (toEuclideanCLM (𝕜 := ℝ) Mdotm) y)
    (hfield : ∀ y, (f y).2 = (g2Field (toEuclideanCLM (𝕜 := ℝ) Cm) (toEuclideanCLM (𝕜 := ℝ) Dm)
      (toEuclideanCLM (𝕜 := ℝ) Km) (toEuclideanCLM (𝕜 := ℝ) Jm) (toEuclideanCLM (𝕜 := ℝ) Mm⁻¹)
      (toEuclideanCLM (𝕜 := ℝ) Jmᵀ) y).2)
    (y₀ : CoupledState (EuclideanSpace ℝ n))
    (hcpt : ForwardPrecompact ϕ y₀) :
    Tendsto (fun t : ℝ => ϕ t y₀) atTop (𝓝 0) :=
  coupled_attractive ϕ hϕ hV
    (euclideanCLM_self_adjoint hM.isHermitian)
    (euclideanCLM_self_adjoint hK.isHermitian)
    (euclideanCLM_inv hM)
    (euclideanCLM_adjoint Jm)
    (euclideanCLM_passivity hchris)
    hreal hfield
    (euclideanCLM_dotProduct_nonneg hD)
    (euclideanCLM_dotProduct_def hD)
    (euclideanCLM_stiffness_injective hK (mulVec_injective_of_isUnit hJ))
    y₀ hcpt

@[deprecated coupled_attractive_matrix (since := "2026-08-15")]
alias coupled_gas_matrix := coupled_attractive_matrix

end Ctrllib

#print axioms Ctrllib.euclideanCLM_adjoint
#print axioms Ctrllib.euclideanCLM_passivity
#print axioms Ctrllib.euclideanCLM_injective_of_isUnit
#print axioms Ctrllib.euclideanCLM_stiffness_injective
#print axioms Ctrllib.gamma_jacobian_mulVec_injective
#print axioms Ctrllib.coupled_attractive_matrix
