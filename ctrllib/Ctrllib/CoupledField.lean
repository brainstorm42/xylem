/-
TARGET G2 — the closed-loop coupled-block field, once (ctrllib infrastructure).

The shared prerequisite for the cascade's driven-block (`g₂`) analysis. Prop IV.1
step 2 (giordano2019coordinated §IV.D; the source model note §4.6 eqs 4.10/4.12; Giordano
eqs 37-38) studies the AUTONOMOUS coupled attitude+EE block — the CoM driver zeroed
(x̃_c = ẋ̃_c = 0 on Γ₂, so the eq-4.10 forcing drops):

    ẋ̃      = J_x̃ v̆                                     (eq 26 shape, J 9×9)
    M̆ v̇̆ = -C̆ v̆ - D̆ v̆ - J_x̃ᵀ K̆ x̃                  (eq 4.10 / 34b, forcing 0)

as the first-order field on the state y = (x̃, v̆):

    g₂(y) = ( J v̆ ,  -M̆⁻¹( C̆ v̆ + D̆ v̆ + J_x̃ᵀ K̆ x̃ ) ).

The storage/Lyapunov candidate (eq 37 / 4.15) is the mechanical energy

    V(y) = ½⟪v̆, M̆ v̆⟫ + ½⟪x̃, K̆ x̃⟫ .

THIS MODULE IS INFRASTRUCTURE — no stability claims. It defines the field, the
energy, and the fderiv-friendly form the hdec lane differentiates along, following
the `ComLaSalle` formulation pattern (abstract real inner-product space `H`, the
operators M̆,C̆,D̆,K̆,J,M̆⁻¹,Jᵀ as continuous linear maps, adjoint/inverse supplied
with their defining identities as named hypotheses — the `hMinv` precedent).

WHAT IS PROVEN (real content, non-vacuous):
  `g2Field_origin`         — g₂(0) = 0 (the origin is an equilibrium; pure linearity).
  `coupledEnergy_origin`   — V(0) = 0.
  `coupledEnergy_differentiable` — V ∈ C¹ (quadratic form of continuous operators).
  `coupledEnergy_fderiv`   — THE reusable stone: for M̆,K̆ symmetric, the state-space
    derivative in ANY direction w is `DV(y)[w] = ⟪v̆, M̆ w.2⟫ + ⟪x̃, K̆ w.1⟫`. The hdec
    lane plugs w = g₂(y) (below) AND the time-varying-M̆ correction direction.
  `coupledEnergy_fderiv_field` — the field specialization the pin froze:
    `DV(y)[g₂(y)] = -⟪v̆, C̆ v̆⟫ - ⟪v̆, D̆ v̆⟫`. The STIFFNESS cross terms cancel
    (K̆ symmetric + Jᵀ the adjoint of J) — the "cross-term bookkeeping" of the house
    derivation. This is NOT sign-definite (the Coriolis term survives): that is why
    it is infrastructure, not a stability claim.

SymPy-pinned (the corresponding symbolic check (not bundled).py) BEFORE freezing the definition:
  (1) TOTAL derivative along the field (M̆ time-varying, house eq 38):
      d/dt V = -v̆ᵀD̆v̆ + ½v̆ᵀ(Ṁ̆ - 2C̆)v̆, symbolic n=2,3 + numeric n=3,6,9.
  (2) the STATE-SPACE partial `DV[g₂] = -v̆ᵀC̆v̆ - v̆ᵀD̆v̆` (this module's field lemma);
  (3) g₂(0)=0; (4) M̆ symmetry is load-bearing for the gradient half-term collapse.

INTERFACE BOUNDARY (honest). The sign-definite dissipation `d/dt V = -v̆ᵀD̆v̆ ≤ 0`
(eq 38, the hdec lane's target) is the TOTAL time derivative, which adds to the
state-space partial above the term `½v̆ᵀṀ̆v̆` from the time-varying inertia M̆(q(t)).
Giordano eq 23 passivity — the sealed `Ctrllib.passivity_identity` /
`transported_passivity_identity` — gives `½v̆ᵀṀ̆v̆ = v̆ᵀC̆v̆`, exactly cancelling the
Coriolis term the field lemma leaves. Both the time-varying-M̆ curve and that
passivity cancellation are the hdec lane's, named here, not smuggled. The adjoint
`Jᵀ = Jadj` and inverse `M̆⁻¹ = Minv` are supplied operators with defining
identities (`hJadj`, `hMinv`) — the ComLaSalle `hMinv` precedent; for concrete
matrices on `EuclideanSpace` these are `Matrix.toEuclideanCLM` facts.

Human derivation: the corresponding derivation record (not bundled)
-/
import Mathlib.Analysis.InnerProductSpace.Calculus

open scoped InnerProductSpace

namespace Ctrllib

section CoupledBlock

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  (M C D K J Minv Jadj : H →L[ℝ] H)

/-- The state space of the coupled error block: error `×` velocity, `y = (x̃, v̆)`
(so `y.1 = x̃`, `y.2 = v̆`). -/
abbrev CoupledState (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] := H × H

/-- The autonomous coupled-block field `g₂(y) = (J v̆, -M̆⁻¹(C̆ v̆ + D̆ v̆ + Jᵀ K̆ x̃))`
(the source model note eq 4.10 / Giordano eq 34b, CoM forcing zeroed). `Minv` is the given
inverse of `M̆`, `Jadj` the given adjoint of `J`. -/
def g2Field (y : CoupledState H) : CoupledState H :=
  (J y.2, -(Minv (C y.2 + D y.2 + Jadj (K y.1))))

/-- The mechanical energy `V(y) = ½⟪v̆, M̆ v̆⟫ + ½⟪x̃, K̆ x̃⟫` (eq 37 / 4.15). -/
noncomputable def coupledEnergy (y : CoupledState H) : ℝ :=
  (1 / 2 : ℝ) * ⟪y.2, M y.2⟫_ℝ + (1 / 2 : ℝ) * ⟪y.1, K y.1⟫_ℝ

variable {M C D K J Minv Jadj}

/-- **The origin is an equilibrium.** `g₂(0) = 0` — pure linearity of the operators,
no hypotheses. -/
theorem g2Field_origin : g2Field C D K J Minv Jadj 0 = 0 := by
  simp [g2Field]

/-- **`V(0) = 0`.** -/
theorem coupledEnergy_origin : coupledEnergy M K 0 = 0 := by
  simp [coupledEnergy]

/-- `V` is differentiable everywhere (quadratic form of continuous operators). -/
theorem coupledEnergy_differentiable : Differentiable ℝ (coupledEnergy M K) := by
  intro y
  have h1 : DifferentiableAt ℝ (fun w : CoupledState H => ⟪w.2, M w.2⟫_ℝ) y :=
    differentiableAt_snd.inner ℝ (M.differentiableAt.comp y differentiableAt_snd)
  have h2 : DifferentiableAt ℝ (fun w : CoupledState H => ⟪w.1, K w.1⟫_ℝ) y :=
    differentiableAt_fst.inner ℝ (K.differentiableAt.comp y differentiableAt_fst)
  exact (h1.const_mul _).add (h2.const_mul _)

/-- **The fderiv-friendly form (the reusable stone).** For `M̆, K̆` symmetric, the
state-space derivative of `V` in ANY direction `w` is `⟪v̆, M̆ w.2⟫ + ⟪x̃, K̆ w.1⟫`:
the gradient is `(K̆ x̃, M̆ v̆)`, the `½(S+Sᵀ)=S` collapse made exact by symmetry. The
hdec lane consumes this at `w = g₂(y)` and at the time-varying-M̆ correction
direction. -/
theorem coupledEnergy_fderiv
    (hMsa : ∀ a b : H, ⟪M a, b⟫_ℝ = ⟪a, M b⟫_ℝ)
    (hKsa : ∀ a b : H, ⟪K a, b⟫_ℝ = ⟪a, K b⟫_ℝ)
    (y w : CoupledState H) :
    fderiv ℝ (coupledEnergy M K) y w = ⟪y.2, M w.2⟫_ℝ + ⟪y.1, K w.1⟫_ℝ := by
  have hMf : DifferentiableAt ℝ (fun u : CoupledState H => M u.2) y :=
    M.differentiableAt.comp y differentiableAt_snd
  have hKf : DifferentiableAt ℝ (fun u : CoupledState H => K u.1) y :=
    K.differentiableAt.comp y differentiableAt_fst
  have hi1 : DifferentiableAt ℝ (fun u : CoupledState H => ⟪u.2, M u.2⟫_ℝ) y :=
    differentiableAt_snd.inner ℝ hMf
  have hi2 : DifferentiableAt ℝ (fun u : CoupledState H => ⟪u.1, K u.1⟫_ℝ) y :=
    differentiableAt_fst.inner ℝ hKf
  rw [show coupledEnergy M K =
      (fun u : CoupledState H => (1 / 2 : ℝ) * ⟪u.2, M u.2⟫_ℝ)
        + (fun u : CoupledState H => (1 / 2 : ℝ) * ⟪u.1, K u.1⟫_ℝ) from rfl]
  rw [fderiv_add (hi1.const_mul _) (hi2.const_mul _), add_apply,
    fderiv_const_mul hi1, fderiv_const_mul hi2, smul_apply,
    smul_apply, smul_eq_mul, smul_eq_mul,
    fderiv_inner_apply ℝ differentiableAt_snd hMf w,
    fderiv_inner_apply ℝ differentiableAt_fst hKf w]
  have d_fst : fderiv ℝ (Prod.fst : CoupledState H → H) y = ContinuousLinearMap.fst ℝ H H :=
    hasFDerivAt_fst.fderiv
  have d_snd : fderiv ℝ (Prod.snd : CoupledState H → H) y = ContinuousLinearMap.snd ℝ H H :=
    hasFDerivAt_snd.fderiv
  have d_Mf : fderiv ℝ (fun u : CoupledState H => M u.2) y
      = M.comp (ContinuousLinearMap.snd ℝ H H) :=
    (M.hasFDerivAt.comp y hasFDerivAt_snd).fderiv
  have d_Kf : fderiv ℝ (fun u : CoupledState H => K u.1) y
      = K.comp (ContinuousLinearMap.fst ℝ H H) :=
    (K.hasFDerivAt.comp y hasFDerivAt_fst).fderiv
  rw [d_fst, d_snd, d_Mf, d_Kf]
  simp only [ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.comp_apply]
  -- the two "reversed" inner products collapse by symmetry of M̆, K̆
  have eM : ⟪w.2, M y.2⟫_ℝ = ⟪y.2, M w.2⟫_ℝ := by
    rw [← hMsa w.2 y.2, real_inner_comm]
  have eK : ⟪w.1, K y.1⟫_ℝ = ⟪y.1, K w.1⟫_ℝ := by
    rw [← hKsa w.1 y.1, real_inner_comm]
  rw [eM, eK]; ring

/-- **The field specialization (the form the pin froze).** Along `g₂`, the
state-space derivative is `DV(y)[g₂(y)] = -⟪v̆, C̆ v̆⟫ - ⟪v̆, D̆ v̆⟫`. The stiffness
cross terms `-⟪v̆, Jᵀ K̆ x̃⟫` (momentum block) and `+⟪x̃, K̆ J v̆⟫` (stiffness block)
cancel because `K̆` is symmetric and `Jᵀ = Jadj` is the adjoint of `J`. The residual
Coriolis term `-⟪v̆, C̆ v̆⟫` is what the sealed passivity identity kills once the hdec
lane adds the time-varying-M̆ term `½⟪v̆, Ṁ̆ v̆⟫ = ⟪v̆, C̆ v̆⟫`. -/
theorem coupledEnergy_fderiv_field
    (hMsa : ∀ a b : H, ⟪M a, b⟫_ℝ = ⟪a, M b⟫_ℝ)
    (hKsa : ∀ a b : H, ⟪K a, b⟫_ℝ = ⟪a, K b⟫_ℝ)
    (hMinv : ∀ w : H, M (Minv w) = w)
    (hJadj : ∀ a b : H, ⟪J a, b⟫_ℝ = ⟪a, Jadj b⟫_ℝ)
    (y : CoupledState H) :
    fderiv ℝ (coupledEnergy M K) y (g2Field C D K J Minv Jadj y)
      = -⟪y.2, C y.2⟫_ℝ - ⟪y.2, D y.2⟫_ℝ := by
  rw [coupledEnergy_fderiv hMsa hKsa y (g2Field C D K J Minv Jadj y)]
  have hv : (g2Field C D K J Minv Jadj y).2 = -(Minv (C y.2 + D y.2 + Jadj (K y.1))) := rfl
  have hx : (g2Field C D K J Minv Jadj y).1 = J y.2 := rfl
  rw [hv, hx]
  have e1 : ⟪y.2, M (-(Minv (C y.2 + D y.2 + Jadj (K y.1))))⟫_ℝ
      = -(⟪y.2, C y.2⟫_ℝ + ⟪y.2, D y.2⟫_ℝ + ⟪y.2, Jadj (K y.1)⟫_ℝ) := by
    rw [map_neg, hMinv, inner_neg_right, inner_add_right, inner_add_right]
  have e2 : ⟪y.1, K (J y.2)⟫_ℝ = ⟪y.2, Jadj (K y.1)⟫_ℝ := by
    rw [← hKsa y.1 (J y.2), real_inner_comm (J y.2) (K y.1), hJadj y.2 (K y.1)]
  rw [e1, e2]; ring

end CoupledBlock

end Ctrllib

#print axioms Ctrllib.g2Field_origin
#print axioms Ctrllib.coupledEnergy_origin
#print axioms Ctrllib.coupledEnergy_differentiable
#print axioms Ctrllib.coupledEnergy_fderiv
#print axioms Ctrllib.coupledEnergy_fderiv_field
