/-
Tracking-extension energy rate (the corresponding design note, gap 1) — the exact rate
identity of the tracking storage along the WORKING control equation
(the source model note eq 4.12; `the implemented dynamics expression`, the implementation revision
86a522b), naming the residual that separates the implemented tracking loop from
the regulator whose Lyapunov argument is already sealed
(BlockLyapunov / CoupledDissipation).

THE STEP. The regulator (Giordano eq 34b, 36–38) has V = ½v̆ᵀM̆v̆ + ½x̃ᵀK̆x̃ and
V̇ = −v̆ᵀD̆v̆ by passivity. The implemented tracking loop moves the damper onto the
velocity error e := v̆ − v̆_d and adds the acceleration feedforward M̆ v̇̆_d:

    M̆ v̇̆ = −C̆ v̆ − D̆ (v̆ − v̆_d) − J_x̃ᵀ K̆ x̃ − F + M̆ v̇̆_d,   F := (C_c + D̆ Ğ_vc) ẋ̃_c
                                                    (eq 4.12; `velocity_ff = False`)
    M̆ v̇̆ = −C̆ (v̆ − v̆_d) − D̆ (v̆ − v̆_d) − J_x̃ᵀ K̆ x̃ − F + M̆ v̇̆_d
                                                    (code branch `velocity_ff = True`)

with the tracking storage V_e := ½eᵀM̆e + ½x̃ᵀK̆x̃ = `blockLyap M K e x` and its rate
along (ė, ẋ̃), M̆ time-varying:  V̇_e = eᵀM̆ė + ½eᵀṀ̆e + x̃ᵀK̆ẋ̃.

WHAT IS PROVEN (value-level algebra at one instant, K̆ symmetric):
  `tracking_rate_identity`   — Coriolis on absolute velocity, error kinematics
      ẋ̃ = J_x̃ e:   V̇_e = −eᵀD̆e − eᵀC̆v̆_d − eᵀF + [½eᵀṀ̆e − eᵀC̆e].
  `tracking_rate_passive`    — with Ṁ̆ = C̆ + C̆ᵀ the bracket vanishes
      (Passivity.lean):       V̇_e = −eᵀD̆e − eᵀC̆v̆_d − eᵀF.
      The term −eᵀC̆v̆_d is THE RESIDUAL: it is absent from the regulator proof and
      does not vanish in general (pin (D): it can make V̇_e > 0 for D̆ ≻ 0).
  `tracking_rate_velocity_ff` — the code's `velocity_ff` branch removes it:
      V̇_e = −eᵀD̆e − eᵀF.
  `tracking_rate_velocity_ff_nonpos` — hence V̇_e ≤ 0 when D̆ ⪰ 0 and the CoM
      coupling F is zero (perfect CoM tracking).
  `tracking_rate_identity_absKin` — if instead the REGULATOR kinematics ẋ̃ = J_x̃ v̆
      are kept under tracking, a second term + x̃ᵀK̆J_x̃v̆_d survives.
  `tracking_storage_coercive` — the storage is the sealed block Lyapunov value,
      so it is coercive for M̆, K̆ ≻ 0 (BlockLyapunov.lean).

SYMPY-PINNED (the corresponding project check (not bundled).py):
  (A) identity + bracket = 0; (B) velocity_ff branch; (C) regulator-kinematics
  residual; (D) numeric witness that −eᵀDe − eᵀCv_d can be positive.

INTERFACE BOUNDARY (honest). These are pointwise identities in the matrices and
vectors of one instant; the ODE realisation (a flow whose derivative is the
displayed rate) is the same `IsSolutionTo`/`hreal` interface used by
CoupledDissipation.lean and is not discharged here. Which branch the fresh
nominal run used, and the sign/size of the residual along it, are simulation
evidence (the corresponding design note), not theorems. Nothing here claims convergence of the
tracking loop: the residual −eᵀC̆v̆_d is the named mathematical gap that a
convergence argument (the corresponding design note) must either remove (velocity_ff), bound
(TimeVaryingComparison.lean shape), or accept as a steady lag (CruiseLag.lean).
-/
import Ctrllib.Passivity
import Ctrllib.BlockLyapunov

open Matrix

namespace Ctrllib

variable {n m : Type*} [Fintype n] [Fintype m]

/-- Rate of the tracking storage `V_e = ½eᵀMe + ½xᵀKx` along `(ė, ẋ)` with `M`
time-varying (`Mdot` its rate): `eᵀM ė + ½ eᵀ Ṁ e + xᵀ K ẋ`. -/
noncomputable def trackingRate (M Mdot : Matrix n n ℝ) (K : Matrix m m ℝ)
    (e edot : n → ℝ) (x xdot : m → ℝ) : ℝ :=
  e ⬝ᵥ M *ᵥ edot + (1 / 2) * (e ⬝ᵥ Mdot *ᵥ e) + x ⬝ᵥ K *ᵥ xdot

/-- Stiffness cross term is symmetric under `Kᵀ = K`:
`eᵀ Jᵀ (K x) = xᵀ K (J e)`. -/
theorem stiffness_cross_symm {K : Matrix m m ℝ} (hK : Kᵀ = K)
    (J : Matrix m n ℝ) (x : m → ℝ) (e : n → ℝ) :
    e ⬝ᵥ Jᵀ *ᵥ (K *ᵥ x) = x ⬝ᵥ K *ᵥ (J *ᵥ e) := by
  rw [mulVec_transpose, dotProduct_comm, ← dotProduct_mulVec]
  rw [dotProduct_mulVec x K (J *ᵥ e)]
  congr 1
  rw [← vecMul_transpose, hK]

/-- Passivity bracket: with `Ṁ = C + Cᵀ`, `½ eᵀṀe − eᵀCe = 0` (Giordano eq 23). -/
theorem passivity_bracket {Mdot C : Matrix n n ℝ} (hM : Mdot = C + Cᵀ) (e : n → ℝ) :
    (1 / 2) * (e ⬝ᵥ Mdot *ᵥ e) - e ⬝ᵥ C *ᵥ e = 0 := by
  have h := passivity_identity hM e
  rw [two_smul, sub_mulVec, add_mulVec, dotProduct_sub, dotProduct_add] at h
  linarith

section Identity

variable {M Mdot C D : Matrix n n ℝ} {K : Matrix m m ℝ} {J : Matrix m n ℝ}
variable {v vd vdot vddot F : n → ℝ} {x xdot : m → ℝ}

/-- **Tracking rate identity, eq 4.12 as implemented** (`velocity_ff = False`:
Coriolis on the absolute velocity), with the error kinematics `ẋ = J (v − v_d)`.
The rate splits into pure damping, the RESIDUAL `−eᵀ C v_d`, the CoM-coupling
forcing, and the passivity bracket. -/
theorem tracking_rate_identity (hK : Kᵀ = K)
    (hdyn : M *ᵥ vdot = -(C *ᵥ v) - D *ᵥ (v - vd) - Jᵀ *ᵥ (K *ᵥ x) - F + M *ᵥ vddot)
    (hkin : xdot = J *ᵥ (v - vd)) :
    trackingRate M Mdot K (v - vd) (vdot - vddot) x xdot
      = -((v - vd) ⬝ᵥ D *ᵥ (v - vd)) - (v - vd) ⬝ᵥ C *ᵥ vd - (v - vd) ⬝ᵥ F
        + ((1 / 2) * ((v - vd) ⬝ᵥ Mdot *ᵥ (v - vd)) - (v - vd) ⬝ᵥ C *ᵥ (v - vd)) := by
  set e := v - vd with he
  have hCv : C *ᵥ v = C *ᵥ e + C *ᵥ vd := by rw [← mulVec_add, he, sub_add_cancel]
  have hstiff : x ⬝ᵥ K *ᵥ xdot = e ⬝ᵥ Jᵀ *ᵥ (K *ᵥ x) := by
    rw [hkin, stiffness_cross_symm hK]
  have h1 : e ⬝ᵥ M *ᵥ (vdot - vddot)
      = -(e ⬝ᵥ C *ᵥ e) - e ⬝ᵥ C *ᵥ vd - e ⬝ᵥ D *ᵥ e - e ⬝ᵥ Jᵀ *ᵥ (K *ᵥ x) - e ⬝ᵥ F := by
    rw [mulVec_sub, hdyn, hCv]
    simp only [dotProduct_add, dotProduct_sub, dotProduct_neg]
    ring
  unfold trackingRate
  rw [h1, hstiff]
  ring

/-- **With passivity** (`Ṁ = C + Cᵀ`): `V̇_e = −eᵀDe − eᵀ C v_d − eᵀF`.
The middle term is the residual the regulator argument does not have. -/
theorem tracking_rate_passive (hK : Kᵀ = K) (hM : Mdot = C + Cᵀ)
    (hdyn : M *ᵥ vdot = -(C *ᵥ v) - D *ᵥ (v - vd) - Jᵀ *ᵥ (K *ᵥ x) - F + M *ᵥ vddot)
    (hkin : xdot = J *ᵥ (v - vd)) :
    trackingRate M Mdot K (v - vd) (vdot - vddot) x xdot
      = -((v - vd) ⬝ᵥ D *ᵥ (v - vd)) - (v - vd) ⬝ᵥ C *ᵥ vd - (v - vd) ⬝ᵥ F := by
  rw [tracking_rate_identity hK hdyn hkin, passivity_bracket hM, add_zero]

/-- **The `velocity_ff` branch** (`−C (v − v_d)`, `the private implementation note:420-425`):
the residual disappears, `V̇_e = −eᵀDe − eᵀF`. -/
theorem tracking_rate_velocity_ff (hK : Kᵀ = K) (hM : Mdot = C + Cᵀ)
    (hdyn : M *ᵥ vdot = -(C *ᵥ (v - vd)) - D *ᵥ (v - vd) - Jᵀ *ᵥ (K *ᵥ x) - F
      + M *ᵥ vddot)
    (hkin : xdot = J *ᵥ (v - vd)) :
    trackingRate M Mdot K (v - vd) (vdot - vddot) x xdot
      = -((v - vd) ⬝ᵥ D *ᵥ (v - vd)) - (v - vd) ⬝ᵥ F := by
  set e := v - vd with he
  have hstiff : x ⬝ᵥ K *ᵥ xdot = e ⬝ᵥ Jᵀ *ᵥ (K *ᵥ x) := by
    rw [hkin, stiffness_cross_symm hK]
  have h1 : e ⬝ᵥ M *ᵥ (vdot - vddot)
      = -(e ⬝ᵥ C *ᵥ e) - e ⬝ᵥ D *ᵥ e - e ⬝ᵥ Jᵀ *ᵥ (K *ᵥ x) - e ⬝ᵥ F := by
    rw [mulVec_sub, hdyn]
    simp only [dotProduct_add, dotProduct_sub, dotProduct_neg]
    ring
  have hb := passivity_bracket hM e
  unfold trackingRate
  rw [h1, hstiff]
  linarith

/-- With `D ⪰ 0` (as a quadratic form) and perfect CoM tracking (`F = 0`), the
`velocity_ff` branch is dissipative: `V̇_e ≤ 0`. -/
theorem tracking_rate_velocity_ff_nonpos (hK : Kᵀ = K) (hM : Mdot = C + Cᵀ)
    (hD : ∀ w : n → ℝ, 0 ≤ w ⬝ᵥ D *ᵥ w) (hF : F = 0)
    (hdyn : M *ᵥ vdot = -(C *ᵥ (v - vd)) - D *ᵥ (v - vd) - Jᵀ *ᵥ (K *ᵥ x) - F
      + M *ᵥ vddot)
    (hkin : xdot = J *ᵥ (v - vd)) :
    trackingRate M Mdot K (v - vd) (vdot - vddot) x xdot ≤ 0 := by
  rw [tracking_rate_velocity_ff hK hM hdyn hkin, hF, dotProduct_zero, sub_zero]
  have := hD (v - vd)
  linarith

/-- **Regulator kinematics kept under tracking** (`ẋ = J v` instead of `J (v − v_d)`):
a second residual `+ xᵀ K J v_d` survives in addition to `−eᵀ C v_d`. -/
theorem tracking_rate_identity_absKin (hK : Kᵀ = K) (hM : Mdot = C + Cᵀ)
    (hdyn : M *ᵥ vdot = -(C *ᵥ v) - D *ᵥ (v - vd) - Jᵀ *ᵥ (K *ᵥ x) - F + M *ᵥ vddot)
    (hkin : xdot = J *ᵥ v) :
    trackingRate M Mdot K (v - vd) (vdot - vddot) x xdot
      = -((v - vd) ⬝ᵥ D *ᵥ (v - vd)) - (v - vd) ⬝ᵥ C *ᵥ vd - (v - vd) ⬝ᵥ F
        + x ⬝ᵥ K *ᵥ (J *ᵥ vd) := by
  set e := v - vd with he
  have hCv : C *ᵥ v = C *ᵥ e + C *ᵥ vd := by rw [← mulVec_add, he, sub_add_cancel]
  have hJv : J *ᵥ v = J *ᵥ e + J *ᵥ vd := by rw [← mulVec_add, he, sub_add_cancel]
  have hstiff : x ⬝ᵥ K *ᵥ xdot = e ⬝ᵥ Jᵀ *ᵥ (K *ᵥ x) + x ⬝ᵥ K *ᵥ (J *ᵥ vd) := by
    rw [hkin, hJv, mulVec_add, dotProduct_add, stiffness_cross_symm hK]
  have h1 : e ⬝ᵥ M *ᵥ (vdot - vddot)
      = -(e ⬝ᵥ C *ᵥ e) - e ⬝ᵥ C *ᵥ vd - e ⬝ᵥ D *ᵥ e - e ⬝ᵥ Jᵀ *ᵥ (K *ᵥ x) - e ⬝ᵥ F := by
    rw [mulVec_sub, hdyn, hCv]
    simp only [dotProduct_add, dotProduct_sub, dotProduct_neg]
    ring
  have hb := passivity_bracket hM e
  unfold trackingRate
  rw [h1, hstiff]
  linarith

end Identity

-- `DecidableEq` is needed by `blockLyap_coercive` in the *proof* only (same pattern
-- as `BlockLyapunov`/`StiffnessResidual`).
set_option linter.unusedDecidableInType false in
/-- The tracking storage is the sealed block Lyapunov value `blockLyap M K e x`;
for `M, K ≻ 0` it is coercive (BlockLyapunov.lean). -/
theorem tracking_storage_coercive [DecidableEq n] [DecidableEq m] [Nonempty n] [Nonempty m]
    {M : Matrix n n ℝ} {K : Matrix m m ℝ} (hM : M.PosDef) (hK : K.PosDef) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ (v vd : n → ℝ) (x : m → ℝ),
      c₁ * ((v - vd) ⬝ᵥ (v - vd) + x ⬝ᵥ x) ≤ blockLyap M K (v - vd) x := by
  obtain ⟨c₁, hc₁, h⟩ := blockLyap_coercive hM hK
  exact ⟨c₁, hc₁, fun v vd x => h (v - vd) x⟩

end Ctrllib

#print axioms Ctrllib.stiffness_cross_symm
#print axioms Ctrllib.passivity_bracket
#print axioms Ctrllib.tracking_rate_identity
#print axioms Ctrllib.tracking_rate_passive
#print axioms Ctrllib.tracking_rate_velocity_ff
#print axioms Ctrllib.tracking_rate_velocity_ff_nonpos
#print axioms Ctrllib.tracking_rate_identity_absKin
#print axioms Ctrllib.tracking_storage_coercive
