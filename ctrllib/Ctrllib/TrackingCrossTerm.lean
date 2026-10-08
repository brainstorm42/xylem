/-
PD+ strict-Lyapunov candidate for the tracking loop (the corresponding design note, follow-up to
TrackingDissipation) — the exact rate identity of the CROSS-TERM-AUGMENTED storage
along the `velocity_ff` working control equation (the source model note eq 4.12 with
`desired_twist.velocity_ff: true`, the scientific configuration adopted 2026-08-15),
with the moving-reference kinematics residual (the source model note eq 4.1c) carried.

THE STEP. TrackingDissipation seals `V̇_e = −eᵀD̆e − eᵀF` for the storage
`V_e = ½eᵀM̆e + ½x̃ᵀK̆x̃`; that rate has no strict term in x̃, so convergence of x̃
needs invariance (not available: the loop is non-autonomous through v̆_d(t)) or a
strict Lyapunov function. The PD+ literature (Paden–Panja 1988; Kelly–Santibáñez–
Loría 2005, ch. 11) adds a small cross term. Here the cross term is built on the
STIFFNESS FORCE in twist coordinates,

    g := J_x̃ᵀ K̆ x̃                        (the term −g on the RHS of eq 4.12)
    W := V_e + α gᵀ M̆ e,

and NOT on x̃ᵀM̆e: for the code's error-rate Jacobian (eq 4.1a) the form x̃ᵀJ_x̃ᵀK̆x̃
is indefinite (rotation blocks −ηE, position block +E; pin (B)), so an x̃-cross term
gives no definite term, whereas the g-cross term yields −α‖g‖² outright.

WHAT IS PROVEN (value-level algebra at one instant, K̆ symmetric, Ṁ̆ = C̆ + C̆ᵀ):
  `cross_term_rate_identity` — along
      M̆ ė = −C̆e − D̆e − g − F,        ẋ̃ = J_x̃ e + r,        ġ = J̇_x̃ᵀK̆x̃ + J_x̃ᵀK̆ẋ̃,
    the rate of W is
      Ẇ = −eᵀD̆e − eᵀF + x̃ᵀK̆r
          + α [ ġᵀM̆e + gᵀṀ̆e − gᵀC̆e − gᵀD̆e − ‖g‖² − gᵀF ].
  `cross_term_rate_no_forcing` — with F = 0 and r = 0 (perfect CoM tracking, exact
    relative-twist kinematics):  Ẇ = −eᵀD̆e + α[ġᵀM̆e + gᵀṀ̆e − gᵀC̆e − gᵀD̆e − ‖g‖²].
  `strict_term_zero_iff` — the strict term vanishes only at zero pose error when
    K̆ ≻ 0 and J_x̃ is nonsingular (via the sealed `stiffness_residual_injective`).

SYMPY-PINNED (the corresponding project check (not bundled).py):
  (A) the identity; (B) indefiniteness of x̃ᵀJᵀK̆x̃ for eq 4.1a; (C) W ≥ 0 for small α.

INTERFACE BOUNDARY (honest). Pointwise identities only. NOT here: (i) that the flow
realises the displayed rate (`IsSolutionTo`/`hreal`, as in CoupledDissipation);
(ii) the domination step — bounds ‖Ṁ̆‖, ‖C̆‖ ≤ c(‖e‖ + ‖v̆_d‖), ‖J̇‖ ≤ c', ‖r‖ ≤ 3‖x̃‖‖v̆_d‖
on a forward-invariant set, and a choice of α making Ẇ ≤ −κ(‖e‖² + ‖x̃‖²) locally;
(iii) positivity/coercivity of W for that α (pin (C) numeric). Those are the named
inputs of the local PD+ convergence theorem, still open (research deliverable
the corresponding local note, gap 1 route (a)).
-/
import Ctrllib.TrackingDissipation
import Ctrllib.StiffnessResidual

open Matrix

namespace Ctrllib

variable {n m : Type*} [Fintype n] [Fintype m]

/-- Stiffness force in twist coordinates, `g = Jᵀ (K x)` (the term `−g` in eq 4.12). -/
noncomputable def stiffForce (J : Matrix m n ℝ) (K : Matrix m m ℝ) (x : m → ℝ) : n → ℝ :=
  Jᵀ *ᵥ (K *ᵥ x)

/-- Rate of the cross term `α gᵀ M e` by the product rule with `M` time-varying:
`α (ġᵀ M e + gᵀ Ṁ e + gᵀ M ė)`. -/
noncomputable def crossRate (M Mdot : Matrix n n ℝ) (α : ℝ) (g gdot e edot : n → ℝ) : ℝ :=
  α * (gdot ⬝ᵥ M *ᵥ e + g ⬝ᵥ Mdot *ᵥ e + g ⬝ᵥ M *ᵥ edot)

/-- Rate of the augmented storage `W = V_e + α gᵀ M e` along `(ė, ẋ)`, with
`ġ = J̇ᵀ K x + Jᵀ K ẋ`. -/
noncomputable def strictRate (M Mdot : Matrix n n ℝ) (K : Matrix m m ℝ) (J Jdot : Matrix m n ℝ)
    (α : ℝ) (e edot : n → ℝ) (x xdot : m → ℝ) : ℝ :=
  trackingRate M Mdot K e edot x xdot
    + crossRate M Mdot α (stiffForce J K x) (Jdotᵀ *ᵥ (K *ᵥ x) + Jᵀ *ᵥ (K *ᵥ xdot)) e edot

section Identity

variable {M Mdot C D : Matrix n n ℝ} {K : Matrix m m ℝ} {J Jdot : Matrix m n ℝ}
variable {e edot F : n → ℝ} {x xdot r : m → ℝ} {α : ℝ}

/-- **Cross-term rate identity** for the `velocity_ff` loop with the kinematics residual. -/
theorem cross_term_rate_identity (hK : Kᵀ = K) (hM : Mdot = C + Cᵀ)
    (hdyn : M *ᵥ edot = -(C *ᵥ e) - D *ᵥ e - Jᵀ *ᵥ (K *ᵥ x) - F)
    (hkin : xdot = J *ᵥ e + r) :
    strictRate M Mdot K J Jdot α e edot x xdot
      = -(e ⬝ᵥ D *ᵥ e) - e ⬝ᵥ F + x ⬝ᵥ K *ᵥ r
        + α * ((Jdotᵀ *ᵥ (K *ᵥ x) + Jᵀ *ᵥ (K *ᵥ xdot)) ⬝ᵥ M *ᵥ e
              + stiffForce J K x ⬝ᵥ Mdot *ᵥ e
              - stiffForce J K x ⬝ᵥ C *ᵥ e
              - stiffForce J K x ⬝ᵥ D *ᵥ e
              - stiffForce J K x ⬝ᵥ stiffForce J K x
              - stiffForce J K x ⬝ᵥ F) := by
  set g := stiffForce J K x with hg
  have hstiff : x ⬝ᵥ K *ᵥ xdot = e ⬝ᵥ g + x ⬝ᵥ K *ᵥ r := by
    rw [hkin, mulVec_add, dotProduct_add, hg, stiffForce, stiffness_cross_symm hK]
  have h1 : e ⬝ᵥ M *ᵥ edot
      = -(e ⬝ᵥ C *ᵥ e) - e ⬝ᵥ D *ᵥ e - e ⬝ᵥ g - e ⬝ᵥ F := by
    rw [hdyn]
    simp only [dotProduct_sub, dotProduct_neg, hg, stiffForce]
  have h2 : g ⬝ᵥ M *ᵥ edot
      = -(g ⬝ᵥ C *ᵥ e) - g ⬝ᵥ D *ᵥ e - g ⬝ᵥ g - g ⬝ᵥ F := by
    rw [hdyn]
    simp only [dotProduct_sub, dotProduct_neg, hg, stiffForce]
  have hb := passivity_bracket hM e
  unfold strictRate trackingRate crossRate
  rw [h1, h2, hstiff]
  ring_nf
  ring_nf at hb
  linarith

/-- No CoM forcing and exact relative-twist kinematics (`F = 0`, `r = 0`). -/
theorem cross_term_rate_no_forcing (hK : Kᵀ = K) (hM : Mdot = C + Cᵀ)
    (hdyn : M *ᵥ edot = -(C *ᵥ e) - D *ᵥ e - Jᵀ *ᵥ (K *ᵥ x))
    (hkin : xdot = J *ᵥ e) :
    strictRate M Mdot K J Jdot α e edot x xdot
      = -(e ⬝ᵥ D *ᵥ e)
        + α * ((Jdotᵀ *ᵥ (K *ᵥ x) + Jᵀ *ᵥ (K *ᵥ xdot)) ⬝ᵥ M *ᵥ e
              + stiffForce J K x ⬝ᵥ Mdot *ᵥ e
              - stiffForce J K x ⬝ᵥ C *ᵥ e
              - stiffForce J K x ⬝ᵥ D *ᵥ e
              - stiffForce J K x ⬝ᵥ stiffForce J K x) := by
  have hdyn' : M *ᵥ edot = -(C *ᵥ e) - D *ᵥ e - Jᵀ *ᵥ (K *ᵥ x) - (0 : n → ℝ) := by
    rw [sub_zero]; exact hdyn
  have hkin' : xdot = J *ᵥ e + (0 : m → ℝ) := by rw [add_zero]; exact hkin
  rw [cross_term_rate_identity hK hM hdyn' hkin']
  simp only [dotProduct_zero, mulVec_zero, sub_zero]
  ring

end Identity

-- `DecidableEq` is needed by `stiffness_residual_injective` (matrix inverse) in the
-- proof only (same pattern as StiffnessResidual/TrackingDissipation).
set_option linter.unusedDecidableInType false in
/-- The strict term `‖g‖²` vanishes only at zero pose error when `K ≻ 0` and `J` is
nonsingular (mulVec-injective) — the sealed stiffness-residual finish. -/
theorem strict_term_zero_iff [DecidableEq m] {K : Matrix m m ℝ} (hK : K.PosDef)
    {J : Matrix m m ℝ} (hJ : Function.Injective J.mulVec) (x : m → ℝ) :
    stiffForce J K x ⬝ᵥ stiffForce J K x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hg : stiffForce J K x = 0 := dotProduct_self_eq_zero.mp h
    have hres : (Jᵀ * K) *ᵥ x = 0 := by
      rw [← mulVec_mulVec]; exact hg
    exact stiffness_residual_injective hK hJ hres
  · intro h
    simp [stiffForce, h]

end Ctrllib

#print axioms Ctrllib.cross_term_rate_identity
#print axioms Ctrllib.cross_term_rate_no_forcing
#print axioms Ctrllib.strict_term_zero_iff
