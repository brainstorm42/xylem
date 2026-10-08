/-
Arc 7 — the 7-DOF passivity extension (ctrllib).

Ground: the corresponding local note §5 (passivity preserved under the
augmentation) and §6/P4 (null-space damping). The augmented transformation is SQUARE:
`Γ_a = [Γ; z_aᵀ] ∈ ℝ^{13×13}`, invertible on the singularity-free region Ω, with
`z_aᵀ = k̂ᵀM / (k̂ᵀM k̂)` the inertia-weighted (dynamically consistent) covector. The
transformed dynamics are `M̂ = Γ_a⁻ᵀ M Γ_a⁻¹`, `Ĉ = Γ_a⁻ᵀ(C − M Γ_a⁻¹ Γ̇_a) Γ_a⁻¹`.

P3 — passivity survives the augmentation (§5 Lemma). For ANY smooth invertible `Γ_a(t)`:
if `Ṁ − 2C` is skew, so is `M̂̇ − 2Ĉ`. The paper's §5 proof is the ADDITIVE decomposition

    M̂̇ − 2Ĉ = Γ_a⁻ᵀ(Ṁ−2C)Γ_a⁻¹ + (S − Sᵀ),   S = Γ_a⁻ᵀ M Γ_a⁻¹ Γ̇_a Γ_a⁻¹,

using d/dt(Γ_a⁻¹) = −Γ_a⁻¹ Γ̇_a Γ_a⁻¹; congruence of a skew matrix is skew, `S − Sᵀ` is
skew by construction, and a sum of skews is skew. This module formalizes exactly that
route (writing `P := Γ_a⁻¹`, `Pdot := Γ_a⁻¹̇`, `D := Γ̇_a`):
  * `inv_deriv_eq`             — the §5 "differentiate Γ_a Γ_a⁻¹ = E and solve" step.
  * `congruence_skew`          — "a change of basis of a skew matrix is skew" (§5).
  * `augmented_passivity_decomp` — the §5 additive identity above (the Arc's new content).
  * `augmented_passivity_skew` — `M̂̇ − 2Ĉ` skew, via the additive route (§5 headline).
  * `augmented_passivity_identity` — the eq-23 quadratic form vanishes for the augmentation.

This EXTENDS the sealed `PassivityTransport.lean`: `transported_skew` /
`transported_passivity_identity` already prove the same skew/identity via the FACTORIZATION
route (`M̂̇ = Ĉ + Ĉᵀ`) and are polymorphic in the index type, so they ALREADY cover the
13×13 augmentation with no size hypothesis. What is new here is the paper's own §5 additive
decomposition made explicit, and the inverse-derivative step it rides on.

Honest boundary (from the derivation doc §6/P3): `Ĉ` is NOT block-diagonal — the Coriolis
cross-terms coupling the self-motion `v_n` to the task block `(ω_b, ν_e⁺)` genuinely EXIST
(pointwise-in-q inertia decoupling does not kill the rate terms). Those cross-terms do not
break passivity (this is exactly the content sealed here); they DRIVE the null-space in P4.

P4 — closed-loop null-space damping (§6 P4). Add `u_n = −k_n x̃_n − d_n v_n`; the null-space
state `(x̃_n, v_n)` becomes a DRIVEN subsystem, forced by the (passivity-workless, non-zero)
task-block cross-Coriolis. Reusing the sealed cascade engine `cascade_attractive` (R4) with the task
block as the vanishing driving output, the null-space converges. `nullspace_damping_attractive` is
the engine instantiation; `nullspace_damping_driven` discharges the driver from the sealed
`propIV1_cascade_attractive` (the com→coupled task cascade), giving the joint
(null-space, task) → 0; `nullspace_damping_attractive_concrete` restates the engine
instantiation with `hsand`/`hα₁` discharged from the explicit reshaped `V_n` (below).

The null-space Lyapunov is the RESHAPED `V_n` (Panteley Prop 1 shape: the raw mechanical
energy ½m̂_n v_n² + ½k_n x̃_n² lacks the −x̃_n² decrease, so it does NOT satisfy the
proportional inequality; the reshaped V_n does). `nullspace_damping_attractive` carries its
sandwich `hsand` and interconnection inequality `hdi` as the two named modelling inputs —
the same status the sealed cascade gives them (the corresponding local note).

`hsand` IS NOW DISCHARGED for the concrete oscillator. `nullspaceLyap` writes `V_n` down
explicitly as ½ of the quadratic form of `K_n = [[k_n, ε], [ε, m̂_n]]`; `nullspaceLyap_coercive`
proves the class-𝒦∞ lower sandwich by a sum-of-squares identity under `ε² < k_n m̂_n`, and
`nullspace_damping_attractive_concrete` republishes the P4 conclusion with `hsand` and `hα₁`
removed from the interface. The self-motion subsystem is a 1-DOF damped oscillator on ℝ × ℝ,
strictly easier than the coupled block `CoupledSandwich.blockLyap_hsand` already discharged,
so the converse-Lyapunov wall the ledger cites does not bind here.

`hdi` STAYS OPEN by design: its constant `c` is trajectory-dependent (the null-space forcing
is the cross-Coriolis term, bilinear in `(v_n, v_task)`), so closing it needs an a-priori
bound on `‖v_n‖` that nothing here supplies. The redundancy pair moves from two named
modelling inputs to one, not to zero.

The reshaping itself — the presence of a cross term and the coefficient ε — is a MODELLING
CHOICE, not a derivation, and needs user sign-off: a different reshaping changes the decay
constant `a` that downstream numbers inherit. Out of scope (flagged design decision):
allocating the 1-D null-space DOF among the three competing secondary objectives.

SymPy/NumPy-pinned BEFORE formalizing (the corresponding symbolic check (not bundled).py):
  (A) inverse-derivative identity (algebraic solve + honest d/dt);
  (B) the §5 additive decomposition + S−Sᵀ skew + congruence-of-skew;
  (C) a concrete 13-dim model: Γk̂=0, z_aᵀc_i=0 (M-orthogonality), block-diagonal M̂,
      m̂_n=k̂ᵀMk̂, and time-varying §5 skew;
  (D) the §6/P4 reshaped-Lyapunov differential inequality V_n' ≤ −a V_n + c‖x₂‖.

Prior art: Giordano's thesis (whole-body coordinated control) §5.2 + §5.8c — the redundant
formulation and the null-space damping law; framing paper giordano2019coordinated (RA-L 2019)
assumes a NONREDUNDANT arm (the redundant extension is the new content). Null-space
reconstruction for redundant manipulators: Nakamura (redundant-manipulator null-space) — on
disk, NOT yet corpus-filed; cited as plain text and flagged, same discipline as the pending
sources.

Human derivation: wiki dir the corresponding derivation record (not bundled)
(no the corresponding local note page filed yet)
-/
import Ctrllib.PassivityTransport
import Ctrllib.Cascade
import Ctrllib.CoupledSandwich
import Mathlib.LinearAlgebra.Matrix.Notation

open Matrix
open Set Filter Topology
open scoped InnerProductSpace

namespace Ctrllib

set_option linter.unusedDecidableInType false

/-! ## P3 — passivity survives the augmentation (§5 Lemma) -/

section Passivity

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **§5 inverse-derivative** (differentiate `Γ_a Γ_a⁻¹ = E` and solve). If `Ginv` is a left
inverse of `G` (`Ginv * G = 1`) and the product rule holds for the identity
(`Gdot * Ginv + G * Ginvdot = 0`), then the inverse's rate is
`Ginvdot = −Ginv * Gdot * Ginv`. Purely algebraic; no size, symmetry or positivity used. -/
theorem inv_deriv_eq {R : Type*} [CommRing R] {Ginv G Gdot Ginvdot : Matrix n n R}
    (hinv : Ginv * G = 1) (hprod : Gdot * Ginv + G * Ginvdot = 0) :
    Ginvdot = -(Ginv * Gdot * Ginv) := by
  have h1 : G * Ginvdot = -(Gdot * Ginv) := eq_neg_of_add_eq_zero_right hprod
  calc Ginvdot = Ginv * G * Ginvdot := by rw [hinv, one_mul]
    _ = Ginv * (G * Ginvdot) := by rw [mul_assoc]
    _ = Ginv * -(Gdot * Ginv) := by rw [h1]
    _ = -(Ginv * Gdot * Ginv) := by rw [mul_neg, mul_assoc]

omit [DecidableEq n] in
/-- **A change of basis of a skew matrix is skew** (§5). If `Aᵀ = -A` then the congruence
`Pᵀ * A * P` is again skew, for any `P`. Over any commutative ring. -/
theorem congruence_skew {R : Type*} [CommRing R] {A P : Matrix n n R}
    (hA : Aᵀ = -A) : (Pᵀ * A * P)ᵀ = -(Pᵀ * A * P) := by
  rw [transpose_mul, transpose_mul, transpose_transpose, hA, neg_mul, mul_neg, mul_assoc]

/-- **The §5 additive decomposition.** With `M` symmetric and the Christoffel factorization
`Ṁ = C + Cᵀ` (written inline as `C + Cᵀ`), and the inverse-derivative
`Ginvdot = −(Ginv * Gdot * Ginv)`, the transported passivity residual splits as

    M̂̇ − 2Ĉ = Ginvᵀ(Ṁ − 2C)Ginv + (S − Sᵀ),   S = Ginvᵀ M Ginv Gdot Ginv,

the congruence of the original skew term plus a manifestly antisymmetric correction. Here
`M̂̇ = Ginvdotᵀ M Ginv + Ginvᵀ Ṁ Ginv + Ginvᵀ M Ginvdot` is the product-rule derivative and
`Ĉ = Ginvᵀ(C Ginv + M Ginvdot)` is the transported Coriolis (the source model note eq 3.2, `P = Ginv`).
This is the exact identity of the corresponding local note §5; SymPy pin (B). -/
theorem augmented_passivity_decomp {R : Type*} [CommRing R]
    {M C Ginv Gdot Ginvdot : Matrix n n R}
    (hMsymm : Mᵀ = M) (hid : Ginvdot = -(Ginv * Gdot * Ginv)) :
    (Ginvdotᵀ * M * Ginv + Ginvᵀ * (C + Cᵀ) * Ginv + Ginvᵀ * M * Ginvdot)
        - 2 • (Ginvᵀ * (C * Ginv + M * Ginvdot))
      = Ginvᵀ * ((C + Cᵀ) - 2 • C) * Ginv
        + ((Ginvᵀ * M * Ginv * Gdot * Ginv) - (Ginvᵀ * M * Ginv * Gdot * Ginv)ᵀ) := by
  subst hid
  simp only [transpose_neg, transpose_mul, transpose_transpose, hMsymm, two_smul]
  noncomm_ring

/-- **P3 headline — passivity survives, via the §5 additive route.** `M̂̇ − 2Ĉ` is
skew-symmetric: the congruence term is skew (`congruence_skew` on the sealed
`mdot_sub_two_coriolis_skew`), the `S − Sᵀ` correction is antisymmetric, and a sum of
skews is skew. Independent of `transported_skew`'s factorization route. -/
theorem augmented_passivity_skew {R : Type*} [CommRing R]
    {M C Ginv Gdot Ginvdot : Matrix n n R}
    (hMsymm : Mᵀ = M) (hid : Ginvdot = -(Ginv * Gdot * Ginv)) :
    ((Ginvdotᵀ * M * Ginv + Ginvᵀ * (C + Cᵀ) * Ginv + Ginvᵀ * M * Ginvdot)
        - 2 • (Ginvᵀ * (C * Ginv + M * Ginvdot)))ᵀ
      = -((Ginvdotᵀ * M * Ginv + Ginvᵀ * (C + Cᵀ) * Ginv + Ginvᵀ * M * Ginvdot)
        - 2 • (Ginvᵀ * (C * Ginv + M * Ginvdot))) := by
  rw [augmented_passivity_decomp hMsymm hid, transpose_add, transpose_sub,
    transpose_transpose, congruence_skew (mdot_sub_two_coriolis_skew (rfl : C + Cᵀ = C + Cᵀ))]
  abel

/-- **Giordano eq 23 for the augmented dynamics.** The velocity quadratic form of the
transported `M̂̇ − 2Ĉ` vanishes for every `v` — the passivity/energy-balance identity, now
established for the SQUARE 13×13 augmentation via the §5 additive route. -/
theorem augmented_passivity_identity {M C Ginv Gdot Ginvdot : Matrix n n ℝ}
    (hMsymm : Mᵀ = M) (hid : Ginvdot = -(Ginv * Gdot * Ginv)) (v : n → ℝ) :
    v ⬝ᵥ ((Ginvdotᵀ * M * Ginv + Ginvᵀ * (C + Cᵀ) * Ginv + Ginvᵀ * M * Ginvdot)
        - 2 • (Ginvᵀ * (C * Ginv + M * Ginvdot))) *ᵥ v = 0 :=
  dotProduct_mulVec_self_of_skew (augmented_passivity_skew hMsymm hid) v

end Passivity

/-! ## P4 — closed-loop null-space damping (§6 P4) -/

section NullSpaceDamping

/-- **Null-space damping — the cascade engine instantiation.** The damped self-motion state
`xn = (x̃_n, v_n) : ℝ × ℝ` (from `u_n = −k_n x̃_n − d_n v_n`) is the DRIVEN subsystem of the
sealed `cascade_attractive`: its reshaped Lyapunov `Vn` lower-bounded by a class-𝒦∞ `α₁`
(`hsand`), and driven by the vanishing task output `x₂` through the interconnection inequality
`vn' ≤ −a Vn + c‖x₂‖` (`hdi`). When the driver converges (`hx2`, the sealed task attractivity),
the joint `(xn, x₂)` reaches the origin — attractivity along the given trajectory, not ε–δ
stability (see `KhalilStability.AsympStable`; formerly named `nullspace_damping_gas`).
`hsand`/`hdi` are the named Panteley-Prop-1 modelling inputs (SymPy pin (D) shows them
realizable for the concrete damped oscillator). Honest note on `hdi`: its constant `c` is
trajectory-dependent — the null-space forcing is the cross-Coriolis term, bilinear in
`(v_n, v_task)`, so `c` scales with an a-priori bound on `‖v_n‖` along the trajectory
(the Panteley–Loría growth condition + upstream boundedness, bundled here as one input;
the corresponding local note row `hdi`). -/
theorem nullspace_damping_attractive
    {E₂ : Type*} [NormedAddCommGroup E₂]
    {xn : ℝ → ℝ × ℝ} {x₂ : ℝ → E₂} {Vn : ℝ × ℝ → ℝ} {vn' α₁ : ℝ → ℝ} {a c : ℝ}
    (ha : 0 < a) (hα₁ : IsClassKInfinity α₁)
    (hsand : ∀ t ∈ Ici (0 : ℝ), α₁ ‖xn t‖ ≤ Vn (xn t))
    (hvc : ContinuousOn (fun t => Vn (xn t)) (Ici 0))
    (hv : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt (fun t => Vn (xn t)) (vn' t) (Ici t) t)
    (hdi : ∀ t ∈ Ici (0 : ℝ), vn' t ≤ -a * Vn (xn t) + c * ‖x₂ t‖)
    (hx2 : Tendsto x₂ atTop (𝓝 0)) :
    Tendsto (fun t => (xn t, x₂ t)) atTop (𝓝 0) :=
  cascade_attractive ha hα₁ hsand hvc hv hdi hx2

@[deprecated nullspace_damping_attractive (since := "2026-08-15")]
alias nullspace_damping_gas := nullspace_damping_attractive

/-- **Null-space damping driven by the sealed task cascade (§6 P4, assembled).** The driving
output is the full task block — the com→coupled cascade `propIV1_cascade_attractive` gives
`(xt, ϕc·z₀) → 0` — fed as the vanishing driver of the null-space cascade. Conclusion: the
joint (null-space, task) state `(xn, (xt, ϕc·z₀)) → 0`. Two sealed cascade stones composed;
no fresh convergence proof. The `d`-suffixed hypotheses are the sealed Prop IV.1 interface
(discharged for concrete SPD blocks by ComLaSalleMatrix), the `n`-suffixed ones the named
null-space reshaping inputs (`hdin`'s constant `cn` is trajectory-dependent, as for `hdi`
in `nullspace_damping_attractive`). -/
theorem nullspace_damping_driven
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (ϕc : Flow ℝ (ComState H)) (Mc Dc Kc Mcinv : H →L[ℝ] H)
    (hϕc : IsSolutionTo ϕc (comField Dc Kc Mcinv))
    (hMsa : ∀ a b : H, ⟪Mc a, b⟫_ℝ = ⟪a, Mc b⟫_ℝ)
    (hKsa : ∀ a b : H, ⟪Kc a, b⟫_ℝ = ⟪a, Kc b⟫_ℝ)
    (hMinv : ∀ w : H, Mc (Mcinv w) = w)
    (hDnn : ∀ v : H, 0 ≤ ⟪v, Dc v⟫_ℝ)
    (hDdef : ∀ v : H, ⟪v, Dc v⟫_ℝ = 0 → v = 0)
    (hKdef : ∀ x : H, Kc x = 0 → x = 0)
    (z₀ : ComState H) (hcptc : ForwardPrecompact ϕc z₀)
    {xt : ℝ → CoupledState H} {Vd : CoupledState H → ℝ} {vt' α₁d : ℝ → ℝ} {ad cd : ℝ}
    (had : 0 < ad) (hα₁d : IsClassKInfinity α₁d)
    (hsandd : ∀ t ∈ Ici (0 : ℝ), α₁d ‖xt t‖ ≤ Vd (xt t))
    (hvcd : ContinuousOn (fun t => Vd (xt t)) (Ici 0))
    (hvd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt (fun t => Vd (xt t)) (vt' t) (Ici t) t)
    (hdid : ∀ t ∈ Ici (0 : ℝ), vt' t ≤ -ad * Vd (xt t) + cd * ‖ϕc t z₀‖)
    {xn : ℝ → ℝ × ℝ} {Vn : ℝ × ℝ → ℝ} {vn' α₁n : ℝ → ℝ} {an cn : ℝ}
    (han : 0 < an) (hα₁n : IsClassKInfinity α₁n)
    (hsandn : ∀ t ∈ Ici (0 : ℝ), α₁n ‖xn t‖ ≤ Vn (xn t))
    (hvcn : ContinuousOn (fun t => Vn (xn t)) (Ici 0))
    (hvn : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt (fun t => Vn (xn t)) (vn' t) (Ici t) t)
    (hdin : ∀ t ∈ Ici (0 : ℝ), vn' t ≤ -an * Vn (xn t) + cn * ‖(xt t, ϕc t z₀)‖) :
    Tendsto (fun t => (xn t, (xt t, ϕc t z₀))) atTop (𝓝 0) := by
  have htask : Tendsto (fun t => (xt t, ϕc t z₀)) atTop (𝓝 0) :=
    propIV1_cascade_attractive ϕc Mc Dc Kc Mcinv hϕc hMsa hKsa hMinv hDnn hDdef hKdef z₀ hcptc
      had hα₁d hsandd hvcd hvd hdid
  exact nullspace_damping_attractive han hα₁n hsandn hvcn hvn hdin htask

/-! ### The CONCRETE reshaped null-space Lyapunov — `hsand` discharged

`nullspace_damping_attractive` above carries `hsand` and `hα₁` as named modelling inputs, the
same status the sealed cascade gives them. For the CONCRETE self-motion subsystem they are not
modelling inputs at all: the null-space state `(x̃_n, v_n)` lives on `ℝ × ℝ`, so the reshaped
Lyapunov can be WRITTEN DOWN rather than obtained from a converse-Lyapunov theorem. This
mirrors what `CoupledSandwich.blockLyap_hsand` does for the coupled block, one dimension down.

MODELLING CHOICE, NOT A DERIVATION (flagged for user sign-off). The reshaping — the presence
of a cross term and its coefficient `ε` — is a design decision. A different reshaping changes
the decay constant `a` that downstream numbers inherit. What is machine-checked here is only
that THIS reshaping is coercive under `ε² < k_n m̂_n`, hence admissible.

Correspondence to SymPy/NumPy pin (D) (`the corresponding private check`, §6/P4 leg): the pin writes
`V = ½ m̂_n v² + ½ k_n x̃² + ε_pin·m̂_n·x̃v` with coercivity `ε_pin² < k_n/m̂_n`. Setting
`ε = ε_pin·m̂_n` makes the two identical, and the pin's condition becomes `ε² < k_n m̂_n`.

WHAT THIS DOES NOT DO. `hdi` stays open. Its constant `c` is trajectory-dependent — the
null-space forcing is the cross-Coriolis term, bilinear in `(v_n, v_task)` — so closing it
needs an a-priori bound on `‖v_n‖` that nothing here supplies. The redundancy pair therefore
moves from two named modelling inputs to one, not to zero. -/

/-- **The reshaped null-space Lyapunov form** `K_n = [[k_n, ε], [ε, m̂_n]]`. The self-motion
stiffness and inertia on the diagonal, the reshaping cross-term off it. `V_n` below is
`½ yᵀ K_n y`. -/
def nullspaceLyapMatrix (kn mn eps : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![kn, eps; eps, mn]

/-- **The reshaped null-space Lyapunov function** on the self-motion state `y = (x̃_n, v_n)`:

    `V_n(x̃_n, v_n) = ½ k_n x̃_n² + ½ m̂_n v_n² + ε x̃_n v_n`.

The raw mechanical energy (`ε = 0`) lacks the `−x̃_n²` decrease and so does NOT satisfy the
proportional inequality the cascade needs; the cross term is what supplies it (Panteley
Prop 1 shape, SymPy pin (D)). -/
noncomputable def nullspaceLyap (kn mn eps : ℝ) (y : ℝ × ℝ) : ℝ :=
  2⁻¹ * kn * y.1 ^ 2 + 2⁻¹ * mn * y.2 ^ 2 + eps * y.1 * y.2

/-- `V_n` IS the quadratic form of `K_n`, halved: `V_n(y) = ½ yᵀ K_n y`. -/
theorem nullspaceLyap_eq_quadraticForm (kn mn eps : ℝ) (y : ℝ × ℝ) :
    nullspaceLyap kn mn eps y
      = 2⁻¹ * (![y.1, y.2] ⬝ᵥ nullspaceLyapMatrix kn mn eps *ᵥ ![y.1, y.2]) := by
  simp [nullspaceLyap, nullspaceLyapMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- **`K_n ≻ 0` under the smallness condition on the reshaping.** `0 < k_n` and
`ε² < k_n m̂_n` make the reshaped form positive definite — the 2×2 leading-minor test, done
by hand because the index type is `Fin 2`. This is the statement that `V_n` is a legitimate
Lyapunov candidate at all. -/
theorem nullspaceLyapMatrix_posDef {kn mn eps : ℝ} (hk : 0 < kn) (heps : eps ^ 2 < kn * mn) :
    (nullspaceLyapMatrix kn mn eps).PosDef := by
  have hm : 0 < mn := by nlinarith [sq_nonneg eps]
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [nullspaceLyapMatrix]
  · intro x hx
    have hquad : star x ⬝ᵥ nullspaceLyapMatrix kn mn eps *ᵥ x
        = kn * x 0 ^ 2 + 2 * eps * (x 0 * x 1) + mn * x 1 ^ 2 := by
      simp [nullspaceLyapMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring
    rw [hquad]
    have hne : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      rcases eq_or_ne (x 0) 0 with h0 | h0
      · rcases eq_or_ne (x 1) 0 with h1 | h1
        · exact absurd (by ext i; fin_cases i <;> simp [h0, h1]) hx
        · exact Or.inr h1
      · exact Or.inl h0
    rcases hne with h | h
    · rcases eq_or_ne (x 1) 0 with h1 | h1
      · rw [h1]; nlinarith [pow_pos (abs_pos.mpr h) 2, sq_abs (x 0)]
      · nlinarith [sq_nonneg (kn * x 0 + eps * x 1), pow_pos (abs_pos.mpr h1) 2, sq_abs (x 1)]
    · nlinarith [sq_nonneg (kn * x 0 + eps * x 1), pow_pos (abs_pos.mpr h) 2, sq_abs (x 1)]

/-- **`V_n` is coercive, with an EXPLICIT constant.** For every self-motion state,

    `c₁ ‖y‖² ≤ V_n(y)`,   `c₁ = (k_n m̂_n − ε²) / (2(k_n + m̂_n)) > 0`.

The proof is a sum of squares, not an eigenvalue computation:

    `2(k_n+m̂_n)·(V_n(y) − c₁(x̃² + v²)) = (k_n x̃ + ε v)² + (m̂_n v + ε x̃)²`,

so no spectral machinery is needed. `c₁` is a lower bound for `½λ_min(K_n)` — the pin's
constant — and is strictly smaller in general (pin (D) numbers: `c₁ = 0.586` against
`½λ_min = 0.825`), so it is conservative in the safe direction. The product norm on `ℝ × ℝ`
is the sup norm (`Prod.norm_def`), and `‖y‖² ≤ x̃² + v²` for it, with room to spare. -/
theorem nullspaceLyap_coercive {kn mn eps : ℝ} (hk : 0 < kn) (hm : 0 < mn)
    (heps : eps ^ 2 < kn * mn) (y : ℝ × ℝ) :
    (kn * mn - eps ^ 2) / (2 * (kn + mn)) * ‖y‖ ^ 2 ≤ nullspaceLyap kn mn eps y := by
  have hden : (0 : ℝ) < 2 * (kn + mn) := by linarith
  have hc : 0 < (kn * mn - eps ^ 2) / (2 * (kn + mn)) := div_pos (by linarith) hden
  have hnorm : ‖y‖ ^ 2 ≤ y.1 ^ 2 + y.2 ^ 2 := by
    have h1 : ‖y.1‖ ^ 2 = y.1 ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
    have h2 : ‖y.2‖ ^ 2 = y.2 ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
    rw [Prod.norm_def]
    rcases le_total ‖y.1‖ ‖y.2‖ with h | h
    · rw [max_eq_right h, h2]; nlinarith [sq_nonneg y.1]
    · rw [max_eq_left h, h1]; nlinarith [sq_nonneg y.2]
  have hstep : (kn * mn - eps ^ 2) / (2 * (kn + mn)) * (y.1 ^ 2 + y.2 ^ 2)
      ≤ nullspaceLyap kn mn eps y := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hden, nullspaceLyap]
    nlinarith [sq_nonneg (kn * y.1 + eps * y.2), sq_nonneg (mn * y.2 + eps * y.1)]
  exact le_trans (mul_le_mul_of_nonneg_left hnorm hc.le) hstep

/-- **The `hsand` interface, DISCHARGED for the concrete null-space oscillator.** Exactly the
hypothesis shape `nullspace_damping_attractive` consumes, produced as a theorem: the concrete
class-𝒦∞ witness is `α₁(s) = c₁ s²` built from the sealed `isClassKInfinity_sq` and
`IsClassKInfinity.const_mul`, with `c₁` the explicit constant of `nullspaceLyap_coercive`.
Holds along ANY trajectory `xn` — no regularity, no boundedness. -/
theorem nullspaceLyap_hsand {kn mn eps : ℝ} (hk : 0 < kn) (hm : 0 < mn)
    (heps : eps ^ 2 < kn * mn) (xn : ℝ → ℝ × ℝ) :
    ∃ α₁ : ℝ → ℝ, IsClassKInfinity α₁ ∧
      ∀ t ∈ Ici (0 : ℝ), α₁ ‖xn t‖ ≤ nullspaceLyap kn mn eps (xn t) := by
  refine ⟨fun s => (kn * mn - eps ^ 2) / (2 * (kn + mn)) * s ^ 2,
    isClassKInfinity_sq.const_mul (div_pos (by linarith) (by linarith)), ?_⟩
  exact fun t _ => nullspaceLyap_coercive hk hm heps (xn t)

/-- **Null-space damping with `hsand` discharged (§6 P4, concrete).** Same conclusion as
`nullspace_damping_attractive` — the joint (null-space, task) state reaches the origin — but
`hsand` and `hα₁` are GONE from the interface, replaced by the scalar conditions
`0 < k_n`, `0 < m̂_n` and `ε² < k_n m̂_n` on the concrete reshaped Lyapunov `V_n`. One fewer
interface row than the abstract statement carries.

`hm : 0 < m̂_n` is implied by `hk` and `heps`; it is kept explicit because `m̂_n > 0` is the
physically named input, discharged downstream by
`SevenDofDecoupling.selfmotion_inertia_pos` (`m̂_n = k̂ᵀM k̂ > 0` for `M ≻ 0`). It is stated as a
hypothesis rather than imported because `SevenDofDecoupling` imports THIS module.

Remaining interface rows: `hvc`, `hv` (the trajectory is differentiable along `V_n`) and
`hdi` (the interconnection inequality). `hdi` is the one that stays a named modelling input —
its constant `c` is trajectory-dependent, so this theorem does not close it. The damping gain
`d_n > 0` does not appear: it enters only through `hdi`, so listing it here would be an unused
binder. -/
theorem nullspace_damping_attractive_concrete
    {E₂ : Type*} [NormedAddCommGroup E₂]
    {xn : ℝ → ℝ × ℝ} {x₂ : ℝ → E₂} {vn' : ℝ → ℝ} {a c kn mn eps : ℝ}
    (ha : 0 < a) (hk : 0 < kn) (hm : 0 < mn) (heps : eps ^ 2 < kn * mn)
    (hvc : ContinuousOn (fun t => nullspaceLyap kn mn eps (xn t)) (Ici 0))
    (hv : ∀ t ∈ Ici (0 : ℝ),
      HasDerivWithinAt (fun t => nullspaceLyap kn mn eps (xn t)) (vn' t) (Ici t) t)
    (hdi : ∀ t ∈ Ici (0 : ℝ),
      vn' t ≤ -a * nullspaceLyap kn mn eps (xn t) + c * ‖x₂ t‖)
    (hx2 : Tendsto x₂ atTop (𝓝 0)) :
    Tendsto (fun t => (xn t, x₂ t)) atTop (𝓝 0) := by
  obtain ⟨α₁, hα₁, hsand⟩ := nullspaceLyap_hsand hk hm heps xn
  exact nullspace_damping_attractive ha hα₁ hsand hvc hv hdi hx2

end NullSpaceDamping

end Ctrllib

#print axioms Ctrllib.inv_deriv_eq
#print axioms Ctrllib.congruence_skew
#print axioms Ctrllib.augmented_passivity_decomp
#print axioms Ctrllib.augmented_passivity_skew
#print axioms Ctrllib.augmented_passivity_identity
#print axioms Ctrllib.nullspace_damping_attractive
#print axioms Ctrllib.nullspace_damping_driven
#print axioms Ctrllib.nullspaceLyap_eq_quadraticForm
#print axioms Ctrllib.nullspaceLyapMatrix_posDef
#print axioms Ctrllib.nullspaceLyap_coercive
#print axioms Ctrllib.nullspaceLyap_hsand
#print axioms Ctrllib.nullspace_damping_attractive_concrete
