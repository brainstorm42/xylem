/-
TARGET 6 — the coupled block's Lyapunov derivative (the genuine core of Prop IV.1,
difficulty L). Along the sealed closed-loop field `g₂` the storage function

    V(y) = ½⟪v̆, M̆ v̆⟫ + ½⟪x̃, K̆ x̃⟫

has TOTAL time derivative `V̇ = -⟪v̆, D̆ v̆⟫ ≤ 0` (Giordano eqs 37-38; the source model note
§4.6 eqs 4.15-4.16). This is the `hdec` input the sealed `propIV1_tendsto` consumes.

The sealed `CoupledField.coupledEnergy_fderiv_field` gives only the STATE-SPACE
partial (M̆ held constant), already with the stiffness cross-terms cancelled:

    DV(y)[g₂(y)] = -⟪v̆, C̆ v̆⟫ - ⟪v̆, D̆ v̆⟫ .

That partial is NOT sign-definite — the Coriolis term survives. The TOTAL derivative
along a real trajectory adds the term the constant-operator storage form drops,
`½⟪v̆, Ṁ̆ v̆⟫`, because `M̆ = M̆(q(t))` is configuration-dependent (the source model note eq 38).
The sealed passivity identity — `Ctrllib.transported_passivity_identity`, which
*produces* `Ṁ̆ = C̆ + C̆ᵀ` by congruence transport of the Christoffel choice, hence
`v̆ᵀ(Ṁ̆ - 2C̆)v̆ = 0` — collapses that correction to `⟪v̆, C̆ v̆⟫`, EXACTLY cancelling
the surviving Coriolis term:

    V̇ = DV[g₂] + ½⟪v̆, Ṁ̆ v̆⟫ = (-⟪v̆,C̆v̆⟫ - ⟪v̆,D̆v̆⟫) + ⟪v̆,C̆v̆⟫ = -⟪v̆, D̆ v̆⟫ .

WHAT IS PROVEN (real content):
  `coupled_total_dissipation` — the identity `V̇ = -⟪v̆, D̆ v̆⟫`, consuming the sealed
    field lemma + the passivity collapse. THE genuine core: the cross-cancellation
    plus the Coriolis kill, the whole point of Prop IV.1 step 2.
  `coupled_decrease` — `V̇ ≤ 0` (negative semidefinite: D̆ ⪰ 0).
  `coupled_hdec` — the exact `∀ y, DV[f] y ≤ 0` shape `propIV1_tendsto` names as
    `hdec`, given the field realizes the total rate (named `hreal`, below).
  `coupled_block_tendsto` — the capstone: feeds `coupled_hdec` straight into the
    sealed `propIV1_tendsto`, so the coupled-block trajectory converges to Γ₁.
    The `hdec` hole of Prop IV.1's assembly is now filled by construction.

SymPy-pinned (the corresponding symbolic check (not bundled).py) BEFORE the Lean:
  (1) `partial + ½ v̆ᵀ(C̆+C̆ᵀ)v̆ = -v̆ᵀD̆v̆` — symbolic n=2,3 + numeric n=3,6,9 (<4e-13);
  (2) sign `-v̆ᵀD̆v̆ ≤ 0` for D̆ PSD (numeric);
  (3) the operator form `v̆ᵀ(C̆+C̆ᵀ)v̆ = 2 v̆ᵀC̆v̆` — the faithful transcription of the
      sealed matrix identity `v ⬝ᵥ (Ṁ̆ - 2•C̆) *ᵥ v = 0`.

INTERFACE BOUNDARY (honest, the ComLaSalle `hMinv`/`hJadj` precedent):
  * `hpass : ∀ v, ⟪v, Ṁ̆ v⟫ = 2⟪v, C̆ v⟫` — the passivity property in OPERATOR form
    on the abstract inner-product space `H`. It is the abstract transcription of the
    sealed MATRIX theorem `Ctrllib.transported_passivity_identity`
    (`v ⬝ᵥ (Ṁ̆ - 2•C̆) *ᵥ v = 0`); for the concrete `EuclideanSpace` block the two are
    one and the same via `Matrix.toEuclideanCLM`. Bridging matrix↔operator is the
    same `toEuclideanCLM`/`WithLp` plumbing `CoupledField` already defers for
    `hMinv`/`hJadj`/`hMsa`/`hKsa`; this lane inherits `CoupledField`'s abstract-`H`
    formulation and defers it identically — never a weaker substitution.
  * `hMsa/hKsa/hMinv/hJadj/hDnn` — the CoupledField/ComLaSalle operator hypotheses
    (symmetry, inverse, adjoint, D̆ ⪰ 0); theorems for concrete SPD blocks.
  * `hreal : ∀ y, fderiv ℝ V y (f y) = coupledLyapRate … y` — the ONE modelling
    interface: the TRUE closed-loop field carries the state-dependent operators
    `M̆(q),C̆(q),…`, and its Lyapunov Fréchet-derivative equals the assembled total
    rate `DV[g₂] + ½⟪v̆,Ṁ̆v̆⟫`. The constant-operator `g₂` linearises those operators
    pointwise; identifying the state-dependent-`M̆` calculus with the assembled rate
    is the deferred piece (the `IsSolutionTo` / product-rule precedent). Named, never
    a silent `sorry`; the ALGEBRA it brackets — the cross-cancellation + Coriolis
    kill — is proved outright in `coupled_total_dissipation`.

Human derivation: the corresponding derivation record (not bundled)
-/
import Ctrllib.CoupledField
import Ctrllib.Reduction

open Set Filter Topology
open scoped InnerProductSpace

namespace Ctrllib

section CoupledDissipation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  (M C D K J Minv Jadj Mdot : H →L[ℝ] H)

/-- The TOTAL Lyapunov rate along the coupled block: the sealed state-space partial
`DV(y)[g₂(y)]` PLUS the time-varying-inertia correction `½⟪v̆, Ṁ̆ v̆⟫` that the
constant-operator storage form drops (the source model note eq 38). `Mdot` (= Ṁ̆) is the
supplied inertia-rate operator carrying the passivity identity as its defining
property (`hpass`). -/
noncomputable def coupledLyapRate (y : CoupledState H) : ℝ :=
  fderiv ℝ (coupledEnergy M K) y (g2Field C D K J Minv Jadj y)
    + (1 / 2 : ℝ) * ⟪y.2, Mdot y.2⟫_ℝ

variable {M C D K J Minv Jadj Mdot}

/-- **The total dissipation identity (the genuine core).** `V̇ = -⟪v̆, D̆ v̆⟫`.
Consumes the sealed field lemma `coupledEnergy_fderiv_field` (which already cancels
the stiffness cross-terms) and the passivity collapse `½⟪v̆,Ṁ̆v̆⟫ = ⟪v̆,C̆v̆⟫`, which
kills the surviving Coriolis term. SymPy-pinned (the corresponding private check (1)). -/
theorem coupled_total_dissipation
    (hMsa : ∀ a b : H, ⟪M a, b⟫_ℝ = ⟪a, M b⟫_ℝ)
    (hKsa : ∀ a b : H, ⟪K a, b⟫_ℝ = ⟪a, K b⟫_ℝ)
    (hMinv : ∀ w : H, M (Minv w) = w)
    (hJadj : ∀ a b : H, ⟪J a, b⟫_ℝ = ⟪a, Jadj b⟫_ℝ)
    (hpass : ∀ v : H, ⟪v, Mdot v⟫_ℝ = 2 * ⟪v, C v⟫_ℝ)
    (y : CoupledState H) :
    coupledLyapRate M C D K J Minv Jadj Mdot y = -⟪y.2, D y.2⟫_ℝ := by
  rw [coupledLyapRate, coupledEnergy_fderiv_field hMsa hKsa hMinv hJadj y, hpass y.2]
  ring

/-- **Weak decrease.** `V̇ ≤ 0` — negative semidefinite (`D̆ ⪰ 0`). This is the
`hdec` content the sealed `propIV1_tendsto` requires. -/
theorem coupled_decrease
    (hMsa : ∀ a b : H, ⟪M a, b⟫_ℝ = ⟪a, M b⟫_ℝ)
    (hKsa : ∀ a b : H, ⟪K a, b⟫_ℝ = ⟪a, K b⟫_ℝ)
    (hMinv : ∀ w : H, M (Minv w) = w)
    (hJadj : ∀ a b : H, ⟪J a, b⟫_ℝ = ⟪a, Jadj b⟫_ℝ)
    (hpass : ∀ v : H, ⟪v, Mdot v⟫_ℝ = 2 * ⟪v, C v⟫_ℝ)
    (hDnn : ∀ v : H, 0 ≤ ⟪v, D v⟫_ℝ) (y : CoupledState H) :
    coupledLyapRate M C D K J Minv Jadj Mdot y ≤ 0 := by
  rw [coupled_total_dissipation hMsa hKsa hMinv hJadj hpass y]
  exact neg_nonpos.mpr (hDnn y.2)

/-- **Discharge of `propIV1_tendsto`'s `hdec`.** Given a closed-loop field `f` and
Lyapunov `V` whose Fréchet-derivative along `f` realizes the assembled total rate
(`hreal` — the deferred state-dependent-operator calculus), the required
`∀ y, DV(y)[f y] ≤ 0` holds. This is the exact hypothesis shape Prop IV.1's assembly
names, now supplied from `coupled_decrease` rather than assumed. -/
theorem coupled_hdec
    (hMsa : ∀ a b : H, ⟪M a, b⟫_ℝ = ⟪a, M b⟫_ℝ)
    (hKsa : ∀ a b : H, ⟪K a, b⟫_ℝ = ⟪a, K b⟫_ℝ)
    (hMinv : ∀ w : H, M (Minv w) = w)
    (hJadj : ∀ a b : H, ⟪J a, b⟫_ℝ = ⟪a, Jadj b⟫_ℝ)
    (hpass : ∀ v : H, ⟪v, Mdot v⟫_ℝ = 2 * ⟪v, C v⟫_ℝ)
    (hDnn : ∀ v : H, 0 ≤ ⟪v, D v⟫_ℝ)
    {V : CoupledState H → ℝ} {f : CoupledState H → CoupledState H}
    (hreal : ∀ y, fderiv ℝ V y (f y) = coupledLyapRate M C D K J Minv Jadj Mdot y)
    (y : CoupledState H) :
    fderiv ℝ V y (f y) ≤ 0 := by
  rw [hreal y]
  exact coupled_decrease hMsa hKsa hMinv hJadj hpass hDnn y

/-- **Capstone: the coupled-block trajectory converges to Γ₁.** Plugs the
discharged `hdec` (`coupled_hdec`) straight into the sealed `propIV1_tendsto`. The
remaining inputs are exactly Prop IV.1's established named interfaces: `hϕ`
(`IsSolutionTo`, Picard–Lindelöf), `hreal` (the Lyapunov rate along the field, with
constant operators `M C D K J Minv Jadj Mdot`), `hzero`, and `hcpt` (forward
precompactness, bounded by `blockLyap_coercive`). What `hzero` actually carries: with
`hreal`, `{y | DV[f] y = 0} = {y | ⟪y.2, D y.2⟫ = 0} ⊇ {(x̃, 0)}`, so any admissible
`Γ₁` contains the whole velocity-zero subspace `{v̆ = 0}` and the conclusion is
convergence to (at best) that subspace — the pointwise route's ceiling. `hzero` cannot
carry the `v̆ ≡ 0 ⇒ x̃ = 0` step; that needs the invariance argument of
`CoupledCollapse.coupled_collapse`. The `hdec` hole is filled by construction here. -/
theorem coupled_block_tendsto (ϕ : Flow ℝ (CoupledState H))
    {V : CoupledState H → ℝ} {f : CoupledState H → CoupledState H}
    (hϕ : IsSolutionTo ϕ f) (hV : Differentiable ℝ V)
    (hMsa : ∀ a b : H, ⟪M a, b⟫_ℝ = ⟪a, M b⟫_ℝ)
    (hKsa : ∀ a b : H, ⟪K a, b⟫_ℝ = ⟪a, K b⟫_ℝ)
    (hMinv : ∀ w : H, M (Minv w) = w)
    (hJadj : ∀ a b : H, ⟪J a, b⟫_ℝ = ⟪a, Jadj b⟫_ℝ)
    (hpass : ∀ v : H, ⟪v, Mdot v⟫_ℝ = 2 * ⟪v, C v⟫_ℝ)
    (hDnn : ∀ v : H, 0 ≤ ⟪v, D v⟫_ℝ)
    (hreal : ∀ y, fderiv ℝ V y (f y) = coupledLyapRate M C D K J Minv Jadj Mdot y)
    {Γ₁ : Set (CoupledState H)} (hzero : {y | fderiv ℝ V y (f y) = 0} ⊆ Γ₁)
    (y₀ : CoupledState H)
    (hcpt : ForwardPrecompact ϕ y₀) :
    Tendsto (fun t : ℝ => Metric.infDist (ϕ t y₀) Γ₁) atTop (𝓝 0) :=
  propIV1_tendsto ϕ hϕ hV
    (coupled_hdec hMsa hKsa hMinv hJadj hpass hDnn hreal) hzero y₀ hcpt

end CoupledDissipation

end Ctrllib

#print axioms Ctrllib.coupled_total_dissipation
#print axioms Ctrllib.coupled_decrease
#print axioms Ctrllib.coupled_hdec
#print axioms Ctrllib.coupled_block_tendsto
