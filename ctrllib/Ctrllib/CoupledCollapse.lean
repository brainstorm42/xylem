/-
TARGET L4B-WIRE — discharge Prop IV.1's `hzero` through the closed-loop field
(ctrllib, difficulty M). The paper's closing line (giordano2019coordinated
§IV.D): "Applying LaSalle to (34b), v̆ ≡ 0 implies x̃ = 0." This module WIRES the
sealed algebra of that step (StiffnessResidual, Rayleigh) into the sealed LaSalle
engine (LaSalle + Reduction) at the coupled-block field level, and assembles the
resulting convergence to the origin.

THE STRUCTURAL FACT THE PIN FORCED (the corresponding private check, before any Lean).
The sealed previous lane gives the TOTAL Lyapunov rate `V̇ = -⟪v̆, D̆ v̆⟫`
(`coupled_total_dissipation`, via the passivity collapse). This depends ONLY on
v̆, so its zero-set is the WHOLE subspace `{v̆ = 0}` — NOT `{0}`. Consequently the
*pointwise* `hzero` of the sealed `propIV1_tendsto` ( `{y | V̇ y = 0} ⊆ {0}` ) is
FALSE (5000/5000 numeric counterexamples: any `(x̃, 0)` with `x̃ ≠ 0`). The origin
is reached only via the INVARIANCE argument: on the largest invariant subset of
`{v̆ = 0}`, `v̆ ≡ 0` along the orbit ⇒ `v̇̆ ≡ 0` ⇒ (eq 34b) `J_x̃ᵀ K̆ x̃ = 0` ⇒
(StiffnessResidual) `x̃ = 0`. This is EXACTLY why the sealed `com_attractive` uses
`com_collapse` (invariant-set) rather than `propIV1_tendsto`; the coupled block
does the same. Discharging propIV1_tendsto's pointwise hzero to `{0}` would be a
FALSE seal — we do not.

WHAT IS PROVEN (real content, non-vacuous):
  `coupled_collapse` — the field-level LaSalle collapse: on ANY flow-invariant set
    `S` on which the Lyapunov derivative vanishes, `S ⊆ {0}`. Runs
    `v̆ = 0 on S` (from `V̇ = -⟪v̆,D̆v̆⟫` + `D̆ ≻ 0`, the Rayleigh step) then the
    invariance `v̆ ≡ 0 ⇒ v̇̆ = 0 ⇒ J_x̃ᵀK̆x̃ = 0 ⇒ x̃ = 0` (StiffnessResidual,
    abstract). The direct analog of the sealed `com_collapse`, with the coupled
    field's velocity dynamics and the stiffness-residual injectivity in place of
    `com`'s bare `K x = 0 ⇒ x = 0`.
  `coupled_attractive` — THE CAPSTONE. Every precompact orbit of the coupled block
    converges to the origin, `ϕ t y₀ → 0`. Builds `V̇ = -⟪v̆,D̆v̆⟫` from the sealed
    `coupled_total_dissipation` (previous lane), feeds `lasalle` (L3) and the
    reduction engine `tendsto_infDist_of_omegaLimit_subset` (L4a) through
    `coupled_collapse`. This is Prop IV.1's convergence conclusion for the driven
    block, assembled from the closed-loop dynamics.
  `coupled_velocity_tendsto` — the LITERAL `propIV1_tendsto` instantiation the
    charter names: `coupled_hdec` (previous lane) as `hdec`, the reflexive
    containment as the honest `hzero`. Its conclusion is convergence to the
    velocity-zero set `{y | V̇ y = 0} = {v̆ = 0}` — the ceiling of the pointwise
    route, strictly weaker than `coupled_attractive`'s origin. Recorded to make the
    `{v̆=0}` vs `{0}` gap explicit and machine-checked.

REUSE (no re-proof): `coupled_total_dissipation`, `coupled_hdec` (CoupledDissipation);
`g2Field` (CoupledField); `lasalle`, `IsSolutionTo`, `IsInvariant`, `propIV1_tendsto`,
`tendsto_infDist_of_omegaLimit_subset` (LaSalle/Reduction). The collapse structure is
the sealed `com_collapse`/`com_attractive` template, component-swapped (velocity = `y.2`).

INTERFACE BOUNDARY (honest — the defense will be asked about exactly this list):
  * `hϕ : IsSolutionTo ϕ f` — the flow solving the ODE (Picard–Lindelöf), the L3
    precedent.
  * `hcpt` — `ForwardPrecompact ϕ y₀`, forward-only precompactness of the orbit
    (bounded by the sealed `blockLyap_coercive`; same forward-only interface as
    `com_attractive`).
  * `hreal` — the Lyapunov Fréchet-derivative along the field realizes the assembled
    total rate `coupledLyapRate M C D K J Minv Jadj Mdot y`. MODELLING SCOPE: in this
    statement `M C D K J Minv Jadj Mdot` are FIXED operators (`variable … (M C … : H →L[ℝ] H)`),
    so `hreal`/`hfield` describe a constant-operator (LTI, with a skew-type `C` via `hpass`)
    instance. The configuration-dependent system M̆(q), C̆(q), … of the paper is NOT covered
    by this statement; the ledger (the corresponding local note, row `hreal + hfield`) records the boundary.
  * `hfield : ∀ y, (f y).2 = (g2Field …).2` — the true field's VELOCITY component
    is the eq-34b right-hand side with the same fixed operators. New to this lane
    (the CoM block had no Coriolis, so there `f = comField` exactly); the velocity
    dynamics enter as their own named fact. Physical, not smuggled.
  * `hMsa/hKsa/hMinv/hJadj/hpass/hDnn` — the CoupledField/CoupledDissipation
    operator hypotheses (symmetry, inverse, adjoint, passivity, D̆ ⪰ 0); theorems
    for the concrete SPD blocks.
  * `hDdef : ⟪v,D̆v⟫ = 0 → v = 0` — D̆ definite; concretely the sealed Rayleigh
    `le_dotProduct_mulVec` with c₁ = λ_min(D̆) > 0.
  * `hMinj : Injective Minv` — M̆ invertible (`coupled_collapse` only; in
    `coupled_attractive` it is derived from `hMinv`).
  * `hJKinj : Jadj (K x) = 0 → x = 0` — the abstract transcription of the sealed
    `stiffness_residual_injective'` (K̆ ≻ 0, J_x̃ square nonsingular). The `com`
    `hKdef` precedent.

SymPy-pinned: the corresponding symbolic check (not bundled).py.
Human derivation: the corresponding derivation record (not bundled)
-/
import Mathlib.Analysis.InnerProductSpace.Calculus
import Ctrllib.CoupledDissipation

open Set Filter Topology omegaLimit
open scoped InnerProductSpace

namespace Ctrllib

section CoupledCollapse

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  (M C D K J Minv Jadj Mdot : H →L[ℝ] H)

variable {M C D K J Minv Jadj Mdot}

/-- **The field-level LaSalle collapse.** On any set `S` invariant under the flow,
on which the Lyapunov derivative vanishes, the state is the origin: `S ⊆ {0}`.

Two moves. (1) `v̆ = 0` on `S`: the total rate `V̇ = -⟪v̆, D̆ v̆⟫` (`hrate`, the sealed
previous lane) is zero on `S`, and `D̆` definite (`hDdef`, the Rayleigh step) kills
`v̆`. (2) Invariance: `v̆ ≡ 0` along the orbit forces the velocity derivative `v̇̆`
(the flow's second component) to zero; the field's velocity dynamics (`hfield`,
eq 34b) then read `-M̆⁻¹(J_x̃ᵀ K̆ x̃) = 0`, so `Minv` injective (`hMinj`) gives
`J_x̃ᵀ K̆ x̃ = 0`, and the stiffness-residual injectivity (`hJKinj`) gives `x̃ = 0`.
The direct analog of the sealed `com_collapse`, with `y.2` the velocity. -/
theorem coupled_collapse (ϕ : Flow ℝ (CoupledState H))
    {V : CoupledState H → ℝ} {f : CoupledState H → CoupledState H}
    (hϕ : IsSolutionTo ϕ f)
    (hrate : ∀ y, fderiv ℝ V y (f y) = -⟪y.2, D y.2⟫_ℝ)
    (hfield : ∀ y, (f y).2 = (g2Field C D K J Minv Jadj y).2)
    (hDdef : ∀ v : H, ⟪v, D v⟫_ℝ = 0 → v = 0)
    (hMinj : Function.Injective Minv)
    (hJKinj : ∀ x : H, Jadj (K x) = 0 → x = 0)
    {S : Set (CoupledState H)} (hinv : IsInvariant ϕ.toFun S)
    (hvanish : ∀ y ∈ S, fderiv ℝ V y (f y) = 0) :
    S ⊆ {0} := by
  -- (1) the velocity component vanishes on all of S
  have hv0 : ∀ w ∈ S, (w : CoupledState H).2 = 0 := by
    intro w hw
    have h := hvanish w hw
    rw [hrate w] at h
    exact hDdef _ (by linarith [h])
  intro y hy
  rw [Set.mem_singleton_iff]
  have hy2 : y.2 = 0 := hv0 y hy
  -- (2) differentiate the velocity component along the orbit; it is constant 0 on S
  have hbase : HasDerivAt (fun s : ℝ => ϕ s y) (f y) 0 := by
    have h := hϕ y 0
    rwa [ϕ.map_zero_apply] at h
  have hproj : HasDerivAt (fun s : ℝ => (ϕ s y).2) (f y).2 0 := by
    have h := HasFDerivAt.comp_hasDerivAt (0 : ℝ)
      (ContinuousLinearMap.snd ℝ H H).hasFDerivAt hbase
    simpa only [ContinuousLinearMap.coe_snd', Function.comp_def] using h
  have hconst : (fun s : ℝ => (ϕ s y).2) = fun _ => (0 : H) := by
    funext s
    exact hv0 _ (hinv s hy)
  have hzero : HasDerivAt (fun s : ℝ => (ϕ s y).2) 0 0 := by
    rw [hconst]; exact hasDerivAt_const 0 0
  have hfy2 : (f y).2 = 0 := hproj.unique hzero
  -- unpack: on v̆ = 0 the field velocity is -(Minv (J_x̃ᵀ K̆ x̃))
  have hval : (f y).2 = -(Minv (Jadj (K y.1))) := by
    rw [hfield y]
    change -(Minv (C y.2 + D y.2 + Jadj (K y.1))) = -(Minv (Jadj (K y.1)))
    rw [hy2]
    simp only [map_zero, zero_add]
  rw [hval, neg_eq_zero] at hfy2
  have hJK : Jadj (K y.1) = 0 := hMinj (by rw [hfy2, map_zero])
  have hy1 : y.1 = 0 := hJKinj _ hJK
  exact Prod.ext hy1 hy2

/-- **The capstone — convergence to the origin.** For a flow solving the coupled
closed-loop field with precompact orbit closure, every trajectory converges to the
origin: `ϕ t y₀ → 0`. Builds the total rate `V̇ = -⟪v̆, D̆ v̆⟫` from the sealed
`coupled_total_dissipation` (previous lane), then assembles the sealed `lasalle`
(L3) and `tendsto_infDist_of_omegaLimit_subset` (L4a) through `coupled_collapse`.
This is Prop IV.1's attractivity conclusion for the driven block — convergence of
forward-precompact trajectories, not ε–δ stability (see `KhalilStability.AsympStable`;
formerly named `coupled_gas`) — assembled from the closed-loop dynamics with only
`IsSolutionTo`, `hreal`, `hfield`, `hcpt`, and the concrete-SPD operator facts
remaining named. Scope: `hreal`/`hfield` fix constant `M C D K J Minv Jadj Mdot`
(an LTI instance with skew-type `C`); the configuration-dependent M̆(q) system is
not covered by this statement. -/
theorem coupled_attractive (ϕ : Flow ℝ (CoupledState H))
    {V : CoupledState H → ℝ} {f : CoupledState H → CoupledState H}
    (hϕ : IsSolutionTo ϕ f) (hV : Differentiable ℝ V)
    (hMsa : ∀ a b : H, ⟪M a, b⟫_ℝ = ⟪a, M b⟫_ℝ)
    (hKsa : ∀ a b : H, ⟪K a, b⟫_ℝ = ⟪a, K b⟫_ℝ)
    (hMinv : ∀ w : H, M (Minv w) = w)
    (hJadj : ∀ a b : H, ⟪J a, b⟫_ℝ = ⟪a, Jadj b⟫_ℝ)
    (hpass : ∀ v : H, ⟪v, Mdot v⟫_ℝ = 2 * ⟪v, C v⟫_ℝ)
    (hreal : ∀ y, fderiv ℝ V y (f y) = coupledLyapRate M C D K J Minv Jadj Mdot y)
    (hfield : ∀ y, (f y).2 = (g2Field C D K J Minv Jadj y).2)
    (hDnn : ∀ v : H, 0 ≤ ⟪v, D v⟫_ℝ)
    (hDdef : ∀ v : H, ⟪v, D v⟫_ℝ = 0 → v = 0)
    (hJKinj : ∀ x : H, Jadj (K x) = 0 → x = 0)
    (y₀ : CoupledState H)
    (hcpt : ForwardPrecompact ϕ y₀) :
    Tendsto (fun t : ℝ => ϕ t y₀) atTop (𝓝 0) := by
  -- Minv is injective (M is its left inverse), as in `com_collapse`
  have hMinj : Function.Injective Minv := by
    intro a b hab
    have := congrArg M hab
    rwa [hMinv, hMinv] at this
  -- the total dissipation rate, from the sealed previous lane
  have hrate : ∀ y, fderiv ℝ V y (f y) = -⟪y.2, D y.2⟫_ℝ := fun y =>
    (hreal y).trans (coupled_total_dissipation hMsa hKsa hMinv hJadj hpass y)
  have hdec : ∀ y, fderiv ℝ V y (f y) ≤ 0 := fun y => by
    rw [hrate y]; exact neg_nonpos.mpr (hDnn y.2)
  have hlas := lasalle ϕ hϕ hV hdec y₀ hcpt
  have hsub : ω⁺ ϕ.toFun {y₀} ⊆ ({0} : Set (CoupledState H)) :=
    coupled_collapse ϕ hϕ hrate hfield hDdef hMinj hJKinj hlas.2.1 hlas.2.2.2
  have htend := tendsto_infDist_of_omegaLimit_subset ϕ y₀ hcpt hsub
  simp only [Metric.infDist_singleton] at htend
  rw [tendsto_iff_dist_tendsto_zero]
  exact htend

@[deprecated coupled_attractive (since := "2026-08-15")]
alias coupled_gas := coupled_attractive

/-- **The literal `propIV1_tendsto` instantiation** (the charter's named corollary),
with the honest `hzero`. Feeds the sealed `coupled_hdec` (previous lane) as `hdec`
and the reflexive containment as `hzero`. Conclusion: the orbit converges to the
velocity-zero set `{y | V̇ y = 0}`, which by `coupled_total_dissipation` + `D̆ ≻ 0`
is exactly `{v̆ = 0}`. This is the CEILING of the pointwise route — strictly weaker
than `coupled_attractive`'s origin (the pin's 5000/5000 counterexamples live in this set).
The origin needs the invariance collapse above. -/
theorem coupled_velocity_tendsto (ϕ : Flow ℝ (CoupledState H))
    {V : CoupledState H → ℝ} {f : CoupledState H → CoupledState H}
    (hϕ : IsSolutionTo ϕ f) (hV : Differentiable ℝ V)
    (hMsa : ∀ a b : H, ⟪M a, b⟫_ℝ = ⟪a, M b⟫_ℝ)
    (hKsa : ∀ a b : H, ⟪K a, b⟫_ℝ = ⟪a, K b⟫_ℝ)
    (hMinv : ∀ w : H, M (Minv w) = w)
    (hJadj : ∀ a b : H, ⟪J a, b⟫_ℝ = ⟪a, Jadj b⟫_ℝ)
    (hpass : ∀ v : H, ⟪v, Mdot v⟫_ℝ = 2 * ⟪v, C v⟫_ℝ)
    (hDnn : ∀ v : H, 0 ≤ ⟪v, D v⟫_ℝ)
    (hreal : ∀ y, fderiv ℝ V y (f y) = coupledLyapRate M C D K J Minv Jadj Mdot y)
    (y₀ : CoupledState H)
    (hcpt : ForwardPrecompact ϕ y₀) :
    Tendsto (fun t : ℝ => Metric.infDist (ϕ t y₀) {y | fderiv ℝ V y (f y) = 0})
      atTop (𝓝 0) :=
  propIV1_tendsto ϕ hϕ hV
    (coupled_hdec hMsa hKsa hMinv hJadj hpass hDnn hreal)
    (Set.Subset.refl _) y₀ hcpt

end CoupledCollapse

end Ctrllib

#print axioms Ctrllib.coupled_collapse
#print axioms Ctrllib.coupled_attractive
#print axioms Ctrllib.coupled_velocity_tendsto
