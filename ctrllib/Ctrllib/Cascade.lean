/-
The Panteley–Loría cascade theorem (TARGET R4 of the ctrllib stream).

ENGINE + INSTANTIATION (ratified 2026-07-08).

SOURCES (rendered, Docs/raw/md/):
  * panteley2001growth (Automatica 37 (2001) 453-460) — the primary source. Lemma 2:
      "If systems (2) and (4) are UGAS and the solutions of (1) and (2) are globally
       uniformly bounded then (1) and (2) is UGAS."  (the GAS+GAS+BS ⇒ GAS assembly)
    Its proof rides eq (35)   `v̇_(1)(t) ≤ -v(t) + c(r)‖x₂(t)‖`
    where `v = 𝒱(x₁)` is the reshaped Lyapunov function of Proposition 1 (eq 14:
    `𝒱̇_(4) ≤ -𝒱`), and the sandwich eq (10)/(13) `α₁(‖x₁‖) ≤ V ≤ α₂(‖x₁‖)`, α₁,α₂ ∈ 𝒦∞.
  * panteley1998global (Syst. Control Lett.) — companion; Theorem 2 is the same cascade
    attractivity conclusion, its eq (22) `V̇_(4) ≤ α_v‖x₂(t)‖` the same interconnection bound.

THE REUSE THAT MAKES THIS CHEAP AND HONEST. Panteley's eq (35) is *exactly* the shape the
already-sealed comparison layer consumes: `TimeVaryingComparison.comparison_tendsto_zero`
proves `v' t ≤ -a·v t + ε t` with `ε → 0` forces `v → 0`, and `comparison_bounded` gives the
bounded-ε ultimate bound. Set `a = 1`, `ε(t) = c‖x₂(t)‖`. The remaining step — turning
`v = V∘x₁ → 0` into `x₁ → 0` — is the class-𝒦∞ sandwich inverted, and the inverse `classKInv`
with its continuity, monotonicity and `classKInv α 0 = 0` are the sealed
`ComparisonFunctions` stones. So the cascade's
attractivity is the sealed comparison lemma + the sealed 𝒦∞ inverse, assembled — no new analysis.

WHAT IS PROVEN (real content):
  `IsClassKInfinity.tendsto_zero_of_sandwich` — the 𝒦∞ squeeze: `α ∈ 𝒦∞`, `α‖x t‖ ≤ w t` eventually,
    `w → 0` ⇒ `x t → 0`. The ISS-standard "V → 0 ⇒ state → 0" via `α⁻¹`, on the sealed inverse.
  `cascade_attractive` — THE ENGINE (attractivity). Driving output `x₂ → 0` (Σ₂ UGAS) + the reshaped
    Lyapunov sandwich (eq 10/13) + the interconnection differential inequality (eq 35) ⇒ the joint
    cascade state `(x₁, x₂) → 0`. This is Lemma 2's / Theorem 2's attractivity conclusion at the
    trajectory level: convergence of the given forward-precompact trajectory, NOT ε–δ stability
    (for the genuine notion see `KhalilStability.AsympStable`). The `_attractive` suffix
    (formerly `_gas`) names exactly this.
  `cascade_bounded` — Lemma 2's boundedness / UGS half (eq 39): a bounded driving output keeps the
    reshaped Lyapunov value inside the ultimate bound `V(x₁ 0) + c·Mx/a`, from `comparison_bounded`.
  `propIV1_cascade_attractive` — THE INSTANTIATION. A second, independent kernel-checked route to
    Prop IV.1's conclusion: `com_attractive` (the sealed CoM-loop attractivity) discharges the
    DRIVING subsystem `x₂ = ϕc·z₀ → 0`, fed straight into `cascade_attractive`; the DRIVEN
    subsystem is the coupled block (`x₁ : CoupledState H`, reshaped `Vd`). Conclusion: the full
    closed-loop state `(x₁, ϕc·z₀) → 0`.

WHY IT IS INDEPENDENT of the sealed `coupled_attractive` route. `coupled_attractive` reaches the
coupled block's origin by LaSalle on the coupled field directly. This route reaches the JOINT
(com, coupled) origin through the CASCADE theorem, using `com_attractive` as the driving engine
and the comparison/growth argument (not LaSalle) for the driven convergence.
`coupled_attractive` is the JUSTIFICATION for the driven-block reshaping interface (its
zero-input attractivity is Prop 1's premise), documented in the corresponding local note — never a silent
substitution.

ISS. Deliberately NOT defined: the majorization route (panteley2001growth Theorem 4) needs only
the differential inequality, not the ISS characterisation (Theorem 3's optional extra
conclusion). Per the ratified done-bar, "ISS definitions ONLY where the theorem needs them" —
here, nowhere.

INTERFACE BOUNDARY (honest; the corresponding local note carries the rows):
  * `hsand` — the class-𝒦∞ sandwich `α₁‖x₁‖ ≤ V(x₁)` (eq 10/13). For the reshaped 𝒱 of Proposition 1
    it is a theorem (converse Lyapunov), here the named modelling input.
  * `hdi` (eq 35) — the interconnection differential inequality `v' ≤ -a·V(x₁) + c‖x₂‖`. Bundles the
    reshaped decrease (Prop 1 eq 14) + the linear growth bound (A5) + the a-priori boundedness
    that Theorem 4/5's forward-completeness (`∫ds/α₆ = ∞` non-escape) establishes upstream. It is
    the honest input, exactly the object Panteley–Loría integrate — the same status
    TimeVaryingComparison gives its `hbound`.
  * `hvc`, `hv` — continuity/right-derivative of `V∘x₁`; applier-side chain-rule regularity, as in
    TimeVaryingComparison.
  * (instantiation) `hϕc`, `hcptc` + the CoM operator hypotheses — the sealed `com_attractive`
    interface, discharged for concrete SPD blocks exactly as ComLaSalle documents.

SymPy pin: the corresponding symbolic check (not bundled).py
  (𝒦∞ inverse leftInv + Panteley Example 2 numeric).
Human derivation: the corresponding derivation record (not bundled)
-/
import Ctrllib.TimeVaryingComparison
import Ctrllib.ComparisonFunctions
import Ctrllib.ComLaSalle
import Ctrllib.CoupledCollapse

open Set Filter Topology
open scoped InnerProductSpace

namespace Ctrllib

/-! ### The class-𝒦∞ squeeze -/

/-- **The ISS-standard squeeze.** If `α ∈ 𝒦∞`, the norm of `x t` is bounded (eventually) by
`α⁻¹(w t)` through `α ‖x t‖ ≤ w t`, and `w → 0`, then `x t → 0`. This is the honest general way to
turn a Lyapunov value's decay into state decay: invert the class-𝒦∞ lower sandwich. The inverse
`classKInv α` and its monotonicity, continuity and `classKInv α 0 = 0` are the sealed
`ComparisonFunctions` stones (`classKInv_isClassKInfinity`, `classKInv_leftInvOn`). -/
theorem IsClassKInfinity.tendsto_zero_of_sandwich
    {E : Type*} [NormedAddCommGroup E] {α : ℝ → ℝ} {x : ℝ → E} {w : ℝ → ℝ}
    (hα : IsClassKInfinity α)
    (hsand : ∀ᶠ t in atTop, α ‖x t‖ ≤ w t)
    (hw : Tendsto w atTop (𝓝 0)) :
    Tendsto x atTop (𝓝 0) := by
  have hinv : IsClassKInfinity (classKInv α) := hα.classKInv_isClassKInfinity
  -- eventually `‖x t‖ ≤ classKInv α (w t)` (monotone inverse of the lower sandwich)
  have hbound : ∀ᶠ t in atTop, ‖x t‖ ≤ classKInv α (w t) := by
    filter_upwards [hsand] with t ht
    have hxn : (0 : ℝ) ≤ ‖x t‖ := norm_nonneg _
    have hαn : (0 : ℝ) ≤ α ‖x t‖ := hα.toIsClassK.nonneg hxn
    have hwn : (0 : ℝ) ≤ w t := le_trans hαn ht
    have hmono := hinv.toIsClassK.monotoneOn (mem_Ici.mpr hαn) (mem_Ici.mpr hwn) ht
    rwa [hα.classKInv_leftInvOn (mem_Ici.mpr hxn)] at hmono
  -- `w t ∈ [0,∞)` eventually, so the composition can ride the inverse's continuity at `0`
  have hwnn : ∀ᶠ t in atTop, w t ∈ Ici (0 : ℝ) := by
    filter_upwards [hsand] with t ht
    exact mem_Ici.mpr (le_trans (hα.toIsClassK.nonneg (norm_nonneg _)) ht)
  -- `classKInv α (w t) → classKInv α 0 = 0`
  have hcw : Tendsto (fun t => classKInv α (w t)) atTop (𝓝 0) := by
    have hcont : ContinuousWithinAt (classKInv α) (Ici 0) 0 :=
      hinv.toIsClassK.continuousOn.continuousWithinAt (mem_Ici.mpr le_rfl)
    have hct : Tendsto (classKInv α) (𝓝[Ici (0 : ℝ)] 0) (𝓝 (classKInv α 0)) := hcont
    rw [hinv.toIsClassK.map_zero] at hct
    have hwin : Tendsto w atTop (𝓝[Ici (0 : ℝ)] 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within w hw hwnn
    exact hct.comp hwin
  exact squeeze_zero_norm' hbound hcw

/-! ### The cascade engine -/

section Engine

variable {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedAddCommGroup E₂]
  {x₁ : ℝ → E₁} {x₂ : ℝ → E₂} {V : E₁ → ℝ} {v' α₁ : ℝ → ℝ} {a c : ℝ}

/-- **The Panteley–Loría cascade theorem (attractivity engine).** The driving subsystem's output
`x₂ → 0` (Σ₂ UGAS) together with the reshaped Lyapunov sandwich `α₁‖x₁‖ ≤ V(x₁)` (eq 10/13,
`α₁ ∈ 𝒦∞`) and the interconnection differential inequality `v' ≤ -a·V(x₁) + c‖x₂‖` (eq 35) force
the joint cascade state `(x₁, x₂)` to the origin. Attractivity of the given trajectory only —
no ε–δ stability, no uniformity (see `KhalilStability.AsympStable` for the genuine notion) —
the attractivity conclusion of panteley2001growth Lemma 2 / panteley1998global Theorem 2.

The proof: `ε(t) = c‖x₂ t‖ → 0` since `x₂ → 0`; the sealed `comparison_tendsto_zero` gives
`V(x₁ t) → 0` (nonnegativity `hnn` is read off the sandwich, not assumed); the 𝒦∞ squeeze
`tendsto_zero_of_sandwich` turns that into `x₁ → 0`; pairing with `x₂ → 0` gives the joint limit. -/
theorem cascade_attractive
    (ha : 0 < a)
    (hα₁ : IsClassKInfinity α₁)
    (hsand : ∀ t ∈ Ici (0 : ℝ), α₁ ‖x₁ t‖ ≤ V (x₁ t))
    (hvc : ContinuousOn (fun t => V (x₁ t)) (Ici 0))
    (hv : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt (fun t => V (x₁ t)) (v' t) (Ici t) t)
    (hdi : ∀ t ∈ Ici (0 : ℝ), v' t ≤ -a * V (x₁ t) + c * ‖x₂ t‖)
    (hx2 : Tendsto x₂ atTop (𝓝 0)) :
    Tendsto (fun t => (x₁ t, x₂ t)) atTop (𝓝 0) := by
  -- the disturbance `ε(t) = c‖x₂ t‖` vanishes
  have hnorm2 : Tendsto (fun t => ‖x₂ t‖) atTop (𝓝 0) := by
    simpa using hx2.norm
  have heps : Tendsto (fun t => c * ‖x₂ t‖) atTop (𝓝 0) := by
    simpa using hnorm2.const_mul c
  -- nonnegativity of the Lyapunov value from the lower sandwich
  have hnn : ∀ t ∈ Ici (0 : ℝ), 0 ≤ V (x₁ t) := fun t ht =>
    le_trans (hα₁.toIsClassK.nonneg (norm_nonneg _)) (hsand t ht)
  -- the sealed comparison lemma: `V(x₁ t) → 0`
  have hVzero : Tendsto (fun t => V (x₁ t)) atTop (𝓝 0) :=
    comparison_tendsto_zero ha hvc hv hdi hnn heps
  -- the 𝒦∞ squeeze: `x₁ → 0`
  have hsand' : ∀ᶠ t in atTop, α₁ ‖x₁ t‖ ≤ V (x₁ t) :=
    eventually_atTop.mpr ⟨0, fun t ht => hsand t (mem_Ici.mpr ht)⟩
  have hx1 : Tendsto x₁ atTop (𝓝 0) := hα₁.tendsto_zero_of_sandwich hsand' hVzero
  -- pair the two component limits
  change Tendsto (fun t => (x₁ t, x₂ t)) atTop (𝓝 ((0 : E₁), (0 : E₂)))
  exact hx1.prodMk_nhds hx2

@[deprecated cascade_attractive (since := "2026-08-15")]
alias cascade_gas := cascade_attractive

/-- **Lemma 2's boundedness / UGS half** (eq 39). A bounded driving output `‖x₂‖ ≤ Mx` keeps the
reshaped Lyapunov value inside the ultimate bound `V(x₁ 0) + c·Mx/a` — the time-varying
analogue of an ultimate bound, from the sealed `comparison_bounded`. With properness of `V`
this is the uniform global boundedness Lemma 2 assumes; here we deliver it at the Lyapunov
level. -/
theorem cascade_bounded
    (ha : 0 < a) (hc : 0 ≤ c) {Mx : ℝ} (hMx : 0 ≤ Mx)
    (hα₁ : IsClassKInfinity α₁)
    (hsand : ∀ t ∈ Ici (0 : ℝ), α₁ ‖x₁ t‖ ≤ V (x₁ t))
    (hvc : ContinuousOn (fun t => V (x₁ t)) (Ici 0))
    (hv : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt (fun t => V (x₁ t)) (v' t) (Ici t) t)
    (hdi : ∀ t ∈ Ici (0 : ℝ), v' t ≤ -a * V (x₁ t) + c * ‖x₂ t‖)
    (hx2M : ∀ t ∈ Ici (0 : ℝ), ‖x₂ t‖ ≤ Mx) :
    ∀ t ∈ Ici (0 : ℝ), V (x₁ t) ≤ V (x₁ 0) + c * Mx / a := by
  have hv0 : 0 ≤ V (x₁ 0) :=
    le_trans (hα₁.toIsClassK.nonneg (norm_nonneg _)) (hsand 0 self_mem_Ici)
  have hεM : ∀ t ∈ Ici (0 : ℝ), c * ‖x₂ t‖ ≤ c * Mx := fun t ht =>
    mul_le_mul_of_nonneg_left (hx2M t ht) hc
  exact comparison_bounded ha (mul_nonneg hc hMx) hvc hv hdi hεM hv0

end Engine

/-! ### The instantiation against the sealed CoM-loop attractivity -/

section Instantiation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- **A second, independent kernel-checked route to Prop IV.1's conclusion.** The sealed
`com_attractive` (every forward-precompact CoM-loop trajectory converges to the origin)
discharges the cascade's DRIVING subsystem `x₂ = ϕc · z₀ → 0`; the DRIVEN subsystem is the
coupled block (`x₁ : CoupledState H`, its reshaped Lyapunov `Vd`), entering through the named
cascade interface (sandwich `hsand` = eq 10/13, differential inequality `hdi` = eq 35). Feeding
both into `cascade_attractive` yields convergence of the FULL closed-loop state
`(x₁, ϕc·z₀) → 0` — attractivity of the given forward-precompact trajectory, not ε–δ stability
(see `KhalilStability.AsympStable`).

Independent of the `coupled_attractive` LaSalle route: here the coupled block's convergence
comes from the cascade comparison argument driven by the CoM loop, not from LaSalle on the
coupled field. The coupled block's zero-input attractivity (`coupled_attractive`) is the
justification for the reshaping interface (Proposition 1), recorded in the corresponding local note — never
silently substituted. -/
theorem propIV1_cascade_attractive
    -- driving subsystem: the CoM loop, with the sealed `com_attractive` hypotheses
    (ϕc : Flow ℝ (ComState H)) (Mc Dc Kc Mcinv : H →L[ℝ] H)
    (hϕc : IsSolutionTo ϕc (comField Dc Kc Mcinv))
    (hMsa : ∀ a b : H, ⟪Mc a, b⟫_ℝ = ⟪a, Mc b⟫_ℝ)
    (hKsa : ∀ a b : H, ⟪Kc a, b⟫_ℝ = ⟪a, Kc b⟫_ℝ)
    (hMinv : ∀ w : H, Mc (Mcinv w) = w)
    (hDnn : ∀ v : H, 0 ≤ ⟪v, Dc v⟫_ℝ)
    (hDdef : ∀ v : H, ⟪v, Dc v⟫_ℝ = 0 → v = 0)
    (hKdef : ∀ x : H, Kc x = 0 → x = 0)
    (z₀ : ComState H)
    (hcptc : ForwardPrecompact ϕc z₀)
    -- driven subsystem: the coupled block, through the named cascade interface
    {x₁ : ℝ → CoupledState H} {Vd : CoupledState H → ℝ} {v' α₁ : ℝ → ℝ} {a c : ℝ}
    (ha : 0 < a) (hα₁ : IsClassKInfinity α₁)
    (hsand : ∀ t ∈ Ici (0 : ℝ), α₁ ‖x₁ t‖ ≤ Vd (x₁ t))
    (hvc : ContinuousOn (fun t => Vd (x₁ t)) (Ici 0))
    (hv : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt (fun t => Vd (x₁ t)) (v' t) (Ici t) t)
    (hdi : ∀ t ∈ Ici (0 : ℝ), v' t ≤ -a * Vd (x₁ t) + c * ‖ϕc t z₀‖) :
    Tendsto (fun t => (x₁ t, ϕc t z₀)) atTop (𝓝 0) := by
  have hx2 : Tendsto (fun t => ϕc t z₀) atTop (𝓝 0) :=
    com_attractive ϕc hϕc hMsa hKsa hMinv hDnn hDdef hKdef z₀ hcptc
  exact cascade_attractive ha hα₁ hsand hvc hv hdi hx2

@[deprecated propIV1_cascade_attractive (since := "2026-08-15")]
alias propIV1_cascade_gas := propIV1_cascade_attractive

end Instantiation

end Ctrllib

#print axioms Ctrllib.IsClassKInfinity.tendsto_zero_of_sandwich
#print axioms Ctrllib.cascade_attractive
#print axioms Ctrllib.cascade_bounded
#print axioms Ctrllib.propIV1_cascade_attractive
