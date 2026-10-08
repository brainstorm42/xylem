/-
TrackingCascade — cascading the PD+ tracking loop's forced storage bound
(`TrackingStrictBound.forced_rate_sqrt_comparison`) with the CoM loop
(`ComLaSalleMatrix.com_gas_matrix`), mirroring `Cascade.propIV1_cascade_gas` for
the tracking side (the corresponding design note follow-up).

THE STEP. `forced_rate_sqrt_comparison` seals the pointwise inequality
`Ẇ ≤ −(κ/c_hi)W + c'(f+ρ)√W` (`f = ‖x₂‖` the CoM-loop coupling norm, `ρ ≥ 0` a
regularization/residual floor) and stops there — its own note and the wiki page
the corresponding local note ("What is not bricked") name the missing piece: turning
this into `u := √W`'s LINEAR comparison shape `u' ≤ −(κ/(2c_hi))u + (c'/2)(f+ρ)`
needs `HasDerivWithinAt.sqrt` applied to a REALIZED trajectory — the flow
realisation neither `TrackingStrictBound` nor `TrackingCrossTerm` establishes.

THE ROUTE TAKEN HERE avoids that gap entirely by working on `W` directly with
Young's inequality (the report's alternative route) instead of on `u = √W`:
`c'(f+ρ)√W ≤ aW + K(f+ρ)²` with `a = κ/(2c_hi)`, `K = c'²c_hi/(2κ)` (`young_cross`
with `s = √W`, `t = f+ρ`, `λ = κ/(c_hi c')`). This turns the forced rate bound into
the exact `v' ≤ −a v + ε(t)` shape `TimeVaryingComparison.comparison_tendsto_zero`
/ `comparison_bounded` consume, on `W` itself — no chain rule for `√`, no
positivity of `W` beyond what the sandwich already gives (`W ≥ 0`).

WHAT IS PROVEN (real content):
  `tracking_forced_rate_majorant` — the Young-inequality reduction above: the
    √W-shaped forced rate bound implies the LINEAR comparison shape. Pure
    algebra, no flow realisation needed; pinned symbolically and against a
    numeric ODE integration (`the corresponding private check` (A)–(C)).
  `tracking_cascade_gas` — THE ENGINE, ρ = 0 case: `W`'s sandwich + the forced
    rate bound + `x₂ → 0` (CoM loop driving output) ⇒ `x₁ → 0`, via
    `comparison_tendsto_zero` (linear majorant → `W → 0`) then the class-𝒦∞
    squeeze `IsClassKInfinity.tendsto_zero_of_sandwich` with `α₁(s) = c_lo s²`
    (item 1, reusing the sealed `isClassKInfinity_sq` from `CoupledSandwich`) —
    the same two-stage assembly `Cascade.cascade_gas` uses, built directly from
    the sealed primitives rather than forced through `cascade_gas`'s own
    linear-in-`‖x₂‖` `hdi` shape (ours is √W-shaped; the Young reduction above is
    the bridge, done once at the `W` level instead of per-caller).
  `tracking_cascade_storage_bounded` / `tracking_cascade_bounded` — the ρ ≥ 0
    ultimate-bound half, mirroring `Cascade.cascade_bounded`: a uniform ceiling
    `‖x₂ t‖ ≤ Mx` (not `x₂ → 0`) keeps `W`, hence `‖x₁‖`, inside an explicit bound
    via `comparison_bounded`.
  `tracking_cascade_gas_com` — THE INSTANTIATION, mirroring
    `Cascade.propIV1_cascade_gas`: feeds the sealed `com_gas_matrix` (concrete SPD
    CoM loop, GAS) straight into `tracking_cascade_gas` as the driving `x₂ → 0`.

INTERFACE BOUNDARY (honest; status: INTERFACED, given assumptions — not derived).
  * `hWc`, `hWderiv`, `hdi` — the storage-along-the-flow function `W`, its
    derivative, and the forced rate bound `Ẇ ≤ −(κ/c_hi)W + c'(f+ρ)√W` ITSELF are
    all named hypotheses, exactly as `Cascade.cascade_gas` takes its own `hvc`/
    `hv`/`hdi` as named modelling inputs (never derived from a field/flow here).
    This bundles the SAME open gap `forced_rate_sqrt_comparison`'s note names:
    the flow realisation of `Ẇ` as the genuine derivative of `strictStorage`
    along a real closed-loop trajectory. Discharging it is explicitly NOT this
    module's job (it would mean inventing the bridge `TrackingStrictBound` and
    `TrackingCrossTerm` both decline to invent); a caller with a realized
    trajectory supplies `hWc`/`hWderiv`/`hdi` and the rest composes.
  * `hsand_lo` (`c_lo‖x₁‖² ≤ W`) — the lower half of the storage sandwich
    (`TrackingStrictBound.strict_storage_sandwich`'s shape, applied along the
    trajectory — a named hypothesis, not re-derived here); mirrors
    `Cascade.cascade_gas`'s own `hsand`, which likewise carries only the lower
    half (the upper half's role — supplying `hdi`'s `c_hi` coefficient — is
    already folded into `hdi` upstream via `forced_rate_sqrt_comparison`, so it
    is not re-carried as a separate hypothesis here).
  * `hx2` / `hx2M` — the CoM loop's convergence / uniform bound; for the concrete
    SPD CoM block, `tracking_cascade_gas_com` discharges `hx2` as a theorem via
    `com_gas_matrix`, exactly as `propIV1_cascade_gas` does for `com_gas`.

PINNED (the corresponding project check (not bundled).py):
  (A) the Young-split algebra `a = κ/(2c_hi)`, `K = c'²c_hi/(2κ)`; (B) the
  pointwise domination `−(κ/c_hi)W + c'(f+ρ)√W ≤ −aW + K(f+ρ)²` (5000 random
  cases); (C)–(D) numeric ODE integration of the actual nonlinear rate against the
  linear Grönwall majorant, `ρ = 0` convergence; (E) `ρ > 0` uniform-`Mx` ultimate
  bound matching `comparison_bounded`'s conclusion.

Human derivation: the corresponding local note
("Update" sections); wiki mirror
the corresponding local note.
-/
import Ctrllib.TrackingStrictBound
import Ctrllib.TimeVaryingComparison
import Ctrllib.Cascade
import Ctrllib.CoupledSandwich
import Ctrllib.ComLaSalleMatrix

open Set Filter Topology Matrix

namespace Ctrllib

section Engine

variable {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedAddCommGroup E₂]
  {x₁ : ℝ → E₁} {x₂ : ℝ → E₂} {W W' : ℝ → ℝ} {c_lo c_hi κ c' ρ : ℝ}

/-- **The Young-inequality majorant.** Converts the forced rate bound's `√W` shape
`W' ≤ −(κ/c_hi)W + c'(‖x₂‖+ρ)√W` (`forced_rate_sqrt_comparison`'s conclusion) into
the LINEAR comparison shape `TimeVaryingComparison.comparison_tendsto_zero` /
`comparison_bounded` consume directly: `W' ≤ −aW + K(‖x₂‖+ρ)²`,
`a = κ/(2c_hi)`, `K = c'²c_hi/(2κ)`. Pure algebra (`young_cross` with `s = √W`,
`t = ‖x₂‖+ρ`, `λ = κ/(c_hi c')`); needs only `W ≥ 0` (from the sandwich), never
the chain rule for `√` — the "work on `W` directly with Young" route, avoiding the
open flow-realisation gap the corresponding local note ("What is not bricked")
names for the `u = √W` route. Pinned algebraically and against a numeric ODE
integration in `the corresponding private check` (A)–(C).
(`0 ≤ ρ` is carried for interface fidelity with `forced_rate_sqrt_comparison`'s
own `hρ`, though the Young step below holds for any real `ρ`.) -/
theorem tracking_forced_rate_majorant
    (hchi : 0 < c_hi) (hκ : 0 < κ) (hcp : 0 < c') (_hρ : 0 ≤ ρ)
    (hWnn : ∀ t ∈ Ici (0 : ℝ), 0 ≤ W t)
    (hdi : ∀ t ∈ Ici (0 : ℝ), W' t ≤ -(κ / c_hi) * W t + c' * (‖x₂ t‖ + ρ) * Real.sqrt (W t)) :
    ∀ t ∈ Ici (0 : ℝ), W' t ≤ -(κ / (2 * c_hi)) * W t
      + c' ^ 2 * c_hi / (2 * κ) * (‖x₂ t‖ + ρ) ^ 2 := by
  intro t ht
  set lam : ℝ := κ / (c_hi * c') with hlam_def
  have hlam : 0 < lam := div_pos hκ (mul_pos hchi hcp)
  have hy := young_cross (C := c') (lam := lam) (s := Real.sqrt (W t)) (t := ‖x₂ t‖ + ρ)
    hcp.le hlam
  have hWsq : Real.sqrt (W t) ^ 2 = W t := Real.sq_sqrt (hWnn t ht)
  have ha : c' * lam / 2 = κ / (2 * c_hi) := by
    rw [hlam_def]; field_simp
  have hK : c' / (2 * lam) = c' ^ 2 * c_hi / (2 * κ) := by
    rw [hlam_def]; field_simp
  have hstep : c' * Real.sqrt (W t) * (‖x₂ t‖ + ρ)
      ≤ κ / (2 * c_hi) * W t + c' ^ 2 * c_hi / (2 * κ) * (‖x₂ t‖ + ρ) ^ 2 := by
    calc c' * Real.sqrt (W t) * (‖x₂ t‖ + ρ)
        ≤ c' * lam / 2 * Real.sqrt (W t) ^ 2 + c' / (2 * lam) * (‖x₂ t‖ + ρ) ^ 2 := hy
      _ = κ / (2 * c_hi) * W t + c' ^ 2 * c_hi / (2 * κ) * (‖x₂ t‖ + ρ) ^ 2 := by
          rw [hWsq, ha, hK]
  calc W' t ≤ -(κ / c_hi) * W t + c' * (‖x₂ t‖ + ρ) * Real.sqrt (W t) := hdi t ht
    _ = -(κ / c_hi) * W t + c' * Real.sqrt (W t) * (‖x₂ t‖ + ρ) := by ring
    _ ≤ -(κ / c_hi) * W t
        + (κ / (2 * c_hi) * W t + c' ^ 2 * c_hi / (2 * κ) * (‖x₂ t‖ + ρ) ^ 2) := by
        linarith [hstep]
    _ = -(κ / (2 * c_hi)) * W t + c' ^ 2 * c_hi / (2 * κ) * (‖x₂ t‖ + ρ) ^ 2 := by
        field_simp; ring

/-- **The tracking cascade engine (attractivity, `ρ = 0`).** The storage sandwich's
LOWER half `c_lo‖x₁‖² ≤ W` (`hsand_lo`) — the upper half's role, supplying `hdi`'s
`c_hi` coefficient, is already folded into `hdi` upstream via
`forced_rate_sqrt_comparison`, so it is not re-carried as a separate hypothesis
here — together with the forced rate bound `Ẇ ≤ −(κ/c_hi)W + c'‖x₂‖√W` and
the CoM loop's convergence `x₂ → 0` force `x₁ → 0`. Mirrors `Cascade.cascade_gas`'s
two-stage assembly (comparison decay then the class-𝒦∞ squeeze) but built directly
from the sealed primitives: the Young majorant above turns the forced rate into
the linear shape `comparison_tendsto_zero` consumes (`W → 0`), then
`IsClassKInfinity.tendsto_zero_of_sandwich` with `α₁(s) = c_lo s²`
(`isClassKInfinity_sq.const_mul`, item 1) squeezes `W → 0` into `x₁ → 0`.

Status: INTERFACED (given assumptions) — `hWc`/`hWderiv`/`hdi` name the storage's
flow realisation as a hypothesis, exactly as `Cascade.cascade_gas` takes its own
`hvc`/`hv`/`hdi`; discharging that bridge is `forced_rate_sqrt_comparison`'s named
open gap (see the module docstring), not derived here. -/
theorem tracking_cascade_gas
    (hclo : 0 < c_lo) (hchi : 0 < c_hi) (hκ : 0 < κ) (hcp : 0 < c')
    (hsand_lo : ∀ t ∈ Ici (0 : ℝ), c_lo * ‖x₁ t‖ ^ 2 ≤ W t)
    (hWc : ContinuousOn W (Ici 0))
    (hWderiv : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt W (W' t) (Ici t) t)
    (hdi : ∀ t ∈ Ici (0 : ℝ), W' t ≤ -(κ / c_hi) * W t + c' * ‖x₂ t‖ * Real.sqrt (W t))
    (hx2 : Tendsto x₂ atTop (𝓝 0)) :
    Tendsto x₁ atTop (𝓝 0) := by
  have hWnn : ∀ t ∈ Ici (0 : ℝ), 0 ≤ W t := fun t ht =>
    le_trans (mul_nonneg hclo.le (sq_nonneg _)) (hsand_lo t ht)
  have hdi0 : ∀ t ∈ Ici (0 : ℝ),
      W' t ≤ -(κ / c_hi) * W t + c' * (‖x₂ t‖ + 0) * Real.sqrt (W t) := by
    intro t ht; simpa using hdi t ht
  have hmaj := tracking_forced_rate_majorant (x₂ := x₂) (ρ := 0) hchi hκ hcp le_rfl hWnn hdi0
  have ha : (0 : ℝ) < κ / (2 * c_hi) := by positivity
  have heps : Tendsto (fun t => c' ^ 2 * c_hi / (2 * κ) * (‖x₂ t‖ + 0) ^ 2) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t => ‖x₂ t‖) atTop (𝓝 0) := by simpa using hx2.norm
    have h2 : Tendsto (fun t => (‖x₂ t‖ + 0) ^ 2) atTop (𝓝 0) := by
      have := h1.pow 2
      simpa using this
    simpa using h2.const_mul (c' ^ 2 * c_hi / (2 * κ))
  have hWzero : Tendsto W atTop (𝓝 0) :=
    comparison_tendsto_zero ha hWc hWderiv hmaj hWnn heps
  have hα : IsClassKInfinity (fun s : ℝ => c_lo * s ^ 2) := isClassKInfinity_sq.const_mul hclo
  have hsand' : ∀ᶠ t in atTop, (fun s : ℝ => c_lo * s ^ 2) ‖x₁ t‖ ≤ W t :=
    eventually_atTop.mpr ⟨0, fun t ht => hsand_lo t (mem_Ici.mpr ht)⟩
  exact hα.tendsto_zero_of_sandwich hsand' hWzero

/-- **Ultimate boundedness of the storage (`ρ ≥ 0`, general forcing ceiling).**
Mirrors `Cascade.cascade_bounded`: a uniform ceiling `‖x₂ t‖ ≤ Mx` on the CoM
coupling (not convergence) keeps `W` inside the Grönwall ultimate bound
`W 0 + M/a`, `a = κ/(2c_hi)`, `M = c'²c_hi/(2κ)(Mx+ρ)²`, via the Young majorant
above feeding `comparison_bounded`.

Note: `hWnn0 : 0 ≤ W 0` is implied by `hWnn` at `t = 0` (`hWnn 0 (left_mem_Ici)`);
it is kept as its own hypothesis only because `comparison_bounded`'s own signature
takes it separately — the statement above is not changed. -/
theorem tracking_cascade_storage_bounded
    (hchi : 0 < c_hi) (hκ : 0 < κ) (hcp : 0 < c') (hρ : 0 ≤ ρ)
    {Mx : ℝ} (hMx : 0 ≤ Mx)
    (hWnn0 : 0 ≤ W 0)
    (hWc : ContinuousOn W (Ici 0))
    (hWderiv : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt W (W' t) (Ici t) t)
    (hdi : ∀ t ∈ Ici (0 : ℝ), W' t ≤ -(κ / c_hi) * W t + c' * (‖x₂ t‖ + ρ) * Real.sqrt (W t))
    (hx2M : ∀ t ∈ Ici (0 : ℝ), ‖x₂ t‖ ≤ Mx)
    (hWnn : ∀ t ∈ Ici (0 : ℝ), 0 ≤ W t) :
    ∀ t ∈ Ici (0 : ℝ), W t ≤ W 0 + c' ^ 2 * c_hi / (2 * κ) * (Mx + ρ) ^ 2 / (κ / (2 * c_hi)) := by
  have hmaj := tracking_forced_rate_majorant (x₂ := x₂) (ρ := ρ) hchi hκ hcp hρ hWnn hdi
  have ha : (0 : ℝ) < κ / (2 * c_hi) := by positivity
  have hM : (0 : ℝ) ≤ c' ^ 2 * c_hi / (2 * κ) * (Mx + ρ) ^ 2 := by positivity
  have hεM : ∀ t ∈ Ici (0 : ℝ),
      c' ^ 2 * c_hi / (2 * κ) * (‖x₂ t‖ + ρ) ^ 2 ≤ c' ^ 2 * c_hi / (2 * κ) * (Mx + ρ) ^ 2 := by
    intro t ht
    have hnn2 : (0 : ℝ) ≤ ‖x₂ t‖ := norm_nonneg _
    have hle : ‖x₂ t‖ + ρ ≤ Mx + ρ := by linarith [hx2M t ht]
    have hle2 : (‖x₂ t‖ + ρ) ^ 2 ≤ (Mx + ρ) ^ 2 :=
      sq_le_sq' (by linarith) hle
    have hKnn : (0 : ℝ) ≤ c' ^ 2 * c_hi / (2 * κ) := by positivity
    exact mul_le_mul_of_nonneg_left hle2 hKnn
  exact comparison_bounded ha hM hWc hWderiv hmaj hεM hWnn0

/-- **Ultimate bound on the tracking error (`ρ ≥ 0`).** Corollary of
`tracking_cascade_storage_bounded` through the lower sandwich `c_lo‖x₁‖² ≤ W`:
`‖x₁ t‖` stays inside an explicit ultimate bound built from `W 0`, the CoM
coupling ceiling `Mx`, and the regularization floor `ρ` — the report's asserted
"limsup‖x₁‖ ≤ C·ρ" ultimate bound, delivered here as the honest uniform-in-`t`
bound `comparison_bounded` actually proves. The sharper eventual floor, dropping
the `W 0` transient, is now provided separately by `tracking_norm_eventual_floor`
in `TrackingUltimateBound`; the present theorem retains its all-time bound. -/
theorem tracking_cascade_bounded
    (hclo : 0 < c_lo) (hchi : 0 < c_hi) (hκ : 0 < κ) (hcp : 0 < c') (hρ : 0 ≤ ρ)
    {Mx : ℝ} (hMx : 0 ≤ Mx)
    (hsand_lo : ∀ t ∈ Ici (0 : ℝ), c_lo * ‖x₁ t‖ ^ 2 ≤ W t)
    (hWnn0 : 0 ≤ W 0)
    (hWc : ContinuousOn W (Ici 0))
    (hWderiv : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt W (W' t) (Ici t) t)
    (hdi : ∀ t ∈ Ici (0 : ℝ), W' t ≤ -(κ / c_hi) * W t + c' * (‖x₂ t‖ + ρ) * Real.sqrt (W t))
    (hx2M : ∀ t ∈ Ici (0 : ℝ), ‖x₂ t‖ ≤ Mx) :
    ∀ t ∈ Ici (0 : ℝ), ‖x₁ t‖ ≤
      Real.sqrt ((W 0 + c' ^ 2 * c_hi / (2 * κ) * (Mx + ρ) ^ 2 / (κ / (2 * c_hi))) / c_lo) := by
  have hWnn : ∀ t ∈ Ici (0 : ℝ), 0 ≤ W t := fun t ht =>
    le_trans (mul_nonneg hclo.le (sq_nonneg _)) (hsand_lo t ht)
  have hWbdd := tracking_cascade_storage_bounded hchi hκ hcp hρ hMx hWnn0 hWc hWderiv hdi hx2M hWnn
  intro t ht
  have h1 : c_lo * ‖x₁ t‖ ^ 2
      ≤ W 0 + c' ^ 2 * c_hi / (2 * κ) * (Mx + ρ) ^ 2 / (κ / (2 * c_hi)) :=
    le_trans (hsand_lo t ht) (hWbdd t ht)
  have hclone : c_lo ≠ 0 := hclo.ne'
  have h2 : ‖x₁ t‖ ^ 2 ≤
      (W 0 + c' ^ 2 * c_hi / (2 * κ) * (Mx + ρ) ^ 2 / (κ / (2 * c_hi))) / c_lo := by
    rw [le_div_iff₀ hclo]; linarith [h1]
  have h3 : ‖x₁ t‖ = Real.sqrt (‖x₁ t‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
  rw [h3]
  exact Real.sqrt_le_sqrt h2

end Engine

/-! ### The instantiation against the sealed CoM-loop GAS -/

section Instantiation

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {E₁ : Type*} [NormedAddCommGroup E₁] {x₁ : ℝ → E₁} {W W' : ℝ → ℝ}
  {c_lo c_hi κ c' : ℝ}

/-- **THE INSTANTIATION** — mirrors `Cascade.propIV1_cascade_gas`. The sealed
`com_gas_matrix` (concrete SPD CoM loop, GAS) discharges `tracking_cascade_gas`'s
driving subsystem `x₂ = ϕc·z₀ → 0`; the DRIVEN subsystem is the tracking-error
state `x₁`, entering through the same named cascade interface (storage sandwich,
forced rate bound). -/
theorem tracking_cascade_gas_com
    (hclo : 0 < c_lo) (hchi : 0 < c_hi) (hκ : 0 < κ) (hcp : 0 < c')
    (hsand_lo : ∀ t ∈ Ici (0 : ℝ), c_lo * ‖x₁ t‖ ^ 2 ≤ W t)
    (hWc : ContinuousOn W (Ici 0))
    (hWderiv : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt W (W' t) (Ici t) t)
    -- driving subsystem: the CoM loop, with the sealed `com_gas_matrix` hypotheses
    (Mm Dm Km : Matrix n n ℝ) (hM : Mm.PosDef) (hD : Dm.PosDef) (hK : Km.PosDef)
    (ϕc : Flow ℝ (ComState (EuclideanSpace ℝ n)))
    (hϕc : IsSolutionTo ϕc (comField (toEuclideanCLM (𝕜 := ℝ) Dm)
      (toEuclideanCLM (𝕜 := ℝ) Km) (toEuclideanCLM (𝕜 := ℝ) Mm⁻¹)))
    (z₀ : ComState (EuclideanSpace ℝ n)) (hcptc : ForwardPrecompact ϕc z₀)
    (hdi : ∀ t ∈ Ici (0 : ℝ),
      W' t ≤ -(κ / c_hi) * W t + c' * ‖ϕc t z₀‖ * Real.sqrt (W t)) :
    Tendsto x₁ atTop (𝓝 0) :=
  tracking_cascade_gas hclo hchi hκ hcp hsand_lo hWc hWderiv hdi
    (com_gas_matrix Mm Dm Km hM hD hK ϕc hϕc z₀ hcptc)

end Instantiation

end Ctrllib

#print axioms Ctrllib.tracking_forced_rate_majorant
#print axioms Ctrllib.tracking_cascade_gas
#print axioms Ctrllib.tracking_cascade_storage_bounded
#print axioms Ctrllib.tracking_cascade_bounded
#print axioms Ctrllib.tracking_cascade_gas_com
