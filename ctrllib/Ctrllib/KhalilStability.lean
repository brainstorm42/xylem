/-
Khalil's Lyapunov direct method for autonomous systems (R3, Lane A).

Khalil, *Nonlinear Systems*, 3rd ed. (2002):
- Theorem 4.1 (Lyapunov stability + asymptotic upgrade), render 3606–3622.
- Theorem 4.2 (Barbashin–Krasovskii, global asymptotic stability), render 3920–3931.

Mathlib has no Lyapunov stability layer (verified absent 2026-07-04). This file
states the classical ε–δ theorem and its asymptotic / global upgrades as concrete
targets, all riding the sealed `IsSolutionTo` interface (LaSalle.lean:55) — the
flow is given, no ODE existence is developed here. The point-stability predicates
`LyapStable` / `AsympStable` are new to the library and disjoint from EHM's
set-relative `StableSet` (Reduction.lean); no collision.

Domain is global (`D = E`), matching the autonomous flow.

Reuses (all sealed):
- `IsSolutionTo.hasDerivAt_comp` + `antitone_of_deriv_nonpos` (the `lasalle` engine),
- `forwardPrecompact_of_isBounded`, `lasalle`, `eventually_mem_of_omegaLimit_subset`.
-/
import Ctrllib.LaSalle
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact

open Set Filter Topology omegaLimit

namespace Ctrllib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Lyapunov stability of the origin for a flow: ε–δ, forward time.
Khalil (2002) Def 4.1 / Theorem 4.1 conclusion. -/
def LyapStable (ϕ : Flow ℝ E) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, ‖x‖ < δ → ∀ t : ℝ, 0 ≤ t → ‖ϕ t x‖ < ε

/-- Local asymptotic stability: stable and locally attractive.
Khalil (2002) Theorem 4.1 (asymptotic half). -/
def AsympStable (ϕ : Flow ℝ E) : Prop :=
  LyapStable ϕ ∧ ∃ δ > 0, ∀ x, ‖x‖ < δ → Tendsto (fun t => ϕ t x) atTop (𝓝 0)

/-- **Khalil (2002), Theorem 4.1 (stability half).** Let `V` be continuously
differentiable, positive definite (`V 0 = 0`, `V x > 0` for `x ≠ 0`), with
`V̇ ≤ 0` along the field. Then the origin is Lyapunov stable.

The classic sublevel-set trapping argument: for `ε`, the sphere `‖·‖ = ε` is
compact (finite dim), `α = min V > 0` is attained there; pick `β = α/2`, and the
open neighbourhood `{V < β} ∩ B_ε` contains a ball `B_δ`. An orbit starting in
`B_δ` cannot reach the sphere (there `V ≥ α > β`, but `V` is nonincreasing along
orbits and started below `β`), so by the intermediate value theorem it never
leaves `B_ε`. -/
theorem lyapunov_stable [FiniteDimensional ℝ E] (ϕ : Flow ℝ E) {f : E → E}
    (hϕ : IsSolutionTo ϕ f) {V : E → ℝ} (hVdiff : Differentiable ℝ V)
    (hV0 : V 0 = 0) (hVpos : ∀ x, x ≠ 0 → 0 < V x)
    (hdec : ∀ y, fderiv ℝ V y (f y) ≤ 0) :
    LyapStable ϕ := by
  obtain hsub | hnon := subsingleton_or_nontrivial E
  · -- Trivial state space: every point is `0`.
    intro ε hε
    exact ⟨1, one_pos, fun x _ t _ => by
      rw [Subsingleton.elim (ϕ t x) 0, norm_zero]; exact hε⟩
  · intro ε hε
    -- Minimum of `V` over the compact sphere `‖·‖ = ε`.
    have hcompact : IsCompact (Metric.sphere (0 : E) ε) := isCompact_sphere 0 ε
    have hsne : (Metric.sphere (0 : E) ε).Nonempty := NormedSpace.sphere_nonempty.mpr hε.le
    obtain ⟨xm, hxm_mem, hxm_min⟩ :=
      hcompact.exists_isMinOn hsne hVdiff.continuous.continuousOn
    have hxm_ne : xm ≠ 0 := by
      intro h
      rw [Metric.mem_sphere, dist_zero_right, h, norm_zero] at hxm_mem
      exact (ne_of_gt hε) hxm_mem.symm
    have hαpos : 0 < V xm := hVpos xm hxm_ne
    -- Threshold `β = α/2`, strictly between `0` and the sphere-minimum.
    set β := V xm / 2 with hβ
    have hβpos : 0 < β := by rw [hβ]; linarith
    have hβα : β < V xm := by rw [hβ]; linarith
    -- Open neighbourhood of `0` inside `{V < β} ∩ B_ε`, and a ball `B_δ` within it.
    have hU : IsOpen (V ⁻¹' Set.Iio β ∩ Metric.ball (0 : E) ε) :=
      (isOpen_Iio.preimage hVdiff.continuous).inter Metric.isOpen_ball
    have h0mem : (0 : E) ∈ V ⁻¹' Set.Iio β ∩ Metric.ball (0 : E) ε :=
      ⟨by rw [Set.mem_preimage, Set.mem_Iio, hV0]; exact hβpos,
       by rw [Metric.mem_ball, dist_zero_right, norm_zero]; exact hε⟩
    obtain ⟨δ, hδpos, hδsub⟩ := Metric.isOpen_iff.mp hU 0 h0mem
    refine ⟨δ, hδpos, fun x hx t ht => ?_⟩
    have hxball : x ∈ Metric.ball (0 : E) δ := by
      rw [Metric.mem_ball, dist_zero_right]; exact hx
    have hxU := hδsub hxball
    have hVxβ : V x < β := hxU.1
    have hxε : ‖x‖ < ε := by
      have := Metric.mem_ball.mp hxU.2; rwa [dist_zero_right] at this
    -- The orbit is continuous, and `V` is nonincreasing along it.
    have horbit_cont : Continuous (fun s => ϕ s x) :=
      continuous_iff_continuousAt.mpr (fun s => (hϕ x s).continuousAt)
    have hg_diff : Differentiable ℝ (fun s : ℝ => V (ϕ s x)) := fun s =>
      (hϕ.hasDerivAt_comp hVdiff x s).differentiableAt
    have hg_deriv : ∀ s : ℝ, deriv (fun s : ℝ => V (ϕ s x)) s ≤ 0 := fun s => by
      rw [(hϕ.hasDerivAt_comp hVdiff x s).deriv]; exact hdec _
    have hanti : Antitone (fun s : ℝ => V (ϕ s x)) :=
      antitone_of_deriv_nonpos hg_diff hg_deriv
    -- Suppose the orbit reaches the sphere; derive a contradiction via IVT.
    by_contra hcon
    rw [not_lt] at hcon
    have hgcont : ContinuousOn (fun s => ‖ϕ s x‖) (Set.Icc 0 t) :=
      (continuous_norm.comp horbit_cont).continuousOn
    have hg0 : ‖ϕ (0 : ℝ) x‖ = ‖x‖ := by rw [ϕ.map_zero_apply]
    have hmem : ε ∈ Set.Icc (‖ϕ (0 : ℝ) x‖) (‖ϕ t x‖) := by
      rw [hg0]; exact ⟨hxε.le, hcon⟩
    obtain ⟨s, hs_mem, hgs⟩ := intermediate_value_Icc ht hgcont hmem
    have hsphere : ϕ s x ∈ Metric.sphere (0 : E) ε := by
      rw [Metric.mem_sphere, dist_zero_right]; exact hgs
    have h1 : V xm ≤ V (ϕ s x) := isMinOn_iff.mp hxm_min _ hsphere
    have h2 : V (ϕ s x) ≤ V x := by
      simpa only [ϕ.map_zero_apply] using hanti hs_mem.1
    linarith

/-- **Khalil (2002), Theorem 4.1 (asymptotic half).** With the strict decrease
`V̇ < 0` off the origin (and `f 0 = 0`), the origin is asymptotically stable.

Stability is `lyapunov_stable` (strict decrease ⟹ nonstrict). Attraction: near
`0` the forward orbit is trapped in a bounded sublevel set (from the stability
proof at radius `1`), hence forward-precompact in finite dim; `lasalle` yields a
nonempty invariant ω-limit set on which `V̇ = 0`; strict decrease forces that set
to `{0}`; `eventually_mem_of_omegaLimit_subset` into shrinking balls upgrades to
convergence. -/
theorem lyapunov_asymptotically_stable [FiniteDimensional ℝ E] (ϕ : Flow ℝ E)
    {f : E → E} (hϕ : IsSolutionTo ϕ f) {V : E → ℝ} (hVdiff : Differentiable ℝ V)
    (hV0 : V 0 = 0) (hVpos : ∀ x, x ≠ 0 → 0 < V x) (hf0 : f 0 = 0)
    (hdecStrict : ∀ y, y ≠ 0 → fderiv ℝ V y (f y) < 0) :
    AsympStable ϕ := by
  -- Nonstrict decrease everywhere (at `0`, `f 0 = 0` gives `V̇ 0 = 0`).
  have hdec : ∀ y, fderiv ℝ V y (f y) ≤ 0 := by
    intro y
    rcases eq_or_ne y 0 with rfl | hy
    · simp [hf0]
    · exact (hdecStrict y hy).le
  have hstab : LyapStable ϕ := lyapunov_stable ϕ hϕ hVdiff hV0 hVpos hdec
  refine ⟨hstab, ?_⟩
  -- A radius-`1` trap gives a bounded forward orbit near `0`.
  obtain ⟨δ, hδpos, htrap⟩ := hstab 1 one_pos
  refine ⟨δ, hδpos, fun x hx => ?_⟩
  have hbdd : Bornology.IsBounded ((fun t : ℝ => ϕ t x) '' Set.Ici 0) := by
    apply (Metric.isBounded_ball (x := (0 : E)) (r := 1)).subset
    rintro _ ⟨t, ht, rfl⟩
    rw [Metric.mem_ball, dist_zero_right]
    exact htrap x hx t ht
  have hcpt : ForwardPrecompact ϕ x := forwardPrecompact_of_isBounded ϕ x hbdd
  obtain ⟨_hne, _hinv, _hconst, hderiv0⟩ := lasalle ϕ hϕ hVdiff hdec x hcpt
  -- The ω-limit set is `{0}`: strict decrease contradicts `V̇ = 0` off the origin.
  have hsub0 : ω⁺ ϕ.toFun {x} ⊆ {0} := by
    intro y hy
    rw [Set.mem_singleton_iff]
    by_contra hy0
    exact absurd (hderiv0 y hy) (ne_of_lt (hdecStrict y hy0))
  -- Enter every ball `B_ε`, i.e. converge to `0`.
  refine Metric.tendsto_atTop.mpr (fun ε hε => ?_)
  have h0inball : ω⁺ ϕ.toFun {x} ⊆ Metric.ball (0 : E) ε := by
    refine hsub0.trans ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy; subst hy
    rw [Metric.mem_ball, dist_self]; exact hε
  have hev := eventually_mem_of_omegaLimit_subset ϕ x hcpt Metric.isOpen_ball h0inball
  rw [eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  exact ⟨N, fun n hn => by have := hN n hn; rwa [Metric.mem_ball] at this⟩

omit [NormedSpace ℝ E] in
/-- Radial unboundedness (`V → ∞` along the cobounded filter) makes every
sublevel set `{V ≤ c}` bounded. This is the contrapositive of
`cobounded → atTop`: on the cobounded filter `V > c` eventually, so `{V ≤ c}`
is the complement of a cobounded-member set, hence bounded. -/
theorem sublevel_isBounded_of_tendsto_cobounded {V : E → ℝ}
    (hV : Tendsto V (Bornology.cobounded E) atTop) (c : ℝ) :
    Bornology.IsBounded {y : E | V y ≤ c} := by
  rw [Bornology.isBounded_def]
  have hev : ∀ᶠ y in Bornology.cobounded E, c < V y :=
    hV.eventually (eventually_gt_atTop c)
  have hset : {y : E | V y ≤ c}ᶜ = {y | c < V y} := by
    ext y; simp [not_le]
  rw [hset]; exact hev

/-- **Khalil (2002), Theorem 4.2 (Barbashin–Krasovskii).** With `V` radially
unbounded (`V → ∞` as `‖x‖ → ∞`) in addition to the asymptotic-stability
hypotheses, the origin is globally asymptotically stable: Lyapunov stable, and
*every* orbit converges to `0`.

Radial unboundedness makes the sublevel `{V ≤ V x}` bounded, so *every* forward
orbit (confined there by the nonincreasing `V`) is forward-precompact; the T2
argument then runs from any `x`. -/
theorem lyapunov_globally_asymptotically_stable [FiniteDimensional ℝ E]
    (ϕ : Flow ℝ E) {f : E → E} (hϕ : IsSolutionTo ϕ f)
    {V : E → ℝ} (hVdiff : Differentiable ℝ V) (hV0 : V 0 = 0)
    (hVpos : ∀ x, x ≠ 0 → 0 < V x) (hf0 : f 0 = 0)
    (hRadUnbdd : Tendsto V (Bornology.cobounded E) atTop)
    (hdecStrict : ∀ y, y ≠ 0 → fderiv ℝ V y (f y) < 0) :
    LyapStable ϕ ∧ ∀ x, Tendsto (fun t => ϕ t x) atTop (𝓝 0) := by
  have hdec : ∀ y, fderiv ℝ V y (f y) ≤ 0 := by
    intro y
    rcases eq_or_ne y 0 with rfl | hy
    · simp [hf0]
    · exact (hdecStrict y hy).le
  have hstab : LyapStable ϕ := lyapunov_stable ϕ hϕ hVdiff hV0 hVpos hdec
  refine ⟨hstab, fun x => ?_⟩
  -- `V` is nonincreasing along the orbit; the forward orbit lies in `{V ≤ V x}`.
  have hg_diff : Differentiable ℝ (fun s : ℝ => V (ϕ s x)) := fun s =>
    (hϕ.hasDerivAt_comp hVdiff x s).differentiableAt
  have hg_deriv : ∀ s : ℝ, deriv (fun s : ℝ => V (ϕ s x)) s ≤ 0 := fun s => by
    rw [(hϕ.hasDerivAt_comp hVdiff x s).deriv]; exact hdec _
  have hanti : Antitone (fun s : ℝ => V (ϕ s x)) :=
    antitone_of_deriv_nonpos hg_diff hg_deriv
  have hsublevel : Bornology.IsBounded {y : E | V y ≤ V x} :=
    sublevel_isBounded_of_tendsto_cobounded hRadUnbdd (V x)
  have hbdd : Bornology.IsBounded ((fun t : ℝ => ϕ t x) '' Set.Ici 0) := by
    apply hsublevel.subset
    rintro _ ⟨t, ht, rfl⟩
    simpa only [Set.mem_setOf_eq, ϕ.map_zero_apply] using hanti (mem_Ici.mp ht)
  have hcpt : ForwardPrecompact ϕ x := forwardPrecompact_of_isBounded ϕ x hbdd
  obtain ⟨_hne, _hinv, _hconst, hderiv0⟩ := lasalle ϕ hϕ hVdiff hdec x hcpt
  have hsub0 : ω⁺ ϕ.toFun {x} ⊆ {0} := by
    intro y hy
    rw [Set.mem_singleton_iff]
    by_contra hy0
    exact absurd (hderiv0 y hy) (ne_of_lt (hdecStrict y hy0))
  refine Metric.tendsto_atTop.mpr (fun ε hε => ?_)
  have h0inball : ω⁺ ϕ.toFun {x} ⊆ Metric.ball (0 : E) ε := by
    refine hsub0.trans ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy; subst hy
    rw [Metric.mem_ball, dist_self]; exact hε
  have hev := eventually_mem_of_omegaLimit_subset ϕ x hcpt Metric.isOpen_ball h0inball
  rw [eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  exact ⟨N, fun n hn => by have := hN n hn; rwa [Metric.mem_ball] at this⟩

end Ctrllib

#print axioms Ctrllib.lyapunov_stable
#print axioms Ctrllib.lyapunov_asymptotically_stable
#print axioms Ctrllib.sublevel_isBounded_of_tendsto_cobounded
#print axioms Ctrllib.lyapunov_globally_asymptotically_stable
