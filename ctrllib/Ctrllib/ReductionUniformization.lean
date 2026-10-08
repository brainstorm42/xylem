/-
R6 — EHM-2009 Lemma 2.5, converse direction: the uniform semi-attractor from
relative asymptotic stability. Discharges `hUSA`, the one external core left
under the R5 seals.

EHM-2009 (arXiv:0907.0686) Lemma 2.5 (p. 5, §2.3) states that for closed
positively invariant Γ ⊂ U, semi-asymptotic stability relative to U implies
(under local uniform boundedness) that Γ is a uniform semi-attractor relative
to U — the property (A.1)/eq. (18) consumed by the EHM-2013 Theorem-6 finish.
The Lean target `UniformSemiAttractorRelativeTo` (ReductionStabilityFinish) is
a quantifier-for-quantifier transcription of eq. (18), so no adapter is needed
(recon the corresponding local note §4).

ROUTE DEVIATION (user-decided 2026-07-10, recorded loudly): the paper's own
Appendix-A proof of this direction runs through prolongational limit sets
J⁺ (Ura) with two steps cited to Bhatia–Szegö 1970; Mathlib has none of that
machinery. THIS module proves the identical conclusion in our setting (proper
space, tube-form predicates) by the classical compactness-and-finite-subcover
argument. The compact-case bridge is the paper's own p. 4 Remark: for compact
sets, uniform semi-attractivity coincides with the uniform attractivity of
Lin–Sontag–Wang 1996 (their [33]). Consequences of the route: neither
`LUBNear` nor compactness of `Γ₁` nor `Γ₁.Nonempty` is consumed here — only
`ProperSpace` (from `[FiniteDimensional ℝ E]`), `Γ₂` closed + forward
invariant, and the two halves of relative asymptotic stability in their
existing tube forms.

  R6-a `exists_captureTime_ball` — the per-point brick: an orbit drawn to Γ₁
    admits a strictly positive capture time T and a ball of initial points
    all landing strictly inside the δ-tube at time T (flow continuity at a
    fixed time).
  R6-b `uniformSemiAttractor_of_asymStableRelativeTo` — the uniformization:
    finite subcover of the compact slab B̄_{δa/2}(x) ∩ Γ₂ by capture balls,
    Finset-max time, semigroup tail through relative stability.
  R6-c `reduction_asymptotic_stability_of_asymStableRelativeTo` — the rewire:
    T8-D's `hUSA` discharged by R6-b; the trust boundary of the reduction
    theorem is now EHM Theorem-6/8 standing conditions alone. L-C and T8-D
    are consumed, not edited.

Human derivation:
the corresponding derivation record (not bundled).
-/
import Ctrllib.ReductionAttraction

open Set Filter Topology

namespace Ctrllib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- **R6-a** — capture time + capture ball: if the forward orbit of `y` is
drawn to `Γ₁` (point-to-set distance → 0), then for any `δs > 0` there are a
strictly positive time `T` and a radius `r > 0` such that EVERY initial point
`z` within `r` of `y` sits strictly inside the `δs`-tube of `Γ₁` at time `T`.
Pure Mathlib: pick `T` on the eventual tail of the tendsto, then the time-`T`
tube function `z ↦ infDist (ϕ T z) Γ₁` is continuous (`Flow.continuous_toFun`),
so its open `δs`-sublevel set contains a ball around `y`. Metric-only. -/
theorem exists_captureTime_ball (ϕ : Flow ℝ E) {Γ₁ : Set E} {y : E}
    (hy : Tendsto (fun t : ℝ => Metric.infDist (ϕ t y) Γ₁) atTop (𝓝 0))
    {δs : ℝ} (hδs : 0 < δs) :
    ∃ T > 0, ∃ r > 0, ∀ z, dist z y < r → Metric.infDist (ϕ T z) Γ₁ < δs := by
  -- a strictly positive time with the orbit of y strictly inside the δs-tube
  obtain ⟨T, hT0, hTd⟩ :=
    ((eventually_gt_atTop (0 : ℝ)).and (hy.eventually_lt_const hδs)).exists
  -- the time-T tube function is continuous, so its δs-sublevel set is open
  have hg : Continuous fun z => Metric.infDist (ϕ T z) Γ₁ :=
    (Metric.continuous_infDist_pt Γ₁).comp (ϕ.continuous_toFun T)
  obtain ⟨r, hr, hball⟩ :=
    Metric.isOpen_iff.mp (isOpen_lt hg continuous_const) y hTd
  exact ⟨T, hT0, r, hr, fun z hz => hball (Metric.mem_ball.mpr hz)⟩

/-- **R6-b** — the uniformization (EHM-2009 Lemma 2.5, converse direction,
compact/proper-branch direct proof): relative asymptotic stability of `Γ₁`
with respect to a closed, forward-invariant `Γ₂ ⊇ Γ₁` yields the uniform
semi-attractor property. Fix `x ∈ Γ₁` and take `μ := δa/2` (half the tube
radius of `hAttrRel`); the slab `B̄_μ(x) ∩ Γ₂` is compact (`ProperSpace` from
`[FiniteDimensional ℝ E]`), every slab point is in the attraction basin, R6-a
gives each a capture ball, `IsCompact.elim_nhds_subcover` extracts finitely
many, and `T := 1 + max` of their capture times works: any admissible `y` is
captured by some ball at its time `T w` into the `δs`-tube (`δs` = the
relative-stability radius at level `ε'`), lands in `Γ₂` by forward invariance,
and relative stability holds the remaining tail `t − T w ≥ 0` inside the
`ε'`-tube. -/
theorem uniformSemiAttractor_of_asymStableRelativeTo
    [FiniteDimensional ℝ E] (ϕ : Flow ℝ E) {Γ₁ Γ₂ : Set E}
    (hΓ₂closed : IsClosed Γ₂) (hsub : Γ₁ ⊆ Γ₂)
    (hpi₂ : IsForwardInvariant ϕ.toFun Γ₂)
    (hStabRel : StableRelativeTo ϕ Γ₁ Γ₂)
    (hAttrRel : AttractiveRelativeTo ϕ Γ₁ Γ₂) :
    UniformSemiAttractorRelativeTo ϕ Γ₁ Γ₂ := by
  intro x hxΓ₁
  obtain ⟨δa, hδa, hattr⟩ := hAttrRel
  refine ⟨δa / 2, half_pos hδa, fun ε' hε' => ?_⟩
  -- the relative-stability tube δs at level ε'
  obtain ⟨δs, hδs, hstab⟩ := hStabRel ε' hε'
  -- the compact slab of admissible initial points
  have hKcpt : IsCompact (Metric.closedBall x (δa / 2) ∩ Γ₂) :=
    (isCompact_closedBall x (δa / 2)).inter_right hΓ₂closed
  -- every slab point sits inside the attraction tube: orbit-distance → 0
  have hbasin : ∀ y ∈ Metric.closedBall x (δa / 2) ∩ Γ₂,
      Tendsto (fun t : ℝ => Metric.infDist (ϕ t y) Γ₁) atTop (𝓝 0) := by
    rintro y ⟨hyball, hyΓ₂⟩
    refine hattr y hyΓ₂ ?_
    calc Metric.infDist y Γ₁ ≤ dist y x := Metric.infDist_le_dist_of_mem hxΓ₁
      _ ≤ δa / 2 := Metric.mem_closedBall.mp hyball
      _ < δa := by linarith
  -- R6-a at every slab point: a capture time and a capture ball
  have hkey : ∀ y ∈ Metric.closedBall x (δa / 2) ∩ Γ₂,
      ∃ T > 0, ∃ r > 0, ∀ z, dist z y < r → Metric.infDist (ϕ T z) Γ₁ < δs :=
    fun y hy => exists_captureTime_ball ϕ (hbasin y hy) hδs
  choose! T hTpos r hrpos hcap using hkey
  -- finite subcover of the slab by capture balls
  obtain ⟨s, hsK, hcov⟩ := hKcpt.elim_nhds_subcover (fun y => Metric.ball y (r y))
    (fun y hy => Metric.ball_mem_nhds y (hrpos y hy))
  -- x itself lies in the slab, so the subcover is nonempty
  have hxK : x ∈ Metric.closedBall x (δa / 2) ∩ Γ₂ :=
    ⟨Metric.mem_closedBall_self (by positivity), hsub hxΓ₁⟩
  have hsne : s.Nonempty := by
    obtain ⟨w, hws, -⟩ := mem_iUnion₂.mp (hcov hxK)
    exact ⟨w, hws⟩
  -- the uniform time: one past the finite max of the capture times
  refine ⟨1 + s.sup' hsne T, ?_, fun y hyx hyΓ₂ t ht => ?_⟩
  · obtain ⟨w, hws⟩ := hsne
    have h0 := hTpos w (hsK w hws)
    have hle := Finset.le_sup' T hws
    linarith
  · -- route y into a covering capture ball
    have hyK : y ∈ Metric.closedBall x (δa / 2) ∩ Γ₂ :=
      ⟨Metric.mem_closedBall.mpr hyx.le, hyΓ₂⟩
    obtain ⟨w, hws, hyw⟩ := mem_iUnion₂.mp (hcov hyK)
    rw [Metric.mem_ball] at hyw
    have hwK := hsK w hws
    -- capture: at time T w the point is strictly inside the δs-tube, still in Γ₂
    have hcapture : Metric.infDist (ϕ (T w) y) Γ₁ < δs := hcap w hwK y hyw
    have hmemΓ₂ : ϕ (T w) y ∈ Γ₂ := hpi₂ (hTpos w hwK).le hyΓ₂
    -- semigroup tail: rewrite ϕ t y over the capture point, t − T w ≥ 0
    have htail : 0 ≤ t - T w := by
      have hle := Finset.le_sup' T hws
      linarith
    have hflow : ϕ t y = ϕ (t - T w) (ϕ (T w) y) := by
      have harg : t - T w + T w = t := by ring
      calc ϕ t y = ϕ (t - T w + T w) y := by rw [harg]
        _ = ϕ (t - T w) (ϕ (T w) y) := ϕ.map_add (t - T w) (T w) y
    rw [hflow]
    exact hstab (ϕ (T w) y) hmemΓ₂ hcapture (t - T w) htail

/-- **R6-c** — the rung-closing rewire: EHM-2013 Theorem 10 (compact branch)
with the last external core discharged. T8-D's `hUSA` is instantiated by R6-b
applied to the Theorem-6/8 primitives already in T8-D's signature, plus the
one newly threaded primitive `hpi₂` (forward invariance of `Γ₂` — paper-
faithful: EHM's standing setup is two closed positively invariant sets).
Neither L-C nor T8-D is edited; relative to a given `Flow ℝ E` the reduction
theorem's trust boundary is EHM standing conditions alone. What remains
interfaced is the flow itself: `Flow ℝ E` is a two-sided group action (all
`t : ℝ`), and the chain uses negative times essentially
(`ReductionAttraction.omegaLimit_subset_of_stableRelativeTo`, the backward
sequence in the ω-limit set); existence of such a flow for the closed-loop
field is the open `IsSolutionTo` row of the corresponding local note. -/
theorem reduction_asymptotic_stability_of_asymStableRelativeTo
    [FiniteDimensional ℝ E] (ϕ : Flow ℝ E) {Γ₁ Γ₂ : Set E}
    (hΓ₁cpt : IsCompact Γ₁) (hΓ₁ne : Γ₁.Nonempty)
    (hΓ₂closed : IsClosed Γ₂) (hsub : Γ₁ ⊆ Γ₂)
    (hfi : IsForwardInvariant ϕ.toFun Γ₁)
    (hpi₂ : IsForwardInvariant ϕ.toFun Γ₂)
    (hLUB : LUBNear ϕ Γ₁)
    (hLSN : LocallyStableNear ϕ Γ₂ Γ₁)
    (hStabRel : StableRelativeTo ϕ Γ₁ Γ₂)
    (hAttrRel : AttractiveRelativeTo ϕ Γ₁ Γ₂)
    (hLAN : LocallyAttractiveNear ϕ Γ₂ Γ₁) :
    AsymStableSet ϕ Γ₁ :=
  reduction_asymptotic_stability_of_uniformSemiAttractor ϕ hΓ₁cpt hΓ₁ne hΓ₂closed
    hsub hfi hLUB hLSN hStabRel hAttrRel hLAN
    (uniformSemiAttractor_of_asymStableRelativeTo ϕ hΓ₂closed hsub hpi₂
      hStabRel hAttrRel)

end Ctrllib

#print axioms Ctrllib.exists_captureTime_ball
#print axioms Ctrllib.uniformSemiAttractor_of_asymStableRelativeTo
#print axioms Ctrllib.reduction_asymptotic_stability_of_asymStableRelativeTo
