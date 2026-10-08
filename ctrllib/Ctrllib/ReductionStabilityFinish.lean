/-
R5 L-C — EHM-2013 Theorem-6 *finish*: `StableSet ϕ Γ₁` from the uniform
semi-attractor, interface-cut at the EHM-2009 Lemma-2.5 boundary.

This module discharges the `hStable : StableSet ϕ Γ₁` hypothesis of L4a
(`Ctrllib.Reduction.reduction_asymptotic_stability`) down to graded interfaces.
EHM-2013 Theorem 6 (set stability, compact-`Γ₁` branch) is proved by
contradiction: assuming `Γ₁` unstable, Lemma 22 extracts a bounded escape
sequence (our sealed `escape_sequence_of_not_stableSet` = L-A, refined to
first-exit form; `exists_subseq_tendsto_mem_of_infDist_tendsto_zero` = L-B
gives the `Γ₁`-limit), and the finish (corpus
the corresponding local note) drives these into a contradiction via a
µ-tube compactness argument.

The finish invokes, at `:1347`, "Lemma 2.5 in El-Hawwary & Maggiore (2009)"
(arXiv:0907.0686, Def 2.1(iv) + Appendix A) to obtain a UNIFORM SEMI-ATTRACTOR
relative to `Γ₂`. That bridge — attractivity ⟹ stability — is a rung-sized
external theorem; per the charter's honest-boundary discipline and the L3/L4a
`IsSolutionTo` interface precedent, L-C takes its output `hUSA` as a NAMED
hypothesis and seals the surrounding topology.

Graded interfaces of the core theorem `stableSet_of_uniformSemiAttractor`,
and their fate (both flow-side interfaces were DISCHARGED in-module the same
day, by the tightening theorems below the core):

  `hUSA`       — the Lemma-2.5 output (EHM-2009 Def 2.1(iv), relative form).
                 STILL OPEN — the one genuine external core. Discharging it =
                 formalizing EHM-2009 Appendix A (R6; route decided:
                 compact-branch direct). EHM-2013's assumptions (i) `hAttr`
                 and the closedness of `Γ₂` are consumed THERE, so they do
                 not appear below.
  `hFirstExit` — the Lemma-22 escape sequence in first-exit form, one exit-time
                 family per level `ε ≤ ε₀` for a SINGLE base sequence (paper
                 footnote 3, `:1396-1398`, needs level-shrinking below µ with
                 the base points — hence `x̄` — unchanged). DISCHARGED by
                 `firstExit_of_not_stableSet` (from L-A via
                 `exists_firstExitTime` + `exists_uniform_tube_radius`);
                 positive invariance `hfi` is consumed exactly there
                 (Lemma 22, `:1303` + the unbounded-times claim `:1421`).
  `hContDep`   — continuous dependence at a fixed time on a ball (`:1447`).
                 DISCHARGED by `contDep_of_flow` (Heine–Cantor on the compact
                 closed ball, from the flow's per-time continuity).

The public assembly `stableSet_of_uniformSemiAttractor_of_forwardInvariant`
composes the core with both discharges: its only interface hypothesis is
`hUSA`; everything else in its signature is a standing condition of EHM
Theorem 6 itself (compact branch).

What IS sealed here, beyond the assembly: the ball-nesting brick (`:1382-1408`),
the uniform-basin extraction (A.2)+(A.3) (`:1352-1381`,
`IsCompact.elim_nhds_subcover` + finite min/max), and the
segment-approaches-`Γ₂` step (`:1325-1343`) — the latter derived INLINE from
`hLSN` + `hLUB` (the source derives it from local stability (ii) + local
uniform boundedness; no flow regularity needed, so no interface).

Trust-boundary shrink: `reduction_asymptotic_stability`'s `hStable` (all of
Theorem 6) → `hUSA` alone.

Recon: the corresponding local note §3-§5. Charter: the corresponding local note
Human derivation for THIS module:
the corresponding derivation record (not bundled).
-/
import Ctrllib.ReductionStability
import Mathlib.Data.Finset.Lattice.Fold

open Set Filter Topology

namespace Ctrllib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## The interface core — EHM-2009 Lemma 2.5 output

`Γ₁` is a *uniform semi-attractor relative to* `Γ₂` (EHM-2009 arXiv:0907.0686
Def 2.1(iv), relative form; the property (A.1) produced by that paper's
Lemma 2.5 and consumed in EHM-2013 Theorem 6's finish): every `x ∈ Γ₁` has a
uniform basin radius `μ` from which the `Γ₂`-restricted forward orbit is drawn
into any `ε'`-tube of `Γ₁` after a finite time `T = T(ε')` INDEPENDENT of the
initial point in `B_μ(x) ∩ Γ₂`. This is the one genuine external core L-C rests
on; everything around it is discharged in `stableSet_of_uniformSemiAttractor`. -/
def UniformSemiAttractorRelativeTo (ϕ : Flow ℝ E) (Γ₁ Γ₂ : Set E) : Prop :=
  ∀ x ∈ Γ₁, ∃ μ > 0, ∀ ε' > 0, ∃ T > 0, ∀ y, dist y x < μ → y ∈ Γ₂ →
    ∀ t ≥ T, Metric.infDist (ϕ t y) Γ₁ < ε'

/-! ## Ball-nesting brick (pure metric) -/

/-- Ball-nesting (EHM-2013 `:1382-1408`): with `x̄ ∈ Γ₁`, the part of the `μ`-tube
of `Γ₁` that also lies in `B_m(x̄)` already lies in the `μ`-tube of the compact
sub-collar `Γ₁' = Γ₁ ∩ closedBall x̄ (2m)`. Pure metric — the triangle inequality
plus `x̄ ∈ Γ₁'`. Both the paper's cases (`μ ≤ m`: the `Γ₁`-witness lands in the
collar; `μ > m`: `x̄` itself works) are discharged. -/
theorem infDist_subCollar_of_mem_inter {Γ₁ : Set E} (hΓ₁ne : Γ₁.Nonempty)
    {xbar : E} (hxbar : xbar ∈ Γ₁) {μ m : ℝ} (hm : 0 < m) {z : E}
    (hzΓ : Metric.infDist z Γ₁ < μ) (hzx : dist z xbar < m) :
    Metric.infDist z (Γ₁ ∩ Metric.closedBall xbar (2 * m)) < μ := by
  have hxbar' : xbar ∈ Γ₁ ∩ Metric.closedBall xbar (2 * m) :=
    ⟨hxbar, Metric.mem_closedBall_self (by positivity)⟩
  by_cases hμm : μ ≤ m
  · -- μ ≤ m: the `Γ₁`-witness `y` (dist `< μ`) lands in `closedBall xbar (2m)`.
    obtain ⟨y, hyΓ, hzy⟩ := (Metric.infDist_lt_iff hΓ₁ne).mp hzΓ
    have hyz : dist y z < μ := by rwa [dist_comm] at hzy
    have hyx : dist y xbar ≤ 2 * m := by
      have htri := dist_triangle y z xbar
      linarith
    calc Metric.infDist z (Γ₁ ∩ Metric.closedBall xbar (2 * m))
        ≤ dist z y := Metric.infDist_le_dist_of_mem ⟨hyΓ, Metric.mem_closedBall.mpr hyx⟩
      _ < μ := hzy
  · -- m < μ: `xbar` itself is a collar witness within `μ`.
    have hμm' : m < μ := not_le.mp hμm
    calc Metric.infDist z (Γ₁ ∩ Metric.closedBall xbar (2 * m))
        ≤ dist z xbar := Metric.infDist_le_dist_of_mem hxbar'
      _ < μ := hzx.trans hμm'

/-! ## Uniform basin over a compact set — EHM-2013 (A.2)+(A.3)

From the per-point basin radii of `hUSA`, compactness extracts a SINGLE radius
`μ` valid across a compact `K ⊆ Γ₁`, and then per tube level `ε'` a SINGLE time
`T` (the paper's "the infimum of µ(x) … exists and is greater than zero" at
`:1352-1360` and the "again a compactness argument" step at `:1372-1381`).
Cover `K` by half-radius balls, take a finite subcover, set `μ` = the finite
min of half-radii and `T` = the finite max of the subcover's times; the
triangle inequality routes any `B_μ(x)` into a covering `B_{μ(x₀)}(x₀)`. -/
theorem uniform_basin_of_uniformSemiAttractor (ϕ : Flow ℝ E) {Γ₁ Γ₂ : Set E}
    (hUSA : UniformSemiAttractorRelativeTo ϕ Γ₁ Γ₂)
    {K : Set E} (hKcpt : IsCompact K) (hKne : K.Nonempty) (hKsub : K ⊆ Γ₁) :
    ∃ μ > 0, ∀ ε' > 0, ∃ T > 0, ∀ x ∈ K, ∀ y, dist y x < μ → y ∈ Γ₂ →
      ∀ t ≥ T, Metric.infDist (ϕ t y) Γ₁ < ε' := by
  choose! μf hμpos hμP using hUSA
  choose! Tf hTpos hTP using hμP
  -- finite subcover of K by half-radius basin balls
  obtain ⟨s, hsK, hcov⟩ := hKcpt.elim_nhds_subcover
    (fun w => Metric.ball w (μf w / 2))
    (fun w hw => Metric.ball_mem_nhds w (by have := hμpos w (hKsub hw); positivity))
  have hsne : s.Nonempty := by
    obtain ⟨p, hp⟩ := hKne
    obtain ⟨w, hws, -⟩ := mem_iUnion₂.mp (hcov hp)
    exact ⟨w, hws⟩
  refine ⟨s.inf' hsne (fun w => μf w / 2), ?_, ?_⟩
  · -- the finite min of half-radii is positive
    refine (Finset.lt_inf'_iff hsne).mpr fun w hws => ?_
    have := hμpos w (hKsub (hsK w hws))
    positivity
  · intro ε' hε'
    refine ⟨s.sup' hsne (fun w => Tf w ε'), ?_, ?_⟩
    · -- the finite max of times is positive
      obtain ⟨w, hws⟩ := hsne
      exact lt_of_lt_of_le (hTpos w (hKsub (hsK w hws)) ε' hε')
        (Finset.le_sup' (fun w => Tf w ε') hws)
    · intro x hx y hyx hyΓ₂ t ht
      -- route B_μ(x) into the covering ball B_{μf w}(w)
      obtain ⟨w, hws, hxw⟩ := mem_iUnion₂.mp (hcov hx)
      rw [Metric.mem_ball] at hxw
      have hwΓ₁ : w ∈ Γ₁ := hKsub (hsK w hws)
      have hμle : s.inf' hsne (fun w => μf w / 2) ≤ μf w / 2 :=
        Finset.inf'_le (fun w => μf w / 2) hws
      have hyw : dist y w < μf w := by
        calc dist y w ≤ dist y x + dist x w := dist_triangle y x w
          _ < s.inf' hsne (fun w => μf w / 2) + μf w / 2 := add_lt_add hyx hxw
          _ ≤ μf w / 2 + μf w / 2 := by linarith
          _ = μf w := by ring
      exact hTP w hwΓ₁ ε' hε' y hyw hyΓ₂ t
        (le_trans (Finset.le_sup' (fun w => Tf w ε') hws) ht)

/-! ## L-C — Theorem-6 finish: `StableSet ϕ Γ₁`

Compact-`Γ₁` branch of EHM-2013 Theorem 6, interface-cut as recorded in the
module docstring: `hUSA` carries assumption (i) + `Γ₂`-closedness (via the
EHM-2009 Lemma-2.5 seal), `hFirstExit` carries Lemma 22 + positive invariance,
`hContDep` carries flow regularity. Assumption (ii) enters directly as `hLSN`,
the compact-branch setup as `hΓ₁cpt`/`hΓ₁ne`/`hsub`/`hLUB`; the LUB rider (iii)
is exactly `hLUB` (non-vacuous here since it feeds the collar radius `m`).
`[FiniteDimensional ℝ E]` unlocks Bolzano–Weierstrass for L-B. -/
theorem stableSet_of_uniformSemiAttractor
    [FiniteDimensional ℝ E] (ϕ : Flow ℝ E) {Γ₁ Γ₂ : Set E}
    (hΓ₁cpt : IsCompact Γ₁) (hΓ₁ne : Γ₁.Nonempty) (hsub : Γ₁ ⊆ Γ₂)
    (hLUB : LUBNear ϕ Γ₁)
    (hLSN : LocallyStableNear ϕ Γ₂ Γ₁)
    (hUSA : UniformSemiAttractorRelativeTo ϕ Γ₁ Γ₂)
    (hFirstExit : ¬ StableSet ϕ Γ₁ →
      ∃ ε₀ > 0, ∃ x : ℕ → E,
        Tendsto (fun i => Metric.infDist (x i) Γ₁) atTop (𝓝 0) ∧
        ∀ ε > 0, ε ≤ ε₀ → ∃ t : ℕ → ℝ, Tendsto t atTop atTop ∧
          ∀ᶠ i in atTop, Metric.infDist (ϕ (t i) (x i)) Γ₁ = ε ∧
            ∀ s ∈ Set.Ico (0 : ℝ) (t i), Metric.infDist (ϕ s (x i)) Γ₁ < ε)
    (hContDep : ∀ (T : ℝ) (p : E), ∀ r > 0, ∀ η > 0, ∃ δ > 0,
      ∀ z z', dist z p < r → dist z z' < δ → dist (ϕ T z) (ϕ T z') < η) :
    StableSet ϕ Γ₁ := by
  by_contra hns
  obtain ⟨ε₀, hε₀, x, hx0, hexit⟩ := hFirstExit hns
  -- L-B: a subsequence of the escape base points converges to some x̄ ∈ Γ₁
  obtain ⟨xbar, hxbarΓ, σ, hσ, hxσ⟩ :=
    exists_subseq_tendsto_mem_of_infDist_tendsto_zero hΓ₁ne hΓ₁cpt.isClosed
      hΓ₁cpt.isBounded hx0
  -- local uniform boundedness at x̄: orbits from B_lam(x̄) stay in B_m(x̄)
  obtain ⟨lam, hlam, m, hm, hLUBx⟩ := hLUB xbar hxbarΓ
  -- the widened compact sub-collar (radius m+1 absorbs the Γ₂-witness slack)
  have hMpos : (0 : ℝ) < m + 1 := by positivity
  have hKcpt : IsCompact (Γ₁ ∩ Metric.closedBall xbar (2 * (m + 1))) :=
    hΓ₁cpt.inter_right Metric.isClosed_closedBall
  have hxbarK : xbar ∈ Γ₁ ∩ Metric.closedBall xbar (2 * (m + 1)) :=
    ⟨hxbarΓ, Metric.mem_closedBall_self (by positivity)⟩
  -- uniform basin radius µ over the sub-collar — depends only on x̄ and m
  obtain ⟨μ, hμ, hbasin⟩ := uniform_basin_of_uniformSemiAttractor ϕ hUSA hKcpt
    ⟨xbar, hxbarK⟩ inter_subset_left
  -- the working escape level: ε ≤ ε₀ AND ε < µ (paper footnote 3, `:1396-1398`)
  set ε := min ε₀ (μ / 2) with hεdef
  have hε : 0 < ε := lt_min hε₀ (by positivity)
  have hεle : ε ≤ ε₀ := by rw [hεdef]; exact min_le_left _ _
  have hεμ2 : ε ≤ μ / 2 := by rw [hεdef]; exact min_le_right _ _
  have hεμ : ε < μ := by linarith
  obtain ⟨t, htT, hev⟩ := hexit ε hε hεle
  -- uniform time T for the tube level ε/4
  obtain ⟨T, hT, hTP⟩ := hbasin (ε / 4) (by positivity)
  -- continuous dependence at time T on the widened ball
  obtain ⟨δcd, hδcd, hcd⟩ := hContDep T xbar (m + 1) hMpos (ε / 2) (by positivity)
  -- the working perturbation radius
  set δ := min (min δcd ((μ - ε) / 2)) 1 with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    refine lt_min (lt_min hδcd ?_) one_pos
    linarith
  have hδcdle : δ ≤ δcd := by
    rw [hδdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hδμε : δ ≤ (μ - ε) / 2 := by
    rw [hδdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hδ1 : δ ≤ 1 := by rw [hδdef]; exact min_le_right _ _
  -- segment-approaches-Γ₂ tooling (EHM `:1325-1343`, from hLSN + hLUB)
  obtain ⟨δ', hδ', hseg⟩ := hLSN xbar hxbarΓ m hm δ hδpos
  -- a single index far enough along the subsequence
  have h1 : ∀ᶠ j in atTop, dist (x (σ j)) xbar < lam :=
    Metric.tendsto_nhds.mp hxσ lam hlam
  have h2 : ∀ᶠ j in atTop, Metric.infDist (x (σ j)) Γ₁ < δ' := by
    have h2' := Metric.tendsto_nhds.mp hx0 δ' hδ'
    have h2'' : ∀ᶠ i in atTop, Metric.infDist (x i) Γ₁ < δ' := by
      filter_upwards [h2'] with i hi
      rwa [Real.dist_eq, sub_zero, abs_of_nonneg Metric.infDist_nonneg] at hi
    exact hσ.tendsto_atTop.eventually h2''
  have h3 : ∀ᶠ j in atTop, T < t (σ j) :=
    hσ.tendsto_atTop.eventually (htT.eventually (eventually_gt_atTop T))
  have h4 := hσ.tendsto_atTop.eventually hev
  obtain ⟨j, hjlam, hjδ', hjT, hjeq, hjlt⟩ := (h1.and (h2.and (h3.and h4))).exists
  -- the glue at index k = σ j
  set k := σ j with hkdef
  -- z: the trajectory point T before the first exit
  have h0Tk : 0 ≤ t k - T := by linarith
  have hzΓ₁ : Metric.infDist (ϕ (t k - T) (x k)) Γ₁ < ε :=
    hjlt (t k - T) ⟨h0Tk, by linarith⟩
  have hzx : dist (ϕ (t k - T) (x k)) xbar < m := hLUBx (x k) hjlam (t k - T) h0Tk
  -- the pre-exit segment lies in B_m(x̄) (hLUB), so hLSN pushes z within δ of Γ₂
  have hzΓ₂ : Metric.infDist (ϕ (t k - T) (x k)) Γ₂ < δ := by
    have hcond : ∀ s ∈ Set.Icc (0 : ℝ) (t k), dist (ϕ s (x k)) xbar < m :=
      fun s hs => hLUBx (x k) hjlam s hs.1
    exact hseg (x k) hjδ' (t k) (by linarith) hcond (t k - T) ⟨h0Tk, by linarith⟩
  -- a Γ₂ witness δ-close to z
  obtain ⟨z', hz'Γ₂, hzz'⟩ :=
    (Metric.infDist_lt_iff (hΓ₁ne.mono hsub)).mp hzΓ₂
  -- z' lies in the µ-tube of Γ₁ (ε + δ < µ) …
  have hz'Γ₁ : Metric.infDist z' Γ₁ < μ := by
    have hle : Metric.infDist z' Γ₁ ≤
        Metric.infDist (ϕ (t k - T) (x k)) Γ₁ + dist z' (ϕ (t k - T) (x k)) :=
      Metric.infDist_le_infDist_add_dist
    have hd : dist z' (ϕ (t k - T) (x k)) < δ := by rwa [dist_comm] at hzz'
    calc Metric.infDist z' Γ₁
        ≤ Metric.infDist (ϕ (t k - T) (x k)) Γ₁ + dist z' (ϕ (t k - T) (x k)) := hle
      _ < ε + δ := add_lt_add hzΓ₁ hd
      _ ≤ ε + (μ - ε) / 2 := by linarith
      _ < μ := by linarith
  -- … and within the widened ball at x̄ (δ ≤ 1 absorbs the witness slack)
  have hz'x : dist z' xbar < m + 1 := by
    have hd : dist z' (ϕ (t k - T) (x k)) < δ := by rwa [dist_comm] at hzz'
    calc dist z' xbar
        ≤ dist z' (ϕ (t k - T) (x k)) + dist (ϕ (t k - T) (x k)) xbar :=
          dist_triangle _ _ _
      _ < δ + m := add_lt_add hd hzx
      _ ≤ 1 + m := by linarith
      _ = m + 1 := by ring
  -- ball-nesting into the compact sub-collar, then a collar witness within µ
  have hz'K : Metric.infDist z' (Γ₁ ∩ Metric.closedBall xbar (2 * (m + 1))) < μ :=
    infDist_subCollar_of_mem_inter hΓ₁ne hxbarΓ hMpos hz'Γ₁ hz'x
  obtain ⟨xstar, hxstarK, hz'xstar⟩ :=
    (Metric.infDist_lt_iff ⟨xbar, hxbarK⟩).mp hz'K
  -- uniform basin: from time T on, the orbit of z' is inside the ε/4-tube
  have hfar : Metric.infDist (ϕ T z') Γ₁ < ε / 4 :=
    hTP xstar hxstarK z' hz'xstar hz'Γ₂ T le_rfl
  -- continuous dependence transports it to z
  have hnear : dist (ϕ T (ϕ (t k - T) (x k))) (ϕ T z') < ε / 2 :=
    hcd (ϕ (t k - T) (x k)) z' (hzx.trans (lt_add_one m)) (hzz'.trans_le hδcdle)
  -- the flow law: the exit point is the T-image of z
  have hflow : ϕ (t k) (x k) = ϕ T (ϕ (t k - T) (x k)) := by
    have harg : T + (t k - T) = t k := by ring
    calc ϕ (t k) (x k) = ϕ (T + (t k - T)) (x k) := by rw [harg]
      _ = ϕ T (ϕ (t k - T) (x k)) := ϕ.map_add T (t k - T) (x k)
  -- contradiction with the first-exit equality
  have hlt : Metric.infDist (ϕ (t k) (x k)) Γ₁ < ε := by
    rw [hflow]
    calc Metric.infDist (ϕ T (ϕ (t k - T) (x k))) Γ₁
        ≤ Metric.infDist (ϕ T z') Γ₁ + dist (ϕ T (ϕ (t k - T) (x k))) (ϕ T z') :=
          Metric.infDist_le_infDist_add_dist
      _ < ε / 4 + ε / 2 := add_lt_add hfar hnear
      _ < ε := by linarith
  exact absurd hjeq (ne_of_lt hlt)

/-! ## Tightening seals — the flow-side interfaces discharged

Same-day discharges of the core theorem's two flow-regularity hypotheses,
leaving `hUSA` as the module's only interface. -/

/-- `hContDep` discharged (EHM-2013 `:1447`): continuous dependence of the
time-`T` map on a ball, by Heine–Cantor uniform continuity on the compact
closed ball of radius `r + 1` (`ProperSpace` from `[FiniteDimensional ℝ E]`);
the `min δ 1` cap keeps both points inside the collar. -/
theorem contDep_of_flow [FiniteDimensional ℝ E] (ϕ : Flow ℝ E) :
    ∀ (T : ℝ) (p : E), ∀ r > 0, ∀ η > 0, ∃ δ > 0,
      ∀ z z', dist z p < r → dist z z' < δ → dist (ϕ T z) (ϕ T z') < η := by
  intro T p r hr η hη
  have hK : IsCompact (Metric.closedBall p (r + 1)) := isCompact_closedBall p (r + 1)
  have hUC : UniformContinuousOn (ϕ T) (Metric.closedBall p (r + 1)) :=
    hK.uniformContinuousOn_of_continuous (ϕ.continuous_toFun T).continuousOn
  obtain ⟨δ, hδpos, hδ⟩ := Metric.uniformContinuousOn_iff.mp hUC η hη
  refine ⟨min δ 1, lt_min hδpos one_pos, fun z z' hz hzz' => ?_⟩
  have hz1 : z ∈ Metric.closedBall p (r + 1) := by
    rw [Metric.mem_closedBall]
    linarith
  have hz'1 : z' ∈ Metric.closedBall p (r + 1) := by
    rw [Metric.mem_closedBall]
    have h1 : dist z' z < 1 := by
      rw [dist_comm]
      exact lt_of_lt_of_le hzz' (min_le_right _ _)
    have h2 : dist z' p ≤ dist z' z + dist z p := dist_triangle z' z p
    linarith
  exact hδ z hz1 z' hz'1 (lt_of_lt_of_le hzz' (min_le_left _ _))

omit [NormedSpace ℝ E] in
/-- Brick 1 of the `hFirstExit` discharge (EHM-2013 Lemma 22 first-exit
refinement, `:1290-1316`): if the trajectory of `x₀` starts strictly inside
the `ε`-tube of `Γ₁` and is outside it (≥ ε) at some `t₁ ≥ 0`, there is a
first time `τ ∈ [0, t₁]` at which the point-to-set distance EQUALS `ε`, the
distance staying `< ε` on `[0, τ)`. Route: `τ := sInf` of the closed hitting
set `Icc 0 t₁ ∩ {ε ≤ g}`; `IsClosed.csInf_mem` gives `ε ≤ g τ`; minimality
gives `g < ε` before `τ`; the left-limit of the pre-`τ` values gives
`g τ ≤ ε` (`τ = 0` is excluded by `g 0 < ε`). -/
theorem exists_firstExitTime (ϕ : Flow ℝ E) {Γ₁ : Set E} {ε : ℝ} {x₀ : E}
    (hx₀ : Metric.infDist x₀ Γ₁ < ε) {t₁ : ℝ} (ht₁ : 0 ≤ t₁)
    (hexit : ε ≤ Metric.infDist (ϕ t₁ x₀) Γ₁) :
    ∃ τ ∈ Set.Icc (0 : ℝ) t₁, Metric.infDist (ϕ τ x₀) Γ₁ = ε ∧
      ∀ s ∈ Set.Ico (0 : ℝ) τ, Metric.infDist (ϕ s x₀) Γ₁ < ε := by
  have hgc : Continuous fun s : ℝ => Metric.infDist (ϕ s x₀) Γ₁ :=
    (Metric.continuous_infDist_pt Γ₁).comp (ϕ.continuous continuous_id continuous_const)
  -- the hitting set: closed, nonempty (t₁), bounded below (0)
  set H : Set ℝ := Set.Icc (0 : ℝ) t₁ ∩ {s | ε ≤ Metric.infDist (ϕ s x₀) Γ₁} with hHdef
  have hHcl : IsClosed H := isClosed_Icc.inter (isClosed_le continuous_const hgc)
  have hHne : H.Nonempty := ⟨t₁, ⟨ht₁, le_rfl⟩, hexit⟩
  have hHbdd : BddBelow H := ⟨0, fun s hs => hs.1.1⟩
  have hτH : sInf H ∈ H := hHcl.csInf_mem hHne hHbdd
  obtain ⟨⟨hτ0, hτt₁⟩, hτge⟩ := hτH
  -- strictly inside the tube before the infimum
  have hpre : ∀ s ∈ Set.Ico (0 : ℝ) (sInf H), Metric.infDist (ϕ s x₀) Γ₁ < ε := by
    rintro s ⟨hs0, hsτ⟩
    by_contra hcon
    have hsH : s ∈ H := ⟨⟨hs0, hsτ.le.trans hτt₁⟩, not_lt.mp hcon⟩
    exact absurd (csInf_le hHbdd hsH) (not_le.mpr hsτ)
  -- τ = 0 is excluded: g 0 = infDist x₀ Γ₁ < ε
  have hg0 : Metric.infDist (ϕ (0 : ℝ) x₀) Γ₁ < ε := by
    rw [ϕ.map_zero_apply]; exact hx₀
  have hτpos : 0 < sInf H := by
    rcases hτ0.lt_or_eq with h | h
    · exact h
    · rw [← h] at hτge
      exact absurd hτge (not_le.mpr hg0)
  -- left-limit of the pre-τ values: g τ ≤ ε
  have hτle : Metric.infDist (ϕ (sInf H) x₀) Γ₁ ≤ ε := by
    have htend : Tendsto (fun s : ℝ => Metric.infDist (ϕ s x₀) Γ₁) (𝓝[<] sInf H)
        (𝓝 (Metric.infDist (ϕ (sInf H) x₀) Γ₁)) :=
      (hgc.tendsto (sInf H)).mono_left nhdsWithin_le_nhds
    refine le_of_tendsto htend ?_
    filter_upwards [Ico_mem_nhdsLT hτpos] with s hs
    exact (hpre s hs).le
  exact ⟨sInf H, ⟨hτ0, hτt₁⟩, le_antisymm hτle hτge, hpre⟩

omit [NormedSpace ℝ E] in
/-- Brick 3 core of the `hFirstExit` discharge (EHM-2013 `:1421`,
unbounded-escape-times mechanism): on a compact time window `[0, B]`, forward
invariance of the compact `Γ₁` plus joint continuity of the flow confine some
`δ`-collar of `Γ₁` inside the `η`-tube for ALL `s ∈ [0, B]`. Tube lemma on
`[0,B] ×ˢ Γ₁` inside the open sublevel set of `(s, z) ↦ infDist (ϕ s z) Γ₁`,
then a compact thickening inside the open tube factor. No finite dimension
needed. -/
theorem exists_uniform_tube_radius (ϕ : Flow ℝ E) {Γ₁ : Set E}
    (hΓ₁cpt : IsCompact Γ₁) (hΓ₁ne : Γ₁.Nonempty)
    (hfi : IsForwardInvariant ϕ.toFun Γ₁) (B : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ z, Metric.infDist z Γ₁ < δ →
      ∀ s ∈ Set.Icc (0 : ℝ) B, Metric.infDist (ϕ s z) Γ₁ < η := by
  -- the open sublevel set of the jointly-continuous tube function
  have hcont : Continuous fun p : ℝ × E => Metric.infDist (ϕ p.1 p.2) Γ₁ :=
    (Metric.continuous_infDist_pt Γ₁).comp (ϕ.continuous continuous_fst continuous_snd)
  have hnopen : IsOpen {p : ℝ × E | Metric.infDist (ϕ p.1 p.2) Γ₁ < η} :=
    isOpen_lt hcont continuous_const
  -- it contains [0,B] × Γ₁ by forward invariance
  have hsub : Set.Icc (0 : ℝ) B ×ˢ Γ₁ ⊆
      {p : ℝ × E | Metric.infDist (ϕ p.1 p.2) Γ₁ < η} := by
    rintro ⟨s, y⟩ ⟨hs, hy⟩
    have hmem : ϕ s y ∈ Γ₁ := hfi hs.1 hy
    show Metric.infDist (ϕ s y) Γ₁ < η
    rw [Metric.infDist_zero_of_mem hmem]
    exact hη
  obtain ⟨u, v, -, hvo, huI, hvΓ, huv⟩ :=
    generalized_tube_lemma isCompact_Icc hΓ₁cpt hnopen hsub
  obtain ⟨δ, hδ, hthick⟩ := hΓ₁cpt.exists_thickening_subset_open hvo hvΓ
  refine ⟨δ, hδ, fun z hz s hs => ?_⟩
  have hzv : z ∈ v := hthick ((Metric.mem_thickening_iff_infDist_lt hΓ₁ne).mpr hz)
  have hpm : ((s, z) : ℝ × E) ∈ u ×ˢ v := ⟨huI hs, hzv⟩
  exact huv hpm

/-- `hFirstExit` discharged (EHM-2013 Lemma 22, first-exit form + `:1421`):
the base sequence comes from L-A (`escape_sequence_of_not_stableSet`); for
each level `ε ≤ ε₀` the exit-time family comes from `exists_firstExitTime` on
the eventual tail where the base point is inside the `ε`-tube (junk time
elsewhere); unboundedness of the exit times is Brick 3 — bounded times would
confine the exit point strictly inside the `ε`-tube, contradicting the exit
equality. Positive invariance enters HERE, as the module docstring promised. -/
theorem firstExit_of_not_stableSet (ϕ : Flow ℝ E) {Γ₁ : Set E}
    (hΓ₁cpt : IsCompact Γ₁) (hΓ₁ne : Γ₁.Nonempty)
    (hfi : IsForwardInvariant ϕ.toFun Γ₁)
    (hns : ¬ StableSet ϕ Γ₁) :
    ∃ ε₀ > 0, ∃ x : ℕ → E,
      Tendsto (fun i => Metric.infDist (x i) Γ₁) atTop (𝓝 0) ∧
      ∀ ε > 0, ε ≤ ε₀ → ∃ t : ℕ → ℝ, Tendsto t atTop atTop ∧
        ∀ᶠ i in atTop, Metric.infDist (ϕ (t i) (x i)) Γ₁ = ε ∧
          ∀ s ∈ Set.Ico (0 : ℝ) (t i), Metric.infDist (ϕ s (x i)) Γ₁ < ε := by
  obtain ⟨ε₀, hε₀, x, t', ht'0, hx0, hge⟩ := escape_sequence_of_not_stableSet ϕ hns
  refine ⟨ε₀, hε₀, x, hx0, fun ε hε hεle => ?_⟩
  -- the eventual tail where the base point is inside the ε-tube
  have hev : ∀ᶠ i in atTop, Metric.infDist (x i) Γ₁ < ε := hx0.eventually_lt_const hε
  -- per-index first-exit time on that tail (Brick 1)
  have hkey : ∀ i, Metric.infDist (x i) Γ₁ < ε →
      ∃ τ, 0 ≤ τ ∧ Metric.infDist (ϕ τ (x i)) Γ₁ = ε ∧
        ∀ s ∈ Set.Ico (0 : ℝ) τ, Metric.infDist (ϕ s (x i)) Γ₁ < ε := by
    intro i hi
    obtain ⟨τ, hτmem, hτeq, hτpre⟩ :=
      exists_firstExitTime ϕ hi (ht'0 i) (hεle.trans (hge i))
    exact ⟨τ, hτmem.1, hτeq, hτpre⟩
  choose! t ht0 hteq htpre using hkey
  refine ⟨t, ?_, ?_⟩
  · -- Brick 3: the exit times are unbounded
    by_contra hcon
    rw [tendsto_atTop_atTop] at hcon
    push Not at hcon
    obtain ⟨B, hB⟩ := hcon
    obtain ⟨δ, hδ, htube⟩ := exists_uniform_tube_radius ϕ hΓ₁cpt hΓ₁ne hfi B hε
    have hevδ : ∀ᶠ i in atTop, Metric.infDist (x i) Γ₁ < δ := hx0.eventually_lt_const hδ
    have hfreq : ∃ᶠ i in atTop, t i < B := frequently_atTop.mpr hB
    obtain ⟨i, hiB, hiε, hiδ⟩ := (hfreq.and_eventually (hev.and hevδ)).exists
    exact absurd (hteq i hiε)
      (ne_of_lt (htube (x i) hiδ (t i) ⟨ht0 i hiε, hiB.le⟩))
  · -- the eventual first-exit property
    filter_upwards [hev] with i hi
    exact ⟨hteq i hi, htpre i hi⟩

/-- The public assembly — EHM-2013 Theorem 6 (compact branch, stability half)
with both flow-side interfaces discharged: the ONLY interface hypothesis left
is `hUSA` (EHM-2009 Lemma 2.5, the R6 target); every other hypothesis is a
standing condition of the paper's Theorem 6 itself. -/
theorem stableSet_of_uniformSemiAttractor_of_forwardInvariant
    [FiniteDimensional ℝ E] (ϕ : Flow ℝ E) {Γ₁ Γ₂ : Set E}
    (hΓ₁cpt : IsCompact Γ₁) (hΓ₁ne : Γ₁.Nonempty) (hsub : Γ₁ ⊆ Γ₂)
    (hfi : IsForwardInvariant ϕ.toFun Γ₁)
    (hLUB : LUBNear ϕ Γ₁)
    (hLSN : LocallyStableNear ϕ Γ₂ Γ₁)
    (hUSA : UniformSemiAttractorRelativeTo ϕ Γ₁ Γ₂) :
    StableSet ϕ Γ₁ :=
  stableSet_of_uniformSemiAttractor ϕ hΓ₁cpt hΓ₁ne hsub hLUB hLSN hUSA
    (fun hns => firstExit_of_not_stableSet ϕ hΓ₁cpt hΓ₁ne hfi hns)
    (contDep_of_flow ϕ)

end Ctrllib

#print axioms Ctrllib.infDist_subCollar_of_mem_inter
#print axioms Ctrllib.uniform_basin_of_uniformSemiAttractor
#print axioms Ctrllib.stableSet_of_uniformSemiAttractor
#print axioms Ctrllib.contDep_of_flow
#print axioms Ctrllib.exists_firstExitTime
#print axioms Ctrllib.exists_uniform_tube_radius
#print axioms Ctrllib.firstExit_of_not_stableSet
#print axioms Ctrllib.stableSet_of_uniformSemiAttractor_of_forwardInvariant
