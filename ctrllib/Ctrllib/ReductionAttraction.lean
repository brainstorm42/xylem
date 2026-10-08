/-
R5 F3 — the `hLandsInΓ₁` discharge (EHM-2013 Theorem 8, local branch) and the
rung-closing rewire.

L4a's `reduction_asymptotic_stability` (`Ctrllib.Reduction`, EHM Theorem 10
compact branch) took BOTH Appendix-A topology cores as named hypotheses:
`hStable` (Theorem 6) and `hLandsInΓ₁` (Theorem 8 local core). The sibling
module `ReductionStabilityFinish` discharged `hStable` down to `hUSA`; this
module discharges `hLandsInΓ₁` outright — EHM-2013 Appendix A.2 (corpus
the corresponding local note) is self-contained, so NO interface cut
is needed (recon the corresponding local note, finding 1) — and then wires
everything together:

  T8-A `omegaLimit_subset_of_tendsto_infDist` — ω-limit sets of trajectories
    drawn to a closed set lie in it (the dual of the reduction engine).
  T8-B `omegaLimit_subset_of_stableRelativeTo` — the backward-orbit core:
    a forward-precompact orbit whose ω-limit set lies in `Γ₂`, is pointwise
    drawn to `Γ₁`, with `Γ₁` stable relative to `Γ₂`, has its ω-limit set
    inside `Γ₁`. Restructured from the paper's letter (recon §6.2): the
    α-limit set is replaced by one Bolzano–Weierstrass limit point of the
    backward sequence — the same mathematical move, recorded loudly.
  T8-C `exists_forwardPrecompact_omegaLimit_subset_of_stableSet` — the
    assembly producing the exact `hLandsInΓ₁` formula; derives the paper's
    condition (iii) from set stability (the Theorem-10 combination sentence
    EHM leave implicit at `:308`).
  T8-D `reduction_asymptotic_stability_of_uniformSemiAttractor` — the rewire:
    ledger rows 23 (`hStable`) and 24 (`hLandsInΓ₁`) collapse onto the single
    external core `hUSA` (EHM-2009 Lemma 2.5, the R6 target). Every other
    hypothesis is a standing condition of EHM Theorems 8/10 themselves.

Human derivation for THIS module:
the corresponding derivation record (not bundled).
-/
import Ctrllib.ReductionStabilityFinish

open Set Filter Topology omegaLimit

namespace Ctrllib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- **T8-A** — the ω-limit set of a trajectory converging to a closed nonempty
set `Γ₂` is contained in `Γ₂`. The dual of the reduction engine
`tendsto_infDist_of_omegaLimit_subset`: one application of
`eq_on_omegaLimit_of_tendsto` to the continuous function `infDist (·) Γ₂`
(constant `0` on the ω-limit set), then closedness converts
`infDist y Γ₂ = 0` into membership. Metric-only — no `NormedSpace` needed. -/
theorem omegaLimit_subset_of_tendsto_infDist (ϕ : Flow ℝ E) (x : E)
    {Γ₂ : Set E} (hclosed : IsClosed Γ₂) (hne : Γ₂.Nonempty)
    (htend : Tendsto (fun t : ℝ => Metric.infDist (ϕ t x) Γ₂) atTop (𝓝 0)) :
    ω⁺ ϕ.toFun {x} ⊆ Γ₂ := by
  have h0 : ∀ y ∈ ω⁺ ϕ.toFun {x}, Metric.infDist y Γ₂ = 0 :=
    eq_on_omegaLimit_of_tendsto (Metric.continuous_infDist_pt Γ₂) htend
  exact fun y hy => (hclosed.mem_iff_infDist_zero hne).mpr (h0 y hy)

omit [NormedSpace ℝ E] in
/-- **T8-B** — the backward-orbit core of EHM-2013 Theorem 8 (Appendix A.2,
local branch, steps 4–7): if the ω-limit set of a forward-precompact orbit
lies in `Γ₂`, every point of it is drawn to `Γ₁` in forward time, and `Γ₁` is
stable relative to `Γ₂`, then the ω-limit set lies in `Γ₁`.

Restructured from the paper's letter (recon §6.2): the α-limit set `L⁻(ω)` is
replaced by a single Bolzano–Weierstrass limit point `q` of the backward
sequence `ϕ (−k) w` inside the compact invariant ω-limit set — the same
mathematical move (a backward-orbit limit point whose forward orbit visits the
stability tube of `Γ₁`, after which relative stability forbids the return to
`w`). Metric-only: no `ProperSpace`, no `FiniteDimensional` — compactness of
the ω-limit set comes from `hcpt` via `IsCompact.of_isClosed_subset`. -/
theorem omegaLimit_subset_of_stableRelativeTo (ϕ : Flow ℝ E) (x : E)
    {Γ₁ Γ₂ : Set E} (hΓ₁closed : IsClosed Γ₁) (hΓ₁ne : Γ₁.Nonempty)
    (hcpt : ForwardPrecompact ϕ x)
    (hω₂ : ω⁺ ϕ.toFun {x} ⊆ Γ₂)
    (hbasin : ∀ q ∈ ω⁺ ϕ.toFun {x},
      Tendsto (fun t : ℝ => Metric.infDist (ϕ t q) Γ₁) atTop (𝓝 0))
    (hStabRel : StableRelativeTo ϕ Γ₁ Γ₂) :
    ω⁺ ϕ.toFun {x} ⊆ Γ₁ := by
  intro w hw
  by_contra hwΓ₁
  -- step 4: ε := infDist w Γ₁ > 0 (contrapositive of closed-membership)
  have hε : 0 < Metric.infDist w Γ₁ :=
    lt_of_le_of_ne Metric.infDist_nonneg fun h =>
      hwΓ₁ ((hΓ₁closed.mem_iff_infDist_zero hΓ₁ne).mpr h.symm)
  -- step 6: the relative-stability tube δ at level ε (the paper's N₄)
  obtain ⟨δ, hδ, hstab⟩ := hStabRel (Metric.infDist w Γ₁) hε
  -- the ω-limit set is closed, inside the orbit closure, hence compact
  have hLclosed : IsClosed (ω⁺ ϕ.toFun {x}) := isClosed_omegaLimit atTop ϕ.toFun {x}
  have horbit_fwd : image2 ϕ.toFun (Ici 0) {x} = (fun t : ℝ => ϕ t x) '' Ici 0 := by
    rw [image2_singleton_right]
  have hLsub : ω⁺ ϕ.toFun {x} ⊆ closure ((fun t : ℝ => ϕ t x) '' Ici 0) := by
    have h := omegaLimit_subset_closure_image2 atTop ϕ.toFun {x} (Ici_mem_atTop (0 : ℝ))
    rwa [horbit_fwd] at h
  have hLcpt : IsCompact (ω⁺ ϕ.toFun {x}) := hcpt.of_isClosed_subset hLclosed hLsub
  -- two-sided invariance (all t : ℝ, the lasalle shift recipe)
  have hshift : ∀ t : ℝ, Tendsto (t + ·) (atTop : Filter ℝ) atTop := fun t =>
    tendsto_atTop_add_const_left atTop t tendsto_id
  have hinv : IsInvariant ϕ.toFun (ω⁺ ϕ.toFun {x}) :=
    ϕ.isInvariant_omegaLimit atTop {x} hshift
  -- step 5: backward sequence in the compact ω-limit set; one limit point q
  have hyL : ∀ k : ℕ, ϕ (-(k : ℝ)) w ∈ ω⁺ ϕ.toFun {x} := fun k =>
    hinv (-(k : ℝ)) hw
  obtain ⟨q, hqL, σ, hσ, hqlim⟩ := hLcpt.tendsto_subseq hyL
  -- the forward orbit of q enters the δ/2-tube of Γ₁ at some s ≥ 0
  obtain ⟨s, hs0, hsδ⟩ : ∃ s : ℝ, 0 ≤ s ∧ Metric.infDist (ϕ s q) Γ₁ < δ / 2 := by
    have hev : ∀ᶠ s : ℝ in atTop, Metric.infDist (ϕ s q) Γ₁ < δ / 2 :=
      (hbasin q hqL).eventually_lt_const (half_pos hδ)
    obtain ⟨s, h1, h2⟩ := (hev.and (eventually_ge_atTop (0 : ℝ))).exists
    exact ⟨s, h2, h1⟩
  -- continuity of the fixed-time map transports the tube bound along σ
  have hzlim : Tendsto (fun j => ϕ s (ϕ (-(σ j : ℝ)) w)) atTop (𝓝 (ϕ s q)) :=
    ((ϕ.continuous_toFun s).tendsto q).comp hqlim
  have hnear : ∀ᶠ j in atTop, dist (ϕ s (ϕ (-(σ j : ℝ)) w)) (ϕ s q) < δ / 2 :=
    Metric.tendsto_nhds.mp hzlim (δ / 2) (half_pos hδ)
  -- the subsequence index eventually dominates s
  have hbig : ∀ᶠ j in atTop, s ≤ (σ j : ℝ) :=
    (tendsto_natCast_atTop_atTop.comp hσ.tendsto_atTop).eventually_ge_atTop s
  obtain ⟨j, hjnear, hjbig⟩ := (hnear.and hbig).exists
  -- step 7: the tube point z ∈ ω⁺ ⊆ Γ₂ within δ of Γ₁, and T := σ j − s ≥ 0
  set z := ϕ s (ϕ (-(σ j : ℝ)) w) with hzdef
  have hzL : z ∈ ω⁺ ϕ.toFun {x} := hinv s (hinv (-(σ j : ℝ)) hw)
  have hzΓ₂ : z ∈ Γ₂ := hω₂ hzL
  have hzΓ₁ : Metric.infDist z Γ₁ < δ := by
    calc Metric.infDist z Γ₁
        ≤ Metric.infDist (ϕ s q) Γ₁ + dist z (ϕ s q) :=
          Metric.infDist_le_infDist_add_dist
      _ < δ / 2 + δ / 2 := add_lt_add hsδ hjnear
      _ = δ := by ring
  -- flow reassembly: ϕ (σ j − s) z = w
  have hflow : ϕ ((σ j : ℝ) - s) z = w := by
    rw [hzdef, ← ϕ.map_add, ← ϕ.map_add]
    have harg : (σ j : ℝ) - s + s + -(σ j : ℝ) = 0 := by ring
    rw [harg, ϕ.map_zero_apply]
  -- relative stability at (z, T) puts ϕ T z = w strictly inside the ε-tube
  have hcontra : Metric.infDist (ϕ ((σ j : ℝ) - s) z) Γ₁ < Metric.infDist w Γ₁ :=
    hstab z hzΓ₂ hzΓ₁ ((σ j : ℝ) - s) (sub_nonneg.mpr hjbig)
  rw [hflow] at hcontra
  exact lt_irrefl _ hcontra

/-- **T8-C** — the `hLandsInΓ₁` assembly (EHM-2013 Theorem 8, local branch,
steps 1–3 of the recon map, feeding T8-A and T8-B): around a compact `Γ₁`
there is a tube of initial conditions whose orbits are forward-precompact
with ω-limit sets inside `Γ₁` — the exact formula
`reduction_asymptotic_stability` consumes as `hLandsInΓ₁`.

The paper states Theorem 8's condition (iii) as a modelling input and leaves
its Theorem-10 derivation implicit ("By combining Theorems 8 and 6", `:308`);
here, for compact `Γ₁`, condition (iii) is DERIVED from set stability
`hStable : StableSet ϕ Γ₁` (Theorem 6's output, ledger row 23): stability at
level `δa/2` confines orbits from a `δ₀`-tube to a bounded tube strictly
inside the relative basin of attraction, giving both boundedness (hence
forward precompactness — `ProperSpace` from `[FiniteDimensional ℝ E]`) and
the (A.5) basin inclusion. `hLAN` (condition (ii)) feeds T8-A to place
ω-limit sets in `Γ₂`; T8-B (condition (i) via `hStabRel`/`hAttrRel`)
collapses them into `Γ₁`. `hsub` is the paper's standing condition
`Γ₁ ⊂ Γ₂`, consumed only for `Γ₂.Nonempty`. -/
theorem exists_forwardPrecompact_omegaLimit_subset_of_stableSet
    [FiniteDimensional ℝ E] (ϕ : Flow ℝ E) {Γ₁ Γ₂ : Set E}
    (hΓ₁cpt : IsCompact Γ₁) (hΓ₁ne : Γ₁.Nonempty)
    (hΓ₂closed : IsClosed Γ₂) (hsub : Γ₁ ⊆ Γ₂)
    (hStable : StableSet ϕ Γ₁)
    (hStabRel : StableRelativeTo ϕ Γ₁ Γ₂)
    (hAttrRel : AttractiveRelativeTo ϕ Γ₁ Γ₂)
    (hLAN : LocallyAttractiveNear ϕ Γ₂ Γ₁) :
    ∃ δ > 0, ∀ x, Metric.infDist x Γ₁ < δ →
      ForwardPrecompact ϕ x ∧ ω⁺ ϕ.toFun {x} ⊆ Γ₁ := by
  -- the relative basin radius δa (condition (i), attractivity half)
  obtain ⟨δa, hδa, hattr⟩ := hAttrRel
  -- stability at level δa/2: the confinement tube δ₀ — the derived condition (iii)
  obtain ⟨δ₀, hδ₀, htube⟩ := hStable (δa / 2) (half_pos hδa)
  -- the local-attractivity tube δL (condition (ii))
  obtain ⟨δL, hδL, hlan⟩ := hLAN
  refine ⟨min δ₀ δL, lt_min hδ₀ hδL, fun x hx => ?_⟩
  have hxδ₀ : Metric.infDist x Γ₁ < δ₀ := hx.trans_le (min_le_left _ _)
  have hxδL : Metric.infDist x Γ₁ < δL := hx.trans_le (min_le_right _ _)
  -- step 1: the forward orbit stays in the δa/2-tube of the compact Γ₁ …
  have horb : ∀ t ≥ (0 : ℝ), Metric.infDist (ϕ t x) Γ₁ < δa / 2 := htube x hxδ₀
  -- … hence is bounded (thickening of a compact set), hence forward-precompact
  have hbdd : Bornology.IsBounded ((fun t : ℝ => ϕ t x) '' Ici 0) := by
    apply (hΓ₁cpt.isBounded.thickening (δ := δa / 2)).subset
    rintro _ ⟨t, ht, rfl⟩
    exact (Metric.mem_thickening_iff_infDist_lt hΓ₁ne).mpr (horb t (mem_Ici.mp ht))
  have hcpt : ForwardPrecompact ϕ x := forwardPrecompact_of_isBounded ϕ x hbdd
  -- step 2: hLAN feeds T8-A — the ω-limit set lands in Γ₂
  have hω₂ : ω⁺ ϕ.toFun {x} ⊆ Γ₂ :=
    omegaLimit_subset_of_tendsto_infDist ϕ x hΓ₂closed (hΓ₁ne.mono hsub) (hlan x hxδL)
  -- step 3 (A.5): the ω-limit set lies in the CLOSED δa/2-tube, strictly
  -- inside the relative basin, so every ω-limit point is drawn to Γ₁
  have horbit_fwd : image2 ϕ.toFun (Ici 0) {x} = (fun t : ℝ => ϕ t x) '' Ici 0 := by
    rw [image2_singleton_right]
  have hLsub : ω⁺ ϕ.toFun {x} ⊆ closure ((fun t : ℝ => ϕ t x) '' Ici 0) := by
    have h := omegaLimit_subset_closure_image2 atTop ϕ.toFun {x} (Ici_mem_atTop (0 : ℝ))
    rwa [horbit_fwd] at h
  have hωtube : ω⁺ ϕ.toFun {x} ⊆ {z : E | Metric.infDist z Γ₁ ≤ δa / 2} := by
    refine hLsub.trans (closure_minimal ?_ ?_)
    · rintro _ ⟨t, ht, rfl⟩
      exact (horb t (mem_Ici.mp ht)).le
    · exact isClosed_le (Metric.continuous_infDist_pt Γ₁) continuous_const
  have hbasin : ∀ q ∈ ω⁺ ϕ.toFun {x},
      Tendsto (fun t : ℝ => Metric.infDist (ϕ t q) Γ₁) atTop (𝓝 0) := fun q hq =>
    hattr q (hω₂ hq) (lt_of_le_of_lt (hωtube hq) (half_lt_self hδa))
  -- step 4: T8-B closes — the ω-limit set collapses into Γ₁
  exact ⟨hcpt, omegaLimit_subset_of_stableRelativeTo ϕ x hΓ₁cpt.isClosed hΓ₁ne
    hcpt hω₂ hbasin hStabRel⟩

/-- **T8-D** — the rung-closing rewire: EHM-2013 Theorem 10 (compact branch)
with BOTH Appendix-A topology cores discharged. Ledger rows 23 (`hStable`)
and 24 (`hLandsInΓ₁`) collapse onto the single external core `hUSA`
(EHM-2009 Lemma 2.5, the R6 target); every other hypothesis is a standing
condition of EHM Theorems 8/10 themselves — conditions (i)
(`hStabRel`/`hAttrRel` = `AsymStableRelativeTo` unbundled), (ii) (`hLSN`,
`hLAN`), the LUB rider (`hLUB`), positive invariance, and the compact
two-set setup. -/
theorem reduction_asymptotic_stability_of_uniformSemiAttractor
    [FiniteDimensional ℝ E] (ϕ : Flow ℝ E) {Γ₁ Γ₂ : Set E}
    (hΓ₁cpt : IsCompact Γ₁) (hΓ₁ne : Γ₁.Nonempty)
    (hΓ₂closed : IsClosed Γ₂) (hsub : Γ₁ ⊆ Γ₂)
    (hfi : IsForwardInvariant ϕ.toFun Γ₁)
    (hLUB : LUBNear ϕ Γ₁)
    (hLSN : LocallyStableNear ϕ Γ₂ Γ₁)
    (hStabRel : StableRelativeTo ϕ Γ₁ Γ₂)
    (hAttrRel : AttractiveRelativeTo ϕ Γ₁ Γ₂)
    (hLAN : LocallyAttractiveNear ϕ Γ₂ Γ₁)
    (hUSA : UniformSemiAttractorRelativeTo ϕ Γ₁ Γ₂) :
    AsymStableSet ϕ Γ₁ :=
  have hStable : StableSet ϕ Γ₁ :=
    stableSet_of_uniformSemiAttractor_of_forwardInvariant ϕ hΓ₁cpt hΓ₁ne hsub hfi
      hLUB hLSN hUSA
  reduction_asymptotic_stability ϕ hStable
    (exists_forwardPrecompact_omegaLimit_subset_of_stableSet ϕ hΓ₁cpt hΓ₁ne
      hΓ₂closed hsub hStable hStabRel hAttrRel hLAN)

end Ctrllib

#print axioms Ctrllib.omegaLimit_subset_of_tendsto_infDist
#print axioms Ctrllib.omegaLimit_subset_of_stableRelativeTo
#print axioms Ctrllib.exists_forwardPrecompact_omegaLimit_subset_of_stableSet
#print axioms Ctrllib.reduction_asymptotic_stability_of_uniformSemiAttractor
