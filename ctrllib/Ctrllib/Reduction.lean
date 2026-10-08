/-
El-Hawwary–Maggiore reduction step (L4a of the ctrllib stream).

The framing paper's Prop IV.1 (giordano2019coordinated §IV.D) closes its
cascade proof with "cascade theorems for compact invariant sets [13]", where
[13] = El-Hawwary & Maggiore, "Reduction theorems for stability of closed sets
with application to backstepping control design", Automatica 49(1):214–222,
2013 (bibkey elhawwary2013reduction). This file formalizes the piece of that
reduction Prop IV.1 actually consumes and wires the sealed L3 `lasalle` output
through it to the paper's conclusion.

WHAT IS PROVEN (real content, non-vacuous):
  `tendsto_infDist_of_omegaLimit_subset` — the reduction engine: if a
    precompact orbit's ω-limit set lies in a set Γ, the trajectory converges
    to Γ (infDist → 0). This is the "converges to the largest invariant
    subset" clause; it is what turns lasalle's invariant-set output into
    convergence to the invariant target.
  `reduction_asymptotic_stability` — EHM Theorem 10 (asymptotic-stability
    conclusion), compact-Γ₁ branch, ASSEMBLED form: attractivity is derived
    from the engine; the two topological cores EHM prove in their Appendix A
    (the ε–δ set stability, and the relative-attraction collapse placing
    ω-limits inside Γ₁) enter as NAMED hypotheses — the `IsSolutionTo`
    interface precedent from L3, not a silent `sorry`.
  `propIV1_tendsto` — Prop IV.1 assembly: feeds the L3 `lasalle` derivative-
    vanishing output through the engine to conclude the trajectory converges
    to the invariant set Γ₁, given the application-specific zero-set
    containment {y : DV[f] y = 0} ⊆ Γ₁ (the paper's "v̆ ≡ 0 implies x̃ = 0"
    step, which needs the un-formalized closed-loop field and so enters as a
    named hypothesis).

INTERFACED, NOT PROVEN (flagged, per the charter's documented fallback and the
L3 retreat precedent
the corresponding derivation record (not bundled)):
  - The EHM Appendix-A topological reduction (Theorem 6 stability ε–δ; the
    Lemma-22 relative-attraction collapse). These are Prop IV.1's cited [13]
    engine; here they are the named hypotheses `hStable` / `hLandsInΓ₁`, and
    in `propIV1_tendsto` the named `hzero`. The compact-Γ₁ branch is the only
    branch Prop IV.1 uses (T^n compact ⇒ the LUB rider is vacuous).

T1 predicate definitions below (`StableSet`, relative forms, `LocallyStableNear`,
`LocallyAttractiveNear`, `LUBNear`) transcribe EHM Definitions 1/3/4/5 verbatim
in ε–δ form, for the record and to type the interface hypotheses.

Human derivation: the corresponding derivation record (not bundled)
-/
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Ctrllib.LaSalle

open Set Filter Topology omegaLimit

namespace Ctrllib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## T1 — set-stability predicates (interface, EHM Definitions 1/3/4/5)

These type the interface hypotheses and record the EHM notions. `Metric.infDist
x Γ` is the point-to-set distance; `Metric.infDist x Γ < δ` is EHM's `x ∈
B_δ(Γ)`. Nothing here is proven; these are definitions. -/

/-- EHM Def 1(i), set form: `Γ` is stable — every ε-neighbourhood of `Γ`
admits a δ-neighbourhood forward-mapped into it. -/
def StableSet (ϕ : Flow ℝ E) (Γ : Set E) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, Metric.infDist x Γ < δ →
    ∀ t ≥ (0 : ℝ), Metric.infDist (ϕ t x) Γ < ε

/-- EHM Def 1(ii), set form: a neighbourhood of `Γ` is attracted to `Γ`. -/
def AttractiveSet (ϕ : Flow ℝ E) (Γ : Set E) : Prop :=
  ∃ δ > 0, ∀ x, Metric.infDist x Γ < δ →
    Tendsto (fun t : ℝ => Metric.infDist (ϕ t x) Γ) atTop (𝓝 0)

/-- EHM Def 1(v): asymptotic stability of a set = stability + attractivity. -/
def AsymStableSet (ϕ : Flow ℝ E) (Γ : Set E) : Prop :=
  StableSet ϕ Γ ∧ AttractiveSet ϕ Γ

/-- EHM Def 4: `Γ₁` is stable relative to `Γ₂` — the ε–δ of `StableSet` with
initial conditions restricted to `Γ₂`. -/
def StableRelativeTo (ϕ : Flow ℝ E) (Γ₁ Γ₂ : Set E) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x ∈ Γ₂, Metric.infDist x Γ₁ < δ →
    ∀ t ≥ (0 : ℝ), Metric.infDist (ϕ t x) Γ₁ < ε

/-- EHM Def 4: `Γ₁` is attractive relative to `Γ₂`. -/
def AttractiveRelativeTo (ϕ : Flow ℝ E) (Γ₁ Γ₂ : Set E) : Prop :=
  ∃ δ > 0, ∀ x ∈ Γ₂, Metric.infDist x Γ₁ < δ →
    Tendsto (fun t : ℝ => Metric.infDist (ϕ t x) Γ₁) atTop (𝓝 0)

/-- EHM Def 4: relative asymptotic stability — the cascade step's input
hypothesis (condition (i) of Theorem 10 / (iv) of Corollary 12). -/
def AsymStableRelativeTo (ϕ : Flow ℝ E) (Γ₁ Γ₂ : Set E) : Prop :=
  StableRelativeTo ϕ Γ₁ Γ₂ ∧ AttractiveRelativeTo ϕ Γ₁ Γ₂

/-- EHM Def 3: `Γ₂` is locally stable near `Γ₁` — trajectories from a
neighbourhood of `Γ₁` cannot leave a neighbourhood of `Γ₂` before first
leaving a ball at a point of `Γ₁`. -/
def LocallyStableNear (ϕ : Flow ℝ E) (Γ₂ Γ₁ : Set E) : Prop :=
  ∀ p ∈ Γ₁, ∀ c > 0, ∀ ε > 0, ∃ δ > 0, ∀ x₀, Metric.infDist x₀ Γ₁ < δ →
    ∀ t > (0 : ℝ), (∀ s ∈ Set.Icc (0 : ℝ) t, dist (ϕ s x₀) p < c) →
      ∀ s ∈ Set.Icc (0 : ℝ) t, Metric.infDist (ϕ s x₀) Γ₂ < ε

/-- EHM Def 3: `Γ₂` is locally attractive near `Γ₁` — a neighbourhood of `Γ₁`
is attracted to `Γ₂`. -/
def LocallyAttractiveNear (ϕ : Flow ℝ E) (Γ₂ Γ₁ : Set E) : Prop :=
  ∃ δ > 0, ∀ x, Metric.infDist x Γ₁ < δ →
    Tendsto (fun t : ℝ => Metric.infDist (ϕ t x) Γ₂) atTop (𝓝 0)

/-- EHM Def 5: local uniform boundedness near `Γ` — each point of `Γ` has a
ball whose forward orbit stays bounded. The rider needed only when the target
set is unbounded (vacuous for the compact `z̄` of Prop IV.1). -/
def LUBNear (ϕ : Flow ℝ E) (Γ : Set E) : Prop :=
  ∀ p ∈ Γ, ∃ lam > 0, ∃ m > 0, ∀ y, dist y p < lam →
    ∀ t ≥ (0 : ℝ), dist (ϕ t y) p < m

/-! ## The reduction engine (proved) -/

omit [NormedSpace ℝ E] in
/-- Reduction engine: if a precompact orbit's ω-limit set lies in `Γ`, the
trajectory converges to `Γ` (point-to-set distance → 0). No closedness of `Γ`
is needed. Built on L3's `eventually_mem_of_omegaLimit_subset` (Mathlib's
compact-absorbing attraction machinery). This is the step that turns
`lasalle`'s invariant-set output into convergence to the invariant target.

(`NormedSpace` omitted: the engine uses only the metric structure and L3's
`eventually_mem_of_omegaLimit_subset`, which itself omits it.) -/
theorem tendsto_infDist_of_omegaLimit_subset (ϕ : Flow ℝ E) (x₀ : E)
    (hcpt : ForwardPrecompact ϕ x₀)
    {Γ : Set E} (hsub : ω⁺ ϕ.toFun {x₀} ⊆ Γ) :
    Tendsto (fun t : ℝ => Metric.infDist (ϕ t x₀) Γ) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hopen : IsOpen {z : E | Metric.infDist z Γ < ε} :=
    isOpen_lt (Metric.continuous_infDist_pt Γ) continuous_const
  have hsubu : ω⁺ ϕ.toFun {x₀} ⊆ {z : E | Metric.infDist z Γ < ε} := fun y hy => by
    rw [Set.mem_setOf_eq, Metric.infDist_zero_of_mem (hsub hy)]
    exact hε
  have hev := eventually_mem_of_omegaLimit_subset ϕ x₀ hcpt hopen hsubu
  rw [eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  refine ⟨N, fun n hn => ?_⟩
  have hlt : Metric.infDist (ϕ n x₀) Γ < ε := hN n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg Metric.infDist_nonneg]
  exact hlt

/-! ## T2 — EHM Theorem 10, compact-Γ₁ branch, assembled -/

omit [NormedSpace ℝ E] in
/-- EHM Theorem 10 (asymptotic-stability conclusion), compact-`Γ₁` branch,
assembled form. The two topological cores EHM prove in Appendix A enter as
named hypotheses (the L3 `IsSolutionTo` interface precedent):
  `hStable`     — the ε–δ set stability (EHM Theorem 6, compact branch);
  `hLandsInΓ₁`  — the relative-attraction collapse: on a neighbourhood of `Γ₁`
                  orbits are precompact and their ω-limit sets lie in `Γ₁`
                  (EHM Theorem 8, Appendix A.2, self-contained; the older
                  "Lemma 22" attribution was imprecise — Lemma 22 lives in
                  A.1's Proof of Theorem 6 and A.2 never uses it).
What is PROVEN is the assembly: `hLandsInΓ₁` fed through the reduction engine
yields `AttractiveSet`, which with `hStable` gives `AsymStableSet`. The
attractivity conclusion is genuine reduction content, not assumed. -/
theorem reduction_asymptotic_stability (ϕ : Flow ℝ E) {Γ₁ : Set E}
    (hStable : StableSet ϕ Γ₁)
    (hLandsInΓ₁ : ∃ δ > 0, ∀ x, Metric.infDist x Γ₁ < δ →
      ForwardPrecompact ϕ x ∧ ω⁺ ϕ.toFun {x} ⊆ Γ₁) :
    AsymStableSet ϕ Γ₁ := by
  refine ⟨hStable, ?_⟩
  obtain ⟨δ, hδ, hx⟩ := hLandsInΓ₁
  refine ⟨δ, hδ, fun x hxδ => ?_⟩
  exact tendsto_infDist_of_omegaLimit_subset ϕ x (hx x hxδ).1 (hx x hxδ).2

/-! ## T3 — Prop IV.1 assembly: lasalle → engine → convergence -/

/-- Prop IV.1 assembly. Wiring the sealed L3 `lasalle` output through the
reduction engine: for a flow solving `x' = f x`, a differentiable Lyapunov `V`
nonincreasing along the field (the framing paper's eq 37/38, `DV[f] = -v̆ᵀD̆v̆
≤ 0`), and the application-specific zero-set containment
`{y : DV[f] y = 0} ⊆ Γ₁` (the paper's "v̆ ≡ 0 implies x̃ = 0" step, needing the
un-formalized closed-loop field, hence a named hypothesis `hzero`), any
precompact orbit converges to the invariant set `Γ₁ = z̄`. `lasalle` supplies
`DV[f] = 0` on the ω-limit set; `hzero` places that ω-limit set inside `Γ₁`;
the engine delivers convergence — exactly Prop IV.1's attractivity conclusion. -/
theorem propIV1_tendsto (ϕ : Flow ℝ E) {f : E → E} (hϕ : IsSolutionTo ϕ f)
    {V : E → ℝ} (hV : Differentiable ℝ V)
    (hdec : ∀ y, fderiv ℝ V y (f y) ≤ 0)
    {Γ₁ : Set E} (hzero : {y : E | fderiv ℝ V y (f y) = 0} ⊆ Γ₁)
    (x₀ : E) (hcpt : ForwardPrecompact ϕ x₀) :
    Tendsto (fun t : ℝ => Metric.infDist (ϕ t x₀) Γ₁) atTop (𝓝 0) := by
  have hlas := lasalle ϕ hϕ hV hdec x₀ hcpt
  have hsub : ω⁺ ϕ.toFun {x₀} ⊆ Γ₁ := fun y hy => hzero (hlas.2.2.2 y hy)
  exact tendsto_infDist_of_omegaLimit_subset ϕ x₀ hcpt hsub

end Ctrllib

#print axioms Ctrllib.tendsto_infDist_of_omegaLimit_subset
#print axioms Ctrllib.reduction_asymptotic_stability
#print axioms Ctrllib.propIV1_tendsto
