/-
LaSalle's invariance principle (L3 sub-phases i + ii of the ctrllib stream).

Mathlib's Dynamics library already holds three of the four stones:
ω-limit invariance (`Flow.isInvariant_omegaLimit`, monoid-level), nonemptiness
over compact absorbers (`nonempty_omegaLimit_of_isCompact_absorbing`), and
attraction (`eventually_mapsTo_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset`).
Missing — and added here — is the Lyapunov-specific pair: V is CONSTANT on
ω-limit sets, and (through the ODE bridge) the Lyapunov derivative VANISHES
there.

Sub-phase (i), the ODE-solutions-to-flow bridge, is an interface, not a
construction: `IsSolutionTo ϕ f` says every orbit of the given flow is
differentiable with derivative given by the field. How such a flow arises on
the region of interest (Picard–Lindelöf, completeness on Ω) deliberately
stays on the applier's side of the Prop — the documented design choice.

giordano2019coordinated Prop IV.1 proof (verbatim): "Applying LaSalle to
(34b), v̆ ≡ 0 implies x̃ = 0" — the theorems below are that step's engine.

Human derivation: the corresponding derivation record (not bundled)
-/
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Dynamics.OmegaLimit
import Ctrllib.Lyapunov

open Set Filter Topology omegaLimit

namespace Ctrllib

section Constancy

variable {τ α : Type*} [TopologicalSpace α]

/-- The stone LaSalle needs beyond Mathlib's invariance: a continuous
function converging along the orbit is constant on the ω-limit set. Stated
for any map family `ϕ : τ → α → α` and any nontrivial filter. -/
theorem eq_on_omegaLimit_of_tendsto {f : Filter τ} [f.NeBot] {ϕ : τ → α → α}
    {x₀ : α} {V : α → ℝ} {c : ℝ} (hV : Continuous V)
    (hc : Tendsto (fun t => V (ϕ t x₀)) f (𝓝 c)) :
    ∀ y ∈ omegaLimit f ϕ {x₀}, V y = c := by
  intro y hy
  rw [mem_omegaLimit_singleton_iff_mapClusterPt] at hy
  have h2 : MapClusterPt (V y) f (V ∘ fun t => ϕ t x₀) :=
    hy.continuousAt_comp hV.continuousAt
  exact t2_iff_nhds.mp inferInstance (h2.clusterPt.mono hc)

end Constancy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- ODE-solutions-to-flow bridge (interface form): the flow `ϕ` solves
`x' = f x` when every orbit is everywhere differentiable with derivative
given by the field. -/
def IsSolutionTo (ϕ : Flow ℝ E) (f : E → E) : Prop :=
  ∀ (x : E) (t : ℝ), HasDerivAt (fun s => ϕ s x) (f (ϕ t x)) t

/-- Forward-orbit precompactness — the FORWARD-ONLY replacement for two-sided
orbit precompactness. The closure of the forward orbit `{ϕ t x₀ : t ≥ 0}` is
compact. Strictly weaker (more honest) than `IsCompact (closure (range fun t : ℝ
=> ϕ t x₀))`: a stable system's BACKWARD orbit is unbounded, so full two-sided
precompactness is more than a Lyapunov argument supplies, while the forward orbit
is bounded by coercivity of `V` (the sealed `blockLyap_coercive` is the witness).
The `ω⁺` (forward) ω-limit argument needs exactly this and no more. -/
abbrev ForwardPrecompact (ϕ : Flow ℝ E) (x₀ : E) : Prop :=
  IsCompact (closure ((fun t : ℝ => ϕ t x₀) '' Set.Ici 0))

omit [NormedSpace ℝ E] in
/-- **Boundedness discharges `ForwardPrecompact`** in a proper (e.g. finite-
dimensional) state space: a bounded forward orbit has compact closure. This is
the topological heart of the discharge — it reduces the forward-precompactness
interface to mere boundedness of the forward orbit. -/
theorem forwardPrecompact_of_isBounded [ProperSpace E] (ϕ : Flow ℝ E) (x₀ : E)
    (hbdd : Bornology.IsBounded ((fun t : ℝ => ϕ t x₀) '' Set.Ici 0)) :
    ForwardPrecompact ϕ x₀ :=
  hbdd.isCompact_closure

omit [NormedSpace ℝ E] in
/-- **Coercivity discharges `ForwardPrecompact`** (the sealed witness). If `V` is
norm-coercive (`c₁‖y‖² ≤ V y`, `c₁ > 0` — the shape `blockLyap_coercive`
provides) and nonincreasing along the forward orbit (`V(ϕ t x₀) ≤ V x₀` for
`t ≥ 0`, which the Lyapunov decrease integrates), then the forward orbit lies in
the bounded sublevel set `{V ≤ V x₀}`, so in a proper state space it is forward-
precompact. This is exactly "a stable system's backward orbit blows up, but
forward coercivity confines the forward orbit" made precise — no two-sided
precompactness assumed. -/
theorem forwardPrecompact_of_coercive [ProperSpace E] (ϕ : Flow ℝ E) (x₀ : E)
    {V : E → ℝ} {c₁ : ℝ} (hc₁ : 0 < c₁) (hcoer : ∀ y, c₁ * ‖y‖ ^ 2 ≤ V y)
    (horbit : ∀ t : ℝ, 0 ≤ t → V (ϕ t x₀) ≤ V x₀) :
    ForwardPrecompact ϕ x₀ := by
  apply forwardPrecompact_of_isBounded
  apply (Metric.isBounded_closedBall (x := (0 : E)) (r := V x₀ / c₁ + 1)).subset
  rintro _ ⟨t, ht, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  have h1 : c₁ * ‖ϕ t x₀‖ ^ 2 ≤ V x₀ := (hcoer _).trans (horbit t ht)
  have h2 : ‖ϕ t x₀‖ ^ 2 ≤ V x₀ / c₁ := by rw [le_div_iff₀ hc₁]; nlinarith [h1]
  nlinarith [sq_nonneg (‖ϕ t x₀‖ - 1), sq_nonneg ‖ϕ t x₀‖, norm_nonneg (ϕ t x₀), h2]

/-- Chain rule along an orbit: the bridge's consumption lemma. -/
theorem IsSolutionTo.hasDerivAt_comp {ϕ : Flow ℝ E} {f : E → E}
    (hϕ : IsSolutionTo ϕ f) {V : E → ℝ} (hV : Differentiable ℝ V)
    (x : E) (t : ℝ) :
    HasDerivAt (fun s => V (ϕ s x)) (fderiv ℝ V (ϕ t x) (f (ϕ t x))) t :=
  HasFDerivAt.comp_hasDerivAt t (hV (ϕ t x)).hasFDerivAt (hϕ x t)

/-- LaSalle's invariance principle at flow level. For a flow solving
`x' = f x`, a differentiable `V` nonincreasing along the field, and a point
with precompact orbit closure: the ω-limit set is nonempty, invariant, `V`
is constant on it, and the Lyapunov derivative vanishes on it. Mathlib
supplies invariance and nonemptiness; constancy and derivative-vanishing are
the LaSalle-specific stones. -/
theorem lasalle (ϕ : Flow ℝ E) {f : E → E} (hϕ : IsSolutionTo ϕ f)
    {V : E → ℝ} (hV : Differentiable ℝ V)
    (hdec : ∀ y, fderiv ℝ V y (f y) ≤ 0) (x₀ : E)
    (hcpt : ForwardPrecompact ϕ x₀) :
    (ω⁺ ϕ.toFun {x₀}).Nonempty ∧
      IsInvariant ϕ.toFun (ω⁺ ϕ.toFun {x₀}) ∧
      (∀ y ∈ ω⁺ ϕ.toFun {x₀}, V y = ⨅ t : ℝ, V (ϕ t x₀)) ∧
      ∀ y ∈ ω⁺ ϕ.toFun {x₀}, fderiv ℝ V y (f y) = 0 := by
  have hshift : ∀ t : ℝ, Tendsto (t + ·) (atTop : Filter ℝ) atTop := fun t =>
    tendsto_atTop_add_const_left atTop t tendsto_id
  have horbit_fwd : image2 ϕ.toFun (Ici 0) {x₀} = (fun t : ℝ => ϕ t x₀) '' Ici 0 := by
    rw [image2_singleton_right]
  have hnonempty : (ω⁺ ϕ.toFun {x₀}).Nonempty :=
    nonempty_omegaLimit_of_isCompact_absorbing atTop ϕ.toFun {x₀} hcpt
      ⟨Ici 0, Ici_mem_atTop 0, le_of_eq (congrArg closure horbit_fwd)⟩
      (singleton_nonempty x₀)
  have hinv : IsInvariant ϕ.toFun (ω⁺ ϕ.toFun {x₀}) :=
    ϕ.isInvariant_omegaLimit atTop {x₀} hshift
  have hg_diff : Differentiable ℝ fun t : ℝ => V (ϕ t x₀) := fun t =>
    (hϕ.hasDerivAt_comp hV x₀ t).differentiableAt
  have hg_deriv : ∀ t : ℝ, deriv (fun t : ℝ => V (ϕ t x₀)) t ≤ 0 := fun t => by
    rw [(hϕ.hasDerivAt_comp hV x₀ t).deriv]
    exact hdec _
  have hmono : Antitone fun t : ℝ => V (ϕ t x₀) :=
    antitone_of_deriv_nonpos hg_diff hg_deriv
  -- Forward-only precompactness bounds `V` below on the forward orbit; the
  -- backward orbit is handled by antitonicity (`V(ϕ t x₀) ≥ V(x₀)` for `t ≤ 0`),
  -- so the same bound serves the whole two-sided range.
  have hbdd : BddBelow (range fun t : ℝ => V (ϕ t x₀)) := by
    obtain ⟨b, hb⟩ := (hcpt.image hV.continuous).bddBelow
    refine ⟨b, ?_⟩
    rintro _ ⟨t, rfl⟩
    rcases le_total (0 : ℝ) t with ht | ht
    · exact hb ⟨ϕ t x₀, subset_closure ⟨t, mem_Ici.mpr ht, rfl⟩, rfl⟩
    · have h0 : V (ϕ (0 : ℝ) x₀) ≤ V (ϕ t x₀) := hmono ht
      have hb0 : b ≤ V (ϕ (0 : ℝ) x₀) :=
        hb ⟨ϕ 0 x₀, subset_closure ⟨0, mem_Ici.mpr le_rfl, rfl⟩, rfl⟩
      linarith
  have hlim : Tendsto (fun t : ℝ => V (ϕ t x₀)) atTop
      (𝓝 (⨅ t : ℝ, V (ϕ t x₀))) := tendsto_atTop_ciInf hmono hbdd
  have hconst : ∀ y ∈ ω⁺ ϕ.toFun {x₀}, V y = ⨅ t : ℝ, V (ϕ t x₀) :=
    eq_on_omegaLimit_of_tendsto hV.continuous hlim
  refine ⟨hnonempty, hinv, hconst, fun y hy => ?_⟩
  have horb : ∀ t : ℝ, V (ϕ t y) = ⨅ t : ℝ, V (ϕ t x₀) := fun t =>
    hconst _ (hinv t hy)
  have hconst_fun : (fun s : ℝ => V (ϕ s y)) = fun _ => ⨅ t : ℝ, V (ϕ t x₀) :=
    funext horb
  have hzero : HasDerivAt (fun s : ℝ => V (ϕ s y)) 0 0 := by
    rw [hconst_fun]
    exact hasDerivAt_const _ _
  have huniq := (hϕ.hasDerivAt_comp hV y 0).unique hzero
  simpa [ϕ.map_zero_apply] using huniq

omit [NormedSpace ℝ E] in
/-- Attraction: the orbit eventually enters any open neighbourhood of its
ω-limit set — Mathlib's compact-absorbing machinery, specialized to a point
orbit. Together with `lasalle` this is the classical principle. -/
theorem eventually_mem_of_omegaLimit_subset (ϕ : Flow ℝ E) (x₀ : E)
    (hcpt : ForwardPrecompact ϕ x₀)
    {u : Set E} (hu : IsOpen u) (hsub : ω⁺ ϕ.toFun {x₀} ⊆ u) :
    ∀ᶠ t in (atTop : Filter ℝ), ϕ t x₀ ∈ u := by
  have habs : ∀ᶠ t in (atTop : Filter ℝ),
      MapsTo (ϕ.toFun t) {x₀} (closure ((fun s : ℝ => ϕ s x₀) '' Set.Ici 0)) := by
    rw [eventually_atTop]
    refine ⟨0, fun t ht x hx => ?_⟩
    rw [mem_singleton_iff] at hx
    subst hx
    exact subset_closure ⟨t, mem_Ici.mpr ht, rfl⟩
  have h := eventually_mapsTo_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset
    atTop ϕ.toFun {x₀} hcpt habs hu hsub
  exact h.mono fun t ht => ht (mem_singleton x₀)

end Ctrllib

#print axioms Ctrllib.eq_on_omegaLimit_of_tendsto
#print axioms Ctrllib.lasalle
#print axioms Ctrllib.eventually_mem_of_omegaLimit_subset
#print axioms Ctrllib.forwardPrecompact_of_isBounded
#print axioms Ctrllib.forwardPrecompact_of_coercive
