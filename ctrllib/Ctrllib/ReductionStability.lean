/-
R5 `hStable`-discharge groundwork (L-B + L-A of the EHM Theorem-6 / Lemma-22
topology cores).

The consuming rung L4a (`Ctrllib.Reduction`, `reduction_asymptotic_stability`)
takes the El-Hawwary–Maggiore Appendix-A set-stability core `hStable :
StableSet ϕ Γ₁` as a NAMED hypothesis. R5 works toward discharging it. This
file banks the two lowest-risk pieces of the Lemma-22 → Theorem-6 argument, each
sealed axiom-clean and standalone:

  L-B `exists_subseq_tendsto_mem_of_infDist_tendsto_zero` — a Bolzano–Weierstrass
    wrapper: in a finite-dimensional space, a sequence whose point-to-set
    distance to a nonempty closed BOUNDED set tends to 0 has a subsequence
    converging to a point OF that set. This is the "convergent subsequence with
    limit in Γ" step of Lemma 22 (compact branch), where compactness of Γ makes
    the escape sequence bounded for free.

  L-A `escape_sequence_of_not_stableSet` — the negation-unpacking: from
    `¬ StableSet ϕ Γ` extract one ε>0 and sequences xᵢ, tᵢ≥0 with
    infDist(xᵢ,Γ)→0 and ε ≤ infDist(ϕ tᵢ xᵢ, Γ). Pure logic (push_neg + choose +
    a reciprocal squeeze); no library topology. This is the first-exit-time-FREE
    version (`≥ ε`, not `= ε`); the `= ε` refinement is L-C's problem.

L-C (the Lemma-22 assembly + Theorem-6 finish that actually produces
`StableSet`, gluing L-A and L-B and closing the neighbourhood-tube
contradiction) is out of this lane; it is where the external EHM-2009 lemma
bites and is the second interface-cut candidate.

Recon: the corresponding local note Cascade context:
the corresponding derivation record (not bundled).
Human derivation for THIS module:
the corresponding derivation record (not bundled).
-/
import Ctrllib.Reduction
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecificLimits.Basic

open Set Filter Topology

namespace Ctrllib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## L-B — Bolzano–Weierstrass wrapper

In a finite-dimensional real normed space `E` (whence `ProperSpace E` by the
priority-900 instance `FiniteDimensional.proper_real`, unlocking Heine–Borel and
Bolzano–Weierstrass by typeclass resolution), a sequence whose point-to-set
distance to a nonempty closed bounded `Γ` tends to 0 admits a subsequence
converging to a point of `Γ`.

`Γ.Nonempty` is genuinely required, not cosmetic: `Metric.infDist x ∅ = 0`, so
for empty `Γ` the hypothesis holds vacuously while the conclusion `∃ x̄ ∈ Γ`
is false. In the intended application `Γ = Γ₁` is the compact (hence nonempty)
target set, so the hypothesis is free. -/
theorem exists_subseq_tendsto_mem_of_infDist_tendsto_zero
    [FiniteDimensional ℝ E] {Γ : Set E} (hne : Γ.Nonempty)
    (hcl : IsClosed Γ) (hbd : Bornology.IsBounded Γ)
    {x : ℕ → E} (hx : Tendsto (fun i => Metric.infDist (x i) Γ) atTop (𝓝 (0 : ℝ))) :
    ∃ xbar ∈ Γ, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 xbar) := by
  -- The tail of `x` lies in the bounded open 1-thickening of `Γ`.
  have hev : ∀ᶠ n in atTop, x n ∈ Metric.thickening 1 Γ := by
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hx) 1 one_pos
    rw [eventually_atTop]
    refine ⟨N, fun n hn => ?_⟩
    rw [Metric.mem_thickening_iff_infDist_lt hne]
    have h1 := hN n hn
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg Metric.infDist_nonneg] at h1
  -- Bolzano–Weierstrass on the bounded thickening.
  obtain ⟨a, -, φ, hφ, hlim⟩ :=
    tendsto_subseq_of_frequently_bounded hbd.thickening hev.frequently
  refine ⟨a, ?_, φ, hφ, hlim⟩
  -- The limit lands in `Γ`: `infDist a Γ = 0` by uniqueness of limits, `Γ` closed.
  rw [hcl.mem_iff_infDist_zero hne]
  have hA : Tendsto (fun i => Metric.infDist ((x ∘ φ) i) Γ) atTop
      (𝓝 (Metric.infDist a Γ)) :=
    ((Metric.continuous_infDist_pt Γ).tendsto a).comp hlim
  have hB : Tendsto (fun i => Metric.infDist ((x ∘ φ) i) Γ) atTop (𝓝 0) :=
    hx.comp hφ.tendsto_atTop
  exact tendsto_nhds_unique hA hB

/-! ## L-A — escape sequence from the negation of set-stability

Unpack `¬ StableSet ϕ Γ` into an escape ε and sequences. Pure logic: unfold the
`∀ε>0 ∃δ>0 ∀x… ∀t≥0, … < ε` predicate, `push_neg`, instantiate `δ := 1/(i+1)`,
`choose` the witnesses, and squeeze `infDist(xᵢ,Γ) < 1/(i+1) → 0` between the
nonnegativity floor and the nat-reciprocal limit. No library topology. -/
theorem escape_sequence_of_not_stableSet (ϕ : Flow ℝ E) {Γ : Set E}
    (hns : ¬ StableSet ϕ Γ) :
    ∃ ε > 0, ∃ (x : ℕ → E) (t : ℕ → ℝ),
      (∀ i, 0 ≤ t i) ∧
      Tendsto (fun i => Metric.infDist (x i) Γ) atTop (𝓝 (0 : ℝ)) ∧
      (∀ i, ε ≤ Metric.infDist (ϕ (t i) (x i)) Γ) := by
  rw [StableSet] at hns
  push_neg at hns
  obtain ⟨ε, hε, hns⟩ := hns
  -- Instantiate δ = 1/(i+1) and choose the escape witnesses.
  have hstep : ∀ i : ℕ, ∃ xi, Metric.infDist xi Γ < 1 / ((i : ℝ) + 1) ∧
      ∃ ti, ti ≥ 0 ∧ ε ≤ Metric.infDist (ϕ ti xi) Γ :=
    fun i => hns (1 / ((i : ℝ) + 1)) (by positivity)
  choose x hlt t ht hge using hstep
  refine ⟨ε, hε, x, t, ht, ?_, hge⟩
  -- Squeeze: 0 ≤ infDist(xᵢ,Γ) ≤ 1/(i+1) → 0.
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    tendsto_one_div_add_atTop_nhds_zero_nat
    (fun i => Metric.infDist_nonneg) (fun i => (hlt i).le)

end Ctrllib

#print axioms Ctrllib.exists_subseq_tendsto_mem_of_infDist_tendsto_zero
#print axioms Ctrllib.escape_sequence_of_not_stableSet
