/-
Bounded-actuation-noise ultimate bound (obligation C1, bounded case) — a thin
wiring corollary of the SEALED engine `comparison_bounded` (TimeVaryingComparison.lean).

The risk-aware program (the corresponding local note row C1, §7 item 3) needs
one quantitative fact for the bounded/truncated actuation-noise model: an actuation
disturbance under a constant ceiling ε(t) ≤ εbar keeps the closed-loop Lyapunov
value inside an explicit ultimate ball. The sealed `comparison_bounded` already
proves v(t) ≤ v(0) + M/a from v' ≤ -a·v + ε and ε ≤ M; this file specializes it to
the actuation-noise ceiling (headline seal) and reads it back onto the state through
the quadratic sandwich (`QuadSandwich`, discharged by `quadSandwich_matrix`).

No new analysis: the engine and the sandwich are both sealed elsewhere; the
regularity quartet (hvc/hv/hbound + nonnegativity) stays applier-side BY DESIGN,
exactly as in TimeVaryingComparison — see the corresponding local note.

Numeric sanity pin: the corresponding local note
Human derivation: wiki dir the corresponding derivation record (not bundled)
(no the corresponding local note page filed yet).
-/
import Ctrllib.TimeVaryingComparison
import Ctrllib.Lyapunov

open Set

namespace Ctrllib

variable {v v' ε : ℝ → ℝ} {a : ℝ}

/-- **Bounded-actuation-noise uniform bound** (obligation C1, bounded case).
A closed-loop Lyapunov value `v` driven by an actuation disturbance `ε` with the
decrease `v'(t) ≤ -a·v(t) + ε(t)` under a CONSTANT actuation-noise ceiling
`ε(t) ≤ εbar` (the bounded/truncated noise model) stays inside the explicit ball
`v(0) + εbar/a` for all `t ≥ 0`. This is a UNIFORM (for-all-time) bound that
depends on the initial value `v 0` — not an ultimate bound in Khalil's lim-sup
sense (that would be `εbar/a`, which the exponential form of the comparison lemma
would give; not proved here). Direct specialization of the sealed
`comparison_bounded` with disturbance ceiling `M := εbar`; the constant `εbar/a`
is the noise-floor level. Near-zero new proof, by design. -/
theorem actuation_ultimate_bound
    (ha : 0 < a) {εbar : ℝ} (hεbar : 0 ≤ εbar)
    (hvc : ContinuousOn v (Ici 0))
    (hv : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt v (v' t) (Ici t) t)
    (hbound : ∀ t ∈ Ici (0 : ℝ), v' t ≤ -a * v t + ε t)
    (hεbarM : ∀ t ∈ Ici (0 : ℝ), ε t ≤ εbar)
    (hv0 : 0 ≤ v 0) :
    ∀ t ∈ Ici (0 : ℝ), v t ≤ v 0 + εbar / a :=
  comparison_bounded ha hεbar hvc hv hbound hεbarM hv0

/-- **State-level residual ball.** Reading the scalar uniform bound back onto the
state through a quadratic Lyapunov sandwich `QuadSandwich V c₁ c₂`. If the Lyapunov
value along the trajectory, `t ↦ V (x t)`, obeys the comparison hypotheses under the
actuation ceiling `εbar`, then the squared state norm stays inside an explicit ball
depending on the initial state: `c₁‖x t‖² ≤ c₂‖x 0‖² + εbar/a` for all `t ≥ 0`
(a uniform bound, not a lim-sup ultimate bound). One-line composition of
`actuation_ultimate_bound` with the sandwich (the sandwich is discharged for the
concrete SPD matrix model by `quadSandwich_matrix`). Dividing by `c₁ > 0` gives the
familiar residual-set radius; stated division-free. -/
theorem actuation_state_ball
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {V : E → ℝ} {x : ℝ → E} {c₁ c₂ : ℝ}
    (ha : 0 < a) {εbar : ℝ} (hεbar : 0 ≤ εbar)
    (hsand : QuadSandwich V c₁ c₂)
    (hvc : ContinuousOn (fun t => V (x t)) (Ici 0))
    (hv : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt (fun t => V (x t)) (v' t) (Ici t) t)
    (hbound : ∀ t ∈ Ici (0 : ℝ), v' t ≤ -a * V (x t) + ε t)
    (hεbarM : ∀ t ∈ Ici (0 : ℝ), ε t ≤ εbar)
    (hv0 : 0 ≤ V (x 0)) :
    ∀ t ∈ Ici (0 : ℝ), c₁ * ‖x t‖ ^ 2 ≤ c₂ * ‖x 0‖ ^ 2 + εbar / a := by
  intro t ht
  have hub : V (x t) ≤ V (x 0) + εbar / a :=
    actuation_ultimate_bound (v := fun s => V (x s)) ha hεbar hvc hv hbound hεbarM hv0 t ht
  have hlow := (hsand (x t)).1
  have hupp := (hsand (x 0)).2
  linarith

end Ctrllib

#print axioms Ctrllib.actuation_ultimate_bound
#print axioms Ctrllib.actuation_state_ball
