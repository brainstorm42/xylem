import Percolation.Continuity.Statements

/-!
# `AdditiveGluingSuffices`: the additive gluing inequality implies near-one gluing

The additive gluing inequality `P(o ↔ b) ≥ P(o ↔ A) − t` (for any slack `t ≥ max_{a ∈ A} P(a ↮ b)`)
implies Kozma–Nitzan near-one gluing (Conjecture 3 form) with `δ = ε / 2`: apply the additive
inequality with `t = ε / 2`.
-/

namespace Percolation.Continuity

open Percolation.Continuity.Statements

/-- **AdditiveGluing ⇒ NearOneGluing** with `δ = ε / 2`.
Given `ε > 0`, put `δ := ε / 2`.  If `P(o ↔ A) > 1 − δ` and `P(a ↔ b) > 1 − δ` for all `a ∈ A`,
the additive gluing inequality with slack `t := ε / 2` gives
`P(o ↔ b) ≥ P(o ↔ A) − ε/2 > 1 − ε/2 − ε/2 = 1 − ε`. -/
theorem additiveGluingSuffices_proof : AdditiveGluingSuffices := by
  unfold AdditiveGluingSuffices
  intro hAG ε hε
  refine ⟨ε / 2, by positivity, ?_⟩
  intro n w A o b hoA hAb
  have key := hAG n w A o b (ε / 2) (by positivity) (fun a ha => (hAb a ha).le)
  linarith

end Percolation.Continuity
