import Percolation.Continuity.AdditiveGluing.Suffices

/-!
# `AdditiveGluingGlue`: the additive gluing inequality implies near-one gluing

The additive gluing inequality `AdditiveGluing` implies
`NearOneGluing` (Kozma–Nitzan near-one gluing, Conjecture 3 form) with `δ = ε / 2`.
The statement `AdditiveGluingGlue := AdditiveGluing → NearOneGluing` is definitionally the
already-proved `AdditiveGluingSuffices`, so the proof
is a direct application of `additiveGluingSuffices_proof`.
-/

namespace Percolation.Continuity

open Percolation.Continuity.Statements

/-- **AdditiveGluing ⇒ NearOneGluing** (`δ = ε / 2`): unfold the definition and
apply `additiveGluingSuffices_proof`, whose statement is
definitionally `AdditiveGluing → NearOneGluing`. -/
theorem additiveGluingGlue_proof : AdditiveGluingGlue := by
  unfold AdditiveGluingGlue
  intro hAG
  exact additiveGluingSuffices_proof hAG

end Percolation.Continuity
