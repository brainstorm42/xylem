import Percolation.Continuity.AdditiveGluing.Glue
import Percolation.Literature.KozmaNitzanTheorem6SlabCritical

/-!
# θ(p_c) = 0 on ℤ^d, d ≥ 2, from near-one gluing (Kozma–Nitzan's Theorem 6) and from additive gluing

Kozma–Nitzan's Theorem 6 — "if Conjecture 3 holds then `P_{p_c}(|C(0)| = ∞) = 0` on `ℤ^d` for every
`d ≥ 2`" — is the unconditional theorem
`Percolation.Literature.KozmaNitzan2024_thm6_holds` (its slab input `θ_{S_k}(p_c(ℤ^d)) =
0` comes from the Barsky–Grimmett–Newman half-space theorem `BarskyGrimmettNewman1991_holds`).

* `nearOneGluing_iff_conjecture3` — `NearOneGluing` is, verbatim, Kozma–Nitzan's Conjecture 3
  (`Percolation.Literature.KozmaNitzan2024_conjecture3`);
* `percolationContinuity_of_nearOneGluing` — `NearOneGluing → ∀ d ≥ 2, PercolationContinuity d`;
* `percolationContinuity_of_additiveGluing` — likewise for the additive gluing inequality
  `AdditiveGluing` (`P(o ↔ b) ≥ P(o ↔ A) − t` whenever `P(a ↔ b) ≥ 1 − t` for all `a ∈ A`), through
  `additiveGluingGlue_proof : AdditiveGluing → NearOneGluing`;

[cite: KozmaNitzan2024, Conj. 3 and Thm. 6 (p. 15)]
-/

namespace Percolation.Continuity

open Percolation.Continuity.Statements
open Percolation.Literature

/-- `NearOneGluing` is verbatim Kozma–Nitzan's Conjecture 3 (arXiv:2401.12397, p. 15) as stated in
`Percolation.Literature.KozmaNitzan2024_conjecture3`. [cite: KozmaNitzan2024, Conj. 3 (p. 15)] -/
theorem nearOneGluing_iff_conjecture3 :
    Percolation.Continuity.Statements.NearOneGluing ↔ KozmaNitzan2024_conjecture3 :=
  Iff.rfl

/-- **Near-one gluing implies `θ_{ℤ^d}(p_c(ℤ^d)) = 0` for every `d ≥ 2`**: Kozma–Nitzan's Theorem 6
(the unconditional theorem `KozmaNitzan2024_thm6_holds`) applied to `NearOneGluing`.
[cite: KozmaNitzan2024, Thm. 6 (p. 15)] -/
theorem percolationContinuity_of_nearOneGluing (hX : Percolation.Continuity.Statements.NearOneGluing)
    (d : ℕ) (hd : 2 ≤ d) : PercolationContinuity d :=
  KozmaNitzan2024_thm6_holds (nearOneGluing_iff_conjecture3.1 hX) d hd

/-- **The additive gluing inequality implies `θ_{ℤ^d}(p_c(ℤ^d)) = 0` for every `d ≥ 2`**:
`additiveGluingGlue_proof : AdditiveGluing → NearOneGluing` (take `δ = ε / 2`) followed by
`percolationContinuity_of_nearOneGluing`. -/
theorem percolationContinuity_of_additiveGluing (h : Percolation.Continuity.Statements.AdditiveGluing)
    (d : ℕ) (hd : 2 ≤ d) : PercolationContinuity d :=
  percolationContinuity_of_nearOneGluing (additiveGluingGlue_proof h) d hd

end Percolation.Continuity
