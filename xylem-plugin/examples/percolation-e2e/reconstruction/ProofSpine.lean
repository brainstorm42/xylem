import Solution

/-!
Checked reconstruction witnesses for the compiler-derived percolation proof spine.

Each example below is intentionally small: the exact theorem constants and
applications are checked by Lean 4.32.0, while compact application/reference
evidence and separate boundary Expr trees are retained in the proof-trace
artifacts. These witnesses do not claim to inline opaque theorem bodies or to
replace human mathematical exposition.
-/

noncomputable section

open Percolation.Literature
open Percolation.Literature.LatticeModels
open Percolation.Continuity
open Percolation.Continuity.Statements

namespace PercolationProofSpine

-- Public Solution surface -> the all-dimensional formal endpoint.
example (d : ℕ) (hd : 2 ≤ d) : BondPercolation.PercolationContinuity d :=
  (BondPercolation.bridge d).mpr
    (Percolation.Continuity.CSH.percolationContinuity_allDimensions d hd)

-- CSH interface -> the formal all-dimensional endpoint.
example (d : ℕ) (hd : 2 ≤ d) : PercolationContinuity d :=
  Percolation.Continuity.CSH.percolationContinuity_of_csh
    Percolation.Continuity.CSH.cshAll d hd

-- The CSH theorem supplies the additive gluing proposition.
example : Percolation.Continuity.Statements.AdditiveGluing :=
  Percolation.Continuity.CSH.additiveGluing_holds

-- Additive gluing supplies the formal endpoint through the generated near-one bridge.
example (d : ℕ) (hd : 2 ≤ d) : PercolationContinuity d :=
  Percolation.Continuity.percolationContinuity_of_additiveGluing
    Percolation.Continuity.CSH.additiveGluing_holds d hd

-- The definitionally aligned NearOne/Conjecture-3 bridge is used in the direction
-- required by the endpoint theorem; this is not an independent literature check.
example (d : ℕ) (hd : 2 ≤ d) : PercolationContinuity d :=
  Percolation.Continuity.percolationContinuity_of_nearOneGluing
    (Percolation.Continuity.nearOneGluing_iff_conjecture3.2
      Percolation.Continuity.CSH.kozmaNitzan_conjecture3_holds) d hd

-- The independently captured Theorem-6 endpoint and its explicit two-input route.
example : KozmaNitzan2024_thm6 :=
  KozmaNitzan2024_thm6_holds

example : KozmaNitzan2024_thm6 :=
  KozmaNitzan2024_thm6_holds_of
    KozmaNitzan2024_slabPercolation_holds
    theta_slab_criticalProb_zd_eq_zero_holds

-- The formal endpoint is the exact theta(p_c)=0 proposition, not a stronger
-- continuity theorem inferred from the surrounding source prose.
example (d : ℕ) (hd : 2 ≤ d) :
    theta (zdGraph d) (0 : LatticeModels.Site d) (criticalProbI d) = 0 :=
  Percolation.Continuity.CSH.percolationContinuity_allDimensions d hd

end PercolationProofSpine
