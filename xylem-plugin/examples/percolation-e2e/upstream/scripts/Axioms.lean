import Percolation
import Solution

/-! Axiom listing for the main theorems. Run from the repository root:
`lake env lean scripts/Axioms.lean`. Expected: only `propext`, `Classical.choice`, `Quot.sound`. -/

set_option pp.fullNames true
set_option format.width 400

#check @Percolation.Continuity.CSH.percolationContinuity_allDimensions
#print axioms Percolation.Continuity.CSH.percolationContinuity_allDimensions
#check @Percolation.Continuity.CSH.percolationContinuity_three
#print axioms Percolation.Continuity.CSH.percolationContinuity_three
#check @Percolation.Continuity.CSH.kozmaNitzan_conjecture3_holds
#print axioms Percolation.Continuity.CSH.kozmaNitzan_conjecture3_holds
#check @Percolation.Continuity.CSH.additiveGluing_holds
#print axioms Percolation.Continuity.CSH.additiveGluing_holds
#check @Percolation.Continuity.CSH.cshHolds
#print axioms Percolation.Continuity.CSH.cshHolds
#check @BondPercolation.percolation_continuity
#print axioms BondPercolation.percolation_continuity
#check @BondPercolation.percolation_continuity_Z3
#print axioms BondPercolation.percolation_continuity_Z3
