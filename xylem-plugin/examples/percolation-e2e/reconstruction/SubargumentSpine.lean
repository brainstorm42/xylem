import Solution

/-!
Trace-backed interface checks for the pinned percolation proof.

This file is a deliberately small Lean client, not a replacement for the
upstream proof bodies.  Its named definitions carry the exact CSH assumptions
and reassemble the public endpoint through the theorem interfaces identified
in the compact reachable trace and the separate boundary artifact.  The
boundary Expr trees and declaration signatures are the evidence for the finer
local boundaries; Lean checks the client's applications here. Opaque theorem
bodies remain opaque.
-/

noncomputable section

open Percolation.Continuity
open Percolation.Continuity.Statements
open Percolation.Literature
open Percolation.Literature.LatticeModels

namespace PercolationProofSubarguments

/-- Exact universal CSH hypothesis consumed by the CSH-to-continuity bridges. -/
abbrev CSHInterface : Prop :=
  ∀ (n : ℕ) (w : Sym2 (Fin n) → unitInterval),
    (∀ (e : Sym2 (Fin n)), 0 < w e ∧ w e < 1) →
      ∀ (o v x : Fin n) (Y : Finset (Fin n)) (D : List (Fin n)),
        o ≠ v →
          x ∉ Y →
            o ≠ x →
              v ≠ x →
                o ∉ Y →
                  v ∉ Y →
                    D.Nodup →
                      (∀ d ∈ D, d ≠ x ∧ d ∉ Y ∧ d ≠ o ∧ d ≠ v) →
                        Percolation.Continuity.CSH.CSHHolds w x (↑Y) D o v

/- A checked local-assumption application.  The application record for the
   boundary `cshHolds` proof classifies this shape separately from theorem
   heads; keeping it here makes the binder order and all local premises
   executable rather than merely described in the component manifest. -/
theorem cshAssumptionApplication
    (hCSH : CSHInterface) (n : ℕ) (w : Sym2 (Fin n) → unitInterval)
    (hw : ∀ e, 0 < w e ∧ w e < 1) (o v x : Fin n)
    (Y : Finset (Fin n)) (D : List (Fin n))
    (hov : o ≠ v) (hxY : x ∉ Y) (hox : o ≠ x) (hvx : v ≠ x)
    (hoY : o ∉ Y) (hvY : v ∉ Y) (hnd : D.Nodup)
    (hdis : ∀ d ∈ D, d ≠ x ∧ d ∉ Y ∧ d ≠ o ∧ d ≠ v) :
    Percolation.Continuity.CSH.CSHHolds w x (↑Y) D o v :=
  hCSH n w hw o v x Y D hov hxY hox hvx hoY hvY hnd hdis

/-- The first named interface step in the captured CSH route. -/
theorem additiveGluingStep (hCSH : CSHInterface) : AdditiveGluing :=
  Percolation.Continuity.CSH.additiveGluing_of_csh hCSH

/-- The definitionally aligned Conjecture-3 interface step. -/
theorem conjecture3Step (hCSH : CSHInterface) : KozmaNitzan2024_conjecture3 :=
  Percolation.Continuity.CSH.conjecture3_of_csh hCSH

/-- The endpoint interface obtained from the universal CSH hypothesis. -/
theorem continuityStep (hCSH : CSHInterface) (d : ℕ) (hd : 2 ≤ d) :
    PercolationContinuity d :=
  Percolation.Continuity.CSH.percolationContinuity_of_csh hCSH d hd

/-- The intermediate additive-gluing endpoint retained as a separately typed step. -/
theorem additiveContinuityStep (h : AdditiveGluing) (d : ℕ) (hd : 2 ≤ d) :
    PercolationContinuity d :=
  Percolation.Continuity.percolationContinuity_of_additiveGluing h d hd

/-- The near-one endpoint retains the theorem-6 and bridge assumptions explicitly. -/
theorem nearOneContinuityStep (hX : NearOneGluing) (d : ℕ) (hd : 2 ≤ d) :
    PercolationContinuity d :=
  Percolation.Continuity.percolationContinuity_of_nearOneGluing hX d hd

/-- The independently named theorem-6 split with its exact two input propositions. -/
theorem theorem6FromSlabCritical
    (hslab : KozmaNitzan2024_slabPercolation)
    (hAG : theta_slab_criticalProb_zd_eq_zero) :
    KozmaNitzan2024_thm6 :=
  KozmaNitzan2024_thm6_holds_of hslab hAG

/-- Reassemble the public Solution theorem from the checked formal endpoint. -/
theorem reassembledPublicEndpoint (d : ℕ) (hd : 2 ≤ d) :
    BondPercolation.PercolationContinuity d :=
  (BondPercolation.bridge d).mpr (continuityStep CSH.cshAll d hd)

/- This names the CSH → Conjecture 3 → NearOneGluing → continuity → public
   endpoint chain.  It is a client-side reconstruction of theorem interfaces;
   it does not claim to inline the opaque upstream theorem bodies. -/
theorem reassembledNamedChain (d : ℕ) (hd : 2 ≤ d) :
    BondPercolation.PercolationContinuity d := by
  have hConjecture3 := conjecture3Step CSH.cshAll
  have hNear : NearOneGluing :=
    Percolation.Continuity.nearOneGluing_iff_conjecture3.mpr hConjecture3
  exact (BondPercolation.bridge d).mpr (nearOneContinuityStep hNear d hd)

-- These examples make the interface compatibility and the named helper terms
-- checkable without pretending that the opaque upstream bodies were copied
-- into this client.
example : CSHInterface := CSH.cshAll

example : AdditiveGluing := additiveGluingStep CSH.cshAll

example : KozmaNitzan2024_conjecture3 := conjecture3Step CSH.cshAll

example (d : ℕ) (hd : 2 ≤ d) : PercolationContinuity d :=
  continuityStep CSH.cshAll d hd

example (d : ℕ) (hd : 2 ≤ d) : BondPercolation.PercolationContinuity d :=
  reassembledPublicEndpoint d hd

example (d : ℕ) (hd : 2 ≤ d) : BondPercolation.PercolationContinuity d :=
  reassembledNamedChain d hd

-- The local proof-trace boundary declarations are checked at their exact
-- elaborated types.  Their opaque bodies are intentionally not reconstructed
-- here because the capture records them as named theorem applications.
#check Percolation.Continuity.CSH.cshHolds_of_unfold
#check Percolation.Continuity.CSH.within_nonneg_of_hpart
#check Percolation.Continuity.CSH.hpart_nonneg
#check Percolation.Continuity.CSH.surplusMargin_nonneg_of_csh
#check Percolation.Continuity.CSH.additiveGluing_of_surplusMargin_nondegenerate

end PercolationProofSubarguments
