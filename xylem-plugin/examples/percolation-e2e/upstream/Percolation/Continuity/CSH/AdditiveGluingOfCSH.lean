import Percolation.Continuity.AdditiveGluing.OfSurplusTransfer
import Percolation.Continuity.CSH.Peel
import Percolation.Continuity.OfGluing
import Percolation.Util.Linter

/-!
# Additive gluing, and hence θ(p_c) = 0, from the conditioned slack hierarchy

Every theorem in this file takes as hypothesis `hCSH` the conditioned slack hierarchy `CSH.CSHHolds` for non-degenerate weights
(`0 < w e < 1`) and pairwise distinct named vertices, in the `Fin n` / `Finset` form (the statement of `CSH.cshAll`), and derives:
* `CSH.additiveGluing_of_csh` — the additive gluing inequality `Percolation.Continuity.Statements.AdditiveGluing`, by the surplus-margin bound
  `CSH.surplusMargin_nonneg_of_csh` plugged into `CSH.additiveGluing_of_surplusMargin_nondegenerate` (degenerate observers + closure over
  degenerate weights via the min-form of the surplus);
* `CSH.conjecture3_of_csh` — Kozma–Nitzan's Conjecture 3, from additive gluing;
* `CSH.percolationContinuity_of_csh` — `θ_{ℤ^d}(p_c) = 0` for all `d ≥ 2`, from Conjecture 3 and Kozma–Nitzan's Theorem 6
  (`KozmaNitzan2024_thm6_holds`);
[cite: KozmaNitzan2024, Conj. 1 (p. 3), Conj. 3 (p. 15), Conj. 4 (p. 32), Thm. 6]
-/

noncomputable section

namespace Percolation.Continuity

open MeasureTheory Set Percolation.Literature.LatticeModels Percolation.Literature
open scoped Classical
open Percolation.Continuity.Statements

namespace CSH

/-- **Additive gluing `Percolation.Continuity.Statements.AdditiveGluing` from the conditioned slack hierarchy** (hypothesis `hCSH`: `CSH.CSHHolds`
for non-degenerate weights and pairwise distinct named vertices, the statement of `CSH.cshAll`), via `CSH.surplusMargin_nonneg_of_csh` and
`CSH.additiveGluing_of_surplusMargin_nondegenerate`.  The statement is the additive form implied by [cite: KozmaNitzan2024, Conj. 1 (p. 3)] -/
theorem additiveGluing_of_csh
    (hCSH : ∀ (n : ℕ) (w : Sym2 (Fin n) → unitInterval), (∀ e, 0 < w e ∧ w e < 1) →
      ∀ (o v x : Fin n) (Y : Finset (Fin n)) (D : List (Fin n)),
      o ≠ v → x ∉ Y → o ≠ x → v ≠ x → o ∉ Y → v ∉ Y → D.Nodup → (∀ d ∈ D, d ≠ x ∧ d ∉ Y ∧ d ≠ o ∧ d ≠ v) →
      CSHHolds w x (↑Y : Set (Fin n)) D o v) :
    Percolation.Continuity.Statements.AdditiveGluing :=
  additiveGluing_of_surplusMargin_nondegenerate fun n p hp T o v F r hoT hvT hov hF _ hr hcompat =>
    surplusMargin_nonneg_of_csh p hp o v (fun x Y D => hCSH n p hp o v x Y D hov) T r [] F hF hr hcompat hoT hvT
      List.nodup_nil (fun _ hd => absurd hd List.not_mem_nil)

/-- **Kozma–Nitzan's Conjecture 3 from the conditioned slack hierarchy.** [cite: KozmaNitzan2024, Conjecture 3 (p. 15)] -/
theorem conjecture3_of_csh
    (hCSH : ∀ (n : ℕ) (w : Sym2 (Fin n) → unitInterval), (∀ e, 0 < w e ∧ w e < 1) →
      ∀ (o v x : Fin n) (Y : Finset (Fin n)) (D : List (Fin n)),
      o ≠ v → x ∉ Y → o ≠ x → v ≠ x → o ∉ Y → v ∉ Y → D.Nodup → (∀ d ∈ D, d ≠ x ∧ d ∉ Y ∧ d ≠ o ∧ d ≠ v) →
      CSHHolds w x (↑Y : Set (Fin n)) D o v) :
    KozmaNitzan2024_conjecture3 :=
  nearOneGluing_iff_conjecture3.1 (additiveGluingGlue_proof (additiveGluing_of_csh hCSH))

/-- **`θ_{ℤ^d}(p_c) = 0` for every `d ≥ 2` from the conditioned slack hierarchy.** [cite: KozmaNitzan2024, Thm. 6 with Conj. 3 (p. 15)] -/
theorem percolationContinuity_of_csh
    (hCSH : ∀ (n : ℕ) (w : Sym2 (Fin n) → unitInterval), (∀ e, 0 < w e ∧ w e < 1) →
      ∀ (o v x : Fin n) (Y : Finset (Fin n)) (D : List (Fin n)),
      o ≠ v → x ∉ Y → o ≠ x → v ≠ x → o ∉ Y → v ∉ Y → D.Nodup → (∀ d ∈ D, d ≠ x ∧ d ∉ Y ∧ d ≠ o ∧ d ≠ v) →
      CSHHolds w x (↑Y : Set (Fin n)) D o v)
    (d : ℕ) (hd : 2 ≤ d) : PercolationContinuity d :=
  percolationContinuity_of_additiveGluing (additiveGluing_of_csh hCSH) d hd

end CSH

end Percolation.Continuity
