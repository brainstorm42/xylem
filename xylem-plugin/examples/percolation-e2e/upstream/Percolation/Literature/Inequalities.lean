import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Order.Interval.Set.ProjIcc
import Percolation.Literature.Basic
import Percolation.Literature.PercolationEvents
import Percolation.Util.Linter

/-!
# Correlation inequalities for Bernoulli bond percolation

Throughout, `G : SimpleGraph V` is an arbitrary simple graph, `p : unitInterval`, and `μ =
bondPercolation G p = setBer(G.edgeSet, p)` is Bernoulli bond percolation on `G`
(`bondPercolation`), a product measure on `BondConfig V = Set (Sym2 V)` under which edges of `G` are
open independently with probability `p` and non-edges are a.s. closed. Increasing events are
Mathlib's `IsUpperSet`; local events, pivotality and disjoint occurrence are those of
`PercolationEvents`.

## Contents

* Russo's formula `d/dp P_p(A) = E_p N(A) = Σ_e P_p(e pivotal for A)` for
  increasing local events (`russo_formula`, `russo_formula_sum`). Russo, *Z. Wahrsch.* 56
  (1981); Margulis (1974); Grimmett (1999), Thm. 2.25.

## Design choices

* Configurations carry the (a.s. closed) non-edge coordinates of `Sym2 V`. Harris–FKG and
  BK/Reimer are insensitive to this (they hold for any product of Bernoulli measures, degenerate
  ones included). In Russo's formula only edges of `G` contribute to the derivative, so the
  pivotal count is `|pivotals A ω ∩ E(G)|` and the sum form uses the events
  `{ω | e ∈ E(G) ∧ IsPivotal A e ω}` (empty for non-edges); this keeps events such as
  `openConnIn (box d n) 0 y`, which are determined by all pairs inside the box, in scope.
* Russo's formula is a `HasDerivAt` statement for the real-parameter map
  `q ↦ P_{projIcc 0 1 q}(A)` at `p ∈ (0, 1)` (real-parameter wrapper via
  `Set.projIcc 0 1 zero_le_one`).
-/

namespace Percolation.Literature

open MeasureTheory LatticeModels
open scoped LatticeModels

variable {V : Type*}

/-! ### Harris–FKG -/

/-- **Harris–FKG inequality for events** (Harris, *Proc. Camb. Phil. Soc.* 56
(1960), Lemma; Fortuin–Kasteleyn–Ginibre, *Comm. Math. Phys.* 22 (1971); Grimmett,
*Percolation* (1999), Thm. 2.4). Under Bernoulli bond percolation `P_p` on any graph `G`,
increasing measurable events are positively correlated: `P_p(A) P_p(B) ≤ P_p(A ∩ B)`. [cite: GrimmettPercolation1999, Thm. 2.4] [cite: HarrisPCPS1960, Lemma] [cite: FortuinKasteleynGinibreCMP1971] -/
def harris_fkg : Prop :=
  ∀ (G : SimpleGraph V) (p : unitInterval) {A B : Set (BondConfig V)} (hA : IsUpperSet A) (hB : IsUpperSet B) (hAm : MeasurableSet A) (hBm : MeasurableSet B),
    (bondPercolation G p).real A * (bondPercolation G p).real B ≤
      (bondPercolation G p).real (A ∩ B)

/-- **Square-root trick** (Grimmett, *Percolation* (1999), (11.14); consequence
of Harris–FKG applied to the decreasing complements). If `A₁, …, Aₙ` (`n ≥ 1`) are increasing
measurable events with union `A = ⋃ᵢ Aᵢ`, then
`maxᵢ P_p(Aᵢ) ≥ 1 - (1 - P_p(A))^{1/n}`. [cite: GrimmettPercolation1999, (11.14)] -/
def sqrt_trick : Prop :=
  ∀ (G : SimpleGraph V) (p : unitInterval) {ι : Type*} [Fintype ι] [Nonempty ι] (A : ι → Set (BondConfig V)) (hA : ∀ i, IsUpperSet (A i)) (hAm : ∀ i, MeasurableSet (A i)),
    ∃ i, 1 - (1 - (bondPercolation G p).real (⋃ j, A j)) ^ ((Fintype.card ι : ℝ)⁻¹) ≤
      (bondPercolation G p).real (A i)

/-! ### Russo's formula -/

/-- **Russo's formula, expectation form** (Russo, *Z. Wahrsch. verw. Gebiete* 56
(1981) 229; Margulis, *Probl. Inf. Transm.* 10 (1974); Grimmett, *Percolation* (1999),
Thm. 2.25). For an increasing event `A` depending on finitely many coordinates, `p ↦ P_p(A)` is
differentiable on `(0, 1)` with `d/dp P_p(A) = E_p N(A)`, where `N(A)(ω)` is the number of edges
of `G` pivotal for `A` in `ω` (finite, since pivotal coordinates lie in any set determining `A`;
`ℕ∞`-valued `encard` converted by `toNat`). The parameter map is extended constantly outside
`[0, 1]` via `Set.projIcc`. [cite: RussoZW1981, main theorem] [cite: GrimmettPercolation1999, Thm. 2.25] -/
def russo_formula : Prop :=
  ∀ (G : SimpleGraph V) {A : Set (BondConfig V)} (hA : IsUpperSet A) (hAl : IsLocalEvent A) (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1),
    HasDerivAt (fun q : ℝ => (bondPercolation G (Set.projIcc 0 1 zero_le_one q)).real A)
      (∫ ω, ((pivotals A ω ∩ G.edgeSet).encard.toNat : ℝ)
        ∂bondPercolation G (Set.projIcc 0 1 zero_le_one p)) p

/-- **Russo's formula, sum form** (Russo (1981); Margulis (1974); Grimmett,
*Percolation* (1999), Thm. 2.25). For an increasing event `A` determined by the finite set of
coordinates `F`, `d/dp P_p(A) = Σ_{e ∈ F} P_p(e ∈ E(G) is pivotal for A)` on `(0, 1)`; edges
outside `F` are never pivotal and non-edges of `G` do not contribute. [cite: RussoZW1981] -/
def russo_formula_sum : Prop :=
  ∀ (G : SimpleGraph V) {A : Set (BondConfig V)} (hA : IsUpperSet A) (F : Finset (Sym2 V)) (hF : DeterminedBy A (↑F : Set (Sym2 V))) (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1),
    HasDerivAt (fun q : ℝ => (bondPercolation G (Set.projIcc 0 1 zero_le_one q)).real A)
      (∑ e ∈ F, (bondPercolation G (Set.projIcc 0 1 zero_le_one p)).real
        {ω | e ∈ G.edgeSet ∧ IsPivotal A e ω}) p

end Percolation.Literature
