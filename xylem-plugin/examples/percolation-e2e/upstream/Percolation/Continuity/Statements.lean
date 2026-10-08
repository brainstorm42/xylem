import Percolation.Literature.LatticeModels.ProdBernoulli
import Percolation.Literature.Basic
import Percolation.Util.Linter

/-!
# Named statements: near-one gluing (Kozma–Nitzan's Conjecture 3) and additive gluing, on finite weighted graphs
-/

namespace Percolation.Continuity.Statements

open scoped Classical

/-- **Near-one gluing, uniformly in the number of relays (Kozma–Nitzan's Conjecture 3).** For every `ε > 0` there is `δ > 0` such
that, for every `n`, every weight function `w : Sym2 (Fin n) → [0,1]` on the pairs of `n` labelled vertices (product Bernoulli measure
`prodBernoulli w`; a pair of weight `0` is an absent edge), every finite set `A` of vertices (the *relays*) and all vertices `o, b`:
if `P(o ↔ A) > 1 − δ` and `P(a ↔ b) > 1 − δ` for every `a ∈ A`, then `P(o ↔ b) > 1 − ε`. Here `u ↔ v` (`openConn u v`) is the event
that `u` and `v` are joined by an open path and `o ↔ A` is `⋃ a ∈ A, {o ↔ a}`. The whole content is that `δ` does not depend on `|A|`
(for `|A| ≤ k` the union bound gives `P(o ↮ b) < (k+1)δ`). This `Prop` is, letter for letter,
`Percolation.Literature.KozmaNitzan2024_conjecture3`; it is proved in this library as `Percolation.Continuity.CSH.kozmaNitzan_conjecture3_holds`
(from additive gluing with `δ = ε/2`), and by Kozma–Nitzan's Theorem 6 (`Percolation.Literature.KozmaNitzan2024_thm6_holds`) it implies
`θ(p_c) = 0` on `ℤ^d` for every `d ≥ 2`. [cite: KozmaNitzan2024, Conjecture 3 (p. 15)] -/
def NearOneGluing : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ℕ) (w : Sym2 (Fin n) → unitInterval) (A : Finset (Fin n)) (o b : Fin n), 1 - δ < (Percolation.Literature.LatticeModels.prodBernoulli w).real (⋃ a ∈ A, Percolation.Literature.openConn o a) → (∀ a ∈ A, 1 - δ < (Percolation.Literature.LatticeModels.prodBernoulli w).real (Percolation.Literature.openConn a b)) → 1 - ε < (Percolation.Literature.LatticeModels.prodBernoulli w).real (Percolation.Literature.openConn o b)

/-- **Additive gluing.** For every `n`, every weight function `w : Sym2 (Fin n) → [0,1]` (measure `prodBernoulli w`), every finite set
`A` of vertices, all vertices `o, b` and every real `t ≥ 0`: if `P(a ↔ b) ≥ 1 − t` for every `a ∈ A`, then `P(o ↔ b) ≥ P(o ↔ A) − t`.
Equivalently, for `A ≠ ∅`, `P(o ↮ b) ≤ P(o ↮ A) + max_{a ∈ A} P(a ↮ b)`: the relay set is treated as if it were a single vertex (for
`|A| = 1` this IS the union bound `{o ↮ b} ⊆ {o ↮ a} ∪ {a ↮ b}`), with no loss growing with `|A|`. Relation to Kozma–Nitzan's
Conjecture 1: that conjecture is the MULTIPLICATIVE inequality `P(o ↔ b) ≥ P(o ↔ A) · min_{a ∈ A} P(a ↔ b)`; since
`P(o ↔ A)(1 − t) ≥ P(o ↔ A) − t`, Conjecture 1 implies this statement, which is its additive (constant-one) form and not Conjecture 1
itself. Taking `t = δ = ε/2` gives `NearOneGluing` (Conjecture 3) at once. Unlike an `ε–δ` statement it is refutable by a single
weighted graph; none exists: it is proved in this library as `Percolation.Continuity.CSH.additiveGluing_holds`, from the conditioned slack
hierarchy `Percolation.Continuity.CSH.cshHolds`. [cite: KozmaNitzan2024, Conj. 1 (p. 3)] -/
def AdditiveGluing : Prop :=
  ∀ (n : ℕ) (w : Sym2 (Fin n) → unitInterval) (A : Finset (Fin n)) (o b : Fin n) (t : ℝ), 0 ≤ t → (∀ a ∈ A, 1 - t ≤ (Percolation.Literature.LatticeModels.prodBernoulli w).real (Percolation.Literature.openConn a b)) → (Percolation.Literature.LatticeModels.prodBernoulli w).real (⋃ a ∈ A, Percolation.Literature.openConn o a) - t ≤ (Percolation.Literature.LatticeModels.prodBernoulli w).real (Percolation.Literature.openConn o b)

/-- `AdditiveGluing → NearOneGluing`, the by-name form of `AdditiveGluingSuffices` (the two are definitionally equal; take `δ = ε / 2`). -/
def AdditiveGluingGlue : Prop :=
  AdditiveGluing → NearOneGluing

/-- The implication `AdditiveGluing → NearOneGluing`, with both statements spelled out. -/
def AdditiveGluingSuffices : Prop :=
  (∀ (n : ℕ) (w : Sym2 (Fin n) → unitInterval) (A : Finset (Fin n)) (o b : Fin n) (t : ℝ), 0 ≤ t → (∀ a ∈ A, 1 - t ≤ (Percolation.Literature.LatticeModels.prodBernoulli w).real (Percolation.Literature.openConn a b)) → (Percolation.Literature.LatticeModels.prodBernoulli w).real (⋃ a ∈ A, Percolation.Literature.openConn o a) - t ≤ (Percolation.Literature.LatticeModels.prodBernoulli w).real (Percolation.Literature.openConn o b)) → (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ℕ) (w : Sym2 (Fin n) → unitInterval) (A : Finset (Fin n)) (o b : Fin n), 1 - δ < (Percolation.Literature.LatticeModels.prodBernoulli w).real (⋃ a ∈ A, Percolation.Literature.openConn o a) → (∀ a ∈ A, 1 - δ < (Percolation.Literature.LatticeModels.prodBernoulli w).real (Percolation.Literature.openConn a b)) → 1 - ε < (Percolation.Literature.LatticeModels.prodBernoulli w).real (Percolation.Literature.openConn o b))

end Percolation.Continuity.Statements
