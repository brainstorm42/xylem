import Percolation.Literature.CriticalContinuity
import Percolation.Literature.LatticeModels.ProdBernoulli
import Percolation.Util.Linter

/-!
# Kozma–Nitzan: `θ(p_c) = 0` on `ℤ^d` reduced to a gluing inequality on finite graphs (Conjecture 3 ⇒ Theorem 6)

The statements of Conjecture 3 and Theorem 6 of G. Kozma and S. Nitzan, *A reduction of the `θ(p_c) = 0`
problem to a conjectured inequality*, arXiv:2401.12397 (2024), typed over this library's percolation on
finite weighted graphs (`prodBernoulli`) and its lattice statement `PercolationContinuity`.

## Source (arXiv:2401.12397v1, pp. 1, 3–4, 15)

* Setting, p. 4: "For a graph `G` and a function `p : E(G) → [0,1]` we will consider the measure on
  subsets `ω` of `E(G)` such that for every edge `e` the probability that `e ∈ ω` is `p(e)`, and
  these events are independent. … For two vertices `v` and `w` we denote by `v ↔ w` the event that
  `v` and `w` are connected in `ω`"; graphs are finite (Conjecture 1, p. 3: "Let `G` be a finite
  graph with arbitrary probabilities on its edges").
* Conjecture 3, p. 15 (verbatim): "For every `ε > 0` there exists `δ > 0` such that for any graph
  `G`, any `A ⊂ G`, and any `0, b ∈ G` which satisfy `P(0 ↔ A) > 1 − δ` and `P(a ↔ b) > 1 − δ` for
  all `a ∈ A`, we have `P(0 ↔ b) > 1 − ε`." It is posed as a weakening of Conjecture 1, p. 3
  (`P(0 ↔ b) ≥ P(0 ↔ A) · min_{a ∈ A} P(a ↔ b)`; "We were not able to prove or disprove this
  conjecture. Our belief that it holds is based on some (admittedly restricted) numerical evidence
  and on some simple cases where we were able to prove it"): "Conjecture 3 clearly follows from
  conjecture 1 (by taking `δ = 1 − √(1−ε)`)" (p. 15).  The paper proves the pre-FKG form of
  Conjecture 1 for `|A| = 2`, for some configurations with `|A| = 3`, and when `0` is close to `A`
  (§3; Thm 8, p. 32).
* Theorem 6, p. 15 (verbatim): "If conjecture 3 holds then `P(|C(0)| = ∞) = 0` at the critical
  probability for `ℤ^d` for any `d ≥ 2`." Proof: §4, pp. 15–31, a one-step renormalisation at a
  fixed value of `p`: assuming `θ(p) > 0` and `d ≥ 3`, Conjecture 3 applied to finite auxiliary graphs
  built from boxes of `ℤ^d` produces percolation in a two-dimensional slab of `ℤ^d` at the same `p`,
  which is impossible at `p = p_c` (the printed proof invokes the strict inequality
  `p_c(slab) > p_c(ℤ^d)` of Aizenman–Grimmett); `d = 2` is [Grimmett 1999, §11].  Abstract: "This
  inequality, if true, implies that there is no percolation at criticality at `ℤ^d`"; p. 1:
  `θ(p_c) = 0` is "A captivating question, open since at least the 80s", settled in print for `d = 2`
  (Harris, Kesten) and `d ≥ 11` (Hara, `d ≥ 19`; Fitzner–van der Hofstad, `d ≥ 11`; the lace expansion
  being "inherently limited to `d > 6`").

## Transposition (design note)

A finite graph with edge probabilities is a weight function `w : Sym2 (Fin n) → [0,1]` on all
unordered pairs of `n` labelled vertices (absent edges = weight `0`; the diagonal of `Sym2` is
irrelevant to connectivity); the percolation measure is the inhomogeneous product Bernoulli measure
`prodBernoulli w` on `Set (Sym2 (Fin n))` (`Literature/LatticeModels/ProdBernoulli.lean`), `v ↔ w` is `openConn v w`, and
`0 ↔ A` is `⋃ a ∈ A, openConn 0 a`.  "`P(|C(0)| = ∞) = 0` at the critical probability for `ℤ^d`" is
`PercolationContinuity d := theta (zdGraph d) 0 (criticalProbI d) = 0` (`CriticalContinuity.lean`).
Conjecture 3 is recorded as a `Prop`, `KozmaNitzan2024_conjecture3`, so that Theorem 6 can be stated as
the implication `KozmaNitzan2024_thm6`; nothing in this file asserts either.

## Status

* In print, Conjecture 3 is open: arXiv:2401.12397 has a single version and no published proof or
  refutation of Conjectures 1–4, and no result on `θ(p_c) = 0` for `3 ≤ d ≤ 10`, is known; Gladkov, arXiv:2408.08457, p. 1,
  reports it as "a conjectured inequality for percolation on general graphs that would imply
  `θ(p_c) = 0` for bond percolation on `ℤ^d`, which is an old conjecture".
* In this development both statements are theorems.  `KozmaNitzan2024_thm6` is proved as
  `KozmaNitzan2024_thm6_holds` (`KozmaNitzanTheorem6SlabCritical.lean`): the §4 renormalisation
  `KozmaNitzan2024_slabPercolation_holds` (`Literature/KozmaNitzanTheorem6OfSlab.lean`) together with "no slab
  percolates at `p_c(ℤ^d)`", `theta_slab_criticalProb_zd_eq_zero_holds`, obtained from the half-space
  theorem of Barsky–Grimmett–Newman 1991 and Grimmett–Marstrand 1990 rather than from Aizenman–Grimmett;
  `d = 2` from Harris' and Kesten's theorems.  `KozmaNitzan2024_conjecture3` is proved downstream of the
  `Literature` library (which this file cannot import) as `CSH.kozmaNitzan_conjecture3_holds`, from the
  additive gluing inequality `CSH.additiveGluing_holds` — `P(0 ↔ b) ≥ P(0 ↔ A) − t` whenever
  `P(a ↔ b) ≥ 1 − t` for all `a ∈ A`; take `t = δ = ε/2` — which is itself derived from a new hierarchy
  of conditioned covariance inequalities for a single open cluster on finite weighted graphs, the
  conditioned slack hierarchy `CSH.cshHolds`.  The two together give
  `CSH.percolationContinuity_allDimensions : ∀ d ≥ 2, PercolationContinuity d`.  Inside `Literature/`,
  users take Conjecture 3 as the hypothesis of `KozmaNitzan2024_thm6`.
-/

noncomputable section

open MeasureTheory Percolation.Literature.LatticeModels

namespace Percolation.Literature

/-- **Kozma–Nitzan Conjecture 3** (arXiv:2401.12397, p. 15), the `|A|`-uniform near-one gluing
principle on finite weighted graphs: for every `ε > 0` there is `δ > 0` such that, for every `n`, every
weight function `w : Sym2 (Fin n) → [0,1]` (measure `prodBernoulli w`), every finite set `A` of vertices
and all vertices `o, b`, if `P(o ↔ A) > 1 − δ` and `P(a ↔ b) > 1 − δ` for every `a ∈ A`, then
`P(o ↔ b) > 1 − ε` — in one sentence: an observer joined with high probability to a set of relays each of
which is joined with high probability to a target is itself joined to the target with high probability,
with bounds independent of the graph and of the number of relays.  Posed by Kozma and Nitzan as an open
conjecture (the weakest of their gluing conjectures; of the stronger Conjecture 1, from which it "clearly
follows", they write "we were not able to prove or disprove", p. 3) and typed here only so that their
Theorem 6 can be stated (`KozmaNitzan2024_thm6`).  Status: open in print; proved in this development, downstream of `Literature/`, as `CSH.kozmaNitzan_conjecture3_holds` (from
the additive gluing inequality `CSH.additiveGluing_holds` with `δ = ε/2`; see the module docstring,
"Status"), whence `θ(p_c) = 0` on `ℤ^d` for all `d ≥ 2` via `KozmaNitzan2024_thm6_holds`.  Since this file
cannot import that proof, users inside `Literature/` take the statement as a hypothesis.
[cite: KozmaNitzan2024, Conjecture 3 (p. 15)] -/
def KozmaNitzan2024_conjecture3 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ℕ) (w : Sym2 (Fin n) → unitInterval) (A : Finset (Fin n))
    (o b : Fin n),
    1 - δ < (prodBernoulli w).real (⋃ a ∈ A, openConn o a) →
      (∀ a ∈ A, 1 - δ < (prodBernoulli w).real (openConn a b)) →
        1 - ε < (prodBernoulli w).real (openConn o b)

/-- **Kozma–Nitzan 2024, Theorem 6** (arXiv:2401.12397, p. 15; proof §4, pp. 15–31): "If
conjecture 3 holds then `P(|C(0)| = ∞) = 0` at the critical probability for `ℤ^d` for any `d ≥ 2`",
i.e. `KozmaNitzan2024_conjecture3 → ∀ d ≥ 2, PercolationContinuity d` (`θ_{ℤ^d}(p_c(ℤ^d)) = 0` for
nearest-neighbour bond percolation).  The printed proof is a one-step renormalisation at a fixed value
of `p` showing that, under Conjecture 3, an infinite cluster at `p` forces percolation in a slab at the
same `p`; `d = 2` is Harris–Kesten (Grimmett 1999, §11).  Recorded as a `Prop`; proved in this library
as `KozmaNitzan2024_thm6_holds` (`KozmaNitzanTheorem6SlabCritical.lean`, with the slab step closed by
the half-space theorem of Barsky–Grimmett–Newman and Grimmett–Marstrand), so that with
`CSH.kozmaNitzan_conjecture3_holds` it yields `θ(p_c) = 0` on `ℤ^d` for every `d ≥ 2`.
[cite: KozmaNitzan2024, Thm 6 (p. 15)] -/
def KozmaNitzan2024_thm6 : Prop :=
  KozmaNitzan2024_conjecture3 → ∀ d : ℕ, 2 ≤ d → PercolationContinuity d

end Percolation.Literature

end
