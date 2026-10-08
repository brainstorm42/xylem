import Percolation.Literature.TwoClusterConditionalAssociationProofs
import Percolation.Util.Linter

/-!
# The tripod exchange inequality `P(ox|yz) · P(oy|xz) ≤ P(oxz|y) · P(oyz|x)` — a corollary of van den Berg–Häggström–Kahn 2006, Thm. 1.5

Bond percolation with arbitrary edge probabilities on a
finite vertex type `V` (`μ = prodBernoulli w` on `BondConfig V = Set (Sym2 V)`, `w e = p_e`), four
vertices `o, x, y, z`, and for a set partition `π` of `{o, x, y, z}` write `P(π)` for the probability
that the partition of `{o, x, y, z}` induced by the open clusters is exactly `π`.  This file PROVES

  `P(ox|yz) · P(oy|xz) ≤ P(oxz|y) · P(oyz|x)`                                    (C⁺)

## Status in print and derivation

(C⁺) does not appear in (van den Berg–Kahn 2001; van den Berg–Häggström–Kahn
2006; Grimmett, *The Random-Cluster Model* §3; Kozma–Nitzan arXiv:2401.12397; Gladkov
arXiv:2408.08457; the bunkbed literature), but it is a five-line COROLLARY of
[VandenbergHaggstromKahn2005, Thm. 1.5 (p. 7, eq. (9))]: "Let `s` and `t` be (distinct) vertices,
and `f` and `g` bounded, measurable functions of `(C_s, C_t)`, each increasing in `C_s` and
decreasing in `C_t`. Then `E[f g | s ↮ t] ≥ E[f | s ↮ t] E[g | s ↮ t]`. In other words, on `{s ↮ t}`
we have positive association of all the r.v.'s `1{e ∈ C_s}` and `1{e ∉ C_t}`" — in this library the
named fact `BHK2006_twoClusterConditionalAssociation`, proved by
`BHK2006_twoClusterConditionalAssociation_holds` (`TwoClusterConditionalAssociationProofs.lean`).

## References

* J. van den Berg, O. Häggström, J. Kahn, *Some conditional correlation inequalities for
  percolation and related processes*, Random Structures Algorithms 29 (2006) 417–435
  (arXiv:math/0408176), Thm. 1.5, eq. (9), p. 7. [VandenbergHaggstromKahn2005]
-/

noncomputable section

open MeasureTheory Set
open Percolation.Literature.LatticeModels (prodBernoulli)

namespace Percolation.Literature

variable {V : Type*}

namespace TripodExchange

/-! The function of a pair of edge sets `(C, D) ↦ F_a^s(C) · (1 − F_a^t(D))`, where
`F_a^s = connIndicatorFn s a` (`= 1{a = s or some edge of C contains a}`, this library's increasing
function with `F_a^s(C_s ω) = 1{s ↔ a}(ω)`): evaluated at `(C_s ω, C_t ω)` it is the indicator of
`{s ↔ a} ∩ {t ↮ a}` ("`a` lies in the cluster of `s` and not in that of `t`"), a function
increasing in `C_s` and decreasing in `C_t` as in BHK's Theorem 1.5 ("positive association of all
the r.v.'s `1{e ∈ C_s}` and `1{e ∉ C_t}`", p. 7).  No definition is introduced: the product is
written out in each statement. -/

/-- `∫_D 1_S dμ = μ(D ∩ S)` for the (finite, discrete) percolation space. [folklore] -/
theorem setIntegral_indicator_one_eq [Fintype V] (w : Sym2 V → unitInterval)
    (D S : Set (BondConfig V)) :
    ∫ ω in D, S.indicator (1 : BondConfig V → ℝ) ω ∂(prodBernoulli w) =
      (prodBernoulli w).real (D ∩ S) := by
  have hS : MeasurableSet S := MeasurableSet.of_discrete
  rw [setIntegral_indicator hS]
  simp only [Pi.one_apply, setIntegral_const, smul_eq_mul, mul_one]

/-- `∫_D 1_S 1_T dμ = μ(D ∩ (S ∩ T))`. [folklore] -/
theorem setIntegral_indicator_mul_indicator_eq [Fintype V] (w : Sym2 V → unitInterval)
    (D S T : Set (BondConfig V)) :
    ∫ ω in D, S.indicator (1 : BondConfig V → ℝ) ω * T.indicator (1 : BondConfig V → ℝ) ω
        ∂(prodBernoulli w) =
      (prodBernoulli w).real (D ∩ (S ∩ T)) := by
  have hST : (fun ω => S.indicator (1 : BondConfig V → ℝ) ω * T.indicator (1 : BondConfig V → ℝ) ω)
      = (S ∩ T).indicator 1 :=
    funext fun ω => (congrFun (Set.inter_indicator_one (s := S) (t := T) (M₀ := ℝ)) ω).symm
  rw [hST]
  exact setIntegral_indicator_one_eq w D (S ∩ T)

end TripodExchange

/-! ## The general cluster-event exchange

Of the events `{x ↔ o}`, `{x ↔ z}`, `{y ↔ z}`, `{y ↔ o}` the four-line derivation of (C⁺) uses only
that the first two are increasing events determined by `C_x` and the last two increasing events
determined by `C_y`.  For arbitrary such events `A₁, A₂` (of `C_x`) and `B₁, B₂` (of `C_y`) the
same sandwich — BHK's Remark 2 after Thm. 1.2 (arXiv p. 4 / RSA p. 5: "conditioned on `R_{X∩Y}`,
each of the pairs `(A, R_{X∖Y})`, `(B, R_{Y∖X})` is negatively correlated, while each of `(A,B)`,
`(R_{X∖Y}, R_{Y∖X})` is positively correlated. So …
`Pr'(A R_{X∖Y}) Pr'(B R_{Y∖X}) ≤ Pr'(A) Pr'(R_{X∖Y}) Pr'(B) Pr'(R_{Y∖X}) ≤ Pr'(A B) Pr'(R_{X∖Y} R_{Y∖X})`")
— gives, with `D = {x ↮ y}`,

  `μ(D ∩ (A₁ ∩ B₁)) · μ(D ∩ (A₂ ∩ B₂)) ≤ μ(D ∩ (A₁ ∩ A₂)) · μ(D ∩ (B₁ ∩ B₂))`       (C⁺_gen)

. Examples of admissible events: `{x ↔ o₁} ∩ {x ↔ o₂}`, `⋃ o ∈ O, {x ↔ o}` ("`x` is joined to the
set `O`"), `{e ∈ C_x}`. (C⁺) is the case `A₁ = {x ↔ o}`, `A₂ = {x ↔ z}`, `B₁ = {y ↔ z}`, `B₂ = {y ↔
o}`. By BHK's Thm. 2.1 the same holds for random-cluster measures with `q ≥ 1` and with `x, y`
replaced by disjoint vertex sets; neither extension is formalised here.
-/

end Percolation.Literature

end
