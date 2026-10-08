import Percolation.Literature.Basic
import Percolation.Literature.LatticeModels.ProdBernoulli
import Percolation.Util.Linter

/-!
# Conditional positive association of an open cluster given a disconnection (van den Berg–Häggström–Kahn 2006, Thm. 1.3)

Consumer: the singleton superadditivity lemma `∑_{r ∈ R} P(o ↔ r | r ↮ R∖r) ≤ P(o ↔ R)` of
Kozma–Nitzan, arXiv:2401.12397, Lemma 2.  ONE statement (`def … : Prop`, Thm. 1.3, proved in
`ConditionalPositiveAssociationProofs.lean` as `BHK2006_clusterConditionalPositiveAssociation_holds`),
the definition it speaks about (the open EDGE cluster), and a proved corollary (the
increasing/decreasing case); setting = Bernoulli bond percolation with arbitrary
edge probabilities on a finite vertex set (`Percolation.Literature.LatticeModels.prodBernoulli w` on
`Set (Sym2 V)`, `Percolation.Literature.openGraph`).

## Source, as printed (RSA 29 (2006) 417–435, doi:10.1002/rsa.20102)

§1, p. 2: "Consider bond percolation on a (finite or countably infinite, locally finite) graph
`G = (V, E)`, where each edge `e` is, independently of all other edges, open with probability `p_e`
and closed with probability `1 − p_e`. For `a, b ∈ V` the event that there is an open path from `a`
to `b` is denoted by `a ↔ b`, and the complement of this event by `a ↮ b`." P. 3: "Let `s` be a
fixed vertex. By the open cluster, `C_s`, of `s` we mean the set of all edges which are in open
paths starting at `s`. As in [BK01] we define, for `X ⊆ V`, the event
`R_X := {s ↮ X} = {s ↮ x ∀ x ∈ X}`. … an event `A` is increasing and determined by the open cluster
of `s` if `ω ∈ A` and `C_s(ω′) ⊇ C_s(ω)` imply `ω′ ∈ A`."  **Theorem 1.2** (p. 5): "For `s, A, B` and
`X` as in Theorem 1.1 [`A`, `B` increasing events determined by the open cluster of `s`;
`X ⊆ V ∖ {s}`], `Pr(A B | s ↮ X) ≥ Pr(A | s ↮ X) Pr(B | s ↮ X)`."  **Theorem 1.3** (p. 6, "the
functional extension of Theorem 1.2"): "For `s, X` as in Theorem 1.2, and `f, g` bounded,
increasing, measurable functions of `C_s`, `E[f g | s ↮ X] ≥ E[f | s ↮ X] E[g | s ↮ X]`. The
inequality is reversed if one of `f, g` is increasing and the other decreasing." P. 6: "Theorem 1.3
says that the open cluster of `s` is conditionally positively associated given the event
`{s ↮ X}`." Proof: Thm. 1.1 by induction on `|V|` (pp. 3–5; for finite `G`), Thm. 1.2 = Thm. 1.1
with `Y = X`, Thm. 1.3 by "a standard (and easy) reduction".

## Contents

* `openEdgeCluster ω s` — definition: BHK's `C_s`, the set of (non-loop) open edges lying on open
  paths from `s`, i.e. the open edges both of whose endpoints are joined to `s` by an open path
  (`openGraph ω`-reachable; an open edge with one endpoint reachable has both reachable).
* `BHK2006_clusterConditionalPositiveAssociation` — statement of Thm. 1.3 (increasing/increasing
  case) for a FINITE vertex type `V` (the printed theorem covers finite graphs, the proof being by
  induction on `|V|`), parameters `w : Sym2 V → [0,1]` (`w e = p_e`; non-edges of the intended graph
  carry `p_e = 0`, loops are ignored by `openGraph`/`openEdgeCluster`), `s ∉ X`, and `f = F ∘ C_s`,
  `g = G ∘ C_s` with `F, G : Set (Sym2 V) → ℝ` monotone for `⊆` ("increasing functions of `C_s`";
  boundedness is automatic, `V` being finite).  Conditional expectations are cleared of
  denominators: with `μ = prodBernoulli w`, `D = {s ↮ X}`,
  `(∫_D f dμ)(∫_D g dμ) ≤ μ(D) ∫_D f g dμ` — for `μ(D) > 0` this is the printed
  `E[fg | D] ≥ E[f | D] E[g | D]`, and for `μ(D) = 0` both sides vanish.
* `BHK2006_clusterConditionalPositiveAssociation.antitone_right` — proved from the fact: the
  reversed inequality when `F` is increasing and `G` decreasing ("(b) is (a) applied to `(f, −g)`").

Not restated: Thm. 1.1 (two sets `X, Y`), Thms. 1.4–1.5 (two clusters), the random-cluster and
directed versions (§§2–3), infinite graphs.  The payload notes the fact is also a realistic
formalisation target (induction on `|V|` + Ahlswede–Daykin, Mathlib `Finset.four_functions_theorem`).
-/

noncomputable section

open MeasureTheory Set
open Percolation.Literature.LatticeModels (prodBernoulli)

namespace Percolation.Literature

universe v

variable {V : Type*}

/-- **The open (edge) cluster `C_s` of van den Berg–Häggström–Kahn**: "the set of all edges which
are in open paths starting at `s`" — the open, non-loop edges both of whose endpoints are joined to
`s` by an open path of the configuration `ω` (`openGraph ω`). [cite: VandenbergHaggstromKahn2005, §1 p. 3 (definition of C_s)] -/
def openEdgeCluster (ω : BondConfig V) (s : V) : Set (Sym2 V) :=
  {e | e ∈ ω ∧ ¬ e.IsDiag ∧ ∀ v ∈ e, (openGraph ω).Reachable s v}

/-- Edges of the open cluster are open. [folklore] -/
theorem openEdgeCluster_subset (ω : BondConfig V) (s : V) : openEdgeCluster ω s ⊆ ω :=
  fun _ he => he.1

/-- Unfolding of membership in the open edge cluster. [folklore] -/
theorem mem_openEdgeCluster_iff (ω : BondConfig V) (s : V) (e : Sym2 V) :
    e ∈ openEdgeCluster ω s ↔ e ∈ ω ∧ ¬ e.IsDiag ∧ ∀ v ∈ e, (openGraph ω).Reachable s v :=
  Iff.rfl

/-- **van den Berg–Häggström–Kahn (2006), Theorem 1.3 — the open cluster of `s` is conditionally
positively associated given `{s ↮ X}`.** Printed: "For `s, X` as in Theorem 1.2 [`X ⊆ V ∖ {s}`],
and `f, g` bounded, increasing, measurable functions of `C_s`,
`E[f g | s ↮ X] ≥ E[f | s ↮ X] E[g | s ↮ X]`" (bond percolation with arbitrary edge probabilities
`p_e`; finite graphs, proof by induction on `|V|`).  Stated for a finite vertex type `V`,
`μ = prodBernoulli w` on `Set (Sym2 V)` (each `e` open independently with probability `w e`),
`D = {ω | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x}` (`= {s ↮ X}`), and `f = F ∘ C_s`, `g = G ∘ C_s`
with `F, G` monotone for inclusion (`C_s = openEdgeCluster`), in the denominator-free form
`(∫_D f dμ)(∫_D g dμ) ≤ μ(D) · ∫_D f g dμ`.  Users take
`(h : BHK2006_clusterConditionalPositiveAssociation)`, supplied by `BHK2006_clusterConditionalPositiveAssociation_holds`.
[cite: VandenbergHaggstromKahn2005, Thm. 1.3 (p. 6), with Thm. 1.2 (p. 5) and Thm. 1.1 (pp. 3–5)] -/
def BHK2006_clusterConditionalPositiveAssociation : Prop :=
  ∀ (V : Type v) [Fintype V] (w : Sym2 V → unitInterval) (s : V) (X : Set V)
    (F G : Set (Sym2 V) → ℝ), Monotone F → Monotone G → s ∉ X →
    (∫ ω in {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x},
        F (openEdgeCluster ω s) ∂(prodBernoulli w)) *
      (∫ ω in {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x},
        G (openEdgeCluster ω s) ∂(prodBernoulli w)) ≤
    (prodBernoulli w).real {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x} *
      ∫ ω in {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x},
        F (openEdgeCluster ω s) * G (openEdgeCluster ω s) ∂(prodBernoulli w)

/-- **The increasing/decreasing case** (proved from the fact, as printed: "(b) is (a) applied to
the pair `(f, −g)`"): for `F` monotone and `G` antitone the inequality is reversed,
`μ(D) · ∫_D f g dμ ≤ (∫_D f dμ)(∫_D g dμ)`. [cite: VandenbergHaggstromKahn2005, Thm. 1.3 (p. 6, last sentence)] -/
theorem BHK2006_clusterConditionalPositiveAssociation.antitone_right
    (h : BHK2006_clusterConditionalPositiveAssociation.{v}) (V : Type v) [Fintype V]
    (w : Sym2 V → unitInterval) (s : V) (X : Set V) (F G : Set (Sym2 V) → ℝ)
    (hF : Monotone F) (hG : Antitone G) (hs : s ∉ X) :
    (prodBernoulli w).real {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x} *
      (∫ ω in {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x},
        F (openEdgeCluster ω s) * G (openEdgeCluster ω s) ∂(prodBernoulli w)) ≤
    (∫ ω in {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x},
        F (openEdgeCluster ω s) ∂(prodBernoulli w)) *
      ∫ ω in {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x},
        G (openEdgeCluster ω s) ∂(prodBernoulli w) := by
  have hnegG : Monotone (fun C => -G C) := fun _ _ hab => neg_le_neg (hG hab)
  have key := h V w s X F (fun C => -G C) hF hnegG hs
  simp only [mul_neg, integral_neg] at key
  linarith

end Percolation.Literature
