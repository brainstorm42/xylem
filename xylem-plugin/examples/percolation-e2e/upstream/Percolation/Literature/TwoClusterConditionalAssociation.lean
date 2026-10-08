import Percolation.Literature.ConditionalPositiveAssociation
import Percolation.Literature.PercolationProofs
import Percolation.Util.Linter

/-!
# The open clusters of `s` and `t` are conditionally negatively correlated given `{s ↮ t}` (van den Berg–Häggström–Kahn 2006, Thms. 1.4–1.5 and eq. (2))

Consumers: the increment-domination lemma `Cov(1{o↔a}, 1{c↔b}) ≤ …` and Kozma–Nitzan,
arXiv:2401.12397, Lemmas 1, 3, Thms. 1–2, which use exactly this form.  Companion of
`ConditionalPositiveAssociation.lean` (Thm. 1.3, the ONE-cluster statement, recorded
there as the statement `BHK2006_clusterConditionalPositiveAssociation` with the open EDGE cluster
`openEdgeCluster`).  ONE statement (`def … : Prop`) — Thm. 1.5, the two-cluster functional statement,
proved in `TwoClusterConditionalAssociationProofs.lean` as `BHK2006_twoClusterConditionalAssociation_holds` —
and proved corollaries: Thm. 1.4 (negative correlation of `C_s` and `C_t`) and eq. (2)
(`P(s↔a, t↔b | s↮t) ≤ P(s↔a | s↮t) P(t↔b | s↮t)`), in the same setting and the same
denominator-free form as Thm. 1.3.

## Source, as printed (RSA 29 (2006) 417–435, doi:10.1002/rsa.20102; page numbers of the preprint)

§1, p. 2: "Consider bond percolation on a (finite or countably infinite, locally finite) graph
`G = (V, E)`, where each edge `e` is, independently of all other edges, open with probability `p_e`
and closed with probability `1 − p_e`. For `a, b ∈ V` the event that there is an open path from `a`
to `b` is denoted by `a ↔ b`, and the complement of this event by `a ↮ b`. … Here we show, among
other results, a sort of complement of (1), viz.
**(2)** `Pr(s ↔ a, t ↔ b | s ↮ t) ≤ Pr(s ↔ a | s ↮ t) Pr(t ↔ b | s ↮ t)`." P. 3: "By the open
cluster, `C_s`, of `s` we mean the set of all edges which are in open paths starting at `s`."
P. 7: "[Theorem 1.2] implies the following intuitively more natural statement, which says,
informally, that conditioned on nonexistence of an open `(s, t)`-path, the clusters `C_s` and `C_t`
are negatively correlated.  **Theorem 1.4.** Let `s` and `t` be (distinct) vertices, and `f` and
`g` bounded measurable increasing functions of `C_s` and `C_t` respectively. Then
`E[f g | s ↮ t] ≤ E[f | s ↮ t] E[g | s ↮ t]`.  Note that (2) is the special case where `f` is the
indicator of the event `{s ↔ a}`, and `g` that of the event `{t ↔ b}`. … **Theorem 1.5.** Let `s`
and `t` be (distinct) vertices, and `f` and `g` bounded, measurable functions of `(C_s, C_t)`,
each increasing in `C_s` and decreasing in `C_t`. Then
**(9)** `E[f g | s ↮ t] ≥ E[f | s ↮ t] E[g | s ↮ t]`.  In other words, on `{s ↮ t}` we have
positive association of all the r.v.'s `1{e ∈ C_s}` and `1{e ∉ C_t}`." Proof of 1.5 (pp. 7–8):
"it is enough to prove this for finite `G`"; condition on `C_s = W` (eq. (10)), Harris' inequality
in the fresh variables off `W̄`, stochastic monotonicity of `C_t` given `C_s = W`, and Thm. 1.3;
"As just shown, Theorem 1.4 follows easily from Theorem 1.3."

## Contents

* `BHK2006_twoClusterConditionalAssociation` — statement of Thm. 1.5 for a FINITE vertex type `V`
  (the printed reduction is to finite `G`), parameters `w : Sym2 V → [0,1]` (`w e = p_e`;
  non-edges of the intended graph carry `p_e = 0`, loops are ignored by `openGraph` /
  `openEdgeCluster`), `s ≠ t`, and `f ω = F (C_s ω) (C_t ω)`, `g ω = G (C_s ω) (C_t ω)` with
  `F, G : Set (Sym2 V) → Set (Sym2 V) → ℝ` monotone in the first and antitone in the second
  variable ("increasing in `C_s` and decreasing in `C_t`"; boundedness and measurability are
  automatic, `V` being finite).  Denominators cleared exactly as for Thm. 1.3: with
  `μ = prodBernoulli w`, `D = {s ↮ t}`, `(∫_D f dμ)(∫_D g dμ) ≤ μ(D) ∫_D f g dμ`.
* proved from it: `….negCorrelation` — **Thm. 1.4** (`f` increasing in `C_s`, `g` increasing
  in `C_t` ⇒ `μ(D) ∫_D f g ≤ (∫_D f)(∫_D g)`; "(1.5) applied to `(f, −g)`"), and
  `….openConn_negCorrelation` — **eq. (2)**,
  `μ(D) · μ(D ∩ {s↔a} ∩ {t↔b}) ≤ μ(D ∩ {s↔a}) · μ(D ∩ {t↔b})` ("the special case where `f` is the
  indicator of `{s ↔ a}` and `g` that of `{t ↔ b}`"; `1{s ↔ a}` IS an increasing function of the
  edge cluster `C_s`: `reachable_iff_exists_mem_openEdgeCluster`).

Not restated: the random-cluster version (Thm. 2.1 / (12)), the directed version (Thm. 3.4),
infinite graphs.  Thm. 1.5 itself is proved on top of Thm. 1.3 (half a page: domain Markov property of
`prodBernoulli` given `C_s = W`, Harris, Thm. 1.3) in `TwoClusterConditionalAssociationProofs.lean`; this
file records the statement and proves the reduction 1.5 ⇒ 1.4 ⇒ (2).
-/

noncomputable section

open MeasureTheory Set
open Percolation.Literature.LatticeModels (prodBernoulli)

namespace Percolation.Literature

universe v

variable {V : Type*}

/-! ### `1{s ↔ a}` is an increasing function of the open edge cluster `C_s` -/

/-- **`s ↔ a` read off the edge cluster**: `s` is joined to `a` by an open path iff `a = s` or some
edge of `C_s` contains `a` (the last edge of an open path from `s` to `a ≠ s` is an open, non-loop
edge with both endpoints in the cluster). [cite: VandenbergHaggstromKahn2005, §1 p. 3 ("A simple example of such an event is {s ↔ a}")] -/
theorem reachable_iff_exists_mem_openEdgeCluster (ω : BondConfig V) (s a : V) :
    (openGraph ω).Reachable s a ↔ a = s ∨ ∃ e ∈ openEdgeCluster ω s, a ∈ e := by
  constructor
  · intro h
    by_cases has : a = s
    · exact Or.inl has
    · obtain ⟨p⟩ := h.symm
      cases p with
      | nil => exact absurd rfl has
      | cons hadj q =>
        rename_i b
        have hab := (openGraph_adj ω a b).1 hadj
        refine Or.inr ⟨s(a, b), ?_, Sym2.mem_mk_left a b⟩
        refine (mem_openEdgeCluster_iff ω s _).2 ⟨hab.1, ?_, fun v hv => ?_⟩
        · rw [Sym2.mk_isDiag_iff]
          exact hab.2
        · rcases Sym2.mem_iff.1 hv with rfl | rfl
          · exact h
          · exact h.trans ⟨SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil⟩
  · rintro (rfl | ⟨e, he, hae⟩)
    · exact SimpleGraph.Reachable.refl a
    · exact ((mem_openEdgeCluster_iff ω s e).1 he).2.2 a hae

open Classical in
/-- The increasing function `F_a` of a set of edges `C` with `F_a(C_s(ω)) = 1{s ↔ a}(ω)`:
`F_a(C) = 1` if `a = s` or some edge of `C` contains `a`, else `0`.
[cite: VandenbergHaggstromKahn2005, Thm. 1.4 (p. 7, "f is the indicator of the event {s ↔ a}")] -/
def connIndicatorFn (s a : V) (C : Set (Sym2 V)) : ℝ :=
  if a = s ∨ ∃ e ∈ C, a ∈ e then 1 else 0

/-- `F_a` is increasing in `C`. [folklore] -/
theorem monotone_connIndicatorFn (s a : V) : Monotone (connIndicatorFn s a) := by
  classical
  intro C C' hCC'
  unfold connIndicatorFn
  by_cases h : a = s ∨ ∃ e ∈ C, a ∈ e
  · have h' : a = s ∨ ∃ e ∈ C', a ∈ e := h.imp id fun ⟨e, he, hae⟩ => ⟨e, hCC' he, hae⟩
    rw [if_pos h, if_pos h']
  · rw [if_neg h]
    split_ifs
    · exact zero_le_one
    · exact le_rfl

/-- `F_a(C_s(ω)) = 1{s ↔ a}(ω)`. [cite: VandenbergHaggstromKahn2005, Thm. 1.4 (p. 7)] -/
theorem connIndicatorFn_openEdgeCluster (ω : BondConfig V) (s a : V) :
    connIndicatorFn s a (openEdgeCluster ω s) = (openConn s a).indicator 1 ω := by
  classical
  unfold connIndicatorFn
  by_cases h : (openGraph ω).Reachable s a
  · rw [if_pos ((reachable_iff_exists_mem_openEdgeCluster ω s a).1 h),
      indicator_of_mem (show ω ∈ openConn s a from h), Pi.one_apply]
  · rw [if_neg (fun h' => h ((reachable_iff_exists_mem_openEdgeCluster ω s a).2 h')),
      indicator_of_notMem (show ω ∉ openConn s a from h)]

/-! ### Theorem 1.5 (statement) and its corollaries Thm. 1.4 and eq. (2) -/

/-- **van den Berg–Häggström–Kahn (2006), Theorem 1.5 — given `{s ↮ t}`, functions of
`(C_s, C_t)` increasing in `C_s` and decreasing in `C_t` are positively associated.** Printed:
"Let `s` and `t` be (distinct) vertices, and `f` and `g` bounded, measurable functions of
`(C_s, C_t)`, each increasing in `C_s` and decreasing in `C_t`. Then
`E[f g | s ↮ t] ≥ E[f | s ↮ t] E[g | s ↮ t]`" (bond percolation with arbitrary edge
probabilities `p_e`; "it is enough to prove this for finite `G`").  Stated for a finite vertex
type `V`, `μ = prodBernoulli w` on `Set (Sym2 V)` (each `e` open independently with probability
`w e`), `D = {ω | ¬ (openGraph ω).Reachable s t}` (`= {s ↮ t}`), `f ω = F (C_s ω) (C_t ω)`,
`g ω = G (C_s ω) (C_t ω)` with `F, G` monotone in the first and antitone in the second variable
(`C_s = openEdgeCluster ω s`), in the denominator-free form
`(∫_D f dμ)(∫_D g dμ) ≤ μ(D) · ∫_D f g dμ` (for `μ(D) > 0` this is the printed inequality of
conditional expectations; for `μ(D) = 0` both sides vanish).  Users take `(h : BHK2006_twoClusterConditionalAssociation)`, supplied by
`BHK2006_twoClusterConditionalAssociation_holds`.
[cite: VandenbergHaggstromKahn2005, Thm. 1.5 (p. 7, eq. (9)), proof pp. 7–8 (from Thm. 1.3 and Harris)] -/
def BHK2006_twoClusterConditionalAssociation : Prop :=
  ∀ (V : Type v) [Fintype V] (w : Sym2 V → unitInterval) (s t : V)
    (F G : Set (Sym2 V) → Set (Sym2 V) → ℝ),
    (∀ D, Monotone fun C => F C D) → (∀ C, Antitone fun D => F C D) →
    (∀ D, Monotone fun C => G C D) → (∀ C, Antitone fun D => G C D) → s ≠ t →
    (∫ ω in {ω : BondConfig V | ¬ (openGraph ω).Reachable s t},
        F (openEdgeCluster ω s) (openEdgeCluster ω t) ∂(prodBernoulli w)) *
      (∫ ω in {ω : BondConfig V | ¬ (openGraph ω).Reachable s t},
        G (openEdgeCluster ω s) (openEdgeCluster ω t) ∂(prodBernoulli w)) ≤
    (prodBernoulli w).real {ω : BondConfig V | ¬ (openGraph ω).Reachable s t} *
      ∫ ω in {ω : BondConfig V | ¬ (openGraph ω).Reachable s t},
        F (openEdgeCluster ω s) (openEdgeCluster ω t) * G (openEdgeCluster ω s) (openEdgeCluster ω t)
          ∂(prodBernoulli w)

/-- **van den Berg–Häggström–Kahn (2006), Theorem 1.4 — `C_s` and `C_t` are negatively correlated
given `{s ↮ t}`** (proved from Thm. 1.5, as printed: it is "contained" in 1.5, namely 1.5 for the
pair `(f, -g)`): for `f = F ∘ C_s`, `g = G ∘ C_t` with `F, G` increasing,
`μ(D) · ∫_D f g dμ ≤ (∫_D f dμ)(∫_D g dμ)`, `D = {s ↮ t}` — the denominator-free form of
"`E[f g | s ↮ t] ≤ E[f | s ↮ t] E[g | s ↮ t]`".
[cite: VandenbergHaggstromKahn2005, Thm. 1.4 (p. 7)] -/
theorem BHK2006_twoClusterConditionalAssociation.negCorrelation
    (h : BHK2006_twoClusterConditionalAssociation.{v}) (V : Type v) [Fintype V]
    (w : Sym2 V → unitInterval) (s t : V) (F G : Set (Sym2 V) → ℝ)
    (hF : Monotone F) (hG : Monotone G) (hst : s ≠ t) :
    (prodBernoulli w).real {ω : BondConfig V | ¬ (openGraph ω).Reachable s t} *
      (∫ ω in {ω : BondConfig V | ¬ (openGraph ω).Reachable s t},
        F (openEdgeCluster ω s) * G (openEdgeCluster ω t) ∂(prodBernoulli w)) ≤
    (∫ ω in {ω : BondConfig V | ¬ (openGraph ω).Reachable s t},
        F (openEdgeCluster ω s) ∂(prodBernoulli w)) *
      ∫ ω in {ω : BondConfig V | ¬ (openGraph ω).Reachable s t},
        G (openEdgeCluster ω t) ∂(prodBernoulli w) := by
  have key := h V w s t (fun C _ => F C) (fun _ D => -G D) (fun _ => hF)
    (fun _ => antitone_const) (fun _ => monotone_const) (fun _ _ _ hDD' => neg_le_neg (hG hDD'))
    hst
  simp only [mul_neg, integral_neg] at key
  linarith

/-- **van den Berg–Häggström–Kahn (2006), eq. (2)** (proved from Thm. 1.4 with `f = 1{s ↔ a}`,
`g = 1{t ↔ b}`, as printed): `P(s↔a, t↔b, D) · P(D) ≤ P(s↔a, D) · P(t↔b, D)` for
`D = {s ↮ t}`, i.e. "`Pr(s ↔ a, t ↔ b | s ↮ t) ≤ Pr(s ↔ a | s ↮ t) Pr(t ↔ b | s ↮ t)`" when
`P(D) > 0`. [cite: VandenbergHaggstromKahn2005, eq. (2) (p. 2) and Thm. 1.4 (p. 7, "Note that (2) is the special case …")] -/
theorem BHK2006_twoClusterConditionalAssociation.openConn_negCorrelation
    (h : BHK2006_twoClusterConditionalAssociation.{v}) (V : Type v) [Fintype V]
    (w : Sym2 V → unitInterval) (s t a b : V) (hst : s ≠ t) :
    (prodBernoulli w).real (openConn s t)ᶜ *
        (prodBernoulli w).real ((openConn s t)ᶜ ∩ (openConn s a ∩ openConn t b)) ≤
      (prodBernoulli w).real ((openConn s t)ᶜ ∩ openConn s a) *
        (prodBernoulli w).real ((openConn s t)ᶜ ∩ openConn t b) := by
  have key := h.negCorrelation V w s t (connIndicatorFn s a) (connIndicatorFn t b)
    (monotone_connIndicatorFn s a) (monotone_connIndicatorFn t b) hst
  have hD : {ω : BondConfig V | ¬ (openGraph ω).Reachable s t} = (openConn s t)ᶜ := rfl
  have hma : MeasurableSet (openConn s a : Set (BondConfig V)) := measurableSet_openConn_holds s a
  have hmb : MeasurableSet (openConn t b : Set (BondConfig V)) := measurableSet_openConn_holds t b
  simp only [connIndicatorFn_openEdgeCluster, hD] at key
  rw [show (fun ω : BondConfig V => (openConn s a).indicator (1 : BondConfig V → ℝ) ω *
        (openConn t b).indicator 1 ω) = (openConn s a ∩ openConn t b).indicator 1 from
      funext fun ω => (congrFun (Set.inter_indicator_one (s := openConn s a)
        (t := openConn t b) (M₀ := ℝ)) ω).symm] at key
  rw [setIntegral_indicator (hma.inter hmb), setIntegral_indicator hma, setIntegral_indicator hmb]
    at key
  simpa only [Pi.one_apply, setIntegral_const, smul_eq_mul, mul_one] using key

end Percolation.Literature

end
