import Percolation.Continuity.CovTau.Transfer
import Percolation.Continuity.HullPort.TACE
import Percolation.Continuity.LowerTail.SurplusTransferPairOfCov
import Percolation.Util.Linter

/-!
# COV(τ) IS MDL(X): the conditioned covariance transfer, (S5)₂, (GEN) for three relays and Kozma–Nitzan's Conjecture 1 for `|A| = 3`, UNCONDITIONALLY, from the `T_A` chain

OBSERVATION.  The conditioned covariance transfer

  COV(τ):  `Cov(f(C_x), 1{x ↔ o} | x ↮ y) ≥ μ(v ↔ o | v ↮ x, v ↮ y) · Cov(f(C_x), 1{x ↔ v} | x ↮ y)`   (`f` monotone),

is LITERALLY the functional marker dominance lemma MDL(X) of the `HullPort` files under the
dictionary `(s, X, y, z) := (x, {y}, v, o)`: `Cov_{s↮X}(F(C_s), 1{s↔z}) ≥ μ(y↔z | y ↮ X ∪ {s}) ·
Cov_{s↮X}(F(C_s), 1{s↔y})`. So nothing is left to assume:

* `CovTau.ta_nonneg` — `T_A ≥ 0` for all `(s, y, z, X)`, all non-degenerate weights, all monotone `g ≥ 0` (hypothesis `hTA` of
  `HullPort.markerDominanceAvoid_of_TA`, proved).
* `CovTau.markerDominanceAvoid` — MDL(X) for every finite avoided set `X` and every monotone `F` (no hypothesis).

(A second, independent proof of the same inequality — (★_N) + two-source Lemma A2 by an Ahlswede–Daykin induction,
files `Continuity/CovTau/A2*`, `Continuity/CovTau/StarN*` — also starts from Gladkov's Theorem 3.2.)
[cite: VandenbergHaggstromKahn2005, Thms. 1.3–1.5 (pp. 6–8), §2.1 (pp. 9–13)] [cite: KozmaNitzan2024, Conj. 1 (p. 3), Conj. 4 (p. 32)]
[cite: Gladkov2024, Thm. 3.2]
-/

noncomputable section

namespace Percolation.Continuity

open MeasureTheory Set Percolation.Literature.LatticeModels Percolation.Literature
open scoped Classical

namespace CovTau

variable {V : Type*} [Fintype V]

/-- **`T_A ≥ 0`, unconditionally** (K-decomposition functional of the marker dominance lemma; owner `s`, avoided
set `X`, markers `y, z`; all non-degenerate weights `p`, all monotone `g ≥ 0`) — exactly the hypothesis `hTA` of
`HullPort.markerDominanceAvoid_of_TA`, proved by `HullPort.TA_of_PvI` + `HullPort.PvI_of_CE` + `HullPort.CE_holds`.
[cite: Gladkov2024, Thm. 3.2] [cite: VandenbergHaggstromKahn2005, Thm. 1.3 (p. 6)] -/
theorem ta_nonneg (s y z : V) (X : Set V) (hsy : s ≠ y) :
    ∀ p : Sym2 V → unitInterval, (∀ e, 0 < p e ∧ p e < 1) →
      ∀ g : Set (Sym2 V) → ℝ, Monotone g → (∀ C, 0 ≤ g C) →
      0 ≤ ∫ ω in {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x},
        ((prodBernoulli p).real {ω' : BondConfig V | ∀ x ∈ insert s X, ¬ (openGraph ω').Reachable y x} *
              ((prodBernoulli p).real ((· \ {e : Sym2 V | ∃ v ∈ e, ∃ x ∈ X, (openGraph ω).Reachable x v}) ⁻¹'
                  ((openConn s y : Set (BondConfig V))ᶜ ∩ openConn y z)) /
                (prodBernoulli p).real ((· \ {e : Sym2 V | ∃ v ∈ e, ∃ x ∈ X, (openGraph ω).Reachable x v}) ⁻¹'
                  ((openConn s y : Set (BondConfig V))ᶜ))) -
            (prodBernoulli p).real ({ω' : BondConfig V | ∀ x ∈ insert s X, ¬ (openGraph ω').Reachable y x} ∩
              openConn y z)) *
          ((∫ η in (· \ {e : Sym2 V | ∃ v ∈ e, ∃ x ∈ X, (openGraph ω).Reachable x v}) ⁻¹'
                (openConn s y : Set (BondConfig V)),
                g (openEdgeCluster (η \ {e : Sym2 V | ∃ v ∈ e, ∃ x ∈ X, (openGraph ω).Reachable x v}) s)
                ∂(prodBernoulli p)) -
            (∫ η, g (openEdgeCluster (η \ {e : Sym2 V | ∃ v ∈ e, ∃ x ∈ X, (openGraph ω).Reachable x v}) s)
              ∂(prodBernoulli p)) *
              (prodBernoulli p).real ((· \ {e : Sym2 V | ∃ v ∈ e, ∃ x ∈ X, (openGraph ω).Reachable x v}) ⁻¹'
                (openConn s y : Set (BondConfig V))))
        ∂(prodBernoulli p) :=
  HullPort.TA_of_PvI s y z X hsy
    (HullPort.PvI_of_CE s y hsy (fun U hU q _ v => HullPort.CE_holds s y U hU q v))

/-- **MDL(X), unconditionally** — the functional marker dominance lemma with an avoided set: for the owner `s`, a finite
avoided set `X`, markers `y ≠ s` and `z`, and every monotone `F` of the open edge cluster of `s`,
`μ(y ↮ X∪{s}, y ↔ z) · cov_D(F, 1{s↔y}) ≤ μ(y ↮ X∪{s}) · cov_D(F, 1{s↔z})`, `D = {s ↮ X}`,
`cov_D(F, 1_A) = μ(D) ∫_{D∩A} F − (∫_D F) μ(D∩A)`.  (`HullPort.markerDominanceAvoid_of_TA` + `ta_nonneg`.)
[cite: VandenbergHaggstromKahn2005, §2.1 (pp. 9–13)] [cite: Gladkov2024, Thm. 3.2] -/
theorem markerDominanceAvoid (w : Sym2 V → unitInterval) (s y z : V) (X : Set V) (hsy : s ≠ y)
    (F : Set (Sym2 V) → ℝ) (hF : Monotone F) :
    (prodBernoulli w).real ({ω : BondConfig V | ∀ x ∈ insert s X, ¬ (openGraph ω).Reachable y x} ∩ openConn y z) *
        ((prodBernoulli w).real {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x} *
            (∫ ω in {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x} ∩ openConn s y,
              F (openEdgeCluster ω s) ∂(prodBernoulli w)) -
          (∫ ω in {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x},
              F (openEdgeCluster ω s) ∂(prodBernoulli w)) *
            (prodBernoulli w).real ({ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x} ∩ openConn s y)) ≤
      (prodBernoulli w).real {ω : BondConfig V | ∀ x ∈ insert s X, ¬ (openGraph ω).Reachable y x} *
        ((prodBernoulli w).real {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x} *
            (∫ ω in {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x} ∩ openConn s z,
              F (openEdgeCluster ω s) ∂(prodBernoulli w)) -
          (∫ ω in {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x},
              F (openEdgeCluster ω s) ∂(prodBernoulli w)) *
            (prodBernoulli w).real ({ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x} ∩ openConn s z)) :=
  HullPort.markerDominanceAvoid_of_TA w s y z X hsy (ta_nonneg s y z X hsy) F hF

/-- [cite: VandenbergHaggstromKahn2005, Thms. 1.3–1.4 (pp. 6–7), §2.1 (pp. 9–13)] [cite: Gladkov2024,
 Thm. 3.2]
-/
theorem covTau (w : Sym2 V → unitInterval) (x y o v : V) (hvx : v ≠ x)
    (f : Set (Sym2 V) → ℝ) (hf : Monotone f) :
    (prodBernoulli w).real ({ω : BondConfig V | ¬ (openGraph ω).Reachable v x} ∩
          {ω | ¬ (openGraph ω).Reachable v y} ∩ openConn v o) *
        ((prodBernoulli w).real {ω : BondConfig V | ¬ (openGraph ω).Reachable x y} *
            (∫ ω in {ω : BondConfig V | ¬ (openGraph ω).Reachable x y} ∩ openConn x v,
              f (openEdgeCluster ω x) ∂(prodBernoulli w)) -
          (∫ ω in {ω : BondConfig V | ¬ (openGraph ω).Reachable x y},
              f (openEdgeCluster ω x) ∂(prodBernoulli w)) *
            (prodBernoulli w).real ({ω : BondConfig V | ¬ (openGraph ω).Reachable x y} ∩ openConn x v)) ≤
      (prodBernoulli w).real ({ω : BondConfig V | ¬ (openGraph ω).Reachable v x} ∩
          {ω | ¬ (openGraph ω).Reachable v y}) *
        ((prodBernoulli w).real {ω : BondConfig V | ¬ (openGraph ω).Reachable x y} *
            (∫ ω in {ω : BondConfig V | ¬ (openGraph ω).Reachable x y} ∩ openConn x o,
              f (openEdgeCluster ω x) ∂(prodBernoulli w)) -
          (∫ ω in {ω : BondConfig V | ¬ (openGraph ω).Reachable x y},
              f (openEdgeCluster ω x) ∂(prodBernoulli w)) *
            (prodBernoulli w).real ({ω : BondConfig V | ¬ (openGraph ω).Reachable x y} ∩ openConn x o)) := by
  have h := markerDominanceAvoid w x v o ({y} : Set V) hvx.symm f hf
  have e1 : {ω : BondConfig V | ∀ x' ∈ ({y} : Set V), ¬ (openGraph ω).Reachable x x'} =
      {ω : BondConfig V | ¬ (openGraph ω).Reachable x y} := by
    ext ω
    simp only [mem_setOf_eq, mem_singleton_iff, forall_eq]
  have e2 : {ω : BondConfig V | ∀ x' ∈ insert x ({y} : Set V), ¬ (openGraph ω).Reachable v x'} =
      {ω : BondConfig V | ¬ (openGraph ω).Reachable v x} ∩ {ω | ¬ (openGraph ω).Reachable v y} := by
    ext ω
    simp only [mem_setOf_eq, mem_inter_iff, mem_insert_iff, mem_singleton_iff, forall_eq_or_imp, forall_eq]
  rw [e1, e2] at h
  exact h

/-- **COV(τ) for the Kozma–Nitzan functional `F(C(b)) − F(C(a))`, unconditionally** (the hypothesis `hCOV` of
`SurplusTransfer.surplusTransfer_pair_of_covTransfer`): `CovTau.covTransfer_of_covTau` applied to `covTau` for the projected
functional of `CovTau.monotone_projFun`. [cite: VandenbergHaggstromKahn2005, §2.1 Lemma 2.4 (p. 10)] [cite: KozmaNitzan2024, Conj. 4 (p. 32)] -/
theorem covTransfer (w : Sym2 V → unitInterval) (o v a b : V) (hvb : v ≠ b)
    (F : Set V → ℝ) (hF : ∀ S T : Set V, S ⊆ T → F S ≤ F T) :
    (prodBernoulli w).real (({ω : BondConfig V | ¬ (openGraph ω).Reachable v a} ∩ {ω | ¬ (openGraph ω).Reachable v b}) ∩
              openConn o v) *
        ((prodBernoulli w).real ((openConn a b)ᶜ : Set (BondConfig V)) *
            ∫ ω in (openConn v b ∩ (openConn a b)ᶜ : Set (BondConfig V)), (F (openCluster ω b) - F (openCluster ω a)) ∂(prodBernoulli w) -
          (prodBernoulli w).real (openConn v b ∩ (openConn a b)ᶜ : Set (BondConfig V)) *
            ∫ ω in ((openConn a b)ᶜ : Set (BondConfig V)), (F (openCluster ω b) - F (openCluster ω a)) ∂(prodBernoulli w)) ≤
      (prodBernoulli w).real ({ω : BondConfig V | ¬ (openGraph ω).Reachable v a} ∩ {ω | ¬ (openGraph ω).Reachable v b}) *
        ((prodBernoulli w).real ((openConn a b)ᶜ : Set (BondConfig V)) *
            ∫ ω in (openConn o b ∩ (openConn a b)ᶜ : Set (BondConfig V)), (F (openCluster ω b) - F (openCluster ω a)) ∂(prodBernoulli w) -
          (prodBernoulli w).real (openConn o b ∩ (openConn a b)ᶜ : Set (BondConfig V)) *
            ∫ ω in ((openConn a b)ᶜ : Set (BondConfig V)), (F (openCluster ω b) - F (openCluster ω a)) ∂(prodBernoulli w)) :=
  covTransfer_of_covTau w o v a b F (covTau w b a o v hvb _ (monotone_projFun w a b F hF))

/-- **(GEN) for three relays, unconditionally**: for `F` monotone nonnegative on vertex sets, an observer `o`, relays with
`m₁ ≤ m₂ ≤ m₃`, `a₃ ≠ a₁, a₂`:
`μ(o↔a₁)·m₁ + μ(o↔a₂, o↮a₁)·m₂ + μ(o↔a₃, o↮a₁, o↮a₂)·m₃ ≤ ∫_{o ↔ {a₁,a₂,a₃}} F(C(o))`.
[cite: KozmaNitzan2024, Conj. 4 (p. 32)] [cite: VandenbergHaggstromKahn2005, Thms. 1.3–1.5 (pp. 6–8)] -/
theorem gen_triple (w : Sym2 V → unitInterval) (o a₁ a₂ a₃ : V) (h31 : a₃ ≠ a₁) (h32 : a₃ ≠ a₂)
    (F : Set V → ℝ) (hF : ∀ S T : Set V, S ⊆ T → F S ≤ F T) (hF0 : ∀ S, 0 ≤ F S)
    (hm12 : ∫ ω, F (openCluster ω a₁) ∂(prodBernoulli w) ≤ ∫ ω, F (openCluster ω a₂) ∂(prodBernoulli w))
    (hm23 : ∫ ω, F (openCluster ω a₂) ∂(prodBernoulli w) ≤ ∫ ω, F (openCluster ω a₃) ∂(prodBernoulli w)) :
    (prodBernoulli w).real (openConn o a₁) * ∫ ω, F (openCluster ω a₁) ∂(prodBernoulli w) +
        (prodBernoulli w).real (openConn o a₂ ∩ (openConn o a₁)ᶜ : Set (BondConfig V)) *
          ∫ ω, F (openCluster ω a₂) ∂(prodBernoulli w) +
        (prodBernoulli w).real (openConn o a₃ ∩ (openConn o a₁ ∪ openConn o a₂)ᶜ : Set (BondConfig V)) *
          ∫ ω, F (openCluster ω a₃) ∂(prodBernoulli w) ≤
      ∫ ω in (openConn o a₁ ∪ openConn o a₂ ∪ openConn o a₃), F (openCluster ω o) ∂(prodBernoulli w) :=
  SurplusTransfer.gen_triple_of_covTransfer w o a₁ a₂ a₃ h31 h32 F hF hF0 hm12 hm23
    (covTransfer w o a₃ a₁ a₂ h32 F hF)

/-- **Kozma–Nitzan's Conjecture 1 for three relays, unconditionally** (relays ordered `μ(a₁↔b') ≤
 μ(a₂↔b') ≤ μ(a₃↔b')`, `a₃ ≠ a₁, a₂`): if `t ≤ μ(a_i ↔ b')` for all `i` then `t · μ(o ↔ {a₁,a₂,a₃})
 ≤ μ(o ↔ b')`. Proof: `gen_triple` at `F = 1{b' ∈ ·}`. [cite: KozmaNitzan2024, Conj. 1 (p. 3)]
-/
theorem kn_conj1_three (w : Sym2 V → unitInterval) (o b' a₁ a₂ a₃ : V) (h31 : a₃ ≠ a₁) (h32 : a₃ ≠ a₂)
    (hm12 : (prodBernoulli w).real (openConn a₁ b') ≤ (prodBernoulli w).real (openConn a₂ b'))
    (hm23 : (prodBernoulli w).real (openConn a₂ b') ≤ (prodBernoulli w).real (openConn a₃ b'))
    (t : ℝ) (ht1 : t ≤ (prodBernoulli w).real (openConn a₁ b')) :
    t * (prodBernoulli w).real (openConn o a₁ ∪ openConn o a₂ ∪ openConn o a₃ : Set (BondConfig V)) ≤
      (prodBernoulli w).real (openConn o b') := by
  classical
  set μ := prodBernoulli w with hμ
  have hmeas : ∀ S : Set (BondConfig V), MeasurableSet S := fun _ => MeasurableSet.of_discrete
  have hn := fun (S : Set (BondConfig V)) => (measureReal_nonneg : 0 ≤ μ.real S)
  -- the set function `F = 1{b' ∈ ·}`
  set F : Set V → ℝ := fun M => if b' ∈ M then 1 else 0 with hF
  have hFmono : ∀ S T : Set V, S ⊆ T → F S ≤ F T := by
    intro S T hST
    simp only [hF]
    by_cases hS : b' ∈ S
    · rw [if_pos hS, if_pos (hST hS)]
    · rw [if_neg hS]
      split_ifs <;> norm_num
  have hF0 : ∀ S, 0 ≤ F S := by
    intro S
    simp only [hF]
    split_ifs <;> norm_num
  have hFind : ∀ x : V, (fun ω : BondConfig V => F (openCluster ω x)) =
      (openConn x b' : Set (BondConfig V)).indicator 1 := by
    intro x
    funext ω
    simp only [hF]
    by_cases hω : ω ∈ (openConn x b' : Set (BondConfig V))
    · rw [Set.indicator_of_mem hω, Pi.one_apply, if_pos (show b' ∈ openCluster ω x from hω)]
    · rw [Set.indicator_of_notMem hω, if_neg (show b' ∉ openCluster ω x from hω)]
  have hint : ∀ x : V, ∫ ω, F (openCluster ω x) ∂μ = μ.real (openConn x b') := by
    intro x
    rw [hFind x, integral_indicator_one (hmeas _)]
  have hsetint : ∀ (x : V) (S : Set (BondConfig V)),
      ∫ ω in S, F (openCluster ω x) ∂μ = μ.real (S ∩ openConn x b' : Set (BondConfig V)) := by
    intro x S
    rw [hFind x, ← integral_indicator (hmeas _), Set.indicator_indicator,
      integral_indicator_one ((hmeas _).inter (hmeas _))]
  have key := gen_triple w o a₁ a₂ a₃ h31 h32 F hFmono hF0
    (by rw [hint, hint]; exact hm12) (by rw [hint, hint]; exact hm23)
  rw [hint, hint, hint, hsetint] at key
  -- `Σ μ(P_i) = μ(U)` and `t ≤ m_i`
  set U : Set (BondConfig V) := openConn o a₁ ∪ openConn o a₂ ∪ openConn o a₃ with hU
  have hP : μ.real U = μ.real (openConn o a₁) + μ.real (openConn o a₂ ∩ (openConn o a₁)ᶜ : Set (BondConfig V)) +
      μ.real (openConn o a₃ ∩ (openConn o a₁ ∪ openConn o a₂)ᶜ : Set (BondConfig V)) := by
    have h1 : μ.real U = μ.real (U ∩ (openConn o a₁ ∪ openConn o a₂)) +
        μ.real (U \ (openConn o a₁ ∪ openConn o a₂)) :=
      (measureReal_inter_add_sdiff (s := U) (h := measure_ne_top _ _) ((hmeas _).union (hmeas _))).symm
    have h2 : μ.real (openConn o a₁ ∪ openConn o a₂ : Set (BondConfig V)) =
        μ.real ((openConn o a₁ ∪ openConn o a₂ : Set (BondConfig V)) ∩ openConn o a₁) +
          μ.real ((openConn o a₁ ∪ openConn o a₂ : Set (BondConfig V)) \ openConn o a₁) :=
      (measureReal_inter_add_sdiff (s := (openConn o a₁ ∪ openConn o a₂ : Set (BondConfig V)))
        (h := measure_ne_top _ _) (hmeas _)).symm
    rw [inter_eq_right.2 subset_union_left, hU, Set.union_sdiff_left, Set.sdiff_eq] at h1
    rw [inter_eq_right.2 subset_union_left, Set.union_sdiff_left, Set.sdiff_eq] at h2
    rw [hU, h1, h2]
  have ht2 : t ≤ μ.real (openConn a₂ b') := ht1.trans hm12
  have ht3 : t ≤ μ.real (openConn a₃ b') := ht2.trans hm23
  have hmono : μ.real (U ∩ openConn o b' : Set (BondConfig V)) ≤ μ.real (openConn o b') :=
    measureReal_mono inter_subset_right (measure_ne_top _ _)
  rw [hP]
  nlinarith [key, hmono, hn (openConn o a₁), hn (openConn o a₂ ∩ (openConn o a₁)ᶜ),
    hn (openConn o a₃ ∩ (openConn o a₁ ∪ openConn o a₂)ᶜ),
    mul_le_mul_of_nonneg_right ht1 (hn (openConn o a₁)),
    mul_le_mul_of_nonneg_right ht2 (hn (openConn o a₂ ∩ (openConn o a₁)ᶜ)),
    mul_le_mul_of_nonneg_right ht3 (hn (openConn o a₃ ∩ (openConn o a₁ ∪ openConn o a₂)ᶜ))]

end CovTau

end Percolation.Continuity

end
