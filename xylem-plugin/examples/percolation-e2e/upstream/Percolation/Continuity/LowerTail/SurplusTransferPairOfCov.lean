import Percolation.Continuity.AdditiveGluing.SurplusTransfer
import Percolation.Continuity.LowerTail.SurplusTransferPairTools
import Percolation.Util.Linter

/-!
# The two-relay surplus transfer (S5)₂ from the conditioned covariance transfer

`μ = prodBernoulli w`, `F` monotone nonnegative on vertex sets, relays `a, b` with `m_a ≤ m_b`, observers `o, v`;
`Q = {a ↮ b}`, `D = {v ↮ a} ∩ {v ↮ b}`,
`S15_x = μ(Q)·∫_{{x↔b}∩Q} (F(C_b) − F(C_a)) − μ({x↔b}∩Q)·∫_Q (F(C_b) − F(C_a)) = μ(Q)²·Cov(F(C_b) − F(C_a), 1{x∈C_b} | a ↮ b)`.

* `SurplusTransfer.surplusTransfer_pair_of_covTransfer` — (S5)₂ (see `Continuity/AdditiveGluing/SurplusTransfer.lean`) from
  (COV) `μ(D ∩ {o↔v})·S15_v ≤ μ(D)·S15_o`, i.e. `Cov(h, 1{o∈C_b} | a↮b) ≥ μ(o↔v | v↮a, v↮b)·Cov(h, 1{v∈C_b} | a↮b)` for
  `h = F(C_b) − F(C_a)`, the conditioned covariance transfer with the constant `τ = μ(o↔v | v↮a, v↮b)` (projecting on `σ(C_b)`,
  `h` may be replaced by the increasing functional `F(C_b) − E[F(C_a) | C_b]` of the owner's cluster alone:
  `Continuity/CovTau/Transfer.lean`), using the tools of `Continuity/LowerTail/SurplusTransferPairTools.lean`;
* `SurplusTransfer.gen_triple_of_covTransfer` — hence (GEN) for three relays (`AGloc.gen_triple_of_surplusTransfer_pair`).
[cite: VandenbergHaggstromKahn2005, Thms. 1.3–1.5 (pp. 6–8)] [cite: KozmaNitzan2024, Conj. 1 (p. 3), Conj. 4 (p. 32)] [cite: Gladkov2024, Thm. 3.2]
-/

noncomputable section

namespace Percolation.Continuity.SurplusTransfer

open MeasureTheory Set
open Percolation.Literature.LatticeModels (prodBernoulli)
open Percolation.Literature Percolation.Literature.KNPreFKG
open Percolation.Literature.TwoSetExchange

variable {V : Type*} [Fintype V]

theorem surplusTransfer_pair_of_covTransfer (w : Sym2 V → unitInterval) (o v a b : V) (hva : v ≠ a) (hvb : v ≠ b)
    (F : Set V → ℝ) (hF : ∀ S T : Set V, S ⊆ T → F S ≤ F T) (hF0 : ∀ S, 0 ≤ F S)
    (hmab : ∫ ω, F (openCluster ω a) ∂(prodBernoulli w) ≤ ∫ ω, F (openCluster ω b) ∂(prodBernoulli w))
    (hCOV : (prodBernoulli w).real (({ω : BondConfig V | ¬ (openGraph ω).Reachable v a} ∩ {ω | ¬ (openGraph ω).Reachable v b}) ∩
              openConn o v) *
        ((prodBernoulli w).real ((openConn a b)ᶜ : Set (BondConfig V)) *
            ∫ ω in (openConn v b ∩ (openConn a b)ᶜ : Set (BondConfig V)), (F (openCluster ω b) - F (openCluster ω a)) ∂(prodBernoulli w) -
          (prodBernoulli w).real (openConn v b ∩ (openConn a b)ᶜ : Set (BondConfig V)) *
            ∫ ω in ((openConn a b)ᶜ : Set (BondConfig V)), (F (openCluster ω b) - F (openCluster ω a)) ∂(prodBernoulli w)) ≤
      (prodBernoulli w).real ({ω : BondConfig V | ¬ (openGraph ω).Reachable v a} ∩ {ω | ¬ (openGraph ω).Reachable v b}) *
        ((prodBernoulli w).real ((openConn a b)ᶜ : Set (BondConfig V)) *
            ∫ ω in (openConn o b ∩ (openConn a b)ᶜ : Set (BondConfig V)), (F (openCluster ω b) - F (openCluster ω a)) ∂(prodBernoulli w) -
          (prodBernoulli w).real (openConn o b ∩ (openConn a b)ᶜ : Set (BondConfig V)) *
            ∫ ω in ((openConn a b)ᶜ : Set (BondConfig V)), (F (openCluster ω b) - F (openCluster ω a)) ∂(prodBernoulli w))) :
    (prodBernoulli w).real ({ω : BondConfig V | ¬ (openGraph ω).Reachable v a} ∩
          {ω : BondConfig V | ¬ (openGraph ω).Reachable v b} ∩ openConn o v) *
        (∫ ω in (openConn v a ∪ openConn v b), F (openCluster ω v) ∂(prodBernoulli w) -
          ((prodBernoulli w).real (openConn v a) * ∫ ω, F (openCluster ω a) ∂(prodBernoulli w) +
            (prodBernoulli w).real (openConn v b ∩ (openConn v a)ᶜ : Set (BondConfig V)) *
              ∫ ω, F (openCluster ω b) ∂(prodBernoulli w))) ≤
      (prodBernoulli w).real ({ω : BondConfig V | ¬ (openGraph ω).Reachable v a} ∩
          {ω : BondConfig V | ¬ (openGraph ω).Reachable v b}) *
        (∫ ω in (openConn o a ∪ openConn o b), F (openCluster ω o) ∂(prodBernoulli w) -
          ((prodBernoulli w).real (openConn o a) * ∫ ω, F (openCluster ω a) ∂(prodBernoulli w) +
            (prodBernoulli w).real (openConn o b ∩ (openConn o a)ᶜ : Set (BondConfig V)) *
              ∫ ω, F (openCluster ω b) ∂(prodBernoulli w))) := by
  classical
  have hmeas : ∀ T : Set (BondConfig V), MeasurableSet T := fun _ => MeasurableSet.of_discrete
  -- the case `a = b` is (S5)₁
  by_cases hab : a = b
  · subst hab
    have h1 := AGloc.surplusTransfer_single w o v a hva F hF hF0
    have hI : ∀ x : V, ∫ ω in openConn x a, F (openCluster ω x) ∂(prodBernoulli w) =
        ∫ ω in openConn x a, F (openCluster ω a) ∂(prodBernoulli w) := fun x =>
      setIntegral_congr_fun (hmeas _) fun ω hω => by
        show F (openCluster ω x) = F (openCluster ω a)
        rw [openCluster_eq_of_reachable (hω : (openGraph ω).Reachable x a)]
    rw [inter_self, union_self, union_self, inter_compl_self, inter_compl_self, hI, hI]
    simp only [measureReal_empty, zero_mul, add_zero]
    exact h1
  -- the four proved transfers / signs (stated before the abbreviations, so that `set` rewrites them too)
  have hT1 := blockHarrisTransfer w o v a b F hF hF0
  have hT4 := ordTransfer w o v a b
  have hpos := plusPiece_nonneg w v a b hab F hF
  have hHar : (prodBernoulli w).real ({ω : BondConfig V | ¬ (openGraph ω).Reachable v a} ∩ {ω | ¬ (openGraph ω).Reachable v b}) *
      (prodBernoulli w).real ((openConn a b)ᶜ : Set (BondConfig V)) ≤
      (prodBernoulli w).real (({ω : BondConfig V | ¬ (openGraph ω).Reachable v a} ∩ {ω | ¬ (openGraph ω).Reachable v b}) ∩
        (openConn a b)ᶜ) :=
    Percolation.Literature.LatticeModels.prodBernoulli_harris_lower w
      (((isUpperSet_openConn v a).compl).inter (isUpperSet_openConn v b).compl) (isUpperSet_openConn a b).compl
      (hmeas _) (hmeas _)
  set μ := prodBernoulli w with hμ
  set fa : BondConfig V → ℝ := fun ω => F (openCluster ω a) with hfa
  set fb : BondConfig V → ℝ := fun ω => F (openCluster ω b) with hfb
  set ma : ℝ := ∫ ω, fa ω ∂μ with hma
  set mb : ℝ := ∫ ω, fb ω ∂μ with hmb
  have hint : ∀ (k : BondConfig V → ℝ) (T : Set (BondConfig V)), IntegrableOn k T μ :=
    fun k T => (Integrable.of_finite).integrableOn
  have hn := fun (S : Set (BondConfig V)) => (measureReal_nonneg : 0 ≤ μ.real S)
  set D : Set (BondConfig V) := {ω | ¬ (openGraph ω).Reachable v a} ∩ {ω | ¬ (openGraph ω).Reachable v b} with hD
  set Qc : Set (BondConfig V) := (openConn a b)ᶜ with hQc
  set Ov : Set (BondConfig V) := openConn o v with hOv
  -- cluster identities
  have hXbQ : ∀ x : V, (openConn x b ∩ (openConn x a)ᶜ : Set (BondConfig V)) = openConn x b ∩ Qc := by
    intro x; ext ω
    simp only [mem_inter_iff, mem_compl_iff, openConn, mem_setOf_eq, hQc]
    constructor
    · rintro ⟨hxb, hxa⟩; exact ⟨hxb, fun h => hxa (hxb.trans h.symm)⟩
    · rintro ⟨hxb, hq⟩; exact ⟨hxb, fun hxa => hq (hxa.symm.trans hxb)⟩
  have hdiff : ∀ x : V, (openConn x a ∪ openConn x b : Set (BondConfig V)) \ openConn x a = openConn x b ∩ Qc := by
    intro x; rw [← hXbQ x]; ext ω
    simp only [mem_sdiff, mem_union, mem_inter_iff, mem_compl_iff]; tauto
  -- `Sur_x` in terms of `fa`, `fb`
  have hSur : ∀ x : V, ∫ ω in (openConn x a ∪ openConn x b), F (openCluster ω x) ∂μ =
      ∫ ω in openConn x a, fa ω ∂μ + ∫ ω in openConn x b ∩ Qc, fb ω ∂μ := by
    intro x
    rw [← integral_inter_add_sdiff (hmeas (openConn x a)) (hint _ _), inter_eq_right.2 subset_union_left, hdiff x]
    congr 1
    · exact setIntegral_congr_fun (hmeas _) fun ω hω => by
        show F (openCluster ω x) = F (openCluster ω a)
        rw [openCluster_eq_of_reachable (hω : (openGraph ω).Reachable x a)]
    · exact setIntegral_congr_fun (hmeas _) fun ω hω => by
        show F (openCluster ω x) = F (openCluster ω b)
        rw [openCluster_eq_of_reachable (hω.1 : (openGraph ω).Reachable x b)]
  -- `SH_x` in terms of `fa`
  have hSH : ∀ x : V, ∫ ω in (openConn x a ∪ openConn x b), fa ω ∂μ =
      ∫ ω in openConn x a, fa ω ∂μ + ∫ ω in openConn x b ∩ Qc, fa ω ∂μ := by
    intro x
    rw [← integral_inter_add_sdiff (hmeas (openConn x a)) (hint _ _), inter_eq_right.2 subset_union_left, hdiff x]
  have hUμ : ∀ x : V, μ.real (openConn x a ∪ openConn x b : Set (BondConfig V)) = μ.real (openConn x a) + μ.real (openConn x b ∩ Qc) := by
    intro x
    rw [← measureReal_inter_add_sdiff (s := (openConn x a ∪ openConn x b : Set (BondConfig V))) (h := measure_ne_top _ _)
      (hmeas (openConn x a)), inter_eq_right.2 subset_union_left, hdiff x]
  -- `∫_{Qc} (fb - fa) = mb - ma`
  have hQint : ∫ ω in Qc, (fb ω - fa ω) ∂μ = mb - ma := by
    have h1 := integral_add_compl (hmeas (openConn a b : Set (BondConfig V))) (Integrable.of_finite (f := fun ω => fb ω - fa ω) (μ := μ))
    have h2 : ∫ ω in (openConn a b : Set (BondConfig V)), (fb ω - fa ω) ∂μ = 0 := by
      refine (setIntegral_congr_fun (hmeas _) (g := fun _ => (0 : ℝ)) fun ω hω => ?_).trans (by simp)
      show F (openCluster ω b) - F (openCluster ω a) = 0
      rw [openCluster_eq_of_reachable (hω : (openGraph ω).Reachable a b), sub_self]
    rw [h2, zero_add] at h1
    rw [hQc, h1, integral_sub (Integrable.of_finite) (Integrable.of_finite)]
  have hsubint : ∀ S : Set (BondConfig V), ∫ ω in S, (fb ω - fa ω) ∂μ = ∫ ω in S, fb ω ∂μ - ∫ ω in S, fa ω ∂μ :=
    fun S => integral_sub (hint fb S) (hint fa S)
  have hmab' : ma ≤ mb := hmab
  have hQc1 : μ.real Qc ≤ 1 := measureReal_le_one
  -- rewrite everything in terms of the pieces
  rw [hSur v, hSur o, hXbQ v, hXbQ o]
  rw [hSH v, hSH o, hUμ v, hUμ o] at hT1
  rw [hQint, hsubint, hsubint] at hCOV
  rw [hQint, hsubint] at hpos
  -- real arithmetic
  set P := μ.real Qc with hP
  set d := μ.real D with hd
  set dov := μ.real (D ∩ Ov) with hdov
  set IaO := ∫ ω in openConn o a, fa ω ∂μ
  set IaV := ∫ ω in openConn v a, fa ω ∂μ
  set IbO := ∫ ω in openConn o b ∩ Qc, fb ω ∂μ with hIbO
  set IbV := ∫ ω in openConn v b ∩ Qc, fb ω ∂μ with hIbV
  set JaO := ∫ ω in openConn o b ∩ Qc, fa ω ∂μ with hJaO
  set JaV := ∫ ω in openConn v b ∩ Qc, fa ω ∂μ with hJaV
  set xO := μ.real (openConn o b ∩ Qc) with hxO'
  set xV := μ.real (openConn v b ∩ Qc) with hxV'
  set yO := μ.real (openConn o a : Set (BondConfig V))
  set yV := μ.real (openConn v a : Set (BondConfig V))
  -- s15 pieces
  set sO := P * (IbO - JaO) - xO * (mb - ma) with hsO
  set sV := P * (IbV - JaV) - xV * (mb - ma) with hsV
  have hsV0 : 0 ≤ sV := by rw [hsV]; linarith [hpos]
  have hkey : dov * sV ≤ d * sO := by
    rw [hsO, hsV]
    exact hCOV
  -- assemble: `P·(want)` from `P·T1 + key + (1-P)(mb-ma)·T4`, then divide by `P` (or `P = 0`)
  have hT4' : dov * xV ≤ d * xO := hT4
  by_cases hP0 : P = 0
  · have hxO : xO = 0 := le_antisymm (hP0 ▸ measureReal_mono inter_subset_right (measure_ne_top _ _)) (hn _)
    have hxV : xV = 0 := le_antisymm (hP0 ▸ measureReal_mono inter_subset_right (measure_ne_top _ _)) (hn _)
    have hI0 : ∀ (k : BondConfig V → ℝ) (S : Set (BondConfig V)), μ.real (S ∩ Qc) = 0 → ∫ ω in S ∩ Qc, k ω ∂μ = 0 :=
      fun k S h0 => setIntegral_measure_zero k ((measureReal_eq_zero_iff (measure_ne_top _ _)).1 h0)
    have h1 : IbO = 0 := hI0 fb _ hxO
    have h2 : IbV = 0 := hI0 fb _ hxV
    have h3 : JaO = 0 := hI0 fa _ hxO
    have h4 : JaV = 0 := hI0 fa _ hxV
    rw [h1, h2, hxO, hxV]
    rw [h3, h4, hxO, hxV] at hT1
    simp only [add_zero, zero_mul] at hT1 ⊢
    exact hT1
  · have hPpos : 0 < P := lt_of_le_of_ne (hn _) (Ne.symm hP0)
    have hc : 0 ≤ (1 - P) * (mb - ma) := mul_nonneg (by linarith) (by linarith)
    have i1 : dov * (P * (IaV + JaV - (yV + xV) * ma)) ≤ d * (P * (IaO + JaO - (yO + xO) * ma)) :=
      calc dov * (P * (IaV + JaV - (yV + xV) * ma)) = P * (dov * (IaV + JaV - (yV + xV) * ma)) := by ring
        _ ≤ P * (d * (IaO + JaO - (yO + xO) * ma)) := mul_le_mul_of_nonneg_left hT1 (hn Qc)
        _ = d * (P * (IaO + JaO - (yO + xO) * ma)) := by ring
    have i3 : dov * ((1 - P) * (mb - ma) * xV) ≤ d * ((1 - P) * (mb - ma) * xO) :=
      calc dov * ((1 - P) * (mb - ma) * xV) = (1 - P) * (mb - ma) * (dov * xV) := by ring
        _ ≤ (1 - P) * (mb - ma) * (d * xO) := mul_le_mul_of_nonneg_left hT4' hc
        _ = d * ((1 - P) * (mb - ma) * xO) := by ring
    have split : ∀ (Ia Ib Ja x y : ℝ), P * (Ia + Ib - (y * ma + x * mb)) =
        P * (Ia + Ja - (y + x) * ma) + (P * (Ib - Ja) - x * (mb - ma)) + (1 - P) * (mb - ma) * x := by
      intro Ia Ib Ja x y; ring
    have hfinal : P * (dov * (IaV + IbV - (yV * ma + xV * mb))) ≤ P * (d * (IaO + IbO - (yO * ma + xO * mb))) :=
      calc P * (dov * (IaV + IbV - (yV * ma + xV * mb))) = dov * (P * (IaV + IbV - (yV * ma + xV * mb))) := by ring
        _ = dov * (P * (IaV + JaV - (yV + xV) * ma)) + dov * sV + dov * ((1 - P) * (mb - ma) * xV) := by
          rw [split IaV IbV JaV xV yV]; ring
        _ ≤ d * (P * (IaO + JaO - (yO + xO) * ma)) + d * sO + d * ((1 - P) * (mb - ma) * xO) := by
          linarith [i1, hkey, i3]
        _ = d * (P * (IaO + IbO - (yO * ma + xO * mb))) := by rw [split IaO IbO JaO xO yO]; ring
        _ = P * (d * (IaO + IbO - (yO * ma + xO * mb))) := by ring
    exact le_of_mul_le_mul_left hfinal hPpos

/-- **(GEN) for three relays from the conditioned covariance transfer with the weak constant.** For `F` monotone nonnegative, an
observer `o` and relays `a₁, a₂, a₃` with `m₁ ≤ m₂ ≤ m₃` (`m_i = ∫ F(C(a_i))`), `a₃ ≠ a₁, a₂`: IF (COV) holds with
`(a, b, v) = (a₁, a₂, a₃)`, THEN `μ(o↔a₁)·m₁ + μ(o↔a₂, o↮a₁)·m₂ + μ(o↔a₃, o↮a₁, o↮a₂)·m₃ ≤ ∫_{o ↔ {a₁,a₂,a₃}} F(C(o))`
(`surplusTransfer_pair_of_covTransfer` + `AGloc.gen_triple_of_surplusTransfer_pair`). [cite: KozmaNitzan2024, Conj. 4 (p. 32)] -/
theorem gen_triple_of_covTransfer (w : Sym2 V → unitInterval) (o a₁ a₂ a₃ : V) (h31 : a₃ ≠ a₁) (h32 : a₃ ≠ a₂)
    (F : Set V → ℝ) (hF : ∀ S T : Set V, S ⊆ T → F S ≤ F T) (hF0 : ∀ S, 0 ≤ F S)
    (hm12 : ∫ ω, F (openCluster ω a₁) ∂(prodBernoulli w) ≤ ∫ ω, F (openCluster ω a₂) ∂(prodBernoulli w))
    (hm23 : ∫ ω, F (openCluster ω a₂) ∂(prodBernoulli w) ≤ ∫ ω, F (openCluster ω a₃) ∂(prodBernoulli w))
    (hCOV : (prodBernoulli w).real (({ω : BondConfig V | ¬ (openGraph ω).Reachable a₃ a₁} ∩ {ω | ¬ (openGraph ω).Reachable a₃ a₂}) ∩
              openConn o a₃) *
        ((prodBernoulli w).real ((openConn a₁ a₂)ᶜ : Set (BondConfig V)) *
            ∫ ω in (openConn a₃ a₂ ∩ (openConn a₁ a₂)ᶜ : Set (BondConfig V)), (F (openCluster ω a₂) - F (openCluster ω a₁)) ∂(prodBernoulli w) -
          (prodBernoulli w).real (openConn a₃ a₂ ∩ (openConn a₁ a₂)ᶜ : Set (BondConfig V)) *
            ∫ ω in ((openConn a₁ a₂)ᶜ : Set (BondConfig V)), (F (openCluster ω a₂) - F (openCluster ω a₁)) ∂(prodBernoulli w)) ≤
      (prodBernoulli w).real ({ω : BondConfig V | ¬ (openGraph ω).Reachable a₃ a₁} ∩ {ω | ¬ (openGraph ω).Reachable a₃ a₂}) *
        ((prodBernoulli w).real ((openConn a₁ a₂)ᶜ : Set (BondConfig V)) *
            ∫ ω in (openConn o a₂ ∩ (openConn a₁ a₂)ᶜ : Set (BondConfig V)), (F (openCluster ω a₂) - F (openCluster ω a₁)) ∂(prodBernoulli w) -
          (prodBernoulli w).real (openConn o a₂ ∩ (openConn a₁ a₂)ᶜ : Set (BondConfig V)) *
            ∫ ω in ((openConn a₁ a₂)ᶜ : Set (BondConfig V)), (F (openCluster ω a₂) - F (openCluster ω a₁)) ∂(prodBernoulli w))) :
    (prodBernoulli w).real (openConn o a₁) * ∫ ω, F (openCluster ω a₁) ∂(prodBernoulli w) +
        (prodBernoulli w).real (openConn o a₂ ∩ (openConn o a₁)ᶜ : Set (BondConfig V)) *
          ∫ ω, F (openCluster ω a₂) ∂(prodBernoulli w) +
        (prodBernoulli w).real (openConn o a₃ ∩ (openConn o a₁ ∪ openConn o a₂)ᶜ : Set (BondConfig V)) *
          ∫ ω, F (openCluster ω a₃) ∂(prodBernoulli w) ≤
      ∫ ω in (openConn o a₁ ∪ openConn o a₂ ∪ openConn o a₃), F (openCluster ω o) ∂(prodBernoulli w) :=
  AGloc.gen_triple_of_surplusTransfer_pair w o a₁ a₂ a₃ h31 h32 F hF hF0 hm12 hm23
    (surplusTransfer_pair_of_covTransfer w o a₃ a₁ a₂ h31 h32 F hF hF0 hm12 hCOV)

end Percolation.Continuity.SurplusTransfer

end
