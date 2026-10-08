import Percolation.Continuity.AdditiveGluing.GenPair
import Percolation.Util.Linter

/-!
# The surplus-transfer inequality (S5) for one relay, and (GEN) for three relays from (S5) for two

For `F` monotone nonnegative on vertex sets, an observer `x` and a relay set `T` with `m_a := ∫ F(C(a))` sorted increasingly along
`T = {a₁, …, a_j}`, the (GEN)-surplus of `x` is `Sur_x(T) := ∫_{x ↔ T} F(C(x)) − Σ_i μ(x ↔ a_i, x ↮ a_1..a_{i-1})·m_{a_i}`
((GEN) for `(x, T)` says `Sur_x(T) ≥ 0`; for `|T| ≤ 2` this is `AGloc.gen_pair`). The surplus-transfer inequality is

  (S5)_T   `μ(v ↮ T) · Sur_o(T) ≥ μ(o ↔ v, v ↮ T) · Sur_v(T)`   ("`Sur_o ≥ P(o ↔ v | v ↮ T)·Sur_v`").

* `AGloc.surplusTransfer_single` — (S5) for `|T| = 1`: with `D = {v ↮ a}`,
  `μ(D)·Cov(F(C_a), 1_{o↔a}) − μ(D, o↔v)·Cov(F(C_a), 1_{v↔a}) = μ(D)·Cov(F(C_a), 1_{o ↔ {a,v}}) − μ(D)²·Cov(F(C_a), 1_{o↔v} | D)`,
  the first term `≥ 0` by Harris and the second `≥ 0` by the two-cluster inequality of van den Berg–Häggström–Kahn (Thm 1.4:
  `F(C_a)` and `{o ↔ v}` are negatively correlated given `a ↮ v`).
* `AGloc.gen_triple_of_surplusTransfer_pair` — (GEN) for three relays `a₁, a₂, a₃` (`m₁ ≤ m₂ ≤ m₃`) from (S5)_T for
  `T = {a₁, a₂}` and the second observer `v = a₃`: the (GEN)(3) defect splits as `Sur_o(T) − deficit₃` with
  `deficit₃ = m₃ μ(P₃) − ∫_{P₃} F(C(a₃))`, `P₃ = {o ↔ a₃} ∩ {a₃ ↮ T}`; the one-cluster inequality (vdBHK Thm 1.3, `C(a₃)` given
  `a₃ ↮ T`) gives `μ(a₃ ↮ T)·deficit₃ ≤ μ(P₃)·Sur_{a₃}(T)` (as `m₃` is maximal), and (S5)_T turns this into `μ(a₃ ↮ T)·Sur_o(T)`.
With the constant `μ(o ↔ v)` in place of `μ(o ↔ v | v ↮ T)`, (S5) is false.
[cite: VandenbergHaggstromKahn2005, Thms. 1.3–1.5 (pp. 6–8)] [cite: KozmaNitzan2024, Conj. 1 (p. 3), Conj. 4 and Thm. 7 (p. 32)]
-/

noncomputable section

namespace Percolation.Continuity.AGloc

open MeasureTheory Set
open Percolation.Literature.LatticeModels (prodBernoulli)
open Percolation.Literature Percolation.Literature.KNPreFKG

variable {V : Type*} [Fintype V]

/-- **Surplus transfer, one relay (S5)₁.** For `F` monotone nonnegative on vertex sets, a relay `a`, an observer `o` and a second
observer `v ≠ a`, with `m = ∫ F(C(a))` and `D = {v ↮ a}`:
`μ(D ∩ {o ↔ v}) · (∫_{v ↔ a} F(C(a)) − μ(v ↔ a)·m) ≤ μ(D) · (∫_{o ↔ a} F(C(a)) − μ(o ↔ a)·m)`,
i.e. `Cov(F(C_a), 1_{o↔a}) ≥ P(o ↔ v | v ↮ a)·Cov(F(C_a), 1_{v↔a})`.  Proof: Harris for `F(C_a)` on `{o ↔ a} ∪ {o ↔ v}` plus the
two-cluster BHK inequality for `F(C_a)` and `{o ↔ v}` given `v ↮ a`. [cite: VandenbergHaggstromKahn2005, Thm. 1.4 (p. 7)] -/
theorem surplusTransfer_single (w : Sym2 V → unitInterval) (o v a : V) (hva : v ≠ a) (F : Set V → ℝ)
    (hF : ∀ S T : Set V, S ⊆ T → F S ≤ F T) (hF0 : ∀ S, 0 ≤ F S) :
    (prodBernoulli w).real ({ω : BondConfig V | ¬ (openGraph ω).Reachable v a} ∩ openConn o v) *
        (∫ ω in openConn v a, F (openCluster ω a) ∂(prodBernoulli w) -
          (prodBernoulli w).real (openConn v a) * ∫ ω, F (openCluster ω a) ∂(prodBernoulli w)) ≤
      (prodBernoulli w).real {ω : BondConfig V | ¬ (openGraph ω).Reachable v a} *
        (∫ ω in openConn o a, F (openCluster ω a) ∂(prodBernoulli w) -
          (prodBernoulli w).real (openConn o a) * ∫ ω, F (openCluster ω a) ∂(prodBernoulli w)) := by
  classical
  set μ := prodBernoulli w with hμ
  set f : BondConfig V → ℝ := fun ω => F (openCluster ω a) with hf
  set m : ℝ := ∫ ω, f ω ∂μ with hm
  have hmeas : ∀ T : Set (BondConfig V), MeasurableSet T := fun _ => MeasurableSet.of_discrete
  have hint : ∀ (k : BondConfig V → ℝ) (T : Set (BondConfig V)), IntegrableOn k T μ :=
    fun k T => (Integrable.of_finite).integrableOn
  have hn := fun (S : Set (BondConfig V)) => (measureReal_nonneg : 0 ≤ μ.real S)
  set D : Set (BondConfig V) := {ω | ¬ (openGraph ω).Reachable v a} with hD
  set Oa : Set (BondConfig V) := openConn o a with hOa
  set Ov : Set (BondConfig V) := openConn o v with hOv
  set Q : Set (BondConfig V) := openConn v a with hQ
  set U : Set (BondConfig V) := Oa ∪ Ov with hU
  -- (1) Harris on `U`
  have hHarris : μ.real U * m ≤ ∫ ω in U, f ω ∂μ :=
    setIntegral_clusterFun_ge w a F hF hF0 U ((isUpperSet_openConn o a).union (isUpperSet_openConn o v))
  -- (2) two-cluster BHK: `F(C_a)` and `{o ↔ v}` are negatively correlated given `v ↮ a`
  have hind : ∀ ω : BondConfig V, (connFamily v o).indicator (1 : Set (Sym2 V) → ℝ) (openEdgeCluster ω v) =
      Ov.indicator (1 : BondConfig V → ℝ) ω := fun ω => by
    rw [congrFun (indicator_comp_openEdgeCluster (connFamily v o) v) ω, ← openConn_eq_setOf_connFamily, openConn_symm v o]
  have hprod : ∀ (T : Set (BondConfig V)) (k : BondConfig V → ℝ),
      ∫ ω in D, T.indicator (1 : BondConfig V → ℝ) ω * k ω ∂μ = ∫ ω in D ∩ T, k ω ∂μ := by
    intro T k
    rw [← setIntegral_mul_indicator_one μ D T k]
    refine setIntegral_congr_fun (hmeas D) fun ω _ => ?_
    ring
  have hBHK := BHK2006_twoClusterConditionalAssociation.negCorrelation
    BHK2006_twoClusterConditionalAssociation_holds V w v a
    ((connFamily v o).indicator 1) (fun C => F {x | x = a ∨ ∃ e ∈ C, x ∈ e})
    (monotone_indicator_one_of_isUpperSet (isUpperSet_connFamily v o)) (monotone_clusterFun a F hF) hva
  simp only [clusterFun_openEdgeCluster, hind] at hBHK
  rw [setIntegral_indicator_one_eq, hprod Ov] at hBHK
  change μ.real D * ∫ ω in D ∩ Ov, f ω ∂μ ≤ μ.real (D ∩ Ov) * ∫ ω in D, f ω ∂μ at hBHK
  -- (3) `U = Oa ⊔ (D ∩ Ov)`
  have hUdiff : U \ Oa = D ∩ Ov := by
    ext ω
    simp only [hU, hOa, hOv, hD, mem_sdiff, mem_union, mem_inter_iff, openConn, mem_setOf_eq]
    constructor
    · rintro ⟨h1 | h2, hn1⟩
      · exact absurd h1 hn1
      · exact ⟨fun h => hn1 (h2.trans h), h2⟩
    · rintro ⟨hn', h2⟩
      exact ⟨Or.inr h2, fun h1 => hn' (h2.symm.trans h1)⟩
  have hUint : ∫ ω in U, f ω ∂μ = ∫ ω in Oa, f ω ∂μ + ∫ ω in D ∩ Ov, f ω ∂μ := by
    rw [← integral_inter_add_sdiff (hmeas Oa) (hint f U), inter_eq_right.2 subset_union_left, hUdiff]
  have hUμ : μ.real U = μ.real Oa + μ.real (D ∩ Ov) := by
    rw [← measureReal_inter_add_sdiff (s := U) (h := measure_ne_top _ _) (hmeas Oa), inter_eq_right.2 subset_union_left, hUdiff]
  -- (4) `D = Qᶜ`
  have hDQ : D = Qᶜ := by
    ext ω
    simp [hD, hQ, openConn]
  have hDint : ∫ ω in D, f ω ∂μ = m - ∫ ω in Q, f ω ∂μ := by
    have := integral_add_compl (hmeas Q) (Integrable.of_finite (f := f) (μ := μ))
    rw [← hDQ] at this
    linarith
  have hDμ : μ.real D = 1 - μ.real Q := by
    have h1 : μ.real (univ : Set (BondConfig V)) = μ.real (univ ∩ Q) + μ.real (univ \ Q) :=
      (measureReal_inter_add_sdiff (s := univ) (h := measure_ne_top _ _) (hmeas Q)).symm
    rw [probReal_univ, univ_inter, ← compl_eq_univ_sdiff, ← hDQ] at h1
    linarith
  -- assemble
  have hm0 : 0 ≤ m := integral_nonneg fun ω => hF0 _
  have hA : ∫ ω in Oa, f ω ∂μ - μ.real Oa * m ≥ μ.real (D ∩ Ov) * m - ∫ ω in D ∩ Ov, f ω ∂μ := by
    rw [hUint, hUμ] at hHarris
    linarith
  have hB : μ.real D * (μ.real (D ∩ Ov) * m - ∫ ω in D ∩ Ov, f ω ∂μ) ≥
      μ.real D * (μ.real (D ∩ Ov) * m) - μ.real (D ∩ Ov) * ∫ ω in D, f ω ∂μ := by
    rw [mul_sub]
    linarith [hBHK]
  have hC := mul_le_mul_of_nonneg_left hA (hn D)
  rw [hDint, hDμ] at hB
  rw [hDμ] at hC ⊢
  nlinarith [hB, hC, hn (D ∩ Ov), hn Q]

/-- **(GEN) for three relays from the surplus-transfer inequality (S5) with `|T| = 2`.** For `F` monotone nonnegative on vertex
sets, an observer `o` and relays `a₁, a₂, a₃` with `m₁ ≤ m₂ ≤ m₃` (`m_i = ∫ F(C(a_i))`), ASSUME the surplus transfer from `a₃` to `o`
over `T = {a₁, a₂}`:  `μ(a₃ ↮ T, o ↔ a₃) · Sur_{a₃}(T) ≤ μ(a₃ ↮ T) · Sur_o(T)` where
`Sur_x(T) = ∫_{x ↔ T} F(C(x)) − (μ(x ↔ a₁)·m₁ + μ(x ↔ a₂, x ↮ a₁)·m₂)`.  THEN the master form (GEN) holds for `(o; a₁, a₂, a₃)`:
`μ(o ↔ a₁)·m₁ + μ(o ↔ a₂, o ↮ a₁)·m₂ + μ(o ↔ a₃, o ↮ a₁, o ↮ a₂)·m₃ ≤ ∫_{o ↔ A} F(C(o))`.
Proof: the defect is `Sur_o(T) − deficit₃`, and the one-cluster BHK inequality for `C(a₃)` given `a₃ ↮ T` bounds
`μ(a₃ ↮ T)·deficit₃` by `μ(o ↔ a₃, a₃ ↮ T)·Cov(F(C(a₃)), 1_{a₃ ↔ T}) ≤ μ(o ↔ a₃, a₃ ↮ T)·Sur_{a₃}(T)`; `Sur_o(T) ≥ 0` is `gen_pair`.
[cite: VandenbergHaggstromKahn2005, Thm. 1.3 (p. 6)] [cite: KozmaNitzan2024, Conj. 4 (p. 32)] -/
theorem gen_triple_of_surplusTransfer_pair (w : Sym2 V → unitInterval) (o a₁ a₂ a₃ : V) (h31 : a₃ ≠ a₁) (h32 : a₃ ≠ a₂)
    (F : Set V → ℝ) (hF : ∀ S T : Set V, S ⊆ T → F S ≤ F T) (hF0 : ∀ S, 0 ≤ F S)
    (hm12 : ∫ ω, F (openCluster ω a₁) ∂(prodBernoulli w) ≤ ∫ ω, F (openCluster ω a₂) ∂(prodBernoulli w))
    (hm23 : ∫ ω, F (openCluster ω a₂) ∂(prodBernoulli w) ≤ ∫ ω, F (openCluster ω a₃) ∂(prodBernoulli w))
    (hST : (prodBernoulli w).real ({ω : BondConfig V | ¬ (openGraph ω).Reachable a₃ a₁} ∩
              {ω : BondConfig V | ¬ (openGraph ω).Reachable a₃ a₂} ∩ openConn o a₃) *
        (∫ ω in (openConn a₃ a₁ ∪ openConn a₃ a₂), F (openCluster ω a₃) ∂(prodBernoulli w) -
          ((prodBernoulli w).real (openConn a₃ a₁) * ∫ ω, F (openCluster ω a₁) ∂(prodBernoulli w) +
            (prodBernoulli w).real (openConn a₃ a₂ ∩ (openConn a₃ a₁)ᶜ : Set (BondConfig V)) *
              ∫ ω, F (openCluster ω a₂) ∂(prodBernoulli w))) ≤
      (prodBernoulli w).real ({ω : BondConfig V | ¬ (openGraph ω).Reachable a₃ a₁} ∩
          {ω : BondConfig V | ¬ (openGraph ω).Reachable a₃ a₂}) *
        (∫ ω in (openConn o a₁ ∪ openConn o a₂), F (openCluster ω o) ∂(prodBernoulli w) -
          ((prodBernoulli w).real (openConn o a₁) * ∫ ω, F (openCluster ω a₁) ∂(prodBernoulli w) +
            (prodBernoulli w).real (openConn o a₂ ∩ (openConn o a₁)ᶜ : Set (BondConfig V)) *
              ∫ ω, F (openCluster ω a₂) ∂(prodBernoulli w)))) :
    (prodBernoulli w).real (openConn o a₁) * ∫ ω, F (openCluster ω a₁) ∂(prodBernoulli w) +
        (prodBernoulli w).real (openConn o a₂ ∩ (openConn o a₁)ᶜ : Set (BondConfig V)) *
          ∫ ω, F (openCluster ω a₂) ∂(prodBernoulli w) +
        (prodBernoulli w).real (openConn o a₃ ∩ (openConn o a₁ ∪ openConn o a₂)ᶜ : Set (BondConfig V)) *
          ∫ ω, F (openCluster ω a₃) ∂(prodBernoulli w) ≤
      ∫ ω in (openConn o a₁ ∪ openConn o a₂ ∪ openConn o a₃), F (openCluster ω o) ∂(prodBernoulli w) := by
  classical
  set μ := prodBernoulli w with hμ
  set f₀ : BondConfig V → ℝ := fun ω => F (openCluster ω o) with hf₀
  set f₃ : BondConfig V → ℝ := fun ω => F (openCluster ω a₃) with hf₃
  set m₁ : ℝ := ∫ ω, F (openCluster ω a₁) ∂μ with hm₁
  set m₂ : ℝ := ∫ ω, F (openCluster ω a₂) ∂μ with hm₂
  set m₃ : ℝ := ∫ ω, f₃ ω ∂μ with hm₃
  have hmeas : ∀ T : Set (BondConfig V), MeasurableSet T := fun _ => MeasurableSet.of_discrete
  have hint : ∀ (k : BondConfig V → ℝ) (T : Set (BondConfig V)), IntegrableOn k T μ :=
    fun k T => (Integrable.of_finite).integrableOn
  have hn := fun (S : Set (BondConfig V)) => (measureReal_nonneg : 0 ≤ μ.real S)
  set O₁ : Set (BondConfig V) := openConn o a₁ with hO₁
  set O₂ : Set (BondConfig V) := openConn o a₂ with hO₂
  set O₃ : Set (BondConfig V) := openConn o a₃ with hO₃
  set U₂ : Set (BondConfig V) := O₁ ∪ O₂ with hU₂
  set P₃ : Set (BondConfig V) := O₃ ∩ U₂ᶜ with hP₃
  set D₃ : Set (BondConfig V) := {ω : BondConfig V | ¬ (openGraph ω).Reachable a₃ a₁} ∩
    {ω : BondConfig V | ¬ (openGraph ω).Reachable a₃ a₂} with hD₃
  set W₃ : Set (BondConfig V) := openConn a₃ a₁ ∪ openConn a₃ a₂ with hW₃
  -- surplus of `o` is nonnegative (this library's (GEN) for two relays)
  have hSur0 : μ.real O₁ * m₁ + μ.real (O₂ ∩ O₁ᶜ) * m₂ ≤ ∫ ω in U₂, f₀ ω ∂μ := gen_pair w o a₁ a₂ F hF hF0 hm12
  -- (a) `∫_{U₂ ∪ O₃} f₀ = ∫_{U₂} f₀ + ∫_{P₃} f₃`
  have h03 : ∀ ω ∈ O₃, f₀ ω = f₃ ω := fun ω hω => by
    simp only [hf₀, hf₃]; rw [openCluster_eq_of_reachable (hω : (openGraph ω).Reachable o a₃)]
  have hsplit : ∫ ω in U₂ ∪ O₃, f₀ ω ∂μ = ∫ ω in U₂, f₀ ω ∂μ + ∫ ω in P₃, f₃ ω ∂μ := by
    rw [← integral_inter_add_sdiff (hmeas U₂) (hint f₀ (U₂ ∪ O₃)), inter_eq_right.2 subset_union_left]
    have hd : (U₂ ∪ O₃) \ U₂ = P₃ := by
      ext ω
      simp only [hP₃, mem_sdiff, mem_union, mem_inter_iff, mem_compl_iff]
      tauto
    rw [hd, setIntegral_congr_fun (hmeas P₃) fun ω hω => h03 ω hω.1]
  -- (b) `P₃ = D₃ ∩ O₃`
  have hPD : P₃ = D₃ ∩ O₃ := by
    ext ω
    simp only [hP₃, hD₃, hU₂, hO₁, hO₂, hO₃, mem_inter_iff, mem_compl_iff, mem_union, openConn, mem_setOf_eq]
    constructor
    · rintro ⟨h3, hno⟩
      refine ⟨⟨fun h => hno (Or.inl (h3.trans h)), fun h => hno (Or.inr (h3.trans h))⟩, h3⟩
    · rintro ⟨⟨hn1, hn2⟩, h3⟩
      exact ⟨h3, fun h => h.elim (fun h1 => hn1 (h3.symm.trans h1)) fun h2 => hn2 (h3.symm.trans h2)⟩
  -- (c) one-cluster BHK for `C(a₃)` given `a₃ ↮ {a₁, a₂}`
  have hind3 : ∀ ω : BondConfig V, (connFamily a₃ o).indicator (1 : Set (Sym2 V) → ℝ) (openEdgeCluster ω a₃) =
      O₃.indicator (1 : BondConfig V → ℝ) ω := fun ω => by
    rw [congrFun (indicator_comp_openEdgeCluster (connFamily a₃ o) a₃) ω, ← openConn_eq_setOf_connFamily,
      openConn_symm a₃ o]
  have hprod : ∀ (T : Set (BondConfig V)) (k : BondConfig V → ℝ),
      ∫ ω in D₃, T.indicator (1 : BondConfig V → ℝ) ω * k ω ∂μ = ∫ ω in D₃ ∩ T, k ω ∂μ := by
    intro T k
    rw [← setIntegral_mul_indicator_one μ D₃ T k]
    refine setIntegral_congr_fun (hmeas D₃) fun ω _ => ?_
    ring
  have hDset : {ω : BondConfig V | ∀ x ∈ ({a₁, a₂} : Set V), ¬ (openGraph ω).Reachable a₃ x} = D₃ := by
    ext ω
    simp [hD₃]
  have hBHK := BHK2006_clusterConditionalPositiveAssociation_holds V w a₃ ({a₁, a₂} : Set V)
    ((connFamily a₃ o).indicator 1) (fun C => F {a | a = a₃ ∨ ∃ e ∈ C, a ∈ e})
    (monotone_indicator_one_of_isUpperSet (isUpperSet_connFamily a₃ o)) (monotone_clusterFun a₃ F hF)
    (by simp [h31, h32])
  simp only [hDset, clusterFun_openEdgeCluster, hind3] at hBHK
  rw [setIntegral_indicator_one_eq, hprod O₃] at hBHK
  change μ.real (D₃ ∩ O₃) * ∫ ω in D₃, f₃ ω ∂μ ≤ μ.real D₃ * ∫ ω in D₃ ∩ O₃, f₃ ω ∂μ at hBHK
  -- (d) `D₃ = W₃ᶜ`
  have hDW : D₃ = W₃ᶜ := by
    ext ω
    simp [hD₃, hW₃, openConn]
  have hDint : ∫ ω in D₃, f₃ ω ∂μ = m₃ - ∫ ω in W₃, f₃ ω ∂μ := by
    have := integral_add_compl (hmeas W₃) (Integrable.of_finite (f := f₃) (μ := μ))
    rw [← hDW] at this
    linarith
  have hDμ : μ.real D₃ = 1 - μ.real W₃ := by
    have h1 : μ.real (univ : Set (BondConfig V)) = μ.real (univ ∩ W₃) + μ.real (univ \ W₃) :=
      (measureReal_inter_add_sdiff (s := univ) (h := measure_ne_top _ _) (hmeas W₃)).symm
    rw [probReal_univ, univ_inter, ← compl_eq_univ_sdiff, ← hDW] at h1
    linarith
  -- (e) `Cov(f₃, 1_{W₃}) ≤ Sur_{a₃}(T)` since `m₃` is maximal
  have hWμ : μ.real W₃ = μ.real (openConn a₃ a₁) + μ.real (openConn a₃ a₂ ∩ (openConn a₃ a₁)ᶜ : Set (BondConfig V)) := by
    rw [← measureReal_inter_add_sdiff (s := W₃) (h := measure_ne_top _ _) (hmeas (openConn a₃ a₁)),
      inter_eq_right.2 subset_union_left, Set.sdiff_eq]
    congr 2
    ext ω
    simp only [hW₃, mem_inter_iff, mem_union, mem_compl_iff]
    tauto
  have hm13 : m₁ ≤ m₃ := hm12.trans hm23
  have hCovSur : ∫ ω in W₃, f₃ ω ∂μ - m₃ * μ.real W₃ ≤
      ∫ ω in W₃, f₃ ω ∂μ - (μ.real (openConn a₃ a₁) * m₁ +
        μ.real (openConn a₃ a₂ ∩ (openConn a₃ a₁)ᶜ : Set (BondConfig V)) * m₂) := by
    rw [hWμ]
    nlinarith [hn (openConn a₃ a₁), hn (openConn a₃ a₂ ∩ (openConn a₃ a₁)ᶜ : Set (BondConfig V)), hm13, hm23]
  -- (f) assemble: `μ(D₃)·deficit₃ ≤ μ(P₃)·Cov ≤ μ(P₃)·Sur_{a₃} ≤ μ(D₃)·Sur_o`
  have hm3n : 0 ≤ m₃ := integral_nonneg fun ω => hF0 _
  have hP3int : 0 ≤ ∫ ω in P₃, f₃ ω ∂μ := setIntegral_nonneg (hmeas P₃) fun ω _ => hF0 _
  rw [hPD] at hsplit hP3int
  change μ.real (D₃ ∩ O₃) * (∫ ω in W₃, f₃ ω ∂μ - (μ.real (openConn a₃ a₁) * m₁ +
      μ.real (openConn a₃ a₂ ∩ (openConn a₃ a₁)ᶜ : Set (BondConfig V)) * m₂)) ≤
    μ.real D₃ * (∫ ω in U₂, f₀ ω ∂μ - (μ.real O₁ * m₁ + μ.real (O₂ ∩ O₁ᶜ) * m₂)) at hST
  have hkey : μ.real D₃ * (m₃ * μ.real (D₃ ∩ O₃) - ∫ ω in D₃ ∩ O₃, f₃ ω ∂μ) ≤
      μ.real D₃ * (∫ ω in U₂, f₀ ω ∂μ - (μ.real O₁ * m₁ + μ.real (O₂ ∩ O₁ᶜ) * m₂)) := by
    have h1 : μ.real D₃ * (m₃ * μ.real (D₃ ∩ O₃) - ∫ ω in D₃ ∩ O₃, f₃ ω ∂μ) ≤
        μ.real (D₃ ∩ O₃) * (∫ ω in W₃, f₃ ω ∂μ - m₃ * μ.real W₃) := by
      rw [hDint, hDμ] at hBHK
      rw [hDμ]
      nlinarith [hBHK]
    have h2 := mul_le_mul_of_nonneg_left hCovSur (hn (D₃ ∩ O₃))
    linarith
  have hgoal : 0 ≤ (∫ ω in U₂, f₀ ω ∂μ - (μ.real O₁ * m₁ + μ.real (O₂ ∩ O₁ᶜ) * m₂)) -
      (m₃ * μ.real (D₃ ∩ O₃) - ∫ ω in D₃ ∩ O₃, f₃ ω ∂μ) := by
    by_cases hD0 : μ.real D₃ = 0
    · have hP0 : μ.real (D₃ ∩ O₃) = 0 := le_antisymm (hD0 ▸ measureReal_mono inter_subset_left (measure_ne_top _ _)) (hn _)
      rw [hP0]
      nlinarith [hSur0, hP3int]
    · have hDpos : 0 < μ.real D₃ := lt_of_le_of_ne (hn _) (Ne.symm hD0)
      by_contra hneg
      have := mul_neg_of_pos_of_neg hDpos (lt_of_not_ge hneg)
      nlinarith [hkey]
  have hPm : μ.real P₃ = μ.real (D₃ ∩ O₃) := by rw [hPD]
  rw [hsplit, hPm]
  linarith

end Percolation.Continuity.AGloc

end
