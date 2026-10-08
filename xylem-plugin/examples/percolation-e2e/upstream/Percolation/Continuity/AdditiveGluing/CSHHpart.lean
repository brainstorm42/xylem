import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Order.CompletePartialOrder
import Percolation.Continuity.CSH.Defs
import Percolation.Continuity.CovTau.StarHPrelim
import Percolation.Literature.KozmaNitzanClusterPropertyReal
import Percolation.Literature.KozmaNitzanPreFKG
import Percolation.Literature.LatticeModels.ProdBernoulliWeightContinuity
import Percolation.Util.Linter

/-!
# The conditioned slack hierarchy — LEMMA H (the H-part of the world-wise unfolding is nonnegative, given the two-source diagonal (Htw))

The set four-point transfer (K6) for edge-cluster functionals, and LEMMA H: the H-part of the world-wise unfolding of the conditioned
slack hierarchy is nonnegative, given the two-source diagonal inequality (Htw).

* `setIntegral_edgeFun_ge` — Harris for a monotone nonnegative functional of the open EDGE cluster and an increasing event.
* `prodBernoulli_real_pos_of_empty_mem` — an event containing the empty configuration has positive probability as soon as every weight is `< 1`
  (the WORLD weights `w^ω` — `w` zeroed on the pairs meeting the cluster of `Y` — are not non-degenerate, but stay `< 1`).
* `hpart_nonneg_of_htw` — LEMMA H: for non-degenerate `w`, owner `x ∈ S`, `v ∉ S`, worlds `w^ω` over `ω ∈ {x ↮ Y}`:
  `0 ≤ ∫_{x↮Y} [Cov_{w^ω}(g(C_x), 1{o↔S}) − p·Cov_{w^ω}(g(C_x), 1{v↔S})] dμ_w(ω)`, `p = μ(o↔v | v↮S∪Y)` (`CSH.obsConst`), GIVEN the
  two-source diagonal (Htw) `μ(v↮S∪Y, o↔v)·∫_{x↮Y} Cov_{w^ω}(g,1{v↔S}) ≤ μ(v↮S∪Y)·∫_{x↮Y} p_{ω}·Cov_{w^ω}(g,1{v↔S})`,
  `p_ω = μ_{w^ω}(o↔v | v↮S)` (`CovTau.p1H`): (K6) world by world gives `Cov_ω(g,1{o↔S}) ≥ p_ω Cov_ω(g,1{v↔S})`, and (Htw)
  trades `p_ω` for the global `p`.  This is the `Hpart ≥ 0` input of `CSH.cshMargin_nonneg_of_unfold` (hypothesis `hU`), in the same
  world vocabulary (`prodBernoulli fun e => if (∃ z ∈ e, ∃ y ∈ Y, Reachable y z) then 0 else w e`).
[cite: VandenbergHaggstromKahn2005, Thm. 1.4 (p. 7), Remark 1 after Thm. 1.2 (p. 5), §2 p. 9] [cite: KozmaNitzan2024, Conj. 4 (p. 32)]
-/

noncomputable section

namespace Percolation.Continuity.CSH

open MeasureTheory Set
open Percolation.Literature.LatticeModels (prodBernoulli prodBernoulli_real_pos_of_nonempty prodBernoulli_real_setOf_forall_iff)
open Percolation.Literature Percolation.Literature.KNPreFKG
open Percolation.Literature.BHK2006 (weight harris integral_prodBernoulli_eq_sum weight_nonneg openEdgeCluster_mono)
open DecisionTree (ind ind_of_mem ind_of_not_mem ind_nonneg)
open scoped Classical

variable {V : Type*} [Fintype V]

/-- **Harris, integral form, edge-cluster functional**: for `g` monotone nonnegative on edge sets and an increasing event `U`,
`μ(U)·∫ g(C_a) dμ ≤ ∫_U g(C_a) dμ`. [cite: VandenbergHaggstromKahn2005, §1 p. 6 ("Harris' inequality")] -/
theorem setIntegral_edgeFun_ge (w : Sym2 V → unitInterval) (a : V) (g : Set (Sym2 V) → ℝ)
    (hg : Monotone g) (hg0 : ∀ C, 0 ≤ g C) (U : Set (BondConfig V)) (hU : IsUpperSet U) :
    (prodBernoulli w).real U * ∫ ω, g (openEdgeCluster ω a) ∂(prodBernoulli w) ≤
      ∫ ω in U, g (openEdgeCluster ω a) ∂(prodBernoulli w) := by
  set w' : Sym2 V → ℝ := fun e => ((w e : unitInterval) : ℝ) with hw'
  have hw0 : ∀ e, 0 ≤ w' e := fun e => (w e).2.1
  have hw1 : ∀ e, w' e ≤ 1 := fun e => (w e).2.2
  have hUm : MeasurableSet U := MeasurableSet.of_discrete
  set f : Set (Sym2 V) → ℝ := fun ω => g (openEdgeCluster ω a) with hf
  have hfmono : Monotone f := fun ω ω' h => hg (openEdgeCluster_mono h a)
  have hgmono : Monotone (ind U) := fun ω ω' h => by
    by_cases hω : ω ∈ U
    · rw [ind_of_mem hω, ind_of_mem (hU h hω)]
    · rw [ind_of_not_mem hω]; exact ind_nonneg U ω'
  have key := harris hw0 hw1 (f := f) (g := ind U) (fun ω => hg0 _) (fun ω => ind_nonneg U ω) hfmono hgmono
  have hm : ∑ ω, weight w' ω = 1 := by
    have h1 := integral_prodBernoulli_eq_sum w fun _ => (1 : ℝ)
    simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at h1
    exact h1.symm
  have hI : ∫ ω, g (openEdgeCluster ω a) ∂(prodBernoulli w) = ∑ ω, weight w' ω * f ω :=
    integral_prodBernoulli_eq_sum w f
  have hUr : (prodBernoulli w).real U = ∑ ω, weight w' ω * ind U ω := by
    rw [← integral_indicator_one hUm, integral_prodBernoulli_eq_sum]
    refine Finset.sum_congr rfl fun ω _ => ?_
    by_cases hω : ω ∈ U
    · rw [Set.indicator_of_mem hω, ind_of_mem hω, Pi.one_apply]
    · simp [Set.indicator_of_notMem hω, ind_of_not_mem hω]
  have hIU : ∫ ω in U, g (openEdgeCluster ω a) ∂(prodBernoulli w) = ∑ ω, weight w' ω * (f ω * ind U ω) := by
    rw [← integral_indicator hUm, integral_prodBernoulli_eq_sum]
    refine Finset.sum_congr rfl fun ω _ => ?_
    by_cases hω : ω ∈ U
    · rw [Set.indicator_of_mem hω, ind_of_mem hω, mul_one]
    · simp [Set.indicator_of_notMem hω, ind_of_not_mem hω]
  rw [hI, hUr, hIU]
  rw [hm, one_mul] at key
  linarith [key, mul_comm (∑ ω, weight w' ω * f ω) (∑ ω, weight w' ω * ind U ω)]

/-- **(K6) for edge-cluster functionals — covariance transfer across a set.** For `x ∈ S`, `g` monotone nonnegative on edge sets,
`m = ∫ g(C_x)`, `D = {v ↮ S}`:  `μ(D ∩ {o ↔ v})·(∫_{v ↔ S} g(C_x) − μ(v ↔ S)·m) ≤ μ(D)·(∫_{o ↔ S} g(C_x) − μ(o ↔ S)·m)`
(Harris + vdBHK Thm 1.4 with the vertex set `S`; (K6)). [cite: VandenbergHaggstromKahn2005, Thm. 1.4 (p. 7) with Remark 1 after Thm. 1.2 (p. 5)] -/
theorem covTransfer_relaySet_edge (w : Sym2 V → unitInterval) (S : Finset V) (o v x : V) (hxS : x ∈ S)
    (g : Set (Sym2 V) → ℝ) (hg : Monotone g) (hg0 : ∀ C, 0 ≤ g C) :
    (prodBernoulli w).real ({ω : BondConfig V | ∀ t ∈ S, ¬ (openGraph ω).Reachable v t} ∩ openConn o v) *
        (∫ ω in (⋃ t ∈ S, openConn v t), g (openEdgeCluster ω x) ∂(prodBernoulli w) -
          (prodBernoulli w).real (⋃ t ∈ S, openConn v t) * ∫ ω, g (openEdgeCluster ω x) ∂(prodBernoulli w)) ≤
      (prodBernoulli w).real {ω : BondConfig V | ∀ t ∈ S, ¬ (openGraph ω).Reachable v t} *
        (∫ ω in (⋃ t ∈ S, openConn o t), g (openEdgeCluster ω x) ∂(prodBernoulli w) -
          (prodBernoulli w).real (⋃ t ∈ S, openConn o t) * ∫ ω, g (openEdgeCluster ω x) ∂(prodBernoulli w)) := by
  set μ := prodBernoulli w with hμ
  set f : BondConfig V → ℝ := fun ω => g (openEdgeCluster ω x) with hf
  set m : ℝ := ∫ ω, f ω ∂μ with hm
  have hmeas : ∀ T : Set (BondConfig V), MeasurableSet T := fun _ => MeasurableSet.of_discrete
  have hint : ∀ (k : BondConfig V → ℝ) (T : Set (BondConfig V)), IntegrableOn k T μ :=
    fun k T => (Integrable.of_finite).integrableOn
  have hn := fun (T : Set (BondConfig V)) => (measureReal_nonneg : 0 ≤ μ.real T)
  set D : Set (BondConfig V) := {ω | ∀ t ∈ S, ¬ (openGraph ω).Reachable v t} with hD
  set OT : Set (BondConfig V) := ⋃ t ∈ S, openConn o t with hOT
  set Ov : Set (BondConfig V) := openConn o v with hOv
  set Q : Set (BondConfig V) := ⋃ t ∈ S, openConn v t with hQ
  set U : Set (BondConfig V) := OT ∪ Ov with hU
  -- (1) Harris on `U`
  have hupT : IsUpperSet OT := isUpperSet_iUnion₂ fun t _ => isUpperSet_openConn o t
  have hHarris : μ.real U * m ≤ ∫ ω in U, f ω ∂μ :=
    setIntegral_edgeFun_ge w x g hg hg0 U (hupT.union (isUpperSet_openConn o v))
  -- (2) two-set BHK: `g(C_x)` (increasing in `C_S`) and `{o ↔ v}` (increasing in `C_v`) are negatively correlated given `v ↮ S`
  have hind : ∀ ω : BondConfig V, (connFamily v o).indicator (1 : Set (Sym2 V) → ℝ) (⋃ s ∈ ({v} : Set V), openEdgeCluster ω s) =
      Ov.indicator (1 : BondConfig V → ℝ) ω := fun ω => by
    rw [biUnion_singleton, congrFun (indicator_comp_openEdgeCluster (connFamily v o) v) ω, ← openConn_eq_setOf_connFamily,
      openConn_symm v o]
  have hprod : ∀ (T : Set (BondConfig V)) (k : BondConfig V → ℝ),
      ∫ ω in D, T.indicator (1 : BondConfig V → ℝ) ω * k ω ∂μ = ∫ ω in D ∩ T, k ω ∂μ := by
    intro T k
    rw [← setIntegral_mul_indicator_one μ D T k]
    refine setIntegral_congr_fun (hmeas D) fun ω _ => ?_
    ring
  have hDset : {ω : BondConfig V | ∀ s ∈ ({v} : Set V), ∀ t ∈ (↑S : Set V), ¬ (openGraph ω).Reachable s t} = D := by
    ext ω; simp [hD]
  have hGmono : Monotone (fun W : Set (Sym2 V) => g (openEdgeCluster W x)) := fun W W' h => hg (openEdgeCluster_mono h x)
  have hGval : ∀ ω : BondConfig V, g (openEdgeCluster (⋃ t ∈ (↑S : Set V), openEdgeCluster ω t) x) = f ω := fun ω => by
    simp only [hf]; rw [CovTauStarN.openEdgeCluster_biUnion_eq (Finset.mem_coe.2 hxS)]
  have hBHK := BHK2006_twoSetConditionalAssociation.negCorrelation w ({v} : Set V) (↑S : Set V)
    ((connFamily v o).indicator 1) (fun W => g (openEdgeCluster W x))
    (monotone_indicator_one_of_isUpperSet (isUpperSet_connFamily v o)) hGmono
  simp only [hDset, hind, hGval] at hBHK
  rw [setIntegral_indicator_one_eq, hprod Ov] at hBHK
  change μ.real D * ∫ ω in D ∩ Ov, f ω ∂μ ≤ μ.real (D ∩ Ov) * ∫ ω in D, f ω ∂μ at hBHK
  -- (3) `U = OT ⊔ (D ∩ Ov)`
  have hUdiff : U \ OT = D ∩ Ov := by
    ext ω
    simp only [hU, hOT, hOv, hD, mem_sdiff, mem_union, mem_iUnion, mem_inter_iff, exists_prop, not_exists, not_and, openConn,
      mem_setOf_eq]
    constructor
    · rintro ⟨h | h, hno⟩
      · obtain ⟨t, ht, h'⟩ := h; exact absurd h' (hno t ht)
      · exact ⟨fun t ht hvt => hno t ht (h.trans hvt), h⟩
    · rintro ⟨hd, hov⟩
      exact ⟨Or.inr hov, fun t ht hot => hd t ht (hov.symm.trans hot)⟩
  have hUint : ∫ ω in U, f ω ∂μ = ∫ ω in OT, f ω ∂μ + ∫ ω in D ∩ Ov, f ω ∂μ := by
    rw [← integral_inter_add_sdiff (hmeas OT) (hint f U), inter_eq_right.2 subset_union_left, hUdiff]
  have hUμ : μ.real U = μ.real OT + μ.real (D ∩ Ov) := by
    rw [← measureReal_inter_add_sdiff (s := U) (h := measure_ne_top _ _) (hmeas OT), inter_eq_right.2 subset_union_left, hUdiff]
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
  -- combine
  have hA : ∫ ω in OT, f ω ∂μ - μ.real OT * m ≥ μ.real (D ∩ Ov) * m - ∫ ω in D ∩ Ov, f ω ∂μ := by
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

/-- **An event containing the empty configuration has positive probability when every weight is `< 1`** (e.g. under the world weights,
which vanish on the deleted pairs). [cite: GrimmettPercolation1999, §1.3 p. 10] -/
theorem prodBernoulli_real_pos_of_empty_mem {ι : Type*} [Fintype ι] (p : ι → unitInterval) (hp : ∀ i, p i < 1)
    {C : Set (Set ι)} (hC : (∅ : Set ι) ∈ C) : 0 < (prodBernoulli p).real C := by
  have hcyl := prodBernoulli_real_setOf_forall_iff p Finset.univ (· ∈ (∅ : Set ι))
  have hpos : 0 < (prodBernoulli p).real {ω' : Set ι | ∀ i ∈ (Finset.univ : Finset ι), (i ∈ ω' ↔ i ∈ (∅ : Set ι))} := by
    rw [hcyl]
    refine Finset.prod_pos fun i _ => ?_
    rw [if_neg (Set.notMem_empty i)]
    exact sub_pos.2 (unitInterval.coe_lt_one.2 (hp i))
  have hsub : {ω' : Set ι | ∀ i ∈ (Finset.univ : Finset ι), (i ∈ ω' ↔ i ∈ (∅ : Set ι))} ⊆ C := by
    intro ω' hω'
    have hωω : ω' = ∅ := Set.ext fun i => hω' i (Finset.mem_univ i)
    rw [hωω]; exact hC
  exact hpos.trans_le (measureReal_mono hsub)

/-- **LEMMA H**: the H-part of the world-wise unfolding is nonnegative, GIVEN the two-source diagonal
inequality (Htw).  Setting: non-degenerate weights `w`, owner `x ∈ S` (`S` = owner ∪ decoys), observers `o`, `v ∉ S`, `v ∉ Y`, worlds
`w^ω` = `w` zeroed on the pairs meeting the open vertex cluster of the avoided set `Y`, integrated over `ω ∈ {x ↮ Y}`; `g` monotone `≥ 0` on
edge clusters; `p = μ(o↔v | v ↮ S ∪ Y)`.  CLAIM: `0 ≤ ∫_{x↮Y} [Cov_{w^ω}(g(C_x),1{o↔S}) − p·Cov_{w^ω}(g(C_x),1{v↔S})] dμ_w`, from (K6) in each
world (`covTransfer_relaySet_edge` at the weights `w^ω`) and (Htw) (hypothesis `hHtw`). [cite: VandenbergHaggstromKahn2005, Thm. 1.4 (p. 7)] -/
theorem hpart_nonneg_of_htw (w : Sym2 V → unitInterval) (hw : ∀ e, 0 < w e ∧ w e < 1) (x : V) (Y : Set V) (S : Finset V)
    (hxS : x ∈ S) (o v : V) (hvS : v ∉ S) (hvY : v ∉ Y) (g : Set (Sym2 V) → ℝ) (hg : Monotone g) (hg0 : ∀ C, 0 ≤ g C)
    (hHtw : (prodBernoulli w).real ({ω : BondConfig V | ∀ a ∈ (↑S ∪ Y : Set V), ¬ (openGraph ω).Reachable v a} ∩ openConn o v) *
        (∫ ω in {ω : BondConfig V | ∀ y ∈ Y, ¬ (openGraph ω).Reachable x y},
          ((∫ η in (⋃ t ∈ S, openConn v t), g (openEdgeCluster η x)
              ∂(prodBernoulli fun e => if (∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z) then (0 : unitInterval) else w e)) -
            (prodBernoulli fun e => if (∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z) then (0 : unitInterval) else w e).real
                (⋃ t ∈ S, openConn v t) *
              (∫ η, g (openEdgeCluster η x)
                ∂(prodBernoulli fun e => if (∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z) then (0 : unitInterval) else w e)))
          ∂(prodBernoulli w)) ≤
      (prodBernoulli w).real {ω : BondConfig V | ∀ a ∈ (↑S ∪ Y : Set V), ¬ (openGraph ω).Reachable v a} *
        (∫ ω in {ω : BondConfig V | ∀ y ∈ Y, ¬ (openGraph ω).Reachable x y},
          ((prodBernoulli fun e => if (∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z) then (0 : unitInterval) else w e).real
                ({η : BondConfig V | ∀ t ∈ S, ¬ (openGraph η).Reachable v t} ∩ openConn o v) /
              (prodBernoulli fun e => if (∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z) then (0 : unitInterval) else w e).real
                {η : BondConfig V | ∀ t ∈ S, ¬ (openGraph η).Reachable v t}) *
          ((∫ η in (⋃ t ∈ S, openConn v t), g (openEdgeCluster η x)
              ∂(prodBernoulli fun e => if (∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z) then (0 : unitInterval) else w e)) -
            (prodBernoulli fun e => if (∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z) then (0 : unitInterval) else w e).real
                (⋃ t ∈ S, openConn v t) *
              (∫ η, g (openEdgeCluster η x)
                ∂(prodBernoulli fun e => if (∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z) then (0 : unitInterval) else w e)))
          ∂(prodBernoulli w))) :
    0 ≤ ∫ ω in {ω : BondConfig V | ∀ y ∈ Y, ¬ (openGraph ω).Reachable x y},
      (((∫ η in (⋃ t ∈ S, openConn o t), g (openEdgeCluster η x)
            ∂(prodBernoulli fun e => if (∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z) then (0 : unitInterval) else w e)) -
          (prodBernoulli fun e => if (∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z) then (0 : unitInterval) else w e).real
              (⋃ t ∈ S, openConn o t) *
            (∫ η, g (openEdgeCluster η x)
              ∂(prodBernoulli fun e => if (∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z) then (0 : unitInterval) else w e))) -
        obsConst w o v (↑S ∪ Y) *
          ((∫ η in (⋃ t ∈ S, openConn v t), g (openEdgeCluster η x)
              ∂(prodBernoulli fun e => if (∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z) then (0 : unitInterval) else w e)) -
            (prodBernoulli fun e => if (∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z) then (0 : unitInterval) else w e).real
                (⋃ t ∈ S, openConn v t) *
              (∫ η, g (openEdgeCluster η x)
                ∂(prodBernoulli fun e => if (∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z) then (0 : unitInterval) else w e))))
      ∂(prodBernoulli w) := by
  set μ := prodBernoulli w with hμ
  -- world weights and world quantities
  set wW : BondConfig V → Sym2 V → unitInterval := fun ω e =>
    if (∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z) then (0 : unitInterval) else w e with hwW
  set CovO : BondConfig V → ℝ := fun ω =>
    (∫ η in (⋃ t ∈ S, openConn o t), g (openEdgeCluster η x) ∂(prodBernoulli (wW ω))) -
      (prodBernoulli (wW ω)).real (⋃ t ∈ S, openConn o t) * ∫ η, g (openEdgeCluster η x) ∂(prodBernoulli (wW ω)) with hCovO
  set CovV : BondConfig V → ℝ := fun ω =>
    (∫ η in (⋃ t ∈ S, openConn v t), g (openEdgeCluster η x) ∂(prodBernoulli (wW ω))) -
      (prodBernoulli (wW ω)).real (⋃ t ∈ S, openConn v t) * ∫ η, g (openEdgeCluster η x) ∂(prodBernoulli (wW ω)) with hCovV
  set pW : BondConfig V → ℝ := fun ω =>
    (prodBernoulli (wW ω)).real ({η : BondConfig V | ∀ t ∈ S, ¬ (openGraph η).Reachable v t} ∩ openConn o v) /
      (prodBernoulli (wW ω)).real {η : BondConfig V | ∀ t ∈ S, ¬ (openGraph η).Reachable v t} with hpW
  set M : ℝ := μ.real {ω : BondConfig V | ∀ a ∈ (↑S ∪ Y : Set V), ¬ (openGraph ω).Reachable v a} with hM
  set E : ℝ := μ.real ({ω : BondConfig V | ∀ a ∈ (↑S ∪ Y : Set V), ¬ (openGraph ω).Reachable v a} ∩ openConn o v) with hE
  set Dset : Set (BondConfig V) := {ω : BondConfig V | ∀ y ∈ Y, ¬ (openGraph ω).Reachable x y} with hDset
  change E * ∫ ω in Dset, CovV ω ∂μ ≤ M * ∫ ω in Dset, pW ω * CovV ω ∂μ at hHtw
  change 0 ≤ ∫ ω in Dset, (CovO ω - obsConst w o v (↑S ∪ Y) * CovV ω) ∂μ
  have hmeas : ∀ T : Set (BondConfig V), MeasurableSet T := fun _ => MeasurableSet.of_discrete
  have hint : ∀ (k : BondConfig V → ℝ) (T : Set (BondConfig V)), IntegrableOn k T μ :=
    fun k T => (Integrable.of_finite).integrableOn
  -- positivity of the global conditioning probability and the observers' constant
  have hMpos : 0 < M := by
    refine prodBernoulli_real_pos_of_nonempty hw ⟨∅, fun a ha hreach => ?_⟩
    have hbot : openGraph (∅ : BondConfig V) = ⊥ := by
      unfold openGraph; exact SimpleGraph.fromEdgeSet_empty
    rw [hbot, SimpleGraph.reachable_bot] at hreach
    subst hreach
    rcases ha with ha | ha
    · exact hvS (Finset.mem_coe.1 ha)
    · exact hvY ha
  have hobs : obsConst w o v (↑S ∪ Y) = E / M := by unfold obsConst; rfl
  -- (K6) in each world: `pW ω · CovV ω ≤ CovO ω`
  have hworld : ∀ ω : BondConfig V, pW ω * CovV ω ≤ CovO ω := by
    intro ω
    have hK6 := covTransfer_relaySet_edge (wW ω) S o v x hxS g hg hg0
    -- positivity of the world probability of `{v ↮ S}` (all world weights are `< 1`)
    have hlt : ∀ e, wW ω e < 1 := by
      intro e
      simp only [hwW]
      split_ifs
      · exact zero_lt_one
      · exact (hw e).2
    have hMWpos : 0 < (prodBernoulli (wW ω)).real {η : BondConfig V | ∀ t ∈ S, ¬ (openGraph η).Reachable v t} := by
      refine prodBernoulli_real_pos_of_empty_mem (wW ω) hlt (fun t ht hreach => ?_)
      have hbot : openGraph (∅ : BondConfig V) = ⊥ := by
        unfold openGraph; exact SimpleGraph.fromEdgeSet_empty
      rw [hbot, SimpleGraph.reachable_bot] at hreach
      exact hvS (hreach ▸ ht)
    set MW := (prodBernoulli (wW ω)).real {η : BondConfig V | ∀ t ∈ S, ¬ (openGraph η).Reachable v t} with hMW
    set EW := (prodBernoulli (wW ω)).real ({η : BondConfig V | ∀ t ∈ S, ¬ (openGraph η).Reachable v t} ∩ openConn o v) with hEW
    change EW * CovV ω ≤ MW * CovO ω at hK6
    have hp : pW ω = EW / MW := rfl
    rw [hp, div_mul_eq_mul_div, div_le_iff₀ hMWpos]
    linarith [hK6, mul_comm MW (CovO ω)]
  -- integrate the world inequality over `Dset`
  have hI1 : ∫ ω in Dset, pW ω * CovV ω ∂μ ≤ ∫ ω in Dset, CovO ω ∂μ :=
    setIntegral_mono_on (hint _ _) (hint _ _) (hmeas Dset) fun ω _ => hworld ω
  -- (Htw) divided by `M`
  have hI2 : E / M * ∫ ω in Dset, CovV ω ∂μ ≤ ∫ ω in Dset, pW ω * CovV ω ∂μ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hMpos]
    linarith [hHtw, mul_comm M (∫ ω in Dset, pW ω * CovV ω ∂μ)]
  rw [integral_sub (hint _ _) (hint _ _), integral_const_mul, hobs]
  linarith [hI1, hI2]

end Percolation.Continuity.CSH

end
