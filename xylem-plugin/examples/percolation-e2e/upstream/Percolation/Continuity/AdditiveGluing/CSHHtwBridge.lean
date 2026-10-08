import Percolation.Continuity.AdditiveGluing.CSHHpart
import Percolation.Continuity.CovTau.A2H
import Percolation.Continuity.CovTau.Bridge
import Percolation.Util.Linter

/-!
# The conditioned slack hierarchy — (Htw) in world form and LEMMA H UNCONDITIONALLY (the H-part of the unfolding is nonnegative)

The bridge between `CovTau.p1H_univ` (BHK2006 weight-sum framework on `G[U]`, `U = univ`, worlds `rest univ Y ω = V ∖ C_Y(ω)`) and the world vocabulary of the
induction skeleton `CSH.cshMargin_nonneg_of_unfold` / Lemma T `CSH.cshMargin_nonneg_of_within` (worlds = `prodBernoulli` with the weights ZEROED on
the pairs meeting the open vertex cluster of `Y`).

* `BfS_rest_univ`, `qav_rest_univ`, `Eav_univ_eq`, `Mav_univ_eq` — the dictionary for the functionals of `CovTau.p1H_univ` with a marker SET `S`.
* `htw_world` — (Htw) in world form: `μ(v↮S∪Y, o↔v)·∫_{x↮Y} Cov_{w^ω}(g(C_x),1{v↔S}) ≤ μ(v↮S∪Y)·∫_{x↮Y} p_ω·Cov_{w^ω}(g(C_x),1{v↔S})`,
  UNCONDITIONAL (from `CovTau.p1H_univ`).
* `hpart_nonneg` — LEMMA H, UNCONDITIONAL: for non-degenerate weights, `x ∈ S`, `v ∉ S`, `v ∉ Y`, `g` monotone `≥ 0`,
  `0 ≤ ∫_{x↮Y} [Cov_{w^ω}(g(C_x),1{o↔S}) − μ(o↔v | v↮S∪Y)·Cov_{w^ω}(g(C_x),1{v↔S})] dμ_w(ω)` (`CSH.hpart_nonneg_of_htw` + `htw_world`).
[cite: VandenbergHaggstromKahn2005, Thm. 1.1 (pp. 3–5), Thm. 1.4 (p. 7), §2.1 Lemmas 2.3–2.4 (p. 10)] [cite: Gladkov2024, Thm. 3.2 (p. 4)]
[cite: KozmaNitzan2024, Conj. 4 (p. 32)]
-/

noncomputable section

namespace Percolation.Continuity.CSH

open MeasureTheory Set
open Percolation.Literature.LatticeModels (prodBernoulli)
open Percolation.Literature Percolation.Literature.KNPreFKG
open Percolation.Literature.BHK2006 (weight edgesIn rC rD integral_comp_sdiff_prodBernoulli ind_inter)
open DecisionTree (ind ind_of_mem ind_of_not_mem ind_nonneg)
open CovTau
open scoped Classical

variable {V : Type*} [Fintype V]

/-- In the world `U = V ∖ C_Y(ω)`, restricting a configuration to `edgesIn U` deletes exactly the pairs
 meeting the open vertex cluster of the set `Y`. [cite: VandenbergHaggstromKahn2005, §2.1 Lemma 2.3
 (p. 10)]
-/
theorem inter_edgesIn_rest_univ_set (Y : Set V) (ω η : Set (Sym2 V)) :
    η ∩ edgesIn (rest Finset.univ Y ω) = η \ {e | ∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z} := by
  ext e
  simp only [mem_inter_iff, BHK2006.edgesIn, mem_setOf_eq, mem_sdiff, not_exists, not_and]
  constructor
  · rintro ⟨he, h⟩
    refine ⟨he, fun u hu y hy hr => ?_⟩
    have := (mem_rest.1 (h u hu)).2
    exact this (mem_sC_univ.2 ⟨y, hy, hr⟩)
  · rintro ⟨he, h⟩
    refine ⟨he, fun u hu => mem_rest.2 ⟨Finset.mem_univ u, fun hC => ?_⟩⟩
    obtain ⟨z, hz, hr⟩ := mem_sC_univ.1 hC
    exact h u hu z hz hr

/-- **Fresh expectations in the world `G ∖ C_Y(ω)` are zeroed-weight integrals**: `Σ_η weight(η) G(η ∩
 edgesIn(V ∖ C_Y ω)) = ∫ G dμ_{p^ω}`, `p^ω` = `p` zeroed on the pairs meeting `C_Y(ω)`. [cite:
 VandenbergHaggstromKahn2005, §2.1 Lemmas 2.3–2.4 (p. 10)]
-/
theorem sum_weight_rest_univ_set (p : Sym2 V → unitInterval) (Y : Set V) (ω : Set (Sym2 V)) (G : Set (Sym2 V) → ℝ) :
    ∑ η, weight (fun e => (p e : ℝ)) η * G (η ∩ edgesIn (rest Finset.univ Y ω)) =
      ∫ η, G η ∂(prodBernoulli fun e => if (∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z) then (0 : unitInterval) else p e) := by
  simp only [inter_edgesIn_rest_univ_set]
  rw [sum_weight_mul_eq_integral, integral_comp_sdiff_prodBernoulli p {e | ∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z} G]
  congr 2
  funext e
  by_cases h : ∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z
  · rw [if_pos h, if_pos (show e ∈ {e : Sym2 V | ∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z} from h)]
  · rw [if_neg h, if_neg (show e ∉ {e : Sym2 V | ∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z} from h)]

omit [Fintype V] in
/-- `{v ↔ S}` as a union of connection events: `{η | ∃ s ∈ S, s ↔ v} = ⋃_{t ∈ S} {v ↔ t}`. [folklore] -/
theorem setOf_exists_reachable_eq_biUnion (S : Finset V) (v : V) :
    {η : Set (Sym2 V) | ∃ s ∈ (↑S : Set V), (openGraph η).Reachable s v} = ⋃ t ∈ S, (openConn v t : Set (BondConfig V)) := by
  ext η
  simp only [mem_setOf_eq, Finset.mem_coe, mem_iUnion, exists_prop]
  constructor
  · rintro ⟨s, hs, h⟩; exact ⟨s, hs, h.symm⟩
  · rintro ⟨s, hs, h⟩; exact ⟨s, hs, SimpleGraph.Reachable.symm h⟩

omit [Fintype V] in
/-- The restricted-reachability indicator read on the restricted configuration. [folklore] -/
theorem ind_reach_inter (S : Finset V) (v : V) (E η : Set (Sym2 V)) :
    ind {ζ : Set (Sym2 V) | ∃ s ∈ (↑S : Set V), (openGraph (ζ ∩ E)).Reachable s v} η =
      ind (⋃ t ∈ S, (openConn v t : Set (BondConfig V))) (η ∩ E) := by
  rw [← setOf_exists_reachable_eq_biUnion]
  rfl

/-- **`H^S` in the world `G ∖ C_Y(ω)` is the zeroed-weight covariance bracket**:
`BfS(V ∖ C_Y ω) = ∫_{v↔S} g(C_x) dμ_{p^ω} − μ_{p^ω}(v↔S)·∫ g(C_x) dμ_{p^ω}`. [cite: VandenbergHaggstromKahn2005, §2.1 Lemmas 2.3–2.4 (p. 10)] -/
theorem BfS_rest_univ (p : Sym2 V → unitInterval) (x v : V) (S : Finset V) (Y : Set V) (g : Set (Sym2 V) → ℝ) (ω : Set (Sym2 V)) :
    BfS (fun e => (p e : ℝ)) (rest Finset.univ Y ω) x (↑S : Set V) v g =
      (∫ η in (⋃ t ∈ S, openConn v t), g (openEdgeCluster η x)
          ∂(prodBernoulli fun e => if (∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z) then (0 : unitInterval) else p e)) -
        (prodBernoulli fun e => if (∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z) then (0 : unitInterval) else p e).real
            (⋃ t ∈ S, openConn v t) *
          (∫ η, g (openEdgeCluster η x)
            ∂(prodBernoulli fun e => if (∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z) then (0 : unitInterval) else p e)) := by
  set pw : Sym2 V → unitInterval := fun e => if (∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z) then (0 : unitInterval) else p e
    with hpw
  have h1 : tfE (fun e => (p e : ℝ)) (rest Finset.univ Y ω) x g = ∫ η, g (openEdgeCluster η x) ∂(prodBernoulli pw) :=
    sum_weight_rest_univ_set p Y ω (fun ζ => g (openEdgeCluster ζ x))
  have h2 : cfS (fun e => (p e : ℝ)) (rest Finset.univ Y ω) (↑S : Set V) v =
      ∫ η, ind (⋃ t ∈ S, (openConn v t : Set (BondConfig V))) η ∂(prodBernoulli pw) := by
    have h := sum_weight_rest_univ_set p Y ω (fun ζ => ind (⋃ t ∈ S, (openConn v t : Set (BondConfig V))) ζ)
    refine Eq.trans ?_ h
    rw [cfS]
    exact Finset.sum_congr rfl fun η _ => by rw [ind_reach_inter]
  have h3 : (∑ η, weight (fun e => (p e : ℝ)) η * (g (rC (rest Finset.univ Y ω) x η) *
      ind {η : Set (Sym2 V) | ∃ s ∈ (↑S : Set V), (openGraph (η ∩ edgesIn (rest Finset.univ Y ω))).Reachable s v} η)) =
      ∫ η, g (openEdgeCluster η x) * ind (⋃ t ∈ S, (openConn v t : Set (BondConfig V))) η ∂(prodBernoulli pw) := by
    have h := sum_weight_rest_univ_set p Y ω
      (fun ζ => g (openEdgeCluster ζ x) * ind (⋃ t ∈ S, (openConn v t : Set (BondConfig V))) ζ)
    refine Eq.trans ?_ h
    refine Finset.sum_congr rfl fun η _ => ?_
    rw [ind_reach_inter]
    rfl
  rw [BfS, h1, h2, h3, ind_eq_indicator_one, integral_indicator_one MeasurableSet.of_discrete]
  have h4 : ∫ η, g (openEdgeCluster η x) * ind (⋃ t ∈ S, (openConn v t : Set (BondConfig V))) η ∂(prodBernoulli pw) =
      ∫ η in (⋃ t ∈ S, openConn v t), g (openEdgeCluster η x) ∂(prodBernoulli pw) := by
    rw [← integral_indicator MeasurableSet.of_discrete]
    congr 1
    funext η
    by_cases h : η ∈ (⋃ t ∈ S, (openConn v t : Set (BondConfig V)))
    · rw [ind_of_mem h, mul_one, indicator_of_mem h]
    · rw [ind_of_not_mem h, mul_zero, indicator_of_notMem h]
  rw [h4]
  ring

/-- **`q_S` in the world `G ∖ C_Y(ω)`** = `μ_{p^ω}(v ↮ S, o ↔ v) / μ_{p^ω}(v ↮ S)`. [cite: VandenbergHaggstromKahn2005, §2.1 Lemmas 2.3–2.4 (p. 10)] -/
theorem qav_rest_univ (p : Sym2 V → unitInterval) (o v : V) (S : Finset V) (Y : Set V) (ω : Set (Sym2 V)) :
    qav (fun e => (p e : ℝ)) (rest Finset.univ Y ω) (↑S : Set V) o v =
      (prodBernoulli fun e => if (∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z) then (0 : unitInterval) else p e).real
          ({η : BondConfig V | ∀ t ∈ S, ¬ (openGraph η).Reachable v t} ∩ openConn o v) /
        (prodBernoulli fun e => if (∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z) then (0 : unitInterval) else p e).real
          {η : BondConfig V | ∀ t ∈ S, ¬ (openGraph η).Reachable v t} := by
  set pw : Sym2 V → unitInterval := fun e => if (∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z) then (0 : unitInterval) else p e
    with hpw
  have hset : {ζ : Set (Sym2 V) | ∀ z ∈ (↑S : Set V) ∪ (∅ : Set V), ¬ (openGraph ζ).Reachable v z} =
      {η : BondConfig V | ∀ t ∈ S, ¬ (openGraph η).Reachable v t} := by
    ext ζ; simp only [union_empty, mem_setOf_eq, Finset.mem_coe]
  have h1 : Eav (fun e => (p e : ℝ)) (rest Finset.univ Y ω) (↑S : Set V) o v ∅ =
      ∫ η, ind ({η : BondConfig V | ∀ t ∈ S, ¬ (openGraph η).Reachable v t} ∩ openConn o v) η ∂(prodBernoulli pw) := by
    have h := sum_weight_rest_univ_set p Y ω (fun ζ => oInd o v (openEdgeCluster ζ v) *
      ind {ζ : Set (Sym2 V) | ∀ z ∈ (↑S : Set V) ∪ (∅ : Set V), ¬ (openGraph ζ).Reachable v z} ζ)
    refine (Eq.trans (by rfl) h).trans ?_
    congr 1
    funext η
    rw [oInd_openEdgeCluster, ← ind_inter, inter_comm, hset, openConn_symm v o]
  have h2 : Mav (fun e => (p e : ℝ)) (rest Finset.univ Y ω) (↑S : Set V) v ∅ =
      ∫ η, ind {η : BondConfig V | ∀ t ∈ S, ¬ (openGraph η).Reachable v t} η ∂(prodBernoulli pw) := by
    have h := sum_weight_rest_univ_set p Y ω (fun ζ =>
      ind {ζ : Set (Sym2 V) | ∀ z ∈ (↑S : Set V) ∪ (∅ : Set V), ¬ (openGraph ζ).Reachable v z} ζ)
    refine (Eq.trans (by rfl) h).trans ?_
    rw [hset]
  rw [qav, h1, h2, ind_eq_indicator_one, ind_eq_indicator_one, integral_indicator_one MeasurableSet.of_discrete,
    integral_indicator_one MeasurableSet.of_discrete]

/-- `M_S(Y) = μ(v ↮ S ∪ Y)` in `G = G[univ]`. [cite: VandenbergHaggstromKahn2005, §1 p. 3] -/
theorem Mav_univ_eq (p : Sym2 V → unitInterval) (v : V) (S : Finset V) (Y : Set V) :
    Mav (fun e => (p e : ℝ)) Finset.univ (↑S : Set V) v Y =
      (prodBernoulli p).real {ω : BondConfig V | ∀ a ∈ (↑S ∪ Y : Set V), ¬ (openGraph ω).Reachable v a} := by
  rw [Mav, rD_univ, sum_weight_ind]

/-- `E_S(Y) = μ(v ↮ S ∪ Y, o ↔ v)` in `G = G[univ]`. [cite: VandenbergHaggstromKahn2005, §1 p. 3] -/
theorem Eav_univ_eq (p : Sym2 V → unitInterval) (o v : V) (S : Finset V) (Y : Set V) :
    Eav (fun e => (p e : ℝ)) Finset.univ (↑S : Set V) o v Y =
      (prodBernoulli p).real ({ω : BondConfig V | ∀ a ∈ (↑S ∪ Y : Set V), ¬ (openGraph ω).Reachable v a} ∩ openConn o v) := by
  rw [Eav, ← sum_weight_ind]
  refine Finset.sum_congr rfl fun ω _ => ?_
  congr 1
  rw [rC_univ, rD_univ, oInd_openEdgeCluster, ← ind_inter, inter_comm, openConn_symm v o]

/-- **(Htw) in world form, UNCONDITIONAL** (from `CovTau.p1H_univ`): for `x ∈ S`, `v ∉ S`, `g` monotone `≥ 0`, every `Y`,
`μ(v↮S∪Y, o↔v)·∫_{x↮Y} Cov_{w^ω}(g(C_x),1{v↔S}) dμ ≤ μ(v↮S∪Y)·∫_{x↮Y} p_ω·Cov_{w^ω}(g(C_x),1{v↔S}) dμ`, `p_ω = μ_{w^ω}(o↔v | v↮S)`.
[cite: VandenbergHaggstromKahn2005, Thm. 1.1 (pp. 3–5), Thm. 1.4 (p. 7)] [cite: Gladkov2024, Thm. 3.2 (p. 4)] -/
theorem htw_world (w : Sym2 V → unitInterval) (x : V) (Y : Set V) (S : Finset V) (hxS : x ∈ S) (o v : V) (hvS : v ∉ S)
    (g : Set (Sym2 V) → ℝ) (hg : Monotone g) (hg0 : ∀ C, 0 ≤ g C) :
    (prodBernoulli w).real ({ω : BondConfig V | ∀ a ∈ (↑S ∪ Y : Set V), ¬ (openGraph ω).Reachable v a} ∩ openConn o v) *
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
          ∂(prodBernoulli w)) := by
  set w' : Sym2 V → ℝ := fun e => (w e : ℝ) with hw'
  have hw0 : ∀ e, 0 ≤ w' e := fun e => (w e).2.1
  have hw1 : ∀ e, w' e ≤ 1 := fun e => (w e).2.2
  have hm : ∑ ω, weight w' ω = 1 := sum_weight_coe_eq_one w
  have key := p1H_univ w' hw0 hw1 hm (S := (↑S : Set V)) (Finset.mem_coe.2 hxS) (fun h => hvS (Finset.mem_coe.1 h)) o hg hg0 Y
  -- translate the four functionals
  have hE := Eav_univ_eq w o v S Y
  have hM := Mav_univ_eq w v S Y
  have hY : Yw w' Finset.univ x (fun U' => BfS w' U' x (↑S : Set V) v g) Y =
      ∫ ω in {ω : BondConfig V | ∀ y ∈ Y, ¬ (openGraph ω).Reachable x y},
          ((∫ η in (⋃ t ∈ S, openConn v t), g (openEdgeCluster η x)
              ∂(prodBernoulli fun e => if (∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z) then (0 : unitInterval) else w e)) -
            (prodBernoulli fun e => if (∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z) then (0 : unitInterval) else w e).real
                (⋃ t ∈ S, openConn v t) *
              (∫ η, g (openEdgeCluster η x)
                ∂(prodBernoulli fun e => if (∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z) then (0 : unitInterval) else w e)))
          ∂(prodBernoulli w) := by
    rw [Yw]
    simp only [hw', BfS_rest_univ, rD_univ]
    exact sum_weight_mul_ind w _ _
  have hX : Xw w' Finset.univ x (↑S : Set V) o v (fun U' => BfS w' U' x (↑S : Set V) v g) Y =
      ∫ ω in {ω : BondConfig V | ∀ y ∈ Y, ¬ (openGraph ω).Reachable x y},
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
          ∂(prodBernoulli w) := by
    rw [Xw]
    simp only [hw', BfS_rest_univ, qav_rest_univ, rD_univ]
    exact sum_weight_mul_ind w _ _
  rw [hE, hY, hM, hX] at key
  exact key

/-- **LEMMA H, UNCONDITIONAL**: for non-degenerate weights, a marker set `S ∋ x` (owner and decoys),
observers `o`, `v ∉ S`, `v ∉ Y`, and a monotone edge-cluster functional `g ≥ 0`, the H-part of the world-wise unfolding is nonnegative:
`0 ≤ ∫_{x↮Y} [Cov_{w^ω}(g(C_x),1{o↔S}) − μ(o↔v | v↮S∪Y)·Cov_{w^ω}(g(C_x),1{v↔S})] dμ_w(ω)`  (`CSH.hpart_nonneg_of_htw` fed with `htw_world`).
[cite: VandenbergHaggstromKahn2005, Thm. 1.1 (pp. 3–5), Thm. 1.4 (p. 7)] [cite: Gladkov2024, Thm. 3.2 (p. 4)] -/
theorem hpart_nonneg (w : Sym2 V → unitInterval) (hw : ∀ e, 0 < w e ∧ w e < 1) (x : V) (Y : Set V) (S : Finset V)
    (hxS : x ∈ S) (o v : V) (hvS : v ∉ S) (hvY : v ∉ Y) (g : Set (Sym2 V) → ℝ) (hg : Monotone g) (hg0 : ∀ C, 0 ≤ g C) :
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
      ∂(prodBernoulli w) :=
  hpart_nonneg_of_htw w hw x Y S hxS o v hvS hvY g hg hg0 (htw_world w x Y S hxS o v hvS g hg hg0)

end Percolation.Continuity.CSH

end
