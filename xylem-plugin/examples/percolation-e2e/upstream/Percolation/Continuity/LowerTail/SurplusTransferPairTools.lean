import Percolation.Continuity.AdditiveGluing.GenPair
import Percolation.Literature.TwoSetExchange
import Percolation.Util.Linter

/-!
# Tools for the termwise split of the two-relay surplus transfer (S5)₂: the block-Harris piece, the order piece, and the sign of the BHK-1.5 piece

Setting: `μ = prodBernoulli w`, `F` monotone nonnegative on vertex sets, relays `a, b`, an observer `o` and a second observer `v`;
`Q = {a ↮ b}`, `D = {v ↮ a} ∩ {v ↮ b}`, `Xa = {x ↔ a}`, `Xb = {x ↔ b}` for `x ∈ {o, v}`. Proved here:
* `ordTransfer` (T4):         `μ(D ∩ {o↔v})·μ(Vb ∩ Q) ≤ μ(D)·μ(Ob ∩ Q)`                    — BHK Thm 1.3 for `C_v` given `v ↮ a`, twice;
* `blockHarrisTransfer` (T1): `μ(D ∩ {o↔v})·SH_v ≤ μ(D)·SH_o`, `SH_x = ∫_{Xa ∪ Xb} F(C(a)) − μ(Xa ∪ Xb)·∫F(C(a))`
  — Harris on `{o ↔ {a,b,v}}` + BHK two-SET association (`S = {v}`, `T = {a,b}`: given `v ↮ {a,b}`, `1{o ∈ C_v}` and `F(C(a))`
  are negatively correlated);
* `plusPiece_nonneg`: `μ(Xb ∩ Q)·∫_Q (F(C_b) − F(C_a)) ≤ μ(Q)·∫_{Xb ∩ Q} (F(C_b) − F(C_a))`     — BHK Thm 1.5.
They are assembled in `Continuity/LowerTail/SurplusTransferPairOfCov.lean`.
[cite: VandenbergHaggstromKahn2005, Thms. 1.3–1.5 (pp. 6–8), Thm. 2.1 (p. 9), Remark 1 (p. 5)]
-/

noncomputable section

namespace Percolation.Continuity.SurplusTransfer

open MeasureTheory Set
open Percolation.Literature.LatticeModels (prodBernoulli)
open Percolation.Literature Percolation.Literature.KNPreFKG
open Percolation.Literature.TwoSetExchange

variable {V : Type*}

/-! ## Tools: types of events for the two-set exchange, reading a cluster off the union of clusters -/

/-- Reading the cluster of `a` off an edge set squeezed between `C_a(ω)` and `ω` gives `C(a)`. [folklore] -/
theorem openCluster_eq_of_subset_of_subset {ω : BondConfig V} {E : Set (Sym2 V)} {a : V}
    (h1 : openEdgeCluster ω a ⊆ E) (h2 : E ⊆ ω) : openCluster E a = openCluster ω a := by
  refine Subset.antisymm (openCluster_mono h2 a) fun x hx => ?_
  obtain ⟨p⟩ := (hx : (openGraph ω).Reachable a x)
  have hp : ∀ e' ∈ p.edges, e' ∈ (openGraph E).edgeSet := fun e' he => by
    have he1 : e' ∈ openEdgeCluster ω a := edge_mem_openEdgeCluster_of_walk p e' he
    have he2 := ((mem_openEdgeCluster_iff ω a e').1 he1).2.1
    change e' ∈ (SimpleGraph.fromEdgeSet E).edgeSet
    rw [SimpleGraph.edgeSet_fromEdgeSet]
    exact ⟨h1 he1, he2⟩
  exact ⟨p.transfer (openGraph E) hp⟩

/-- The cluster of `a ∈ T` read off `C_T = ⋃_{t ∈ T} C_t` is `C(a)`. [folklore] -/
theorem openCluster_biUnion_eq {ω : BondConfig V} {T : Set V} {a : V} (ha : a ∈ T) :
    openCluster (⋃ t ∈ T, openEdgeCluster ω t) a = openCluster ω a :=
  openCluster_eq_of_subset_of_subset (fun _ he => Set.mem_biUnion ha he)
    (Set.iUnion₂_subset fun t _ => openEdgeCluster_subset ω t)

/-- The union of clusters over a singleton. [folklore] -/
theorem biUnion_singleton_openEdgeCluster (ω : BondConfig V) (v : V) :
    (⋃ s ∈ ({v} : Set V), openEdgeCluster ω s) = openEdgeCluster ω v :=
  Set.biUnion_singleton v _

/-- The separation event of the two-set exchange for `S = {v}`, `T = {a, b}` is `{v ↮ a} ∩ {v ↮ b}`. [folklore] -/
theorem sep_singleton_pair (v a b : V) :
    {ω : BondConfig V | ∀ s ∈ ({v} : Set V), ∀ t ∈ ({a, b} : Set V), ¬ (openGraph ω).Reachable s t} =
      {ω : BondConfig V | ¬ (openGraph ω).Reachable v a} ∩ {ω | ¬ (openGraph ω).Reachable v b} := by
  ext ω
  simp only [mem_singleton_iff, mem_insert_iff, forall_eq_or_imp, forall_eq, mem_setOf_eq, mem_inter_iff]

/-- The separation event of the two-set exchange for `S = {v}`, `T = {a}` is `{v ↮ a}`. [folklore] -/
theorem sep_singleton_singleton (v a : V) :
    {ω : BondConfig V | ∀ s ∈ ({v} : Set V), ∀ t ∈ ({a} : Set V), ¬ (openGraph ω).Reachable s t} =
      {ω : BondConfig V | ¬ (openGraph ω).Reachable v a} := by
  ext ω
  simp only [mem_singleton_iff, forall_eq, mem_setOf_eq]

section Measure

variable [Fintype V]

/-! ## (α) and T4: pure event inequalities from the two-set exchange -/

/-- **T4, the transfer of the order piece.**  `μ(D ∩ {o ↔ v})·μ({v ↔ b} ∩ Q) ≤ μ(D)·μ({o ↔ b} ∩ Q)` with
`D = {v ↮ a} ∩ {v ↮ b}`, `Q = {a ↮ b}`: given `v ↮ a`, `{v ↔ o}` is positively correlated with `{v ↔ b}` and negatively
with `{v ↮ b}` (BHK Thm 1.3 for `C_v`), and `{v ↔ o} ∩ {v ↔ b} ∩ {v ↮ a} ⊆ {o ↔ b} ∩ Q`.
[cite: VandenbergHaggstromKahn2005, Thm. 1.3 (p. 6)] -/
theorem ordTransfer (w : Sym2 V → unitInterval) (o v a b : V) :
    (prodBernoulli w).real (({ω : BondConfig V | ¬ (openGraph ω).Reachable v a} ∩ {ω | ¬ (openGraph ω).Reachable v b}) ∩
        openConn o v) *
      (prodBernoulli w).real (openConn v b ∩ (openConn a b)ᶜ : Set (BondConfig V)) ≤
    (prodBernoulli w).real ({ω : BondConfig V | ¬ (openGraph ω).Reachable v a} ∩ {ω | ¬ (openGraph ω).Reachable v b}) *
      (prodBernoulli w).real (openConn o b ∩ (openConn a b)ᶜ : Set (BondConfig V)) := by
  classical
  set μ := prodBernoulli w with hμ
  have hn := fun (S : Set (BondConfig V)) => (measureReal_nonneg : 0 ≤ μ.real S)
  set D' : Set (BondConfig V) := {ω | ¬ (openGraph ω).Reachable v a} with hD'
  set Nb : Set (BondConfig V) := {ω | ¬ (openGraph ω).Reachable v b} with hNb
  -- (i) positive correlation of `{v↔o}`, `{v↔b}` given `v ↮ a`
  have h1 := setTwoClusterExchange w ({v} : Set V) ({a} : Set V)
    (A₁ := openConn v o) (B₁ := univ) (A₂ := openConn v b) (B₂ := univ)
    (typePlus_openConn_of_mem {v} {a} (by simp) o) (typePlus_openConn_of_mem {v} {a} (by simp) b)
    (fun _ _ _ _ _ => mem_univ _) (fun _ _ _ _ _ => mem_univ _)
  -- (ii) negative correlation of `{v↔o}`, `{v↮b}` given `v ↮ a`
  have h2 := setTwoClusterExchange w ({v} : Set V) ({a} : Set V)
    (A₁ := openConn v o) (B₁ := (openConn v b : Set (BondConfig V))ᶜ) (A₂ := univ) (B₂ := univ)
    (typePlus_openConn_of_mem {v} {a} (by simp) o) (fun _ _ _ _ _ => mem_univ _)
    (typeMinus_not_openConn_of_mem {v} {a} (by simp) b) (fun _ _ _ _ _ => mem_univ _)
  simp only [sep_singleton_singleton, inter_univ] at h1 h2
  -- identify the sets
  have hNb' : (openConn v b : Set (BondConfig V))ᶜ = Nb := by ext ω; simp [hNb, openConn]
  rw [hNb'] at h2
  have hDOV : (D' ∩ Nb) ∩ openConn o v = D' ∩ (openConn v o ∩ Nb) := by
    rw [openConn_symm o v]; ext ω; simp only [mem_inter_iff]; tauto
  have hVbQ : (openConn v b ∩ (openConn a b)ᶜ : Set (BondConfig V)) = D' ∩ openConn v b := by
    ext ω
    simp only [mem_inter_iff, mem_compl_iff, openConn, mem_setOf_eq, hD']
    constructor
    · rintro ⟨hvb, hab⟩; exact ⟨fun hva => hab (hva.symm.trans hvb), hvb⟩
    · rintro ⟨hva, hvb⟩; exact ⟨hvb, fun hab => hva (hvb.trans hab.symm)⟩
  have hsub : D' ∩ (openConn v o ∩ openConn v b) ⊆ (openConn o b ∩ (openConn a b)ᶜ : Set (BondConfig V)) := by
    intro ω hω
    simp only [mem_inter_iff, mem_compl_iff, openConn, mem_setOf_eq, hD'] at hω ⊢
    obtain ⟨hva, hvo, hvb⟩ := hω
    exact ⟨hvo.symm.trans hvb, fun hab => hva (hvb.trans hab.symm)⟩
  have h3 : μ.real (D' ∩ (openConn v o ∩ openConn v b)) ≤ μ.real (openConn o b ∩ (openConn a b)ᶜ : Set (BondConfig V)) :=
    measureReal_mono hsub (measure_ne_top _ _)
  rw [hDOV, hVbQ]
  -- chain: μ(D')·[μ(D'∩(vo∩Nb))·μ(D'∩vb)] ≤ μ(D'∩vo)μ(D'∩Nb)μ(D'∩vb) ≤ μ(D'∩Nb)·μ(D')μ(D'∩vo∩vb)
  by_cases hD0 : μ.real D' = 0
  · have h0 : μ.real (D' ∩ (openConn v o ∩ Nb)) = 0 :=
      le_antisymm (hD0 ▸ measureReal_mono inter_subset_left (measure_ne_top _ _)) (hn _)
    rw [h0, zero_mul]
    exact mul_nonneg (hn _) (hn _)
  · have hDpos : 0 < μ.real D' := lt_of_le_of_ne (hn _) (Ne.symm hD0)
    have e1 : μ.real D' * (μ.real (D' ∩ (openConn v o ∩ Nb)) * μ.real (D' ∩ openConn v b)) ≤
        μ.real (D' ∩ openConn v o) * μ.real (D' ∩ Nb) * μ.real (D' ∩ openConn v b) := by
      nlinarith [h2, hn (D' ∩ openConn v b)]
    have e2 : μ.real (D' ∩ openConn v o) * μ.real (D' ∩ Nb) * μ.real (D' ∩ openConn v b) ≤
        μ.real (D' ∩ Nb) * (μ.real D' * μ.real (D' ∩ (openConn v o ∩ openConn v b))) := by
      nlinarith [h1, hn (D' ∩ Nb)]
    have e3 : μ.real (D' ∩ Nb) * (μ.real D' * μ.real (D' ∩ (openConn v o ∩ openConn v b))) ≤
        μ.real (D' ∩ Nb) * (μ.real D' * μ.real (openConn o b ∩ (openConn a b)ᶜ : Set (BondConfig V))) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 (hn _)) (hn _)
    have e4 : μ.real D' * (μ.real (D' ∩ (openConn v o ∩ Nb)) * μ.real (D' ∩ openConn v b)) ≤
        μ.real D' * (μ.real (D' ∩ Nb) * μ.real (openConn o b ∩ (openConn a b)ᶜ : Set (BondConfig V))) := by
      nlinarith [e1, e2, e3]
    exact le_of_mul_le_mul_left e4 hDpos

/-! ## T1: the transfer of the block-Harris piece -/

/-- **T1, the transfer of the block-Harris piece.** With `f_a = F(C(a))`, `m_a = ∫ f_a`, `D = {v ↮ a} ∩ {v ↮ b}`,
`SH_x = ∫_{x↔a ∨ x↔b} f_a − μ(x↔a ∨ x↔b)·m_a`:  `μ(D ∩ {o ↔ v})·SH_v ≤ μ(D)·SH_o`.
Proof: `{o↔a} ∪ {o↔b} ∪ {o↔v} = ({o↔a} ∪ {o↔b}) ⊔ (D ∩ {o↔v})`, Harris for `f_a` on this increasing event, and the
two-SET conditional association (BHK Thm 2.1 at `q = 1`, `S = {v}`, `T = {a,b}`): given `v ↮ {a,b}`, `1{v ↔ o}` (increasing in
`C_v`) and `F(C(a))` (increasing in `C_a ∪ C_b`) are negatively correlated; finally `Dᶜ = {v↔a} ∪ {v↔b}`.
[cite: VandenbergHaggstromKahn2005, Thm. 2.1 (p. 9) at q = 1, Remark 1 (p. 5)] -/
theorem blockHarrisTransfer (w : Sym2 V → unitInterval) (o v a b : V) (F : Set V → ℝ)
    (hF : ∀ S T : Set V, S ⊆ T → F S ≤ F T) (hF0 : ∀ S, 0 ≤ F S) :
    (prodBernoulli w).real (({ω : BondConfig V | ¬ (openGraph ω).Reachable v a} ∩ {ω | ¬ (openGraph ω).Reachable v b}) ∩
        openConn o v) *
      (∫ ω in (openConn v a ∪ openConn v b), F (openCluster ω a) ∂(prodBernoulli w) -
        (prodBernoulli w).real (openConn v a ∪ openConn v b : Set (BondConfig V)) * ∫ ω, F (openCluster ω a) ∂(prodBernoulli w)) ≤
    (prodBernoulli w).real ({ω : BondConfig V | ¬ (openGraph ω).Reachable v a} ∩ {ω | ¬ (openGraph ω).Reachable v b}) *
      (∫ ω in (openConn o a ∪ openConn o b), F (openCluster ω a) ∂(prodBernoulli w) -
        (prodBernoulli w).real (openConn o a ∪ openConn o b : Set (BondConfig V)) * ∫ ω, F (openCluster ω a) ∂(prodBernoulli w)) := by
  classical
  set μ := prodBernoulli w with hμ
  set f : BondConfig V → ℝ := fun ω => F (openCluster ω a) with hf
  set m : ℝ := ∫ ω, f ω ∂μ with hm
  have hmeas : ∀ T : Set (BondConfig V), MeasurableSet T := fun _ => MeasurableSet.of_discrete
  have hint : ∀ (k : BondConfig V → ℝ) (T : Set (BondConfig V)), IntegrableOn k T μ :=
    fun k T => (Integrable.of_finite).integrableOn
  have hn := fun (S : Set (BondConfig V)) => (measureReal_nonneg : 0 ≤ μ.real S)
  set D : Set (BondConfig V) := {ω | ¬ (openGraph ω).Reachable v a} ∩ {ω | ¬ (openGraph ω).Reachable v b} with hD
  set Uo : Set (BondConfig V) := openConn o a ∪ openConn o b with hUo
  set Uv : Set (BondConfig V) := openConn v a ∪ openConn v b with hUv
  set Ov : Set (BondConfig V) := openConn o v with hOv
  set U' : Set (BondConfig V) := Uo ∪ Ov with hU'
  -- (1) Harris on `U'`
  have hHarris : μ.real U' * m ≤ ∫ ω in U', f ω ∂μ :=
    AGloc.setIntegral_clusterFun_ge w a F hF hF0 U'
      (((isUpperSet_openConn o a).union (isUpperSet_openConn o b)).union (isUpperSet_openConn o v))
  -- (2) two-set association: `1{v ↔ o}` and `F(C(a))` negatively correlated given `v ↮ {a,b}`
  have hG : Monotone fun E : Set (Sym2 V) => F (openCluster E a) := fun E E' h => hF _ _ (openCluster_mono h a)
  have hBHK := BHK2006_twoSetConditionalAssociation.negCorrelation w ({v} : Set V) ({a, b} : Set V)
    ((connFamily v o).indicator 1) (fun E => F (openCluster E a))
    (monotone_indicator_one_of_isUpperSet (isUpperSet_connFamily v o)) hG
  have hfun1 : ∀ ω : BondConfig V, (connFamily v o).indicator (1 : Set (Sym2 V) → ℝ) (⋃ s ∈ ({v} : Set V), openEdgeCluster ω s) =
      Ov.indicator (1 : BondConfig V → ℝ) ω := fun ω => by
    rw [biUnion_singleton_openEdgeCluster, congrFun (indicator_comp_openEdgeCluster (connFamily v o) v) ω,
      ← openConn_eq_setOf_connFamily, hOv, openConn_symm o v]
  have hfun2 : ∀ ω : BondConfig V, F (openCluster (⋃ t ∈ ({a, b} : Set V), openEdgeCluster ω t) a) = f ω := fun ω => by
    rw [openCluster_biUnion_eq (show a ∈ ({a, b} : Set V) by simp)]
  simp only [sep_singleton_pair, hfun1, hfun2] at hBHK
  rw [setIntegral_indicator_one_eq] at hBHK
  have hprod : ∫ ω in D, Ov.indicator (1 : BondConfig V → ℝ) ω * f ω ∂μ = ∫ ω in D ∩ Ov, f ω ∂μ := by
    rw [← setIntegral_mul_indicator_one μ D Ov f]
    refine setIntegral_congr_fun (hmeas D) fun ω _ => ?_
    ring
  rw [hprod] at hBHK
  change μ.real D * ∫ ω in D ∩ Ov, f ω ∂μ ≤ μ.real (D ∩ Ov) * ∫ ω in D, f ω ∂μ at hBHK
  -- (3) `U' = Uo ⊔ (D ∩ Ov)`
  have hUdiff : U' \ Uo = D ∩ Ov := by
    ext ω
    simp only [hU', hUo, hOv, hD, mem_sdiff, mem_union, mem_inter_iff, openConn, mem_setOf_eq]
    constructor
    · rintro ⟨(h1 | h1) | h2, hn1⟩
      · exact absurd (Or.inl h1) hn1
      · exact absurd (Or.inr h1) hn1
      · exact ⟨⟨fun h => hn1 (Or.inl (h2.trans h)), fun h => hn1 (Or.inr (h2.trans h))⟩, h2⟩
    · rintro ⟨⟨hna, hnb⟩, h2⟩
      exact ⟨Or.inr h2, fun h1 => h1.elim (fun h => hna (h2.symm.trans h)) (fun h => hnb (h2.symm.trans h))⟩
  have hUint : ∫ ω in U', f ω ∂μ = ∫ ω in Uo, f ω ∂μ + ∫ ω in D ∩ Ov, f ω ∂μ := by
    rw [← integral_inter_add_sdiff (hmeas Uo) (hint f U'), inter_eq_right.2 subset_union_left, hUdiff]
  have hUμ : μ.real U' = μ.real Uo + μ.real (D ∩ Ov) := by
    rw [← measureReal_inter_add_sdiff (s := U') (h := measure_ne_top _ _) (hmeas Uo), inter_eq_right.2 subset_union_left,
      hUdiff]
  -- (4) `D = Uvᶜ`
  have hDU : D = Uvᶜ := by
    ext ω
    simp [hD, hUv, openConn]
  have hDint : ∫ ω in D, f ω ∂μ = m - ∫ ω in Uv, f ω ∂μ := by
    have := integral_add_compl (hmeas Uv) (Integrable.of_finite (f := f) (μ := μ))
    rw [← hDU] at this
    linarith
  have hDμ : μ.real D = 1 - μ.real Uv := by
    have h1 : μ.real (univ : Set (BondConfig V)) = μ.real (univ ∩ Uv) + μ.real (univ \ Uv) :=
      (measureReal_inter_add_sdiff (s := univ) (h := measure_ne_top _ _) (hmeas Uv)).symm
    rw [probReal_univ, univ_inter, ← compl_eq_univ_sdiff, ← hDU] at h1
    linarith
  -- assemble
  have hA : ∫ ω in Uo, f ω ∂μ - μ.real Uo * m ≥ μ.real (D ∩ Ov) * m - ∫ ω in D ∩ Ov, f ω ∂μ := by
    rw [hUint, hUμ] at hHarris
    linarith
  have hB : μ.real D * (μ.real (D ∩ Ov) * m - ∫ ω in D ∩ Ov, f ω ∂μ) ≥
      μ.real D * (μ.real (D ∩ Ov) * m) - μ.real (D ∩ Ov) * ∫ ω in D, f ω ∂μ := by
    rw [mul_sub]
    linarith [hBHK]
  have hC := mul_le_mul_of_nonneg_left hA (hn D)
  have hDOv : D ∩ openConn o v = D ∩ Ov := rfl
  rw [hDOv]
  rw [hDint, hDμ] at hB
  rw [hDμ] at hC ⊢
  nlinarith [hB, hC, hn (D ∩ Ov), hn Uv]

/-! ## The BHK-1.5 piece is nonnegative -/

/-- **The (+)-type piece is nonnegative.** With `Q = {a ↮ b}` and `h = F(C(b)) − F(C(a))` (increasing in `C_b`, decreasing in `C_a`):
`μ({x ↔ b} ∩ Q)·∫_Q h ≤ μ(Q)·∫_{{x↔b} ∩ Q} h` (BHK Thm 1.5 for `(C_b, C_a)` given `a ↮ b`: `1{x ∈ C_b}` and `h` are both of type `(+)`).
[cite: VandenbergHaggstromKahn2005, Thm. 1.5 (p. 7, eq. (9))] -/
theorem plusPiece_nonneg (w : Sym2 V → unitInterval) (x a b : V) (hab : a ≠ b) (F : Set V → ℝ)
    (hF : ∀ S T : Set V, S ⊆ T → F S ≤ F T) :
    (prodBernoulli w).real (openConn x b ∩ (openConn a b)ᶜ : Set (BondConfig V)) *
        ∫ ω in (openConn a b)ᶜ, (F (openCluster ω b) - F (openCluster ω a)) ∂(prodBernoulli w) ≤
      (prodBernoulli w).real ((openConn a b)ᶜ : Set (BondConfig V)) *
        ∫ ω in (openConn x b ∩ (openConn a b)ᶜ : Set (BondConfig V)), (F (openCluster ω b) - F (openCluster ω a)) ∂(prodBernoulli w) := by
  classical
  set μ := prodBernoulli w with hμ
  have hmeas : ∀ T : Set (BondConfig V), MeasurableSet T := fun _ => MeasurableSet.of_discrete
  have key := BHK2006_twoClusterConditionalAssociation_holds V w b a
    (fun C _ => (connFamily b x).indicator (1 : Set (Sym2 V) → ℝ) C)
    (fun C E => F {y | y = b ∨ ∃ e ∈ C, y ∈ e} - F {y | y = a ∨ ∃ e ∈ E, y ∈ e})
    (fun _ => monotone_indicator_one_of_isUpperSet (isUpperSet_connFamily b x)) (fun _ => antitone_const)
    (fun E C C' h => sub_le_sub_right (monotone_clusterFun b F hF h) _)
    (fun C E E' h => sub_le_sub_left (monotone_clusterFun a F hF h) _) hab.symm
  have hind : ∀ ω : BondConfig V, (connFamily b x).indicator (1 : Set (Sym2 V) → ℝ) (openEdgeCluster ω b) =
      (openConn x b : Set (BondConfig V)).indicator (1 : BondConfig V → ℝ) ω := fun ω => by
    rw [congrFun (indicator_comp_openEdgeCluster (connFamily b x) b) ω, ← openConn_eq_setOf_connFamily, openConn_symm x b]
  have hQ : {ω : BondConfig V | ¬ (openGraph ω).Reachable b a} = (openConn a b : Set (BondConfig V))ᶜ := by
    ext ω
    simp only [mem_setOf_eq, mem_compl_iff, openConn]
    exact ⟨fun h h' => h h'.symm, fun h h' => h h'.symm⟩
  simp only [clusterFun_openEdgeCluster, hind, hQ] at key
  rw [setIntegral_indicator_one_eq] at key
  have hprod : ∫ ω in (openConn a b : Set (BondConfig V))ᶜ,
      (openConn x b : Set (BondConfig V)).indicator (1 : BondConfig V → ℝ) ω * (F (openCluster ω b) - F (openCluster ω a)) ∂μ =
      ∫ ω in ((openConn a b)ᶜ ∩ openConn x b : Set (BondConfig V)), (F (openCluster ω b) - F (openCluster ω a)) ∂μ := by
    rw [← setIntegral_mul_indicator_one μ _ (openConn x b) (fun ω => F (openCluster ω b) - F (openCluster ω a))]
    refine setIntegral_congr_fun (hmeas _) fun ω _ => ?_
    ring
  rw [hprod] at key
  rw [inter_comm]
  exact key

end Measure

end Percolation.Continuity.SurplusTransfer

end
