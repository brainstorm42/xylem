import Percolation.Continuity.CovTau.MetaA2Defs
import Percolation.Continuity.CovTau.StarBridgeEdge
import Percolation.Continuity.CovTau.StarH
import Percolation.Util.Linter

/-!
# The one-source bounds (★^H) and `Y^H ≤ H` IN THE VOCABULARY OF THE GENERIC TWO-SOURCE INDUCTION (META-A2: `CovTau.Yw / Mav`, world functional `F(U') = Cov_{G[U']}(g(C_x), 1{v ↔ S})`)

The generic two-source induction META-A2 (`Continuity/CovTau/MetaA2Defs.lean` ff.: avoided SET `A`, observer functionals
`CovTau.Eav / Mav`, an arbitrary nonnegative pure world functional `F : Finset V → ℝ` entering through `CovTau.Yw / Xw`) is run, in
the instance "A2^H", with `A = S` (a marker set, `x ∈ S`, `v ∉ S`) and the world functional
  `F(U') = H_{G[U']}(v) = Cov_{G[U']}(g(C_x), 1{v ↔ S})`  (`CovTau.BfS`, this file; `CovTau.cfS = μ_{G[U]}(v ↔ S)`).
Its two ONE-SOURCE inputs are, for every sub-world `U'` and every source set `N`,
* `hstarH : Yw w U' x F N * Mav w U' S v ∅ ≤ Mav w U' S v N * F U'` — Lemma (★^H), and
* `hYBH  : Yw w U' x F N ≤ F U'` — its corollary (decision-tree Harris alone).
THIS FILE proves both (`CovTauStarN.yS_mul_mS_le`, `CovTauStarN.yS_le_bS`) from the finitary
edge-set forms `CovTauStarN.starH_ED` / `CovTauStarN.yH_le_covH` (`Continuity/CovTau/StarH.lean`:
law of total covariance along the exploration of `C_N`, Gladkov's decision-tree Harris inequality,
van den Berg–Häggström–Kahn's Theorem 1.4 with the set `S`) through the dictionary of
`Continuity/CovTau/StarBridge.lean` (`G[U] ↔` coordinates `pairsIn U`, `sum_weight_restrict`, `rest
U N = U ∖ C_N ↔ off`, `srcF`): `Mav_eq_ED`, `BfS_sdiff_eq_covH`, `Yw_BfS_eq_yH`. Also: `BfS ≥ 0`
(Harris) and the vanishing of `BfS` in worlds missing `v` or `x`. At `S = {x}` everything
specialises to `Continuity/CovTau/StarBridgeEdge.lean`. [cite: VandenbergHaggstromKahn2005, Thm. 1.1
(pp. 3–5), Thm. 1.4 (p. 7), eq. (6) (p. 4)] [cite: Gladkov2024, Thm. 3.2 (p. 4)]
-/

noncomputable section

namespace Percolation.Continuity

open Finset MeasureTheory Percolation.Literature Percolation.Literature.DecisionTree
open Percolation.Literature.BHK2006 (weight edgesIn rC rD weight_nonneg harris)
open SetClusterExploration TreeHarris
open scoped Classical

namespace CovTau

variable {V : Type*} [Fintype V]

/-! ### The world functional `H_{G[U]}(v) = Cov_{G[U]}(g(C_x), 1{v ↔ S})` -/

/-- `μ_{G[U]}(v ↔ S)`: some vertex of the marker set `S` is joined to `v` by an open path inside `U`.
[cite: VandenbergHaggstromKahn2005, §1 p. 3 (the restricted model)] -/
def cfS (w : Sym2 V → ℝ) (U : Finset V) (S : Set V) (v : V) : ℝ :=
  ∑ ω, weight w ω * ind {ω : Set (Sym2 V) | ∃ s ∈ S, (openGraph (ω ∩ edgesIn U)).Reachable s v} ω

/-- **`H_{G[U]}(v) = Cov_{G[U]}(g(C_x), 1{v ↔ S})`** for an edge-cluster functional `g` and a marker
 set `S`. [cite: VandenbergHaggstromKahn2005, §1 p. 6 (Harris' inequality)]
-/
def BfS (w : Sym2 V → ℝ) (U : Finset V) (x : V) (S : Set V) (v : V) (g : Set (Sym2 V) → ℝ) : ℝ :=
  (∑ ω, weight w ω * (g (rC U x ω) *
      ind {ω : Set (Sym2 V) | ∃ s ∈ S, (openGraph (ω ∩ edgesIn U)).Reachable s v} ω)) - tfE w U x g * cfS w U S v

/-- **`H ≥ 0` (Harris)**: `g(C_x)` and `1{v ↔ S}` are increasing. [cite: VandenbergHaggstromKahn2005, §1 p. 6 (Harris' inequality)] -/
theorem BfS_nonneg {w : Sym2 V → ℝ} (hw0 : ∀ e, 0 ≤ w e) (hw1 : ∀ e, w e ≤ 1) (hm : ∑ ω, weight w ω = 1)
    (U : Finset V) (x : V) (S : Set V) (v : V) {g : Set (Sym2 V) → ℝ} (hg : Monotone g) (hg0 : ∀ C, 0 ≤ g C) :
    0 ≤ BfS w U x S v g := by
  have h := harris hw0 hw1 (f := fun ω => g (rC U x ω))
    (g := ind {ω : Set (Sym2 V) | ∃ s ∈ S, (openGraph (ω ∩ edgesIn U)).Reachable s v})
    (fun _ => hg0 _) (fun _ => ind_nonneg _ _) (fun a b hab => hg (BHK2006.rC_mono U x hab))
    (by
      intro a b hab
      by_cases ha : a ∈ {ω : Set (Sym2 V) | ∃ s ∈ S, (openGraph (ω ∩ edgesIn U)).Reachable s v}
      · have hb : b ∈ {ω : Set (Sym2 V) | ∃ s ∈ S, (openGraph (ω ∩ edgesIn U)).Reachable s v} := by
          obtain ⟨s, hs, hr⟩ := Set.mem_setOf.1 ha
          exact Set.mem_setOf.2 ⟨s, hs, hr.mono (BHK2006.openGraph_le (Set.inter_subset_inter_left _ hab))⟩
        rw [ind_of_mem ha, ind_of_mem hb]
      · rw [ind_of_not_mem ha]; exact ind_nonneg _ _)
  rw [hm, one_mul] at h
  unfold BfS tfE cfS
  linarith

/-- In a world not containing `v`, with `v ∉ S`, the covariance `H` vanishes (`v` is isolated in `G[U]`). [folklore] -/
theorem BfS_eq_zero_of_not_mem (w : Sym2 V → ℝ) {U : Finset V} (x : V) {S : Set V} {v : V} (hv : v ∉ U) (hvS : v ∉ S)
    (g : Set (Sym2 V) → ℝ) : BfS w U x S v g = 0 := by
  unfold BfS tfE cfS
  have h0 : ∀ ω : Set (Sym2 V), ind {ω : Set (Sym2 V) | ∃ s ∈ S, (openGraph (ω ∩ edgesIn U)).Reachable s v} ω = 0 :=
    fun ω => ind_of_not_mem fun ⟨s, hs, h⟩ => hv (SandwichBHK.mem_of_reachable h fun h' => hvS (h' ▸ hs))
  simp only [h0, mul_zero, Finset.sum_const_zero]; ring

end CovTau

namespace CovTauStarN

open CovTau

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Dictionary: `Mav`, `cfS`, `BfS`, `Yw` as `ED`-expressions on the coordinates `pairsIn U` -/

omit [DecidableEq V] in
/-- `1{v ↔ S in G[U]}` on `K ⊆ pairsIn U` is `nr (srcF S) v K`. [folklore] -/
theorem ind_nreach_eq_nr {U : Finset V} (S : Set V) (v : V) {K : Finset (Sym2 V)} (hK : K ⊆ pairsIn U) :
    ind {ω : Set (Sym2 V) | ∃ s ∈ S, (openGraph (ω ∩ edgesIn U)).Reachable s v} (↑K : Set (Sym2 V)) = nr (srcF S) v K := by
  unfold nr
  refine BystanderBHK.ind_congr ?_
  simp only [Set.mem_setOf_eq, coe_inter_edgesIn_of_subset hK, mem_srcF]

omit [DecidableEq V] in
/-- `1{v ↮ S ∪ N in G[U]}` on `K ⊆ pairsIn U` is `(1 − nr (srcF S) v K)(1 − nr (srcF N) v K)`. [folklore] -/
theorem ind_rD_union_eq {U : Finset V} (v : V) (S N : Set V) {K : Finset (Sym2 V)} (hK : K ⊆ pairsIn U) :
    ind (rD U v (S ∪ N)) (↑K : Set (Sym2 V)) = (1 - nr (srcF S) v K) * (1 - nr (srcF N) v K) := by
  unfold nr
  have hmem : (↑K : Set (Sym2 V)) ∈ rD U v (S ∪ N) ↔
      (¬ ∃ s ∈ srcF S, (openGraph (↑K : Set (Sym2 V))).Reachable s v) ∧
        ¬ ∃ s ∈ srcF N, (openGraph (↑K : Set (Sym2 V))).Reachable s v := by
    simp only [rD, Set.mem_setOf_eq, coe_inter_edgesIn_of_subset hK, Set.mem_union, or_imp, forall_and, not_exists,
      not_and, mem_srcF]
    exact ⟨fun h => ⟨fun s hs h' => h.1 s hs h'.symm, fun s hs h' => h.2 s hs h'.symm⟩,
      fun h => ⟨fun s hs h' => h.1 s hs h'.symm, fun s hs h' => h.2 s hs h'.symm⟩⟩
  by_cases h1 : ∃ s ∈ srcF S, (openGraph (↑K : Set (Sym2 V))).Reachable s v
  · rw [ind_of_mem (show K ∈ {L : Finset (Sym2 V) | ∃ s ∈ srcF S, (openGraph (↑L : Set (Sym2 V))).Reachable s v} from h1),
      ind_of_not_mem (show (↑K : Set (Sym2 V)) ∉ rD U v (S ∪ N) from fun h => (hmem.1 h).1 h1)]
    ring
  · rw [ind_of_not_mem (show K ∉ {L : Finset (Sym2 V) | ∃ s ∈ srcF S, (openGraph (↑L : Set (Sym2 V))).Reachable s v} from h1)]
    by_cases h2 : ∃ s ∈ srcF N, (openGraph (↑K : Set (Sym2 V))).Reachable s v
    · rw [ind_of_mem (show K ∈ {L : Finset (Sym2 V) | ∃ s ∈ srcF N, (openGraph (↑L : Set (Sym2 V))).Reachable s v} from h2),
        ind_of_not_mem (show (↑K : Set (Sym2 V)) ∉ rD U v (S ∪ N) from fun h => (hmem.1 h).2 h2)]
      ring
    · rw [ind_of_not_mem (show K ∉ {L : Finset (Sym2 V) | ∃ s ∈ srcF N, (openGraph (↑L : Set (Sym2 V))).Reachable s v}
          from h2), ind_of_mem (hmem.2 ⟨h1, h2⟩)]
      ring

/-- `Mav w U S v N = E[(1 − nr S)(1 − nr N)]` on the coordinates `pairsIn U`. [folklore] -/
theorem Mav_eq_ED (w : Sym2 V → ℝ) (U : Finset V) (S : Set V) (v : V) (N : Set V) :
    Mav w U S v N = ED (pairsIn U) w (fun K => (1 - nr (srcF S) v K) * (1 - nr (srcF N) v K)) := by
  unfold Mav
  rw [sum_weight_restrict w U _ (fun ω => by
    refine BystanderBHK.ind_congr ?_
    simp only [rD, Set.mem_setOf_eq, Set.inter_assoc, Set.inter_self])]
  exact ED_congr_on _ w fun K hK => ind_rD_union_eq v S N (Finset.mem_powerset.1 hK)

/-- `Mav w U S v ∅ = E[1 − nr S]`. [folklore] -/
theorem Mav_empty_eq_ED (w : Sym2 V → ℝ) (U : Finset V) (S : Set V) (v : V) :
    Mav w U S v ∅ = ED (pairsIn U) w (fun K => 1 - nr (srcF S) v K) := by
  rw [Mav_eq_ED]
  refine ED_congr_on _ w fun K _ => ?_
  have : nr (srcF (∅ : Set V)) v K = 0 := ind_of_not_mem fun ⟨s, hs, _⟩ => by
    rw [mem_srcF] at hs; exact hs
  rw [this]; ring

/-- **`BfS` in the world `U ∖ W` is `covH` on the coordinates `pairsIn U`.** [folklore] -/
theorem BfS_sdiff_eq_covH (w : Sym2 V → ℝ) (U W : Finset V) (x : V) (S : Set V) (v : V) (g : Set (Sym2 V) → ℝ) :
    BfS w (U \ W) x S v g = covH (pairsIn U) w g x (srcF S) v W := by
  have hsub : pairsIn (U \ W) ⊆ pairsIn U := by rw [pairsIn_sdiff]; exact off_subset W _
  have hrC : ∀ (U' : Finset V) (ω : Set (Sym2 V)), rC U' x (ω ∩ edgesIn U') = rC U' x ω := fun U' ω => by
    show openEdgeCluster (ω ∩ edgesIn U' ∩ edgesIn U') x = openEdgeCluster (ω ∩ edgesIn U') x
    rw [Set.inter_assoc, Set.inter_self]
  have h1 : ∑ ω, weight w ω * (g (rC (U \ W) x ω) *
      ind {ω : Set (Sym2 V) | ∃ s ∈ S, (openGraph (ω ∩ edgesIn (U \ W))).Reachable s v} ω) =
      ED (pairsIn (U \ W)) w (fun K => fcl g x K * nr (srcF S) v K) := by
    rw [sum_weight_restrict w (U \ W) _ (fun ω => by
      rw [hrC]
      congr 1
      refine BystanderBHK.ind_congr ?_
      simp only [Set.mem_setOf_eq, Set.inter_assoc, Set.inter_self])]
    exact ED_congr_on _ w fun K hK => by
      rw [g_rC_eq_fcl g x (Finset.mem_powerset.1 hK), ind_nreach_eq_nr S v (Finset.mem_powerset.1 hK)]
  have h2 : tfE w (U \ W) x g = ED (pairsIn (U \ W)) w (fcl g x) := by
    unfold tfE
    rw [sum_weight_restrict w (U \ W) _ (fun ω => by rw [hrC])]
    exact ED_congr_on _ w fun K hK => g_rC_eq_fcl g x (Finset.mem_powerset.1 hK)
  have h3 : cfS w (U \ W) S v = ED (pairsIn (U \ W)) w (nr (srcF S) v) := by
    unfold cfS
    rw [sum_weight_restrict w (U \ W) _ (fun ω => by
      refine BystanderBHK.ind_congr ?_
      simp only [Set.mem_setOf_eq, Set.inter_assoc, Set.inter_self])]
    exact ED_congr_on _ w fun K hK => ind_nreach_eq_nr S v (Finset.mem_powerset.1 hK)
  unfold BfS covH
  rw [h1, h2, h3]
  have e1 : ED (pairsIn U) w (fun K => fcl g x (off W K) * nr (srcF S) v (off W K)) =
      ED (pairsIn (U \ W)) w (fun K => fcl g x K * nr (srcF S) v K) := by
    rw [← ED_inter_eq hsub w (fun K => fcl g x K * nr (srcF S) v K)]
    exact ED_congr_on _ w fun K hK => by rw [off_eq_inter W (Finset.mem_powerset.1 hK)]
  have e2 : ED (pairsIn U) w (fun K => fcl g x (off W K)) = ED (pairsIn (U \ W)) w (fcl g x) := by
    rw [← ED_inter_eq hsub w (fcl g x)]
    exact ED_congr_on _ w fun K hK => by rw [off_eq_inter W (Finset.mem_powerset.1 hK)]
  have e3 : ED (pairsIn U) w (fun K => nr (srcF S) v (off W K)) = ED (pairsIn (U \ W)) w (nr (srcF S) v) := by
    rw [← ED_inter_eq hsub w (nr (srcF S) v)]
    exact ED_congr_on _ w fun K hK => by rw [off_eq_inter W (Finset.mem_powerset.1 hK)]
  rw [e1, e2, e3]

/-- `BfS w U x S v g = covH (pairsIn U) w g x (srcF S) v ∅`. [folklore] -/
theorem BfS_eq_covH (w : Sym2 V → ℝ) (U : Finset V) (x : V) (S : Set V) (v : V) (g : Set (Sym2 V) → ℝ) :
    BfS w U x S v g = covH (pairsIn U) w g x (srcF S) v ∅ := by
  rw [← BfS_sdiff_eq_covH, Finset.sdiff_empty]

/-- **`Yw` of the world functional `U' ↦ H_{G[U']}(v)` is `yH`** on the coordinates `pairsIn U`. [folklore] -/
theorem Yw_BfS_eq_yH (w : Sym2 V → ℝ) (U : Finset V) (x : V) (S : Set V) (v : V) (g : Set (Sym2 V) → ℝ) (N : Set V) :
    Yw w U x (fun U' => BfS w U' x S v g) N = yH (pairsIn U) w g x (srcF S) v (srcF N) := by
  unfold Yw yH
  rw [sum_weight_restrict w U _ (fun ω => by
    have h1 : rest U N (ω ∩ edgesIn U) = rest U N ω := by simp only [rest, sC, Set.inter_assoc, Set.inter_self]
    have h2 : ind (rD U x N) (ω ∩ edgesIn U) = ind (rD U x N) ω :=
      BystanderBHK.ind_congr (by simp only [rD, Set.mem_setOf_eq, Set.inter_assoc, Set.inter_self])
    rw [h1, h2])]
  refine ED_congr_on _ w fun K hK => ?_
  have hK' := Finset.mem_powerset.1 hK
  dsimp only
  rw [rest_eq_sdiff hK', BfS_sdiff_eq_covH, ind_rD_eq x N hK', mul_comm]

/-! ### The one-source bounds in META-A2 vocabulary -/

/-- **(★^H) in every world `G[U]`, META-A2 vocabulary**: `Yw·Mav ∅ ≤ Mav N·H` for the world functional
`U' ↦ H_{G[U']}(v) = Cov_{G[U']}(g(C_x), 1{v ↔ S})`, `x ∈ S`, `v ∉ S` — the hypothesis `hstarH` of META-A2 / A2^H,
proved from `CovTauStarN.starH_ED`. [cite: Gladkov2024, Thm. 3.2 (p. 4)]
[cite: VandenbergHaggstromKahn2005, Thm. 1.4 (p. 7), eq. (6) (p. 4)] -/
theorem yS_mul_mS_le (w : Sym2 V → ℝ) (hw0 : ∀ e, 0 ≤ w e) (hw1 : ∀ e, w e ≤ 1) {x v : V} {S : Set V} (hxS : x ∈ S)
    (hvS : v ∉ S) {g : Set (Sym2 V) → ℝ} (hg : Monotone g) (hg0 : ∀ C, 0 ≤ g C) (U : Finset V) (N : Set V) :
    Yw w U x (fun U' => BfS w U' x S v g) N * Mav w U S v ∅ ≤ Mav w U S v N * BfS w U x S v g := by
  rw [Yw_BfS_eq_yH, Mav_empty_eq_ED, Mav_eq_ED, BfS_eq_covH]
  exact starH_ED (pairsIn U) hw0 hw1 (srcF N) x v (srcF S) (fun h => hvS (mem_srcF.1 h)) g (mem_srcF.2 hxS) hg hg0

/-- **`Y^H ≤ H` in every world `G[U]`, META-A2 vocabulary**: the hypothesis `hYBH` of META-A2 / A2^H, proved from
`CovTauStarN.yH_le_covH` (decision-tree Harris alone). [cite: Gladkov2024, Thm. 3.2 (p. 4)] -/
theorem yS_le_bS (w : Sym2 V → ℝ) (hw0 : ∀ e, 0 ≤ w e) (hw1 : ∀ e, w e ≤ 1) (x : V) {v : V} {S : Set V} (hvS : v ∉ S)
    {g : Set (Sym2 V) → ℝ} (hg : Monotone g) (hg0 : ∀ C, 0 ≤ g C) (U : Finset V) (N : Set V) :
    Yw w U x (fun U' => BfS w U' x S v g) N ≤ BfS w U x S v g := by
  rw [Yw_BfS_eq_yH, BfS_eq_covH]
  exact yH_le_covH (pairsIn U) hw0 hw1 (srcF N) x v (srcF S) (fun h => hvS (mem_srcF.1 h)) g hg hg0

end CovTauStarN

end Percolation.Continuity

end
