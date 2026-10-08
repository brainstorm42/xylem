import Percolation.Continuity.LowerTail.TreeHarrisReal
import Percolation.Literature.ConditionalPositiveAssociationProofs
import Percolation.Literature.SetClusterExploration
import Percolation.Util.Linter

/-!
# Preliminaries for Lemma (★_N) of the conditioned covariance transfer COV(τ) — finitary bridges, the world `G ∖ W`, and the hybrid along the exploration of `C_N`

* `integral_eq_ED`, `setIntegral_eq_ED`, `measureReal_eq_ED`, `ED_univ_eq_ED_of_zero` — `prodBernoulli` integrals are
  weighted-cube expectations `DecisionTree.ED` (all pairs), and zeroing the weights off `D` restricts to the coordinates `D`;
* `off W K` (the pairs meeting `W` closed = the world `G ∖ W`), cluster congruence `reachable_congr_of_agree` /
  `openEdgeCluster_congr_of_agree`;
* `splice_congr_of_mem_reached` / `splice_congr_of_not_mem_reached` — the Markov property at the explored cluster of `N`
  (`SetClusterExploration`): from `x ∈ C_N(K)` the hybrid `K →_{S_N(K)} K₂` looks like `K`, from
  `x ∉ C_N(K)` like `off (C_N K) K₂` [VandenbergHaggstromKahn2005, eq. (6)];
[cite: VandenbergHaggstromKahn2005, §1 pp. 3–4, eq. (6)] [cite: Gladkov2024, Def. 2.3–2.4, Lemma 3.1]
-/

noncomputable section

namespace Percolation.Continuity

namespace CovTauStarN

open Finset MeasureTheory Percolation.Literature Percolation.Literature.DecisionTree
open Percolation.Literature.LatticeModels (prodBernoulli)
open SetClusterExploration TreeHarris
open scoped Classical

/-! ### Finitary bridges: `prodBernoulli` integrals are weighted-cube expectations `ED` -/

section Bridge

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Restriction**: the expectation on all coordinates with the weights ZEROED off `D` is the expectation on the
coordinates `D`. [folklore] -/
theorem ED_univ_eq_ED_of_zero (D : Finset ι) (p q : ι → ℝ) (hq : ∀ i ∈ D, q i = p i) (hq0 : ∀ i ∉ D, q i = 0)
    (φ : Finset ι → ℝ) : ED Finset.univ q φ = ED D p φ := by
  unfold ED
  -- on `K ⊆ D` the weights agree
  have h1 : ∑ K ∈ D.powerset, wtW D p K * φ K = ∑ K ∈ D.powerset, wtW Finset.univ q K * φ K := by
    refine Finset.sum_congr rfl fun K hK => ?_
    rw [Finset.mem_powerset] at hK
    congr 1
    unfold wtW
    rw [← Finset.prod_subset (Finset.subset_univ D) (fun i _ hiD => by
      rw [if_neg (fun hiK => hiD (hK hiK)), hq0 i hiD, sub_zero])]
    exact Finset.prod_congr rfl fun i hiD => by rw [hq i hiD]
  rw [h1]
  symm
  -- a configuration not inside `D` has weight zero
  refine Finset.sum_subset (Finset.powerset_mono.2 (Finset.subset_univ D)) fun K _ hKD => ?_
  rw [Finset.mem_powerset, Finset.not_subset] at hKD
  obtain ⟨i, hiK, hiD⟩ := hKD
  have : wtW Finset.univ q K = 0 := by
    unfold wtW
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [if_pos hiK, hq0 i hiD])
  rw [this, zero_mul]

/-- The product weight of `BHK2006` on a coerced finite configuration is `wtW univ`. [folklore] -/
theorem weight_coe_eq_wtW (p : ι → ℝ) (K : Finset ι) :
    BHK2006.weight p (↑K : Set ι) = wtW Finset.univ p K := by
  unfold BHK2006.weight wtW
  exact Finset.prod_congr rfl fun i _ => by simp only [Finset.mem_coe]

/-- **Integrals under `prodBernoulli w` are `ED univ`-expectations.** [folklore] -/
theorem integral_eq_ED (w : ι → unitInterval) (φ : Set ι → ℝ) :
    ∫ ω, φ ω ∂(prodBernoulli w) = ED Finset.univ (fun i => (w i : ℝ)) (fun K => φ ↑K) := by
  rw [BHK2006.integral_prodBernoulli_eq_sum]
  unfold ED
  rw [Finset.powerset_univ]
  refine (Fintype.sum_equiv (Fintype.finsetEquivSet (α := ι)) _ _ fun K => ?_).symm
  rw [Fintype.finsetEquivSet_apply, weight_coe_eq_wtW]

/-- Set integrals under `prodBernoulli w` as `ED univ`-expectations. [folklore] -/
theorem setIntegral_eq_ED (w : ι → unitInterval) (C : Set (Set ι)) (φ : Set ι → ℝ) :
    ∫ ω in C, φ ω ∂(prodBernoulli w) = ED Finset.univ (fun i => (w i : ℝ)) (fun K => ind C ↑K * φ ↑K) := by
  rw [← integral_indicator (MeasurableSet.of_discrete), integral_eq_ED]
  unfold ED
  refine Finset.sum_congr rfl fun K _ => ?_
  dsimp only
  rw [indicator_eq_mul_ind, mul_comm (φ _)]

/-- Probabilities under `prodBernoulli w` as `ED univ`-expectations of indicators. [folklore] -/
theorem measureReal_eq_ED (w : ι → unitInterval) (C : Set (Set ι)) :
    (prodBernoulli w).real C = ED Finset.univ (fun i => (w i : ℝ)) (fun K => ind C ↑K) := by
  rw [← integral_indicator_one (MeasurableSet.of_discrete), integral_eq_ED]
  unfold ED
  refine Finset.sum_congr rfl fun K _ => ?_
  dsimp only
  rw [indicator_eq_mul_ind, Pi.one_apply, one_mul]

end Bridge

/-! ### Configurations with the pairs meeting a vertex set closed; cluster congruence -/

section Clusters

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The configuration `K` with every pair meeting the vertex set `W` CLOSED ("the world `G ∖ W`").
[cite: VandenbergHaggstromKahn2005, §1 p. 4 (the induced model on `G` minus a vertex set)] -/
def off (W : Finset V) (K : Finset (Sym2 V)) : Finset (Sym2 V) := K.filter fun e => ∀ w ∈ e, w ∉ W

/-- Membership in `off`. [folklore] -/
theorem mem_off {W : Finset V} {K : Finset (Sym2 V)} {e : Sym2 V} : e ∈ off W K ↔ e ∈ K ∧ ∀ w ∈ e, w ∉ W := by
  rw [off, Finset.mem_filter]

/-- `off ∅ = id`. [folklore] -/
@[simp] theorem off_empty (K : Finset (Sym2 V)) : off ∅ K = K := by
  ext e; simp [mem_off]

/-- `off W K ⊆ K`. [folklore] -/
theorem off_subset (W : Finset V) (K : Finset (Sym2 V)) : off W K ⊆ K := Finset.filter_subset _ _

omit [Fintype V] [DecidableEq V] in
/-- A walk from inside a set closed under the open pairs of `L` stays inside. [folklore] -/
theorem mem_of_reachable_closed {L : Finset (Sym2 V)} {W : Set V}
    (hcl : ∀ a b, a ∈ W → s(a, b) ∈ L → b ∈ W) {x z : V} (hx : x ∈ W)
    (h : (openGraph (↑L : Set (Sym2 V))).Reachable x z) : z ∈ W := by
  obtain ⟨walk⟩ := h
  induction walk with
  | nil => exact hx
  | cons hadj _ ih =>
      rw [openGraph_adj, Finset.mem_coe] at hadj
      exact ih (hcl _ _ hx hadj.1)

omit [Fintype V] [DecidableEq V] in
/-- One direction of the cluster congruence: a walk from inside `W` (closed under the open pairs of `M`) is open in any
`M'` agreeing with `M` on the pairs meeting `W`. [folklore] -/
theorem reachable_of_walk_agree {M M' : Finset (Sym2 V)} {W : Set V}
    (hcl : ∀ a b, a ∈ W → s(a, b) ∈ M → b ∈ W) (hag : ∀ e : Sym2 V, (∃ a ∈ W, a ∈ e) → (e ∈ M ↔ e ∈ M'))
    {a z : V} (q : (openGraph (↑M : Set (Sym2 V))).Walk a z) (ha : a ∈ W) :
    (openGraph (↑M' : Set (Sym2 V))).Reachable a z := by
  induction q with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons hadj _ ih =>
      rw [openGraph_adj, Finset.mem_coe] at hadj
      rename_i a b c _
      have hb : b ∈ W := hcl a b ha hadj.1
      have hadj' : (openGraph (↑M' : Set (Sym2 V))).Adj a b := by
        rw [openGraph_adj, Finset.mem_coe]
        exact ⟨(hag _ ⟨a, ha, Sym2.mem_mk_left a b⟩).1 hadj.1, hadj.2⟩
      exact hadj'.reachable.trans (ih hb)

omit [Fintype V] [DecidableEq V] in
/-- **Cluster congruence.** If `x ∈ W`, `W` is closed under the open pairs of `L`, and `L, L'` agree on every pair
meeting `W`, then `x` reaches the same vertices in `L` and `L'`. [folklore] -/
theorem reachable_congr_of_agree {L L' : Finset (Sym2 V)} {W : Set V} {x : V} (hx : x ∈ W)
    (hcl : ∀ a b, a ∈ W → s(a, b) ∈ L → b ∈ W) (hag : ∀ e : Sym2 V, (∃ a ∈ W, a ∈ e) → (e ∈ L ↔ e ∈ L'))
    (z : V) : (openGraph (↑L : Set (Sym2 V))).Reachable x z ↔ (openGraph (↑L' : Set (Sym2 V))).Reachable x z := by
  -- `W` is closed under the open pairs of `L'` as well
  have hcl' : ∀ a b, a ∈ W → s(a, b) ∈ L' → b ∈ W := fun a b ha hab =>
    hcl a b ha ((hag _ ⟨a, ha, Sym2.mem_mk_left a b⟩).2 hab)
  constructor
  · rintro ⟨q⟩; exact reachable_of_walk_agree hcl hag q hx
  · rintro ⟨q⟩; exact reachable_of_walk_agree hcl' (fun e he => (hag e he).symm) q hx

omit [Fintype V] [DecidableEq V] in
/-- **Edge-cluster congruence** under the hypotheses of `reachable_congr_of_agree`. [folklore] -/
theorem openEdgeCluster_congr_of_agree {L L' : Finset (Sym2 V)} {W : Set V} {x : V} (hx : x ∈ W)
    (hcl : ∀ a b, a ∈ W → s(a, b) ∈ L → b ∈ W) (hag : ∀ e : Sym2 V, (∃ a ∈ W, a ∈ e) → (e ∈ L ↔ e ∈ L')) :
    openEdgeCluster (↑L' : Set (Sym2 V)) x = openEdgeCluster (↑L : Set (Sym2 V)) x := by
  ext e
  rw [mem_openEdgeCluster_iff, mem_openEdgeCluster_iff, Finset.mem_coe, Finset.mem_coe]
  constructor
  · rintro ⟨heL', hd, hr⟩
    have hr' : ∀ u ∈ e, (openGraph (↑L : Set (Sym2 V))).Reachable x u := fun u hu =>
      (reachable_congr_of_agree hx hcl hag u).2 (hr u hu)
    obtain ⟨u, hu⟩ : ∃ u, u ∈ e := ⟨_, Sym2.out_fst_mem e⟩
    exact ⟨(hag e ⟨u, mem_of_reachable_closed hcl hx (hr' u hu), hu⟩).2 heL', hd, hr'⟩
  · rintro ⟨heL, hd, hr⟩
    obtain ⟨u, hu⟩ : ∃ u, u ∈ e := ⟨_, Sym2.out_fst_mem e⟩
    exact ⟨(hag e ⟨u, mem_of_reachable_closed hcl hx (hr u hu), hu⟩).1 heL, hd,
      fun u hu => (reachable_congr_of_agree hx hcl hag u).1 (hr u hu)⟩

end Clusters

/-! ### The exploration of `C_N`: closure, and what the hybrid `K →_{S_N(K)} K₂` looks like from `x` -/

section Exploration

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {D : Finset (Sym2 V)} {N : Finset V}

/-- The reached set `C_N` is closed under the open pairs of `K ∩ D`. [folklore] -/
theorem mem_reached_of_mem {K : Finset (Sym2 V)} {a b : V} (ha : a ∈ reached D N K) (he : s(a, b) ∈ K)
    (heD : s(a, b) ∈ D) : b ∈ reached D N K := by
  rw [mem_reached_iff] at ha ⊢
  obtain ⟨s, hs, hsa⟩ := ha
  by_cases hab : a = b
  · subst hab; exact ⟨s, hs, hsa⟩
  · refine ⟨s, hs, hsa.trans (SimpleGraph.Adj.reachable ?_)⟩
    rw [openGraph_adj, Finset.mem_coe, Finset.mem_inter]
    exact ⟨⟨he, heD⟩, hab⟩

/-- For `K ⊆ D`, membership in the reached set is reachability from `N` in `K`. [folklore] -/
theorem mem_reached_iff' {K : Finset (Sym2 V)} (hK : K ⊆ D) {u : V} :
    u ∈ reached D N K ↔ ∃ s ∈ N, (openGraph (↑K : Set (Sym2 V))).Reachable s u := by
  rw [mem_reached_iff, Finset.inter_eq_left.2 hK]

/-- **Inside the explored cluster nothing changes**: for `x ∈ C_N(K)` (`K, K₂ ⊆ D`) the hybrid `K →_{S_N(K)} K₂` has the
same reachability from `x` and the same edge cluster of `x` as `K`. [cite: VandenbergHaggstromKahn2005, eq. (6) (p. 4)] -/
theorem splice_congr_of_mem_reached {K K₂ : Finset (Sym2 V)} (hK : K ⊆ D) (hK₂ : K₂ ⊆ D) {x : V}
    (hx : x ∈ reached D N K) :
    (∀ z, (openGraph (↑K : Set (Sym2 V))).Reachable x z ↔
        (openGraph (↑(splice (revealedAt D N K) K K₂) : Set (Sym2 V))).Reachable x z) ∧
      openEdgeCluster (↑(splice (revealedAt D N K) K K₂) : Set (Sym2 V)) x =
        openEdgeCluster (↑K : Set (Sym2 V)) x := by
  have hcl : ∀ a b, a ∈ (↑(reached D N K) : Set V) → s(a, b) ∈ K → b ∈ (↑(reached D N K) : Set V) :=
    fun a b ha hab => Finset.mem_coe.2 (mem_reached_of_mem (Finset.mem_coe.1 ha) hab (hK hab))
  have hag : ∀ e : Sym2 V, (∃ a ∈ (↑(reached D N K) : Set V), a ∈ e) →
      (e ∈ K ↔ e ∈ splice (revealedAt D N K) K K₂) := by
    rintro e ⟨a, ha, hae⟩
    by_cases heD : e ∈ D
    · exact (splice_agree (revealedAt D N K) K K₂ e
        (mem_revealedAt_iff.2 ⟨heD, a, Finset.mem_coe.1 ha, hae⟩)).symm
    · exact ⟨fun h => absurd (hK h) heD, fun h => absurd (splice_subset hK hK₂ h) heD⟩
  exact ⟨reachable_congr_of_agree (Finset.mem_coe.2 hx) hcl hag,
    openEdgeCluster_congr_of_agree (Finset.mem_coe.2 hx) hcl hag⟩

/-- **Outside the explored cluster one sees `K₂` with the pairs meeting `C_N(K)` closed**: for `x ∉ C_N(K)`
(`K, K₂ ⊆ D`) the hybrid `K →_{S_N(K)} K₂` has, from `x`, the reachability and the edge cluster of `off (C_N K) K₂`.
[cite: VandenbergHaggstromKahn2005, eq. (6) (p. 4)] -/
theorem splice_congr_of_not_mem_reached {K K₂ : Finset (Sym2 V)} (hK : K ⊆ D) (hK₂ : K₂ ⊆ D) {x : V}
    (hx : x ∉ reached D N K) :
    (∀ z, (openGraph (↑(off (reached D N K) K₂) : Set (Sym2 V))).Reachable x z ↔
        (openGraph (↑(splice (revealedAt D N K) K K₂) : Set (Sym2 V))).Reachable x z) ∧
      openEdgeCluster (↑(splice (revealedAt D N K) K K₂) : Set (Sym2 V)) x =
        openEdgeCluster (↑(off (reached D N K) K₂) : Set (Sym2 V)) x := by
  set W := reached D N K with hW
  have hcl : ∀ a b, a ∈ ({z | z ∉ W} : Set V) → s(a, b) ∈ off W K₂ → b ∈ ({z | z ∉ W} : Set V) :=
    fun a b _ hab => (mem_off.1 hab).2 b (Sym2.mem_mk_right a b)
  have hag : ∀ e : Sym2 V, (∃ a ∈ ({z | z ∉ W} : Set V), a ∈ e) →
      (e ∈ off W K₂ ↔ e ∈ splice (revealedAt D N K) K K₂) := by
    rintro e ⟨a, ha, hae⟩
    rw [Set.mem_setOf_eq] at ha
    by_cases hout : ∀ w ∈ e, w ∉ W
    · -- no endpoint in `W`: not revealed, read in `K₂`
      have heS : e ∉ revealedAt D N K := fun h => by
        obtain ⟨-, u, hu, hue⟩ := mem_revealedAt_iff.1 h
        exact hout u hue hu
      rw [mem_off, mem_splice_of_not_mem heS]
      exact ⟨fun h => h.1, fun h => ⟨h, hout⟩⟩
    · -- an endpoint `w ∈ W` (and `a ∉ W`): closed on both sides
      push Not at hout
      obtain ⟨w, hwe, hwW⟩ := hout
      have haw : a ≠ w := fun h => ha (h ▸ hwW)
      have he : e = s(w, a) := ((Sym2.mem_and_mem_iff haw.symm).1 ⟨hwe, hae⟩)
      refine ⟨fun h => absurd ((mem_off.1 h).2 w hwe) (not_not.2 hwW), fun h => ?_⟩
      exfalso
      have heD : e ∈ D := splice_subset hK hK₂ h
      have heK : e ∈ K := (splice_agree (revealedAt D N K) K K₂ e (mem_revealedAt_iff.2 ⟨heD, w, hwW, hwe⟩)).1 h
      rw [he] at heK heD
      exact ha (mem_reached_of_mem hwW heK heD)
  exact ⟨reachable_congr_of_agree (show x ∈ ({z | z ∉ W} : Set V) from hx) hcl hag,
    openEdgeCluster_congr_of_agree (show x ∈ ({z | z ∉ W} : Set V) from hx) hcl hag⟩

end Exploration

/-! ### The functionals -/

section Functionals

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `Ψ(C_x)` as a function of the finite configuration (`C_x` = BHK's open EDGE cluster of `x`).
[cite: VandenbergHaggstromKahn2005, §1 p. 3 (C_s)] -/
def fcl (Ψ : Set (Sym2 V) → ℝ) (x : V) (K : Finset (Sym2 V)) : ℝ := Ψ (openEdgeCluster (↑K : Set (Sym2 V)) x)

/-- The indicator of `{v ↔ N}` (some vertex of `N` is joined to `v`) on finite configurations. [folklore] -/
def nr (N : Finset V) (v : V) (K : Finset (Sym2 V)) : ℝ :=
  ind {L : Finset (Sym2 V) | ∃ s ∈ N, (openGraph (↑L : Set (Sym2 V))).Reachable s v} K

variable (Ψ : Set (Sym2 V) → ℝ) (x v : V) (N : Finset V)

omit [Fintype V] [DecidableEq V] in
/-- `fcl` is monotone for monotone `Ψ`. [folklore] -/
theorem fcl_mono (hΨ : Monotone Ψ) : Monotone (fcl Ψ x) := fun _ _ h =>
  hΨ (BHK2006.openEdgeCluster_mono (Finset.coe_subset.2 h) x)

omit [Fintype V] [DecidableEq V] in
/-- `nr` only takes the values `0, 1`; here: `0 ≤ nr ≤ 1`. [folklore] -/
theorem nr_nonneg_le_one (K : Finset (Sym2 V)) : 0 ≤ nr N v K ∧ nr N v K ≤ 1 :=
  ⟨ind_nonneg _ _, BHK2006.ind_le_one _ _⟩

end Functionals

end CovTauStarN

end Percolation.Continuity

end
