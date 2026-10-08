import Percolation.Continuity.CovTau.StarNReal
import Percolation.Util.Linter

/-!
# Lemma (★^H), part 1 — functionals, BHK 1.4 with a vertex SET, Markov bookkeeping (the one-source bound of the COV(τ) proof with the owner replaced by a finite SET `S ∋ x`)

The proof of (S5)_r for every r runs the A2 / T_A induction of the COV(τ) proof with the functional
`H_Γ(v) = Cov_Γ(Ψ(C_x), 1{v ↔ S})` for a finite set `S ∋ x` (`S = {x} ∪ decoys`) in place of
`Cov_Γ(Ψ(C_x), 1{v ↔ x})`. Its one-source input is Lemma (★^H): for a source set `N`, `θ = μ(v ↮ N |
v ↮ S)`, `Y^H(N) := E[ H_{G∖C_N}(v) ; x ∉ C_N ] ≤ θ · H_G(v)`, i.e. `Y^H(N)·P(v ↮ S) ≤ P(v ↮ S, v ↮
N)·H_G(v)`, and its corollary `Y^H(N) ≤ H_G(v)` (decision-tree Harris alone). The companion file
`Continuity/CovTau/StarH.lean` proves both in the finitary `ED` form of
`Continuity/CovTau/StarNReal.lean`; THIS FILE has the functionals `covH`, `yH`, the set form of BHK
1.4 (`bhk14S_ED`) and the Markov bookkeeping of the hybrid (`starH_markov`). Proof: law of total
covariance along the exploration `ℱ_N` of `C_N` (`SetClusterExploration`; on `{x ∈ C_N}` the owner's
functional is decided, on `{x ∉ C_N, v ∈ C_N}` the indicator `1{v ↔ S}` is decided, on `{x, v ∉
C_N}` the hybrid is the world `G ∖ C_N`), the decision-tree Harris inequality for `E[Ψ(C_x) | ℱ_N]`
and the increasing event `{v ↔ S ∪ N}` (`TreeHarris.treeHarris_real`, [Gladkov2024, Thm. 3.2]), and
van den Berg–Häggström–Kahn's Theorem 1.4 with the vertex SET `S`
(`BHK2006_twoSetConditionalAssociation.negCorrelation`: given `S ↮ v`, `Ψ(C_x)` (↑ in `C_S`) and
`1{v ↔ N}` (↑ in `C_v`) are negatively correlated; finitary form `bhk14S_ED`). [cite: Gladkov2024,
Thm. 3.2 (p. 4)] [cite: VandenbergHaggstromKahn2005, Thm. 1.4 (p. 7) with Remark 1 (p. 5), eq. (6)
(p. 4)]
-/

noncomputable section

namespace Percolation.Continuity

namespace CovTauStarN

open Finset MeasureTheory Percolation.Literature Percolation.Literature.DecisionTree
open Percolation.Literature.LatticeModels (prodBernoulli)
open SetClusterExploration TreeHarris
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### The functionals with the set `S` -/

/-- **`H(W) = Cov_{G∖W}(Ψ(C_x), 1{v ↔ S})`** on the coordinates `D` (world `G ∖ W` = `off W`). [cite: VandenbergHaggstromKahn2005, Thm. 1.5 eq. (9) (p. 7)] -/
def covH (D : Finset (Sym2 V)) (p : Sym2 V → ℝ) (Ψ : Set (Sym2 V) → ℝ) (x : V) (S : Finset V) (v : V) (W : Finset V) : ℝ :=
  ED D p (fun K => fcl Ψ x (off W K) * nr S v (off W K)) -
    ED D p (fun K => fcl Ψ x (off W K)) * ED D p (fun K => nr S v (off W K))

/-- **`Y^H(N) = E[ H(V(C_N)) ; x ∉ C_N ]`**. [cite: VandenbergHaggstromKahn2005, eq. (6) (p. 4)] -/
def yH (D : Finset (Sym2 V)) (p : Sym2 V → ℝ) (Ψ : Set (Sym2 V) → ℝ) (x : V) (S : Finset V) (v : V) (N : Finset V) : ℝ :=
  ED D p (fun K => ind {L : Finset (Sym2 V) | x ∉ reached D N L} K * covH D p Ψ x S v (reached D N K))

/-! ### BHK's Theorem 1.4 with the vertex set `S`, finitary -/

omit [Fintype V] [DecidableEq V] in
/-- Walk induction for `reachable_openEdgeCluster_self`. [folklore] -/
theorem reachable_openEdgeCluster_aux {ω : Set (Sym2 V)} {x a u : V} (q : (openGraph ω).Walk a u)
    (hxa : (openGraph ω).Reachable x a) (hxa' : (openGraph (openEdgeCluster ω x)).Reachable x a) :
    (openGraph (openEdgeCluster ω x)).Reachable x u := by
  induction q with
  | nil => exact hxa'
  | cons hadj _ ih =>
      rename_i a b c _
      have hadj2 := hadj
      rw [openGraph_adj] at hadj2
      have hxb : (openGraph ω).Reachable x b := hxa.trans hadj.reachable
      have he : s(a, b) ∈ openEdgeCluster ω x := by
        rw [mem_openEdgeCluster_iff]
        refine ⟨hadj2.1, by rw [Sym2.mk_isDiag_iff]; exact hadj2.2, fun t ht => ?_⟩
        rcases Sym2.mem_iff.1 ht with rfl | rfl
        · exact hxa
        · exact hxb
      have hadj' : (openGraph (openEdgeCluster ω x)).Adj a b := by
        rw [openGraph_adj]; exact ⟨he, hadj2.2⟩
      exact ih hxb (hxa'.trans hadj'.reachable)

omit [Fintype V] [DecidableEq V] in
/-- An `ω`-open path from `x` is open in the edge cluster `C_x` itself. [folklore] -/
theorem reachable_openEdgeCluster_self {ω : Set (Sym2 V)} {x u : V} (h : (openGraph ω).Reachable x u) :
    (openGraph (openEdgeCluster ω x)).Reachable x u := by
  obtain ⟨q⟩ := h
  exact reachable_openEdgeCluster_aux q (SimpleGraph.Reachable.refl _) (SimpleGraph.Reachable.refl _)

omit [Fintype V] [DecidableEq V] in
/-- For `x ∈ S`, the cluster of `x` read inside BHK's `C_S = ⋃_{s∈S} C_s` is `C_x`. [cite: VandenbergHaggstromKahn2005, §2 p. 9 (C_S)] -/
theorem openEdgeCluster_biUnion_eq {ω : Set (Sym2 V)} {S : Set V} {x : V} (hx : x ∈ S) :
    openEdgeCluster (⋃ s ∈ S, openEdgeCluster ω s) x = openEdgeCluster ω x := by
  have hsub : (⋃ s ∈ S, openEdgeCluster ω s) ⊆ ω := Set.iUnion₂_subset fun s _ => openEdgeCluster_subset ω s
  refine Set.Subset.antisymm (BHK2006.openEdgeCluster_mono hsub x) fun e he => ?_
  rw [mem_openEdgeCluster_iff] at he ⊢
  refine ⟨Set.mem_iUnion₂.2 ⟨x, hx, (mem_openEdgeCluster_iff ω x e).2 he⟩, he.2.1, fun u hu => ?_⟩
  exact (reachable_openEdgeCluster_self (he.2.2 u hu)).mono
    (openGraph_mono (Set.subset_iUnion₂ (s := fun s _ => openEdgeCluster ω s) x hx))

/-- **BHK Theorem 1.4 with the vertex set `S` (`x ∈ S`), finitary, on the coordinates `D`**: given `S ↮ v`, `Ψ(C_x)` and `1{v ↔ N}`
are negatively correlated: `P(v↮S)·E[Ψ(C_x) 1{v↔N}; v↮S] ≤ E[1{v↔N}; v↮S]·E[Ψ(C_x); v↮S]`.
[cite: VandenbergHaggstromKahn2005, Thm. 1.4 (p. 7) with Remark 1 after Thm. 1.2 (p. 5)] -/
theorem bhk14S_ED (D : Finset (Sym2 V)) {p : Sym2 V → ℝ} (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    (N : Finset V) (x v : V) (S : Finset V) (hxS : x ∈ S) (Ψ : Set (Sym2 V) → ℝ) (hΨ : Monotone Ψ) :
    ED D p (fun K => 1 - nr S v K) * ED D p (fun K => fcl Ψ x K * ((1 - nr S v K) * nr N v K)) ≤
      ED D p (fun K => (1 - nr S v K) * nr N v K) * ED D p (fun K => fcl Ψ x K * (1 - nr S v K)) := by
  set w : Sym2 V → unitInterval := fun e => if e ∈ D then ⟨max 0 (min 1 (p e)), by
    exact ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩⟩ else 0 with hw
  have hwD : ∀ e ∈ D, ((w e : unitInterval) : ℝ) = p e := fun e he => by
    simp only [hw, if_pos he]
    rw [min_eq_right (hp1 e), max_eq_right (hp0 e)]
  have hwD' : ∀ e ∉ D, ((w e : unitInterval) : ℝ) = 0 := fun e he => by simp only [hw, if_neg he]; rfl
  have hED : ∀ φ : Finset (Sym2 V) → ℝ, ED Finset.univ (fun e => (w e : ℝ)) φ = ED D p φ :=
    fun φ => ED_univ_eq_ED_of_zero D p _ hwD hwD' φ
  -- the increasing test functions of `C_S` and of `C_v`
  set F : Set (Sym2 V) → ℝ := fun C => Ψ (openEdgeCluster C x) with hF
  have hFmono : Monotone F := fun C C' h => hΨ (BHK2006.openEdgeCluster_mono h x)
  set G : Set (Sym2 V) → ℝ := fun C => if (v ∈ N ∨ ∃ e ∈ C, ∃ s ∈ N, s ∈ e) then 1 else 0 with hG
  have hGmono : Monotone G := by
    intro C C' hCC'
    simp only [hG]
    by_cases h : v ∈ N ∨ ∃ e ∈ C, ∃ s ∈ N, s ∈ e
    · rw [if_pos h, if_pos (h.imp id (fun ⟨e, he, hs⟩ => ⟨e, hCC' he, hs⟩))]
    · rw [if_neg h]; split_ifs <;> norm_num
  have key := BHK2006_twoSetConditionalAssociation.negCorrelation w (↑S : Set V) {v} F G hFmono hGmono
  set D0 : Set (Set (Sym2 V)) := {ω | ∀ s ∈ (↑S : Set V), ∀ t ∈ ({v} : Set V), ¬ (openGraph ω).Reachable s t} with hD0
  have hind : ∀ K : Finset (Sym2 V), ind D0 (↑K : Set (Sym2 V)) = 1 - nr S v K := by
    intro K
    unfold nr
    by_cases h : ∃ s ∈ S, (openGraph (↑K : Set (Sym2 V))).Reachable s v
    · rw [ind_of_mem (show K ∈ {L : Finset (Sym2 V) | ∃ s ∈ S, (openGraph (↑L : Set (Sym2 V))).Reachable s v} from h),
        ind_of_not_mem (show (↑K : Set (Sym2 V)) ∉ D0 from fun hK => by
          obtain ⟨s, hs, hsv⟩ := h; exact hK s (Finset.mem_coe.2 hs) v rfl hsv)]
      ring
    · rw [ind_of_not_mem (show K ∉ {L : Finset (Sym2 V) | ∃ s ∈ S, (openGraph (↑L : Set (Sym2 V))).Reachable s v} from h),
        ind_of_mem (show (↑K : Set (Sym2 V)) ∈ D0 from fun s hs t ht => by
          rw [Set.mem_singleton_iff] at ht; rw [ht]; exact fun hr => h ⟨s, Finset.mem_coe.1 hs, hr⟩)]
      ring
  simp only [Set.biUnion_singleton] at key
  rw [measureReal_eq_ED, setIntegral_eq_ED, setIntegral_eq_ED, setIntegral_eq_ED, hED, hED, hED, hED] at key
  have e1 : ED D p (fun K => ind D0 (↑K : Set (Sym2 V))) = ED D p (fun K => 1 - nr S v K) :=
    ED_congr_on D p fun K _ => hind K
  have hFx : ∀ K : Finset (Sym2 V), F (⋃ s ∈ (↑S : Set V), openEdgeCluster (↑K : Set (Sym2 V)) s) = fcl Ψ x K := fun K => by
    simp only [hF, fcl, openEdgeCluster_biUnion_eq (Finset.mem_coe.2 hxS)]
  have hGx : ∀ K : Finset (Sym2 V), G (openEdgeCluster (↑K : Set (Sym2 V)) v) = nr N v K := fun K => by
    simp only [hG, nr_eq_ite N v K]
  have e2 : ED D p (fun K => ind D0 (↑K : Set (Sym2 V)) *
      (F (⋃ s ∈ (↑S : Set V), openEdgeCluster (↑K : Set (Sym2 V)) s) * G (openEdgeCluster (↑K : Set (Sym2 V)) v))) =
      ED D p (fun K => fcl Ψ x K * ((1 - nr S v K) * nr N v K)) :=
    ED_congr_on D p fun K _ => by rw [hind, hFx, hGx]; ring
  have e3 : ED D p (fun K => ind D0 (↑K : Set (Sym2 V)) * F (⋃ s ∈ (↑S : Set V), openEdgeCluster (↑K : Set (Sym2 V)) s)) =
      ED D p (fun K => fcl Ψ x K * (1 - nr S v K)) :=
    ED_congr_on D p fun K _ => by rw [hind, hFx]; ring
  have e4 : ED D p (fun K => ind D0 (↑K : Set (Sym2 V)) * G (openEdgeCluster (↑K : Set (Sym2 V)) v)) =
      ED D p (fun K => (1 - nr S v K) * nr N v K) :=
    ED_congr_on D p fun K _ => by rw [hind, hGx]
  rw [e1, e2, e3, e4] at key
  linarith

/-! ### Lemma (★^H) -/

omit [Fintype V] in
/-- `nr S v + (1 − nr S v)·nr N v = nr (S ∪ N) v`. [folklore] -/
theorem nr_union_eq (S N : Finset V) (v : V) (K : Finset (Sym2 V)) :
    nr (S ∪ N) v K = nr S v K + (1 - nr S v K) * nr N v K := by
  unfold nr
  by_cases h1 : ∃ s ∈ S, (openGraph (↑K : Set (Sym2 V))).Reachable s v
  · rw [ind_of_mem (show K ∈ {L : Finset (Sym2 V) | ∃ s ∈ S, (openGraph (↑L : Set (Sym2 V))).Reachable s v} from h1),
      ind_of_mem (show K ∈ {L : Finset (Sym2 V) | ∃ s ∈ S ∪ N, (openGraph (↑L : Set (Sym2 V))).Reachable s v} from by
        obtain ⟨s, hs, h⟩ := h1; exact ⟨s, Finset.mem_union_left _ hs, h⟩)]
    ring
  · rw [ind_of_not_mem (show K ∉ {L : Finset (Sym2 V) | ∃ s ∈ S, (openGraph (↑L : Set (Sym2 V))).Reachable s v} from h1)]
    by_cases h2 : ∃ s ∈ N, (openGraph (↑K : Set (Sym2 V))).Reachable s v
    · rw [ind_of_mem (show K ∈ {L : Finset (Sym2 V) | ∃ s ∈ N, (openGraph (↑L : Set (Sym2 V))).Reachable s v} from h2),
        ind_of_mem (show K ∈ {L : Finset (Sym2 V) | ∃ s ∈ S ∪ N, (openGraph (↑L : Set (Sym2 V))).Reachable s v} from by
          obtain ⟨s, hs, h⟩ := h2; exact ⟨s, Finset.mem_union_right _ hs, h⟩)]
      ring
    · rw [ind_of_not_mem (show K ∉ {L : Finset (Sym2 V) | ∃ s ∈ N, (openGraph (↑L : Set (Sym2 V))).Reachable s v} from h2),
        ind_of_not_mem (show K ∉ {L : Finset (Sym2 V) | ∃ s ∈ S ∪ N, (openGraph (↑L : Set (Sym2 V))).Reachable s v} from by
          rintro ⟨s, hs, h⟩
          rcases Finset.mem_union.1 hs with hs | hs
          · exact h1 ⟨s, hs, h⟩
          · exact h2 ⟨s, hs, h⟩)]
      ring

/-- In the world `off W K₂`, a root inside `W` reaches nothing else. [folklore] -/
theorem not_reachable_off_of_mem {W : Finset V} {K₂ : Finset (Sym2 V)} {s u : V} (hs : s ∈ W) (hsu : s ≠ u) :
    ¬ (openGraph (↑(off W K₂) : Set (Sym2 V))).Reachable s u := by
  rintro ⟨q⟩
  cases q with
  | nil => exact hsu rfl
  | cons hadj _ =>
      rw [openGraph_adj, Finset.mem_coe] at hadj
      exact (mem_off.1 hadj.1).2 s (Sym2.mem_mk_left _ _) hs

/-- For `K ⊆ D`: nothing outside `C_N(K)` is reached (in `K`) from inside `C_N(K)`. [folklore] -/
theorem not_reachable_of_mem_reached {D : Finset (Sym2 V)} {N : Finset V} {K : Finset (Sym2 V)} (hK : K ⊆ D) {s u : V}
    (hs : s ∈ reached D N K) (hu : u ∉ reached D N K) : ¬ (openGraph (↑K : Set (Sym2 V))).Reachable s u := fun h =>
  hu (mem_of_reachable_closed (W := (↑(reached D N K) : Set V))
    (fun _ _ ha hab => Finset.mem_coe.2 (mem_reached_of_mem (Finset.mem_coe.1 ha) hab (hK hab))) (Finset.mem_coe.2 hs) h)

section Main

variable (D : Finset (Sym2 V)) {p : Sym2 V → ℝ} (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
variable (N : Finset V) (x v : V) (S : Finset V) (hvS : v ∉ S) (Ψ : Set (Sym2 V) → ℝ)
include hvS

/-- MARKOV BOOKKEEPING for (★^H): along the exploration of `C_N(K)` (`K ⊆ D`), for every `K₂ ⊆ D`, the hybrid `K →_{S_N(K)} K₂` has
(i) for `x ∈ C_N`: the owner's functional of `K`; (ii) for `x ∉ C_N`: the owner's functional of the world `off (C_N) K₂`;
(iii) for `v ∈ C_N`: the indicator `1{v ↔ S}` of `K`; (iv) for `v ∉ C_N`: the indicator `1{v ↔ S}` of the world; and for `v ∈ C_N` the
world indicator vanishes. [cite: VandenbergHaggstromKahn2005, eq. (6) (p. 4)] -/
theorem starH_markov {K K₂ : Finset (Sym2 V)} (hK : K ⊆ D) (hK₂ : K₂ ⊆ D) :
    (x ∈ reached D N K → fcl Ψ x (splice (revealedAt D N K) K K₂) = fcl Ψ x K) ∧
    (x ∉ reached D N K → fcl Ψ x (splice (revealedAt D N K) K K₂) = fcl Ψ x (off (reached D N K) K₂)) ∧
    (v ∈ reached D N K → nr S v (splice (revealedAt D N K) K K₂) = nr S v K) ∧
    (v ∉ reached D N K → nr S v (splice (revealedAt D N K) K K₂) = nr S v (off (reached D N K) K₂)) ∧
    (v ∈ reached D N K → nr S v (off (reached D N K) K₂) = 0) := by
  have hcl_off : ∀ a b, a ∈ ({z | z ∉ reached D N K} : Set V) → s(a, b) ∈ off (reached D N K) K₂ →
      b ∈ ({z | z ∉ reached D N K} : Set V) :=
    fun _ b _ hab => (mem_off.1 hab).2 b (Sym2.mem_mk_right _ b)
  refine ⟨fun hx => ?_, fun hx => ?_, fun hv => ?_, fun hv => ?_, fun hv => ?_⟩
  · simp only [fcl, (splice_congr_of_mem_reached hK hK₂ hx).2]
  · simp only [fcl, (splice_congr_of_not_mem_reached hK hK₂ hx).2]
  · refine BystanderBHK.ind_congr ?_
    show (∃ s ∈ S, _) ↔ (∃ s ∈ S, _)
    refine exists_congr fun s => and_congr_right fun hs => ?_
    by_cases hsW : s ∈ reached D N K
    · exact ((splice_congr_of_mem_reached hK hK₂ hsW).1 v).symm
    · constructor
      · intro h
        have h' := ((splice_congr_of_not_mem_reached hK hK₂ hsW).1 v).2 h
        exact absurd hv (mem_of_reachable_closed hcl_off (show s ∈ ({z | z ∉ reached D N K} : Set V) from hsW) h')
      · intro h
        exact absurd (not_reachable_of_mem_reached hK hv hsW) (not_not.2 h.symm)
  · refine BystanderBHK.ind_congr ?_
    show (∃ s ∈ S, _) ↔ (∃ s ∈ S, _)
    refine exists_congr fun s => and_congr_right fun hs => ?_
    by_cases hsW : s ∈ reached D N K
    · have hsv : s ≠ v := fun h => hvS (h ▸ hs)
      constructor
      · intro h
        exact absurd (((splice_congr_of_mem_reached hK hK₂ hsW).1 v).2 h) (not_reachable_of_mem_reached hK hsW hv)
      · intro h; exact absurd h (not_reachable_off_of_mem hsW hsv)
    · exact ((splice_congr_of_not_mem_reached hK hK₂ hsW).1 v).symm
  · refine ind_of_not_mem ?_
    rintro ⟨s, hs, hr⟩
    have hsv : s ≠ v := fun h => hvS (h ▸ hs)
    by_cases hsW : s ∈ reached D N K
    · exact not_reachable_off_of_mem hsW hsv hr
    · exact absurd hv (mem_of_reachable_closed hcl_off (show s ∈ ({z | z ∉ reached D N K} : Set V) from hsW) hr)

end Main

end CovTauStarN

end Percolation.Continuity

end
