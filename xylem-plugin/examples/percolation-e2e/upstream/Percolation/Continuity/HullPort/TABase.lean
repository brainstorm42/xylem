import Percolation.Continuity.HullPort.TASections
import Percolation.Continuity.HullPort.TAStep
import Percolation.Util.Linter

/-!
# Marker dominance with an avoided set: base case and degenerate cases for `T_A`

Part 4 of the proof of `T_A ≥ 0`, set-`X` form:
* `HullPort.tab_insert_eq` — `b_{X∪{v}} = b_X − a^{(v)}_X`;
* `HullPort.tab_pos` — `b_X > 0` when `y ∉ X ∪ {s}` and all weights are `< 1`;
* `HullPort.taC_eq_zero_of_mem` (and consequences) — if `y ∈ X` then `c ≡ 0`, so `A = B = a = b = 0`;
* `HullPort.taQ_eq_zero_of_noBoundary` — the BASE CASE: if no pair of positive weight joins `X` to `V ∖ X`, then
  `Q = A·b − a·B = 0` (the cluster of `X` is `X`, the cut set is constant, and `r_K = a/b`).
[cite: VandenbergHaggstromKahn2005, §1 pp. 3–5 (bookkeeping in the induced model)]
-/

noncomputable section

namespace Percolation.Continuity

open MeasureTheory Set Percolation.Literature.LatticeModels Percolation.Literature
open scoped Classical

variable {V : Type*}

namespace HullPort

open LonePortSum LonePortSumGeneral BHK2006 DecisionTree KNPreFKG

section TA

variable [Fintype V]

/-- `b_{X ∪ {v}} = b_X − a^{(v)}_X`: `μ(y ↮ s, X, v) = μ(y ↮ s, X) − μ(y ↮ s, X; y ↔ v)`. [folklore] -/
theorem tab_insert_eq (w : Sym2 V → ℝ) (s y v : V) (X : Set V) :
    tab w s y (insert v X) = tab w s y X - taa w s y v X := by
  simp only [tab, taa, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [avoidEv_insert_insert_eq, ind_inter_compl, ind_inter]
  ring

omit [Fintype V] in
/-- In the empty configuration only trivial connections exist. [folklore] -/
theorem reachable_empty_iff (a b : V) : (openGraph (∅ : Set (Sym2 V))).Reachable a b ↔ a = b := by
  constructor
  · intro h
    rw [SimpleGraph.reachable_iff_reflTransGen] at h
    induction h with
    | refl => rfl
    | tail _ hbc ih =>
      obtain ⟨hmem, _⟩ := (openGraph_adj _ _ _).1 hbc
      exact absurd hmem (Set.notMem_empty _)
  · rintro rfl; exact SimpleGraph.Reachable.refl _

/-- The weight of the empty configuration is positive when all weights are `< 1`. [folklore] -/
theorem weight_empty_pos (w : Sym2 V → ℝ) (hw : ∀ e, w e < 1) : 0 < weight w (∅ : Set (Sym2 V)) := by
  unfold weight
  refine Finset.prod_pos fun e _ => ?_
  split_ifs with h
  · exact absurd h (Set.notMem_empty e)
  · linarith [hw e]

/-- `b_X > 0` when `y ∉ X ∪ {s}` and all weights are `< 1` (the empty configuration contributes). [folklore] -/
theorem tab_pos (w : Sym2 V → ℝ) (hw0 : ∀ e, 0 ≤ w e) (hw : ∀ e, w e < 1) (s y : V) (X : Set V)
    (hy : y ∉ insert s X) : 0 < tab w s y X := by
  have hw1 : ∀ e, w e ≤ 1 := fun e => (hw e).le
  have hmem : (∅ : Set (Sym2 V)) ∈ avoidEv y (insert s X) := by
    intro t ht h
    rw [reachable_empty_iff] at h
    exact hy (h ▸ ht)
  calc 0 < weight w (∅ : Set (Sym2 V)) * ind (avoidEv y (insert s X)) ∅ := by
        rw [ind_of_mem hmem, mul_one]; exact weight_empty_pos w hw
    _ ≤ tab w s y X :=
        Finset.single_le_sum (f := fun ω => weight w ω * ind (avoidEv y (insert s X)) ω)
          (fun ω _ => mul_nonneg (weight_nonneg hw0 hw1 ω) (ind_nonneg _ _)) (Finset.mem_univ _)

omit [Fintype V] in
/-- A vertex all of whose pairs are absent is joined only to itself. [folklore] -/
theorem eq_of_reachable_of_isolated {ζ : Set (Sym2 V)} {y : V} (hy : ∀ e ∈ ζ, y ∉ e) (a : V)
    (h : (openGraph ζ).Reachable y a) : a = y := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => rfl
  | @tail b c _ hbc ih =>
    subst ih
    obtain ⟨hmem, _⟩ := (openGraph_adj _ _ c).1 hbc
    exact absurd (Sym2.mem_mk_left _ c) (hy _ hmem)

omit [Fintype V] in
/-- Every pair at a vertex of `X` lies in the cut set of `X`. [folklore] -/
theorem mem_cut_of_mem {X : Set V} {y : V} (hy : y ∈ X) {e : Sym2 V} (hye : y ∈ e) (ω : Set (Sym2 V)) :
    e ∈ cut X ω := ⟨y, hye, y, hy, SimpleGraph.Reachable.refl _⟩

/-- If `y ∈ X` then `c ≡ 0` (in `G − cut_X`, `y` is isolated, so `{s ↔ y}` is impossible for `s ≠ y`). [folklore] -/
theorem taC_eq_zero_of_mem (w : Sym2 V → ℝ) (s y : V) (hsy : s ≠ y) (X : Set V) (hy : y ∈ X)
    (g : Set (Sym2 V) → ℝ) (ω : Set (Sym2 V)) : taC w s y X g ω = 0 := by
  have hY : ∀ η : Set (Sym2 V), ind (openConn s y : Set (BondConfig V)) (η \ cut X ω) = 0 := by
    intro η
    refine ind_of_not_mem fun h => hsy ?_
    have hiso : ∀ e ∈ η \ cut X ω, y ∉ e := fun e he hye => he.2 (mem_cut_of_mem hy hye ω)
    exact (eq_of_reachable_of_isolated hiso s ((h : (openGraph _).Reachable s y).symm))
  simp only [taC, delE, hY, mul_zero, Finset.sum_const_zero, sub_zero]

/-- If `y ∈ X` then `B = 0`. [folklore] -/
theorem taB_eq_zero_of_mem (w : Sym2 V → ℝ) (s y : V) (hsy : s ≠ y) (X : Set V) (hy : y ∈ X)
    (g : Set (Sym2 V) → ℝ) : taB w s y X g = 0 :=
  Finset.sum_eq_zero fun ω _ => by rw [taC_eq_zero_of_mem w s y hsy X hy g ω]; ring

/-- If `y ∈ X` then `A = 0`. [folklore] -/
theorem taA_eq_zero_of_mem (w : Sym2 V → ℝ) (s y z : V) (hsy : s ≠ y) (X : Set V) (hy : y ∈ X)
    (g : Set (Sym2 V) → ℝ) : taA w s y z X g = 0 :=
  Finset.sum_eq_zero fun ω _ => by rw [taC_eq_zero_of_mem w s y hsy X hy g ω]; ring

/-- If `y ∈ X ∪ {s}` then `b = 0`. [folklore] -/
theorem tab_eq_zero_of_mem (w : Sym2 V → ℝ) (s y : V) (X : Set V) (hy : y ∈ insert s X) : tab w s y X = 0 :=
  Finset.sum_eq_zero fun ω _ => by
    rw [ind_of_not_mem fun h => (h : ∀ t ∈ insert s X, ¬ (openGraph ω).Reachable y t) y hy
      (SimpleGraph.Reachable.refl _), mul_zero]

/-- If `y ∈ X ∪ {s}` then `a = 0`. [folklore] -/
theorem taa_eq_zero_of_mem (w : Sym2 V → ℝ) (s y z : V) (X : Set V) (hy : y ∈ insert s X) :
    taa w s y z X = 0 :=
  Finset.sum_eq_zero fun ω _ => by
    rw [ind_of_not_mem fun h => (h.1 : ∀ t ∈ insert s X, ¬ (openGraph ω).Reachable y t) y hy
      (SimpleGraph.Reachable.refl _), mul_zero]

/-- If `s ∈ X` then `B = 0` (`{s ↮ X}` is empty). [folklore] -/
theorem taB_eq_zero_of_root_mem (w : Sym2 V → ℝ) (s y : V) (X : Set V) (hs : s ∈ X) (g : Set (Sym2 V) → ℝ) :
    taB w s y X g = 0 :=
  Finset.sum_eq_zero fun ω _ => by
    rw [ind_of_not_mem fun h => (h : ∀ t ∈ X, ¬ (openGraph ω).Reachable s t) s hs (SimpleGraph.Reachable.refl _)]
    ring

/-- If `s ∈ X` then `A = 0`. [folklore] -/
theorem taA_eq_zero_of_root_mem (w : Sym2 V → ℝ) (s y z : V) (X : Set V) (hs : s ∈ X)
    (g : Set (Sym2 V) → ℝ) : taA w s y z X g = 0 :=
  Finset.sum_eq_zero fun ω _ => by
    rw [ind_of_not_mem fun h => (h : ∀ t ∈ X, ¬ (openGraph ω).Reachable s t) s hs (SimpleGraph.Reachable.refl _)]
    ring

/-! ### The base case: no pair of positive weight joins `X` to its complement -/

omit [Fintype V] in
/-- In a configuration with no open pair joining `X` to its complement, open paths do not leave `X`. [folklore] -/
theorem mem_of_reachable_of_noBoundary {X : Set V} {ζ : Set (Sym2 V)}
    (hζ : ∀ e ∈ ζ, ¬ e.IsDiag → ∀ a ∈ e, ∀ b ∈ e, a ∈ X → b ∈ X) {x u : V} (hx : x ∈ X)
    (h : (openGraph ζ).Reachable x u) : u ∈ X := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact hx
  | @tail b c _ hbc ih =>
    obtain ⟨hmem, hne⟩ := (openGraph_adj _ b c).1 hbc
    exact hζ _ hmem (fun hd => hne (Sym2.mk_isDiag_iff.1 hd)) b (Sym2.mem_mk_left b c) c
      (Sym2.mem_mk_right b c) ih

omit [Fintype V] in
/-- … nor enter `X`. [folklore] -/
theorem not_mem_of_reachable_of_noBoundary {X : Set V} {ζ : Set (Sym2 V)}
    (hζ : ∀ e ∈ ζ, ¬ e.IsDiag → ∀ a ∈ e, ∀ b ∈ e, a ∈ X → b ∈ X) {x u : V} (hu : u ∉ X)
    (h : (openGraph ζ).Reachable u x) : x ∉ X := fun hx =>
  hu (mem_of_reachable_of_noBoundary hζ hx h.symm)

omit [Fintype V] in
/-- With no open boundary pair, the cut set of `X` is the set of pairs meeting `X`. [folklore] -/
theorem cut_eq_of_noBoundary {X : Set V} {ζ : Set (Sym2 V)}
    (hζ : ∀ e ∈ ζ, ¬ e.IsDiag → ∀ a ∈ e, ∀ b ∈ e, a ∈ X → b ∈ X) :
    cut X ζ = {e | ∃ u ∈ e, u ∈ X} := by
  ext e
  constructor
  · rintro ⟨u, hu, x, hx, hxu⟩
    exact ⟨u, hu, mem_of_reachable_of_noBoundary hζ hx hxu⟩
  · rintro ⟨u, hu, huX⟩
    exact ⟨u, hu, u, huX, SimpleGraph.Reachable.refl _⟩

omit [Fintype V] in
/-- With no open boundary pair, deleting the pairs meeting `X` does not change connections outside `X`. [folklore] -/
theorem reachable_sdiff_iff_of_noBoundary {X : Set V} {ζ : Set (Sym2 V)}
    (hζ : ∀ e ∈ ζ, ¬ e.IsDiag → ∀ a ∈ e, ∀ b ∈ e, a ∈ X → b ∈ X) {a : V} (ha : a ∉ X) (b : V) :
    (openGraph (ζ \ {e | ∃ u ∈ e, u ∈ X})).Reachable a b ↔ (openGraph ζ).Reachable a b := by
  refine ⟨fun h => h.mono (openGraph_le Set.sdiff_subset), fun h => ?_⟩
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact SimpleGraph.Reachable.refl _
  | @tail b c hab hbc ih =>
    obtain ⟨hmem, hne⟩ := (openGraph_adj _ b c).1 hbc
    have hb : b ∉ X := not_mem_of_reachable_of_noBoundary hζ ha
      ((SimpleGraph.reachable_iff_reflTransGen a b).2 hab)
    have hc : c ∉ X := fun hc => hb (hζ _ hmem (fun hd => hne (Sym2.mk_isDiag_iff.1 hd)) c
      (Sym2.mem_mk_right b c) b (Sym2.mem_mk_left b c) hc)
    refine ih.trans (SimpleGraph.Adj.reachable ((openGraph_adj _ b c).2 ⟨⟨hmem, ?_⟩, hne⟩))
    rintro ⟨u, hu, huX⟩
    rcases Sym2.mem_iff.1 hu with rfl | rfl
    · exact hb huX
    · exact hc huX

/-- Removing the pairs of weight `0` from the configuration does not change any expectation. [folklore] -/
theorem sum_weight_eq_sum_sdiff_zeros (w : Sym2 V → ℝ) (F : Set (Sym2 V) → ℝ) :
    ∑ η, weight w η * F η = ∑ η, weight w η * F (η \ {e | w e = 0}) := by
  rw [sum_weight_mul_comp_sdiff w {e | w e = 0} F]
  refine Finset.sum_congr rfl fun η _ => ?_
  congr 2
  funext e
  by_cases he : w e = 0
  · rw [if_pos (show e ∈ {e | w e = 0} from he), he]
  · rw [if_neg (show e ∉ {e | w e = 0} from he)]

/-- **Base case of the induction** (set form): if every non-loop pair joining `X` to `V ∖ X` has
weight `0`, then `Q = A·b − a·B = 0` (the vertex cluster of `X` is `X`, the cut set is the constant set of pairs meeting
`X`, `{s ↮ X}` is sure, and `taNW/taN = a/b`). [folklore] -/
theorem taQ_eq_zero_of_noBoundary (w : Sym2 V → ℝ) (hw0 : ∀ e, 0 ≤ w e) (hw1 : ∀ e, w e ≤ 1)
    (hm : ∑ ω, weight w ω = 1) (s y z : V) (hsy : s ≠ y) (X : Set V) (g : Set (Sym2 V) → ℝ)
    (hbd : ∀ e : Sym2 V, ¬ e.IsDiag → ∀ a ∈ e, ∀ b ∈ e, a ∈ X → b ∉ X → w e = 0) :
    taQ w s y z X g = 0 := by
  classical
  by_cases hs : s ∈ X
  · simp only [taQ, taA_eq_zero_of_root_mem w s y z X hs, taB_eq_zero_of_root_mem w s y X hs]; ring
  by_cases hyX : y ∈ X
  · simp only [taQ, tab_eq_zero_of_mem w s y X (Set.mem_insert_of_mem _ hyX),
      taa_eq_zero_of_mem w s y z X (Set.mem_insert_of_mem _ hyX)]; ring
  -- configurations without zero-weight pairs have no open boundary pair
  have hnb : ∀ η : Set (Sym2 V), ∀ e ∈ η \ {e | w e = 0}, ¬ e.IsDiag → ∀ a ∈ e, ∀ b ∈ e, a ∈ X → b ∈ X := by
    intro η e he hd a ha b hb haX
    by_contra hbX
    exact he.2 (hbd e hd a ha b hb haX hbX)
  -- hence the cut set is the set `B₀` of pairs meeting `X`, and `s ↮ X` holds
  have hcut : ∀ η : Set (Sym2 V), cut X (η \ {e | w e = 0}) = {e | ∃ u ∈ e, u ∈ X} :=
    fun η => cut_eq_of_noBoundary (hnb η)
  have hD : ∀ η : Set (Sym2 V), η \ {e | w e = 0} ∈ avoidEv s X := fun η x hx hsx =>
    hs (mem_of_reachable_of_noBoundary (hnb η) hx hsx.symm)
  -- the constant values
  set c₀ : ℝ := delE w {e | ∃ u ∈ e, u ∈ X} (fun η => g (openEdgeCluster η s) * ind (openConn s y) η) -
    delE w {e | ∃ u ∈ e, u ∈ X} (fun η => g (openEdgeCluster η s)) *
      delE w {e | ∃ u ∈ e, u ∈ X} (ind (openConn s y)) with hc₀
  set n₀ : ℝ := delE w {e | ∃ u ∈ e, u ∈ X} (ind (openConn s y : Set (BondConfig V))ᶜ) with hn₀
  set nw₀ : ℝ := delE w {e | ∃ u ∈ e, u ∈ X} (ind ((openConn s y : Set (BondConfig V))ᶜ ∩ openConn y z))
    with hnw₀
  have hB : taB w s y X g = c₀ := by
    rw [taB, sum_weight_eq_sum_sdiff_zeros w]
    have h1 : ∀ η : Set (Sym2 V), weight w η * (fun ω => ind (avoidEv s X) ω * taC w s y X g ω) (η \ {e | w e = 0}) =
        weight w η * c₀ := by
      intro η; simp only; rw [ind_of_mem (hD η), one_mul, taC, hcut η]
    rw [Finset.sum_congr rfl fun η _ => h1 η, ← Finset.sum_mul, hm, one_mul]
  have hA : taA w s y z X g = nw₀ / n₀ * c₀ := by
    rw [taA, sum_weight_eq_sum_sdiff_zeros w]
    have h1 : ∀ η : Set (Sym2 V), weight w η * (fun ω => ind (avoidEv s X) ω *
        (taNW w s y z X ω / taN w s y X ω * taC w s y X g ω)) (η \ {e | w e = 0}) = weight w η * (nw₀ / n₀ * c₀) := by
      intro η; simp only; rw [ind_of_mem (hD η), one_mul, taC, taN, taNW, hcut η]
    rw [Finset.sum_congr rfl fun η _ => h1 η, ← Finset.sum_mul, hm, one_mul]
  -- the y-side masses: `b = n₀`, `a = nw₀`
  have hconn : ∀ (η : Set (Sym2 V)) (t : V),
      (openGraph ((η \ {e | w e = 0}) \ {e | ∃ u ∈ e, u ∈ X})).Reachable y t ↔
        (openGraph (η \ {e | w e = 0})).Reachable y t :=
    fun η t => reachable_sdiff_iff_of_noBoundary (hnb η) hyX t
  have hE : ∀ η : Set (Sym2 V), ind (avoidEv y (insert s X)) (η \ {e | w e = 0}) =
      ind (openConn s y : Set (BondConfig V))ᶜ ((η \ {e | w e = 0}) \ {e | ∃ u ∈ e, u ∈ X}) := by
    intro η
    by_cases h : η \ {e | w e = 0} ∈ avoidEv y (insert s X)
    · rw [ind_of_mem h, ind_of_mem]
      intro hsy'
      exact h s (Set.mem_insert _ _) (((hconn η s).1 (hsy' : (openGraph _).Reachable s y).symm))
    · rw [ind_of_not_mem h, ind_of_not_mem]
      intro hN
      apply h
      intro t ht hyt
      rcases Set.mem_insert_iff.1 ht with rfl | ht
      · exact hN (((hconn η t).2 hyt).symm : (openGraph _).Reachable t y)
      · exact hyX (mem_of_reachable_of_noBoundary (hnb η) ht hyt.symm)
  have hb : tab w s y X = n₀ := by
    rw [tab, sum_weight_eq_sum_sdiff_zeros w, hn₀, delE,
      sum_weight_eq_sum_sdiff_zeros w (fun η => ind _ (η \ {e | ∃ u ∈ e, u ∈ X}))]
    exact Finset.sum_congr rfl fun η _ => by rw [hE η]
  have ha : taa w s y z X = nw₀ := by
    rw [taa, sum_weight_eq_sum_sdiff_zeros w, hnw₀, delE,
      sum_weight_eq_sum_sdiff_zeros w (fun η => ind _ (η \ {e | ∃ u ∈ e, u ∈ X}))]
    refine Finset.sum_congr rfl fun η _ => ?_
    rw [ind_inter, ind_inter, hE η]
    congr 1
    by_cases h : η \ {e | w e = 0} ∈ openConn y z
    · have h' : (η \ {e | w e = 0}) \ {e | ∃ u ∈ e, u ∈ X} ∈ openConn y z :=
        ((hconn η z).2 h : (openGraph _).Reachable y z)
      rw [ind_of_mem h, ind_of_mem h']
    · have h' : (η \ {e | w e = 0}) \ {e | ∃ u ∈ e, u ∈ X} ∉ openConn y z := fun hh => h ((hconn η z).1 hh)
      rw [ind_of_not_mem h, ind_of_not_mem h']
  -- `nw₀ ≤ n₀`, both nonnegative; conclude
  have hle : nw₀ ≤ n₀ := by
    simp only [hnw₀, hn₀, delE]
    refine Finset.sum_le_sum fun η _ => mul_le_mul_of_nonneg_left ?_ (weight_nonneg hw0 hw1 η)
    rw [ind_inter]
    have h1 := ind_le_one (openConn y z : Set (BondConfig V)) (η \ {e | ∃ u ∈ e, u ∈ X})
    have h2 := ind_nonneg (openConn s y : Set (BondConfig V))ᶜ (η \ {e | ∃ u ∈ e, u ∈ X})
    nlinarith [ind_nonneg (openConn y z : Set (BondConfig V)) (η \ {e | ∃ u ∈ e, u ∈ X})]
  have hnw0 : 0 ≤ nw₀ := by
    simp only [hnw₀, delE]
    exact Finset.sum_nonneg fun η _ => mul_nonneg (weight_nonneg hw0 hw1 η) (ind_nonneg _ _)
  rw [taQ, hA, hB, ha, hb]
  by_cases hn : n₀ = 0
  · have : nw₀ = 0 := le_antisymm (hn ▸ hle) hnw0
    rw [this, hn]; ring
  · field_simp
    ring

end TA

end HullPort

end Percolation.Continuity
