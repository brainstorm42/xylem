import Percolation.Continuity.HullPort.DeletedEdges
import Percolation.Continuity.HullPort.TADefs
import Percolation.Literature.KozmaNitzanSeparatingTriple
import Percolation.Util.Linter

/-!
# Marker dominance with an avoided set: the `T_A` functionals and their one-edge sections

The functionals `delE, cut, avoidEv, taC, taN, taNW, taB, taA, tab, taa, taQ` are defined in `Continuity/HullPort/TADefs.lean`.
First part of the proof of `T_A ≥ 0`, in the "avoided SET `X`, same weights,
deleted pairs" bookkeeping (sum level, `BHK2006.weight`):

* `HullPort.sum_weight_resample` — one-coordinate resampling `E_w[F] = E_{w₀}[(1−w_e)F(η∖e) + w_e F(η ∪ e)]`
  (`w₀ = w` off `e`, `w₀ e = 0`);
* the SECTION IDENTITIES along an edge `e = {x₀, v}`, `x₀ ∈ X`:
  `Φ_X(w) = (1 − w e)·Φ_X(w₀) + (w e)·Φ_{X ∪ {v}}(w₀)` for `Φ ∈ {taB, taA, tab, taa}`, `w₀ = w[e ↦ 0]`
  (`taB_section`, `taA_section`, `tab_section`, `taa_section`): the `p_e = 1` endpoint of the one-edge
  deformation is the state "`v` added to `X`", with no contraction;
[cite: VandenbergHaggstromKahn2005, §1 pp. 3–5 (the induced model on `G − Z`, display (6)) — bookkeeping derived here]
-/

noncomputable section

namespace Percolation.Continuity

open MeasureTheory Set Percolation.Literature.LatticeModels Percolation.Literature
open scoped Classical

variable {V : Type*}

namespace HullPort

open LonePortSum LonePortSumGeneral BHK2006 DecisionTree KNPreFKG KNSep

section Resample

variable {ι : Type*} [Fintype ι]

/-- **One-coordinate resampling**: `Σ_η weight(w) η F(η) = Σ_η weight(w₀) η [(1 − w e) F(η ∖ {e}) + (w e) F(η ∪ {e})]`
whenever `w₀ = w` off `e` and `w₀ e = 0` (independence of the coordinate `e`). [folklore] -/
theorem sum_weight_resample (w w₀ : ι → ℝ) (e : ι) (he0 : w₀ e = 0) (hoff : ∀ i, i ≠ e → w₀ i = w i)
    (F : Set ι → ℝ) :
    ∑ η, weight w η * F η = ∑ η, weight w₀ η * ((1 - w e) * F (η \ {e}) + w e * F (insert e η)) := by
  classical
  set R : Set ι → ℝ := fun η => ∏ i ∈ Finset.univ.erase e, (if i ∈ η then w i else 1 - w i) with hR
  have hfac : ∀ η : Set ι, weight w η = (if e ∈ η then w e else 1 - w e) * R η := fun η =>
    (Finset.mul_prod_erase Finset.univ (fun i => if i ∈ η then w i else 1 - w i) (Finset.mem_univ e)).symm
  have hfac₀ : ∀ η : Set ι, weight w₀ η = (if e ∈ η then 0 else 1) * R η := by
    intro η
    have h := (Finset.mul_prod_erase Finset.univ (fun i => if i ∈ η then w₀ i else 1 - w₀ i)
      (Finset.mem_univ e)).symm
    have hRe : ∏ i ∈ Finset.univ.erase e, (if i ∈ η then w₀ i else 1 - w₀ i) = R η := by
      refine Finset.prod_congr rfl fun i hi => ?_
      have hie : i ≠ e := Finset.ne_of_mem_erase hi
      simp only [hoff i hie]
    rw [hRe, he0] at h
    rw [show weight w₀ η = ∏ i, (if i ∈ η then w₀ i else 1 - w₀ i) from rfl, h]
    split_ifs <;> ring
  have hRins : ∀ η : Set ι, R (insert e η) = R η := fun η =>
    Finset.prod_congr rfl fun i hi => by
      have hie : i ≠ e := Finset.ne_of_mem_erase hi
      simp only [Set.mem_insert_iff, hie, false_or]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun η : Set ι => e ∈ η),
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun η : Set ι => e ∈ η)
      (fun η => weight w₀ η * ((1 - w e) * F (η \ {e}) + w e * F (insert e η)))]
  have hzero : ∑ η ∈ Finset.univ.filter (fun η : Set ι => e ∈ η),
      weight w₀ η * ((1 - w e) * F (η \ {e}) + w e * F (insert e η)) = 0 := by
    refine Finset.sum_eq_zero fun η hη => ?_
    have he : e ∈ η := (Finset.mem_filter.1 hη).2
    rw [hfac₀ η, if_pos he]; ring
  have hreidx : ∑ η ∈ Finset.univ.filter (fun η : Set ι => e ∈ η), weight w η * F η =
      ∑ η ∈ Finset.univ.filter (fun η : Set ι => ¬ e ∈ η), weight w (insert e η) * F (insert e η) := by
    refine Finset.sum_nbij' (fun η => η \ {e}) (fun η => insert e η) ?_ ?_ ?_ ?_ ?_
    · intro η hη
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_sdiff, Set.mem_singleton_iff,
        not_true_eq_false, and_false, not_false_eq_true]
    · intro η hη
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_insert_iff, true_or]
    · intro η hη
      have he : e ∈ η := (Finset.mem_filter.1 hη).2
      simp only [Set.insert_sdiff_singleton, Set.insert_eq_of_mem he]
    · intro η hη
      have he : e ∉ η := (Finset.mem_filter.1 hη).2
      show insert e η \ {e} = η
      rw [← Set.union_singleton, Set.union_sdiff_right, Set.sdiff_singleton_eq_self he]
    · intro η hη
      have he : e ∈ η := (Finset.mem_filter.1 hη).2
      simp only [Set.insert_sdiff_singleton, Set.insert_eq_of_mem he]
  rw [hreidx, hzero, zero_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun η hη => ?_
  have he : e ∉ η := (Finset.mem_filter.1 hη).2
  rw [hfac (insert e η), hfac η, hfac₀ η, hRins η, if_pos (Set.mem_insert e η), if_neg he, if_neg he,
    Set.sdiff_singleton_eq_self he]
  ring

/-- Deleting a coordinate of weight `0` changes nothing: `Σ_η weight(w₀) η φ(η ∖ {e}) = Σ_η weight(w₀) η φ(η)` if
`w₀ e = 0`. [folklore] -/
theorem sum_weight_mul_comp_sdiff_singleton_of_zero (w₀ : ι → ℝ) (e : ι) (he0 : w₀ e = 0) (φ : Set ι → ℝ) :
    ∑ η, weight w₀ η * φ (η \ {e}) = ∑ η, weight w₀ η * φ η := by
  classical
  refine Finset.sum_congr rfl fun η _ => ?_
  by_cases he : e ∈ η
  · have h0 : weight w₀ η = 0 := by
      have h := (Finset.mul_prod_erase Finset.univ (fun i => if i ∈ η then w₀ i else 1 - w₀ i)
        (Finset.mem_univ e)).symm
      rw [show weight w₀ η = ∏ i, (if i ∈ η then w₀ i else 1 - w₀ i) from rfl, h, if_pos he, he0, zero_mul]
    rw [h0, zero_mul, zero_mul]
  · rw [Set.sdiff_singleton_eq_self he]

end Resample

section TA

variable [Fintype V]

/-! ### Combinatorics of one added edge `e = {x₀, v}` with `x₀ ∈ X` -/

omit [Fintype V] in
/-- Adding the edge `{x₀, v}` (`x₀ ∈ T`): `r ↮ T` afterwards iff `r ↮ T ∪ {v}` before. [folklore] -/
theorem insert_mem_avoidEv_iff (r x₀ v : V) (T : Set V) (hx₀ : x₀ ∈ T) (ω : Set (Sym2 V)) :
    insert s(x₀, v) ω ∈ avoidEv r T ↔ ω ∈ avoidEv r (insert v T) := by
  constructor
  · intro h t ht hrt
    rcases Set.mem_insert_iff.1 ht with rfl | ht'
    · exact h x₀ hx₀ ((reachable_insert_iff ω x₀ t r x₀).2
        (Or.inr (Or.inr ⟨hrt, SimpleGraph.Reachable.refl _⟩)))
    · exact h t ht' (hrt.mono (openGraph_le (Set.subset_insert _ _)))
  · intro h t ht hrt
    rcases (reachable_insert_iff ω x₀ v r t).1 hrt with h1 | ⟨h2, _⟩ | ⟨h3, _⟩
    · exact h t (Set.mem_insert_of_mem _ ht) h1
    · exact h x₀ (Set.mem_insert_of_mem _ hx₀) h2
    · exact h v (Set.mem_insert _ _) h3

omit [Fintype V] in
/-- Adding the edge `{x₀, v}` (`x₀ ∈ X`): the cut set of `X` afterwards is the cut set of `X ∪ {v}` before. [folklore] -/
theorem cut_insert_edge (x₀ v : V) (X : Set V) (hx₀ : x₀ ∈ X) (ω : Set (Sym2 V)) :
    cut X (insert s(x₀, v) ω) = cut (insert v X) ω := by
  ext e
  simp only [cut, Set.mem_setOf_eq]
  constructor
  · rintro ⟨u, hu, x, hx, hxu⟩
    rcases (reachable_insert_iff ω x₀ v x u).1 hxu with h1 | ⟨_, h2⟩ | ⟨_, h3⟩
    · exact ⟨u, hu, x, Set.mem_insert_of_mem _ hx, h1⟩
    · exact ⟨u, hu, v, Set.mem_insert _ _, h2⟩
    · exact ⟨u, hu, x₀, Set.mem_insert_of_mem _ hx₀, h3⟩
  · rintro ⟨u, hu, x, hx, hxu⟩
    rcases Set.mem_insert_iff.1 hx with rfl | hx'
    · exact ⟨u, hu, x₀, hx₀, (reachable_insert_iff ω x₀ x x₀ u).2
        (Or.inr (Or.inl ⟨SimpleGraph.Reachable.refl _, hxu⟩))⟩
    · exact ⟨u, hu, x, hx', hxu.mono (openGraph_le (Set.subset_insert _ _))⟩

omit [Fintype V] in
/-- On `{r ↮ T ∪ {v}}` (`x₀ ∈ T`), adding the edge `{x₀, v}` does not change the connections of `r`. [folklore] -/
theorem reachable_insert_edge_iff_of_avoid (r x₀ v z : V) (T : Set V) (hx₀ : x₀ ∈ T) (ω : Set (Sym2 V))
    (hω : ω ∈ avoidEv r (insert v T)) :
    (openGraph (insert s(x₀, v) ω)).Reachable r z ↔ (openGraph ω).Reachable r z := by
  constructor
  · intro h
    rcases (reachable_insert_iff ω x₀ v r z).1 h with h1 | ⟨h2, _⟩ | ⟨h3, _⟩
    · exact h1
    · exact absurd h2 (hω x₀ (Set.mem_insert_of_mem _ hx₀))
    · exact absurd h3 (hω v (Set.mem_insert _ _))
  · exact fun h => h.mono (openGraph_le (Set.subset_insert _ _))

omit [Fintype V] in
/-- The edge `{x₀, v}` with `x₀ ∈ X` lies in every cut set of `X`. [folklore] -/
theorem edge_mem_cut (x₀ v : V) (X : Set V) (hx₀ : x₀ ∈ X) (ω : Set (Sym2 V)) : s(x₀, v) ∈ cut X ω :=
  ⟨x₀, Sym2.mem_mk_left _ _, x₀, hx₀, SimpleGraph.Reachable.refl _⟩

/-- A deleted-pairs expectation does not see the weights of the deleted pairs. [folklore] -/
theorem delE_congr_of_mem {w w' : Sym2 V → ℝ} {B : Set (Sym2 V)} (h : ∀ e ∉ B, w e = w' e)
    (φ : Set (Sym2 V) → ℝ) : delE w B φ = delE w' B φ := by
  simp only [delE]
  rw [sum_weight_mul_comp_sdiff w B φ, sum_weight_mul_comp_sdiff w' B φ]
  refine Finset.sum_congr rfl fun η _ => ?_
  congr 2
  funext e
  by_cases he : e ∈ B
  · simp only [if_pos he]
  · simp only [if_neg he, h e he]

/-! ### The section identities -/

/-- Generic section identity: for a functional `Σ_ω w(ω) 1_{D_X}(ω) Φ(w, cut_X ω)` whose integrand depends on `ω`
only through the cut set and on the weights only off the cut set,
`F_X(w) = (1 − w e) F_X(w₀) + (w e) F_{X∪{v}}(w₀)`. [folklore] -/
theorem section_generic (w w₀ : Sym2 V → ℝ) (s x₀ v : V) (X : Set V) (hx₀ : x₀ ∈ X)
    (he0 : w₀ s(x₀, v) = 0) (hoff : ∀ f, f ≠ s(x₀, v) → w₀ f = w f)
    (Φ : (Sym2 V → ℝ) → Set (Sym2 V) → ℝ)
    (hΦ : ∀ (w w' : Sym2 V → ℝ) (B : Set (Sym2 V)), (∀ e ∉ B, w e = w' e) → Φ w B = Φ w' B) :
    ∑ ω, weight w ω * (ind (avoidEv s X) ω * Φ w (cut X ω)) =
      (1 - w s(x₀, v)) * ∑ ω, weight w₀ ω * (ind (avoidEv s X) ω * Φ w₀ (cut X ω)) +
        w s(x₀, v) * ∑ ω, weight w₀ ω * (ind (avoidEv s (insert v X)) ω * Φ w₀ (cut (insert v X) ω)) := by
  classical
  have hΦw : ∀ (Y : Set V) (ω : Set (Sym2 V)), x₀ ∈ Y → Φ w (cut Y ω) = Φ w₀ (cut Y ω) := by
    intro Y ω hY
    refine hΦ w w₀ (cut Y ω) fun f hf => ?_
    have hfe : f ≠ s(x₀, v) := fun h => hf (h ▸ edge_mem_cut x₀ v Y hY ω)
    rw [hoff f hfe]
  rw [sum_weight_resample w w₀ s(x₀, v) he0 hoff]
  simp only [mul_add, Finset.sum_add_distrib]
  congr 1
  · -- the `e`-closed section
    have h1 := sum_weight_mul_comp_sdiff_singleton_of_zero w₀ s(x₀, v) he0
      (fun ζ => (1 - w s(x₀, v)) * (ind (avoidEv s X) ζ * Φ w (cut X ζ)))
    rw [h1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun η _ => ?_
    rw [hΦw X _ hx₀]; ring
  · -- the `e`-open section
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun η _ => ?_
    have hD : ind (avoidEv s X) (insert s(x₀, v) η) = ind (avoidEv s (insert v X)) η := by
      by_cases h : insert s(x₀, v) η ∈ avoidEv s X
      · rw [ind_of_mem h, ind_of_mem ((insert_mem_avoidEv_iff s x₀ v X hx₀ η).1 h)]
      · rw [ind_of_not_mem h, ind_of_not_mem fun h' => h ((insert_mem_avoidEv_iff s x₀ v X hx₀ η).2 h')]
    rw [hD, cut_insert_edge x₀ v X hx₀ η, hΦw (insert v X) η (Set.mem_insert_of_mem _ hx₀)]
    ring

/-- **Section identity for `B`**: `B_X(w) = (1 − w e) B_X(w₀) + (w e) B_{X∪{v}}(w₀)`, `e = {x₀, v}`, `x₀ ∈ X`.
[folklore] -/
theorem taB_section (w w₀ : Sym2 V → ℝ) (s y x₀ v : V) (X : Set V) (hx₀ : x₀ ∈ X)
    (he0 : w₀ s(x₀, v) = 0) (hoff : ∀ f, f ≠ s(x₀, v) → w₀ f = w f) (g : Set (Sym2 V) → ℝ) :
    taB w s y X g = (1 - w s(x₀, v)) * taB w₀ s y X g + w s(x₀, v) * taB w₀ s y (insert v X) g := by
  have key := section_generic w w₀ s x₀ v X hx₀ he0 hoff
    (fun w' B => delE w' B (fun η => g (openEdgeCluster η s) * ind (openConn s y) η) -
      delE w' B (fun η => g (openEdgeCluster η s)) * delE w' B (ind (openConn s y)))
    (fun w w' B h => by simp only [delE_congr_of_mem h])
  simpa only [taB, taC] using key

/-- **Section identity for `A`**. [folklore] -/
theorem taA_section (w w₀ : Sym2 V → ℝ) (s y z x₀ v : V) (X : Set V) (hx₀ : x₀ ∈ X)
    (he0 : w₀ s(x₀, v) = 0) (hoff : ∀ f, f ≠ s(x₀, v) → w₀ f = w f) (g : Set (Sym2 V) → ℝ) :
    taA w s y z X g = (1 - w s(x₀, v)) * taA w₀ s y z X g + w s(x₀, v) * taA w₀ s y z (insert v X) g := by
  have key := section_generic w w₀ s x₀ v X hx₀ he0 hoff
    (fun w' B => delE w' B (ind ((openConn s y : Set (BondConfig V))ᶜ ∩ openConn y z)) /
        delE w' B (ind (openConn s y : Set (BondConfig V))ᶜ) *
      (delE w' B (fun η => g (openEdgeCluster η s) * ind (openConn s y) η) -
        delE w' B (fun η => g (openEdgeCluster η s)) * delE w' B (ind (openConn s y))))
    (fun w w' B h => by simp only [delE_congr_of_mem h])
  simpa only [taA, taC, taN, taNW] using key

/-- Section identity for an event of the root `y` avoiding `T ∋ x₀`, intersected with a connection of `y`:
`μ_w(y ↮ T, y ↔ z) = (1 − w e) μ_{w₀}(y ↮ T, y ↔ z) + (w e) μ_{w₀}(y ↮ T ∪ {v}, y ↔ z)`. [folklore] -/
theorem avoid_conn_section (w w₀ : Sym2 V → ℝ) (y z x₀ v : V) (T : Set V) (hx₀ : x₀ ∈ T)
    (he0 : w₀ s(x₀, v) = 0) (hoff : ∀ f, f ≠ s(x₀, v) → w₀ f = w f) :
    ∑ ω, weight w ω * ind (avoidEv y T ∩ openConn y z) ω =
      (1 - w s(x₀, v)) * ∑ ω, weight w₀ ω * ind (avoidEv y T ∩ openConn y z) ω +
        w s(x₀, v) * ∑ ω, weight w₀ ω * ind (avoidEv y (insert v T) ∩ openConn y z) ω := by
  classical
  rw [sum_weight_resample w w₀ s(x₀, v) he0 hoff]
  simp only [mul_add, Finset.sum_add_distrib]
  congr 1
  · have h1 := sum_weight_mul_comp_sdiff_singleton_of_zero w₀ s(x₀, v) he0
      (fun ζ => (1 - w s(x₀, v)) * ind (avoidEv y T ∩ openConn y z) ζ)
    rw [h1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun η _ => ?_
    ring
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun η _ => ?_
    have hD : ind (avoidEv y T ∩ openConn y z) (insert s(x₀, v) η) =
        ind (avoidEv y (insert v T) ∩ openConn y z) η := by
      by_cases h : η ∈ avoidEv y (insert v T)
      · have h' : insert s(x₀, v) η ∈ avoidEv y T := (insert_mem_avoidEv_iff y x₀ v T hx₀ η).2 h
        have hz : insert s(x₀, v) η ∈ openConn y z ↔ η ∈ openConn y z :=
          reachable_insert_edge_iff_of_avoid y x₀ v z T hx₀ η h
        by_cases hzz : η ∈ openConn y z
        · rw [ind_of_mem (Set.mem_inter h' (hz.2 hzz)), ind_of_mem (Set.mem_inter h hzz)]
        · rw [ind_of_not_mem fun hh => hzz (hz.1 hh.2), ind_of_not_mem fun hh => hzz hh.2]
      · have h' : insert s(x₀, v) η ∉ avoidEv y T :=
          fun hh => h ((insert_mem_avoidEv_iff y x₀ v T hx₀ η).1 hh)
        rw [ind_of_not_mem fun hh => h' hh.1, ind_of_not_mem fun hh => h hh.1]
    rw [hD]; ring

/-- **Section identity for `a`**. [folklore] -/
theorem taa_section (w w₀ : Sym2 V → ℝ) (s y z x₀ v : V) (X : Set V) (hx₀ : x₀ ∈ X)
    (he0 : w₀ s(x₀, v) = 0) (hoff : ∀ f, f ≠ s(x₀, v) → w₀ f = w f) :
    taa w s y z X = (1 - w s(x₀, v)) * taa w₀ s y z X + w s(x₀, v) * taa w₀ s y z (insert v X) := by
  have key := avoid_conn_section w w₀ y z x₀ v (insert s X) (Set.mem_insert_of_mem _ hx₀) he0 hoff
  rw [Set.insert_comm] at key
  simpa only [taa] using key

/-- **Section identity for `b`**. [folklore] -/
theorem tab_section (w w₀ : Sym2 V → ℝ) (s y x₀ v : V) (X : Set V) (hx₀ : x₀ ∈ X)
    (he0 : w₀ s(x₀, v) = 0) (hoff : ∀ f, f ≠ s(x₀, v) → w₀ f = w f) :
    tab w s y X = (1 - w s(x₀, v)) * tab w₀ s y X + w s(x₀, v) * tab w₀ s y (insert v X) := by
  have key := avoid_conn_section w w₀ y y x₀ v (insert s X) (Set.mem_insert_of_mem _ hx₀) he0 hoff
  rw [Set.insert_comm] at key
  have hyy : ∀ (T : Set V) (ω : Set (Sym2 V)), ind (avoidEv y T ∩ openConn y y) ω = ind (avoidEv y T) ω := by
    intro T ω
    have : avoidEv y T ∩ openConn y y = avoidEv y T := by
      ext ω'; simp only [Set.mem_inter_iff, openConn, Set.mem_setOf_eq, and_iff_left_iff_imp]
      exact fun _ => SimpleGraph.Reachable.refl _
    rw [this]
  simp only [hyy] at key
  simpa only [tab] using key

end TA

end HullPort

end Percolation.Continuity
