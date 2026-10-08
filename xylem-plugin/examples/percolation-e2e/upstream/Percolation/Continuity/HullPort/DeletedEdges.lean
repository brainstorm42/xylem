import Percolation.Continuity.HullPort.MarkerDominanceTools
import Percolation.Util.Linter

/-!
# Marker dominance toolkit: deleting edges = zero weights ("`G − K`" bookkeeping)

The proof of the marker dominance lemma with an avoided vertex conditions on the cluster `K = C_x` and works
"in `G − K`": here this is always the SAME weight
vector `w` on the full `Sym2 V` applied to the configuration `η ∖ B` with a set of pairs `B` deleted
(`BHK2006.sum_cond_cluster_sdiff`, `BHK2006.set_sum_cond_cluster`).  To run results stated for `prodBernoulli w'`
(e.g. `HullPort.markerDominance_noAvoid`, the `X = ∅` marker dominance lemma) inside `G − K`, one needs that the law
of `η ∖ B` under `prodBernoulli w` is `prodBernoulli w_B` with `w_B = w` off `B` and `w_B = 0` on `B`:

* `HullPort.sum_weight_mul_comp_sdiff` — `Σ_η weight(w) η · φ(η ∖ B) = Σ_η weight(w_B) η · φ(η)` (finite sums;
  one coordinate at a time, `sum_weight_mul_comp_sdiff_singleton`);
* `HullPort.integral_comp_sdiff_prodBernoulli` — `∫ φ(ω ∖ B) d(prodBernoulli w) = ∫ φ d(prodBernoulli w_B)`;
  `HullPort.measureReal_preimage_sdiff_prodBernoulli` — `μ_w((· ∖ B)⁻¹ E) = μ_{w_B}(E)`;
  `HullPort.setIntegral_preimage_sdiff_prodBernoulli` — `∫_{(·∖B)⁻¹ E} φ(ω ∖ B) dμ_w = ∫_E φ dμ_{w_B}`;
Compare the induced model on `G − Z` of [cite: VandenbergHaggstromKahn2005, §1 pp. 7–8].
-/

noncomputable section

namespace Percolation.Continuity

open MeasureTheory Set Percolation.Literature.LatticeModels Percolation.Literature
open scoped Classical

variable {V : Type*}

namespace HullPort

open LonePortSum LonePortSumGeneral BHK2006 DecisionTree KNPreFKG

section Weights

variable {ι : Type*} [Fintype ι]

/-- One coordinate: `Σ_η weight(w) η · φ(η ∖ {e}) = Σ_η weight(w₀) η · φ(η)` with `w₀ = w` except `w₀ e = 0`
(the law of `η ∖ {e}` is the product law with the coordinate `e` switched off). [folklore] -/
theorem sum_weight_mul_comp_sdiff_singleton (w : ι → ℝ) (e : ι) (φ : Set ι → ℝ) :
    ∑ η, weight w η * φ (η \ {e}) = ∑ η, weight (fun i => if i = e then 0 else w i) η * φ η := by
  classical
  set w₀ : ι → ℝ := fun i => if i = e then 0 else w i with hw₀
  -- the weight factors as (factor at `e`) × (product over the other coordinates)
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
      simp only [hw₀, if_neg hie]
    rw [hRe] at h
    have hwe : w₀ e = 0 := by simp only [hw₀, if_true]
    rw [hwe] at h
    rw [show weight w₀ η = ∏ i, (if i ∈ η then w₀ i else 1 - w₀ i) from rfl, h]
    split_ifs <;> ring
  have hRins : ∀ η : Set ι, R (insert e η) = R η := fun η =>
    Finset.prod_congr rfl fun i hi => by
      have hie : i ≠ e := Finset.ne_of_mem_erase hi
      simp only [Set.mem_insert_iff, hie, false_or]
  -- split both sums along `e ∈ η`
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun η : Set ι => e ∈ η),
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun η : Set ι => e ∈ η)
      (fun η => weight w₀ η * φ η)]
  -- the `e ∈ η` part of the right-hand side vanishes
  have hzero : ∑ η ∈ Finset.univ.filter (fun η : Set ι => e ∈ η), weight w₀ η * φ η = 0 := by
    refine Finset.sum_eq_zero fun η hη => ?_
    have he : e ∈ η := (Finset.mem_filter.1 hη).2
    rw [hfac₀ η, if_pos he]; ring
  -- the `e ∈ η` part of the left-hand side, reindexed by `η ↦ η ∖ {e}`
  have hreidx : ∑ η ∈ Finset.univ.filter (fun η : Set ι => e ∈ η), weight w η * φ (η \ {e}) =
      ∑ η ∈ Finset.univ.filter (fun η : Set ι => ¬ e ∈ η), weight w (insert e η) * φ η := by
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
  have hrest : ∑ η ∈ Finset.univ.filter (fun η : Set ι => ¬ e ∈ η), weight w η * φ (η \ {e}) =
      ∑ η ∈ Finset.univ.filter (fun η : Set ι => ¬ e ∈ η), weight w η * φ η := by
    refine Finset.sum_congr rfl fun η hη => ?_
    have he : e ∉ η := (Finset.mem_filter.1 hη).2
    rw [Set.sdiff_singleton_eq_self he]
  rw [hreidx, hrest, hzero, zero_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun η hη => ?_
  have he : e ∉ η := (Finset.mem_filter.1 hη).2
  rw [hfac (insert e η), hfac η, hfac₀ η, hRins η, if_pos (Set.mem_insert e η), if_neg he, if_neg he]
  ring

/-- **Deleting coordinates = switching them off**: for any `B : Set ι`,
`Σ_η weight(w) η · φ(η ∖ B) = Σ_η weight(w_B) η · φ(η)` with `w_B = w` off `B` and `w_B = 0` on `B`. [folklore] -/
theorem sum_weight_mul_comp_sdiff (w : ι → ℝ) (B : Set ι) (φ : Set ι → ℝ) :
    ∑ η, weight w η * φ (η \ B) = ∑ η, weight (fun i => if i ∈ B then 0 else w i) η * φ η := by
  classical
  -- induction on a finset `S` with `↑S = B`
  suffices h : ∀ (S : Finset ι) (w : ι → ℝ) (φ : Set ι → ℝ),
      ∑ η, weight w η * φ (η \ ↑S) = ∑ η, weight (fun i => if i ∈ S then 0 else w i) η * φ η by
    have hB : B = ↑B.toFinset := (Set.coe_toFinset B).symm
    have := h B.toFinset w φ
    rw [← hB] at this
    rw [this]
    refine Finset.sum_congr rfl fun η _ => ?_
    congr 1
    simp only [Set.mem_toFinset]
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro w φ
    simp only [Finset.coe_empty, Set.sdiff_empty, Finset.notMem_empty, if_false]
  | @insert e S heS ih =>
    intro w φ
    have h1 : ∀ η : Set ι, η \ ↑(insert e S) = (η \ {e}) \ ↑S := fun η => by
      rw [Finset.coe_insert, ← Set.union_singleton, Set.union_comm, Set.sdiff_sdiff]
    simp only [h1]
    rw [sum_weight_mul_comp_sdiff_singleton w e (fun ζ => φ (ζ \ ↑S)), ih]
    refine Finset.sum_congr rfl fun η _ => ?_
    congr 2
    funext i
    by_cases hi : i = e
    · subst hi; simp
    · simp [hi]

end Weights

/-- **Deleting pairs = switching them off, integral form**: for `B : Set (Sym2 V)` and any `φ`,
`∫ φ(ω ∖ B) d(prodBernoulli w) = ∫ φ d(prodBernoulli w_B)`, `w_B = w` off `B`, `= 0` on `B`. [folklore] -/
theorem integral_comp_sdiff_prodBernoulli [Fintype V] (w : Sym2 V → unitInterval) (B : Set (Sym2 V))
    (φ : BondConfig V → ℝ) :
    ∫ ω, φ (ω \ B) ∂(prodBernoulli w) = ∫ ω, φ ω ∂(prodBernoulli fun e => if e ∈ B then 0 else w e) := by
  classical
  rw [integral_prodBernoulli_eq_sum w (fun ω => φ (ω \ B)), integral_prodBernoulli_eq_sum]
  rw [sum_weight_mul_comp_sdiff (fun e => (w e : ℝ)) B φ]
  refine Finset.sum_congr rfl fun η _ => ?_
  congr 2
  funext e
  split_ifs <;> rfl

/-- **Deleting pairs = switching them off, events**: `μ_w((· ∖ B)⁻¹ E) = μ_{w_B}(E)`. [folklore] -/
theorem measureReal_preimage_sdiff_prodBernoulli [Fintype V] (w : Sym2 V → unitInterval) (B : Set (Sym2 V))
    (E : Set (BondConfig V)) :
    (prodBernoulli w).real ((· \ B) ⁻¹' E) = (prodBernoulli fun e => if e ∈ B then 0 else w e).real E := by
  classical
  rw [← integral_indicator_one (MeasurableSet.of_discrete : MeasurableSet ((· \ B) ⁻¹' E)),
    ← integral_indicator_one (MeasurableSet.of_discrete : MeasurableSet E)]
  have h : (((· \ B) ⁻¹' E).indicator (1 : BondConfig V → ℝ)) =
      fun ω => (E.indicator (1 : BondConfig V → ℝ)) (ω \ B) := by
    funext ω
    simp only [Set.indicator, Set.mem_preimage, Pi.one_apply]
  rw [h, integral_comp_sdiff_prodBernoulli w B (E.indicator 1)]

/-- **Deleting pairs = switching them off, restricted integrals**:
`∫_{(·∖B)⁻¹ E} φ(ω ∖ B) dμ_w = ∫_E φ dμ_{w_B}`. [folklore] -/
theorem setIntegral_preimage_sdiff_prodBernoulli [Fintype V] (w : Sym2 V → unitInterval) (B : Set (Sym2 V))
    (E : Set (BondConfig V)) (φ : BondConfig V → ℝ) :
    ∫ ω in (· \ B) ⁻¹' E, φ (ω \ B) ∂(prodBernoulli w) =
      ∫ ω in E, φ ω ∂(prodBernoulli fun e => if e ∈ B then 0 else w e) := by
  classical
  rw [← integral_indicator (MeasurableSet.of_discrete : MeasurableSet ((· \ B) ⁻¹' E)),
    ← integral_indicator (MeasurableSet.of_discrete : MeasurableSet E)]
  have h : (fun ω => ((· \ B) ⁻¹' E).indicator (fun ω => φ (ω \ B)) ω) =
      fun ω => (E.indicator φ) (ω \ B) := by
    funext ω
    simp only [Set.indicator, Set.mem_preimage]
  rw [h, integral_comp_sdiff_prodBernoulli w B (E.indicator φ)]

end HullPort

end Percolation.Continuity
