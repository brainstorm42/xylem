import Percolation.Literature.InequalitiesProofs
import Percolation.Literature.LatticeModels.ProdBernoulliIndependence
import Percolation.Util.Linter

/-!
# The BK inequality for inhomogeneous product Bernoulli measures

Proofs-only companion of `Percolation.Literature.LatticeModels.prodBernoulli`
(`Literature/LatticeModels/ProdBernoulli.lean`). This file transports it to `prodBernoulli p` on
`Set ι` for an arbitrary index type `ι` and coordinate-dependent parameters `p : ι → [0,1]` — the
form needed for long-range percolation with edge weights `p_e = 1 - e^{-β J_e}` (Hutchcroft 2021,
proof of Thm. 2.3: "The van den Berg and Kesten inequality … if `G = (V,E,J)` is a finite weighted
graph and `A₁, …, A_k` are increasing events then `ℙ_β(A₁ ∘ ⋯ ∘ A_k) ≤ ∏ ℙ_β(A_i)`") and for
labelled configuration spaces `Set (ι × Fin 2)`:

* `prodBernoulli_real_eq_sum_cube` — finite-dimensional distributions: for `C` determined by the
  finite set `F`, `P(C) = Σ_{a : F → Bool} 𝟙[pattern a ∈ C] ∏_{i : F} w_i(a_i)` with
  `w_i(true) = p_i`, `w_i(false) = 1 - p_i`;

## References

* J. van den Berg, H. Kesten, *Inequalities with applications to percolation and reliability*,
  J. Appl. Probab. 22 (1985) 556–569 (BK inequality for product measures).
* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §2.3: Thm. (2.12), (2.14), (2.17).
* T. Hutchcroft, *Power-law bounds for critical long-range percolation below the upper-critical
  dimension*, Probab. Theory Related Fields 181 (2021), arXiv:2008.11197, proof of Thm. 2.3.
-/

noncomputable section

namespace Percolation.Literature.LatticeModels

open MeasureTheory Measure ProbabilityTheory Percolation.Literature
open scoped ENNReal

variable {ι : Type*}

/-! ### Finite-dimensional distributions in cube form -/

/-- The `prodBernoulli p`-probability of the cylinder of configurations with pattern `a` on the
finite set `F` is `∏_{i : F} w_i(a_i)`, `w_i(true) = p_i`, `w_i(false) = 1 - p_i`.
[cite: GrimmettPercolation1999, §1.3 p. 10 (product measure)] -/
theorem prodBernoulli_real_cylinder_pattern (p : ι → unitInterval) (F : Finset ι) (a : F → Bool) :
    (prodBernoulli p).real {ω : Set ι | ∀ (i) (h : i ∈ F), i ∈ ω ↔ a ⟨i, h⟩ = true} =
      ∏ i : F, (if a i = true then ((p i : unitInterval) : ℝ) else 1 - ((p i : unitInterval) : ℝ)) := by
  classical
  set t : ι → Set Prop := fun i => {r | r ↔ (if h : i ∈ F then a ⟨i, h⟩ else false) = true}
  have hpre : (fun q : ι → Prop => {i | q i}) ⁻¹'
      {ω : Set ι | ∀ (i) (h : i ∈ F), i ∈ ω ↔ a ⟨i, h⟩ = true} = Set.pi (↑F) t := by
    ext q
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_pi, Finset.mem_coe, t]
    constructor
    · intro h i hi; rw [dif_pos hi]; exact h i hi
    · intro h i hi; have := h i hi; rwa [dif_pos hi] at this
  rw [prodBernoulli_real_eq_infinitePi, measureReal_def, hpre,
    Measure.infinitePi_pi _ (fun _ _ => MeasurableSet.of_discrete), ENNReal.toReal_prod,
    ← Finset.prod_attach]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hi : (i : ι) ∈ F := i.2
  by_cases ha : a i = true
  · have hset : t i = {True} := by
      ext r
      simp only [t, Set.mem_setOf_eq, Set.mem_singleton_iff, dif_pos hi, Subtype.coe_eta, ha,
        iff_true, eq_iff_iff]
    rw [hset, bernoulliMeasure_prop_apply_true, if_pos ha, ENNReal.toReal_ofReal (p i).2.1]
  · have hset : t i = {False} := by
      ext r
      simp only [Bool.not_eq_true] at ha
      simp only [t, Set.mem_setOf_eq, Set.mem_singleton_iff, dif_pos hi, Subtype.coe_eta, ha,
        Bool.false_eq_true, iff_false, eq_iff_iff]
    rw [hset, bernoulliMeasure_prop_apply_false, if_neg ha,
      ENNReal.toReal_ofReal (sub_nonneg.2 (p i).2.2)]

open Classical in
/-- **Finite-dimensional distributions of `prodBernoulli p` in cube form.** For an event `C`
determined by the finite set `F`, `P(C) = Σ_{a : F → Bool} 𝟙[{i ∈ F | a_i} ∈ C] ∏_{i : F} w_i(a_i)`:
the cylinders over `F` partition the space and `C` is the union of those whose pattern lies in
`C`. (Grimmett 1999, §2.2.) [cite: GrimmettPercolation1999, §2.2] -/
theorem prodBernoulli_real_eq_sum_cube (p : ι → unitInterval) (F : Finset ι) {C : Set (Set ι)}
    (hC : DeterminedBy C (↑F : Set ι)) :
    (prodBernoulli p).real C =
      ∑ a : F → Bool, ({a : F → Bool | {i : ι | ∃ h : i ∈ F, a ⟨i, h⟩ = true} ∈ C}).indicator
        (fun a => ∏ i : F,
          (if a i = true then ((p i : unitInterval) : ℝ) else 1 - ((p i : unitInterval) : ℝ))) a := by
  classical
  -- the cylinders and patterns over `F`
  set cyl : (F → Bool) → Set (Set ι) :=
    fun a => {ω | ∀ (i) (h : i ∈ F), i ∈ ω ↔ a ⟨i, h⟩ = true} with hcyl
  set cfg : (F → Bool) → Set ι := fun a => {i | ∃ h : i ∈ F, a ⟨i, h⟩ = true} with hcfg
  have hCeq : C = ⋃ a ∈ (Finset.univ.filter fun a : F → Bool => cfg a ∈ C), cyl a := by
    rw [determinedBy_iff] at hC
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_iUnion, exists_prop]
    constructor
    · intro hω
      refine ⟨fun i => decide ((i : ι) ∈ ω), ?_, ?_⟩
      · refine (hC ω _ ?_).1 hω
        ext i
        simp only [Set.mem_inter_iff, Finset.mem_coe, hcfg, Set.mem_setOf_eq, decide_eq_true_eq]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨⟨h2, h1⟩, h2⟩
        · rintro ⟨⟨h2, h1⟩, -⟩; exact ⟨h1, h2⟩
      · intro i hi; simp
    · rintro ⟨a, haC, hω⟩
      refine (hC ω (cfg a) ?_).2 haC
      ext i
      simp only [Set.mem_inter_iff, Finset.mem_coe, hcfg, Set.mem_setOf_eq]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨⟨h2, (hω i h2).1 h1⟩, h2⟩
      · rintro ⟨⟨h2, h1⟩, -⟩; exact ⟨(hω i h2).2 h1, h2⟩
  have hdisj : Set.PairwiseDisjoint
      (↑(Finset.univ.filter fun a : F → Bool => cfg a ∈ C) : Set (F → Bool)) cyl := by
    intro a _ b _ hab
    rw [Function.onFun, Set.disjoint_left]
    intro ω ha hb
    apply hab
    funext i
    have h1 := ha i i.2
    have h2 := hb i i.2
    simp only [Subtype.coe_eta] at h1 h2
    rw [Bool.eq_iff_iff, ← h1, ← h2]
  have hmeas : ∀ a : F → Bool, MeasurableSet (cyl a) := by
    intro a
    have : cyl a = ⋂ i : F, {ω : Set ι | (i : ι) ∈ ω ↔ a i = true} := by
      ext ω; simp only [hcyl, Set.mem_setOf_eq, Set.mem_iInter, Subtype.forall]
    rw [this]
    refine MeasurableSet.iInter fun i => ?_
    by_cases h : a i = true
    · simpa [h] using measurableSet_mem (i : ι)
    · simpa [h] using measurableSet_notMem (i : ι)
  conv_lhs => rw [hCeq]
  rw [measureReal_biUnion_finset hdisj (fun a _ => hmeas a), Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : cfg a ∈ C
  · rw [if_pos h, Set.indicator_of_mem (show a ∈ {a : F → Bool | cfg a ∈ C} from h)]
    exact prodBernoulli_real_cylinder_pattern p F a
  · rw [if_neg h, Set.indicator_of_notMem (show a ∉ {a : F → Bool | cfg a ∈ C} from h)]

end Percolation.Literature.LatticeModels
