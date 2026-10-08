import Mathlib.Probability.Distributions.Bernoulli
import Percolation.Literature.LatticeModels.ProdBernoulli
import Percolation.Literature.LocallyMonotoneFKG
import Percolation.Literature.PercolationEvents
import Percolation.Util.Linter

/-!
# Independence, cylinder probabilities and Harris' inequality for `prodBernoulli`

proofs-only companion of
`Percolation.Literature.LatticeModels.prodBernoulli` (`Literature/LatticeModels/ProdBernoulli.lean`): the product
of Bernoulli laws with coordinate-dependent parameters `p : ι → [0, 1]` on `Set ι` (each `i`
belongs to the random set independently with probability `p i`; Grimmett, *Percolation*, 2nd ed.
1999, §1.3 p. 10, `P = ∏_e μ_e`, here with `μ_e = Bernoulli(p_e)`). Everything below is the
standard product-measure toolkit, transported from Mathlib's `Measure.infinitePi` on `ι → Prop`
along the measurable equivalence `MeasurableEquiv.setOf : (ι → Prop) ≃ᵐ Set ι`
(`prodBernoulli_eq_map`); the
constant-parameter versions for `bondPercolation G p = setBer(E(G), p)` are in
`Percolation/BernoulliPercolation.lean`, `Percolation/FiniteEnergy.lean` and
`Percolation/HarrisLocal.lean`, whose statements are followed.

## Contents (all proved)

* the one-coordinate factor is Mathlib's `Ber(True, False, p i)`
  (`ProbabilityTheory.bernoulliMeasure`; `= p i • δ_True + (1 - p i) • δ_False` by `rfl`), its
  values on `{True}` / `{False}`, and `prodBernoulli_apply_eq_infinitePi`:
  `prodBernoulli p S = (⨂ᵢ Ber(True, False, p i)) (setOf ⁻¹' S)` for every `S`;
* `prodBernoulli_real_inter_of_determinedBy` — an event determined by a finite set `F` of
  coordinates and one determined by `Fᶜ` are independent (`P(A ∩ B) = P(A) P(B)`), with the
  two-finite-sets variant and the iterated form `prodBernoulli_real_inter_biInter_of_determinedBy`
  (`P(A ∩ ⋂ₖ Cₖ) = P(A) ∏ₖ P(Cₖ)` for `Cₖ` determined by pairwise disjoint finite sets `Sₖ` and
  `A` determined by the complement of their union — the "conditional independence given an
  exploration" identity in finitary form);

## References

* G. R. Grimmett, *Percolation*, 2nd ed., Springer 1999: §1.3 p. 10 (product measure),
  §2.2 (events depending on finitely many edges), Thm. (2.4) p. 34 (Harris–FKG).
* T. E. Harris, *A lower bound for the critical probability in a certain percolation process*,
  Proc. Camb. Phil. Soc. 56 (1960), Lemma 4.1.
-/

noncomputable section

namespace Percolation.Literature.LatticeModels

open MeasureTheory Measure ProbabilityTheory Filter Percolation.Literature
open scoped ENNReal Topology

variable {ι : Type*}

/-! ### The one-coordinate factor and the transport along `setOf` -/

/-- The `i`-th factor of `prodBernoulli p` is Mathlib's Bernoulli law `Ber(True, False, p i)`
on `Prop` (`ProbabilityTheory.bernoulliMeasure`); it shows `True` with probability `q`.
(Grimmett 1999, §1.3 p. 10: "`μ_e(ω(e) = 1) = p(e)`".) [cite: GrimmettPercolation1999, §1.3 p. 10] -/
theorem bernoulliMeasure_prop_apply_true (q : unitInterval) :
    Ber(True, False, q) {True} = ENNReal.ofReal q := by
  rw [ENNReal.ofReal_eq_coe_nnreal q.2.1]
  simp [bernoulliMeasure_def]
  rfl

/-- The coin shows `False` with probability `1 - q`. [cite: GrimmettPercolation1999, §1.3 p. 10] -/
theorem bernoulliMeasure_prop_apply_false (q : unitInterval) :
    Ber(True, False, q) {False} = ENNReal.ofReal (1 - q) := by
  rw [ENNReal.ofReal_eq_coe_nnreal (sub_nonneg.2 q.2.2)]
  simp [bernoulliMeasure_def]
  rfl

/-- Every event has the `prodBernoulli`-probability of its pull-back to `ι → Prop` under the
product of the Bernoulli laws (no measurability needed: `setOf` is a measurable equivalence).
[cite: GrimmettPercolation1999, §1.3 p. 10] -/
theorem prodBernoulli_apply_eq_infinitePi (p : ι → unitInterval) (S : Set (Set ι)) :
    prodBernoulli p S =
      infinitePi (fun i => Ber(True, False, p i)) ((fun q : ι → Prop => {i | q i}) ⁻¹' S) := by
  rw [prodBernoulli_eq_map]
  exact MeasurableEquiv.setOf.map_apply S

/-- Real-valued form of `prodBernoulli_apply_eq_infinitePi`. [cite: GrimmettPercolation1999, §1.3 p. 10] -/
theorem prodBernoulli_real_eq_infinitePi (p : ι → unitInterval) (S : Set (Set ι)) :
    (prodBernoulli p).real S =
      (infinitePi fun i => Ber(True, False, p i)).real ((fun q : ι → Prop => {i | q i}) ⁻¹' S) := by
  simp only [measureReal_def, prodBernoulli_apply_eq_infinitePi]

/-! ### Independence of the coordinates and cylinder probabilities -/

/-- **All coordinates of a finite set `F` are absent with probability `∏_{i ∈ F} (1 - p i)`.**
(Grimmett 1999, §1.3 p. 10, product measure.) [cite: GrimmettPercolation1999, §1.3 p. 10] -/
theorem prodBernoulli_real_forall_notMem (p : ι → unitInterval) (F : Finset ι) :
    (prodBernoulli p).real {ω | ∀ i ∈ F, i ∉ ω} = ∏ i ∈ F, (1 - (p i : ℝ)) := by
  classical
  have hpre : (fun q : ι → Prop => {i | q i}) ⁻¹' {ω : Set ι | ∀ i ∈ F, i ∉ ω}
      = Set.pi (F : Set ι) (fun _ => {False}) := by
    ext q
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_pi, Finset.mem_coe,
      Set.mem_singleton_iff, eq_iff_iff, iff_false]
  rw [prodBernoulli_real_eq_infinitePi, measureReal_def, hpre,
    infinitePi_pi _ (fun _ _ => MeasurableSet.of_discrete), ENNReal.toReal_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [bernoulliMeasure_prop_apply_false, ENNReal.toReal_ofReal (sub_nonneg.2 (p i).2.2)]

/-- **All coordinates of a finite set `F` are present with probability `∏_{i ∈ F} p i`.**
(Grimmett 1999, §1.3 p. 10.) [cite: GrimmettPercolation1999, §1.3 p. 10] -/
theorem prodBernoulli_real_subset (p : ι → unitInterval) (F : Finset ι) :
    (prodBernoulli p).real {ω | (F : Set ι) ⊆ ω} = ∏ i ∈ F, (p i : ℝ) := by
  classical
  have hpre : (fun q : ι → Prop => {i | q i}) ⁻¹' {ω : Set ι | (F : Set ι) ⊆ ω}
      = Set.pi (F : Set ι) (fun _ => {True}) := by
    ext q
    simp [Set.subset_def, Set.mem_pi]
  rw [prodBernoulli_real_eq_infinitePi, measureReal_def, hpre,
    infinitePi_pi _ (fun _ _ => MeasurableSet.of_discrete), ENNReal.toReal_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [bernoulliMeasure_prop_apply_true, ENNReal.toReal_ofReal (p i).2.1]

/-- One-coordinate marginal: `P(i ∈ ω) = p i`. [cite: GrimmettPercolation1999, §1.3 p. 10] -/
theorem prodBernoulli_real_setOf_mem (p : ι → unitInterval) (i : ι) :
    (prodBernoulli p).real {ω | i ∈ ω} = p i := by
  simpa using prodBernoulli_real_subset p {i}

/-- One-coordinate marginal: `P(i ∉ ω) = 1 - p i`. [cite: GrimmettPercolation1999, §1.3 p. 10] -/
theorem prodBernoulli_real_setOf_notMem (p : ι → unitInterval) (i : ι) :
    (prodBernoulli p).real {ω | i ∉ ω} = 1 - p i := by
  simpa using prodBernoulli_real_forall_notMem p {i}

/-- **Union bound**: some coordinate of the finite set `F` is present with probability at most
`∑_{i ∈ F} p i`. [folklore] -/
theorem prodBernoulli_real_exists_mem_le_sum (p : ι → unitInterval) (F : Finset ι) :
    (prodBernoulli p).real {ω | ∃ i ∈ F, i ∈ ω} ≤ ∑ i ∈ F, (p i : ℝ) := by
  have hU : {ω : Set ι | ∃ i ∈ F, i ∈ ω} = ⋃ i ∈ F, {ω | i ∈ ω} := by ext ω; simp
  rw [hU]
  refine le_trans (measureReal_biUnion_finset_le F _) (Finset.sum_le_sum fun i _ => ?_)
  rw [prodBernoulli_real_setOf_mem]

/-- The event "all coordinates of `F` are absent" is measurable (`F` countable). [folklore] -/
theorem measurableSet_forall_notMem_of_countable {T : Set ι} (hT : T.Countable) :
    MeasurableSet {ω : Set ι | ∀ i ∈ T, i ∉ ω} := by
  have : {ω : Set ι | ∀ i ∈ T, i ∉ ω} = ⋂ i ∈ T, {ω | i ∉ ω} := by ext ω; simp
  rw [this]
  exact MeasurableSet.biInter hT fun i _ => measurableSet_notMem i

/-! ### Independence of events determined by disjoint sets of coordinates -/

/-- **An event determined by the finite set `F` of coordinates and an event determined by `Fᶜ`
are independent under `prodBernoulli p`**: `P(A ∩ B) = P(A) P(B)` (Grimmett 1999, §2.2;
transport of `infinitePi_real_inter_of_dependsOn`). [cite: GrimmettPercolation1999, §2.2] -/
theorem prodBernoulli_real_inter_of_determinedBy (p : ι → unitInterval) (F : Finset ι)
    {A B : Set (Set ι)} (hA : DeterminedBy A (↑F : Set ι)) (hB : DeterminedBy B (↑F : Set ι)ᶜ)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) :
    (prodBernoulli p).real (A ∩ B) = (prodBernoulli p).real A * (prodBernoulli p).real B := by
  classical
  simp only [prodBernoulli_real_eq_infinitePi, Set.preimage_inter]
  exact infinitePi_real_inter_of_dependsOn _ F hA hB (measurable_setOf hAm) (measurable_setOf hBm)

/-- Variant for two disjoint finite sets of coordinates. [cite: GrimmettPercolation1999, §2.2] -/
theorem prodBernoulli_real_inter_of_determinedBy_disjoint (p : ι → unitInterval) {F F' : Finset ι}
    (hFF' : Disjoint F F') {A B : Set (Set ι)} (hA : DeterminedBy A (↑F : Set ι))
    (hB : DeterminedBy B (↑F' : Set ι)) (hAm : MeasurableSet A) (hBm : MeasurableSet B) :
    (prodBernoulli p).real (A ∩ B) = (prodBernoulli p).real A * (prodBernoulli p).real B := by
  refine prodBernoulli_real_inter_of_determinedBy p F hA (hB.mono fun i hi hiF => ?_) hAm hBm
  exact Finset.disjoint_left.1 hFF' (Finset.mem_coe.1 hiF) (Finset.mem_coe.1 hi)

/-- **Iterated independence over pairwise disjoint finite supports.** If the events `C k`
(`k ∈ s`) are determined by pairwise disjoint finite sets `S k` of coordinates and `A` is
determined by the complement of `⋃_{k ∈ s} S k`, then
`P(A ∩ ⋂_{k ∈ s} C k) = P(A) ∏_{k ∈ s} P(C k)`. This is the finitary form of "conditionally on
everything outside the `S k`, the events `C k` are independent with their unconditional
probabilities" (Grimmett 1999, §2.2). [cite: GrimmettPercolation1999, §2.2] -/
theorem prodBernoulli_real_inter_biInter_of_determinedBy {κ : Type*} (p : ι → unitInterval)
    (s : Finset κ) (S : κ → Finset ι) (hS : (s : Set κ).PairwiseDisjoint S)
    {C : κ → Set (Set ι)} (hC : ∀ k ∈ s, DeterminedBy (C k) (↑(S k) : Set ι))
    (hCm : ∀ k ∈ s, MeasurableSet (C k)) {A : Set (Set ι)}
    (hA : DeterminedBy A (⋃ k ∈ s, (↑(S k) : Set ι))ᶜ) (hAm : MeasurableSet A) :
    (prodBernoulli p).real (A ∩ ⋂ k ∈ s, C k) =
      (prodBernoulli p).real A * ∏ k ∈ s, (prodBernoulli p).real (C k) := by
  classical
  induction s using Finset.induction_on generalizing A with
  | empty => simp
  | insert a s ha ih =>
    have hs : ∀ k ∈ s, k ∈ insert a s := fun k hk => Finset.mem_insert_of_mem hk
    have hdisj : ∀ k ∈ s, Disjoint (S a) (S k) := fun k hk =>
      hS (Finset.mem_coe.2 (Finset.mem_insert_self a s)) (Finset.mem_coe.2 (hs k hk))
        (fun h => ha (h ▸ hk))
    -- peel off `C a`: `A ∩ ⋂_{k ∈ s} C k` is determined by the complement of `S a`
    have hrest : DeterminedBy (A ∩ ⋂ k ∈ s, C k) (↑(S a) : Set ι)ᶜ := by
      refine DeterminedBy.inter (hA.mono fun i hi hi' => hi ?_) ?_
      · exact Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_insert_self a s)) hi'
      · rw [determinedBy_iff]
        intro ω ω' hω
        simp only [Set.mem_iInter]
        refine forall₂_congr fun k hk => (determinedBy_iff _ _).1 (hC k (hs k hk)) ω ω' ?_
        have hsub : (↑(S k) : Set ι) ⊆ (↑(S a) : Set ι)ᶜ := fun i hi hia =>
          Finset.disjoint_left.1 (hdisj k hk) (Finset.mem_coe.1 hia) (Finset.mem_coe.1 hi)
        rw [← Set.inter_eq_self_of_subset_right hsub, ← Set.inter_assoc, ← Set.inter_assoc, hω]
    have hrestm : MeasurableSet (A ∩ ⋂ k ∈ s, C k) :=
      hAm.inter (Finset.measurableSet_biInter s fun k hk => hCm k (hs k hk))
    rw [Finset.set_biInter_insert, Finset.prod_insert ha, ← Set.inter_assoc,
      Set.inter_comm A (C a), Set.inter_assoc,
      prodBernoulli_real_inter_of_determinedBy p (S a) (hC a (Finset.mem_insert_self a s)) hrest
        (hCm a (Finset.mem_insert_self a s)) hrestm,
      ih (fun x hx y hy hxy => hS (Finset.mem_coe.2 (hs x hx)) (Finset.mem_coe.2 (hs y hy)) hxy)
        (fun k hk => hC k (hs k hk)) (fun k hk => hCm k (hs k hk)) ?_ hAm]
    · ring
    · refine hA.mono (Set.compl_subset_compl.2 fun i hi => ?_)
      obtain ⟨k, hk, hik⟩ := Set.mem_iUnion₂.1 hi
      exact Set.mem_biUnion (Finset.mem_coe.2 (hs k (Finset.mem_coe.1 hk))) hik

/-! ### Harris' inequality -/

/-- Harris' inequality for two decreasing events: `P(A) P(B) ≤ P(A ∩ B)`.
[cite: GrimmettPercolation1999, Thm. (2.4) p. 34] -/
theorem prodBernoulli_harris_lower (p : ι → unitInterval) {A B : Set (Set ι)} (hA : IsLowerSet A)
    (hB : IsLowerSet B) (hAm : MeasurableSet A) (hBm : MeasurableSet B) :
    (prodBernoulli p).real A * (prodBernoulli p).real B ≤ (prodBernoulli p).real (A ∩ B) := by
  simp only [prodBernoulli_real_eq_infinitePi, Set.preimage_inter]
  exact infinitePi_harris_lower _ (hA.preimage fun _ _ h => h) (hB.preimage fun _ _ h => h)
    (measurable_setOf hAm) (measurable_setOf hBm)

/-- Harris' inequality for an increasing and a decreasing event: `P(A ∩ B) ≤ P(A) P(B)`.
[cite: GrimmettPercolation1999, Thm. (2.4) p. 34] -/
theorem prodBernoulli_harris_upper_lower (p : ι → unitInterval) {A B : Set (Set ι)}
    (hA : IsUpperSet A) (hB : IsLowerSet B) (hAm : MeasurableSet A) (hBm : MeasurableSet B) :
    (prodBernoulli p).real (A ∩ B) ≤ (prodBernoulli p).real A * (prodBernoulli p).real B := by
  simp only [prodBernoulli_real_eq_infinitePi, Set.preimage_inter]
  exact infinitePi_harris_upper_lower _ (hA.preimage fun _ _ h => h)
    (hB.preimage fun _ _ h => h) (measurable_setOf hAm) (measurable_setOf hBm)

end Percolation.Literature.LatticeModels
