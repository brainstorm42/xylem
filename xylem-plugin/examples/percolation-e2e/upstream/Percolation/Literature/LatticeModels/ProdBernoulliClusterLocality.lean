import Percolation.Literature.LatticeModels.ProdBernoulliCoupling
import Percolation.Literature.LatticeModels.ProdBernoulliIndependence
import Percolation.Literature.PercolationProofs
import Percolation.Util.Linter

/-!
# Cluster locality for inhomogeneous product Bernoulli measures

proofs-only companion of `prodBernoulli`
(`Literature/LatticeModels/ProdBernoulli.lean`, `ProdBernoulliIndependence.lean`,
`ProdBernoulliCoupling.lean`): how the law of the open cluster of a vertex under `prodBernoulli p`
(each pair `e : Sym2 V` open independently with probability `p e`) depends on the parameters.
Everything is the standard product-measure toolkit (Grimmett, *Percolation*, 2nd ed. 1999, §1.3,
§2.2), written for coordinate-dependent parameters; used by the sign-symmetry argument for the level
sets of the cable-system Gaussian free field.

## Contents (all proved)

* `prodBernoulli_apply_eq_of_determinedBy` (+ `_real_`) — two parameter functions agreeing on `F`
  give the same probability to every event determined by `F` (both are laws of `{i | U_i ≤ p_i}`
  under i.i.d. uniform labels, `prodBernoulli_eq_map_labels`);
* `prodBernoulli_ae_notMem`, `prodBernoulli_ae_forall_notMem` — coordinates with parameter `0` are
  a.s. absent;

The factorisation of `μ{C(x) = K}` into an inside part and the closed edge boundary is in the
sequel.
-/

noncomputable section

namespace Percolation.Literature.LatticeModels

open _root_.MeasureTheory _root_.ProbabilityTheory Percolation.Literature Filter
open scoped ENNReal

section General

variable {ι : Type*}

/-- **Two product Bernoulli measures whose parameters agree on `F` agree on every event determined
by `F`.** Proof: both are laws of `{i | U_i ≤ p_i}` under i.i.d. uniform labels
(`prodBernoulli_eq_map_labels`), and these random sets have the same trace on `F`.
(Grimmett 1999, §1.3 p. 11, the simultaneous coupling.) [cite: GrimmettPercolation1999, §1.3 p. 11] -/
theorem prodBernoulli_apply_eq_of_determinedBy (p q : ι → unitInterval) {F : Set ι}
    (hpq : ∀ i ∈ F, p i = q i) {A : Set (Set ι)} (hA : DeterminedBy A F) (hAm : MeasurableSet A) :
    prodBernoulli p A = prodBernoulli q A := by
  have hmeas : ∀ r : ι → unitInterval, Measurable fun U : ι → ℝ => {i | U i ≤ (r i : ℝ)} :=
    fun r => measurable_set_iff.2 fun i =>
      (show Measurable fun t : ℝ => (t ≤ (r i : ℝ)) from
        measurableSet_setOf.1 measurableSet_Iic).comp (measurable_pi_apply i)
  rw [prodBernoulli_eq_map_labels p, prodBernoulli_eq_map_labels q,
    Measure.map_apply (hmeas p) hAm, Measure.map_apply (hmeas q) hAm]
  congr 1
  ext U
  simp only [Set.mem_preimage]
  refine (determinedBy_iff A F).1 hA _ _ ?_
  ext i
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h, hi⟩; exact ⟨by rw [← hpq i hi]; exact h, hi⟩
  · rintro ⟨h, hi⟩; exact ⟨by rw [hpq i hi]; exact h, hi⟩

/-- Real-valued form of `prodBernoulli_apply_eq_of_determinedBy`. [cite: GrimmettPercolation1999, §1.3 p. 11] -/
theorem prodBernoulli_real_eq_of_determinedBy (p q : ι → unitInterval) {F : Set ι}
    (hpq : ∀ i ∈ F, p i = q i) {A : Set (Set ι)} (hA : DeterminedBy A F) (hAm : MeasurableSet A) :
    (prodBernoulli p).real A = (prodBernoulli q).real A := by
  simp only [measureReal_def, prodBernoulli_apply_eq_of_determinedBy p q hpq hA hAm]

/-- A coordinate with parameter `0` is almost surely absent. [cite: GrimmettPercolation1999, §1.3 p. 10] -/
theorem prodBernoulli_ae_notMem (p : ι → unitInterval) {i : ι} (hi : p i = 0) :
    ∀ᵐ ω ∂prodBernoulli p, i ∉ ω := by
  rw [ae_iff]
  simp only [not_not]
  have h := prodBernoulli_real_setOf_mem p i
  rw [hi] at h
  have : (prodBernoulli p).real {ω | i ∈ ω} = 0 := by simpa using h
  exact (measureReal_eq_zero_iff (measure_ne_top _ _)).1 this

/-- All coordinates of a countable family with parameter `0` are almost surely absent.
[cite: GrimmettPercolation1999, §1.3 p. 10] -/
theorem prodBernoulli_ae_forall_notMem (p : ι → unitInterval) {Z : Set ι} (hZ : Z.Countable)
    (hp : ∀ i ∈ Z, p i = 0) : ∀ᵐ ω ∂prodBernoulli p, ∀ i ∈ Z, i ∉ ω := by
  have : Countable Z := hZ.to_subtype
  have h : ∀ i : Z, ∀ᵐ ω ∂prodBernoulli p, (i : ι) ∉ ω := fun i =>
    prodBernoulli_ae_notMem p (hp i i.2)
  filter_upwards [ae_all_iff.2 h] with ω hω i hi using hω ⟨i, hi⟩

end General

end Percolation.Literature.LatticeModels

end
