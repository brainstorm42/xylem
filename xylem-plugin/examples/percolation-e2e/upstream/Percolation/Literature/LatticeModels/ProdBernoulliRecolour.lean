import Percolation.Literature.LatticeModels.ProdBernoulliIndependence
import Percolation.Util.Linter

/-!
# Finite energy with a reconstructible modification site (Bollobás–Riordan's recolouring step)

Companion of `prodBernoulli`
(`ProdBernoulliIndependence.lean`).

Bollobás–Riordan, *Percolation on self-dual polygon configurations* (2010, arXiv:1001.4674), §5.2,
end of the proof of Theorem 5.12 (p. 29): to join a translated path to the two explored interfaces
they "adjust the colourings of at most two faces"; the adjusted configuration has probability at
least `p₀²` times the original one, and "given some `(ω̃, ω₂, v) ∈ E'` known to be the image of some
unknown `(ω₁, ω₂, v)` under `g`, we can read off … which two (or at most two) faces were recoloured,
though not how. It follows that `g⁻¹({(ω̃, ω₂, v)})` consists of a bounded number of configurations,
each of whose probabilities is at most `p₀⁻²` times that of `(ω̃, ω₂, v)`.

## References

* B. Bollobás, O. Riordan, *Percolation on self-dual polygon configurations*, Bolyai Soc. Math.
  Stud. 21 (2010) 131–217, arXiv:1001.4674, §5.2, proof of Thm. 5.12 (the map `g : E → Ω² × 𝓛`,
  "`Pr(E') ≥ Pr(E)/C`"). [BollobasRiordan2010]
* G. R. Grimmett, *Percolation*, 2nd ed., Springer (1999), §2.2 (finite energy / local
  modification). [GrimmettPercolation1999]
-/

noncomputable section

namespace Percolation.Literature.LatticeModels

open _root_.MeasureTheory Measure ProbabilityTheory Percolation.Literature
open scoped ENNReal

variable {ι : Type*}

/-! ### Cylinder probabilities -/

section Cylinder

variable (p : ι → unitInterval)

/-- **Cylinder probabilities**: `μ([P]_K) = ∏_{i ∈ K, i ∈ P} p i · ∏_{i ∈ K, i ∉ P} (1 - p i)`.
(Grimmett 1999, §1.3, product measure.) [cite: GrimmettPercolation1999, §1.3 p. 10] -/
theorem prodBernoulli_real_localCylinder [DecidableEq ι] (K : Finset ι) (P : Set ι) [DecidablePred (· ∈ P)] :
    (prodBernoulli p).real (localCylinder (↑K : Set ι) P) =
      (∏ i ∈ K.filter (· ∈ P), (p i : ℝ)) * ∏ i ∈ K.filter (· ∉ P), (1 - (p i : ℝ)) := by
  have hsplit : localCylinder (↑K : Set ι) P =
      {ω : Set ι | ↑(K.filter (· ∈ P)) ⊆ ω} ∩ {ω | ∀ i ∈ K.filter (· ∉ P), i ∉ ω} := by
    ext ω
    simp only [localCylinder, Set.mem_setOf_eq, Finset.mem_coe, Set.mem_inter_iff, Set.subset_def,
      Finset.coe_filter, Finset.mem_filter]
    constructor
    · intro h
      exact ⟨fun i hi => (h i hi.1).2 hi.2, fun i hi hω => hi.2 ((h i hi.1).1 hω)⟩
    · rintro ⟨h₁, h₂⟩ i hi
      by_cases hP : i ∈ P
      · exact ⟨fun _ => hP, fun _ => h₁ i ⟨hi, hP⟩⟩
      · exact ⟨fun hω => absurd hω (h₂ i ⟨hi, hP⟩), fun h => absurd h hP⟩
  have hA : DeterminedBy {ω : Set ι | ↑(K.filter (· ∈ P)) ⊆ ω} ↑(K.filter (· ∈ P)) := by
    rw [determinedBy_iff]
    intro ω ω' hω
    simp only [Set.mem_setOf_eq, Set.subset_def]
    refine forall₂_congr fun i hi => ?_
    exact ⟨fun h => ((Set.ext_iff.1 hω i).1 ⟨h, hi⟩).1, fun h => ((Set.ext_iff.1 hω i).2 ⟨h, hi⟩).1⟩
  have hB : DeterminedBy {ω : Set ι | ∀ i ∈ K.filter (· ∉ P), i ∉ ω} ↑(K.filter (· ∉ P)) := by
    rw [determinedBy_iff]
    intro ω ω' hω
    simp only [Set.mem_setOf_eq]
    refine forall₂_congr fun i hi => not_congr ?_
    exact ⟨fun h => ((Set.ext_iff.1 hω i).1 ⟨h, Finset.mem_coe.2 hi⟩).1,
      fun h => ((Set.ext_iff.1 hω i).2 ⟨h, Finset.mem_coe.2 hi⟩).1⟩
  have hdisj : Disjoint (K.filter (· ∈ P)) (K.filter (· ∉ P)) :=
    Finset.disjoint_filter_filter_not K K (· ∈ P)
  rw [hsplit, prodBernoulli_real_inter_of_determinedBy_disjoint p hdisj hA hB
    hA.measurableSet_of_finset hB.measurableSet_of_finset, prodBernoulli_real_subset,
    prodBernoulli_real_forall_notMem]

end Cylinder

end Percolation.Literature.LatticeModels
