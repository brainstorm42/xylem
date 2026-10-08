import Percolation.Literature.LatticeModels.ProdBernoulliIndependence
import Percolation.Util.Linter

/-!
# Atom expansion of `prodBernoulli` over four coordinates

proofs-only companion of
`Percolation.Literature.LatticeModels.prodBernoulli` (`Literature/LatticeModels/ProdBernoulli.lean`) and of
`ProdBernoulliIndependence.lean` / `ProdBernoulliBK.lean` (`prodBernoulli_real_eq_sum_cube`, the
finite-dimensional distributions in cube form, indexed by patterns `F → Bool`).  For EXACT
evaluation of probabilities on small weighted graphs (explicit counterexamples) one wants the same
bookkeeping in a form that `norm_num` can close: an iterated sum over `Bool` with the event read
off through an explicit propositional function of finitely many named coordinates.  Contents
(all proved; Grimmett, *Percolation*, 2nd ed. 1999, §1.3 p. 10 — the product measure — and §2.2 —
events depending on finitely many coordinates):

* `prodBernoulli_real_setOf_forall_iff` — cylinders with PRESCRIBED truth values:
  `P(∀ i ∈ F, (i ∈ ω ↔ γ i)) = ∏_{i ∈ F} (p i if γ i, else 1 - p i)` (predicate form of
  `prodBernoulli_real_cylinder_pattern`);
-/

noncomputable section

namespace Percolation.Literature.LatticeModels

open MeasureTheory Measure ProbabilityTheory
open scoped ENNReal

variable {ι : Type*}

open Classical in
/-- **Cylinders with prescribed truth values.** For a finite set `F` of coordinates and a
predicate `γ`, `P(∀ i ∈ F, (i ∈ ω ↔ γ i)) = ∏_{i ∈ F} (γ i ? p i : 1 - p i)` (product measure;
predicate form of `prodBernoulli_real_cylinder_pattern`). [cite: GrimmettPercolation1999, §1.3 p. 10] -/
theorem prodBernoulli_real_setOf_forall_iff (p : ι → unitInterval) (F : Finset ι) (γ : ι → Prop) :
    (prodBernoulli p).real {ω | ∀ i ∈ F, (i ∈ ω ↔ γ i)} =
      ∏ i ∈ F, (if γ i then (p i : ℝ) else 1 - p i) := by
  have hpre : (fun q : ι → Prop => {i | q i}) ⁻¹' {ω : Set ι | ∀ i ∈ F, (i ∈ ω ↔ γ i)}
      = Set.pi (F : Set ι) (fun i => {γ i}) := by
    ext q
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_pi, Finset.mem_coe,
      Set.mem_singleton_iff, eq_iff_iff]
  rw [prodBernoulli_real_eq_infinitePi, measureReal_def, hpre,
    Measure.infinitePi_pi _ (fun _ _ => MeasurableSet.of_discrete), ENNReal.toReal_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases h : γ i
  · have hs : ({γ i} : Set Prop) = {True} := by rw [eq_true h]
    rw [hs, bernoulliMeasure_prop_apply_true, ENNReal.toReal_ofReal (p i).2.1, if_pos h]
  · have hs : ({γ i} : Set Prop) = {False} := by rw [eq_false h]
    rw [hs, bernoulliMeasure_prop_apply_false, ENNReal.toReal_ofReal (sub_nonneg.2 (p i).2.2),
      if_neg h]

end Percolation.Literature.LatticeModels
