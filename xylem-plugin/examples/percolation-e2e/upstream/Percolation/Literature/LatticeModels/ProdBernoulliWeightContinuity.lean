import Percolation.Literature.LatticeModels.ProdBernoulliAtomExpansion
import Percolation.Literature.LatticeModels.ProdBernoulliBK
import Percolation.Util.Linter

/-!
# Continuity of finite-volume `prodBernoulli` probabilities in the weights, density of non-degenerate weights, and the closure principle for weighted-graph inequalities

Proofs-only companion of
`Percolation.Literature.LatticeModels.prodBernoulli` (`Literature/LatticeModels/ProdBernoulli.lean`), of
`ProdBernoulliBK.lean` (`prodBernoulli_real_eq_sum_cube`: the finite-dimensional distributions as a
polynomial in the weights) and of `ProdBernoulliAtomExpansion.lean`
(`prodBernoulli_real_setOf_forall_iff`: cylinder probabilities).  Everything here is proved.

The point of the file is the routine **closure step** used when an inequality between percolation
probabilities on a finite weighted graph has been proved only for *non-degenerate* weights — typically
because the proof divides by the probability of some conditioning event, which is positive as soon as
every weight lies in `(0,1)` — and one wants it for all weights in `[0,1]`:

* `dense_setOf_weights_pos_lt_one` — the non-degenerate weight functions `{p | ∀ i, 0 < p i < 1}` are
  dense in `ι → [0,1]`.
* `weights_le_of_forall_pos_lt_one` — **closure principle**: if `f, g : (ι → [0,1]) → ℝ` are
  continuous and `f p ≤ g p` for all non-degenerate `p`, then `f p ≤ g p` for all `p`.

## References
* [GrimmettPercolation1999] G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §2.2 (events depending on
  finitely many edges), §7.3 p. 162 (polynomial dependence on `p`, continuity).
-/

noncomputable section

namespace Percolation.Literature.LatticeModels

open MeasureTheory Set
open _root_.Topology
open Percolation.Literature (DeterminedBy)

variable {ι : Type*}

/-- The weight of a fixed coordinate, `p ↦ (p i : ℝ)`, is continuous on `ι → [0,1]`. [folklore] -/
theorem continuous_coe_weight_apply (i : ι) :
    Continuous fun p : ι → unitInterval => ((p i : unitInterval) : ℝ) :=
  continuous_subtype_val.comp (continuous_apply i)

/-- **Continuity in the weights, finitely determined events.** If the event `C` is determined by the
finite set `F` of coordinates, then `p ↦ P_p(C)` is continuous on `ι → [0,1]`: by
`prodBernoulli_real_eq_sum_cube` it is a finite sum of finite products of the functions `p i`,
`1 - p i`, `i ∈ F` ("a finite polynomial … and therefore a continuous function").
[cite: GrimmettPercolation1999, §7.3 p. 162] -/
theorem prodBernoulli_real_continuous_of_determinedBy (F : Finset ι) {C : Set (Set ι)}
    (hC : DeterminedBy C (↑F : Set ι)) :
    Continuous fun p : ι → unitInterval => (prodBernoulli p).real C := by
  refine Continuous.congr ?_ fun p => (prodBernoulli_real_eq_sum_cube p F hC).symm
  refine continuous_finsetSum _ fun a _ => ?_
  by_cases ha : a ∈ {a : F → Bool | {i : ι | ∃ h : i ∈ F, a ⟨i, h⟩ = true} ∈ C}
  · simp only [Set.indicator_of_mem ha]
    refine continuous_finsetProd _ fun i _ => ?_
    by_cases hi : a i = true
    · simp only [hi, if_true]
      exact continuous_coe_weight_apply (i : ι)
    · simp only [hi]
      exact continuous_const.sub (continuous_coe_weight_apply (i : ι))
  · simp only [Set.indicator_of_notMem ha]
    exact continuous_const

/-- **Continuity in the weights, finite index set.** On a finite index set every event is finitely
determined, so `p ↦ P_p(C)` is continuous on `ι → [0,1]` for every event `C`.
[cite: GrimmettPercolation1999, §7.3 p. 162] -/
theorem prodBernoulli_real_continuous [Fintype ι] (C : Set (Set ι)) :
    Continuous fun p : ι → unitInterval => (prodBernoulli p).real C :=
  prodBernoulli_real_continuous_of_determinedBy Finset.univ
    (by rw [Finset.coe_univ]; exact dependsOn_univ _)

/-- **Non-degenerate weights are dense.** The weight functions with every weight in the open interval
`(0,1)` form a dense subset of `ι → [0,1]` (product of the dense subsets `(0,1) ⊆ [0,1]`).
[folklore] -/
theorem dense_setOf_weights_pos_lt_one :
    Dense {p : ι → unitInterval | ∀ i, 0 < p i ∧ p i < 1} := by
  have h : {p : ι → unitInterval | ∀ i, 0 < p i ∧ p i < 1} =
      Set.pi Set.univ fun _ : ι => Set.Ioo (0 : unitInterval) 1 := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, forall_const, Set.mem_Ioo]
  rw [h]
  refine dense_pi Set.univ fun i _ => ?_
  rw [dense_iff_closure_eq, closure_Ioo zero_ne_one]
  exact Set.eq_univ_of_forall fun x => ⟨unitInterval.nonneg x, unitInterval.le_one x⟩

/-- **Closure principle.** If `f, g : (ι → [0,1]) → ℝ` are continuous and `f p ≤ g p` for every
non-degenerate weight function `p` (all weights in `(0,1)`), then `f p ≤ g p` for every `p`: the set
`{f ≤ g}` is closed and contains a dense set. [folklore] -/
theorem weights_le_of_forall_pos_lt_one {f g : (ι → unitInterval) → ℝ} (hf : Continuous f)
    (hg : Continuous g) (h : ∀ p : ι → unitInterval, (∀ i, 0 < p i ∧ p i < 1) → f p ≤ g p)
    (p : ι → unitInterval) : f p ≤ g p := by
  have hcl : IsClosed {p : ι → unitInterval | f p ≤ g p} := isClosed_le hf hg
  have hdense : Dense {p : ι → unitInterval | f p ≤ g p} :=
    dense_setOf_weights_pos_lt_one.mono fun q hq => h q hq
  have huniv : {p : ι → unitInterval | f p ≤ g p} = Set.univ := by
    rw [← hcl.closure_eq]; exact hdense.closure_eq
  exact (Set.eq_univ_iff_forall.1 huniv p)

/-- **Non-degenerate weights charge every configuration.** On a finite index set, if every weight lies
in `(0,1)` then every nonempty event has positive probability: it contains a configuration `ω`, whose
probability is `∏_i (p i if i ∈ ω, else 1 - p i) > 0`. [cite: GrimmettPercolation1999, §1.3 p. 10] -/
theorem prodBernoulli_real_pos_of_nonempty [Fintype ι] {p : ι → unitInterval}
    (hp : ∀ i, 0 < p i ∧ p i < 1) {C : Set (Set ι)} (hC : C.Nonempty) :
    0 < (prodBernoulli p).real C := by
  classical
  obtain ⟨ω, hω⟩ := hC
  have hcyl : (prodBernoulli p).real {ω' : Set ι | ∀ i ∈ (Finset.univ : Finset ι), (i ∈ ω' ↔ i ∈ ω)}
      = ∏ i ∈ (Finset.univ : Finset ι), (if i ∈ ω then ((p i : unitInterval) : ℝ) else 1 - p i) :=
    prodBernoulli_real_setOf_forall_iff p Finset.univ (· ∈ ω)
  have hpos : 0 < ∏ i ∈ (Finset.univ : Finset ι),
      (if i ∈ ω then ((p i : unitInterval) : ℝ) else 1 - p i) := by
    refine Finset.prod_pos fun i _ => ?_
    by_cases hi : i ∈ ω
    · rw [if_pos hi]; exact unitInterval.coe_pos.2 (hp i).1
    · rw [if_neg hi]; exact sub_pos.2 (unitInterval.coe_lt_one.2 (hp i).2)
  have hsub : {ω' : Set ι | ∀ i ∈ (Finset.univ : Finset ι), (i ∈ ω' ↔ i ∈ ω)} ⊆ C := by
    intro ω' hω'
    have hωω : ω' = ω := Set.ext fun i => hω' i (Finset.mem_univ i)
    rw [hωω]; exact hω
  calc (0 : ℝ) < _ := hpos
    _ = _ := hcyl.symm
    _ ≤ (prodBernoulli p).real C := measureReal_mono hsub

end Percolation.Literature.LatticeModels
