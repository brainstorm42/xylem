import Mathlib.Combinatorics.SetFamily.FourFunctions
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Distributions.SetBernoulli
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProductMeasure
import Percolation.Literature.Basic
import Percolation.Literature.PercolationEvents
import Percolation.Util.Linter

/-!
# Site percolation measure: coordinates, symmetries and the Harris–FKG inequality

Sorry-free tools for the Bernoulli site percolation
measure `sitePercolation V p = setBer(univ, p)` (`Literature/Basic.lean`), needed bottom-up for the
discharge of Cerf 2015 (`CerfTwoArms.lean`) and usable by any site model:

* `bernoulliProp p` — an `abbrev` for Mathlib's Bernoulli law `Ber(True, False, p)` on `Prop`
  (`ProbabilityTheory.bernoulliMeasure`), and `sitePercolation_apply'`:
  `P_p(S) = (⨂_{v ∈ V} bernoulliProp p)(setOf ⁻¹' S)` (Mathlib's `setBernoulli_apply'`);
* (measurability of such local events is `DeterminedBy.measurableSet_of_finset` in
  `PercolationEvents.lean`; here only the trace on the finite discrete space `F → Prop` is used);

References: T. E. Harris, Proc. Camb. Phil. Soc. 56 (1960); G. Grimmett, *Percolation* (1999),
§2.2 Thm 2.4 (FKG), §1.6 (site models).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Measure unitInterval
open scoped ENNReal

namespace Percolation.Literature

variable {V : Type*}

/-! ### The Bernoulli law on `Prop` and the product formula -/

/-- The `p`-Bernoulli law on `Prop`: `True` (open) with probability `p`, `False` with
probability `1 - p`; the one-site marginal of `sitePercolation`. An `abbrev` for Mathlib's
`Ber(True, False, p) = toNNReal p • dirac True + toNNReal (σ p) • dirac False` (so Mathlib's
`IsProbabilityMeasure` instance applies). [cite: GrimmettPercolation1999, §1.6] -/
abbrev bernoulliProp (p : unitInterval) : Measure Prop := Ber(True, False, p)

/-- `bernoulliProp p {True} = p`. [cite: GrimmettPercolation1999, §1.6] -/
@[simp] theorem bernoulliProp_real_true (p : unitInterval) :
    (bernoulliProp p).real {True} = p := by
  simp [bernoulliProp, bernoulliMeasure_def, measureReal_def]

/-- `bernoulliProp p {False} = 1 - p`. [cite: GrimmettPercolation1999, §1.6] -/
@[simp] theorem bernoulliProp_real_false (p : unitInterval) :
    (bernoulliProp p).real {False} = 1 - p := by
  simp [bernoulliProp, bernoulliMeasure_def, measureReal_def]

/-- The product of the one-site Bernoulli laws over `V`, on `V → Prop`. [cite: GrimmettPercolation1999, §1.6] -/
def sitePi (V : Type*) (p : unitInterval) : Measure (V → Prop) :=
  infinitePi fun _ : V => bernoulliProp p

/-- `P_p(S) = sitePi V p (setOf ⁻¹' S)`: site percolation is the product Bernoulli measure
transported along `setOf : (V → Prop) ≃ Set V` (Mathlib's `setBernoulli_apply'`). [cite: GrimmettPercolation1999, §1.6] -/
theorem sitePercolation_apply' (p : unitInterval) (S : Set (SiteConfig V)) :
    sitePercolation V p S = sitePi V p ((fun χ : V → Prop => {v | χ v}) ⁻¹' S) := by
  rw [sitePercolation, setBernoulli_apply']
  simp only [Set.mem_univ, sitePi, bernoulliProp, bernoulliMeasure_def]

/-! ### Lattice symmetries: relabelling sites along a bijection -/

section Relabel

variable {W : Type*}

/-- Relabelling of site configurations along a bijection `e : V ≃ W`, `ω ↦ e '' ω`, as a
measurable equivalence (each coordinate `w ∈ e '' ω ↔ e⁻¹ w ∈ ω` is measurable). Used for
the translation and reflection invariance of site percolation on `ℤ^d`. [cite: GrimmettPercolation1999, §1.6] -/
def SiteConfig.relabel (e : V ≃ W) : SiteConfig V ≃ᵐ SiteConfig W where
  toEquiv := Equiv.Set.congr e
  measurable_toFun := by
    refine measurable_set_iff.2 fun w => ?_
    have : (fun ω : Set V => w ∈ Equiv.Set.congr e ω) = fun ω => e.symm w ∈ ω := by
      ext ω
      change w ∈ e '' ω ↔ _
      rw [Equiv.image_eq_preimage_symm]; rfl
    rw [this]; exact measurable_set_mem _
  measurable_invFun := by
    refine measurable_set_iff.2 fun v => ?_
    have : (fun ω : Set W => v ∈ (Equiv.Set.congr e).symm ω) = fun ω => e v ∈ ω := by
      ext ω
      change v ∈ e.symm '' ω ↔ _
      rw [Equiv.image_eq_preimage_symm]; rfl
    rw [this]; exact measurable_set_mem _

/-- `relabel e ω = e '' ω`. [cite: GrimmettPercolation1999, §1.6] -/
@[simp] theorem SiteConfig.relabel_apply (e : V ≃ W) (ω : SiteConfig V) :
    SiteConfig.relabel e ω = e '' ω := rfl

/-- `w ∈ relabel e ω ↔ e⁻¹ w ∈ ω`. [cite: GrimmettPercolation1999, §1.6] -/
theorem SiteConfig.mem_relabel_iff (e : V ≃ W) (ω : SiteConfig V) (w : W) :
    w ∈ SiteConfig.relabel e ω ↔ e.symm w ∈ ω := by
  rw [SiteConfig.relabel_apply, Equiv.image_eq_preimage_symm]; rfl

end Relabel

end Percolation.Literature
