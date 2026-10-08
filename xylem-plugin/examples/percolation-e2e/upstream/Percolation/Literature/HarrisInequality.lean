import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Order.PropInstances
import Mathlib.Probability.ProductMeasure
import Percolation.Util.Linter

/-!
# The Harris inequality on infinite product spaces

Support for the Harris–FKG statement `Percolation.Literature.harris_fkg`.

Let `X i`, `i : ι`, be linearly ordered measurable spaces and `μ i` probability measures on them;
write `μ∞ = Measure.infinitePi μ` for the product measure on `Π i, X i` (Mathlib), ordered
coordinatewise. We prove the Harris (Harris–FKG for product measures) inequality

* `infinitePi_harris_dependsOn`: if `f, g : (Π i, X i) → ℝ` are increasing, measurable, bounded
  and depend on finitely many coordinates, then `∫ f dμ∞ * ∫ g dμ∞ ≤ ∫ f g dμ∞`;
* `infinitePi_harris`: if `A, B` are increasing (`IsUpperSet`) measurable events, then
  `μ∞ A * μ∞ B ≤ μ∞ (A ∩ B)`.

The proof is Grimmett's proof of *Percolation* (2nd ed., 1999), Thm. (2.4), pp. 34–36:
the one-coordinate case is Chebyshev's "sum" inequality
`∫∫ (φ x - φ y)(ψ x - ψ y) ≥ 0` (`integral_mul_integral_le_integral_mul_of_monotone`); the
finite-dimensional case is an induction on the number of coordinates, averaging out one coordinate
at a time (the averaging operator `T_s f (ω) = ∫ f (s.piecewise ω η) dμ∞(η)` is the
conditional expectation given the coordinates in `s`, and it preserves monotonicity); the general
case follows by approximating a measurable set by a measurable cylinder in measure
(`Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite`, replacing Grimmett's appeal to the
martingale convergence theorem, so that no countability of `ι` is needed).

## References

* T. E. Harris, A lower bound for the critical probability in a certain percolation process,
  *Proc. Camb. Phil. Soc.* 56 (1960) 13–20, Lemma 4.1.
* G. Grimmett, *Percolation*, 2nd ed., Springer (1999), §2.2, Theorem (2.4).

## Design choices

* Everything is stated for `Measure.infinitePi` of an arbitrary family of probability measures on
  linearly ordered measurable spaces (no topology, no countability); the percolation instance
  (`setBer(E, p)` on `Set (Sym2 V)`, i.e. `X i = Prop`) is derived in
  `InequalitiesProofs.lean` (`harris_fkg_holds`).
* Boundedness hypotheses are phrased as `∀ ω, ‖f ω‖ ≤ C`.
-/

namespace Percolation.Literature

open MeasureTheory Measure Filter Set Function
open scoped ENNReal symmDiff

/-! ### One coordinate: Chebyshev's inequality for monotone functions -/

section OneDim

variable {Y : Type*} [MeasurableSpace Y] [LinearOrder Y] (ν : Measure Y) [IsProbabilityMeasure ν]

/-- **Chebyshev's integral inequality** (the case `n = 1` of Harris' lemma; Grimmett, *Percolation*
(1999), proof of Thm. (2.4), p. 35): if `φ, ψ` are increasing bounded measurable functions on a
linearly ordered probability space then `∫ φ * ∫ ψ ≤ ∫ φ ψ`, because
`0 ≤ ∫∫ (φ x - φ y)(ψ x - ψ y) = 2 (∫ φ ψ - ∫ φ ∫ ψ)`. [cite: GrimmettPercolation1999, Thm. 2.4 (proof, case n = 1)] -/
theorem integral_mul_integral_le_integral_mul_of_monotone {φ ψ : Y → ℝ} (hφ : Monotone φ)
    (hψ : Monotone ψ) (hφm : Measurable φ) (hψm : Measurable ψ) {C : ℝ} (hφb : ∀ y, ‖φ y‖ ≤ C)
    (hψb : ∀ y, ‖ψ y‖ ≤ C) :
    (∫ y, φ y ∂ν) * (∫ y, ψ y ∂ν) ≤ ∫ y, φ y * ψ y ∂ν := by
  have iφ : Integrable φ ν := .of_bound hφm.aestronglyMeasurable C (ae_of_all _ hφb)
  have iψ : Integrable ψ ν := .of_bound hψm.aestronglyMeasurable C (ae_of_all _ hψb)
  have iφψ : Integrable (fun y => φ y * ψ y) ν :=
    .of_bound (hφm.mul hψm).aestronglyMeasurable (C * C) (ae_of_all _ fun y => by
      rw [norm_mul]
      exact mul_le_mul (hφb y) (hψb y) (norm_nonneg _) ((norm_nonneg _).trans (hφb y)))
  set a := ∫ y, φ y ∂ν with ha
  set b := ∫ y, ψ y ∂ν with hb
  set c := ∫ y, φ y * ψ y ∂ν with hc
  have hpt : ∀ x y, 0 ≤ (φ x - φ y) * (ψ x - ψ y) := by
    intro x y
    rcases le_total x y with h | h
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 (hφ h)) (sub_nonpos.2 (hψ h))
    · exact mul_nonneg (sub_nonneg.2 (hφ h)) (sub_nonneg.2 (hψ h))
  have h1 : ∀ y, ∫ x, (φ x - φ y) * (ψ x - ψ y) ∂ν = c - φ y * b - ψ y * a + φ y * ψ y := by
    intro y
    have e : (fun x => (φ x - φ y) * (ψ x - ψ y)) =
        fun x => (φ x * ψ x - φ y * ψ x - ψ y * φ x) + φ y * ψ y := by
      funext x; ring
    rw [e, integral_add, integral_sub, integral_sub, integral_const_mul, integral_const_mul,
      integral_const]
    · simp [ha, hb, hc]
    all_goals first
      | exact integrable_const _
      | exact iφψ
      | exact iψ.const_mul _
      | exact iφ.const_mul _
      | exact iφψ.sub (iψ.const_mul _)
      | exact (iφψ.sub (iψ.const_mul _)).sub (iφ.const_mul _)
  have h2 : 0 ≤ ∫ y, (c - φ y * b - ψ y * a + φ y * ψ y) ∂ν := by
    have h0 : 0 ≤ ∫ y, ∫ x, (φ x - φ y) * (ψ x - ψ y) ∂ν ∂ν :=
      integral_nonneg fun y => integral_nonneg fun x => hpt x y
    simpa only [h1] using h0
  have h3 : ∫ y, (c - φ y * b - ψ y * a + φ y * ψ y) ∂ν = c - a * b - b * a + c := by
    rw [integral_add, integral_sub, integral_sub, integral_mul_const, integral_mul_const,
      integral_const]
    · simp [ha, hb, hc]
    all_goals first
      | exact integrable_const _
      | exact iφψ
      | exact iφ.mul_const _
      | exact iψ.mul_const _
      | exact (integrable_const c).sub (iφ.mul_const _)
      | exact ((integrable_const c).sub (iφ.mul_const _)).sub (iψ.mul_const _)
  rw [h3] at h2
  linarith

end OneDim

/-! ### The averaging (conditional expectation) operator on a product space -/

section Product

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
  (μ : (i : ι) → Measure (X i)) [hμ : ∀ i, IsProbabilityMeasure (μ i)]

section Piecewise

variable [DecidableEq ι] (s : Finset ι)

omit hμ in
/-- The gluing map `(ω, η) ↦ s.piecewise ω η` (coordinates in `s` from `ω`, the others from `η`) is
measurable. [folklore] -/
theorem measurable_finsetPiecewise :
    Measurable fun p : (Π i, X i) × (Π i, X i) => s.piecewise p.1 p.2 := by
  refine measurable_pi_iff.2 fun j => ?_
  by_cases hj : j ∈ s
  · simp only [Finset.piecewise_eq_of_mem _ _ _ hj]; fun_prop
  · simp only [Finset.piecewise_eq_of_notMem _ _ _ hj]; fun_prop

omit hμ in
/-- For fixed `ω`, `η ↦ s.piecewise ω η` is measurable. [folklore] -/
theorem measurable_finsetPiecewise_right (ω : Π i, X i) :
    Measurable fun η : Π i, X i => s.piecewise ω η :=
  (measurable_finsetPiecewise s).comp measurable_prodMk_left

/-- Gluing two independent samples of the product measure along a finite set of coordinates gives
a sample of the product measure: `(μ∞ ⊗ μ∞).map (s.piecewise) = μ∞`. (Grimmett 1999, §2.2,
implicit in (2.9).) [folklore] -/
theorem infinitePi_prod_map_piecewise :
    ((infinitePi μ).prod (infinitePi μ)).map (fun p => s.piecewise p.1 p.2) = infinitePi μ := by
  refine eq_infinitePi μ fun I t ht => ?_
  rw [Measure.map_apply (measurable_finsetPiecewise s)
    (.pi I.countable_toSet fun j _ => ht j)]
  have : (fun p : (Π i, X i) × (Π i, X i) => s.piecewise p.1 p.2) ⁻¹' Set.pi ↑I t =
      Set.pi ↑(I.filter (· ∈ s)) t ×ˢ Set.pi ↑(I.filter (· ∉ s)) t := by
    ext ⟨ω, η⟩
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_prod, Finset.mem_filter]
    constructor
    · intro h
      refine ⟨fun j hj => ?_, fun j hj => ?_⟩
      · simpa [Finset.piecewise_eq_of_mem _ _ _ hj.2] using h j hj.1
      · simpa [Finset.piecewise_eq_of_notMem _ _ _ hj.2] using h j hj.1
    · rintro ⟨h1, h2⟩ j hj
      by_cases hjs : j ∈ s
      · rw [Finset.piecewise_eq_of_mem _ _ _ hjs]; exact h1 j ⟨hj, hjs⟩
      · rw [Finset.piecewise_eq_of_notMem _ _ _ hjs]; exact h2 j ⟨hj, hjs⟩
  rw [this, Measure.prod_prod, infinitePi_pi _ (fun j _ => ht j), infinitePi_pi _ (fun j _ => ht j),
    Finset.prod_filter_mul_prod_filter_not]

/-!
The averaging operator `T_s f (ω) = ∫ f (s.piecewise ω η) dμ∞(η)` integrates out all coordinates
outside the finite set `s`. Under the product measure this is (a version of) the conditional
expectation of `f` given the coordinates in `s`, Grimmett's `X_n = E_p(X | 𝓕_n)` ((2.9) in the
proof of Thm. (2.4)); we keep it as an explicit iterated integral rather than a definition.
-/

variable {s}

/-- A bounded measurable function has integrable sections `η ↦ f (s.piecewise ω η)`. [folklore] -/
theorem integrable_comp_piecewise {f : (Π i, X i) → ℝ} (hfm : Measurable f) {C : ℝ}
    (hb : ∀ ω, ‖f ω‖ ≤ C) (ω : Π i, X i) :
    Integrable (fun η => f (s.piecewise ω η)) (infinitePi μ) :=
  .of_bound (hfm.comp (measurable_finsetPiecewise_right s ω)).aestronglyMeasurable C
    (ae_of_all _ fun _ => hb _)

/-- Averaging preserves the integral: `∫ T_s f dμ∞ = ∫ f dμ∞` (tower property / Fubini for the
gluing map). [cite: GrimmettPercolation1999, Thm. 2.4 (proof)] -/
theorem integral_integral_piecewise {f : (Π i, X i) → ℝ} (hf : Integrable f (infinitePi μ)) :
    ∫ ω, ∫ η, f (s.piecewise ω η) ∂infinitePi μ ∂infinitePi μ = ∫ ω, f ω ∂infinitePi μ := by
  have hae : AEStronglyMeasurable f
      (((infinitePi μ).prod (infinitePi μ)).map (fun p => s.piecewise p.1 p.2)) := by
    rw [infinitePi_prod_map_piecewise]; exact hf.aestronglyMeasurable
  have hint : Integrable (fun p : (Π i, X i) × (Π i, X i) => f (s.piecewise p.1 p.2))
      ((infinitePi μ).prod (infinitePi μ)) := by
    have h := hf
    rw [← infinitePi_prod_map_piecewise μ s] at h
    exact h.comp_measurable (measurable_finsetPiecewise s)
  calc ∫ ω, ∫ η, f (s.piecewise ω η) ∂infinitePi μ ∂infinitePi μ
      = ∫ p, f (s.piecewise p.1 p.2) ∂(infinitePi μ).prod (infinitePi μ) :=
        (integral_prod _ hint).symm
    _ = ∫ ω, f ω ∂((infinitePi μ).prod (infinitePi μ)).map (fun p => s.piecewise p.1 p.2) :=
        (integral_map (measurable_finsetPiecewise s).aemeasurable hae).symm
    _ = ∫ ω, f ω ∂infinitePi μ := by rw [infinitePi_prod_map_piecewise]

/-- Averaging an increasing function gives an increasing function (product measure!): the map
`ω ↦ ∫ f (s.piecewise ω η) dμ∞(η)` is monotone if `f` is. [cite: GrimmettPercolation1999, Thm. 2.4 (proof)] -/
theorem monotone_integral_piecewise [∀ i, Preorder (X i)] {f : (Π i, X i) → ℝ} (hf : Monotone f)
    (hfm : Measurable f) {C : ℝ} (hb : ∀ ω, ‖f ω‖ ≤ C) :
    Monotone fun ω => ∫ η, f (s.piecewise ω η) ∂infinitePi μ := by
  intro ω ω' h
  exact integral_mono (integrable_comp_piecewise μ hfm hb ω)
    (integrable_comp_piecewise μ hfm hb ω')
    fun η => hf (Finset.piecewise_le_piecewise _ h le_rfl)

/-- `ω ↦ ∫ f (s.piecewise ω η) dμ∞(η)` is measurable (Fubini). [folklore] -/
theorem measurable_integral_piecewise {f : (Π i, X i) → ℝ} (hfm : Measurable f) :
    Measurable fun ω => ∫ η, f (s.piecewise ω η) ∂infinitePi μ :=
  ((hfm.comp (measurable_finsetPiecewise s)).stronglyMeasurable.integral_prod_right'
    (ν := infinitePi μ)).measurable

/-- Averaging is a contraction for the sup norm. [folklore] -/
theorem norm_integral_piecewise_le {f : (Π i, X i) → ℝ} {C : ℝ} (hb : ∀ ω, ‖f ω‖ ≤ C)
    (ω : Π i, X i) : ‖∫ η, f (s.piecewise ω η) ∂infinitePi μ‖ ≤ C := by
  have h := norm_integral_le_of_norm_le_const (μ := infinitePi μ)
    (ae_of_all _ fun η => hb (s.piecewise ω η))
  rwa [probReal_univ, mul_one] at h

omit hμ in
/-- `ω ↦ ∫ f (s.piecewise ω η) dμ∞(η)` depends only on the coordinates in `s`. [folklore] -/
theorem dependsOn_integral_piecewise (f : (Π i, X i) → ℝ) :
    DependsOn (fun ω => ∫ η, f (s.piecewise ω η) ∂infinitePi μ) ↑s := by
  intro ω ω' h
  dsimp only
  congr 1 with η
  rw [s.piecewise_congr (fun j hj => h j hj) fun _ (_ : _ ∉ s) => (rfl : η _ = η _)]

/-- A function depending only on the coordinates in `s` is fixed by averaging over the other
coordinates. [folklore] -/
theorem integral_piecewise_eq_self {f : (Π i, X i) → ℝ} (hf : DependsOn f ↑s) (ω : Π i, X i) :
    ∫ η, f (s.piecewise ω η) ∂infinitePi μ = f ω := by
  have : ∀ η, f (s.piecewise ω η) = f ω :=
    fun η => hf fun j hj => Finset.piecewise_eq_of_mem _ _ _ hj
  simp [this, integral_const]

/-- Averaging is a contraction in `L¹(μ∞)`. [folklore] -/
theorem integral_norm_integral_piecewise_sub_le {f g : (Π i, X i) → ℝ} (hfm : Measurable f)
    (hgm : Measurable g) {C : ℝ} (hfb : ∀ ω, ‖f ω‖ ≤ C) (hgb : ∀ ω, ‖g ω‖ ≤ C) :
    ∫ ω, ‖(∫ η, f (s.piecewise ω η) ∂infinitePi μ) - ∫ η, g (s.piecewise ω η) ∂infinitePi μ‖
        ∂infinitePi μ ≤ ∫ ω, ‖f ω - g ω‖ ∂infinitePi μ := by
  have hd : ∀ ω, ‖f ω - g ω‖ ≤ C + C :=
    fun ω => (norm_sub_le _ _).trans (add_le_add (hfb ω) (hgb ω))
  have hdn : ∀ ω, ‖‖f ω - g ω‖‖ ≤ C + C := fun ω => by rw [norm_norm]; exact hd ω
  have h1 : ∀ ω, ‖(∫ η, f (s.piecewise ω η) ∂infinitePi μ) - ∫ η, g (s.piecewise ω η) ∂infinitePi μ‖
      ≤ ∫ η, ‖f (s.piecewise ω η) - g (s.piecewise ω η)‖ ∂infinitePi μ := by
    intro ω
    rw [← integral_sub (integrable_comp_piecewise μ hfm hfb ω)
      (integrable_comp_piecewise μ hgm hgb ω)]
    exact norm_integral_le_integral_norm _
  have iT : ∀ {h : (Π i, X i) → ℝ}, Measurable h → ∀ {C : ℝ}, (∀ ω, ‖h ω‖ ≤ C) →
      Integrable (fun ω => ∫ η, h (s.piecewise ω η) ∂infinitePi μ) (infinitePi μ) :=
    fun hm _ hb => .of_bound (measurable_integral_piecewise μ hm).aestronglyMeasurable _
      (ae_of_all _ (norm_integral_piecewise_le μ hb))
  calc ∫ ω, ‖(∫ η, f (s.piecewise ω η) ∂infinitePi μ) - ∫ η, g (s.piecewise ω η) ∂infinitePi μ‖
        ∂infinitePi μ
      ≤ ∫ ω, ∫ η, ‖f (s.piecewise ω η) - g (s.piecewise ω η)‖ ∂infinitePi μ ∂infinitePi μ :=
        integral_mono ((iT hfm hfb).sub (iT hgm hgb)).norm (iT (hfm.sub hgm).norm hdn) h1
    _ = ∫ ω, ‖f ω - g ω‖ ∂infinitePi μ :=
        integral_integral_piecewise μ
          (.of_bound (hfm.sub hgm).norm.aestronglyMeasurable _ (ae_of_all _ hdn))

end Piecewise

/-! ### Harris' inequality: finitely many coordinates -/

/-- **Harris' lemma, finite-dimensional case** (Harris 1960, Lemma 4.1; Grimmett, *Percolation*
(1999), Thm. (2.4), first part of the proof, pp. 35–36). Under a product probability measure on
a product of linearly ordered spaces, increasing bounded measurable functions `f, g` depending on
finitely many coordinates are positively correlated: `∫ f * ∫ g ≤ ∫ f g`. Induction on the number of
coordinates, averaging out one coordinate at a time. [cite: GrimmettPercolation1999, Thm. 2.4] -/
theorem infinitePi_harris_dependsOn [DecidableEq ι] [∀ i, LinearOrder (X i)] (s : Finset ι) :
    ∀ {f g : (Π i, X i) → ℝ} {C : ℝ}, Monotone f → Monotone g → Measurable f → Measurable g →
      DependsOn f ↑s → DependsOn g ↑s → (∀ ω, ‖f ω‖ ≤ C) → (∀ ω, ‖g ω‖ ≤ C) →
      (∫ ω, f ω ∂infinitePi μ) * (∫ ω, g ω ∂infinitePi μ) ≤ ∫ ω, f ω * g ω ∂infinitePi μ := by
  induction s using Finset.induction_on with
  | empty =>
    intro f g C hf hg hfm hgm hfs hgs hfb hgb
    rcases isEmpty_or_nonempty (Π i, X i) with h | ⟨⟨ω₀⟩⟩
    · simp [Measure.eq_zero_of_isEmpty (infinitePi μ)]
    · have hf' : f = fun _ => f ω₀ := funext fun ω => hfs (by simp)
      have hg' : g = fun _ => g ω₀ := funext fun ω => hgs (by simp)
      rw [hf', hg']
      simp [integral_const]
  | insert i s hi ih =>
    intro f g C hf hg hfm hgm hfs hgs hfb hgb
    -- integrability of bounded measurable functions on the probability space `μ∞`
    have iB : ∀ {h : (Π i, X i) → ℝ}, Measurable h → ∀ {C : ℝ}, (∀ ω, ‖h ω‖ ≤ C) →
        Integrable h (infinitePi μ) := fun hm C hb =>
      .of_bound hm.aestronglyMeasurable C (ae_of_all _ hb)
    have hprod : ∀ {u v : (Π i, X i) → ℝ} {C : ℝ}, (∀ ω, ‖u ω‖ ≤ C) → (∀ ω, ‖v ω‖ ≤ C) →
        ∀ ω, ‖u ω * v ω‖ ≤ C * C := fun hu hv ω => by
      rw [norm_mul]
      exact mul_le_mul (hu ω) (hv ω) (norm_nonneg _) ((norm_nonneg _).trans (hu ω))
    have hfgs : DependsOn (fun ω => f ω * g ω) ↑(insert i s) := fun x y h => by
      simp only [hfs h, hgs h]
    -- Step 1: for fixed `ω`, averaging over the coordinates outside `s` of a function depending on
    -- `insert i s` is a one-dimensional integral in the coordinate `i`; apply Chebyshev there.
    have red : ∀ {h : (Π i, X i) → ℝ}, DependsOn h ↑(insert i s) → Measurable h → ∀ ω,
        ∫ η, h (s.piecewise ω η) ∂infinitePi μ = ∫ x, h (update ω i x) ∂μ i := by
      intro h hh hhm ω
      have e : ∀ η, h (s.piecewise ω η) = h (update ω i (η i)) := by
        intro η
        apply hh
        intro j hj
        rcases Finset.mem_insert.1 hj with rfl | hj
        · simp [Finset.piecewise_eq_of_notMem _ _ _ hi]
        · have hji : j ≠ i := fun h' => hi (h' ▸ hj)
          simp [Finset.piecewise_eq_of_mem _ _ _ hj, update_of_ne hji]
      simp only [e]
      rw [← infinitePi_map_eval μ i, integral_map (measurable_pi_apply i).aemeasurable]
      exact (hhm.comp (measurable_update ω)).aestronglyMeasurable
    have key : ∀ ω, (∫ η, f (s.piecewise ω η) ∂infinitePi μ) * (∫ η, g (s.piecewise ω η) ∂infinitePi μ)
        ≤ ∫ η, f (s.piecewise ω η) * g (s.piecewise ω η) ∂infinitePi μ := by
      intro ω
      rw [red hfs hfm, red hgs hgm, red hfgs (hfm.mul hgm)]
      exact integral_mul_integral_le_integral_mul_of_monotone (μ i) (hf.comp update_mono)
        (hg.comp update_mono) (hfm.comp (measurable_update ω)) (hgm.comp (measurable_update ω))
        (fun x => hfb _) (fun x => hgb _)
    -- Step 2: induction hypothesis for the averaged functions, which depend on `s` only.
    have hF := ih (monotone_integral_piecewise μ hf hfm hfb) (monotone_integral_piecewise μ hg hgm hgb)
      (measurable_integral_piecewise μ hfm) (measurable_integral_piecewise μ hgm)
      (dependsOn_integral_piecewise μ f) (dependsOn_integral_piecewise μ g)
      (norm_integral_piecewise_le μ hfb) (norm_integral_piecewise_le μ hgb)
    rw [integral_integral_piecewise μ (iB hfm hfb), integral_integral_piecewise μ (iB hgm hgb)] at hF
    calc (∫ ω, f ω ∂infinitePi μ) * (∫ ω, g ω ∂infinitePi μ)
        ≤ ∫ ω, (∫ η, f (s.piecewise ω η) ∂infinitePi μ) * (∫ η, g (s.piecewise ω η) ∂infinitePi μ)
            ∂infinitePi μ := hF
      _ ≤ ∫ ω, ∫ η, f (s.piecewise ω η) * g (s.piecewise ω η) ∂infinitePi μ ∂infinitePi μ :=
          integral_mono (iB ((measurable_integral_piecewise μ hfm).mul
              (measurable_integral_piecewise μ hgm))
            (hprod (norm_integral_piecewise_le μ hfb) (norm_integral_piecewise_le μ hgb)))
            (iB (measurable_integral_piecewise μ (hfm.mul hgm))
              (norm_integral_piecewise_le μ (hprod hfb hgb))) key
      _ = ∫ ω, f ω * g ω ∂infinitePi μ :=
          integral_integral_piecewise μ (iB (hfm.mul hgm) (hprod hfb hgb))

/-! ### Harris' inequality: general measurable increasing events -/

/-- Approximation step (replacing the martingale convergence theorem in Grimmett's proof of
Thm. (2.4), p. 36): for a measurable set `A`, the averages `T_s 1_A` converge to `1_A` in `L¹(μ∞)`
along the directed set of finite coordinate sets `s`. Proof: approximate `A` in measure by a
measurable cylinder (`Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite`), which `T_s`
fixes, and use that `T_s` is an `L¹` contraction. [cite: GrimmettPercolation1999, Thm. 2.4 (proof, (2.11))] -/
theorem exists_integral_norm_integral_piecewise_indicator_sub_le [DecidableEq ι]
    {A : Set (Π i, X i)} (hA : MeasurableSet A) {ε : ℝ} (hε : 0 < ε) :
    ∃ s₀ : Finset ι, ∀ s : Finset ι, s₀ ⊆ s →
      ∫ ω, ‖(∫ η, A.indicator (1 : (Π i, X i) → ℝ) (s.piecewise ω η) ∂infinitePi μ) -
        A.indicator 1 ω‖ ∂infinitePi μ ≤ ε := by
  have hd : (infinitePi μ).MeasureDense (measurableCylinders X) :=
    .of_generateFrom_isSetAlgebra_finite (infinitePi μ) isSetAlgebra_measurableCylinders
      generateFrom_measurableCylinders.symm
  obtain ⟨C, hC, hAC⟩ := hd.approx A hA (measure_ne_top _ _) (ε / 2) (half_pos hε)
  have hCm : MeasurableSet C := hd.measurable C hC
  obtain ⟨s₀, S, hS, rfl⟩ := (mem_measurableCylinders C).1 hC
  refine ⟨s₀, fun s hs => ?_⟩
  set a : (Π i, X i) → ℝ := A.indicator 1 with ha_def
  set c : (Π i, X i) → ℝ := (cylinder s₀ S).indicator 1 with hc_def
  have ham : Measurable a := measurable_const.indicator hA
  have hcm : Measurable c := measurable_const.indicator hCm
  have hbd : ∀ (B : Set (Π i, X i)) (ω), ‖B.indicator (1 : (Π i, X i) → ℝ) ω‖ ≤ 1 := by
    intro B ω
    by_cases hω : ω ∈ B <;> simp [hω]
  have hcs : DependsOn c ↑s := by
    intro x y hxy
    have hr : s₀.restrict x = s₀.restrict y := funext fun j => hxy j (hs j.2)
    have hx : x ∈ cylinder s₀ S ↔ y ∈ cylinder s₀ S := by
      simp only [MeasureTheory.cylinder, Set.mem_preimage, hr]
    by_cases hxm : x ∈ cylinder s₀ S
    · simp [hc_def, hxm, hx.1 hxm]
    · simp [hc_def, hxm, mt hx.2 hxm]
  -- shorthand for the averages
  set Ta : (Π i, X i) → ℝ := fun ω => ∫ η, a (s.piecewise ω η) ∂infinitePi μ with hTa_def
  set Tc : (Π i, X i) → ℝ := fun ω => ∫ η, c (s.piecewise ω η) ∂infinitePi μ with hTc_def
  -- pointwise: ‖T a - a‖ ≤ ‖T a - T c‖ + ‖a - c‖, and `T c = c`
  have hTc : ∀ ω, Tc ω = c ω := integral_piecewise_eq_self μ hcs
  have hpt : ∀ ω, ‖Ta ω - a ω‖ ≤ ‖Ta ω - Tc ω‖ + ‖a ω - c ω‖ := by
    intro ω
    calc ‖Ta ω - a ω‖ = ‖(Ta ω - Tc ω) - (a ω - c ω)‖ := by rw [hTc]; ring_nf
      _ ≤ ‖Ta ω - Tc ω‖ + ‖a ω - c ω‖ := norm_sub_le _ _
  -- `∫ ‖a - c‖ = μ∞ (A ∆ C) < ε / 2`
  have hac : ∫ ω, ‖a ω - c ω‖ ∂infinitePi μ = (infinitePi μ).real (A ∆ cylinder s₀ S) := by
    rw [← integral_indicator_one (hA.symmDiff hCm)]
    congr 1 with ω
    rw [Real.norm_eq_abs, ha_def, hc_def, ← Set.abs_indicator_symmDiff, abs_of_nonneg]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have hε2 : (infinitePi μ).real (A ∆ cylinder s₀ S) < ε / 2 :=
    ENNReal.toReal_lt_of_lt_ofReal hAC
  have iTa : Integrable Ta (infinitePi μ) :=
    .of_bound (measurable_integral_piecewise μ ham).aestronglyMeasurable 1
      (ae_of_all _ (norm_integral_piecewise_le μ (hbd A)))
  have iTc : Integrable Tc (infinitePi μ) :=
    .of_bound (measurable_integral_piecewise μ hcm).aestronglyMeasurable 1
      (ae_of_all _ (norm_integral_piecewise_le μ (hbd _)))
  have ia : Integrable a (infinitePi μ) :=
    .of_bound ham.aestronglyMeasurable 1 (ae_of_all _ (hbd A))
  have ic : Integrable c (infinitePi μ) :=
    .of_bound hcm.aestronglyMeasurable 1 (ae_of_all _ (hbd _))
  calc ∫ ω, ‖Ta ω - a ω‖ ∂infinitePi μ
      ≤ ∫ ω, (‖Ta ω - Tc ω‖ + ‖a ω - c ω‖) ∂infinitePi μ :=
        integral_mono (iTa.sub ia).norm ((iTa.sub iTc).norm.add (ia.sub ic).norm) hpt
    _ = ∫ ω, ‖Ta ω - Tc ω‖ ∂infinitePi μ + ∫ ω, ‖a ω - c ω‖ ∂infinitePi μ :=
        integral_add (iTa.sub iTc).norm (ia.sub ic).norm
    _ ≤ ∫ ω, ‖a ω - c ω‖ ∂infinitePi μ + ∫ ω, ‖a ω - c ω‖ ∂infinitePi μ := by
        linarith [integral_norm_integral_piecewise_sub_le μ (s := s) ham hcm (hbd A) (hbd _)]
    _ ≤ ε := by rw [hac]; linarith

/-- **Harris' inequality** (Harris–FKG inequality for product measures; Harris, *Proc. Camb.
Phil. Soc.* 56 (1960), Lemma 4.1; Grimmett, *Percolation* (2nd ed., 1999), Thm. (2.4)(b)). Under a
product probability measure `μ∞ = ⨂ μ i` on a product `Π i, X i` of linearly ordered measurable
spaces (coordinatewise order; the index set `ι` is arbitrary), increasing measurable events are
positively correlated: `μ∞ A * μ∞ B ≤ μ∞ (A ∩ B)`. [cite: GrimmettPercolation1999, Thm. 2.4] -/
theorem infinitePi_harris [∀ i, LinearOrder (X i)] {A B : Set (Π i, X i)} (hA : IsUpperSet A)
    (hB : IsUpperSet B) (hAm : MeasurableSet A) (hBm : MeasurableSet B) :
    (infinitePi μ).real A * (infinitePi μ).real B ≤ (infinitePi μ).real (A ∩ B) := by
  classical
  set a : (Π i, X i) → ℝ := A.indicator 1 with ha_def
  set b : (Π i, X i) → ℝ := B.indicator 1 with hb_def
  have hbd : ∀ {B : Set (Π i, X i)} (ω), ‖B.indicator (1 : (Π i, X i) → ℝ) ω‖ ≤ 1 := by
    intro B ω
    by_cases hω : ω ∈ B <;> simp [hω]
  have hmono : ∀ {B : Set (Π i, X i)}, IsUpperSet B →
      Monotone (B.indicator (1 : (Π i, X i) → ℝ)) := by
    intro B hB x y hxy
    by_cases hx : x ∈ B
    · simp [hx, hB hxy hx]
    · have h0 : (0 : ℝ) ≤ B.indicator 1 y := Set.indicator_nonneg (fun _ _ => zero_le_one) y
      simpa [hx] using h0
  have ham : Measurable a := measurable_const.indicator hAm
  have hbm : Measurable b := measurable_const.indicator hBm
  have iB : ∀ {h : (Π i, X i) → ℝ}, Measurable h → ∀ {C : ℝ}, (∀ ω, ‖h ω‖ ≤ C) →
      Integrable h (infinitePi μ) := fun hm C hb =>
    .of_bound hm.aestronglyMeasurable C (ae_of_all _ hb)
  have iA : ∫ ω, a ω ∂infinitePi μ = (infinitePi μ).real A := integral_indicator_one hAm
  have iBB : ∫ ω, b ω ∂infinitePi μ = (infinitePi μ).real B := integral_indicator_one hBm
  have iAB : ∫ ω, a ω * b ω ∂infinitePi μ = (infinitePi μ).real (A ∩ B) := by
    rw [← integral_indicator_one (hAm.inter hBm), Set.inter_indicator_one]
    rfl
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨s₁, hs₁⟩ := exists_integral_norm_integral_piecewise_indicator_sub_le μ hAm (half_pos hε)
  obtain ⟨s₂, hs₂⟩ := exists_integral_norm_integral_piecewise_indicator_sub_le μ hBm (half_pos hε)
  set s : Finset ι := s₁ ∪ s₂
  have h1 := hs₁ s Finset.subset_union_left
  have h2 := hs₂ s Finset.subset_union_right
  -- shorthand for the averaged indicators
  set Ta : (Π i, X i) → ℝ := fun ω => ∫ η, a (s.piecewise ω η) ∂infinitePi μ with hTa_def
  set Tb : (Π i, X i) → ℝ := fun ω => ∫ η, b (s.piecewise ω η) ∂infinitePi μ with hTb_def
  -- finite-dimensional Harris for the averaged indicators
  have hfin := infinitePi_harris_dependsOn μ s (monotone_integral_piecewise μ (hmono hA) ham hbd)
    (monotone_integral_piecewise μ (hmono hB) hbm hbd) (measurable_integral_piecewise μ ham)
    (measurable_integral_piecewise μ hbm) (dependsOn_integral_piecewise μ a)
    (dependsOn_integral_piecewise μ b) (norm_integral_piecewise_le μ hbd)
    (norm_integral_piecewise_le μ hbd)
  rw [integral_integral_piecewise μ (iB ham hbd), integral_integral_piecewise μ (iB hbm hbd), iA,
    iBB] at hfin
  -- pass back from `T a * T b` to `a * b` at `L¹` cost `‖T a - a‖ + ‖T b - b‖`
  have hpt : ∀ ω, Ta ω * Tb ω ≤ a ω * b ω + (‖Ta ω - a ω‖ + ‖Tb ω - b ω‖) := by
    intro ω
    have e : Ta ω * Tb ω - a ω * b ω = (Ta ω - a ω) * Tb ω + a ω * (Tb ω - b ω) := by ring
    have k1 : |(Ta ω - a ω) * Tb ω| ≤ ‖Ta ω - a ω‖ := by
      rw [abs_mul, ← Real.norm_eq_abs, ← Real.norm_eq_abs]
      exact mul_le_of_le_one_right (norm_nonneg _) (norm_integral_piecewise_le μ hbd ω)
    have k2 : |a ω * (Tb ω - b ω)| ≤ ‖Tb ω - b ω‖ := by
      rw [abs_mul, ← Real.norm_eq_abs, ← Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) (hbd ω)
    linarith [le_abs_self ((Ta ω - a ω) * Tb ω), le_abs_self (a ω * (Tb ω - b ω))]
  have iTa : Integrable Ta (infinitePi μ) :=
    iB (measurable_integral_piecewise μ ham) (norm_integral_piecewise_le μ hbd)
  have iTb : Integrable Tb (infinitePi μ) :=
    iB (measurable_integral_piecewise μ hbm) (norm_integral_piecewise_le μ hbd)
  have hprod : ∀ {u v : (Π i, X i) → ℝ}, (∀ ω, ‖u ω‖ ≤ 1) → (∀ ω, ‖v ω‖ ≤ 1) →
      ∀ ω, ‖u ω * v ω‖ ≤ 1 * 1 := fun hu hv ω => by
    rw [norm_mul]
    exact mul_le_mul (hu ω) (hv ω) (norm_nonneg _) zero_le_one
  have i1 : Integrable (fun ω => Ta ω * Tb ω) (infinitePi μ) :=
    iB ((measurable_integral_piecewise μ ham).mul (measurable_integral_piecewise μ hbm))
      (hprod (norm_integral_piecewise_le μ hbd) (norm_integral_piecewise_le μ hbd))
  have i2 : Integrable (fun ω => a ω * b ω) (infinitePi μ) := iB (ham.mul hbm) (hprod hbd hbd)
  have i3 : Integrable (fun ω => ‖Ta ω - a ω‖) (infinitePi μ) := (iTa.sub (iB ham hbd)).norm
  have i4 : Integrable (fun ω => ‖Tb ω - b ω‖) (infinitePi μ) := (iTb.sub (iB hbm hbd)).norm
  have i34 : Integrable (fun ω => ‖Ta ω - a ω‖ + ‖Tb ω - b ω‖) (infinitePi μ) := i3.add i4
  have i234 : Integrable (fun ω => a ω * b ω + (‖Ta ω - a ω‖ + ‖Tb ω - b ω‖)) (infinitePi μ) :=
    i2.add i34
  have hint := integral_mono i1 i234 hpt
  rw [integral_add i2 i34, integral_add i3 i4, iAB] at hint
  linarith

end Product

end Percolation.Literature
