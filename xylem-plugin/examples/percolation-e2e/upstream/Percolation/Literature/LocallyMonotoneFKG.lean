import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Combinatorics.SimpleGraph.Dart
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Probability.ConditionalProbability
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Percolation.Literature.HarrisInequality
import Percolation.Literature.SitePercolationMeasure
import Percolation.Util.Linter

/-!
# A generalised FKG inequality for locally monotone events (Nolin 2008, Lemma 13)

Bottom-up input for the quasi-multiplicativity of polychromatic
arm events: when a colour sequence contains both colours, the arm events are not monotone and the
Harris–FKG inequality cannot glue them directly. Nolin's remedy (EJP Lemma 13 = Lemma 12 of
arXiv:0711.4948, in the proof of the "first relations", §4.3) is the following *generalised FKG
inequality for locally monotone events*, valid for any product measure:

> Consider `A⁺, Ã⁺` two increasing events, and `A⁻, Ã⁻` two decreasing events. Assume that there
> exist three disjoint finite sets of vertices `𝒜`, `𝒜⁺` and `𝒜⁻` such that `A⁺, A⁻, Ã⁺` and
> `Ã⁻` depend only on the sites in, respectively, `𝒜 ∪ 𝒜⁺`, `𝒜 ∪ 𝒜⁻`, `𝒜⁺` and `𝒜⁻`. Then
> `P(Ã⁺ ∩ Ã⁻ | A⁺ ∩ A⁻) ≥ P(Ã⁺) P(Ã⁻)` for any product measure `P`.

The proof is Nolin's: conditionally on the configuration `ω_𝒜` on `𝒜` — here: for fixed `ω`,
as functions of an independent sample `η` glued to `ω` along `𝒜` (`𝒜.piecewise ω η`, the
averaging operator of `HarrisInequality.lean`) — the events `A⁺ ∩ Ã⁺` and `A⁻ ∩ Ã⁻` depend on
the disjoint sets `𝒜⁺`, `𝒜⁻` and are independent (`infinitePi_real_inter_of_dependsOn`), the
sections of `A⁺` (resp. `A⁻`) are increasing (resp. decreasing), so Harris' inequality
(`infinitePi_harris`, and `infinitePi_harris_lower` for decreasing events) bounds each factor
below; integrating over `ω` (Fubini for the gluing map, `integral_integral_piecewise`) gives the
claim.

Also recorded: Harris' inequality for two decreasing events and for an increasing and a
decreasing event (`infinitePi_harris_lower`, `infinitePi_harris_upper_lower`), by passing to
complements in `infinitePi_harris`.

## References
* P. Nolin, *Near-critical percolation in two dimensions*, Electron. J. Probab. 13 (2008),
  1562–1623, §4.3, Lemma 13 (EJP numbering; Lemma 12 in arXiv:0711.4948) [Nolin2008].
* G. Grimmett, *Percolation*, 2nd ed., Springer (1999), §2.2, Thm. (2.4) [GrimmettPercolation1999].

Numbering: arXiv:0711.4948 (v1); the published EJP version numbers the
results of §4–5 one higher (EJP Prop. 16/17, Thm. 21 = arXiv Prop. 15/16, Thm. 20, as), and the EJP
number "Lemma 13" of the generalised FKG lemma (arXiv Lemma 12, stated inside the proof of arXiv
Prop. 11) is inferred from this offset; locators give the EJP number with the arXiv number in
brackets, and the statement is quoted in full above.
-/

namespace Percolation.Literature

open MeasureTheory Measure ProbabilityTheory Set

noncomputable section

section Product

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
  (μ : (i : ι) → Measure (X i)) [hμ : ∀ i, IsProbabilityMeasure (μ i)]

/-! ### Harris' inequality for decreasing events -/

/-- **Harris' inequality for two decreasing events** (Grimmett 1999, Thm. (2.4)(b) applied to
the complements): under a product probability measure on a product of linearly ordered spaces,
decreasing measurable events are positively correlated, `μ∞ A * μ∞ B ≤ μ∞ (A ∩ B)`. [cite: GrimmettPercolation1999, Thm. 2.4] -/
theorem infinitePi_harris_lower [∀ i, LinearOrder (X i)] {A B : Set (Π i, X i)}
    (hA : IsLowerSet A) (hB : IsLowerSet B) (hAm : MeasurableSet A) (hBm : MeasurableSet B) :
    (infinitePi μ).real A * (infinitePi μ).real B ≤ (infinitePi μ).real (A ∩ B) := by
  have h := infinitePi_harris μ hA.compl hB.compl hAm.compl hBm.compl
  rw [← Set.compl_union, measureReal_compl hAm, measureReal_compl hBm,
    measureReal_compl (hAm.union hBm), probReal_univ] at h
  have hu := measureReal_union_add_inter hBm (μ := infinitePi μ) (s := A)
  have e : (1 - (infinitePi μ).real A) * (1 - (infinitePi μ).real B) =
      1 - (infinitePi μ).real A - (infinitePi μ).real B +
        (infinitePi μ).real A * (infinitePi μ).real B := by ring
  linarith

/-- **Harris' inequality for an increasing and a decreasing event** (Grimmett 1999,
Thm. (2.4)(b) applied to `A` and `Bᶜ`): they are negatively correlated,
`μ∞ (A ∩ B) ≤ μ∞ A * μ∞ B`. [cite: GrimmettPercolation1999, Thm. 2.4] -/
theorem infinitePi_harris_upper_lower [∀ i, LinearOrder (X i)] {A B : Set (Π i, X i)}
    (hA : IsUpperSet A) (hB : IsLowerSet B) (hAm : MeasurableSet A) (hBm : MeasurableSet B) :
    (infinitePi μ).real (A ∩ B) ≤ (infinitePi μ).real A * (infinitePi μ).real B := by
  have h := infinitePi_harris μ hA hB.compl hAm hBm.compl
  rw [measureReal_compl hBm, probReal_univ] at h
  have hs : (infinitePi μ).real (A ∩ Bᶜ) + (infinitePi μ).real (A ∩ B) =
      (infinitePi μ).real A := by
    rw [← Set.sdiff_eq, add_comm]
    exact measureReal_inter_add_sdiff hBm
  linarith

/-! ### Independence of events depending on disjoint sets of coordinates -/

/-- Under a product measure, an event depending only on the coordinates in a finite set `s` and an
event depending only on the coordinates outside `s` are independent:
`μ∞ (A ∩ B) = μ∞ A * μ∞ B`. (Grimmett 1999, §2.2; the gluing map `(ω, η) ↦ s.piecewise ω η`
transports `μ∞ ⊗ μ∞` to `μ∞` and pulls `A ∩ B` back to `A ×ˢ B`.) [cite: GrimmettPercolation1999, §2.2] -/
theorem infinitePi_real_inter_of_dependsOn [DecidableEq ι] (s : Finset ι) {A B : Set (Π i, X i)}
    (hA : DependsOn (· ∈ A) ↑s) (hB : DependsOn (· ∈ B) (↑s)ᶜ) (hAm : MeasurableSet A)
    (hBm : MeasurableSet B) :
    (infinitePi μ).real (A ∩ B) = (infinitePi μ).real A * (infinitePi μ).real B := by
  have hpre : (fun p : (Π i, X i) × (Π i, X i) => s.piecewise p.1 p.2) ⁻¹' (A ∩ B) = A ×ˢ B := by
    ext p
    have h1 : (s.piecewise p.1 p.2 ∈ A) = (p.1 ∈ A) :=
      hA fun i hi => Finset.piecewise_eq_of_mem _ _ _ (Finset.mem_coe.1 hi)
    have h2 : (s.piecewise p.1 p.2 ∈ B) = (p.2 ∈ B) :=
      hB fun i hi => Finset.piecewise_eq_of_notMem _ _ _ fun h => hi (Finset.mem_coe.2 h)
    simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_prod]
    rw [h1, h2]
  have h : ((infinitePi μ).prod (infinitePi μ)).map (fun p => s.piecewise p.1 p.2) (A ∩ B) =
      infinitePi μ (A ∩ B) := by
    rw [infinitePi_prod_map_piecewise]
  rw [Measure.map_apply (measurable_finsetPiecewise s) (hAm.inter hBm), hpre,
    Measure.prod_prod] at h
  simp only [measureReal_def, ← h, ENNReal.toReal_mul]

/-- Variant of `infinitePi_real_inter_of_dependsOn` for two disjoint finite sets of
coordinates. [cite: GrimmettPercolation1999, §2.2] -/
theorem infinitePi_real_inter_of_dependsOn_disjoint {s t : Finset ι} (hst : Disjoint s t)
    {A B : Set (Π i, X i)} (hA : DependsOn (· ∈ A) ↑s) (hB : DependsOn (· ∈ B) ↑t)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) :
    (infinitePi μ).real (A ∩ B) = (infinitePi μ).real A * (infinitePi μ).real B := by
  classical
  refine infinitePi_real_inter_of_dependsOn μ s hA (hB.mono fun i hi his => ?_) hAm hBm
  exact Finset.disjoint_left.1 hst (Finset.mem_coe.1 his) (Finset.mem_coe.1 hi)

/-! ### Sections along the gluing map -/

/-- Fubini for the gluing map, event form: `μ∞ E = ∫ μ∞ {η | s.piecewise ω η ∈ E} dμ∞(ω)`.
[cite: GrimmettPercolation1999, Thm. 2.4 (proof, (2.9))] -/
theorem infinitePi_real_eq_integral_piecewise [DecidableEq ι] (s : Finset ι) {E : Set (Π i, X i)}
    (hE : MeasurableSet E) :
    (infinitePi μ).real E =
      ∫ ω, (infinitePi μ).real ((fun η => s.piecewise ω η) ⁻¹' E) ∂infinitePi μ := by
  have hint : Integrable (E.indicator (1 : (Π i, X i) → ℝ)) (infinitePi μ) :=
    (integrable_const 1).indicator hE
  rw [← integral_indicator_one hE, ← integral_integral_piecewise μ (s := s) hint]
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  dsimp only
  rw [← integral_indicator_one ((measurable_finsetPiecewise_right s ω) hE)]
  rfl

/-! ### Nolin's generalised FKG inequality -/

/-- **Generalised FKG inequality for locally monotone events** (Nolin 2008, §4.3, EJP Lemma 13 =
arXiv Lemma 12): "Consider `A⁺, Ã⁺` two increasing events, and `A⁻, Ã⁻` two decreasing
events. Assume that there exist three disjoint finite sets of vertices `𝒜, 𝒜⁺` and `𝒜⁻` such
that `A⁺, A⁻, Ã⁺` and `Ã⁻` depend only on the sites in, respectively, `𝒜 ∪ 𝒜⁺`, `𝒜 ∪ 𝒜⁻`,
`𝒜⁺` and `𝒜⁻`. Then we have `P(Ã⁺ ∩ Ã⁻ | A⁺ ∩ A⁻) ≥ P(Ã⁺) P(Ã⁻)` for any product measure
`P`." Product form (no positivity proviso): `P(A⁺ ∩ A⁻) P(Ã⁺) P(Ã⁻) ≤ P((A⁺ ∩ A⁻) ∩ (Ã⁺ ∩ Ã⁻))`,
for the product `μ∞` of arbitrary probability measures on linearly ordered measurable spaces
(here `S = 𝒜`, `P = 𝒜⁺`, `M = 𝒜⁻`, `Ap = A⁺`, `Am = A⁻`, `Bp = Ã⁺`, `Bm = Ã⁻`). [cite: Nolin2008, §4.3, Lemma 13 (arXiv 0711.4948: Lemma 12)] -/
theorem infinitePi_locallyMonotone_fkg [∀ i, LinearOrder (X i)] {S P M : Finset ι}
    (hSP : Disjoint S P) (hSM : Disjoint S M) (hPM : Disjoint P M)
    {Ap Am Bp Bm : Set (Π i, X i)}
    (hAp : IsUpperSet Ap) (hAm : IsLowerSet Am) (hBp : IsUpperSet Bp) (hBm : IsLowerSet Bm)
    (mAp : MeasurableSet Ap) (mAm : MeasurableSet Am) (mBp : MeasurableSet Bp)
    (mBm : MeasurableSet Bm)
    (dAp : DependsOn (· ∈ Ap) (↑S ∪ ↑P)) (dAm : DependsOn (· ∈ Am) (↑S ∪ ↑M))
    (dBp : DependsOn (· ∈ Bp) ↑P) (dBm : DependsOn (· ∈ Bm) ↑M) :
    (infinitePi μ).real (Ap ∩ Am) * ((infinitePi μ).real Bp * (infinitePi μ).real Bm) ≤
      (infinitePi μ).real (Ap ∩ Am ∩ (Bp ∩ Bm)) := by
  classical
  -- notation: `Φ ω = S.piecewise ω ·` glues `ω` on `S` to an independent sample off `S`
  have mΦ : ∀ ω : Π i, X i, Measurable fun η => S.piecewise ω η :=
    fun ω => measurable_finsetPiecewise_right S ω
  -- coordinates of `P` and `M` lie outside `S`
  have hPS : ∀ {i}, i ∈ P → i ∉ S := fun hi h => Finset.disjoint_left.1 hSP h hi
  have hMS : ∀ {i}, i ∈ M → i ∉ S := fun hi h => Finset.disjoint_left.1 hSM h hi
  -- the `B`-events do not see the glued coordinates
  have ΦBp : ∀ ω η : Π i, X i, (S.piecewise ω η ∈ Bp) = (η ∈ Bp) := fun ω η =>
    dBp fun i hi => Finset.piecewise_eq_of_notMem _ _ _ (hPS (Finset.mem_coe.1 hi))
  have ΦBm : ∀ ω η : Π i, X i, (S.piecewise ω η ∈ Bm) = (η ∈ Bm) := fun ω η =>
    dBm fun i hi => Finset.piecewise_eq_of_notMem _ _ _ (hMS (Finset.mem_coe.1 hi))
  -- sections of the `A`-events: monotone, measurable, depending on `P` (resp. `M`) only
  set secP : (Π i, X i) → Set (Π i, X i) := fun ω => {η | S.piecewise ω η ∈ Ap} with hsecP
  set secM : (Π i, X i) → Set (Π i, X i) := fun ω => {η | S.piecewise ω η ∈ Am} with hsecM
  have secP_upper : ∀ ω, IsUpperSet (secP ω) := fun ω η η' hle hη =>
    hAp (Finset.piecewise_le_piecewise S le_rfl hle) hη
  have secM_lower : ∀ ω, IsLowerSet (secM ω) := fun ω η η' hle hη =>
    hAm (Finset.piecewise_le_piecewise S le_rfl hle) hη
  have secP_meas : ∀ ω, MeasurableSet (secP ω) := fun ω => (mΦ ω) mAp
  have secM_meas : ∀ ω, MeasurableSet (secM ω) := fun ω => (mΦ ω) mAm
  have agree : ∀ (T : Finset ι) (ω η η' : Π i, X i), (∀ i ∈ (↑T : Set ι), η i = η' i) →
      ∀ i ∈ (↑S ∪ ↑T : Set ι), S.piecewise ω η i = S.piecewise ω η' i := by
    intro T ω η η' h i hi
    by_cases hiS : i ∈ S
    · simp only [Finset.piecewise_eq_of_mem _ _ _ hiS]
    · simp only [Finset.piecewise_eq_of_notMem _ _ _ hiS]
      rcases hi with hi | hi
      · exact absurd (Finset.mem_coe.1 hi) hiS
      · exact h i hi
  have secP_dep : ∀ ω, DependsOn (· ∈ secP ω) ↑P := fun ω η η' h =>
    show (S.piecewise ω η ∈ Ap) = (S.piecewise ω η' ∈ Ap) from dAp (agree P ω η η' h)
  have secM_dep : ∀ ω, DependsOn (· ∈ secM ω) ↑M := fun ω η η' h =>
    show (S.piecewise ω η ∈ Am) = (S.piecewise ω η' ∈ Am) from dAm (agree M ω η η' h)
  have inter_dep : ∀ {C D : Set (Π i, X i)} {T : Set ι}, DependsOn (· ∈ C) T →
      DependsOn (· ∈ D) T → DependsOn (· ∈ C ∩ D) T := by
    intro C D T hC hD η η' h
    exact congrArg₂ (· ∧ ·) (hC h) (hD h)
  -- the pointwise (conditional) inequality
  have key : ∀ ω, (infinitePi μ).real ((fun η => S.piecewise ω η) ⁻¹' (Ap ∩ Am)) *
      ((infinitePi μ).real Bp * (infinitePi μ).real Bm) ≤
      (infinitePi μ).real ((fun η => S.piecewise ω η) ⁻¹' (Ap ∩ Am ∩ (Bp ∩ Bm))) := by
    intro ω
    have e1 : (fun η => S.piecewise ω η) ⁻¹' (Ap ∩ Am ∩ (Bp ∩ Bm)) =
        (secP ω ∩ Bp) ∩ (secM ω ∩ Bm) := by
      ext η
      simp only [Set.mem_preimage, Set.mem_inter_iff, hsecP, hsecM, Set.mem_setOf_eq]
      rw [ΦBp, ΦBm]
      tauto
    have e2 : (fun η => S.piecewise ω η) ⁻¹' (Ap ∩ Am) = secP ω ∩ secM ω := by
      ext η
      simp only [Set.mem_preimage, Set.mem_inter_iff, hsecP, hsecM, Set.mem_setOf_eq]
    rw [e1, e2,
      infinitePi_real_inter_of_dependsOn_disjoint μ hPM (inter_dep (secP_dep ω) dBp)
        (inter_dep (secM_dep ω) dBm) ((secP_meas ω).inter mBp) ((secM_meas ω).inter mBm),
      infinitePi_real_inter_of_dependsOn_disjoint μ hPM (secP_dep ω) (secM_dep ω) (secP_meas ω)
        (secM_meas ω)]
    have hP := infinitePi_harris μ (secP_upper ω) hBp (secP_meas ω) mBp
    have hM := infinitePi_harris_lower μ (secM_lower ω) hBm (secM_meas ω) mBm
    calc (infinitePi μ).real (secP ω) * (infinitePi μ).real (secM ω) *
          ((infinitePi μ).real Bp * (infinitePi μ).real Bm)
        = ((infinitePi μ).real (secP ω) * (infinitePi μ).real Bp) *
            ((infinitePi μ).real (secM ω) * (infinitePi μ).real Bm) := by ring
      _ ≤ (infinitePi μ).real (secP ω ∩ Bp) * (infinitePi μ).real (secM ω ∩ Bm) :=
          mul_le_mul hP hM (mul_nonneg measureReal_nonneg measureReal_nonneg) measureReal_nonneg
  -- integrate over `ω`
  have mD : MeasurableSet (Ap ∩ Am) := mAp.inter mAm
  have mE : MeasurableSet (Ap ∩ Am ∩ (Bp ∩ Bm)) := mD.inter (mBp.inter mBm)
  rw [infinitePi_real_eq_integral_piecewise μ S mD, infinitePi_real_eq_integral_piecewise μ S mE,
    ← integral_mul_const]
  have hmeasI : ∀ {E : Set (Π i, X i)}, MeasurableSet E →
      Measurable fun ω : Π i, X i => (infinitePi μ).real ((fun η => S.piecewise ω η) ⁻¹' E) := by
    intro E hE
    have heq : (fun ω : Π i, X i => (infinitePi μ).real ((fun η => S.piecewise ω η) ⁻¹' E)) =
        fun ω => ∫ η, E.indicator (1 : (Π i, X i) → ℝ) (S.piecewise ω η) ∂infinitePi μ := by
      funext ω
      rw [← integral_indicator_one ((mΦ ω) hE)]
      rfl
    rw [heq]
    exact measurable_integral_piecewise μ (measurable_const.indicator hE)
  have hbdI : ∀ (E : Set (Π i, X i)) (ω : Π i, X i),
      ‖(infinitePi μ).real ((fun η => S.piecewise ω η) ⁻¹' E)‖ ≤ 1 := fun E ω => by
    rw [Real.norm_of_nonneg measureReal_nonneg]; exact measureReal_le_one
  refine integral_mono ?_ ?_ key
  · refine Integrable.of_bound ((hmeasI mD).mul_const _).aestronglyMeasurable (1 * 1)
      (ae_of_all _ fun ω => ?_)
    rw [norm_mul]
    refine mul_le_mul (hbdI _ ω) ?_ (norm_nonneg _) zero_le_one
    rw [Real.norm_of_nonneg (mul_nonneg measureReal_nonneg measureReal_nonneg)]
    exact mul_le_one₀ measureReal_le_one measureReal_nonneg measureReal_le_one
  · exact .of_bound (hmeasI mE).aestronglyMeasurable 1 (ae_of_all _ (hbdI _))

end Product

/-! ### Bernoulli site percolation -/

section Site

variable {V : Type*}

/-- **Nolin's generalised FKG inequality for Bernoulli site percolation** (Nolin 2008, EJP
Lemma 13 = arXiv Lemma 12, the case of `P_p`; Nolin states it for any product measure on the
sites of the triangular lattice): for three pairwise disjoint finite sets of sites `S, P, M`, an
increasing event `A⁺` and a decreasing event `A⁻` determined by the sites of `S ∪ P`, resp.
`S ∪ M`, and an increasing event `Ã⁺` and a decreasing event `Ã⁻` determined by the sites of
`P`, resp. `M`, `P_p(A⁺ ∩ A⁻) P_p(Ã⁺) P_p(Ã⁻) ≤ P_p((A⁺ ∩ A⁻) ∩ (Ã⁺ ∩ Ã⁻))`. [cite: Nolin2008, §4.3, Lemma 13 (arXiv 0711.4948: Lemma 12)] -/
theorem sitePercolation_locallyMonotone_fkg (p : unitInterval) {S P M : Finset V}
    (hSP : Disjoint S P) (hSM : Disjoint S M) (hPM : Disjoint P M)
    {Ap Am Bp Bm : Set (SiteConfig V)}
    (hAp : IsUpperSet Ap) (hAm : IsLowerSet Am) (hBp : IsUpperSet Bp) (hBm : IsLowerSet Bm)
    (dAp : DeterminedBy Ap (↑S ∪ ↑P)) (dAm : DeterminedBy Am (↑S ∪ ↑M))
    (dBp : DeterminedBy Bp ↑P) (dBm : DeterminedBy Bm ↑M) :
    (sitePercolation V p).real (Ap ∩ Am) *
        ((sitePercolation V p).real Bp * (sitePercolation V p).real Bm) ≤
      (sitePercolation V p).real (Ap ∩ Am ∩ (Bp ∩ Bm)) := by
  classical
  -- transport to the product measure `sitePi V p` on `V → Prop` along `χ ↦ {v | χ v}`
  set mk : (V → Prop) → SiteConfig V := fun χ => {v | χ v} with hmk
  have hmk_meas : Measurable mk := measurable_setOf
  have hmono : Monotone mk := fun χ χ' h v (hv : χ v) => h v hv
  have hreal : ∀ A : Set (SiteConfig V),
      (sitePercolation V p).real A = (sitePi V p).real (mk ⁻¹' A) := fun A => by
    simp only [measureReal_def, sitePercolation_apply', hmk]
  have hup : ∀ {A : Set (SiteConfig V)}, IsUpperSet A → IsUpperSet (mk ⁻¹' A) :=
    fun hA χ χ' h hχ => hA (hmono h) hχ
  have hlow : ∀ {A : Set (SiteConfig V)}, IsLowerSet A → IsLowerSet (mk ⁻¹' A) :=
    fun hA χ χ' h hχ => hA (hmono h) hχ
  have hdep : ∀ {A : Set (SiteConfig V)} {F : Set V}, DeterminedBy A F →
      DependsOn (· ∈ mk ⁻¹' A) F := fun hA χ χ' h => hA h
  have hSP' : DeterminedBy Ap ↑(S ∪ P) := by simpa only [Finset.coe_union] using dAp
  have hSM' : DeterminedBy Am ↑(S ∪ M) := by simpa only [Finset.coe_union] using dAm
  have hmeas : ∀ {A : Set (SiteConfig V)} {F : Finset V}, DeterminedBy A ↑F →
      MeasurableSet (mk ⁻¹' A) := fun hA => hmk_meas hA.measurableSet_of_finset
  rw [hreal, hreal, hreal, hreal, Set.preimage_inter, Set.preimage_inter, Set.preimage_inter]
  exact infinitePi_locallyMonotone_fkg (fun _ : V => bernoulliProp p) hSP hSM hPM (hup hAp)
    (hlow hAm) (hup hBp) (hlow hBm) (hmeas hSP') (hmeas hSM') (hmeas dBp) (hmeas dBm) (hdep dAp)
    (hdep dAm) (hdep dBp) (hdep dBm)

end Site

end

end Percolation.Literature
