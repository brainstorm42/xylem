import Percolation.Literature.KozmaNitzanReduction
import Percolation.Literature.LatticeModels.ProdBernoulliClusterLocality
import Percolation.Literature.LatticeModels.ProdBernoulliCoupling
import Percolation.Literature.SharpnessDCTProofs
import Percolation.Literature.SubgraphMonotonicity
import Percolation.Util.Linter

/-!
# Kozma–Nitzan, Theorem 6 — toolkit I: pinned and wired weightings; Conjecture 3 on any finite graph

First proofs-only companion of
`KozmaNitzanReduction.lean` (G. Kozma, S. Nitzan, *A reduction of the `θ(p_c) = 0` problem to a
conjectured inequality*, arXiv:2401.12397, §4), on the way to the discharge
`KozmaNitzan2024_thm6_holds`. The printed proof of Theorem 6 (pp. 15–31) repeatedly performs two
operations on a percolation measure with independent edges:

* **conditioning on the states of all edges of a finite set `F`** ("`P(· | ω|_D)`", eq. (30);
  "for `ξ ⊆ E(S)` … the event that all edges in `ξ` are open and all other edges in `E(S)` are
  closed", p. 20), and
* **contracting a set of vertices to a point** ("identifying the cube `[-n,n]^d` to a point",
  p. 22; "we identified the set `T` to a point and used that point as the `b` of conjecture 3",
  p. 22; the graphs `K_ξ`, p. 20).

For a product measure `prodBernoulli w` on `Set ι` both are changes of the WEIGHTS: conditioning on
`ω ∩ F = ξ` is the weighting `pinW w F ξ` (weight `1` on `ξ ∩ F`, `0` on `F \ ξ`, unchanged off
`F`), and contracting `T` is, as far as connection probabilities to/through `T` are concerned, the
weighting `wireW T w` (weight `1` on every pair inside `T`).

## References

* G. Kozma, S. Nitzan, arXiv:2401.12397 (2024), §2.1 (percolation measures with arbitrary edge
  probabilities), §4 pp. 17–22 (proof of Lemma 10, Steps IV–V), p. 27 (eq. (30)).
* G. Grimmett, *Percolation*, 2nd ed. (1999), §1.3 (product measure), §2.2 (cylinder events).
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Percolation.Literature

open LatticeModels

/-! ## Pinned weightings: conditioning on the states of finitely many coordinates -/

section Pin

variable {ι : Type*}

open Classical in
/-- **Pinned weights**: the coordinates of `F` are forced open on `ξ` and closed off `ξ`, the
others keep their weight. `prodBernoulli (pinW w F ξ)` is the conditional law of `prodBernoulli w`
given `ω ∩ F = ξ ∩ F` (Kozma–Nitzan 2024, p. 20: the events "`ξ`" for `ξ ⊆ E(S)`, and the graphs
`K_ξ`). [cite: KozmaNitzan2024, §4 p. 20 (Step IV–V)] -/
def pinW (w : ι → unitInterval) (F ξ : Set ι) : ι → unitInterval :=
  fun i => if i ∈ F then (if i ∈ ξ then 1 else 0) else w i

open Classical in
/-- Unfolding of `pinW`. [folklore] -/
theorem pinW_apply (w : ι → unitInterval) (F ξ : Set ι) (i : ι) :
    pinW w F ξ i = if i ∈ F then (if i ∈ ξ then 1 else 0) else w i := by
  simp only [pinW]

/-- Off `F` the weights are unchanged. [folklore] -/
theorem pinW_apply_of_not_mem (w : ι → unitInterval) {F : Set ι} (ξ : Set ι) {i : ι} (hi : i ∉ F) :
    pinW w F ξ i = w i := by
  classical
  simp [pinW_apply, hi]

/-- On `ξ ∩ F` the weight is `1`. [folklore] -/
theorem pinW_apply_of_mem_of_mem (w : ι → unitInterval) {F ξ : Set ι} {i : ι} (hi : i ∈ F)
    (hξ : i ∈ ξ) : pinW w F ξ i = 1 := by
  classical
  simp [pinW_apply, hi, hξ]

/-- On `F \ ξ` the weight is `0`. [folklore] -/
theorem pinW_apply_of_mem_of_not_mem (w : ι → unitInterval) {F ξ : Set ι} {i : ι} (hi : i ∈ F)
    (hξ : i ∉ ξ) : pinW w F ξ i = 0 := by
  classical
  simp [pinW_apply, hi, hξ]

/-- The pinned weights only depend on the pattern `ξ ∩ F`. [folklore] -/
theorem pinW_congr (w : ι → unitInterval) {F ξ ξ' : Set ι} (h : ∀ i ∈ F, i ∈ ξ ↔ i ∈ ξ') :
    pinW w F ξ = pinW w F ξ' := by
  classical
  funext i
  by_cases hi : i ∈ F
  · simp [pinW_apply, hi, h i hi]
  · simp [pinW_apply, hi]

/-- A coordinate with parameter `1` is almost surely present. [cite: GrimmettPercolation1999, §1.3 p. 10] -/
theorem prodBernoulli_ae_mem_of_eq_one (p : ι → unitInterval) {i : ι} (hi : p i = 1) :
    ∀ᵐ ω ∂prodBernoulli p, i ∈ ω := by
  rw [ae_iff]
  have h := prodBernoulli_real_setOf_notMem p i
  rw [hi] at h
  have : (prodBernoulli p).real {ω | i ∉ ω} = 0 := by simpa using h
  exact (measureReal_eq_zero_iff (measure_ne_top _ _)).1 this

/-- **Under the pinned law the pattern on `F` is almost surely `ξ`** (`F` countable).
[cite: KozmaNitzan2024, §4 p. 20] -/
theorem prodBernoulli_pinW_ae_localCylinder (w : ι → unitInterval) {F : Set ι} (hF : F.Countable)
    (ξ : Set ι) : ∀ᵐ ω ∂prodBernoulli (pinW w F ξ), ω ∈ localCylinder F ξ := by
  have : Countable F := hF.to_subtype
  have h : ∀ i : F, ∀ᵐ ω ∂prodBernoulli (pinW w F ξ), ((i : ι) ∈ ω ↔ (i : ι) ∈ ξ) := by
    intro i
    by_cases hξ : (i : ι) ∈ ξ
    · filter_upwards [prodBernoulli_ae_mem_of_eq_one (pinW w F ξ)
        (pinW_apply_of_mem_of_mem w i.2 hξ)] with ω hω using iff_of_true hω hξ
    · filter_upwards [prodBernoulli_ae_notMem (pinW w F ξ)
        (pinW_apply_of_mem_of_not_mem w i.2 hξ)] with ω hω using iff_of_false hω hξ
  filter_upwards [ae_all_iff.2 h] with ω hω i hi using hω ⟨i, hi⟩

/-- Consequence: pinned probabilities may be computed inside the cylinder `[ξ]_F`.
[cite: KozmaNitzan2024, §4 p. 20] -/
theorem prodBernoulli_pinW_real_inter_localCylinder (w : ι → unitInterval) {F : Set ι}
    (hF : F.Countable) (ξ : Set ι) (A : Set (Set ι)) :
    (prodBernoulli (pinW w F ξ)).real (A ∩ localCylinder F ξ) =
      (prodBernoulli (pinW w F ξ)).real A := by
  refine measureReal_congr ?_
  filter_upwards [prodBernoulli_pinW_ae_localCylinder w hF ξ] with ω hω
  exact propext ⟨fun h => h.1, fun h => ⟨h, hω⟩⟩

/-! ### Overwriting the pattern on `F` -/

/-- The configuration `ω` with its pattern on `F` replaced by `ξ`. [folklore] -/
def overwrite (F ξ ω : Set ι) : Set ι := (ω \ F) ∪ (ξ ∩ F)

/-- Membership in the overwritten configuration. [folklore] -/
theorem mem_overwrite_iff {F ξ ω : Set ι} {i : ι} :
    i ∈ overwrite F ξ ω ↔ (i ∈ ω ∧ i ∉ F) ∨ (i ∈ ξ ∧ i ∈ F) := by
  simp [overwrite]

/-- On `F` the overwritten configuration is `ξ`. [folklore] -/
theorem mem_overwrite_iff_of_mem {F ξ ω : Set ι} {i : ι} (hi : i ∈ F) :
    i ∈ overwrite F ξ ω ↔ i ∈ ξ := by
  rw [mem_overwrite_iff]; tauto

/-- Off `F` the overwritten configuration is `ω`. [folklore] -/
theorem mem_overwrite_iff_of_not_mem {F ξ ω : Set ι} {i : ι} (hi : i ∉ F) :
    i ∈ overwrite F ξ ω ↔ i ∈ ω := by
  rw [mem_overwrite_iff]; tauto

/-- Inside the cylinder, overwriting does nothing. [folklore] -/
theorem overwrite_eq_self_of_mem {F ξ ω : Set ι} (h : ω ∈ localCylinder F ξ) :
    overwrite F ξ ω = ω := by
  ext i
  by_cases hi : i ∈ F
  · rw [mem_overwrite_iff_of_mem hi]; exact (h i hi).symm
  · exact mem_overwrite_iff_of_not_mem hi

/-- `overwrite F ξ` is measurable. [folklore] -/
theorem measurable_overwrite (F ξ : Set ι) : Measurable (overwrite F ξ : Set ι → Set ι) := by
  classical
  refine measurable_set_iff.2 fun i => ?_
  by_cases hi : i ∈ F
  · have : (fun ω : Set ι => i ∈ overwrite F ξ ω) = fun _ => i ∈ ξ := by
      funext ω; exact propext (mem_overwrite_iff_of_mem hi)
    rw [this]; exact measurable_const
  · have : (fun ω : Set ι => i ∈ overwrite F ξ ω) = fun ω => i ∈ ω := by
      funext ω; exact propext (mem_overwrite_iff_of_not_mem hi)
    rw [this]; exact measurable_set_mem i

/-- The pull-back of any event along `overwrite F ξ` is determined by `Fᶜ`. [folklore] -/
theorem determinedBy_preimage_overwrite (F ξ : Set ι) (A : Set (Set ι)) :
    DeterminedBy (overwrite F ξ ⁻¹' A) Fᶜ := by
  rw [determinedBy_iff]
  intro ω ω' h
  have : overwrite F ξ ω = overwrite F ξ ω' := by
    ext i
    by_cases hi : i ∈ F
    · rw [mem_overwrite_iff_of_mem hi, mem_overwrite_iff_of_mem hi]
    · rw [mem_overwrite_iff_of_not_mem hi, mem_overwrite_iff_of_not_mem hi]
      have h1 := Set.ext_iff.1 h i
      simp only [Set.mem_inter_iff, Set.mem_compl_iff] at h1
      tauto
  simp only [Set.mem_preimage, this]

/-- On the cylinder `[ξ]_F`, an event and its overwritten pull-back agree. [folklore] -/
theorem inter_localCylinder_eq_preimage_overwrite_inter (F ξ : Set ι) (A : Set (Set ι)) :
    A ∩ localCylinder F ξ = overwrite F ξ ⁻¹' A ∩ localCylinder F ξ := by
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_preimage]
  constructor
  · rintro ⟨hA, hc⟩; exact ⟨by rwa [overwrite_eq_self_of_mem hc], hc⟩
  · rintro ⟨hA, hc⟩; exact ⟨by rwa [overwrite_eq_self_of_mem hc] at hA, hc⟩

/-- Cylinders over `F` are determined by `F`. [folklore] -/
theorem determinedBy_localCylinder (F ξ : Set ι) : DeterminedBy (localCylinder F ξ) F := by
  rw [determinedBy_iff]
  intro ω ω' h
  have h1 : ∀ i ∈ F, (i ∈ ω ↔ i ∈ ω') := fun i hi => by
    have := Set.ext_iff.1 h i
    simp only [Set.mem_inter_iff] at this
    tauto
  exact ⟨fun hω i hi => (h1 i hi).symm.trans (hω i hi), fun hω i hi => (h1 i hi).trans (hω i hi)⟩

/-! ### The law of total probability over the patterns on `F` -/

/-- **Conditioning on the pattern of `F` is pinning**: for a finite set `F` of coordinates, a
pattern `ξ` and a measurable event `A`,
`P_w(A ∩ [ξ]_F) = P_w([ξ]_F) · P_{pinW w F ξ}(A)`.
Proof: on `[ξ]_F` the event `A` coincides with the pull-back `A'` of `A` along `overwrite F ξ`,
which is determined by `Fᶜ`, hence independent of `[ξ]_F` (Grimmett 1999, §2.2); and
`P_w(A') = P_{pin}(A') = P_{pin}(A)` because the two weightings agree off `F` and the pinned law
lives on `[ξ]_F`. [cite: KozmaNitzan2024, §4 p. 20 (Step IV: Σ_ξ p_ξ P(G(v) | ξ))] -/
theorem prodBernoulli_real_inter_localCylinder (w : ι → unitInterval) (F : Finset ι) (ξ : Set ι)
    {A : Set (Set ι)} (hA : MeasurableSet A) :
    (prodBernoulli w).real (A ∩ localCylinder ↑F ξ) =
      (prodBernoulli w).real (localCylinder ↑F ξ) * (prodBernoulli (pinW w ↑F ξ)).real A := by
  have hcylm : MeasurableSet (localCylinder (↑F : Set ι) ξ) :=
    measurableSet_localCylinder F.finite_toSet.countable ξ
  have hA'm : MeasurableSet (overwrite (↑F : Set ι) ξ ⁻¹' A) := measurable_overwrite _ _ hA
  have hA'd := determinedBy_preimage_overwrite (↑F : Set ι) ξ A
  rw [inter_localCylinder_eq_preimage_overwrite_inter, Set.inter_comm,
    prodBernoulli_real_inter_of_determinedBy w F (determinedBy_localCylinder _ _) hA'd hcylm hA'm]
  congr 1
  -- `P_w(A') = P_pin(A') = P_pin(A' ∩ cyl) = P_pin(A ∩ cyl) = P_pin(A)`
  rw [prodBernoulli_real_eq_of_determinedBy w (pinW w ↑F ξ) (F := (↑F : Set ι)ᶜ)
      (fun i hi => (pinW_apply_of_not_mem w ξ hi).symm) hA'd hA'm,
    ← prodBernoulli_pinW_real_inter_localCylinder w F.finite_toSet.countable ξ (overwrite ↑F ξ ⁻¹' A),
    ← inter_localCylinder_eq_preimage_overwrite_inter,
    prodBernoulli_pinW_real_inter_localCylinder w F.finite_toSet.countable ξ A]

/-- The cylinders over a finite `F`, indexed by the subsets of `F`, partition the space: the
pattern of `ω` is `F ∩ ω`. [folklore] -/
theorem mem_localCylinder_filter (F : Finset ι) (ω : Set ι) [DecidablePred (· ∈ ω)] :
    ω ∈ localCylinder (↑F : Set ι) ↑(F.filter (· ∈ ω)) := by
  intro i hi
  simp [Finset.mem_coe.1 hi]

/-- Distinct patterns give disjoint cylinders. [folklore] -/
theorem localCylinder_disjoint {F : Finset ι} {T T' : Finset ι} (hT : T ⊆ F) (hT' : T' ⊆ F)
    (hne : T ≠ T') : Disjoint (localCylinder (↑F : Set ι) ↑T) (localCylinder (↑F : Set ι) ↑T') := by
  rw [Set.disjoint_left]
  intro ω h h'
  apply hne
  ext i
  constructor
  · intro hi
    have h1 := (h i (hT hi)).2 (Finset.mem_coe.2 hi)
    exact Finset.mem_coe.1 ((h' i (hT hi)).1 h1)
  · intro hi
    have h1 := (h' i (hT' hi)).2 (Finset.mem_coe.2 hi)
    exact Finset.mem_coe.1 ((h i (hT' hi)).1 h1)

/-- On the cylinder `[T]_F` an event determined by `F` holds iff its pattern `T` does.
[folklore] -/
theorem mem_iff_coe_mem_of_determinedBy {B : Set (Set ι)} {F : Finset ι}
    (hB : DeterminedBy B (↑F : Set ι)) {T : Finset ι} (hT : T ⊆ F) {ω : Set ι}
    (hω : ω ∈ localCylinder (↑F : Set ι) ↑T) : ω ∈ B ↔ (↑T : Set ι) ∈ B := by
  refine (determinedBy_iff _ _).1 hB ω ↑T ?_
  ext i
  simp only [Set.mem_inter_iff, Finset.mem_coe]
  constructor
  · rintro ⟨hiω, hiF⟩; exact ⟨Finset.mem_coe.1 ((hω i (Finset.mem_coe.2 hiF)).1 hiω), hiF⟩
  · rintro ⟨hiT, hiF⟩; exact ⟨(hω i (Finset.mem_coe.2 hiF)).2 (Finset.mem_coe.2 hiT), hT hiT⟩

open Classical in
/-- **Law of total probability over the patterns of `F`** (finite): for `A` measurable and `B`
determined by `F`,
`P_w(A ∩ B) = Σ_{T ⊆ F, T ∈ B} P_w([T]_F) · P_{pinW w F T}(A)`
(Kozma–Nitzan 2024, p. 20: "`Σ_{ξ ⊆ E(S)} p_ξ P(G(v) | ξ)`"; p. 22: "summing over `ξ`").
[cite: KozmaNitzan2024, §4 pp. 20–22] -/
theorem prodBernoulli_real_inter_eq_sum_pinW (w : ι → unitInterval) (F : Finset ι)
    {A B : Set (Set ι)} (hA : MeasurableSet A) (hB : DeterminedBy B (↑F : Set ι)) :
    (prodBernoulli w).real (A ∩ B) =
      ∑ T ∈ F.powerset.filter (fun T : Finset ι => (↑T : Set ι) ∈ B),
        (prodBernoulli w).real (localCylinder ↑F ↑T) * (prodBernoulli (pinW w ↑F ↑T)).real A := by
  have hBm : MeasurableSet B := hB.measurableSet_of_finset
  -- `A ∩ B` is the disjoint union over the good patterns of `A ∩ [T]_F`
  have hdec : A ∩ B = ⋃ T ∈ F.powerset.filter (fun T : Finset ι => (↑T : Set ι) ∈ B),
      A ∩ localCylinder (↑F : Set ι) ↑T := by
    ext ω
    constructor
    · rintro ⟨hωA, hωB⟩
      have hT : F.filter (· ∈ ω) ⊆ F := Finset.filter_subset _ _
      have hω : ω ∈ localCylinder (↑F : Set ι) ↑(F.filter (· ∈ ω)) := mem_localCylinder_filter F ω
      refine Set.mem_iUnion₂.2 ⟨F.filter (· ∈ ω), ?_, hωA, hω⟩
      exact Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hT, (mem_iff_coe_mem_of_determinedBy hB hT hω).1 hωB⟩
    · intro hω
      obtain ⟨T, hT, hωA, hωT⟩ := Set.mem_iUnion₂.1 hω
      obtain ⟨hTF, hTB⟩ := Finset.mem_filter.1 hT
      exact ⟨hωA, (mem_iff_coe_mem_of_determinedBy hB (Finset.mem_powerset.1 hTF) hωT).2 hTB⟩
  rw [hdec, measureReal_biUnion_finset]
  · refine Finset.sum_congr rfl fun T _ => ?_
    exact prodBernoulli_real_inter_localCylinder w F ↑T hA
  · intro T hT T' hT' hne
    have h1 : T ⊆ F := Finset.mem_powerset.1 (Finset.mem_filter.1 (Finset.mem_coe.1 hT)).1
    have h2 : T' ⊆ F := Finset.mem_powerset.1 (Finset.mem_filter.1 (Finset.mem_coe.1 hT')).1
    exact (localCylinder_disjoint h1 h2 hne).mono Set.inter_subset_right Set.inter_subset_right
  · intro T _
    exact hA.inter (measurableSet_localCylinder F.finite_toSet.countable _)

open Classical in
/-- The case `A = univ`: `P_w(B) = Σ_{T ⊆ F, T ∈ B} P_w([T]_F)`. [folklore] -/
theorem prodBernoulli_real_eq_sum_localCylinder (w : ι → unitInterval) (F : Finset ι)
    {B : Set (Set ι)} (hB : DeterminedBy B (↑F : Set ι)) :
    (prodBernoulli w).real B =
      ∑ T ∈ F.powerset.filter (fun T : Finset ι => (↑T : Set ι) ∈ B),
        (prodBernoulli w).real (localCylinder ↑F ↑T) := by
  have := prodBernoulli_real_inter_eq_sum_pinW w F MeasurableSet.univ hB
  rw [Set.univ_inter] at this
  rw [this]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [probReal_univ, mul_one]

open Classical in
/-- **Transfer of an upper bound on the conditional probabilities**: if `P_{pin T}(A) ≤ c` for
every pattern `T ⊆ F` with `T ∈ B`, then `P_w(A ∩ B) ≤ c · P_w(B)`. [cite: KozmaNitzan2024, §4 p. 21] -/
theorem prodBernoulli_real_inter_le_of_pinW_le (w : ι → unitInterval) (F : Finset ι)
    {A B : Set (Set ι)} (hA : MeasurableSet A) (hB : DeterminedBy B (↑F : Set ι)) {c : ℝ}
    (h : ∀ T ⊆ F, (↑T : Set ι) ∈ B → (prodBernoulli (pinW w ↑F ↑T)).real A ≤ c) :
    (prodBernoulli w).real (A ∩ B) ≤ c * (prodBernoulli w).real B := by
  rw [prodBernoulli_real_inter_eq_sum_pinW w F hA hB, prodBernoulli_real_eq_sum_localCylinder w F hB,
    Finset.mul_sum]
  refine Finset.sum_le_sum fun T hT => ?_
  obtain ⟨hT1, hT2⟩ := Finset.mem_filter.1 hT
  rw [mul_comm c]
  exact mul_le_mul_of_nonneg_left (h T (Finset.mem_powerset.1 hT1) hT2) measureReal_nonneg

/-! ### The event "the conditional probability of `A` given `ω|_F` is low" -/

/-- `pinLow w F A δ`: the configurations `ω` for which `P_w(A | ω|_F) ≤ 1 - δ`, i.e.
`P_{pinW w F ω}(A) ≤ 1 - δ` (Kozma–Nitzan 2024, p. 30: the events `B_j`).
[cite: KozmaNitzan2024, §4 p. 30 (events B_j)] -/
def pinLow (w : ι → unitInterval) (F : Set ι) (A : Set (Set ι)) (δ : ℝ) : Set (Set ι) :=
  {ω | (prodBernoulli (pinW w F ω)).real A ≤ 1 - δ}

/-- Membership in `pinLow`. [folklore] -/
theorem mem_pinLow_iff {w : ι → unitInterval} {F : Set ι} {A : Set (Set ι)} {δ : ℝ} {ω : Set ι} :
    ω ∈ pinLow w F A δ ↔ (prodBernoulli (pinW w F ω)).real A ≤ 1 - δ := Iff.rfl

/-- `pinLow` is determined by `F`. [folklore] -/
theorem determinedBy_pinLow (w : ι → unitInterval) (F : Set ι) (A : Set (Set ι)) (δ : ℝ) :
    DeterminedBy (pinLow w F A δ) F := by
  rw [determinedBy_iff]
  intro ω ω' h
  have : pinW w F ω = pinW w F ω' := pinW_congr w fun i hi => by
    have := Set.ext_iff.1 h i
    simp only [Set.mem_inter_iff] at this
    tauto
  simp only [mem_pinLow_iff, this]

/-- **Markov-type bound** (how (21) gives (24), and how the set `W` is estimated on p. 21): for
`A` measurable, `B` determined by the finite `F` and `δ > 0`… in the form
`δ · P_w(B ∩ {P(A | ω|_F) ≤ 1 - δ}) ≤ P_w(B) - P_w(A ∩ B)`.
[cite: KozmaNitzan2024, §4 pp. 20–21 ((21) ⟹ (24); the set W)] -/
theorem prodBernoulli_real_pinLow_le (w : ι → unitInterval) (F : Finset ι) {A B : Set (Set ι)}
    (hA : MeasurableSet A) (hB : DeterminedBy B (↑F : Set ι)) (δ : ℝ) :
    δ * (prodBernoulli w).real (B ∩ pinLow w ↑F A δ) ≤
      (prodBernoulli w).real B - (prodBernoulli w).real (A ∩ B) := by
  set L := pinLow w (↑F : Set ι) A δ with hL
  have hBL : DeterminedBy (B ∩ L) (↑F : Set ι) := hB.inter (determinedBy_pinLow w _ A δ)
  have hBm : MeasurableSet B := hB.measurableSet_of_finset
  have hBLm : MeasurableSet (B ∩ L) := hBL.measurableSet_of_finset
  -- `P(A ∩ (B ∩ L)) ≤ (1 - δ) P(B ∩ L)`
  have h1 : (prodBernoulli w).real (A ∩ (B ∩ L)) ≤ (1 - δ) * (prodBernoulli w).real (B ∩ L) := by
    refine prodBernoulli_real_inter_le_of_pinW_le w F hA hBL fun T _ hT => ?_
    have hT2 : (↑T : Set ι) ∈ L := hT.2
    exact hT2
  -- `P(B ∩ L) - P(A ∩ B ∩ L) ≤ P(B) - P(A ∩ B)`
  have h2 : (prodBernoulli w).real (B ∩ L) - (prodBernoulli w).real (A ∩ (B ∩ L)) ≤
      (prodBernoulli w).real B - (prodBernoulli w).real (A ∩ B) := by
    have e1 : (prodBernoulli w).real (B ∩ L) =
        (prodBernoulli w).real (A ∩ (B ∩ L)) + (prodBernoulli w).real ((B ∩ L) \ A) := by
      rw [← measureReal_inter_add_sdiff (s := B ∩ L) hA, Set.inter_comm]
    have e2 : (prodBernoulli w).real B =
        (prodBernoulli w).real (A ∩ B) + (prodBernoulli w).real (B \ A) := by
      rw [← measureReal_inter_add_sdiff (s := B) hA, Set.inter_comm]
    have e3 : (prodBernoulli w).real ((B ∩ L) \ A) ≤ (prodBernoulli w).real (B \ A) :=
      measureReal_mono (Set.sdiff_subset_sdiff_left Set.inter_subset_left)
    linarith
  nlinarith [h1, h2, measureReal_nonneg (μ := prodBernoulli w) (s := B ∩ L)]

/-- The case `B = univ`: `δ · P_w{P(A | ω|_F) ≤ 1 - δ} ≤ 1 - P_w(A)`.
[cite: KozmaNitzan2024, §4 pp. 20–21] -/
theorem prodBernoulli_real_pinLow_le' (w : ι → unitInterval) (F : Finset ι) {A : Set (Set ι)}
    (hA : MeasurableSet A) (δ : ℝ) :
    δ * (prodBernoulli w).real (pinLow w ↑F A δ) ≤ 1 - (prodBernoulli w).real A := by
  have := prodBernoulli_real_pinLow_le w F hA (determinedBy_univ _) δ
  rwa [Set.univ_inter, Set.inter_univ, probReal_univ] at this

end Pin

/-! ## Paths of a superposed configuration that avoid the added edges -/

section Paths

variable {V : Type*}

/-- A path of the open graph of `ω ∪ E` inside a vertex set `A`, no two vertices of which span an
edge of `E`, is a path of the open graph of `ω`. [folklore] -/
theorem pathIn_of_pathIn_union {ω E : Set (Sym2 V)} {A : Set V} {u v : V}
    (h : PathIn (openGraph (ω ∪ E)) A u v) (hE : ∀ x ∈ A, ∀ y ∈ A, s(x, y) ∉ E) :
    PathIn (openGraph ω) A u v := by
  obtain ⟨hu, h⟩ := h
  refine ⟨hu, ?_⟩
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hab hbc ih =>
    have hb : b ∈ A := (show PathIn (openGraph (ω ∪ E)) A u b from ⟨hu, hab⟩).right_mem
    refine ih.tail ⟨?_, hbc.2⟩
    have h1 := hbc.1
    rw [openGraph_adj] at h1 ⊢
    refine ⟨?_, h1.2⟩
    rcases h1.1 with h2 | h2
    · exact h2
    · exact absurd h2 (hE b hb c hbc.2)

/-- A path of the open graph all of whose vertices lie in `A` gives reachability. [folklore] -/
theorem reachable_of_pathIn {ω : Set (Sym2 V)} {A : Set V} {u v : V}
    (h : PathIn (openGraph ω) A u v) : (openGraph ω).Reachable u v := by
  obtain ⟨-, h⟩ := h
  induction h with
  | refl => exact SimpleGraph.Reachable.refl _
  | tail _ hbc ih => exact ih.trans hbc.1.reachable

end Paths

/-! ## Wired weightings: contracting a set of vertices -/

section Wire

variable {V : Type*}

/-- The pairs of distinct vertices inside `T`. [folklore] -/
def wireSet (T : Set V) : Set (Sym2 V) := {e | (∀ x ∈ e, x ∈ T) ∧ ¬ e.IsDiag}

/-- Membership of a pair in `wireSet`. [folklore] -/
theorem mk_mem_wireSet_iff {T : Set V} {x y : V} : s(x, y) ∈ wireSet T ↔ x ∈ T ∧ y ∈ T ∧ x ≠ y := by
  simp only [wireSet, Set.mem_setOf_eq, Sym2.mem_iff, forall_eq_or_imp, forall_eq, Sym2.mk_isDiag_iff]
  tauto

open Classical in
/-- **Wired weights**: every pair of distinct vertices of `T` gets weight `1`; this realises the
contraction of `T` to a single vertex as far as connections to or through `T` are concerned
(Kozma–Nitzan 2024, p. 22: "we identified the set `T` to a point"; p. 22, proof of Lemma 11:
"identifying the cube `[-n, n]^d` to a point (which will be `o`)").
[cite: KozmaNitzan2024, §4 p. 22] -/
def wireW (T : Set V) (w : Sym2 V → unitInterval) : Sym2 V → unitInterval :=
  fun e => if e ∈ wireSet T then 1 else w e

/-- Wired pairs have weight `1`. [folklore] -/
theorem wireW_apply_of_mem {T : Set V} (w : Sym2 V → unitInterval) {e : Sym2 V} (he : e ∈ wireSet T) :
    wireW T w e = 1 := by
  classical
  simp [wireW, he]

/-- Unwired pairs keep their weight. [folklore] -/
theorem wireW_apply_of_not_mem {T : Set V} (w : Sym2 V → unitInterval) {e : Sym2 V}
    (he : e ∉ wireSet T) : wireW T w e = w e := by
  classical
  simp [wireW, he]

/-- Wiring only raises weights. [folklore] -/
theorem le_wireW (T : Set V) (w : Sym2 V → unitInterval) : w ≤ wireW T w := by
  classical
  intro e
  by_cases he : e ∈ wireSet T
  · rw [wireW_apply_of_mem w he]; exact le_top
  · rw [wireW_apply_of_not_mem w he]

/-- The superposition map `ω ↦ ω ∪ E` is measurable. [folklore] -/
theorem measurable_union_right_const (E : Set (Sym2 V)) : Measurable fun ω : Set (Sym2 V) => ω ∪ E := by
  classical
  refine measurable_set_iff.2 fun e => ?_
  by_cases he : e ∈ E
  · have : (fun ω : Set (Sym2 V) => e ∈ ω ∪ E) = fun _ => True := by
      funext ω; exact propext (iff_of_true (Or.inr he) trivial)
    rw [this]; exact measurable_const
  · have : (fun ω : Set (Sym2 V) => e ∈ ω ∪ E) = fun ω => e ∈ ω := by
      funext ω; exact propext ⟨fun h => h.resolve_right he, fun h => Or.inl h⟩
    rw [this]; exact measurable_set_mem e

/-- The pull-back of any event along `ω ↦ ω ∪ E` is determined by `Eᶜ`. [folklore] -/
theorem determinedBy_preimage_union_const (E : Set (Sym2 V)) (A : Set (Set (Sym2 V))) :
    DeterminedBy ((fun ω : Set (Sym2 V) => ω ∪ E) ⁻¹' A) Eᶜ := by
  rw [determinedBy_iff]
  intro ω ω' h
  have : ω ∪ E = ω' ∪ E := by
    ext e
    by_cases he : e ∈ E
    · simp [he]
    · have h1 := Set.ext_iff.1 h e
      simp only [Set.mem_inter_iff, Set.mem_compl_iff] at h1
      simp only [Set.mem_union, he, or_false]
      tauto
  simp only [Set.mem_preimage, this]

/-- **The wiring identity for events**: `o` is joined to `t₀ ∈ T` in `ω ∪ wireSet T` iff `o` is
joined to SOME vertex of `T` in `ω` (stop an open path at its first vertex in `T`).
[cite: KozmaNitzan2024, §4 p. 22] -/
theorem preimage_union_wireSet_openConn (T : Set V) {t₀ : V} (ht₀ : t₀ ∈ T) (o : V) :
    (fun ω : Set (Sym2 V) => ω ∪ wireSet T) ⁻¹' openConn o t₀ = ⋃ t ∈ T, openConn o t := by
  ext ω
  simp only [Set.mem_preimage, Set.mem_iUnion, exists_prop]
  constructor
  · intro h
    change (openGraph (ω ∪ wireSet T)).Reachable o t₀ at h
    by_cases ho : o ∈ T
    · exact ⟨o, ho, SimpleGraph.Reachable.refl _⟩
    · have hp := DCT16.pathIn_univ_of_reachable h
      obtain ⟨a, b, ha, hb, -, hab, hpa⟩ := hp.exit (R := Tᶜ) ho (fun h' => h' ht₀)
      simp only [Set.mem_compl_iff, not_not] at hb
      refine ⟨b, hb, ?_⟩
      have hpa' : PathIn (openGraph ω) (Tᶜ ∩ Set.univ) o a :=
        pathIn_of_pathIn_union hpa fun x hx y _ hxy => hx.1 (mk_mem_wireSet_iff.1 hxy).1
      refine (reachable_of_pathIn hpa').trans (SimpleGraph.Adj.reachable ?_)
      rw [openGraph_adj] at hab ⊢
      refine ⟨hab.1.resolve_right fun h' => ha (mk_mem_wireSet_iff.1 h').1, hab.2⟩
  · rintro ⟨t, ht, h⟩
    change (openGraph (ω ∪ wireSet T)).Reachable o t₀
    have h1 : (openGraph (ω ∪ wireSet T)).Reachable o t :=
      h.mono (openGraph_mono Set.subset_union_left)
    refine h1.trans ?_
    by_cases htt : t = t₀
    · subst htt; exact SimpleGraph.Reachable.refl _
    · refine SimpleGraph.Adj.reachable ?_
      rw [openGraph_adj]
      exact ⟨Or.inr (mk_mem_wireSet_iff.2 ⟨ht, ht₀, htt⟩), htt⟩

/-- **Wiring = contraction, for connection probabilities** (`V` countable, `t₀ ∈ T`):
`P_{wireW T w}(o ↔ t₀) = P_w(o ↔ T)`. Proof: under the wired law the pairs of `wireSet T` are
a.s. open, so `{o ↔ t₀}` a.s. equals the pull-back of `{o ↔ t₀}` along `ω ↦ ω ∪ wireSet T`,
which is `{o ↔ T}` (previous lemma), an event determined by the complement of `wireSet T`,
where the two weightings agree. [cite: KozmaNitzan2024, §4 p. 22 ("we identified the set T to a point")] -/
theorem prodBernoulli_wireW_real_openConn [Countable V] (w : Sym2 V → unitInterval) (T : Set V)
    {t₀ : V} (ht₀ : t₀ ∈ T) (o : V) :
    (prodBernoulli (wireW T w)).real (openConn o t₀) =
      (prodBernoulli w).real (⋃ t ∈ T, openConn o t) := by
  set E := wireSet T with hE
  have hEc : E.Countable := Set.to_countable E
  have hA'm : MeasurableSet ((fun ω : Set (Sym2 V) => ω ∪ E) ⁻¹' openConn o t₀) :=
    measurable_union_right_const E (measurableSet_openConn_holds o t₀)
  -- a.s. all wired pairs are open
  have hae : ∀ᵐ ω ∂prodBernoulli (wireW T w), ∀ e ∈ E, e ∈ ω := by
    have : Countable E := hEc.to_subtype
    have h : ∀ e : E, ∀ᵐ ω ∂prodBernoulli (wireW T w), (e : Sym2 V) ∈ ω := fun e =>
      prodBernoulli_ae_mem_of_eq_one _ (wireW_apply_of_mem w e.2)
    filter_upwards [ae_all_iff.2 h] with ω hω e he using hω ⟨e, he⟩
  calc (prodBernoulli (wireW T w)).real (openConn o t₀)
      = (prodBernoulli (wireW T w)).real ((fun ω : Set (Sym2 V) => ω ∪ E) ⁻¹' openConn o t₀) := by
        refine measureReal_congr ?_
        filter_upwards [hae] with ω hω
        have : ω ∪ E = ω := Set.union_eq_self_of_subset_right fun e he => hω e he
        refine propext ?_
        change ω ∈ openConn o t₀ ↔ ω ∪ E ∈ openConn o t₀
        rw [this]
    _ = (prodBernoulli w).real ((fun ω : Set (Sym2 V) => ω ∪ E) ⁻¹' openConn o t₀) := by
        refine prodBernoulli_real_eq_of_determinedBy _ _ (F := Eᶜ) (fun e he => ?_)
          (determinedBy_preimage_union_const E _) hA'm
        exact wireW_apply_of_not_mem w he
    _ = (prodBernoulli w).real (⋃ t ∈ T, openConn o t) := by
        rw [hE, preimage_union_wireSet_openConn T ht₀ o]

/-- The event `{o ↔ T}` is measurable (`V` countable). [folklore] -/
theorem measurableSet_biUnion_openConn [Countable V] (o : V) (T : Set V) :
    MeasurableSet (⋃ t ∈ T, openConn o t : Set (BondConfig V)) :=
  MeasurableSet.biUnion (Set.to_countable T) fun t _ => measurableSet_openConn_holds o t

/-- The event `{o ↔ T}` is increasing. [folklore] -/
theorem isUpperSet_biUnion_openConn (o : V) (T : Set V) :
    IsUpperSet (⋃ t ∈ T, openConn o t : Set (BondConfig V)) := by
  intro ω ω' hle hω
  simp only [Set.mem_iUnion, exists_prop] at hω ⊢
  obtain ⟨t, ht, h⟩ := hω
  exact ⟨t, ht, isUpperSet_openConn o t hle h⟩

/-- Raising weights raises the probability of `{o ↔ A}`; in particular for wiring.
[cite: KozmaNitzan2024, §4 p. 22] -/
theorem prodBernoulli_real_biUnion_openConn_mono [Countable V] {w w' : Sym2 V → unitInterval}
    (h : w ≤ w') (o : V) (A : Set V) :
    (prodBernoulli w).real (⋃ a ∈ A, openConn o a) ≤ (prodBernoulli w').real (⋃ a ∈ A, openConn o a) :=
  prodBernoulli_real_mono_of_isUpperSet h (isUpperSet_biUnion_openConn o A)
    (measurableSet_biUnion_openConn o A)

end Wire

/-! ## Conjecture 3 over an arbitrary finite vertex type, and for finitely supported weights -/

section Transfer

variable {V W : Type*}

/-- **The restriction coupling for inhomogeneous weights**: for injective `f : W → V`, the image
of `prodBernoulli w` under `restrictConfig f` (the pair `e` of `W` is open iff `e.map f` is) is
`prodBernoulli (w ∘ Sym2.map f)` (same proof as `bondPercolation_map_comap`).
[cite: GrimmettPercolation1999, §1.3 p. 10 (product measure)] -/
theorem prodBernoulli_map_restrictConfig (w : Sym2 V → unitInterval) {f : W → V}
    (hf : Function.Injective f) :
    (prodBernoulli w).map (restrictConfig f) = prodBernoulli (w ∘ Sym2.map f) := by
  have hSV : Measurable fun q : Sym2 V → Prop => {i | q i} := measurable_setOf
  have hSW : Measurable fun q : Sym2 W → Prop => {i | q i} := measurable_setOf
  rw [prodBernoulli_eq_map, prodBernoulli_eq_map, Measure.map_map (measurable_restrictConfig f) hSV]
  have hcomp : (restrictConfig f ∘ fun q : Sym2 V → Prop => {i | q i}) =
      (fun q : Sym2 W → Prop => {i | q i}) ∘
        fun (q : Sym2 V → Prop) (i : Sym2 W) => q (Sym2.map f i) := rfl
  rw [hcomp, ← Measure.map_map hSW (by fun_prop),
    Measure.map_infinitePi_infinitePi_of_inj (Sym2.map.injective hf)]
  rfl

/-- For a BIJECTION `e`, restriction along `e.symm` pulls `{e o ↔ e b}` back to `{o ↔ b}`.
[folklore] -/
theorem restrictConfig_symm_preimage_openConn (e : V ≃ W) (o b : V) :
    restrictConfig e.symm ⁻¹' (openConn (e o) (e b) : Set (BondConfig W)) = openConn o b := by
  ext ω
  simp only [Set.mem_preimage]
  change (openGraph (restrictConfig e.symm ω)).Reachable (e o) (e b) ↔ (openGraph ω).Reachable o b
  constructor
  · intro h
    have := reachable_map_of_restrictConfig e.symm.injective ω h
    simpa using this
  · intro h
    let φ : openGraph ω →g openGraph (restrictConfig (e.symm : W → V) ω) :=
      { toFun := e
        map_rel' := fun {a c} hac => by
          rw [openGraph_adj] at hac ⊢
          refine ⟨?_, e.injective.ne hac.2⟩
          rw [mem_restrictConfig, Sym2.map_mk]
          simpa using hac.1 }
    exact h.map φ

/-- Same for the union event `{o ↔ A}`. [folklore] -/
theorem restrictConfig_symm_preimage_biUnion_openConn (e : V ≃ W) (o : V) (A : Finset V) :
    restrictConfig e.symm ⁻¹' (⋃ a ∈ A.map e.toEmbedding, openConn (e o) a : Set (BondConfig W)) =
      ⋃ a ∈ A, openConn o a := by
  ext ω
  simp only [Set.mem_preimage, Set.mem_iUnion, exists_prop, Finset.mem_map_equiv]
  constructor
  · rintro ⟨a, ha, h⟩
    refine ⟨e.symm a, ha, ?_⟩
    have h' : ω ∈ restrictConfig e.symm ⁻¹' (openConn (e o) (e (e.symm a)) : Set (BondConfig W)) := by
      simpa using h
    rwa [restrictConfig_symm_preimage_openConn] at h'
  · rintro ⟨a, ha, h⟩
    refine ⟨e a, by simpa using ha, ?_⟩
    have h' : ω ∈ restrictConfig e.symm ⁻¹' (openConn (e o) (e a) : Set (BondConfig W)) := by
      rwa [restrictConfig_symm_preimage_openConn]
    exact h'

/-- **Conjecture 3 holds over every finite vertex type** if it holds as typed (over `Fin n`):
relabel along `Fintype.equivFin`. [cite: KozmaNitzan2024, Conjecture 3 (p. 15)] -/
theorem KozmaNitzan2024_conjecture3.fintype (hC : KozmaNitzan2024_conjecture3) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (V : Type) [Fintype V] (w : Sym2 V → unitInterval)
      (A : Finset V) (o b : V),
      1 - δ < (prodBernoulli w).real (⋃ a ∈ A, openConn o a) →
        (∀ a ∈ A, 1 - δ < (prodBernoulli w).real (openConn a b)) →
          1 - ε < (prodBernoulli w).real (openConn o b) := by
  obtain ⟨δ, hδ, h⟩ := hC ε hε
  refine ⟨δ, hδ, fun V _ w A o b hoA hab => ?_⟩
  classical
  set e := Fintype.equivFin V with he
  have hf : Function.Injective (e.symm : Fin (Fintype.card V) → V) := e.symm.injective
  set w' : Sym2 (Fin (Fintype.card V)) → unitInterval := w ∘ Sym2.map e.symm with hw'
  have hmap := prodBernoulli_map_restrictConfig w hf
  -- transport of the three probabilities
  have key : ∀ x y : V, (prodBernoulli w').real (openConn (e x) (e y)) = (prodBernoulli w).real (openConn x y) := by
    intro x y
    rw [hw', ← hmap, map_measureReal_apply (measurable_restrictConfig _) (measurableSet_openConn_holds _ _),
      restrictConfig_symm_preimage_openConn]
  have keyU : (prodBernoulli w').real (⋃ a ∈ A.map e.toEmbedding, openConn (e o) a) =
      (prodBernoulli w).real (⋃ a ∈ A, openConn o a) := by
    rw [hw', ← hmap, map_measureReal_apply (measurable_restrictConfig _)
      (Finset.measurableSet_biUnion _ fun a _ => measurableSet_openConn_holds _ _)]
    congr 1
    exact restrictConfig_symm_preimage_biUnion_openConn e o A
  have h1 := h (Fintype.card V) w' (A.map e.toEmbedding) (e o) (e b) (by rwa [keyU]) (by
    intro a ha
    rw [Finset.mem_map_equiv] at ha
    have := hab (e.symm a) ha
    rwa [← key, Equiv.apply_symm_apply] at this)
  rwa [key] at h1

/-- An open path from a vertex of `S`, in a configuration all of whose open pairs lie inside `S`,
is an open path of the configuration restricted to `S`. [folklore] -/
theorem reachable_restrictConfig_subtype_of_reachable {S : Set V} {ω : BondConfig V}
    (hω : ∀ e ∈ ω, ∀ x ∈ e, x ∈ S) {o b : V} (ho : o ∈ S) (hb : b ∈ S)
    (h : (openGraph ω).Reachable o b) :
    (openGraph (restrictConfig (Subtype.val : S → V) ω)).Reachable ⟨o, ho⟩ ⟨b, hb⟩ := by
  obtain ⟨-, hp⟩ := DCT16.pathIn_univ_of_reachable h
  suffices H : ∀ c, Relation.ReflTransGen (fun a b => (openGraph ω).Adj a b ∧ b ∈ Set.univ) o c →
      ∀ hc : c ∈ S, (openGraph (restrictConfig (Subtype.val : S → V) ω)).Reachable ⟨o, ho⟩ ⟨c, hc⟩ from
    H b hp hb
  intro c hc
  induction hc with
  | refl => intro _; exact SimpleGraph.Reachable.refl _
  | @tail x y _ hxy ih =>
    intro hy
    have hadj := hxy.1
    rw [openGraph_adj] at hadj
    have hx : x ∈ S := hω _ hadj.1 x (Sym2.mem_mk_left x y)
    refine (ih hx).trans (SimpleGraph.Adj.reachable ?_)
    rw [openGraph_adj, mem_restrictConfig, Sym2.map_mk]
    exact ⟨hadj.1, fun h' => hadj.2 (congrArg Subtype.val h')⟩

/-- **Conjecture 3 for finitely supported weights on a countable vertex type**: if `w` vanishes on
every pair not inside the finite set `S`, then the `ε`–`δ` statement of Conjecture 3 holds for
`prodBernoulli w` with `A ⊆ S`, `o, b ∈ S` (restriction coupling to the finite graph on `S`, on
which the configuration a.s. lives). [cite: KozmaNitzan2024, Conjecture 3 (p. 15)] -/
theorem KozmaNitzan2024_conjecture3.finSupp (hC : KozmaNitzan2024_conjecture3) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (V : Type) [Countable V] (w : Sym2 V → unitInterval) (S : Finset V),
      (∀ e : Sym2 V, (∃ x ∈ e, x ∉ S) → w e = 0) →
      ∀ (A : Finset V) (o b : V), A ⊆ S → o ∈ S → b ∈ S →
        1 - δ < (prodBernoulli w).real (⋃ a ∈ A, openConn o a) →
          (∀ a ∈ A, 1 - δ < (prodBernoulli w).real (openConn a b)) →
            1 - ε < (prodBernoulli w).real (openConn o b) := by
  obtain ⟨δ, hδ, h⟩ := hC.fintype hε
  refine ⟨δ, hδ, fun V _ w S hw A o b hAS ho hb hoA hab => ?_⟩
  classical
  set Sset : Set V := ↑S with hSset
  set f : Sset → V := Subtype.val with hf
  have hfi : Function.Injective f := Subtype.val_injective
  set w' : Sym2 Sset → unitInterval := w ∘ Sym2.map f with hw'
  have hmap := prodBernoulli_map_restrictConfig w hfi
  -- a.s. every open pair lies inside `S`
  have hae : ∀ᵐ ω ∂prodBernoulli w, ∀ e ∈ ω, ∀ x ∈ e, x ∈ Sset := by
    have hZ : ({e : Sym2 V | ∃ x ∈ e, x ∉ S}).Countable := Set.to_countable _
    filter_upwards [prodBernoulli_ae_forall_notMem w hZ fun e he => hw e he] with ω hω e he x hx
    by_contra hxS
    exact hω e ⟨x, hx, hxS⟩ he
  -- transport of connection probabilities
  have key : ∀ (x y : V) (hx : x ∈ Sset) (hy : y ∈ Sset),
      (prodBernoulli w').real (openConn (⟨x, hx⟩ : Sset) ⟨y, hy⟩) = (prodBernoulli w).real (openConn x y) := by
    intro x y hx hy
    rw [hw', ← hmap, map_measureReal_apply (measurable_restrictConfig _) (measurableSet_openConn_holds _ _)]
    refine measureReal_congr ?_
    filter_upwards [hae] with ω hω
    refine propext ⟨fun h' => ?_, fun h' => ?_⟩
    · exact reachable_map_of_restrictConfig hfi ω h'
    · exact reachable_restrictConfig_subtype_of_reachable hω hx hy h'
  set A' : Finset Sset := A.subtype (· ∈ Sset) with hA'
  have keyU : (prodBernoulli w').real (⋃ a ∈ A', openConn (⟨o, ho⟩ : Sset) a) =
      (prodBernoulli w).real (⋃ a ∈ A, openConn o a) := by
    rw [hw', ← hmap, map_measureReal_apply (measurable_restrictConfig _)
      (Finset.measurableSet_biUnion _ fun a _ => measurableSet_openConn_holds _ _)]
    refine measureReal_congr ?_
    filter_upwards [hae] with ω hω
    change (ω ∈ restrictConfig f ⁻¹' (⋃ a ∈ A', openConn (⟨o, ho⟩ : Sset) a)) =
      (ω ∈ ⋃ a ∈ A, openConn o a)
    simp only [Set.mem_preimage, Set.mem_iUnion, exists_prop, hA', Finset.mem_subtype, eq_iff_iff]
    constructor
    · rintro ⟨a, ha, h'⟩
      exact ⟨a, ha, reachable_map_of_restrictConfig hfi ω h'⟩
    · rintro ⟨a, ha, h'⟩
      exact ⟨⟨a, hAS ha⟩, ha, reachable_restrictConfig_subtype_of_reachable hω ho (hAS ha) h'⟩
  have h1 := h Sset w' A' ⟨o, ho⟩ ⟨b, hb⟩ (by rwa [keyU]) (by
    intro a ha
    rw [hA', Finset.mem_subtype] at ha
    have := hab a ha
    rwa [← key a b a.2 hb] at this)
  rwa [key] at h1

/-- **Conjecture 3 with a target SET** (the form used on p. 22: "`P_{K_ξ}(o ↔ T) ≥ 1 - ½ε` … we
identified the set `T` to a point and used that point as the `b` of conjecture 3"): for finitely
supported weights on a countable vertex type, if `P_w(o ↔ A) > 1 - δ` and `P_w(a ↔ T) > 1 - δ`
for all `a ∈ A`, then `P_w(o ↔ T) > 1 - ε`. Proof: apply the previous form to the wired weights
`wireW T w` and any `t₀ ∈ T` (`prodBernoulli_wireW_real_openConn`, and monotonicity of
`{o ↔ A}` under wiring). [cite: KozmaNitzan2024, §4 p. 22 and Conjecture 3 (p. 15)] -/
theorem KozmaNitzan2024_conjecture3.openConn_set (hC : KozmaNitzan2024_conjecture3) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (V : Type) [Countable V] (w : Sym2 V → unitInterval) (S : Finset V),
      (∀ e : Sym2 V, (∃ x ∈ e, x ∉ S) → w e = 0) →
      ∀ (A T : Finset V) (o : V), A ⊆ S → T ⊆ S → o ∈ S → T.Nonempty →
        1 - δ < (prodBernoulli w).real (⋃ a ∈ A, openConn o a) →
          (∀ a ∈ A, 1 - δ < (prodBernoulli w).real (⋃ t ∈ T, openConn a t)) →
            1 - ε < (prodBernoulli w).real (⋃ t ∈ T, openConn o t) := by
  obtain ⟨δ, hδ, h⟩ := hC.finSupp hε
  refine ⟨δ, hδ, fun V _ w S hw A T o hAS hTS ho hT hoA haT => ?_⟩
  obtain ⟨t₀, ht₀⟩ := hT
  have hw' : ∀ e : Sym2 V, (∃ x ∈ e, x ∉ S) → wireW (↑T : Set V) w e = 0 := by
    intro e he
    rw [wireW_apply_of_not_mem w ?_, hw e he]
    obtain ⟨x, hx, hxS⟩ := he
    exact fun h' => hxS (hTS (h'.1 x hx))
  have h1 := h V (wireW (↑T : Set V) w) S hw' A o t₀ hAS ho (hTS ht₀)
    (hoA.trans_le (prodBernoulli_real_biUnion_openConn_mono (le_wireW _ w) o _)) (by
      intro a ha
      rw [prodBernoulli_wireW_real_openConn w (↑T : Set V) (Finset.mem_coe.2 ht₀) a]
      exact haT a ha)
  rwa [prodBernoulli_wireW_real_openConn w (↑T : Set V) (Finset.mem_coe.2 ht₀) o] at h1

end Transfer

end Percolation.Literature

end
