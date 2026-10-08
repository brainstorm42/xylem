import Percolation.Literature.FiniteEnergy
import Percolation.Util.Linter

/-!
# Insertion tolerance of Bernoulli bond percolation (opening finitely many edges)

Companion of `FiniteEnergy.lean` (which bounds the
cost of *closing* conditionally specified edges by `(1 - p)^k`): the "local modification" step
of the Newman–Schulman / Burton–Keane uniqueness arguments, in which a fixed finite set `F` of
edges is declared *open*.

* `openEdges F ω = ω ∪ F` — the configuration `ω` with the edges of `F` opened.
* `bondPercolation_pow_mul_real_preimage_openEdges_le` — for `P_p = bondPercolation G p`, a finite
  set `F` of edges of `G` and a measurable event `E`,
  `p ^ |F| · P_p({ω | ω ∪ F ∈ E}) ≤ P_p(E)`.
  This is the inequality behind Bollobás–Riordan, *Percolation* (2006), Ch. 5, proof of Lemma 2,
  p. 106 ("if `ω ∈ T_{n,k,s}` and `ω'` is the configuration obtained from `ω` by changing the state
  of each of the closed sites in `B_n(x₀)` from closed to open, then `ω' ∈ I₁`. Thus
  `P(I₁) ≥ P({ω' : ω ∈ T_{n,k,s}}) = (p/(1-p))^c P(T_{n,k,s}) > 0`") and proof of Thm. 4, p. 107
  ("if … `ω'` is obtained from `ω` by changing the states of all the sites in `B_r(x₀)` to open,
  then `ω' ∈ T_r(x₀)`. Hence, `P(T_r(x₀)) > 0`"), and Grimmett, *Percolation* (1999), §8.2, p. 198
  ("Since every configuration on `𝔼_B` has a strictly positive probability …").
* `bondPercolation_real_pos_of_openEdges` — the qualitative form: if `P_p(A) > 0`, `p > 0` and
  `ω ∪ F ∈ E` for all `ω ∈ A`, then `P_p(E) > 0`.

Proof: `D = {ω | ω ∪ F ∈ E}` is determined by the edges off `F` and `{F ⊆ ω}` by the edges of
`F` (`DeterminedBy`, `PercolationEvents.lean`), so `P_p({F ⊆ ω} ∩ D) = p^{|F|} P_p(D)` by
`bondPercolation_real_inter_of_disjoint` (`FiniteEnergy.lean`) and
`Percolation.Literature.bondPercolation_real_setOf_subset`; and `{F ⊆ ω} ∩ D ⊆ E` because `ω ∪ F = ω`
there. Mathlib has no percolation; `FiniteEnergy.lean` treats closing edges only.
-/

namespace Percolation.Literature

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {V : Type*}

/-- The configuration `ω` with the edges of `F` opened, `ω ∪ F` (Bollobás–Riordan 2006, Ch. 5,
p. 106: "the configuration obtained from `ω` by changing the state of each of the closed sites in
`B_n(x₀)` from closed to open"; bond version). [cite: BollobasRiordanPercolation2006, Ch. 5, proof of Lemma 2 (p. 106)] -/
def openEdges (F : Set (Sym2 V)) (ω : BondConfig V) : BondConfig V := ω ∪ F

/-- Membership in `openEdges F ω`. [folklore] -/
@[simp] theorem mem_openEdges (F : Set (Sym2 V)) (ω : BondConfig V) (e : Sym2 V) :
    e ∈ openEdges F ω ↔ e ∈ ω ∨ e ∈ F := Iff.rfl

/-- `ω ⊆ openEdges F ω`. [folklore] -/
theorem subset_openEdges (F : Set (Sym2 V)) (ω : BondConfig V) : ω ⊆ openEdges F ω :=
  Set.subset_union_left

/-- `F ⊆ openEdges F ω`. [folklore] -/
theorem subset_openEdges_right (F : Set (Sym2 V)) (ω : BondConfig V) : F ⊆ openEdges F ω :=
  Set.subset_union_right

/-- If the edges of `F` are already open then opening them changes nothing. [folklore] -/
theorem openEdges_eq_self_of_subset {F : Set (Sym2 V)} {ω : BondConfig V} (h : F ⊆ ω) :
    openEdges F ω = ω :=
  Set.union_eq_self_of_subset_right h

/-- `ω ↦ ω ∪ F` is measurable (coordinatewise it is `ω ↦ (e ∈ ω) ∨ (e ∈ F)`). [folklore] -/
theorem measurable_openEdges (F : Set (Sym2 V)) :
    Measurable (openEdges F : BondConfig V → BondConfig V) :=
  measurable_set_iff.2 fun e => (measurable_set_mem e).or measurable_const

/-- The event `{ω | ω ∪ F ∈ E}` is determined by the edges off `F`. [folklore] -/
theorem determinedBy_preimage_openEdges (F : Set (Sym2 V)) (E : Set (BondConfig V)) :
    DeterminedBy (openEdges F ⁻¹' E) Fᶜ := by
  rw [determinedBy_iff]
  intro ω ω' h
  have hω : openEdges F ω = openEdges F ω' := by
    ext e
    simp only [mem_openEdges]
    by_cases he : e ∈ F
    · simp [he]
    · have := Set.ext_iff.1 h e
      simp only [Set.mem_inter_iff, Set.mem_compl_iff, he, not_false_eq_true, and_true] at this
      rw [this]
  simp only [Set.mem_preimage, hω]

/-- The cylinder event `{F ⊆ ω}` is determined by the edges of `F`. [folklore] -/
theorem determinedBy_setOf_subset (F : Set (Sym2 V)) :
    DeterminedBy {ω : BondConfig V | F ⊆ ω} F := by
  rw [determinedBy_iff]
  intro ω ω' h
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hs e he
    exact ((Set.ext_iff.1 h e).1 ⟨hs he, he⟩).1
  · intro hs e he
    exact ((Set.ext_iff.1 h e).2 ⟨hs he, he⟩).1

/-- The cylinder event `{F ⊆ ω}` is measurable for countable `F`. [folklore] -/
theorem measurableSet_setOf_subset {F : Set (Sym2 V)} (hF : F.Countable) :
    MeasurableSet {ω : BondConfig V | F ⊆ ω} := by
  have h : {ω : BondConfig V | F ⊆ ω} = ⋂ e ∈ F, {ω | e ∈ ω} := by
    ext ω; simp [Set.subset_def]
  rw [h]
  exact MeasurableSet.biInter hF fun e _ => measurableSet_mem e

/-- **Insertion tolerance (finite energy for opening edges).** For a finite set `F` of edges of
`G` and a measurable event `E`, `p^{|F|} · P_p({ω | ω ∪ F ∈ E}) ≤ P_p(E)`. Proof: with
`D = {ω | ω ∪ F ∈ E}` (determined by the edges off `F`) and `C = {F ⊆ ω}` (determined by `F`),
`P_p(C ∩ D) = P_p(C) P_p(D) = p^{|F|} P_p(D)` by independence of disjoint edge sets, and
`C ∩ D ⊆ E`. (Bollobás–Riordan 2006, Ch. 5, proof of Lemma 2, p. 106:
"`P(I₁) ≥ P({ω' : ω ∈ T_{n,k,s}}) = (p/(1-p))^c P(T_{n,k,s})`"; Grimmett 1999, §8.2, p. 198:
"every configuration on `𝔼_B` has a strictly positive probability".) [cite: BollobasRiordanPercolation2006, Ch. 5, proof of Lemma 2 (p. 106)] -/
theorem bondPercolation_pow_mul_real_preimage_openEdges_le [Countable V] (G : SimpleGraph V)
    (p : unitInterval) (F : Finset (Sym2 V)) (hF : (↑F : Set (Sym2 V)) ⊆ G.edgeSet)
    {E : Set (BondConfig V)} (hE : MeasurableSet E) :
    (p : ℝ) ^ F.card * (bondPercolation G p).real (openEdges ↑F ⁻¹' E) ≤
      (bondPercolation G p).real E := by
  set D : Set (BondConfig V) := openEdges ↑F ⁻¹' E with hD
  set C : Set (BondConfig V) := {ω | (↑F : Set (Sym2 V)) ⊆ ω} with hC
  have hDm : MeasurableSet D := measurable_openEdges _ hE
  have hCm : MeasurableSet C := measurableSet_setOf_subset F.countable_toSet
  have hind : (bondPercolation G p).real (C ∩ D) =
      (bondPercolation G p).real C * (bondPercolation G p).real D :=
    bondPercolation_real_inter_of_disjoint G p disjoint_compl_right (determinedBy_setOf_subset _)
      (determinedBy_preimage_openEdges _ E) hCm hDm
  have hCμ : (bondPercolation G p).real C = (p : ℝ) ^ F.card :=
    Percolation.Literature.bondPercolation_real_setOf_subset G p F hF
  have hsub : C ∩ D ⊆ E := by
    rintro ω ⟨hωC, hωD⟩
    have : openEdges ↑F ω = ω := openEdges_eq_self_of_subset hωC
    simpa only [hD, Set.mem_preimage, this] using hωD
  calc (p : ℝ) ^ F.card * (bondPercolation G p).real D
        = (bondPercolation G p).real (C ∩ D) := by rw [hind, hCμ]
    _ ≤ (bondPercolation G p).real E := measureReal_mono hsub

/-- **Insertion tolerance, qualitative form**: if `p > 0`, `A` has positive probability and
opening the finite set `F` of edges of `G` maps `A` into the measurable event `E`, then `E` has
positive probability. (Bollobás–Riordan 2006, Ch. 5, proof of Lemma 2, p. 106, and proof of
Thm. 4, p. 107: "Hence, `P(T_r(x₀)) > 0`".) [cite: BollobasRiordanPercolation2006, Ch. 5, proof of Lemma 2 (p. 106) and of Thm. 4 (p. 107)] -/
theorem bondPercolation_real_pos_of_openEdges [Countable V] (G : SimpleGraph V)
    {p : unitInterval} (hp : 0 < (p : ℝ)) (F : Finset (Sym2 V))
    (hF : (↑F : Set (Sym2 V)) ⊆ G.edgeSet) {A E : Set (BondConfig V)} (hE : MeasurableSet E)
    (hA : 0 < (bondPercolation G p).real A) (hAE : ∀ ω ∈ A, openEdges ↑F ω ∈ E) :
    0 < (bondPercolation G p).real E := by
  have h1 : (bondPercolation G p).real A ≤ (bondPercolation G p).real (openEdges ↑F ⁻¹' E) :=
    measureReal_mono fun ω hω => hAE ω hω
  have h2 := bondPercolation_pow_mul_real_preimage_openEdges_le G p F hF hE
  have h3 : 0 < (p : ℝ) ^ F.card := pow_pos hp _
  nlinarith

end Percolation.Literature
