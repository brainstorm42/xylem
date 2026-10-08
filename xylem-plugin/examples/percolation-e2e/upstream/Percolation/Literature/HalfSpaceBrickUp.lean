import Percolation.Literature.HalfSpaceSlab
import Percolation.Literature.SiteMonotonicity
import Percolation.Util.Linter

/-!
# Fine tuning of the height and the vertical-edge step: (7.43)–(7.46) of Lemma (7.36)

Fourth step of the proof of Lemma (7.36) of Grimmett, *Percolation*, 2nd ed. (1999), §7.3,
pp. 166–167 (finite-size criterion of the Barsky–Grimmett–Newman theorem `θ_ℍ(p_c) = 0`),
proved here:

> "We now 'fine tune' the height `h` in such a way that `U(l,h)` is 'only just large enough' …
> The sequence `a(h) = P_{p_c}(U(l,h) ≥ N₂)` satisfies `a(H₀) > 1 - 2ε` (by (7.42)), and
> furthermore `a(h) → 0` as `h → ∞`. It follows that there exists an integer `H₁ = H₁(l) (> H₀)`
> such that (7.43) [`a(H₁ - 1) > 1 - 2ε ≥ a(H₁)`]. Since `U(l,h) ↑ U(h)` as `l → ∞`, we have that
> `H₁(l)` is non-decreasing in `l`. … Therefore, (7.44) `H₁(l) → ∞` as `l → ∞`. …
> (7.45) `P(U(l, H₁(l)) ≥ M) ≥ P(U(l, H₁(l) - 1) ≥ N₂) × P(U(l,H₁(l)) ≥ M | U(l,H₁(l)-1) ≥ N₂)`
> … given `N₂` points `z` in `T(l, H₁(l) - 1)`, there is by (7.40) at least probability `1 - ε`
> that `M` or more of the edges `⟨z, z + (0,0,1)⟩` are open (note that this last event is
> conditionally independent of the states of all edges in `B(l, H₁(l) - 1)`). Therefore, the
> conditional probability in (7.45) is at least `1 - ε`, whence
> (7.46) `P_{p_c}(U(l, H₁(l)) ≥ M) ≥ (1 - 2ε)(1 - ε)`."

## References

* G. Grimmett, *Percolation*, 2nd ed., Grundlehren 321, Springer 1999, §7.3, proof of
  Lemma (7.36), pp. 166–167, (7.43)–(7.46).
-/

noncomputable section

namespace Percolation.Literature

open MeasureTheory ProbabilityTheory Filter LatticeModels unitInterval
open scoped ENNReal Topology

namespace BGN

/-! ## At least `M` open edges among many: the vertical-edge step without binomial tails -/

section AtLeastOpen

variable {V : Type*}

/-- The event "at least `M` of the edges of `F` are open". [cite: GrimmettPercolation1999, §7.3 p. 167 (7.45)] -/
def atLeastOpen (F : Finset (Sym2 V)) (M : ℕ) : Set (BondConfig V) :=
  {ω | ∃ Z ⊆ F, M ≤ Z.card ∧ (↑Z : Set (Sym2 V)) ⊆ ω}

/-- `atLeastOpen F M` is measurable (a finite union of finite intersections of one-edge events).
[folklore] -/
theorem measurableSet_atLeastOpen (F : Finset (Sym2 V)) (M : ℕ) : MeasurableSet (atLeastOpen F M) := by
  have : atLeastOpen F M = ⋃ Z ∈ F.powerset.filter (fun Z => M ≤ Z.card), ⋂ e ∈ Z, {ω : BondConfig V | e ∈ ω} := by
    ext ω
    simp only [atLeastOpen, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_iInter, Finset.mem_filter,
      Finset.mem_powerset, exists_prop, Set.subset_def, Finset.mem_coe]
    constructor
    · rintro ⟨Z, hZF, hM, hZω⟩
      exact ⟨Z, ⟨hZF, hM⟩, hZω⟩
    · rintro ⟨Z, ⟨hZF, hM⟩, hZω⟩
      exact ⟨Z, hZF, hM, hZω⟩
  rw [this]
  exact MeasurableSet.biUnion (Set.to_countable _) fun Z _ =>
    MeasurableSet.biInter (Set.to_countable _) fun e _ => measurableSet_mem e

/-- `atLeastOpen F M` is determined by the edges of `F`. [folklore] -/
theorem determinedBy_atLeastOpen (F : Finset (Sym2 V)) (M : ℕ) :
    DeterminedBy (atLeastOpen F M) (↑F : Set (Sym2 V)) := by
  rw [determinedBy_iff]
  intro ω ω' h
  simp only [atLeastOpen, Set.mem_setOf_eq]
  constructor
  · rintro ⟨Z, hZF, hM, hZω⟩
    refine ⟨Z, hZF, hM, fun e he => ?_⟩
    exact ((Set.ext_iff.1 h e).1 ⟨hZω he, hZF he⟩).1
  · rintro ⟨Z, hZF, hM, hZω⟩
    refine ⟨Z, hZF, hM, fun e he => ?_⟩
    exact ((Set.ext_iff.1 h e).2 ⟨hZω he, hZF he⟩).1

/-- **All edges of a finite set of edges of `G` are closed with probability exactly
`(1 - p)^{|F|}`** (product measure). [cite: GrimmettPercolation1999, §1.3 p. 10 (product measure)] -/
theorem bondPercolation_real_forall_notMem_eq (G : SimpleGraph V) (p : unitInterval)
    (F : Finset (Sym2 V)) (hF : (↑F : Set (Sym2 V)) ⊆ G.edgeSet) :
    (bondPercolation G p).real {ω | ∀ e ∈ F, e ∉ ω} = (1 - (p : ℝ)) ^ F.card := by
  classical
  have hpre : (fun q : Sym2 V → Prop => {i | q i}) ⁻¹' {ω : BondConfig V | ∀ e ∈ F, e ∉ ω}
      = Set.pi (F : Set (Sym2 V)) (fun _ => {False}) := by
    ext q
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_pi, Finset.mem_coe,
      Set.mem_singleton_iff, eq_iff_iff, iff_false]
  rw [measureReal_def, bondPercolation, setBernoulli_apply', hpre,
    Measure.infinitePi_pi _ (fun _ _ => MeasurableSet.of_discrete)]
  have h1 : ∀ e ∈ F, (toNNReal p • Measure.dirac (e ∈ G.edgeSet) +
      toNNReal (σ p) • Measure.dirac False : Measure Prop) {False} = toNNReal (σ p) := by
    intro e he
    have heT : (e ∈ G.edgeSet) = True := propext ⟨fun _ => trivial, fun _ => hF he⟩
    simp [heT]
  rw [Finset.prod_congr rfl h1, Finset.prod_const, ENNReal.toReal_pow, ENNReal.coe_toReal,
    coe_toNNReal, coe_symm_eq]

/-- **Grouping bound**: if `|F| ≥ M g` (edges of `G`) then
`P_p(fewer than M edges of F are open) ≤ M (1 - p)^g`. Split `M g` of the edges into `M`
disjoint groups of `g`; if every group contains an open edge, at least `M` edges are open. This
elementary bound stands in for the binomial estimate (7.40) of Grimmett 1999.
[cite: GrimmettPercolation1999, §7.3 p. 165 (7.40), p. 167] -/
theorem prob_compl_atLeastOpen_le [Countable V] (G : SimpleGraph V) (p : unitInterval)
    {F : Finset (Sym2 V)} (hF : (↑F : Set (Sym2 V)) ⊆ G.edgeSet) {M g : ℕ} (hcard : M * g ≤ F.card) :
    (bondPercolation G p).real (atLeastOpen F M)ᶜ ≤ M * (1 - (p : ℝ)) ^ g := by
  classical
  obtain ⟨T, hTF, hTcard⟩ := Finset.exists_subset_card_eq hcard
  -- a bijection between `T` and `Fin M × Fin g`, and the `M` groups
  let E : T ≃ Fin M × Fin g := (Finset.equivFinOfCardEq hTcard).trans finProdFinEquiv.symm
  let grp : Fin M → Finset (Sym2 V) := fun j =>
    (Finset.univ : Finset (Fin g)).image fun i => ((E.symm (j, i) : T) : Sym2 V)
  have hinj : ∀ j, Function.Injective fun i : Fin g => ((E.symm (j, i) : T) : Sym2 V) := by
    intro j i i' h
    have := E.symm.injective (Subtype.val_injective h)
    simpa using this
  have hgrp_card : ∀ j, (grp j).card = g := by
    intro j
    rw [Finset.card_image_of_injective _ (hinj j), Finset.card_univ, Fintype.card_fin]
  have hgrp_sub : ∀ j, (↑(grp j) : Set (Sym2 V)) ⊆ G.edgeSet := by
    intro j e he
    rw [Finset.mem_coe, Finset.mem_image] at he
    obtain ⟨i, -, rfl⟩ := he
    exact hF (hTF (E.symm (j, i)).2)
  have hgrp_T : ∀ j, ∀ e ∈ grp j, e ∈ F := by
    intro j e he
    rw [Finset.mem_image] at he
    obtain ⟨i, -, rfl⟩ := he
    exact hTF (E.symm (j, i)).2
  -- if every group has an open edge, at least `M` edges of `F` are open
  have hsub : (atLeastOpen F M)ᶜ ⊆ ⋃ j : Fin M, {ω : BondConfig V | ∀ e ∈ grp j, e ∉ ω} := by
    intro ω hω
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    by_contra hall
    push Not at hall
    choose f hf hfω using hall
    apply hω
    refine ⟨(Finset.univ : Finset (Fin M)).image f, ?_, ?_, ?_⟩
    · intro e he
      rw [Finset.mem_image] at he
      obtain ⟨j, -, rfl⟩ := he
      exact hgrp_T j _ (hf j)
    · rw [Finset.card_image_of_injective _ ?_, Finset.card_univ, Fintype.card_fin]
      intro j j' hjj'
      have h1 := hf j
      have h2 := hf j'
      rw [Finset.mem_image] at h1 h2
      obtain ⟨i, -, hi⟩ := h1
      obtain ⟨i', -, hi'⟩ := h2
      have : (E.symm (j, i) : Sym2 V) = E.symm (j', i') := by rw [hi, hi', hjj']
      have := E.symm.injective (Subtype.val_injective this)
      simpa using (Prod.ext_iff.1 this).1
    · intro e he
      rw [Finset.coe_image, Set.mem_image] at he
      obtain ⟨j, -, rfl⟩ := he
      exact hfω j
  calc (bondPercolation G p).real (atLeastOpen F M)ᶜ
      ≤ (bondPercolation G p).real (⋃ j : Fin M, {ω : BondConfig V | ∀ e ∈ grp j, e ∉ ω}) :=
        measureReal_mono hsub
    _ ≤ ∑ j : Fin M, (bondPercolation G p).real {ω : BondConfig V | ∀ e ∈ grp j, e ∉ ω} :=
        measureReal_iUnion_fintype_le _
    _ = ∑ _j : Fin M, (1 - (p : ℝ)) ^ g := Finset.sum_congr rfl fun j _ => by
        rw [bondPercolation_real_forall_notMem_eq G p (grp j) (hgrp_sub j), hgrp_card]
    _ = M * (1 - (p : ℝ)) ^ g := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Hence `1 - M(1-p)^g ≤ P_p(atLeastOpen F M)` when `|F| ≥ M g`.
[cite: GrimmettPercolation1999, §7.3 p. 167 (7.45)] -/
theorem le_prob_atLeastOpen [Countable V] (G : SimpleGraph V) (p : unitInterval)
    {F : Finset (Sym2 V)} (hF : (↑F : Set (Sym2 V)) ⊆ G.edgeSet) {M g : ℕ} (hcard : M * g ≤ F.card) :
    1 - M * (1 - (p : ℝ)) ^ g ≤ (bondPercolation G p).real (atLeastOpen F M) := by
  have h := prob_compl_atLeastOpen_le G p hF hcard
  rw [probReal_compl_eq_one_sub (measurableSet_atLeastOpen F M)] at h
  linarith

end AtLeastOpen

end BGN

end Percolation.Literature

end
