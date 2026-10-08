import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProductMeasure
import Percolation.Literature.Basic
import Percolation.Literature.BondPercolationSymmetry
import Percolation.Util.Linter

/-!
# The zero–one law for shift-invariant events of independent families

Grimmett, *Percolation*, 2nd ed. (1999) uses, at
several places, "the zero–one law for the invariant σ-field of a family of independent random
variables indexed by `ℤ²`" (§7.3, p. 165, in the proof of Lemma (7.36): the event
`J = {L ↔ ∞ in ℍ*}` "is invariant under shifts of the form `x ↦ x + (i, j, 0)` … therefore `J` has
probability either `0` or `1`"; likewise §8.2, p. 199, proof of Thm. (8.1): "the underlying
product measure is ergodic with respect to translations of the lattice"). This is the ergodicity
of Bernoulli shifts, which Mathlib does not have (its `Dynamics/Ergodic` provides the bundled
/`Ergodic` and their API, which we use). We prove it here, sorry-free, in
three layers:

* `ergodic_relabel_shift_bondPercolation` — PERCOLATION FORM (the statement quoted above): for
  bond percolation `P_p` on `ℤ^d` and a non-zero `v ∈ ℤ^d`, the translation of configurations
  `ω ↦ ω + v` (`BondConfig.relabel (sym2Equiv (Site.shift v))`, `BondPercolationSymmetry.lean`)
  is `Ergodic`; `bondPercolation_zero_one_of_relabel_shift`: every measurable event invariant
  under it has `P_p`-probability `0` or `1`.

## References

* G. Grimmett, *Percolation*, 2nd ed., Grundlehren 321, Springer 1999, §7.3 p. 165 (proof of
  Lemma (7.36)); §8.2 p. 199.
* (Standard) P. Walters, *An Introduction to Ergodic Theory*, GTM 79, Springer 1982, Thm. 1.17
  (mixing on a generating semi-algebra) and §1.5 (Bernoulli shifts are mixing).
-/

noncomputable section

namespace Percolation.Literature

open MeasureTheory ProbabilityTheory
open scoped symmDiff ENNReal

/-! ## Abstract form: invariant events of a mixing transformation are trivial -/

section Abstract

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

/-- **Abstract zero–one law** (mixing on a generating ring ⇒ invariant events are trivial;
Walters 1982, Thm. 1.17 & §1.5, the mechanism behind Grimmett 1999, p. 165 "zero–one law for the
invariant σ-field"). Let `T` preserve the probability measure `μ`, let the ring of sets `C`
generate the σ-algebra and cover the space up to a null set, and suppose that for every `B ∈ C`
some iterate `T⁻ⁿB` is independent of `B`. Then every measurable `A` with `T⁻¹A = A` has
`μ(A) = 0` or `μ(A) = 1`. [cite: GrimmettPercolation1999, §7.3 p. 165 (zero-one law for the invariant σ-field)] -/
theorem measure_eq_zero_or_one_of_preimage_eq [IsProbabilityMeasure μ] {C : Set (Set Ω)}
    (hC : IsSetRing C) (hcov : ∃ D : Set (Set Ω), D.Countable ∧ D ⊆ C ∧ μ (⋃₀ D)ᶜ = 0)
    (hgen : mΩ = MeasurableSpace.generateFrom C) {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    (hmix : ∀ B ∈ C, ∃ n : ℕ, μ (B ∩ T^[n] ⁻¹' B) = μ B * μ B)
    {A : Set Ω} (hA : MeasurableSet A) (hinv : T ⁻¹' A = A) :
    μ A = 0 ∨ μ A = 1 := by
  -- Step 1: `|μ(A) - μ(A)²| < 4ε` for every `ε > 0`.
  have key : ∀ ε : ℝ, 0 < ε → |μ.real A - μ.real A * μ.real A| < 4 * ε := by
    intro ε hε
    obtain ⟨B, hBC, hBA⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing hC hcov hgen hA
      (ENNReal.ofReal_pos.2 hε)
    have hBm : MeasurableSet B := by
      have : MeasurableSet[MeasurableSpace.generateFrom C] B :=
        MeasurableSpace.measurableSet_generateFrom hBC
      rwa [← hgen] at this
    obtain ⟨n, hn⟩ := hmix B hBC
    have hS : MeasurePreserving T^[n] μ μ := hT.iterate n
    have hSA : T^[n] ⁻¹' A = A := Function.IsFixedPt.preimage_iterate hinv n
    -- the approximation error `d = μ(B ∆ A) < ε`
    have hd : μ.real (B ∆ A) < ε := ENNReal.toReal_lt_of_lt_ofReal hBA
    have h1 : |μ.real A - μ.real B| ≤ μ.real (B ∆ A) := by
      rw [symmDiff_comm]
      exact abs_measureReal_sub_le_measureReal_symmDiff hA.nullMeasurableSet hBm.nullMeasurableSet
    -- `|μ(A) - μ(B ∩ T⁻ⁿB)| ≤ 2d`
    have h2 : |μ.real A - μ.real (B ∩ T^[n] ⁻¹' B)| ≤ 2 * μ.real (B ∆ A) := by
      have hpre : μ.real (T^[n] ⁻¹' (A ∆ B)) = μ.real (A ∆ B) := by
        simp only [measureReal_def]
        rw [hS.measure_preimage (hA.symmDiff hBm).nullMeasurableSet]
      calc |μ.real A - μ.real (B ∩ T^[n] ⁻¹' B)|
          = |μ.real (A ∩ T^[n] ⁻¹' A) - μ.real (B ∩ T^[n] ⁻¹' B)| := by
            rw [hSA, Set.inter_self]
        _ ≤ μ.real ((A ∩ T^[n] ⁻¹' A) ∆ (B ∩ T^[n] ⁻¹' B)) :=
            abs_measureReal_sub_le_measureReal_symmDiff
              (hA.inter (hS.measurable hA)).nullMeasurableSet
              (hBm.inter (hS.measurable hBm)).nullMeasurableSet
        _ ≤ μ.real ((A ∆ B) ∪ T^[n] ⁻¹' (A ∆ B)) := by
            refine measureReal_mono ?_
            intro x hx
            simp only [Set.mem_symmDiff, Set.mem_inter_iff, Set.mem_preimage, Set.mem_union] at hx ⊢
            tauto
        _ ≤ μ.real (A ∆ B) + μ.real (T^[n] ⁻¹' (A ∆ B)) := measureReal_union_le _ _
        _ = 2 * μ.real (B ∆ A) := by rw [hpre, symmDiff_comm]; ring
    -- independence: `μ(B ∩ T⁻ⁿB) = μ(B)²`
    have h3 : μ.real (B ∩ T^[n] ⁻¹' B) = μ.real B * μ.real B := by
      simp only [measureReal_def]; rw [hn, ENNReal.toReal_mul]
    rw [h3] at h2
    have hA0 : 0 ≤ μ.real A := measureReal_nonneg
    have hA1 : μ.real A ≤ 1 := measureReal_le_one
    have hB0 : 0 ≤ μ.real B := measureReal_nonneg
    have hB1 : μ.real B ≤ 1 := measureReal_le_one
    have h4 : |μ.real B * μ.real B - μ.real A * μ.real A| ≤ 2 * μ.real (B ∆ A) := by
      have : μ.real B * μ.real B - μ.real A * μ.real A =
          (μ.real B - μ.real A) * (μ.real B + μ.real A) := by ring
      rw [this, abs_mul, abs_sub_comm]
      calc |μ.real A - μ.real B| * |μ.real B + μ.real A| ≤ μ.real (B ∆ A) * 2 := by
            refine mul_le_mul h1 ?_ (abs_nonneg _) measureReal_nonneg
            rw [abs_le]; constructor <;> linarith
        _ = 2 * μ.real (B ∆ A) := by ring
    calc |μ.real A - μ.real A * μ.real A|
        ≤ |μ.real A - μ.real B * μ.real B| + |μ.real B * μ.real B - μ.real A * μ.real A| :=
          abs_sub_le _ _ _
      _ ≤ 4 * μ.real (B ∆ A) := by linarith
      _ < 4 * ε := by linarith
  -- Step 2: hence `μ(A) = μ(A)²`, i.e. `μ(A) ∈ {0, 1}`.
  have ha : μ.real A - μ.real A * μ.real A = 0 := by
    by_contra hne
    have hpos : 0 < |μ.real A - μ.real A * μ.real A| := abs_pos.2 hne
    have := key (|μ.real A - μ.real A * μ.real A| / 4) (by positivity)
    linarith
  have hreal : μ.real A = 0 ∨ μ.real A = 1 := by
    have : μ.real A * (1 - μ.real A) = 0 := by rw [← ha]; ring
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  rcases hreal with h | h
  · exact Or.inl ((measureReal_eq_zero_iff (measure_ne_top μ A)).1 h)
  · right
    rw [measureReal_def] at h
    exact (ENNReal.toReal_eq_one_iff _).1 h

/-- From the zero–one property to Mathlib's `PreErgodic`. [folklore] -/
theorem preErgodic_of_prob_eq_zero_or_one [IsProbabilityMeasure μ] {T : Ω → Ω}
    (h : ∀ ⦃A : Set Ω⦄, MeasurableSet A → T ⁻¹' A = A → μ A = 0 ∨ μ A = 1) : PreErgodic T μ := by
  refine ⟨fun A hA hinv => ?_⟩
  rw [Filter.eventuallyConst_set']
  rcases h hA hinv with h0 | h1
  · exact Or.inl (ae_eq_empty.2 h0)
  · exact Or.inr (ae_eq_univ.2 ((prob_compl_eq_zero_iff hA).2 h1))

/-- **Abstract zero–one law, bundled**: under the hypotheses of
`measure_eq_zero_or_one_of_preimage_eq` (mixing on a generating ring), `T` is `PreErgodic`, hence
`Ergodic`, for `μ` (Walters 1982, Thm. 1.17). [folklore] -/
theorem ergodic_of_mixing_on_isSetRing [IsProbabilityMeasure μ] {C : Set (Set Ω)}
    (hC : IsSetRing C) (hcov : ∃ D : Set (Set Ω), D.Countable ∧ D ⊆ C ∧ μ (⋃₀ D)ᶜ = 0)
    (hgen : mΩ = MeasurableSpace.generateFrom C) {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    (hmix : ∀ B ∈ C, ∃ n : ℕ, μ (B ∩ T^[n] ⁻¹' B) = μ B * μ B) : Ergodic T μ :=
  ⟨hT, preErgodic_of_prob_eq_zero_or_one fun _ hA hinv =>
    measure_eq_zero_or_one_of_preimage_eq hC hcov hgen hT hmix hA hinv⟩

end Abstract

/-! ## Product form: Bernoulli shifts are ergodic -/

section Product

variable {ι : Type*} {X : Type*}

/-- The coordinate shift `ω ↦ ω ∘ g` along a reindexing `g`. [folklore] -/
def coordShift (g : ι → ι) (ω : ι → X) : ι → X := fun i => ω (g i)

/-- The coordinate shift, evaluated. [folklore] -/
@[simp] theorem coordShift_apply (g : ι → ι) (ω : ι → X) (i : ι) : coordShift g ω i = ω (g i) :=
  rfl

/-- Iterating the shift along `g` is the shift along the iterate of `g`. [folklore] -/
theorem coordShift_iterate (g : ι → ι) (n : ℕ) :
    (coordShift (X := X) g)^[n] = coordShift (g^[n]) := by
  induction n with
  | zero => funext ω; funext i; simp [coordShift]
  | succ n ih =>
    funext ω; funext i
    rw [Function.iterate_succ', Function.comp_apply, ih]
    change ω (g^[n] (g i)) = ω (g^[n + 1] i)
    rw [Function.iterate_succ_apply]

variable [MeasurableSpace X]

/-- `coordShift g` is measurable for the product σ-algebra. [folklore] -/
theorem measurable_coordShift (g : ι → ι) : Measurable (coordShift (X := X) g) :=
  measurable_pi_lambda _ fun i => measurable_pi_apply (g i)

/-- The shift along an injective, law-preserving reindexing preserves the product measure
(Mathlib's `Measure.map_infinitePi_infinitePi_of_inj`). [folklore] -/
theorem measurePreserving_coordShift (P : ι → Measure X) [∀ i, IsProbabilityMeasure (P i)]
    {g : ι → ι} (hg : Function.Injective g) (hP : ∀ i, P (g i) = P i) :
    MeasurePreserving (coordShift (X := X) g) (Measure.infinitePi P) (Measure.infinitePi P) := by
  refine ⟨measurable_coordShift g, ?_⟩
  have h := Measure.map_infinitePi_infinitePi_of_inj (P := P) hg
  have hP' : (fun i => P (g i)) = P := funext hP
  rw [hP'] at h
  exact h

/-- Under a product probability measure, a cylinder event over the finite index set `s` is
independent of its shift along `g` as soon as `g(s)` is disjoint from `s`
(`iIndepFun_infinitePi`). [folklore] -/
theorem infinitePi_inter_preimage_coordShift_cylinder (P : ι → Measure X)
    [∀ i, IsProbabilityMeasure (P i)] {g : ι → ι} (s : Finset ι)
    (hdisj : ∀ i ∈ s, g i ∉ s) {S : Set (s → X)} (hS : MeasurableSet S) :
    Measure.infinitePi P (cylinder s S ∩ coordShift g ⁻¹' cylinder s S) =
      Measure.infinitePi P (cylinder s S) * Measure.infinitePi P (coordShift g ⁻¹' cylinder s S) := by
  classical
  have hdisj' : Disjoint (s.image g) s := by
    rw [Finset.disjoint_left]
    intro j hj hjs
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hj
    exact hdisj i hi hjs
  -- the coordinates are independent under the product measure
  have hind : iIndepFun (fun (i : ι) (ω : ι → X) => ω i) (Measure.infinitePi P) :=
    iIndepFun_infinitePi (P := P) (X := fun _ x => x) fun _ => measurable_id
  have hst := hind.indepFun_finset s (s.image g) hdisj'.symm fun _ => measurable_pi_apply _
  -- express both events through the restrictions to `s` and to `g(s)`
  let ρ : (↥(s.image g) → X) → (↥s → X) :=
    fun v i => v ⟨g i, Finset.mem_image_of_mem g i.2⟩
  have hρ : Measurable ρ := measurable_pi_lambda _ fun i => measurable_pi_apply _
  have hB : cylinder s S = (fun (ω : ι → X) (i : ↥s) => ω i) ⁻¹' S := rfl
  have hB' : coordShift g ⁻¹' cylinder s S =
      (fun (ω : ι → X) (i : ↥(s.image g)) => ω i) ⁻¹' (ρ ⁻¹' S) := by
    ext ω; simp only [Set.mem_preimage, mem_cylinder]; rfl
  rw [hB', hB]
  exact hst.measure_inter_preimage_eq_mul _ _ hS (hρ hS)

/-- **Bernoulli shifts are ergodic** (indeed mixing; the "zero–one law for the invariant σ-field
of a family of independent random variables indexed by `ℤ²`" of Grimmett 1999, p. 165, in
Mathlib's bundled form). Let `P_i` be probability measures with `P_{g i} = P_i` for an injective
`g : ι → ι` some iterate of which moves any given finite set of indices off itself. Then the shift
`ω ↦ ω ∘ g` is `Ergodic` for `⨂ P_i`.
[cite: GrimmettPercolation1999, §7.3 p. 165 (zero-one law for the invariant σ-field)] -/
theorem ergodic_coordShift_infinitePi (P : ι → Measure X) [∀ i, IsProbabilityMeasure (P i)]
    {g : ι → ι} (hg : Function.Injective g) (hP : ∀ i, P (g i) = P i)
    (hdis : ∀ s : Finset ι, ∃ n : ℕ, ∀ i ∈ s, g^[n] i ∉ s) :
    Ergodic (coordShift (X := X) g) (Measure.infinitePi P) := by
  classical
  refine ergodic_of_mixing_on_isSetRing (C := measurableCylinders fun _ : ι => X)
    isSetRing_measurableCylinders ?_ generateFrom_measurableCylinders.symm
    (measurePreserving_coordShift P hg hP) ?_
  · refine ⟨{Set.univ}, Set.countable_singleton _, ?_, by simp⟩
    rw [Set.singleton_subset_iff]
    exact isSetAlgebra_measurableCylinders.univ_mem
  · have hPn : ∀ (n : ℕ) (i : ι), P (g^[n] i) = P i := by
      intro n
      induction n with
      | zero => intro i; rfl
      | succ k ih => intro i; rw [Function.iterate_succ_apply', hP, ih]
    intro B hB
    obtain ⟨s, S, hS, rfl⟩ := (mem_measurableCylinders B).1 hB
    obtain ⟨n, hn⟩ := hdis s
    refine ⟨n, ?_⟩
    rw [coordShift_iterate,
      infinitePi_inter_preimage_coordShift_cylinder P s hn hS,
      (measurePreserving_coordShift P (hg.iterate n) (hPn n)).measure_preimage
        (MeasurableSet.cylinder s hS).nullMeasurableSet]

end Product

/-! ## Percolation form: translation-invariant events of `P_p` on `ℤ^d` are trivial -/

section Percolation

open unitInterval

variable {d : ℕ}

/-- Iterated edge translation: `(· + v)^n = (· + n • v)` on edges. [folklore] -/
theorem sym2Map_add_iterate (v : LatticeModels.Site d) (n : ℕ) :
    (Sym2.map fun x : LatticeModels.Site d => x + v)^[n] = Sym2.map fun x : LatticeModels.Site d => x + n • v := by
  induction n with
  | zero => funext e; simp
  | succ n ih =>
    funext e
    rw [Function.iterate_succ', Function.comp_apply, ih, Sym2.map_map]
    congr 1
    funext x
    simp only [Function.comp_apply, succ_nsmul]
    abel

/-- A large multiple of a non-zero vector moves every finite set of edges off itself: if
`v_k ≠ 0`, the functional `s(x, y) ↦ x_k + y_k` is bounded on `s` and is translated by
`2 n v_k`. [folklore] -/
theorem exists_iterate_sym2Map_add_notMem {v : LatticeModels.Site d} (hv : v ≠ 0)
    (s : Finset (Sym2 (LatticeModels.Site d))) :
    ∃ n : ℕ, ∀ e ∈ s, (Sym2.map fun x : LatticeModels.Site d => x + v)^[n] e ∉ s := by
  classical
  obtain ⟨k, hk⟩ : ∃ k, v k ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  let φ : Sym2 (LatticeModels.Site d) → ℤ := Sym2.lift ⟨fun x y => x k + y k, fun x y => add_comm _ _⟩
  have hφ : ∀ (e : Sym2 (LatticeModels.Site d)) (n : ℕ),
      φ (e.map fun x : LatticeModels.Site d => x + n • v) = φ e + 2 * n * v k := by
    intro e n
    induction e using Sym2.ind with
    | h x y =>
      simp only [φ, Sym2.map_mk, Sym2.lift_mk, Pi.add_apply, nsmul_eq_mul, Pi.mul_apply,
        Pi.natCast_apply]
      ring
  let M : ℕ := s.sup fun e => (φ e).natAbs
  have hM : ∀ e ∈ s, |φ e| ≤ M := by
    intro e he
    have h : (φ e).natAbs ≤ M := Finset.le_sup (f := fun e => (φ e).natAbs) he
    rw [← Int.natCast_natAbs]
    exact_mod_cast h
  refine ⟨M + 1, ?_⟩
  rw [sym2Map_add_iterate]
  intro e he he's
  have h1 := hM e he
  have h2 := hM _ he's
  rw [hφ] at h2
  have hvk : 1 ≤ |v k| := Int.one_le_abs hk
  have h3 : |2 * ((M + 1 : ℕ) : ℤ) * v k| ≤ 2 * M := by
    calc |2 * ((M + 1 : ℕ) : ℤ) * v k| = |(φ e + 2 * ((M + 1 : ℕ) : ℤ) * v k) - φ e| := by
          ring_nf
      _ ≤ |φ e + 2 * ((M + 1 : ℕ) : ℤ) * v k| + |φ e| := abs_sub _ _
      _ ≤ M + M := add_le_add h2 h1
      _ = 2 * M := by ring
  rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℤ) < 2),
    abs_of_nonneg (by positivity : (0 : ℤ) ≤ ((M + 1 : ℕ) : ℤ))] at h3
  push_cast at h3
  nlinarith

/-- The inverse of the edge translation `sym2Equiv (Site.shift v)` is the edge translation by
`-v`. [folklore] -/
theorem coe_sym2Equiv_shift_symm (v : LatticeModels.Site d) :
    ⇑(sym2Equiv (LatticeModels.Site.shift v)).symm = Sym2.map fun x : LatticeModels.Site d => x + -v := by
  have h : ((LatticeModels.Site.shift v).symm : LatticeModels.Site d → LatticeModels.Site d) = fun x : LatticeModels.Site d => x + -v := by
    funext x
    rw [LatticeModels.Site.shift_symm_apply, sub_eq_add_neg]
  funext e
  rw [sym2Equiv_symm, sym2Equiv_apply, h]

/-- Translation by `-v` is a graph automorphism of `ℤ^d`. [folklore] -/
def zdShiftSymmIso (v : LatticeModels.Site d) : LatticeModels.zdGraph d ≃g LatticeModels.zdGraph d where
  toEquiv := (LatticeModels.Site.shift v).symm
  map_rel_iff' := fun {a b} => by
    rw [← LatticeModels.zdGraph_adj_shift_iff v ((LatticeModels.Site.shift v).symm a) ((LatticeModels.Site.shift v).symm b),
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- `P_p = P^{setOf}`: the coordinate encoding `q ↦ {e | q e}` carries the product of the one-edge
laws to `bondPercolation` (Mathlib's `setBernoulli_eq_map`). [folklore] -/
theorem measurePreserving_setOf_bondPercolation (G : SimpleGraph (LatticeModels.Site d)) (p : unitInterval) :
    MeasurePreserving (fun q : Sym2 (LatticeModels.Site d) → Prop => {i | q i})
      (Measure.infinitePi fun e : Sym2 (LatticeModels.Site d) =>
        toNNReal p • Measure.dirac (e ∈ G.edgeSet) + toNNReal (σ p) • Measure.dirac False)
      (bondPercolation G p) :=
  ⟨measurable_setOf, by rw [bondPercolation, setBernoulli_eq_map]⟩

/-- **Translations of `ℤ^d` act ergodically on bond percolation** (Grimmett 1999, §7.3, p. 165:
an event "invariant under shifts of the form `x ↦ x + (i, j, 0)` … has probability either `0` or
`1`, by the zero–one law for the invariant σ-field of a family of independent random variables";
§8.2 p. 199: "the underlying product measure is ergodic with respect to translations of the
lattice"). For every `p ∈ [0, 1]` and every non-zero `v ∈ ℤ^d`, the translation of
configurations `ω ↦ ω + v` (`BondConfig.relabel (sym2Equiv (Site.shift v))`) is `Ergodic` for
`P_p`. A single non-zero translation suffices.
[cite: GrimmettPercolation1999, §7.3 p. 165 (zero-one law for the invariant σ-field)] -/
theorem ergodic_relabel_shift_bondPercolation (p : unitInterval) {v : LatticeModels.Site d} (hv : v ≠ 0) :
    Ergodic (BondConfig.relabel (sym2Equiv (LatticeModels.Site.shift v))) (bondPercolation (LatticeModels.zdGraph d) p) := by
  classical
  set μ : Sym2 (LatticeModels.Site d) → Measure Prop := fun e =>
    toNNReal p • Measure.dirac (e ∈ (LatticeModels.zdGraph d).edgeSet) + toNNReal (σ p) • Measure.dirac False
    with hμ
  set g : Sym2 (LatticeModels.Site d) → Sym2 (LatticeModels.Site d) := ⇑(sym2Equiv (LatticeModels.Site.shift v)).symm with hg
  -- the coordinate shift along `g` (edge translation by `-v`) is ergodic for the product measure
  have herg : Ergodic (coordShift (X := Prop) g) (Measure.infinitePi μ) := by
    refine ergodic_coordShift_infinitePi μ (sym2Equiv (LatticeModels.Site.shift v)).symm.injective
      (fun e => ?_) fun s => ?_
    · have he : (g e ∈ (LatticeModels.zdGraph d).edgeSet) = (e ∈ (LatticeModels.zdGraph d).edgeSet) := by
        rw [hg, sym2Equiv_symm]
        exact propext (sym2Equiv_mem_edgeSet_iff (zdShiftSymmIso v) e)
      simp only [hμ, he]
    · rw [hg, coe_sym2Equiv_shift_symm]
      exact exists_iterate_sym2Map_add_notMem (neg_ne_zero.2 hv) s
  -- and it is semiconjugate, via `setOf`, to the relabelling by `Site.shift v`
  refine (measurePreserving_setOf_bondPercolation (LatticeModels.zdGraph d) p).ergodic_of_ergodic_semiconj herg
    (BondConfig.relabel (sym2Equiv (LatticeModels.Site.shift v))).measurable fun q => ?_
  ext e
  rw [BondConfig.mem_relabel_iff]
  rfl

/-- **Zero–one law for translation-invariant events of bond percolation on `ℤ^d`**: an event
invariant under the translation `ω ↦ ω + v` (`BondConfig.relabel (sym2Equiv (Site.shift v))`)
by a non-zero vector has `P_p`-probability `0` or `1`
(`ergodic_relabel_shift_bondPercolation` and `PreErgodic.prob_eq_zero_or_one`).
[cite: GrimmettPercolation1999, §7.3 p. 165 (zero-one law for the invariant σ-field)] -/
theorem bondPercolation_zero_one_of_relabel_shift (p : unitInterval) {v : LatticeModels.Site d} (hv : v ≠ 0)
    {A : Set (BondConfig (LatticeModels.Site d))} (hA : MeasurableSet A)
    (hinv : BondConfig.relabel (sym2Equiv (LatticeModels.Site.shift v)) ⁻¹' A = A) :
    bondPercolation (LatticeModels.zdGraph d) p A = 0 ∨ bondPercolation (LatticeModels.zdGraph d) p A = 1 :=
  (ergodic_relabel_shift_bondPercolation p hv).toPreErgodic.prob_eq_zero_or_one hA hinv

end Percolation

end Percolation.Literature

end
