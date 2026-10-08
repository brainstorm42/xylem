import Mathlib.Combinatorics.SetFamily.FourFunctions
import Percolation.Literature.Inequalities
import Percolation.Util.Linter

/-!
# Harris's inequality for local increasing events (the local case of `harris_fkg`)

Harris's lemma (Harris, *Proc. Camb. Phil. Soc.* 56 (1960),
Lemma 4.1; Bollobás–Riordan, *Percolation* (2006), Ch. 2, Lemma 3 "Harris's Lemma"; Grimmett,
*Percolation* (1999), Thm. 2.4, first part of the proof, "suppose first that `X`, `Y` depend only
on the states of finitely many edges") for Bernoulli bond percolation `P_p = bondPercolation G p`
on an arbitrary graph: increasing events `A`, `B` that depend on finitely many coordinates
(`Percolation.Literature.IsLocalEvent`) satisfy `P_p(A) P_p(B) ≤ P_p(A ∩ B)` (`harris_fkg_local`).

This is the case of the statement `Percolation.Literature.harris_fkg` (`Inequalities.lean`) that all
box-crossing arguments use (crossing events of finite rectangles are local); the extension to
arbitrary measurable increasing events (Grimmett's second step, by martingale convergence) is
not done here.

Proof. Fix a finite set `F` of coordinates determining both events. The cylinders
`cylOf F a = {ω | ω ∩ F ≙ a}`, `a : F → Bool`, partition the configuration space into finitely
many measurable pieces of `P_p`-mass `cylWeight G p F a = ∏_{e ∈ F} ν_e({a e})`, where `ν_e` is
the one-coordinate law of `setBer(E(G), p)` (`coordMeasure`; Mathlib's `Measure.infinitePi_pi`).
Hence `P_p(A) = ∑_a cylWeight a · 𝟙_A(cfgOf a)` for every event `A` determined by `F`
(`real_eq_sum_of_determinedBy`). The weight is a product over coordinates, so it is
log-modular on the Boolean lattice `F → Bool` (`cylWeight_mul`), and Mathlib's FKG inequality on
finite distributive lattices (`fkg`, `Mathlib/Combinatorics/SetFamily/FourFunctions.lean`,
Ahlswede–Daykin four functions theorem) applied to the monotone indicators gives the claim.

Mathlib anchors: `fkg`, `Measure.infinitePi_pi`, `ProbabilityTheory.setBernoulli_apply'`,
`measureReal_biUnion_finset`, `Set.indicator`.
-/

namespace Percolation.Literature

open MeasureTheory ProbabilityTheory LatticeModels unitInterval
open scoped ENNReal

noncomputable section

variable {V : Type*} (G : SimpleGraph V) (p : unitInterval) (F : Finset (Sym2 V))

/-- The one-coordinate law of `setBer(E(G), p)` at the coordinate `e : Sym2 V`, a probability
measure on `Prop`: `p δ_{e ∈ E(G)} + (1 - p) δ_{False}` (so an edge of `G` is open with
probability `p`, a non-edge never). This is the factor of Mathlib's `setBernoulli`.
(Grimmett 1999, §1.3, `μ_e`.) [folklore] -/
def coordMeasure (e : Sym2 V) : Measure Prop :=
  toNNReal p • Measure.dirac (e ∈ G.edgeSet) + toNNReal (σ p) • Measure.dirac False

/-- `coordMeasure G p e` is a probability measure. [folklore] -/
instance instIsProbabilityMeasureCoordMeasure (e : Sym2 V) :
    IsProbabilityMeasure (coordMeasure G p e) := by
  unfold coordMeasure; infer_instance

/-- `P_p(S)` is the infinite product of the one-coordinate laws evaluated on the preimage of `S`
under `q ↦ {i | q i}` (Mathlib's `setBernoulli_apply'`). (Grimmett 1999, §1.3, `P_p = ∏_e μ_e`.) [folklore] -/
theorem bondPercolation_apply' (S : Set (BondConfig V)) :
    bondPercolation G p S =
      Measure.infinitePi (coordMeasure G p) ((fun q : Sym2 V → Prop => {i | q i}) ⁻¹' S) :=
  setBernoulli_apply' S

/-- The configuration `{e ∈ F | a e}` on `F` encoded by `a : F → Bool`, as a set of edges (all
coordinates outside `F` closed). [folklore] -/
def cfgOf (a : F → Bool) : Set (Sym2 V) := {e | ∃ h : e ∈ F, a ⟨e, h⟩ = true}

/-- The cylinder of configurations whose restriction to `F` is `a`. (Grimmett 1999, §2.2,
cylinder events.) [folklore] -/
def cylOf (a : F → Bool) : Set (BondConfig V) :=
  {ω | ∀ (e) (h : e ∈ F), e ∈ ω ↔ a ⟨e, h⟩ = true}

/-- The `P_p`-mass of the cylinder `cylOf F a`, written as the product over `e ∈ F` of the
one-coordinate masses `ν_e({P | P ↔ a e})`. [folklore] -/
def cylWeight (a : F → Bool) : ℝ :=
  ∏ e : F, ((coordMeasure G p e) {P | P ↔ a e = true}).toReal

/-- `cfgOf` is monotone for the pointwise order on `F → Bool`. [folklore] -/
theorem cfgOf_mono : Monotone (cfgOf F) := by
  intro a b hab e
  simp only [cfgOf, Set.mem_setOf_eq]
  rintro ⟨h, ha⟩
  exact ⟨h, by have := hab ⟨e, h⟩; rw [ha] at this; exact top_le_iff.mp this⟩

/-- `P_p(cylOf F a) = cylWeight G p F a` (Mathlib's `Measure.infinitePi_pi` on the box
`Set.pi F _`). (Grimmett 1999, §1.3, product structure of `P_p`.) [folklore] -/
theorem real_cylOf (a : F → Bool) :
    (bondPercolation G p).real (cylOf F a) = cylWeight G p F a := by
  classical
  rw [measureReal_def, bondPercolation_apply']
  set t : Sym2 V → Set Prop := fun e => {P | P ↔ (if h : e ∈ F then a ⟨e, h⟩ else false) = true}
  have hpre : (fun q : Sym2 V → Prop => {i | q i}) ⁻¹' cylOf F a = Set.pi (↑F) t := by
    ext q
    simp only [cylOf, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_pi, Finset.mem_coe, t]
    constructor
    · intro h e he; rw [dif_pos he]; exact h e he
    · intro h e he; have := h e he; rwa [dif_pos he] at this
  rw [hpre, Measure.infinitePi_pi _ (fun _ _ => MeasurableSet.of_discrete), cylWeight,
    ENNReal.toReal_prod, ← Finset.prod_attach]
  refine Finset.prod_congr rfl fun e _ => ?_
  simp only [t, dif_pos e.2]

/-- Cylinder weights are non-negative. [folklore] -/
theorem cylWeight_nonneg (a : F → Bool) : 0 ≤ cylWeight G p F a :=
  Finset.prod_nonneg fun _ _ => ENNReal.toReal_nonneg

/-- Cylinder weights are log-modular on the Boolean lattice `F → Bool`:
`w(a) w(b) = w(a ⊓ b) w(a ⊔ b)`, coordinate by coordinate. This is the lattice condition of the
FKG inequality for product measures. (Grimmett 1999, Thm. 2.4; Fortuin–Kasteleyn–Ginibre 1971.) [folklore] -/
theorem cylWeight_mul (a b : F → Bool) :
    cylWeight G p F a * cylWeight G p F b =
      cylWeight G p F (a ⊓ b) * cylWeight G p F (a ⊔ b) := by
  simp only [cylWeight, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun e _ => ?_
  simp only [Pi.inf_apply, Pi.sup_apply]
  cases a e <;> cases b e <;> simp [mul_comm]

/-- Distinct restrictions give disjoint cylinders. [folklore] -/
theorem pairwiseDisjoint_cylOf :
    Set.PairwiseDisjoint (Set.univ : Set (F → Bool)) (cylOf F) := by
  intro a _ b _ hab
  rw [Function.onFun, Set.disjoint_left]
  intro ω ha hb
  apply hab
  funext e
  have h1 := ha e e.2
  have h2 := hb e e.2
  simp only [Subtype.coe_eta] at h1 h2
  rw [Bool.eq_iff_iff, ← h1, ← h2]

/-- Cylinders over the finite set `F` are measurable. (Grimmett 1999, §2.2.) [folklore] -/
theorem measurableSet_cylOf (a : F → Bool) : MeasurableSet (cylOf F a) := by
  have : cylOf F a = ⋂ e : F, {ω : BondConfig V | (e : Sym2 V) ∈ ω ↔ a e = true} := by
    ext ω; simp only [cylOf, Set.mem_setOf_eq, Set.mem_iInter, Subtype.forall]
  rw [this]
  refine MeasurableSet.iInter fun e => ?_
  by_cases h : a e = true
  · simpa [h] using measurableSet_mem (e : Sym2 V)
  · simpa [h] using measurableSet_notMem (e : Sym2 V)

open Classical in
/-- **Finite-dimensional distributions of `P_p`.** For an event `A` determined by the finite
set `F` of coordinates, `P_p(A) = ∑_{a : F → Bool} P_p(cylOf F a) 𝟙_A(cfgOf F a)`: the cylinders
partition the space and `A` is the union of those whose pattern lies in `A`.
(Grimmett 1999, §2.2; Bollobás–Riordan 2006, Ch. 2, proof of Lemma 3.) [folklore] -/
theorem real_eq_sum_of_determinedBy {A : Set (BondConfig V)} (hA : DeterminedBy A (↑F : Set (Sym2 V))) :
    (bondPercolation G p).real A =
      ∑ a : F → Bool, cylWeight G p F a * A.indicator 1 (cfgOf F a) := by
  have hAeq : A = ⋃ a ∈ (Finset.univ.filter fun a : F → Bool => cfgOf F a ∈ A), cylOf F a := by
    rw [determinedBy_iff] at hA
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_iUnion, exists_prop]
    constructor
    · intro hω
      refine ⟨fun e => decide ((e : Sym2 V) ∈ ω), ?_, ?_⟩
      · refine (hA ω _ ?_).1 hω
        ext e
        simp only [Set.mem_inter_iff, Finset.mem_coe, cfgOf, Set.mem_setOf_eq, decide_eq_true_eq]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨⟨h2, h1⟩, h2⟩
        · rintro ⟨⟨h2, h1⟩, -⟩; exact ⟨h1, h2⟩
      · intro e he; simp
    · rintro ⟨a, haA, hω⟩
      refine (hA ω (cfgOf F a) ?_).2 haA
      ext e
      simp only [Set.mem_inter_iff, Finset.mem_coe, cfgOf, Set.mem_setOf_eq]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨⟨h2, (hω e h2).1 h1⟩, h2⟩
      · rintro ⟨⟨h2, h1⟩, -⟩; exact ⟨(hω e h2).2 h1, h2⟩
  conv_lhs => rw [hAeq]
  rw [measureReal_biUnion_finset ((pairwiseDisjoint_cylOf F).subset (Set.subset_univ _))
    (fun a _ => measurableSet_cylOf F a)]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : cfgOf F a ∈ A
  · simp [h, real_cylOf]
  · simp [h]

/-- The sure event is determined by any index set (auxiliary copy; the general lemma belongs to
`PercolationEvents.lean`). [folklore] -/
private theorem determinedBy_univ_aux (K : Set (Sym2 V)) :
    DeterminedBy (Set.univ : Set (BondConfig V)) K := by
  rw [determinedBy_iff]; simp

/-- Intersections of events determined by `K` are determined by `K` (auxiliary copy). [folklore] -/
private theorem determinedBy_inter_aux {ι : Type*} {A B : Set (Set ι)} {K : Set ι}
    (hA : DeterminedBy A K) (hB : DeterminedBy B K) : DeterminedBy (A ∩ B) K := by
  rw [determinedBy_iff] at hA hB ⊢
  intro ω ω' h
  rw [Set.mem_inter_iff, Set.mem_inter_iff, hA ω ω' h, hB ω ω' h]

/-- `DeterminedBy` is monotone in the index set (auxiliary copy). [folklore] -/
private theorem determinedBy_mono_aux {ι : Type*} {A : Set (Set ι)} {K K' : Set ι}
    (h : DeterminedBy A K) (hK : K ⊆ K') : DeterminedBy A K' := by
  rw [determinedBy_iff] at h ⊢
  intro ω ω' hω
  refine h ω ω' ?_
  rw [← Set.inter_eq_self_of_subset_left hK, Set.inter_comm K K', ← Set.inter_assoc,
    ← Set.inter_assoc, hω]

/-- Indicators of increasing events are monotone functions of the pattern `a : F → Bool`.
(Grimmett 1999, §2.1.) [folklore] -/
theorem monotone_indicator_cfgOf {A : Set (BondConfig V)} (hA : IsUpperSet A) :
    Monotone fun a : F → Bool => A.indicator (1 : BondConfig V → ℝ) (cfgOf F a) := by
  intro a b hab
  by_cases ha : cfgOf F a ∈ A
  · have hb : cfgOf F b ∈ A := hA (cfgOf_mono F hab) ha
    simp [ha, hb]
  · simp only [Set.indicator_of_notMem ha]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) _

/-- **Harris's inequality, local case** (Harris, *Proc. Camb. Phil. Soc.* 56
(1960), Lemma 4.1; Bollobás–Riordan, *Percolation* (2006), Ch. 2, Lemma 3; Grimmett,
*Percolation* (1999), Thm. 2.4, first step of the proof). Under Bernoulli bond percolation
`P_p` on any graph `G`, increasing events depending on finitely many coordinates are positively
correlated: `P_p(A) P_p(B) ≤ P_p(A ∩ B)`. This is `Percolation.Literature.harris_fkg` restricted to local
events (no measurability hypothesis is needed: local events are measurable). Proof by Mathlib's
FKG inequality `fkg` on the finite distributive lattice `F → Bool` with the log-modular product
weight `cylWeight`. [cite: BollobasRiordanPercolation2006, Ch. 2, Lemma 3] [cite: GrimmettPercolation1999, Thm. 2.4] -/
theorem harris_fkg_local {A B : Set (BondConfig V)} (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hAl : IsLocalEvent A) (hBl : IsLocalEvent B) :
    (bondPercolation G p).real A * (bondPercolation G p).real B ≤
      (bondPercolation G p).real (A ∩ B) := by
  classical
  obtain ⟨FA, hFA⟩ := hAl
  obtain ⟨FB, hFB⟩ := hBl
  set F := FA ∪ FB
  have hA' : DeterminedBy A (↑F : Set (Sym2 V)) := determinedBy_mono_aux hFA (by simp [F])
  have hB' : DeterminedBy B (↑F : Set (Sym2 V)) := determinedBy_mono_aux hFB (by simp [F])
  have key := fkg (μ := cylWeight G p F)
    (f := fun a => A.indicator (1 : BondConfig V → ℝ) (cfgOf F a))
    (g := fun a => B.indicator (1 : BondConfig V → ℝ) (cfgOf F a))
    (cylWeight_nonneg G p F) (fun a => Set.indicator_nonneg (fun _ _ => zero_le_one) _)
    (fun a => Set.indicator_nonneg (fun _ _ => zero_le_one) _)
    (monotone_indicator_cfgOf F hA) (monotone_indicator_cfgOf F hB)
    (fun a b => (cylWeight_mul G p F a b).le)
  have h1 : ∑ a, cylWeight G p F a = 1 := by
    have := real_eq_sum_of_determinedBy G p F (determinedBy_univ_aux (↑F : Set (Sym2 V)))
    simp only [Set.indicator_univ, Pi.one_apply, mul_one, probReal_univ] at this
    exact this.symm
  rw [real_eq_sum_of_determinedBy G p F hA', real_eq_sum_of_determinedBy G p F hB',
    real_eq_sum_of_determinedBy G p F (determinedBy_inter_aux hA' hB')]
  rw [h1, one_mul] at key
  refine key.trans_eq (Finset.sum_congr rfl fun a _ => ?_)
  congr 1
  by_cases ha : cfgOf F a ∈ A <;> by_cases hb : cfgOf F a ∈ B <;> simp [ha, hb]

end

end Percolation.Literature
