import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Percolation.Literature.Inequalities
import Percolation.Util.Linter

/-!
# Russo's formula for Bernoulli bond percolation: proof

This file proves the statements `Percolation.Literature.russo_formula` and
`Percolation.Literature.russo_formula_sum` of `Percolation.Literature.Inequalities`:

* `russo_formula_sum_holds : russo_formula_sum` — for an increasing event `A` determined by a
  finite set `F` of pairs, `d/dp P_p(A) = Σ_{e ∈ F} P_p(e ∈ E(G) is pivotal for A)` on
  `(0, 1)`;
* `russo_formula_holds : russo_formula` — `d/dp P_p(A) = E_p |pivotals A ∩ E(G)|` for an
  increasing local event `A`.

Source: L. Russo, *On the critical percolation probabilities*, Z. Wahrsch. verw. Gebiete 56
(1981) 229–237, §4, Lemma 3, eq. (4.2), p. 234: "If `A` is a positive event,
`d/dx μ_x(A) = ⟨n(A)⟩_{μ_x}`", where `n(A)(ω) = Σ_i χ_{δ_i A}(ω)` (eq. (4.1)) is the
number of critical (= pivotal) points of `ω` for `A`. Also Grimmett, *Percolation* (1999),
Thm. 2.25.

## Proof architecture

Russo's printed proof puts an independent parameter `x_i` on every site, observes `∂/∂x_i μ_x(A) =
μ_x(δ_i A)` for positive `A`, and sums over `i` on the diagonal.

1. (`Russo.setBernoulli_real_localCylinder`, `Russo.measureReal_eq_cylPoly`) An event `B`
   determined by a finite set `K` is the disjoint union of the `K`-cylinders `[S]_K`, `S ⊆ K`,
   `S ∈ B` (`DeterminedBy.eq_biUnion_localCylinder`), and under `setBer(u, q)` the cylinder
   `[S]_K` has probability `∏_{i ∈ K} weight u S i q`, an explicit polynomial (`Russo.cylPoly`).
2. (`Russo.hasDerivAt_cylPoly`) Product rule.
3. (`Russo.sum_dweight_eq_measureReal_pivotal`) For `e ∈ K`, pairing `S ↔ S ∪ {e}` turns the
   `e`-th term of the derivative into
   `Σ_{S ⊆ K \ {e}} (∏_{i ≠ e} weight) (1[S ∪ {e} ∈ A] - 1[S ∈ A])`,
   and for increasing `A` the bracket is the indicator that `e` is pivotal
   (`Russo.isPivotal_iff_of_notMem`); the pivotality event is determined by `K \ {e}`
   (`Russo.determinedBy_isPivotal`), so step 1 identifies the sum with `P(e pivotal)`.
4. On the neighbourhood `(0, 1)` of `p` the map `q ↦ P_{projIcc q}(A)` agrees with the
   polynomial, whence `russo_formula_sum_holds`; `russo_formula_holds` follows from Russo's
   (4.1): pivotal pairs lie in `F` (`Russo.mem_of_isPivotal`), so
   `E_p |pivotals A ∩ E(G)| = Σ_{e ∈ F} P_p(e ∈ E(G) pivotal)`.

Design notes: non-edges of `G` carry the degenerate Bernoulli factor of `setBer(E(G), p)`; the
weights `weight`/`dweight` record this (`0`/`1` and derivative `0` off `E(G)`), so no countability
or `ω ⊆ E(G)` reduction is needed.
-/

namespace Percolation.Literature

open MeasureTheory ProbabilityTheory LatticeModels unitInterval
open scoped ProbabilityTheory ENNReal

variable {ι : Type*}

namespace Russo

/-! #### Pivotality and finite dependence -/

/-- If `A` is determined by `K`, then whether `e` is pivotal for `A` is determined by
`K \ {e}` (Russo 1981, §4, proof of Lemma 3: "`δ_i A ∈ 𝒜_{Λ ∖ {i}}`").
[cite: RussoZW1981, §4 Lemma 3 (proof)] -/
theorem determinedBy_isPivotal {A : Set (Set ι)} {K : Finset ι} [DecidableEq ι]
    (hA : DeterminedBy A (↑K : Set ι)) (e : ι) :
    DeterminedBy {ω | IsPivotal A e ω} (↑(K.erase e) : Set ι) := by
  rw [determinedBy_iff] at hA ⊢
  intro ω ω' h
  have hi : ∀ i ∈ K, i ≠ e → (i ∈ ω ↔ i ∈ ω') := by
    intro i hiK hie
    have := Set.ext_iff.1 h i
    simp only [Set.mem_inter_iff, Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe,
      Set.mem_singleton_iff] at this
    tauto
  have h1 : insert e ω ∩ ↑K = insert e ω' ∩ ↑K := by
    ext i
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Finset.mem_coe]
    by_cases hie : i = e
    · simp [hie]
    · constructor
      · rintro ⟨hi', hiK⟩
        exact ⟨Or.inr (((hi i hiK hie).1 (hi'.resolve_left hie))), hiK⟩
      · rintro ⟨hi', hiK⟩
        exact ⟨Or.inr (((hi i hiK hie).2 (hi'.resolve_left hie))), hiK⟩
  have h2 : (ω \ {e}) ∩ ↑K = (ω' \ {e}) ∩ ↑K := by
    ext i
    simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_singleton_iff, Finset.mem_coe]
    by_cases hie : i = e
    · simp [hie]
    · constructor
      · rintro ⟨⟨hi', -⟩, hiK⟩
        exact ⟨⟨(hi i hiK hie).1 hi', hie⟩, hiK⟩
      · rintro ⟨⟨hi', -⟩, hiK⟩
        exact ⟨⟨(hi i hiK hie).2 hi', hie⟩, hiK⟩
  simp only [Set.mem_setOf_eq, IsPivotal]
  rw [hA _ _ h1, hA _ _ h2]

/-- A coordinate outside a determining set is never pivotal (so Russo's
`n(A) = Σ_{i ∈ Λ} χ_{δ_i A}`, eq. (4.1), counts all pivotal coordinates).
[cite: RussoZW1981, §4 (4.1)] -/
theorem mem_of_isPivotal {A : Set (Set ι)} {K : Finset ι}
    (hA : DeterminedBy A (↑K : Set ι)) {e : ι} {ω : Set ι} (he : IsPivotal A e ω) :
    e ∈ K := by
  by_contra heK
  rw [determinedBy_iff] at hA
  have h : insert e ω ∩ ↑K = (ω \ {e}) ∩ ↑K := by
    ext i
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_sdiff, Set.mem_singleton_iff,
      Finset.mem_coe]
    constructor
    · rintro ⟨rfl | hi, hiK⟩
      · exact absurd hiK heK
      · exact ⟨⟨hi, fun hie => heK (hie ▸ hiK)⟩, hiK⟩
    · rintro ⟨⟨hi, -⟩, hiK⟩
      exact ⟨Or.inr hi, hiK⟩
  have := hA _ _ h
  unfold IsPivotal at he
  rw [this] at he
  exact (xor_self _).mp he |>.elim

/-- For an increasing event `A` and `e ∉ S`, `e` is pivotal in `S` iff `S ∉ A` and
`insert e S ∈ A` (Russo 1981, §4, proof of Lemma 3: for positive `A`,
`A ∖ S_i A = E_i⁺ ∩ δ_i A`). [cite: RussoZW1981, §4 Lemma 3 (proof)] -/
theorem isPivotal_iff_of_notMem {A : Set (Set ι)} (hA : IsUpperSet A) {e : ι} {S : Set ι}
    (he : e ∉ S) : IsPivotal A e S ↔ insert e S ∈ A ∧ S ∉ A := by
  unfold IsPivotal
  rw [Set.sdiff_singleton_eq_self he]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨h1, h2⟩
    · exact absurd (hA (Set.subset_insert e S) h1) h2
  · rintro ⟨h1, h2⟩
    exact Or.inl ⟨h1, h2⟩

/-! #### Cylinder probabilities as polynomials -/

open Classical in
/-- The one-coordinate weight of the cylinder `[S]_K` at coordinate `i` under `setBer(u, q)`:
`q` or `1 - q` for coordinates in `u` according as `i ∈ S` or not, and `0` or `1` for
coordinates outside `u` (which are a.s. closed); the factors of Russo's product measure
`μ_x = ∏_i ν_{x_i}` on the diagonal. [cite: RussoZW1981, §4 Lemma 3 (proof)] -/
noncomputable def weight (u : Set ι) (S : Set ι) (i : ι) (q : ℝ) : ℝ :=
  if i ∈ S then (if i ∈ u then q else 0) else (if i ∈ u then 1 - q else 1)

open Classical in
/-- The `q`-derivative of `weight u S i q`: `±1` on coordinates of `u`, `0` elsewhere.
[folklore] -/
noncomputable def dweight (u : Set ι) (S : Set ι) (i : ι) : ℝ :=
  if i ∈ S then (if i ∈ u then 1 else 0) else (if i ∈ u then -1 else 0)

/-- `weight u S i` is affine with derivative `dweight u S i`. [folklore] -/
theorem hasDerivAt_weight (u S : Set ι) (i : ι) (q : ℝ) :
    HasDerivAt (weight u S i) (dweight u S i) q := by
  classical
  by_cases hS : i ∈ S <;> by_cases hu : i ∈ u
  · have h1 : weight u S i = fun q => q := by ext q; simp [weight, hS, hu]
    have h2 : dweight u S i = 1 := by simp [dweight, hS, hu]
    rw [h1, h2]; exact hasDerivAt_id' q
  · have h1 : weight u S i = fun _ => 0 := by ext q; simp [weight, hS, hu]
    have h2 : dweight u S i = 0 := by simp [dweight, hS, hu]
    rw [h1, h2]; exact hasDerivAt_const q (0 : ℝ)
  · have h1 : weight u S i = fun q => 1 - q := by ext q; simp [weight, hS, hu]
    have h2 : dweight u S i = -1 := by simp [dweight, hS, hu]
    rw [h1, h2]; exact HasDerivAt.const_sub (1 : ℝ) (hasDerivAt_id' q)
  · have h1 : weight u S i = fun _ => 1 := by ext q; simp [weight, hS, hu]
    have h2 : dweight u S i = 0 := by simp [dweight, hS, hu]
    rw [h1, h2]; exact hasDerivAt_const q (1 : ℝ)

/-- Off the coordinate `e`, the weights of `S` and `insert e S` agree. [folklore] -/
theorem weight_insert_of_ne (u S : Set ι) {e i : ι} (h : i ≠ e) (q : ℝ) :
    weight u (insert e S) i q = weight u S i q := by
  classical
  simp [weight, Set.mem_insert_iff, h]

/-- The probability of the cylinder `[S]_K` (`K` finite) under `setBer(u, p)` is the product of
the one-coordinate weights (finite-dimensional marginal of the product measure;
`Measure.infinitePi_pi`). (Grimmett 1999, §2.2; Russo 1981, §4, `μ_x = ∏ ν_{x_i}`.)
[cite: RussoZW1981, §4 Lemma 3 (proof)] -/
theorem setBernoulli_real_localCylinder (u : Set ι) (p : unitInterval) (K : Finset ι)
    (S : Set ι) :
    (setBer(u, p)).real (localCylinder (↑K) S) = ∏ i ∈ K, weight u S i p := by
  classical
  rw [measureReal_def, setBernoulli_apply']
  have hpre : (fun χ : ι → Prop => {i | χ i}) ⁻¹' localCylinder (↑K : Set ι) S
      = Set.pi (↑K) (fun i => {x : Prop | x ↔ i ∈ S}) := by
    ext χ; simp [localCylinder, Set.mem_pi]
  rw [hpre, Measure.infinitePi_pi _ (fun i _ => MeasurableSpace.measurableSet_top),
    ENNReal.toReal_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
    Measure.dirac_apply, weight]
  by_cases hS : i ∈ S <;> by_cases hu : i ∈ u <;>
    simp [hS, hu, Set.indicator, ENNReal.smul_def, ← ENNReal.coe_add]

open Classical in
/-- The polynomial `q ↦ Σ_{S ⊆ K, S ∈ B} ∏_{i ∈ K} weight u S i q`, which computes
`setBer(u, q)(B)` for an event `B` determined by the finite set `K` (Russo 1981, proof of
Prop. 1: such probabilities are "a continuous function of `x` (namely a polynomial)").
[cite: RussoZW1981, §4 Lemma 3 (proof)] -/
noncomputable def cylPoly (u : Set ι) (K : Finset ι) (B : Set (Set ι)) : ℝ → ℝ :=
  fun q => ∑ S ∈ K.powerset, if (↑S : Set ι) ∈ B then ∏ i ∈ K, weight u ↑S i q else 0

/-- Distinct subsets of `K` define disjoint `K`-cylinders. [folklore] -/
theorem disjoint_localCylinder {K S T : Finset ι} (hS : S ⊆ K) (hT : T ⊆ K) (hST : S ≠ T) :
    Disjoint (localCylinder (↑K : Set ι) ↑S) (localCylinder (↑K : Set ι) ↑T) := by
  rw [Set.disjoint_left]
  intro ω hωS hωT
  apply hST
  ext i
  constructor
  · intro hi
    exact Finset.mem_coe.1 ((hωT i (hS hi)).1 ((hωS i (hS hi)).2 (Finset.mem_coe.2 hi)))
  · intro hi
    exact Finset.mem_coe.1 ((hωS i (hT hi)).1 ((hωT i (hT hi)).2 (Finset.mem_coe.2 hi)))

/-- For an event `B` determined by the finite set `K`, `setBer(u, p)(B) = cylPoly u K B p`
(sum of the cylinder probabilities over the cylinders composing `B`).
[cite: RussoZW1981, §4 Lemma 3 (proof)] -/
theorem measureReal_eq_cylPoly {B : Set (Set ι)} {K : Finset ι}
    (hB : DeterminedBy B (↑K : Set ι)) (u : Set ι) (p : unitInterval) :
    (setBer(u, p)).real B = cylPoly u K B p := by
  classical
  conv_lhs => rw [hB.eq_biUnion_localCylinder]
  rw [measureReal_biUnion_finset]
  · simp only [cylPoly]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun S _ => ?_
    split_ifs
    · exact setBernoulli_real_localCylinder u p K ↑S
    · rfl
  · intro S hS T hT hST
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_powerset] at hS hT
    exact disjoint_localCylinder hS.1 hT.1 hST
  · intro S _
    exact measurableSet_localCylinder K.finite_toSet.countable _

open Classical in
/-- The derivative of `cylPoly`, computed by the product rule and with the two sums exchanged
(the one-variable form of Russo's `Σ_i ∂/∂x_i` on the diagonal).
[cite: RussoZW1981, §4 Lemma 3 (proof)] -/
theorem hasDerivAt_cylPoly [DecidableEq ι] (u : Set ι) (K : Finset ι) (B : Set (Set ι))
    (q : ℝ) :
    HasDerivAt (cylPoly u K B)
      (∑ e ∈ K, ∑ S ∈ K.powerset, if (↑S : Set ι) ∈ B then
        (∏ j ∈ K.erase e, weight u ↑S j q) * dweight u ↑S e else 0) q := by
  classical
  rw [Finset.sum_comm]
  unfold cylPoly
  refine HasDerivAt.fun_sum fun S _ => ?_
  split_ifs with hSB
  · have := HasDerivAt.fun_finsetProd (u := K) (x := q)
      (fun i _ => hasDerivAt_weight u (↑S : Set ι) i q)
    simpa [smul_eq_mul] using this
  · simpa using hasDerivAt_const q (0 : ℝ)

open Classical in
/-- The pairing `S ↔ insert e S`: for an increasing event `A` determined by `K` and `e ∈ K`,
the `e`-th partial derivative of `cylPoly` is the probability that `e ∈ u` is pivotal —
Russo's `∂/∂x_i μ_x(A) = μ_x(δ_i A)` (1981, §4, proof of Lemma 3), with the convention that
coordinates outside `u` (a.s. closed, weight independent of `q`) contribute `0`.
[cite: RussoZW1981, §4 Lemma 3 (proof)] -/
theorem sum_dweight_eq_measureReal_pivotal [DecidableEq ι] {A : Set (Set ι)}
    (hA : IsUpperSet A) {K : Finset ι} (hK : DeterminedBy A (↑K : Set ι)) (u : Set ι)
    (p : unitInterval) {e : ι} (he : e ∈ K) :
    (∑ S ∈ K.powerset, if (↑S : Set ι) ∈ A then
        (∏ j ∈ K.erase e, weight u ↑S j p) * dweight u ↑S e else 0) =
      (setBer(u, p)).real {ω | e ∈ u ∧ IsPivotal A e ω} := by
  classical
  by_cases heu : e ∈ u
  swap
  · have h0 : ∀ S : Finset ι, dweight u (↑S : Set ι) e = 0 := by
      intro S; unfold dweight; simp [heu]
    simp [h0, heu]
  have hev : {ω | e ∈ u ∧ IsPivotal A e ω} = {ω | IsPivotal A e ω} := by
    ext ω; simp [heu]
  rw [hev, measureReal_eq_cylPoly (determinedBy_isPivotal hK e) u p]
  simp only [cylPoly]
  have hpow : K.powerset = (K.erase e).powerset ∪ (K.erase e).powerset.image (insert e) := by
    rw [← Finset.powerset_insert, Finset.insert_erase he]
  have hdisj : Disjoint (K.erase e).powerset ((K.erase e).powerset.image (insert e)) := by
    rw [Finset.disjoint_left]
    intro S hS hS'
    obtain ⟨T, -, rfl⟩ := Finset.mem_image.1 hS'
    have := Finset.mem_powerset.1 hS (Finset.mem_insert_self e T)
    simp at this
  have hinj : Set.InjOn (insert e) (↑(K.erase e).powerset : Set (Finset ι)) := by
    intro S hS T hT hST
    have heS : e ∉ S := fun h => by simpa using Finset.mem_powerset.1 hS h
    have heT : e ∉ T := fun h => by simpa using Finset.mem_powerset.1 hT h
    rw [← Finset.erase_insert heS, ← Finset.erase_insert heT, hST]
  rw [hpow, Finset.sum_union hdisj, Finset.sum_image hinj, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun S hS => ?_
  have heS : e ∉ S := fun h => by simpa using Finset.mem_powerset.1 hS h
  have heS' : e ∉ (↑S : Set ι) := by simpa using heS
  have hdS : dweight u (↑S : Set ι) e = -1 := by simp [dweight, heS', heu]
  have hdiS : dweight u (↑(insert e S) : Set ι) e = 1 := by simp [dweight, heu]
  have hwi : ∏ j ∈ K.erase e, weight u (↑(insert e S) : Set ι) j p =
      ∏ j ∈ K.erase e, weight u (↑S : Set ι) j p := by
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [Finset.coe_insert]
    exact weight_insert_of_ne u _ (Finset.ne_of_mem_erase hj) _
  rw [hdS, hdiS, hwi, Set.mem_setOf_eq, isPivotal_iff_of_notMem hA heS', Finset.coe_insert]
  by_cases hSA : (↑S : Set ι) ∈ A
  · have hiA : insert e (↑S : Set ι) ∈ A := hA (Set.subset_insert e _) hSA
    simp [hSA, hiA]
  · by_cases hiA : insert e (↑S : Set ι) ∈ A
    · simp [hSA, hiA]
    · simp [hSA, hiA]

end Russo

/-! #### Conclusion -/

variable {V : Type*}

/-- Proof of `russo_formula_sum` (Russo, *Z. Wahrsch. verw. Gebiete* 56 (1981), §4,
Lemma 3, eq. (4.2), p. 234; Grimmett, *Percolation* (1999), Thm. 2.25). Proof: for `A`
determined by the finite set `F`, `P_q(A)` is the polynomial `cylPoly E(G) F A q` on `(0, 1)`
(sum over the `F`-cylinders composing `A`); differentiate by the product rule and pair the
cylinders `S ↔ S ∪ {e}` coordinate by coordinate, as in Russo's proof via `∂/∂x_i μ_x(A) =
μ_x(δ_i A)`. [cite: RussoZW1981, §4 Lemma 3 (4.2)] -/
theorem russo_formula_sum_holds : russo_formula_sum (V := V) := by
  intro G A hA F hF p hp
  classical
  have hpI : p ∈ Set.Icc (0 : ℝ) 1 := ⟨hp.1.le, hp.2.le⟩
  have heq : Russo.cylPoly G.edgeSet F A =ᶠ[nhds p]
      (fun q : ℝ => (bondPercolation G (Set.projIcc 0 1 zero_le_one q)).real A) := by
    filter_upwards [Ioo_mem_nhds hp.1 hp.2] with q hq
    rw [Set.projIcc_of_mem _ ⟨hq.1.le, hq.2.le⟩, bondPercolation]
    exact (Russo.measureReal_eq_cylPoly hF G.edgeSet ⟨q, hq.1.le, hq.2.le⟩).symm
  refine ((Russo.hasDerivAt_cylPoly G.edgeSet F A p).congr_deriv ?_).congr_of_eventuallyEq
    heq.symm
  rw [Set.projIcc_of_mem _ hpI]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [bondPercolation]
  exact Russo.sum_dweight_eq_measureReal_pivotal hA hF G.edgeSet ⟨p, hpI⟩ he

/-- Proof of `russo_formula` (Russo, *Z. Wahrsch. verw. Gebiete* 56 (1981), §4, Lemma 3,
eq. (4.2), p. 234: `d/dx μ_x(A) = ⟨n(A)⟩_{μ_x}` for a positive event `A`, `n(A)` the number of
critical (pivotal) points; Grimmett, *Percolation* (1999), Thm. 2.25). Obtained from the sum
form `russo_formula_sum_holds` and Russo's (4.1) `n(A) = Σ_i χ_{δ_i A}`: pivotal edges lie
in any finite set `F` determining `A`, so
`E_p |pivotals ∩ E(G)| = Σ_{e ∈ F} P_p(e ∈ E(G) pivotal)`.
[cite: RussoZW1981, §4 Lemma 3 (4.2)] -/
theorem russo_formula_holds : russo_formula (V := V) := by
  intro G A hA hAl p hp
  classical
  obtain ⟨F, hF⟩ := hAl
  have hsum := russo_formula_sum_holds G hA F hF p hp
  refine hsum.congr_deriv ?_
  -- the events `{e ∈ E(G) pivotal}` are measurable
  have hmeas : ∀ e ∈ F,
      MeasurableSet {ω : BondConfig V | e ∈ G.edgeSet ∧ IsPivotal A e ω} := by
    intro e _
    by_cases heE : e ∈ G.edgeSet
    · have : {ω : BondConfig V | e ∈ G.edgeSet ∧ IsPivotal A e ω} =
          {ω | IsPivotal A e ω} := by
        ext ω; simp [heE]
      rw [this]
      exact (Russo.determinedBy_isPivotal hF e).measurableSet_of_finset
    · have : {ω : BondConfig V | e ∈ G.edgeSet ∧ IsPivotal A e ω} = ∅ := by
        ext ω; simp [heE]
      rw [this]; exact MeasurableSet.empty
  -- the pivotal count is the sum of the indicators
  have hcount : ∀ ω : BondConfig V, ((pivotals A ω ∩ G.edgeSet).encard.toNat : ℝ) =
      ∑ e ∈ F, {ω : BondConfig V | e ∈ G.edgeSet ∧ IsPivotal A e ω}.indicator 1 ω := by
    intro ω
    have hset : pivotals A ω ∩ G.edgeSet =
        ↑(F.filter fun e => e ∈ G.edgeSet ∧ IsPivotal A e ω) := by
      ext e
      simp only [Set.mem_inter_iff, mem_pivotals, Finset.coe_filter, Set.mem_setOf_eq]
      constructor
      · rintro ⟨hpiv, heE⟩
        exact ⟨Russo.mem_of_isPivotal hF hpiv, heE, hpiv⟩
      · rintro ⟨-, heE, hpiv⟩
        exact ⟨hpiv, heE⟩
    rw [hset, Set.encard_coe_eq_coe_finsetCard, ENat.toNat_coe, Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [Set.indicator, Set.mem_setOf_eq, Pi.one_apply]
  simp_rw [hcount]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun e he => ?_
    exact (integral_indicator_one (hmeas e he)).symm
  · intro e he
    exact (integrable_const (1 : ℝ)).indicator (hmeas e he)

end Percolation.Literature
