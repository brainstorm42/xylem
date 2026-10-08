import Percolation.Literature.TwoSetConditionalAssociation
import Percolation.Util.Linter

/-!
# The two-SET exchange inequality (event form of van den Berg–Häggström–Kahn 2006, Thm. 1.5 / Thm. 2.1 at `q = 1`, with the vertices `s, t` replaced by vertex sets `S, T`)

The block version of: bond percolation with arbitrary edge probabilities on a finite vertex type (`μ
= prodBernoulli w`), two sets of vertices `S, T`, `D = {S ↮ T} = {ω | ∀ s ∈ S, ∀ t ∈ T, s ↮ t}`, and
the unions of open edge clusters `C_S ω = ⋃_{s ∈ S} C_s ω`, `C_T ω = ⋃_{t ∈ T} C_t ω` (BHK p. 9:
"`C_S`, the set of edges belonging to open paths starting at vertices of `S`"). An event is of TYPE
`(+)` if it is closed under enlarging `C_S` and shrinking `C_T`, of TYPE `(−)` if it is closed under
shrinking `C_S` and enlarging `C_T`. From the set form of BHK's Theorem 1.5 proved in
`TwoSetConditionalAssociation.lean` (`BHK2006_twoSetConditionalAssociation` =
[VandenbergHaggstromKahn2005, Thm. 2.1 (p. 9)] at `q = 1`, i.e. Thm. 1.5 with Remark 1 after Thm.
1.2 (p. 5): "we could replace `s` …, and `t` in Theorems (1.4) and (1.5), by sets of vertices") one
gets, word for word as:

* `TwoSetExchange.setFourProduct` — the functional four-product form;
* `setTwoClusterExchange` — for `A₁, A₂` of type `(+)` and `B₁, B₂` of type `(−)`,
  `μ(D ∩ A₁ ∩ B₁) · μ(D ∩ A₂ ∩ B₂) ≤ μ(D ∩ A₁ ∩ A₂) · μ(D ∩ B₁ ∩ B₂)`;

No definition is introduced; everything is proved.

## References

* J. van den Berg, O. Häggström, J. Kahn, *Some conditional correlation inequalities for
  percolation and related processes*, Random Structures Algorithms 29 (2006) 417–435
  (arXiv:math/0408176), Thm. 1.5 (p. 7), Remark 1 after Thm. 1.2 (p. 5), Thm. 2.1 (p. 9).
  [VandenbergHaggstromKahn2005]
-/

noncomputable section

open MeasureTheory Set
open Percolation.Literature.LatticeModels (prodBernoulli)

namespace Percolation.Literature

variable {V : Type*}

namespace TwoSetExchange

/-- **Functional four-product form of BHK Thm. 1.5 with vertex sets.** For `F₁, F₂ ≥ 0` increasing
in `C_S` and decreasing in `C_T`, and `G₁, G₂ ≥ 0` decreasing in `C_S` and increasing in `C_T`:
`(∫_D F₁G₁)(∫_D F₂G₂) ≤ (∫_D F₁F₂)(∫_D G₁G₂)`, `D = {S ↮ T}`.
[cite: VandenbergHaggstromKahn2005, Thm. 2.1 (p. 9) at q = 1 — corollary, derived in this file] -/
theorem setFourProduct [Fintype V] (w : Sym2 V → unitInterval) (S T : Set V)
    (F₁ F₂ G₁ G₂ : Set (Sym2 V) → Set (Sym2 V) → ℝ)
    (hF₁m : ∀ E, Monotone fun C => F₁ C E) (hF₁a : ∀ C, Antitone fun E => F₁ C E)
    (hF₂m : ∀ E, Monotone fun C => F₂ C E) (hF₂a : ∀ C, Antitone fun E => F₂ C E)
    (hG₁a : ∀ E, Antitone fun C => G₁ C E) (hG₁m : ∀ C, Monotone fun E => G₁ C E)
    (hG₂a : ∀ E, Antitone fun C => G₂ C E) (hG₂m : ∀ C, Monotone fun E => G₂ C E)
    (hF₁ : ∀ C E, 0 ≤ F₁ C E) (hF₂ : ∀ C E, 0 ≤ F₂ C E) (hG₁ : ∀ C E, 0 ≤ G₁ C E)
    (hG₂ : ∀ C E, 0 ≤ G₂ C E) :
    (∫ ω in {ω : BondConfig V | ∀ s ∈ S, ∀ t ∈ T, ¬ (openGraph ω).Reachable s t},
        F₁ (⋃ s ∈ S, openEdgeCluster ω s) (⋃ t ∈ T, openEdgeCluster ω t) *
          G₁ (⋃ s ∈ S, openEdgeCluster ω s) (⋃ t ∈ T, openEdgeCluster ω t) ∂(prodBernoulli w)) *
      (∫ ω in {ω : BondConfig V | ∀ s ∈ S, ∀ t ∈ T, ¬ (openGraph ω).Reachable s t},
        F₂ (⋃ s ∈ S, openEdgeCluster ω s) (⋃ t ∈ T, openEdgeCluster ω t) *
          G₂ (⋃ s ∈ S, openEdgeCluster ω s) (⋃ t ∈ T, openEdgeCluster ω t) ∂(prodBernoulli w)) ≤
    (∫ ω in {ω : BondConfig V | ∀ s ∈ S, ∀ t ∈ T, ¬ (openGraph ω).Reachable s t},
        F₁ (⋃ s ∈ S, openEdgeCluster ω s) (⋃ t ∈ T, openEdgeCluster ω t) *
          F₂ (⋃ s ∈ S, openEdgeCluster ω s) (⋃ t ∈ T, openEdgeCluster ω t) ∂(prodBernoulli w)) *
      (∫ ω in {ω : BondConfig V | ∀ s ∈ S, ∀ t ∈ T, ¬ (openGraph ω).Reachable s t},
        G₁ (⋃ s ∈ S, openEdgeCluster ω s) (⋃ t ∈ T, openEdgeCluster ω t) *
          G₂ (⋃ s ∈ S, openEdgeCluster ω s) (⋃ t ∈ T, openEdgeCluster ω t) ∂(prodBernoulli w)) := by
  have hBHK := BHK2006_twoSetConditionalAssociation w S T
  -- (a) F₁, F₂ same type
  have key_a := hBHK F₁ F₂ hF₁m hF₁a hF₂m hF₂a
  -- (b) -G₁, -G₂ same type
  have key_b := hBHK (fun C E => -G₁ C E) (fun C E => -G₂ C E)
    (fun E _ _ h => neg_le_neg (hG₁a E h)) (fun C _ _ h => neg_le_neg (hG₁m C h))
    (fun E _ _ h => neg_le_neg (hG₂a E h)) (fun C _ _ h => neg_le_neg (hG₂m C h))
  -- (c) F₁, -G₁ ; (d) F₂, -G₂
  have key_c := hBHK F₁ (fun C E => -G₁ C E) hF₁m hF₁a
    (fun E _ _ h => neg_le_neg (hG₁a E h)) (fun C _ _ h => neg_le_neg (hG₁m C h))
  have key_d := hBHK F₂ (fun C E => -G₂ C E) hF₂m hF₂a
    (fun E _ _ h => neg_le_neg (hG₂a E h)) (fun C _ _ h => neg_le_neg (hG₂m C h))
  simp only [integral_neg, mul_neg, neg_mul, neg_neg, neg_le_neg_iff] at key_b key_c key_d
  set μ := prodBernoulli w with hμ
  set D := {ω : BondConfig V | ∀ s ∈ S, ∀ t ∈ T, ¬ (openGraph ω).Reachable s t} with hD
  have hDm : MeasurableSet D := MeasurableSet.of_discrete
  set m := μ.real D
  set a1 := ∫ ω in D, F₁ (⋃ s ∈ S, openEdgeCluster ω s) (⋃ t ∈ T, openEdgeCluster ω t) ∂μ
  set a2 := ∫ ω in D, F₂ (⋃ s ∈ S, openEdgeCluster ω s) (⋃ t ∈ T, openEdgeCluster ω t) ∂μ
  set b1 := ∫ ω in D, G₁ (⋃ s ∈ S, openEdgeCluster ω s) (⋃ t ∈ T, openEdgeCluster ω t) ∂μ
  set b2 := ∫ ω in D, G₂ (⋃ s ∈ S, openEdgeCluster ω s) (⋃ t ∈ T, openEdgeCluster ω t) ∂μ
  set L1 := ∫ ω in D, F₁ (⋃ s ∈ S, openEdgeCluster ω s) (⋃ t ∈ T, openEdgeCluster ω t) *
    G₁ (⋃ s ∈ S, openEdgeCluster ω s) (⋃ t ∈ T, openEdgeCluster ω t) ∂μ
  set L2 := ∫ ω in D, F₂ (⋃ s ∈ S, openEdgeCluster ω s) (⋃ t ∈ T, openEdgeCluster ω t) *
    G₂ (⋃ s ∈ S, openEdgeCluster ω s) (⋃ t ∈ T, openEdgeCluster ω t) ∂μ
  set R1 := ∫ ω in D, F₁ (⋃ s ∈ S, openEdgeCluster ω s) (⋃ t ∈ T, openEdgeCluster ω t) *
    F₂ (⋃ s ∈ S, openEdgeCluster ω s) (⋃ t ∈ T, openEdgeCluster ω t) ∂μ
  set R2 := ∫ ω in D, G₁ (⋃ s ∈ S, openEdgeCluster ω s) (⋃ t ∈ T, openEdgeCluster ω t) *
    G₂ (⋃ s ∈ S, openEdgeCluster ω s) (⋃ t ∈ T, openEdgeCluster ω t) ∂μ
  have hm0 : 0 ≤ m := measureReal_nonneg
  have ha1 : 0 ≤ a1 := setIntegral_nonneg hDm fun ω _ => hF₁ _ _
  have ha2 : 0 ≤ a2 := setIntegral_nonneg hDm fun ω _ => hF₂ _ _
  have hb1 : 0 ≤ b1 := setIntegral_nonneg hDm fun ω _ => hG₁ _ _
  have hb2 : 0 ≤ b2 := setIntegral_nonneg hDm fun ω _ => hG₂ _ _
  have hL1 : 0 ≤ L1 := setIntegral_nonneg hDm fun ω _ => mul_nonneg (hF₁ _ _) (hG₁ _ _)
  have hL2 : 0 ≤ L2 := setIntegral_nonneg hDm fun ω _ => mul_nonneg (hF₂ _ _) (hG₂ _ _)
  have hR1 : 0 ≤ R1 := setIntegral_nonneg hDm fun ω _ => mul_nonneg (hF₁ _ _) (hF₂ _ _)
  have hR2 : 0 ≤ R2 := setIntegral_nonneg hDm fun ω _ => mul_nonneg (hG₁ _ _) (hG₂ _ _)
  rcases hm0.eq_or_lt with hm | hm
  · -- `μ(D) = 0`: every integral over `D` vanishes
    have hD0 : μ D = 0 := (measureReal_eq_zero_iff (measure_ne_top μ D)).1 hm.symm
    have hL10 : L1 = 0 := setIntegral_measure_zero _ hD0
    rw [hL10, zero_mul]
    exact mul_nonneg hR1 hR2
  · have h1 : m * L1 * (m * L2) ≤ a1 * b1 * (a2 * b2) :=
      mul_le_mul key_c key_d (mul_nonneg hm0 hL2) (mul_nonneg ha1 hb1)
    have h2 : a1 * a2 * (b1 * b2) ≤ m * R1 * (m * R2) :=
      mul_le_mul key_a key_b (mul_nonneg hb1 hb2) (mul_nonneg hm0 hR1)
    have h3 : m * m * (L1 * L2) ≤ m * m * (R1 * R2) :=
      calc m * m * (L1 * L2) = m * L1 * (m * L2) := by ring
        _ ≤ a1 * b1 * (a2 * b2) := h1
        _ = a1 * a2 * (b1 * b2) := by ring
        _ ≤ m * R1 * (m * R2) := h2
        _ = m * m * (R1 * R2) := by ring
    exact le_of_mul_le_mul_left h3 (mul_pos hm hm)

end TwoSetExchange

open TwoSetExchange in
/-- **The two-set exchange inequality (event form of BHK 2006 Thm. 1.5 / Thm. 2.1 at `q = 1`, with
 vertex sets).** Let `S, T` be sets of vertices, `D = {S ↮ T}`, `C_S ω = ⋃_{s ∈ S} C_s ω`, `C_T ω =
 ⋃_{t ∈ T} C_t ω`; let `A₁, A₂` be events closed under (enlarging `C_S`, shrinking `C_T`) and `B₁,
 B₂` events closed under (shrinking `C_S`, enlarging `C_T`). Then `μ(D ∩ (A₁ ∩ B₁)) · μ(D ∩ (A₂ ∩
 B₂)) ≤ μ(D ∩ (A₁ ∩ A₂)) · μ(D ∩ (B₁ ∩ B₂))`. [cite: VandenbergHaggstromKahn2005, Thm. 2.1 (p. 9) at
 q = 1 — corollary, derived in this file]
-/
theorem setTwoClusterExchange [Fintype V] (w : Sym2 V → unitInterval) (S T : Set V)
    {A₁ A₂ B₁ B₂ : Set (BondConfig V)}
    (hA₁ : ∀ ⦃ω ω' : BondConfig V⦄, (⋃ s ∈ S, openEdgeCluster ω s) ⊆ (⋃ s ∈ S, openEdgeCluster ω' s) →
      (⋃ t ∈ T, openEdgeCluster ω' t) ⊆ (⋃ t ∈ T, openEdgeCluster ω t) → ω ∈ A₁ → ω' ∈ A₁)
    (hA₂ : ∀ ⦃ω ω' : BondConfig V⦄, (⋃ s ∈ S, openEdgeCluster ω s) ⊆ (⋃ s ∈ S, openEdgeCluster ω' s) →
      (⋃ t ∈ T, openEdgeCluster ω' t) ⊆ (⋃ t ∈ T, openEdgeCluster ω t) → ω ∈ A₂ → ω' ∈ A₂)
    (hB₁ : ∀ ⦃ω ω' : BondConfig V⦄, (⋃ s ∈ S, openEdgeCluster ω' s) ⊆ (⋃ s ∈ S, openEdgeCluster ω s) →
      (⋃ t ∈ T, openEdgeCluster ω t) ⊆ (⋃ t ∈ T, openEdgeCluster ω' t) → ω ∈ B₁ → ω' ∈ B₁)
    (hB₂ : ∀ ⦃ω ω' : BondConfig V⦄, (⋃ s ∈ S, openEdgeCluster ω' s) ⊆ (⋃ s ∈ S, openEdgeCluster ω s) →
      (⋃ t ∈ T, openEdgeCluster ω t) ⊆ (⋃ t ∈ T, openEdgeCluster ω' t) → ω ∈ B₂ → ω' ∈ B₂) :
    (prodBernoulli w).real ({ω : BondConfig V | ∀ s ∈ S, ∀ t ∈ T, ¬ (openGraph ω).Reachable s t} ∩
        (A₁ ∩ B₁)) *
      (prodBernoulli w).real ({ω : BondConfig V | ∀ s ∈ S, ∀ t ∈ T, ¬ (openGraph ω).Reachable s t} ∩
        (A₂ ∩ B₂)) ≤
    (prodBernoulli w).real ({ω : BondConfig V | ∀ s ∈ S, ∀ t ∈ T, ¬ (openGraph ω).Reachable s t} ∩
        (A₁ ∩ A₂)) *
      (prodBernoulli w).real ({ω : BondConfig V | ∀ s ∈ S, ∀ t ∈ T, ¬ (openGraph ω).Reachable s t} ∩
        (B₁ ∩ B₂)) := by
  classical
  -- witness functions: `F_A(C,E) = 1{∃ ω ∈ A, C_S ω ⊆ C, E ⊆ C_T ω}`, `G_B(C,E) = 1{∃ ω ∈ B, C ⊆ C_S ω, C_T ω ⊆ E}`
  let FA : Set (BondConfig V) → Set (Sym2 V) → Set (Sym2 V) → ℝ := fun A C E =>
    if ∃ ω ∈ A, (⋃ s ∈ S, openEdgeCluster ω s) ⊆ C ∧ E ⊆ (⋃ t ∈ T, openEdgeCluster ω t) then 1
    else 0
  let GB : Set (BondConfig V) → Set (Sym2 V) → Set (Sym2 V) → ℝ := fun B C E =>
    if ∃ ω ∈ B, C ⊆ (⋃ s ∈ S, openEdgeCluster ω s) ∧ (⋃ t ∈ T, openEdgeCluster ω t) ⊆ E then 1
    else 0
  have FA_mono : ∀ A E, Monotone fun C => FA A C E := by
    intro A E C C' hCC'
    simp only [FA]
    by_cases h : ∃ ω ∈ A, (⋃ s ∈ S, openEdgeCluster ω s) ⊆ C ∧ E ⊆ (⋃ t ∈ T, openEdgeCluster ω t)
    · obtain ⟨ω, hω, h1, h2⟩ := h
      rw [if_pos ⟨ω, hω, h1, h2⟩, if_pos ⟨ω, hω, h1.trans hCC', h2⟩]
    · rw [if_neg h]; split_ifs <;> norm_num
  have FA_anti : ∀ A C, Antitone fun E => FA A C E := by
    intro A C E E' hEE'
    simp only [FA]
    by_cases h : ∃ ω ∈ A, (⋃ s ∈ S, openEdgeCluster ω s) ⊆ C ∧ E' ⊆ (⋃ t ∈ T, openEdgeCluster ω t)
    · obtain ⟨ω, hω, h1, h2⟩ := h
      rw [if_pos ⟨ω, hω, h1, h2⟩, if_pos ⟨ω, hω, h1, hEE'.trans h2⟩]
    · rw [if_neg h]; split_ifs <;> norm_num
  have GB_anti : ∀ B E, Antitone fun C => GB B C E := by
    intro B E C C' hCC'
    simp only [GB]
    by_cases h : ∃ ω ∈ B, C' ⊆ (⋃ s ∈ S, openEdgeCluster ω s) ∧ (⋃ t ∈ T, openEdgeCluster ω t) ⊆ E
    · obtain ⟨ω, hω, h1, h2⟩ := h
      rw [if_pos ⟨ω, hω, h1, h2⟩, if_pos ⟨ω, hω, hCC'.trans h1, h2⟩]
    · rw [if_neg h]; split_ifs <;> norm_num
  have GB_mono : ∀ B C, Monotone fun E => GB B C E := by
    intro B C E E' hEE'
    simp only [GB]
    by_cases h : ∃ ω ∈ B, C ⊆ (⋃ s ∈ S, openEdgeCluster ω s) ∧ (⋃ t ∈ T, openEdgeCluster ω t) ⊆ E
    · obtain ⟨ω, hω, h1, h2⟩ := h
      rw [if_pos ⟨ω, hω, h1, h2⟩, if_pos ⟨ω, hω, h1, h2.trans hEE'⟩]
    · rw [if_neg h]; split_ifs <;> norm_num
  have FA_nn : ∀ A C E, 0 ≤ FA A C E := by
    intro A C E; simp only [FA]; split_ifs <;> norm_num
  have GB_nn : ∀ B C E, 0 ≤ GB B C E := by
    intro B C E; simp only [GB]; split_ifs <;> norm_num
  -- evaluation on a configuration
  have FA_eval : ∀ {A : Set (BondConfig V)},
      (∀ ⦃ω ω' : BondConfig V⦄, (⋃ s ∈ S, openEdgeCluster ω s) ⊆ (⋃ s ∈ S, openEdgeCluster ω' s) →
        (⋃ t ∈ T, openEdgeCluster ω' t) ⊆ (⋃ t ∈ T, openEdgeCluster ω t) → ω ∈ A → ω' ∈ A) →
      ∀ ω', FA A (⋃ s ∈ S, openEdgeCluster ω' s) (⋃ t ∈ T, openEdgeCluster ω' t) =
        A.indicator 1 ω' := by
    intro A hA ω'
    simp only [FA]
    by_cases hω' : ω' ∈ A
    · rw [if_pos ⟨ω', hω', subset_rfl, subset_rfl⟩, indicator_of_mem hω', Pi.one_apply]
    · rw [indicator_of_notMem hω', if_neg]
      rintro ⟨ω, hω, h1, h2⟩
      exact hω' (hA h1 h2 hω)
  have GB_eval : ∀ {B : Set (BondConfig V)},
      (∀ ⦃ω ω' : BondConfig V⦄, (⋃ s ∈ S, openEdgeCluster ω' s) ⊆ (⋃ s ∈ S, openEdgeCluster ω s) →
        (⋃ t ∈ T, openEdgeCluster ω t) ⊆ (⋃ t ∈ T, openEdgeCluster ω' t) → ω ∈ B → ω' ∈ B) →
      ∀ ω', GB B (⋃ s ∈ S, openEdgeCluster ω' s) (⋃ t ∈ T, openEdgeCluster ω' t) =
        B.indicator 1 ω' := by
    intro B hB ω'
    simp only [GB]
    by_cases hω' : ω' ∈ B
    · rw [if_pos ⟨ω', hω', subset_rfl, subset_rfl⟩, indicator_of_mem hω', Pi.one_apply]
    · rw [indicator_of_notMem hω', if_neg]
      rintro ⟨ω, hω, h1, h2⟩
      exact hω' (hB h1 h2 hω)
  have key := setFourProduct w S T (FA A₁) (FA A₂) (GB B₁) (GB B₂)
    (FA_mono A₁) (FA_anti A₁) (FA_mono A₂) (FA_anti A₂)
    (GB_anti B₁) (GB_mono B₁) (GB_anti B₂) (GB_mono B₂)
    (FA_nn A₁) (FA_nn A₂) (GB_nn B₁) (GB_nn B₂)
  simp only [FA_eval hA₁, FA_eval hA₂, GB_eval hB₁, GB_eval hB₂,
    TripodExchange.setIntegral_indicator_mul_indicator_eq] at key
  exact key

/-! ### Single-source generators and one-sided guards

BHK's reduction of vertex sets to vertices (Remark 1 after Thm. 1.2, p. 5: "identify the vertices of
`X` … Similarly, we could replace `s` …, and `t` in Theorems (1.4) and (1.5), by sets of vertices";
Thm. 2.1, p. 9) conditions on `{S ↮ T}` and types events by the UNIONS `C_S`, `C_T`. For a single
source `s₀ ∈ S` the cluster `C_{s₀}` is itself an increasing function of `C_S`: an open path from
`s₀` has all its edges in `C_{s₀} ⊆ C_S` (`edge_mem_openEdgeCluster_of_walk`), so if `C_S(ω) ⊆
C_S(ω') (⊆ ω')` the path is open in `ω'` (`openEdgeCluster_mono_of_biUnion`). Only ONE-sided guards
are covered: every extra separation must involve a vertex of `S` and a vertex of `T` (a guard `{u ↮
u'}` between two vertices on the same side, e.g. conditioning on `s, t, u` pairwise separated, is
not of this form, and the corresponding association statement fails in general).
-/

namespace TwoSetExchange

/-- Every edge of an open walk starting at `s` belongs to `C_s` ("the set of all edges which are
in open paths starting at `s`", BHK p. 3). [cite: VandenbergHaggstromKahn2005, §1 p. 3 (definition of C_s)] -/
theorem edge_mem_openEdgeCluster_of_walk {ω : BondConfig V} {s v : V}
    (p : (openGraph ω).Walk s v) : ∀ e ∈ p.edges, e ∈ openEdgeCluster ω s := by
  classical
  refine Sym2.ind (fun a b hab => ?_)
  have hadj : (openGraph ω).Adj a b := by
    simpa using p.edges_subset_edgeSet hab
  have hω := (openGraph_adj ω a b).1 hadj
  refine (mem_openEdgeCluster_iff ω s _).2 ⟨hω.1, ?_, fun x hx => ?_⟩
  · rw [Sym2.mk_isDiag_iff]
    exact hω.2
  · rcases Sym2.mem_iff.1 hx with rfl | rfl
    · exact (p.takeUntil _ (p.fst_mem_support_of_mem_edges hab)).reachable
    · exact (p.takeUntil _ (p.snd_mem_support_of_mem_edges hab)).reachable

/-- If every edge of `C_s(ω)` is open in `ω'` then `C_s(ω) ⊆ C_s(ω')`: an open path from `s` in
`ω` has all its edges in `C_s(ω)`, hence is open in `ω'`. [folklore] -/
theorem openEdgeCluster_subset_of_subset {ω ω' : BondConfig V} {s : V}
    (h : openEdgeCluster ω s ⊆ ω') : openEdgeCluster ω s ⊆ openEdgeCluster ω' s := by
  intro e he
  obtain ⟨-, hdiag, hreach⟩ := (mem_openEdgeCluster_iff ω s e).1 he
  refine (mem_openEdgeCluster_iff ω' s e).2 ⟨h he, hdiag, fun x hx => ?_⟩
  obtain ⟨p⟩ := hreach x hx
  have hp : ∀ e' ∈ p.edges, e' ∈ (openGraph ω').edgeSet := fun e' he' => by
    have h1 : e' ∈ openEdgeCluster ω s := edge_mem_openEdgeCluster_of_walk p e' he'
    have h2 := ((mem_openEdgeCluster_iff ω s e').1 h1).2.1
    change e' ∈ (SimpleGraph.fromEdgeSet ω').edgeSet
    rw [SimpleGraph.edgeSet_fromEdgeSet]
    exact ⟨h h1, h2⟩
  exact ⟨p.transfer (openGraph ω') hp⟩

/-- **A single cluster is increasing in the union**: for `s₀ ∈ S`,
`C_S(ω) ⊆ C_S(ω') → C_{s₀}(ω) ⊆ C_{s₀}(ω')` (`C_S = ⋃_{s ∈ S} C_s`).  This is the observation behind
BHK's reduction of sets to single vertices. [cite: VandenbergHaggstromKahn2005, Remark 1 after Thm. 1.2 (p. 5)] -/
theorem openEdgeCluster_mono_of_biUnion {S : Set V} {s₀ : V} (hs₀ : s₀ ∈ S) {ω ω' : BondConfig V}
    (h : (⋃ s ∈ S, openEdgeCluster ω s) ⊆ (⋃ s ∈ S, openEdgeCluster ω' s)) :
    openEdgeCluster ω s₀ ⊆ openEdgeCluster ω' s₀ := by
  refine openEdgeCluster_subset_of_subset fun e he => ?_
  obtain ⟨x, -, hex⟩ := Set.mem_iUnion₂.1 (h (Set.mem_biUnion hs₀ he))
  exact openEdgeCluster_subset ω' x hex

/-- For `s₀ ∈ S`, `{s₀ ↔ v}` is of type `(+)` for `(C_S, C_T)`. [folklore] -/
theorem typePlus_openConn_of_mem (S T : Set V) {s₀ : V} (hs₀ : s₀ ∈ S) (v : V)
    ⦃ω ω' : BondConfig V⦄
    (hs : (⋃ s ∈ S, openEdgeCluster ω s) ⊆ (⋃ s ∈ S, openEdgeCluster ω' s))
    (_ht : (⋃ t ∈ T, openEdgeCluster ω' t) ⊆ (⋃ t ∈ T, openEdgeCluster ω t))
    (h : ω ∈ (openConn s₀ v : Set (BondConfig V))) : ω' ∈ (openConn s₀ v : Set (BondConfig V)) := by
  have hmono := openEdgeCluster_mono_of_biUnion hs₀ hs
  change (openGraph ω').Reachable s₀ v
  rw [reachable_iff_exists_mem_openEdgeCluster]
  rcases (reachable_iff_exists_mem_openEdgeCluster ω s₀ v).1 h with h1 | ⟨e, he, hve⟩
  · exact Or.inl h1
  · exact Or.inr ⟨e, hmono he, hve⟩

/-- For `s₀ ∈ S`, `{s₀ ↮ v}` is of type `(−)` for `(C_S, C_T)`. [folklore] -/
theorem typeMinus_not_openConn_of_mem (S T : Set V) {s₀ : V} (hs₀ : s₀ ∈ S) (v : V)
    ⦃ω ω' : BondConfig V⦄
    (hs : (⋃ s ∈ S, openEdgeCluster ω' s) ⊆ (⋃ s ∈ S, openEdgeCluster ω s))
    (_ht : (⋃ t ∈ T, openEdgeCluster ω t) ⊆ (⋃ t ∈ T, openEdgeCluster ω' t))
    (h : ω ∈ (openConn s₀ v : Set (BondConfig V))ᶜ) : ω' ∈ (openConn s₀ v : Set (BondConfig V))ᶜ := by
  have hmono := openEdgeCluster_mono_of_biUnion hs₀ hs
  intro h'
  apply h
  change (openGraph ω).Reachable s₀ v
  rw [reachable_iff_exists_mem_openEdgeCluster]
  rcases (reachable_iff_exists_mem_openEdgeCluster ω' s₀ v).1 h' with h1 | ⟨e, he, hve⟩
  · exact Or.inl h1
  · exact Or.inr ⟨e, hmono he, hve⟩

end TwoSetExchange

end Percolation.Literature

end
