import Percolation.Literature.GladkovZiminKernel
import Percolation.Util.Linter

/-!
# Conditional expectations along a decision tree and the decision-tree Harris–Kleitman inequality for REAL increasing functions

Finitary weighted calculus of `DecisionTreeWeighted.lean` / `GladkovZiminKernel.lean`: configurations `K ⊆ D`, weights
`wtW D p K` (`p i ∈ [0,1]`), expectation `ED D p φ`; a self-determined revealed-set map `Fm` (e.g. `revealed T` for a
decision tree `T`) and the splice `K →_{Fm K} K₂` (`K` on `Fm K`, `K₂` elsewhere).

* `cE D p Fm φ K = Σ_{K₂ ⊆ D} wtW K₂ · φ (K →_{Fm K} K₂)` — the conditional expectation of `φ` given the revealed
  coordinates ("resample outside the revealed set"; `condSumW` of this library is the case `φ = 1_B`);
* `ED_cE` (tower: `E[cE φ] = E[φ]`, by Gladkov's swap Lemma 3.1 = `sum_pair_reindexW`), `cE_mul_of_local` (pull out an
  `Fm`-determined factor), `cE_local`, `ED_mul_cE_comm` (`E[φ · cE ψ] = E[cE φ · ψ]`), linearity;
* `sum_mul_nonneg_of_upperSet` — LAYER-CAKE EXTENSION: a linear functional `Σ_K a_K f(K)` nonnegative on indicators of
  up-sets is nonnegative on every monotone `f ≥ 0` (induction on the support);
* **`ED_mul_PrW_le_ED_mul_cE_ind`**, **`treeHarris_real`** — Gladkov's decision-tree Harris–Kleitman inequality
  [Gladkov2024, Thm. 3.2] ( `PrW_mul_PrW_le_Pr2W_treeHK`, for two increasing EVENTS) extended to a real monotone
  `f ≥ 0` and an increasing event `Y`: `E[f]·P(Y) ≤ E[f · E[1_Y | ℱ_T]] = E[E[f | ℱ_T] · 1_Y]`, i.e.
  `Cov(E[f | ℱ_T], 1_Y) ≥ 0` (the martingale form of Harris' inequality
  stopped along the tree).
-/

noncomputable section

namespace Percolation.Continuity

namespace TreeHarris

open Finset Percolation.Literature Percolation.Literature.DecisionTree

variable {ι : Type*} [DecidableEq ι]

/-! ### Conditional expectation given the revealed coordinates -/

/-- **`E[φ | ℱ_{Fm}](K) = Σ_{K₂ ⊆ D} wtW K₂ · φ (K →_{Fm K} K₂)`**: resample the coordinates outside the revealed set
`Fm K`. [cite: Gladkov2024, Def. 2.3 and Thm. 3.2 (`C₁ →_S C₂`)] -/
def cE (D : Finset ι) (p : ι → ℝ) (Fm : Finset ι → Finset ι) (φ : Finset ι → ℝ) (K : Finset ι) : ℝ :=
  ∑ K₂ ∈ D.powerset, wtW D p K₂ * φ (splice (Fm K) K K₂)

section Calculus

variable (D : Finset ι) (p : ι → ℝ) (Fm : Finset ι → Finset ι)

/-- Constants are reproduced (total mass one). [folklore] -/
theorem cE_const (c : ℝ) (K : Finset ι) : cE D p Fm (fun _ => c) K = c := by
  unfold cE; rw [← Finset.sum_mul, sum_wtW, one_mul]

/-- **Pull-out**: a factor determined by the revealed coordinates comes out of the conditional expectation.
[folklore] -/
theorem cE_mul_of_local {Z : Finset ι → ℝ} (hZ : ∀ K K' : Finset ι, (∀ i ∈ Fm K, (i ∈ K ↔ i ∈ K')) → Z K' = Z K)
    (φ : Finset ι → ℝ) (K : Finset ι) :
    cE D p Fm (fun L => Z L * φ L) K = Z K * cE D p Fm φ K := by
  unfold cE
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun K₂ _ => ?_
  show wtW D p K₂ * (Z (splice (Fm K) K K₂) * φ (splice (Fm K) K K₂)) = _
  rw [hZ K (splice (Fm K) K K₂) (fun i hi => (mem_splice_of_mem hi).symm)]
  ring

variable {Fm}

/-- `cE φ` is itself determined by the revealed coordinates (self-determined `Fm`). [cite: Gladkov2024, Def. 2.4] -/
theorem cE_local (hF : SelfDetermined Fm) (φ : Finset ι → ℝ) :
    ∀ K K' : Finset ι, (∀ i ∈ Fm K, (i ∈ K ↔ i ∈ K')) → cE D p Fm φ K' = cE D p Fm φ K := by
  intro K K' h
  unfold cE
  rw [hF K K' h]
  exact Finset.sum_congr rfl fun K₂ _ => by rw [splice_congr_left h K₂]

/-- **Tower property** `E[cE φ] = E[φ]`: the hybrid `K →_{Fm K} K₂` of two independent copies has the law of one copy
(Gladkov's swap Lemma 3.1). [cite: Gladkov2024, Lemma 3.1] -/
theorem ED_cE (hF : SelfDetermined Fm) (φ : Finset ι → ℝ) : ED D p (cE D p Fm φ) = ED D p φ := by
  have h := sum_pair_reindexW D p hF (fun x => φ x.1)
  simp only [swapPair] at h
  unfold ED cE
  rw [show ∑ S ∈ D.powerset, wtW D p S * φ S =
      ∑ x ∈ D.powerset ×ˢ D.powerset, wt2W D p x * φ x.1 by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun K _ => ?_
    simp only [wt2W]
    rw [← Finset.sum_mul, ← Finset.mul_sum, sum_wtW]; ring]
  rw [h, Finset.sum_product]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun K₂ _ => by simp only [wt2W]; ring

/-- `E[φ · cE ψ]` as a sum over independent pairs. [folklore] -/
theorem ED_mul_cE_eq_sum (φ ψ : Finset ι → ℝ) :
    ED D p (fun K => φ K * cE D p Fm ψ K) =
      ∑ x ∈ D.powerset ×ˢ D.powerset, wt2W D p x * (φ x.1 * ψ (splice (Fm x.1) x.1 x.2)) := by
  unfold ED cE
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun K _ => ?_
  dsimp only
  rw [Finset.mul_sum D.powerset _ (φ K), Finset.mul_sum D.powerset _ (wtW D p K)]
  refine Finset.sum_congr rfl fun K₂ _ => ?_
  simp only [wt2W]; ring

/-- `E[cE φ · ψ]` as a sum over independent pairs. [folklore] -/
theorem ED_cE_mul_eq_sum (φ ψ : Finset ι → ℝ) :
    ED D p (fun K => cE D p Fm φ K * ψ K) =
      ∑ x ∈ D.powerset ×ˢ D.powerset, wt2W D p x * (φ (splice (Fm x.1) x.1 x.2) * ψ x.1) := by
  unfold ED cE
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun K _ => ?_
  dsimp only
  rw [Finset.sum_mul, Finset.mul_sum D.powerset _ (wtW D p K)]
  refine Finset.sum_congr rfl fun K₂ _ => ?_
  simp only [wt2W]; ring

/-- **Symmetry** `E[φ · cE ψ] = E[cE φ · ψ]` (both equal `E⊗E[φ(C₁) ψ(C₁ →_S C₂)]` up to the swap).
[cite: Gladkov2024, Lemma 3.1] -/
theorem ED_mul_cE_comm (hF : SelfDetermined Fm) (φ ψ : Finset ι → ℝ) :
    ED D p (fun K => φ K * cE D p Fm ψ K) = ED D p (fun K => cE D p Fm φ K * ψ K) := by
  have h := sum_pair_reindexW D p hF (fun x => φ x.1 * ψ (splice (Fm x.1) x.1 x.2))
  have hfst : ∀ x : Finset ι × Finset ι, Fm (swapPair Fm x).1 = Fm x.1 := fun x => apply_swapPair_fst hF x
  have hswap : ∀ x : Finset ι × Finset ι,
      φ (swapPair Fm x).1 * ψ (splice (Fm (swapPair Fm x).1) (swapPair Fm x).1 (swapPair Fm x).2) =
        φ (splice (Fm x.1) x.1 x.2) * ψ x.1 := by
    intro x
    rw [hfst x]
    simp only [swapPair, splice_splice_left]
  simp only [hswap] at h
  rw [ED_mul_cE_eq_sum, ED_cE_mul_eq_sum, h]

end Calculus

/-! ### Layer-cake extension: from up-set indicators to monotone nonnegative functions -/

/-- **Layer-cake extension.** On a finite set `s` of elements of a preorder, a linear functional `f ↦ Σ_{K ∈ s} a_K f(K)`
that is nonnegative on the indicator of every up-set is nonnegative on every monotone `f ≥ 0` (peel off
`m · 1_{f > 0}`, `m = min f|_{f>0}`, and induct on the support). [folklore] -/
theorem sum_mul_nonneg_of_upperSet {α : Type*} [Preorder α] (s : Finset α) (a : α → ℝ)
    (ha : ∀ U : Set α, IsUpperSet U → 0 ≤ ∑ K ∈ s, a K * ind U K) :
    ∀ (f : α → ℝ), Monotone f → (∀ K, 0 ≤ f K) → 0 ≤ ∑ K ∈ s, a K * f K := by
  classical
  intro f hf hf0
  induction hn : (s.filter fun K => 0 < f K).card using Nat.strong_induction_on generalizing f with
  | _ n ih =>
    by_cases hsupp : (s.filter fun K => 0 < f K) = ∅
    · -- `f = 0` on `s`
      have h0 : ∀ K ∈ s, f K = 0 := fun K hK => by
        have : K ∉ s.filter fun K => 0 < f K := by rw [hsupp]; exact Finset.notMem_empty K
        rw [Finset.mem_filter, not_and, not_lt] at this
        exact le_antisymm (this hK) (hf0 K)
      rw [Finset.sum_eq_zero fun K hK => by rw [h0 K hK, mul_zero]]
    · have hne : (s.filter fun K => 0 < f K).Nonempty := Finset.nonempty_iff_ne_empty.2 hsupp
      -- the minimum positive value and the up-set `{f > 0}`
      set m₀ : ℝ := ((s.filter fun K => 0 < f K).image f).min' (hne.image f) with hm₀
      set U : Set α := {K | 0 < f K} with hU
      have hUup : IsUpperSet U := fun K K' hKK' hK => lt_of_lt_of_le hK (hf hKK')
      have hm₀pos : 0 < m₀ := by
        obtain ⟨K, hK, hKm⟩ := Finset.mem_image.1 (Finset.min'_mem _ (hne.image f))
        rw [← hm₀] at hKm
        rw [← hKm]; exact (Finset.mem_filter.1 hK).2
      have hm₀le : ∀ K ∈ s, 0 < f K → m₀ ≤ f K := fun K hK hfK =>
        Finset.min'_le _ _ (Finset.mem_image.2 ⟨K, Finset.mem_filter.2 ⟨hK, hfK⟩, rfl⟩)
      -- the peeled function
      set f' : α → ℝ := fun K => f K - m₀ * ind U K with hf'
      have hf'U : ∀ K, 0 < f K → f' K = f K - m₀ := fun K hK => by
        simp only [hf']; rw [ind_of_mem (show K ∈ U from hK), mul_one]
      have hf'nU : ∀ K, ¬ 0 < f K → f' K = f K := fun K hK => by
        simp only [hf']; rw [ind_of_not_mem (show K ∉ U from hK), mul_zero, sub_zero]
      have hfz : ∀ K, ¬ 0 < f K → f K = 0 := fun K hK => le_antisymm (not_lt.1 hK) (hf0 K)
      have hf'0s : ∀ K ∈ s, 0 ≤ f' K := fun K hK => by
        by_cases hfK : 0 < f K
        · rw [hf'U K hfK]; linarith [hm₀le K hK hfK]
        · rw [hf'nU K hfK]; exact hf0 K
      -- monotone and nonnegative off `s` as well, except that `m₀ ≤ f` may fail off `s`: clip at `0`
      set f'' : α → ℝ := fun K => max (f' K) 0 with hf''
      have hf''mono : Monotone f'' := by
        intro K K' hKK'
        simp only [hf'', hf']
        by_cases hK : 0 < f K
        · have hK' : 0 < f K' := lt_of_lt_of_le hK (hf hKK')
          rw [ind_of_mem (show K ∈ U from hK), ind_of_mem (show K' ∈ U from hK')]
          exact max_le_max (by linarith [hf hKK']) le_rfl
        · rw [hfz K hK, ind_of_not_mem (show K ∉ U from hK)]
          simp only [mul_zero, sub_zero, max_self]
          exact le_max_right _ _
      have hf''0 : ∀ K, 0 ≤ f'' K := fun K => le_max_right _ _
      have hf''s : ∀ K ∈ s, f'' K = f' K := fun K hK => max_eq_left (hf'0s K hK)
      -- the support shrinks: the minimiser drops out
      obtain ⟨K₀, hK₀, hK₀m⟩ := Finset.mem_image.1 (Finset.min'_mem _ (hne.image f))
      have hlt : (s.filter fun K => 0 < f'' K).card < n := by
        rw [← hn]
        refine Finset.card_lt_card ⟨fun K hK => ?_, fun hsub => ?_⟩
        · rw [Finset.mem_filter] at hK ⊢
          refine ⟨hK.1, ?_⟩
          by_contra hfK
          rw [hf''s K hK.1, hf'nU K hfK, hfz K hfK] at hK
          exact lt_irrefl _ hK.2
        · have h1 : K₀ ∈ s.filter fun K => 0 < f'' K := hsub hK₀
          rw [Finset.mem_filter] at h1
          have hs₀ := (Finset.mem_filter.1 hK₀)
          rw [hf''s K₀ hs₀.1, hf'U K₀ hs₀.2, hK₀m, ← hm₀] at h1
          exact lt_irrefl _ (by linarith [h1.2] : m₀ < m₀)
      have hrec := ih _ hlt f'' hf''mono hf''0 rfl
      -- reassemble
      have hsplit : ∑ K ∈ s, a K * f K = ∑ K ∈ s, a K * f'' K + m₀ * ∑ K ∈ s, a K * ind U K := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun K hK => ?_
        rw [hf''s K hK]
        simp only [hf']; ring
      rw [hsplit]
      exact add_nonneg hrec (mul_nonneg hm₀pos.le (ha U hUup))

/-! ### Decision-tree Harris–Kleitman for a real increasing function -/

/-- The event form of Theorem 3.2 as a sum: `P⊗P{C₁ ∈ X, C₁ →_S C₂ ∈ Y} = E[1_X · cE 1_Y]`. [cite: Gladkov2024, Thm. 3.2] -/
theorem Pr2W_treeHK_eq_ED (D : Finset ι) (p : ι → ℝ) (T : DTree ι) (X Y : Set (Finset ι)) :
    Pr2W D p (treeHK ∅ T X Y) = ED D p (fun K => ind X K * cE D p (revealed T) (ind Y) K) := by
  rw [Pr2W_eq_sum_ind, Finset.sum_product]
  unfold ED cE
  refine Finset.sum_congr rfl fun K _ => ?_
  dsimp only
  rw [Finset.mul_sum D.powerset _ (ind X K), Finset.mul_sum D.powerset _ (wtW D p K)]
  refine Finset.sum_congr rfl fun K₂ _ => ?_
  have hind : ind (treeHK ∅ T X Y) (K, K₂) = ind X K * ind Y (splice (revealed T K) K K₂) := by
    have hmem : (K, K₂) ∈ treeHK ∅ T X Y ↔ K ∈ X ∧ splice (revealed T K) K K₂ ∈ Y := by
      simp only [treeHK, hkWith, Finset.empty_union, Set.mem_setOf_eq]
    by_cases h1 : K ∈ X
    · by_cases h2 : splice (revealed T K) K K₂ ∈ Y
      · rw [ind_of_mem (hmem.2 ⟨h1, h2⟩), ind_of_mem h1, ind_of_mem h2, mul_one]
      · rw [ind_of_not_mem (fun h => h2 (hmem.1 h).2), ind_of_mem h1, ind_of_not_mem h2, mul_zero]
    · rw [ind_of_not_mem (fun h => h1 (hmem.1 h).1), ind_of_not_mem h1, zero_mul]
  rw [hind]
  simp only [wt2W]; ring

section TH

variable (D : Finset ι) {p : ι → ℝ} (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
include hp0 hp1

/-- **Decision-tree Harris–Kleitman for a real monotone `f ≥ 0` and an increasing event `Y`**:
`E[f]·P(Y) ≤ E[f · E[1_Y | ℱ_T]]`. [cite: Gladkov2024, Thm. 3.2] -/
theorem ED_mul_PrW_le_ED_mul_cE_ind (T : DTree ι) {f : Finset ι → ℝ} (hf : Monotone f) (hf0 : ∀ K, 0 ≤ f K)
    {Y : Set (Finset ι)} (hY : IsUpperSet Y) :
    ED D p f * PrW D p Y ≤ ED D p (fun K => f K * cE D p (revealed T) (ind Y) K) := by
  -- the linear functional `f ↦ E[f · (cE 1_Y − P(Y))]` is nonnegative on up-set indicators by Theorem 3.2
  have key := sum_mul_nonneg_of_upperSet D.powerset
    (fun K => wtW D p K * (cE D p (revealed T) (ind Y) K - PrW D p Y)) (fun U hU => by
      have h32 := PrW_mul_PrW_le_Pr2W_treeHK D hp0 hp1 T hU hY
      rw [Pr2W_treeHK_eq_ED, PrW_eq_sum_ind D p U] at h32
      unfold ED at h32
      have : ∑ K ∈ D.powerset, wtW D p K * (cE D p (revealed T) (ind Y) K - PrW D p Y) * ind U K =
          ∑ K ∈ D.powerset, wtW D p K * (ind U K * cE D p (revealed T) (ind Y) K) -
            (∑ K ∈ D.powerset, wtW D p K * ind U K) * PrW D p Y := by
        rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun K _ => by ring
      rw [this]; linarith) f hf hf0
  have : ∑ K ∈ D.powerset, wtW D p K * (cE D p (revealed T) (ind Y) K - PrW D p Y) * f K =
      ED D p (fun K => f K * cE D p (revealed T) (ind Y) K) - ED D p f * PrW D p Y := by
    unfold ED
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun K _ => by ring
  rw [this] at key
  linarith

/-- **Lemma TH** (`Cov(E[f | ℱ_T], 1_Y) ≥ 0`): `E[f]·P(Y) ≤ E[E[f | ℱ_T] · 1_Y]` for `f` monotone nonnegative and `Y`
increasing — the decision-tree Harris–Kleitman inequality for a real function. [cite: Gladkov2024, Thm. 3.2] -/
theorem treeHarris_real (T : DTree ι) {f : Finset ι → ℝ} (hf : Monotone f) (hf0 : ∀ K, 0 ≤ f K)
    {Y : Set (Finset ι)} (hY : IsUpperSet Y) :
    ED D p f * PrW D p Y ≤ ED D p (fun K => cE D p (revealed T) f K * ind Y K) := by
  rw [← ED_mul_cE_comm D p (selfDetermined_revealed T) f (ind Y)]
  exact ED_mul_PrW_le_ED_mul_cE_ind D hp0 hp1 T hf hf0 hY

end TH

end TreeHarris

end Percolation.Continuity

end
