import Percolation.Continuity.AdditiveGluing.GenPair
import Percolation.Continuity.Statements
import Percolation.Util.Linter

/-!
# `Percolation.Continuity.Statements.AdditiveGluing` from the localised union bound (AG-loc), and (AG-loc) from the master form (GEN)

No `Prop` definitions: the two kernels (AG-loc) and (GEN) appear as explicit HYPOTHESES of the reduction theorems.

* (AG-loc), first-in-rank form: for a rank `r` injective on `A` with less reliable relays first and
  `P_a := {o ↔ a} ∩ ⋂_{a' ∈ A, r a' < r a} {o ↮ a'}`:  `μ(o ↔ A, o ↮ b) ≤ Σ_{a ∈ A} μ(P_a)·μ(a ↮ b)`.
* (GEN): for `F` monotone nonnegative on vertex sets, `m_a := ∫ F(C(a))`, a rank `r` injective on `A` with `m` non-decreasing along `r`:
  `Σ_{a ∈ A} μ(P_a)·m_a ≤ ∫_{o ↔ A} F(C(o))`  ("the value of `F` on the observer's cluster is on average at least the mean value of the
  least-valued relay it holds").

[cite: KozmaNitzan2024, Conj. 1 (p. 3), Question 5 (p. 32), Conj. 4 and Thm. 7 (p. 32)]
-/

noncomputable section

namespace Percolation.Continuity.AGloc

open MeasureTheory Set Finset
open Percolation.Literature.LatticeModels (prodBernoulli)
open Percolation.Literature
open Percolation.Continuity.Statements

variable {n : ℕ}

/-! ## A score-compatible injective rank -/

/-- The filter `{a' ∈ A : a' precedes a}` (score order, ties broken by the vertex order) grows strictly along that order. [folklore] -/
theorem scoreFilter_ssubset (A : Finset (Fin n)) (s : Fin n → ℝ) {a a'' : Fin n} (ha : a ∈ A)
    (hlt : s a < s a'' ∨ (s a = s a'' ∧ a < a'')) :
    (A.filter fun a' => s a' < s a ∨ (s a' = s a ∧ a' < a)) ⊂
      (A.filter fun a' => s a' < s a'' ∨ (s a' = s a'' ∧ a' < a'')) := by
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · intro x hx
    rw [Finset.mem_filter] at hx ⊢
    refine ⟨hx.1, ?_⟩
    rcases hx.2 with h1 | ⟨h1, h2⟩
    · rcases hlt with h3 | ⟨h3, _⟩
      · exact Or.inl (h1.trans h3)
      · exact Or.inl (h3 ▸ h1)
    · rcases hlt with h3 | ⟨h3, h4⟩
      · exact Or.inl (h1 ▸ h3)
      · exact Or.inr ⟨h1.trans h3, h2.trans h4⟩
  · intro heq
    have hmem : a ∈ A.filter fun a' => s a' < s a'' ∨ (s a' = s a'' ∧ a' < a'') := Finset.mem_filter.2 ⟨ha, hlt⟩
    rw [← heq, Finset.mem_filter] at hmem
    rcases hmem.2 with h | ⟨_, h⟩
    · exact lt_irrefl _ h
    · exact lt_irrefl _ h

/-- **A score-compatible injective rank exists**: for every real score `s` on the relays there is a rank `r : Fin n → ℕ`, injective on `A`,
with `r a < r a' → s a ≤ s a'` (rank = number of relays that come strictly before, ties broken by the vertex order). [folklore] -/
theorem exists_rank_compat (A : Finset (Fin n)) (s : Fin n → ℝ) :
    ∃ r : Fin n → ℕ, Set.InjOn r ↑A ∧ ∀ a ∈ A, ∀ a' ∈ A, r a < r a' → s a ≤ s a' := by
  refine ⟨fun a => (A.filter fun a' => s a' < s a ∨ (s a' = s a ∧ a' < a)).card, ?_, ?_⟩
  · intro a ha a'' ha'' h
    by_contra hne
    rcases lt_trichotomy (s a) (s a'') with hlt | heq | hgt
    · exact absurd h (Finset.card_lt_card (scoreFilter_ssubset A s ha (Or.inl hlt))).ne
    · rcases lt_or_gt_of_ne hne with h1 | h1
      · exact absurd h (Finset.card_lt_card (scoreFilter_ssubset A s ha (Or.inr ⟨heq, h1⟩))).ne
      · exact absurd h.symm (Finset.card_lt_card (scoreFilter_ssubset A s ha'' (Or.inr ⟨heq.symm, h1⟩))).ne
    · exact absurd h.symm (Finset.card_lt_card (scoreFilter_ssubset A s ha'' (Or.inl hgt))).ne
  · intro a _ a' ha' h
    by_contra hle
    exact lt_asymm h (Finset.card_lt_card (scoreFilter_ssubset A s ha' (Or.inl (lt_of_not_ge hle))))

/-! ## The first-in-rank patterns partition `{o ↔ A}` -/

/-- The first-in-rank patterns `P_a = {o ↔ a} ∩ ⋂_{a' ∈ A, r a' < r a} {o ↮ a'}` are pairwise disjoint when `r` is injective on `A`. [folklore] -/
theorem firstRank_disjoint (A : Finset (Fin n)) (r : Fin n → ℕ) (o : Fin n) (hr : Set.InjOn r ↑A) :
    Set.PairwiseDisjoint (↑A : Set (Fin n))
      (fun a => (openConn o a ∩ ⋂ a' ∈ A.filter (fun a' => r a' < r a), (openConn o a')ᶜ : Set (BondConfig (Fin n)))) := by
  intro a ha a'' ha'' hne
  rw [Function.onFun, Set.disjoint_left]
  intro ω h1 h2
  rcases lt_or_gt_of_ne (fun h => hne (hr ha ha'' h)) with hlt | hlt
  · have hna : ω ∈ (openConn o a : Set (BondConfig (Fin n)))ᶜ := by
      have := h2.2
      rw [Set.mem_iInter₂] at this
      exact this a (Finset.mem_filter.2 ⟨ha, hlt⟩)
    exact hna h1.1
  · have hna : ω ∈ (openConn o a'' : Set (BondConfig (Fin n)))ᶜ := by
      have := h1.2
      rw [Set.mem_iInter₂] at this
      exact this a'' (Finset.mem_filter.2 ⟨ha'', hlt⟩)
    exact hna h2.1

/-- The first-in-rank patterns cover `{o ↔ A}` when `r` is injective on `A` (the observer's cluster has a rank-minimal relay). [folklore] -/
theorem firstRank_cover (A : Finset (Fin n)) (r : Fin n → ℕ) (o : Fin n) :
    (⋃ a ∈ A, (openConn o a ∩ ⋂ a' ∈ A.filter (fun a' => r a' < r a), (openConn o a')ᶜ : Set (BondConfig (Fin n)))) =
      ⋃ a ∈ A, (openConn o a : Set (BondConfig (Fin n))) := by
  ext ω
  simp only [Set.mem_iUnion, Set.mem_inter_iff, exists_prop]
  constructor
  · rintro ⟨a, ha, h1, _⟩
    exact ⟨a, ha, h1⟩
  · rintro ⟨a, ha, h1⟩
    classical
    -- a rank-minimal attached relay
    have hne : (A.filter fun a' => ω ∈ (openConn o a' : Set (BondConfig (Fin n)))).Nonempty := ⟨a, Finset.mem_filter.2 ⟨ha, h1⟩⟩
    obtain ⟨a₀, ha₀, hmin⟩ := Finset.exists_min_image _ r hne
    rw [Finset.mem_filter] at ha₀
    refine ⟨a₀, ha₀.1, ha₀.2, ?_⟩
    rw [Set.mem_iInter₂]
    intro a' ha'
    rw [Finset.mem_filter] at ha'
    intro hω
    have := hmin a' (Finset.mem_filter.2 ⟨ha'.1, hω⟩)
    exact absurd ha'.2 (not_lt.2 this)

/-- The first-in-rank patterns have total measure `μ(o ↔ A)`. [folklore] -/
theorem sum_measureReal_firstRank (w : Sym2 (Fin n) → unitInterval) (A : Finset (Fin n)) (r : Fin n → ℕ) (o : Fin n)
    (hr : Set.InjOn r ↑A) :
    ∑ a ∈ A, (prodBernoulli w).real
        (openConn o a ∩ ⋂ a' ∈ A.filter (fun a' => r a' < r a), (openConn o a')ᶜ : Set (BondConfig (Fin n))) =
      (prodBernoulli w).real (⋃ a ∈ A, openConn o a) := by
  have hmeas : ∀ S : Set (BondConfig (Fin n)), MeasurableSet S := fun S => (Set.toFinite S).measurableSet
  rw [← firstRank_cover A r o, measureReal_biUnion_finset (firstRank_disjoint A r o hr) (fun a _ => hmeas _)
    (fun _ _ => measure_ne_top _ _)]

/-! ## `AdditiveGluing` from (AG-loc) -/

/-- **Graded reduction.** If the localised union bound (AG-loc, first-in-rank form) holds for every relay set of size `≤ K`, then
`AdditiveGluing` holds for every relay set of size `≤ K`: under `μ(a ↮ b) ≤ t` the right-hand side of (AG-loc) is `≤ t·μ(o ↔ A) ≤ t`,
and `μ(o ↔ A) − μ(o ↔ b) ≤ μ(o ↔ A, o ↮ b)`. [cite: KozmaNitzan2024, Conj. 1 (p. 3)] -/
theorem additiveGluing_card_of_agloc_firstRank (K : ℕ)
    (h : ∀ (n : ℕ) (w : Sym2 (Fin n) → unitInterval) (A : Finset (Fin n)) (o b : Fin n) (r : Fin n → ℕ),
      A.card ≤ K → Set.InjOn r ↑A →
      (∀ a ∈ A, ∀ a' ∈ A, r a < r a' →
        (prodBernoulli w).real (openConn a b) ≤ (prodBernoulli w).real (openConn a' b)) →
      (prodBernoulli w).real ((⋃ a ∈ A, openConn o a) ∩ (openConn o b)ᶜ : Set (BondConfig (Fin n))) ≤
        ∑ a ∈ A, (prodBernoulli w).real
            (openConn o a ∩ ⋂ a' ∈ A.filter (fun a' => r a' < r a), (openConn o a')ᶜ : Set (BondConfig (Fin n))) *
          (1 - (prodBernoulli w).real (openConn a b))) :
    ∀ (n : ℕ) (w : Sym2 (Fin n) → unitInterval) (A : Finset (Fin n)) (o b : Fin n) (t : ℝ), A.card ≤ K → 0 ≤ t →
      (∀ a ∈ A, 1 - t ≤ (prodBernoulli w).real (openConn a b)) →
      (prodBernoulli w).real (⋃ a ∈ A, openConn o a) - t ≤ (prodBernoulli w).real (openConn o b) := by
  intro n w A o b t hK ht hrel
  classical
  set μ := prodBernoulli w with hμ
  have hmeas : ∀ S : Set (BondConfig (Fin n)), MeasurableSet S := fun S => (Set.toFinite S).measurableSet
  obtain ⟨r, hrinj, hrc⟩ := exists_rank_compat A (fun a => μ.real (openConn a b))
  have key := h n w A o b r hK hrinj hrc
  rw [← hμ] at key
  have h1 : ∑ a ∈ A, μ.real (openConn o a ∩ ⋂ a' ∈ A.filter (fun a' => r a' < r a), (openConn o a')ᶜ : Set (BondConfig (Fin n))) *
        (1 - μ.real (openConn a b)) ≤
      ∑ a ∈ A, μ.real (openConn o a ∩ ⋂ a' ∈ A.filter (fun a' => r a' < r a), (openConn o a')ᶜ : Set (BondConfig (Fin n))) * t := by
    refine Finset.sum_le_sum fun a ha => ?_
    exact mul_le_mul_of_nonneg_left (by linarith [hrel a ha]) measureReal_nonneg
  have h2 : ∑ a ∈ A, μ.real (openConn o a ∩ ⋂ a' ∈ A.filter (fun a' => r a' < r a), (openConn o a')ᶜ : Set (BondConfig (Fin n))) * t =
      t * μ.real (⋃ a ∈ A, openConn o a) := by
    rw [← Finset.sum_mul, mul_comm, sum_measureReal_firstRank w A r o hrinj]
  have h3 : μ.real (⋃ a ∈ A, openConn o a) ≤ 1 := by
    have : μ.real (⋃ a ∈ A, openConn o a) ≤ μ.real (Set.univ : Set (BondConfig (Fin n))) :=
      measureReal_mono (Set.subset_univ _) (measure_ne_top _ _)
    rwa [probReal_univ] at this
  have h4 : μ.real (⋃ a ∈ A, openConn o a) - μ.real (openConn o b) ≤
      μ.real ((⋃ a ∈ A, openConn o a) ∩ (openConn o b)ᶜ : Set (BondConfig (Fin n))) := by
    have hsp : μ.real (⋃ a ∈ A, openConn o a) =
        μ.real ((⋃ a ∈ A, openConn o a) ∩ openConn o b : Set (BondConfig (Fin n))) +
          μ.real ((⋃ a ∈ A, openConn o a) ∩ (openConn o b)ᶜ : Set (BondConfig (Fin n))) := by
      rw [← measureReal_inter_add_sdiff (s := ⋃ a ∈ A, (openConn o a : Set (BondConfig (Fin n)))) (h := measure_ne_top _ _)
        (hmeas (openConn o b)), Set.sdiff_eq]
    have hm : μ.real ((⋃ a ∈ A, openConn o a) ∩ openConn o b : Set (BondConfig (Fin n))) ≤ μ.real (openConn o b) :=
      measureReal_mono Set.inter_subset_right (measure_ne_top _ _)
    linarith
  have h5 : t * μ.real (⋃ a ∈ A, openConn o a) ≤ t := by
    simpa using mul_le_mul_of_nonneg_left h3 ht
  linarith [key, h1, h2, h4, h5]

/-- **`AdditiveGluing` from (AG-loc)**, by name from the localised union bound in first-in-rank form (for all relay sets).
[cite: KozmaNitzan2024, Conj. 1 (p. 3), Question 5 (p. 32)] -/
theorem additiveGluing_of_agloc_firstRank
    (h : ∀ (n : ℕ) (w : Sym2 (Fin n) → unitInterval) (A : Finset (Fin n)) (o b : Fin n) (r : Fin n → ℕ),
      Set.InjOn r ↑A →
      (∀ a ∈ A, ∀ a' ∈ A, r a < r a' →
        (prodBernoulli w).real (openConn a b) ≤ (prodBernoulli w).real (openConn a' b)) →
      (prodBernoulli w).real ((⋃ a ∈ A, openConn o a) ∩ (openConn o b)ᶜ : Set (BondConfig (Fin n))) ≤
        ∑ a ∈ A, (prodBernoulli w).real
            (openConn o a ∩ ⋂ a' ∈ A.filter (fun a' => r a' < r a), (openConn o a')ᶜ : Set (BondConfig (Fin n))) *
          (1 - (prodBernoulli w).real (openConn a b))) :
    AdditiveGluing := by
  intro n w A o b t ht hrel
  exact additiveGluing_card_of_agloc_firstRank A.card
    (fun n' w' A' o' b' r' _ hr' hc' => h n' w' A' o' b' r' hr' hc') n w A o b t le_rfl ht hrel

/-! ## (AG-loc) from the master form (GEN) -/

/-- **(GEN) ⇒ (AG-loc).** If the master form (GEN) holds for relay sets of size `≤ K` (for every monotone nonnegative set function `F`
and every `F`-compatible injective rank), then the localised union bound (first-in-rank form) holds for relay sets of size `≤ K`:
take `F = 1{b ∈ ·}`, so that `∫ F(C(a)) = μ(a ↔ b)` and `∫_{o ↔ A} F(C(o)) = μ(o ↔ A, o ↔ b)`, and use that the patterns `P_a`
partition `{o ↔ A}`. [cite: KozmaNitzan2024, Conj. 4 (p. 32), Thm. 10 (p. 32)] -/
theorem agloc_firstRank_of_gen (K : ℕ)
    (hgen : ∀ (n : ℕ) (w : Sym2 (Fin n) → unitInterval) (A : Finset (Fin n)) (o : Fin n) (F : Set (Fin n) → ℝ) (r : Fin n → ℕ),
      A.card ≤ K → (∀ S T : Set (Fin n), S ⊆ T → F S ≤ F T) → (∀ S, 0 ≤ F S) → Set.InjOn r ↑A →
      (∀ a ∈ A, ∀ a' ∈ A, r a < r a' →
        ∫ ω, F (openCluster ω a) ∂(prodBernoulli w) ≤ ∫ ω, F (openCluster ω a') ∂(prodBernoulli w)) →
      ∑ a ∈ A, (prodBernoulli w).real
            (openConn o a ∩ ⋂ a' ∈ A.filter (fun a' => r a' < r a), (openConn o a')ᶜ : Set (BondConfig (Fin n))) *
          ∫ ω, F (openCluster ω a) ∂(prodBernoulli w) ≤
        ∫ ω in (⋃ a ∈ A, openConn o a), F (openCluster ω o) ∂(prodBernoulli w)) :
    ∀ (n : ℕ) (w : Sym2 (Fin n) → unitInterval) (A : Finset (Fin n)) (o b : Fin n) (r : Fin n → ℕ),
      A.card ≤ K → Set.InjOn r ↑A →
      (∀ a ∈ A, ∀ a' ∈ A, r a < r a' →
        (prodBernoulli w).real (openConn a b) ≤ (prodBernoulli w).real (openConn a' b)) →
      (prodBernoulli w).real ((⋃ a ∈ A, openConn o a) ∩ (openConn o b)ᶜ : Set (BondConfig (Fin n))) ≤
        ∑ a ∈ A, (prodBernoulli w).real
            (openConn o a ∩ ⋂ a' ∈ A.filter (fun a' => r a' < r a), (openConn o a')ᶜ : Set (BondConfig (Fin n))) *
          (1 - (prodBernoulli w).real (openConn a b)) := by
  intro n w A o b r hK hr hcompat
  classical
  set μ := prodBernoulli w with hμ
  have hmeas : ∀ S : Set (BondConfig (Fin n)), MeasurableSet S := fun S => (Set.toFinite S).measurableSet
  -- the set function `F = 1{b ∈ ·}`
  set F : Set (Fin n) → ℝ := fun M => if b ∈ M then 1 else 0 with hF
  have hFmono : ∀ S T : Set (Fin n), S ⊆ T → F S ≤ F T := by
    intro S T hST
    simp only [hF]
    by_cases hS : b ∈ S
    · rw [if_pos hS, if_pos (hST hS)]
    · rw [if_neg hS]
      split_ifs <;> norm_num
  have hF0 : ∀ S, 0 ≤ F S := by
    intro S
    simp only [hF]
    split_ifs <;> norm_num
  -- `F(C(x)) = 1_{x ↔ b}`
  have hFind : ∀ x : Fin n, (fun ω : BondConfig (Fin n) => F (openCluster ω x)) =
      (openConn x b : Set (BondConfig (Fin n))).indicator 1 := by
    intro x
    funext ω
    simp only [hF]
    by_cases hω : ω ∈ (openConn x b : Set (BondConfig (Fin n)))
    · rw [Set.indicator_of_mem hω, Pi.one_apply, if_pos (show b ∈ openCluster ω x from hω)]
    · rw [Set.indicator_of_notMem hω, if_neg (show b ∉ openCluster ω x from hω)]
  have hint : ∀ x : Fin n, ∫ ω, F (openCluster ω x) ∂μ = μ.real (openConn x b) := by
    intro x
    rw [hFind x, integral_indicator_one (hmeas _)]
  have hsetint : ∫ ω in (⋃ a ∈ A, openConn o a), F (openCluster ω o) ∂μ =
      μ.real ((⋃ a ∈ A, openConn o a) ∩ openConn o b : Set (BondConfig (Fin n))) := by
    rw [hFind o, ← integral_indicator (hmeas _), Set.indicator_indicator, integral_indicator_one ((hmeas _).inter (hmeas _))]
  have hcompat' : ∀ a ∈ A, ∀ a' ∈ A, r a < r a' →
      ∫ ω, F (openCluster ω a) ∂μ ≤ ∫ ω, F (openCluster ω a') ∂μ := by
    intro a ha a' ha' hlt
    rw [hint a, hint a']
    exact hcompat a ha a' ha' hlt
  have key := hgen n w A o F r hK hFmono hF0 hr hcompat'
  rw [← hμ] at key
  simp only [hint] at key
  rw [hsetint] at key
  -- `μ(U ∩ (o↔b)ᶜ) = μ(U) − μ(U ∩ (o↔b))`, `μ(U) = Σ μ(P_a)`
  have hsp : μ.real (⋃ a ∈ A, openConn o a) =
      μ.real ((⋃ a ∈ A, openConn o a) ∩ openConn o b : Set (BondConfig (Fin n))) +
        μ.real ((⋃ a ∈ A, openConn o a) ∩ (openConn o b)ᶜ : Set (BondConfig (Fin n))) := by
    rw [← measureReal_inter_add_sdiff (s := ⋃ a ∈ A, (openConn o a : Set (BondConfig (Fin n)))) (h := measure_ne_top _ _)
      (hmeas (openConn o b)), Set.sdiff_eq]
  have hsum := sum_measureReal_firstRank w A r o hr
  rw [← hμ] at hsum
  have hexp : ∑ a ∈ A, μ.real (openConn o a ∩ ⋂ a' ∈ A.filter (fun a' => r a' < r a), (openConn o a')ᶜ : Set (BondConfig (Fin n))) *
        (1 - μ.real (openConn a b)) =
      ∑ a ∈ A, μ.real (openConn o a ∩ ⋂ a' ∈ A.filter (fun a' => r a' < r a), (openConn o a')ᶜ : Set (BondConfig (Fin n))) -
        ∑ a ∈ A, μ.real (openConn o a ∩ ⋂ a' ∈ A.filter (fun a' => r a' < r a), (openConn o a')ᶜ : Set (BondConfig (Fin n))) *
          μ.real (openConn a b) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [hexp, hsum]
  linarith [key, hsp]

end Percolation.Continuity.AGloc

end
