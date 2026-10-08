import Percolation.Continuity.AdditiveGluing.OfAGloc
import Percolation.Continuity.AdditiveGluing.SurplusTransfer
import Percolation.Util.Linter

/-!
# (GEN) for every relay set, and `Percolation.Continuity.Statements.AdditiveGluing`, from the surplus-transfer inequality (S5)

With `Sur_x(T) := ∫_{x ↔ T} F(C(x)) − Σ_{a ∈ T} μ(P^x_a)·m_a` (`P^x_a` the first-in-rank patterns of an `m`-compatible injective rank `r` on `T`,
`m_a = ∫ F(C(a))`), the surplus-transfer inequality is
  (S5)  `μ({v ↮ T} ∩ {o ↔ v}) · Sur_v(T) ≤ μ(v ↮ T) · Sur_o(T)`   (`v ∉ T`; all `o`, monotone nonnegative `F`, compatible injective `r`).
`gen_firstRank_of_surplusTransfer`: (S5) for all relay sets of size `≤ K` ⟹ (GEN) (`Sur_o(A) ≥ 0`) for all relay sets of size `≤ K + 1`, by induction on
`|A|`: remove the rank-maximal relay `a_k`, `Sur_o(A) = Sur_o(T) − deficit_k`, bound `μ(a_k ↮ T)·deficit_k ≤ μ(P_k)·Cov(F(C(a_k)), 1_{a_k ↔ T}) ≤ μ(P_k)·Sur_{a_k}(T)`
by the one-cluster BHK inequality (vdBHK Thm 1.3 for `C(a_k)` given `a_k ↮ T`) and the maximality of `m_{a_k}`, then apply (S5) with `v = a_k`
(`|T| = 1`: `surplusTransfer_single`; `|A| = 3` spelled out: `gen_triple_of_surplusTransfer_pair`).  With `agloc_firstRank_of_gen` and
`additiveGluing_of_agloc_firstRank`: `additiveGluing_of_surplusTransfer` — `AdditiveGluing` FROM (S5) ALONE.
[cite: VandenbergHaggstromKahn2005, Thm. 1.3 (p. 6)] [cite: KozmaNitzan2024, Conj. 1 (p. 3), Conj. 4 (p. 32)]
-/

noncomputable section

namespace Percolation.Continuity.AGloc

open MeasureTheory Set
open Percolation.Literature.LatticeModels (prodBernoulli)
open Percolation.Literature Percolation.Literature.KNPreFKG
open Percolation.Continuity.Statements

variable {n : ℕ}

theorem filter_erase_of_not {A : Finset (Fin n)} {k : Fin n} {p : Fin n → Prop} [DecidablePred p] (hk : ¬ p k) :
    (A.erase k).filter p = A.filter p := by
  ext a
  simp only [Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨⟨_, ha⟩, hp⟩; exact ⟨ha, hp⟩
  · rintro ⟨ha, hp⟩; exact ⟨⟨fun h => hk (h ▸ hp), ha⟩, hp⟩

/-- **(S5) ⟹ (GEN), all relay sets.** If the surplus-transfer inequality holds for every relay set of size `≤ K` (every observer `o`, second
observer `v ∉ T`, monotone nonnegative `F`, `m`-compatible injective rank), then the master form (GEN) `Sur_o(A) ≥ 0` holds for every relay set of
size `≤ K + 1`. [cite: VandenbergHaggstromKahn2005, Thm. 1.3 (p. 6)] -/
theorem gen_firstRank_of_surplusTransfer (K : ℕ)
    (hST : ∀ (n : ℕ) (w : Sym2 (Fin n) → unitInterval) (T : Finset (Fin n)) (o v : Fin n) (F : Set (Fin n) → ℝ) (r : Fin n → ℕ),
      T.card ≤ K → v ∉ T → (∀ S S' : Set (Fin n), S ⊆ S' → F S ≤ F S') → (∀ S, 0 ≤ F S) → Set.InjOn r ↑T →
      (∀ a ∈ T, ∀ a' ∈ T, r a < r a' →
        ∫ ω, F (openCluster ω a) ∂(prodBernoulli w) ≤ ∫ ω, F (openCluster ω a') ∂(prodBernoulli w)) →
      (prodBernoulli w).real ({ω : BondConfig (Fin n) | ∀ a ∈ T, ¬ (openGraph ω).Reachable v a} ∩ openConn o v) *
          (∫ ω in (⋃ a ∈ T, openConn v a), F (openCluster ω v) ∂(prodBernoulli w) -
            ∑ a ∈ T, (prodBernoulli w).real
                (openConn v a ∩ ⋂ a' ∈ T.filter (fun a' => r a' < r a), (openConn v a')ᶜ : Set (BondConfig (Fin n))) *
              ∫ ω, F (openCluster ω a) ∂(prodBernoulli w)) ≤
        (prodBernoulli w).real {ω : BondConfig (Fin n) | ∀ a ∈ T, ¬ (openGraph ω).Reachable v a} *
          (∫ ω in (⋃ a ∈ T, openConn o a), F (openCluster ω o) ∂(prodBernoulli w) -
            ∑ a ∈ T, (prodBernoulli w).real
                (openConn o a ∩ ⋂ a' ∈ T.filter (fun a' => r a' < r a), (openConn o a')ᶜ : Set (BondConfig (Fin n))) *
              ∫ ω, F (openCluster ω a) ∂(prodBernoulli w))) :
    ∀ (n : ℕ) (w : Sym2 (Fin n) → unitInterval) (A : Finset (Fin n)) (o : Fin n) (F : Set (Fin n) → ℝ) (r : Fin n → ℕ),
      A.card ≤ K + 1 → (∀ S S' : Set (Fin n), S ⊆ S' → F S ≤ F S') → (∀ S, 0 ≤ F S) → Set.InjOn r ↑A →
      (∀ a ∈ A, ∀ a' ∈ A, r a < r a' →
        ∫ ω, F (openCluster ω a) ∂(prodBernoulli w) ≤ ∫ ω, F (openCluster ω a') ∂(prodBernoulli w)) →
      ∑ a ∈ A, (prodBernoulli w).real
            (openConn o a ∩ ⋂ a' ∈ A.filter (fun a' => r a' < r a), (openConn o a')ᶜ : Set (BondConfig (Fin n))) *
          ∫ ω, F (openCluster ω a) ∂(prodBernoulli w) ≤
        ∫ ω in (⋃ a ∈ A, openConn o a), F (openCluster ω o) ∂(prodBernoulli w) := by
  induction K with
  | zero =>
    -- `|A| ≤ 1`: empty (trivial) or a singleton (Harris)
    intro n w A o F r hA hF hF0 _ _
    classical
    rcases Nat.lt_or_ge A.card 1 with h0 | h1
    · have hA0 : A = ∅ := Finset.card_eq_zero.1 (Nat.lt_one_iff.1 h0)
      subst hA0
      simp
    · obtain ⟨a, hAa⟩ := Finset.card_eq_one.1 (le_antisymm hA h1)
      subst hAa
      have hf : ({a} : Finset (Fin n)).filter (fun a' => r a' < r a) = ∅ := by
        rw [Finset.filter_eq_empty_iff]; intro x hx; rw [Finset.mem_singleton] at hx; subst hx; exact lt_irrefl _
      simp only [Finset.sum_singleton, hf, Finset.notMem_empty, Set.iInter_of_empty, Set.iInter_univ, Set.inter_univ,
        Finset.mem_singleton, Set.iUnion_iUnion_eq_left]
      exact setIntegral_clusterFun_ge w a F hF hF0 (openConn o a) (isUpperSet_openConn o a) |>.trans
        (le_of_eq (setIntegral_congr_fun MeasurableSet.of_discrete fun ω hω => by
          rw [openCluster_eq_of_reachable (hω : (openGraph ω).Reachable o a)]))
  | succ K ih =>
    intro n w A o F r hA hF hF0 hr hcompat
    classical
    -- if `|A| ≤ K + 1` use the induction hypothesis directly
    by_cases hsmall : A.card ≤ K + 1
    · exact ih (fun n w T o v F r hT => hST n w T o v F r (hT.trans (Nat.le_succ K))) n w A o F r hsmall hF hF0 hr hcompat
    have hcard : A.card = K + 2 := by omega
    have hne : A.Nonempty := Finset.card_pos.1 (by omega)
    -- the rank-maximal relay `k` and `T = A.erase k`
    obtain ⟨k, hkA, hkmax⟩ := Finset.exists_max_image A r hne
    set T : Finset (Fin n) := A.erase k with hT
    have hTcard : T.card ≤ K + 1 := by rw [hT, Finset.card_erase_of_mem hkA]; omega
    have hTA : ∀ a ∈ T, a ∈ A := fun a ha => Finset.mem_of_mem_erase ha
    have hkT : k ∉ T := Finset.notMem_erase k A
    have hlt : ∀ a ∈ T, r a < r k := by
      intro a ha
      rcases (hkmax a (hTA a ha)).lt_or_eq with h | h
      · exact h
      · exact absurd (hr (hTA a ha) hkA h) (Finset.ne_of_mem_erase ha)
    have hrT : Set.InjOn r ↑T := hr.mono (by intro a ha; exact hTA a ha)
    have hcompatT : ∀ a ∈ T, ∀ a' ∈ T, r a < r a' →
        ∫ ω, F (openCluster ω a) ∂(prodBernoulli w) ≤ ∫ ω, F (openCluster ω a') ∂(prodBernoulli w) :=
      fun a ha a' ha' h => hcompat a (hTA a ha) a' (hTA a' ha') h
    -- (GEN) for `T` (induction hypothesis) and (S5) for `(o, k, T)`
    have hGenT := ih (fun n w T o v F r hT' => hST n w T o v F r (hT'.trans (Nat.le_succ K))) n w T o F r hTcard hF hF0 hrT hcompatT
    have hS5k := hST n w T o k F r hTcard hkT hF hF0 hrT hcompatT
    set μ := prodBernoulli w with hμ
    set f₀ : BondConfig (Fin n) → ℝ := fun ω => F (openCluster ω o) with hf₀
    set fk : BondConfig (Fin n) → ℝ := fun ω => F (openCluster ω k) with hfk
    set mk : ℝ := ∫ ω, fk ω ∂μ with hmk
    have hmeas : ∀ S : Set (BondConfig (Fin n)), MeasurableSet S := fun _ => MeasurableSet.of_discrete
    have hint : ∀ (g : BondConfig (Fin n) → ℝ) (S : Set (BondConfig (Fin n))), IntegrableOn g S μ :=
      fun g S => (Integrable.of_finite).integrableOn
    have hn := fun (S : Set (BondConfig (Fin n))) => (measureReal_nonneg : 0 ≤ μ.real S)
    set UT : Set (BondConfig (Fin n)) := ⋃ a ∈ T, openConn o a with hUT
    set Ok : Set (BondConfig (Fin n)) := openConn o k with hOk
    set Dk : Set (BondConfig (Fin n)) := {ω : BondConfig (Fin n) | ∀ a ∈ T, ¬ (openGraph ω).Reachable k a} with hDk
    set Wk : Set (BondConfig (Fin n)) := ⋃ a ∈ T, openConn k a with hWk
    set pat : Fin n → Fin n → Set (BondConfig (Fin n)) := fun x a =>
      (openConn x a ∩ ⋂ a' ∈ T.filter (fun a' => r a' < r a), (openConn x a')ᶜ : Set (BondConfig (Fin n))) with hpat
    -- patterns over `A`: for `a ∈ T` they are the `T`-patterns, for `k` it is `Ok ∩ Dk`
    have hfiltT : ∀ a ∈ T, A.filter (fun a' => r a' < r a) = T.filter (fun a' => r a' < r a) := by
      intro a ha
      rw [hT, filter_erase_of_not]
      exact fun h => lt_asymm h (hlt a ha)
    have hfiltk : A.filter (fun a' => r a' < r k) = T := by
      ext a
      simp only [Finset.mem_filter, hT, Finset.mem_erase]
      constructor
      · rintro ⟨ha, h⟩; exact ⟨fun hak => lt_irrefl _ (hak ▸ h), ha⟩
      · rintro ⟨hak, ha⟩; exact ⟨ha, hlt a (Finset.mem_erase.2 ⟨hak, ha⟩)⟩
    have hPk : (openConn o k ∩ ⋂ a' ∈ A.filter (fun a' => r a' < r k), (openConn o a')ᶜ : Set (BondConfig (Fin n))) = Dk ∩ Ok := by
      rw [hfiltk]
      ext ω
      simp only [hDk, hOk, mem_inter_iff, mem_iInter, mem_compl_iff, openConn, mem_setOf_eq]
      constructor
      · rintro ⟨hk', h⟩
        exact ⟨fun a ha hka => h a ha (hk'.trans hka), hk'⟩
      · rintro ⟨h, hk'⟩
        exact ⟨hk', fun a ha hoa => h a ha (hk'.symm.trans hoa)⟩
    have hsumA : ∑ a ∈ A, μ.real (openConn o a ∩ ⋂ a' ∈ A.filter (fun a' => r a' < r a), (openConn o a')ᶜ : Set (BondConfig (Fin n))) *
          ∫ ω, F (openCluster ω a) ∂μ =
        ∑ a ∈ T, μ.real (pat o a) * ∫ ω, F (openCluster ω a) ∂μ + μ.real (Dk ∩ Ok) * mk := by
      rw [← Finset.add_sum_erase A _ hkA, hPk, add_comm]
      congr 1
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [hfiltT a ha]
    -- the union over `A` splits as `UT ∪ Ok`, and `(UT ∪ Ok) \ UT = Dk ∩ Ok`
    have hUA : (⋃ a ∈ A, (openConn o a : Set (BondConfig (Fin n)))) = UT ∪ Ok := by
      ext ω
      simp only [hUT, hOk, mem_iUnion, mem_union, exists_prop, hT, Finset.mem_erase]
      constructor
      · rintro ⟨a, ha, h⟩
        by_cases hak : a = k
        · exact Or.inr (hak ▸ h)
        · exact Or.inl ⟨a, ⟨hak, ha⟩, h⟩
      · rintro (⟨a, ⟨_, ha⟩, h⟩ | h)
        · exact ⟨a, ha, h⟩
        · exact ⟨k, hkA, h⟩
    have h0k : ∀ ω ∈ Ok, f₀ ω = fk ω := fun ω hω => by
      simp only [hf₀, hfk]; rw [openCluster_eq_of_reachable (hω : (openGraph ω).Reachable o k)]
    have hdiff : (UT ∪ Ok) \ UT = Dk ∩ Ok := by
      ext ω
      simp only [hUT, hOk, hDk, mem_sdiff, mem_union, mem_iUnion, mem_inter_iff, exists_prop, not_exists, not_and, openConn,
        mem_setOf_eq]
      constructor
      · rintro ⟨h | h, hno⟩
        · obtain ⟨a, ha, h'⟩ := h; exact absurd h' (hno a ha)
        · exact ⟨fun a ha hka => hno a ha (h.trans hka), h⟩
      · rintro ⟨hd, hk'⟩
        exact ⟨Or.inr hk', fun a ha hoa => hd a ha (hk'.symm.trans hoa)⟩
    have hsplit : ∫ ω in UT ∪ Ok, f₀ ω ∂μ = ∫ ω in UT, f₀ ω ∂μ + ∫ ω in Dk ∩ Ok, fk ω ∂μ := by
      rw [← integral_inter_add_sdiff (hmeas UT) (hint f₀ (UT ∪ Ok)), inter_eq_right.2 subset_union_left, hdiff,
        setIntegral_congr_fun (hmeas (Dk ∩ Ok)) fun ω hω => h0k ω hω.2]
    -- one-cluster BHK for `C(k)` given `k ↮ T`
    have hindk : ∀ ω : BondConfig (Fin n), (connFamily k o).indicator (1 : Set (Sym2 (Fin n)) → ℝ) (openEdgeCluster ω k) =
        Ok.indicator (1 : BondConfig (Fin n) → ℝ) ω := fun ω => by
      rw [congrFun (indicator_comp_openEdgeCluster (connFamily k o) k) ω, ← openConn_eq_setOf_connFamily, openConn_symm k o]
    have hprod : ∀ (S : Set (BondConfig (Fin n))) (g : BondConfig (Fin n) → ℝ),
        ∫ ω in Dk, S.indicator (1 : BondConfig (Fin n) → ℝ) ω * g ω ∂μ = ∫ ω in Dk ∩ S, g ω ∂μ := by
      intro S g
      rw [← setIntegral_mul_indicator_one μ Dk S g]
      refine setIntegral_congr_fun (hmeas Dk) fun ω _ => ?_
      ring
    have hDset : {ω : BondConfig (Fin n) | ∀ x ∈ (↑T : Set (Fin n)), ¬ (openGraph ω).Reachable k x} = Dk := by
      ext ω; simp [hDk]
    have hBHK := BHK2006_clusterConditionalPositiveAssociation_holds (Fin n) w k (↑T : Set (Fin n))
      ((connFamily k o).indicator 1) (fun C => F {a | a = k ∨ ∃ e ∈ C, a ∈ e})
      (monotone_indicator_one_of_isUpperSet (isUpperSet_connFamily k o)) (monotone_clusterFun k F hF)
      (by exact_mod_cast hkT)
    simp only [hDset, clusterFun_openEdgeCluster, hindk] at hBHK
    rw [setIntegral_indicator_one_eq, hprod Ok] at hBHK
    change μ.real (Dk ∩ Ok) * ∫ ω in Dk, fk ω ∂μ ≤ μ.real Dk * ∫ ω in Dk ∩ Ok, fk ω ∂μ at hBHK
    -- `Dk = Wkᶜ`
    have hDW : Dk = Wkᶜ := by
      ext ω
      simp [hDk, hWk, openConn]
    have hDint : ∫ ω in Dk, fk ω ∂μ = mk - ∫ ω in Wk, fk ω ∂μ := by
      have := integral_add_compl (hmeas Wk) (Integrable.of_finite (f := fk) (μ := μ))
      rw [← hDW] at this
      linarith
    have hDμ : μ.real Dk = 1 - μ.real Wk := by
      have h1 : μ.real (univ : Set (BondConfig (Fin n))) = μ.real (univ ∩ Wk) + μ.real (univ \ Wk) :=
        (measureReal_inter_add_sdiff (s := univ) (h := measure_ne_top _ _) (hmeas Wk)).symm
      rw [probReal_univ, univ_inter, ← compl_eq_univ_sdiff, ← hDW] at h1
      linarith
    -- `Cov(fk, 1_{Wk}) ≤ Sur_k(T)` since `m_k` is maximal on `A`
    have hWsum : ∑ a ∈ T, μ.real (pat k a) = μ.real Wk := sum_measureReal_firstRank w T r k hrT
    have hmle : ∀ a ∈ T, ∫ ω, F (openCluster ω a) ∂μ ≤ mk := fun a ha => hcompat a (hTA a ha) k hkA (hlt a ha)
    have hCovSur : ∫ ω in Wk, fk ω ∂μ - mk * μ.real Wk ≤
        ∫ ω in Wk, fk ω ∂μ - ∑ a ∈ T, μ.real (pat k a) * ∫ ω, F (openCluster ω a) ∂μ := by
      have : ∑ a ∈ T, μ.real (pat k a) * ∫ ω, F (openCluster ω a) ∂μ ≤ ∑ a ∈ T, μ.real (pat k a) * mk :=
        Finset.sum_le_sum fun a ha => mul_le_mul_of_nonneg_left (hmle a ha) (hn _)
      rw [← Finset.sum_mul, hWsum] at this
      linarith
    -- combine
    have hmkn : 0 ≤ mk := integral_nonneg fun ω => hF0 _
    have hPint : 0 ≤ ∫ ω in Dk ∩ Ok, fk ω ∂μ := setIntegral_nonneg (hmeas _) fun ω _ => hF0 _
    change μ.real (Dk ∩ Ok) * (∫ ω in Wk, fk ω ∂μ - ∑ a ∈ T, μ.real (pat k a) * ∫ ω, F (openCluster ω a) ∂μ) ≤
      μ.real Dk * (∫ ω in UT, f₀ ω ∂μ - ∑ a ∈ T, μ.real (pat o a) * ∫ ω, F (openCluster ω a) ∂μ) at hS5k
    change ∑ a ∈ T, μ.real (pat o a) * ∫ ω, F (openCluster ω a) ∂μ ≤ ∫ ω in UT, f₀ ω ∂μ at hGenT
    have hkey : μ.real Dk * (mk * μ.real (Dk ∩ Ok) - ∫ ω in Dk ∩ Ok, fk ω ∂μ) ≤
        μ.real Dk * (∫ ω in UT, f₀ ω ∂μ - ∑ a ∈ T, μ.real (pat o a) * ∫ ω, F (openCluster ω a) ∂μ) := by
      have h1 : μ.real Dk * (mk * μ.real (Dk ∩ Ok) - ∫ ω in Dk ∩ Ok, fk ω ∂μ) ≤
          μ.real (Dk ∩ Ok) * (∫ ω in Wk, fk ω ∂μ - mk * μ.real Wk) := by
        rw [hDint, hDμ] at hBHK
        rw [hDμ]
        nlinarith [hBHK]
      have h2 := mul_le_mul_of_nonneg_left hCovSur (hn (Dk ∩ Ok))
      linarith
    have hgoal : 0 ≤ (∫ ω in UT, f₀ ω ∂μ - ∑ a ∈ T, μ.real (pat o a) * ∫ ω, F (openCluster ω a) ∂μ) -
        (mk * μ.real (Dk ∩ Ok) - ∫ ω in Dk ∩ Ok, fk ω ∂μ) := by
      by_cases hD0 : μ.real Dk = 0
      · have hP0 : μ.real (Dk ∩ Ok) = 0 :=
          le_antisymm (hD0 ▸ measureReal_mono inter_subset_left (measure_ne_top _ _)) (hn _)
        rw [hP0]
        nlinarith [hGenT, hPint]
      · have hDpos : 0 < μ.real Dk := lt_of_le_of_ne (hn _) (Ne.symm hD0)
        by_contra hneg
        have := mul_neg_of_pos_of_neg hDpos (lt_of_not_ge hneg)
        nlinarith [hkey]
    rw [hsumA, hUA, hsplit]
    linarith

/-- **`AdditiveGluing` from (S5).** If the surplus-transfer inequality holds for all relay sets (all sizes), then `AdditiveGluing` holds: (S5) ⟹ (GEN)
(`gen_firstRank_of_surplusTransfer`) ⟹ (AG-loc) (`agloc_firstRank_of_gen`) ⟹ `AdditiveGluing` (`additiveGluing_of_agloc_firstRank`).
[cite: KozmaNitzan2024, Conj. 1 (p. 3)] -/
theorem additiveGluing_of_surplusTransfer
    (hST : ∀ (n : ℕ) (w : Sym2 (Fin n) → unitInterval) (T : Finset (Fin n)) (o v : Fin n) (F : Set (Fin n) → ℝ) (r : Fin n → ℕ),
      v ∉ T → (∀ S S' : Set (Fin n), S ⊆ S' → F S ≤ F S') → (∀ S, 0 ≤ F S) → Set.InjOn r ↑T →
      (∀ a ∈ T, ∀ a' ∈ T, r a < r a' →
        ∫ ω, F (openCluster ω a) ∂(prodBernoulli w) ≤ ∫ ω, F (openCluster ω a') ∂(prodBernoulli w)) →
      (prodBernoulli w).real ({ω : BondConfig (Fin n) | ∀ a ∈ T, ¬ (openGraph ω).Reachable v a} ∩ openConn o v) *
          (∫ ω in (⋃ a ∈ T, openConn v a), F (openCluster ω v) ∂(prodBernoulli w) -
            ∑ a ∈ T, (prodBernoulli w).real
                (openConn v a ∩ ⋂ a' ∈ T.filter (fun a' => r a' < r a), (openConn v a')ᶜ : Set (BondConfig (Fin n))) *
              ∫ ω, F (openCluster ω a) ∂(prodBernoulli w)) ≤
        (prodBernoulli w).real {ω : BondConfig (Fin n) | ∀ a ∈ T, ¬ (openGraph ω).Reachable v a} *
          (∫ ω in (⋃ a ∈ T, openConn o a), F (openCluster ω o) ∂(prodBernoulli w) -
            ∑ a ∈ T, (prodBernoulli w).real
                (openConn o a ∩ ⋂ a' ∈ T.filter (fun a' => r a' < r a), (openConn o a')ᶜ : Set (BondConfig (Fin n))) *
              ∫ ω, F (openCluster ω a) ∂(prodBernoulli w))) :
    AdditiveGluing := by
  refine additiveGluing_of_agloc_firstRank fun n w A o b r hr hc => ?_
  refine agloc_firstRank_of_gen A.card (fun n' w' A' o' F r' hA' hF hF0 hr' hc' => ?_) n w A o b r le_rfl hr hc
  rcases Nat.eq_zero_or_pos A.card with h0 | hpos
  · -- `A' = ∅`
    have : A'.card = 0 := by omega
    rw [Finset.card_eq_zero.1 this]
    simp
  · obtain ⟨K, hK⟩ : ∃ K, A.card = K + 1 := ⟨A.card - 1, by omega⟩
    exact gen_firstRank_of_surplusTransfer K (fun n w T o v F r _ => hST n w T o v F r) n' w' A' o' F r' (hK ▸ hA') hF hF0 hr' hc'

end Percolation.Continuity.AGloc

end
