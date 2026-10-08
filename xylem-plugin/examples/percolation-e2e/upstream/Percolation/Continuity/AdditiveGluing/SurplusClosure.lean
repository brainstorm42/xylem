import Percolation.Continuity.AdditiveGluing.GenOfSurplusTransfer
import Percolation.Continuity.CSH.Defs
import Percolation.Literature.TwoClusterGibbsCovariance
import Percolation.Util.Linter

/-!
# The surplus-transfer inequality (S5) for ALL weights from (S5) for non-degenerate weights — closure over degenerate weights via the pattern-free min-form of the surplus (towards `Percolation.Continuity.Statements.AdditiveGluing`)

WHY THIS IS NOT A ONE-LINE CLOSURE.  The hypothesis `hST` of `AGloc.additiveGluing_of_surplusTransfer` is stated for every weight function
`w : Sym2 (Fin n) → [0,1]` and every injective rank `r` on the relay set `T` that is COMPATIBLE with the means `m_a(w) = ∫ F(C_a) dμ_w`
(`r a < r a' → m_a ≤ m_a'`).  The peeling proof of (S5) divides by probabilities of conditioning events and uses `μ(x isolated) > 0`,
so it gives (S5) only for non-degenerate weights (`0 < w e < 1` for every pair).  Passing to the limit `p → w` is delicate because
compatibility of a FIXED rank `r` is not preserved under perturbation of the weights at ties of the means.  The way out: the ranked surplus
`Sur_x(T) = ∫_{x↔T} F(C_x) − Σ_a μ(P^x_a) m_a` does not depend on the compatible injective rank at all — on the first-in-rank pattern
`P^x_a` the relay `a` MINIMISES `m` over the relays joined to `x` — so it equals the pattern-free MIN-FORM
`∫_{x↔T} (F(C_x) − min_{a ∈ T, x ↔ a} m_a)` (`surplus_eq_minForm`), which is continuous in the weights (`continuous_minForm`); the
closure principle `weights_le_of_forall_pos_lt_one` and the existence of a compatible injective rank at every weight function
(`AGloc.exists_rank_compat`) finish (`surplusTransfer_of_nondegenerate`).  Consequence: `additiveGluing_of_surplusTransfer_nondegenerate` —
`AdditiveGluing` from (S5) for non-degenerate weights only.
[cite: KozmaNitzan2024, Conj. 1 (p. 3), Conj. 4 (p. 32)] [cite: GrimmettPercolation1999, §7.3 p. 162 (continuity in the weights)]
-/

noncomputable section

namespace Percolation.Continuity.CSH

open MeasureTheory Set
open Percolation.Literature.LatticeModels (prodBernoulli weights_le_of_forall_pos_lt_one prodBernoulli_real_continuous)
open Percolation.Literature
open Percolation.Literature.BHK2006 (weight integral_prodBernoulli_eq_sum continuous_weight)
open Percolation.Continuity.Statements
open scoped Classical

variable {n : ℕ}

/-- The relay mean `p ↦ m_a(p) = ∫ F(C_a) dμ_p` is continuous in the weights (a polynomial). [cite: GrimmettPercolation1999, §7.3 p. 162] -/
theorem continuous_relayMean (F : Set (Fin n) → ℝ) (a : Fin n) :
    Continuous fun p : Sym2 (Fin n) → unitInterval => ∫ ω, F (openCluster ω a) ∂(prodBernoulli p) := by
  have h : (fun p : Sym2 (Fin n) → unitInterval => ∫ ω, F (openCluster ω a) ∂(prodBernoulli p)) =
      fun p => ∑ ω : Set (Sym2 (Fin n)), weight (fun e => (p e : ℝ)) ω * F (openCluster ω a) := by
    funext p; exact integral_prodBernoulli_eq_sum p _
  rw [h]
  exact continuous_finsetSum _ fun ω _ => (continuous_weight ω).mul continuous_const

/-- A set integral `p ↦ ∫_U h_p dμ_p` is continuous in the weights when the integrand is, pointwise. [cite: GrimmettPercolation1999, §7.3 p. 162] -/
theorem continuous_setIntegral_weights (U : Set (BondConfig (Fin n)))
    (h : (Sym2 (Fin n) → unitInterval) → BondConfig (Fin n) → ℝ) (hh : ∀ ω, Continuous fun p => h p ω) :
    Continuous fun p : Sym2 (Fin n) → unitInterval => ∫ ω in U, h p ω ∂(prodBernoulli p) := by
  have hU : MeasurableSet U := MeasurableSet.of_discrete
  have e : (fun p : Sym2 (Fin n) → unitInterval => ∫ ω in U, h p ω ∂(prodBernoulli p)) =
      fun p => ∑ ω : Set (Sym2 (Fin n)), weight (fun e => (p e : ℝ)) ω * U.indicator (h p) ω := by
    funext p
    rw [← integral_indicator hU, integral_prodBernoulli_eq_sum]
  rw [e]
  refine continuous_finsetSum _ fun ω _ => (continuous_weight ω).mul ?_
  by_cases hω : ω ∈ U
  · simp only [indicator_of_mem hω]; exact hh ω
  · simp only [indicator_of_notMem hω]; exact continuous_const

/-- **On a first-in-rank pattern the pattern's relay minimises the mean** over the relays joined to the observer, for an injective
`m`-compatible rank. [folklore] -/
theorem inf'_eq_of_mem_pattern (T : Finset (Fin n)) (r : Fin n → ℕ) (m : Fin n → ℝ) (x a : Fin n) (ha : a ∈ T)
    (hr : Set.InjOn r ↑T) (hcompat : ∀ b ∈ T, ∀ b' ∈ T, r b < r b' → m b ≤ m b')
    (ω : BondConfig (Fin n))
    (hω : ω ∈ (openConn x a ∩ ⋂ a' ∈ T.filter (fun a' => r a' < r a), (openConn x a')ᶜ : Set (BondConfig (Fin n))))
    (hne : (T.filter fun b => ω ∈ (openConn x b : Set (BondConfig (Fin n)))).Nonempty) :
    (T.filter fun b => ω ∈ (openConn x b : Set (BondConfig (Fin n)))).inf' hne m = m a := by
  have haF : a ∈ T.filter fun b => ω ∈ (openConn x b : Set (BondConfig (Fin n))) := Finset.mem_filter.2 ⟨ha, hω.1⟩
  refine le_antisymm (Finset.inf'_le m haF) (Finset.le_inf' hne m fun b hb => ?_)
  rw [Finset.mem_filter] at hb
  have hnot : ¬ r b < r a := by
    intro hlt
    have h2 := hω.2
    rw [Set.mem_iInter₂] at h2
    exact h2 b (Finset.mem_filter.2 ⟨hb.1, hlt⟩) hb.2
  rcases (not_lt.1 hnot).lt_or_eq with hlt | heq
  · exact hcompat a ha b hb.1 hlt
  · rw [hr ha hb.1 heq]

/-- **The ranked surplus equals the pattern-free min-form** for every injective `m`-compatible rank:
`Sur_x(T) = ∫_{x↔T} (F(C_x) − min_{a ∈ T, x ↔ a} m_a) dμ`. [folklore] -/
theorem surplus_eq_minForm (w : Sym2 (Fin n) → unitInterval) (T : Finset (Fin n)) (r : Fin n → ℕ) (F : Set (Fin n) → ℝ) (x : Fin n)
    (hr : Set.InjOn r ↑T)
    (hcompat : ∀ b ∈ T, ∀ b' ∈ T, r b < r b' →
      ∫ ω, F (openCluster ω b) ∂(prodBernoulli w) ≤ ∫ ω, F (openCluster ω b') ∂(prodBernoulli w)) :
    surplus w T r F x =
      ∫ ω in (⋃ a ∈ T, openConn x a), (F (openCluster ω x) -
        (if h : (T.filter fun b => ω ∈ (openConn x b : Set (BondConfig (Fin n)))).Nonempty then
          (T.filter fun b => ω ∈ (openConn x b : Set (BondConfig (Fin n)))).inf' h
            (fun b => ∫ η, F (openCluster η b) ∂(prodBernoulli w)) else 0)) ∂(prodBernoulli w) := by
  set μ := prodBernoulli w with hμ
  set m : Fin n → ℝ := fun b => ∫ η, F (openCluster η b) ∂μ with hm
  set g : BondConfig (Fin n) → ℝ := fun ω =>
    if h : (T.filter fun b => ω ∈ (openConn x b : Set (BondConfig (Fin n)))).Nonempty then
      (T.filter fun b => ω ∈ (openConn x b : Set (BondConfig (Fin n)))).inf' h m else 0 with hg
  set pat : Fin n → Set (BondConfig (Fin n)) := fun a =>
    (openConn x a ∩ ⋂ a' ∈ T.filter (fun a' => r a' < r a), (openConn x a')ᶜ : Set (BondConfig (Fin n))) with hpat
  have hmeas : ∀ S : Set (BondConfig (Fin n)), MeasurableSet S := fun _ => MeasurableSet.of_discrete
  have hint : ∀ (f : BondConfig (Fin n) → ℝ) (S : Set (BondConfig (Fin n))), IntegrableOn f S μ :=
    fun f S => (Integrable.of_finite).integrableOn
  -- on `pat a`, `g = m a`
  have hg_pat : ∀ a ∈ T, ∀ ω ∈ pat a, g ω = m a := by
    intro a ha ω hω
    have hne : (T.filter fun b => ω ∈ (openConn x b : Set (BondConfig (Fin n)))).Nonempty :=
      ⟨a, Finset.mem_filter.2 ⟨ha, hω.1⟩⟩
    simp only [hg, hne, dif_pos]
    exact inf'_eq_of_mem_pattern T r m x a ha hr hcompat ω hω hne
  -- `Σ_a μ(pat a) m_a = ∫_{x↔T} g`
  have hsum : ∑ a ∈ T, μ.real (pat a) * m a = ∫ ω in (⋃ a ∈ T, openConn x a), g ω ∂μ := by
    rw [← AGloc.firstRank_cover T r x, integral_biUnion_finset T (fun a _ => hmeas _) (AGloc.firstRank_disjoint T r x hr)
      (fun a _ => hint g _)]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [setIntegral_congr_fun (hmeas (pat a)) (hg_pat a ha), setIntegral_const, smul_eq_mul]
  rw [integral_sub (hint _ _) (hint _ _), ← hsum]
  rfl

/-- **The min-form of the surplus is continuous in the weights.** [cite: GrimmettPercolation1999, §7.3 p. 162] -/
theorem continuous_minForm (T : Finset (Fin n)) (F : Set (Fin n) → ℝ) (x : Fin n) :
    Continuous fun p : Sym2 (Fin n) → unitInterval =>
      ∫ ω in (⋃ a ∈ T, openConn x a), (F (openCluster ω x) -
        (if h : (T.filter fun b => ω ∈ (openConn x b : Set (BondConfig (Fin n)))).Nonempty then
          (T.filter fun b => ω ∈ (openConn x b : Set (BondConfig (Fin n)))).inf' h
            (fun b => ∫ η, F (openCluster η b) ∂(prodBernoulli p)) else 0)) ∂(prodBernoulli p) := by
  refine continuous_setIntegral_weights _ _ fun ω => continuous_const.sub ?_
  by_cases hne : (T.filter fun b => ω ∈ (openConn x b : Set (BondConfig (Fin n)))).Nonempty
  · simp only [hne, dif_pos]
    exact Continuous.finset_inf'_apply hne fun b _ => continuous_relayMean F b
  · simp only [hne, dif_neg, not_false_eq_true]
    exact continuous_const

/-- **(S5) for all weights from (S5) for non-degenerate weights.** If for every NON-DEGENERATE weight function `p` (all `p e ∈ (0,1)`)
and every injective `m(p)`-compatible rank the surplus-transfer inequality `μ_p(v ↮ T, o ↔ v)·Sur_v(T) ≤ μ_p(v ↮ T)·Sur_o(T)` holds, then it
holds at EVERY weight function `w` for every injective `m(w)`-compatible rank (closure principle applied to the min-form).
[cite: GrimmettPercolation1999, §7.3 p. 162] [cite: KozmaNitzan2024, Conj. 4 (p. 32)] -/
theorem surplusTransfer_of_nondegenerate (T : Finset (Fin n)) (o v : Fin n) (F : Set (Fin n) → ℝ)
    (h : ∀ p : Sym2 (Fin n) → unitInterval, (∀ e, 0 < p e ∧ p e < 1) → ∀ r : Fin n → ℕ, Set.InjOn r ↑T →
      (∀ a ∈ T, ∀ a' ∈ T, r a < r a' →
        ∫ ω, F (openCluster ω a) ∂(prodBernoulli p) ≤ ∫ ω, F (openCluster ω a') ∂(prodBernoulli p)) →
      (prodBernoulli p).real ({ω : BondConfig (Fin n) | ∀ a ∈ T, ¬ (openGraph ω).Reachable v a} ∩ openConn o v) *
          surplus p T r F v ≤
        (prodBernoulli p).real {ω : BondConfig (Fin n) | ∀ a ∈ T, ¬ (openGraph ω).Reachable v a} * surplus p T r F o)
    (w : Sym2 (Fin n) → unitInterval) (r : Fin n → ℕ) (hr : Set.InjOn r ↑T)
    (hcompat : ∀ a ∈ T, ∀ a' ∈ T, r a < r a' →
      ∫ ω, F (openCluster ω a) ∂(prodBernoulli w) ≤ ∫ ω, F (openCluster ω a') ∂(prodBernoulli w)) :
    (prodBernoulli w).real ({ω : BondConfig (Fin n) | ∀ a ∈ T, ¬ (openGraph ω).Reachable v a} ∩ openConn o v) *
        surplus w T r F v ≤
      (prodBernoulli w).real {ω : BondConfig (Fin n) | ∀ a ∈ T, ¬ (openGraph ω).Reachable v a} * surplus w T r F o := by
  -- the min-forms as functions of the weights
  set S : Fin n → (Sym2 (Fin n) → unitInterval) → ℝ := fun x p =>
    ∫ ω in (⋃ a ∈ T, openConn x a), (F (openCluster ω x) -
      (if h : (T.filter fun b => ω ∈ (openConn x b : Set (BondConfig (Fin n)))).Nonempty then
        (T.filter fun b => ω ∈ (openConn x b : Set (BondConfig (Fin n)))).inf' h
          (fun b => ∫ η, F (openCluster η b) ∂(prodBernoulli p)) else 0)) ∂(prodBernoulli p) with hS
  set f : (Sym2 (Fin n) → unitInterval) → ℝ := fun p =>
    (prodBernoulli p).real ({ω : BondConfig (Fin n) | ∀ a ∈ T, ¬ (openGraph ω).Reachable v a} ∩ openConn o v) * S v p with hf
  set g : (Sym2 (Fin n) → unitInterval) → ℝ := fun p =>
    (prodBernoulli p).real {ω : BondConfig (Fin n) | ∀ a ∈ T, ¬ (openGraph ω).Reachable v a} * S o p with hg
  have hfc : Continuous f := (prodBernoulli_real_continuous _).mul (continuous_minForm T F v)
  have hgc : Continuous g := (prodBernoulli_real_continuous _).mul (continuous_minForm T F o)
  have hfg : ∀ p : Sym2 (Fin n) → unitInterval, (∀ e, 0 < p e ∧ p e < 1) → f p ≤ g p := by
    intro p hp
    obtain ⟨r', hr', hc'⟩ := AGloc.exists_rank_compat T (fun a => ∫ ω, F (openCluster ω a) ∂(prodBernoulli p))
    have key := h p hp r' hr' hc'
    rw [surplus_eq_minForm p T r' F v hr' hc', surplus_eq_minForm p T r' F o hr' hc'] at key
    exact key
  have hw := weights_le_of_forall_pos_lt_one hfc hgc hfg w
  simp only [hf, hg, hS] at hw
  rw [surplus_eq_minForm w T r F v hr hcompat, surplus_eq_minForm w T r F o hr hcompat]
  exact hw

/-- **`AdditiveGluing` from (S5) for non-degenerate weights only.**  `AdditiveGluing` follows from the surplus-transfer inequality (S5) restricted to
NON-DEGENERATE weight functions (all pair probabilities in `(0,1)`): close over degenerate weights by `surplusTransfer_of_nondegenerate`, then
apply `AGloc.additiveGluing_of_surplusTransfer` ((S5) ⟹ (GEN) ⟹ (AG-loc) ⟹ `AdditiveGluing`). [cite: KozmaNitzan2024, Conj. 1 (p. 3), Conj. 4 (p. 32)] -/
theorem additiveGluing_of_surplusTransfer_nondegenerate
    (hST : ∀ (n : ℕ) (p : Sym2 (Fin n) → unitInterval), (∀ e, 0 < p e ∧ p e < 1) →
      ∀ (T : Finset (Fin n)) (o v : Fin n) (F : Set (Fin n) → ℝ) (r : Fin n → ℕ),
      v ∉ T → (∀ S S' : Set (Fin n), S ⊆ S' → F S ≤ F S') → (∀ S, 0 ≤ F S) → Set.InjOn r ↑T →
      (∀ a ∈ T, ∀ a' ∈ T, r a < r a' →
        ∫ ω, F (openCluster ω a) ∂(prodBernoulli p) ≤ ∫ ω, F (openCluster ω a') ∂(prodBernoulli p)) →
      (prodBernoulli p).real ({ω : BondConfig (Fin n) | ∀ a ∈ T, ¬ (openGraph ω).Reachable v a} ∩ openConn o v) *
          surplus p T r F v ≤
        (prodBernoulli p).real {ω : BondConfig (Fin n) | ∀ a ∈ T, ¬ (openGraph ω).Reachable v a} * surplus p T r F o) :
    AdditiveGluing := by
  refine AGloc.additiveGluing_of_surplusTransfer fun n w T o v F r hvT hF hF0 hr hcompat => ?_
  exact surplusTransfer_of_nondegenerate T o v F
    (fun p hp r' hr' hc' => hST n p hp T o v F r' hvT hF hF0 hr' hc') w r hr hcompat

end Percolation.Continuity.CSH

end
