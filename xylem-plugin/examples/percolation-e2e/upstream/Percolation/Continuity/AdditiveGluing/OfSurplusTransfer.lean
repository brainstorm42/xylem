import Percolation.Continuity.AdditiveGluing.SurplusClosure
import Percolation.Util.Linter

/-!
# Additive gluing from the nonnegativity of the surplus-transfer margin

The peeling theorem delivers `0 ≤ CSH.surplusMargin p T r [] o v F` for NON-DEGENERATE `p` and DISTINCT named vertices
(`o ∉ T`, `v ∉ T`, `o ≠ v`).  The hypothesis `hST` (`AGloc.additiveGluing_of_surplusTransfer`) only assumes `v ∉ T`.  Here:
* `surplus_nonneg_of_mem` — for an observer INSIDE the relay set, `Sur_o(T) ≥ 0` (the first-in-rank relay of `o`'s cluster has mean `≤ m_o`;
  via the min-form `CSH.surplus_eq_minForm`);
* `surplusTransfer_nondegenerate_of_surplusMargin` — the `hST` inequality at a non-degenerate weight function from the decoy-free margin, all
  observer positions (`o = v`: equality; `o ∈ T`: the left side vanishes; else `CSH.surplusTransfer_of_surplusMargin_nil` with `μ(v ↮ T) > 0`);
* `additiveGluing_of_surplusMargin_nondegenerate` — THE FINAL REDUCTION: `AdditiveGluing` from
  `∀ non-degenerate p, ∀ T, o ∉ T, v ∉ T, o ≠ v, F monotone ≥ 0, r injective m(p)-compatible: 0 ≤ CSH.surplusMargin p T r [] o v F`
  (through `CSH.additiveGluing_of_surplusTransfer_nondegenerate`, i.e. the min-form closure over degenerate weights, and
  `AGloc.additiveGluing_of_surplusTransfer`).
[cite: KozmaNitzan2024, Conj. 1 (p. 3), Conj. 4 (p. 32)] [cite: GrimmettPercolation1999, §7.3 p. 162]
-/

noncomputable section

namespace Percolation.Continuity.CSH

open MeasureTheory Set
open Percolation.Literature.LatticeModels (prodBernoulli prodBernoulli_real_pos_of_nonempty)
open Percolation.Literature
open Percolation.Continuity.Statements
open scoped Classical

variable {n : ℕ}

/-- **An observer inside the relay set has nonnegative surplus**: for `o ∈ T` and an injective `m`-compatible rank,
`Sur_o(T) = m_o − E[min_{a ∈ C_o ∩ T} m_a] ≥ 0`. [cite: KozmaNitzan2024, Conj. 4 (p. 32)] -/
theorem surplus_nonneg_of_mem (w : Sym2 (Fin n) → unitInterval) (T : Finset (Fin n)) (r : Fin n → ℕ) (F : Set (Fin n) → ℝ)
    (o : Fin n) (ho : o ∈ T) (hr : Set.InjOn r ↑T)
    (hcompat : ∀ b ∈ T, ∀ b' ∈ T, r b < r b' →
      ∫ ω, F (openCluster ω b) ∂(prodBernoulli w) ≤ ∫ ω, F (openCluster ω b') ∂(prodBernoulli w)) :
    0 ≤ surplus w T r F o := by
  rw [surplus_eq_minForm w T r F o hr hcompat]
  set μ := prodBernoulli w with hμ
  set m : Fin n → ℝ := fun b => ∫ η, F (openCluster η b) ∂μ with hm
  have hmeas : ∀ S : Set (BondConfig (Fin n)), MeasurableSet S := fun _ => MeasurableSet.of_discrete
  -- `{o ↔ T}` is everything since `o ∈ T`
  have hU : (⋃ a ∈ T, (openConn o a : Set (BondConfig (Fin n)))) = univ := by
    refine eq_univ_of_forall fun ω => mem_iUnion₂.2 ⟨o, ho, ?_⟩
    exact SimpleGraph.Reachable.refl _
  have hoF : ∀ ω : BondConfig (Fin n), o ∈ T.filter fun b => ω ∈ (openConn o b : Set (BondConfig (Fin n))) :=
    fun ω => Finset.mem_filter.2 ⟨ho, SimpleGraph.Reachable.refl _⟩
  -- pointwise the integrand is `≥ F(C_o) − m_o`
  have hpt : ∀ ω : BondConfig (Fin n), F (openCluster ω o) - m o ≤ F (openCluster ω o) -
      (if h : (T.filter fun b => ω ∈ (openConn o b : Set (BondConfig (Fin n)))).Nonempty then
        (T.filter fun b => ω ∈ (openConn o b : Set (BondConfig (Fin n)))).inf' h m else 0) := by
    intro ω
    have hne : (T.filter fun b => ω ∈ (openConn o b : Set (BondConfig (Fin n)))).Nonempty := ⟨o, hoF ω⟩
    simp only [hne, dif_pos]
    linarith [Finset.inf'_le m (hoF ω)]
  have hint : ∀ (f : BondConfig (Fin n) → ℝ), Integrable f μ := fun f => Integrable.of_finite
  have h1 : ∫ ω, (F (openCluster ω o) - m o) ∂μ = 0 := by
    rw [integral_sub (hint _) (hint _), integral_const, probReal_univ, one_smul]
    simp [hm]
  rw [hU, Measure.restrict_univ]
  calc (0 : ℝ) = ∫ ω, (F (openCluster ω o) - m o) ∂μ := h1.symm
    _ ≤ _ := integral_mono (hint _) (hint _) hpt

/-- **(S5) at a non-degenerate weight function from the decoy-free (S5D) margin, every observer position.** If `v ∉ T` and, in
case `o ∉ T` and `o ≠ v`, the margin `Sur_o − p·Sur_v` is nonnegative, then `μ(v ↮ T, o ↔ v)·Sur_v(T) ≤ μ(v ↮ T)·Sur_o(T)`.
[cite: KozmaNitzan2024, Conj. 4 (p. 32)] -/
theorem surplusTransfer_nondegenerate_of_surplusMargin (p : Sym2 (Fin n) → unitInterval) (hp : ∀ e, 0 < p e ∧ p e < 1)
    (T : Finset (Fin n)) (o v : Fin n) (F : Set (Fin n) → ℝ) (r : Fin n → ℕ) (hvT : v ∉ T) (hr : Set.InjOn r ↑T)
    (hcompat : ∀ b ∈ T, ∀ b' ∈ T, r b < r b' →
      ∫ ω, F (openCluster ω b) ∂(prodBernoulli p) ≤ ∫ ω, F (openCluster ω b') ∂(prodBernoulli p))
    (hmarg : o ∉ T → o ≠ v → 0 ≤ surplusMargin p T r [] o v F) :
    (prodBernoulli p).real ({ω : BondConfig (Fin n) | ∀ a ∈ T, ¬ (openGraph ω).Reachable v a} ∩ openConn o v) *
        surplus p T r F v ≤
      (prodBernoulli p).real {ω : BondConfig (Fin n) | ∀ a ∈ T, ¬ (openGraph ω).Reachable v a} * surplus p T r F o := by
  set μ := prodBernoulli p with hμ
  by_cases hov : o = v
  · subst hov
    have hOO : (openConn o o : Set (BondConfig (Fin n))) = univ :=
      eq_univ_of_forall fun ω => SimpleGraph.Reachable.refl _
    rw [hOO, inter_univ]
  by_cases hoT : o ∈ T
  · have hempty : ({ω : BondConfig (Fin n) | ∀ a ∈ T, ¬ (openGraph ω).Reachable v a} ∩ openConn o v) = ∅ := by
      refine eq_empty_of_forall_notMem fun ω hω => ?_
      exact hω.1 o hoT (SimpleGraph.Reachable.symm hω.2)
    rw [hempty, measureReal_empty, zero_mul]
    exact mul_nonneg measureReal_nonneg (surplus_nonneg_of_mem p T r F o hoT hr hcompat)
  · have hne : ({ω : BondConfig (Fin n) | ∀ a ∈ (↑T : Set (Fin n)), ¬ (openGraph ω).Reachable v a}).Nonempty := by
      refine ⟨∅, fun a ha hreach => ?_⟩
      have hbot : openGraph (∅ : BondConfig (Fin n)) = ⊥ := by
        unfold openGraph; exact SimpleGraph.fromEdgeSet_empty
      rw [hbot, SimpleGraph.reachable_bot] at hreach
      exact hvT (hreach ▸ ha)
    have hpos := prodBernoulli_real_pos_of_nonempty hp hne
    exact surplusTransfer_of_surplusMargin_nil p T r o v F hpos (hmarg hoT hov)

/-- **THE FINAL REDUCTION: `AdditiveGluing` from the decoy-free (S5D) margin at non-degenerate weights.** If for every non-degenerate weight function,
every relay set `T`, observers `o ∉ T`, `v ∉ T`, `o ≠ v`, every monotone nonnegative `F` and every injective `m`-compatible rank `r` the margin
`CSH.surplusMargin p T r [] o v F = Sur_o(T) − μ(o↔v | v↮T)·Sur_v(T)` is nonnegative, then `AdditiveGluing` holds.
[cite: KozmaNitzan2024, Conj. 1 (p. 3), Conj. 4 (p. 32)] -/
theorem additiveGluing_of_surplusMargin_nondegenerate
    (h : ∀ (n : ℕ) (p : Sym2 (Fin n) → unitInterval), (∀ e, 0 < p e ∧ p e < 1) →
      ∀ (T : Finset (Fin n)) (o v : Fin n) (F : Set (Fin n) → ℝ) (r : Fin n → ℕ),
      o ∉ T → v ∉ T → o ≠ v → (∀ S S' : Set (Fin n), S ⊆ S' → F S ≤ F S') → (∀ S, 0 ≤ F S) → Set.InjOn r ↑T →
      (∀ a ∈ T, ∀ a' ∈ T, r a < r a' →
        ∫ ω, F (openCluster ω a) ∂(prodBernoulli p) ≤ ∫ ω, F (openCluster ω a') ∂(prodBernoulli p)) →
      0 ≤ surplusMargin p T r [] o v F) :
    AdditiveGluing :=
  additiveGluing_of_surplusTransfer_nondegenerate fun n p hp T o v F r hvT hF hF0 hr hcompat =>
    surplusTransfer_nondegenerate_of_surplusMargin p hp T o v F r hvT hr hcompat
      fun hoT hov => h n p hp T o v F r hoT hvT hov hF hF0 hr hcompat

end Percolation.Continuity.CSH

end
