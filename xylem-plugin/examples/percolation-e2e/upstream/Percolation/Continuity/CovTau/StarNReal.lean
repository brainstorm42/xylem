import Percolation.Continuity.AdditiveGluing.BystanderCluster
import Percolation.Continuity.CovTau.StarNPrelim
import Percolation.Literature.TwoSetConditionalAssociation
import Percolation.Util.Linter

/-!
# Lemma (★_N) of the conditioned covariance transfer COV(τ)

THE CHAIN. COV(τ): `Cov(Ψ(C_x), 1{o∈C_x} | x↮y) ≥ μ(o↔v | v↮x, v↮y)·Cov(Ψ(C_x), 1{v∈C_x} | x↮y)`; it
yields (S5)₂ (`SurplusTransfer.surplusTransfer_pair_of_covTransfer`), (GEN) for three relays
(`gen_triple_of_covTransfer`) and hence Kozma–Nitzan's Conjecture 1 for `|A| = 3`. Its proof has
three Lean pieces: Lemma (★_N) (THIS FILE; indicator form modulo BHK), the two-source induction A2
and the final combination.

LEMMA (★_N). Bond percolation with weights `p ∈ [0,1]` on a finite set `D` of pairs; vertices `x,
v`, a source set `N`, `Ψ` monotone nonnegative on edge sets, `C_x` the open EDGE cluster of `x`.
With `B(W) = Cov_{G∖W}(Ψ(C_x), 1{x↔v})` (the world `G ∖ W` = the pairs meeting `W` closed, `off W`)
and `Y(N) = E[ B(V(C_N)) ; x ∉ C_N ]`: `Y(N) · P(x ↮ v) ≤ P(x ↮ v, v ↮ N) · B(∅)`.

PROOF.  Let `ℱ_N` be the exploration σ-algebra of `C_N` — the decision tree
`SetClusterExploration.ttree` (Literature), which reveals exactly the pairs of `D` meeting `C_N`; conditional
expectations `cE` along it and the decision-tree Harris inequality for REAL monotone functions are in
`Continuity/LowerTail/TreeHarrisReal.lean` (`TreeHarris.treeHarris_real`, [Gladkov2024, Thm. 3.2]).
1. MARKOV (`splice_congr_of_not_mem_reached` / `splice_congr_of_mem_reached`): from `x ∉ C_N(K)` the hybrid `K →_{S_N(K)} K₂`
   looks like `off (C_N K) K₂`; from `x ∈ C_N(K)` it looks like `K`.  Hence (law of total covariance, tower `ED_cE`, symmetry
   `ED_mul_cE_comm`):  `B(∅) = Y(N) + Cov(ĝ, 1{x↔v})`, `ĝ = E[Ψ(C_x) | ℱ_N]`.
2. TREE-HARRIS: `Cov(ĝ, 1{x↔v} + Z) ≥ 0` with `Z = 1{x↮v}·1{v↔N}` (`{x↔v} ∪ {v↔N}` is increasing), and `Z` is
   `ℱ_N`-measurable (`hZloc`), so `Cov(ĝ, Z) = E[(Ψ − t) Z]`.
4. Linear combination.
[cite: Gladkov2024, Thm. 3.2 (p. 4)] [cite: VandenbergHaggstromKahn2005, Thm. 1.4 (p. 7), eq. (6)
(p. 4)]
-/

noncomputable section

namespace Percolation.Continuity

namespace CovTauStarN

open Finset MeasureTheory Percolation.Literature Percolation.Literature.DecisionTree
open Percolation.Literature.LatticeModels (prodBernoulli)
open SetClusterExploration TreeHarris
open scoped Classical

/-! ### Small `ED`/`cE` calculus on `D.powerset` -/

section EDCalc

variable {ι : Type*} [DecidableEq ι] (D : Finset ι) (p : ι → ℝ)

/-- Expectations of functions agreeing on the configurations `⊆ D` agree. [folklore] -/
theorem ED_congr_on {φ ψ : Finset ι → ℝ} (h : ∀ K ∈ D.powerset, φ K = ψ K) : ED D p φ = ED D p ψ :=
  Finset.sum_congr rfl fun K hK => by rw [h K hK]

/-- Differences. [folklore] -/
theorem ED_sub (φ ψ : Finset ι → ℝ) : ED D p (fun K => φ K - ψ K) = ED D p φ - ED D p ψ := by
  unfold ED; rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun _ _ => by ring

variable (Fm : Finset ι → Finset ι)

/-- Pull-out of a factor constant along the splices of configurations `⊆ D`. [folklore] -/
theorem cE_mul_of_local_on {Z : Finset ι → ℝ} {K : Finset ι}
    (hZ : ∀ K₂ ∈ D.powerset, Z (splice (Fm K) K K₂) = Z K) (φ : Finset ι → ℝ) :
    cE D p Fm (fun L => Z L * φ L) K = Z K * cE D p Fm φ K := by
  unfold cE
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun K₂ hK₂ => ?_
  show wtW D p K₂ * (Z (splice (Fm K) K K₂) * φ (splice (Fm K) K K₂)) = _
  rw [hZ K₂ hK₂]; ring

/-- `cE` of a conditional expectation is itself (self-determined `Fm`). [cite: Gladkov2024, Def. 2.4] -/
theorem cE_cE (hF : SelfDetermined Fm) (φ : Finset ι → ℝ) (K : Finset ι) :
    cE D p Fm (cE D p Fm φ) K = cE D p Fm φ K := by
  have h := cE_mul_of_local D p Fm (Z := cE D p Fm φ) (cE_local D p hF φ) (fun _ => (1 : ℝ)) K
  simp only [mul_one] at h
  rw [h, cE_const, mul_one]

end EDCalc

/-! ### BHK's Theorem 1.4 (two clusters) in finitary form on the coordinates `D` -/

section BHK14

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `{v ↔ N}` read on the edge cluster of `v`: `v ∈ N` or some edge of `C_v` contains a vertex of `N`. [folklore] -/
theorem nr_eq_ite (N : Finset V) (v : V) (K : Finset (Sym2 V)) :
    nr N v K = if (v ∈ N ∨ ∃ e ∈ openEdgeCluster (↑K : Set (Sym2 V)) v, ∃ s ∈ N, s ∈ e) then 1 else 0 := by
  unfold nr ind
  have key : (∃ s ∈ N, (openGraph (↑K : Set (Sym2 V))).Reachable s v) ↔
      (v ∈ N ∨ ∃ e ∈ openEdgeCluster (↑K : Set (Sym2 V)) v, ∃ s ∈ N, s ∈ e) := by
    constructor
    · rintro ⟨s, hs, hsv⟩
      by_cases hsv' : s = v
      · exact Or.inl (hsv' ▸ hs)
      · right
        obtain ⟨q⟩ := hsv
        cases q with
        | nil => exact absurd rfl hsv'
        | @cons _ u _ hadj q' =>
            have hadj2 := hadj
            rw [openGraph_adj] at hadj2
            refine ⟨s(s, u), ?_, s, hs, Sym2.mem_mk_left s u⟩
            rw [mem_openEdgeCluster_iff]
            refine ⟨hadj2.1, by rw [Sym2.mk_isDiag_iff]; exact hadj2.2, fun t ht => ?_⟩
            have hvs : (openGraph (↑K : Set (Sym2 V))).Reachable v s := (hadj.reachable.trans ⟨q'⟩).symm
            rcases Sym2.mem_iff.1 ht with rfl | rfl
            · exact hvs
            · exact ⟨q'.reverse⟩
    · rintro (hv | ⟨e, he, s, hs, hse⟩)
      · exact ⟨v, hv, SimpleGraph.Reachable.refl _⟩
      · rw [mem_openEdgeCluster_iff] at he
        exact ⟨s, hs, (he.2.2 s hse).symm⟩
  by_cases h : ∃ s ∈ N, (openGraph (↑K : Set (Sym2 V))).Reachable s v
  · rw [if_pos (show K ∈ {L : Finset (Sym2 V) | ∃ s ∈ N, (openGraph (↑L : Set (Sym2 V))).Reachable s v} from h),
      if_pos (key.1 h)]
  · rw [if_neg (show K ∉ {L : Finset (Sym2 V) | ∃ s ∈ N, (openGraph (↑L : Set (Sym2 V))).Reachable s v} from h),
      if_neg (fun h' => h (key.2 h'))]

end BHK14

end CovTauStarN

end Percolation.Continuity

end
