import Percolation.Literature.LonePortSum
import Percolation.Util.Linter

/-!
# Separation-family positive correlation given `{s ↮ X}`, and lone-port sums for any number of ports — corollaries of van den Berg–Häggström–Kahn 2006, Thm. 1.3

Bond percolation with arbitrary edge probabilities on a
finite vertex type `V` (`μ = prodBernoulli w` on `BondConfig V = Set (Sym2 V)`); `C_s` the open edge
cluster of `s` (`openEdgeCluster`), `W̄ = {e | ∃ v ∈ e, v = s ∨ ∃ e' ∈ W, v ∈ e'}` the pairs meeting
`{s} ∪ V(W)` (as in `TwoClusterConditionalAssociationProofs.lean`), `D_X = {s ↮ x ∀ x ∈ X}`.

BHK's Theorem 1.3 [VandenbergHaggstromKahn2005, Thm. 1.3 p. 6; here the proved statement
`BHK2006_clusterConditionalPositiveAssociation`] says that given `D_X` the cluster `C_s` is
positively associated; their proof of Theorems 1.4/1.5 (pp. 7–8, display (10)) conditions on `{C_s =
W}`, where the configuration off `W̄` is a fresh product configuration and every monotone statistic
of it has a conditional mean monotone in `W`. The file `LonePortSum.lean` ran this printed argument
for an INCREASING statistic of one separated cluster `C_t`, `t ∈ X`. This file runs it for the
DECREASING statistic "the pairs `(x_i, y_i)`, `x_i ∈ X`, are all separated" (positive correlation),
and derives the lone-port sums of the hull-port line for an arbitrary finite port set. Everything is
proved; no definition is introduced:

* `BHK2006.sum_cond_cluster_sdiff` — display (10) without a separation event: for any `K`,
  `E[K(C_s, ω ∖ W̄(C_s))] = E[ Σ_η weight(η) K(C_s, η ∖ W̄(C_s)) ]` (block independence on `W̄`);
* `LonePortSumGeneral.reachable_sdiff_bar_iff` — on `D_X`, connections from `x ∈ X` are read in
  the configuration off `W̄(C_s)`;
* `setSep_offCluster_posCorrelation` / `setSep_offCluster_negCorrelation` — the same for an
  ARBITRARY antitone / monotone statistic `G` of the configuration with the locality property
  `G(ω ∖ W̄(C_s ω)) = G(ω)` on `D_X` (positive / negative correlation with increasing `F(C_s)`);

`STAR_3` and the 20 three-port menus are the theorems of `LonePortSum.lean`; `STAR_m`, `m ≥ 4`, and
the `3^m − m − 1` `m`-port menus (checked numerically beforehand: 0 violations in 765 480 exact
four-port instances, equality locus ZERO ∪ GLUED ∪ SINGLEPORT) are proved here.
Not in print; derived here from the printed BHK argument.

## References

* J. van den Berg, O. Häggström, J. Kahn, *Some conditional correlation inequalities for percolation and
  related processes*, Random Structures Algorithms 29 (2006) 417–435: Thm. 1.3 (p. 6), proof of
  Thm. 1.5 (pp. 7–8, display (10)). [VandenbergHaggstromKahn2005]
* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, Thm. (2.4) p. 34 (Harris–FKG). [GrimmettPercolation1999]
-/

noncomputable section

open MeasureTheory Set
open Percolation.Literature.LatticeModels

namespace Percolation.Literature

variable {V : Type*}

/-! ### Display (10) of BHK without a separation event -/

namespace BHK2006

open scoped Classical
open DecisionTree (ind ind_of_mem ind_of_not_mem ind_nonneg)

/-- **Block independence on `W̄`** (BHK's display (10) and the paragraph following it, with no
separation event and an arbitrary statistic of the configuration off `W̄`): for any `K`,
`Σ_ω weight(ω) K(C_s(ω), ω ∖ W̄(C_s ω)) = Σ_ω weight(ω) Σ_η weight(η) K(C_s(ω), η ∖ W̄(C_s ω))`
— given `{C_s = W}` (a cylinder event on `W̄`) the coordinates off `W̄` are fresh.
[cite: VandenbergHaggstromKahn2005, §1 pp. 7–8, display (10) and the paragraph following it —
corollary, derived in this file] -/
theorem sum_cond_cluster_sdiff [Fintype V] (w : Sym2 V → ℝ) (hm : ∑ ω, weight w ω = 1) (s : V)
    (K : Set (Sym2 V) → Set (Sym2 V) → ℝ) :
    ∑ ω, weight w ω * K (openEdgeCluster ω s)
        (ω \ {e | ∃ v ∈ e, v = s ∨ ∃ e' ∈ openEdgeCluster ω s, v ∈ e'}) =
      ∑ ω, weight w ω * ∑ η, weight w η * K (openEdgeCluster ω s)
        (η \ {e | ∃ v ∈ e, v = s ∨ ∃ e' ∈ openEdgeCluster ω s, v ∈ e'}) := by
  -- the identity on each event `{C_s = W}`: block Fubini with the block `A = W̄`
  have key : ∀ W : Set (Sym2 V),
      ∑ ω, (if openEdgeCluster ω s = W then
          weight w ω * K W (ω \ {e | ∃ v ∈ e, v = s ∨ ∃ e' ∈ W, v ∈ e'}) else 0) =
      ∑ ω, (if openEdgeCluster ω s = W then
          weight w ω * ∑ η, weight w η * K W (η \ {e | ∃ v ∈ e, v = s ∨ ∃ e' ∈ W, v ∈ e'})
        else 0) := by
    intro W
    set A : Set (Sym2 V) := {e | ∃ v ∈ e, v = s ∨ ∃ e' ∈ W, v ∈ e'} with hA
    set Φ : Set (Sym2 V) → Set (Sym2 V) → ℝ := fun ζ η =>
      if openEdgeCluster ζ s = W then K W (η \ A) else 0 with hΦ
    have hsd : ∀ ω : Set (Sym2 V), (ω \ A) \ A = ω \ A := fun ω => by
      rw [Set.sdiff_sdiff, Set.union_self]
    have h1 : ∀ ω, (if openEdgeCluster ω s = W then weight w ω * K W (ω \ A) else 0) =
        weight w ω * Φ (ω ∩ A) (ω \ A) := by
      intro ω
      simp only [hΦ, hA, openEdgeCluster_inter_bar_eq_iff]
      split_ifs with hW
      · rw [← hA, hsd]
      · rw [mul_zero]
    have h2 : ∀ ω, weight w ω * ∑ ω', weight w ω' * Φ (ω ∩ A) (ω' \ A) =
        (if openEdgeCluster ω s = W then
          weight w ω * ∑ η, weight w η * K W (η \ A) else 0) := by
      intro ω
      simp only [hΦ, hA, openEdgeCluster_inter_bar_eq_iff]
      split_ifs with hW
      · rw [← hA]
        refine congrArg (weight w ω * ·) (Finset.sum_congr rfl fun η _ => ?_)
        rw [hsd]
      · simp
    calc ∑ ω, (if openEdgeCluster ω s = W then weight w ω * K W (ω \ A) else 0)
        = (∑ ω, weight w ω) * ∑ ω, weight w ω * Φ (ω ∩ A) (ω \ A) := by
          rw [hm, one_mul]; exact Finset.sum_congr rfl fun ω _ => h1 ω
      _ = ∑ ω, weight w ω * ∑ ω', weight w ω' * Φ (ω ∩ A) (ω' \ A) := blockFubini w A Φ
      _ = _ := Finset.sum_congr rfl fun ω _ => h2 ω
  -- sum over `W`
  calc ∑ ω, weight w ω * K (openEdgeCluster ω s)
        (ω \ {e | ∃ v ∈ e, v = s ∨ ∃ e' ∈ openEdgeCluster ω s, v ∈ e'})
      = ∑ ω, ∑ W, (if openEdgeCluster ω s = W then
          weight w ω * K W (ω \ {e | ∃ v ∈ e, v = s ∨ ∃ e' ∈ W, v ∈ e'}) else 0) :=
        Finset.sum_congr rfl fun ω _ => (Fintype.sum_ite_eq (openEdgeCluster ω s)
          fun W => weight w ω * K W (ω \ {e | ∃ v ∈ e, v = s ∨ ∃ e' ∈ W, v ∈ e'})).symm
    _ = ∑ W, ∑ ω, (if openEdgeCluster ω s = W then
          weight w ω * K W (ω \ {e | ∃ v ∈ e, v = s ∨ ∃ e' ∈ W, v ∈ e'}) else 0) :=
        Finset.sum_comm
    _ = ∑ W, ∑ ω, (if openEdgeCluster ω s = W then
          weight w ω * ∑ η, weight w η * K W (η \ {e | ∃ v ∈ e, v = s ∨ ∃ e' ∈ W, v ∈ e'})
          else 0) := Finset.sum_congr rfl fun W _ => key W
    _ = ∑ ω, ∑ W, (if openEdgeCluster ω s = W then
          weight w ω * ∑ η, weight w η * K W (η \ {e | ∃ v ∈ e, v = s ∨ ∃ e' ∈ W, v ∈ e'})
          else 0) := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun ω _ => Fintype.sum_ite_eq (openEdgeCluster ω s)
          fun W => weight w ω * ∑ η, weight w η *
            K W (η \ {e | ∃ v ∈ e, v = s ∨ ∃ e' ∈ W, v ∈ e'})

end BHK2006

/-! ### Locality of the separated ports' connections -/

namespace LonePortSumGeneral

open BHK2006

/-- **Connections of a separated vertex are read off `W̄`**: if `s ↮ x`, then for every `y`,
`x ↔ y` in `ω` iff `x ↔ y` in the configuration `ω ∖ W̄(C_s ω)` with the pairs meeting the cluster
of `s` deleted (an open path from `x` meets no such pair).
[cite: VandenbergHaggstromKahn2005, §1 p. 8 (proof of Thm. 1.5) — corollary, derived in this file] -/
theorem reachable_sdiff_bar_iff {s x : V} {ω : BondConfig V} (hx : ¬ (openGraph ω).Reachable s x)
    (y : V) :
    (openGraph (ω \ {e | ∃ v ∈ e, v = s ∨ ∃ e' ∈ openEdgeCluster ω s, v ∈ e'})).Reachable x y ↔
      (openGraph ω).Reachable x y := by
  refine ⟨fun h => h.mono (openGraph_mono Set.sdiff_subset), fun h => ?_⟩
  have hxs : ¬ (x = s ∨ ∃ e ∈ openEdgeCluster ω s, x ∈ e) := fun h' =>
    hx ((reachable_iff_exists_mem_openEdgeCluster ω s x).2 h')
  have hC := openEdgeCluster_eq_sdiff_bar (rfl : openEdgeCluster ω s = openEdgeCluster ω s) hxs
  rw [reachable_iff_exists_mem_openEdgeCluster, ← hC, ← reachable_iff_exists_mem_openEdgeCluster]
  exact h

end LonePortSumGeneral

/-! ### The general off-cluster statistic (both signs) -/

open LonePortSum LonePortSumGeneral BHK2006 DecisionTree in
/-- **Cluster / off-cluster correlation given `{s ↮ X}`, general form** (BHK 2006, the argument of pp.
 7–8 for an ARBITRARY statistic `G` of the configuration that, on `D_X = {s ↮ X}`, is read off the
 coordinates outside `W̄(C_s)` — "every monotone statistic of the fresh configuration off `W̄` has a
 conditional mean monotone in `W`"). For `s ∉ X`, `F` monotone (applied to `C_s`), and `G :
 BondConfig V → ℝ` with the LOCALITY property `G(ω ∖ W̄(C_s ω)) = G(ω)` for every `ω ∈ D_X`: (a,
 this theorem) if `G` is ANTItone (decreasing in the configuration) then `(∫_{D_X} F(C_s) dμ) ·
 (∫_{D_X} G dμ) ≤ μ(D_X) · ∫_{D_X} F(C_s) G dμ` (positive correlation); (b,
 `setSep_offCluster_negCorrelation`) if `G` is monotone the inequality is reversed. Proof of (a):
 `∫_{D_X} F(C_s) G = ∫_{D_X} F(C_s) ψ(C_s)` with `ψ(W) = Σ_η weight(η) G(η ∖ W̄)`
 (`sum_cond_cluster_sdiff` + locality), `ψ` increasing (`G` antitone, `W̄` increasing), then Theorem
 1.3 for the increasing pair (`F`, `ψ`). Not in print in this form; derived here. [cite:
 VandenbergHaggstromKahn2005, Thm. 1.3 (p. 6) and pp. 7–8 — corollary, derived in this file]
-/
theorem setSep_offCluster_posCorrelation [Fintype V] (w : Sym2 V → unitInterval) (s : V) (X : Set V)
    (hs : s ∉ X) (F : Set (Sym2 V) → ℝ) (hF : Monotone F) (G : BondConfig V → ℝ) (hG : Antitone G)
    (hloc : ∀ ω : BondConfig V, (∀ x ∈ X, ¬ (openGraph ω).Reachable s x) →
      G (ω \ {e | ∃ v ∈ e, v = s ∨ ∃ e' ∈ openEdgeCluster ω s, v ∈ e'}) = G ω) :
    (∫ ω in {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x},
        F (openEdgeCluster ω s) ∂(prodBernoulli w)) *
      (∫ ω in {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x},
        G ω ∂(prodBernoulli w)) ≤
    (prodBernoulli w).real {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x} *
      ∫ ω in {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x},
        F (openEdgeCluster ω s) * G ω ∂(prodBernoulli w) := by
  classical
  set DX : Set (BondConfig V) := {ω | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x} with hDX
  set w' : Sym2 V → ℝ := fun e => (w e : ℝ) with hw'
  have hw0 : ∀ e, 0 ≤ w' e := fun e => (w e).2.1
  have hw1 : ∀ e, w' e ≤ 1 := fun e => (w e).2.2
  have hm : ∑ ω, weight w' ω = 1 := by
    have h1 := integral_prodBernoulli_eq_sum w fun _ => (1 : ℝ)
    simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at h1
    exact h1.symm
  -- `1_{D_X} = NX(C_s)`
  set NX : Set (Sym2 V) → ℝ := fun C => if ∀ x ∈ X, ¬ (x = s ∨ ∃ e ∈ C, x ∈ e) then 1 else 0
    with hNX
  have hind : ∀ ω : BondConfig V, ind DX ω = NX (openEdgeCluster ω s) := by
    intro ω
    by_cases hω : ω ∈ DX
    · have hω' : ∀ x ∈ X, ¬ (openGraph ω).Reachable s x := hω
      have h1 : ∀ x ∈ X, ¬ (x = s ∨ ∃ e ∈ openEdgeCluster ω s, x ∈ e) := fun x hx h =>
        hω' x hx ((reachable_iff_exists_mem_openEdgeCluster ω s x).2 h)
      rw [ind_of_mem hω, hNX]
      simp only [if_pos h1]
    · have hω' : ∃ x ∈ X, (openGraph ω).Reachable s x := by
        by_contra hcon
        exact hω fun x hx hr => hcon ⟨x, hx, hr⟩
      obtain ⟨x, hx, hr⟩ := hω'
      have h1 : ¬ ∀ x ∈ X, ¬ (x = s ∨ ∃ e ∈ openEdgeCluster ω s, x ∈ e) := fun h =>
        h x hx ((reachable_iff_exists_mem_openEdgeCluster ω s x).1 hr)
      rw [ind_of_not_mem hω, hNX]
      simp only [if_neg h1]
  -- the pointwise identity `G(ω) 1_{D_X}(ω) = NX(C_s ω) · G(ω ∖ W̄(C_s ω))`
  have hptw : ∀ ω : BondConfig V, G ω * ind DX ω =
      NX (openEdgeCluster ω s) *
        G (ω \ {e | ∃ v ∈ e, v = s ∨ ∃ e' ∈ openEdgeCluster ω s, v ∈ e'}) := by
    intro ω
    rw [hind ω]
    by_cases hω : ω ∈ DX
    · rw [hloc ω hω, mul_comm]
    · have h0 : NX (openEdgeCluster ω s) = 0 := by rw [← hind ω, ind_of_not_mem hω]
      rw [h0, zero_mul, mul_zero]
  -- `ψ(W) = E[G(η ∖ W̄)]`; it is increasing in `W`
  set ψ : Set (Sym2 V) → ℝ := fun W => ∑ η, weight w' η *
      G (η \ {e | ∃ v ∈ e, v = s ∨ ∃ e' ∈ W, v ∈ e'}) with hψ
  have hψmono : Monotone ψ := by
    intro W W' hWW'
    refine Finset.sum_le_sum fun η _ => mul_le_mul_of_nonneg_left ?_ (weight_nonneg hw0 hw1 η)
    exact hG (Set.sdiff_subset_sdiff_right (bar_mono s hWW'))
  -- display (10) for `K = F · NX · G` and for `K = NX · G`
  have e1 := sum_cond_cluster_sdiff w' hm s (fun C ξ => F C * NX C * G ξ)
  have e2 := sum_cond_cluster_sdiff w' hm s (fun C ξ => NX C * G ξ)
  have i1 : ∫ ω in DX, F (openEdgeCluster ω s) * G ω ∂(prodBernoulli w) =
      ∫ ω in DX, F (openEdgeCluster ω s) * ψ (openEdgeCluster ω s) ∂(prodBernoulli w) := by
    rw [setIntegral_eq_sum w DX, setIntegral_eq_sum w DX]
    have lhs : ∑ ω, weight w' ω * (F (openEdgeCluster ω s) * G ω * ind DX ω) =
        ∑ ω, weight w' ω * ((fun C ξ => F C * NX C * G ξ) (openEdgeCluster ω s)
          (ω \ {e | ∃ v ∈ e, v = s ∨ ∃ e' ∈ openEdgeCluster ω s, v ∈ e'})) :=
      Finset.sum_congr rfl fun ω _ => by simp only; rw [mul_assoc, hptw ω]; ring
    rw [lhs, e1]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [hind ω, hψ]
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun η _ => ?_
    ring
  have i2 : ∫ ω in DX, G ω ∂(prodBernoulli w) =
      ∫ ω in DX, ψ (openEdgeCluster ω s) ∂(prodBernoulli w) := by
    rw [setIntegral_eq_sum w DX, setIntegral_eq_sum w DX]
    have lhs : ∑ ω, weight w' ω * (G ω * ind DX ω) =
        ∑ ω, weight w' ω * ((fun C ξ => NX C * G ξ) (openEdgeCluster ω s)
          (ω \ {e | ∃ v ∈ e, v = s ∨ ∃ e' ∈ openEdgeCluster ω s, v ∈ e'})) :=
      Finset.sum_congr rfl fun ω _ => by simp only; rw [hptw ω]
    rw [lhs, e2]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [hind ω, hψ]
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun η _ => ?_
    ring
  have h13 := BHK2006_clusterConditionalPositiveAssociation_holds V w s X F ψ hF hψmono hs
  rw [i2, i1]
  exact h13

open LonePortSum LonePortSumGeneral BHK2006 DecisionTree in
/-- **Cluster / off-cluster correlation given `{s ↮ X}`, general form (b): an INCREASING off-cluster
 statistic is negatively correlated with the cluster of `s`.** For `s ∉ X`, `F` monotone, `G :
 BondConfig V → ℝ` monotone with the locality property `G(ω ∖ W̄(C_s ω)) = G(ω)` on `D_X`: `μ(D_X) ·
 ∫_{D_X} F(C_s) G dμ ≤ (∫_{D_X} F(C_s) dμ) · (∫_{D_X} G dμ)`. Proof: (a) applied to `−G`. [cite:
 VandenbergHaggstromKahn2005, Thm. 1.3 (p. 6) and pp. 7–8 — corollary, derived in this file]
-/
theorem setSep_offCluster_negCorrelation [Fintype V] (w : Sym2 V → unitInterval) (s : V) (X : Set V)
    (hs : s ∉ X) (F : Set (Sym2 V) → ℝ) (hF : Monotone F) (G : BondConfig V → ℝ) (hG : Monotone G)
    (hloc : ∀ ω : BondConfig V, (∀ x ∈ X, ¬ (openGraph ω).Reachable s x) →
      G (ω \ {e | ∃ v ∈ e, v = s ∨ ∃ e' ∈ openEdgeCluster ω s, v ∈ e'}) = G ω) :
    (prodBernoulli w).real {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x} *
      (∫ ω in {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x},
        F (openEdgeCluster ω s) * G ω ∂(prodBernoulli w)) ≤
    (∫ ω in {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x},
        F (openEdgeCluster ω s) ∂(prodBernoulli w)) *
      ∫ ω in {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x},
        G ω ∂(prodBernoulli w) := by
  have h := setSep_offCluster_posCorrelation w s X hs F hF (fun ω => -G ω)
    (fun _ _ hab => neg_le_neg (hG hab)) (fun ω hω => by simp only [hloc ω hω])
  have e1 : ∫ ω in {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x},
      (fun ω => -G ω) ω ∂(prodBernoulli w) =
      -∫ ω in {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x}, G ω ∂(prodBernoulli w) := by
    simp only [integral_neg]
  have e2 : ∫ ω in {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x},
      F (openEdgeCluster ω s) * (fun ω => -G ω) ω ∂(prodBernoulli w) =
      -∫ ω in {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x},
        F (openEdgeCluster ω s) * G ω ∂(prodBernoulli w) := by
    rw [← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [mul_neg]
  rw [e1, e2] at h
  linarith [h]

end Percolation.Literature

end
