import Percolation.Literature.KozmaNitzanClusterPropertyReal
import Percolation.Literature.TwoClusterGibbsCovariance
import Percolation.Util.Linter

/-!
# The conditioned covariance transfer for the Kozma–Nitzan functional `F(C(b)) − F(C(a))` from the transfer for a monotone function of the owner's edge cluster

The conditioned covariance transfer COV(τ) (`CovTau.covTau`, `Continuity/CovTau/OfTA.lean`) is a statement about a MONOTONE
function `f` of the open edge cluster `C_b` of the owner `b`, in the world `D = {b ↮ a}`:
`μ(v↮b, v↮a, v↔o) · cov_D(f(C_b), 1{b↔v}) ≤ μ(v↮b, v↮a) · cov_D(f(C_b), 1{b↔o})`.
The two-relay surplus transfer (`SurplusTransfer.surplusTransfer_pair_of_covTransfer`, `Continuity/LowerTail/SurplusTransferPairOfCov.lean`)
consumes the same inequality for the non-`σ(C_b)`-measurable integrand `h = F(C(b)) − F(C(a))` (`F` monotone on vertex sets,
`C(x)` the open vertex cluster). This file supplies the projection: on `D` the conditional mean `E[F(C(a)) | C_b = K]` is fresh
percolation on `G` minus the pairs meeting `{b} ∪ V(K)` (van den Berg–Häggström–Kahn, Lemma 2.4), a DECREASING function of `K`,
so `h` projects to the monotone edge-cluster functional `f(K) = F({b} ∪ V(K)) − E[F(C(a)) | C_b = K]`, and the three integrals
(over `D`, `D ∩ {b↔v}`, `D ∩ {b↔o}` — all `σ(C_b)`-events) are unchanged.

* `CovTau.tower_clusterFun` — `∫_{D ∩ {C_b ∈ 𝒮}} F(C(a)) = ∫_{D ∩ {C_b ∈ 𝒮}} E[F(C(a)) | C_b]` (Lemma 2.4, measure form);
* `CovTau.antitone_condMean`, `CovTau.monotone_projFun` — monotonicity of the projection;
* `CovTau.setIntegral_sub_eq_projFun` — `∫ h = ∫ f(C_b)` on `σ(C_b)`-events inside `D`;
* `CovTau.covTransfer_of_covTau` — COV(τ) for `f` ⟹ the hypothesis `hCOV` of the two-relay surplus transfer verbatim.
[cite: VandenbergHaggstromKahn2005, §2.1 Lemma 2.4 (p. 10), §2.2 p. 12] [cite: KozmaNitzan2024, Conj. 4 (p. 32), §5.1 (p. 31)]
-/

noncomputable section

namespace Percolation.Continuity

open MeasureTheory Set Percolation.Literature.LatticeModels Percolation.Literature
open scoped Classical
open KNPreFKG BHK2006 DecisionTree

namespace CovTau

variable {V : Type*} [Fintype V]

/-- **Tower property along `σ(C_b)` on `{b ↮ a}` (vdBHK Lemma 2.4).** For any `F` on vertex sets and any
of edge sets: `∫_{D ∩ {C_b ∈ 𝒮}} F(C(a)) dμ = ∫_{D ∩ {C_b ∈ 𝒮}} g(C_b) dμ` with `D = {b ↮ a}` and
`g(K) = ∫ F(C_a(η ∖ B(K))) dμ(η)`, `B(K)` the pairs meeting `{b} ∪ V(K)` — given `C_b = K` (inside `D`) the cluster
of `a` is the cluster of `a` for fresh percolation on `G` minus the pairs meeting the cluster of `b`.
[cite: VandenbergHaggstromKahn2005, §2.1 Lemma 2.4 (p. 10)] -/
theorem tower_clusterFun (w : Sym2 V → unitInterval) (a b : V) (F : Set V → ℝ) (𝒮 : Set (Set (Sym2 V))) :
    ∫ ω in {ω : BondConfig V | ¬ (openGraph ω).Reachable b a} ∩ {ω | openEdgeCluster ω b ∈ 𝒮},
        F (openCluster ω a) ∂(prodBernoulli w) =
      ∫ ω in {ω : BondConfig V | ¬ (openGraph ω).Reachable b a} ∩ {ω | openEdgeCluster ω b ∈ 𝒮},
        (∫ η, F (openCluster (η \ barOf {b} (openEdgeCluster ω b)) a) ∂(prodBernoulli w))
          ∂(prodBernoulli w) := by
  classical
  set μ := prodBernoulli w with hμ
  set D : Set (BondConfig V) := {ω : BondConfig V | ¬ (openGraph ω).Reachable b a} with hD
  have hDiff : ∀ ω : BondConfig V, ω ∈ D ↔ ∀ s ∈ ({b} : Set V), ∀ t ∈ ({a} : Set V),
      ¬ (openGraph ω).Reachable s t := by
    intro ω; simp [hD]
  have hm : ∑ ω : Set (Sym2 V), weight (fun e => (w e : ℝ)) ω = 1 := by
    have h1 := integral_prodBernoulli_eq_sum w fun _ => (1 : ℝ)
    simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at h1
    exact h1.symm
  -- the two-cluster identity with `H(K, L) = 1_𝒮(K) · F(V_a(L))`
  have key := set_sum_cond_cluster (fun e => (w e : ℝ)) hm ({b} : Set V) ({a} : Set V)
    (fun K L => ind 𝒮 K * F {z | z = a ∨ ∃ e ∈ L, z ∈ e}) hDiff
  simp only [setCl_singleton] at key
  -- rewrite both sides as sums
  have hvert : ∀ η : BondConfig V, F {z | z = a ∨ ∃ e ∈ openEdgeCluster η a, z ∈ e} = F (openCluster η a) :=
    fun η => clusterFun_openEdgeCluster F η a
  simp only [hvert] at key
  rw [← integral_indicator (MeasurableSet.of_discrete), ← integral_indicator (MeasurableSet.of_discrete),
    integral_prodBernoulli_eq_sum, integral_prodBernoulli_eq_sum]
  have hL : ∀ ω : BondConfig V, (D ∩ {ω | openEdgeCluster ω b ∈ 𝒮}).indicator
      (fun ω => F (openCluster ω a)) ω = ind 𝒮 (openEdgeCluster ω b) * F (openCluster ω a) * ind D ω := by
    intro ω
    by_cases h1 : ω ∈ D
    · by_cases h2 : openEdgeCluster ω b ∈ 𝒮
      · rw [indicator_of_mem (show ω ∈ D ∩ {ω | openEdgeCluster ω b ∈ 𝒮} from ⟨h1, h2⟩),
          ind_of_mem h1, ind_of_mem h2]; ring
      · rw [indicator_of_notMem (fun h => h2 h.2), ind_of_not_mem h2]; ring
    · rw [indicator_of_notMem (fun h => h1 h.1), ind_of_not_mem h1]; ring
  have hR : ∀ ω : BondConfig V, (D ∩ {ω | openEdgeCluster ω b ∈ 𝒮}).indicator
      (fun ω => ∫ η, F (openCluster (η \ barOf {b} (openEdgeCluster ω b)) a) ∂μ) ω =
      (∑ η : Set (Sym2 V), weight (fun e => (w e : ℝ)) η *
        (ind 𝒮 (openEdgeCluster ω b) * F (openCluster (η \ barOf {b} (openEdgeCluster ω b)) a))) *
        ind D ω := by
    intro ω
    have hint : ∫ η, F (openCluster (η \ barOf {b} (openEdgeCluster ω b)) a) ∂μ =
        ∑ η : Set (Sym2 V), weight (fun e => (w e : ℝ)) η *
          F (openCluster (η \ barOf {b} (openEdgeCluster ω b)) a) := integral_prodBernoulli_eq_sum w _
    by_cases h1 : ω ∈ D
    · by_cases h2 : openEdgeCluster ω b ∈ 𝒮
      · rw [indicator_of_mem (show ω ∈ D ∩ {ω | openEdgeCluster ω b ∈ 𝒮} from ⟨h1, h2⟩),
          ind_of_mem h1, ind_of_mem h2, hint]
        simp only [one_mul, mul_one]
      · rw [indicator_of_notMem (fun h => h2 h.2), ind_of_not_mem h2]
        simp only [zero_mul, mul_zero, Finset.sum_const_zero]
    · rw [indicator_of_notMem (fun h => h1 h.1), ind_of_not_mem h1]; ring
  simp only [hL, hR]
  exact key

/-- **`E[F(C_a) | C_b = ·]` is decreasing** for `F` monotone on vertex sets: `K ⊆ K'` deletes more pairs, and the cluster of
`a` in the thinned configuration can only shrink. [cite: VandenbergHaggstromKahn2005, §2.2 p. 12 (`X^i ⊆ Y^i` since `Y^{i-1} ⊆ X^{i-1}`)] -/
theorem antitone_condMean (w : Sym2 V → unitInterval) (a b : V) (F : Set V → ℝ)
    (hF : ∀ S T : Set V, S ⊆ T → F S ≤ F T) :
    Antitone fun K : Set (Sym2 V) => ∫ η, F (openCluster (η \ barOf {b} K) a) ∂(prodBernoulli w) := by
  intro K K' hKK'
  refine integral_mono (Integrable.of_finite) (Integrable.of_finite) fun η => ?_
  have hsub : η \ barOf {b} K' ⊆ η \ barOf {b} K := fun e he => ⟨he.1, fun h' => he.2 (barOf_mono {b} hKK' h')⟩
  exact hF _ _ (openCluster_mono hsub a)

/-- The Kozma–Nitzan functional projected on `σ(C_b)`: `f(K) = F({b} ∪ V(K)) − E[F(C_a) | C_b = K]` is a MONOTONE function
of the owner's edge cluster. [cite: KozmaNitzan2024, §5.1 (p. 31)] [cite: VandenbergHaggstromKahn2005, §2.2 p. 12] -/
theorem monotone_projFun (w : Sym2 V → unitInterval) (a b : V) (F : Set V → ℝ)
    (hF : ∀ S T : Set V, S ⊆ T → F S ≤ F T) :
    Monotone fun K : Set (Sym2 V) => F {z | z = b ∨ ∃ e ∈ K, z ∈ e} -
      ∫ η, F (openCluster (η \ barOf {b} K) a) ∂(prodBernoulli w) :=
  fun _ _ hKK' => sub_le_sub (monotone_clusterFun b F hF hKK') (antitone_condMean w a b F hF hKK')

/-- **The projection identity**: on `D ∩ {C_b ∈ 𝒮}` (`D = {b ↮ a}`),
`∫ (F(C(b)) − F(C(a))) dμ = ∫ f(C_b) dμ` with `f` the projected functional of `monotone_projFun`.
[cite: VandenbergHaggstromKahn2005, §2.1 Lemma 2.4 (p. 10)] -/
theorem setIntegral_sub_eq_projFun (w : Sym2 V → unitInterval) (a b : V) (F : Set V → ℝ) (𝒮 : Set (Set (Sym2 V))) :
    ∫ ω in {ω : BondConfig V | ¬ (openGraph ω).Reachable b a} ∩ {ω | openEdgeCluster ω b ∈ 𝒮},
        (F (openCluster ω b) - F (openCluster ω a)) ∂(prodBernoulli w) =
      ∫ ω in {ω : BondConfig V | ¬ (openGraph ω).Reachable b a} ∩ {ω | openEdgeCluster ω b ∈ 𝒮},
        (F {z | z = b ∨ ∃ e ∈ openEdgeCluster ω b, z ∈ e} -
          ∫ η, F (openCluster (η \ barOf {b} (openEdgeCluster ω b)) a) ∂(prodBernoulli w))
          ∂(prodBernoulli w) := by
  rw [integral_sub (Integrable.of_finite).integrableOn (Integrable.of_finite).integrableOn,
    integral_sub (Integrable.of_finite).integrableOn (Integrable.of_finite).integrableOn,
    tower_clusterFun]
  simp only [clusterFun_openEdgeCluster]

theorem covTransfer_of_covTau (w : Sym2 V → unitInterval) (o v a b : V) (F : Set V → ℝ)
    (hCT : (prodBernoulli w).real ({ω : BondConfig V | ¬ (openGraph ω).Reachable v b} ∩
          {ω | ¬ (openGraph ω).Reachable v a} ∩ openConn v o) *
        ((prodBernoulli w).real {ω : BondConfig V | ¬ (openGraph ω).Reachable b a} *
            (∫ ω in {ω : BondConfig V | ¬ (openGraph ω).Reachable b a} ∩ openConn b v,
              (F {z | z = b ∨ ∃ e ∈ openEdgeCluster ω b, z ∈ e} -
                ∫ η, F (openCluster (η \ barOf {b} (openEdgeCluster ω b)) a) ∂(prodBernoulli w))
              ∂(prodBernoulli w)) -
          (∫ ω in {ω : BondConfig V | ¬ (openGraph ω).Reachable b a},
              (F {z | z = b ∨ ∃ e ∈ openEdgeCluster ω b, z ∈ e} -
                ∫ η, F (openCluster (η \ barOf {b} (openEdgeCluster ω b)) a) ∂(prodBernoulli w))
              ∂(prodBernoulli w)) *
            (prodBernoulli w).real ({ω : BondConfig V | ¬ (openGraph ω).Reachable b a} ∩ openConn b v)) ≤
      (prodBernoulli w).real ({ω : BondConfig V | ¬ (openGraph ω).Reachable v b} ∩
          {ω | ¬ (openGraph ω).Reachable v a}) *
        ((prodBernoulli w).real {ω : BondConfig V | ¬ (openGraph ω).Reachable b a} *
            (∫ ω in {ω : BondConfig V | ¬ (openGraph ω).Reachable b a} ∩ openConn b o,
              (F {z | z = b ∨ ∃ e ∈ openEdgeCluster ω b, z ∈ e} -
                ∫ η, F (openCluster (η \ barOf {b} (openEdgeCluster ω b)) a) ∂(prodBernoulli w))
              ∂(prodBernoulli w)) -
          (∫ ω in {ω : BondConfig V | ¬ (openGraph ω).Reachable b a},
              (F {z | z = b ∨ ∃ e ∈ openEdgeCluster ω b, z ∈ e} -
                ∫ η, F (openCluster (η \ barOf {b} (openEdgeCluster ω b)) a) ∂(prodBernoulli w))
              ∂(prodBernoulli w)) *
            (prodBernoulli w).real ({ω : BondConfig V | ¬ (openGraph ω).Reachable b a} ∩ openConn b o))) :
    (prodBernoulli w).real (({ω : BondConfig V | ¬ (openGraph ω).Reachable v a} ∩ {ω | ¬ (openGraph ω).Reachable v b}) ∩
              openConn o v) *
        ((prodBernoulli w).real ((openConn a b)ᶜ : Set (BondConfig V)) *
            ∫ ω in (openConn v b ∩ (openConn a b)ᶜ : Set (BondConfig V)), (F (openCluster ω b) - F (openCluster ω a)) ∂(prodBernoulli w) -
          (prodBernoulli w).real (openConn v b ∩ (openConn a b)ᶜ : Set (BondConfig V)) *
            ∫ ω in ((openConn a b)ᶜ : Set (BondConfig V)), (F (openCluster ω b) - F (openCluster ω a)) ∂(prodBernoulli w)) ≤
      (prodBernoulli w).real ({ω : BondConfig V | ¬ (openGraph ω).Reachable v a} ∩ {ω | ¬ (openGraph ω).Reachable v b}) *
        ((prodBernoulli w).real ((openConn a b)ᶜ : Set (BondConfig V)) *
            ∫ ω in (openConn o b ∩ (openConn a b)ᶜ : Set (BondConfig V)), (F (openCluster ω b) - F (openCluster ω a)) ∂(prodBernoulli w) -
          (prodBernoulli w).real (openConn o b ∩ (openConn a b)ᶜ : Set (BondConfig V)) *
            ∫ ω in ((openConn a b)ᶜ : Set (BondConfig V)), (F (openCluster ω b) - F (openCluster ω a)) ∂(prodBernoulli w)) := by
  classical
  set μ := prodBernoulli w with hμ
  set D : Set (BondConfig V) := {ω : BondConfig V | ¬ (openGraph ω).Reachable b a} with hD
  have eQ : ((openConn a b)ᶜ : Set (BondConfig V)) = D := by
    ext ω
    simp only [mem_compl_iff, openConn, mem_setOf_eq, hD]
    exact ⟨fun h h' => h h'.symm, fun h h' => h h'.symm⟩
  have eO : ∀ x : V, (openConn x b ∩ (openConn a b)ᶜ : Set (BondConfig V)) = D ∩ openConn b x := by
    intro x; rw [eQ, inter_comm, openConn_symm]
  have eS : ∀ x : V, D ∩ openConn b x = D ∩ {ω | openEdgeCluster ω b ∈ {K : Set (Sym2 V) | x = b ∨ ∃ e ∈ K, x ∈ e}} := by
    intro x; ext ω
    simp only [mem_inter_iff, openConn, mem_setOf_eq, reachable_iff_exists_mem_openEdgeCluster ω b x]
  have iD : ∫ ω in D, (F (openCluster ω b) - F (openCluster ω a)) ∂μ =
      ∫ ω in D, (F {z | z = b ∨ ∃ e ∈ openEdgeCluster ω b, z ∈ e} -
        ∫ η, F (openCluster (η \ barOf {b} (openEdgeCluster ω b)) a) ∂μ) ∂μ := by
    have h := setIntegral_sub_eq_projFun w a b F (univ : Set (Set (Sym2 V)))
    simp only [mem_univ, setOf_true, inter_univ] at h
    exact h
  have iO : ∀ x : V, ∫ ω in D ∩ openConn b x, (F (openCluster ω b) - F (openCluster ω a)) ∂μ =
      ∫ ω in D ∩ openConn b x, (F {z | z = b ∨ ∃ e ∈ openEdgeCluster ω b, z ∈ e} -
        ∫ η, F (openCluster (η \ barOf {b} (openEdgeCluster ω b)) a) ∂μ) ∂μ := by
    intro x; rw [eS x]; exact setIntegral_sub_eq_projFun w a b F _
  have mSa : ({ω : BondConfig V | ¬ (openGraph ω).Reachable v a} ∩ {ω | ¬ (openGraph ω).Reachable v b}) =
      {ω : BondConfig V | ¬ (openGraph ω).Reachable v b} ∩ {ω | ¬ (openGraph ω).Reachable v a} := inter_comm _ _
  rw [eO v, eO o, eQ, iD, iO v, iO o, mSa, openConn_symm o v]
  linarith [hCT]

end CovTau

end Percolation.Continuity

end
