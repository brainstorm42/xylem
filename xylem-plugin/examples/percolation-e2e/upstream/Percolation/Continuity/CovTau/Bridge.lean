import Percolation.Continuity.CovTau.A2EdgeDefs
import Percolation.Literature.KozmaNitzanClusterPropertyReal
import Percolation.Literature.TwoClusterGibbsCovariance
import Percolation.Util.Linter

/-!
# The dictionary between the (A2) weight-sum framework and the A2-diagonal hypothesis of the conditioned covariance transfer

THIS FILE is the dictionary:

* `inter_edgesIn_univ`, `rC_univ`, `rD_univ`, `mem_sC_univ` — restriction to `univ` is no restriction;
* `sum_weight_mul_eq_integral`, `sum_weight_ind`, `sum_weight_mul_ind`, `sum_weight_coe_eq_one` — weight sums are integrals;
* `Mf_univ_singleton = μ(v↮x, v↮y)`, `Ef_univ_singleton = μ(v↮x, v↮y, v↔o)`;
[cite: VandenbergHaggstromKahn2005, §1 pp. 3–4, §2.1 Lemmas 2.3–2.4 (p. 10)] [cite: KozmaNitzan2024, Conj. 1 (p. 3)]
-/

noncomputable section

namespace Percolation.Continuity

namespace CovTau

open MeasureTheory Set Percolation.Literature
open Percolation.Literature.LatticeModels (prodBernoulli)
open scoped Classical
open BHK2006 DecisionTree

variable {V : Type*} [Fintype V]

/-! ### Percolation restricted to `univ` is percolation; weight sums are integrals -/

omit [Fintype V] in
/-- `ind D` is the real indicator of `D`. [folklore] -/
theorem ind_eq_indicator_one (D : Set (BondConfig V)) : (fun ω => ind D ω) = D.indicator (1 : BondConfig V → ℝ) := by
  funext ω
  by_cases h : ω ∈ D
  · rw [ind_of_mem h, indicator_of_mem h, Pi.one_apply]
  · rw [ind_of_not_mem h, indicator_of_notMem h]

omit [Fintype V] in
/-- `1{o ∈ C_v}` read on the edge cluster is the indicator of `{v ↔ o}`. [folklore] -/
theorem oInd_openEdgeCluster (o v : V) (ζ : Set (Sym2 V)) :
    oInd o v (openEdgeCluster ζ v) = ind (openConn v o : Set (BondConfig V)) ζ := by
  rw [oInd]
  by_cases h : (openGraph ζ).Reachable v o
  · rw [ind_of_mem (show ζ ∈ (openConn v o : Set (BondConfig V)) from h),
      ind_of_mem (show openEdgeCluster ζ v ∈ {C : Set (Sym2 V) | o = v ∨ ∃ e ∈ C, o ∈ e} from
        (reachable_iff_exists_mem_openEdgeCluster ζ v o).1 h)]
  · rw [ind_of_not_mem (show ζ ∉ (openConn v o : Set (BondConfig V)) from h),
      ind_of_not_mem (show openEdgeCluster ζ v ∉ {C : Set (Sym2 V) | o = v ∨ ∃ e ∈ C, o ∈ e} from
        fun h' => h ((reachable_iff_exists_mem_openEdgeCluster ζ v o).2 h'))]

/-- Every pair lies in `edgesIn univ`. [folklore] -/
theorem inter_edgesIn_univ (ω : Set (Sym2 V)) : ω ∩ BHK2006.edgesIn (Finset.univ : Finset V) = ω := by
  ext e
  simp only [mem_inter_iff, BHK2006.edgesIn, Finset.mem_univ, implies_true, mem_setOf_eq, and_true]

/-- `rC univ s ω = C_s(ω)`. [folklore] -/
theorem rC_univ (s : V) (ω : Set (Sym2 V)) : rC (Finset.univ : Finset V) s ω = openEdgeCluster ω s := by
  rw [rC, inter_edgesIn_univ]

/-- `rD univ s X = {s ↮ X}`. [folklore] -/
theorem rD_univ (s : V) (X : Set V) :
    rD (Finset.univ : Finset V) s X = {ω : Set (Sym2 V) | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x} := by
  ext ω; simp only [rD, inter_edgesIn_univ, mem_setOf_eq]

/-- `sC univ N ω` is the open vertex cluster of the set `N`. [folklore] -/
theorem mem_sC_univ {N : Set V} {ω : Set (Sym2 V)} {u : V} :
    u ∈ sC (Finset.univ : Finset V) N ω ↔ ∃ z ∈ N, (openGraph ω).Reachable z u := by
  rw [mem_sC, inter_edgesIn_univ]

/-- Weight sums are integrals against `prodBernoulli`. [folklore] -/
theorem sum_weight_mul_eq_integral (p : Sym2 V → unitInterval) (F : Set (Sym2 V) → ℝ) :
    ∑ ω, weight (fun e => (p e : ℝ)) ω * F ω = ∫ ω, F ω ∂(prodBernoulli p) :=
  (integral_prodBernoulli_eq_sum p F).symm

/-- `Σ weight · 1_D = μ(D)`. [folklore] -/
theorem sum_weight_ind (p : Sym2 V → unitInterval) (D : Set (BondConfig V)) :
    ∑ ω, weight (fun e => (p e : ℝ)) ω * ind D ω = (prodBernoulli p).real D := by
  rw [sum_weight_mul_eq_integral, ind_eq_indicator_one, integral_indicator_one MeasurableSet.of_discrete]

/-- `Σ weight · F · 1_D = ∫_D F`. [folklore] -/
theorem sum_weight_mul_ind (p : Sym2 V → unitInterval) (F : Set (Sym2 V) → ℝ) (D : Set (BondConfig V)) :
    ∑ ω, weight (fun e => (p e : ℝ)) ω * (F ω * ind D ω) = ∫ ω in D, F ω ∂(prodBernoulli p) := by
  rw [sum_weight_mul_eq_integral, ← integral_indicator MeasurableSet.of_discrete]
  congr 1
  funext ω
  by_cases h : ω ∈ D
  · rw [ind_of_mem h, mul_one, indicator_of_mem h]
  · rw [ind_of_not_mem h, mul_zero, indicator_of_notMem h]

/-- The total weight is `1`. [folklore] -/
theorem sum_weight_coe_eq_one (p : Sym2 V → unitInterval) : ∑ ω, weight (fun e => (p e : ℝ)) ω = 1 := by
  have h := sum_weight_mul_eq_integral p fun _ => (1 : ℝ)
  simp only [mul_one, integral_const, probReal_univ, smul_eq_mul] at h
  exact h

end CovTau

end Percolation.Continuity

end
