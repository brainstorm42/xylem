import Percolation.Literature.KozmaNitzanPreFKG
import Percolation.Literature.LonePortSumGeneral
import Percolation.Util.Linter

/-!
# Tools for the marker dominance lemma

[cite: VandenbergHaggstromKahn2005, Thm. 1.3 (p. 6) and pp. 7–8 — corollary]
-/

noncomputable section

namespace Percolation.Continuity

open MeasureTheory Set Percolation.Literature.LatticeModels Percolation.Literature
open scoped Classical

variable {V : Type*}

namespace HullPort

open LonePortSum LonePortSumGeneral BHK2006 DecisionTree KNPreFKG

/-! ### Functional Harris for the product measure (integral form) -/

/-- **Harris' inequality, functional form**: for monotone nonnegative `f, g : BondConfig V → ℝ`,
`(∫ f dμ)(∫ g dμ) ≤ ∫ f g dμ` under `μ = prodBernoulli w` (a probability measure).
[cite: GrimmettPercolation1999, Thm. (2.4) p. 34] -/
theorem integral_harris [Fintype V] (w : Sym2 V → unitInterval) (f g : BondConfig V → ℝ)
    (hf : Monotone f) (hg : Monotone g) (hf0 : ∀ ω, 0 ≤ f ω) (hg0 : ∀ ω, 0 ≤ g ω) :
    (∫ ω, f ω ∂(prodBernoulli w)) * (∫ ω, g ω ∂(prodBernoulli w)) ≤
      ∫ ω, f ω * g ω ∂(prodBernoulli w) := by
  classical
  set w' : Sym2 V → ℝ := fun e => (w e : ℝ) with hw'
  have hw0 : ∀ e, 0 ≤ w' e := fun e => (w e).2.1
  have hw1 : ∀ e, w' e ≤ 1 := fun e => (w e).2.2
  have hm : ∑ ω, weight w' ω = 1 := by
    have h1 := integral_prodBernoulli_eq_sum w fun _ => (1 : ℝ)
    simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at h1
    exact h1.symm
  have key := harris hw0 hw1 hf0 hg0 hf hg
  rw [hm, one_mul] at key
  rw [integral_prodBernoulli_eq_sum, integral_prodBernoulli_eq_sum, integral_prodBernoulli_eq_sum]
  exact key

/-! ### The marker dominance lemma without avoidance (`X = ∅`) -/

/-- **Marker dominance lemma, `X = ∅` (functional form).** Bond percolation `μ = prodBernoulli w` on a
finite vertex type; `s, y, z` vertices with `s ≠ y`; `F` a monotone nonnegative function of the open edge
cluster `C_s`; `Y = {s ↔ y}`, `Z = {s ↔ z}`, `N = {s ↮ y}`, `W = {y ↔ z}`.  Then
`μ(N) · [∫_Z F(C_s) − (∫ F(C_s)) μ(Z)] ≥ μ(W ∩ N) · [∫_Y F(C_s) − (∫ F(C_s)) μ(Y)]`,
i.e. `Cov(F(C_s), 1_Z) ≥ μ(y ↔ z | s ↮ y) · Cov(F(C_s), 1_Y)` ("the marker `z` is at least `s''` times as
correlated with every increasing function of the cluster as `y` is", `s'' = μ(z ∈ C_y | s ∉ C_y)`).
Proof: with `B = Z ∪ W` one has `1_Z = 1_B − 1_{W ∩ N}`, whence the identity
`μ(N)Cov(F,1_Z) − μ(WN)Cov(F,1_Y) = μ(N)·[∫_B F − (∫F)μ(B)] + [μ(WN)∫_N F − μ(N)∫_{W∩N} F]`;
the first bracket is `≥ 0` by Harris (`F(C_s)` and `1_B` are increasing in the configuration), the second by
van den Berg–Häggström–Kahn Thm 1.3 given `{s ↮ y}` for `F(C_s)` and the off-cluster statistic `1_W`
(`setSep_offCluster_negCorrelation`).  Not in print; derived here.
[cite: VandenbergHaggstromKahn2005, Thm. 1.3 (p. 6) — corollary, derived here] -/
theorem markerDominance_noAvoid [Fintype V] (w : Sym2 V → unitInterval) (s y z : V) (hsy : s ≠ y)
    (F : Set (Sym2 V) → ℝ) (hF : Monotone F) (hF0 : ∀ C, 0 ≤ F C) :
    (prodBernoulli w).real ((openConn s y : Set (BondConfig V))ᶜ ∩ openConn y z) *
        ((∫ ω in (openConn s y : Set (BondConfig V)), F (openEdgeCluster ω s) ∂(prodBernoulli w)) -
          (∫ ω, F (openEdgeCluster ω s) ∂(prodBernoulli w)) *
            (prodBernoulli w).real (openConn s y : Set (BondConfig V))) ≤
      (prodBernoulli w).real ((openConn s y : Set (BondConfig V))ᶜ) *
        ((∫ ω in (openConn s z : Set (BondConfig V)), F (openEdgeCluster ω s) ∂(prodBernoulli w)) -
          (∫ ω, F (openEdgeCluster ω s) ∂(prodBernoulli w)) *
            (prodBernoulli w).real (openConn s z : Set (BondConfig V))) := by
  classical
  set μ := prodBernoulli w with hμ
  have hmeas : ∀ S : Set (BondConfig V), MeasurableSet S := fun S => MeasurableSet.of_discrete
  set Y : Set (BondConfig V) := openConn s y with hY
  set Z : Set (BondConfig V) := openConn s z with hZ
  set W : Set (BondConfig V) := openConn y z with hW
  set N : Set (BondConfig V) := Yᶜ with hN
  set f : BondConfig V → ℝ := fun ω => F (openEdgeCluster ω s) with hf
  have hfmono : Monotone f := fun ω ω' h => hF (openEdgeCluster_mono h s)
  have hf0 : ∀ ω, 0 ≤ f ω := fun ω => hF0 _
  have hint : ∀ S : Set (BondConfig V), IntegrableOn f S μ := fun S => (Integrable.of_finite).integrableOn
  -- `Z ∪ W = Z ⊔ (W ∩ N)` and `N = (W ∩ N) ⊔ (N \ W)`-type decompositions
  have hWN : W ∩ N = W \ Z := by
    ext ω
    simp only [hW, hN, hZ, hY, mem_inter_iff, mem_compl_iff, mem_sdiff]
    constructor
    · rintro ⟨hyz, hsy'⟩
      exact ⟨hyz, fun hsz => hsy' ((hsz : (openGraph ω).Reachable s z).trans
        (hyz : (openGraph ω).Reachable y z).symm)⟩
    · rintro ⟨hyz, hsz⟩
      exact ⟨hyz, fun hsy' => hsz ((hsy' : (openGraph ω).Reachable s y).trans
        (hyz : (openGraph ω).Reachable y z))⟩
  have hBdisj : Disjoint Z (W ∩ N) := by
    rw [hWN]; exact disjoint_sdiff_right
  have hBunion : Z ∪ W = Z ∪ (W ∩ N) := by rw [hWN, union_sdiff_self]
  -- the set `B = Z ∪ W` is increasing
  have hBup : IsUpperSet (Z ∪ W) := (isUpperSet_openConn s z).union (isUpperSet_openConn y z)
  -- integrals and masses
  have iB : ∫ ω in Z ∪ W, f ω ∂μ = (∫ ω in Z, f ω ∂μ) + ∫ ω in W ∩ N, f ω ∂μ := by
    rw [hBunion]; exact setIntegral_union hBdisj (hmeas _) (hint _) (hint _)
  have mB : μ.real (Z ∪ W) = μ.real Z + μ.real (W ∩ N) := by
    rw [hBunion]; exact measureReal_union hBdisj (hmeas _)
  have iY : (∫ ω in Y, f ω ∂μ) + ∫ ω in N, f ω ∂μ = ∫ ω, f ω ∂μ := integral_add_compl (hmeas Y) Integrable.of_finite
  have mY : μ.real Y + μ.real N = 1 := by
    have := measureReal_add_measureReal_compl (μ := μ) (hmeas Y); rwa [probReal_univ] at this
  have iWN : ∫ ω in N, f ω * W.indicator 1 ω ∂μ = ∫ ω in W ∩ N, f ω ∂μ := by
    have e : (fun ω => f ω * W.indicator (1 : BondConfig V → ℝ) ω) = W.indicator f := by
      funext ω
      by_cases hω : ω ∈ W
      · rw [indicator_of_mem hω, indicator_of_mem hω, Pi.one_apply, mul_one]
      · rw [indicator_of_notMem hω, indicator_of_notMem hω, mul_zero]
    rw [e, setIntegral_indicator (hmeas W), inter_comm]
  -- (a) Harris: `(∫ f) μ(B) ≤ ∫_B f`
  have ha : (∫ ω, f ω ∂μ) * μ.real (Z ∪ W) ≤ ∫ ω in Z ∪ W, f ω ∂μ := by
    have h := integral_harris w f ((Z ∪ W).indicator 1) hfmono
      (monotone_indicator_one_of_isUpperSet hBup) hf0 (fun ω => indicator_nonneg (fun _ _ => zero_le_one) _)
    rw [integral_indicator_one (hmeas _)] at h
    have e : ∫ ω, f ω * (Z ∪ W).indicator 1 ω ∂μ = ∫ ω in Z ∪ W, f ω ∂μ := by
      rw [← integral_indicator (hmeas _)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      by_cases hω : ω ∈ Z ∪ W
      · simp [indicator_of_mem hω]
      · simp [indicator_of_notMem hω]
    rw [e] at h
    exact h
  -- (b) off-cluster negative correlation given `{s ↮ y}`
  have hsX : s ∉ ({y} : Set V) := by simpa using hsy
  have hNeq : {ω : BondConfig V | ∀ x ∈ ({y} : Set V), ¬ (openGraph ω).Reachable s x} = N := by
    ext ω; simp only [mem_setOf_eq, mem_singleton_iff, forall_eq, hN, hY, mem_compl_iff]; rfl
  have hb := setSep_offCluster_negCorrelation w s ({y} : Set V) hsX F hF (W.indicator 1)
    (monotone_indicator_one_of_isUpperSet (isUpperSet_openConn y z)) (fun ω hω => by
      have hns : ¬ (openGraph ω).Reachable s y := hω y rfl
      have key : (ω \ {e | ∃ v ∈ e, v = s ∨ ∃ e' ∈ openEdgeCluster ω s, v ∈ e'}) ∈ W ↔ ω ∈ W :=
        LonePortSumGeneral.reachable_sdiff_bar_iff hns z
      by_cases hyz : ω ∈ W
      · rw [indicator_of_mem hyz, indicator_of_mem (key.2 hyz), Pi.one_apply, Pi.one_apply]
      · rw [indicator_of_notMem hyz, indicator_of_notMem (mt key.1 hyz)])
  rw [hNeq] at hb
  change μ.real N * ∫ ω in N, f ω * W.indicator 1 ω ∂μ ≤ (∫ ω in N, f ω ∂μ) * ∫ ω in N, W.indicator 1 ω ∂μ at hb
  rw [iWN, setIntegral_indicator_one_eq] at hb
  -- combine
  have hN0 : 0 ≤ μ.real N := measureReal_nonneg
  have hNW : μ.real (N ∩ W) = μ.real (W ∩ N) := by rw [inter_comm]
  rw [hNW] at hb ⊢
  have mY' : μ.real Y = 1 - μ.real N := by linarith
  have ident : μ.real N * ((∫ ω in Z, f ω ∂μ) - (∫ ω, f ω ∂μ) * μ.real Z) -
      μ.real (W ∩ N) * ((∫ ω in Y, f ω ∂μ) - (∫ ω, f ω ∂μ) * μ.real Y) =
      μ.real N * ((∫ ω in Z ∪ W, f ω ∂μ) - (∫ ω, f ω ∂μ) * μ.real (Z ∪ W)) +
        (μ.real (W ∩ N) * (∫ ω in N, f ω ∂μ) - μ.real N * ∫ ω in W ∩ N, f ω ∂μ) := by
    rw [mY', ← iY, iB, mB]; ring
  have ha' := mul_le_mul_of_nonneg_left ha hN0
  have h1 : 0 ≤ μ.real N * ((∫ ω in Z ∪ W, f ω ∂μ) - (∫ ω, f ω ∂μ) * μ.real (Z ∪ W)) := by
    nlinarith [ha', hN0]
  have h2 : 0 ≤ μ.real (W ∩ N) * (∫ ω in N, f ω ∂μ) - μ.real N * ∫ ω in W ∩ N, f ω ∂μ := by
    linarith [hb]
  linarith [ident, h1, h2]

end HullPort

end Percolation.Continuity

end
