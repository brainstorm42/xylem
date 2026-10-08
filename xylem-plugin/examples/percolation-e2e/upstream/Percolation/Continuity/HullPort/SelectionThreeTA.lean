import Percolation.Continuity.HullPort.DeletedEdges
import Percolation.Literature.TwoClusterGibbsCovariance
import Percolation.Util.Linter

/-!
# Marker dominance with an avoided set: MDL(X) and SL(3,1) from the averaged inequality `T_A ≥ 0`

The chain for the marker dominance lemma with an avoided set `X` (MDLX):  `T_A ≥ 0`  ⟹  `R_1 ≥ 0`  ⟹ MDLX  ⟹  SL(3,1).
* `R_1 ≥ 0 ⟹ MDLX` is the reduction theorem (BHK 2006 §2.1 Gibbs sampler;
  `BHK2006_clusterConditionalCov_nonneg_of_within_of_forall_nondegenerate`, `TwoClusterGibbsCovariance.lean`);
* `T_A ≥ 0 ⟹ R_1 ≥ 0` is the `X = ∅` marker dominance lemma (`HullPort.markerDominance_noAvoid`) applied,
  for each configuration `ω ∈ D = {s ↮ X}`, to percolation with the pairs `A_X(ω)` (those meeting the open cluster of `X`)
  switched off (`BHK2006.integral_comp_sdiff_prodBernoulli`);
The remaining hypothesis `hTA` reads, for weights `p ∈ (0,1)^{Sym2 V}` and monotone `g ≥ 0`, with
`μ_p = prodBernoulli p`, `μ'_ω` = `prodBernoulli` of `p` zeroed on `A_X(ω)`, `A = {y ↮ s, X}`, `W =
{y ↔ z}`, `Y = {s ↔ y}`, `N = Yᶜ`: `0 ≤ ∫_D ( μ_p(A) · μ'_ω(N ∩ W)/μ'_ω(N) − μ_p(A ∩ W) ) · ( ∫_Y
g(C_s) dμ'_ω − (∫ g(C_s) dμ'_ω) μ'_ω(Y) ) dμ_p(ω)` (= `μ(A) · T_A(g)` in the "zeroed weights"
bookkeeping; `x/0 := 0`). [cite: VandenbergHaggstromKahn2005, Thm. 1.3 (p. 6), §2.1 pp. 10–13 —
corollaries, derived here]
-/

noncomputable section

namespace Percolation.Continuity

open MeasureTheory Set Percolation.Literature.LatticeModels Percolation.Literature
open scoped Classical

variable {V : Type*}

namespace HullPort

open LonePortSum LonePortSumGeneral BHK2006 DecisionTree KNPreFKG

/-- **MDL(X) from `T_A ≥ 0`.** For `s ≠ y`, a marker `z`, an avoided set `X`, `D = {s ↮ X}`, `A = {y ↮ s, X}` (as
`{ω | ∀ x ∈ insert s X, y ↮ x}`), `W = {y ↔ z}`, `Y = {s ↔ y}`, `Z = {s ↔ z}`: if the averaged inequality `T_A ≥ 0`
(hypothesis `hTA`, see the file header; theorem) holds at all non-degenerate weights, then for every monotone
`F` of the edge cluster `C_s`,
`μ(A ∩ W)·[μ(D)∫_{D∩Y} F − (∫_D F) μ(D∩Y)] ≤ μ(A)·[μ(D)∫_{D∩Z} F − (∫_D F) μ(D∩Z)]` (the functional marker dominance
lemma with avoidance, MDLX).  Proof: the reduction theorem with the test function
`h_p = μ_p(A)·1{z ∈ V(C)} − μ_p(A∩W)·1{y ∈ V(C)}` (continuous in `p`); its hypothesis is, configuration by configuration,
`μ_p(A)·Cov'(g,1_Z) − μ_p(A∩W)·Cov'(g,1_Y) ≥ (μ_p(A) μ'(N∩W)/μ'(N) − μ_p(A∩W))·Cov'(g,1_Y)` under the zeroed weights,
which is `markerDominance_noAvoid` there (and Harris when `μ'(N) = 0`).
[cite: VandenbergHaggstromKahn2005, Thm. 1.3 (p. 6), §2.1 pp. 10–13 — corollaries] -/
theorem markerDominanceAvoid_of_TA [Fintype V] (w : Sym2 V → unitInterval) (s y z : V) (X : Set V) (hsy : s ≠ y)
    (hTA : ∀ p : Sym2 V → unitInterval, (∀ e, 0 < p e ∧ p e < 1) →
      ∀ g : Set (Sym2 V) → ℝ, Monotone g → (∀ C, 0 ≤ g C) →
      0 ≤ ∫ ω in {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x},
        ((prodBernoulli p).real {ω' : BondConfig V | ∀ x ∈ insert s X, ¬ (openGraph ω').Reachable y x} *
              ((prodBernoulli p).real ((· \ {e : Sym2 V | ∃ v ∈ e, ∃ x ∈ X, (openGraph ω).Reachable x v}) ⁻¹'
                  ((openConn s y : Set (BondConfig V))ᶜ ∩ openConn y z)) /
                (prodBernoulli p).real ((· \ {e : Sym2 V | ∃ v ∈ e, ∃ x ∈ X, (openGraph ω).Reachable x v}) ⁻¹'
                  ((openConn s y : Set (BondConfig V))ᶜ))) -
            (prodBernoulli p).real ({ω' : BondConfig V | ∀ x ∈ insert s X, ¬ (openGraph ω').Reachable y x} ∩
              openConn y z)) *
          ((∫ η in (· \ {e : Sym2 V | ∃ v ∈ e, ∃ x ∈ X, (openGraph ω).Reachable x v}) ⁻¹' (openConn s y : Set (BondConfig V)),
                g (openEdgeCluster (η \ {e : Sym2 V | ∃ v ∈ e, ∃ x ∈ X, (openGraph ω).Reachable x v}) s) ∂(prodBernoulli p)) -
            (∫ η, g (openEdgeCluster (η \ {e : Sym2 V | ∃ v ∈ e, ∃ x ∈ X, (openGraph ω).Reachable x v}) s) ∂(prodBernoulli p)) *
              (prodBernoulli p).real ((· \ {e : Sym2 V | ∃ v ∈ e, ∃ x ∈ X, (openGraph ω).Reachable x v}) ⁻¹'
                (openConn s y : Set (BondConfig V))))
        ∂(prodBernoulli p))
    (F : Set (Sym2 V) → ℝ) (hF : Monotone F) :
    (prodBernoulli w).real ({ω : BondConfig V | ∀ x ∈ insert s X, ¬ (openGraph ω).Reachable y x} ∩ openConn y z) *
        ((prodBernoulli w).real {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x} *
            (∫ ω in {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x} ∩ openConn s y,
              F (openEdgeCluster ω s) ∂(prodBernoulli w)) -
          (∫ ω in {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x},
              F (openEdgeCluster ω s) ∂(prodBernoulli w)) *
            (prodBernoulli w).real ({ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x} ∩ openConn s y)) ≤
      (prodBernoulli w).real {ω : BondConfig V | ∀ x ∈ insert s X, ¬ (openGraph ω).Reachable y x} *
        ((prodBernoulli w).real {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x} *
            (∫ ω in {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x} ∩ openConn s z,
              F (openEdgeCluster ω s) ∂(prodBernoulli w)) -
          (∫ ω in {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x},
              F (openEdgeCluster ω s) ∂(prodBernoulli w)) *
            (prodBernoulli w).real ({ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x} ∩ openConn s z)) := by
  classical
  set D : Set (BondConfig V) := {ω | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x} with hD
  set Ay : Set (BondConfig V) := {ω | ∀ x ∈ insert s X, ¬ (openGraph ω).Reachable y x} with hAy
  set W : Set (BondConfig V) := openConn y z with hW
  set Y : Set (BondConfig V) := openConn s y with hY
  set Z : Set (BondConfig V) := openConn s z with hZ
  -- cluster-side indicators of `Z` and `Y`
  set χz : Set (Sym2 V) → ℝ := fun C => if (z = s ∨ ∃ e ∈ C, z ∈ e) then 1 else 0 with hχz
  set χy : Set (Sym2 V) → ℝ := fun C => if (y = s ∨ ∃ e ∈ C, y ∈ e) then 1 else 0 with hχy
  have hχzeq : ∀ ω : BondConfig V, χz (openEdgeCluster ω s) = ind Z ω := by
    intro ω
    by_cases h : ω ∈ Z
    · rw [ind_of_mem h, hχz]
      simp only [if_pos ((reachable_iff_exists_mem_openEdgeCluster ω s z).1 h)]
    · rw [ind_of_not_mem h, hχz]
      have h' : ¬ (z = s ∨ ∃ e ∈ openEdgeCluster ω s, z ∈ e) := fun hh =>
        h ((reachable_iff_exists_mem_openEdgeCluster ω s z).2 hh)
      simp only [if_neg h']
  have hχyeq : ∀ ω : BondConfig V, χy (openEdgeCluster ω s) = ind Y ω := by
    intro ω
    by_cases h : ω ∈ Y
    · rw [ind_of_mem h, hχy]
      simp only [if_pos ((reachable_iff_exists_mem_openEdgeCluster ω s y).1 h)]
    · rw [ind_of_not_mem h, hχy]
      have h' : ¬ (y = s ∨ ∃ e ∈ openEdgeCluster ω s, y ∈ e) := fun hh =>
        h ((reachable_iff_exists_mem_openEdgeCluster ω s y).2 hh)
      simp only [if_neg h']
  -- the test functions `h_p = μ_p(A) χ_z − μ_p(A ∩ W) χ_y`, continuous in the weights
  set h : (Sym2 V → unitInterval) → Set (Sym2 V) → ℝ := fun p C =>
    (prodBernoulli p).real Ay * χz C - (prodBernoulli p).real (Ay ∩ W) * χy C with hh
  have hcont : ∀ C, Continuous fun p => h p C := fun C =>
    ((prodBernoulli_real_continuous Ay).mul continuous_const).sub
      ((prodBernoulli_real_continuous (Ay ∩ W)).mul continuous_const)
  -- two integral identities, valid for every weight vector `q`
  have intZY : ∀ (q : Sym2 V → unitInterval) (a b : ℝ) (g : Set (Sym2 V) → ℝ) (E : Set (BondConfig V)),
      ∫ ω in E, g (openEdgeCluster ω s) * (a * χz (openEdgeCluster ω s) - b * χy (openEdgeCluster ω s))
          ∂(prodBernoulli q) =
        a * (∫ ω in E ∩ Z, g (openEdgeCluster ω s) ∂(prodBernoulli q)) -
          b * (∫ ω in E ∩ Y, g (openEdgeCluster ω s) ∂(prodBernoulli q)) := by
    intro q a b g E
    rw [setIntegral_eq_sum q E, setIntegral_eq_sum q (E ∩ Z), setIntegral_eq_sum q (E ∩ Y), Finset.mul_sum,
      Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [hχzeq ω, hχyeq ω, ind_inter, ind_inter]; ring
  have intH : ∀ (q : Sym2 V → unitInterval) (a b : ℝ) (E : Set (BondConfig V)),
      ∫ ω in E, (a * χz (openEdgeCluster ω s) - b * χy (openEdgeCluster ω s)) ∂(prodBernoulli q) =
        a * (prodBernoulli q).real (E ∩ Z) - b * (prodBernoulli q).real (E ∩ Y) := by
    intro q a b E
    rw [setIntegral_eq_sum q E, measureReal_eq_sum q (E ∩ Z), measureReal_eq_sum q (E ∩ Y), Finset.mul_sum,
      Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [hχzeq ω, hχyeq ω, ind_inter, ind_inter]; ring
  -- the hypothesis of the reduction theorem, from `hTA` and the `X = ∅` marker dominance lemma per configuration
  have hR : ∀ p : Sym2 V → unitInterval, (∀ e, 0 < p e ∧ p e < 1) →
      ∀ g : Set (Sym2 V) → ℝ, Monotone g → (∀ C, 0 ≤ g C) →
      0 ≤ ∫ ω in D,
        ((∫ η, g (openEdgeCluster (η \ {e | ∃ v ∈ e, ∃ x ∈ X, (openGraph ω).Reachable x v}) s) *
              h p (openEdgeCluster (η \ {e | ∃ v ∈ e, ∃ x ∈ X, (openGraph ω).Reachable x v}) s)
            ∂(prodBernoulli p)) -
          (∫ η, g (openEdgeCluster (η \ {e | ∃ v ∈ e, ∃ x ∈ X, (openGraph ω).Reachable x v}) s)
            ∂(prodBernoulli p)) *
          (∫ η, h p (openEdgeCluster (η \ {e | ∃ v ∈ e, ∃ x ∈ X, (openGraph ω).Reachable x v}) s)
            ∂(prodBernoulli p))) ∂(prodBernoulli p) := by
    intro p hp g hg hg0
    refine le_trans (hTA p hp g hg hg0) (setIntegral_mono_on (Integrable.of_finite).integrableOn
      (Integrable.of_finite).integrableOn MeasurableSet.of_discrete fun ω _ => ?_)
    -- fix the configuration `ω`; `μ'` = the zeroed weights
    set AX : Set (Sym2 V) := {e | ∃ v ∈ e, ∃ x ∈ X, (openGraph ω).Reachable x v} with hAX
    set p' : Sym2 V → unitInterval :=
      fun e => @ite _ (e ∈ AX) (Classical.propDecidable _) (0 : unitInterval) (p e) with hp'
    set a : ℝ := (prodBernoulli p).real Ay with ha
    set b : ℝ := (prodBernoulli p).real (Ay ∩ W) with hb
    have ha0 : 0 ≤ a := measureReal_nonneg
    have hb0 : 0 ≤ b := measureReal_nonneg
    have r1 : ∫ η, g (openEdgeCluster (η \ AX) s) * h p (openEdgeCluster (η \ AX) s) ∂(prodBernoulli p) =
        ∫ η, g (openEdgeCluster η s) * h p (openEdgeCluster η s) ∂(prodBernoulli p') := by
      rw [hp']; exact BHK2006.integral_comp_sdiff_prodBernoulli p AX
        (fun η => g (openEdgeCluster η s) * h p (openEdgeCluster η s))
    have r2 : ∫ η, g (openEdgeCluster (η \ AX) s) ∂(prodBernoulli p) =
        ∫ η, g (openEdgeCluster η s) ∂(prodBernoulli p') := by
      rw [hp']; exact BHK2006.integral_comp_sdiff_prodBernoulli p AX (fun η => g (openEdgeCluster η s))
    have r3 : ∫ η, h p (openEdgeCluster (η \ AX) s) ∂(prodBernoulli p) =
        ∫ η, h p (openEdgeCluster η s) ∂(prodBernoulli p') := by
      rw [hp']; exact BHK2006.integral_comp_sdiff_prodBernoulli p AX (fun η => h p (openEdgeCluster η s))
    have t1 : (prodBernoulli p).real ((· \ AX) ⁻¹' (Yᶜ ∩ W)) = (prodBernoulli p').real (Yᶜ ∩ W) := by
      rw [hp']; exact measureReal_preimage_sdiff_prodBernoulli p AX (Yᶜ ∩ W)
    have t2 : (prodBernoulli p).real ((· \ AX) ⁻¹' Yᶜ) = (prodBernoulli p').real Yᶜ := by
      rw [hp']; exact measureReal_preimage_sdiff_prodBernoulli p AX Yᶜ
    have t3 : (prodBernoulli p).real ((· \ AX) ⁻¹' Y) = (prodBernoulli p').real Y := by
      rw [hp']; exact measureReal_preimage_sdiff_prodBernoulli p AX Y
    have t4 : ∫ η in (· \ AX) ⁻¹' Y, g (openEdgeCluster (η \ AX) s) ∂(prodBernoulli p) =
        ∫ η in Y, g (openEdgeCluster η s) ∂(prodBernoulli p') := by
      rw [hp']; exact setIntegral_preimage_sdiff_prodBernoulli p AX Y (fun η => g (openEdgeCluster η s))
    rw [r1, r2, r3, t1, t2, t3, t4]
    -- everything under `μ' = prodBernoulli p'`
    have e1 : ∫ η, g (openEdgeCluster η s) * h p (openEdgeCluster η s) ∂(prodBernoulli p') =
        a * (∫ η in Z, g (openEdgeCluster η s) ∂(prodBernoulli p')) -
          b * (∫ η in Y, g (openEdgeCluster η s) ∂(prodBernoulli p')) := by
      have := intZY p' a b g Set.univ
      simp only [Measure.restrict_univ, Set.univ_inter] at this
      exact this
    have e2 : ∫ η, h p (openEdgeCluster η s) ∂(prodBernoulli p') =
        a * (prodBernoulli p').real Z - b * (prodBernoulli p').real Y := by
      have := intH p' a b Set.univ
      simp only [Measure.restrict_univ, Set.univ_inter] at this
      exact this
    rw [e1, e2]
    -- the `X = ∅` marker dominance lemma for the zeroed weights, and Harris
    have mdl := markerDominance_noAvoid p' s y z hsy g hg hg0
    have hgC : Monotone fun η : BondConfig V => g (openEdgeCluster η s) :=
      fun η η' hle => hg (openEdgeCluster_mono hle s)
    have hZmono : Monotone fun η : BondConfig V => ind Z η := by
      intro η η' hle
      show ind Z η ≤ ind Z η'
      by_cases h1 : η ∈ Z
      · have h2 : η' ∈ Z := (h1 : (openGraph η).Reachable s z).mono (openGraph_le hle)
        rw [ind_of_mem h1, ind_of_mem h2]
      · rw [ind_of_not_mem h1]; exact ind_nonneg _ _
    have harris := integral_harris p' (fun η => g (openEdgeCluster η s)) (fun η => ind Z η) hgC
      hZmono (fun η => hg0 _) (fun η => ind_nonneg _ _)
    have hZint : ∫ η, g (openEdgeCluster η s) * ind Z η ∂(prodBernoulli p') =
        ∫ η in Z, g (openEdgeCluster η s) ∂(prodBernoulli p') := by
      rw [integral_prodBernoulli_eq_sum, setIntegral_eq_sum p' Z]
    have hZmass : ∫ η, ind Z η ∂(prodBernoulli p') = (prodBernoulli p').real Z := by
      rw [integral_prodBernoulli_eq_sum, measureReal_eq_sum p' Z]
    rw [hZint, hZmass] at harris
    set IZ := ∫ η in Z, g (openEdgeCluster η s) ∂(prodBernoulli p') with hIZ
    set IY := ∫ η in Y, g (openEdgeCluster η s) ∂(prodBernoulli p') with hIY
    set I1 := ∫ η, g (openEdgeCluster η s) ∂(prodBernoulli p') with hI1
    set mZ := (prodBernoulli p').real Z with hmZ
    set mY := (prodBernoulli p').real Y with hmY
    set mN := (prodBernoulli p').real Yᶜ with hmN
    set mNW := (prodBernoulli p').real (Yᶜ ∩ W) with hmNW
    change mNW * (IY - I1 * mY) ≤ mN * (IZ - I1 * mZ) at mdl
    change I1 * mZ ≤ IZ at harris
    -- the pointwise inequality `T_A`-integrand ≤ `R_1`-integrand
    have hcovZ : 0 ≤ IZ - I1 * mZ := by linarith
    have key : mNW / mN * (IY - I1 * mY) ≤ IZ - I1 * mZ := by
      by_cases hN : mN = 0
      · rw [hN, div_zero, zero_mul]; exact hcovZ
      · have hpos : 0 < mN := lt_of_le_of_ne measureReal_nonneg (Ne.symm hN)
        rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
        linarith
    have hfinal : 0 ≤ a * ((IZ - I1 * mZ) - mNW / mN * (IY - I1 * mY)) :=
      mul_nonneg ha0 (sub_nonneg.2 key)
    have hid : a * IZ - b * IY - I1 * (a * mZ - b * mY) - (a * (mNW / mN) - b) * (IY - I1 * mY) =
        a * ((IZ - I1 * mZ) - mNW / mN * (IY - I1 * mY)) := by ring
    linarith [hfinal, hid]
  -- the reduction theorem
  have main := BHK2006_clusterConditionalCov_nonneg_of_within_of_forall_nondegenerate w s X h hcont hR F hF
  -- rewrite its conclusion into the MDLX shape
  have c1 : ∫ ω in D, F (openEdgeCluster ω s) * h w (openEdgeCluster ω s) ∂(prodBernoulli w) =
      (prodBernoulli w).real Ay * (∫ ω in D ∩ Z, F (openEdgeCluster ω s) ∂(prodBernoulli w)) -
        (prodBernoulli w).real (Ay ∩ W) * (∫ ω in D ∩ Y, F (openEdgeCluster ω s) ∂(prodBernoulli w)) :=
    intZY w _ _ F D
  have c2 : ∫ ω in D, h w (openEdgeCluster ω s) ∂(prodBernoulli w) =
      (prodBernoulli w).real Ay * (prodBernoulli w).real (D ∩ Z) -
        (prodBernoulli w).real (Ay ∩ W) * (prodBernoulli w).real (D ∩ Y) :=
    intH w _ _ D
  change 0 ≤ (prodBernoulli w).real D * (∫ ω in D, F (openEdgeCluster ω s) * h w (openEdgeCluster ω s)
      ∂(prodBernoulli w)) - (∫ ω in D, F (openEdgeCluster ω s) ∂(prodBernoulli w)) *
        (∫ ω in D, h w (openEdgeCluster ω s) ∂(prodBernoulli w)) at main
  rw [c1, c2] at main
  change (prodBernoulli w).real (Ay ∩ W) * ((prodBernoulli w).real D *
        (∫ ω in D ∩ Y, F (openEdgeCluster ω s) ∂(prodBernoulli w)) -
      (∫ ω in D, F (openEdgeCluster ω s) ∂(prodBernoulli w)) * (prodBernoulli w).real (D ∩ Y)) ≤
    (prodBernoulli w).real Ay * ((prodBernoulli w).real D *
        (∫ ω in D ∩ Z, F (openEdgeCluster ω s) ∂(prodBernoulli w)) -
      (∫ ω in D, F (openEdgeCluster ω s) ∂(prodBernoulli w)) * (prodBernoulli w).real (D ∩ Z))
  linarith [main]

end HullPort

end Percolation.Continuity
