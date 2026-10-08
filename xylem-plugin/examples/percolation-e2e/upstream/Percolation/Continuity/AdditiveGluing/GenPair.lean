import Percolation.Literature.ConditionalPositiveAssociationProofs
import Percolation.Literature.KozmaNitzanClusterPropertyReal
import Percolation.Literature.PercolationEvents
import Percolation.Literature.PercolationProofs
import Percolation.Util.Linter

/-!
# The master form (GEN) of the localised union bound, for two relays

(GEN): for percolation with arbitrary edge weights, a monotone function `F` of vertex sets, an
observer `o` and relays `A`, with `m_a := E[F(C(a))]` and `S := C(o) ∩ A`: `E[F(C(o)); S ≠ ∅] ≥
E[min_{a ∈ S} m_a; S ≠ ∅]`. (AG-loc = the case `F(C) = 1{b ∈ C}`, file; (GEN) is the natural
induction target: it charges only the relays the observer holds.) THIS FILE PROVES (GEN) FOR `|A| =
2`:

* `AGloc.setIntegral_clusterFun_ge` — Harris in integral form for a monotone nonnegative cluster function and an increasing event
  (`μ(U)·∫ F(C(a)) ≤ ∫_U F(C(a))`), from the weight-sum Harris inequality `BHK2006.harris`;
* `AGloc.gen_pair` — for `F` monotone and nonnegative and `m₁ ≤ m₂` (`m_i = ∫ F(C(a_i))`):
  `μ(o ↔ a₁)·m₁ + μ(o ↔ a₂, o ↮ a₁)·m₂ ≤ ∫_{o ↔ {a₁,a₂}} F(C(o))`.
Proof = Kozma–Nitzan's "BHK four times" for a real monotone cluster property (`KNPreFKG.clusterFun_pair`, integral forms of
vdBHK Thms 1.3/1.4), in the WEIGHTED form `(x₁ + x₂)·∫_U f₀ ≥ x₁ ∫_U f₁ + x₂ ∫_U f₂` (`x_i = μ({a₁ ↮ a₂} ∩ {o ↔ a_i})`), plus Harris
`∫_U f_i ≥ μ(U) m_i` and `x₂ ≥ μ(o ↔ a₂, o ↮ a₁)`, `x₁ ≤ μ(o ↔ a₁)`.
[cite: KozmaNitzan2024, Thm. 7 (p. 32) with Thm. 1 (pp. 7–8)] [cite: VandenbergHaggstromKahn2005, Thms. 1.3–1.5 (pp. 6–8)]
-/

noncomputable section

namespace Percolation.Continuity.AGloc

open MeasureTheory Set
open Percolation.Literature.LatticeModels (prodBernoulli)
open Percolation.Literature Percolation.Literature.KNPreFKG
open Percolation.Literature.BHK2006 (weight harris integral_prodBernoulli_eq_sum weight_nonneg)
open DecisionTree (ind ind_of_mem ind_of_not_mem ind_nonneg)

variable {V : Type*} [Fintype V]

/-- **Harris, integral form**: for `F` monotone and nonnegative on vertex sets and an increasing event `U`,
`μ(U) · ∫ F(C(a)) dμ ≤ ∫_U F(C(a)) dμ`. [cite: VandenbergHaggstromKahn2005, §1 p. 6 ("Harris' inequality")] -/
theorem setIntegral_clusterFun_ge (w : Sym2 V → unitInterval) (a : V) (F : Set V → ℝ)
    (hF : ∀ S T : Set V, S ⊆ T → F S ≤ F T) (hF0 : ∀ S, 0 ≤ F S) (U : Set (BondConfig V)) (hU : IsUpperSet U) :
    (prodBernoulli w).real U * ∫ ω, F (openCluster ω a) ∂(prodBernoulli w) ≤
      ∫ ω in U, F (openCluster ω a) ∂(prodBernoulli w) := by
  classical
  set w' : Sym2 V → ℝ := fun e => ((w e : unitInterval) : ℝ) with hw'
  have hw0 : ∀ e, 0 ≤ w' e := fun e => (w e).2.1
  have hw1 : ∀ e, w' e ≤ 1 := fun e => (w e).2.2
  have hUm : MeasurableSet U := MeasurableSet.of_discrete
  set f : Set (Sym2 V) → ℝ := fun ω => F (openCluster ω a) with hf
  have hfmono : Monotone f := fun ω ω' h => hF _ _ (openCluster_mono h a)
  have hgmono : Monotone (ind U) := fun ω ω' h => by
    by_cases hω : ω ∈ U
    · rw [ind_of_mem hω, ind_of_mem (hU h hω)]
    · rw [ind_of_not_mem hω]; exact ind_nonneg U ω'
  have key := harris hw0 hw1 (f := f) (g := ind U) (fun ω => hF0 _) (fun ω => ind_nonneg U ω) hfmono hgmono
  have hm : ∑ ω, weight w' ω = 1 := by
    have h1 := integral_prodBernoulli_eq_sum w fun _ => (1 : ℝ)
    simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at h1
    exact h1.symm
  have hI : ∫ ω, F (openCluster ω a) ∂(prodBernoulli w) = ∑ ω, weight w' ω * f ω :=
    integral_prodBernoulli_eq_sum w f
  have hUr : (prodBernoulli w).real U = ∑ ω, weight w' ω * ind U ω := by
    rw [← integral_indicator_one hUm, integral_prodBernoulli_eq_sum]
    refine Finset.sum_congr rfl fun ω _ => ?_
    by_cases hω : ω ∈ U
    · rw [Set.indicator_of_mem hω, ind_of_mem hω, Pi.one_apply]
    · simp [Set.indicator_of_notMem hω, ind_of_not_mem hω]
  have hIU : ∫ ω in U, F (openCluster ω a) ∂(prodBernoulli w) = ∑ ω, weight w' ω * (f ω * ind U ω) := by
    rw [← integral_indicator hUm, integral_prodBernoulli_eq_sum]
    refine Finset.sum_congr rfl fun ω _ => ?_
    by_cases hω : ω ∈ U
    · rw [Set.indicator_of_mem hω, ind_of_mem hω, mul_one]
    · simp [Set.indicator_of_notMem hω, ind_of_not_mem hω]
  rw [hI, hUr, hIU]
  rw [hm, one_mul] at key
  linarith [key, mul_comm (∑ ω, weight w' ω * f ω) (∑ ω, weight w' ω * ind U ω)]

/-- **(GEN) for two relays.** For `F` monotone and nonnegative on vertex sets, relays `a₁, a₂` with
`∫ F(C(a₁)) ≤ ∫ F(C(a₂))`, and an observer `o`:
`μ(o ↔ a₁)·∫ F(C(a₁)) + μ(o ↔ a₂, o ↮ a₁)·∫ F(C(a₂)) ≤ ∫_{o ↔ a₁ ∨ o ↔ a₂} F(C(o))` — the value of `F` on the observer's cluster,
when it holds a relay, is on average at least the mean value of the least-valued relay it holds.
[cite: KozmaNitzan2024, Thm. 7 (p. 32) with Thm. 1 (pp. 7–8)] -/
theorem gen_pair (w : Sym2 V → unitInterval) (o a₁ a₂ : V) (F : Set V → ℝ)
    (hF : ∀ S T : Set V, S ⊆ T → F S ≤ F T) (hF0 : ∀ S, 0 ≤ F S)
    (hm : ∫ ω, F (openCluster ω a₁) ∂(prodBernoulli w) ≤ ∫ ω, F (openCluster ω a₂) ∂(prodBernoulli w)) :
    (prodBernoulli w).real (openConn o a₁) * ∫ ω, F (openCluster ω a₁) ∂(prodBernoulli w) +
        (prodBernoulli w).real (openConn o a₂ ∩ (openConn o a₁)ᶜ : Set (BondConfig V)) *
          ∫ ω, F (openCluster ω a₂) ∂(prodBernoulli w) ≤
      ∫ ω in (openConn o a₁ ∪ openConn o a₂), F (openCluster ω o) ∂(prodBernoulli w) := by
  classical
  set μ := prodBernoulli w with hμ
  set f₀ : BondConfig V → ℝ := fun ω => F (openCluster ω o) with hf₀
  set f₁ : BondConfig V → ℝ := fun ω => F (openCluster ω a₁) with hf₁
  set f₂ : BondConfig V → ℝ := fun ω => F (openCluster ω a₂) with hf₂
  set m₁ : ℝ := ∫ ω, f₁ ω ∂μ with hm₁
  set m₂ : ℝ := ∫ ω, f₂ ω ∂μ with hm₂
  have hmeas : ∀ T : Set (BondConfig V), MeasurableSet T := fun _ => MeasurableSet.of_discrete
  have hint : ∀ (k : BondConfig V → ℝ) (T : Set (BondConfig V)), IntegrableOn k T μ :=
    fun k T => (Integrable.of_finite).integrableOn
  have hup : ∀ x y : V, IsUpperSet (openConn x y : Set (BondConfig V)) := fun x y => isUpperSet_openConn x y
  have hn := fun (S : Set (BondConfig V)) => (measureReal_nonneg : 0 ≤ μ.real S)
  set O₁ : Set (BondConfig V) := openConn o a₁ with hO₁
  set O₂ : Set (BondConfig V) := openConn o a₂ with hO₂
  set D : Set (BondConfig V) := {ω | ¬ (openGraph ω).Reachable a₁ a₂} with hD
  set U : Set (BondConfig V) := O₁ ∪ O₂ with hU
  -- nonnegativity of integrals and `m₁ ≥ 0`
  have hI0 : ∀ (k : BondConfig V → ℝ) (T : Set (BondConfig V)), (∀ ω, 0 ≤ k ω) → 0 ≤ ∫ ω in T, k ω ∂μ :=
    fun k T hk => setIntegral_nonneg (hmeas T) fun ω _ => hk ω
  -- Harris for `f₁, f₂` on `U`, and for `f₁` on `O₁`
  have hHU1 : μ.real U * m₁ ≤ ∫ ω in U, f₁ ω ∂μ :=
    setIntegral_clusterFun_ge w a₁ F hF hF0 U ((hup o a₁).union (hup o a₂))
  have hHU2 : μ.real U * m₂ ≤ ∫ ω in U, f₂ ω ∂μ :=
    setIntegral_clusterFun_ge w a₂ F hF hF0 U ((hup o a₁).union (hup o a₂))
  have hHO1 : μ.real O₁ * m₁ ≤ ∫ ω in O₁, f₁ ω ∂μ := setIntegral_clusterFun_ge w a₁ F hF hF0 O₁ (hup o a₁)
  -- same cluster ⇒ same value
  have h01 : ∀ ω ∈ O₁, f₀ ω = f₁ ω := fun ω hω => by
    simp only [hf₀, hf₁]; rw [openCluster_eq_of_reachable (hω : (openGraph ω).Reachable o a₁)]
  have h02 : ∀ ω ∈ O₂, f₀ ω = f₂ ω := fun ω hω => by
    simp only [hf₀, hf₂]; rw [openCluster_eq_of_reachable (hω : (openGraph ω).Reachable o a₂)]
  -- the degenerate bound `μ(O₁) m₁ ≤ ∫_U f₀` (`∫_U f₀ ≥ ∫_{O₁} f₀ = ∫_{O₁} f₁`)
  have hE_O1 : μ.real O₁ * m₁ ≤ ∫ ω in U, f₀ ω ∂μ := by
    have h1 : ∫ ω in O₁, f₁ ω ∂μ = ∫ ω in O₁, f₀ ω ∂μ := (setIntegral_congr_fun (hmeas O₁) h01).symm
    have h2 : ∫ ω in O₁, f₀ ω ∂μ ≤ ∫ ω in U, f₀ ω ∂μ :=
      setIntegral_mono_set (hint f₀ U) (Filter.Eventually.of_forall fun ω => hF0 _)
        (Filter.Eventually.of_forall (subset_union_left : O₁ ⊆ U))
    linarith
  -- `μ(U) = μ(O₁) + μ(O₂ ∖ O₁)`, `O₂ ∖ O₁ ⊆ D ∩ O₂`, `D ∩ O₁ ⊆ O₁`
  have hsplitμ : ∀ A S : Set (BondConfig V), μ.real A = μ.real (A ∩ S) + μ.real (A ∩ Sᶜ) := by
    intro A S
    rw [← measureReal_inter_add_sdiff (s := A) (h := measure_ne_top _ _) (hmeas S), Set.sdiff_eq]
  have hUμ : μ.real U = μ.real O₁ + μ.real (O₂ ∩ O₁ᶜ) := by
    rw [hsplitμ U O₁]
    congr 1
    · rw [inter_eq_right.2 subset_union_left]
    · congr 1
      ext ω
      simp only [hU, mem_inter_iff, mem_union, mem_compl_iff]
      tauto
  have hx2 : μ.real (O₂ ∩ O₁ᶜ) ≤ μ.real (D ∩ O₂) := by
    refine measureReal_mono ?_ (measure_ne_top _ _)
    rintro ω ⟨h2, hn1⟩
    refine ⟨?_, h2⟩
    simp only [hD, mem_setOf_eq]
    intro h12
    simp only [hO₁, hO₂, openConn, mem_setOf_eq, mem_compl_iff] at h2 hn1
    exact hn1 (h2.trans h12.symm)
  have hx1 : μ.real (D ∩ O₁) ≤ μ.real O₁ := measureReal_mono inter_subset_right (measure_ne_top _ _)
  by_cases h12 : a₁ = a₂
  · subst h12
    have h0 : μ.real (O₂ ∩ O₁ᶜ) = 0 := by
      rw [show O₂ ∩ O₁ᶜ = (∅ : Set (BondConfig V)) by rw [hO₁, hO₂]; exact inter_compl_self _]
      simp
    rw [h0, zero_mul, add_zero]
    exact hE_O1
  -- set identities (as in `KNPreFKG.clusterFun_pair`)
  have hU1 : U \ O₁ = D ∩ O₂ := by
    ext ω
    simp only [hU, hO₁, hO₂, hD, mem_sdiff, mem_union, mem_inter_iff, openConn, mem_setOf_eq]
    constructor
    · rintro ⟨h1 | h2, hn1⟩
      · exact absurd h1 hn1
      · exact ⟨fun h => hn1 (h2.trans h.symm), h2⟩
    · rintro ⟨hn, h2⟩
      exact ⟨Or.inr h2, fun h1 => hn (h1.symm.trans h2)⟩
  have hU2 : U \ O₂ = D ∩ O₁ := by
    ext ω
    simp only [hU, hO₁, hO₂, hD, mem_sdiff, mem_union, mem_inter_iff, openConn, mem_setOf_eq]
    constructor
    · rintro ⟨h1 | h2, hn2⟩
      · exact ⟨fun h => hn2 (h1.trans h), h1⟩
      · exact absurd h2 hn2
    · rintro ⟨hn, h1⟩
      exact ⟨Or.inl h1, fun h2 => hn (h1.symm.trans h2)⟩
  have hO1U : U ∩ O₁ = O₁ := inter_eq_right.2 subset_union_left
  have hO2U : U ∩ O₂ = O₂ := inter_eq_right.2 subset_union_right
  have hsplit : ∀ (k : BondConfig V → ℝ) (T : Set (BondConfig V)),
      ∫ ω in U, k ω ∂μ = ∫ ω in U ∩ T, k ω ∂μ + ∫ ω in U \ T, k ω ∂μ :=
    fun k T => (integral_inter_add_sdiff (hmeas T) (hint k U)).symm
  have hdiff1 : ∫ ω in U, f₀ ω ∂μ - ∫ ω in U, f₁ ω ∂μ =
      ∫ ω in D ∩ O₂, f₂ ω ∂μ - ∫ ω in D ∩ O₂, f₁ ω ∂μ := by
    rw [hsplit f₀ O₁, hsplit f₁ O₁, hO1U, hU1, setIntegral_congr_fun (hmeas O₁) h01,
      setIntegral_congr_fun ((hmeas D).inter (hmeas O₂)) fun ω hω => h02 ω hω.2]
    ring
  have hdiff2 : ∫ ω in U, f₀ ω ∂μ - ∫ ω in U, f₂ ω ∂μ =
      ∫ ω in D ∩ O₁, f₁ ω ∂μ - ∫ ω in D ∩ O₁, f₂ ω ∂μ := by
    rw [hsplit f₀ O₂, hsplit f₂ O₂, hO2U, hU2, setIntegral_congr_fun (hmeas O₂) h02,
      setIntegral_congr_fun ((hmeas D).inter (hmeas O₁)) fun ω hω => h01 ω hω.2]
    ring
  -- "Applying BHK 4 times" (integral forms), verbatim from `KNPreFKG.clusterFun_pair`
  have hD1 : {ω : BondConfig V | ∀ x ∈ ({a₂} : Set V), ¬ (openGraph ω).Reachable a₁ x} = D := by
    ext ω
    simp [hD]
  have hD2 : {ω : BondConfig V | ∀ x ∈ ({a₁} : Set V), ¬ (openGraph ω).Reachable a₂ x} = D := by
    ext ω
    simp only [mem_setOf_eq, mem_singleton_iff, forall_eq, hD]
    exact not_congr ⟨SimpleGraph.Reachable.symm, SimpleGraph.Reachable.symm⟩
  have hD3 : {ω : BondConfig V | ¬ (openGraph ω).Reachable a₂ a₁} = D := by
    ext ω
    simp only [mem_setOf_eq, hD]
    exact not_congr ⟨SimpleGraph.Reachable.symm, SimpleGraph.Reachable.symm⟩
  have hind1 : ∀ ω : BondConfig V, (connFamily a₁ o).indicator (1 : Set (Sym2 V) → ℝ) (openEdgeCluster ω a₁) =
      O₁.indicator (1 : BondConfig V → ℝ) ω := fun ω => by
    rw [congrFun (indicator_comp_openEdgeCluster (connFamily a₁ o) a₁) ω, ← openConn_eq_setOf_connFamily,
      openConn_symm a₁ o]
  have hind2 : ∀ ω : BondConfig V, (connFamily a₂ o).indicator (1 : Set (Sym2 V) → ℝ) (openEdgeCluster ω a₂) =
      O₂.indicator (1 : BondConfig V → ℝ) ω := fun ω => by
    rw [congrFun (indicator_comp_openEdgeCluster (connFamily a₂ o) a₂) ω, ← openConn_eq_setOf_connFamily,
      openConn_symm a₂ o]
  have hprod : ∀ (T : Set (BondConfig V)) (k : BondConfig V → ℝ),
      ∫ ω in D, T.indicator (1 : BondConfig V → ℝ) ω * k ω ∂μ = ∫ ω in D ∩ T, k ω ∂μ := by
    intro T k
    rw [← setIntegral_mul_indicator_one μ D T k]
    refine setIntegral_congr_fun (hmeas D) fun ω _ => ?_
    ring
  have h_i := BHK2006_clusterConditionalPositiveAssociation_holds V w a₂ ({a₁} : Set V)
    ((connFamily a₂ o).indicator 1) (fun C => F {a | a = a₂ ∨ ∃ e ∈ C, a ∈ e})
    (monotone_indicator_one_of_isUpperSet (isUpperSet_connFamily a₂ o)) (monotone_clusterFun a₂ F hF)
    (by simpa using Ne.symm h12)
  simp only [hD2, clusterFun_openEdgeCluster, hind2] at h_i
  rw [setIntegral_indicator_one_eq, hprod O₂] at h_i
  have h_ii := BHK2006_twoClusterConditionalAssociation.negCorrelation
    BHK2006_twoClusterConditionalAssociation_holds V w a₂ a₁
    ((connFamily a₂ o).indicator 1) (fun C => F {a | a = a₁ ∨ ∃ e ∈ C, a ∈ e})
    (monotone_indicator_one_of_isUpperSet (isUpperSet_connFamily a₂ o)) (monotone_clusterFun a₁ F hF)
    (Ne.symm h12)
  simp only [hD3, clusterFun_openEdgeCluster, hind2] at h_ii
  rw [setIntegral_indicator_one_eq, hprod O₂] at h_ii
  have h_iii := BHK2006_clusterConditionalPositiveAssociation_holds V w a₁ ({a₂} : Set V)
    ((connFamily a₁ o).indicator 1) (fun C => F {a | a = a₁ ∨ ∃ e ∈ C, a ∈ e})
    (monotone_indicator_one_of_isUpperSet (isUpperSet_connFamily a₁ o)) (monotone_clusterFun a₁ F hF)
    (by simpa using h12)
  simp only [hD1, clusterFun_openEdgeCluster, hind1] at h_iii
  rw [setIntegral_indicator_one_eq, hprod O₁] at h_iii
  have h_iv := BHK2006_twoClusterConditionalAssociation.negCorrelation
    BHK2006_twoClusterConditionalAssociation_holds V w a₁ a₂
    ((connFamily a₁ o).indicator 1) (fun C => F {a | a = a₂ ∨ ∃ e ∈ C, a ∈ e})
    (monotone_indicator_one_of_isUpperSet (isUpperSet_connFamily a₁ o)) (monotone_clusterFun a₂ F hF)
    h12
  simp only [clusterFun_openEdgeCluster, hind1] at h_iv
  rw [setIntegral_indicator_one_eq, hprod O₁] at h_iv
  change μ.real (D ∩ O₂) * ∫ ω in D, f₂ ω ∂μ ≤ μ.real D * ∫ ω in D ∩ O₂, f₂ ω ∂μ at h_i
  change μ.real D * ∫ ω in D ∩ O₂, f₁ ω ∂μ ≤ μ.real (D ∩ O₂) * ∫ ω in D, f₁ ω ∂μ at h_ii
  change μ.real (D ∩ O₁) * ∫ ω in D, f₁ ω ∂μ ≤ μ.real D * ∫ ω in D ∩ O₁, f₁ ω ∂μ at h_iii
  change μ.real D * ∫ ω in D ∩ O₁, f₂ ω ∂μ ≤ μ.real (D ∩ O₁) * ∫ ω in D, f₂ ω ∂μ at h_iv
  -- one-sided bounds and the weighted form (6)
  have key1 : μ.real D * (∫ ω in U, f₀ ω ∂μ - ∫ ω in U, f₁ ω ∂μ) ≥
      μ.real (D ∩ O₂) * (∫ ω in D, f₂ ω ∂μ - ∫ ω in D, f₁ ω ∂μ) := by
    rw [hdiff1, mul_sub, mul_sub]
    linarith [h_i, h_ii]
  have key2 : μ.real D * (∫ ω in U, f₀ ω ∂μ - ∫ ω in U, f₂ ω ∂μ) ≥
      μ.real (D ∩ O₁) * (∫ ω in D, f₁ ω ∂μ - ∫ ω in D, f₂ ω ∂μ) := by
    rw [hdiff2, mul_sub, mul_sub]
    linarith [h_iii, h_iv]
  have key6 : μ.real D * (μ.real (D ∩ O₁) * (∫ ω in U, f₀ ω ∂μ - ∫ ω in U, f₁ ω ∂μ) +
      μ.real (D ∩ O₂) * (∫ ω in U, f₀ ω ∂μ - ∫ ω in U, f₂ ω ∂μ)) ≥ 0 := by
    have hx1n := hn (D ∩ O₁)
    have hx2n := hn (D ∩ O₂)
    nlinarith [mul_le_mul_of_nonneg_left key1 hx1n, mul_le_mul_of_nonneg_left key2 hx2n]
  by_cases hx : μ.real (D ∩ O₁) + μ.real (D ∩ O₂) = 0
  · have hx2z : μ.real (D ∩ O₂) = 0 := by linarith [hn (D ∩ O₁), hn (D ∩ O₂)]
    have h0 : μ.real (O₂ ∩ O₁ᶜ) = 0 := le_antisymm (hx2.trans hx2z.le) (hn _)
    rw [h0, zero_mul, add_zero]
    exact hE_O1
  · have hxpos : 0 < μ.real (D ∩ O₁) + μ.real (D ∩ O₂) := lt_of_le_of_ne (by positivity) (Ne.symm hx)
    have hDpos : 0 < μ.real D := by
      have : μ.real (D ∩ O₁) ≤ μ.real D := measureReal_mono inter_subset_left (measure_ne_top _ _)
      have : μ.real (D ∩ O₂) ≤ μ.real D := measureReal_mono inter_subset_left (measure_ne_top _ _)
      linarith
    have h6 : μ.real (D ∩ O₁) * (∫ ω in U, f₀ ω ∂μ - ∫ ω in U, f₁ ω ∂μ) +
        μ.real (D ∩ O₂) * (∫ ω in U, f₀ ω ∂μ - ∫ ω in U, f₂ ω ∂μ) ≥ 0 := by
      by_contra hneg
      have := mul_neg_of_pos_of_neg hDpos (lt_of_not_ge hneg)
      linarith [key6]
    have hprod' : μ.real (O₂ ∩ O₁ᶜ) * μ.real (D ∩ O₁) ≤ μ.real (D ∩ O₂) * μ.real O₁ :=
      mul_le_mul hx2 hx1 (hn _) (hn _)
    have hm' : 0 ≤ m₂ - m₁ := by linarith [hm]
    have hm1n : 0 ≤ m₁ := integral_nonneg fun ω => hF0 _
    have hgoal : (μ.real (D ∩ O₁) + μ.real (D ∩ O₂)) *
        (∫ ω in U, f₀ ω ∂μ - (μ.real O₁ * m₁ + μ.real (O₂ ∩ O₁ᶜ) * m₂)) ≥ 0 := by
      have hA : μ.real (D ∩ O₁) * ∫ ω in U, f₁ ω ∂μ ≥ μ.real (D ∩ O₁) * (μ.real U * m₁) :=
        mul_le_mul_of_nonneg_left hHU1 (hn _)
      have hB : μ.real (D ∩ O₂) * ∫ ω in U, f₂ ω ∂μ ≥ μ.real (D ∩ O₂) * (μ.real U * m₂) :=
        mul_le_mul_of_nonneg_left hHU2 (hn _)
      rw [hUμ] at hA hB
      nlinarith [h6, hA, hB, mul_le_mul_of_nonneg_left hprod' hm', hn O₁, hn (O₂ ∩ O₁ᶜ), hm1n]
    by_contra hlt
    have : (μ.real (D ∩ O₁) + μ.real (D ∩ O₂)) *
        (∫ ω in U, f₀ ω ∂μ - (μ.real O₁ * m₁ + μ.real (O₂ ∩ O₁ᶜ) * m₂)) < 0 :=
      mul_neg_of_pos_of_neg hxpos (by linarith [lt_of_not_ge hlt])
    linarith [hgoal]

end Percolation.Continuity.AGloc

end
