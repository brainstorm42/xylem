import Percolation.Literature.KozmaNitzanClusterProperty
import Percolation.Util.Linter

/-!
# Kozma–Nitzan's Conjecture 4 on its two proved classes — Theorems 7 and 8 — for REAL-valued monotone cluster properties

Source: G. Kozma, S. Nitzan, *A reduction of the
`θ(p_c) = 0` problem to a conjectured inequality*, arXiv:2401.12397 (2024) [KozmaNitzan2024], §5.1
(pp. 31–32: monotone cluster properties, **Conjecture 4**, **Theorems 7 and 8**), proved with the tools of
§2.2, §3.1 and §3.2 (Lemma 3, Theorem 1, Lemma 5, Theorem 4).  This file supplies the general (real-valued)
form announced in `KozmaNitzanClusterProperty.lean`, which reproduces Theorems 7 and 8 for `{0,1}`-valued properties only
(`KozmaNitzan2024_thm7_event`, `KozmaNitzan2024_thm8_event`).  Everything here is proved (from the BHK theorems
`BHK2006_clusterConditionalPositiveAssociation_holds` (Thm. 1.3) and
`BHK2006_twoClusterConditionalAssociation_holds` (Thm. 1.5), in their integral forms); no new definitions.

## Printed statements (arXiv:2401.12397, pp. 31–32)

§5.1 (p. 31): "Let `G` be a graph and let `f : G × {0,1}^{E(G)} → ℝ`. We say that `f` is a monotone
cluster property if it satisfies the following two requirements: (1) `f(v, ω)` depends only on `C_ω(v)`
the cluster of `v` in `ω`, and is increasing in it, i.e. if `C_ω(v) ⊆ C_ξ(v)` then `f(v, ω) ≤ f(v, ξ)`.
(2) if `{v, w} ∈ ω` then `f(v, ω) = f(w, ω)`."  (p. 32: "Examples of monotone cluster properties include
`f(v, ω) = |C_ω(v)|` and, for a fixed vertex `b`, `f(v, ω) = 𝟙{b ↔_ω v}`.")

**Conjecture 4** (p. 32): "For any graph `G`, any monotone cluster property `f`, any `A ⊂ G` and any
`0 ∈ G`, `E(f(0)·𝟙{0 ↔ A}) ≥ min_{a∈A} E(f(a)·𝟙{0 ↔ A})`."

**Theorem 7** (p. 32): "Conjecture 4 holds when `|A| = 2`, for any `f`."

**Theorem 8** (p. 32): "Conjecture 4 holds in any `G` in which `0` is an isolated vertex in `G ∖ A`,
for any `f`."  ("We omit the proof of these theorems, as they do not contain any ideas which we did
not already use in § 3.")

## What is reproduced, and how

On a finite vertex type every monotone cluster property is `f(v, ω) = F(C_ω(v))` for a real function `F`
of vertex sets increasing along nonempty sets (requirement (1); requirement (2) is then automatic since
joined vertices have the same cluster).  The development is written for `F` increasing on ALL vertex sets
and transferred to the printed generality at the end (`KNPreFKG.monotoneOnNonempty_extension`: the value of
`F` at `∅` is never read on a cluster).  In the order of the file:

* `KozmaNitzan2024_lemma3_ii_real` — Lemma 3(ii) (pp. 6–7) for a real monotone cluster property: if
  `E F(C(a₁)) ≤ E F(C(a₂))` and `Q` is a decreasing event in the (edge) cluster of `a₁`, then
  `E[F(C(a₁)); Q] ≤ E[F(C(a₂)); Q]`.  As printed: on `{a₁ ↔ a₂}` the clusters coincide; on `{a₁ ↮ a₂}`,
  BHK Thm. 1.3 (increasing `F(C(a₁))` against decreasing `𝟙_Q`, both in `C_{a₁}`) and Thm. 1.5
  (`F(C(a₂))` increasing in `C_{a₂}` against `𝟙_Q` decreasing in `C_{a₁}`), in integral form.
* `KozmaNitzan2024_lemma5_real` — Lemma 5 (p. 13) for a real monotone cluster property: for `a, v ≠ 0`,
  `v ∈ B`, if `E_{G∖{0}} F(C(a)) ≤ E_{G∖{0}} F(C(v))` then `E[F(C(a)); σ_B] ≤ E[F(C(0)); σ_B]`, `σ_B` the
  star event of Lemma 5 (`KNPreFKG.starEvent`).  Under `σ_B`, `C(0) = {0} ∪ ⋃_{u∈B} C_{G∖0}(u)` and `C(a)`
  is `C_{G∖0}(a)` if `a ↮ B` off `0`, contained in `C(0)` otherwise; the star of `0` is independent of the
  pairs off `0` (`KNPreFKG.setIntegral_starEvent_comp_restrict`), and on `G ∖ {0}` the real Lemma 3(ii)
  with `Q = {a ↮ B}` is used.
* `KozmaNitzan2024_thm8_real` — **Theorem 8**: if every pair `s(0,u)`, `u ∉ A`, `u ≠ 0`, has weight `0`
  and `A ≠ ∅`, then some `a ∈ A` has `E[F(C(a)); 0 ↔ A] ≤ E[F(C(0)); 0 ↔ A]`; along the printed proof of
  Theorem 4 (pp. 13–14): `a₀` minimising `E_{G∖{0}} F(C(a))`, Lemma 5 on each star `σ_B`, `∅ ≠ B ⊆ A`,
  summed over `B` (`KNPreFKG.setIntegral_eq_sum_inter_starEvent`).
* `KozmaNitzan2024_thm7_real` — **Theorem 7**: `|A| = 2`; along the printed proof of Theorem 1
  (pp. 7–8) with `𝟙{aᵢ ↔ b}` replaced by `F(C(aᵢ))`: remove the common part `{0 ↔ aᵢ}` (where
  `C(0) = C(aᵢ)`), then "BHK four times" given `{a₁ ↮ a₂}` (`KNPreFKG.clusterFun_pair`).
* `KozmaNitzan2024_thm8_clusterProperty`, `KozmaNitzan2024_thm7_clusterProperty` — the same two theorems
  for `F` increasing along nonempty vertex sets only (the printed notion).

Transcription (as in `KozmaNitzanPreFKG.lean` / `KozmaNitzanClusterProperty.lean`): finite weighted graph
= `w : Sym2 V → [0,1]` on a finite vertex type, `μ = prodBernoulli w`, `C_ω(x) = openCluster ω x` (the
VERTEX cluster, p. 4), `{0 ↔ A} = ⋃_{a∈A} openConn 0 a`, `E[f ; D] = ∫ ω in D, f ω ∂μ`,
"`0` isolated in `G ∖ A`" = `∀ u ≠ 0, u ∉ A → w s(0,u) = 0`, `E_{G∖{0}} F(C(x))` =
`∫ F {y | ω ∈ openConnIn {0}ᶜ x y} ∂μ` (the cluster of `x` avoiding `0`, which has the law of the cluster
in `G ∖ {0}`: `KNPreFKG.integral_comp_restrictConfig_val`).  The conclusion "`≥ min_{a∈A}`" is rendered
as "`∃ a ∈ A, E[f(a); 0↔A] ≤ E[f(0); 0↔A]`" (equivalent for finite nonempty `A`; for `A = ∅` the printed
minimum is over the empty set and the event `{0 ↔ A}` is empty).

## References

* [KozmaNitzan2024] G. Kozma, S. Nitzan, *A reduction of the θ(p_c) = 0 problem to a conjectured
  inequality*, arXiv:2401.12397v2 (2024), §2.2 (Lemma 3), §3.1 (Theorem 1), §3.2 (Lemma 5, Theorem 4),
  §5.1 (Conjecture 4, Theorems 7–8).
* [VandenbergHaggstromKahn2005] J. van den Berg, O. Häggström, J. Kahn, *Some conditional correlation inequalities for
  percolation and related processes*, Random Structures Algorithms 29 (2006) 417–435, Thms. 1.3, 1.5
  (proved in `ConditionalPositiveAssociationProofs.lean` and
  `TwoClusterConditionalAssociationProofs.lean`).
-/

noncomputable section

open MeasureTheory Set
open Percolation.Literature.LatticeModels (prodBernoulli)

namespace Percolation.Literature

variable {V : Type*}

namespace KNPreFKG

/-- A monotone function of vertex sets, read on the edge cluster of `s` through its vertex span, is a
monotone function of the edge cluster. [cite: KozmaNitzan2024, §5.1 (p. 31, requirement (1))] -/
theorem monotone_clusterFun (s : V) (F : Set V → ℝ) (hF : ∀ S T : Set V, S ⊆ T → F S ≤ F T) :
    Monotone fun C : Set (Sym2 V) => F {a | a = s ∨ ∃ e ∈ C, a ∈ e} := by
  intro C C' hCC'
  refine hF _ _ fun a ha => ?_
  rcases ha with h | ⟨e, he, hae⟩
  · exact Or.inl h
  · exact Or.inr ⟨e, hCC' he, hae⟩

/-- The vertex-span reading agrees with the vertex cluster. [folklore] -/
theorem clusterFun_openEdgeCluster (F : Set V → ℝ) (ω : BondConfig V) (s : V) :
    F {a | a = s ∨ ∃ e ∈ openEdgeCluster ω s, a ∈ e} = F (openCluster ω s) := by
  rw [openCluster_eq_setOf_openEdgeCluster]

section Real

variable [Fintype V]

/-- `f · 𝟙_Q` integrated over `D` is `f` integrated over `D ∩ Q`. [folklore] -/
theorem setIntegral_mul_indicator_one (μ : Measure (BondConfig V)) (D Q : Set (BondConfig V))
    (f : BondConfig V → ℝ) :
    ∫ ω in D, f ω * Q.indicator (1 : BondConfig V → ℝ) ω ∂μ = ∫ ω in D ∩ Q, f ω ∂μ := by
  classical
  have hQ : MeasurableSet Q := MeasurableSet.of_discrete
  have hfun : (fun ω => f ω * Q.indicator (1 : BondConfig V → ℝ) ω) = Q.indicator f := by
    funext ω
    by_cases h : ω ∈ Q
    · rw [indicator_of_mem h, indicator_of_mem h, Pi.one_apply, mul_one]
    · rw [indicator_of_notMem h, indicator_of_notMem h, mul_zero]
  rw [hfun, setIntegral_indicator hQ]

end Real

end KNPreFKG

/-! ### Lemma 3(ii) for a real-valued monotone cluster property -/

section Lemma3Real

open KNPreFKG

variable [Fintype V]

/-- **Kozma–Nitzan 2024, Lemma 3(ii), for a real-valued monotone cluster property** (pp. 6–7 with
§5.1, p. 31; the printed Theorems 7–8 are stated "for any `f`"): if `F` is monotone on vertex sets,
`E F(C(a₁)) ≤ E F(C(a₂))`, and `Q = {C_{a₁} ∈ 𝒬}` is a decreasing event in the (edge) cluster of `a₁`,
then `E[F(C(a₁)); Q] ≤ E[F(C(a₂)); Q]`.  Proof as printed for `{aᵢ ↔ b}` (and as in the event form
`KozmaNitzan2024_lemma3_ii_cluster`): on `{a₁ ↔ a₂}` the two clusters coincide; on `D = {a₁ ↮ a₂}`, BHK
Thm. 1.3 (increasing `F(C(a₁))` × decreasing `𝟙_Q` in `C_{a₁}`) and Thm. 1.5 (increasing in `C_{a₂}` ×
decreasing in `C_{a₁}`), in integral form. [cite: KozmaNitzan2024, Lemma 3(ii) (pp. 6–7) and §5.1 (pp. 31–32)] -/
theorem KozmaNitzan2024_lemma3_ii_real (w : Sym2 V → unitInterval) (a₁ a₂ : V) (F : Set V → ℝ)
    (hF : ∀ S T : Set V, S ⊆ T → F S ≤ F T)
    (h : ∫ ω, F (openCluster ω a₁) ∂(prodBernoulli w) ≤ ∫ ω, F (openCluster ω a₂) ∂(prodBernoulli w))
    {𝒬 : Set (Set (Sym2 V))} (h𝒬 : IsLowerSet 𝒬) :
    ∫ ω in {ω | openEdgeCluster ω a₁ ∈ 𝒬}, F (openCluster ω a₁) ∂(prodBernoulli w) ≤
      ∫ ω in {ω | openEdgeCluster ω a₁ ∈ 𝒬}, F (openCluster ω a₂) ∂(prodBernoulli w) := by
  classical
  set μ := prodBernoulli w with hμ
  by_cases h12 : a₁ = a₂
  · subst h12
    exact le_rfl
  set f₁ : BondConfig V → ℝ := fun ω => F (openCluster ω a₁) with hf₁
  set f₂ : BondConfig V → ℝ := fun ω => F (openCluster ω a₂) with hf₂
  set Q : Set (BondConfig V) := {ω | openEdgeCluster ω a₁ ∈ 𝒬} with hQ
  set D : Set (BondConfig V) := {ω | ¬ (openGraph ω).Reachable a₁ a₂} with hD
  have hmeas : ∀ S : Set (BondConfig V), MeasurableSet S := fun _ => MeasurableSet.of_discrete
  have hint : ∀ (g : BondConfig V → ℝ) (S : Set (BondConfig V)), IntegrableOn g S μ :=
    fun g S => (Integrable.of_finite).integrableOn
  -- on `Dᶜ` the two clusters coincide
  have hagree : ∀ ω, ω ∉ D → f₁ ω = f₂ ω := by
    intro ω hω
    have hr : (openGraph ω).Reachable a₁ a₂ := by
      by_contra hc
      exact hω hc
    simp only [hf₁, hf₂]
    rw [openCluster_eq_of_reachable hr]
  -- split an integral along `D`
  have hsplit : ∀ (g : BondConfig V → ℝ) (S : Set (BondConfig V)),
      ∫ ω in S, g ω ∂μ = ∫ ω in S ∩ D, g ω ∂μ + ∫ ω in S \ D, g ω ∂μ := by
    intro g S
    rw [integral_inter_add_sdiff (hmeas D) (hint g S)]
  have hdiff : ∀ S : Set (BondConfig V), ∫ ω in S \ D, f₁ ω ∂μ = ∫ ω in S \ D, f₂ ω ∂μ := by
    intro S
    refine setIntegral_congr_fun ((hmeas S).diff (hmeas D)) fun ω hω => ?_
    exact hagree ω hω.2
  -- the hypothesis restricted to `D`
  have hH : ∫ ω in D, f₁ ω ∂μ ≤ ∫ ω in D, f₂ ω ∂μ := by
    have e1 := integral_add_compl (hmeas D) (Integrable.of_finite : Integrable f₁ μ)
    have e2 := integral_add_compl (hmeas D) (Integrable.of_finite : Integrable f₂ μ)
    have e3 : ∫ ω in Dᶜ, f₁ ω ∂μ = ∫ ω in Dᶜ, f₂ ω ∂μ :=
      setIntegral_congr_fun (hmeas D).compl fun ω hω => hagree ω hω
    have h' : ∫ ω, f₁ ω ∂μ ≤ ∫ ω, f₂ ω ∂μ := h
    linarith
  -- (1) one-cluster BHK, increasing `F(C(a₁))` × decreasing `𝟙_Q`, given `D = {a₁ ↮ a₂}`
  have hD1 : {ω : BondConfig V | ∀ x ∈ ({a₂} : Set V), ¬ (openGraph ω).Reachable a₁ x} = D := by
    ext ω
    simp [hD]
  have h1 := BHK2006_clusterConditionalPositiveAssociation_holds.antitone_right V w a₁ ({a₂} : Set V)
    (fun C => F {a | a = a₁ ∨ ∃ e ∈ C, a ∈ e}) (𝒬.indicator 1) (monotone_clusterFun a₁ F hF)
    (antitone_indicator_one_of_isLowerSet h𝒬) (by simpa using h12)
  have hind : ∀ ω : BondConfig V, 𝒬.indicator (1 : Set (Sym2 V) → ℝ) (openEdgeCluster ω a₁) =
      Q.indicator (1 : BondConfig V → ℝ) ω := fun ω => congrFun (indicator_comp_openEdgeCluster 𝒬 a₁) ω
  simp only [hD1, clusterFun_openEdgeCluster, hind] at h1
  rw [setIntegral_indicator_one_eq, setIntegral_mul_indicator_one] at h1
  change μ.real D * ∫ ω in D ∩ Q, f₁ ω ∂μ ≤ (∫ ω in D, f₁ ω ∂μ) * μ.real (D ∩ Q) at h1
  -- h1 : μ.real D * ∫ in D ∩ Q, f₁ ≤ (∫ in D, f₁) * μ.real (D ∩ Q)
  -- (2) two-cluster BHK: increasing `F(C(a₂))` in `C_{a₂}` × decreasing `𝟙_Q` in `C_{a₁}`
  have hD2 : {ω : BondConfig V | ¬ (openGraph ω).Reachable a₂ a₁} = D := by
    ext ω
    simp only [mem_setOf_eq, hD]
    exact not_congr ⟨SimpleGraph.Reachable.symm, SimpleGraph.Reachable.symm⟩
  have h2 := BHK2006_twoClusterConditionalAssociation_holds V w a₂ a₁
    (fun C _ => F {a | a = a₂ ∨ ∃ e ∈ C, a ∈ e}) (fun _ D' => 𝒬.indicator (1 : Set (Sym2 V) → ℝ) D')
    (fun _ => monotone_clusterFun a₂ F hF) (fun _ => antitone_const) (fun _ => monotone_const)
    (fun _ => antitone_indicator_one_of_isLowerSet h𝒬) (Ne.symm h12)
  simp only [hD2, clusterFun_openEdgeCluster, hind] at h2
  rw [setIntegral_indicator_one_eq, setIntegral_mul_indicator_one] at h2
  change (∫ ω in D, f₂ ω ∂μ) * μ.real (D ∩ Q) ≤ μ.real D * ∫ ω in D ∩ Q, f₂ ω ∂μ at h2
  -- h2 : (∫ in D, f₂) * μ.real (D ∩ Q) ≤ μ.real D * ∫ in D ∩ Q, f₂
  have hcore : ∫ ω in D ∩ Q, f₁ ω ∂μ ≤ ∫ ω in D ∩ Q, f₂ ω ∂μ := by
    by_cases hD0 : μ.real D = 0
    · have hDQ0 : μ (D ∩ Q) = 0 := by
        have : μ.real (D ∩ Q) = 0 :=
          le_antisymm ((measureReal_mono inter_subset_left).trans hD0.le) measureReal_nonneg
        exact (measureReal_eq_zero_iff (measure_ne_top _ _)).1 this
      rw [setIntegral_measure_zero _ hDQ0, setIntegral_measure_zero _ hDQ0]
    · have hDpos : 0 < μ.real D := lt_of_le_of_ne measureReal_nonneg (Ne.symm hD0)
      have hDQ : 0 ≤ μ.real (D ∩ Q) := measureReal_nonneg
      have hchain : μ.real D * ∫ ω in D ∩ Q, f₁ ω ∂μ ≤ μ.real D * ∫ ω in D ∩ Q, f₂ ω ∂μ :=
        calc μ.real D * ∫ ω in D ∩ Q, f₁ ω ∂μ ≤ (∫ ω in D, f₁ ω ∂μ) * μ.real (D ∩ Q) := h1
          _ ≤ (∫ ω in D, f₂ ω ∂μ) * μ.real (D ∩ Q) := mul_le_mul_of_nonneg_right hH hDQ
          _ ≤ μ.real D * ∫ ω in D ∩ Q, f₂ ω ∂μ := h2
      exact le_of_mul_le_mul_left hchain hDpos
  -- conclude by adding the parts off `D`, where the integrands coincide
  show ∫ ω in Q, f₁ ω ∂μ ≤ ∫ ω in Q, f₂ ω ∂μ
  rw [hsplit f₁ Q, hsplit f₂ Q, inter_comm Q D, hdiff Q]
  linarith [hcore]

end Lemma3Real

/-! ### Lemma 5 for a real-valued monotone cluster property -/

namespace KNPreFKG

section Restrict

variable [Fintype V]

/-- **Change of variables along the restriction coupling** (integral form of
`real_preimage_restrictConfig_val`): for a function `g` of configurations on `S`,
`∫ g(ω|_S) dμ_w = ∫ g dμ_{w|_S}`. [cite: GrimmettPercolation1999, §1.3 p. 10 (product measure)] -/
theorem integral_comp_restrictConfig_val (w : Sym2 V → unitInterval) (S : Set V)
    (g : BondConfig S → ℝ) :
    ∫ ω, g (restrictConfig (Subtype.val : S → V) ω) ∂(prodBernoulli w) =
      ∫ ω', g ω' ∂(prodBernoulli (w ∘ Sym2.map (Subtype.val : S → V))) := by
  classical
  rw [← prodBernoulli_map_restrictConfig w Subtype.val_injective,
    integral_map (measurable_restrictConfig _).aemeasurable (Measurable.of_discrete).aestronglyMeasurable]

/-- **The star of `0` is independent of the pairs off `0`, integral form**: for a function `g` of the
configuration off `0`, `∫_{σ_B} g(ω|_{{0}ᶜ}) dμ = μ(σ_B) · ∫ g(ω|_{{0}ᶜ}) dμ`.
[cite: GrimmettPercolation1999, §2.2 (product measure)] -/
theorem setIntegral_starEvent_comp_restrict (w : Sym2 V → unitInterval) (o : V) (B : Set V)
    (g : BondConfig ({o}ᶜ : Set V) → ℝ) :
    ∫ ω in starEvent o B, g (restrictConfig (Subtype.val : ({o}ᶜ : Set V) → V) ω) ∂(prodBernoulli w) =
      (prodBernoulli w).real (starEvent o B) *
        ∫ ω, g (restrictConfig (Subtype.val : ({o}ᶜ : Set V) → V) ω) ∂(prodBernoulli w) := by
  classical
  set μ := prodBernoulli w with hμ
  set r := restrictConfig (Subtype.val : ({o}ᶜ : Set V) → V) with hr
  have hrm : Measurable r := measurable_restrictConfig _
  set σ := starEvent o B with hσdef
  have hσm : MeasurableSet σ := MeasurableSet.of_discrete
  -- the two measures `E ↦ μ(σ ∩ r⁻¹ E)` and `E ↦ μ(σ) μ(r⁻¹ E)` agree
  have key : (μ.restrict σ).map r = μ σ • μ.map r := by
    refine Measure.ext fun E hE => ?_
    rw [Measure.map_apply hrm hE, Measure.restrict_apply (hrm hE), Measure.smul_apply,
      Measure.map_apply hrm hE, smul_eq_mul]
    have hreal := real_starEvent_inter_preimage w o B E
    rw [measureReal_def, measureReal_def, measureReal_def, ← ENNReal.toReal_mul] at hreal
    rw [inter_comm]
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
      (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))).1 hreal
  have hg : AEStronglyMeasurable g ((μ.restrict σ).map r) :=
    (Measurable.of_discrete).aestronglyMeasurable
  have hg' : AEStronglyMeasurable g (μ.map r) := (Measurable.of_discrete).aestronglyMeasurable
  calc ∫ ω in σ, g (r ω) ∂μ = ∫ ω', g ω' ∂((μ.restrict σ).map r) :=
        (integral_map hrm.aemeasurable hg).symm
    _ = ∫ ω', g ω' ∂(μ σ • μ.map r) := by rw [key]
    _ = (μ σ).toReal * ∫ ω', g ω' ∂(μ.map r) := by
        rw [integral_smul_measure, smul_eq_mul]
    _ = μ.real σ * ∫ ω, g (r ω) ∂μ := by
        rw [measureReal_def, integral_map hrm.aemeasurable hg']

end Restrict

/-! #### The clusters under the star event `σ_B` -/

/-- Under `σ_B`, if `a ≠ 0` is not joined off `0` to `B ∖ {0}`, then its cluster is its cluster off `0`.
[cite: KozmaNitzan2024, Lemma 5 (p. 13)] -/
theorem openCluster_subset_off_of_starEvent {ω : BondConfig V} {o : V} {B : Set V}
    (hσ : ω ∈ starEvent o B) {a : V} (hao : a ≠ o)
    (hn : ∀ u ∈ B, u ≠ o → ω ∉ openConnIn ({o}ᶜ : Set V) a u) :
    openCluster ω a ⊆ {y | ω ∈ openConnIn ({o}ᶜ : Set V) a y} := by
  intro x hx
  have hxo : x ≠ o := by
    rintro rfl
    obtain ⟨p⟩ := (hx : (openGraph ω).Reachable a x).symm
    obtain ⟨u', hu'B, hu'o, hu'a⟩ := (walk_decomp hσ p hao).2 rfl
    obtain ⟨h1, h2, hr⟩ := hu'a
    exact hn u' hu'B hu'o ⟨h2, h1, hr.symm⟩
  obtain ⟨p⟩ := (hx : (openGraph ω).Reachable a x)
  rcases (walk_decomp hσ p hxo).1 hao with h | ⟨⟨u, huB, huo, hau⟩, _⟩
  · exact h
  · exact absurd hau (hn u huB huo)

/-- Under `σ_B`, if `a ≠ 0` is joined off `0` to `B ∖ {0}`, then its cluster lies inside `{0}` together
with the vertices joined off `0` to `B ∖ {0}`. [cite: KozmaNitzan2024, Lemma 5 (p. 13)] -/
theorem openCluster_subset_insert_of_starEvent {ω : BondConfig V} {o : V} {B : Set V}
    (hσ : ω ∈ starEvent o B) {a : V} (hao : a ≠ o)
    (hy : ∃ u ∈ B, u ≠ o ∧ ω ∈ openConnIn ({o}ᶜ : Set V) a u) :
    openCluster ω a ⊆ {o} ∪ {y | ∃ u ∈ B, u ≠ o ∧ ω ∈ openConnIn ({o}ᶜ : Set V) u y} := by
  obtain ⟨u, huB, huo, hau⟩ := hy
  intro x hx
  by_cases hxo : x = o
  · exact Or.inl hxo
  · right
    obtain ⟨p⟩ := (hx : (openGraph ω).Reachable a x)
    rcases (walk_decomp hσ p hxo).1 hao with h | ⟨_, ⟨u', hu'B, hu'o, hu'x⟩⟩
    · -- `a ↔ x` off `0` and `a ↔ u` off `0`
      obtain ⟨h1, h2, hr⟩ := hau
      exact ⟨u, huB, huo, openConnIn_trans ⟨h2, h1, hr.symm⟩ h⟩
    · exact ⟨u', hu'B, hu'o, hu'x⟩

/-- Under `σ_B`, `0` together with the vertices joined off `0` to `B ∖ {0}` lie in the cluster of `0`.
[cite: KozmaNitzan2024, Lemma 5 (p. 13)] -/
theorem insert_offClusterOf_subset_openCluster {ω : BondConfig V} {o : V} {B : Set V}
    (hσ : ω ∈ starEvent o B) :
    {o} ∪ {y | ∃ u ∈ B, u ≠ o ∧ ω ∈ openConnIn ({o}ᶜ : Set V) u y} ⊆ openCluster ω o := by
  intro x hx
  rcases hx with hxo | ⟨u, huB, huo, hux⟩
  · rw [mem_singleton_iff] at hxo
    subst hxo
    exact mem_openCluster_self ω x
  · have hou : s(o, u) ∈ ω := ((mem_starEvent_iff o B ω).1 hσ u huo).2 huB
    have hadj : (openGraph ω).Adj o u := (openGraph_adj ω o u).2 ⟨hou, huo.symm⟩
    exact hadj.reachable.trans (reachable_of_openConnIn hux)

/-- The off-`0` quantities read on the restricted configuration. [folklore] -/
theorem setOf_openConnIn_eq_image (o : V) (ω : BondConfig V) (x : ({o}ᶜ : Set V)) :
    {y | ω ∈ openConnIn ({o}ᶜ : Set V) (x : V) y} =
      Subtype.val '' openCluster (restrictConfig (Subtype.val : ({o}ᶜ : Set V) → V) ω) x :=
  (image_openCluster_restrictConfig o ω x).symm

/-- The set of vertices joined off `0` to `B ∖ {0}`, read on the restricted configuration. [folklore] -/
theorem offClusterOf_eq_image (o : V) (B : Set V) (ω : BondConfig V) :
    {y | ∃ u ∈ B, u ≠ o ∧ ω ∈ openConnIn ({o}ᶜ : Set V) u y} = Subtype.val ''
      {y' | ∃ u' : ({o}ᶜ : Set V), (u' : V) ∈ B ∧
        (openGraph (restrictConfig (Subtype.val : ({o}ᶜ : Set V) → V) ω)).Reachable u' y'} := by
  ext y
  constructor
  · rintro ⟨u, huB, huo, huy⟩
    have hyo : y ∈ ({o}ᶜ : Set V) := by
      obtain ⟨_, hy2, _⟩ := huy
      exact hy2
    have huS : u ∈ ({o}ᶜ : Set V) := mem_compl_singleton_iff.2 huo
    exact ⟨⟨y, hyo⟩, ⟨⟨u, huS⟩, huB,
      (reachable_restrictConfig_val_iff _ ω ⟨u, huS⟩ ⟨y, hyo⟩).2 huy⟩, rfl⟩
  · rintro ⟨y', ⟨u', hu'B, hu'y⟩, rfl⟩
    exact ⟨u', hu'B, mem_compl_singleton_iff.1 u'.2,
      (reachable_restrictConfig_val_iff _ ω u' y').1 hu'y⟩

end KNPreFKG

/-! #### Lemma 5, real-valued -/

open KNPreFKG in
/-- **Kozma–Nitzan's Lemma 5 for a real-valued monotone cluster property** (Lemma 5, p. 13, with
`{x ↔ b}` replaced by `F(C(x))`, `F` monotone on vertex sets — the step behind Theorem 8 "for any `f`",
p. 32).  Let `a, v ≠ 0`, `v ∈ B`, and suppose that in `G ∖ {0}` the cluster of `a` carries at most as much
`F` in the mean as the cluster of `v`: `E_{G∖{0}} F(C(a)) ≤ E_{G∖{0}} F(C(v))`.  Then
`E[F(C(a)); σ_B] ≤ E[F(C(0)); σ_B]`, `σ_B` the event that the open pairs at `0` are exactly those to `B`.
Proof: under `σ_B`, `C(a) = C_{G∖0}(a)` if `a ↮ B` off `0`, and otherwise `C(a) ⊆ {0} ∪ C_{G∖0}(B) ⊆ C(0)`
(`walk_decomp`); the star of `0` is independent of the pairs off `0` (`setIntegral_starEvent_comp_restrict`),
and on `G ∖ {0}` the real Lemma 3(ii) with `Q = {a ↮ B}` gives
`E'[F(C'(a)); a ↮ B] ≤ E'[F(C'(v)); a ↮ B] ≤ E'[F({0} ∪ C'(B)); a ↮ B]`.
[cite: KozmaNitzan2024, Lemma 5 (p. 13) and Thm. 8 (p. 32)] -/
theorem KozmaNitzan2024_lemma5_real {V : Type*} [Fintype V] (w : Sym2 V → unitInterval)
    (o a v : V) (B : Set V) (F : Set V → ℝ) (hF : ∀ S T : Set V, S ⊆ T → F S ≤ F T)
    (hao : a ≠ o) (hvo : v ≠ o) (hvB : v ∈ B)
    (hyp : ∫ ω, F {y | ω ∈ openConnIn ({o}ᶜ : Set V) a y} ∂(prodBernoulli w) ≤
      ∫ ω, F {y | ω ∈ openConnIn ({o}ᶜ : Set V) v y} ∂(prodBernoulli w)) :
    ∫ ω in starEvent o B, F (openCluster ω a) ∂(prodBernoulli w) ≤
      ∫ ω in starEvent o B, F (openCluster ω o) ∂(prodBernoulli w) := by
  classical
  set μ := prodBernoulli w with hμ
  -- the graph `G ∖ {0}`
  set S : Set V := {o}ᶜ with hS
  haveI : Fintype S := Fintype.ofFinite S
  set f : S → V := Subtype.val with hf
  set r := restrictConfig f with hr
  set w' : Sym2 S → unitInterval := w ∘ Sym2.map f with hw'
  set μ' := prodBernoulli w' with hμ'
  have haS : a ∈ S := mem_compl_singleton_iff.2 hao
  have hvS : v ∈ S := mem_compl_singleton_iff.2 hvo
  set a' : S := ⟨a, haS⟩ with ha'
  set v' : S := ⟨v, hvS⟩ with hv'
  set B' : Set S := {u | (u : V) ∈ B} with hB'
  have hvB' : v' ∈ B' := hvB
  -- the property transported to vertex sets of `G ∖ {0}` (read back in `G`)
  set F' : Set S → ℝ := fun T => F (Subtype.val '' T) with hF'
  have hF'mono : ∀ T T' : Set S, T ⊆ T' → F' T ≤ F' T' :=
    fun T T' hTT' => hF _ _ (image_mono hTT')
  -- the glued-cluster reading `h` and the two-case reading `g` on `G ∖ {0}`
  set CB : BondConfig S → Set S := fun ω' => {y' | ∃ u' : S, (u' : V) ∈ B ∧ (openGraph ω').Reachable u' y'}
    with hCB
  set h : BondConfig S → ℝ := fun ω' => F ({o} ∪ Subtype.val '' CB ω') with hh
  set N : Set (BondConfig S) := {ω' | ∀ u ∈ B', ¬ (openGraph ω').Reachable a' u} with hN
  set g : BondConfig S → ℝ := fun ω' => if ω' ∈ N then F' (openCluster ω' a') else h ω' with hg
  have hmeasS : ∀ T : Set (BondConfig S), MeasurableSet T := fun _ => MeasurableSet.of_discrete
  have hmeas : ∀ T : Set (BondConfig V), MeasurableSet T := fun _ => MeasurableSet.of_discrete
  -- (1) pointwise on `σ_B`: `F(C(a)) ≤ g(ω|)` and `h(ω|) ≤ F(C(0))`
  have hoff : ∀ ω, {y | ∃ u ∈ B, u ≠ o ∧ ω ∈ openConnIn ({o}ᶜ : Set V) u y} = Subtype.val '' CB (r ω) :=
    fun ω => offClusterOf_eq_image o B ω
  have hN_iff : ∀ ω, r ω ∈ N ↔ ∀ u ∈ B, u ≠ o → ω ∉ openConnIn ({o}ᶜ : Set V) a u := by
    intro ω
    constructor
    · intro hn u huB huo hau
      have huS : u ∈ S := mem_compl_singleton_iff.2 huo
      exact hn ⟨u, huS⟩ huB ((reachable_restrictConfig_val_iff S ω a' ⟨u, huS⟩).2 hau)
    · intro hn u huB hau
      exact hn u huB (mem_compl_singleton_iff.1 u.2) ((reachable_restrictConfig_val_iff S ω a' u).1 hau)
  have hle_a : ∀ ω ∈ starEvent o B, F (openCluster ω a) ≤ g (r ω) := by
    intro ω hσ
    by_cases hn : r ω ∈ N
    · rw [hg]
      simp only [hn, if_true]
      rw [hF']
      change F (openCluster ω a) ≤ F (Subtype.val '' openCluster (restrictConfig Subtype.val ω) a')
      rw [← setOf_openConnIn_eq_image]
      exact hF _ _ (openCluster_subset_off_of_starEvent hσ hao ((hN_iff ω).1 hn))
    · rw [hg]
      simp only [hn, if_false]
      rw [hh]
      change F (openCluster ω a) ≤ F ({o} ∪ Subtype.val '' CB (r ω))
      rw [← hoff]
      refine hF _ _ (openCluster_subset_insert_of_starEvent hσ hao ?_)
      have hn' := mt (hN_iff ω).2 hn
      push Not at hn'
      obtain ⟨u, huB, huo, hau⟩ := hn'
      exact ⟨u, huB, huo, hau⟩
  have hle_o : ∀ ω ∈ starEvent o B, h (r ω) ≤ F (openCluster ω o) := by
    intro ω hσ
    rw [hh]
    change F ({o} ∪ Subtype.val '' CB (r ω)) ≤ F (openCluster ω o)
    rw [← hoff]
    exact hF _ _ (insert_offClusterOf_subset_openCluster hσ)
  -- (2) on `G ∖ {0}`: `∫ g ≤ ∫ h`, by the real Lemma 3(ii) with `Q = {a ↮ B}`
  have hyp' : ∫ ω', F' (openCluster ω' a') ∂μ' ≤ ∫ ω', F' (openCluster ω' v') ∂μ' := by
    have e1 : ∫ ω, F {y | ω ∈ openConnIn ({o}ᶜ : Set V) a y} ∂μ = ∫ ω', F' (openCluster ω' a') ∂μ' := by
      rw [hμ', hw', hf, ← integral_comp_restrictConfig_val]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      change F {y | ω ∈ openConnIn ({o}ᶜ : Set V) a y} = F (Subtype.val '' openCluster (restrictConfig Subtype.val ω) a')
      rw [← setOf_openConnIn_eq_image]
    have e2 : ∫ ω, F {y | ω ∈ openConnIn ({o}ᶜ : Set V) v y} ∂μ = ∫ ω', F' (openCluster ω' v') ∂μ' := by
      rw [hμ', hw', hf, ← integral_comp_restrictConfig_val]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      change F {y | ω ∈ openConnIn ({o}ᶜ : Set V) v y} = F (Subtype.val '' openCluster (restrictConfig Subtype.val ω) v')
      rw [← setOf_openConnIn_eq_image]
    rw [← e1, ← e2]
    exact hyp
  have hN_eq : N = {ω' | openEdgeCluster ω' a' ∈ disconnFamily a' B'} := setOf_forall_not_reachable_eq a' B'
  have L3 : ∫ ω' in N, F' (openCluster ω' a') ∂μ' ≤ ∫ ω' in N, F' (openCluster ω' v') ∂μ' := by
    rw [hN_eq]
    exact KozmaNitzan2024_lemma3_ii_real w' a' v' F' hF'mono hyp' (isLowerSet_disconnFamily a' B')
  have hv_le_h : ∀ ω', F' (openCluster ω' v') ≤ h ω' := by
    intro ω'
    refine hF _ _ (image_subset_iff.2 fun y' hy' => ?_)
    exact Or.inr ⟨y', ⟨v', hvB, hy'⟩, rfl⟩
  have hint' : ∀ (k : BondConfig S → ℝ) (T : Set (BondConfig S)), IntegrableOn k T μ' :=
    fun k T => (Integrable.of_finite).integrableOn
  have hgh : ∫ ω', g ω' ∂μ' ≤ ∫ ω', h ω' ∂μ' := by
    have eg := integral_add_compl (hmeasS N) (Integrable.of_finite : Integrable g μ')
    have eh := integral_add_compl (hmeasS N) (Integrable.of_finite : Integrable h μ')
    have eg1 : ∫ ω' in N, g ω' ∂μ' = ∫ ω' in N, F' (openCluster ω' a') ∂μ' :=
      setIntegral_congr_fun (hmeasS N) fun ω' hω' => by simp only [hg, hω', if_true]
    have eg2 : ∫ ω' in Nᶜ, g ω' ∂μ' = ∫ ω' in Nᶜ, h ω' ∂μ' :=
      setIntegral_congr_fun (hmeasS N).compl fun ω' hω' => by
        simp only [hg, show ω' ∉ N from hω', if_false]
    have e3 : ∫ ω' in N, F' (openCluster ω' v') ∂μ' ≤ ∫ ω' in N, h ω' ∂μ' :=
      setIntegral_mono_on (hint' _ N) (hint' _ N) (hmeasS N) fun ω' _ => hv_le_h ω'
    linarith
  -- (3) assemble with the independence of `σ_B` from the pairs off `0`
  have hintV : ∀ (k : BondConfig V → ℝ) (T : Set (BondConfig V)), IntegrableOn k T μ :=
    fun k T => (Integrable.of_finite).integrableOn
  have hσnn : 0 ≤ μ.real (starEvent o B) := measureReal_nonneg
  calc ∫ ω in starEvent o B, F (openCluster ω a) ∂μ
      ≤ ∫ ω in starEvent o B, g (r ω) ∂μ :=
        setIntegral_mono_on (hintV _ _) (hintV _ _) (hmeas _) hle_a
    _ = μ.real (starEvent o B) * ∫ ω, g (r ω) ∂μ := setIntegral_starEvent_comp_restrict w o B g
    _ = μ.real (starEvent o B) * ∫ ω', g ω' ∂μ' := by
        rw [hμ', hw', hr, hf, integral_comp_restrictConfig_val]
    _ ≤ μ.real (starEvent o B) * ∫ ω', h ω' ∂μ' := mul_le_mul_of_nonneg_left hgh hσnn
    _ = μ.real (starEvent o B) * ∫ ω, h (r ω) ∂μ := by
        rw [hμ', hw', hr, hf, integral_comp_restrictConfig_val]
    _ = ∫ ω in starEvent o B, h (r ω) ∂μ := (setIntegral_starEvent_comp_restrict w o B h).symm
    _ ≤ ∫ ω in starEvent o B, F (openCluster ω o) ∂μ :=
        setIntegral_mono_on (hintV _ _) (hintV _ _) (hmeas _) hle_o

/-! ### Theorem 8 for a real-valued monotone cluster property: `0` isolated in `G ∖ A` -/

namespace KNPreFKG

variable [Fintype V]

/-- **The stars of `0` partition the space, integral form** (from `real_eq_sum_inter_starEvent`): if
every pair `s(0,u)` with `u ∉ A`, `u ≠ 0` has weight `0` and `0 ∉ A`, then for every event `E` and every
`g`, `∫_E g dμ = Σ_{B ⊆ A} ∫_{E ∩ σ_B} g dμ`. [cite: KozmaNitzan2024, proof of Thm. 4 (pp. 13–14, "Summing over all B")] -/
theorem setIntegral_eq_sum_inter_starEvent (w : Sym2 V → unitInterval) (A : Finset V) (o : V)
    (ho : o ∉ A) (hiso : ∀ u, u ≠ o → u ∉ A → w s(o, u) = 0) (E : Set (BondConfig V))
    (g : BondConfig V → ℝ) :
    ∫ ω in E, g ω ∂(prodBernoulli w) =
      ∑ B ∈ A.powerset, ∫ ω in E ∩ starEvent o ↑B, g ω ∂(prodBernoulli w) := by
  classical
  set μ := prodBernoulli w with hμ
  have key : μ.restrict E = ∑ B ∈ A.powerset, μ.restrict (E ∩ starEvent o ↑B) := by
    refine Measure.ext fun T hT => ?_
    rw [Measure.restrict_apply hT, Measure.coe_finsetSum, Finset.sum_apply]
    simp only [Measure.restrict_apply hT]
    have hreal := real_eq_sum_inter_starEvent w A o ho hiso (T ∩ E)
    simp only [measureReal_def, inter_assoc] at hreal
    rw [← ENNReal.toReal_sum (fun B _ => measure_ne_top _ _)] at hreal
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
      (ENNReal.sum_ne_top.2 fun B _ => measure_ne_top _ _)).1 hreal
  change ∫ ω, g ω ∂(μ.restrict E) = ∑ B ∈ A.powerset, ∫ ω, g ω ∂(μ.restrict (E ∩ starEvent o ↑B))
  rw [key, integral_finsetSum_measure fun B _ => Integrable.of_finite]

end KNPreFKG

open KNPreFKG in
/-- **Kozma–Nitzan 2024, Theorem 8, for REAL-valued monotone cluster properties** (p. 32: "Conjecture 4
holds in any `G` in which `0` is an isolated vertex in `G ∖ A`, for any `f`", Conjecture 4 being
"`E(f(0)·𝟙{0↔A}) ≥ min_{a∈A} E(f(a)·𝟙{0↔A})`" for monotone cluster properties `f`; proof omitted in print).
For `f(v,ω) = F(C_ω(v))`, `F` a monotone real function of vertex sets (every monotone cluster property of a
finite graph is of this form): if every pair `s(0,u)` with `u ∉ A`, `u ≠ 0` has weight `0` and `A ≠ ∅`, then
some `a ∈ A` has `E[F(C(a)); 0 ↔ A] ≤ E[F(C(0)); 0 ↔ A]`.  Proof along the printed proof of Theorem 4
(pp. 13–14), exactly as the event form `KozmaNitzan2024_thm8_event`: `a₀ ∈ A` minimising
`E_{G∖{0}} F(C(a))`, the real Lemma 5 (`KozmaNitzan2024_lemma5_real`) for each star `σ_B`, `∅ ≠ B ⊆ A`
(where `σ_B ⊆ {0 ↔ A}`), and summing over `B` (`setIntegral_eq_sum_inter_starEvent`; under `σ_∅`,
`0 ↮ A`).  This is the general form of Theorem 8 announced in `KozmaNitzanClusterProperty.lean`.
With `F(S) = |S ∩ A|` it is Conjecture 4 for the relay count: `E[|C(a)∩A| ; 0↔A] ≤ E[|C(0)∩A| ; 0↔A]` for some
relay `a`, on every weighted graph whose observer is joined only to relays.
[cite: KozmaNitzan2024, Thm. 8 (p. 32) with Conjecture 4 (p. 32) and Thm. 4 (pp. 12–14)] -/
theorem KozmaNitzan2024_thm8_real {V : Type*} [Fintype V] (w : Sym2 V → unitInterval)
    (A : Finset V) (o : V) (F : Set V → ℝ) (hF : ∀ S T : Set V, S ⊆ T → F S ≤ F T)
    (hA : A.Nonempty) (hiso : ∀ u, u ≠ o → u ∉ A → w s(o, u) = 0) :
    ∃ a ∈ A, ∫ ω in ⋃ a' ∈ A, openConn o a', F (openCluster ω a) ∂(prodBernoulli w) ≤
      ∫ ω in ⋃ a' ∈ A, openConn o a', F (openCluster ω o) ∂(prodBernoulli w) := by
  classical
  set μ := prodBernoulli w with hμ
  by_cases hoA : o ∈ A
  · exact ⟨o, hoA, le_rfl⟩
  -- `a₀` minimising `E_{G ∖ {0}} F(C(a))` over `A`
  obtain ⟨a₀, ha₀, hmin⟩ := A.exists_min_image
    (fun a => ∫ ω, F {y | ω ∈ openConnIn ({o}ᶜ : Set V) a y} ∂μ) hA
  refine ⟨a₀, ha₀, ?_⟩
  have ha₀o : a₀ ≠ o := fun h => hoA (h ▸ ha₀)
  set U : Set (BondConfig V) := ⋃ a' ∈ A, (openConn o a' : Set (BondConfig V)) with hU
  rw [setIntegral_eq_sum_inter_starEvent w A o hoA hiso U (fun ω => F (openCluster ω a₀)),
    setIntegral_eq_sum_inter_starEvent w A o hoA hiso U (fun ω => F (openCluster ω o))]
  refine Finset.sum_le_sum fun B hB => ?_
  have hBA : B ⊆ A := Finset.mem_powerset.1 hB
  rcases B.eq_empty_or_nonempty with rfl | ⟨v, hv⟩
  · -- under `σ_∅`, `0 ↮ A`: the `B = ∅` terms vanish
    have h0 : U ∩ starEvent o ↑(∅ : Finset V) = (∅ : Set (BondConfig V)) := by
      ext ω
      simp only [hU, mem_inter_iff, mem_iUnion, exists_prop, mem_empty_iff_false, iff_false, not_and]
      rintro ⟨a', ha', hoa'⟩ hσ
      rw [Finset.coe_empty] at hσ
      exact not_reachable_of_mem_starEvent_empty hσ (fun h => hoA (h ▸ ha')) hoa'
    rw [h0, Measure.restrict_empty, integral_zero_measure, integral_zero_measure]
  · -- `B ≠ ∅`: the real Lemma 5 with any `v ∈ B`, and `σ_B ⊆ {0 ↔ v} ⊆ {0 ↔ A}`
    have hvo : v ≠ o := fun h => hoA (h ▸ hBA hv)
    have L5 := KozmaNitzan2024_lemma5_real w o a₀ v (↑B) F hF ha₀o hvo (Finset.mem_coe.2 hv)
      (hmin v (hBA hv))
    have hσU : starEvent o (↑B : Set V) ⊆ U := by
      intro ω hσ
      have hov : s(o, v) ∈ ω := ((mem_starEvent_iff o (↑B) ω).1 hσ v hvo).2 (Finset.mem_coe.2 hv)
      have hadj : (openGraph ω).Adj o v := (openGraph_adj ω o v).2 ⟨hov, hvo.symm⟩
      exact mem_iUnion₂.2 ⟨v, hBA hv, hadj.reachable⟩
    rw [inter_eq_right.2 hσU]
    exact L5

/-! ### Theorem 7 for a real-valued monotone cluster property: `|A| = 2` -/

namespace KNPreFKG

variable [Fintype V]

/-- **The pair inequality behind Theorem 7, real-valued** (Kozma–Nitzan's Theorem 1, pp. 7–8, run for a
real monotone cluster property): for `F` monotone on vertex sets and vertices `0, a₁, a₂`, with
`E = {0 ↔ a₁} ∪ {0 ↔ a₂}` and `f_x = F(C(x))`, `min(∫_E f_{a₁}, ∫_E f_{a₂}) ≤ ∫_E f_0`.  Proof as printed
for `{aᵢ ↔ b}` and as in the event form `clusterProp_pair`: on `{0 ↔ aᵢ}` the clusters of `0` and `aᵢ`
coincide, so `∫_E f_0 − ∫_E f_{a₁} = ∫_{D ∩ {0↔a₂}} (f_{a₂} − f_{a₁})`, `D = {a₁ ↮ a₂}`; BHK Thm. 1.3 inside
`C_{a₂}` and Thm. 1.4 across `C_{a₂}`/`C_{a₁}` (integral forms) bound `μ(D)` times it below by
`μ(D ∩ {0↔a₂}) (∫_D f_{a₂} − ∫_D f_{a₁})`, and symmetrically; one of the two is nonnegative.
[cite: KozmaNitzan2024, Thm. 7 (p. 32) with Thm. 1 (pp. 7–8)] -/
theorem clusterFun_pair (w : Sym2 V → unitInterval) (o a₁ a₂ : V) (F : Set V → ℝ)
    (hF : ∀ S T : Set V, S ⊆ T → F S ≤ F T) :
    min (∫ ω in (openConn o a₁ ∪ openConn o a₂), F (openCluster ω a₁) ∂(prodBernoulli w))
        (∫ ω in (openConn o a₁ ∪ openConn o a₂), F (openCluster ω a₂) ∂(prodBernoulli w)) ≤
      ∫ ω in (openConn o a₁ ∪ openConn o a₂), F (openCluster ω o) ∂(prodBernoulli w) := by
  classical
  set μ := prodBernoulli w with hμ
  set f₀ : BondConfig V → ℝ := fun ω => F (openCluster ω o) with hf₀
  set f₁ : BondConfig V → ℝ := fun ω => F (openCluster ω a₁) with hf₁
  set f₂ : BondConfig V → ℝ := fun ω => F (openCluster ω a₂) with hf₂
  have hmeas : ∀ T : Set (BondConfig V), MeasurableSet T := fun _ => MeasurableSet.of_discrete
  have hint : ∀ (k : BondConfig V → ℝ) (T : Set (BondConfig V)), IntegrableOn k T μ :=
    fun k T => (Integrable.of_finite).integrableOn
  by_cases h12 : a₁ = a₂
  · -- `A` is a singleton: on `{0 ↔ a₁}` the clusters of `0` and `a₁` coincide
    subst h12
    rw [union_self, min_self]
    refine (setIntegral_congr_fun (hmeas _) fun ω hω => ?_).le
    rw [openCluster_eq_of_reachable (hω : (openGraph ω).Reachable o a₁)]
  set O₁ : Set (BondConfig V) := openConn o a₁ with hO₁
  set O₂ : Set (BondConfig V) := openConn o a₂ with hO₂
  set D : Set (BondConfig V) := {ω | ¬ (openGraph ω).Reachable a₁ a₂} with hD
  set U : Set (BondConfig V) := O₁ ∪ O₂ with hU
  -- set identities
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
  -- same cluster ⇒ same value
  have h01 : ∀ ω ∈ O₁, f₀ ω = f₁ ω := fun ω hω => by
    simp only [hf₀, hf₁]; rw [openCluster_eq_of_reachable (hω : (openGraph ω).Reachable o a₁)]
  have h02 : ∀ ω ∈ O₂, f₀ ω = f₂ ω := fun ω hω => by
    simp only [hf₀, hf₂]; rw [openCluster_eq_of_reachable (hω : (openGraph ω).Reachable o a₂)]
  -- the two "subtract the common event" identities
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
  -- "Applying BHK 4 times", given `D = {a₁ ↮ a₂}`
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
  -- (i) Thm 1.3 in `C_{a₂}`: `μ(D ∩ O₂) ∫_D f₂ ≤ μ(D) ∫_{D ∩ O₂} f₂`
  have h_i := BHK2006_clusterConditionalPositiveAssociation_holds V w a₂ ({a₁} : Set V)
    ((connFamily a₂ o).indicator 1) (fun C => F {a | a = a₂ ∨ ∃ e ∈ C, a ∈ e})
    (monotone_indicator_one_of_isUpperSet (isUpperSet_connFamily a₂ o)) (monotone_clusterFun a₂ F hF)
    (by simpa using Ne.symm h12)
  simp only [hD2, clusterFun_openEdgeCluster, hind2] at h_i
  rw [setIntegral_indicator_one_eq, hprod O₂] at h_i
  -- (ii) Thm 1.4 across `C_{a₂}`, `C_{a₁}`: `μ(D) ∫_{D ∩ O₂} f₁ ≤ μ(D ∩ O₂) ∫_D f₁`
  have h_ii := BHK2006_twoClusterConditionalAssociation.negCorrelation
    BHK2006_twoClusterConditionalAssociation_holds V w a₂ a₁
    ((connFamily a₂ o).indicator 1) (fun C => F {a | a = a₁ ∨ ∃ e ∈ C, a ∈ e})
    (monotone_indicator_one_of_isUpperSet (isUpperSet_connFamily a₂ o)) (monotone_clusterFun a₁ F hF)
    (Ne.symm h12)
  simp only [hD3, clusterFun_openEdgeCluster, hind2] at h_ii
  rw [setIntegral_indicator_one_eq, hprod O₂] at h_ii
  -- (iii) Thm 1.3 in `C_{a₁}`: `μ(D ∩ O₁) ∫_D f₁ ≤ μ(D) ∫_{D ∩ O₁} f₁`
  have h_iii := BHK2006_clusterConditionalPositiveAssociation_holds V w a₁ ({a₂} : Set V)
    ((connFamily a₁ o).indicator 1) (fun C => F {a | a = a₁ ∨ ∃ e ∈ C, a ∈ e})
    (monotone_indicator_one_of_isUpperSet (isUpperSet_connFamily a₁ o)) (monotone_clusterFun a₁ F hF)
    (by simpa using h12)
  simp only [hD1, clusterFun_openEdgeCluster, hind1] at h_iii
  rw [setIntegral_indicator_one_eq, hprod O₁] at h_iii
  -- (iv) Thm 1.4 across `C_{a₁}`, `C_{a₂}`: `μ(D) ∫_{D ∩ O₁} f₂ ≤ μ(D ∩ O₁) ∫_D f₂`
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
  -- combine
  by_cases hD0 : μ.real D = 0
  · have hz : ∀ (T : Set (BondConfig V)) (k : BondConfig V → ℝ), ∫ ω in D ∩ T, k ω ∂μ = 0 := by
      intro T k
      have h0 : μ (D ∩ T) = 0 := by
        have : μ.real (D ∩ T) = 0 :=
          le_antisymm ((measureReal_mono inter_subset_left).trans hD0.le) measureReal_nonneg
        exact (measureReal_eq_zero_iff (measure_ne_top _ _)).1 this
      exact setIntegral_measure_zero _ h0
    have : ∫ ω in U, f₀ ω ∂μ = ∫ ω in U, f₁ ω ∂μ := by
      have := hdiff1
      rw [hz, hz, sub_self, sub_eq_zero] at this
      exact this
    exact (min_le_left _ _).trans this.symm.le
  · have hDpos : 0 < μ.real D := lt_of_le_of_ne measureReal_nonneg (Ne.symm hD0)
    rcases le_total (∫ ω in D, f₁ ω ∂μ) (∫ ω in D, f₂ ω ∂μ) with ht | ht
    · refine (min_le_left _ _).trans ?_
      have key : μ.real D * (∫ ω in U, f₀ ω ∂μ - ∫ ω in U, f₁ ω ∂μ) ≥ 0 := by
        rw [hdiff1, mul_sub]
        have hs2 : 0 ≤ μ.real (D ∩ O₂) := measureReal_nonneg
        nlinarith [h_i, h_ii, mul_le_mul_of_nonneg_left ht hs2]
      nlinarith [key]
    · refine (min_le_right _ _).trans ?_
      have key : μ.real D * (∫ ω in U, f₀ ω ∂μ - ∫ ω in U, f₂ ω ∂μ) ≥ 0 := by
        rw [hdiff2, mul_sub]
        have hs1 : 0 ≤ μ.real (D ∩ O₁) := measureReal_nonneg
        nlinarith [h_iii, h_iv, mul_le_mul_of_nonneg_left ht hs1]
      nlinarith [key]

end KNPreFKG

open KNPreFKG in
/-- **Kozma–Nitzan 2024, Theorem 7, for REAL-valued monotone cluster properties** (p. 32: "Conjecture 4
holds when `|A| = 2`, for any `f`"; proof omitted in print).  For `f(v,ω) = F(C_ω(v))`, `F` monotone on
vertex sets: if `|A| = 2` then some `a ∈ A` has `E[F(C(a)); 0 ↔ A] ≤ E[F(C(0)); 0 ↔ A]`.  Proof: the printed
proof of Theorem 1 (pp. 7–8) with `𝟙{aᵢ ↔ b}` replaced by `F(C(aᵢ))` (`KNPreFKG.clusterFun_pair`).  This is
the general form of Theorem 7 announced in `KozmaNitzanClusterProperty.lean`.
[cite: KozmaNitzan2024, Thm. 7 (p. 32) with Conjecture 4 (p. 32) and Thm. 1 (pp. 7–8)] -/
theorem KozmaNitzan2024_thm7_real {V : Type*} [Fintype V] (w : Sym2 V → unitInterval)
    (A : Finset V) (o : V) (F : Set V → ℝ) (hF : ∀ S T : Set V, S ⊆ T → F S ≤ F T)
    (hA : A.card = 2) :
    ∃ a ∈ A, ∫ ω in ⋃ a' ∈ A, openConn o a', F (openCluster ω a) ∂(prodBernoulli w) ≤
      ∫ ω in ⋃ a' ∈ A, openConn o a', F (openCluster ω o) ∂(prodBernoulli w) := by
  classical
  obtain ⟨a₁, a₂, h12, rfl⟩ := Finset.card_eq_two.1 hA
  have hU : (⋃ a' ∈ ({a₁, a₂} : Finset V), (openConn o a' : Set (BondConfig V))) =
      openConn o a₁ ∪ openConn o a₂ := by
    ext ω
    simp only [mem_iUnion, exists_prop, Finset.mem_insert, Finset.mem_singleton, mem_union]
    constructor
    · rintro ⟨a, rfl | rfl, ha⟩
      · exact Or.inl ha
      · exact Or.inr ha
    · rintro (h | h)
      · exact ⟨a₁, Or.inl rfl, h⟩
      · exact ⟨a₂, Or.inr rfl, h⟩
  rw [hU]
  have key := clusterFun_pair w o a₁ a₂ F hF
  rcases min_le_iff.1 key with h | h
  · exact ⟨a₁, by simp, h⟩
  · exact ⟨a₂, by simp, h⟩

/-! ### The printed generality: `F` monotone along NONEMPTY vertex sets

Kozma–Nitzan's requirement (1) (§5.1, p. 31) constrains `f(v, ·) = F(C(v))` only through clusters, which are
nonempty; a function `F` monotone on nonempty vertex sets agrees on nonempty sets with a function monotone on
all vertex sets (value `min_v F{v}` at `∅`), so the theorems above apply verbatim. -/

namespace KNPreFKG

variable [Fintype V]

/-- A real function of vertex sets that is monotone along nonempty sets agrees on nonempty sets with a
globally monotone one. [folklore] -/
theorem monotoneOnNonempty_extension (o : V) (F : Set V → ℝ)
    (hF : ∀ S T : Set V, S.Nonempty → S ⊆ T → F S ≤ F T) :
    ∃ F' : Set V → ℝ, (∀ S T : Set V, S ⊆ T → F' S ≤ F' T) ∧
      ∀ S : Set V, S.Nonempty → F' S = F S := by
  classical
  refine ⟨fun S => if S.Nonempty then F S
      else Finset.univ.inf' ⟨o, Finset.mem_univ o⟩ (fun v => F {v}), ?_, ?_⟩
  · intro S T hST
    by_cases hS : S.Nonempty
    · have hT : T.Nonempty := hS.mono hST
      simp only [hS, hT, if_true]
      exact hF S T hS hST
    · by_cases hT : T.Nonempty
      · obtain ⟨v, hv⟩ := hT
        have hT' : T.Nonempty := ⟨v, hv⟩
        simp only [hS, hT', if_true, if_false]
        calc Finset.univ.inf' ⟨o, Finset.mem_univ o⟩ (fun v => F {v}) ≤ F {v} :=
              Finset.inf'_le _ (Finset.mem_univ v)
          _ ≤ F T := hF {v} T (Set.singleton_nonempty v) (Set.singleton_subset_iff.2 hv)
      · simp only [hS, hT, if_false]
        exact le_rfl
  · intro S hS
    simp only [hS, if_true]

end KNPreFKG

open KNPreFKG in
/-- **Kozma–Nitzan 2024, Theorem 8**, in the printed generality of §5.1: `f(v,ω) = F(C_ω(v))` with `F`
increasing along nonempty vertex sets (requirement (1), p. 31; requirement (2) is then automatic).  If `0`
is isolated in `G ∖ A` and `A ≠ ∅`, some `a ∈ A` has `E[f(a); 0 ↔ A] ≤ E[f(0); 0 ↔ A]`, i.e.
`E(f(0)·𝟙{0↔A}) ≥ min_{a∈A} E(f(a)·𝟙{0↔A})`.  From `KozmaNitzan2024_thm8_real` via
`monotoneOnNonempty_extension`. [cite: KozmaNitzan2024, Thm. 8 (p. 32) with Conjecture 4 (p. 32) and §5.1 (p. 31)] -/
theorem KozmaNitzan2024_thm8_clusterProperty {V : Type*} [Fintype V] (w : Sym2 V → unitInterval)
    (A : Finset V) (o : V) (F : Set V → ℝ) (hF : ∀ S T : Set V, S.Nonempty → S ⊆ T → F S ≤ F T)
    (hA : A.Nonempty) (hiso : ∀ u, u ≠ o → u ∉ A → w s(o, u) = 0) :
    ∃ a ∈ A, ∫ ω in ⋃ a' ∈ A, openConn o a', F (openCluster ω a) ∂(prodBernoulli w) ≤
      ∫ ω in ⋃ a' ∈ A, openConn o a', F (openCluster ω o) ∂(prodBernoulli w) := by
  obtain ⟨F', hF'mono, hF'eq⟩ := monotoneOnNonempty_extension o F hF
  have hFF : ∀ (ω : BondConfig V) (x : V), F' (openCluster ω x) = F (openCluster ω x) :=
    fun ω x => hF'eq _ ⟨x, mem_openCluster_self ω x⟩
  obtain ⟨a, ha, h⟩ := KozmaNitzan2024_thm8_real w A o F' hF'mono hA hiso
  refine ⟨a, ha, ?_⟩
  simpa only [hFF] using h

open KNPreFKG in
/-- **Kozma–Nitzan 2024, Theorem 7**, in the printed generality of §5.1 (`F` increasing along nonempty
vertex sets): if `|A| = 2`, some `a ∈ A` has `E[f(a); 0 ↔ A] ≤ E[f(0); 0 ↔ A]`.  From
`KozmaNitzan2024_thm7_real` via `monotoneOnNonempty_extension`.
[cite: KozmaNitzan2024, Thm. 7 (p. 32) with Conjecture 4 (p. 32) and §5.1 (p. 31)] -/
theorem KozmaNitzan2024_thm7_clusterProperty {V : Type*} [Fintype V] (w : Sym2 V → unitInterval)
    (A : Finset V) (o : V) (F : Set V → ℝ) (hF : ∀ S T : Set V, S.Nonempty → S ⊆ T → F S ≤ F T)
    (hA : A.card = 2) :
    ∃ a ∈ A, ∫ ω in ⋃ a' ∈ A, openConn o a', F (openCluster ω a) ∂(prodBernoulli w) ≤
      ∫ ω in ⋃ a' ∈ A, openConn o a', F (openCluster ω o) ∂(prodBernoulli w) := by
  obtain ⟨F', hF'mono, hF'eq⟩ := monotoneOnNonempty_extension o F hF
  have hFF : ∀ (ω : BondConfig V) (x : V), F' (openCluster ω x) = F (openCluster ω x) :=
    fun ω x => hF'eq _ ⟨x, mem_openCluster_self ω x⟩
  obtain ⟨a, ha, h⟩ := KozmaNitzan2024_thm7_real w A o F' hF'mono hA
  refine ⟨a, ha, ?_⟩
  simpa only [hFF] using h

end Percolation.Literature
