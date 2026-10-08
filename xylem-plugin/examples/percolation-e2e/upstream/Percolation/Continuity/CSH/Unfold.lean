import Percolation.Continuity.CSH.UnfoldDecoy
import Percolation.Literature.TwoAvoidanceSets
import Percolation.Util.Linter

/-!
# The conditioned slack hierarchy CSH: LEMMA U FOR GENERAL `k` (the world-wise unfolding of the within-covariance of the multi-marker reduction into the H-part and the lower-level margins)

Lemma U, part 3.

THE IDENTITY (`CSH.within_unfold`).  Data: non-loop weights `w`, owner `x`, avoided set `Y`, decoys `D = [d_1,…,d_k]` with the constants of
`CSH.decoyList w ({x} ∪ Y) D` (`c_j(w') = μ(d_j ↔ w' | d_j ↮ {x} ∪ Y ∪ D_{<j})`), the observers' constant `p`, the coefficients
`Λ(u) = Marg[δ_u]` of the margin (`CSH.cshMarg_eq_sum_single`), and a functional `g` of the open edge cluster of `x`.  The hypothesis `hR` of
the multi-marker Lemma T `BHK2006_multiMarkerCov_nonneg_of_within` — the `{x ↮ Y}`-average of the WORLD covariances
`Σ_u Λ(u)·Cov_{world(ω)}(g(C_x), 1{x ↔ u})` (world = weights zeroed on the pairs meeting the open vertex cluster of `Y`) — equals

  `hpartS + Σ_j μ(E_j)⁻¹ · Marg^{(j)}[ covD_{d_j, Y_j}(Φ̃_j) ]`,        `E_j = {d_j ↮ Y_j}`, `Y_j = {x} ∪ Y ∪ D_{<j}`,

where `hpartS = Σ_ω w 1{x↮Y} [Cov_{world}(g(C_x), 1{o ↔ {x}∪D}) − p·Cov_{world}(g(C_x), 1{v ↔ {x}∪D})]` (i.e. `Hpart·μ(x↮Y)`),
`Marg^{(j)}` is the margin of the SUB-SYSTEM list `CSH.decoyList w ({d_j} ∪ Y_j) D_{>j}` with the same `p` (a recursion along `D`, accumulated in `CSH.subT`),
`covD` is the denominator-free conditional covariance of `Continuity/CSH/Defs.lean` for the owner `d_j` and the avoided set `Y_j`, and
`Φ̃_j(K) = Φ({d_j} ∪ V(K))` (`CSH.phiT`, Lemma-Φ functional `CSH.phiFun` read on the edge cluster of `d_j`; monotone, `CSH.phiT_mono`).
Ingredients: the measure ↔ weight-sum dictionary for the zeroed-weight worlds (`BHK2006.integral_comp_sdiff_prodBernoulli`), linearity of the
world covariance, the pointwise CLAIM `CSH.slForm_jn` (`Continuity/CSH/LevelForms.lean`), and the one-decoy world term `CSH.decoy_world_term`
(`Continuity/CSH/UnfoldDecoy.lean`) summed along the decoy list (`CSH.sum_wcov_unfoldT`).
[cite: VandenbergHaggstromKahn2005, §2.1 Lemma 2.4 (p. 10); §1 display (10) (pp. 7–8) — corollaries]
-/

noncomputable section

namespace Percolation.Continuity

open MeasureTheory Set Percolation.Literature.LatticeModels Percolation.Literature
open scoped Classical
open BHK2006 DecisionTree HullPort

namespace CSH

variable {V : Type*} [Fintype V]

/-! ### Measure ↔ weight-sum dictionary -/

/-- `∫_E f dμ_w = Σ_ω weight(ω) 1_E(ω) f(ω)`. [folklore] -/
theorem setIntegral_eq_sum_ind (w : Sym2 V → unitInterval) (E : Set (Set (Sym2 V))) (f : Set (Sym2 V) → ℝ) :
    ∫ ω in E, f ω ∂(prodBernoulli w) = ∑ ω, weight (fun e => (w e : ℝ)) ω * (ind E ω * f ω) := by
  rw [← integral_indicator MeasurableSet.of_discrete, integral_prodBernoulli_eq_sum]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases hω : ω ∈ E
  · rw [Set.indicator_of_mem hω, ind_of_mem hω, one_mul]
  · rw [Set.indicator_of_notMem hω, ind_of_not_mem hω, zero_mul, mul_zero]

/-- **World expectations are `wmeanOff`**: the expectation under the weights zeroed on the pairs meeting the open vertex cluster of `Y`
is the weight-sum of the configuration with those pairs deleted. [cite: VandenbergHaggstromKahn2005, §2.1 Lemma 2.3 (p. 10)] -/
theorem integral_world_eq_wmeanOff (w : Sym2 V → unitInterval) (Y : Set V) (ω : Set (Sym2 V)) (F : Set (Sym2 V) → ℝ) :
    ∫ η, F η ∂(prodBernoulli fun e => if (∃ v ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y v) then (0 : unitInterval) else w e) =
      wmeanOff (fun e => (w e : ℝ)) Y F ω := by
  have h := BHK2006.integral_comp_sdiff_prodBernoulli w (cut Y ω) F
  have e : (fun i => if i ∈ cut Y ω then (0 : unitInterval) else w i) =
      fun e => if (∃ v ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y v) then (0 : unitInterval) else w e := by
    funext i
    by_cases hP : ∃ v ∈ i, ∃ y ∈ Y, (openGraph ω).Reachable y v
    · rw [if_pos hP, if_pos (show i ∈ cut Y ω from hP)]
    · rw [if_neg hP, if_neg (show i ∉ cut Y ω from hP)]
  rw [e] at h
  rw [← h, integral_prodBernoulli_eq_sum]
  rfl

/-- **The world covariance term of the multi-marker reduction is `wcovOff`**. [cite: VandenbergHaggstromKahn2005, §2.1 Lemma 2.3 (p. 10)] -/
theorem world_cov_eq_wcovOff (w : Sym2 V → unitInterval) (Y : Set V) (ω : Set (Sym2 V)) (G : Set (Sym2 V) → ℝ)
    (C : Set (Set (Sym2 V))) :
    (∫ η in C, G η ∂(prodBernoulli fun e => if (∃ v ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y v) then (0 : unitInterval) else w e)) -
        (∫ η, G η ∂(prodBernoulli fun e => if (∃ v ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y v) then (0 : unitInterval) else w e)) *
          (prodBernoulli fun e => if (∃ v ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y v) then (0 : unitInterval) else w e).real C =
      wcovOff (fun e => (w e : ℝ)) Y G (ind C) ω := by
  rw [← integral_indicator MeasurableSet.of_discrete, ← integral_indicator_one MeasurableSet.of_discrete,
    integral_world_eq_wmeanOff, integral_world_eq_wmeanOff, integral_world_eq_wmeanOff]
  unfold wcovOff
  have e1 : (C.indicator G) = fun β => G β * ind C β := by
    funext β
    by_cases hβ : β ∈ C
    · rw [Set.indicator_of_mem hβ, ind_of_mem hβ, mul_one]
    · rw [Set.indicator_of_notMem hβ, ind_of_not_mem hβ, mul_zero]
  have e2 : (C.indicator (1 : Set (Sym2 V) → ℝ)) = ind C := by
    funext β
    by_cases hβ : β ∈ C
    · rw [Set.indicator_of_mem hβ, ind_of_mem hβ, Pi.one_apply]
    · rw [Set.indicator_of_notMem hβ, ind_of_not_mem hβ]
  rw [e1, e2]

/-! ### Linearity of the world covariance -/

/-- The world covariance as a centred sum (restated with the residual factor first). [folklore] -/
theorem wcovOff_finset_sum (w : Sym2 V → ℝ) (Y : Set V) (φ : Set (Sym2 V) → ℝ) {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ψ : ι → Set (Sym2 V) → ℝ) (ω : Set (Sym2 V)) :
    ∑ i ∈ s, a i * wcovOff w Y φ (ψ i) ω = wcovOff w Y φ (fun ζ => ∑ i ∈ s, a i * ψ i ζ) ω := by
  simp only [wcovOff_eq_sum w, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun η _ => ?_
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The world covariance of a general affine combination: `Cov(φ, ψ₁ − p·ψ₂ − (χ₁ − p·χ₂) + K) = Cov(φ,ψ₁) − p·Cov(φ,ψ₂) − Cov(φ,χ₁) + p·Cov(φ,χ₂)`
for a CONSTANT `K`. [folklore] -/
theorem wcovOff_affine (w : Sym2 V → ℝ) (hm : ∑ ω, weight w ω = 1) (Y : Set V) (φ ψ₁ ψ₂ χ₁ χ₂ : Set (Sym2 V) → ℝ) (p K : ℝ)
    (ω : Set (Sym2 V)) :
    wcovOff w Y φ (fun ζ => (ψ₁ ζ - p * ψ₂ ζ) - (χ₁ ζ - p * χ₂ ζ) + K) ω =
      wcovOff w Y φ ψ₁ ω - p * wcovOff w Y φ ψ₂ ω - wcovOff w Y φ χ₁ ω + p * wcovOff w Y φ χ₂ ω := by
  simp only [wcovOff_eq_sum w]
  have h0 : ∑ η, weight w η * ((φ (η \ cut Y ω) - wmeanOff w Y φ ω) * K) = 0 := by
    have e0 : ∀ η, weight w η * ((φ (η \ cut Y ω) - wmeanOff w Y φ ω) * K) =
        K * (weight w η * φ (η \ cut Y ω)) - K * wmeanOff w Y φ ω * weight w η := by intro η; ring
    rw [Finset.sum_congr rfl (fun η _ => e0 η), Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hm]
    unfold wmeanOff; ring
  have e : ∀ η, weight w η * ((φ (η \ cut Y ω) - wmeanOff w Y φ ω) * ((ψ₁ (η \ cut Y ω) - p * ψ₂ (η \ cut Y ω)) -
      (χ₁ (η \ cut Y ω) - p * χ₂ (η \ cut Y ω)) + K)) =
      weight w η * ((φ (η \ cut Y ω) - wmeanOff w Y φ ω) * ψ₁ (η \ cut Y ω)) -
        p * (weight w η * ((φ (η \ cut Y ω) - wmeanOff w Y φ ω) * ψ₂ (η \ cut Y ω))) -
        weight w η * ((φ (η \ cut Y ω) - wmeanOff w Y φ ω) * χ₁ (η \ cut Y ω)) +
        p * (weight w η * ((φ (η \ cut Y ω) - wmeanOff w Y φ ω) * χ₂ (η \ cut Y ω))) +
        weight w η * ((φ (η \ cut Y ω) - wmeanOff w Y φ ω) * K) := by intro η; ring
  rw [Finset.sum_congr rfl (fun η _ => e η), Finset.sum_add_distrib, h0, add_zero, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-! ### The Lemma-Φ functional on the edge cluster of a decoy -/

/-- **`Φ̃_d(K) = Φ({d} ∪ V(K))`**: Lemma-Φ functional (`CSH.phiFun`, a monotone function of vertex sets) read on the open EDGE cluster
`K` of the decoy `d` — the functional of the lower-level system with owner `d`.
[folklore] -/
def phiT (w : Sym2 V → unitInterval) (x : V) (Y : Set V) (g : Set (Sym2 V) → ℝ) (d : V) (K : Set (Sym2 V)) : ℝ :=
  phiFun w x Y g (insert d {u | ∃ e ∈ K, u ∈ e})

/-- `Φ̃_d` is monotone (Lemma Φ(b), `CSH.phiFun_mono`). [folklore] -/
theorem phiT_mono (w : Sym2 V → unitInterval) (x : V) (Y : Set V) {g : Set (Sym2 V) → ℝ} (hg : Monotone g) (d : V) :
    Monotone (phiT w x Y g d) := fun _ _ hKK' =>
  phiFun_mono w x Y hg (Set.insert_subset_insert fun _ ⟨e, he, hue⟩ => ⟨e, hKK' he, hue⟩)

omit [Fintype V] in
/-- The open vertex cluster is the owner together with the span of the open edge cluster. [folklore] -/
theorem openCluster_eq_insert_span (ζ : Set (Sym2 V)) (d : V) :
    openCluster ζ d = insert d {u | ∃ e ∈ openEdgeCluster ζ d, u ∈ e} := by
  ext u
  rw [Set.mem_insert_iff, Set.mem_setOf_eq]
  exact reachable_iff_exists_mem_openEdgeCluster ζ d u

/-- `Φ̃_d(C_d(ζ)) = Φ(C_d(ζ))` (sum level `CSH.phiS`). [folklore] -/
theorem phiT_openEdgeCluster (w : Sym2 V → unitInterval) (x : V) (Y : Set V) (g : Set (Sym2 V) → ℝ) (d : V) (ζ : Set (Sym2 V)) :
    phiT w x Y g d (openEdgeCluster ζ d) = phiS (fun e => (w e : ℝ)) x Y g d ζ := by
  unfold phiT phiS phiFun
  rw [← openCluster_eq_insert_span, integral_prodBernoulli_eq_sum]

/-- **The denominator-free covariance of the sub-system is the centred decoy moment**: for `E = {d ↮ A}`,
`covD_{d,A}(Φ̃_d)(w') = m₀·P₁(w') − m₁(w')·P₀` (masses and `Φ`-moments at sum level). [folklore] -/
theorem covD_phiT_eq (w : Sym2 V → unitInterval) (x : V) (Y A : Set V) (g : Set (Sym2 V) → ℝ) (d w' : V) :
    covD w d A (phiT w x Y g d) w' =
      (∑ ζ, weight (fun e => (w e : ℝ)) ζ * ind (avoidEv d A) ζ) *
          (∑ ζ, weight (fun e => (w e : ℝ)) ζ * (ind (avoidEv d A ∩ openConn d w') ζ * phiS (fun e => (w e : ℝ)) x Y g d ζ)) -
        (∑ ζ, weight (fun e => (w e : ℝ)) ζ * ind (avoidEv d A ∩ openConn d w') ζ) *
          (∑ ζ, weight (fun e => (w e : ℝ)) ζ * (ind (avoidEv d A) ζ * phiS (fun e => (w e : ℝ)) x Y g d ζ)) := by
  unfold covD
  rw [TwoAvoidanceSets.real_eq_sum_ind, TwoAvoidanceSets.real_eq_sum_ind, setIntegral_eq_sum_ind, setIntegral_eq_sum_ind]
  simp only [phiT_openEdgeCluster]
  have hE : ({ω : BondConfig V | ∀ y ∈ A, ¬ (openGraph ω).Reachable d y} : Set (Set (Sym2 V))) = avoidEv d A := rfl
  rw [hE]
  ring

/-- **The decoy constant is the ratio of masses** (sum level). [folklore] -/
theorem avoidConst_eq_div (w : Sym2 V → unitInterval) (d : V) (A : Set V) (w' : V) :
    avoidConst w d A w' = (∑ ζ, weight (fun e => (w e : ℝ)) ζ * ind (avoidEv d A ∩ openConn d w') ζ) /
      ∑ ζ, weight (fun e => (w e : ℝ)) ζ * ind (avoidEv d A) ζ := by
  unfold avoidConst
  rw [TwoAvoidanceSets.real_eq_sum_ind, TwoAvoidanceSets.real_eq_sum_ind]
  rfl

/-! ### Positivity of the avoidance masses for non-degenerate weights -/

/-- For non-degenerate weights and `d ∉ A`, `μ(d ↮ A) = Σ_ζ w 1{d↮A} ≠ 0` (the empty configuration avoids everything). [folklore] -/
theorem sum_ind_avoidEv_ne_zero (w : Sym2 V → unitInterval) (hw : ∀ e, 0 < w e ∧ w e < 1) {d : V} {A : Set V} (hdA : d ∉ A) :
    ∑ ζ, weight (fun e => (w e : ℝ)) ζ * ind (avoidEv d A) ζ ≠ 0 := by
  rw [← TwoAvoidanceSets.real_eq_sum_ind]
  have hmem : (∅ : Set (Sym2 V)) ∈ avoidEv d A := by
    intro a ha hreach
    have hbot : openGraph (∅ : BondConfig V) = ⊥ := by
      unfold openGraph; exact SimpleGraph.fromEdgeSet_empty
    rw [hbot, SimpleGraph.reachable_bot] at hreach
    exact hdA (hreach ▸ ha)
  exact (prodBernoulli_real_pos_of_nonempty hw ⟨∅, hmem⟩).ne'

/-! ### Summing the decoy terms along the list (the `Σ_j` of Lemma U) -/

/-- The accumulated lower-level terms of the unfolding at the marker `u`, as a recursion along the decoy list with a growing source set `S`
(owner + earlier decoys): `subT_S([]) = 0`, `subT_S(d :: ds) = μ(d ↮ S∪Y)⁻¹ · sl_{L_{>d}}[covD_{d,S∪Y}(Φ̃_d)](u) + subT_{S∪{d}}(ds)`.
[folklore] -/
def subT (w : Sym2 V → unitInterval) (x : V) (Y : Set V) (g : Set (Sym2 V) → ℝ) (u : V) : Set V → List V → ℝ
  | _, [] => 0
  | S, d :: ds => ((prodBernoulli w).real (avoidEv d (S ∪ Y)))⁻¹ *
        slForm (decoyList w (insert d (S ∪ Y)) ds) (covD w d (S ∪ Y) (phiT w x Y g d)) u +
      subT w x Y g u (insert d S) ds

/-- The world covariance vanishes on the zero test function. [folklore] -/
theorem wcovOff_zero_right (w : Sym2 V → ℝ) (Y : Set V) (φ : Set (Sym2 V) → ℝ) (ω : Set (Sym2 V)) :
    wcovOff w Y φ (fun _ => 0) ω = 0 := by
  rw [wcovOff_eq_sum w]; simp

/-- The world covariance is additive in the test function. [folklore] -/
theorem wcovOff_add_right (w : Sym2 V → ℝ) (Y : Set V) (φ ψ₁ ψ₂ : Set (Sym2 V) → ℝ) (ω : Set (Sym2 V)) :
    wcovOff w Y φ (fun ζ => ψ₁ ζ + ψ₂ ζ) ω = wcovOff w Y φ ψ₁ ω + wcovOff w Y φ ψ₂ ω := by
  simp only [wcovOff_eq_sum w, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun η _ => by ring

/-- **The `Σ_j` of Lemma U**: the `{x↮Y}`-average of the world covariance of `g(C_x)` with the unfolded terms `unfoldT` (read in the world) is
MINUS the accumulated lower-level terms `subT`.  Hypotheses: non-degenerate weights, `x ∈ S`, the decoys distinct, outside `S ∪ Y` and
different from the marker `u`.
[cite: VandenbergHaggstromKahn2005, §2.1 Lemma 2.4 (p. 10) — corollary] -/
theorem sum_wcov_unfoldT (w : Sym2 V → unitInterval) (hw : ∀ e, 0 < w e ∧ w e < 1) (x : V) (Y : Set V)
    (g : Set (Sym2 V) → ℝ) (u : V) :
    ∀ (D : List V) (S : Set V), x ∈ S → D.Nodup → (∀ d ∈ D, d ∉ S ∧ d ∉ Y ∧ d ≠ u) →
      ∑ ω, weight (fun e => (w e : ℝ)) ω * (ind (avoidEv x Y) ω *
          wcovOff (fun e => (w e : ℝ)) Y (fun β => g (openEdgeCluster β x))
            (fun ζ => unfoldT (openGraph ζ).Reachable S (decoyList w (S ∪ Y) D) u) ω) =
        - subT w x Y g u S D := by
  intro D
  induction D with
  | nil =>
    intro S _ _ _
    simp only [decoyList, unfoldT, subT, neg_zero]
    exact Finset.sum_eq_zero fun ω _ => by rw [wcovOff_zero_right]; ring
  | cons d ds ih =>
    intro S hxS hnd hdis
    set ŵ : Sym2 V → ℝ := fun e => (w e : ℝ) with hŵ
    have hm : ∑ ω, weight ŵ ω = 1 := by
      have h1 := integral_prodBernoulli_eq_sum w fun _ => (1 : ℝ)
      simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at h1
      exact h1.symm
    have hdS : d ∉ S := (hdis d List.mem_cons_self).1
    have hdY : d ∉ Y := (hdis d List.mem_cons_self).2.1
    have hud : u ≠ d := fun h => (hdis d List.mem_cons_self).2.2 h.symm
    have hnd' : ds.Nodup := (List.nodup_cons.1 hnd).2
    have hd_notin : d ∉ ds := (List.nodup_cons.1 hnd).1
    -- the list unfolds at the head
    have hL : decoyList w (S ∪ Y) (d :: ds) = (d, avoidConst w d (S ∪ Y)) :: decoyList w (insert d (S ∪ Y)) ds := rfl
    have hset : insert d (S ∪ Y) = insert d S ∪ Y := by rw [Set.insert_union]
    have hL' : ∀ dc ∈ decoyList w (insert d (S ∪ Y)) ds, dc.1 ≠ d := by
      intro dc hdc hEq
      have : dc.1 ∈ (decoyList w (insert d (S ∪ Y)) ds).map Prod.fst := List.mem_map.2 ⟨dc, hdc, rfl⟩
      rw [map_fst_decoyList, hEq] at this
      exact hd_notin this
    have hm₀ : ∑ ζ, weight ŵ ζ * ind (avoidEv d (S ∪ Y)) ζ ≠ 0 :=
      sum_ind_avoidEv_ne_zero w hw (fun h => h.elim hdS hdY)
    -- split the test function
    have hsplit : ∀ ω, wcovOff ŵ Y (fun β => g (openEdgeCluster β x))
        (fun ζ => unfoldT (openGraph ζ).Reachable S (decoyList w (S ∪ Y) (d :: ds)) u) ω =
        wcovOff ŵ Y (fun β => g (openEdgeCluster β x))
          (fun ζ => av (openGraph ζ).Reachable S d *
            slForm (decoyList w (insert d (S ∪ Y)) ds) (fun w' => chi (openGraph ζ).Reachable w' d - avoidConst w d (S ∪ Y) w') u) ω +
        wcovOff ŵ Y (fun β => g (openEdgeCluster β x))
          (fun ζ => unfoldT (openGraph ζ).Reachable (insert d S) (decoyList w (insert d S ∪ Y) ds) u) ω := by
      intro ω
      rw [← wcovOff_add_right, hL]
      simp only [unfoldT, hset]
    -- the head term: `decoy_world_term`, rewritten with `covD_{d}(Φ̃_d)`
    have hhead := decoy_world_term ŵ hm x Y g hxS hdS (decoyList w (insert d (S ∪ Y)) ds) hL' hud
      (avoidConst w d (S ∪ Y)) hm₀ (fun w' => avoidConst_eq_div w d (S ∪ Y) w')
    have hQ : (fun w' =>
        (∑ ζ, weight ŵ ζ * ind (avoidEv d (S ∪ Y)) ζ) *
            (∑ ζ, weight ŵ ζ * (ind (avoidEv d (S ∪ Y) ∩ openConn d w') ζ * phiS ŵ x Y g d ζ)) -
          (∑ ζ, weight ŵ ζ * ind (avoidEv d (S ∪ Y) ∩ openConn d w') ζ) *
            (∑ ζ, weight ŵ ζ * (ind (avoidEv d (S ∪ Y)) ζ * phiS ŵ x Y g d ζ))) =
        covD w d (S ∪ Y) (phiT w x Y g d) := by
      funext w'; rw [covD_phiT_eq]
    rw [hQ, ← TwoAvoidanceSets.real_eq_sum_ind] at hhead
    -- combine with the induction hypothesis at the source set `S ∪ {d}`
    have htail := ih (insert d S) (Set.mem_insert_of_mem d hxS) hnd' (fun e he =>
      ⟨fun h' => (Set.mem_insert_iff.1 h').elim (fun h0 => hd_notin (h0 ▸ he)) (hdis e (List.mem_cons_of_mem d he)).1,
        (hdis e (List.mem_cons_of_mem d he)).2.1, (hdis e (List.mem_cons_of_mem d he)).2.2⟩)
    have e : ∀ ω, weight ŵ ω * (ind (avoidEv x Y) ω * wcovOff ŵ Y (fun β => g (openEdgeCluster β x))
        (fun ζ => unfoldT (openGraph ζ).Reachable S (decoyList w (S ∪ Y) (d :: ds)) u) ω) =
        weight ŵ ω * (ind (avoidEv x Y) ω * wcovOff ŵ Y (fun β => g (openEdgeCluster β x))
          (fun ζ => av (openGraph ζ).Reachable S d *
            slForm (decoyList w (insert d (S ∪ Y)) ds) (fun w' => chi (openGraph ζ).Reachable w' d - avoidConst w d (S ∪ Y) w') u) ω) +
        weight ŵ ω * (ind (avoidEv x Y) ω * wcovOff ŵ Y (fun β => g (openEdgeCluster β x))
          (fun ζ => unfoldT (openGraph ζ).Reachable (insert d S) (decoyList w (insert d S ∪ Y) ds) u) ω) := by
      intro ω; rw [hsplit]; ring
    rw [Finset.sum_congr rfl (fun ω _ => e ω), Finset.sum_add_distrib, hhead, htail]
    simp only [subT, hset]
    ring

end CSH

end Percolation.Continuity

end
