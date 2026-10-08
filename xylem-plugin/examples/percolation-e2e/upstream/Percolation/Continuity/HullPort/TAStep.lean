import Percolation.Continuity.HullPort.DeletedEdges
import Percolation.Continuity.HullPort.TADefs
import Percolation.Util.Linter

/-!
# Marker dominance with an avoided set: the one-edge Bernstein step and Lemma 2 for `T_A`

Two inputs of the induction for `T_A ≥ 0`, for the functionals of
`Continuity/HullPort/TADefs.lean`:
* `HullPort.bernstein_step` — the identity (★) `b₀b₁·MIX = b₁²Q₀₀ + b₀²Q₁₁ + (B₀b₁ − B₁b₀)(a₀b₁ − a₁b₀)` and its
  consequence `Q(t) = A(t)b(t) − a(t)B(t) ≥ 0` on `[0,1]` for affine `A, B, a, b` (plus the degenerate endpoint case);
* `HullPort.lemma2_avoidance` — Lemma 2 (`μ(y↔z | y↮s,X) ≥ μ(y↔z | y↮s,X,v)`), i.e. `a₁b₀ ≤ a₀b₁` for the
  y-side masses `taa, tab`, from van den Berg–Häggström–Kahn's Theorem 1.3 for the cluster of `y`.
[cite: VandenbergHaggstromKahn2005, Thm. 1.3 (p. 6) — corollary]
-/

noncomputable section

namespace Percolation.Continuity

open MeasureTheory Set Percolation.Literature.LatticeModels Percolation.Literature
open scoped Classical

variable {V : Type*}

namespace HullPort

open LonePortSum LonePortSumGeneral BHK2006 DecisionTree KNPreFKG

section TA

variable [Fintype V]

/-! ### The one-edge Bernstein step (pure algebra) and Lemma 2 -/

/-- **The identity (★) and the Bernstein step**: if `Q₀₀, Q₁₁ ≥ 0`,
`B₀b₁ − B₁b₀ ≥ 0`, `a₀b₁ − a₁b₀ ≥ 0` and `b₀, b₁ > 0`, then
`Q(t) = A(t)b(t) − a(t)B(t) ≥ 0` for the affine interpolations at `t ∈ [0,1]`, because
`b₀b₁·MIX = b₁²Q₀₀ + b₀²Q₁₁ + (B₀b₁ − B₁b₀)(a₀b₁ − a₁b₀)`. [folklore] -/
theorem bernstein_step (A₀ A₁ B₀ B₁ a₀ a₁ b₀ b₁ t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hQ0 : 0 ≤ A₀ * b₀ - a₀ * B₀) (hQ1 : 0 ≤ A₁ * b₁ - a₁ * B₁) (hΔ : 0 ≤ B₀ * b₁ - B₁ * b₀)
    (hL : 0 ≤ a₀ * b₁ - a₁ * b₀) (hb₀ : 0 < b₀) (hb₁ : 0 < b₁) :
    0 ≤ ((1 - t) * A₀ + t * A₁) * ((1 - t) * b₀ + t * b₁) - ((1 - t) * a₀ + t * a₁) * ((1 - t) * B₀ + t * B₁) := by
  have hstar : b₀ * b₁ * (A₀ * b₁ + A₁ * b₀ - a₀ * B₁ - a₁ * B₀) =
      b₁ ^ 2 * (A₀ * b₀ - a₀ * B₀) + b₀ ^ 2 * (A₁ * b₁ - a₁ * B₁) + (B₀ * b₁ - B₁ * b₀) * (a₀ * b₁ - a₁ * b₀) := by
    ring
  have hmix0 : 0 ≤ b₀ * b₁ * (A₀ * b₁ + A₁ * b₀ - a₀ * B₁ - a₁ * B₀) := by
    rw [hstar]
    have h1 := mul_nonneg (sq_nonneg b₁) hQ0
    have h2 := mul_nonneg (sq_nonneg b₀) hQ1
    have h3 := mul_nonneg hΔ hL
    linarith
  have hmix : 0 ≤ A₀ * b₁ + A₁ * b₀ - a₀ * B₁ - a₁ * B₀ :=
    (mul_nonneg_iff_of_pos_left (mul_pos hb₀ hb₁)).1 hmix0
  have hexp : ((1 - t) * A₀ + t * A₁) * ((1 - t) * b₀ + t * b₁) - ((1 - t) * a₀ + t * a₁) * ((1 - t) * B₀ + t * B₁) =
      (1 - t) ^ 2 * (A₀ * b₀ - a₀ * B₀) + t * (1 - t) * (A₀ * b₁ + A₁ * b₀ - a₀ * B₁ - a₁ * B₀) +
        t ^ 2 * (A₁ * b₁ - a₁ * B₁) := by
    ring
  rw [hexp]
  have h1t : 0 ≤ 1 - t := by linarith
  have k1 := mul_nonneg (sq_nonneg (1 - t)) hQ0
  have k2 := mul_nonneg (mul_nonneg ht0 h1t) hmix
  have k3 := mul_nonneg (sq_nonneg t) hQ1
  linarith

/-- Degenerate Bernstein step: if the `t = 1` endpoint vanishes identically (`A₁ = B₁ = a₁ = b₁ = 0`), then
`Q(t) = (1 − t)² Q₀₀ ≥ 0`. [folklore] -/
theorem bernstein_step_degenerate (A₀ A₁ B₀ B₁ a₀ a₁ b₀ b₁ t : ℝ)
    (hQ0 : 0 ≤ A₀ * b₀ - a₀ * B₀) (hA₁ : A₁ = 0) (hB₁ : B₁ = 0) (ha₁ : a₁ = 0) (hb₁ : b₁ = 0) :
    0 ≤ ((1 - t) * A₀ + t * A₁) * ((1 - t) * b₀ + t * b₁) - ((1 - t) * a₀ + t * a₁) * ((1 - t) * B₀ + t * B₁) := by
  subst hA₁ hB₁ ha₁ hb₁
  have hexp : ((1 - t) * A₀ + t * 0) * ((1 - t) * b₀ + t * 0) - ((1 - t) * a₀ + t * 0) * ((1 - t) * B₀ + t * 0) =
      (1 - t) ^ 2 * (A₀ * b₀ - a₀ * B₀) := by ring
  rw [hexp]
  exact mul_nonneg (sq_nonneg _) hQ0

omit [Fintype V] in
/-- `{y ↮ s, v, X} = {y ↮ s, X} ∖ {y ↔ v}`. [folklore] -/
theorem avoidEv_insert_insert_eq (s y v : V) (X : Set V) :
    avoidEv y (insert s (insert v X)) = avoidEv y (insert s X) ∩ (openConn y v : Set (BondConfig V))ᶜ := by
  ext ω
  simp only [avoidEv, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_inter_iff, Set.mem_compl_iff, openConn,
    forall_eq_or_imp]
  tauto

/-- `1_{E ∩ Fᶜ} = 1_E (1 − 1_F)`. [folklore] -/
theorem ind_inter_compl {α : Type*} (E F : Set α) (a : α) : ind (E ∩ Fᶜ) a = ind E a * (1 - ind F a) := by
  by_cases hE : a ∈ E <;> by_cases hF : a ∈ F
  · rw [ind_of_not_mem (fun h => h.2 hF), ind_of_mem hE, ind_of_mem hF]; ring
  · rw [ind_of_mem (Set.mem_inter hE hF), ind_of_mem hE, ind_of_not_mem hF]; ring
  · rw [ind_of_not_mem (fun h => hE h.1), ind_of_not_mem hE]; ring
  · rw [ind_of_not_mem (fun h => hE h.1), ind_of_not_mem hE]; ring

/-- **Lemma 2 (avoidance monotonicity)**: `μ(y↔z | y↮s,X) ≥ μ(y↔z | y↮s,X,v)`, i.e.
`a₁ b₀ ≤ a₀ b₁` with `a_i, b_i` the y-side masses at the states `X` (index `0`) and `X ∪ {v}` (index `1`) —
BHK's Theorem 1.3 for the cluster of `y` given `{y ↮ s, X}` (`1{y↔z}` increasing, `1{y↮v}` decreasing).
[cite: VandenbergHaggstromKahn2005, Thm. 1.3 (p. 6) — corollary] -/
theorem lemma2_avoidance (p : Sym2 V → unitInterval) (s y z v : V) (X : Set V) (hsy : s ≠ y) :
    taa (fun e => (p e : ℝ)) s y z (insert v X) * tab (fun e => (p e : ℝ)) s y X ≤
      taa (fun e => (p e : ℝ)) s y z X * tab (fun e => (p e : ℝ)) s y (insert v X) := by
  classical
  by_cases hyX : y ∈ X
  · -- `y ∈ X`: the masses at the state `X` vanish
    have h0 : tab (fun e => (p e : ℝ)) s y X = 0 := by
      refine Finset.sum_eq_zero fun ω _ => ?_
      have : ω ∉ avoidEv y (insert s X) := fun h =>
        (h : ∀ t ∈ insert s X, ¬ (openGraph ω).Reachable y t) y (Set.mem_insert_of_mem _ hyX)
          (SimpleGraph.Reachable.refl _)
      rw [ind_of_not_mem this, mul_zero]
    have h0' : taa (fun e => (p e : ℝ)) s y z X = 0 := by
      refine Finset.sum_eq_zero fun ω _ => ?_
      have : ω ∉ avoidEv y (insert s X) ∩ openConn y z := fun h =>
        (h.1 : ∀ t ∈ insert s X, ¬ (openGraph ω).Reachable y t) y (Set.mem_insert_of_mem _ hyX)
          (SimpleGraph.Reachable.refl _)
      rw [ind_of_not_mem this, mul_zero]
    rw [h0, h0', mul_zero, zero_mul]
  set T : Set V := insert s X with hT
  have hyT : y ∉ T := by
    intro h
    rcases Set.mem_insert_iff.1 h with h | h
    · exact hsy h.symm
    · exact hyX h
  -- BHK Thm 1.3 for the cluster of `y` given `{y ↮ T}`, `F = χ_z` increasing, `G = 1 − χ_v` decreasing
  set χ : V → Set (Sym2 V) → ℝ := fun u C => if (u = y ∨ ∃ e ∈ C, u ∈ e) then 1 else 0 with hχ
  have hχmono : ∀ u, Monotone (χ u) := by
    intro u C C' hCC'
    simp only [hχ]
    by_cases h : (u = y ∨ ∃ e ∈ C, u ∈ e)
    · rw [if_pos h, if_pos (h.imp id fun ⟨e, he, hue⟩ => ⟨e, hCC' he, hue⟩)]
    · rw [if_neg h]; split_ifs <;> norm_num
  have hχeq : ∀ (u : V) (ω : BondConfig V), χ u (openEdgeCluster ω y) = ind (openConn y u) ω := by
    intro u ω
    by_cases h : ω ∈ openConn y u
    · rw [ind_of_mem h, hχ]; simp only [if_pos ((reachable_iff_exists_mem_openEdgeCluster ω y u).1 h)]
    · rw [ind_of_not_mem h, hχ]
      have h' : ¬ (u = y ∨ ∃ e ∈ openEdgeCluster ω y, u ∈ e) := fun hh =>
        h ((reachable_iff_exists_mem_openEdgeCluster ω y u).2 hh)
      simp only [if_neg h']
  have key := BHK2006_clusterConditionalPositiveAssociation_holds.antitone_right V p y T (χ z)
    (fun C => 1 - χ v C) (hχmono z) (fun C C' h => by have := hχmono v h; linarith) hyT
  have hD : {ω : BondConfig V | ∀ x ∈ T, ¬ (openGraph ω).Reachable y x} = avoidEv y T := rfl
  rw [hD] at key
  have hset : avoidEv y (insert s (insert v X)) = avoidEv y T ∩ (openConn y v : Set (BondConfig V))ᶜ :=
    avoidEv_insert_insert_eq s y v X
  have e1 : (prodBernoulli p).real (avoidEv y T) = tab (fun e => (p e : ℝ)) s y X := by
    rw [measureReal_eq_sum]; rfl
  have e2 : ∫ ω in avoidEv y T, χ z (openEdgeCluster ω y) * (1 - χ v (openEdgeCluster ω y)) ∂(prodBernoulli p) =
      taa (fun e => (p e : ℝ)) s y z (insert v X) := by
    rw [setIntegral_eq_sum, taa, hset]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [hχeq, hχeq, Set.inter_right_comm, ind_inter_compl, ind_inter]
    ring
  have e3 : ∫ ω in avoidEv y T, χ z (openEdgeCluster ω y) ∂(prodBernoulli p) =
      taa (fun e => (p e : ℝ)) s y z X := by
    rw [setIntegral_eq_sum, taa]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [hχeq, ind_inter]
    ring
  have e4 : ∫ ω in avoidEv y T, (1 - χ v (openEdgeCluster ω y)) ∂(prodBernoulli p) =
      tab (fun e => (p e : ℝ)) s y (insert v X) := by
    rw [setIntegral_eq_sum, tab, hset]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [hχeq, ind_inter_compl]
    ring
  rw [e1, e2, e3, e4] at key
  linarith

end TA

end HullPort

end Percolation.Continuity
