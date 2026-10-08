import Percolation.Continuity.HullPort.TAInduction
import Percolation.Util.Linter

/-!
# Marker dominance with an avoided set: `T_A` for indicator test functions suffices (layer cake)

`Q = taQ` is linear in the test function `g`, and a monotone `g ≥ 0` on the finite lattice of edge sets is a nonnegative
combination of indicators of upper sets (peel off `m · 1{g > 0}`, `m` the least positive value).  Hence Lemma
`P_v` is only needed for indicators `g = 1_U` of upper sets `U` of clusters — the event form of Gladkov's
cluster-conditional Harris inequality (`MarkerDominancePv.sum_condSumW_ge`):
(Layer-cake decomposition.)
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

/-- `delE` is linear in the integrand. [folklore] -/
theorem delE_add_smul (w : Sym2 V → ℝ) (B : Set (Sym2 V)) (c : ℝ) (φ ψ : Set (Sym2 V) → ℝ) :
    delE w B (fun η => c * φ η + ψ η) = c * delE w B φ + delE w B ψ := by
  simp only [delE, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun η _ => ?_
  ring

/-- `c` is linear in the test function. [folklore] -/
theorem taC_add_smul (w : Sym2 V → ℝ) (s y : V) (X : Set V) (c : ℝ) (g₁ g₂ : Set (Sym2 V) → ℝ)
    (ω : Set (Sym2 V)) :
    taC w s y X (fun C => c * g₁ C + g₂ C) ω = c * taC w s y X g₁ ω + taC w s y X g₂ ω := by
  simp only [taC]
  have h1 : (fun η : Set (Sym2 V) => (c * g₁ (openEdgeCluster η s) + g₂ (openEdgeCluster η s)) *
      ind (openConn s y) η) = fun η => c * (g₁ (openEdgeCluster η s) * ind (openConn s y) η) +
        g₂ (openEdgeCluster η s) * ind (openConn s y) η := by
    funext η; ring
  have h2 : (fun η : Set (Sym2 V) => c * g₁ (openEdgeCluster η s) + g₂ (openEdgeCluster η s)) =
      fun η => c * (fun ζ => g₁ (openEdgeCluster ζ s)) η + (fun ζ => g₂ (openEdgeCluster ζ s)) η := by
    funext η; rfl
  rw [h1, delE_add_smul, h2, delE_add_smul]
  ring

/-- `Q` is linear in the test function. [folklore] -/
theorem taQ_add_smul (w : Sym2 V → ℝ) (s y z : V) (X : Set V) (c : ℝ) (g₁ g₂ : Set (Sym2 V) → ℝ) :
    taQ w s y z X (fun C => c * g₁ C + g₂ C) = c * taQ w s y z X g₁ + taQ w s y z X g₂ := by
  simp only [taQ, taA, taB, taC_add_smul, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  have e1 : ∀ ω : Set (Sym2 V), weight w ω * (ind (avoidEv s X) ω *
      (taNW w s y z X ω / taN w s y X ω * (c * taC w s y X g₁ ω))) =
      c * (weight w ω * (ind (avoidEv s X) ω * (taNW w s y z X ω / taN w s y X ω * taC w s y X g₁ ω))) := by
    intro ω; ring
  have e2 : ∀ ω : Set (Sym2 V), weight w ω * (ind (avoidEv s X) ω * (c * taC w s y X g₁ ω)) =
      c * (weight w ω * (ind (avoidEv s X) ω * taC w s y X g₁ ω)) := by
    intro ω; ring
  simp only [e1, e2, ← Finset.mul_sum]
  ring

/-- **`Q ≥ 0` for all monotone `g ≥ 0` from `P_v` for indicators of upper sets** (layer cake: a monotone `g ≥ 0` on the
finite lattice `Set (Sym2 V)` is `m · 1_{g > 0} + g'` with `{g > 0}` an upper set, `m` the least positive value and `g'`
monotone, `≥ 0`, of smaller support). [folklore] -/
theorem taQ_nonneg_of_PvI (s y : V) (hsy : s ≠ y)
    (hPvI : ∀ U : Set (Set (Sym2 V)), IsUpperSet U →
      ∀ (q : Sym2 V → unitInterval), (∀ e, (q e : ℝ) < 1) → ∀ v' : V,
      taB (fun e => (q e : ℝ)) s y {v'} (fun C => ind U C) ≤
        (1 - delE (fun e => (q e : ℝ)) ∅ (ind ((openConn s y : Set (BondConfig V))ᶜ ∩ openConn y v')) /
              delE (fun e => (q e : ℝ)) ∅ (ind (openConn s y : Set (BondConfig V))ᶜ)) *
          (delE (fun e => (q e : ℝ)) ∅ (fun η => (fun C => ind U C) (openEdgeCluster η s) * ind (openConn s y) η) -
            delE (fun e => (q e : ℝ)) ∅ (fun η => (fun C => ind U C) (openEdgeCluster η s)) *
              delE (fun e => (q e : ℝ)) ∅ (ind (openConn s y))))
    (g : Set (Sym2 V) → ℝ) (hg : Monotone g) (hg0 : ∀ C, 0 ≤ g C)
    (w : Sym2 V → unitInterval) (hw : ∀ e, (w e : ℝ) < 1) (X : Set V) (z : V) :
    0 ≤ taQ (fun e => (w e : ℝ)) s y z X g := by
  classical
  -- induction on the size of the support of `g`
  suffices H : ∀ (n : ℕ) (g : Set (Sym2 V) → ℝ), Monotone g → (∀ C, 0 ≤ g C) →
      (Finset.univ.filter (fun C : Set (Sym2 V) => 0 < g C)).card = n → 0 ≤ taQ (fun e => (w e : ℝ)) s y z X g from
    H _ g hg hg0 rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro g hg hg0 hn
  set S : Finset (Set (Sym2 V)) := Finset.univ.filter (fun C : Set (Sym2 V) => 0 < g C) with hS
  by_cases hS0 : S = ∅
  · -- `g = 0`
    have hg00 : ∀ C, g C = 0 := by
      intro C
      have hC : C ∉ S := by rw [hS0]; exact Finset.notMem_empty C
      have hC' : ¬ 0 < g C := fun h => hC (Finset.mem_filter.2 ⟨Finset.mem_univ C, h⟩)
      exact le_antisymm (not_lt.1 hC') (hg0 C)
    have hgz : g = fun C => 0 * (fun C : Set (Sym2 V) => ind (Set.univ : Set (Set (Sym2 V))) C) C +
        (fun _ : Set (Sym2 V) => (0 : ℝ)) C := by
      funext C; rw [hg00 C]; ring
    have hQ0 : taQ (fun e => (w e : ℝ)) s y z X (fun _ : Set (Sym2 V) => (0 : ℝ)) = 0 := by
      simp [taQ, taA, taB, taC, delE]
    rw [hgz, taQ_add_smul, hQ0]; simp
  · -- peel off `m · 1_U`, `U = {g > 0}`, `m` the least positive value
    have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.2 hS0
    set m : ℝ := S.inf' hSne g with hm
    have hmpos : 0 < m := by
      obtain ⟨C, hC, hCm⟩ := Finset.exists_mem_eq_inf' hSne g
      rw [hm, hCm]; exact (Finset.mem_filter.1 hC).2
    have hmle : ∀ C, 0 < g C → m ≤ g C := fun C hC =>
      Finset.inf'_le g (Finset.mem_filter.2 ⟨Finset.mem_univ C, hC⟩)
    set U : Set (Set (Sym2 V)) := {C | 0 < g C} with hU
    have hUup : IsUpperSet U := fun C C' hCC' (hC : 0 < g C) => lt_of_lt_of_le hC (hg hCC')
    set g' : Set (Sym2 V) → ℝ := fun C => g C - m * ind U C with hg'
    have hg'0 : ∀ C, 0 ≤ g' C := by
      intro C; simp only [hg']
      by_cases hC : 0 < g C
      · rw [ind_of_mem (show C ∈ U from hC)]; linarith [hmle C hC]
      · rw [ind_of_not_mem (show C ∉ U from hC)]; linarith [hg0 C]
    have hg'mono : Monotone g' := by
      intro C C' hCC'
      simp only [hg']
      by_cases hC : 0 < g C
      · have hC' : 0 < g C' := lt_of_lt_of_le hC (hg hCC')
        rw [ind_of_mem (show C ∈ U from hC), ind_of_mem (show C' ∈ U from hC')]
        linarith [hg hCC']
      · rw [ind_of_not_mem (show C ∉ U from hC)]
        have : g C = 0 := le_antisymm (not_lt.1 hC) (hg0 C)
        rw [this]; linarith [hg'0 C']
    -- the support of `g'` is strictly smaller: the minimisers drop out
    obtain ⟨C₀, hC₀S, hC₀m⟩ := Finset.exists_mem_eq_inf' hSne g
    have hlt : (Finset.univ.filter (fun C : Set (Sym2 V) => 0 < g' C)).card < n := by
      rw [← hn]
      apply Finset.card_lt_card
      refine ⟨fun C hC => ?_, fun hsub => ?_⟩
      · rw [Finset.mem_filter] at hC ⊢
        refine ⟨hC.1, ?_⟩
        by_contra hgC
        have : g' C = 0 := by
          simp only [hg']; rw [ind_of_not_mem (show C ∉ U from hgC)]
          have : g C = 0 := le_antisymm (not_lt.1 hgC) (hg0 C)
          rw [this]; ring
        linarith [hC.2]
      · have h1 := (Finset.mem_filter.1 (hsub hC₀S)).2
        have h2 : g' C₀ = 0 := by
          simp only [hg']
          rw [ind_of_mem (show C₀ ∈ U from (Finset.mem_filter.1 hC₀S).2), ← hC₀m, hm]; ring
        linarith
    have ih' := ih _ hlt g' hg'mono hg'0 rfl
    have hdec : g = fun C => m * (fun C : Set (Sym2 V) => ind U C) C + g' C := by
      funext C; simp only [hg']; ring
    rw [hdec, taQ_add_smul]
    have hQU := taQ_nonneg_of_Pv s y hsy (fun C => ind U C) (hPvI U hUup) w hw X z
    exact add_nonneg (mul_nonneg hmpos.le hQU) ih'

/-- **`T_A ≥ 0` (shape `hTA`) from `P_v` for indicator test functions.** [folklore] -/
theorem TA_of_PvI (s y z : V) (X : Set V) (hsy : s ≠ y)
    (hPvI : ∀ U : Set (Set (Sym2 V)), IsUpperSet U →
      ∀ (q : Sym2 V → unitInterval), (∀ e, (q e : ℝ) < 1) → ∀ v' : V,
      taB (fun e => (q e : ℝ)) s y {v'} (fun C => ind U C) ≤
        (1 - delE (fun e => (q e : ℝ)) ∅ (ind ((openConn s y : Set (BondConfig V))ᶜ ∩ openConn y v')) /
              delE (fun e => (q e : ℝ)) ∅ (ind (openConn s y : Set (BondConfig V))ᶜ)) *
          (delE (fun e => (q e : ℝ)) ∅ (fun η => (fun C => ind U C) (openEdgeCluster η s) * ind (openConn s y) η) -
            delE (fun e => (q e : ℝ)) ∅ (fun η => (fun C => ind U C) (openEdgeCluster η s)) *
              delE (fun e => (q e : ℝ)) ∅ (ind (openConn s y)))) :
    ∀ p : Sym2 V → unitInterval, (∀ e, 0 < p e ∧ p e < 1) →
      ∀ g : Set (Sym2 V) → ℝ, Monotone g → (∀ C, 0 ≤ g C) →
      0 ≤ ∫ ω in {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x},
        ((prodBernoulli p).real {ω' : BondConfig V | ∀ x ∈ insert s X, ¬ (openGraph ω').Reachable y x} *
              ((prodBernoulli p).real ((· \ {e : Sym2 V | ∃ v ∈ e, ∃ x ∈ X, (openGraph ω).Reachable x v}) ⁻¹'
                  ((openConn s y : Set (BondConfig V))ᶜ ∩ openConn y z)) /
                (prodBernoulli p).real ((· \ {e : Sym2 V | ∃ v ∈ e, ∃ x ∈ X, (openGraph ω).Reachable x v}) ⁻¹'
                  ((openConn s y : Set (BondConfig V))ᶜ))) -
            (prodBernoulli p).real ({ω' : BondConfig V | ∀ x ∈ insert s X, ¬ (openGraph ω').Reachable y x} ∩
              openConn y z)) *
          ((∫ η in (· \ {e : Sym2 V | ∃ v ∈ e, ∃ x ∈ X, (openGraph ω).Reachable x v}) ⁻¹'
                (openConn s y : Set (BondConfig V)),
                g (openEdgeCluster (η \ {e : Sym2 V | ∃ v ∈ e, ∃ x ∈ X, (openGraph ω).Reachable x v}) s)
                ∂(prodBernoulli p)) -
            (∫ η, g (openEdgeCluster (η \ {e : Sym2 V | ∃ v ∈ e, ∃ x ∈ X, (openGraph ω).Reachable x v}) s)
              ∂(prodBernoulli p)) *
              (prodBernoulli p).real ((· \ {e : Sym2 V | ∃ v ∈ e, ∃ x ∈ X, (openGraph ω).Reachable x v}) ⁻¹'
                (openConn s y : Set (BondConfig V))))
        ∂(prodBernoulli p) := by
  intro p hp g hg hg0
  rw [TA_integral_eq_taQ]
  have hp' : ∀ e, ((p e : unitInterval) : ℝ) < 1 := fun e => by
    have h1 : p e < 1 := (hp e).2
    exact_mod_cast h1
  exact taQ_nonneg_of_PvI s y hsy hPvI g hg hg0 p hp' X z

end TA

end HullPort

end Percolation.Continuity
