import Percolation.Continuity.HullPort.SelectionThreeTA
import Percolation.Continuity.HullPort.TABase
import Percolation.Continuity.HullPort.TACond
import Percolation.Util.Linter

/-!
# Marker dominance with an avoided set: the induction for `T_A ≥ 0`, and SL(3,1) from `P_v`

Part 5 (last) of the proof of `T_A ≥ 0`, in set-`X` form:
* `HullPort.deltaN_nonneg` — `Δ̂_N ≥ 0` from `Q(S₀; marker v) ≥ 0` and step (II) (`taB_insert_le`);
* `HullPort.taQ_nonneg_of_Pv` — `Q = A·b − a·B ≥ 0` for every weight vector with all weights `< 1`, every avoided set
  `X` and every marker `z`, by strong induction on `(|V ∖ X|, #positive pairs joining X to V ∖ X)`: one-edge sections
  (`Continuity/HullPort/TASections`), Bernstein step and Lemma 2 (`Continuity/HullPort/TAStep`), `Δ̂_N`, base case (`Continuity/HullPort/TABase`);
[cite: VandenbergHaggstromKahn2005, Thm. 1.3 (p. 6), §2.1 (corollaries)]
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

/-- **`Δ̂_N ≥ 0`**: `B₀ b₁ − B₁ b₀ = Q(S₀; marker v) + b₀·(B₀ − A^{(v)}₀ − B₁) ≥ 0`. [folklore] -/
theorem deltaN_nonneg (w : Sym2 V → unitInterval) (hw : ∀ e, (w e : ℝ) < 1) (s y v : V) (X : Set V)
    (g : Set (Sym2 V) → ℝ)
    (hPv : ∀ (q : Sym2 V → unitInterval), (∀ e, (q e : ℝ) < 1) → ∀ v' : V,
      taB (fun e => (q e : ℝ)) s y {v'} g ≤
        (1 - delE (fun e => (q e : ℝ)) ∅ (ind ((openConn s y : Set (BondConfig V))ᶜ ∩ openConn y v')) /
              delE (fun e => (q e : ℝ)) ∅ (ind (openConn s y : Set (BondConfig V))ᶜ)) *
          (delE (fun e => (q e : ℝ)) ∅ (fun η => g (openEdgeCluster η s) * ind (openConn s y) η) -
            delE (fun e => (q e : ℝ)) ∅ (fun η => g (openEdgeCluster η s)) *
              delE (fun e => (q e : ℝ)) ∅ (ind (openConn s y))))
    (hQv : 0 ≤ taQ (fun e => (w e : ℝ)) s y v X g) :
    0 ≤ taB (fun e => (w e : ℝ)) s y X g * tab (fun e => (w e : ℝ)) s y (insert v X) -
      taB (fun e => (w e : ℝ)) s y (insert v X) g * tab (fun e => (w e : ℝ)) s y X := by
  have hII := taB_insert_le w hw s y v X g hPv
  have hw0 : ∀ e, 0 ≤ (w e : ℝ) := fun e => (w e).2.1
  have hw1 : ∀ e, (w e : ℝ) ≤ 1 := fun e => (w e).2.2
  have hb0 : 0 ≤ tab (fun e => (w e : ℝ)) s y X :=
    Finset.sum_nonneg fun ω _ => mul_nonneg (weight_nonneg hw0 hw1 ω) (ind_nonneg _ _)
  rw [tab_insert_eq]
  rw [taQ] at hQv
  have e1 : taB (fun e => (w e : ℝ)) s y X g * (tab (fun e => (w e : ℝ)) s y X - taa (fun e => (w e : ℝ)) s y v X) -
      taB (fun e => (w e : ℝ)) s y (insert v X) g * tab (fun e => (w e : ℝ)) s y X =
      (taA (fun e => (w e : ℝ)) s y v X g * tab (fun e => (w e : ℝ)) s y X -
        taa (fun e => (w e : ℝ)) s y v X * taB (fun e => (w e : ℝ)) s y X g) +
      (taB (fun e => (w e : ℝ)) s y X g - taA (fun e => (w e : ℝ)) s y v X g -
        taB (fun e => (w e : ℝ)) s y (insert v X) g) * tab (fun e => (w e : ℝ)) s y X := by ring
  rw [e1]
  exact add_nonneg hQv (mul_nonneg (by linarith) hb0)

/-- **`T_A ≥ 0` in the form `Q = A·b − a·B ≥ 0`**, for every weight
vector with all weights `< 1`, every avoided set `X` and every marker `z`, given Lemma `P_v` (`hPv`).  Strong induction on
`(|V ∖ X|, #{non-loop pairs of positive weight joining X to V ∖ X})`: the base case is `taQ_eq_zero_of_noBoundary`; in the step
one such pair `e = {x₀, v}` is resampled (`…_section`), the endpoints are the states `(w[e↦0], X)` and `(w[e↦0], X ∪ {v})`
(both smaller), and `bernstein_step` concludes with `lemma2_avoidance` and `deltaN_nonneg` (which uses the induction
hypothesis at `(w[e↦0], X)` with the marker `v`). [folklore] -/
theorem taQ_nonneg_of_Pv (s y : V) (hsy : s ≠ y) (g : Set (Sym2 V) → ℝ)
    (hPv : ∀ (q : Sym2 V → unitInterval), (∀ e, (q e : ℝ) < 1) → ∀ v' : V,
      taB (fun e => (q e : ℝ)) s y {v'} g ≤
        (1 - delE (fun e => (q e : ℝ)) ∅ (ind ((openConn s y : Set (BondConfig V))ᶜ ∩ openConn y v')) /
              delE (fun e => (q e : ℝ)) ∅ (ind (openConn s y : Set (BondConfig V))ᶜ)) *
          (delE (fun e => (q e : ℝ)) ∅ (fun η => g (openEdgeCluster η s) * ind (openConn s y) η) -
            delE (fun e => (q e : ℝ)) ∅ (fun η => g (openEdgeCluster η s)) *
              delE (fun e => (q e : ℝ)) ∅ (ind (openConn s y))))
    (w : Sym2 V → unitInterval) (hw : ∀ e, (w e : ℝ) < 1) (X : Set V) (z : V) :
    0 ≤ taQ (fun e => (w e : ℝ)) s y z X g := by
  classical
  -- the induction measure
  set M : ℕ := Fintype.card (Sym2 V) with hM
  have main : ∀ (N : ℕ) (w : Sym2 V → unitInterval), (∀ e, (w e : ℝ) < 1) → ∀ (X : Set V),
      (Finset.univ.filter (fun u : V => u ∉ X)).card * (M + 1) +
        (Finset.univ.filter (fun e : Sym2 V => ¬ e.IsDiag ∧ (∃ a ∈ e, a ∈ X) ∧ (∃ b ∈ e, b ∉ X) ∧
          0 < (w e : ℝ))).card = N → ∀ z : V, 0 ≤ taQ (fun e => (w e : ℝ)) s y z X g := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
    intro w hw X hN z
    set ŵ : Sym2 V → ℝ := fun e => (w e : ℝ) with hŵ
    have hw0 : ∀ e, 0 ≤ ŵ e := fun e => (w e).2.1
    have hw1 : ∀ e, ŵ e ≤ 1 := fun e => (w e).2.2
    have hm : ∑ ω, weight ŵ ω = 1 := by
      have h1 := integral_prodBernoulli_eq_sum w fun _ => (1 : ℝ)
      simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at h1
      exact h1.symm
    set F : Finset (Sym2 V) := Finset.univ.filter (fun e : Sym2 V => ¬ e.IsDiag ∧ (∃ a ∈ e, a ∈ X) ∧
      (∃ b ∈ e, b ∉ X) ∧ 0 < (w e : ℝ)) with hF
    by_cases hF0 : F = ∅
    · -- base case: no positive boundary pair
      have hbd : ∀ e : Sym2 V, ¬ e.IsDiag → ∀ a ∈ e, ∀ b ∈ e, a ∈ X → b ∉ X → ŵ e = 0 := by
        intro e hd a ha b hb haX hbX
        by_contra hne
        have hpos : 0 < (w e : ℝ) := lt_of_le_of_ne (hw0 e) (Ne.symm hne)
        have : e ∈ F := by
          rw [hF, Finset.mem_filter]
          exact ⟨Finset.mem_univ _, hd, ⟨a, ha, haX⟩, ⟨b, hb, hbX⟩, hpos⟩
        rw [hF0] at this
        exact absurd this (Finset.notMem_empty _)
      rw [taQ_eq_zero_of_noBoundary ŵ hw0 hw1 hm s y z hsy X g hbd]
    · -- inductive step: pick a positive boundary pair `e₀ = {x₀, v}`
      obtain ⟨e₀, he₀⟩ := Finset.nonempty_iff_ne_empty.2 hF0
      have he₀' := (Finset.mem_filter.1 he₀).2
      obtain ⟨hdiag, ⟨x₀, hx₀e, hx₀X⟩, ⟨v, hve, hvX⟩, hpos⟩ := he₀'
      have hx₀v : x₀ ≠ v := fun h => hvX (h ▸ hx₀X)
      have he₀eq : e₀ = s(x₀, v) := (Sym2.mem_and_mem_iff hx₀v).1 ⟨hx₀e, hve⟩
      set w₀ : Sym2 V → unitInterval := Function.update w e₀ 0 with hw₀def
      set ŵ₀ : Sym2 V → ℝ := fun e => (w₀ e : ℝ) with hŵ₀
      have he0 : ŵ₀ s(x₀, v) = 0 := by
        simp only [hŵ₀, hw₀def, ← he₀eq, Function.update_self]; rfl
      have hoff : ∀ f, f ≠ s(x₀, v) → ŵ₀ f = ŵ f := by
        intro f hf
        simp only [hŵ₀, hw₀def, hŵ]
        rw [Function.update_of_ne (he₀eq ▸ hf)]
      have hw₀lt : ∀ e, (w₀ e : ℝ) < 1 := by
        intro e
        by_cases h : e = e₀
        · subst h; simp only [hw₀def, Function.update_self]; norm_num
        · simp only [hw₀def, Function.update_of_ne h]; exact hw e
      -- the two smaller states
      have hN0 : (Finset.univ.filter (fun u : V => u ∉ X)).card * (M + 1) +
          (Finset.univ.filter (fun e : Sym2 V => ¬ e.IsDiag ∧ (∃ a ∈ e, a ∈ X) ∧ (∃ b ∈ e, b ∉ X) ∧
            0 < (w₀ e : ℝ))).card < N := by
        rw [← hN]
        apply Nat.add_lt_add_left
        apply Finset.card_lt_card
        refine ⟨fun f hf => ?_, fun hsub => ?_⟩
        · rw [Finset.mem_filter] at hf ⊢
          obtain ⟨_, hd, ha, hb, hp⟩ := hf
          have hfe : f ≠ e₀ := by
            rintro rfl
            simp only [hw₀def, Function.update_self] at hp
            exact absurd hp (by norm_num)
          refine ⟨Finset.mem_univ _, hd, ha, hb, ?_⟩
          simpa only [hw₀def, Function.update_of_ne hfe] using hp
        · have := (Finset.mem_filter.1 (hsub he₀)).2.2.2.2
          simp only [hw₀def, Function.update_self] at this
          exact absurd this (by norm_num)
      have hN1 : (Finset.univ.filter (fun u : V => u ∉ insert v X)).card * (M + 1) +
          (Finset.univ.filter (fun e : Sym2 V => ¬ e.IsDiag ∧ (∃ a ∈ e, a ∈ insert v X) ∧
            (∃ b ∈ e, b ∉ insert v X) ∧ 0 < (w₀ e : ℝ))).card < N := by
        rw [← hN]
        have hn : (Finset.univ.filter (fun u : V => u ∉ insert v X)).card + 1 ≤
            (Finset.univ.filter (fun u : V => u ∉ X)).card := by
          rw [Nat.add_one_le_iff]
          apply Finset.card_lt_card
          refine ⟨fun u hu => ?_, fun hsub => ?_⟩
          · rw [Finset.mem_filter] at hu ⊢
            exact ⟨hu.1, fun h => hu.2 (Set.mem_insert_of_mem _ h)⟩
          · have := (Finset.mem_filter.1 (hsub (Finset.mem_filter.2 ⟨Finset.mem_univ v, hvX⟩))).2
            exact this (Set.mem_insert _ _)
        have hm' : (Finset.univ.filter (fun e : Sym2 V => ¬ e.IsDiag ∧ (∃ a ∈ e, a ∈ insert v X) ∧
            (∃ b ∈ e, b ∉ insert v X) ∧ 0 < (w₀ e : ℝ))).card ≤ M :=
          (Finset.card_le_univ _).trans (le_of_eq rfl)
        calc (Finset.univ.filter (fun u : V => u ∉ insert v X)).card * (M + 1) +
              (Finset.univ.filter (fun e : Sym2 V => ¬ e.IsDiag ∧ (∃ a ∈ e, a ∈ insert v X) ∧
                (∃ b ∈ e, b ∉ insert v X) ∧ 0 < (w₀ e : ℝ))).card
            < (Finset.univ.filter (fun u : V => u ∉ insert v X)).card * (M + 1) + (M + 1) := by
              linarith
          _ = ((Finset.univ.filter (fun u : V => u ∉ insert v X)).card + 1) * (M + 1) := by ring
          _ ≤ (Finset.univ.filter (fun u : V => u ∉ X)).card * (M + 1) := Nat.mul_le_mul_right _ hn
          _ ≤ _ := Nat.le_add_right _ _
      -- induction hypotheses
      have hQ00 : 0 ≤ taQ ŵ₀ s y z X g := ih _ hN0 w₀ hw₀lt X rfl z
      have hQ11 : 0 ≤ taQ ŵ₀ s y z (insert v X) g := by
        refine ih _ ?_ w₀ hw₀lt (insert v X) rfl z
        convert hN1 using 6
      have hQv : 0 ≤ taQ ŵ₀ s y v X g := ih _ hN0 w₀ hw₀lt X rfl v
      -- the one-edge sections
      have sA := taA_section ŵ ŵ₀ s y z x₀ v X hx₀X he0 hoff g
      have sB := taB_section ŵ ŵ₀ s y x₀ v X hx₀X he0 hoff g
      have sa := taa_section ŵ ŵ₀ s y z x₀ v X hx₀X he0 hoff
      have sb := tab_section ŵ ŵ₀ s y x₀ v X hx₀X he0 hoff
      have ht0 : 0 ≤ ŵ s(x₀, v) := hw0 _
      have ht1 : ŵ s(x₀, v) ≤ 1 := hw1 _
      rw [taQ, sA, sB, sa, sb]
      -- Lemma 2 and Δ̂_N at the state `(w₀, X)`
      have hL2 := lemma2_avoidance w₀ s y z v X hsy
      have hΔ := deltaN_nonneg w₀ hw₀lt s y v X g hPv hQv
      rw [taQ] at hQ00 hQ11
      by_cases hyv : y ∈ insert v X
      · -- degenerate endpoint: `y ∈ X ∪ {v}`
        have hA1 := taA_eq_zero_of_mem ŵ₀ s y z hsy (insert v X) hyv g
        have hB1 := taB_eq_zero_of_mem ŵ₀ s y hsy (insert v X) hyv g
        have ha1 := taa_eq_zero_of_mem ŵ₀ s y z (insert v X) (Set.mem_insert_of_mem _ hyv)
        have hb1 := tab_eq_zero_of_mem ŵ₀ s y (insert v X) (Set.mem_insert_of_mem _ hyv)
        exact bernstein_step_degenerate _ _ _ _ _ _ _ _ (ŵ s(x₀, v)) hQ00 hA1 hB1 ha1 hb1
      · have hyX : y ∉ insert s X := by
          intro h
          rcases Set.mem_insert_iff.1 h with h | h
          · exact hsy h.symm
          · exact hyv (Set.mem_insert_of_mem _ h)
        have hyvX : y ∉ insert s (insert v X) := by
          intro h
          rcases Set.mem_insert_iff.1 h with h | h
          · exact hsy h.symm
          · exact hyv h
        have hw₀0 : ∀ e, 0 ≤ ŵ₀ e := fun e => (w₀ e).2.1
        have hb0 := tab_pos ŵ₀ hw₀0 hw₀lt s y X hyX
        have hb1 := tab_pos ŵ₀ hw₀0 hw₀lt s y (insert v X) hyvX
        exact bernstein_step _ _ _ _ _ _ _ _ (ŵ s(x₀, v)) ht0 ht1 hQ00 hQ11 hΔ (by linarith [hL2]) hb0 hb1
  exact main _ w hw X rfl z

/-! ### Back to the measure-level interface `hTA` and to SL(3,1) -/

theorem TA_integral_eq_taQ (p : Sym2 V → unitInterval) (s y z : V) (X : Set V) (g : Set (Sym2 V) → ℝ) :
    ∫ ω in {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x},
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
        ∂(prodBernoulli p) = taQ (fun e => (p e : ℝ)) s y z X g := by
  classical
  have hAy : (prodBernoulli p).real {ω' : BondConfig V | ∀ x ∈ insert s X, ¬ (openGraph ω').Reachable y x} =
      tab (fun e => (p e : ℝ)) s y X := by
    rw [measureReal_eq_sum]; rfl
  have hAW : (prodBernoulli p).real ({ω' : BondConfig V | ∀ x ∈ insert s X, ¬ (openGraph ω').Reachable y x} ∩
      openConn y z) = taa (fun e => (p e : ℝ)) s y z X := by
    rw [measureReal_eq_sum]; rfl
  have hpre : ∀ (ω : BondConfig V) (E : Set (BondConfig V)),
      (prodBernoulli p).real ((· \ {e : Sym2 V | ∃ v ∈ e, ∃ x ∈ X, (openGraph ω).Reachable x v}) ⁻¹' E) =
        delE (fun e => (p e : ℝ)) (cut X ω) (ind E) := by
    intro ω E; rw [measureReal_eq_sum]; rfl
  have hint1 : ∀ ω : BondConfig V,
      ∫ η in (· \ {e : Sym2 V | ∃ v ∈ e, ∃ x ∈ X, (openGraph ω).Reachable x v}) ⁻¹'
          (openConn s y : Set (BondConfig V)),
          g (openEdgeCluster (η \ {e : Sym2 V | ∃ v ∈ e, ∃ x ∈ X, (openGraph ω).Reachable x v}) s)
          ∂(prodBernoulli p) =
        delE (fun e => (p e : ℝ)) (cut X ω) (fun ζ => g (openEdgeCluster ζ s) * ind (openConn s y) ζ) := by
    intro ω; rw [setIntegral_eq_sum]; rfl
  have hint2 : ∀ ω : BondConfig V,
      ∫ η, g (openEdgeCluster (η \ {e : Sym2 V | ∃ v ∈ e, ∃ x ∈ X, (openGraph ω).Reachable x v}) s)
          ∂(prodBernoulli p) = delE (fun e => (p e : ℝ)) (cut X ω) (fun ζ => g (openEdgeCluster ζ s)) := by
    intro ω; rw [integral_prodBernoulli_eq_sum]; rfl
  rw [setIntegral_eq_sum]
  simp only [hAy, hAW, hpre, hint1, hint2]
  have hD : ∀ ω : BondConfig V, ind {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x} ω =
      ind (avoidEv s X) ω := fun ω => rfl
  simp only [hD]
  have hterm : ∀ ω : BondConfig V,
      weight (fun e => (p e : ℝ)) ω *
        ((tab (fun e => (p e : ℝ)) s y X *
              (delE (fun e => (p e : ℝ)) (cut X ω) (ind ((openConn s y : Set (BondConfig V))ᶜ ∩ openConn y z)) /
                delE (fun e => (p e : ℝ)) (cut X ω) (ind (openConn s y : Set (BondConfig V))ᶜ)) -
            taa (fun e => (p e : ℝ)) s y z X) *
          (delE (fun e => (p e : ℝ)) (cut X ω) (fun ζ => g (openEdgeCluster ζ s) * ind (openConn s y) ζ) -
            delE (fun e => (p e : ℝ)) (cut X ω) (fun ζ => g (openEdgeCluster ζ s)) *
              delE (fun e => (p e : ℝ)) (cut X ω) (ind (openConn s y))) * ind (avoidEv s X) ω) =
      tab (fun e => (p e : ℝ)) s y X * (weight (fun e => (p e : ℝ)) ω *
          (ind (avoidEv s X) ω * (taNW (fun e => (p e : ℝ)) s y z X ω / taN (fun e => (p e : ℝ)) s y X ω *
            taC (fun e => (p e : ℝ)) s y X g ω))) -
        taa (fun e => (p e : ℝ)) s y z X * (weight (fun e => (p e : ℝ)) ω *
          (ind (avoidEv s X) ω * taC (fun e => (p e : ℝ)) s y X g ω)) := by
    intro ω; simp only [taC, taN, taNW]; ring
  simp only [hterm, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [taQ, taA, taB]
  ring

end TA

end HullPort

end Percolation.Continuity
