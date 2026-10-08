import Percolation.Literature.TallInvJ
import Percolation.Util.Linter

/-!
# The tall gait, VII: preservation of the invariant along the trunk `T`

The top steps of the trunk (free, or forced on the
steering windows around the two branch points) and the placements of the two branch bricks `γ₁, γ₂`
preserve `TallInv` (Grimmett, *Percolation*, 2nd ed. (1999), §7.3 (A)–(D)).

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §7.3 pp. 172–174.
-/

noncomputable section

namespace Percolation.Literature

open LatticeModels Contour
open scoped Classical

namespace BGNd

variable {d : ℕ} [NeZero d]
variable (Y : TallLayout) (hd : 3 ≤ d) (hL : Y.m + 1 ≤ Y.L) (hH : 2 * Y.m + 2 ≤ Y.H) (a : Site 2) (e : MDir) (τ : TTok d)

omit [NeZero d] in
/-- In phase `T` the branches are empty and the trunk is not. [folklore] -/
theorem phaseOf_eq_segT {st : RS d} (h : phaseOf st = Phase.segT) : st.sT ≠ [] ∧ st.sB1 = [] ∧ st.sB2 = [] := by
  unfold phaseOf at h
  by_cases h2 : st.sB2 ≠ [] <;> by_cases h1 : st.sB1 ≠ [] <;> by_cases hT : st.sT ≠ [] <;> by_cases hJ : st.sJ ≠ [] <;>
    by_cases hR : st.sR ≠ [] <;> simp_all

/-- One more index in the count of forced trunk steps. [folklore] -/
theorem nForced_succ (n₁ n₂ k : ℕ) :
    nForced Y e n₁ n₂ (k + 1) = nForced Y e n₁ n₂ k + (if trunkForce Y e n₁ n₂ k ≠ 0 then 1 else 0) := by
  unfold nForced
  rw [List.range_succ, List.filter_append, List.length_append]
  congr 1
  by_cases h : trunkForce Y e n₁ n₂ k ≠ 0
  · rw [if_pos h]; simp [h]
  · rw [if_neg h]; simp only [ne_eq, Decidable.not_not] at h; simp [h]

/-- The trunk request is `0`, `1` or `-1`. [folklore] -/
theorem trunkForce_cases (n₁ n₂ k : ℕ) :
    trunkForce Y e n₁ n₂ k = 0 ∨ trunkForce Y e n₁ n₂ k = 1 ∨ trunkForce Y e n₁ n₂ k = -1 := by
  have hs : (br1Sign e : ℤ) = 1 ∨ (br1Sign e : ℤ) = -1 := by
    rcases Int.units_eq_one_or (br1Sign e) with h | h <;> simp [h]
  unfold trunkForce
  simp only
  split_ifs <;> rcases hs with h | h <;> simp [h]

/-- Axis and sign along the trunk. [folklore] -/
theorem InvT.axis_sign {sJ sT : List (BrickRec d)} {g1 g2 : Option (BrickRec d)} {D : Prop} (h : InvT hd Y hL hH a e sJ sT g1 g2 D)
    (hne : sT ≠ []) {k : ℕ} (hk : k < sT.length) : (legOf sT k).a = axOf hd e ∧ (legOf sT k).s = sgOf e := by
  have h1 := (h.grown hne).axis_sign (k := k) hk
  have ht := h.turn hne
  rw [ht.axis, ht.sign] at h1
  exact h1

/-- **A top step of the trunk preserves the invariant.** [cite: GrimmettPercolation1999, §7.3 pp. 172–174 (A), (D)] -/
theorem tallInv_topT (hY : Y.OK) {st : RS d} (hI : TallInv hd Y hL hH a e τ st)
    (hph : st.ph = Phase.segT) {rk : BrickRec d} {tl : List (BrickRec d)} (hTl : st.sT = rk :: tl)
    (hsched : tl.length < legLen Y a e e ((legOf (rk :: tl) 0).b (axOf hd e)))
    (hno1 : st.g1 = none → tl.length < n1Of hd Y a e (rk :: tl))
    (hno2 : st.g1 ≠ none → st.g2 = none → tl.length < n2Of hd Y a e (rk :: tl))
    (hgood : GoodRec Y.m Y.L Y.H rk) (o : Finset (Sym2 (Site d))) {sg : Fin d → Bool}
    (hsg : sg = if trunkForce Y e (n1Of hd Y a e (rk :: tl)) (n2Of hd Y a e (rk :: tl)) tl.length = 0 then
        toward (nomT hd Y e ((legOf (rk :: tl) 0).b (latOf hd e))) rk.1.b
      else force (toward (nomT hd Y e ((legOf (rk :: tl) 0).b (latOf hd e))) rk.1.b) (latOf hd e)
        (trunkForce Y e (n1Of hd Y a e (rk :: tl)) (n2Of hd Y a e (rk :: tl)) tl.length)) :
    TallInv hd Y hL hH a e τ { st.put Slot.toT (tStep hL hH rk sg, o) with ph := Phase.segT } := by
  obtain ⟨hTne, h1, h2⟩ := phaseOf_eq_segT (hI.ph_eq ▸ hph)
  have hLp := hY.Lp_nonneg
  have hIT := hI.invT
  rw [hTl] at hIT
  have hne : (rk :: tl) ≠ [] := List.cons_ne_nil _ _
  set y₀ := (legOf (rk :: tl) 0).b (latOf hd e) with hy₀
  set n₁ := n1Of hd Y a e (rk :: tl) with hn₁
  set n₂ := n2Of hd Y a e (rk :: tl) with hn₂
  set w := trunkForce Y e n₁ n₂ tl.length with hw
  set r : BrickRec d := (tStep hL hH rk sg, o) with hr
  have hold : legOf (rk :: tl) tl.length = rk.1 := legOf_cons_length rk tl
  have hnew : legOf (r :: rk :: tl) (rk :: tl).length = r.1 := legOf_cons_length r _
  have hkeep : ∀ k < (rk :: tl).length, legOf (r :: rk :: tl) k = legOf (rk :: tl) k := fun k hk => legOf_cons_of_lt r _ hk
  have e1 : legOf (r :: rk :: tl) tl.length = rk.1 := by rw [hkeep tl.length (by simp), hold]
  have e2 : legOf (r :: rk :: tl) (tl.length + 1) = r.1 := hnew
  have e0 : legOf (r :: rk :: tl) 0 = legOf (rk :: tl) 0 := hkeep 0 (by simp)
  have en1 : n1Of hd Y a e (r :: rk :: tl) = n₁ := by rw [hn₁]; unfold n1Of; rw [e0]
  have en2 : n2Of hd Y a e (r :: rk :: tl) = n₂ := by rw [hn₂]; unfold n2Of; rw [e0]
  obtain ⟨hax, hsx⟩ := hIT.axis_sign Y hd hL hH a e hne (k := tl.length) (by simp)
  rw [hold] at hax hsx
  have haf : latOf hd e ≠ rk.1.a := by rw [hax]; exact latOf_ne_axOf hd e
  have ha0 : ax0 hd ≠ rk.1.a := by rw [hax]; exact (axOf_ne_ax0 hd e).symm
  have hreq_oth : ∀ j, j ≠ latOf hd e → sg j = toward (nomT hd Y e y₀) rk.1.b j := by
    intro j hj; rw [hsg]; split_ifs
    · rfl
    · exact force_of_ne _ hj _
  have hLp' : Y.Lp = (Y.L : ℤ) - Y.m - 1 := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [RS.put]
    exact (phaseOf_of_T (by simp) (by simpa using h1) (by simpa using h2)).symm
  · simp only [RS.put]; exact hI.invA
  · simp only [RS.put]; exact hI.invR
  · simp only [RS.put, hTl]
    exact hI.invJ.of_done Y hd hL hH a e τ fun _ => hIT.prev hne
  · simp only [RS.put, hTl, h1]
    exact
    { prev := fun _ => hIT.prev hne
      gnil := fun h => absurd h (by simp)
      grown := fun _ => grown_cons hL hH (hIT.grown hne) rfl hgood sg o
      turn := fun _ => by rw [e0]; exact hIT.turn hne
      fit := fun _ => by rw [e0]; exact hIT.fit hne
      sched := fun k hk => by
        rw [e0]
        rw [List.length_cons] at hk
        rcases Nat.lt_or_ge (k + 1) (rk :: tl).length with hlt | hge
        · exact hIT.sched k hlt
        · have : k = tl.length := by simp only [List.length_cons] at hge hk; omega
          subst this; exact hsched
      done := fun h => absurd h (by simp)
      lat := fun k hk => by
        rw [en1, en2, e0]
        rw [List.length_cons] at hk
        rcases Nat.lt_or_ge k (rk :: tl).length with hlt | hge
        · rw [hkeep k hlt]; exact hIT.lat k hlt
        · have hk' : k = (rk :: tl).length := by omega
          rw [hk', hnew, hr]
          have h0 := hIT.lat tl.length (by simp)
          rw [hold] at h0
          rw [List.length_cons, nForced_succ, ← hw]
          by_cases hw0 : w = 0
          · have hreq : sg (latOf hd e) = toward (nomT hd Y e y₀) rk.1.b (latOf hd e) := by rw [hsg, if_pos hw0]
            have h1 := abs_sub_le_of_toward hL hH hgood haf hreq
            have hnom : nomT hd Y e y₀ (latOf hd e) = y₀ := by simp [nomT]
            rw [hnom] at h1
            rw [if_neg (by simpa using hw0)]; push_cast; rw [add_zero]
            refine le_trans h1 (max_le h0 ?_)
            have : (0 : ℤ) ≤ (nForced Y e n₁ n₂ tl.length : ℤ) * Y.Lp := by positivity
            linarith
          · have hreq : sg (latOf hd e) = decide (0 ≤ w) := by rw [hsg, if_neg hw0, force_self]
            have hw1 : w = 1 ∨ w = -1 := by rcases trunkForce_cases Y e n₁ n₂ tl.length with h | h <;> [exact absurd h hw0; exact h]
            have h1 := forced_nonneg hL hH hgood haf hw1 hreq
            rw [if_pos hw0]; push_cast
            have habs : |(tStep hL hH rk sg).b (latOf hd e) - rk.1.b (latOf hd e)| ≤ Y.Lp := by
              rw [hLp']
              rcases hw1 with h | h <;> rw [h] at h1 <;> rw [abs_le] <;> constructor <;> linarith [h1.1, h1.2]
            calc |(tStep hL hH rk sg).b (latOf hd e) - y₀|
                = |((tStep hL hH rk sg).b (latOf hd e) - rk.1.b (latOf hd e)) + (rk.1.b (latOf hd e) - y₀)| := by ring_nf
              _ ≤ |(tStep hL hH rk sg).b (latOf hd e) - rk.1.b (latOf hd e)| + |rk.1.b (latOf hd e) - y₀| := abs_add_le _ _
              _ ≤ Y.Lp + (Y.Lp + (nForced Y e n₁ n₂ tl.length : ℤ) * Y.Lp) := add_le_add habs h0
              _ = Y.Lp + ((nForced Y e n₁ n₂ tl.length : ℤ) + 1) * Y.Lp := by ring
      steer := fun k hk => by
        rw [en1, en2]
        rw [List.length_cons] at hk
        rcases Nat.lt_or_ge (k + 1) (rk :: tl).length with hlt | hge
        · rw [hkeep k (by omega), hkeep (k + 1) hlt]; exact hIT.steer k hlt
        · have hk' : k = tl.length := by simp only [List.length_cons] at hge hk; omega
          subst hk'
          rw [e1, e2, hr, ← hw]
          by_cases hw0 : w = 0
          · rw [hw0, zero_mul]
          · have hreq : sg (latOf hd e) = decide (0 ≤ w) := by rw [hsg, if_neg hw0, force_self]
            have hw1 : w = 1 ∨ w = -1 := by rcases trunkForce_cases Y e n₁ n₂ tl.length with h | h <;> [exact absurd h hw0; exact h]
            exact (forced_nonneg hL hH hgood haf hw1 hreq).1
      ht := fun k hk => by
        rw [List.length_cons] at hk
        rcases Nat.lt_or_ge k (rk :: tl).length with hlt | hge
        · rw [hkeep k hlt]; exact hIT.ht k hlt
        · have hk' : k = (rk :: tl).length := by omega
          rw [hk', hnew, hr]
          have h1 := abs_sub_le_of_toward hL hH hgood ha0 (hreq_oth _ (latOf_ne_ax0 hd e).symm)
          have hnom : nomT hd Y e y₀ (ax0 hd) = Y.zOf e := by simp [nomT, (latOf_ne_ax0 hd e).symm]
          rw [hnom] at h1
          refine le_trans h1 (max_le ?_ hY.Lp_le_ρv)
          have := hIT.ht tl.length (by simp)
          rwa [hold] at this
      oth := fun k hk j hj1 hj2 hj3 => by
        rw [List.length_cons] at hk
        rcases Nat.lt_or_ge k (rk :: tl).length with hlt | hge
        · rw [hkeep k hlt]; exact hIT.oth k hlt j hj1 hj2 hj3
        · have hk' : k = (rk :: tl).length := by omega
          rw [hk', hnew, hr]
          have hja : j ≠ rk.1.a := by rw [hax]; exact hj1
          have h1 := abs_sub_le_of_toward hL hH hgood hja (hreq_oth j hj2)
          have hnom : nomT hd Y e y₀ j = 0 := by simp [nomT, hj2, hj3]
          rw [hnom, sub_zero] at h1
          refine le_trans h1 (max_le ?_ le_rfl)
          have := hIT.oth tl.length (by simp) j hj1 hj2 hj3
          rwa [hold, ← sub_zero (rk.1.b j)] at this
      g1_none := fun hg => by
        rw [en1]; have := hno1 hg; simp only [List.length_cons]; omega
      g1_some := fun g hg => by
        rw [en1]
        obtain ⟨hlt, hturn, hht, hoth⟩ := hIT.g1_some g hg
        refine ⟨by rw [List.length_cons]; omega, ?_, hht, hoth⟩
        rw [hkeep _ hlt]; exact hturn
      g2_none := fun hg2 hg1 => by
        rw [en2]; have := hno2 hg1 hg2; simp only [List.length_cons]; omega
      g2_g1 := hIT.g2_g1
      g2_some := fun g hg => by
        rw [en2]
        obtain ⟨hlt, hturn, hht, hoth⟩ := hIT.g2_some g hg
        refine ⟨by rw [List.length_cons]; omega, ?_, hht, hoth⟩
        rw [hkeep _ hlt]; exact hturn }
  · simp [RS.put, h1]
  · simp only [RS.put]; exact hI.invB1
  · simp only [RS.put]; exact hI.invB2
  · simp [RS.put, h2]
  · simp [RS.put, h1]

end BGNd

end Percolation.Literature

end

namespace Percolation.Literature.BGNd

open LatticeModels Contour
open scoped Classical

variable {d : ℕ} [NeZero d]
variable (Y : TallLayout) (hd : 3 ≤ d) (hL : Y.m + 1 ≤ Y.L) (hH : 2 * Y.m + 2 ≤ Y.H) (a : Site 2) (e : MDir) (τ : TTok d)

/-- **Placing the first branch brick preserves the invariant** (given that the first branch point
comes no later than the second, a property of the layout). [cite: GrimmettPercolation1999, §7.3 pp. 172–174 (B), (C)] -/
theorem tallInv_gamma1 (hY : Y.OK) {st : RS d} (hI : TallInv hd Y hL hH a e τ st)
    (hph : st.ph = Phase.segT) {rk : BrickRec d} {tl : List (BrickRec d)} (hTl : st.sT = rk :: tl) (hg1 : st.g1 = none)
    (hn1 : n1Of hd Y a e (rk :: tl) ≤ tl.length) (hn12 : n1Of hd Y a e (rk :: tl) ≤ n2Of hd Y a e (rk :: tl))
    (hgood : GoodRec Y.m Y.L Y.H rk) (o : Finset (Sym2 (Site d))) :
    TallInv hd Y hL hH a e τ
      { st.put Slot.toG1 (sStep hL hH rk (latOf hd e) (br1Sign e) (toward (nomT hd Y e ((legOf (rk :: tl) 0).b (latOf hd e))) rk.1.b), o)
        with ph := Phase.segT } := by
  obtain ⟨hTne, h1, h2⟩ := phaseOf_eq_segT (hI.ph_eq ▸ hph)
  have hLp := hY.Lp_nonneg
  have hIT := hI.invT
  rw [hTl] at hIT
  have hne : (rk :: tl) ≠ [] := List.cons_ne_nil _ _
  have hg2 : st.g2 = none := by
    by_contra h
    exact hIT.g2_g1 h hg1
  set y₀ := (legOf (rk :: tl) 0).b (latOf hd e) with hy₀
  set r : BrickRec d := (sStep hL hH rk (latOf hd e) (br1Sign e) (toward (nomT hd Y e y₀) rk.1.b), o) with hr
  have hold : legOf (rk :: tl) tl.length = rk.1 := legOf_cons_length rk tl
  have hlen1 := hIT.g1_none hg1
  have hn1eq : n1Of hd Y a e (rk :: tl) = tl.length := by simp only [List.length_cons] at hlen1; omega
  obtain ⟨hax, hsx⟩ := hIT.axis_sign Y hd hL hH a e hne (k := tl.length) (by simp)
  rw [hold] at hax hsx
  have haf : latOf hd e ≠ rk.1.a := by rw [hax]; exact latOf_ne_axOf hd e
  have ha0 : ax0 hd ≠ rk.1.a := by rw [hax]; exact (axOf_ne_ax0 hd e).symm
  have hturn := isTurn_sStep hL hH hgood haf (br1Sign e) (toward (nomT hd Y e y₀) rk.1.b)
  have hht : |r.1.b (ax0 hd) - Y.zOf e| ≤ Y.ρv := by
    rw [hr]
    have h1 := abs_sub_le_of_toward_side hL hH hgood haf (br1Sign e) (nom := nomT hd Y e y₀) ha0 (latOf_ne_ax0 hd e).symm rfl
    have hnom : nomT hd Y e y₀ (ax0 hd) = Y.zOf e := by simp [nomT, (latOf_ne_ax0 hd e).symm]
    rw [hnom] at h1
    refine le_trans h1 (max_le ?_ hY.Lp_le_ρv)
    have := hIT.ht tl.length (by simp)
    rwa [hold] at this
  have hoth : ∀ j, j ≠ axOf hd e → j ≠ latOf hd e → j ≠ ax0 hd → |r.1.b j| ≤ Y.Lp := by
    intro j hj1 hj2 hj3
    rw [hr]
    have hja : j ≠ rk.1.a := by rw [hax]; exact hj1
    have h1 := abs_sub_le_of_toward_side hL hH hgood haf (br1Sign e) (nom := nomT hd Y e y₀) hja hj2 rfl
    have hnom : nomT hd Y e y₀ j = 0 := by simp [nomT, hj2, hj3]
    rw [hnom, sub_zero] at h1
    refine le_trans h1 (max_le ?_ le_rfl)
    have := hIT.oth tl.length (by simp) j hj1 hj2 hj3
    rwa [hold, ← sub_zero (rk.1.b j)] at this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [RS.put, hTl]
    exact (phaseOf_of_T (by simp) (by simpa using h1) (by simpa using h2)).symm
  · simp only [RS.put]; exact hI.invA
  · simp only [RS.put]; exact hI.invR
  · simp only [RS.put, hTl]; rw [← hTl]; exact hI.invJ
  · simp only [RS.put, hTl, hg2, h1]
    exact
    { prev := hIT.prev
      gnil := fun h => absurd h hne
      grown := hIT.grown
      turn := hIT.turn
      fit := hIT.fit
      sched := hIT.sched
      done := fun h => absurd h (by simp)
      lat := hIT.lat
      steer := hIT.steer
      ht := hIT.ht
      oth := hIT.oth
      g1_none := fun h => absurd h (by simp)
      g1_some := fun g hg => by
        simp only [Option.some.injEq] at hg
        subst hg
        refine ⟨by rw [hn1eq]; simp, ?_, hht, hoth⟩
        rw [hn1eq, hold, hr, ← hax, ← hsx]
        exact hturn
      g2_none := fun _ _ => by rw [List.length_cons, ← hn1eq]; omega
      g2_g1 := fun h => absurd rfl h
      g2_some := fun g hg => absurd hg (by simp) }
  · simp [RS.put, h1]
  · simp only [RS.put, h1]
    exact invB_single hd Y hL hH a e _ (by simp [h2]) hht hoth hLp
  · simp only [RS.put, hg2, h2]; exact invB_nil hd Y hL hH a e _
  · simp [RS.put, h2]
  · simp [RS.put, h1]

/-- **Placing the second branch brick preserves the invariant.** [cite: GrimmettPercolation1999, §7.3 pp. 172–174 (B), (C)] -/
theorem tallInv_gamma2 (hY : Y.OK) {st : RS d} (hI : TallInv hd Y hL hH a e τ st)
    (hph : st.ph = Phase.segT) {rk : BrickRec d} {tl : List (BrickRec d)} (hTl : st.sT = rk :: tl) (hg1 : st.g1 ≠ none)
    (hg2 : st.g2 = none) (hn2 : n2Of hd Y a e (rk :: tl) ≤ tl.length)
    (hgood : GoodRec Y.m Y.L Y.H rk) (o : Finset (Sym2 (Site d))) :
    TallInv hd Y hL hH a e τ
      { st.put Slot.toG2 (sStep hL hH rk (latOf hd e) (-br1Sign e) (toward (nomT hd Y e ((legOf (rk :: tl) 0).b (latOf hd e))) rk.1.b), o)
        with ph := Phase.segT } := by
  obtain ⟨hTne, h1, h2⟩ := phaseOf_eq_segT (hI.ph_eq ▸ hph)
  have hLp := hY.Lp_nonneg
  have hIT := hI.invT
  rw [hTl] at hIT
  have hne : (rk :: tl) ≠ [] := List.cons_ne_nil _ _
  set y₀ := (legOf (rk :: tl) 0).b (latOf hd e) with hy₀
  set r : BrickRec d := (sStep hL hH rk (latOf hd e) (-br1Sign e) (toward (nomT hd Y e y₀) rk.1.b), o) with hr
  have hold : legOf (rk :: tl) tl.length = rk.1 := legOf_cons_length rk tl
  have hlen2 := hIT.g2_none hg2 hg1
  have hn2eq : n2Of hd Y a e (rk :: tl) = tl.length := by simp only [List.length_cons] at hlen2; omega
  obtain ⟨hax, hsx⟩ := hIT.axis_sign Y hd hL hH a e hne (k := tl.length) (by simp)
  rw [hold] at hax hsx
  have haf : latOf hd e ≠ rk.1.a := by rw [hax]; exact latOf_ne_axOf hd e
  have ha0 : ax0 hd ≠ rk.1.a := by rw [hax]; exact (axOf_ne_ax0 hd e).symm
  have hturn := isTurn_sStep hL hH hgood haf (-br1Sign e) (toward (nomT hd Y e y₀) rk.1.b)
  have hht : |r.1.b (ax0 hd) - Y.zOf e| ≤ Y.ρv := by
    rw [hr]
    have h1 := abs_sub_le_of_toward_side hL hH hgood haf (-br1Sign e) (nom := nomT hd Y e y₀) ha0 (latOf_ne_ax0 hd e).symm rfl
    have hnom : nomT hd Y e y₀ (ax0 hd) = Y.zOf e := by simp [nomT, (latOf_ne_ax0 hd e).symm]
    rw [hnom] at h1
    refine le_trans h1 (max_le ?_ hY.Lp_le_ρv)
    have := hIT.ht tl.length (by simp)
    rwa [hold] at this
  have hoth : ∀ j, j ≠ axOf hd e → j ≠ latOf hd e → j ≠ ax0 hd → |r.1.b j| ≤ Y.Lp := by
    intro j hj1 hj2 hj3
    rw [hr]
    have hja : j ≠ rk.1.a := by rw [hax]; exact hj1
    have h1 := abs_sub_le_of_toward_side hL hH hgood haf (-br1Sign e) (nom := nomT hd Y e y₀) hja hj2 rfl
    have hnom : nomT hd Y e y₀ j = 0 := by simp [nomT, hj2, hj3]
    rw [hnom, sub_zero] at h1
    refine le_trans h1 (max_le ?_ le_rfl)
    have := hIT.oth tl.length (by simp) j hj1 hj2 hj3
    rwa [hold, ← sub_zero (rk.1.b j)] at this
  obtain ⟨g₁, hg₁⟩ := Option.ne_none_iff_exists'.1 hg1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [RS.put, hTl]
    exact (phaseOf_of_T (by simp) (by simpa using h1) (by simpa using h2)).symm
  · simp only [RS.put]; exact hI.invA
  · simp only [RS.put]; exact hI.invR
  · simp only [RS.put, hTl]; rw [← hTl]; exact hI.invJ
  · simp only [RS.put, hTl, h1]
    exact
    { prev := hIT.prev
      gnil := fun h => absurd h hne
      grown := hIT.grown
      turn := hIT.turn
      fit := hIT.fit
      sched := hIT.sched
      done := fun h => absurd h (by simp)
      lat := hIT.lat
      steer := hIT.steer
      ht := hIT.ht
      oth := hIT.oth
      g1_none := hIT.g1_none
      g1_some := hIT.g1_some
      g2_none := fun h => absurd h (by simp)
      g2_g1 := fun _ => hg1
      g2_some := fun g hg => by
        simp only [Option.some.injEq] at hg
        subst hg
        refine ⟨by rw [hn2eq]; simp, ?_, hht, hoth⟩
        rw [hn2eq, hold, hr, ← hax, ← hsx]
        exact hturn }
  · simp [RS.put, h1]
  · simp only [RS.put]; exact hI.invB1
  · simp only [RS.put, h2]
    exact invB_single hd Y hL hH a e _ (by simp) hht hoth hLp
  · simp [RS.put, h2]
  · simp [RS.put, h1]

end Percolation.Literature.BGNd
