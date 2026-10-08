import Percolation.Literature.TallInvA2
import Percolation.Util.Linter

/-!
# The tall gait, V: preservation of the invariant along the riser `R`

The top steps of the riser (forced forward, pre-steered
towards the jog on the last `P'` bricks) and the turn into the jog preserve `TallInv` (Grimmett,
*Percolation*, 2nd ed. (1999), §7.3 (A), (B), (D)).

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §7.3 pp. 172–174.
-/

noncomputable section

namespace Percolation.Literature

open LatticeModels Contour
open scoped Classical

namespace BGNd

variable {d : ℕ} [NeZero d]

/-! ## Schedules -/

/-- `firstIdx p N ≤ N`. [folklore] -/
theorem firstIdx_le (p : ℕ → Prop) (N : ℕ) : firstIdx p N ≤ N := by
  unfold firstIdx
  exact Nat.find_min' _ (Or.inr rfl)

/-- Below `firstIdx`, `p` fails. [folklore] -/
theorem not_of_lt_firstIdx {p : ℕ → Prop} {N k : ℕ} (hk : k < firstIdx p N) : ¬p k := by
  unfold firstIdx at hk
  have := Nat.find_min _ hk
  tauto

/-- If `firstIdx p N < N` then `p` holds there. [folklore] -/
theorem of_firstIdx_lt {p : ℕ → Prop} {N : ℕ} (h : firstIdx p N < N) : p (firstIdx p N) := by
  unfold firstIdx at h ⊢
  have := Nat.find_spec (⟨N, Or.inr rfl⟩ : ∃ k, p k ∨ k = N)
  rcases this with hp | hk
  · exact hp
  · exact absurd hk (by omega)

variable (Y : TallLayout)

/-- One more index in the count of forced riser steps. [folklore] -/
theorem nForcedR_succ (n k : ℕ) : nForcedR Y n (k + 1) = nForcedR Y n k + (if n ≤ k + Y.Pw then 1 else 0) := by
  unfold nForcedR
  rw [List.range_succ, List.filter_append, List.length_append]
  congr 1
  by_cases h : n ≤ k + Y.Pw <;> simp [h]

variable (hd : 3 ≤ d) (hL : Y.m + 1 ≤ Y.L) (hH : 2 * Y.m + 2 ≤ Y.H) (a : Site 2) (e : MDir) (τ : TTok d)

omit [NeZero d] in
/-- In phase `R` the later segments are empty and the riser is not. [folklore] -/
theorem phaseOf_eq_segR {st : RS d} (h : phaseOf st = Phase.segR) :
    st.sR ≠ [] ∧ st.sJ = [] ∧ st.sT = [] ∧ st.sB1 = [] ∧ st.sB2 = [] := by
  unfold phaseOf at h
  by_cases h2 : st.sB2 ≠ [] <;> by_cases h1 : st.sB1 ≠ [] <;> by_cases hT : st.sT ≠ [] <;> by_cases hJ : st.sJ ≠ [] <;>
    by_cases hR : st.sR ≠ [] <;> simp_all

/-- Changing the completion flag of the `R`-invariant. [folklore] -/
theorem InvR.of_done {sA sR : List (BrickRec d)} {D D' : Prop} (h : InvR hd Y hL hH a e τ sA sR D)
    (hdone : D' → riseDir Y e τ ≠ 0 → sR ≠ [] ∧ riserLen Y e τ ((legOf sR 0).b (ax0 hd)) ≤ sR.length - 1) :
    InvR hd Y hL hH a e τ sA sR D' :=
  ⟨h.nil, h.prev, h.grown, h.turn, h.sched, hdone, h.fwd, h.lat, h.latst, h.oth⟩

/-- Axis and sign along the riser. [folklore] -/
theorem InvR.axis_sign {sA sR : List (BrickRec d)} {D : Prop} (h : InvR hd Y hL hH a e τ sA sR D) (hne : sR ≠ []) {k : ℕ}
    (hk : k < sR.length) : (legOf sR k).a = ax0 hd ∧ (legOf sR k).s = riseUnit Y e τ := by
  have h1 := (h.grown hne).axis_sign (k := k) hk
  have ht := h.turn hne
  rw [ht.axis, ht.sign] at h1
  exact h1

/-- **A top step of the riser preserves the invariant.** [cite: GrimmettPercolation1999, §7.3 pp. 172–173 (A), (D)] -/
theorem tallInv_topR (hY : Y.OK) {st : RS d} (hI : TallInv hd Y hL hH a e τ st)
    (hph : st.ph = Phase.segR) {rk : BrickRec d} {tl : List (BrickRec d)} (hRl : st.sR = rk :: tl)
    (hsched : tl.length < riserLen Y e τ ((legOf (rk :: tl) 0).b (ax0 hd))) (hgood : GoodRec Y.m Y.L Y.H rk)
    (o : Finset (Sym2 (Site d))) {sg : Fin d → Bool}
    (hsg : sg = if riserLen Y e τ ((legOf (rk :: tl) 0).b (ax0 hd)) ≤ tl.length + Y.Pw then
        force (force (toward (nomA hd Y e τ) rk.1.b) (axOf hd e) (sgOf e)) (latOf hd e) (jogDir a e)
      else force (toward (nomA hd Y e τ) rk.1.b) (axOf hd e) (sgOf e)) :
    TallInv hd Y hL hH a e τ { st.put Slot.toR (tStep hL hH rk sg, o) with ph := Phase.segR } := by
  obtain ⟨hRne, hJ, hT, h1, h2⟩ := phaseOf_eq_segR (hI.ph_eq ▸ hph)
  obtain ⟨hg1, hg2⟩ := hI.invT.gnil hT
  have hLp := hY.Lp_nonneg
  have hIR := hI.invR
  rw [hRl] at hIR
  have hne : (rk :: tl) ≠ [] := List.cons_ne_nil _ _
  have hu : riseDir Y e τ ≠ 0 := fun h => absurd (hIR.nil h) hne
  set n := riserLen Y e τ ((legOf (rk :: tl) 0).b (ax0 hd)) with hn
  set r : BrickRec d := (tStep hL hH rk sg, o) with hr
  have hold : legOf (rk :: tl) tl.length = rk.1 := legOf_cons_length rk tl
  have hnew : legOf (r :: rk :: tl) (rk :: tl).length = r.1 := legOf_cons_length r _
  have hkeep : ∀ k < (rk :: tl).length, legOf (r :: rk :: tl) k = legOf (rk :: tl) k := fun k hk => legOf_cons_of_lt r _ hk
  have e1 : legOf (r :: rk :: tl) tl.length = rk.1 := by rw [hkeep tl.length (by simp), hold]
  have e2 : legOf (r :: rk :: tl) (tl.length + 1) = r.1 := hnew
  have e0 : legOf (r :: rk :: tl) 0 = legOf (rk :: tl) 0 := hkeep 0 (by simp)
  obtain ⟨hax, hsx⟩ := hIR.axis_sign Y hd hL hH a e τ hne (k := tl.length) (by simp)
  rw [hold] at hax hsx
  have hae : axOf hd e ≠ rk.1.a := by rw [hax]; exact axOf_ne_ax0 hd e
  have haf : latOf hd e ≠ rk.1.a := by rw [hax]; exact latOf_ne_ax0 hd e
  -- requests
  have hreq_e : sg (axOf hd e) = decide (0 ≤ (sgOf e : ℤ)) := by
    rw [hsg]; split_ifs
    · rw [force_of_ne _ (latOf_ne_axOf hd e).symm, force_self]
    · rw [force_self]
  have hreq_oth : ∀ j, j ≠ axOf hd e → j ≠ latOf hd e → sg j = toward (nomA hd Y e τ) rk.1.b j := by
    intro j hj1 hj2; rw [hsg]; split_ifs
    · rw [force_of_ne _ hj2, force_of_ne _ hj1]
    · rw [force_of_ne _ hj1]
  have hs : (sgOf e : ℤ) = 1 ∨ (sgOf e : ℤ) = -1 := by rcases Int.units_eq_one_or (sgOf e) with h | h <;> simp [h]
  have hv : (jogDir a e : ℤ) = 1 ∨ (jogDir a e : ℤ) = -1 := by rcases Int.units_eq_one_or (jogDir a e) with h | h <;> simp [h]
  have hLp' : Y.Lp = (Y.L : ℤ) - Y.m - 1 := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [RS.put]
    exact (phaseOf_of_R (by simp) (by simpa using hJ) (by simpa using hT) (by simpa using h1) (by simpa using h2)).symm
  · simp only [RS.put, hJ]
    exact hI.invA.of_full hd Y hL hH a e τ fun _ => hI.invR.prev (by rw [hRl]; exact hne)
  · simp only [RS.put, hRl, hJ]
    exact
    { nil := fun h => absurd h hu
      prev := fun _ => hIR.prev hne
      grown := fun _ => grown_cons hL hH (hIR.grown hne) rfl hgood sg o
      turn := fun _ => by rw [e0]; exact hIR.turn hne
      sched := fun k hk => by
        rw [e0]
        rw [List.length_cons] at hk
        rcases Nat.lt_or_ge (k + 1) (rk :: tl).length with hlt | hge
        · exact hIR.sched k hlt
        · have : k = tl.length := by simp only [List.length_cons] at hge hk; omega
          subst this; exact hsched
      done := fun h => absurd h (by simp)
      fwd := fun k _ hk => by
        simp only [List.length_cons, Nat.add_sub_cancel] at hk
        rcases Nat.lt_or_ge (k + 1) (rk :: tl).length with hlt | hge
        · rw [hkeep k (by omega), hkeep (k + 1) hlt]
          exact hIR.fwd k (Nat.zero_le _) (by simp only [List.length_cons, Nat.add_sub_cancel] at hlt ⊢; omega)
        · have hk' : k = tl.length := by simp only [List.length_cons] at hge hk; omega
          subst hk'
          rw [e1, e2, hr]
          exact (forced_nonneg hL hH hgood hae hs hreq_e).1
      lat := fun k hk => by
        rw [e0]
        rw [List.length_cons] at hk
        rcases Nat.lt_or_ge k (rk :: tl).length with hlt | hge
        · rw [hkeep k hlt]; exact hIR.lat k hlt
        · have hk' : k = (rk :: tl).length := by omega
          rw [hk', hnew, hr]
          have h0 := hIR.lat tl.length (by simp)
          rw [hold] at h0
          rw [List.length_cons, nForcedR_succ]
          by_cases hw : n ≤ tl.length + Y.Pw
          · -- forced towards the jog
            have hreq : sg (latOf hd e) = decide (0 ≤ (jogDir a e : ℤ)) := by rw [hsg, if_pos hw, force_self]
            have h1 := forced_nonneg hL hH hgood haf hv hreq
            rw [if_pos hw]; push_cast
            have habs : |(tStep hL hH rk sg).b (latOf hd e) - rk.1.b (latOf hd e)| ≤ Y.Lp := by
              rw [hLp']
              rcases hv with h | h <;> rw [h] at h1 <;> rw [abs_le] <;> constructor <;> linarith [h1.1, h1.2]
            calc |(tStep hL hH rk sg).b (latOf hd e) - τ.pos (latOf hd e)|
                = |((tStep hL hH rk sg).b (latOf hd e) - rk.1.b (latOf hd e)) + (rk.1.b (latOf hd e) - τ.pos (latOf hd e))| := by
                  ring_nf
              _ ≤ |(tStep hL hH rk sg).b (latOf hd e) - rk.1.b (latOf hd e)| + |rk.1.b (latOf hd e) - τ.pos (latOf hd e)| :=
                  abs_add_le _ _
              _ ≤ Y.Lp + (Y.Lp + (nForcedR Y n tl.length : ℤ) * Y.Lp) := add_le_add habs h0
              _ = Y.Lp + ((nForcedR Y n tl.length : ℤ) + 1) * Y.Lp := by ring
          · have hreq : sg (latOf hd e) = toward (nomA hd Y e τ) rk.1.b (latOf hd e) := by
              rw [hsg, if_neg hw, force_of_ne _ (latOf_ne_axOf hd e)]
            have h1 := abs_sub_le_of_toward hL hH hgood haf hreq
            have hnom : nomA hd Y e τ (latOf hd e) = τ.pos (latOf hd e) := by simp [nomA]
            rw [hnom] at h1
            rw [if_neg hw]; push_cast; rw [add_zero]
            refine le_trans h1 (max_le h0 ?_)
            have : (0 : ℤ) ≤ (nForcedR Y n tl.length : ℤ) * Y.Lp := by positivity
            linarith
      latst := fun k hk0 hk => by
        rw [e0] at hk0
        simp only [List.length_cons, Nat.add_sub_cancel] at hk
        rcases Nat.lt_or_ge (k + 1) (rk :: tl).length with hlt | hge
        · rw [hkeep k (by omega), hkeep (k + 1) hlt]
          exact hIR.latst k hk0 (by simp only [List.length_cons, Nat.add_sub_cancel] at hlt ⊢; omega)
        · have hk' : k = tl.length := by simp only [List.length_cons] at hge hk; omega
          subst hk'
          rw [e1, e2, hr]
          have hw : n ≤ tl.length + Y.Pw := by omega
          have hreq : sg (latOf hd e) = decide (0 ≤ (jogDir a e : ℤ)) := by rw [hsg, if_pos hw, force_self]
          exact (forced_nonneg hL hH hgood haf hv hreq).1
      oth := fun k hk j hj1 hj2 hj3 => by
        rw [List.length_cons] at hk
        rcases Nat.lt_or_ge k (rk :: tl).length with hlt | hge
        · rw [hkeep k hlt]; exact hIR.oth k hlt j hj1 hj2 hj3
        · have hk' : k = (rk :: tl).length := by omega
          rw [hk', hnew, hr]
          have hja : j ≠ rk.1.a := by rw [hax]; exact hj3
          have h1 := abs_sub_le_of_toward hL hH hgood hja (hreq_oth j hj1 hj2)
          have hnom : nomA hd Y e τ j = 0 := by simp [nomA, hj2, hj3]
          rw [hnom, sub_zero] at h1
          refine le_trans h1 (max_le ?_ le_rfl)
          have := hIR.oth tl.length (by simp) j hj1 hj2 hj3
          rwa [hold, ← sub_zero (rk.1.b j)] at this }
  · simp only [RS.put, hRl, hJ, hT]; exact invJ_nil hd Y hL hH a e τ _ _ (by simp)
  · simp only [RS.put, hJ, hT, hg1, hg2, h1]; exact invT_nil hd Y hL hH a e _ (by simp)
  · simp [RS.put, h1]
  · simp only [RS.put, hg1, h1]; exact invB_nil hd Y hL hH a e _
  · simp only [RS.put, hg2, h2]; exact invB_nil hd Y hL hH a e _
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

/-- **The turn from the riser into the jog preserves the invariant.** [cite: GrimmettPercolation1999, §7.3 pp. 172–173 (B)] -/
theorem tallInv_turnRJ (hY : Y.OK) {st : RS d} (hI : TallInv hd Y hL hH a e τ st)
    (hph : st.ph = Phase.segR) {rk : BrickRec d} {tl : List (BrickRec d)} (hRl : st.sR = rk :: tl)
    (hdone : riserLen Y e τ ((legOf (rk :: tl) 0).b (ax0 hd)) ≤ tl.length)
    (hfit : fits Y (rk.1.b (ax0 hd)) (riseDir Y e τ) (Y.zOf e)) (hgood : GoodRec Y.m Y.L Y.H rk)
    (o : Finset (Sym2 (Site d))) :
    TallInv hd Y hL hH a e τ
      { st.put Slot.toJ (sStep hL hH rk (latOf hd e) (jogDir a e)
          (force (toward (nomT hd Y e (Y.lane (tgtCell a e) e)) rk.1.b) (axOf hd e) (sgOf e)), o) with
        ph := Phase.segJ } := by
  obtain ⟨hRne, hJ, hT, h1, h2⟩ := phaseOf_eq_segR (hI.ph_eq ▸ hph)
  obtain ⟨hg1, hg2⟩ := hI.invT.gnil hT
  have hLp := hY.Lp_nonneg
  have hIR := hI.invR
  rw [hRl] at hIR
  have hne : (rk :: tl) ≠ [] := List.cons_ne_nil _ _
  have hu : riseDir Y e τ ≠ 0 := fun h => absurd (hIR.nil h) hne
  set y := Y.lane (tgtCell a e) e with hy
  set sg := force (toward (nomT hd Y e y) rk.1.b) (axOf hd e) (sgOf e) with hsg
  set r : BrickRec d := (sStep hL hH rk (latOf hd e) (jogDir a e) sg, o) with hr
  have hold : legOf (rk :: tl) tl.length = rk.1 := legOf_cons_length rk tl
  have hleg0 : legOf [r] 0 = r.1 := legOf_cons_length r []
  obtain ⟨hax, hsx⟩ := hIR.axis_sign Y hd hL hH a e τ hne (k := tl.length) (by simp)
  rw [hold] at hax hsx
  have hae : axOf hd e ≠ rk.1.a := by rw [hax]; exact axOf_ne_ax0 hd e
  have haf : latOf hd e ≠ rk.1.a := by rw [hax]; exact latOf_ne_ax0 hd e
  have hEL : entryLast Y e τ st.sA (rk :: tl) = rk.1 := by
    unfold entryLast; rw [if_neg hu, List.length_cons, Nat.add_sub_cancel, hold]
  have hs : (sgOf e : ℤ) = 1 ∨ (sgOf e : ℤ) = -1 := by rcases Int.units_eq_one_or (sgOf e) with h | h <;> simp [h]
  have hturn := isTurn_sStep hL hH hgood haf (jogDir a e) sg
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [RS.put]
    exact (phaseOf_of_J (by simp) (by simpa using hT) (by simpa using h1) (by simpa using h2)).symm
  · simp only [RS.put, hRl]
    exact hI.invA.of_full hd Y hL hH a e τ fun _ => hIR.prev hne
  · simp only [RS.put, hRl]
    exact hIR.of_done Y hd hL hH a e τ fun _ _ => ⟨hne, by simpa using hdone⟩
  · simp only [RS.put, hRl, hJ, hT]
    exact
    { prevA := fun _ => hIR.prev hne
      prevR := fun _ _ => ⟨hne, by simpa using hdone⟩
      grown := fun _ => grown_singleton hL hH r
      turn := fun _ => by
        rw [if_neg hu, if_neg hu, hEL, hleg0, hr, ← hax, ← hsx]
        exact hturn
      sched := fun k hk => absurd hk (by simp)
      done := fun h => absurd h (by simp)
      fwd := fun k _ hk => absurd hk (by simp)
      fwd0 := fun _ => by
        rw [hEL, hleg0, hr]
        have hreq : sg (axOf hd e) = decide (0 ≤ (sgOf e : ℤ)) := by rw [hsg, force_self]
        exact (forced_nonneg_side hL hH hgood haf (jogDir a e) hae (latOf_ne_axOf hd e).symm hs hreq).1
      ht := fun k hk => by
        have : k = 0 := by simpa using hk
        subst this
        rw [hleg0, hr]
        -- the old axis: the new base lies in the side-exit window, which fits the band
        obtain ⟨hlo, hhi⟩ := hturn.longit
        rw [hax, hsx, riseUnit_val Y e τ hu] at hlo hhi
        obtain ⟨f1, f2, f3, f4⟩ := hfit
        have hℓ : (Y.ell : ℤ) ≤ Y.ρv := by unfold TallLayout.ρv; linarith
        rcases (riseDir_cases Y e τ).resolve_left hu with h | h <;> rw [h] at hlo hhi f1 f2 f3 f4 <;>
          (rw [abs_le]; constructor <;> nlinarith)
      oth := fun k hk j hj1 hj2 hj3 => by
        have : k = 0 := by simpa using hk
        subst this
        rw [hleg0, hr]
        have hja : j ≠ rk.1.a := by rw [hax]; exact hj3
        have hreq : sg j = toward (nomT hd Y e y) rk.1.b j := by rw [hsg]; exact force_of_ne _ hj1 _
        have h1 := abs_sub_le_of_toward_side hL hH hgood haf (jogDir a e) (nom := nomT hd Y e y) hja hj2 hreq
        have hnom : nomT hd Y e y j = 0 := by simp [nomT, hj2, hj3]
        rw [hnom, sub_zero] at h1
        refine le_trans h1 (max_le ?_ le_rfl)
        have := hIR.oth tl.length (by simp) j hj1 hj2 hj3
        rwa [hold, ← sub_zero (rk.1.b j)] at this }
  · simp only [RS.put, hJ, hT, hg1, hg2, h1]; exact invT_nil hd Y hL hH a e _ (by simp)
  · simp [RS.put, h1]
  · simp only [RS.put, hg1, h1]; exact invB_nil hd Y hL hH a e _
  · simp only [RS.put, hg2, h2]; exact invB_nil hd Y hL hH a e _
  · simp [RS.put, h2]
  · simp [RS.put, h1]

end Percolation.Literature.BGNd
