import Percolation.Literature.TallInvR
import Percolation.Util.Linter

/-!
# The tall gait, VI: preservation of the invariant along the jog `J`

The top steps of the jog (forced forward along `e`) and
the turn forward into the trunk preserve `TallInv` (Grimmett, *Percolation*, 2nd ed. (1999), §7.3
(A), (B), (D)).

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
/-- In phase `J` the later segments are empty and the jog is not. [folklore] -/
theorem phaseOf_eq_segJ {st : RS d} (h : phaseOf st = Phase.segJ) : st.sJ ≠ [] ∧ st.sT = [] ∧ st.sB1 = [] ∧ st.sB2 = [] := by
  unfold phaseOf at h
  by_cases h2 : st.sB2 ≠ [] <;> by_cases h1 : st.sB1 ≠ [] <;> by_cases hT : st.sT ≠ [] <;> by_cases hJ : st.sJ ≠ [] <;>
    by_cases hR : st.sR ≠ [] <;> simp_all

omit [NeZero d] in
/-- The phase of a state in the trunk. [folklore] -/
theorem phaseOf_of_T {st : RS d} (hT : st.sT ≠ []) (h1 : st.sB1 = []) (h2 : st.sB2 = []) : phaseOf st = Phase.segT := by
  simp [phaseOf, hT, h1, h2]

/-- Changing the completion flag of the `J`-invariant. [folklore] -/
theorem InvJ.of_done {sA sR sJ : List (BrickRec d)} {D D' : Prop} (h : InvJ hd Y hL hH a e τ sA sR sJ D)
    (hdone : D' → sJ ≠ [] ∧ jogLen Y a e ((legOf sJ 0).b (latOf hd e)) ≤ sJ.length - 1) : InvJ hd Y hL hH a e τ sA sR sJ D' :=
  ⟨h.prevA, h.prevR, h.grown, h.turn, h.sched, hdone, h.fwd, h.fwd0, h.ht, h.oth⟩

/-- Axis and sign along the jog. [folklore] -/
theorem InvJ.axis_sign {sA sR sJ : List (BrickRec d)} {D : Prop} (h : InvJ hd Y hL hH a e τ sA sR sJ D) (hne : sJ ≠ []) {k : ℕ}
    (hk : k < sJ.length) : (legOf sJ k).a = latOf hd e ∧ (legOf sJ k).s = jogDir a e := by
  have h1 := (h.grown hne).axis_sign (k := k) hk
  have ht := h.turn hne
  rw [ht.axis, ht.sign] at h1
  exact h1

/-- **A top step of the jog preserves the invariant.** [cite: GrimmettPercolation1999, §7.3 pp. 172–173 (A), (D)] -/
theorem tallInv_topJ (hY : Y.OK) {st : RS d} (hI : TallInv hd Y hL hH a e τ st)
    (hph : st.ph = Phase.segJ) {rk : BrickRec d} {tl : List (BrickRec d)} (hJl : st.sJ = rk :: tl)
    (hsched : tl.length < jogLen Y a e ((legOf (rk :: tl) 0).b (latOf hd e))) (hgood : GoodRec Y.m Y.L Y.H rk)
    (o : Finset (Sym2 (Site d))) :
    TallInv hd Y hL hH a e τ
      { st.put Slot.toJ (tStep hL hH rk (force (toward (nomT hd Y e (Y.lane (tgtCell a e) e)) rk.1.b) (axOf hd e) (sgOf e)), o)
        with ph := Phase.segJ } := by
  obtain ⟨hJne, hT, h1, h2⟩ := phaseOf_eq_segJ (hI.ph_eq ▸ hph)
  obtain ⟨hg1, hg2⟩ := hI.invT.gnil hT
  have hLp := hY.Lp_nonneg
  have hIJ := hI.invJ
  rw [hJl] at hIJ
  have hne : (rk :: tl) ≠ [] := List.cons_ne_nil _ _
  set y := Y.lane (tgtCell a e) e with hy
  set sg := force (toward (nomT hd Y e y) rk.1.b) (axOf hd e) (sgOf e) with hsg
  set r : BrickRec d := (tStep hL hH rk sg, o) with hr
  have hold : legOf (rk :: tl) tl.length = rk.1 := legOf_cons_length rk tl
  have hnew : legOf (r :: rk :: tl) (rk :: tl).length = r.1 := legOf_cons_length r _
  have hkeep : ∀ k < (rk :: tl).length, legOf (r :: rk :: tl) k = legOf (rk :: tl) k := fun k hk => legOf_cons_of_lt r _ hk
  have e1 : legOf (r :: rk :: tl) tl.length = rk.1 := by rw [hkeep tl.length (by simp), hold]
  have e2 : legOf (r :: rk :: tl) (tl.length + 1) = r.1 := hnew
  have e0 : legOf (r :: rk :: tl) 0 = legOf (rk :: tl) 0 := hkeep 0 (by simp)
  obtain ⟨hax, hsx⟩ := hIJ.axis_sign Y hd hL hH a e τ hne (k := tl.length) (by simp)
  rw [hold] at hax hsx
  have hae : axOf hd e ≠ rk.1.a := by rw [hax]; exact (latOf_ne_axOf hd e).symm
  have ha0 : ax0 hd ≠ rk.1.a := by rw [hax]; exact (latOf_ne_ax0 hd e).symm
  have hs : (sgOf e : ℤ) = 1 ∨ (sgOf e : ℤ) = -1 := by rcases Int.units_eq_one_or (sgOf e) with h | h <;> simp [h]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [RS.put]
    exact (phaseOf_of_J (by simp) (by simpa using hT) (by simpa using h1) (by simpa using h2)).symm
  · simp only [RS.put]
    exact hI.invA.of_full hd Y hL hH a e τ fun _ => hIJ.prevA hne
  · simp only [RS.put]
    exact hI.invR.of_done Y hd hL hH a e τ fun _ hu => hIJ.prevR hne hu
  · simp only [RS.put, hJl, hT]
    exact
    { prevA := fun _ => hIJ.prevA hne
      prevR := fun _ hu => hIJ.prevR hne hu
      grown := fun _ => grown_cons hL hH (hIJ.grown hne) rfl hgood sg o
      turn := fun _ => by rw [e0]; exact hIJ.turn hne
      sched := fun k hk => by
        rw [e0]
        rw [List.length_cons] at hk
        rcases Nat.lt_or_ge (k + 1) (rk :: tl).length with hlt | hge
        · exact hIJ.sched k hlt
        · have : k = tl.length := by simp only [List.length_cons] at hge hk; omega
          subst this; exact hsched
      done := fun h => absurd h (by simp)
      fwd := fun k _ hk => by
        simp only [List.length_cons, Nat.add_sub_cancel] at hk
        rcases Nat.lt_or_ge (k + 1) (rk :: tl).length with hlt | hge
        · rw [hkeep k (by omega), hkeep (k + 1) hlt]
          exact hIJ.fwd k (Nat.zero_le _) (by simp only [List.length_cons, Nat.add_sub_cancel] at hlt ⊢; omega)
        · have hk' : k = tl.length := by simp only [List.length_cons] at hge hk; omega
          subst hk'
          rw [e1, e2, hr]
          have hreq : sg (axOf hd e) = decide (0 ≤ (sgOf e : ℤ)) := by rw [hsg, force_self]
          exact (forced_nonneg hL hH hgood hae hs hreq).1
      fwd0 := fun _ => by
        rw [e0]
        have := hIJ.fwd0 hne
        exact this
      ht := fun k hk => by
        rw [List.length_cons] at hk
        rcases Nat.lt_or_ge k (rk :: tl).length with hlt | hge
        · rw [hkeep k hlt]; exact hIJ.ht k hlt
        · have hk' : k = (rk :: tl).length := by omega
          rw [hk', hnew, hr]
          have hreq : sg (ax0 hd) = toward (nomT hd Y e y) rk.1.b (ax0 hd) := by rw [hsg]; exact force_of_ne _ (axOf_ne_ax0 hd e).symm _
          have h1 := abs_sub_le_of_toward hL hH hgood ha0 hreq
          have hnom : nomT hd Y e y (ax0 hd) = Y.zOf e := by simp [nomT, (latOf_ne_ax0 hd e).symm]
          rw [hnom] at h1
          refine le_trans h1 (max_le ?_ hY.Lp_le_ρv)
          have := hIJ.ht tl.length (by simp)
          rwa [hold] at this
      oth := fun k hk j hj1 hj2 hj3 => by
        rw [List.length_cons] at hk
        rcases Nat.lt_or_ge k (rk :: tl).length with hlt | hge
        · rw [hkeep k hlt]; exact hIJ.oth k hlt j hj1 hj2 hj3
        · have hk' : k = (rk :: tl).length := by omega
          rw [hk', hnew, hr]
          have hja : j ≠ rk.1.a := by rw [hax]; exact hj2
          have hreq : sg j = toward (nomT hd Y e y) rk.1.b j := by rw [hsg]; exact force_of_ne _ hj1 _
          have h1 := abs_sub_le_of_toward hL hH hgood hja hreq
          have hnom : nomT hd Y e y j = 0 := by simp [nomT, hj2, hj3]
          rw [hnom, sub_zero] at h1
          refine le_trans h1 (max_le ?_ le_rfl)
          have := hIJ.oth tl.length (by simp) j hj1 hj2 hj3
          rwa [hold, ← sub_zero (rk.1.b j)] at this }
  · simp only [RS.put, hJl, hT, hg1, hg2, h1]; exact invT_nil hd Y hL hH a e _ (by simp)
  · simp [RS.put, h1]
  · simp only [RS.put, hg1, h1]; exact invB_nil hd Y hL hH a e _
  · simp only [RS.put, hg2, h2]; exact invB_nil hd Y hL hH a e _
  · simp [RS.put, h2]
  · simp [RS.put, h1]

/-- `nForced` at `0`. [folklore] -/
@[simp] theorem nForced_zero (n₁ n₂ : ℕ) : nForced Y e n₁ n₂ 0 = 0 := by simp [nForced]

/-- **The turn from the jog into the trunk preserves the invariant.** [cite: GrimmettPercolation1999, §7.3 pp. 172–173 (B)] -/
theorem tallInv_turnJT (hY : Y.OK) {st : RS d} (hI : TallInv hd Y hL hH a e τ st)
    (hph : st.ph = Phase.segJ) {rk : BrickRec d} {tl : List (BrickRec d)} (hJl : st.sJ = rk :: tl)
    (hdone : jogLen Y a e ((legOf (rk :: tl) 0).b (latOf hd e)) ≤ tl.length)
    (hfit : fits Y (rk.1.b (latOf hd e)) (jogDir a e) (Y.lane (tgtCell a e) e)) (hgood : GoodRec Y.m Y.L Y.H rk)
    (o : Finset (Sym2 (Site d))) :
    TallInv hd Y hL hH a e τ
      { st.put Slot.toT (sStep hL hH rk (axOf hd e) (sgOf e) (toward (nomT hd Y e (Y.lane (tgtCell a e) e)) rk.1.b), o)
        with ph := Phase.segT } := by
  obtain ⟨hJne, hT, h1, h2⟩ := phaseOf_eq_segJ (hI.ph_eq ▸ hph)
  obtain ⟨hg1, hg2⟩ := hI.invT.gnil hT
  have hLp := hY.Lp_nonneg
  have hIJ := hI.invJ
  rw [hJl] at hIJ
  have hne : (rk :: tl) ≠ [] := List.cons_ne_nil _ _
  set y := Y.lane (tgtCell a e) e with hy
  set sg := toward (nomT hd Y e y) rk.1.b with hsg
  set r : BrickRec d := (sStep hL hH rk (axOf hd e) (sgOf e) sg, o) with hr
  have hold : legOf (rk :: tl) tl.length = rk.1 := legOf_cons_length rk tl
  have hleg0 : legOf [r] 0 = r.1 := legOf_cons_length r []
  obtain ⟨hax, hsx⟩ := hIJ.axis_sign Y hd hL hH a e τ hne (k := tl.length) (by simp)
  rw [hold] at hax hsx
  have hae : axOf hd e ≠ rk.1.a := by rw [hax]; exact (latOf_ne_axOf hd e).symm
  have ha0 : ax0 hd ≠ rk.1.a := by rw [hax]; exact (latOf_ne_ax0 hd e).symm
  have hturn := isTurn_sStep hL hH hgood hae (sgOf e) sg
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [RS.put]
    exact (phaseOf_of_T (by simp) (by simpa using h1) (by simpa using h2)).symm
  · simp only [RS.put]
    exact hI.invA.of_full hd Y hL hH a e τ fun _ => hIJ.prevA hne
  · simp only [RS.put]
    exact hI.invR.of_done Y hd hL hH a e τ fun _ hu => hIJ.prevR hne hu
  · simp only [RS.put, hJl]
    exact hIJ.of_done Y hd hL hH a e τ fun _ => ⟨hne, by simpa using hdone⟩
  · simp only [RS.put, hJl, hT, hg1, hg2, h1]
    exact
    { prev := fun _ => ⟨hne, by simpa using hdone⟩
      gnil := fun h => absurd h (by simp)
      grown := fun _ => grown_singleton hL hH r
      turn := fun _ => by
        rw [List.length_cons, Nat.add_sub_cancel, hold, hleg0, hr, ← hax, ← hsx]
        exact hturn
      fit := fun _ => by
        rw [hleg0, hr]
        obtain ⟨hlo, hhi⟩ := hturn.longit
        rw [hax, hsx] at hlo hhi
        obtain ⟨f1, f2, f3, f4⟩ := hfit
        rcases Int.units_eq_one_or (jogDir a e) with h | h <;> simp only [h, Units.val_one, Units.val_neg, one_mul, neg_mul] at hlo hhi f1 f2 f3 f4 <;>
          (rw [abs_le]; constructor <;> nlinarith)
      sched := fun k hk => absurd hk (by simp)
      done := fun h => absurd h (by simp)
      lat := fun k hk => by
        have : k = 0 := by simpa using hk
        subst this
        rw [sub_self, abs_zero, nForced_zero, Nat.cast_zero, zero_mul, add_zero]; exact hLp
      steer := fun k hk => absurd hk (by simp)
      ht := fun k hk => by
        have : k = 0 := by simpa using hk
        subst this
        rw [hleg0, hr]
        have h1 := abs_sub_le_of_toward_side hL hH hgood hae (sgOf e) (nom := nomT hd Y e y) ha0 (axOf_ne_ax0 hd e).symm rfl
        have hnom : nomT hd Y e y (ax0 hd) = Y.zOf e := by simp [nomT, (latOf_ne_ax0 hd e).symm]
        rw [hnom] at h1
        refine le_trans h1 (max_le ?_ hY.Lp_le_ρv)
        have := hIJ.ht tl.length (by simp)
        rwa [hold] at this
      oth := fun k hk j hj1 hj2 hj3 => by
        have : k = 0 := by simpa using hk
        subst this
        rw [hleg0, hr]
        have hja : j ≠ rk.1.a := by rw [hax]; exact hj2
        have h1 := abs_sub_le_of_toward_side hL hH hgood hae (sgOf e) (nom := nomT hd Y e y) hja hj1 rfl
        have hnom : nomT hd Y e y j = 0 := by simp [nomT, hj2, hj3]
        rw [hnom, sub_zero] at h1
        refine le_trans h1 (max_le ?_ le_rfl)
        have := hIJ.oth tl.length (by simp) j hj1 hj2 hj3
        rwa [hold, ← sub_zero (rk.1.b j)] at this
      g1_none := fun _ => by simp
      g1_some := fun g hg => absurd hg (by simp)
      g2_none := fun _ h => absurd rfl h
      g2_g1 := fun h => absurd rfl h
      g2_some := fun g hg => absurd hg (by simp) }
  · simp [RS.put, h1]
  · simp only [RS.put, hg1, h1]; exact invB_nil hd Y hL hH a e _
  · simp only [RS.put, hg2, h2]; exact invB_nil hd Y hL hH a e _
  · simp [RS.put, h2]
  · simp [RS.put, h1]

end BGNd

end Percolation.Literature

end
