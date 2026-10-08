import Percolation.Literature.TallInvT
import Percolation.Util.Linter

/-!
# The tall gait, VIII: preservation of the invariant along the branches `B1, B2`

The top steps of the two branch legs (from the branch
bricks to the lateral faces) preserve `TallInv` (Grimmett, *Percolation*, 2nd ed. (1999), §7.3 (A),
(D)).

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
/-- In phase `B1`. [folklore] -/
theorem phaseOf_eq_segB1 {st : RS d} (h : phaseOf st = Phase.segB1) : st.sB1 ≠ [] ∧ st.sB2 = [] := by
  unfold phaseOf at h
  by_cases h2 : st.sB2 ≠ [] <;> by_cases h1 : st.sB1 ≠ [] <;> by_cases hT : st.sT ≠ [] <;> by_cases hJ : st.sJ ≠ [] <;>
    by_cases hR : st.sR ≠ [] <;> simp_all

omit [NeZero d] in
/-- In phase `B2`. [folklore] -/
theorem phaseOf_eq_segB2 {st : RS d} (h : phaseOf st = Phase.segB2) : st.sB2 ≠ [] := by
  unfold phaseOf at h
  by_cases h2 : st.sB2 ≠ [] <;> by_cases h1 : st.sB1 ≠ [] <;> by_cases hT : st.sT ≠ [] <;> by_cases hJ : st.sJ ≠ [] <;>
    by_cases hR : st.sR ≠ [] <;> simp_all

omit [NeZero d] in
/-- The phase of a state in the first branch. [folklore] -/
theorem phaseOf_of_B1 {st : RS d} (h1 : st.sB1 ≠ []) (h2 : st.sB2 = []) : phaseOf st = Phase.segB1 := by
  simp [phaseOf, h1, h2]

omit [NeZero d] in
/-- The phase of a state in the second branch. [folklore] -/
theorem phaseOf_of_B2 {st : RS d} (h2 : st.sB2 ≠ []) : phaseOf st = Phase.segB2 := by
  simp [phaseOf, h2]

/-- Changing the completion flag of the `T`-invariant. [folklore] -/
theorem InvT.of_done {sJ sT : List (BrickRec d)} {g1 g2 : Option (BrickRec d)} {D D' : Prop} (h : InvT hd Y hL hH a e sJ sT g1 g2 D)
    (hdone : D' → sT ≠ [] ∧ legLen Y a e e ((legOf sT 0).b (axOf hd e)) ≤ sT.length - 1 ∧ g1 ≠ none) :
    InvT hd Y hL hH a e sJ sT g1 g2 D' :=
  ⟨h.prev, h.gnil, h.grown, h.turn, h.fit, h.sched, hdone, h.lat, h.steer, h.ht, h.oth, h.g1_none, h.g1_some, h.g2_none, h.g2_g1,
    h.g2_some⟩

/-- Changing the completion flag of a branch invariant. [folklore] -/
theorem InvB.of_done {w : ℤˣ} {g : Option (BrickRec d)} {sB : List (BrickRec d)} {D D' : Prop} (h : InvB hd Y hL hH a e w g sB D)
    (hdone : ∀ r, g = some r → D' → sB ≠ [] ∧ legLen Y a e (latDir e (decide ((w : ℤ) = 1))) (r.1.b (latOf hd e)) ≤ sB.length) :
    InvB hd Y hL hH a e w g sB D' :=
  ⟨h.prev, h.grown, h.sched, hdone, h.lng, h.ht, h.oth⟩

/-- The oldest placement of `l ++ [g]` is `g`. [folklore] -/
theorem legOf_append_singleton_zero (l : List (BrickRec d)) (g : BrickRec d) : legOf (l ++ [g]) 0 = g.1 := by
  induction l with
  | nil => exact legOf_cons_length g []
  | cons x t ih => rw [List.cons_append, legOf_cons_of_lt _ _ (by simp)]; exact ih

/-- **Growing a branch leg by one top step**, the common core of the four branch placements: from the
invariant of `sB ++ [g]` to that of `(r :: sB) ++ [g]`. [cite: GrimmettPercolation1999, §7.3 pp. 172–174 (A), (D)] -/
theorem InvB.grow (hY : Y.OK) {w : ℤˣ} {g : BrickRec d} {sB : List (BrickRec d)} {D : Prop}
    (h : InvB hd Y hL hH a e w (some g) sB D) (hgax : g.1.a = latOf hd e)
    {rk : BrickRec d} (hrk : (sB ++ [g]).head? = some rk) (hgood : GoodRec Y.m Y.L Y.H rk)
    (hroom : sB.length < legLen Y a e (latDir e (decide ((w : ℤ) = 1))) (g.1.b (latOf hd e))) (o : Finset (Sym2 (Site d)))
    {D' : Prop} (hD' : ¬D') :
    InvB hd Y hL hH a e w (some g)
      ((tStep hL hH rk (toward (Function.update (nomT hd Y e (Y.lane (tgtCell a e) e)) (axOf hd e) (g.1.b (axOf hd e))) rk.1.b), o) :: sB)
      D' := by
  have hLp := hY.Lp_nonneg
  set y := Y.lane (tgtCell a e) e with hy
  set nom := Function.update (nomT hd Y e y) (axOf hd e) (g.1.b (axOf hd e)) with hnom
  set r : BrickRec d := (tStep hL hH rk (toward nom rk.1.b), o) with hr
  -- the grown list `sB ++ [g]` (oldest: `g`)
  have hG : Grown hL hH (sB ++ [g]) := by
    cases hsB : sB with
    | nil => exact grown_singleton hL hH g
    | cons x t => rw [← hsB]; exact h.grown g rfl (by rw [hsB]; exact List.cons_ne_nil _ _)
  have hlenL : (sB ++ [g]).length = sB.length + 1 := by simp
  have hnewest : legOf (sB ++ [g]) sB.length = rk.1 := by
    cases hsB : sB with
    | nil =>
      simp only [hsB, List.nil_append, List.head?_cons, Option.some.injEq] at hrk
      rw [List.nil_append, ← hrk]; exact legOf_cons_length g []
    | cons x t =>
      simp only [hsB, List.cons_append, List.head?_cons, Option.some.injEq] at hrk
      subst hrk
      rw [List.cons_append, List.length_cons]
      have := legOf_cons_length x (t ++ [g])
      rwa [List.length_append, List.length_singleton] at this
  have hax : rk.1.a = latOf hd e := by
    have h1 := (hG.axis_sign (k := sB.length) (by rw [hlenL]; omega)).1
    rw [hnewest] at h1
    rw [legOf_append_singleton_zero] at h1; rw [h1]; exact hgax
  have hae : axOf hd e ≠ rk.1.a := by rw [hax]; exact (latOf_ne_axOf hd e).symm
  have ha0 : ax0 hd ≠ rk.1.a := by rw [hax]; exact (latOf_ne_ax0 hd e).symm
  have hkeep : ∀ k < (sB ++ [g]).length, legOf (r :: (sB ++ [g])) k = legOf (sB ++ [g]) k := fun k hk => legOf_cons_of_lt r _ hk
  have hnew : legOf (r :: (sB ++ [g])) (sB ++ [g]).length = r.1 := legOf_cons_length r _
  have hcons : (r :: sB) ++ [g] = r :: (sB ++ [g]) := rfl
  -- bounds of the old newest brick
  have hold_lng := h.lng g rfl sB.length le_rfl
  have hold_ht := h.ht g rfl sB.length le_rfl
  rw [hnewest] at hold_lng hold_ht
  refine
  { prev := fun _ => by simp
    grown := fun r' hr' _ => ?_
    sched := fun r' hr' k hk => ?_
    done := fun r' _ hd' => absurd hd' hD'
    lng := fun r' hr' k hk => ?_
    ht := fun r' hr' k hk => ?_
    oth := fun r' hr' k hk j hj1 hj2 hj3 => ?_ }
  · simp only [Option.some.injEq] at hr'; subst hr'
    rw [hcons]; exact grown_cons hL hH hG hrk hgood _ o
  · simp only [Option.some.injEq] at hr'; subst hr'
    rw [List.length_cons] at hk
    rcases Nat.lt_or_ge k sB.length with hlt | hge
    · exact h.sched g rfl k hlt
    · have : k = sB.length := by omega
      subst this; exact hroom
  · simp only [Option.some.injEq] at hr'; subst hr'
    rw [hcons]
    rw [List.length_cons] at hk
    rcases Nat.lt_or_ge k (sB.length + 1) with hlt | hge
    · rw [hkeep k (by rw [hlenL]; exact hlt)]; exact h.lng g rfl k (by omega)
    · have hk' : k = (sB ++ [g]).length := by rw [hlenL]; omega
      rw [hk', hnew, hr]
      have hreq : toward nom rk.1.b (axOf hd e) = toward nom rk.1.b (axOf hd e) := rfl
      have h1 := abs_sub_le_of_toward hL hH hgood hae hreq
      have hn : nom (axOf hd e) = g.1.b (axOf hd e) := by rw [hnom, Function.update_self]
      rw [hn] at h1
      exact le_trans h1 (max_le hold_lng le_rfl)
  · simp only [Option.some.injEq] at hr'; subst hr'
    rw [hcons]
    rw [List.length_cons] at hk
    rcases Nat.lt_or_ge k (sB.length + 1) with hlt | hge
    · rw [hkeep k (by rw [hlenL]; exact hlt)]; exact h.ht g rfl k (by omega)
    · have hk' : k = (sB ++ [g]).length := by rw [hlenL]; omega
      rw [hk', hnew, hr]
      have h1 := abs_sub_le_of_toward hL hH hgood ha0 (rfl : toward nom rk.1.b (ax0 hd) = _)
      have hn : nom (ax0 hd) = Y.zOf e := by
        rw [hnom, Function.update_of_ne (axOf_ne_ax0 hd e).symm]; simp [nomT, (latOf_ne_ax0 hd e).symm]
      rw [hn] at h1
      exact le_trans h1 (max_le hold_ht hY.Lp_le_ρv)
  · simp only [Option.some.injEq] at hr'; subst hr'
    rw [hcons]
    rw [List.length_cons] at hk
    rcases Nat.lt_or_ge k (sB.length + 1) with hlt | hge
    · rw [hkeep k (by rw [hlenL]; exact hlt)]; exact h.oth g rfl k (by omega) j hj1 hj2 hj3
    · have hk' : k = (sB ++ [g]).length := by rw [hlenL]; omega
      rw [hk', hnew, hr]
      have hja : j ≠ rk.1.a := by rw [hax]; exact hj2
      have h1 := abs_sub_le_of_toward hL hH hgood hja (rfl : toward nom rk.1.b j = _)
      have hn : nom j = 0 := by
        rw [hnom, Function.update_of_ne hj1]; simp [nomT, hj2, hj3]
      rw [hn, sub_zero] at h1
      refine le_trans h1 (max_le ?_ le_rfl)
      have := h.oth g rfl sB.length le_rfl j hj1 hj2 hj3
      rwa [hnewest, ← sub_zero (rk.1.b j)] at this

/-- **Starting the first branch preserves the invariant.** [cite: GrimmettPercolation1999, §7.3 pp. 172–174] -/
theorem tallInv_startB1 (hY : Y.OK) {st : RS d} (hI : TallInv hd Y hL hH a e τ st)
    (hph : st.ph = Phase.segT) {rk : BrickRec d} {tl : List (BrickRec d)} (hTl : st.sT = rk :: tl)
    (hend : legLen Y a e e ((legOf (rk :: tl) 0).b (axOf hd e)) ≤ tl.length) {g : BrickRec d} (hg1 : st.g1 = some g)
    (hg2 : st.g2 ≠ none)
    (hroom : 0 < legLen Y a e (latDir e (decide ((br1Sign e : ℤ) = 1))) (g.1.b (latOf hd e))) (hgood : GoodRec Y.m Y.L Y.H g)
    (o : Finset (Sym2 (Site d))) :
    TallInv hd Y hL hH a e τ
      { st.put Slot.toB1 (tStep hL hH g (toward (Function.update (nomT hd Y e (Y.lane (tgtCell a e) e)) (axOf hd e) (g.1.b (axOf hd e))) g.1.b), o)
        with ph := Phase.segB1 } := by
  obtain ⟨hTne, h1, h2⟩ := phaseOf_eq_segT (hI.ph_eq ▸ hph)
  have hIT := hI.invT
  rw [hTl] at hIT
  have hne : (rk :: tl) ≠ [] := List.cons_ne_nil _ _
  obtain ⟨-, hgturn, -, -⟩ := hIT.g1_some g hg1
  have hB1 := hI.invB1
  rw [hg1, h1] at hB1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [RS.put]; exact (phaseOf_of_B1 (by simp) (by simpa using h2)).symm
  · simp only [RS.put]; exact hI.invA
  · simp only [RS.put]; exact hI.invR
  · simp only [RS.put]; exact hI.invJ
  · simp only [RS.put, hTl]
    exact hIT.of_done Y hd hL hH a e fun _ => ⟨hne, by simpa using hend, by simp [hg1]⟩
  · simp [RS.put, hTl]
  · simp only [RS.put, hg1, h1]
    exact hB1.grow Y hd hL hH a e hY hgturn.axis (rk := g) rfl hgood (by simpa using hroom) o (by simp [h2])
  · simp only [RS.put]; exact hI.invB2
  · simp [RS.put, h2]
  · simp only [RS.put]; intro; exact hg2

/-- **A top step of the first branch preserves the invariant.** [cite: GrimmettPercolation1999, §7.3 pp. 172–174] -/
theorem tallInv_topB1 (hY : Y.OK) {st : RS d} (hI : TallInv hd Y hL hH a e τ st)
    (hph : st.ph = Phase.segB1) {rk : BrickRec d} {tl : List (BrickRec d)} (hBl : st.sB1 = rk :: tl) {g : BrickRec d}
    (hg1 : st.g1 = some g) (hroom : (rk :: tl).length < legLen Y a e (latDir e (decide ((br1Sign e : ℤ) = 1))) (g.1.b (latOf hd e)))
    (hgood : GoodRec Y.m Y.L Y.H rk) (o : Finset (Sym2 (Site d))) :
    TallInv hd Y hL hH a e τ
      { st.put Slot.toB1 (tStep hL hH rk (toward (Function.update (nomT hd Y e (Y.lane (tgtCell a e) e)) (axOf hd e) (g.1.b (axOf hd e))) rk.1.b), o)
        with ph := Phase.segB1 } := by
  obtain ⟨hB1ne, h2⟩ := phaseOf_eq_segB1 (hI.ph_eq ▸ hph)
  obtain ⟨-, hgturn, -, -⟩ := hI.invT.g1_some g hg1
  have hB1 := hI.invB1
  rw [hg1, hBl] at hB1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [RS.put]; exact (phaseOf_of_B1 (by simp) (by simpa using h2)).symm
  · simp only [RS.put]; exact hI.invA
  · simp only [RS.put]; exact hI.invR
  · simp only [RS.put]; exact hI.invJ
  · simp only [RS.put]
    exact hI.invT.of_done Y hd hL hH a e fun _ => hI.invT.done (by rw [hBl]; exact List.cons_ne_nil _ _)
  · simp only [RS.put]; intro; exact hI.trunk_done_B1 (by rw [hBl]; exact List.cons_ne_nil _ _)
  · simp only [RS.put, hg1, hBl]
    exact hB1.grow Y hd hL hH a e hY hgturn.axis (rk := rk) rfl hgood hroom o (by simp [h2])
  · simp only [RS.put]; exact hI.invB2
  · simp [RS.put, h2]
  · simp only [RS.put]; intro; exact hI.B1_g2 (by rw [hBl]; exact List.cons_ne_nil _ _)

omit [NeZero d] in
/-- The second branch direction, as computed by the plan and as recorded by the invariant. [folklore] -/
theorem decide_neg_br1Sign : decide ((br1Sign e : ℤ) ≠ 1) = decide (((-br1Sign e : ℤˣ) : ℤ) = 1) := by
  rcases Int.units_eq_one_or (br1Sign e) with h | h <;> simp [h]

/-- **Starting the second branch preserves the invariant.** [cite: GrimmettPercolation1999, §7.3 pp. 172–174] -/
theorem tallInv_startB2 (hY : Y.OK) {st : RS d} (hI : TallInv hd Y hL hH a e τ st)
    (hph : st.ph = Phase.segB1) {rk : BrickRec d} {tl : List (BrickRec d)} (hBl : st.sB1 = rk :: tl) {g g' : BrickRec d}
    (hg1 : st.g1 = some g) (hend : legLen Y a e (latDir e (decide ((br1Sign e : ℤ) = 1))) (g.1.b (latOf hd e)) ≤ (rk :: tl).length)
    (hg2 : st.g2 = some g') (hroom : 0 < legLen Y a e (latDir e (decide ((br1Sign e : ℤ) ≠ 1))) (g'.1.b (latOf hd e)))
    (hgood : GoodRec Y.m Y.L Y.H g') (o : Finset (Sym2 (Site d))) :
    TallInv hd Y hL hH a e τ
      { st.put Slot.toB2 (tStep hL hH g' (toward (Function.update (nomT hd Y e (Y.lane (tgtCell a e) e)) (axOf hd e) (g'.1.b (axOf hd e))) g'.1.b), o)
        with ph := Phase.segB2 } := by
  obtain ⟨hB1ne, h2⟩ := phaseOf_eq_segB1 (hI.ph_eq ▸ hph)
  obtain ⟨-, hgturn, -, -⟩ := hI.invT.g2_some g' hg2
  have hB2 := hI.invB2
  rw [hg2, h2] at hB2
  rw [decide_neg_br1Sign] at hroom
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [RS.put]; exact (phaseOf_of_B2 (by simp)).symm
  · simp only [RS.put]; exact hI.invA
  · simp only [RS.put]; exact hI.invR
  · simp only [RS.put]; exact hI.invJ
  · simp only [RS.put]; exact hI.invT
  · simp only [RS.put]; exact hI.trunk_done_B1
  · simp only [RS.put, hBl, hg1]
    have hB1 := hI.invB1
    rw [hg1, hBl] at hB1
    exact hB1.of_done Y hd hL hH a e fun r hr _ => by
      simp only [Option.some.injEq] at hr; subst hr; exact ⟨List.cons_ne_nil _ _, hend⟩
  · simp only [RS.put, hg2, h2]
    exact hB2.grow Y hd hL hH a e hY hgturn.axis (rk := g') rfl hgood (by simpa using hroom) o (by simp)
  · simp only [RS.put, hBl, hg1]
    intro _
    refine ⟨List.cons_ne_nil _ _, fun r hr => ?_⟩
    simp only [Option.some.injEq] at hr; subst hr; exact hend
  · simp only [RS.put]; intro; rw [hg2]; simp

/-- **A top step of the second branch preserves the invariant.** [cite: GrimmettPercolation1999, §7.3 pp. 172–174] -/
theorem tallInv_topB2 (hY : Y.OK) {st : RS d} (hI : TallInv hd Y hL hH a e τ st)
    (hph : st.ph = Phase.segB2) {rk : BrickRec d} {tl : List (BrickRec d)} (hBl : st.sB2 = rk :: tl) {g : BrickRec d}
    (hg2 : st.g2 = some g) (hroom : (rk :: tl).length < legLen Y a e (latDir e (decide ((br1Sign e : ℤ) ≠ 1))) (g.1.b (latOf hd e)))
    (hgood : GoodRec Y.m Y.L Y.H rk) (o : Finset (Sym2 (Site d))) :
    TallInv hd Y hL hH a e τ
      { st.put Slot.toB2 (tStep hL hH rk (toward (Function.update (nomT hd Y e (Y.lane (tgtCell a e) e)) (axOf hd e) (g.1.b (axOf hd e))) rk.1.b), o)
        with ph := Phase.segB2 } := by
  have hB2ne := phaseOf_eq_segB2 (hI.ph_eq ▸ hph)
  obtain ⟨-, hgturn, -, -⟩ := hI.invT.g2_some g hg2
  have hB2 := hI.invB2
  rw [hg2, hBl] at hB2
  rw [decide_neg_br1Sign] at hroom
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [RS.put]; exact (phaseOf_of_B2 (by simp)).symm
  · simp only [RS.put]; exact hI.invA
  · simp only [RS.put]; exact hI.invR
  · simp only [RS.put]; exact hI.invJ
  · simp only [RS.put]; exact hI.invT
  · simp only [RS.put]; exact hI.trunk_done_B1
  · simp only [RS.put]
    exact hI.invB1.of_done Y hd hL hH a e fun r hr _ => hI.invB1.done r hr (by rw [hBl]; exact List.cons_ne_nil _ _)
  · simp only [RS.put, hg2, hBl]
    exact hB2.grow Y hd hL hH a e hY hgturn.axis (rk := rk) rfl hgood hroom o (by simp)
  · simp only [RS.put]; intro; exact hI.B2_prev (by rw [hBl]; exact List.cons_ne_nil _ _)
  · simp only [RS.put]; exact hI.B1_g2

end BGNd

end Percolation.Literature

end
