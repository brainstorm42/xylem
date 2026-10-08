import Percolation.Literature.TallRun4
import Percolation.Util.Linter

/-!
# The tall gait, XXI: the outcome passes the guards; completeness and connectivity

For the tall kit (Grimmett, *Percolation*, 2nd ed.
(1999), §7.3, proof of Lemma (7.52)): the supports of the history avoid the zones of the three exit
tokens; the outcome of a complete plan passes the guard `FinishOK`; hence the **completeness** and
**connectivity** obligations of a good kit (`Kit.Good.complete`, `Kit.Good.connect`).

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §7.3 pp. 171–176.
-/

noncomputable section

namespace Percolation.Literature

open LatticeModels Contour
open scoped Classical

namespace BGNd

variable {d : ℕ} [NeZero d]
variable (Y : TallLayout) (hd : 3 ≤ d) (hL : Y.m + 1 ≤ Y.L) (hH : 2 * Y.m + 2 ≤ Y.H) (a : Site 2) (e : MDir) (τ : TTok d)

/-! ## Macro-directions -/

omit [NeZero d] in
/-- **A macro-direction other than the reverse is the direction itself or a lateral one.** [folklore] -/
theorem MDir.cases_of_ne_rev {e e' : MDir} (h : e' ≠ rev e) : e' = e ∨ ∃ b, e' = latDir e b := by
  obtain ⟨i, b⟩ := e'
  obtain ⟨j, c⟩ := e
  by_cases hij : i = j
  · subst hij
    left
    have : b = c := by
      by_contra hbc
      apply h
      simp only [rev, Prod.mk.injEq, true_and]
      cases b <;> cases c <;> simp_all
    rw [this]
  · right
    refine ⟨b, ?_⟩
    simp only [latDir, Prod.mk.injEq, and_true]
    apply Fin.ext
    have h1 := i.isLt; have h2 := j.isLt
    have h3 : i.val ≠ j.val := fun h' => hij (Fin.ext h')
    simp only; omega

omit [NeZero d] in
/-- A direction is not one of its lateral directions. [folklore] -/
theorem ne_latDir (e : MDir) (b : Bool) : e ≠ latDir e b := by
  intro h
  have := congrArg (fun x : MDir => x.1.val) h
  simp only [latDir] at this
  have := e.1.isLt; omega

omit [NeZero d] in
/-- A direction is not the reverse of one of its lateral directions. [folklore] -/
theorem ne_rev_latDir (e : MDir) (b : Bool) : e ≠ rev (latDir e b) := by
  intro h
  have := congrArg (fun x : MDir => x.1.val) h
  simp only [latDir, rev] at this
  have := e.1.isLt; omega

omit [NeZero d] in
/-- Lateral directions with different signs differ. [folklore] -/
theorem latDir_injective (e : MDir) {b b' : Bool} (h : latDir e b = latDir e b') : b = b' := by
  have := congrArg Prod.snd h; simpa [latDir] using this

/-! ## The axis and sign of a branch brick -/

/-- The axis and sign of a branch brick. [folklore] -/
theorem g_axis_sign (hY : Y.OK) (hτ : TAdm hd Y a e τ) {st : RS d} (hI : TallInv hd Y hL hH a e τ st) {w' : ℤˣ} {g : BrickRec d}
    (hg : brIdx Y a e w' ((legOf st.sT 0).b (axOf hd e)) < st.sT.length ∧
      IsTurn Y.m Y.L Y.H (axOf hd e) (sgOf e) (latOf hd e) w' (legOf st.sT (brIdx Y a e w' ((legOf st.sT 0).b (axOf hd e)))) g.1 ∧
      |g.1.b (ax0 hd) - Y.zOf e| ≤ Y.ρv ∧ ∀ j, j ≠ axOf hd e → j ≠ latOf hd e → j ≠ ax0 hd → |g.1.b j| ≤ Y.Lp) :
    g.1.a = latOf hd e ∧ g.1.s = w' := by
  obtain ⟨hNR, hNJ⟩ := sched_bounds Y hd hL hH a e τ hY hτ hI
  obtain ⟨-, -, -, -, -, -, hallR⟩ := all_length_lt Y hd hL hH a e τ hY hτ hI
  have hlenT : st.sT.length ≤ Y.Rmax := by
    have : st.sT.length ≤ st.all.length := by simp only [RS.all, List.length_append]; omega
    omega
  have hT : st.sT ≠ [] := List.ne_nil_of_length_pos (by omega)
  obtain ⟨-, -, hn1, -⟩ := trunk_feasible Y hd hL hH a e τ hY hτ hI hT
  have h12 := n1Of_le_n2Of Y hd a e st.sT
  have hn1' : 1 ≤ brIdx Y a e w' ((legOf st.sT 0).b (axOf hd e)) := by
    rcases Int.units_eq_one_or w' with rfl | rfl <;> rcases Int.units_eq_one_or (br1Sign e) with h | h
    · rw [← h]; exact hn1
    · have : -br1Sign e = 1 := by rw [h]; simp
      rw [← this]; exact hn1.trans h12
    · have : -br1Sign e = -1 := by rw [h]
      rw [← this]; exact hn1.trans h12
    · rw [← h]; exact hn1
  obtain ⟨hgax, hgs', -⟩ := boundsG Y hd hL hH a e τ hY hI hNR hNJ hlenT hg rfl hn1'
  exact ⟨hgax, hgs'⟩

/-- The axis and sign of the head of a nonempty branch list. [folklore] -/
theorem head_axis_sign_B {w' : ℤˣ} {g : BrickRec d} {sB : List (BrickRec d)} {D : Prop} (hB : InvB hd Y hL hH a e w' (some g) sB D)
    (hgax : g.1.a = latOf hd e) (hgs' : g.1.s = w') {rB : BrickRec d} {tB : List (BrickRec d)} (hBl : sB = rB :: tB) :
    rB.1.a = latOf hd e ∧ rB.1.s = w' ∧ legOf (sB ++ [g]) sB.length = rB.1 := by
  subst hBl
  have hrB : legOf ((rB :: tB) ++ [g]) (rB :: tB).length = rB.1 := by rw [List.length_cons]; exact legOf_head_branch
  have hne : (rB :: tB) ≠ [] := List.cons_ne_nil _ _
  have := (hB.grown g rfl hne).axis_sign (k := (rB :: tB).length) (by simp)
  rw [legOf_append_singleton_zero, hrB] at this
  exact ⟨this.1.trans hgax, this.2.trans hgs', hrB⟩

/-! ## The history avoids the zones of the exit tokens -/

/-- **The supports of the history avoid the zone of the straight exit token.** [cite: GrimmettPercolation1999, §7.3 pp. 173–174 (C)] -/
theorem disjoint_hist_zone_straight (hY : Y.OK) (hτ : TAdm hd Y a e τ) {st : RS d} (hI : TallInv hd Y hY.hL hY.hH a e τ st)
    (hB1 : st.sB1 ≠ []) {rT : BrickRec d} {tT : List (BrickRec d)} (hT : st.sT = rT :: tT) (hg : GoodRec Y.m Y.L Y.H rT)
    {h : BrickHist d} (hh : ∀ r ∈ h, r ∈ st.all) :
    Disjoint (histSupp Y.m Y.L Y.H h) (zoneF Y hd (tgtCell a e) e (exitTok hd Y hY.hL hY.hH a e rT)) := by
  obtain ⟨-, -, -, hell, -⟩ := hY.facts
  have hadm := tAdm_exit_straight Y hd hY.hL hY.hH a e τ hY hτ hI hB1 hT hg
  have hTne : st.sT ≠ [] := by rw [hT]; exact List.cons_ne_nil _ _
  have hk : st.sT.length - 1 < st.sT.length := by have := List.length_pos_of_ne_nil hTne; omega
  obtain ⟨hax, hsx⟩ := hI.invT.axis_sign Y hd hY.hL hY.hH a e hTne hk
  have hrT : legOf st.sT (st.sT.length - 1) = rT.1 := by rw [hT]; exact legOf_head rT tT
  rw [hrT] at hax hsx
  obtain ⟨h1, -, -⟩ := exitTok_coords Y hd hY.hL hY.hH a e hg
  rw [hax, hsx] at h1
  have hlo := hadm.longit.1
  have hss : (sgOf e : ℤ) * (sgOf e : ℤ) = 1 := by rcases Int.units_eq_one_or (sgOf e) with h | h <;> simp [h]
  set pos := (exitTok hd Y hY.hL hY.hH a e rT).pos with hpos
  rw [Finset.disjoint_left]
  intro z hz hz'
  obtain ⟨r, hr, hzr⟩ := (mem_histSupp_iff Y.m Y.L Y.H).1 hz
  have hbox := dmid_mem_boxOf_of_mem_suppP hY.hL hY.hH r.1 hzr
  have hreg := ((mem_zoneF Y hd (tgtCell a e) e _).1 hz').2.2
  have hfw := zoneRegion_forward Y hd hY hadm hreg
  have e1 : (sgOf e : ℤ) * (pos (axOf hd e) - Y.ctr (tgtCell a e) e.1) =
      (sgOf e : ℤ) * rT.1.b (axOf hd e) + ((sgOf e : ℤ) * (sgOf e : ℤ)) * ((Y.H : ℤ) + 1) - (sgOf e : ℤ) * Y.ctr (tgtCell a e) e.1 := by
    rw [h1]; ring
  have e2 : (sgOf e : ℤ) * (dmid z (axOf hd e) - 2 * pos (axOf hd e)) =
      (sgOf e : ℤ) * dmid z (axOf hd e) - 2 * ((sgOf e : ℤ) * rT.1.b (axOf hd e)) - 2 * ((sgOf e : ℤ) * (sgOf e : ℤ)) * ((Y.H : ℤ) + 1) := by
    rw [h1]; ring
  rw [e1, hss] at hlo
  rw [e2, hss] at hfw
  rcases e_bound_all Y hd hY.hL hY.hH a e τ hY hτ hI (hh r hr) hbox with hfar | ⟨-, htube⟩
  · linarith only [hfar, hlo, hfw, hell]
  · rw [hrT] at htube
    linarith only [htube, hfw]

/-- **The supports of the history avoid the zone of a lateral exit token.** [cite: GrimmettPercolation1999, §7.3 pp. 173–174 (C)] -/
theorem disjoint_hist_zone_side (hY : Y.OK) (hτ : TAdm hd Y a e τ) {st : RS d} (hI : TallInv hd Y hY.hL hY.hH a e τ st)
    {w' : ℤˣ} {g : BrickRec d} {sB : List (BrickRec d)} {D : Prop} (hB : InvB hd Y hY.hL hY.hH a e w' (some g) sB D)
    (hgf : brIdx Y a e w' ((legOf st.sT 0).b (axOf hd e)) < st.sT.length ∧
      IsTurn Y.m Y.L Y.H (axOf hd e) (sgOf e) (latOf hd e) w' (legOf st.sT (brIdx Y a e w' ((legOf st.sT 0).b (axOf hd e)))) g.1 ∧
      |g.1.b (ax0 hd) - Y.zOf e| ≤ Y.ρv ∧ ∀ j, j ≠ axOf hd e → j ≠ latOf hd e → j ≠ ax0 hd → |g.1.b j| ≤ Y.Lp)
    (hside : w' = br1Sign e ∧ st.g1 = some g ∧ sB = st.sB1 ∨ w' = -br1Sign e ∧ st.g2 = some g ∧ sB = st.sB2)
    (hdone : legLen Y a e (latDir e (decide ((w' : ℤ) = 1))) (g.1.b (latOf hd e)) ≤ sB.length)
    {rB : BrickRec d} {tB : List (BrickRec d)} (hBl : sB = rB :: tB) (hg : GoodRec Y.m Y.L Y.H rB)
    {h : BrickHist d} (hh : ∀ r ∈ h, r ∈ st.all) :
    Disjoint (histSupp Y.m Y.L Y.H h) (zoneF Y hd (tgtCell a e) (latDir e (decide ((w' : ℤ) = 1))) (exitTok hd Y hY.hL hY.hH a e rB)) := by
  obtain ⟨-, -, -, hell, -⟩ := hY.facts
  have hadm := tAdm_exit_side Y hd hY.hL hY.hH a e τ hY hτ hI hB hgf hdone hBl hg
  obtain ⟨hgax, hgs'⟩ := g_axis_sign Y hd hY.hL hY.hH a e τ hY hτ hI hgf
  obtain ⟨hax, hsx, hrB⟩ := head_axis_sign_B Y hd hY.hL hY.hH a e hB hgax hgs' hBl
  obtain ⟨h1, -, -⟩ := exitTok_coords Y hd hY.hL hY.hH a e hg
  rw [hax, hsx] at h1
  set e' := latDir e (decide ((w' : ℤ) = 1)) with he'
  have hsw : (sgOf e' : ℤ) = w' := by
    rw [he', sgOf_latDir_val]; rcases Int.units_eq_one_or w' with h | h <;> simp [h]
  have hw2 : (w' : ℤ) * (w' : ℤ) = 1 := by rcases Int.units_eq_one_or w' with h | h <;> simp [h]
  have haxe' : axOf hd e' = latOf hd e := axOf_latDir hd e _
  have hctr : Y.ctr (tgtCell a e) e'.1 = Y.ctr (tgtCell a e) (latDir e true).1 := rfl
  have hlo := hadm.longit.1
  rw [haxe', hsw, hctr] at hlo
  set pos := (exitTok hd Y hY.hL hY.hH a e rB).pos with hpos
  rw [Finset.disjoint_left]
  intro z hz hz'
  obtain ⟨r, hr, hzr⟩ := (mem_histSupp_iff Y.m Y.L Y.H).1 hz
  have hbox := dmid_mem_boxOf_of_mem_suppP hY.hL hY.hH r.1 hzr
  have hreg := ((mem_zoneF Y hd (tgtCell a e) e' _).1 hz').2.2
  have hfw := zoneRegion_forward Y hd hY hadm hreg
  rw [haxe', hsw] at hfw
  have e1 : (w' : ℤ) * (pos (latOf hd e) - Y.ctr (tgtCell a e) (latDir e true).1) =
      (w' : ℤ) * rB.1.b (latOf hd e) + ((w' : ℤ) * (w' : ℤ)) * ((Y.H : ℤ) + 1) - (w' : ℤ) * Y.ctr (tgtCell a e) (latDir e true).1 := by
    rw [h1]; ring
  have e2 : (w' : ℤ) * (dmid z (latOf hd e) - 2 * pos (latOf hd e)) =
      (w' : ℤ) * dmid z (latOf hd e) - 2 * ((w' : ℤ) * rB.1.b (latOf hd e)) - 2 * ((w' : ℤ) * (w' : ℤ)) * ((Y.H : ℤ) + 1) := by
    rw [h1]; ring
  rw [e1, hw2] at hlo
  rw [e2, hw2] at hfw
  have hv : br1Sign e ≠ -br1Sign e := by
    rcases Int.units_eq_one_or (br1Sign e) with h | h <;> rw [h] <;> decide
  rcases f_bound_all Y hd hY.hL hY.hH a e τ hY hτ hI w' (hh r hr) hbox with hfar | ⟨hw1, g', hg1, htube⟩ | ⟨hw1, g', hg2, htube⟩
  · linarith only [hfar, hlo, hfw, hell]
  · rcases hside with ⟨-, hg1', hsB⟩ | ⟨hw2', -, -⟩
    · rw [hg1] at hg1'; cases hg1'; subst hsB
      rw [hrB] at htube
      linarith only [htube, hfw]
    · exact absurd (hw1.symm.trans hw2') hv
  · rcases hside with ⟨hw2', -, -⟩ | ⟨-, hg2', hsB⟩
    · exact absurd (hw2'.symm.trans hw1) hv
    · rw [hg2] at hg2'; cases hg2'; subst hsB
      rw [hrB] at htube
      linarith only [htube, hfw]

/-! ## The outcome passes the guards -/

variable (hY : Y.OK)

/-- **The outcome of a complete all-good run**: defined, passing `FinishOK`, and handing on exit
tokens of good records of the run. [cite: GrimmettPercolation1999, §7.3 pp. 173–174] -/
theorem finish_facts (hτ : TAdm hd Y a e τ) {h : BrickHist d} (hI : TallInv hd Y hY.hL hY.hH a e τ (foldState hd Y a e τ h))
    (hperm : (foldState hd Y a e τ h).all.Perm h) (hgood : AllGood Y.m Y.L Y.H h) (hs : step hd Y a e τ (foldState hd Y a e τ h) = none) :
    ∃ f, tallFinish hd Y hY.hL hY.hH a e τ h = some f ∧ (tallKit Y hd hY).FinishOK Y.m Y.L Y.H a e h f ∧
      ∀ e', e' ≠ rev e → ∃ r ∈ h, f e' = exitTok hd Y hY.hL hY.hH a e r := by
  set st := foldState hd Y a e τ h with hst
  obtain ⟨hph, hB2ne, hlen2⟩ := step_eq_none_imp Y hd hY.hL hY.hH a e τ hY hτ hI hs
  obtain ⟨hB1ne, hlen1⟩ := hI.B2_prev hB2ne
  have hTne := hI.trunk_done_B1 hB1ne
  obtain ⟨γ₁, hγ₁⟩ := Option.ne_none_iff_exists'.1 (hI.invB1.prev hB1ne)
  obtain ⟨γ₂, hγ₂⟩ := Option.ne_none_iff_exists'.1 (hI.B1_g2 hB1ne)
  obtain ⟨rT, tT, r1, t1, r2, t2, hT, hB1, hB2, hfin⟩ := tallFinish_eq Y hd hY.hL hY.hH a e τ hY hτ hI hs
  rw [← hst] at hT hB1 hB2
  have hh : ∀ r ∈ h, r ∈ st.all := fun r hr => hperm.symm.subset hr
  have memT : rT ∈ h := hperm.subset (by rw [RS.all, hT]; simp)
  have mem1 : r1 ∈ h := hperm.subset (by rw [RS.all, hB1]; simp)
  have mem2 : r2 ∈ h := hperm.subset (by rw [RS.all, hB2]; simp)
  have hIB1 : InvB hd Y hY.hL hY.hH a e (br1Sign e) (some γ₁) st.sB1 (st.sB2 ≠ []) := by have := hI.invB1; rwa [hγ₁] at this
  have hIB2 : InvB hd Y hY.hL hY.hH a e (-br1Sign e) (some γ₂) st.sB2 False := by have := hI.invB2; rwa [hγ₂] at this
  set b₁ := decide ((br1Sign e : ℤ) = 1) with hb₁
  set b₂ := decide ((br1Sign e : ℤ) ≠ 1) with hb₂
  have hb12 : b₂ = !b₁ := by rw [hb₁, hb₂]; rcases Int.units_eq_one_or (br1Sign e) with h' | h' <;> simp [h']
  have hb₂' : b₂ = decide (((-br1Sign e : ℤˣ) : ℤ) = 1) := decide_neg_br1Sign e
  set f : MDir → TTok d := fun e' => if e' = latDir e b₁ then exitTok hd Y hY.hL hY.hH a e r1
    else if e' = latDir e b₂ then exitTok hd Y hY.hL hY.hH a e r2 else exitTok hd Y hY.hL hY.hH a e rT with hf
  have hfe : f e = exitTok hd Y hY.hL hY.hH a e rT := by
    simp only [hf, if_neg (ne_latDir e b₁), if_neg (ne_latDir e b₂)]
  have hf1 : f (latDir e b₁) = exitTok hd Y hY.hL hY.hH a e r1 := by simp only [hf, if_pos rfl]
  have hf2 : f (latDir e b₂) = exitTok hd Y hY.hL hY.hH a e r2 := by
    have : latDir e b₂ ≠ latDir e b₁ := fun h' => by have := latDir_injective e h'; rw [hb12] at this; cases b₁ <;> simp at this
    show (if latDir e b₂ = latDir e b₁ then exitTok hd Y hY.hL hY.hH a e r1
      else if latDir e b₂ = latDir e b₂ then exitTok hd Y hY.hL hY.hH a e r2 else exitTok hd Y hY.hL hY.hH a e rT) = _
    rw [if_neg this, if_pos rfl]
  -- the three tokens
  have admT := tAdm_exit_straight Y hd hY.hL hY.hH a e τ hY hτ hI hB1ne hT (hgood rT memT)
  have adm1 := tAdm_exit_side Y hd hY.hL hY.hH a e τ hY hτ hI hIB1 (hI.invT.g1_some γ₁ hγ₁) (hlen1 γ₁ hγ₁) hB1 (hgood r1 mem1)
  have hdone2 : legLen Y a e (latDir e (decide (((-br1Sign e : ℤˣ) : ℤ) = 1))) (γ₂.1.b (latOf hd e)) ≤ st.sB2.length := by
    rw [← hb₂']; exact hlen2 γ₂ hγ₂
  have adm2 := tAdm_exit_side Y hd hY.hL hY.hH a e τ hY hτ hI hIB2 (hI.invT.g2_some γ₂ hγ₂) hdone2 hB2 (hgood r2 mem2)
  rw [← hb₂'] at adm2
  have disT := disjoint_hist_zone_straight Y hd a e τ hY hτ hI hB1ne hT (hgood rT memT) hh
  have dis1 := disjoint_hist_zone_side Y hd a e τ hY hτ hI hIB1 (hI.invT.g1_some γ₁ hγ₁) (Or.inl ⟨rfl, hγ₁, rfl⟩) (hlen1 γ₁ hγ₁) hB1
    (hgood r1 mem1) hh
  have dis2 := disjoint_hist_zone_side Y hd a e τ hY hτ hI hIB2 (hI.invT.g2_some γ₂ hγ₂) (Or.inr ⟨rfl, hγ₂, rfl⟩) hdone2 hB2
    (hgood r2 mem2) hh
  rw [← hb₂'] at dis2
  have hsrc : ∀ r, (exitTok hd Y hY.hL hY.hH a e r).src = some e := fun r => rfl
  refine ⟨f, hfin, ⟨fun e' => ?_, fun e' he' => ?_⟩, fun e' he' => ?_⟩
  · show srcDirK Y hd (f e') = some e
    by_cases h1 : e' = latDir e b₁
    · subst h1; rw [hf1]; exact srcDirK_of_adm Y hd hY adm1 (hsrc r1) (ne_rev_latDir e b₁)
    by_cases h2 : e' = latDir e b₂
    · subst h2; rw [hf2]; exact srcDirK_of_adm Y hd hY adm2 (hsrc r2) (ne_rev_latDir e b₂)
    · have : f e' = exitTok hd Y hY.hL hY.hH a e rT := by simp only [hf, if_neg h1, if_neg h2]
      rw [this]; exact srcDirK_of_adm Y hd hY admT (hsrc rT) (rev_ne_self e).symm
  · show (TAdm hd Y (a + stepVec e) e' (f e') ∧ (f e').src ≠ none) ∧ Y.cellOf hd (f e').pos = a + stepVec e ∧
      Disjoint (histSupp Y.m Y.L Y.H h) (zoneF Y hd (a + stepVec e) e' (f e'))
    change (TAdm hd Y (tgtCell a e) e' (f e') ∧ (f e').src ≠ none) ∧ Y.cellOf hd (f e').pos = tgtCell a e ∧
      Disjoint (histSupp Y.m Y.L Y.H h) (zoneF Y hd (tgtCell a e) e' (f e'))
    rcases MDir.cases_of_ne_rev he' with rfl | ⟨b, rfl⟩
    · rw [hfe]; exact ⟨⟨admT, by rw [hsrc]; simp⟩, admT.cellOf_eq Y hd hY, disT⟩
    · by_cases hb : b = b₁
      · subst hb; rw [hf1]; exact ⟨⟨adm1, by rw [hsrc]; simp⟩, adm1.cellOf_eq Y hd hY, dis1⟩
      · have hb' : b = b₂ := by rw [hb12]; exact Bool.eq_not_iff.2 hb
        subst hb'; rw [hf2]; exact ⟨⟨adm2, by rw [hsrc]; simp⟩, adm2.cellOf_eq Y hd hY, dis2⟩
  · rcases MDir.cases_of_ne_rev he' with rfl | ⟨b, rfl⟩
    · exact ⟨rT, memT, hfe⟩
    · by_cases hb : b = b₁
      · subst hb; exact ⟨r1, mem1, hf1⟩
      · have hb' : b = b₂ := by rw [hb12]; exact Bool.eq_not_iff.2 hb
        subst hb'; exact ⟨r2, mem2, hf2⟩

/-! ## Completeness and connectivity -/

/-- **Completeness**: along every all-good guarded run of `R` iterations from an admissible token the
guarded outcome is defined. [cite: GrimmettPercolation1999, §7.3 pp. 171–174] -/
theorem tall_complete (hτ : TAdm hd Y a e τ) (ω : BondConfig (Site d))
    (hgood : AllGood Y.m Y.L Y.H ((tallKit Y hd hY).run Y.m Y.L Y.H a e τ Y.Rmax ω)) :
    ∃ f, (tallKit Y hd hY).gfinish Y.m Y.L Y.H a e τ ((tallKit Y hd hY).run Y.m Y.L Y.H a e τ Y.Rmax ω) = some f ∧
      ∀ e', e' ≠ rev e → ∃ r ∈ (tallKit Y hd hY).run Y.m Y.L Y.H a e τ Y.Rmax ω, f e' = exitTok hd Y hY.hL hY.hH a e r := by
  obtain ⟨hI, hperm⟩ := run_state Y hd a e τ hY hτ ω Y.Rmax
  have hs := step_eq_none_at_R Y hd a e τ hY hτ ω hgood
  obtain ⟨f, hfin, hok, hex⟩ := finish_facts Y hd a e τ hY hτ hI hperm hgood hs
  exact ⟨f, (tallKit Y hd hY).gfinish_eq_some Y.m Y.L Y.H (by rw [tallKit_finish]; exact hfin) hgood hok, hex⟩

/-- **Connectivity**: the tokens handed on by a successful guarded run from an admissible token with
open seed have open seeds joined to the token's centre. [cite: GrimmettPercolation1999, §7.3 pp. 172–174 (A), (B)] -/
theorem tall_connect (hτ : TAdm hd Y a e τ) (ω : BondConfig (Site d)) {f : MDir → TTok d} (hpre : IsSeed ω (square τ.ax Y.m τ.pos))
    (hf : (tallKit Y hd hY).gfinish Y.m Y.L Y.H a e τ ((tallKit Y hd hY).run Y.m Y.L Y.H a e τ Y.Rmax ω) = some f)
    {e' : MDir} (he' : e' ≠ rev e) :
    IsSeed ω (square (f e').ax Y.m (f e').pos) ∧ (openGraph ω).Reachable τ.pos (f e').pos := by
  obtain ⟨-, hgood, -⟩ := (tallKit Y hd hY).gfinish_spec Y.m Y.L Y.H hf
  obtain ⟨f', hf', hex⟩ := tall_complete Y hd a e τ hY hτ ω hgood
  rw [hf] at hf'; cases hf'
  obtain ⟨r, hr, hfr⟩ := hex e' he'
  have hconn := conn_run Y hd a e τ hY hτ hpre Y.Rmax hgood r hr
  have hg : GoodRec Y.m Y.L Y.H r := hgood r hr
  have hsub : cfgOf r ⊆ ω := by
    have hobs := (tallKit Y hd hY).run_obs Y.m Y.L Y.H hr
    have : r = (r.1, obs ω (suppP Y.m Y.L Y.H r.1)) := by rw [← hobs]
    rw [this]; exact cfgOf_obs_subset _ _ _
  rw [hfr]
  set sg := toward (nomT hd Y e (Y.lane (tgtCell a e) e)) r.1.b
  refine ⟨?_, hconn.2.trans (reachable_tStep hY.hL hY.hH hg sg hsub hconn.1)⟩
  exact (isSeed_tStep hY.hL hY.hH hg sg).mono hsub

end BGNd

end Percolation.Literature

end
