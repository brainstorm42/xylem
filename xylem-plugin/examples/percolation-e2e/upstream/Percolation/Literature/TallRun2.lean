import Percolation.Literature.TallRun
import Percolation.Util.Linter

/-!
# The tall gait, XVIII: completion of the plan, the acts' records, connectivity along the run

For the tall kit (Grimmett, *Percolation*, 2nd ed.
(1999), §7.3, proof of Lemma (7.52)): the plan has no next act only when the second branch is
complete (`step_eq_none_imp`), in which case the outcome `tallFinish` hands on the three exit tokens
(`tallFinish_eq`); the record off which an act steps is one of the state's records, with a different
axis for side steps (`act_wf`); and along an all-good guarded run from a token with open seed, every
recorded brick has an open entry square joined to the token's centre (`conn_run`).

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

/-! ## The plan stops only when complete -/

/-- **The plan has no next act only when the second branch is complete.** [cite: GrimmettPercolation1999, §7.3 p. 174] -/
theorem step_eq_none_imp (hY : Y.OK) (hτ : TAdm hd Y a e τ) {st : RS d} (hI : TallInv hd Y hL hH a e τ st)
    (hs : step hd Y a e τ st = none) :
    st.ph = Phase.segB2 ∧ st.sB2 ≠ [] ∧ ∀ g, st.g2 = some g →
      legLen Y a e (latDir e (decide ((br1Sign e : ℤ) ≠ 1))) (g.1.b (latOf hd e)) ≤ st.sB2.length := by
  obtain ⟨-, -, -, -, -, -, hallR⟩ := all_length_lt Y hd hL hH a e τ hY hτ hI
  have hlenT : st.sT.length ≤ Y.Rmax := by
    have : st.sT.length ≤ st.all.length := by simp only [RS.all, List.length_append]; omega
    omega
  unfold step at hs
  rcases hph : st.ph with _ | _ | _ | _ | _ | _ | _
  · exfalso; simp only [hph] at hs
    cases hA : st.sA with
    | nil => rw [hA] at hs; exact absurd hs (by simp)
    | cons r₀ tl => rw [hA] at hs; simp only at hs; split_ifs at hs
  · exfalso
    obtain ⟨hRne, -⟩ := phaseOf_eq_segR (hI.ph_eq ▸ hph)
    obtain ⟨rk, tl, hR⟩ := List.exists_cons_of_ne_nil hRne
    simp only [hph, hR, getLast?_eq_recOf (List.cons_ne_nil rk tl)] at hs
    split_ifs at hs
  · exfalso
    obtain ⟨hJne, -⟩ := phaseOf_eq_segJ (hI.ph_eq ▸ hph)
    obtain ⟨rk, tl, hJ⟩ := List.exists_cons_of_ne_nil hJne
    simp only [hph, hJ, getLast?_eq_recOf (List.cons_ne_nil rk tl)] at hs
    split_ifs at hs
  · exfalso
    obtain ⟨hTne, -⟩ := phaseOf_eq_segT (hI.ph_eq ▸ hph)
    obtain ⟨rk, tl, hT⟩ := List.exists_cons_of_ne_nil hTne
    simp only [hph, hT, getLast?_eq_recOf (List.cons_ne_nil rk tl), List.length_cons, Nat.add_sub_cancel] at hs
    have hn1 : brIdx Y a e (br1Sign e) ((recOf (rk :: tl) 0).1.b (axOf hd e)) = n1Of hd Y a e st.sT := by rw [hT]; rfl
    have hn2 : brIdx Y a e (-br1Sign e) ((recOf (rk :: tl) 0).1.b (axOf hd e)) = n2Of hd Y a e st.sT := by rw [hT]; rfl
    have hnE : legLen Y a e e ((recOf (rk :: tl) 0).1.b (axOf hd e)) = legLen Y a e e ((legOf st.sT 0).b (axOf hd e)) := by rw [hT]; rfl
    rw [hn1, hn2, hnE] at hs
    obtain ⟨-, -, -, hn2le⟩ := trunk_feasible Y hd hL hH a e τ hY hτ hI hTne
    have h12 := n1Of_le_n2Of Y hd a e st.sT
    have hlenT' : st.sT.length = tl.length + 1 := by rw [hT]; rfl
    split_ifs at hs with hc1 hc2 hroom
    · -- the `else` branch: `g1` present, `g2` present and the first branch has room
      cases hg1 : st.g1 with
      | none =>
        rw [hg1] at hs
        have := hI.invT.g1_none hg1
        exact hc1 ⟨hg1, by omega⟩
      | some g =>
        rw [hg1] at hs; simp only at hs
        split_ifs at hs with hcB
        apply hcB
        constructor
        · intro hg2
          have := hI.invT.g2_none hg2 (by rw [hg1]; simp)
          exact hc2 ⟨by rw [hg1]; simp, hg2, by omega⟩
        · exact (branch_feasible Y hd hL hH a e τ hY hτ hI hlenT (hI.invT.g1_some g hg1) rfl).1
  · exfalso
    obtain ⟨hBne, -⟩ := phaseOf_eq_segB1 (hI.ph_eq ▸ hph)
    obtain ⟨rk, tl, hB⟩ := List.exists_cons_of_ne_nil hBne
    obtain ⟨g, hg1⟩ := Option.ne_none_iff_exists'.1 (hI.invB1.prev hBne)
    obtain ⟨g', hg2⟩ := Option.ne_none_iff_exists'.1 (hI.B1_g2 hBne)
    simp only [hph, hB, hg1, hg2] at hs
    split_ifs at hs with h1 h2
    exact h2 (by
      have := (branch_feasible Y hd hL hH a e τ hY hτ hI hlenT (hI.invT.g2_some g' hg2) rfl).1
      rwa [decide_neg_br1Sign])
  · have hBne := phaseOf_eq_segB2 (hI.ph_eq ▸ hph)
    obtain ⟨rk, tl, hB⟩ := List.exists_cons_of_ne_nil hBne
    obtain ⟨g, hg2⟩ := Option.ne_none_iff_exists'.1 (hI.invB2.prev hBne)
    simp only [hph, hB, hg2] at hs
    split_ifs at hs with h1
    refine ⟨rfl, hBne, fun g'' hg'' => ?_⟩
    rw [hg2] at hg''; simp only [Option.some.injEq] at hg''; subst hg''
    rw [hB]; omega
  · exact absurd (hI.ph_eq ▸ hph : phaseOf st = Phase.done) (by unfold phaseOf; split_ifs <;> simp)

/-- **The outcome of a complete plan**: the three exit tokens. [cite: GrimmettPercolation1999, §7.3 p. 174] -/
theorem tallFinish_eq (hY : Y.OK) (hτ : TAdm hd Y a e τ) {h : BrickHist d} (hI : TallInv hd Y hL hH a e τ (foldState hd Y a e τ h))
    (hs : step hd Y a e τ (foldState hd Y a e τ h) = none) :
    ∃ rT tT r1 t1 r2 t2, (foldState hd Y a e τ h).sT = rT :: tT ∧ (foldState hd Y a e τ h).sB1 = r1 :: t1 ∧
      (foldState hd Y a e τ h).sB2 = r2 :: t2 ∧
      tallFinish hd Y hL hH a e τ h = some (fun e' =>
        if e' = latDir e (decide ((br1Sign e : ℤ) = 1)) then exitTok hd Y hL hH a e r1
        else if e' = latDir e (decide ((br1Sign e : ℤ) ≠ 1)) then exitTok hd Y hL hH a e r2
        else exitTok hd Y hL hH a e rT) := by
  obtain ⟨hph, hB2ne, -⟩ := step_eq_none_imp Y hd hL hH a e τ hY hτ hI hs
  obtain ⟨hB1ne, -⟩ := hI.B2_prev hB2ne
  have hTne := hI.trunk_done_B1 hB1ne
  obtain ⟨rT, tT, hT⟩ := List.exists_cons_of_ne_nil hTne
  obtain ⟨r1, t1, hB1⟩ := List.exists_cons_of_ne_nil hB1ne
  obtain ⟨r2, t2, hB2⟩ := List.exists_cons_of_ne_nil hB2ne
  refine ⟨rT, tT, r1, t1, r2, t2, hT, hB1, hB2, ?_⟩
  unfold tallFinish
  simp only [hph, hs, hT, hB1, hB2]

/-! ## The record of an act -/

/-- Well-formedness of an act relative to a run state: the first act needs no record; a top step steps
off one of the state's records; a side step moreover onto a different axis. [folklore] -/
def ActWF (st : RS d) : Act d → Prop
  | Act.first => st.sA = []
  | Act.top r _ => r ∈ st.all
  | Act.side r i _ _ => r ∈ st.all ∧ i ≠ r.1.a

/-- **The act of the plan is well formed.** [folklore] -/
theorem act_wf {st : RS d} (hI : TallInv hd Y hL hH a e τ st) {act : Act d} {slot : Slot} {ph' : Phase}
    (hs : step hd Y a e τ st = some (act, slot, ph')) : ActWF st act := by
  have memA : ∀ r, r ∈ st.sA → r ∈ st.all := fun r h => by simp only [RS.all, List.mem_append]; tauto
  have memR : ∀ r, r ∈ st.sR → r ∈ st.all := fun r h => by simp only [RS.all, List.mem_append]; tauto
  have memJ : ∀ r, r ∈ st.sJ → r ∈ st.all := fun r h => by simp only [RS.all, List.mem_append]; tauto
  have memT : ∀ r, r ∈ st.sT → r ∈ st.all := fun r h => by simp only [RS.all, List.mem_append]; tauto
  have memG1 : ∀ r, st.g1 = some r → r ∈ st.all := fun r h => by simp only [RS.all, List.mem_append, h]; simp
  have memG2 : ∀ r, st.g2 = some r → r ∈ st.all := fun r h => by simp only [RS.all, List.mem_append, h]; simp
  have memB1 : ∀ r, r ∈ st.sB1 → r ∈ st.all := fun r h => by simp only [RS.all, List.mem_append]; tauto
  have memB2 : ∀ r, r ∈ st.sB2 → r ∈ st.all := fun r h => by simp only [RS.all, List.mem_append]; tauto
  have hea : latOf hd e ≠ axOf hd e := latOf_ne_axOf hd e
  have h0a : ax0 hd ≠ axOf hd e := (axOf_ne_ax0 hd e).symm
  have hf0 : latOf hd e ≠ ax0 hd := latOf_ne_ax0 hd e
  unfold step at hs
  rcases hph : st.ph with _ | _ | _ | _ | _ | _ | _
  · simp only [hph] at hs
    cases hA : st.sA with
    | nil => rw [hA] at hs; simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, -, -⟩ := hs; exact hA
    | cons r₀ tl =>
      rw [hA] at hs; simp only at hs
      have hne : st.sA ≠ [] := by rw [hA]; exact List.cons_ne_nil _ _
      have hax : r₀.1.a = axOf hd e := by
        have h1 := (hI.invA.grown hne).axis_sign (k := tl.length) (by rw [hA]; simp)
        rw [hI.invA.zero hne, hA, legOf_cons_length] at h1; exact h1.1
      have hmem : r₀ ∈ st.all := memA r₀ (by rw [hA]; exact List.mem_cons_self)
      split_ifs at hs <;> simp only [Option.some.injEq, Prod.mk.injEq] at hs <;> obtain ⟨rfl, -, -⟩ := hs <;>
        first | exact hmem | (refine ⟨hmem, ?_⟩; rw [hax]; first | exact hea | exact h0a)
  · rcases hR : st.sR with _ | ⟨rk, tl⟩
    · simp only [hph, hR] at hs; exact absurd hs (by simp)
    · simp only [hph, hR, getLast?_eq_recOf (List.cons_ne_nil rk tl), List.length_cons, Nat.add_sub_cancel] at hs
      have hne : st.sR ≠ [] := by rw [hR]; exact List.cons_ne_nil _ _
      have hax : rk.1.a = ax0 hd := by
        have h1 := hI.invR.axis_sign Y hd hL hH a e τ hne (k := tl.length) (by rw [hR]; simp)
        rw [hR, legOf_cons_length] at h1; exact h1.1
      have hmem : rk ∈ st.all := memR rk (by rw [hR]; exact List.mem_cons_self)
      split_ifs at hs <;> simp only [Option.some.injEq, Prod.mk.injEq] at hs <;> obtain ⟨rfl, -, -⟩ := hs <;>
        first | exact hmem | (refine ⟨hmem, ?_⟩; rw [hax]; exact hf0)
  · rcases hJ : st.sJ with _ | ⟨rk, tl⟩
    · simp only [hph, hJ] at hs; exact absurd hs (by simp)
    · simp only [hph, hJ, getLast?_eq_recOf (List.cons_ne_nil rk tl), List.length_cons, Nat.add_sub_cancel] at hs
      have hne : st.sJ ≠ [] := by rw [hJ]; exact List.cons_ne_nil _ _
      have hax : rk.1.a = latOf hd e := by
        have h1 := hI.invJ.axis_sign Y hd hL hH a e τ hne (k := tl.length) (by rw [hJ]; simp)
        rw [hJ, legOf_cons_length] at h1; exact h1.1
      have hmem : rk ∈ st.all := memJ rk (by rw [hJ]; exact List.mem_cons_self)
      split_ifs at hs <;> simp only [Option.some.injEq, Prod.mk.injEq] at hs <;> obtain ⟨rfl, -, -⟩ := hs <;>
        first | exact hmem | (refine ⟨hmem, ?_⟩; rw [hax]; exact hea.symm)
  · rcases hT : st.sT with _ | ⟨rk, tl⟩
    · simp only [hph, hT] at hs; exact absurd hs (by simp)
    · simp only [hph, hT, getLast?_eq_recOf (List.cons_ne_nil rk tl), List.length_cons, Nat.add_sub_cancel] at hs
      have hne : st.sT ≠ [] := by rw [hT]; exact List.cons_ne_nil _ _
      have hax : rk.1.a = axOf hd e := by
        have h1 := hI.invT.axis_sign Y hd hL hH a e hne (k := tl.length) (by rw [hT]; simp)
        rw [hT, legOf_cons_length] at h1; exact h1.1
      have hmem : rk ∈ st.all := memT rk (by rw [hT]; exact List.mem_cons_self)
      by_cases hc1 : st.g1 = none ∧ brIdx Y a e (br1Sign e) ((recOf (rk :: tl) 0).1.b (axOf hd e)) ≤ tl.length
      · rw [if_pos hc1] at hs; simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, -, -⟩ := hs
        exact ⟨hmem, by rw [hax]; exact hea⟩
      · rw [if_neg hc1] at hs
        by_cases hc2 : st.g1 ≠ none ∧ st.g2 = none ∧ brIdx Y a e (-br1Sign e) ((recOf (rk :: tl) 0).1.b (axOf hd e)) ≤ tl.length
        · rw [if_pos hc2] at hs; simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, -, -⟩ := hs
          exact ⟨hmem, by rw [hax]; exact hea⟩
        · rw [if_neg hc2] at hs
          by_cases hroom : tl.length < legLen Y a e e ((recOf (rk :: tl) 0).1.b (axOf hd e))
          · rw [if_pos hroom] at hs; simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, -, -⟩ := hs
            exact hmem
          · rw [if_neg hroom] at hs
            cases hg1 : st.g1 with
            | none => rw [hg1] at hs; exact absurd hs (by simp)
            | some g =>
              rw [hg1] at hs; simp only at hs
              split_ifs at hs
              simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, -, -⟩ := hs; exact memG1 g hg1
  · rcases hB : st.sB1 with _ | ⟨rk, tl⟩
    · simp only [hph, hB] at hs; exact absurd hs (by simp)
    · cases hg1 : st.g1 with
      | none => simp only [hph, hB, hg1] at hs; exact absurd hs (by simp)
      | some g =>
        simp only [hph, hB, hg1] at hs
        by_cases hroom : (rk :: tl).length < legLen Y a e (latDir e (decide ((br1Sign e : ℤ) = 1))) (g.1.b (latOf hd e))
        · rw [if_pos hroom] at hs; simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, -, -⟩ := hs
          exact memB1 rk (by rw [hB]; exact List.mem_cons_self)
        · rw [if_neg hroom] at hs
          cases hg2 : st.g2 with
          | none => rw [hg2] at hs; exact absurd hs (by simp)
          | some g' =>
            rw [hg2] at hs; simp only at hs
            split_ifs at hs
            simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, -, -⟩ := hs; exact memG2 g' hg2
  · rcases hB : st.sB2 with _ | ⟨rk, tl⟩
    · simp only [hph, hB] at hs; exact absurd hs (by simp)
    · cases hg2 : st.g2 with
      | none => simp only [hph, hB, hg2] at hs; exact absurd hs (by simp)
      | some g =>
        simp only [hph, hB, hg2] at hs
        split_ifs at hs
        simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, -, -⟩ := hs
        exact memB2 rk (by rw [hB]; exact List.mem_cons_self)
  · simp only [hph] at hs; exact absurd hs (by simp)

/-! ## Connectivity along the run -/

variable (hY : Y.OK)

/-- Earlier runs are all good if a later one is. [folklore] -/
theorem allGood_run_of_le {k n : ℕ} (hkn : k ≤ n) (ω : BondConfig (Site d))
    (h : AllGood Y.m Y.L Y.H ((tallKit Y hd hY).run Y.m Y.L Y.H a e τ n ω)) : AllGood Y.m Y.L Y.H ((tallKit Y hd hY).run Y.m Y.L Y.H a e τ k ω) := by
  induction n with
  | zero => have : k = 0 := by omega
            subst this; exact h
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le hkn with rfl | hlt
    · exact h
    · apply ih (by omega)
      cases hg : (tallKit Y hd hY).gnext Y.m Y.L Y.H a e τ ((tallKit Y hd hY).run Y.m Y.L Y.H a e τ n ω) with
      | none => rwa [(tallKit Y hd hY).run_succ_of_none Y.m Y.L Y.H hg] at h
      | some β => rw [(tallKit Y hd hY).run_succ_of_some Y.m Y.L Y.H hg, allGood_cons] at h; exact h.2

/-- **Connectivity along the run**: from an admissible token with open seed, along an all-good
guarded run, every recorded brick has an open entry square and its base centre is joined to the
token's centre by an open path. [cite: GrimmettPercolation1999, §7.3 pp. 172–173 (A), (B)] -/
theorem conn_run (hτ : TAdm hd Y a e τ) {ω : BondConfig (Site d)} (hpre : IsSeed ω (square τ.ax Y.m τ.pos)) (n : ℕ)
    (hgood : AllGood Y.m Y.L Y.H ((tallKit Y hd hY).run Y.m Y.L Y.H a e τ n ω)) :
    ∀ r ∈ (tallKit Y hd hY).run Y.m Y.L Y.H a e τ n ω,
      IsSeed ω (square r.1.a Y.m r.1.b) ∧ (openGraph ω).Reachable τ.pos r.1.b := by
  induction n with
  | zero => intro r hr; exact absurd hr (by simp [Kit.run])
  | succ n ih =>
    set h := (tallKit Y hd hY).run Y.m Y.L Y.H a e τ n ω with hh
    have hgood_n : AllGood Y.m Y.L Y.H h := allGood_run_of_le Y hd a e τ hY (Nat.le_succ n) ω hgood
    have ih' := ih hgood_n
    cases hg : (tallKit Y hd hY).gnext Y.m Y.L Y.H a e τ h with
    | none => rw [(tallKit Y hd hY).run_succ_of_none Y.m Y.L Y.H hg]; exact ih'
    | some β =>
      rw [(tallKit Y hd hY).run_succ_of_some Y.m Y.L Y.H hg]
      obtain ⟨act, slot, ph', hs, rfl, -, -⟩ := exists_step_of_gnext Y hd a e τ hY hg
      obtain ⟨hI, hperm⟩ := run_state Y hd a e τ hY hτ ω n
      have hwf := act_wf Y hd hY.hL hY.hH a e τ hI hs
      intro r hr
      rcases List.mem_cons.1 hr with rfl | hr
      · -- the new brick
        simp only
        -- records of the state are records of the run: good, observed on `ω`, with open entry square
        have hfacts : ∀ r₀ ∈ (foldState hd Y a e τ h).all, GoodRec Y.m Y.L Y.H r₀ ∧ cfgOf r₀ ⊆ ω ∧
            IsSeed ω (square r₀.1.a Y.m r₀.1.b) ∧ (openGraph ω).Reachable τ.pos r₀.1.b := by
          intro r₀ hr₀
          have hr₀h : r₀ ∈ h := hperm.subset hr₀
          refine ⟨hgood_n r₀ hr₀h, ?_, ih' r₀ hr₀h⟩
          have hobs := (tallKit Y hd hY).run_obs Y.m Y.L Y.H hr₀h
          have : r₀ = (r₀.1, obs ω (suppP Y.m Y.L Y.H r₀.1)) := by rw [← hobs]
          rw [this]; exact cfgOf_obs_subset _ _ _
        cases act with
        | first =>
          simp only [placeOf]
          rw [← hτ.ax_eq]; exact ⟨hpre, SimpleGraph.Reachable.refl _⟩
        | top r₀ sg =>
          obtain ⟨hg0, hsub, hseed, hreach⟩ := hfacts r₀ hwf
          simp only [placeOf]
          exact ⟨(isSeed_tStep hY.hL hY.hH hg0 sg).mono hsub, hreach.trans (reachable_tStep hY.hL hY.hH hg0 sg hsub hseed)⟩
        | side r₀ i u sg =>
          obtain ⟨hmem, hi⟩ : r₀ ∈ (foldState hd Y a e τ h).all ∧ i ≠ r₀.1.a := hwf
          obtain ⟨hg0, hsub, hseed, hreach⟩ := hfacts r₀ hmem
          simp only [placeOf]
          exact ⟨(isSeed_sStep hY.hL hY.hH hg0 hi u sg).mono hsub, hreach.trans (reachable_sStep hY.hL hY.hH hg0 hi u sg hsub hseed)⟩
      · exact ih' r hr

end BGNd

end Percolation.Literature

end
