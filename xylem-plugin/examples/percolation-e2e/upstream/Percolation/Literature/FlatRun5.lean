import Percolation.Literature.FlatKitDef
import Percolation.Util.Linter

/-!
# The flat gait, XXVIII–XXXII

This module gathers 5 consecutive parts of the flat-gait development, in order:
XXVIII: the run, I — the run state along the guarded run ·
XXIX: the run, II — stopping, the outcome, connectivity along the run ·
XXX: the run, III — the exit tokens are admissible ·
XXXI: the run, IV — the recorded boxes avoid the zones of the exit tokens ·
XXXII: the run, V — the outcome passes the guards; completeness, connectivity.
Part 1 follows; the later parts keep their own headers below.

# Part 1 (The flat gait, XXVIII): the run, I — the run state along the guarded run

The guarded run of the flat block kit (`flatKit`;
Grimmett, *Percolation*, 2nd ed. (1999), §7.3 pp. 171–174, case `H < L`): the state of the plan
along the run satisfies the invariant `FlatInv` and holds exactly the run's records
(`run_stateF`), so the guards of the renormalisation pass at every step (`guards_passF`: the next
support is fresh, by the pairwise disjointness of the boxes, and inside the zone); hence every
iteration of an all-good guarded run places a brick while the plan has a next act
(`run_progressF`), and after `R` iterations the plan is complete (`fstep_eq_none_at_R`).

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §7.3 pp. 171–174.
-/

noncomputable section

namespace Percolation.Literature

open LatticeModels Contour
open scoped Classical

namespace BGNd

variable {d : ℕ} [NeZero d]
variable (Y : FlatLayout) (hd : 3 ≤ d) (a : Site 2) (e : MDir) (τ : TTok d)

/-! ## Filing a record -/

omit [NeZero d] in
/-- Consing onto one value of a family permutes the flattened family over a duplicate-free index
list containing that index. [folklore] -/
theorem perm_flatMap_update {ι : Type*} [DecidableEq ι] (f : ι → List (BrickRec d)) (i : ι) (r : BrickRec d) :
    ∀ (l : List ι), l.Nodup → i ∈ l → (l.flatMap (Function.update f i (r :: f i))).Perm (r :: l.flatMap f) := by
  intro l
  induction l with
  | nil => intro _ h; simp at h
  | cons j tl ih =>
    intro hnd hmem
    rw [List.nodup_cons] at hnd
    rw [List.flatMap_cons, List.flatMap_cons]
    rcases List.mem_cons.1 hmem with rfl | hmem
    · rw [Function.update_self]
      have htl : tl.flatMap (Function.update f i (r :: f i)) = tl.flatMap f := by
        apply List.flatMap_congr
        intro k hk
        rw [Function.update_of_ne]
        rintro rfl; exact hnd.1 hk
      rw [htl]; simp
    · have hji : j ≠ i := by rintro rfl; exact hnd.1 hmem
      rw [Function.update_of_ne hji]
      have h1 : (f j ++ tl.flatMap (Function.update f i (r :: f i))).Perm (f j ++ (r :: tl.flatMap f)) :=
        List.Perm.append_left _ (ih hnd.2 hmem)
      have h2 : (f j ++ (r :: tl.flatMap f)).Perm (r :: (f j ++ tl.flatMap f)) := by
        rw [← List.singleton_append, ← List.append_assoc]
        exact List.Perm.append_right _ List.perm_append_comm |>.trans (by simp)
      exact h1.trans h2

omit [NeZero d] in
/-- **Filing a record permutes the records.** [folklore] -/
theorem perm_all_putF (st : FS d) (i : Fin 13) (r : BrickRec d) : (st.put i r).all.Perm (r :: st.all) := by
  unfold FS.all FS.put
  exact perm_flatMap_update st.segs i r _ (List.nodup_finRange 13) (List.mem_finRange i)

/-! ## The run state along the guarded run -/

variable (hY : Y.OK)

/-- The act behind a guarded placement: `gnext h = some β` means the plan's step at the state of
`h` is some `(act, i)` with `β = fplaceOf act`. [folklore] -/
theorem exists_fstep_of_gnext {h : BrickHist d} {β : BrickPos d}
    (hg : (flatKit Y hd hY).gnext Y.m Y.L Y.H a e τ h = some β) :
    ∃ act i, fstep' hd Y a e τ (ffold' hd Y a e τ h) = some (act, i) ∧ β = fplaceOf hd Y hY.hL hY.hH e τ act ∧
      h.length < FlatLayout.Rmax ∧ AllGood Y.m Y.L Y.H h := by
  obtain ⟨hlen, hgood, hnext, -, -⟩ := (flatKit Y hd hY).gnext_spec Y.m Y.L Y.H hg
  rw [flatKit_next, flatNext'] at hnext
  cases hs : fstep' hd Y a e τ (ffold' hd Y a e τ h) with
  | none => rw [hs] at hnext; exact absurd hnext (by simp)
  | some x =>
    obtain ⟨act, i⟩ := x
    rw [hs] at hnext
    simp only [Option.map_some, Option.some.injEq] at hnext
    exact ⟨act, i, rfl, hnext.symm, hlen, hgood⟩

/-- **The state along the guarded run**: it satisfies the invariant, and its records are exactly
those of the history (as a permutation). [cite: GrimmettPercolation1999, §7.3 pp. 171–174] -/
theorem run_stateF (hτ : FTAdm hd Y a e τ) (ω : BondConfig (Site d)) (n : ℕ) :
    FlatInv hd Y a e τ (ffold' hd Y a e τ ((flatKit Y hd hY).run Y.m Y.L Y.H a e τ n ω)) ∧
      (ffold' hd Y a e τ ((flatKit Y hd hY).run Y.m Y.L Y.H a e τ n ω)).all.Perm ((flatKit Y hd hY).run Y.m Y.L Y.H a e τ n ω) := by
  induction n with
  | zero =>
    refine ⟨flatInv_init hd Y a e τ, ?_⟩
    simp only [Kit.run, ffold', List.foldr_nil]
    simp [FS.all, FS.init]
  | succ n ih =>
    obtain ⟨hI, hperm⟩ := ih
    set h := (flatKit Y hd hY).run Y.m Y.L Y.H a e τ n ω with hh
    cases hg : (flatKit Y hd hY).gnext Y.m Y.L Y.H a e τ h with
    | none => rw [(flatKit Y hd hY).run_succ_of_none Y.m Y.L Y.H hg]; exact ⟨hI, hperm⟩
    | some β =>
      rw [(flatKit Y hd hY).run_succ_of_some Y.m Y.L Y.H hg]
      obtain ⟨act, i, hs, rfl, hlen, hgood⟩ := exists_fstep_of_gnext Y hd a e τ hY hg
      set r : BrickRec d := (fplaceOf hd Y hY.hL hY.hH e τ act, obs ω (suppP Y.m Y.L Y.H (fplaceOf hd Y hY.hL hY.hH e τ act))) with hr
      have hupd : ffold' hd Y a e τ (r :: h) = (ffold' hd Y a e τ h).put i r := by
        rw [ffold'_cons]; unfold fupdate'; rw [hs]
      rw [hupd]
      have hgoodall : ∀ r' ∈ (ffold' hd Y a e τ h).all, GoodRec Y.m Y.L Y.H r' := fun r' hr' => hgood r' (hperm.subset hr')
      exact ⟨flatInv_update hd Y hY.hL hY.hH a e τ hτ hI hgoodall hs _, (perm_all_putF _ i r).trans (hperm.cons r)⟩

/-- **The guards pass**: at the state of the guarded run, the support of the next placement of the
plan is fresh and lies in the zone. [cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
theorem guards_passF (hτ : FTAdm hd Y a e τ) (ω : BondConfig (Site d)) (n : ℕ) {act : Act d} {i : Fin 13}
    (hs : fstep' hd Y a e τ (ffold' hd Y a e τ ((flatKit Y hd hY).run Y.m Y.L Y.H a e τ n ω)) = some (act, i))
    (hgood : AllGood Y.m Y.L Y.H ((flatKit Y hd hY).run Y.m Y.L Y.H a e τ n ω)) :
    Disjoint (suppP Y.m Y.L Y.H (fplaceOf hd Y hY.hL hY.hH e τ act)) (histSupp Y.m Y.L Y.H ((flatKit Y hd hY).run Y.m Y.L Y.H a e τ n ω)) ∧
      suppP Y.m Y.L Y.H (fplaceOf hd Y hY.hL hY.hH e τ act) ⊆ fzoneF Y hd a e τ := by
  obtain ⟨hI, hperm⟩ := run_stateF Y hd a e τ hY hτ ω n
  set h := (flatKit Y hd hY).run Y.m Y.L Y.H a e τ n ω with hh
  set st := ffold' hd Y a e τ h with hst
  set r : BrickRec d := (fplaceOf hd Y hY.hL hY.hH e τ act, ∅) with hr
  have hgoodall : ∀ r' ∈ st.all, GoodRec Y.m Y.L Y.H r' := fun r' hr' => hgood r' (hperm.subset hr')
  have hI' : FlatInv hd Y a e τ (st.put i r) := flatInv_update hd Y hY.hL hY.hH a e τ hτ hI hgoodall hs ∅
  have hperm' : (st.put i r).all.Perm (r :: st.all) := perm_all_putF st i r
  have hpw := hI'.pairwise' hY hτ
  have hpw' : (r :: st.all).Pairwise (fun x y => PlateDisj Y.L Y.H x.1 y.1) := (hperm'.pairwise_iff (fun h => h.symm)).1 hpw
  rw [List.pairwise_cons] at hpw'
  constructor
  · rw [Finset.disjoint_left]
    intro z hz hz'
    rw [mem_histSupp_iff] at hz'
    obtain ⟨r', hr', hz'⟩ := hz'
    have hd' := hpw'.1 r' (hperm.symm.subset hr')
    exact Finset.disjoint_left.1 (disjoint_suppP_of_disjoint_boxOf hY.hL hY.hH hY.hL hY.hH hd') hz hz'
  · have hmem : r ∈ (st.put i r).all := hperm'.symm.subset List.mem_cons_self
    have key : suppP Y.m Y.L Y.H r.1 ⊆ fzoneF Y hd a e τ := FlatInv.suppP_subset_fzoneF hI' hY hτ hmem
    have hr1 : r.1 = fplaceOf hd Y hY.hL hY.hH e τ act := by rw [hr]
    rw [hr1] at key
    exact key

/-- **While the plan has a next act, every iteration of an all-good guarded run places a brick.**
[cite: GrimmettPercolation1999, §7.3 pp. 171–174] -/
theorem run_progressF (hτ : FTAdm hd Y a e τ) (ω : BondConfig (Site d)) (n : ℕ)
    (hgood : AllGood Y.m Y.L Y.H ((flatKit Y hd hY).run Y.m Y.L Y.H a e τ n ω)) :
    fstep' hd Y a e τ (ffold' hd Y a e τ ((flatKit Y hd hY).run Y.m Y.L Y.H a e τ n ω)) = none ∨
      ((flatKit Y hd hY).run Y.m Y.L Y.H a e τ n ω).length = n := by
  induction n with
  | zero => right; rfl
  | succ n ih =>
    set h := (flatKit Y hd hY).run Y.m Y.L Y.H a e τ n ω with hh
    have hgood_n : AllGood Y.m Y.L Y.H h := by
      cases hg : (flatKit Y hd hY).gnext Y.m Y.L Y.H a e τ h with
      | none => rw [(flatKit Y hd hY).run_succ_of_none Y.m Y.L Y.H hg] at hgood; exact hgood
      | some β => rw [(flatKit Y hd hY).run_succ_of_some Y.m Y.L Y.H hg, allGood_cons] at hgood; exact hgood.2
    rcases ih hgood_n with hnone | hlen
    · have hg : (flatKit Y hd hY).gnext Y.m Y.L Y.H a e τ h = none := by
        unfold Kit.gnext; rw [flatKit_next, flatNext', hnone]; simp
      rw [(flatKit Y hd hY).run_succ_of_none Y.m Y.L Y.H hg]; left; exact hnone
    · cases hs : fstep' hd Y a e τ (ffold' hd Y a e τ h) with
      | none =>
        have hg : (flatKit Y hd hY).gnext Y.m Y.L Y.H a e τ h = none := by
          unfold Kit.gnext; rw [flatKit_next, flatNext', hs]; simp
        rw [(flatKit Y hd hY).run_succ_of_none Y.m Y.L Y.H hg]; left; exact hs
      | some x =>
        obtain ⟨act, i⟩ := x
        obtain ⟨hdisj, hzone⟩ := guards_passF Y hd a e τ hY hτ ω n hs hgood_n
        obtain ⟨hI, hperm⟩ := run_stateF Y hd a e τ hY hτ ω n
        have hlenR := hI.all_length_lt hY hτ
        have hlt : h.length < (flatKit Y hd hY).R := by rw [flatKit_R, ← hperm.length_eq]; exact hlenR
        have hg : (flatKit Y hd hY).gnext Y.m Y.L Y.H a e τ h = some (fplaceOf hd Y hY.hL hY.hH e τ act) := by
          unfold Kit.gnext
          rw [if_pos ⟨hlt, hgood_n⟩, flatKit_next, flatNext', hs]
          simp only [Option.map_some]
          rw [if_pos ⟨hdisj, by rw [flatKit_zone]; exact hzone⟩]
        rw [(flatKit Y hd hY).run_succ_of_some Y.m Y.L Y.H hg]
        right; rw [List.length_cons, hlen]

/-- **At the end of an all-good guarded run of `R` iterations the plan is complete** (no next act).
[cite: GrimmettPercolation1999, §7.3 p. 174] -/
theorem fstep_eq_none_at_R (hτ : FTAdm hd Y a e τ) (ω : BondConfig (Site d))
    (hgood : AllGood Y.m Y.L Y.H ((flatKit Y hd hY).run Y.m Y.L Y.H a e τ FlatLayout.Rmax ω)) :
    fstep' hd Y a e τ (ffold' hd Y a e τ ((flatKit Y hd hY).run Y.m Y.L Y.H a e τ FlatLayout.Rmax ω)) = none := by
  rcases run_progressF Y hd a e τ hY hτ ω FlatLayout.Rmax hgood with h | hlen
  · exact h
  · exfalso
    obtain ⟨hI, hperm⟩ := run_stateF Y hd a e τ hY hτ ω FlatLayout.Rmax
    have hlenR := hI.all_length_lt hY hτ
    rw [hperm.length_eq, hlen] at hlenR
    exact lt_irrefl _ hlenR

end BGNd

end Percolation.Literature

end

/-!
# Part 2 (The flat gait, XXIX): the run, II — stopping, the outcome, connectivity along the run

Three facts about the run of the flat gait (Grimmett,
*Percolation*, 2nd ed. (1999), §7.3 pp. 171–174, case `H < L`): the plan has no next act only when
every segment is complete (`fstep'_eq_none_imp`), and then the outcome is defined, handing on the
exit tokens beyond the heads of the last trunk segment and of the two branches
(`flatFinish'_eq`); the act of the plan steps off one of the recorded bricks (`act_wfF`); and
along an all-good guarded run from a token with open seed every recorded brick has an open seed
joined to the token's centre (`conn_runF`).

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §7.3 pp. 171–174.
-/

noncomputable section

namespace Percolation.Literature

open LatticeModels Contour
open scoped Classical

namespace BGNd

variable {d : ℕ} [NeZero d]
variable (Y : FlatLayout) (hd : 3 ≤ d) (a : Site 2) (e : MDir) (τ : TTok d)

/-! ## The plan stops only when complete -/

omit [NeZero d] in
/-- The other plane axis of any axis differs from it. [folklore] -/
theorem pl_oth_plIdx_ne (x : Fin d) : pl hd (oth (plIdx hd x)) ≠ x := by
  intro h
  have : plIdx hd x = oth (plIdx hd x) := by conv_lhs => rw [← h]; rw [plIdx_pl]
  exact oth_ne _ this.symm

omit [NeZero d] in
/-- **The plan has no next act only when every segment is complete.** [cite: GrimmettPercolation1999, §7.3 p. 174] -/
theorem fstep'_eq_none_imp {st : FS d} (hs : fstep' hd Y a e τ st = none) :
    ∀ j : Fin 13, complete' hd Y a e τ (eJOf hd Y a e τ st) j (st.segs j) := by
  set ej := eJOf hd Y a e τ st with hej
  cases hc : curOf' hd Y a e τ ej st with
  | none => exact curOf_none hd Y a e τ hc
  | some i =>
    exfalso
    obtain ⟨hinc, hbefore⟩ := curOf_some hd Y a e τ hc
    unfold fstep' at hs
    simp only at hs
    rw [← hej, hc] at hs
    simp only [Option.map_eq_none_iff] at hs
    -- the start record exists for `i ≥ 1`
    have hstart : ∀ i : Fin 13, 0 < i.val → (∀ j : Fin 13, j < i → complete' hd Y a e τ ej j (st.segs j)) →
        ∃ s, startRec st i = some s := by
      intro i hi hb
      have hlt : startOf i < i := by
        have : (startOf i).val < i.val := by
          have := i.isLt
          fin_cases i <;> simp [startOf] at hi ⊢
        exact Fin.lt_def.2 this
      have hcpl := hb _ hlt
      rcases hh : st.segs (startOf i) with _ | ⟨s, tl⟩
      · rw [hh] at hcpl; simp [complete'] at hcpl
      · exact ⟨s, by rw [startRec_eq, hh]; rfl⟩
    -- case analysis on the kind of `i`
    fin_cases i <;>
      simp only [segAct', kindOf, fdirOf, Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val] at hs hinc
    · -- the lead-in
      rcases hl : st.segs 0 with _ | ⟨A, _ | ⟨A', _ | ⟨A'', tl⟩⟩⟩ <;> rw [hl] at hs hinc <;> simp [complete', kindOf] at hs hinc
    · obtain ⟨s, hsr⟩ := hstart 1 (by decide) hbefore
      rcases hl : st.segs 1 with _ | ⟨r, _ | ⟨r', tl⟩⟩ <;> simp only [hl, hsr] at hs
      · exact absurd hs (by simp)
      · split_ifs at hs
      · split_ifs at hs
    · obtain ⟨s, hsr⟩ := hstart 2 (by decide) hbefore
      rcases hl : st.segs 2 with _ | ⟨r, tl⟩ <;> simp only [hl, hsr] at hs <;> exact absurd hs (by simp)
    · obtain ⟨s, hsr⟩ := hstart 3 (by decide) hbefore
      rcases hl : st.segs 3 with _ | ⟨r, _ | ⟨r', tl⟩⟩ <;> simp only [hl, hsr] at hs hinc
      · exact absurd hs (by simp)
      · exact absurd hs (by simp)
      · simp [complete', kindOf] at hinc
    · obtain ⟨s, hsr⟩ := hstart 4 (by decide) hbefore
      rcases hl : st.segs 4 with _ | ⟨r, tl⟩ <;> simp only [hl, hsr] at hs <;> exact absurd hs (by simp)
    · obtain ⟨s, hsr⟩ := hstart 5 (by decide) hbefore
      rcases hl : st.segs 5 with _ | ⟨r, _ | ⟨r', tl⟩⟩ <;> simp only [hl, hsr] at hs hinc
      · exact absurd hs (by simp)
      · exact absurd hs (by simp)
      · simp [complete', kindOf] at hinc
    · obtain ⟨s, hsr⟩ := hstart 6 (by decide) hbefore
      rcases hl : st.segs 6 with _ | ⟨r, tl⟩ <;> simp only [hl, hsr] at hs <;> exact absurd hs (by simp)
    · obtain ⟨s, hsr⟩ := hstart 7 (by decide) hbefore
      rcases hl : st.segs 7 with _ | ⟨r, _ | ⟨r', tl⟩⟩ <;> simp only [hl, hsr] at hs hinc
      · exact absurd hs (by simp)
      · exact absurd hs (by simp)
      · simp [complete', kindOf] at hinc
    · obtain ⟨s, hsr⟩ := hstart 8 (by decide) hbefore
      rcases hl : st.segs 8 with _ | ⟨r, tl⟩ <;> simp only [hl, hsr] at hs <;> exact absurd hs (by simp)
    · obtain ⟨s, hsr⟩ := hstart 9 (by decide) hbefore
      rcases hl : st.segs 9 with _ | ⟨r, _ | ⟨r', tl⟩⟩ <;> simp only [hl, hsr] at hs hinc
      · exact absurd hs (by simp)
      · exact absurd hs (by simp)
      · simp [complete', kindOf] at hinc
    · obtain ⟨s, hsr⟩ := hstart 10 (by decide) hbefore
      rcases hl : st.segs 10 with _ | ⟨r, tl⟩ <;> simp only [hl, hsr] at hs <;> exact absurd hs (by simp)
    · obtain ⟨s, hsr⟩ := hstart 11 (by decide) hbefore
      rcases hl : st.segs 11 with _ | ⟨r, tl⟩ <;> simp only [hl, hsr] at hs <;> exact absurd hs (by simp)
    · obtain ⟨s, hsr⟩ := hstart 12 (by decide) hbefore
      rcases hl : st.segs 12 with _ | ⟨r, tl⟩ <;> simp only [hl, hsr] at hs <;> exact absurd hs (by simp)

/-- **The outcome at a complete state**: the three exit tokens beyond the heads of the last trunk
segment and of the two branches. [cite: GrimmettPercolation1999, §7.3 p. 174] -/
theorem flatFinish'_eq (hY : Y.OK) {h : BrickHist d} (hs : fstep' hd Y a e τ (ffold' hd Y a e τ h) = none) :
    ∃ rT r1 r2, (ffold' hd Y a e τ h).segs 10 ≠ [] ∧ ((ffold' hd Y a e τ h).segs 10).head? = some rT ∧
      ((ffold' hd Y a e τ h).segs 11).head? = some r1 ∧ ((ffold' hd Y a e τ h).segs 12).head? = some r2 ∧
      flatFinish' hd Y hY.hL hY.hH a e τ h = some (fun e' => if e' = eB1 e then fexitTok hd Y hY.hL hY.hH e (eB1 e) r1
        else if e' = eB2 e then fexitTok hd Y hY.hL hY.hH e (eB2 e) r2 else fexitTok hd Y hY.hL hY.hH e e rT) := by
  set st := ffold' hd Y a e τ h with hst
  have hc := fstep'_eq_none_imp Y hd a e τ hs
  have hne : ∀ j : Fin 13, st.segs j ≠ [] := fun j h0 => by have := hc j; rw [h0] at this; simp [complete'] at this
  obtain ⟨rT, tT, hT, hhT⟩ := exists_head_of_ne_nil (hne 10)
  obtain ⟨r1, t1, h1, hh1⟩ := exists_head_of_ne_nil (hne 11)
  obtain ⟨r2, t2, h2, hh2⟩ := exists_head_of_ne_nil (hne 12)
  refine ⟨rT, r1, r2, hne 10, hhT, hh1, hh2, ?_⟩
  have hcur : curOf' hd Y a e τ (eJOf hd Y a e τ st) st = none := by
    cases hq : curOf' hd Y a e τ (eJOf hd Y a e τ st) st with
    | none => rfl
    | some i => exact absurd (hc i) (curOf_some hd Y a e τ hq).1
  unfold flatFinish'
  simp only [← hst]
  rw [hcur, hT, h1, h2]

/-! ## The record of an act -/

/-- Well-formedness of an act relative to a state: a top stacking steps off one of the state's
records; a hop moreover onto a different axis. [folklore] -/
def ActWFF (st : FS d) : Act d → Prop
  | Act.first => True
  | Act.top r _ => r ∈ st.all
  | Act.side r i _ _ => r ∈ st.all ∧ i ≠ r.1.a

omit [NeZero d] in
/-- The start record of a segment is one of the records. [folklore] -/
theorem mem_all_of_startRec {st : FS d} {i : Fin 13} {s : BrickRec d} (h : startRec st i = some s) : s ∈ st.all := by
  rw [startRec_eq] at h
  exact mem_all_of_mem (k := startOf i) (List.mem_of_mem_head? h)

/-- **The act of the plan is well formed.** [folklore] -/
theorem act_wfF {st : FS d} (hI : FlatInv hd Y a e τ st) {act : Act d} {i : Fin 13}
    (hs : fstep' hd Y a e τ st = some (act, i)) : ActWFF st act := by
  obtain ⟨hcur, hsa⟩ := fstep_eq_some hd Y a e τ hs
  set ej := eJOf hd Y a e τ st with hej
  have h0x : ∀ x : Fin d, pl hd (oth (plIdx hd x)) ≠ x := pl_oth_plIdx_ne hd
  -- hops and top stackings off a record of the state are well formed
  have wf_diag : ∀ (σ : Fin 2 → ℤˣ) (zm : Option Bool) (r : BrickRec d), r ∈ st.all → ActWFF st (diagHop hd Y e σ zm r) :=
    fun σ zm r hr => ⟨hr, h0x _⟩
  -- the hop of a turn off its top plate is onto the other plane axis
  have turn_wf : ∀ (k : Fin 13) {σ σ₀ : Fin 2 → ℤˣ} {p : Fin 2} {r' : BrickRec d},
      (st.segs k ≠ [] → ∃ s0 ∈ (st.segs (startOf k)).head?, Turn hd Y e σ₀ σ p s0.1 (st.segs k)) → st.segs k = [r'] →
      ActWFF st (hop hd Y e σ none r' (pl hd (oth p)) (σ (oth p))) := by
    intro k σ σ₀ p r' hK hl
    rw [hl] at hK
    obtain ⟨s0, -, hT⟩ := hK (by simp)
    have hax := (hT.h0 (by simp)).axis
    have : legOf [r'] 0 = r'.1 := legOf_cons_length r' []
    rw [this] at hax
    refine ⟨mem_all_of_mem (k := k) (by rw [hl]; simp), ?_⟩
    rw [hax]; exact pl_ne_pl hd (oth_ne p)
  fin_cases i <;>
    simp only [segAct', kindOf, fdirOf, Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val] at hsa
  · -- the lead-in
    cases hsr : startRec st 0 <;> rcases hl : st.segs 0 with _ | ⟨A, _ | ⟨A', _ | ⟨A'', tl⟩⟩⟩ <;>
      simp only [hl, hsr, Option.some.injEq, reduceCtorEq] at hsa <;> subst hsa
    all_goals first | trivial | exact wf_diag _ _ A (mem_all_of_mem (k := 0) (by rw [hl]; simp))
  · -- the riser
    have hstart_ax : ∀ s0, startRec st 1 = some s0 → ax0 hd ≠ s0.1.a := by
      intro s0 hsr
      rw [startRec_eq] at hsr
      simp only [startOf, Fin.isValue, Matrix.cons_val] at hsr
      have hne : st.segs 0 ≠ [] := by intro h; rw [h] at hsr; simp at hsr
      have hK0 : SegOK hd Y e τ ej 0 (st.segs 0) (st.segs (startOf 0)) := hI.segOK 0
      simp only [SegOK, startOf, Fin.isValue, Matrix.cons_val] at hK0
      obtain ⟨hD, -, -⟩ := hK0 hne
      have := (hD.axis_sign (k := (st.segs 0).length - 1) (by have := List.length_pos_of_ne_nil hne; omega)).1
      rw [legOf_last_of_head hsr] at this
      rw [this]; exact (pl_ne_ax0 hd _).symm
    cases hsr : startRec st 1 <;> rcases hl : st.segs 1 with _ | ⟨r, _ | ⟨r', tl⟩⟩ <;>
      simp only [hl, hsr, Option.some.injEq, reduceCtorEq] at hsa
    · by_cases hax : r.1.a = ax0 hd <;> simp only [hax, if_true, if_false, Option.some.injEq, reduceCtorEq] at hsa
      subst hsa; exact ⟨mem_all_of_mem (k := 1) (by rw [hl]; simp), Ne.symm hax⟩
    · by_cases hax : r.1.a = ax0 hd <;> simp only [hax, if_true, if_false, Option.some.injEq] at hsa <;> subst hsa
      · exact ⟨mem_all_of_mem (k := 1) (by rw [hl]; simp), by rw [hax]; exact pl_ne_ax0 hd _⟩
      · exact ⟨mem_all_of_mem (k := 1) (by rw [hl]; simp), Ne.symm hax⟩
    · subst hsa; exact ⟨mem_all_of_startRec hsr, hstart_ax _ hsr⟩
    · by_cases hax : r.1.a = ax0 hd <;> simp only [hax, if_true, if_false, Option.some.injEq] at hsa <;> subst hsa
      · exact ⟨mem_all_of_mem (k := 1) (by rw [hl]; simp), by rw [hax]; exact pl_ne_ax0 hd _⟩
      · exact ⟨mem_all_of_mem (k := 1) (by rw [hl]; simp), Ne.symm hax⟩
    · by_cases hax : r.1.a = ax0 hd <;> simp only [hax, if_true, if_false, Option.some.injEq] at hsa <;> subst hsa
      · exact ⟨mem_all_of_mem (k := 1) (by rw [hl]; simp), by rw [hax]; exact pl_ne_ax0 hd _⟩
      · exact ⟨mem_all_of_mem (k := 1) (by rw [hl]; simp), Ne.symm hax⟩
  · cases hsr : startRec st 2 <;> rcases hl : st.segs 2 with _ | ⟨r, tl⟩ <;> simp only [hl, hsr, Option.some.injEq, reduceCtorEq] at hsa <;>
      subst hsa
    · exact wf_diag _ _ r (mem_all_of_mem (k := 2) (by rw [hl]; simp))
    · exact wf_diag _ _ _ (mem_all_of_startRec hsr)
    · exact wf_diag _ _ r (mem_all_of_mem (k := 2) (by rw [hl]; simp))
  · have hK : SegOK hd Y e τ ej 3 (st.segs 3) (st.segs (startOf 3)) := hI.segOK 3
    simp only [SegOK, Fin.isValue] at hK
    cases hsr : startRec st 3 <;> rcases hl : st.segs 3 with _ | ⟨r', _ | ⟨r'', tl⟩⟩ <;>
      simp only [hl, hsr, Option.some.injEq, reduceCtorEq] at hsa <;> subst hsa
    · exact turn_wf 3 hK hl
    · exact mem_all_of_startRec hsr
    · exact turn_wf 3 hK hl
  · cases hsr : startRec st 4 <;> rcases hl : st.segs 4 with _ | ⟨r, tl⟩ <;> simp only [hl, hsr, Option.some.injEq, reduceCtorEq] at hsa <;>
      subst hsa
    · exact wf_diag _ _ r (mem_all_of_mem (k := 4) (by rw [hl]; simp))
    · exact wf_diag _ _ _ (mem_all_of_startRec hsr)
    · exact wf_diag _ _ r (mem_all_of_mem (k := 4) (by rw [hl]; simp))
  · have hK : SegOK hd Y e τ ej 5 (st.segs 5) (st.segs (startOf 5)) := hI.segOK 5
    simp only [SegOK, Fin.isValue] at hK
    cases hsr : startRec st 5 <;> rcases hl : st.segs 5 with _ | ⟨r', _ | ⟨r'', tl⟩⟩ <;>
      simp only [hl, hsr, Option.some.injEq, reduceCtorEq] at hsa <;> subst hsa
    · exact turn_wf 5 hK hl
    · exact mem_all_of_startRec hsr
    · exact turn_wf 5 hK hl
  · cases hsr : startRec st 6 <;> rcases hl : st.segs 6 with _ | ⟨r, tl⟩ <;> simp only [hl, hsr, Option.some.injEq, reduceCtorEq] at hsa <;>
      subst hsa
    · exact wf_diag _ _ r (mem_all_of_mem (k := 6) (by rw [hl]; simp))
    · exact wf_diag _ _ _ (mem_all_of_startRec hsr)
    · exact wf_diag _ _ r (mem_all_of_mem (k := 6) (by rw [hl]; simp))
  · have hK : SegOK hd Y e τ ej 7 (st.segs 7) (st.segs (startOf 7)) := hI.segOK 7
    simp only [SegOK, Fin.isValue] at hK
    cases hsr : startRec st 7 <;> rcases hl : st.segs 7 with _ | ⟨r', _ | ⟨r'', tl⟩⟩ <;>
      simp only [hl, hsr, Option.some.injEq, reduceCtorEq] at hsa <;> subst hsa
    · exact turn_wf 7 hK hl
    · exact mem_all_of_startRec hsr
    · exact turn_wf 7 hK hl
  · cases hsr : startRec st 8 <;> rcases hl : st.segs 8 with _ | ⟨r, tl⟩ <;> simp only [hl, hsr, Option.some.injEq, reduceCtorEq] at hsa <;>
      subst hsa
    · exact wf_diag _ _ r (mem_all_of_mem (k := 8) (by rw [hl]; simp))
    · exact wf_diag _ _ _ (mem_all_of_startRec hsr)
    · exact wf_diag _ _ r (mem_all_of_mem (k := 8) (by rw [hl]; simp))
  · have hK : SegOK hd Y e τ ej 9 (st.segs 9) (st.segs (startOf 9)) := hI.segOK 9
    simp only [SegOK, Fin.isValue] at hK
    cases hsr : startRec st 9 <;> rcases hl : st.segs 9 with _ | ⟨r', _ | ⟨r'', tl⟩⟩ <;>
      simp only [hl, hsr, Option.some.injEq, reduceCtorEq] at hsa <;> subst hsa
    · exact turn_wf 9 hK hl
    · exact mem_all_of_startRec hsr
    · exact turn_wf 9 hK hl
  · cases hsr : startRec st 10 <;> rcases hl : st.segs 10 with _ | ⟨r, tl⟩ <;> simp only [hl, hsr, Option.some.injEq, reduceCtorEq] at hsa <;>
      subst hsa
    · exact wf_diag _ _ r (mem_all_of_mem (k := 10) (by rw [hl]; simp))
    · exact wf_diag _ _ _ (mem_all_of_startRec hsr)
    · exact wf_diag _ _ r (mem_all_of_mem (k := 10) (by rw [hl]; simp))
  · cases hsr : startRec st 11 <;> rcases hl : st.segs 11 with _ | ⟨r, tl⟩ <;> simp only [hl, hsr, Option.some.injEq, reduceCtorEq] at hsa <;>
      subst hsa
    · exact wf_diag _ _ r (mem_all_of_mem (k := 11) (by rw [hl]; simp))
    · exact wf_diag _ _ _ (mem_all_of_startRec hsr)
    · exact wf_diag _ _ r (mem_all_of_mem (k := 11) (by rw [hl]; simp))
  · cases hsr : startRec st 12 <;> rcases hl : st.segs 12 with _ | ⟨r, tl⟩ <;> simp only [hl, hsr, Option.some.injEq, reduceCtorEq] at hsa <;>
      subst hsa
    · exact wf_diag _ _ r (mem_all_of_mem (k := 12) (by rw [hl]; simp))
    · exact wf_diag _ _ _ (mem_all_of_startRec hsr)
    · exact wf_diag _ _ r (mem_all_of_mem (k := 12) (by rw [hl]; simp))

/-! ## Connectivity along the run -/

variable (hY : Y.OK)

/-- Earlier runs are all good if a later one is. [folklore] -/
theorem allGood_run_of_leF {k n : ℕ} (hkn : k ≤ n) (ω : BondConfig (Site d))
    (h : AllGood Y.m Y.L Y.H ((flatKit Y hd hY).run Y.m Y.L Y.H a e τ n ω)) : AllGood Y.m Y.L Y.H ((flatKit Y hd hY).run Y.m Y.L Y.H a e τ k ω) := by
  induction n with
  | zero => have : k = 0 := by omega
            subst this; exact h
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le hkn with rfl | hlt
    · exact h
    · apply ih (by omega)
      cases hg : (flatKit Y hd hY).gnext Y.m Y.L Y.H a e τ ((flatKit Y hd hY).run Y.m Y.L Y.H a e τ n ω) with
      | none => rwa [(flatKit Y hd hY).run_succ_of_none Y.m Y.L Y.H hg] at h
      | some β => rw [(flatKit Y hd hY).run_succ_of_some Y.m Y.L Y.H hg, allGood_cons] at h; exact h.2

/-- **Connectivity along the run**: from an admissible token with open seed, along an all-good
guarded run, every recorded brick has an open seed and its base centre is joined to the token's
centre by an open path. [cite: GrimmettPercolation1999, §7.3 pp. 172–173 (A), (B)] -/
theorem conn_runF (hτ : FTAdm hd Y a e τ) {ω : BondConfig (Site d)} (hpre : IsSeed ω (square τ.ax Y.m τ.pos)) (n : ℕ)
    (hgood : AllGood Y.m Y.L Y.H ((flatKit Y hd hY).run Y.m Y.L Y.H a e τ n ω)) :
    ∀ r ∈ (flatKit Y hd hY).run Y.m Y.L Y.H a e τ n ω,
      IsSeed ω (square r.1.a Y.m r.1.b) ∧ (openGraph ω).Reachable τ.pos r.1.b := by
  induction n with
  | zero => intro r hr; exact absurd hr (by simp [Kit.run])
  | succ n ih =>
    set h := (flatKit Y hd hY).run Y.m Y.L Y.H a e τ n ω with hh
    have hgood_n : AllGood Y.m Y.L Y.H h := allGood_run_of_leF Y hd a e τ hY (Nat.le_succ n) ω hgood
    have ih' := ih hgood_n
    cases hg : (flatKit Y hd hY).gnext Y.m Y.L Y.H a e τ h with
    | none => rw [(flatKit Y hd hY).run_succ_of_none Y.m Y.L Y.H hg]; exact ih'
    | some β =>
      rw [(flatKit Y hd hY).run_succ_of_some Y.m Y.L Y.H hg]
      obtain ⟨act, i, hs, rfl, -, -⟩ := exists_fstep_of_gnext Y hd a e τ hY hg
      obtain ⟨hI, hperm⟩ := run_stateF Y hd a e τ hY hτ ω n
      have hwf := act_wfF Y hd a e τ hI hs
      intro r hr
      rcases List.mem_cons.1 hr with rfl | hr
      · simp only
        have hfacts : ∀ r₀ ∈ (ffold' hd Y a e τ h).all, GoodRec Y.m Y.L Y.H r₀ ∧ cfgOf r₀ ⊆ ω ∧
            IsSeed ω (square r₀.1.a Y.m r₀.1.b) ∧ (openGraph ω).Reachable τ.pos r₀.1.b := by
          intro r₀ hr₀
          have hr₀h : r₀ ∈ h := hperm.subset hr₀
          refine ⟨hgood_n r₀ hr₀h, ?_, ih' r₀ hr₀h⟩
          have hobs := (flatKit Y hd hY).run_obs Y.m Y.L Y.H hr₀h
          have : r₀ = (r₀.1, obs ω (suppP Y.m Y.L Y.H r₀.1)) := by rw [← hobs]
          rw [this]; exact cfgOf_obs_subset _ _ _
        cases act with
        | first =>
          simp only [fplaceOf]
          exact ⟨hpre, SimpleGraph.Reachable.refl _⟩
        | top r₀ sg =>
          obtain ⟨hg0, hsub, hseed, hreach⟩ := hfacts r₀ hwf
          simp only [fplaceOf]
          exact ⟨(isSeed_tStep hY.hL hY.hH hg0 sg).mono hsub, hreach.trans (reachable_tStep hY.hL hY.hH hg0 sg hsub hseed)⟩
        | side r₀ j u sg =>
          obtain ⟨hmem, hj⟩ : r₀ ∈ (ffold' hd Y a e τ h).all ∧ j ≠ r₀.1.a := hwf
          obtain ⟨hg0, hsub, hseed, hreach⟩ := hfacts r₀ hmem
          simp only [fplaceOf]
          exact ⟨(isSeed_sStep hY.hL hY.hH hg0 hj u sg).mono hsub, hreach.trans (reachable_sStep hY.hL hY.hH hg0 hj u sg hsub hseed)⟩
      · exact ih' r hr

end BGNd

end Percolation.Literature

end

/-!
# Part 3 (The flat gait, XXX): the run, III — the exit tokens are admissible

The exit tokens of a complete run of the flat gait
(Grimmett, *Percolation*, 2nd ed. (1999), §7.3 p. 174 (D), case `H < L`) — the bases of the next
hops beyond the heads of the last trunk segment and of the two branches (`fexitTok`) — are
admissible tokens of the target cell for the onward attempts (`FlatInv.ftAdm_exit_T`,
`FlatInv.ftAdm_exit_B1`, `FlatInv.ftAdm_exit_B2`): the stopping rules (no room at the head, room
one plate earlier) put them in the forward window `[D - 2U, D - 1]` before the next face, the
lateral bounds of the trunk and of the branches within `ρ_p` of the lanes, and the heights within
`ρ_v` of the layer. The position of an exit token is that of a diagonal hop (`exit_coords`).

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §7.3 pp. 171–174.
-/

noncomputable section

namespace Percolation.Literature

open LatticeModels Contour
open scoped Classical

namespace BGNd

variable {d : ℕ} [NeZero d]
variable (Y : FlatLayout) (hd : 3 ≤ d) (hL : Y.m + 1 ≤ Y.L) (hH : 2 * Y.m + 2 ≤ Y.H) (a : Site 2) (e : MDir) (τ : TTok d)

/-! ## The position of an exit token -/

/-- The exit token beyond `r` towards `e'`: position the base of the next diagonal hop, axis the
other plane axis, source `e`. [folklore] -/
theorem fexitTok_eq (e' : MDir) (r : BrickRec d) :
    (fexitTok hd Y hL hH e e' r).pos = (sStep hL hH r (pl hd (oth (plIdx hd r.1.a))) (dsg e' (oth (plIdx hd r.1.a))) (hreq hd Y e (dsg e') none r.1.b)).b ∧
      (fexitTok hd Y hL hH e e' r).ax = pl hd (oth (plIdx hd r.1.a)) ∧ (fexitTok hd Y hL hH e e' r).src = some e := ⟨rfl, rfl, rfl⟩

/-- **Coordinates of an exit token** beyond a good record `r` of plane axis `p` and sign `dsg e' p`:
one hop on along the other plane axis, between `m + 1` and `H - m - 1` on along `p`, the height
within `max(previous deviation, L')` of the layer, idle coordinates within `max(previous, L')`. [cite: GrimmettPercolation1999, §7.3 p. 174 (D)] -/
theorem exit_coords {e' : MDir} {r : BrickRec d} (hg : GoodRec Y.m Y.L Y.H r) {p : Fin 2} (ha : r.1.a = pl hd p) (hs : r.1.s = dsg e' p) :
    ox hd (dsg e') (oth p) (fexitTok hd Y hL hH e e' r).pos = ox hd (dsg e') (oth p) r.1.b + Y.U ∧
      (Y.m : ℤ) + 1 ≤ ox hd (dsg e') p (fexitTok hd Y hL hH e e' r).pos - ox hd (dsg e') p r.1.b ∧
      ox hd (dsg e') p (fexitTok hd Y hL hH e e' r).pos - ox hd (dsg e') p r.1.b ≤ (Y.H : ℤ) - Y.m - 1 ∧
      |(fexitTok hd Y hL hH e e' r).pos (ax0 hd) - zN Y e| ≤ max |r.1.b (ax0 hd) - zN Y e| Y.Lp ∧
      (∀ i, Idle hd i → |(fexitTok hd Y hL hH e e' r).pos i| ≤ max |r.1.b i| Y.Lp) ∧
      (fexitTok hd Y hL hH e e' r).ax = pl hd (oth p) := by
  obtain ⟨hpos, hax, -⟩ := fexitTok_eq Y hd hL hH e e' r
  rw [ha, plIdx_pl] at hpos hax
  have hD := dHop_sStep hd Y hL hH e hg (dsg e') none (q := oth p) (by rw [oth_oth]; exact ha) (by rw [oth_oth]; exact hs)
  have hface := hD.face; have hdrift := hD.drift; have hzt := hD.zt rfl; have hidle := hD.idle
  simp only [oth_oth] at hdrift
  rw [← hpos] at hface hdrift hzt hidle
  refine ⟨?_, ?_, ?_, hzt, hidle, hax⟩
  · unfold ox; rw [hface, mul_add, ← mul_assoc, units_sq, one_mul]
  · unfold ox; rw [mul_sub] at hdrift; exact hdrift.1
  · unfold ox; rw [mul_sub] at hdrift; exact hdrift.2

omit [NeZero d] in
/-- Diagonal coordinates are `1`-Lipschitz in each plane coordinate. [folklore] -/
theorem abs_Uc_sub_le (i : Fin 2) (x y : Site d) : |Uc hd i x - Uc hd i y| ≤ |x (pl hd 0) - y (pl hd 0)| + |x (pl hd 1) - y (pl hd 1)| := by
  unfold Uc
  have e1 : x (pl hd 0) + (if i = 0 then (1 : ℤ) else -1) * x (pl hd 1) - (y (pl hd 0) + (if i = 0 then (1 : ℤ) else -1) * y (pl hd 1)) =
      (x (pl hd 0) - y (pl hd 0)) + (if i = 0 then (1 : ℤ) else -1) * (x (pl hd 1) - y (pl hd 1)) := by ring
  rw [e1]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul]
  have : |(if i = 0 then (1 : ℤ) else -1)| = 1 := by split_ifs <;> simp
  rw [this, one_mul]

omit [NeZero d] in
/-- The plane displacement of an exit token from its record: `U` along one oriented coordinate,
between `A ≥ 0` and `B` along the other, is at most `U + B` in total. [folklore] -/
theorem exit_plane_abs {σ : Fin 2 → ℤˣ} {x y : Site d} {p : Fin 2} {U A B : ℤ} (hf : ox hd σ (oth p) x = ox hd σ (oth p) y + U)
    (h1 : A ≤ ox hd σ p x - ox hd σ p y) (h2 : ox hd σ p x - ox hd σ p y ≤ B) (hU : 0 ≤ U) (hA : 0 ≤ A) :
    |x (pl hd 0) - y (pl hd 0)| + |x (pl hd 1) - y (pl hd 1)| ≤ U + B := by
  have key : ∀ i, |x (pl hd i) - y (pl hd i)| = |ox hd σ i x - ox hd σ i y| := fun i => by
    unfold ox; rw [← mul_sub, abs_mul]
    have : |((σ i : ℤˣ) : ℤ)| = 1 := by rcases Int.units_eq_one_or (σ i) with h | h <;> simp [h]
    rw [this, one_mul]
  rw [key 0, key 1]
  have ho : |ox hd σ (oth p) x - ox hd σ (oth p) y| = U := by rw [hf, add_sub_cancel_left, abs_of_nonneg hU]
  have hp' : |ox hd σ p x - ox hd σ p y| ≤ B := by rw [abs_of_nonneg (by linarith)]; exact h2
  rcases Fin.exists_fin_two.1 ⟨p, rfl⟩ with hp | hp
  · rw [hp] at hp' ho; rw [show oth (0 : Fin 2) = 1 from rfl] at ho; linarith
  · rw [hp] at hp' ho; rw [show oth (1 : Fin 2) = 0 from rfl] at ho; linarith

/-! ## The straight exit token -/

variable {Y hd a e τ} {st : FS d}

/-- The head of a complete leg segment `k ∈ {10, 11, 12}` and its stop. [folklore] -/
theorem complete_leg_head (k : Fin 13) (hk : k = 10 ∨ k = 11 ∨ k = 12)
    (hc : complete' hd Y a e τ (eJOf hd Y a e τ st) k (st.segs k)) :
    ∃ r, (st.segs k).head? = some r ∧ r ∈ st.segs k ∧ legOf (st.segs k) ((st.segs k).length - 1) = r.1 ∧
      ¬froom hd Y a e (fdirOf e (eJOf hd Y a e τ st) k) r.1.b := by
  rcases hl : st.segs k with _ | ⟨r, tl⟩
  · rw [hl] at hc; simp [complete'] at hc
  · refine ⟨r, rfl, by simp, by rw [← hl]; exact legOf_last_of_head (by rw [hl]; rfl), ?_⟩
    have h4 : k ≠ 4 := by rcases hk with rfl | rfl | rfl <;> decide
    have h6 : k ≠ 6 := by rcases hk with rfl | rfl | rfl <;> decide
    have h8 : k ≠ 8 := by rcases hk with rfl | rfl | rfl <;> decide
    have hkind : kindOf e (eJOf hd Y a e τ st) k = Kind.leg := by rcases hk with rfl | rfl | rfl <;> rfl
    rw [hl] at hc
    simp only [complete', hkind, legStop, if_neg h4, if_neg h6, if_neg h8] at hc
    exact hc.2.1

/-- **The straight exit token is admissible** for the onward attempt along `e` from the target cell. [cite: GrimmettPercolation1999, §7.3 p. 174 (D)] -/
theorem FlatInv.ftAdm_exit_T (hI : FlatInv hd Y a e τ st) (hY : Y.OK) (hτ : FTAdm hd Y a e τ) (hgood : ∀ r ∈ st.all, GoodRec Y.m Y.L Y.H r)
    (hc : ∀ j : Fin 13, complete' hd Y a e τ (eJOf hd Y a e τ st) j (st.segs j)) {rT : BrickRec d} (hrT : (st.segs 10).head? = some rT) :
    FTAdm hd Y (ftgt a e) e (fexitTok hd Y hY.hL hY.hH e e rT) := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  have hH8 : 8 * ((Y.H : ℤ) + 1) ≤ Y.U := hflat
  obtain ⟨r', hr', hmem, hlast, hstop⟩ := complete_leg_head 10 (Or.inl rfl) (hc 10)
  have hrr : r' = rT := by rw [hrT] at hr'; simpa using hr'.symm
  subst hrr
  have h10 : st.segs 10 ≠ [] := List.ne_nil_of_mem hmem
  -- the head: a plate of the diagonal leg of signs `dsg e`
  have hK : SegOK hd Y e τ (eJOf hd Y a e τ st) 10 (st.segs 10) (st.segs (startOf 10)) := hI.segOK 10
  simp only [SegOK, startOf, Fin.isValue, Matrix.cons_val] at hK
  obtain ⟨-, -, q, hD, -⟩ := hK h10
  obtain ⟨ha, hs⟩ := hD.axis_sign (k := (st.segs 10).length - 1) (by have := List.length_pos_of_ne_nil h10; omega)
  rw [hlast] at ha hs
  generalize hp : qAt q ((st.segs 10).length - 1) = p at ha hs
  have hg : GoodRec Y.m Y.L Y.H r' := hgood r' (mem_all_of_mem hmem)
  obtain ⟨hface, ht1, ht2, hzt, hidle, hax⟩ := exit_coords Y hd hY.hL hY.hH e hg ha hs
  set pos := (fexitTok hd Y hY.hL hY.hH e e r').pos with hposdef
  -- forward: `upar(pos) = upar(r) + U + t`
  have hupar : upar hd (dsg e) pos = upar hd (dsg e) r'.1.b + Y.U + (ox hd (dsg e) p pos - ox hd (dsg e) p r'.1.b) := by
    unfold upar; rcases Fin.exists_fin_two.1 ⟨p, rfl⟩ with h | h <;> rw [h] at hface ⊢ <;>
      simp only [show oth (0 : Fin 2) = 1 from rfl, show oth (1 : Fin 2) = 0 from rfl] at hface <;> linarith
  have hstop' : Y.Df - 3 * Y.U ≤ upar hd (dsg e) r'.1.b - (sgOf e : ℤ) * Y.ctr (ftgt a e) e.1 := by
    have := (froom_e_iff Y a e hd r'.1.b).not.1 hstop; push Not at this; exact this
  obtain ⟨-, hhi, hlat⟩ := hI.abs_T hY hτ r' (by simp [hmem])
  have hz := hI.z_after hY hτ 10 (by decide) r' hmem
  have hidle0 := hI.idle_all hτ (mem_all_of_mem hmem)
  obtain ⟨-, hax', hsrc⟩ := fexitTok_eq Y hd hY.hL hY.hH e e r'
  refine ⟨?_, ?_, ?_, fun d' hd' => ?_, fun i hi => ?_, by rw [hsrc]; simp⟩
  · rw [hax]; rcases Fin.exists_fin_two.1 ⟨oth p, rfl⟩ with h | h <;> rw [h] <;> simp
  · -- the forward window
    rw [mul_sub, upar_dsg]
    change Y.Df - 2 * Y.U ≤ upar hd (dsg e) pos - (sgOf e : ℤ) * Y.ctr (ftgt a e) e.1 ∧ upar hd (dsg e) pos - (sgOf e : ℤ) * Y.ctr (ftgt a e) e.1 ≤ Y.Df - 1
    rw [hupar]
    constructor <;> linarith [hstop', hhi, ht1, ht2, hH8, hm0]
  · -- the lateral window
    have h1 := abs_Uc_sub_le hd (latDir e true).1 pos r'.1.b
    have h2 := exit_plane_abs hd hface ht1 ht2 hU.le (by positivity)
    have : |Uc hd (latDir e true).1 pos - Y.lane (ftgt a e) e| ≤ |Uc hd (latDir e true).1 pos - Uc hd (latDir e true).1 r'.1.b| +
        |Uc hd (latDir e true).1 r'.1.b - Y.lane (ftgt a e) e| := abs_sub_le _ _ _
    unfold FlatLayout.ρp; linarith
  · -- the height
    rw [hsrc] at hd'; simp only [Option.some.injEq] at hd'; subst hd'
    rw [← hposdef]; change |pos (ax0 hd) - zN Y e| ≤ Y.ρv
    refine hzt.trans ?_
    unfold FlatLayout.ρv; rw [max_le_iff]; constructor <;> linarith
  · rw [← hposdef]; refine (hidle i hi).trans ?_; rw [max_le_iff]; exact ⟨hidle0 i hi, le_rfl⟩

/-! ## The lateral exit tokens -/

omit [NeZero d] in
/-- The forward diagonal coordinate is `1`-Lipschitz in each plane coordinate. [folklore] -/
theorem abs_upar_sub_le (σ : Fin 2 → ℤˣ) (x y : Site d) : |upar hd σ x - upar hd σ y| ≤ |x (pl hd 0) - y (pl hd 0)| + |x (pl hd 1) - y (pl hd 1)| := by
  have key : ∀ i, |x (pl hd i) - y (pl hd i)| = |ox hd σ i x - ox hd σ i y| := fun i => by
    unfold ox; rw [← mul_sub, abs_mul]
    have : |((σ i : ℤˣ) : ℤ)| = 1 := by rcases Int.units_eq_one_or (σ i) with h | h <;> simp [h]
    rw [this, one_mul]
  rw [key 0, key 1]
  unfold upar
  calc _ = |(ox hd σ 0 x - ox hd σ 0 y) + (ox hd σ 1 x - ox hd σ 1 y)| := by ring_nf
    _ ≤ _ := abs_add_le _ _

/-- **The first lateral exit token is admissible** for the onward attempt along `eB1 e`. [cite: GrimmettPercolation1999, §7.3 p. 174 (D)] -/
theorem FlatInv.ftAdm_exit_B1 (hI : FlatInv hd Y a e τ st) (hY : Y.OK) (hτ : FTAdm hd Y a e τ) (hgood : ∀ r ∈ st.all, GoodRec Y.m Y.L Y.H r)
    (hc : ∀ j : Fin 13, complete' hd Y a e τ (eJOf hd Y a e τ st) j (st.segs j)) {r1 : BrickRec d} (hr1 : (st.segs 11).head? = some r1) :
    FTAdm hd Y (ftgt a e) (eB1 e) (fexitTok hd Y hY.hL hY.hH e (eB1 e) r1) := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  have hH8 : 8 * ((Y.H : ℤ) + 1) ≤ Y.U := hflat
  have hD : Y.Df = 4096 * Y.U := rfl
  have hΛ : Y.lam = 1280 * Y.U := rfl
  have hΛJ : Y.lamJ = 256 * Y.U := rfl
  obtain ⟨r', hr', hmem, hlast, hstop⟩ := complete_leg_head 11 (Or.inr (Or.inl rfl)) (hc 11)
  have hrr : r' = r1 := by rw [hr1] at hr'; simpa using hr'.symm
  subst hrr
  have h11 : st.segs 11 ≠ [] := List.ne_nil_of_mem hmem
  -- the head: a plate of the branch, a diagonal leg of signs `dsg (eB1 e)` from the fork's hop `γ`
  obtain ⟨γ, hγ, -, hBE⟩ := hI.frame_branch.1 h11
  have hlen : (st.segs 11 ++ [γ]).length = (st.segs 11).length + 1 := by simp
  have hpos11 := List.length_pos_of_ne_nil h11
  obtain ⟨ha, hs⟩ := hBE.axis_sign (k := (st.segs 11).length - 1 + 1) (by rw [hlen]; omega)
  rw [legOf_append_singleton_succ, hlast] at ha hs
  generalize hp : qAt (oth (p1 e)) ((st.segs 11).length - 1 + 1) = p at ha hs
  have hg : GoodRec Y.m Y.L Y.H r' := hgood r' (mem_all_of_mem hmem)
  obtain ⟨hface, ht1, ht2, hzt, hidle, hax⟩ := exit_coords Y hd hY.hL hY.hH e hg ha hs
  set pos := (fexitTok hd Y hY.hL hY.hH e (eB1 e) r').pos with hposdef
  -- the branch's forward coordinate is `-vperp`, its lateral one `-upar` (index `0` flipped)
  obtain ⟨⟨hflip1, hkeep1⟩, -⟩ := flip_keep_B e
  change dsg (eB1 e) 0 = -dsg e 0 at hflip1
  have conv := fun b => upar_vperp_flip0 hd (σ := dsg e) (σ' := dsg (eB1 e)) hflip1 hkeep1 b
  have hupar : upar hd (dsg (eB1 e)) pos = upar hd (dsg (eB1 e)) r'.1.b + Y.U + (ox hd (dsg (eB1 e)) p pos - ox hd (dsg (eB1 e)) p r'.1.b) := by
    unfold upar; rcases Fin.exists_fin_two.1 ⟨p, rfl⟩ with h | h <;> rw [h] at hface ⊢ <;>
      simp only [show oth (0 : Fin 2) = 1 from rfl, show oth (1 : Fin 2) = 0 from rfl] at hface <;> linarith
  have hss : (sgOf e : ℤ) * (sgOf e : ℤ) = 1 := by rcases Int.units_eq_one_or (sgOf e) with h' | h' <;> simp [h']
  have hsv : ∀ b, (sgOf e : ℤ) * Uc hd (latDir e true).1 b = vperp hd (dsg e) b := fun b => by
    rw [Uc_lat_eq_vperp, ← mul_assoc, hss, one_mul]
  -- the stop: no room at the head
  have hstop' : Y.Df - 3 * Y.U ≤ (sgOf e : ℤ) * Y.ctr (ftgt a e) (latDir e true).1 - vperp hd (dsg e) r'.1.b := by
    have := ((froom_eB_iff Y a e hd r'.1.b).1).not.1 hstop; push Not at this; rw [hsv] at this; exact this
  -- room one plate earlier (or the fork's hop far inside)
  have hroom : (sgOf e : ℤ) * Y.ctr (ftgt a e) (latDir e true).1 - vperp hd (dsg e) r'.1.b ≤ Y.Df - 2 * Y.U + Y.H - Y.m - 2 := by
    rcases Nat.lt_or_ge 1 (st.segs 11).length with h2 | h2
    · have hst := hI.B1_stage (j := (st.segs 11).length - 2) (by omega)
      have := ((froom_eB_iff Y a e hd _).1).1 hst
      rw [hsv] at this
      have hstep := hI.B1_step (j := (st.segs 11).length - 2) (by omega)
      rw [show (st.segs 11).length - 2 + 1 = (st.segs 11).length - 1 by omega, hlast] at hstep
      linarith
    · have hl1 : (st.segs 11).length = 1 := by omega
      obtain ⟨-, hhi, -⟩ := hI.win_B1 hY hγ (k := 0) hpos11
      have h0 : legOf (st.segs 11) 0 = r'.1 := by rw [show (0 : ℕ) = (st.segs 11).length - 1 by omega]; exact hlast
      rw [h0] at hhi
      obtain ⟨-, -, hγlat⟩ := hI.abs_G1 hY hτ γ (List.mem_of_mem_head? hγ)
      have hγv : (sgOf e : ℤ) * Y.lane (ftgt a e) e - 534 * Y.U ≤ vperp hd (dsg e) γ.1.b := by
        have e1 : vperp hd (dsg e) γ.1.b - (sgOf e : ℤ) * Y.lane (ftgt a e) e = (sgOf e : ℤ) * (Uc hd (latDir e true).1 γ.1.b - Y.lane (ftgt a e) e) := by
          rw [mul_sub, hsv]
        have hs1 : |(sgOf e : ℤ)| = 1 := by rcases Int.units_eq_one_or (sgOf e) with h' | h' <;> simp [h']
        have : |vperp hd (dsg e) γ.1.b - (sgOf e : ℤ) * Y.lane (ftgt a e) e| ≤ 534 * Y.U := by rw [e1, abs_mul, hs1, one_mul]; exact hγlat
        rw [abs_le] at this; linarith
      have hsL := sLane_e Y a e
      obtain ⟨-, -, hc0, hc1⟩ := sLane_eB Y a e
      have hJ : 0 ≤ Y.lamJ := by rw [hΛJ]; positivity
      have hprod : -Y.lamJ ≤ (sgOf e : ℤ) * (TallLayout.cpar (ftgt a e) * Y.lamJ) := by
        have h0 : 0 ≤ TallLayout.cpar (ftgt a e) * Y.lamJ := mul_nonneg hc0 hJ
        have h1 : TallLayout.cpar (ftgt a e) * Y.lamJ ≤ Y.lamJ := mul_le_of_le_one_left hJ hc1
        rcases Int.units_eq_one_or (sgOf e) with h' | h' <;> simp [h'] <;> linarith
      simp only [Nat.cast_zero, zero_add, one_mul] at hhi
      linarith
  obtain ⟨-, hB⟩ := hI.abs_B1 hY hτ
  obtain ⟨-, -, hBlo, hBhi⟩ := hB r' hmem
  have hz := hI.z_after hY hτ 11 (by decide) r' hmem
  have hidle0 := hI.idle_all hτ (mem_all_of_mem hmem)
  obtain ⟨-, hax', hsrc⟩ := fexitTok_eq Y hd hY.hL hY.hH e (eB1 e) r'
  have hsB : (sgOf (eB1 e) : ℤ) = -(sgOf e : ℤ) := (sgOf_eB e).1
  have hfst : (eB1 e).1 = (latDir e true).1 := rfl
  refine ⟨?_, ?_, ?_, fun d' hd' => ?_, fun i hi => ?_, by rw [hsrc]; simp⟩
  · rw [hax]; rcases Fin.exists_fin_two.1 ⟨oth p, rfl⟩ with h | h <;> rw [h] <;> simp
  · -- the forward window: `upar'(pos) - s' C_l = (s C_l - vperp r) + U + t`
    rw [mul_sub, upar_dsg, hfst, hsB]
    change Y.Df - 2 * Y.U ≤ upar hd (dsg (eB1 e)) pos - -(sgOf e : ℤ) * Y.ctr (ftgt a e) (latDir e true).1 ∧
      upar hd (dsg (eB1 e)) pos - -(sgOf e : ℤ) * Y.ctr (ftgt a e) (latDir e true).1 ≤ Y.Df - 1
    rw [hupar, (conv r'.1.b).1]
    constructor <;> linarith [hstop', hroom, ht1, ht2, hH8, hm0]
  · -- the lateral window: along `e`, the branch keeps within `391 U + U` of the take-off line
    have hfst1 : (latDir (eB1 e) true).1 = e.1 := latDir_latDir_fst e _ _
    rw [hfst1]
    have h1 := abs_upar_sub_le (hd := hd) (dsg e) pos r'.1.b
    have h2 := exit_plane_abs hd (A := (Y.m : ℤ) + 1) hface ht1 ht2 hU.le (by linarith)
    have e1 : Uc hd e.1 pos - Y.lane (ftgt a e) (eB1 e) = (sgOf e : ℤ) * (upar hd (dsg e) pos - (sgOf e : ℤ) * Y.lane (ftgt a e) (eB1 e)) := by
      have := upar_dsg hd e pos
      linear_combination (sgOf e : ℤ) * this + (Y.lane (ftgt a e) (eB1 e) - Uc hd e.1 pos) * hss
    have hs1 : |(sgOf e : ℤ)| = 1 := by rcases Int.units_eq_one_or (sgOf e) with h' | h' <;> simp [h']
    rw [e1, abs_mul, hs1, one_mul]
    have hsU : -(Y.U) ≤ (sgOf e : ℤ) * Y.U ∧ (sgOf e : ℤ) * Y.U ≤ Y.U := by
      rcases Int.units_eq_one_or (sgOf e) with h' | h' <;> simp [h'] <;> linarith
    have := abs_le.1 (show |upar hd (dsg e) pos - upar hd (dsg e) r'.1.b| ≤ Y.U + ((Y.H : ℤ) - Y.m - 1) from h1.trans h2)
    unfold FlatLayout.ρp; rw [abs_le]; constructor <;> linarith
  · rw [hsrc] at hd'; simp only [Option.some.injEq] at hd'; subst hd'
    rw [← hposdef]; change |pos (ax0 hd) - zN Y e| ≤ Y.ρv
    refine hzt.trans ?_
    unfold FlatLayout.ρv; rw [max_le_iff]; constructor <;> linarith
  · rw [← hposdef]; refine (hidle i hi).trans ?_; rw [max_le_iff]; exact ⟨hidle0 i hi, le_rfl⟩

/-- **The second lateral exit token is admissible** for the onward attempt along `eB2 e`. [cite: GrimmettPercolation1999, §7.3 p. 174 (D)] -/
theorem FlatInv.ftAdm_exit_B2 (hI : FlatInv hd Y a e τ st) (hY : Y.OK) (hτ : FTAdm hd Y a e τ) (hgood : ∀ r ∈ st.all, GoodRec Y.m Y.L Y.H r)
    (hc : ∀ j : Fin 13, complete' hd Y a e τ (eJOf hd Y a e τ st) j (st.segs j)) {r2 : BrickRec d} (hr2 : (st.segs 12).head? = some r2) :
    FTAdm hd Y (ftgt a e) (eB2 e) (fexitTok hd Y hY.hL hY.hH e (eB2 e) r2) := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  have hH8 : 8 * ((Y.H : ℤ) + 1) ≤ Y.U := hflat
  have hD : Y.Df = 4096 * Y.U := rfl
  have hΛ : Y.lam = 1280 * Y.U := rfl
  have hΛJ : Y.lamJ = 256 * Y.U := rfl
  obtain ⟨r', hr', hmem, hlast, hstop⟩ := complete_leg_head 12 (Or.inr (Or.inr rfl)) (hc 12)
  have hrr : r' = r2 := by rw [hr2] at hr'; simpa using hr'.symm
  subst hrr
  have h12 : st.segs 12 ≠ [] := List.ne_nil_of_mem hmem
  obtain ⟨γ, hγ, -, hBE⟩ := hI.frame_branch.2 h12
  have hlen : (st.segs 12 ++ [γ]).length = (st.segs 12).length + 1 := by simp
  have hpos12 := List.length_pos_of_ne_nil h12
  obtain ⟨ha, hs⟩ := hBE.axis_sign (k := (st.segs 12).length - 1 + 1) (by rw [hlen]; omega)
  rw [legOf_append_singleton_succ, hlast] at ha hs
  generalize hp : qAt (oth (p2 e)) ((st.segs 12).length - 1 + 1) = p at ha hs
  have hg : GoodRec Y.m Y.L Y.H r' := hgood r' (mem_all_of_mem hmem)
  obtain ⟨hface, ht1, ht2, hzt, hidle, hax⟩ := exit_coords Y hd hY.hL hY.hH e hg ha hs
  set pos := (fexitTok hd Y hY.hL hY.hH e (eB2 e) r').pos with hposdef
  -- the branch's forward coordinate is `vperp`, its lateral one `upar` (index `1` flipped)
  obtain ⟨-, hflip2, hkeep2⟩ := flip_keep_B e
  change dsg (eB2 e) 1 = -dsg e 1 at hflip2
  have conv := fun b => upar_vperp_flip1 hd (σ := dsg e) (σ' := dsg (eB2 e)) hkeep2 hflip2 b
  have hupar : upar hd (dsg (eB2 e)) pos = upar hd (dsg (eB2 e)) r'.1.b + Y.U + (ox hd (dsg (eB2 e)) p pos - ox hd (dsg (eB2 e)) p r'.1.b) := by
    unfold upar; rcases Fin.exists_fin_two.1 ⟨p, rfl⟩ with h | h <;> rw [h] at hface ⊢ <;>
      simp only [show oth (0 : Fin 2) = 1 from rfl, show oth (1 : Fin 2) = 0 from rfl] at hface <;> linarith
  have hss : (sgOf e : ℤ) * (sgOf e : ℤ) = 1 := by rcases Int.units_eq_one_or (sgOf e) with h' | h' <;> simp [h']
  have hsv : ∀ b, (sgOf e : ℤ) * Uc hd (latDir e true).1 b = vperp hd (dsg e) b := fun b => by
    rw [Uc_lat_eq_vperp, ← mul_assoc, hss, one_mul]
  have hstop' : Y.Df - 3 * Y.U ≤ vperp hd (dsg e) r'.1.b - (sgOf e : ℤ) * Y.ctr (ftgt a e) (latDir e true).1 := by
    have := ((froom_eB_iff Y a e hd r'.1.b).2).not.1 hstop; push Not at this; rw [hsv] at this; exact this
  have hroom : vperp hd (dsg e) r'.1.b - (sgOf e : ℤ) * Y.ctr (ftgt a e) (latDir e true).1 ≤ Y.Df - 2 * Y.U + Y.H - Y.m - 2 := by
    rcases Nat.lt_or_ge 1 (st.segs 12).length with h2 | h2
    · have hst := hI.B2_stage (j := (st.segs 12).length - 2) (by omega)
      have := ((froom_eB_iff Y a e hd _).2).1 hst
      rw [hsv] at this
      have hstep := hI.B2_step (j := (st.segs 12).length - 2) (by omega)
      rw [show (st.segs 12).length - 2 + 1 = (st.segs 12).length - 1 by omega, hlast] at hstep
      linarith
    · have hl1 : (st.segs 12).length = 1 := by omega
      obtain ⟨-, hhi, -⟩ := hI.win_B2 hY hγ (k := 0) hpos12
      have h0 : legOf (st.segs 12) 0 = r'.1 := by rw [show (0 : ℕ) = (st.segs 12).length - 1 by omega]; exact hlast
      rw [h0] at hhi
      obtain ⟨-, -, hγlat⟩ := hI.abs_G2 hY hτ γ (List.mem_of_mem_head? hγ)
      have hγv : vperp hd (dsg e) γ.1.b ≤ (sgOf e : ℤ) * Y.lane (ftgt a e) e + 534 * Y.U := by
        have e1 : vperp hd (dsg e) γ.1.b - (sgOf e : ℤ) * Y.lane (ftgt a e) e = (sgOf e : ℤ) * (Uc hd (latDir e true).1 γ.1.b - Y.lane (ftgt a e) e) := by
          rw [mul_sub, hsv]
        have hs1 : |(sgOf e : ℤ)| = 1 := by rcases Int.units_eq_one_or (sgOf e) with h' | h' <;> simp [h']
        have : |vperp hd (dsg e) γ.1.b - (sgOf e : ℤ) * Y.lane (ftgt a e) e| ≤ 534 * Y.U := by rw [e1, abs_mul, hs1, one_mul]; exact hγlat
        rw [abs_le] at this; linarith
      have hsL := sLane_e Y a e
      obtain ⟨-, -, hc0, hc1⟩ := sLane_eB Y a e
      have hJ : 0 ≤ Y.lamJ := by rw [hΛJ]; positivity
      have hprod : (sgOf e : ℤ) * (TallLayout.cpar (ftgt a e) * Y.lamJ) ≤ Y.lamJ := by
        have h0 : 0 ≤ TallLayout.cpar (ftgt a e) * Y.lamJ := mul_nonneg hc0 hJ
        have h1 : TallLayout.cpar (ftgt a e) * Y.lamJ ≤ Y.lamJ := mul_le_of_le_one_left hJ hc1
        rcases Int.units_eq_one_or (sgOf e) with h' | h' <;> simp [h'] <;> linarith
      simp only [Nat.cast_zero, zero_add, one_mul] at hhi
      linarith
  obtain ⟨-, hB⟩ := hI.abs_B2 hY hτ
  obtain ⟨-, -, hBlo, hBhi⟩ := hB r' hmem
  have hz := hI.z_after hY hτ 12 (by decide) r' hmem
  have hidle0 := hI.idle_all hτ (mem_all_of_mem hmem)
  obtain ⟨-, hax', hsrc⟩ := fexitTok_eq Y hd hY.hL hY.hH e (eB2 e) r'
  have hsB : (sgOf (eB2 e) : ℤ) = (sgOf e : ℤ) := (sgOf_eB e).2
  have hfst : (eB2 e).1 = (latDir e true).1 := rfl
  refine ⟨?_, ?_, ?_, fun d' hd' => ?_, fun i hi => ?_, by rw [hsrc]; simp⟩
  · rw [hax]; rcases Fin.exists_fin_two.1 ⟨oth p, rfl⟩ with h | h <;> rw [h] <;> simp
  · rw [mul_sub, upar_dsg, hfst, hsB]
    change Y.Df - 2 * Y.U ≤ upar hd (dsg (eB2 e)) pos - (sgOf e : ℤ) * Y.ctr (ftgt a e) (latDir e true).1 ∧
      upar hd (dsg (eB2 e)) pos - (sgOf e : ℤ) * Y.ctr (ftgt a e) (latDir e true).1 ≤ Y.Df - 1
    rw [hupar, (conv r'.1.b).1]
    constructor <;> linarith [hstop', hroom, ht1, ht2, hH8, hm0]
  · have hfst1 : (latDir (eB2 e) true).1 = e.1 := latDir_latDir_fst e _ _
    rw [hfst1]
    have h1 := abs_upar_sub_le (hd := hd) (dsg e) pos r'.1.b
    have h2 := exit_plane_abs hd (A := (Y.m : ℤ) + 1) hface ht1 ht2 hU.le (by linarith)
    have e1 : Uc hd e.1 pos - Y.lane (ftgt a e) (eB2 e) = (sgOf e : ℤ) * (upar hd (dsg e) pos - (sgOf e : ℤ) * Y.lane (ftgt a e) (eB2 e)) := by
      have := upar_dsg hd e pos
      linear_combination (sgOf e : ℤ) * this + (Y.lane (ftgt a e) (eB2 e) - Uc hd e.1 pos) * hss
    have hs1 : |(sgOf e : ℤ)| = 1 := by rcases Int.units_eq_one_or (sgOf e) with h' | h' <;> simp [h']
    rw [e1, abs_mul, hs1, one_mul]
    have hsU : -(Y.U) ≤ (sgOf e : ℤ) * Y.U ∧ (sgOf e : ℤ) * Y.U ≤ Y.U := by
      rcases Int.units_eq_one_or (sgOf e) with h' | h' <;> simp [h'] <;> linarith
    have := abs_le.1 (show |upar hd (dsg e) pos - upar hd (dsg e) r'.1.b| ≤ Y.U + ((Y.H : ℤ) - Y.m - 1) from h1.trans h2)
    unfold FlatLayout.ρp; rw [abs_le]; constructor <;> linarith
  · rw [hsrc] at hd'; simp only [Option.some.injEq] at hd'; subst hd'
    rw [← hposdef]; change |pos (ax0 hd) - zN Y e| ≤ Y.ρv
    refine hzt.trans ?_
    unfold FlatLayout.ρv; rw [max_le_iff]; constructor <;> linarith
  · rw [← hposdef]; refine (hidle i hi).trans ?_; rw [max_le_iff]; exact ⟨hidle0 i hi, le_rfl⟩

end BGNd

end Percolation.Literature

end

/-!
# Part 4 (The flat gait, XXXI): the run, IV — the recorded boxes avoid the zones of the exit tokens

Grimmett's (C) for the junctions of the flat gait
(*Percolation*, 2nd ed. (1999), §7.3 pp. 173–174, case `H < L`): the boxes of the plates of a
complete run are disjoint from the reserved region of each onward attempt from the target cell
(`FlatInv.box_disjoint_exit_T`, `FlatInv.box_disjoint_exit_B1`, `FlatInv.box_disjoint_exit_B2`).
Three ingredients: the shape of a region near its token — beyond the token along the token's axis,
or a hop on along the other plane axis, or far forward (`fzone_exit_shape`), and at least `-4U`
forward (`fzone_exit_lower`); the plates of the exit leg are behind the exit token along its axis,
at most `2U` on along the other, and not far forward (`DiagLeg.near_exit`); every other plate is
more than `4U` behind the token in the onward forward coordinate (`FlatInv.far_all`).

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §7.3 pp. 171–174.
-/

noncomputable section

namespace Percolation.Literature

open LatticeModels Contour
open scoped Classical

namespace BGNd

variable {d : ℕ} [NeZero d]

/-! ## The shape of a region near its token -/

section Shape

variable (Y : FlatLayout) (hd : 3 ≤ d) (c : Site 2) (e' : MDir) (τ' : TTok d)

omit [NeZero d] in
/-- The forward diagonal coordinate of a point in oriented plane coordinates. [folklore] -/
theorem sUc_eq_oxsum (w : Site d) : (sgOf e' : ℤ) * Uc hd e'.1 w = (dsg e' 0 : ℤ) * w (pl hd 0) + (dsg e' 1 : ℤ) * w (pl hd 1) := by
  rw [upar_dsg]; rfl

omit [NeZero d] in
/-- The same, split at a plane index and the other one. [folklore] -/
theorem sUc_eq_oxsum' (w : Site d) (q : Fin 2) :
    (sgOf e' : ℤ) * Uc hd e'.1 w = (dsg e' q : ℤ) * w (pl hd q) + (dsg e' (oth q) : ℤ) * w (pl hd (oth q)) := by
  rw [sUc_eq_oxsum]
  rcases Fin.exists_fin_two.1 ⟨q, rfl⟩ with h | h <;> rw [h]
  · rfl
  · rw [show oth (1 : Fin 2) = 0 from rfl]; ring

omit [NeZero d] in
/-- **The shape of a region near its token**: a point of the region of an admissible token is
beyond the token along the token's axis, or more than a hop on along the other plane axis, or more
than `180 U` forward (doubled). [folklore] -/
theorem fzone_exit_shape (hY : Y.OK) (hτ' : FTAdm hd Y c e' τ') {w : Site d} (hw : w ∈ fzone Y hd c e' τ') :
    1 ≤ (dsg e' (plIdx hd τ'.ax) : ℤ) * (w (pl hd (plIdx hd τ'.ax)) - 2 * τ'.pos (pl hd (plIdx hd τ'.ax))) ∨
      2 * Y.U + 1 ≤ (dsg e' (oth (plIdx hd τ'.ax)) : ℤ) * (w (pl hd (oth (plIdx hd τ'.ax))) - 2 * τ'.pos (pl hd (oth (plIdx hd τ'.ax)))) ∨
      2 * upar hd (dsg e') τ'.pos + 180 * Y.U < (sgOf e' : ℤ) * Uc hd e'.1 w := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  obtain ⟨f1, f2, -, -, f5, f6, -, -⟩ := FTAdm.frame Y hd c e' τ' hτ'
  have hD : Y.Df = 4096 * Y.U := rfl
  have hΛ : Y.lam = 1280 * Y.U := rfl
  have hΛJ : Y.lamJ = 256 * Y.U := rfl
  have t5 := abs_le.1 f5; have t6 := abs_le.1 f6
  have hsU : -(Y.U) ≤ (sgOf e' : ℤ) * Y.U ∧ (sgOf e' : ℤ) * Y.U ≤ Y.U := by
    rcases Int.units_eq_one_or (sgOf e') with h' | h' <;> simp [h'] <;> linarith
  obtain ⟨-, hcases⟩ := hw
  rcases hcases with ⟨a1, -⟩ | ⟨a1, -⟩ | ⟨a1, -⟩ | ⟨-, -, -, -, -, a6⟩ | ⟨-, -, -, -, -, a6⟩ | ⟨-, a2, -, -, -, a6⟩ | ⟨a1, -⟩ | ⟨a1, -⟩ | ⟨a1, -⟩
  · exact Or.inl a1
  · exact Or.inr (Or.inl a1)
  · left; linarith
  · exact Or.inl a6
  · exact Or.inl a6
  · by_cases hnear : (sgOf e' : ℤ) * Uc hd e'.1 w ≤ 2 * upar hd (dsg e') τ'.pos + 180 * Y.U
    · exact Or.inl (a6 hnear)
    · right; right; push Not at hnear; exact hnear
  · right; right; linarith
  · right; right; have := abs_le.1 a1; linarith
  · right; right; have := abs_le.1 a1; linarith

omit [NeZero d] in
/-- **A region begins at most `4U` (doubled) before its token** in the forward coordinate. [folklore] -/
theorem fzone_exit_lower (hY : Y.OK) (hτ' : FTAdm hd Y c e' τ') {w : Site d} (hw : w ∈ fzone Y hd c e' τ') :
    2 * upar hd (dsg e') τ'.pos - 4 * Y.U ≤ (sgOf e' : ℤ) * Uc hd e'.1 w := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  obtain ⟨f1, f2, -, -, f5, f6, -, -⟩ := FTAdm.frame Y hd c e' τ' hτ'
  have hD : Y.Df = 4096 * Y.U := rfl
  have hΛ : Y.lam = 1280 * Y.U := rfl
  have hΛJ : Y.lamJ = 256 * Y.U := rfl
  have t5 := abs_le.1 f5; have t6 := abs_le.1 f6
  have hsU : -(Y.U) ≤ (sgOf e' : ℤ) * Y.U ∧ (sgOf e' : ℤ) * Y.U ≤ Y.U := by
    rcases Int.units_eq_one_or (sgOf e') with h' | h' <;> simp [h'] <;> linarith
  have hcE : 0 ≤ cE Y e' τ' := by unfold cE; split_ifs <;> linarith
  set q := plIdx hd τ'.ax with hq
  have hP := sUc_eq_oxsum' hd e' w q
  have hS : upar hd (dsg e') τ'.pos = (dsg e' q : ℤ) * τ'.pos (pl hd q) + (dsg e' (oth q) : ℤ) * τ'.pos (pl hd (oth q)) := by
    have := sUc_eq_oxsum' hd e' τ'.pos q; rw [upar_dsg] at this; exact this
  have hσ : ∀ i : Fin 2, ((dsg e' i : ℤ)) = 1 ∨ ((dsg e' i : ℤ)) = -1 := fun i => by rcases Int.units_eq_one_or (dsg e' i) with h' | h' <;> simp [h']
  obtain ⟨-, hcases⟩ := hw
  rcases hcases with ⟨a1, -, a3, -⟩ | ⟨a1, -, a3, -⟩ | ⟨a1, -, a3, -⟩ | ⟨-, -, a3, -⟩ | ⟨-, -, a3, -⟩ | ⟨a1, -⟩ | ⟨a1, -⟩ | ⟨a1, -⟩ | ⟨a1, -⟩
  · have t := abs_le.1 a3
    rw [hP, hS]; rcases hσ (oth q) with h | h <;> rw [h] at * <;> linarith
  · rw [hP, hS]; linarith
  · rw [hP, hS]; linarith
  · exact a3
  · linarith
  · linarith
  · linarith
  · have := abs_le.1 a1; linarith
  · have := abs_le.1 a1; linarith

end Shape

/-! ## The exit leg near its exit token -/

section Near

variable {hd : 3 ≤ d} {Y : FlatLayout} {e : MDir} {σ : Fin 2 → ℤˣ} {q₀ : Fin 2} {l : List (BrickRec d)}

/-- **The plates of a leg are behind the base of the next hop off its head**: with `r` the head
(axis `p`) and `pos` a hop on through the other face (`U` on along the other plane axis, between
`m + 1` and `H - m - 1` on along `p`), every point of the box of every plate is not beyond `pos`
along the other axis, at most `2U` beyond it along `p`, and at most `2H` beyond twice its forward
coordinate (all doubled). [folklore] -/
theorem DiagLeg.near_exit (hD : DiagLeg hd Y e σ none q₀ l) (hY : Y.OK) {r : BrickPos d} (hr : legOf l (l.length - 1) = r) {p : Fin 2}
    {pos : Site d} (hface : ox hd σ (oth p) pos = ox hd σ (oth p) r.b + Y.U)
    (ht1 : (Y.m : ℤ) + 1 ≤ ox hd σ p pos - ox hd σ p r.b) {k : ℕ} (hk : k < l.length) {w : Site d} (hw : w ∈ boxOf Y.L Y.H (legOf l k)) :
    (σ (oth p) : ℤ) * (w (pl hd (oth p)) - 2 * pos (pl hd (oth p))) ≤ 0 ∧ (σ p : ℤ) * (w (pl hd p) - 2 * pos (pl hd p)) ≤ 2 * Y.U ∧
      (σ 0 : ℤ) * w (pl hd 0) + (σ 1 : ℤ) * w (pl hd 1) ≤ 2 * upar hd σ pos + 2 * Y.H := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  have hmono : ∀ j, ox hd σ j (legOf l k).b ≤ ox hd σ j r.b := fun j => by
    rw [← hr]; exact (hD.mono (k := k) (k' := l.length - 1) (by omega) (by omega) j).1
  obtain ⟨hax, hsg⟩ := hD.axis_sign hk
  generalize hi : qAt q₀ k = i at hax hsg
  -- the box in oriented coordinates: thin along `i`, wide along `oth i`
  have thin : (σ i : ℤ) * w (pl hd i) ≤ 2 * ox hd σ i (legOf l k).b + 2 * Y.H + 2 := by
    obtain ⟨-, h2⟩ := box_axis hw
    rw [hax, hsg] at h2; unfold ox; linarith
  have wide : (σ (oth i) : ℤ) * w (pl hd (oth i)) ≤ 2 * ox hd σ (oth i) (legOf l k).b + 2 * Y.U := by
    have := (box_trans hw (i := pl hd (oth i)) (by rw [hax]; exact pl_ne_pl hd (oth_ne i))).2
    have h' := (box_trans hw (i := pl hd (oth i)) (by rw [hax]; exact pl_ne_pl hd (oth_ne i))).1
    unfold ox
    rcases Int.units_eq_one_or (σ (oth i)) with h | h <;> simp [h] <;> linarith
  have bound : ∀ j, (σ j : ℤ) * w (pl hd j) ≤ 2 * ox hd σ j r.b + 2 * Y.U := fun j => by
    rcases eq_or_eq_oth j i with h | h
    · rw [h]; linarith [hmono i]
    · rw [h]; linarith [hmono (oth i)]
  refine ⟨?_, ?_, ?_⟩
  · have := bound (oth p); unfold ox at this hface; nlinarith [units_sq (σ (oth p))]
  · have := bound p; unfold ox at this ht1; nlinarith [units_sq (σ p)]
  · have h0 : (σ i : ℤ) * w (pl hd i) + (σ (oth i) : ℤ) * w (pl hd (oth i)) = (σ 0 : ℤ) * w (pl hd 0) + (σ 1 : ℤ) * w (pl hd 1) := by
      rcases Fin.exists_fin_two.1 ⟨i, rfl⟩ with h | h <;> rw [h]
      · rfl
      · rw [show oth (1 : Fin 2) = 0 from rfl]; ring
    have hup : upar hd σ pos = upar hd σ r.b + Y.U + (ox hd σ p pos - ox hd σ p r.b) := by
      unfold upar; rcases Fin.exists_fin_two.1 ⟨p, rfl⟩ with h | h <;> rw [h] at hface ⊢ <;>
        simp only [show oth (0 : Fin 2) = 1 from rfl, show oth (1 : Fin 2) = 0 from rfl] at hface <;> linarith
    have hub : upar hd σ (legOf l k).b ≤ upar hd σ r.b := by unfold upar; linarith [hmono 0, hmono 1]
    have hsum : (σ i : ℤ) * w (pl hd i) + (σ (oth i) : ℤ) * w (pl hd (oth i)) ≤ 2 * upar hd σ (legOf l k).b + 2 * Y.U + 2 * Y.H + 2 := by
      have : upar hd σ (legOf l k).b = ox hd σ i (legOf l k).b + ox hd σ (oth i) (legOf l k).b := by
        unfold upar; rcases Fin.exists_fin_two.1 ⟨i, rfl⟩ with h | h <;> rw [h]
        · rfl
        · rw [show oth (1 : Fin 2) = 0 from rfl]; ring
      linarith
    rw [← h0]; linarith

end Near

/-! ## The other segments are far behind the exit tokens -/

section Far

variable {Y : FlatLayout} {hd : 3 ≤ d} {a : Site 2} {e : MDir} {τ : TTok d} {st : FS d}

/-- **The windows of all plates**, segment by segment, in the forward and lateral (read along `e`)
coordinates: forward at most `s · ctr + D - 8U` except for the last trunk segment, laterally above
`s · ctr_lat - D + 8U` except for the first branch and below `s · ctr_lat + D - 8U` except for the
second. [folklore] -/
theorem FlatInv.far_all (hI : FlatInv hd Y a e τ st) (hY : Y.OK) (hτ : FTAdm hd Y a e τ) {k : Fin 13} {r : BrickRec d} (hr : r ∈ st.segs k) :
    (k ≠ 10 → upar hd (dsg e) r.1.b ≤ (sgOf e : ℤ) * Y.ctr (ftgt a e) e.1 + Y.Df - 8 * Y.U) ∧
      (k ≠ 11 → (sgOf e : ℤ) * Y.ctr (ftgt a e) (latDir e true).1 - Y.Df + 8 * Y.U ≤ vperp hd (dsg e) r.1.b) ∧
      (k ≠ 12 → vperp hd (dsg e) r.1.b ≤ (sgOf e : ℤ) * Y.ctr (ftgt a e) (latDir e true).1 + Y.Df - 8 * Y.U) := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  obtain ⟨f1, f2, f3, f4, f5, f6, -, -⟩ := FTAdm.frame Y hd a e τ hτ
  have hD : Y.Df = 4096 * Y.U := rfl
  have hΛ : Y.lam = 1280 * Y.U := rfl
  have hΛJ : Y.lamJ = 256 * Y.U := rfl
  have hρ : Y.ρp = 640 * Y.U := rfl
  have hH8 : 8 * ((Y.H : ℤ) + 1) ≤ Y.U := hflat
  have hs : (sgOf e : ℤ) = 1 ∨ (sgOf e : ℤ) = -1 := by rcases Int.units_eq_one_or (sgOf e) with h' | h' <;> simp [h']
  have hss : (sgOf e : ℤ) * (sgOf e : ℤ) = 1 := by rcases hs with h' | h' <;> rw [h'] <;> norm_num
  have hs1 : |(sgOf e : ℤ)| = 1 := by rcases hs with h' | h' <;> simp [h']
  have hsU : -(Y.U) ≤ (sgOf e : ℤ) * Y.U ∧ (sgOf e : ℤ) * Y.U ≤ Y.U := by rcases hs with h' | h' <;> simp [h'] <;> linarith
  have t3 := abs_le.1 f3; have t4 := abs_le.1 f4; have t5 := abs_le.1 f5; have t6 := abs_le.1 f6
  -- lateral quantities read along `e`
  have hsv : ∀ b, (sgOf e : ℤ) * Uc hd (latDir e true).1 b = vperp hd (dsg e) b := fun b => by
    rw [Uc_lat_eq_vperp, ← mul_assoc, hss, one_mul]
  have hVb : |vperp hd (dsg e) τ.pos - (sgOf e : ℤ) * Y.ctr (ftgt a e) (latDir e true).1| ≤ Y.lam + 2 * Y.lamJ + Y.ρp := by
    rw [← hsv, ← mul_sub, abs_mul, hs1, one_mul]; exact f3
  have hlnb : |(sgOf e : ℤ) * Y.lane (ftgt a e) e - (sgOf e : ℤ) * Y.ctr (ftgt a e) (latDir e true).1| ≤ Y.lam + Y.lamJ := by
    rw [← mul_sub, abs_mul, hs1, one_mul]; exact f4
  have tV := abs_le.1 hVb; have tl := abs_le.1 hlnb
  -- from `|Uc_lat b - ln| ≤ B` to `|vperp b - s ln| ≤ B`
  have lat_conv : ∀ b B, |Uc hd (latDir e true).1 b - Y.lane (ftgt a e) e| ≤ B →
      |vperp hd (dsg e) b - (sgOf e : ℤ) * Y.lane (ftgt a e) e| ≤ B := by
    intro b B h; rw [← hsv, ← mul_sub, abs_mul, hs1, one_mul]; exact h
  have hk := k.isLt
  -- dispatch on the segment
  rcases k with ⟨k, hk'⟩
  simp only [ne_eq, Fin.ext_iff]
  interval_cases k <;> simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk] at hr
  · -- the lead-in: within `2 (U + H)` of the token in both coordinates
    have hK : SegOK hd Y e τ (eJOf hd Y a e τ st) 0 (st.segs 0) (st.segs (startOf 0)) := hI.segOK 0
    simp only [SegOK, startOf, Fin.isValue, Matrix.cons_val] at hK
    obtain ⟨hDl, hfirst, hlen3⟩ := hK (List.ne_nil_of_mem hr)
    obtain ⟨j, hj, hjr⟩ := exists_legOf_of_mem hr
    have hm0' := hDl.mono (k := 0) (k' := j) (Nat.zero_le _) hj
    have m0 := (hm0' 0).1; have m1 := (hm0' 1).1; have mu := (hm0' 0).2.2
    rw [hfirst] at m0 m1 mu
    change ox hd (dsg e) 0 τ.pos ≤ _ at m0
    change ox hd (dsg e) 1 τ.pos ≤ _ at m1
    change upar hd (dsg e) (legOf (st.segs 0) j).b - upar hd (dsg e) τ.pos ≤ _ at mu
    have hj2 : (j : ℤ) - (0 : ℕ) ≤ 2 := by have := Nat.cast_le (α := ℤ).2 (show j ≤ 2 by omega); simpa using this
    have hδ : 0 ≤ Y.U + Y.H - Y.m - 1 := by linarith
    have hprod := mul_le_mul_of_nonneg_right hj2 hδ
    rw [← hjr]
    unfold upar vperp at *
    refine ⟨fun _ => by linarith, fun _ => by linarith, fun _ => by linarith⟩
  · -- the riser
    obtain ⟨j, hj, hjr⟩ := exists_legOf_of_mem hr
    obtain ⟨hlo, hhi, hlat, -⟩ := hI.win_riser hY hτ hj
    have hlen := hI.riser_len_le hY hτ
    have hjc : (j : ℤ) + 1 ≤ 106 := by have := Nat.cast_le (α := ℤ).2 (show j + 1 ≤ 106 by omega); push_cast at this; exact this
    have := mul_le_mul_of_nonneg_right hjc hU.le
    have tl' := abs_le.1 hlat
    rw [← hjr]
    refine ⟨fun _ => by linarith, fun _ => by linarith, fun _ => by linarith⟩
  · obtain ⟨-, hhi, hlat⟩ := (hI.abs_P hY hτ).1 r hr
    have tl' := abs_le.1 hlat
    refine ⟨fun _ => by linarith, fun _ => by linarith, fun _ => by linarith⟩
  · obtain ⟨-, hhi, hlat⟩ := hI.abs_GJ hY hτ r hr
    have tl' := abs_le.1 hlat
    refine ⟨fun _ => by linarith, fun _ => by linarith, fun _ => by linarith⟩
  · obtain ⟨-, hhi, hmin, hmax⟩ := (hI.abs_J hY hτ).1 r hr
    have tU := abs_le.1 f3; have tL := abs_le.1 f4
    have hmn : Y.ctr (ftgt a e) (latDir e true).1 - (Y.lam + 2 * Y.lamJ + Y.ρp) - 123 * Y.U ≤
        min (Uc hd (latDir e true).1 τ.pos - 123 * Y.U) (Y.lane (ftgt a e) e - 19 * Y.U) := by
      rw [le_min_iff]; constructor <;> linarith
    have hmx : max (Uc hd (latDir e true).1 τ.pos + 123 * Y.U) (Y.lane (ftgt a e) e + 19 * Y.U) ≤
        Y.ctr (ftgt a e) (latDir e true).1 + (Y.lam + 2 * Y.lamJ + Y.ρp) + 123 * Y.U := by
      rw [max_le_iff]; constructor <;> linarith
    have hv := hsv r.1.b
    refine ⟨fun _ => by linarith, fun _ => ?_, fun _ => ?_⟩ <;> rcases hs with h | h <;> rw [h] at hv ⊢ <;> linarith
  · obtain ⟨-, hhi, hlat⟩ := hI.abs_GT hY hτ r hr
    have tl' := abs_le.1 (lat_conv _ _ hlat)
    refine ⟨fun _ => by linarith, fun _ => by linarith, fun _ => by linarith⟩
  · obtain ⟨h6, -, -⟩ := hI.trunk_hi hY hτ
    have hhi := h6 r hr
    obtain ⟨-, -, hlat⟩ := hI.abs_T hY hτ r (by simp [hr])
    have tl' := abs_le.1 (lat_conv _ _ hlat)
    refine ⟨fun _ => by linarith, fun _ => by linarith, fun _ => by linarith⟩
  · obtain ⟨-, hhi, hlat⟩ := hI.abs_G1 hY hτ r hr
    have tl' := abs_le.1 (lat_conv _ _ hlat)
    refine ⟨fun _ => by linarith, fun _ => by linarith, fun _ => by linarith⟩
  · obtain ⟨-, h8, -⟩ := hI.trunk_hi hY hτ
    have hhi := h8 r hr
    obtain ⟨-, -, hlat⟩ := hI.abs_T hY hτ r (by simp [hr])
    have tl' := abs_le.1 (lat_conv _ _ hlat)
    refine ⟨fun _ => by linarith, fun _ => by linarith, fun _ => by linarith⟩
  · obtain ⟨-, hhi, hlat⟩ := hI.abs_G2 hY hτ r hr
    have tl' := abs_le.1 (lat_conv _ _ hlat)
    refine ⟨fun _ => by linarith, fun _ => by linarith, fun _ => by linarith⟩
  · obtain ⟨-, -, hlat⟩ := hI.abs_T hY hτ r (by simp [hr])
    have tl' := abs_le.1 (lat_conv _ _ hlat)
    refine ⟨fun h => absurd rfl h, fun _ => by linarith, fun _ => by linarith⟩
  · obtain ⟨-, hB⟩ := hI.abs_B1 hY hτ
    obtain ⟨-, hv, -, hhi⟩ := hB r hr
    refine ⟨fun _ => by linarith, fun h => absurd rfl h, fun _ => by linarith⟩
  · obtain ⟨-, hB⟩ := hI.abs_B2 hY hτ
    obtain ⟨-, hv, -, hhi⟩ := hB r hr
    refine ⟨fun _ => by linarith, fun _ => by linarith, fun h => absurd rfl h⟩

end Far

/-! ## The recorded boxes avoid the zones of the exit tokens -/

section Avoid

variable {Y : FlatLayout} {hd : 3 ≤ d} {a : Site 2} {e : MDir} {τ : TTok d} {st : FS d}

omit [NeZero d] in
/-- Membership in the records of a state, by segment. [folklore] -/
theorem mem_all_iff {st : FS d} {r : BrickRec d} : r ∈ st.all ↔ ∃ k : Fin 13, r ∈ st.segs k := by
  unfold FS.all; rw [List.mem_flatMap]; simp

/-- **The boxes of a complete run avoid the zone of the straight exit token.** [cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
theorem FlatInv.box_disjoint_exit_T (hI : FlatInv hd Y a e τ st) (hY : Y.OK) (hτ : FTAdm hd Y a e τ) (hgood : ∀ r ∈ st.all, GoodRec Y.m Y.L Y.H r)
    (hc : ∀ j : Fin 13, complete' hd Y a e τ (eJOf hd Y a e τ st) j (st.segs j)) {rT : BrickRec d} (hrT : (st.segs 10).head? = some rT) :
    ∀ r₀ ∈ st.all, Disjoint (boxOf Y.L Y.H r₀.1) (fzone Y hd (ftgt a e) e (fexitTok hd Y hY.hL hY.hH e e rT)) := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  have hH8 : 8 * ((Y.H : ℤ) + 1) ≤ Y.U := hflat
  have hτ' := hI.ftAdm_exit_T hY hτ hgood hc hrT
  set τ' := fexitTok hd Y hY.hL hY.hH e e rT with hτ'def
  -- the head and the exit geometry
  obtain ⟨r', hr', hmem, hlast, -⟩ := complete_leg_head 10 (Or.inl rfl) (hc 10)
  have hrr : r' = rT := by rw [hrT] at hr'; simpa using hr'.symm
  subst hrr
  have h10 : st.segs 10 ≠ [] := List.ne_nil_of_mem hmem
  have hK : SegOK hd Y e τ (eJOf hd Y a e τ st) 10 (st.segs 10) (st.segs (startOf 10)) := hI.segOK 10
  simp only [SegOK, startOf, Fin.isValue, Matrix.cons_val] at hK
  obtain ⟨-, -, q, hD, -⟩ := hK h10
  obtain ⟨ha, hs⟩ := hD.axis_sign (k := (st.segs 10).length - 1) (by have := List.length_pos_of_ne_nil h10; omega)
  rw [hlast] at ha hs
  generalize hp : qAt q ((st.segs 10).length - 1) = p at ha hs
  have hg : GoodRec Y.m Y.L Y.H r' := hgood r' (mem_all_of_mem hmem)
  obtain ⟨hface, ht1, -, -, -, hax⟩ := exit_coords Y hd hY.hL hY.hH e hg ha hs
  rw [← hτ'def] at hface ht1 hax
  have hq' : plIdx hd τ'.ax = oth p := by rw [hax, plIdx_pl]
  obtain ⟨wlo, -⟩ := hτ'.longit
  rw [mul_sub, upar_dsg] at wlo
  intro r₀ hr₀
  rw [Set.disjoint_left]
  intro w hw hz
  have hshape := fzone_exit_shape Y hd (ftgt a e) e τ' hY hτ' hz
  have hlow := fzone_exit_lower Y hd (ftgt a e) e τ' hY hτ' hz
  rw [hq', oth_oth] at hshape
  obtain ⟨k, hk⟩ := mem_all_iff.1 hr₀
  by_cases hk10 : k = 10
  · -- a plate of the exit leg
    subst hk10
    obtain ⟨j, hj, hjr⟩ := exists_legOf_of_mem hk
    rw [← hjr] at hw
    obtain ⟨n1, n2, n3⟩ := hD.near_exit hY hlast hface ht1 hj hw
    rw [← sUc_eq_oxsum] at n3
    rcases hshape with h | h | h
    · linarith
    · linarith
    · linarith
  · -- a plate of another segment: far behind
    have hfar := (hI.far_all hY hτ hk).1 hk10
    have hbox := abs_le.1 (box_P (hd := hd) (e := e) hY hw)
    linarith

/-- **The boxes of a complete run avoid the zone of the first lateral exit token.** [cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
theorem FlatInv.box_disjoint_exit_B1 (hI : FlatInv hd Y a e τ st) (hY : Y.OK) (hτ : FTAdm hd Y a e τ) (hgood : ∀ r ∈ st.all, GoodRec Y.m Y.L Y.H r)
    (hc : ∀ j : Fin 13, complete' hd Y a e τ (eJOf hd Y a e τ st) j (st.segs j)) {r1 : BrickRec d} (hr1 : (st.segs 11).head? = some r1) :
    ∀ r₀ ∈ st.all, Disjoint (boxOf Y.L Y.H r₀.1) (fzone Y hd (ftgt a e) (eB1 e) (fexitTok hd Y hY.hL hY.hH e (eB1 e) r1)) := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  have hH8 : 8 * ((Y.H : ℤ) + 1) ≤ Y.U := hflat
  have hτ' := hI.ftAdm_exit_B1 hY hτ hgood hc hr1
  set τ' := fexitTok hd Y hY.hL hY.hH e (eB1 e) r1 with hτ'def
  obtain ⟨r', hr', hmem, hlast, -⟩ := complete_leg_head 11 (Or.inr (Or.inl rfl)) (hc 11)
  have hrr : r' = r1 := by rw [hr1] at hr'; simpa using hr'.symm
  subst hrr
  have h11 : st.segs 11 ≠ [] := List.ne_nil_of_mem hmem
  obtain ⟨γ, hγ, -, hBE⟩ := hI.frame_branch.1 h11
  have hlen : (st.segs 11 ++ [γ]).length = (st.segs 11).length + 1 := by simp
  have hpos11 := List.length_pos_of_ne_nil h11
  have hlast' : legOf (st.segs 11 ++ [γ]) ((st.segs 11 ++ [γ]).length - 1) = r'.1 := by
    rw [hlen, show (st.segs 11).length + 1 - 1 = (st.segs 11).length - 1 + 1 by omega, legOf_append_singleton_succ, hlast]
  obtain ⟨ha, hs⟩ := hBE.axis_sign (k := (st.segs 11 ++ [γ]).length - 1) (by omega)
  rw [hlast'] at ha hs
  generalize hp : qAt (oth (p1 e)) ((st.segs 11 ++ [γ]).length - 1) = p at ha hs
  have hg : GoodRec Y.m Y.L Y.H r' := hgood r' (mem_all_of_mem hmem)
  obtain ⟨hface, ht1, -, -, -, hax⟩ := exit_coords Y hd hY.hL hY.hH e hg ha hs
  rw [← hτ'def] at hface ht1 hax
  have hq' : plIdx hd τ'.ax = oth p := by rw [hax, plIdx_pl]
  obtain ⟨wlo, -⟩ := hτ'.longit
  rw [mul_sub, upar_dsg] at wlo
  have hsB : (sgOf (eB1 e) : ℤ) = -(sgOf e : ℤ) := (sgOf_eB e).1
  have hfst : (eB1 e).1 = (latDir e true).1 := rfl
  have hss : (sgOf e : ℤ) * (sgOf e : ℤ) = 1 := by rcases Int.units_eq_one_or (sgOf e) with h' | h' <;> simp [h']
  have hsv : ∀ b, (sgOf e : ℤ) * Uc hd (latDir e true).1 b = vperp hd (dsg e) b := fun b => by
    rw [Uc_lat_eq_vperp, ← mul_assoc, hss, one_mul]
  intro r₀ hr₀
  rw [Set.disjoint_left]
  intro w hw hz
  have hshape := fzone_exit_shape Y hd (ftgt a e) (eB1 e) τ' hY hτ' hz
  have hlow := fzone_exit_lower Y hd (ftgt a e) (eB1 e) τ' hY hτ' hz
  rw [hq', oth_oth] at hshape
  obtain ⟨k, hk⟩ := mem_all_iff.1 hr₀
  by_cases hk11 : k = 11
  · subst hk11
    obtain ⟨j, hj, hjr⟩ := exists_legOf_of_mem hk
    rw [← hjr, ← legOf_append_singleton_succ _ γ] at hw
    obtain ⟨n1, n2, n3⟩ := hBE.near_exit hY hlast' hface ht1 (k := j + 1) (by rw [hlen]; omega) hw
    rw [← sUc_eq_oxsum] at n3
    rcases hshape with h | h | h
    · linarith
    · linarith
    · linarith
  · have hfar := (hI.far_all hY hτ hk).2.1 hk11
    have hbox := abs_le.1 (box_L (hd := hd) (e := e) hY hw)
    rw [hfst, hsB] at hlow wlo
    have hv := hsv r₀.1.b
    have hs1 : (sgOf e : ℤ) = 1 ∨ (sgOf e : ℤ) = -1 := by rcases Int.units_eq_one_or (sgOf e) with h' | h' <;> simp [h']
    rcases hs1 with h | h <;> rw [h] at hlow wlo hv hfar <;> linarith [hbox.1, hbox.2]

/-- **The boxes of a complete run avoid the zone of the second lateral exit token.** [cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
theorem FlatInv.box_disjoint_exit_B2 (hI : FlatInv hd Y a e τ st) (hY : Y.OK) (hτ : FTAdm hd Y a e τ) (hgood : ∀ r ∈ st.all, GoodRec Y.m Y.L Y.H r)
    (hc : ∀ j : Fin 13, complete' hd Y a e τ (eJOf hd Y a e τ st) j (st.segs j)) {r2 : BrickRec d} (hr2 : (st.segs 12).head? = some r2) :
    ∀ r₀ ∈ st.all, Disjoint (boxOf Y.L Y.H r₀.1) (fzone Y hd (ftgt a e) (eB2 e) (fexitTok hd Y hY.hL hY.hH e (eB2 e) r2)) := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  have hH8 : 8 * ((Y.H : ℤ) + 1) ≤ Y.U := hflat
  have hτ' := hI.ftAdm_exit_B2 hY hτ hgood hc hr2
  set τ' := fexitTok hd Y hY.hL hY.hH e (eB2 e) r2 with hτ'def
  obtain ⟨r', hr', hmem, hlast, -⟩ := complete_leg_head 12 (Or.inr (Or.inr rfl)) (hc 12)
  have hrr : r' = r2 := by rw [hr2] at hr'; simpa using hr'.symm
  subst hrr
  have h12 : st.segs 12 ≠ [] := List.ne_nil_of_mem hmem
  obtain ⟨γ, hγ, -, hBE⟩ := hI.frame_branch.2 h12
  have hlen : (st.segs 12 ++ [γ]).length = (st.segs 12).length + 1 := by simp
  have hpos12 := List.length_pos_of_ne_nil h12
  have hlast' : legOf (st.segs 12 ++ [γ]) ((st.segs 12 ++ [γ]).length - 1) = r'.1 := by
    rw [hlen, show (st.segs 12).length + 1 - 1 = (st.segs 12).length - 1 + 1 by omega, legOf_append_singleton_succ, hlast]
  obtain ⟨ha, hs⟩ := hBE.axis_sign (k := (st.segs 12 ++ [γ]).length - 1) (by omega)
  rw [hlast'] at ha hs
  generalize hp : qAt (oth (p2 e)) ((st.segs 12 ++ [γ]).length - 1) = p at ha hs
  have hg : GoodRec Y.m Y.L Y.H r' := hgood r' (mem_all_of_mem hmem)
  obtain ⟨hface, ht1, -, -, -, hax⟩ := exit_coords Y hd hY.hL hY.hH e hg ha hs
  rw [← hτ'def] at hface ht1 hax
  have hq' : plIdx hd τ'.ax = oth p := by rw [hax, plIdx_pl]
  obtain ⟨wlo, -⟩ := hτ'.longit
  rw [mul_sub, upar_dsg] at wlo
  have hsB : (sgOf (eB2 e) : ℤ) = (sgOf e : ℤ) := (sgOf_eB e).2
  have hfst : (eB2 e).1 = (latDir e true).1 := rfl
  have hss : (sgOf e : ℤ) * (sgOf e : ℤ) = 1 := by rcases Int.units_eq_one_or (sgOf e) with h' | h' <;> simp [h']
  have hsv : ∀ b, (sgOf e : ℤ) * Uc hd (latDir e true).1 b = vperp hd (dsg e) b := fun b => by
    rw [Uc_lat_eq_vperp, ← mul_assoc, hss, one_mul]
  intro r₀ hr₀
  rw [Set.disjoint_left]
  intro w hw hz
  have hshape := fzone_exit_shape Y hd (ftgt a e) (eB2 e) τ' hY hτ' hz
  have hlow := fzone_exit_lower Y hd (ftgt a e) (eB2 e) τ' hY hτ' hz
  rw [hq', oth_oth] at hshape
  obtain ⟨k, hk⟩ := mem_all_iff.1 hr₀
  by_cases hk12 : k = 12
  · subst hk12
    obtain ⟨j, hj, hjr⟩ := exists_legOf_of_mem hk
    rw [← hjr, ← legOf_append_singleton_succ _ γ] at hw
    obtain ⟨n1, n2, n3⟩ := hBE.near_exit hY hlast' hface ht1 (k := j + 1) (by rw [hlen]; omega) hw
    rw [← sUc_eq_oxsum] at n3
    rcases hshape with h | h | h
    · linarith
    · linarith
    · linarith
  · have hfar := (hI.far_all hY hτ hk).2.2 hk12
    have hbox := abs_le.1 (box_L (hd := hd) (e := e) hY hw)
    rw [hfst, hsB] at hlow wlo
    have hv := hsv r₀.1.b
    have hs1 : (sgOf e : ℤ) = 1 ∨ (sgOf e : ℤ) = -1 := by rcases Int.units_eq_one_or (sgOf e) with h' | h' <;> simp [h']
    rcases hs1 with h | h <;> rw [h] at hlow wlo hv hfar <;> linarith [hbox.1, hbox.2]

end Avoid

end BGNd

end Percolation.Literature

end

/-!
# Part 5 (The flat gait, XXXII): the run, V — the outcome passes the guards; completeness, connectivity

The end of the run of the flat block kit (`flatKit`;
Grimmett, *Percolation*, 2nd ed. (1999), §7.3 pp. 171–174, case `H < L`): the outcome of a complete
all-good run is defined and passes the guard `FinishOK` of the renormalisation — the exit tokens
are admissible, lie in the target cell, report the provenance `e`, and their zones avoid the
examined edges (`finish_factsF`); hence the kit is **complete**
(`flat_complete`) and **connected** (`flat_connect`): along every all-good guarded run of `R`
iterations the guarded outcome is defined, and from a token with open seed the tokens handed on
have open seeds joined to the token's centre.

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §7.3 pp. 171–174.
-/

noncomputable section

namespace Percolation.Literature

open LatticeModels Contour
open scoped Classical

namespace BGNd

variable {d : ℕ} [NeZero d]
variable (Y : FlatLayout) (hd : 3 ≤ d) (a : Site 2) (e : MDir) (τ : TTok d) (hY : Y.OK)

/-! ## From boxes to supports -/

/-- **A history whose boxes avoid a region has examined edges avoiding its finite zone.** [folklore] -/
theorem disjoint_histSupp_fzoneF (hY : Y.OK) {h : BrickHist d} {c : Site 2} {e' : MDir} {τ' : TTok d}
    (hb : ∀ r ∈ h, Disjoint (boxOf Y.L Y.H r.1) (fzone Y hd c e' τ')) : Disjoint (histSupp Y.m Y.L Y.H h) (fzoneF Y hd c e' τ') := by
  rw [Finset.disjoint_left]
  intro z hz hz'
  rw [mem_histSupp_iff] at hz
  obtain ⟨r, hr, hz⟩ := hz
  have h1 : dmid z ∈ boxOf Y.L Y.H r.1 := dmid_mem_boxOf_of_mem_suppP hY.hL hY.hH r.1 hz
  have h2 : dmid z ∈ fzone Y hd c e' τ' := ((mem_fzoneF Y hd c e' τ').1 hz').2.2
  exact Set.disjoint_left.1 (hb r hr) h1 h2

/-! ## The outcome passes the guards -/

omit [NeZero d] in
/-- The onward directions: straight, or one of the two lateral ones. [folklore] -/
theorem eq_or_eB_of_ne_rev {e e' : MDir} (h : e' ≠ rev e) : e' = e ∨ e' = eB1 e ∨ e' = eB2 e := by
  rcases MDir.cases_of_ne_rev h with rfl | ⟨b, rfl⟩
  · exact Or.inl rfl
  · right
    by_cases hb : b = e.2
    · subst hb; exact Or.inr rfl
    · left; have : b = !e.2 := by cases b <;> cases h2 : e.2 <;> simp_all
      subst this; rfl

omit [NeZero d] in
/-- The two lateral directions differ. [folklore] -/
theorem eB1_ne_eB2 (e : MDir) : eB1 e ≠ eB2 e := by
  intro h; have := latDir_injective e h; cases h2 : e.2 <;> simp [h2] at this

/-- **The outcome of a complete all-good run**: defined, passing `FinishOK`, and handing on exit
tokens beyond good records of the run. [cite: GrimmettPercolation1999, §7.3 pp. 173–174] -/
theorem finish_factsF (hτ : FTAdm hd Y a e τ) {h : BrickHist d} (hI : FlatInv hd Y a e τ (ffold' hd Y a e τ h))
    (hperm : (ffold' hd Y a e τ h).all.Perm h) (hgood : AllGood Y.m Y.L Y.H h) (hs : fstep' hd Y a e τ (ffold' hd Y a e τ h) = none) :
    ∃ f, flatFinish' hd Y hY.hL hY.hH a e τ h = some f ∧ (flatKit Y hd hY).FinishOK Y.m Y.L Y.H a e h f ∧
      ∀ e', e' ≠ rev e → ∃ r ∈ h, ∃ e'' : MDir, f e' = fexitTok hd Y hY.hL hY.hH e e'' r := by
  set st := ffold' hd Y a e τ h with hst
  have hc := fstep'_eq_none_imp Y hd a e τ hs
  obtain ⟨rT, r1, r2, -, hT, h1, h2, hfin⟩ := flatFinish'_eq Y hd a e τ hY hs
  rw [← hst] at hT h1 h2
  have hgoodall : ∀ r ∈ st.all, GoodRec Y.m Y.L Y.H r := fun r hr => hgood r (hperm.subset hr)
  have memT : rT ∈ h := hperm.subset (mem_all_of_mem (List.mem_of_mem_head? hT))
  have mem1 : r1 ∈ h := hperm.subset (mem_all_of_mem (List.mem_of_mem_head? h1))
  have mem2 : r2 ∈ h := hperm.subset (mem_all_of_mem (List.mem_of_mem_head? h2))
  set f : MDir → TTok d := fun e' => if e' = eB1 e then fexitTok hd Y hY.hL hY.hH e (eB1 e) r1
    else if e' = eB2 e then fexitTok hd Y hY.hL hY.hH e (eB2 e) r2 else fexitTok hd Y hY.hL hY.hH e e rT with hf
  have hf1 : f (eB1 e) = fexitTok hd Y hY.hL hY.hH e (eB1 e) r1 := by simp only [hf, if_pos rfl]
  have hf2 : f (eB2 e) = fexitTok hd Y hY.hL hY.hH e (eB2 e) r2 := by
    simp only [hf, if_neg (eB1_ne_eB2 e).symm, if_true]
  have hfo : ∀ e', e' ≠ eB1 e → e' ≠ eB2 e → f e' = fexitTok hd Y hY.hL hY.hH e e rT := fun e' h1 h2 => by
    simp only [hf, if_neg h1, if_neg h2]
  have hfe : f e = fexitTok hd Y hY.hL hY.hH e e rT := hfo e (ne_latDir e _) (ne_latDir e _)
  -- the three tokens
  have admT := hI.ftAdm_exit_T hY hτ hgoodall hc hT
  have adm1 := hI.ftAdm_exit_B1 hY hτ hgoodall hc h1
  have adm2 := hI.ftAdm_exit_B2 hY hτ hgoodall hc h2
  have hh : ∀ r ∈ h, r ∈ st.all := fun r hr => hperm.symm.subset hr
  have disT := disjoint_histSupp_fzoneF Y hd hY fun r hr => hI.box_disjoint_exit_T hY hτ hgoodall hc hT r (hh r hr)
  have dis1 := disjoint_histSupp_fzoneF Y hd hY fun r hr => hI.box_disjoint_exit_B1 hY hτ hgoodall hc h1 r (hh r hr)
  have dis2 := disjoint_histSupp_fzoneF Y hd hY fun r hr => hI.box_disjoint_exit_B2 hY hτ hgoodall hc h2 r (hh r hr)
  have hsrc : ∀ e'' r, (fexitTok hd Y hY.hL hY.hH e e'' r).src = some e := fun _ _ => rfl
  have hre : e ≠ rev e := (rev_ne_self e).symm
  have hr1' : eB1 e ≠ rev e := fun h0 => latDir_fst_ne e (!e.2) (by change (eB1 e).1 = e.1; rw [h0]; rfl)
  have hr2' : eB2 e ≠ rev e := fun h0 => latDir_fst_ne e e.2 (by change (eB2 e).1 = e.1; rw [h0]; rfl)
  refine ⟨f, hfin, ⟨fun e' => ?_, fun e' he' => ?_⟩, fun e' he' => ?_⟩
  · show srcDirF Y hd (f e') = some e
    by_cases hb1 : e' = eB1 e
    · subst hb1; rw [hf1]; exact adm1.srcDirF_eq Y hd hY (hsrc _ _) hr1'
    by_cases hb2 : e' = eB2 e
    · subst hb2; rw [hf2]; exact adm2.srcDirF_eq Y hd hY (hsrc _ _) hr2'
    · rw [hfo e' hb1 hb2]; exact admT.srcDirF_eq Y hd hY (hsrc _ _) hre
  · show (FTAdm hd Y (a + stepVec e) e' (f e') ∧ ((f e').src = some (rev e') → a + stepVec e = 0 ∧ f e' = initTokF Y hd e')) ∧
      Y.cellOf hd (f e').pos = a + stepVec e ∧ Disjoint (histSupp Y.m Y.L Y.H h) (fzoneF Y hd (a + stepVec e) e' (f e'))
    change (FTAdm hd Y (ftgt a e) e' (f e') ∧ ((f e').src = some (rev e') → ftgt a e = 0 ∧ f e' = initTokF Y hd e')) ∧
      Y.cellOf hd (f e').pos = ftgt a e ∧ Disjoint (histSupp Y.m Y.L Y.H h) (fzoneF Y hd (ftgt a e) e' (f e'))
    -- the handed-on tokens have provenance `e ≠ rev e'`
    have hprov : ∀ e'' r, (fexitTok hd Y hY.hL hY.hH e e'' r).src = some (rev e') → ftgt a e = 0 ∧ fexitTok hd Y hY.hL hY.hH e e'' r = initTokF Y hd e' := by
      intro e'' r h0; exfalso; rw [hsrc] at h0; simp only [Option.some.injEq] at h0; apply he'; rw [h0, rev_rev]
    rcases eq_or_eB_of_ne_rev he' with rfl | rfl | rfl
    · rw [hfe]; exact ⟨⟨admT, hprov _ _⟩, admT.cellOf_eq Y hd hY, disT⟩
    · rw [hf1]; exact ⟨⟨adm1, hprov _ _⟩, adm1.cellOf_eq Y hd hY, dis1⟩
    · rw [hf2]; exact ⟨⟨adm2, hprov _ _⟩, adm2.cellOf_eq Y hd hY, dis2⟩
  · rcases eq_or_eB_of_ne_rev he' with rfl | rfl | rfl
    · exact ⟨rT, memT, _, hfe⟩
    · exact ⟨r1, mem1, _, hf1⟩
    · exact ⟨r2, mem2, _, hf2⟩

/-! ## Completeness and connectivity -/

/-- **Completeness**: along every all-good guarded run of `R` iterations from an admissible token the
guarded outcome is defined. [cite: GrimmettPercolation1999, §7.3 pp. 171–174] -/
theorem flat_complete (hτ : FTAdm hd Y a e τ) (ω : BondConfig (Site d))
    (hgood : AllGood Y.m Y.L Y.H ((flatKit Y hd hY).run Y.m Y.L Y.H a e τ FlatLayout.Rmax ω)) :
    ∃ f, (flatKit Y hd hY).gfinish Y.m Y.L Y.H a e τ ((flatKit Y hd hY).run Y.m Y.L Y.H a e τ FlatLayout.Rmax ω) = some f ∧
      ∀ e', e' ≠ rev e → ∃ r ∈ (flatKit Y hd hY).run Y.m Y.L Y.H a e τ FlatLayout.Rmax ω, ∃ e'' : MDir,
        f e' = fexitTok hd Y hY.hL hY.hH e e'' r := by
  obtain ⟨hI, hperm⟩ := run_stateF Y hd a e τ hY hτ ω FlatLayout.Rmax
  have hs := fstep_eq_none_at_R Y hd a e τ hY hτ ω hgood
  obtain ⟨f, hfin, hok, hex⟩ := finish_factsF Y hd a e τ hY hτ hI hperm hgood hs
  exact ⟨f, (flatKit Y hd hY).gfinish_eq_some Y.m Y.L Y.H (by rw [flatKit_finish]; exact hfin) hgood hok, hex⟩

/-- **Connectivity**: the tokens handed on by a successful guarded run from an admissible token with
open seed have open seeds joined to the token's centre. [cite: GrimmettPercolation1999, §7.3 pp. 172–174 (A), (B), (D)] -/
theorem flat_connect (hτ : FTAdm hd Y a e τ) (ω : BondConfig (Site d)) {f : MDir → TTok d} (hpre : IsSeed ω (square τ.ax Y.m τ.pos))
    (hf : (flatKit Y hd hY).gfinish Y.m Y.L Y.H a e τ ((flatKit Y hd hY).run Y.m Y.L Y.H a e τ FlatLayout.Rmax ω) = some f)
    {e' : MDir} (he' : e' ≠ rev e) :
    IsSeed ω (square (f e').ax Y.m (f e').pos) ∧ (openGraph ω).Reachable τ.pos (f e').pos := by
  obtain ⟨-, hgood, -⟩ := (flatKit Y hd hY).gfinish_spec Y.m Y.L Y.H hf
  obtain ⟨f', hf', hex⟩ := flat_complete Y hd a e τ hY hτ ω hgood
  rw [hf] at hf'; cases hf'
  obtain ⟨r, hr, e'', hfr⟩ := hex e' he'
  have hconn := conn_runF Y hd a e τ hY hτ hpre FlatLayout.Rmax hgood r hr
  have hg : GoodRec Y.m Y.L Y.H r := hgood r hr
  have hsub : cfgOf r ⊆ ω := by
    have hobs := (flatKit Y hd hY).run_obs Y.m Y.L Y.H hr
    have : r = (r.1, obs ω (suppP Y.m Y.L Y.H r.1)) := by rw [← hobs]
    rw [this]; exact cfgOf_obs_subset _ _ _
  rw [hfr]
  obtain ⟨hpos, hax, -⟩ := fexitTok_eq Y hd hY.hL hY.hH e e'' r
  rw [hpos, hax]
  have hj : pl hd (oth (plIdx hd r.1.a)) ≠ r.1.a := pl_oth_plIdx_ne hd r.1.a
  set sg := hreq hd Y e (dsg e'') none r.1.b
  set u := dsg e'' (oth (plIdx hd r.1.a))
  refine ⟨?_, hconn.2.trans (reachable_sStep hY.hL hY.hH hg hj u sg hsub hconn.1)⟩
  exact (isSeed_sStep hY.hL hY.hH hg hj u sg).mono hsub

end BGNd

end Percolation.Literature

end
