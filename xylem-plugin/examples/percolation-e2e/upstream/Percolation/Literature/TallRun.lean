import Percolation.Literature.TallKitDef
import Percolation.Util.Linter

/-!
# The tall gait, XVII: the guarded run of the tall kit

Analysis of the guarded run (`Kit.run`, `BlockKit.lean`)
of the tall kit (Grimmett, *Percolation*, 2nd ed. (1999), §7.3, proof of Lemma (7.52)): along the
run, the run state satisfies the invariant, holds exactly the records of the history, and the guards
of the next placement pass (its support is fresh — all recorded bricks being pairwise disjoint — and
lies in the zone); hence, while the plan has a next act, every iteration places a brick, and an
all-good run of `R` iterations ends with the plan complete.

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

/-! ## Filing a record -/

/-- The branch slots are used only when empty. [folklore] -/
theorem step_slot_cond {st : RS d} {act : Act d} {slot : Slot} {ph' : Phase} (hs : step hd Y a e τ st = some (act, slot, ph')) :
    (slot = Slot.toG1 → st.g1 = none) ∧ (slot = Slot.toG2 → st.g2 = none) := by
  unfold step at hs
  rcases hph : st.ph with _ | _ | _ | _ | _ | _ | _
  · simp only [hph] at hs
    cases hA : st.sA with
    | nil => rw [hA] at hs; simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨-, rfl, -⟩ := hs; exact ⟨fun h => Slot.noConfusion h, fun h => Slot.noConfusion h⟩
    | cons r₀ tl =>
      rw [hA] at hs; simp only at hs
      by_cases hlen : (r₀ :: tl).length ≤ Y.Pw
      · rw [if_pos hlen] at hs; simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨-, rfl, -⟩ := hs
        exact ⟨fun h => Slot.noConfusion h, fun h => Slot.noConfusion h⟩
      · rw [if_neg hlen] at hs
        by_cases hu : riseDir Y e τ = 0
        · rw [if_pos hu] at hs; simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨-, rfl, -⟩ := hs
          exact ⟨fun h => Slot.noConfusion h, fun h => Slot.noConfusion h⟩
        · rw [if_neg hu] at hs; simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨-, rfl, -⟩ := hs
          exact ⟨fun h => Slot.noConfusion h, fun h => Slot.noConfusion h⟩
  · rcases hR : st.sR with _ | ⟨rk, tl⟩
    · simp only [hph, hR] at hs; exact absurd hs (by simp)
    · simp only [hph, hR, getLast?_eq_recOf (List.cons_ne_nil rk tl), List.length_cons, Nat.add_sub_cancel] at hs
      split_ifs at hs <;> simp only [Option.some.injEq, Prod.mk.injEq] at hs <;> obtain ⟨-, rfl, -⟩ := hs <;>
        exact ⟨fun h => Slot.noConfusion h, fun h => Slot.noConfusion h⟩
  · rcases hJ : st.sJ with _ | ⟨rk, tl⟩
    · simp only [hph, hJ] at hs; exact absurd hs (by simp)
    · simp only [hph, hJ, getLast?_eq_recOf (List.cons_ne_nil rk tl), List.length_cons, Nat.add_sub_cancel] at hs
      split_ifs at hs <;> simp only [Option.some.injEq, Prod.mk.injEq] at hs <;> obtain ⟨-, rfl, -⟩ := hs <;>
        exact ⟨fun h => Slot.noConfusion h, fun h => Slot.noConfusion h⟩
  · rcases hT : st.sT with _ | ⟨rk, tl⟩
    · simp only [hph, hT] at hs; exact absurd hs (by simp)
    · simp only [hph, hT, getLast?_eq_recOf (List.cons_ne_nil rk tl), List.length_cons, Nat.add_sub_cancel] at hs
      by_cases hc1 : st.g1 = none ∧ brIdx Y a e (br1Sign e) ((recOf (rk :: tl) 0).1.b (axOf hd e)) ≤ tl.length
      · rw [if_pos hc1] at hs; simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨-, rfl, -⟩ := hs
        exact ⟨fun _ => hc1.1, fun h => absurd h (by simp)⟩
      · rw [if_neg hc1] at hs
        by_cases hc2 : st.g1 ≠ none ∧ st.g2 = none ∧ brIdx Y a e (-br1Sign e) ((recOf (rk :: tl) 0).1.b (axOf hd e)) ≤ tl.length
        · rw [if_pos hc2] at hs; simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨-, rfl, -⟩ := hs
          exact ⟨fun h => absurd h (by simp), fun _ => hc2.2.1⟩
        · rw [if_neg hc2] at hs
          by_cases hroom : tl.length < legLen Y a e e ((recOf (rk :: tl) 0).1.b (axOf hd e))
          · rw [if_pos hroom] at hs; simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨-, rfl, -⟩ := hs
            exact ⟨fun h => Slot.noConfusion h, fun h => Slot.noConfusion h⟩
          · rw [if_neg hroom] at hs
            cases hg1 : st.g1 with
            | none => rw [hg1] at hs; exact absurd hs (by simp)
            | some g =>
              rw [hg1] at hs; simp only at hs
              split_ifs at hs
              simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨-, rfl, -⟩ := hs; exact ⟨fun h => Slot.noConfusion h, fun h => Slot.noConfusion h⟩
  · rcases hB : st.sB1 with _ | ⟨rk, tl⟩
    · simp only [hph, hB] at hs; exact absurd hs (by simp)
    · cases hg1 : st.g1 with
      | none => simp only [hph, hB, hg1] at hs; exact absurd hs (by simp)
      | some g =>
        simp only [hph, hB, hg1] at hs
        by_cases hroom : (rk :: tl).length < legLen Y a e (latDir e (decide ((br1Sign e : ℤ) = 1))) (g.1.b (latOf hd e))
        · rw [if_pos hroom] at hs; simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨-, rfl, -⟩ := hs
          exact ⟨fun h => Slot.noConfusion h, fun h => Slot.noConfusion h⟩
        · rw [if_neg hroom] at hs
          cases hg2 : st.g2 with
          | none => rw [hg2] at hs; exact absurd hs (by simp)
          | some g' =>
            rw [hg2] at hs; simp only at hs
            split_ifs at hs
            simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨-, rfl, -⟩ := hs; exact ⟨fun h => Slot.noConfusion h, fun h => Slot.noConfusion h⟩
  · rcases hB : st.sB2 with _ | ⟨rk, tl⟩
    · simp only [hph, hB] at hs; exact absurd hs (by simp)
    · cases hg2 : st.g2 with
      | none => simp only [hph, hB, hg2] at hs; exact absurd hs (by simp)
      | some g =>
        simp only [hph, hB, hg2] at hs
        split_ifs at hs
        simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨-, rfl, -⟩ := hs; exact ⟨fun h => Slot.noConfusion h, fun h => Slot.noConfusion h⟩
  · simp only [hph] at hs; exact absurd hs (by simp)

omit [NeZero d] in
/-- **Filing a record adds it to the state's records**, as a permutation `r :: all`, provided a
branch slot is used only when empty. [folklore] -/
theorem perm_all_put (st : RS d) (slot : Slot) (r : BrickRec d) (h1 : slot = Slot.toG1 → st.g1 = none)
    (h2 : slot = Slot.toG2 → st.g2 = none) (ph' : Phase) : ({ st.put slot r with ph := ph' } : RS d).all.Perm (r :: st.all) := by
  cases slot <;> simp only [RS.put, RS.all]
  · exact List.Perm.refl _
  · simp only [List.append_assoc]; exact List.perm_middle
  · simp only [List.append_assoc]
    exact (List.Perm.refl _).append_left st.sA |>.trans (by
      have := @List.perm_middle _ r (st.sA ++ st.sR) (st.sJ ++ (st.sT ++ (st.g1.toList ++ (st.g2.toList ++ (st.sB1 ++ st.sB2)))))
      simpa [List.append_assoc] using this)
  · have := @List.perm_middle _ r (st.sA ++ st.sR ++ st.sJ) (st.sT ++ (st.g1.toList ++ (st.g2.toList ++ (st.sB1 ++ st.sB2))))
    simpa [List.append_assoc] using this
  · rw [h1 rfl]
    have := @List.perm_middle _ r (st.sA ++ st.sR ++ st.sJ ++ st.sT) (st.g2.toList ++ (st.sB1 ++ st.sB2))
    simpa [List.append_assoc] using this
  · rw [h2 rfl]
    have := @List.perm_middle _ r (st.sA ++ st.sR ++ st.sJ ++ st.sT ++ st.g1.toList) (st.sB1 ++ st.sB2)
    simpa [List.append_assoc] using this
  · have := @List.perm_middle _ r (st.sA ++ st.sR ++ st.sJ ++ st.sT ++ st.g1.toList ++ st.g2.toList) (st.sB1 ++ st.sB2)
    simpa [List.append_assoc] using this
  · have := @List.perm_middle _ r (st.sA ++ st.sR ++ st.sJ ++ st.sT ++ st.g1.toList ++ st.g2.toList ++ st.sB1) st.sB2
    simpa [List.append_assoc] using this

/-! ## The run state along the guarded run -/

variable (hY : Y.OK)

/-- The act behind a guarded placement: `gnext h = some β` means the plan's step at the run state of
`h` is some act `(act, slot, ph')` with `β = placeOf act`. [folklore] -/
theorem exists_step_of_gnext {h : BrickHist d} {β : BrickPos d}
    (hg : (tallKit Y hd hY).gnext Y.m Y.L Y.H a e τ h = some β) :
    ∃ act slot ph', step hd Y a e τ (foldState hd Y a e τ h) = some (act, slot, ph') ∧ β = placeOf hd Y hY.hL hY.hH e τ act ∧
      h.length < Y.Rmax ∧ AllGood Y.m Y.L Y.H h := by
  obtain ⟨hlen, hgood, hnext, -, -⟩ := (tallKit Y hd hY).gnext_spec Y.m Y.L Y.H hg
  rw [tallKit_next, tallNext] at hnext
  cases hs : step hd Y a e τ (foldState hd Y a e τ h) with
  | none => rw [hs] at hnext; exact absurd hnext (by simp)
  | some x =>
    obtain ⟨act, slot, ph'⟩ := x
    rw [hs] at hnext
    simp only [Option.map_some, Option.some.injEq] at hnext
    exact ⟨act, slot, ph', rfl, hnext.symm, hlen, hgood⟩

/-- **The run state along the guarded run**: it satisfies the invariant, and its records are exactly
those of the history (as a permutation). [cite: GrimmettPercolation1999, §7.3 pp. 171–174] -/
theorem run_state (hτ : TAdm hd Y a e τ) (ω : BondConfig (Site d)) (n : ℕ) :
    TallInv hd Y hY.hL hY.hH a e τ (foldState hd Y a e τ ((tallKit Y hd hY).run Y.m Y.L Y.H a e τ n ω)) ∧
      (foldState hd Y a e τ ((tallKit Y hd hY).run Y.m Y.L Y.H a e τ n ω)).all.Perm ((tallKit Y hd hY).run Y.m Y.L Y.H a e τ n ω) := by
  induction n with
  | zero => exact ⟨tallInv_init hd Y hY.hL hY.hH a e τ, by simp [Kit.run, foldState, RS.init, RS.all]⟩
  | succ n ih =>
    obtain ⟨hI, hperm⟩ := ih
    set h := (tallKit Y hd hY).run Y.m Y.L Y.H a e τ n ω with hh
    cases hg : (tallKit Y hd hY).gnext Y.m Y.L Y.H a e τ h with
    | none => rw [(tallKit Y hd hY).run_succ_of_none Y.m Y.L Y.H hg]; exact ⟨hI, hperm⟩
    | some β =>
      rw [(tallKit Y hd hY).run_succ_of_some Y.m Y.L Y.H hg]
      obtain ⟨act, slot, ph', hs, rfl, hlen, hgood⟩ := exists_step_of_gnext Y hd a e τ hY hg
      set r : BrickRec d := (placeOf hd Y hY.hL hY.hH e τ act, obs ω (suppP Y.m Y.L Y.H (placeOf hd Y hY.hL hY.hH e τ act))) with hr
      have hupd : foldState hd Y a e τ (r :: h) = { (foldState hd Y a e τ h).put slot r with ph := ph' } := by
        rw [foldState_cons]; unfold update; rw [hs]
      rw [hupd]
      have hgoodall : ∀ r' ∈ (foldState hd Y a e τ h).all, GoodRec Y.m Y.L Y.H r' := fun r' hr' => hgood r' (hperm.subset hr')
      have hlenall : (foldState hd Y a e τ h).all.length < Y.Rmax := by rw [hperm.length_eq]; exact hlen
      have hR : (foldState hd Y a e τ h).sR.length ≤ Y.Rmax := by
        have : (foldState hd Y a e τ h).sR.length ≤ (foldState hd Y a e τ h).all.length := by simp only [RS.all, List.length_append]; omega
        omega
      have hJ : (foldState hd Y a e τ h).sJ.length ≤ Y.Rmax := by
        have : (foldState hd Y a e τ h).sJ.length ≤ (foldState hd Y a e τ h).all.length := by simp only [RS.all, List.length_append]; omega
        omega
      obtain ⟨c1, c2⟩ := step_slot_cond Y hd a e τ hs
      exact ⟨tallInv_update Y hd hY.hL hY.hH a e τ hY hτ hI hgoodall hR hJ hs _, (perm_all_put _ slot r c1 c2 ph').trans (hperm.cons r)⟩

/-- **The guards pass**: at the run state of the guarded run, the support of the next placement of the
plan is fresh and lies in the zone. [cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
theorem guards_pass (hτ : TAdm hd Y a e τ) (ω : BondConfig (Site d)) (n : ℕ) {act : Act d} {slot : Slot} {ph' : Phase}
    (hs : step hd Y a e τ (foldState hd Y a e τ ((tallKit Y hd hY).run Y.m Y.L Y.H a e τ n ω)) = some (act, slot, ph'))
    (hgood : AllGood Y.m Y.L Y.H ((tallKit Y hd hY).run Y.m Y.L Y.H a e τ n ω)) :
    Disjoint (suppP Y.m Y.L Y.H (placeOf hd Y hY.hL hY.hH e τ act)) (histSupp Y.m Y.L Y.H ((tallKit Y hd hY).run Y.m Y.L Y.H a e τ n ω)) ∧
      suppP Y.m Y.L Y.H (placeOf hd Y hY.hL hY.hH e τ act) ⊆ zoneF Y hd a e τ := by
  obtain ⟨hI, hperm⟩ := run_state Y hd a e τ hY hτ ω n
  set h := (tallKit Y hd hY).run Y.m Y.L Y.H a e τ n ω with hh
  set st := foldState hd Y a e τ h with hst
  -- the post-state
  set r : BrickRec d := (placeOf hd Y hY.hL hY.hH e τ act, ∅) with hr
  set st' : RS d := { st.put slot r with ph := ph' } with hst'
  have hgoodall : ∀ r' ∈ st.all, GoodRec Y.m Y.L Y.H r' := fun r' hr' => hgood r' (hperm.subset hr')
  obtain ⟨-, -, -, -, -, -, hlenR⟩ := all_length_lt Y hd hY.hL hY.hH a e τ hY hτ hI
  have hR : st.sR.length ≤ Y.Rmax := by
    have : st.sR.length ≤ st.all.length := by simp only [RS.all, List.length_append]; omega
    omega
  have hJ : st.sJ.length ≤ Y.Rmax := by
    have : st.sJ.length ≤ st.all.length := by simp only [RS.all, List.length_append]; omega
    omega
  have hI' : TallInv hd Y hY.hL hY.hH a e τ st' := tallInv_update Y hd hY.hL hY.hH a e τ hY hτ hI hgoodall hR hJ hs ∅
  obtain ⟨c1, c2⟩ := step_slot_cond Y hd a e τ hs
  have hperm' : st'.all.Perm (r :: st.all) := perm_all_put st slot r c1 c2 ph'
  have hpw := pairwise_disjoint_all Y hd hY.hL hY.hH a e τ hY hτ hI'
  have hpw' : (r :: st.all).Pairwise (BoxDisj Y.L Y.H) := (hperm'.pairwise_iff (fun h => h.symm)).1 hpw
  rw [List.pairwise_cons] at hpw'
  constructor
  · rw [Finset.disjoint_left]
    intro z hz hz'
    rw [mem_histSupp_iff] at hz'
    obtain ⟨r', hr', hz'⟩ := hz'
    have hd' := hpw'.1 r' (hperm.symm.subset hr')
    exact Finset.disjoint_left.1 (disjoint_suppP_of_disjoint_boxOf hY.hL hY.hH hY.hL hY.hH hd') hz hz'
  · have hmem : r ∈ st'.all := hperm'.symm.subset List.mem_cons_self
    exact suppP_subset_zoneF Y hd a e τ hY hτ (boxOf_subset_zoneRegion Y hd hY.hL hY.hH a e τ hY hτ hI' hmem)

/-- **While the plan has a next act, every iteration of an all-good guarded run places a brick.**
[cite: GrimmettPercolation1999, §7.3 pp. 171–174] -/
theorem run_progress (hτ : TAdm hd Y a e τ) (ω : BondConfig (Site d)) (n : ℕ)
    (hgood : AllGood Y.m Y.L Y.H ((tallKit Y hd hY).run Y.m Y.L Y.H a e τ n ω)) :
    step hd Y a e τ (foldState hd Y a e τ ((tallKit Y hd hY).run Y.m Y.L Y.H a e τ n ω)) = none ∨
      ((tallKit Y hd hY).run Y.m Y.L Y.H a e τ n ω).length = n := by
  induction n with
  | zero => right; rfl
  | succ n ih =>
    set h := (tallKit Y hd hY).run Y.m Y.L Y.H a e τ n ω with hh
    have hgood_n : AllGood Y.m Y.L Y.H h := by
      cases hg : (tallKit Y hd hY).gnext Y.m Y.L Y.H a e τ h with
      | none => rw [(tallKit Y hd hY).run_succ_of_none Y.m Y.L Y.H hg] at hgood; exact hgood
      | some β => rw [(tallKit Y hd hY).run_succ_of_some Y.m Y.L Y.H hg, allGood_cons] at hgood; exact hgood.2
    rcases ih hgood_n with hnone | hlen
    · -- no act: nothing changes
      have hg : (tallKit Y hd hY).gnext Y.m Y.L Y.H a e τ h = none := by
        unfold Kit.gnext; rw [tallKit_next, tallNext, hnone]; simp
      rw [(tallKit Y hd hY).run_succ_of_none Y.m Y.L Y.H hg]; left; exact hnone
    · cases hs : step hd Y a e τ (foldState hd Y a e τ h) with
      | none =>
        have hg : (tallKit Y hd hY).gnext Y.m Y.L Y.H a e τ h = none := by
          unfold Kit.gnext; rw [tallKit_next, tallNext, hs]; simp
        rw [(tallKit Y hd hY).run_succ_of_none Y.m Y.L Y.H hg]; left; exact hs
      | some x =>
        obtain ⟨act, slot, ph'⟩ := x
        obtain ⟨hdisj, hzone⟩ := guards_pass Y hd a e τ hY hτ ω n hs hgood_n
        obtain ⟨hI, hperm⟩ := run_state Y hd a e τ hY hτ ω n
        obtain ⟨-, -, -, -, -, -, hlenR⟩ := all_length_lt Y hd hY.hL hY.hH a e τ hY hτ hI
        have hlt : h.length < (tallKit Y hd hY).R := by rw [tallKit_R, ← hperm.length_eq]; omega
        have hg : (tallKit Y hd hY).gnext Y.m Y.L Y.H a e τ h = some (placeOf hd Y hY.hL hY.hH e τ act) := by
          unfold Kit.gnext
          rw [if_pos ⟨hlt, hgood_n⟩, tallKit_next, tallNext, hs]
          simp only [Option.map_some]
          rw [if_pos ⟨hdisj, by rw [tallKit_zone]; exact hzone⟩]
        rw [(tallKit Y hd hY).run_succ_of_some Y.m Y.L Y.H hg]
        right; rw [List.length_cons, hlen]

/-- **At the end of an all-good guarded run of `R` iterations the plan is complete** (no next act).
[cite: GrimmettPercolation1999, §7.3 p. 174] -/
theorem step_eq_none_at_R (hτ : TAdm hd Y a e τ) (ω : BondConfig (Site d))
    (hgood : AllGood Y.m Y.L Y.H ((tallKit Y hd hY).run Y.m Y.L Y.H a e τ Y.Rmax ω)) :
    step hd Y a e τ (foldState hd Y a e τ ((tallKit Y hd hY).run Y.m Y.L Y.H a e τ Y.Rmax ω)) = none := by
  rcases run_progress Y hd a e τ hY hτ ω Y.Rmax hgood with h | hlen
  · exact h
  · exfalso
    obtain ⟨hI, hperm⟩ := run_state Y hd a e τ hY hτ ω Y.Rmax
    obtain ⟨-, -, -, -, -, -, hlenR⟩ := all_length_lt Y hd hY.hL hY.hH a e τ hY hτ hI
    rw [hperm.length_eq, hlen] at hlenR
    omega

end BGNd

end Percolation.Literature

end
