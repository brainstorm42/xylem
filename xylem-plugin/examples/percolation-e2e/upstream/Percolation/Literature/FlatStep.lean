import Percolation.Literature.FlatInv
import Percolation.Util.Linter

/-!
# The flat gait, VII: the plan preserves the invariant

One step of the plan of the flat gait (`fstep`,
`FlatRoute.lean`; Grimmett, *Percolation*, 2nd ed. (1999), §7.3 pp. 171–174, case `H < L`) preserves
the invariant `FlatInv` (`FlatInv.lean`) when the record it steps off is good: the meaning of the
current segment (`curOf_some`, `curOf_none`), the unfolding of a step (`fstep_eq_some`), the generic
start and growth of legs by the requested hops, and the dispatch over the thirteen segments
(`flatInv_update`).

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §7.3 pp. 171–174.
-/

noncomputable section

namespace Percolation.Literature

open LatticeModels Contour
open scoped Classical

namespace BGNd

variable {d : ℕ} [NeZero d] (hd : 3 ≤ d) (Y : FlatLayout) (hL : Y.m + 1 ≤ Y.L) (hH : 2 * Y.m + 2 ≤ Y.H) (a : Site 2) (e : MDir) (τ : TTok d)

/-! ## The current segment -/

omit [NeZero d] in
theorem firstInc_spec (ej : MDir) (st : FS d) : ∀ n k, 13 - k = n →
    (∀ i, firstInc' hd Y a e τ ej st k = some i → k ≤ i.val ∧ ¬complete' hd Y a e τ ej i (st.segs i) ∧
      ∀ j : Fin 13, k ≤ j.val → j < i → complete' hd Y a e τ ej j (st.segs j)) ∧
    (firstInc' hd Y a e τ ej st k = none → ∀ j : Fin 13, k ≤ j.val → complete' hd Y a e τ ej j (st.segs j)) := by
  intro n
  induction n with
  | zero =>
    intro k hk
    have hk' : ¬(k < 13) := by omega
    rw [firstInc', dif_neg hk']
    exact ⟨fun i h => absurd h (by simp), fun _ j hj => absurd j.isLt (by omega)⟩
  | succ n ih =>
    intro k hk
    have hk' : k < 13 := by omega
    obtain ⟨ih1, ih2⟩ := ih (k + 1) (by omega)
    rw [firstInc', dif_pos hk']
    by_cases hc : complete' hd Y a e τ ej ⟨k, hk'⟩ (st.segs ⟨k, hk'⟩)
    · rw [if_pos hc]
      refine ⟨fun i hi => ?_, fun hnone j hj => ?_⟩
      · obtain ⟨h1, h2, h3⟩ := ih1 i hi
        refine ⟨by omega, h2, fun j hj hji => ?_⟩
        rcases Nat.eq_or_lt_of_le hj with hjk | hjk
        · have : j = ⟨k, hk'⟩ := Fin.ext hjk.symm
          rw [this]; exact hc
        · exact h3 j (by omega) hji
      · rcases Nat.eq_or_lt_of_le hj with hjk | hjk
        · have : j = ⟨k, hk'⟩ := Fin.ext hjk.symm
          rw [this]; exact hc
        · exact ih2 hnone j (by omega)
    · rw [if_neg hc]
      refine ⟨fun i hi => ?_, fun h => absurd h (by simp)⟩
      simp only [Option.some.injEq] at hi
      subst hi
      exact ⟨le_rfl, hc, fun j hj hji => absurd hji (by simp [Fin.lt_def]; omega)⟩

omit [NeZero d] in
/-- **The current segment is the least incomplete one.** [folklore] -/
theorem curOf_some {ej : MDir} {st : FS d} {i : Fin 13} (h : curOf' hd Y a e τ ej st = some i) :
    ¬complete' hd Y a e τ ej i (st.segs i) ∧ ∀ j : Fin 13, j < i → complete' hd Y a e τ ej j (st.segs j) := by
  obtain ⟨-, h2, h3⟩ := (firstInc_spec hd Y a e τ ej st 13 0 rfl).1 i h
  exact ⟨h2, fun j hj => h3 j (Nat.zero_le _) hj⟩

omit [NeZero d] in
/-- **No current segment: all are complete.** [folklore] -/
theorem curOf_none {ej : MDir} {st : FS d} (h : curOf' hd Y a e τ ej st = none) (j : Fin 13) : complete' hd Y a e τ ej j (st.segs j) :=
  (firstInc_spec hd Y a e τ ej st 13 0 rfl).2 h j (Nat.zero_le _)

omit [NeZero d] in
/-- **Unfolding a step.** [folklore] -/
theorem fstep_eq_some {st : FS d} {act : Act d} {i : Fin 13} (h : fstep' hd Y a e τ st = some (act, i)) :
    curOf' hd Y a e τ (eJOf hd Y a e τ st) st = some i ∧ segAct' hd Y e τ (eJOf hd Y a e τ st) i (st.segs i) (startRec st i) = some act := by
  unfold fstep' at h
  simp only at h
  cases hc : curOf' hd Y a e τ (eJOf hd Y a e τ st) st with
  | none => rw [hc] at h; exact absurd h (by simp)
  | some i' =>
    rw [hc] at h; simp only at h
    cases hs : segAct' hd Y e τ (eJOf hd Y a e τ st) i' (st.segs i') (startRec st i') with
    | none => rw [hs] at h; exact absurd h (by simp)
    | some act' =>
      rw [hs] at h; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, hs⟩

/-! ## Filing a record -/

omit [NeZero d] in
/-- Filing into a segment. [folklore] -/
@[simp] theorem put_segs_self (st : FS d) (i : Fin 13) (r : BrickRec d) : (st.put i r).segs i = r :: st.segs i := by
  simp [FS.put]

omit [NeZero d] in
/-- Filing leaves the other segments. [folklore] -/
theorem put_segs_of_ne (st : FS d) {i j : Fin 13} (h : j ≠ i) (r : BrickRec d) : (st.put i r).segs j = st.segs j := by
  simp [FS.put, h]

omit [NeZero d] in
/-- The start record of a segment is the head of its start segment. [folklore] -/
theorem startRec_eq (st : FS d) (i : Fin 13) : startRec st i = (st.segs (startOf i)).head? := rfl

/-! ## Generic growth -/

section Grow

variable {hd Y e}

/-- **Growing a diagonal leg by the requested diagonal hop of its head.** [cite: GrimmettPercolation1999, §7.3 pp. 172–174 (B)] -/
theorem grow_diag {σ : Fin 2 → ℤˣ} {zmode : Option Bool} {q₀ : Fin 2} {r : BrickRec d} {tl : List (BrickRec d)}
    (h : DiagLeg hd Y e σ zmode q₀ (r :: tl)) (hg : GoodRec Y.m Y.L Y.H r) (o : Finset (Sym2 (Site d))) :
    DiagLeg hd Y e σ zmode q₀ ((fplaceOf hd Y hL hH e τ (diagHop hd Y e σ zmode r), o) :: r :: tl) := by
  have hlen : (r :: tl).length = tl.length + 1 := rfl
  obtain ⟨hax, hsx⟩ := h.axis_sign (k := tl.length) (by simp)
  rw [legOf_cons_length] at hax hsx
  have hq : plIdx hd r.1.a = qAt q₀ tl.length := by rw [hax, plIdx_pl]
  apply diagLeg_cons h
  rw [hlen, Nat.add_sub_cancel, legOf_cons_length, qAt_succ]
  show DHop hd Y e σ zmode (oth (qAt q₀ tl.length)) r.1 (sStep hL hH r (pl hd (oth (plIdx hd r.1.a))) (σ (oth (plIdx hd r.1.a))) (hreq hd Y e σ zmode r.1.b))
  rw [hq]
  exact dHop_sStep hd Y hL hH e hg σ zmode (by rw [oth_oth]; exact hax) (by rw [oth_oth]; exact hsx)

/-- **Starting a diagonal leg by the requested diagonal hop off a plane plate.** [cite: GrimmettPercolation1999, §7.3 pp. 172–174 (B)] -/
theorem start_diag {σ : Fin 2 → ℤˣ} {zmode : Option Bool} {s : BrickRec d} {q : Fin 2}
    (ha : s.1.a = pl hd (oth q)) (hs : s.1.s = σ (oth q)) (hg : GoodRec Y.m Y.L Y.H s) (o : Finset (Sym2 (Site d))) :
    DiagLeg hd Y e σ zmode q [(fplaceOf hd Y hL hH e τ (diagHop hd Y e σ zmode s), o)] ∧
      DHop hd Y e σ zmode q s.1 (legOf [(fplaceOf hd Y hL hH e τ (diagHop hd Y e σ zmode s), o)] 0) := by
  have hq : plIdx hd s.1.a = oth q := by rw [ha, plIdx_pl]
  have hD : DHop hd Y e σ zmode q s.1 (fplaceOf hd Y hL hH e τ (diagHop hd Y e σ zmode s)) := by
    show DHop hd Y e σ zmode q s.1 (sStep hL hH s (pl hd (oth (plIdx hd s.1.a))) (σ (oth (plIdx hd s.1.a))) (hreq hd Y e σ zmode s.1.b))
    rw [hq, oth_oth]
    exact dHop_sStep hd Y hL hH e hg σ zmode ha hs
  have h0 : legOf [(fplaceOf hd Y hL hH e τ (diagHop hd Y e σ zmode s), o)] 0 = fplaceOf hd Y hL hH e τ (diagHop hd Y e σ zmode s) := by
    have := legOf_cons_length (fplaceOf hd Y hL hH e τ (diagHop hd Y e σ zmode s), o) []; rwa [List.length_nil] at this
  refine ⟨diagLeg_singleton hd Y e hD.axis hD.sign, by rw [h0]; exact hD⟩

end Grow

/-! ## Membership and completeness, unfolded -/

omit [NeZero d] in
/-- A record of a segment is a record of the state. [folklore] -/
theorem mem_all_of_mem {st : FS d} {k : Fin 13} {r : BrickRec d} (h : r ∈ st.segs k) : r ∈ st.all := by
  unfold FS.all; rw [List.mem_flatMap]; exact ⟨k, List.mem_finRange k, h⟩

/-- The head of a list is its newest record: `legOf` at `length - 1`. [folklore] -/
theorem legOf_head' {r : BrickRec d} {tl : List (BrickRec d)} {n : ℕ} (hn : tl.length = n) : legOf (r :: tl) n = r.1 := by
  subst hn; exact legOf_cons_length r tl

/-! ## The dispatch -/

/-- **One step of the plan preserves the invariant**, the record stepped off being good.
[cite: GrimmettPercolation1999, §7.3 pp. 171–174] -/
theorem flatInv_update (hτ : FTAdm hd Y a e τ) {st : FS d} (hI : FlatInv hd Y a e τ st) (hgood : ∀ r ∈ st.all, GoodRec Y.m Y.L Y.H r)
    {act : Act d} {i : Fin 13} (hs : fstep' hd Y a e τ st = some (act, i)) (o : Finset (Sym2 (Site d))) :
    FlatInv hd Y a e τ (st.put i (fplaceOf hd Y hL hH e τ act, o)) := by
  obtain ⟨hcur, hsa⟩ := fstep_eq_some hd Y a e τ hs
  obtain ⟨hinc, hbefore⟩ := curOf_some hd Y a e τ hcur
  have hafter : ∀ j : Fin 13, i < j → st.segs j = [] := by
    intro j hj; by_contra h; exact hinc (hI.order j i hj h)
  set r : BrickRec d := (fplaceOf hd Y hL hH e τ act, o) with hr
  -- the jog direction is unchanged, unless the riser grows (and then every later segment is empty)
  set ej := eJOf hd Y a e τ st with hej
  have hE : i ≠ 1 → eJOf hd Y a e τ (st.put i r) = ej := by
    intro h1; simp only [hej, eJOf, put_segs_of_ne _ h1.symm]
  refine ⟨fun i' j hj hne => ?_, fun k => ?_, fun k l hl hne => ?_⟩
  rotate_right
  · -- no early stop
    by_cases hk : k = i
    · subst hk
      rw [put_segs_self] at hl hne
      rw [List.suffix_cons_iff] at hl
      rcases hl with rfl | hl
      · exact absurd rfl hne
      · by_cases hl' : l = st.segs k
        · subst hl'
          by_cases hi1 : k = 1
          · subst hi1; revert hinc; simp only [complete', kindOf, Matrix.cons_val]; exact id
          · rw [hE hi1]; exact hinc
        · by_cases hi1 : k = 1
          · subst hi1
            have := hI.nostop 1 l hl hl'
            revert this; simp only [complete', kindOf, Matrix.cons_val]; exact id
          · rw [hE hi1]; exact hI.nostop k l hl hl'
    · rw [put_segs_of_ne _ hk] at hl hne
      by_cases hi1 : i = 1
      · subst hi1
        -- segments other than `1` are `0` (whose completeness ignores the jog direction) or empty
        by_cases hk0 : k = 0
        · subst hk0
          have := hI.nostop 0 l hl hne
          revert this; simp only [complete', kindOf, Matrix.cons_val]; exact id
        · have : 1 < k := by
            rcases lt_trichotomy 1 k with h | h | h
            · exact h
            · exact absurd h.symm hk
            · exact absurd (show k = 0 from Fin.ext (by have := Fin.lt_def.1 h; simp at this ⊢; omega)) hk0
          rw [hafter k this] at hl hne
          exact absurd (List.suffix_nil.1 hl) hne
      · rw [hE hi1]; exact hI.nostop k l hl hne
  · -- order
    by_cases hi1 : i = 1
    · -- only segments 0, 1 are nonempty; completeness of segment 0 does not depend on the jog direction
      subst hi1
      have hi' : i' ≤ 1 := by
        by_contra h; push Not at h
        exact hne (by rw [put_segs_of_ne _ (ne_of_gt h)]; exact hafter i' h)
      have hj0 : j = 0 := by
        apply Fin.ext; have := Fin.lt_def.1 hj; have := Fin.le_def.1 hi'; simp at *; omega
      subst hj0
      have hc := hbefore 0 (by decide)
      rw [put_segs_of_ne _ (by decide)]
      revert hc
      simp only [complete', kindOf, Matrix.cons_val]
      exact id
    rw [hE hi1]
    by_cases h1 : i' = i
    · subst h1
      rw [put_segs_of_ne _ (ne_of_lt hj)]; exact hbefore j hj
    · rw [put_segs_of_ne _ h1] at hne
      have hlt : i' < i := by
        rcases lt_trichotomy i' i with h | h | h
        · exact h
        · exact absurd h h1
        · exact absurd (hafter i' h) hne
      rw [put_segs_of_ne _ (ne_of_lt (hj.trans hlt))]; exact hI.order i' j hj hne
  -- the segment invariants
  by_cases hk : k = i
  swap
  · rw [put_segs_of_ne _ hk]
    by_cases hks : startOf k = i
    · have hki : i < k := by
        have : startOf k ≤ k ∧ (startOf k = k → k = 0) := by
          fin_cases k <;> simp [startOf]
        rw [hks] at this
        rcases lt_or_eq_of_le this.1 with h | h
        · exact h
        · exact absurd (this.2 h ▸ h) (by rintro rfl; exact hk (this.2 h))
      rw [hafter k hki]; exact segOK_nil hd Y e τ _ k _
    · rw [put_segs_of_ne _ hks]
      by_cases hi1 : i = 1
      · subst hi1
        by_cases hk0 : k = 0
        · subst hk0; exact hI.segOK 0
        · have : 1 < k := by
            rcases lt_trichotomy 1 k with h | h | h
            · exact h
            · exact absurd h.symm hk
            · exact absurd (show k = 0 from Fin.ext (by have := Fin.lt_def.1 h; simp at this ⊢; omega)) hk0
          rw [hafter k this]; exact segOK_nil hd Y e τ _ k _
      · rw [hE hi1]; exact hI.segOK k
  subst hk
  rw [put_segs_self]
  have hK := hI.segOK k
  -- case analysis on the segment
  fin_cases k
  all_goals simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk] at *
  · -- segment 0: the lead-in
    show (r :: st.segs 0) ≠ [] → DiagLeg hd Y e (dsg e) (some (zbOf hd Y e τ)) (plIdx hd τ.ax) (r :: st.segs 0) ∧
      legOf (r :: st.segs 0) 0 = firstPlate hd e τ ∧ (r :: st.segs 0).length ≤ 3
    intro _
    have hK' : st.segs 0 ≠ [] → DiagLeg hd Y e (dsg e) (some (zbOf hd Y e τ)) (plIdx hd τ.ax) (st.segs 0) ∧
        legOf (st.segs 0) 0 = firstPlate hd e τ ∧ (st.segs 0).length ≤ 3 := hK
    have hfa : (firstPlate hd e τ).a = pl hd (plIdx hd τ.ax) := by rcases hτ.ax_plane with h | h <;> simp [firstPlate, h, plIdx_pl]
    have hfs : (firstPlate hd e τ).s = dsg e (plIdx hd τ.ax) := rfl
    rcases hl : st.segs 0 with _ | ⟨A, _ | ⟨A', _ | ⟨A'', tl⟩⟩⟩
    · -- the first plate
      simp only [segAct', kindOf, Matrix.cons_val, hl, Option.some.injEq] at hsa
      subst hsa
      have hr1 : r.1 = firstPlate hd e τ := by rw [hr]; rfl
      refine ⟨diagLeg_singleton hd Y e (by rw [hr1, hfa]) (by rw [hr1, hfs]), ?_, by simp⟩
      have := legOf_cons_length r ([] : List (BrickRec d)); rw [List.length_nil] at this; rw [this, hr1]
    · -- the first diagonal hop, off the first plate
      simp only [segAct', kindOf, fdirOf, Matrix.cons_val, hl, Option.some.injEq] at hsa
      subst hsa
      rw [hl] at hK'
      obtain ⟨hD, h0, -⟩ := hK' (by simp)
      refine ⟨grow_diag hL hH τ hD (hgood A (mem_all_of_mem (k := 0) (by rw [hl]; simp))) o, ?_, by simp⟩
      rw [legOf_cons_of_lt _ _ (by simp), h0]
    · -- the second diagonal hop
      simp only [segAct', kindOf, fdirOf, Matrix.cons_val, hl, Option.some.injEq] at hsa
      subst hsa
      rw [hl] at hK'
      obtain ⟨hD, h0, -⟩ := hK' (by simp)
      refine ⟨grow_diag hL hH τ hD (hgood A (mem_all_of_mem (k := 0) (by rw [hl]; simp))) o, ?_, by simp⟩
      rw [legOf_cons_of_lt _ _ (by simp), h0]
    · -- a complete lead-in has no act
      exfalso; apply hinc; simp only [complete', kindOf, Matrix.cons_val, hl]; simp
  · -- segment 1: the riser, off the lead-in's head
    show (r :: st.segs 1) ≠ [] → Riser hd Y (dsg e) (friseDir hd Y e τ) (plIdx hd τ.ax) (rstart hd e τ (st.segs 0)) (r :: st.segs 1)
    intro _
    -- the lead-in is complete: three plates, its head `A` has the token's axis again
    have hc0 := hbefore 0 (by decide)
    have hS0 : SegOK hd Y e τ ej 0 (st.segs 0) (st.segs (startOf 0)) := hI.segOK 0
    obtain ⟨A, tlA, hl0⟩ : ∃ A tl, st.segs 0 = A :: tl := List.exists_cons_of_ne_nil (by intro h; rw [h] at hc0; simp [complete'] at hc0)
    simp only [complete', kindOf, Matrix.cons_val, hl0] at hc0
    obtain ⟨hD0, -, hlen0⟩ := hS0 (by rw [hl0]; simp)
    rw [hl0] at hD0 hlen0
    have htlA : tlA.length = 2 := by simp at hc0 hlen0; omega
    have hA1 : startRec st 1 = some A := by simp [startRec_eq, startOf, hl0]
    have hrs : rstart hd e τ (st.segs 0) = A.1 := by simp [rstart, hl0]
    obtain ⟨hAa, hAs⟩ := hD0.axis_sign (k := 2) (by simp [htlA])
    have hq2 : qAt (plIdx hd τ.ax) 2 = plIdx hd τ.ax := by rw [show qAt (plIdx hd τ.ax) 2 = qAt (plIdx hd τ.ax) (0 + 2) from rfl, qAt_add_two, qAt_zero]
    rw [legOf_head' htlA, hq2] at hAa hAs
    have hsr := hA1
    have hgA : GoodRec Y.m Y.L Y.H A := hgood A (mem_all_of_mem (k := 0) (by rw [hl0]; simp))
    rw [hrs]
    have hR : Riser hd Y (dsg e) (friseDir hd Y e τ) (plIdx hd τ.ax) A.1 (st.segs 1) := by
      by_cases h1 : st.segs 1 = []
      · rw [h1]; exact riser_nil hd Y hAa hAs
      · have := hK h1; simp only [startOf, Fin.isValue, Matrix.cons_val] at this; rw [hrs] at this; exact this
    rcases hl1 : st.segs 1 with _ | ⟨r', tl⟩
    · -- the first up / down hop, off the lead-in's head
      simp only [segAct', kindOf, fdirOf, Matrix.cons_val, hl1, hsr, Option.some.injEq] at hsa
      subst hsa
      rw [hl1] at hR
      refine riser_cons_up hR (j := 0) rfl ?_
      rw [if_pos rfl, qAt_zero]
      exact vHop_sStep hd Y hL hH e hgA (dsg e) none (friseDir hd Y e τ) (q := plIdx hd τ.ax) hAa
    · rw [hl1] at hR hinc
      have hg' : GoodRec Y.m Y.L Y.H r' := hgood r' (mem_all_of_mem (k := 1) (by rw [hl1]; simp))
      by_cases hax : r'.1.a = ax0 hd
      · -- a landing hop off the horizontal head, of even index
        have hev : tl.length % 2 = 0 := by
          by_contra hodd
          have := ((hR.axis_sign (k := tl.length) (by simp)).2 (by omega)).1
          rw [legOf_cons_length, hax] at this; exact absurd this.symm (pl_ne_ax0 hd _)
        obtain ⟨j, hj⟩ : ∃ j, tl.length = 2 * j := ⟨tl.length / 2, by omega⟩
        obtain ⟨pv, hpva, hact⟩ : ∃ pv : BrickRec d, pv.1.a = pl hd (qAt (plIdx hd τ.ax) j) ∧
            act = hop hd Y e (dsg e) none r' (pl hd (oth (plIdx hd pv.1.a))) (dsg e (oth (plIdx hd pv.1.a))) := by
          rcases tl with _ | ⟨r'', tl'⟩
          · refine ⟨A, ?_, ?_⟩
            · have : j = 0 := by simp at hj; omega
              rw [this, qAt_zero, hAa]
            · simp only [segAct', kindOf, fdirOf, Matrix.cons_val, hl1, hsr, hax, if_true, Option.some.injEq] at hsa
              exact hsa.symm
          · refine ⟨r'', ?_, ?_⟩
            · have hlen' : tl'.length = 2 * j - 1 := by simp at hj; omega
              have hj0 : 0 < j := by simp at hj; omega
              have := ((hR.axis_sign (k := tl'.length) (by simp)).2 (by omega)).1
              rw [legOf_cons_of_lt _ _ (by simp), legOf_cons_length] at this
              rw [this, hlen', show (2 * j - 1) / 2 + 1 = j by omega]
            · simp only [segAct', kindOf, fdirOf, Matrix.cons_val, hl1, hax, if_true, Option.some.injEq] at hsa
              exact hsa.symm
        subst hact
        refine riser_cons_land hR (j := j) (by simp [hj]) ?_
        rw [legOf_head' hj, show qAt (plIdx hd τ.ax) (j + 1) = oth (qAt (plIdx hd τ.ax) j) from qAt_succ _ _]
        have := pHop_sStep hd Y hL hH e hg' (dsg e) none (oth (plIdx hd pv.1.a)) (dsg e (oth (plIdx hd pv.1.a))) hax
        rw [hpva, plIdx_pl, oth_oth] at this
        show PHop hd Y (dsg e (oth (oth (qAt (plIdx hd τ.ax) j)))) (dsg e (oth (qAt (plIdx hd τ.ax) j))) (oth (qAt (plIdx hd τ.ax) j)) r'.1
          (sStep hL hH r' (pl hd (oth (plIdx hd pv.1.a))) (dsg e (oth (plIdx hd pv.1.a))) (hreq hd Y e (dsg e) none r'.1.b))
        rw [oth_oth, hpva, plIdx_pl]; exact this
      · -- an up / down hop off the plane head, of odd index
        have hodd : tl.length % 2 = 1 := by
          by_contra hev
          have := ((hR.axis_sign (k := tl.length) (by simp)).1 (by omega)).1
          rw [legOf_cons_length] at this; exact hax this
        obtain ⟨j, hj⟩ : ∃ j, tl.length = 2 * j + 1 := ⟨tl.length / 2, by omega⟩
        obtain ⟨hra, -⟩ := (hR.axis_sign (k := tl.length) (by simp)).2 hodd
        rw [legOf_cons_length, hj, show (2 * j + 1) / 2 + 1 = j + 1 by omega] at hra
        simp only [segAct', kindOf, fdirOf, Matrix.cons_val, hl1, hsr, hax, if_false, Option.some.injEq] at hsa
        subst hsa
        refine riser_cons_up hR (j := j + 1) (by simp [hj]; ring) ?_
        rw [if_neg (by omega), show 2 * (j + 1) - 1 = tl.length by omega, legOf_cons_length]
        exact vHop_sStep hd Y hL hH e hg' (dsg e) none (friseDir hd Y e τ) hra
  · -- segment 2: the preamble, off the riser's head
    rw [put_segs_of_ne _ (by decide)]
    show (r :: st.segs 2) ≠ [] → ∃ s ∈ (st.segs 1).head?, ∃ q, DiagLeg hd Y e (dsg e) none q (r :: st.segs 2) ∧
      DHop hd Y e (dsg e) none q s.1 (legOf (r :: st.segs 2) 0)
    intro _
    rcases hl : st.segs 2 with _ | ⟨r', tl⟩
    · -- the first hop: the riser is complete, its head `s` is a plane plate
      have hc := hbefore 1 (by decide)
      obtain ⟨s, tl1, hl1⟩ : ∃ s tl, st.segs 1 = s :: tl := List.exists_cons_of_ne_nil (by intro h; rw [h] at hc; simp [complete'] at hc)
      have hK1 : SegOK hd Y e τ ej 1 (st.segs 1) (st.segs (startOf 1)) := hI.segOK 1
      simp only [SegOK, startOf, Fin.isValue, Matrix.cons_val] at hK1
      have hR : Riser hd Y (dsg e) (friseDir hd Y e τ) (plIdx hd τ.ax) (rstart hd e τ (st.segs 0)) (st.segs 1) := hK1 (by rw [hl1]; simp)
      simp only [complete', kindOf, Matrix.cons_val, hl1] at hc
      rw [hl1] at hR
      have hodd : tl1.length % 2 = 1 := by
        by_contra hev
        have := ((hR.axis_sign (k := tl1.length) (by simp)).1 (by omega)).1
        rw [legOf_cons_length] at this; exact hc.1 this
      obtain ⟨hsa', hss'⟩ := (hR.axis_sign (k := tl1.length) (by simp)).2 hodd
      rw [legOf_cons_length] at hsa' hss'
      have hsr : startRec st 2 = some s := by simp [startRec_eq, startOf, hl1]
      rw [hl] at hsa
      simp only [segAct', kindOf, fdirOf, Matrix.cons_val, hsr, Option.some.injEq] at hsa
      subst hsa
      refine ⟨s, by simp [hl1], oth (qAt (plIdx hd τ.ax) (tl1.length / 2 + 1)), ?_⟩
      exact start_diag hL hH τ (by rw [oth_oth]; exact hsa') (by rw [oth_oth]; exact hss') (hgood s (mem_all_of_mem (k := 1) (by rw [hl1]; simp))) o
    · have hK' : SegOK hd Y e τ ej 2 (st.segs 2) (st.segs (startOf 2)) := hI.segOK 2
      simp only [startOf, Matrix.cons_val] at hK'
      obtain ⟨s, hsm, q, hD, hD0⟩ := hK' (by rw [hl]; simp)
      rw [hl] at hsa hD hD0
      simp only [segAct', kindOf, fdirOf, Matrix.cons_val, Option.some.injEq] at hsa
      subst hsa
      refine ⟨s, hsm, q, grow_diag hL hH τ hD (hgood r' (mem_all_of_mem (k := 2) (by rw [hl]; simp))) o, ?_⟩
      rw [legOf_cons_of_lt _ _ (by simp)]; exact hD0
  · -- segment 3: a turn, off the head of segment 2
    rw [put_segs_of_ne _ (by decide)]
    show (r :: st.segs 3) ≠ [] → ∃ s ∈ (st.segs 2).head?, Turn hd Y e (dsg e) (dsg ej) (pJ e ej) s.1 (r :: st.segs 3)
    intro _
    have hc := hbefore 2 (by decide)
    obtain ⟨s, tl2, hl2⟩ : ∃ s tl, st.segs 2 = s :: tl := List.exists_cons_of_ne_nil (by intro h; rw [h] at hc; simp [complete'] at hc)
    simp only [complete', kindOf, Matrix.cons_val, hl2] at hc
    have hK2 : SegOK hd Y e τ ej 2 (st.segs 2) (st.segs (startOf 2)) := hI.segOK 2
    simp only [startOf, Matrix.cons_val] at hK2
    obtain ⟨_, _, q, hD, _⟩ := hK2 (by rw [hl2]; simp)
    have hsa2 : s.1.a = pl hd (pJ e ej) := hc.2
    obtain ⟨ha2, hs2⟩ := hD.axis_sign (k := tl2.length) (by rw [hl2]; simp)
    rw [hl2, legOf_cons_length] at ha2 hs2
    have hq : _ = pJ e ej := pl_injective hd (ha2.symm.trans hsa2)
    rw [hq] at hs2
    have hsr : startRec st 3 = some s := by simp [startRec_eq, startOf, hl2]
    have hgs : GoodRec Y.m Y.L Y.H s := hgood s (mem_all_of_mem (k := 2) (by rw [hl2]; simp))
    have hkeep : (dsg ej) (pJ e ej) = (dsg e) (pJ e ej) := (dsg_lat e _).1
    have hK' : SegOK hd Y e τ ej 3 (st.segs 3) (st.segs (startOf 3)) := hI.segOK 3
    simp only [startOf, Matrix.cons_val] at hK'
    refine ⟨s, by simp [hl2], ?_⟩
    rcases hl : st.segs 3 with _ | ⟨r', _ | ⟨r'', tl'⟩⟩
    · -- the top stacking
      rw [hl] at hsa
      simp only [segAct', kindOf, fdirOf, Matrix.cons_val, hsr, Option.some.injEq] at hsa
      subst hsa
      exact turn_cons_top (turn_nil hd Y e hsa2 hs2 hkeep) (tHop_tStep hd Y hL hH e hgs _ hsa2)
    · -- the hop through the new side face
      obtain ⟨s', hs', hT⟩ := hK' (by rw [hl]; simp)
      rw [hl2] at hs'; simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hs'
      subst hs'
      rw [hl] at hT hsa
      have hg' : GoodRec Y.m Y.L Y.H r' := hgood r' (mem_all_of_mem (k := 3) (by rw [hl]; simp))
      obtain ⟨hax, hsx⟩ := hT.axis_sign.1 (by simp)
      have e0 : legOf [r'] 0 = r'.1 := by have := legOf_cons_length r' ([] : List (BrickRec d)); rwa [List.length_nil] at this
      rw [e0] at hax hsx
      simp only [segAct', kindOf, fdirOf, Matrix.cons_val, Option.some.injEq] at hsa
      subst hsa
      refine turn_cons_hop hT ?_
      exact dHop_sStep hd Y hL hH e hg' _ none (by rw [oth_oth]; exact hax) (by rw [oth_oth, hkeep]; exact hsx)
    · -- a complete turn is not current
      exfalso; apply hinc; rw [hl]; simp only [complete', kindOf, Matrix.cons_val, List.length_cons]; omega
  · -- segment 4: a leg, off the head `γ` of the turn 3
    rw [put_segs_of_ne _ (by decide)]
    show (r :: st.segs 4) ≠ [] → ∃ s ∈ (st.segs 3).head?, DiagLeg hd Y e (dsg ej) none (pJ e ej) (r :: st.segs 4) ∧
      DHop hd Y e (dsg ej) none (pJ e ej) s.1 (legOf (r :: st.segs 4) 0)
    intro _
    rcases hl : st.segs 4 with _ | ⟨r', tl⟩
    · have hc := hbefore 3 (by decide)
      obtain ⟨γ, tl3, hl3⟩ : ∃ s tl, st.segs 3 = s :: tl := List.exists_cons_of_ne_nil (by intro h; rw [h] at hc; simp [complete'] at hc)
      simp only [complete', kindOf, Matrix.cons_val, hl3, List.length_cons] at hc
      have hK3 : SegOK hd Y e τ ej 3 (st.segs 3) (st.segs (startOf 3)) := hI.segOK 3
      simp only [startOf, Matrix.cons_val] at hK3
      obtain ⟨_, _, hT⟩ := hK3 (by rw [hl3]; simp)
      rw [hl3] at hT
      have hlen3 := hT.len
      simp only [List.length_cons] at hlen3
      have h1 : tl3.length = 1 := by omega
      obtain ⟨hγa, hγs⟩ := hT.axis_sign.2 (by simp; omega)
      rw [legOf_head' h1] at hγa hγs
      have hsr : startRec st 4 = some γ := by simp [startRec_eq, startOf, hl3]
      rw [hl] at hsa
      simp only [segAct', kindOf, fdirOf, Matrix.cons_val, hsr, Option.some.injEq] at hsa
      subst hsa
      refine ⟨γ, by simp [hl3], ?_⟩
      exact start_diag hL hH τ hγa hγs (hgood γ (mem_all_of_mem (k := 3) (by rw [hl3]; simp))) o
    · have hK' : SegOK hd Y e τ ej 4 (st.segs 4) (st.segs (startOf 4)) := hI.segOK 4
      simp only [startOf, Matrix.cons_val] at hK'
      obtain ⟨s, hsm, hD, hD0⟩ := hK' (by rw [hl]; simp)
      rw [hl] at hsa hD hD0
      simp only [segAct', kindOf, fdirOf, Matrix.cons_val, Option.some.injEq] at hsa
      subst hsa
      refine ⟨s, hsm, grow_diag hL hH τ hD (hgood r' (mem_all_of_mem (k := 4) (by rw [hl]; simp))) o, ?_⟩
      rw [legOf_cons_of_lt _ _ (by simp)]; exact hD0
  · -- segment 5: a turn, off the head of segment 4
    rw [put_segs_of_ne _ (by decide)]
    show (r :: st.segs 5) ≠ [] → ∃ s ∈ (st.segs 4).head?, Turn hd Y e (dsg ej) (dsg e) (pJ e ej) s.1 (r :: st.segs 5)
    intro _
    have hc := hbefore 4 (by decide)
    obtain ⟨s, tl2, hl2⟩ : ∃ s tl, st.segs 4 = s :: tl := List.exists_cons_of_ne_nil (by intro h; rw [h] at hc; simp [complete'] at hc)
    simp only [complete', kindOf, Matrix.cons_val, hl2] at hc
    have hK2 : SegOK hd Y e τ ej 4 (st.segs 4) (st.segs (startOf 4)) := hI.segOK 4
    simp only [startOf, Matrix.cons_val] at hK2
    obtain ⟨_, _, hD, _⟩ := hK2 (by rw [hl2]; simp)
    have hsa2 : s.1.a = pl hd (pJ e ej) := hc.2.2 _ (by simp [legAxisOf, pJ])
    obtain ⟨ha2, hs2⟩ := hD.axis_sign (k := tl2.length) (by rw [hl2]; simp)
    rw [hl2, legOf_cons_length] at ha2 hs2
    have hq : _ = pJ e ej := pl_injective hd (ha2.symm.trans hsa2)
    rw [hq] at hs2
    have hsr : startRec st 5 = some s := by simp [startRec_eq, startOf, hl2]
    have hgs : GoodRec Y.m Y.L Y.H s := hgood s (mem_all_of_mem (k := 4) (by rw [hl2]; simp))
    have hkeep : (dsg e) (pJ e ej) = (dsg ej) (pJ e ej) := (dsg_lat e _).1.symm
    have hK' : SegOK hd Y e τ ej 5 (st.segs 5) (st.segs (startOf 5)) := hI.segOK 5
    simp only [startOf, Matrix.cons_val] at hK'
    refine ⟨s, by simp [hl2], ?_⟩
    rcases hl : st.segs 5 with _ | ⟨r', _ | ⟨r'', tl'⟩⟩
    · -- the top stacking
      rw [hl] at hsa
      simp only [segAct', kindOf, fdirOf, Matrix.cons_val, hsr, Option.some.injEq] at hsa
      subst hsa
      exact turn_cons_top (turn_nil hd Y e hsa2 hs2 hkeep) (tHop_tStep hd Y hL hH e hgs _ hsa2)
    · -- the hop through the new side face
      obtain ⟨s', hs', hT⟩ := hK' (by rw [hl]; simp)
      rw [hl2] at hs'; simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hs'
      subst hs'
      rw [hl] at hT hsa
      have hg' : GoodRec Y.m Y.L Y.H r' := hgood r' (mem_all_of_mem (k := 5) (by rw [hl]; simp))
      obtain ⟨hax, hsx⟩ := hT.axis_sign.1 (by simp)
      have e0 : legOf [r'] 0 = r'.1 := by have := legOf_cons_length r' ([] : List (BrickRec d)); rwa [List.length_nil] at this
      rw [e0] at hax hsx
      simp only [segAct', kindOf, fdirOf, Matrix.cons_val, Option.some.injEq] at hsa
      subst hsa
      refine turn_cons_hop hT ?_
      exact dHop_sStep hd Y hL hH e hg' _ none (by rw [oth_oth]; exact hax) (by rw [oth_oth, hkeep]; exact hsx)
    · -- a complete turn is not current
      exfalso; apply hinc; rw [hl]; simp only [complete', kindOf, Matrix.cons_val, List.length_cons]; omega
  · -- segment 6: a leg, off the head `γ` of the turn 5
    rw [put_segs_of_ne _ (by decide)]
    show (r :: st.segs 6) ≠ [] → ∃ s ∈ (st.segs 5).head?, DiagLeg hd Y e (dsg e) none (pJ e ej) (r :: st.segs 6) ∧
      DHop hd Y e (dsg e) none (pJ e ej) s.1 (legOf (r :: st.segs 6) 0)
    intro _
    rcases hl : st.segs 6 with _ | ⟨r', tl⟩
    · have hc := hbefore 5 (by decide)
      obtain ⟨γ, tl3, hl3⟩ : ∃ s tl, st.segs 5 = s :: tl := List.exists_cons_of_ne_nil (by intro h; rw [h] at hc; simp [complete'] at hc)
      simp only [complete', kindOf, Matrix.cons_val, hl3, List.length_cons] at hc
      have hK3 : SegOK hd Y e τ ej 5 (st.segs 5) (st.segs (startOf 5)) := hI.segOK 5
      simp only [startOf, Matrix.cons_val] at hK3
      obtain ⟨_, _, hT⟩ := hK3 (by rw [hl3]; simp)
      rw [hl3] at hT
      have hlen3 := hT.len
      simp only [List.length_cons] at hlen3
      have h1 : tl3.length = 1 := by omega
      obtain ⟨hγa, hγs⟩ := hT.axis_sign.2 (by simp; omega)
      rw [legOf_head' h1] at hγa hγs
      have hsr : startRec st 6 = some γ := by simp [startRec_eq, startOf, hl3]
      rw [hl] at hsa
      simp only [segAct', kindOf, fdirOf, Matrix.cons_val, hsr, Option.some.injEq] at hsa
      subst hsa
      refine ⟨γ, by simp [hl3], ?_⟩
      exact start_diag hL hH τ hγa hγs (hgood γ (mem_all_of_mem (k := 5) (by rw [hl3]; simp))) o
    · have hK' : SegOK hd Y e τ ej 6 (st.segs 6) (st.segs (startOf 6)) := hI.segOK 6
      simp only [startOf, Matrix.cons_val] at hK'
      obtain ⟨s, hsm, hD, hD0⟩ := hK' (by rw [hl]; simp)
      rw [hl] at hsa hD hD0
      simp only [segAct', kindOf, fdirOf, Matrix.cons_val, Option.some.injEq] at hsa
      subst hsa
      refine ⟨s, hsm, grow_diag hL hH τ hD (hgood r' (mem_all_of_mem (k := 6) (by rw [hl]; simp))) o, ?_⟩
      rw [legOf_cons_of_lt _ _ (by simp)]; exact hD0
  · -- segment 7: a turn, off the head of segment 6
    rw [put_segs_of_ne _ (by decide)]
    show (r :: st.segs 7) ≠ [] → ∃ s ∈ (st.segs 6).head?, Turn hd Y e (dsg e) (dsg (eB1 e)) (p1 e) s.1 (r :: st.segs 7)
    intro _
    have hc := hbefore 6 (by decide)
    obtain ⟨s, tl2, hl2⟩ : ∃ s tl, st.segs 6 = s :: tl := List.exists_cons_of_ne_nil (by intro h; rw [h] at hc; simp [complete'] at hc)
    simp only [complete', kindOf, Matrix.cons_val, hl2] at hc
    have hK2 : SegOK hd Y e τ ej 6 (st.segs 6) (st.segs (startOf 6)) := hI.segOK 6
    simp only [startOf, Matrix.cons_val] at hK2
    obtain ⟨_, _, hD, _⟩ := hK2 (by rw [hl2]; simp)
    have hsa2 : s.1.a = pl hd (p1 e) := hc.2.2 _ (by simp [legAxisOf, p1])
    obtain ⟨ha2, hs2⟩ := hD.axis_sign (k := tl2.length) (by rw [hl2]; simp)
    rw [hl2, legOf_cons_length] at ha2 hs2
    have hq : _ = p1 e := pl_injective hd (ha2.symm.trans hsa2)
    rw [hq] at hs2
    have hsr : startRec st 7 = some s := by simp [startRec_eq, startOf, hl2]
    have hgs : GoodRec Y.m Y.L Y.H s := hgood s (mem_all_of_mem (k := 6) (by rw [hl2]; simp))
    have hkeep : (dsg (eB1 e)) (p1 e) = (dsg e) (p1 e) := (dsg_lat e _).1
    have hK' : SegOK hd Y e τ ej 7 (st.segs 7) (st.segs (startOf 7)) := hI.segOK 7
    simp only [startOf, Matrix.cons_val] at hK'
    refine ⟨s, by simp [hl2], ?_⟩
    rcases hl : st.segs 7 with _ | ⟨r', _ | ⟨r'', tl'⟩⟩
    · -- the top stacking
      rw [hl] at hsa
      simp only [segAct', kindOf, fdirOf, Matrix.cons_val, hsr, Option.some.injEq] at hsa
      subst hsa
      exact turn_cons_top (turn_nil hd Y e hsa2 hs2 hkeep) (tHop_tStep hd Y hL hH e hgs _ hsa2)
    · -- the hop through the new side face
      obtain ⟨s', hs', hT⟩ := hK' (by rw [hl]; simp)
      rw [hl2] at hs'; simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hs'
      subst hs'
      rw [hl] at hT hsa
      have hg' : GoodRec Y.m Y.L Y.H r' := hgood r' (mem_all_of_mem (k := 7) (by rw [hl]; simp))
      obtain ⟨hax, hsx⟩ := hT.axis_sign.1 (by simp)
      have e0 : legOf [r'] 0 = r'.1 := by have := legOf_cons_length r' ([] : List (BrickRec d)); rwa [List.length_nil] at this
      rw [e0] at hax hsx
      simp only [segAct', kindOf, fdirOf, Matrix.cons_val, Option.some.injEq] at hsa
      subst hsa
      refine turn_cons_hop hT ?_
      exact dHop_sStep hd Y hL hH e hg' _ none (by rw [oth_oth]; exact hax) (by rw [oth_oth, hkeep]; exact hsx)
    · -- a complete turn is not current
      exfalso; apply hinc; rw [hl]; simp only [complete', kindOf, Matrix.cons_val, List.length_cons]; omega
  · -- segment 8: the trunk continuing off the head of segment 6
    rw [put_segs_of_ne _ (by decide)]
    show (r :: st.segs 8) ≠ [] → ∃ s ∈ (st.segs 6).head?, ∃ q, DiagLeg hd Y e (dsg e) none q (r :: st.segs 8) ∧
      DHop hd Y e (dsg e) none q s.1 (legOf (r :: st.segs 8) 0)
    intro _
    rcases hl : st.segs 8 with _ | ⟨r', tl⟩
    · have hc := hbefore 6 (by decide)
      obtain ⟨s, tlp, hlp⟩ : ∃ s tl, st.segs 6 = s :: tl := List.exists_cons_of_ne_nil (by intro h; rw [h] at hc; simp [complete'] at hc)
      have hKp : SegOK hd Y e τ ej 6 (st.segs 6) (st.segs (startOf 6)) := hI.segOK 6
      simp only [startOf, Matrix.cons_val] at hKp
      obtain ⟨_, _, hD, _⟩ := hKp (by rw [hlp]; simp)
      obtain ⟨hsa', hss'⟩ := hD.axis_sign (k := tlp.length) (by rw [hlp]; simp)
      rw [hlp, legOf_cons_length] at hsa' hss'
      have hsr : startRec st 8 = some s := by simp [startRec_eq, startOf, hlp]
      rw [hl] at hsa
      simp only [segAct', kindOf, fdirOf, Matrix.cons_val, hsr, Option.some.injEq] at hsa
      subst hsa
      refine ⟨s, by simp [hlp], oth (qAt (pJ e ej) tlp.length), ?_⟩
      exact start_diag hL hH τ (by rw [oth_oth]; exact hsa') (by rw [oth_oth]; exact hss') (hgood s (mem_all_of_mem (k := 6) (by rw [hlp]; simp))) o
    · have hK' : SegOK hd Y e τ ej 8 (st.segs 8) (st.segs (startOf 8)) := hI.segOK 8
      simp only [startOf, Matrix.cons_val] at hK'
      obtain ⟨s, hsm, q, hD, hD0⟩ := hK' (by rw [hl]; simp)
      rw [hl] at hsa hD hD0
      simp only [segAct', kindOf, fdirOf, Matrix.cons_val, Option.some.injEq] at hsa
      subst hsa
      refine ⟨s, hsm, q, grow_diag hL hH τ hD (hgood r' (mem_all_of_mem (k := 8) (by rw [hl]; simp))) o, ?_⟩
      rw [legOf_cons_of_lt _ _ (by simp)]; exact hD0
  · -- segment 9: a turn, off the head of segment 8
    rw [put_segs_of_ne _ (by decide)]
    show (r :: st.segs 9) ≠ [] → ∃ s ∈ (st.segs 8).head?, Turn hd Y e (dsg e) (dsg (eB2 e)) (p2 e) s.1 (r :: st.segs 9)
    intro _
    have hc := hbefore 8 (by decide)
    obtain ⟨s, tl2, hl2⟩ : ∃ s tl, st.segs 8 = s :: tl := List.exists_cons_of_ne_nil (by intro h; rw [h] at hc; simp [complete'] at hc)
    simp only [complete', kindOf, Matrix.cons_val, hl2] at hc
    have hK2 : SegOK hd Y e τ ej 8 (st.segs 8) (st.segs (startOf 8)) := hI.segOK 8
    simp only [startOf, Matrix.cons_val] at hK2
    obtain ⟨_, _, q, hD, _⟩ := hK2 (by rw [hl2]; simp)
    have hsa2 : s.1.a = pl hd (p2 e) := hc.2.2 _ (by simp [legAxisOf, p2])
    obtain ⟨ha2, hs2⟩ := hD.axis_sign (k := tl2.length) (by rw [hl2]; simp)
    rw [hl2, legOf_cons_length] at ha2 hs2
    have hq : _ = p2 e := pl_injective hd (ha2.symm.trans hsa2)
    rw [hq] at hs2
    have hsr : startRec st 9 = some s := by simp [startRec_eq, startOf, hl2]
    have hgs : GoodRec Y.m Y.L Y.H s := hgood s (mem_all_of_mem (k := 8) (by rw [hl2]; simp))
    have hkeep : (dsg (eB2 e)) (p2 e) = (dsg e) (p2 e) := (dsg_lat e _).1
    have hK' : SegOK hd Y e τ ej 9 (st.segs 9) (st.segs (startOf 9)) := hI.segOK 9
    simp only [startOf, Matrix.cons_val] at hK'
    refine ⟨s, by simp [hl2], ?_⟩
    rcases hl : st.segs 9 with _ | ⟨r', _ | ⟨r'', tl'⟩⟩
    · -- the top stacking
      rw [hl] at hsa
      simp only [segAct', kindOf, fdirOf, Matrix.cons_val, hsr, Option.some.injEq] at hsa
      subst hsa
      exact turn_cons_top (turn_nil hd Y e hsa2 hs2 hkeep) (tHop_tStep hd Y hL hH e hgs _ hsa2)
    · -- the hop through the new side face
      obtain ⟨s', hs', hT⟩ := hK' (by rw [hl]; simp)
      rw [hl2] at hs'; simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hs'
      subst hs'
      rw [hl] at hT hsa
      have hg' : GoodRec Y.m Y.L Y.H r' := hgood r' (mem_all_of_mem (k := 9) (by rw [hl]; simp))
      obtain ⟨hax, hsx⟩ := hT.axis_sign.1 (by simp)
      have e0 : legOf [r'] 0 = r'.1 := by have := legOf_cons_length r' ([] : List (BrickRec d)); rwa [List.length_nil] at this
      rw [e0] at hax hsx
      simp only [segAct', kindOf, fdirOf, Matrix.cons_val, Option.some.injEq] at hsa
      subst hsa
      refine turn_cons_hop hT ?_
      exact dHop_sStep hd Y hL hH e hg' _ none (by rw [oth_oth]; exact hax) (by rw [oth_oth, hkeep]; exact hsx)
    · -- a complete turn is not current
      exfalso; apply hinc; rw [hl]; simp only [complete', kindOf, Matrix.cons_val, List.length_cons]; omega
  · -- segment 10: the trunk continuing off the head of segment 8
    rw [put_segs_of_ne _ (by decide)]
    show (r :: st.segs 10) ≠ [] → ∃ s ∈ (st.segs 8).head?, ∃ q, DiagLeg hd Y e (dsg e) none q (r :: st.segs 10) ∧
      DHop hd Y e (dsg e) none q s.1 (legOf (r :: st.segs 10) 0)
    intro _
    rcases hl : st.segs 10 with _ | ⟨r', tl⟩
    · have hc := hbefore 8 (by decide)
      obtain ⟨s, tlp, hlp⟩ : ∃ s tl, st.segs 8 = s :: tl := List.exists_cons_of_ne_nil (by intro h; rw [h] at hc; simp [complete'] at hc)
      have hKp : SegOK hd Y e τ ej 8 (st.segs 8) (st.segs (startOf 8)) := hI.segOK 8
      simp only [startOf, Matrix.cons_val] at hKp
      obtain ⟨_, _, q₀, hD, _⟩ := hKp (by rw [hlp]; simp)
      obtain ⟨hsa', hss'⟩ := hD.axis_sign (k := tlp.length) (by rw [hlp]; simp)
      rw [hlp, legOf_cons_length] at hsa' hss'
      have hsr : startRec st 10 = some s := by simp [startRec_eq, startOf, hlp]
      rw [hl] at hsa
      simp only [segAct', kindOf, fdirOf, Matrix.cons_val, hsr, Option.some.injEq] at hsa
      subst hsa
      refine ⟨s, by simp [hlp], oth (qAt q₀ tlp.length), ?_⟩
      exact start_diag hL hH τ (by rw [oth_oth]; exact hsa') (by rw [oth_oth]; exact hss') (hgood s (mem_all_of_mem (k := 8) (by rw [hlp]; simp))) o
    · have hK' : SegOK hd Y e τ ej 10 (st.segs 10) (st.segs (startOf 10)) := hI.segOK 10
      simp only [startOf, Matrix.cons_val] at hK'
      obtain ⟨s, hsm, q, hD, hD0⟩ := hK' (by rw [hl]; simp)
      rw [hl] at hsa hD hD0
      simp only [segAct', kindOf, fdirOf, Matrix.cons_val, Option.some.injEq] at hsa
      subst hsa
      refine ⟨s, hsm, q, grow_diag hL hH τ hD (hgood r' (mem_all_of_mem (k := 10) (by rw [hl]; simp))) o, ?_⟩
      rw [legOf_cons_of_lt _ _ (by simp)]; exact hD0
  · -- segment 11: a leg, off the head `γ` of the turn 7
    rw [put_segs_of_ne _ (by decide)]
    show (r :: st.segs 11) ≠ [] → ∃ s ∈ (st.segs 7).head?, DiagLeg hd Y e (dsg (eB1 e)) none (p1 e) (r :: st.segs 11) ∧
      DHop hd Y e (dsg (eB1 e)) none (p1 e) s.1 (legOf (r :: st.segs 11) 0)
    intro _
    rcases hl : st.segs 11 with _ | ⟨r', tl⟩
    · have hc := hbefore 7 (by decide)
      obtain ⟨γ, tl3, hl3⟩ : ∃ s tl, st.segs 7 = s :: tl := List.exists_cons_of_ne_nil (by intro h; rw [h] at hc; simp [complete'] at hc)
      simp only [complete', kindOf, Matrix.cons_val, hl3, List.length_cons] at hc
      have hK3 : SegOK hd Y e τ ej 7 (st.segs 7) (st.segs (startOf 7)) := hI.segOK 7
      simp only [startOf, Matrix.cons_val] at hK3
      obtain ⟨_, _, hT⟩ := hK3 (by rw [hl3]; simp)
      rw [hl3] at hT
      have hlen3 := hT.len
      simp only [List.length_cons] at hlen3
      have h1 : tl3.length = 1 := by omega
      obtain ⟨hγa, hγs⟩ := hT.axis_sign.2 (by simp; omega)
      rw [legOf_head' h1] at hγa hγs
      have hsr : startRec st 11 = some γ := by simp [startRec_eq, startOf, hl3]
      rw [hl] at hsa
      simp only [segAct', kindOf, fdirOf, Matrix.cons_val, hsr, Option.some.injEq] at hsa
      subst hsa
      refine ⟨γ, by simp [hl3], ?_⟩
      exact start_diag hL hH τ hγa hγs (hgood γ (mem_all_of_mem (k := 7) (by rw [hl3]; simp))) o
    · have hK' : SegOK hd Y e τ ej 11 (st.segs 11) (st.segs (startOf 11)) := hI.segOK 11
      simp only [startOf, Matrix.cons_val] at hK'
      obtain ⟨s, hsm, hD, hD0⟩ := hK' (by rw [hl]; simp)
      rw [hl] at hsa hD hD0
      simp only [segAct', kindOf, fdirOf, Matrix.cons_val, Option.some.injEq] at hsa
      subst hsa
      refine ⟨s, hsm, grow_diag hL hH τ hD (hgood r' (mem_all_of_mem (k := 11) (by rw [hl]; simp))) o, ?_⟩
      rw [legOf_cons_of_lt _ _ (by simp)]; exact hD0
  · -- segment 12: a leg, off the head `γ` of the turn 9
    rw [put_segs_of_ne _ (by decide)]
    show (r :: st.segs 12) ≠ [] → ∃ s ∈ (st.segs 9).head?, DiagLeg hd Y e (dsg (eB2 e)) none (p2 e) (r :: st.segs 12) ∧
      DHop hd Y e (dsg (eB2 e)) none (p2 e) s.1 (legOf (r :: st.segs 12) 0)
    intro _
    rcases hl : st.segs 12 with _ | ⟨r', tl⟩
    · have hc := hbefore 9 (by decide)
      obtain ⟨γ, tl3, hl3⟩ : ∃ s tl, st.segs 9 = s :: tl := List.exists_cons_of_ne_nil (by intro h; rw [h] at hc; simp [complete'] at hc)
      simp only [complete', kindOf, Matrix.cons_val, hl3, List.length_cons] at hc
      have hK3 : SegOK hd Y e τ ej 9 (st.segs 9) (st.segs (startOf 9)) := hI.segOK 9
      simp only [startOf, Matrix.cons_val] at hK3
      obtain ⟨_, _, hT⟩ := hK3 (by rw [hl3]; simp)
      rw [hl3] at hT
      have hlen3 := hT.len
      simp only [List.length_cons] at hlen3
      have h1 : tl3.length = 1 := by omega
      obtain ⟨hγa, hγs⟩ := hT.axis_sign.2 (by simp; omega)
      rw [legOf_head' h1] at hγa hγs
      have hsr : startRec st 12 = some γ := by simp [startRec_eq, startOf, hl3]
      rw [hl] at hsa
      simp only [segAct', kindOf, fdirOf, Matrix.cons_val, hsr, Option.some.injEq] at hsa
      subst hsa
      refine ⟨γ, by simp [hl3], ?_⟩
      exact start_diag hL hH τ hγa hγs (hgood γ (mem_all_of_mem (k := 9) (by rw [hl3]; simp))) o
    · have hK' : SegOK hd Y e τ ej 12 (st.segs 12) (st.segs (startOf 12)) := hI.segOK 12
      simp only [startOf, Matrix.cons_val] at hK'
      obtain ⟨s, hsm, hD, hD0⟩ := hK' (by rw [hl]; simp)
      rw [hl] at hsa hD hD0
      simp only [segAct', kindOf, fdirOf, Matrix.cons_val, Option.some.injEq] at hsa
      subst hsa
      refine ⟨s, hsm, grow_diag hL hH τ hD (hgood r' (mem_all_of_mem (k := 12) (by rw [hl]; simp))) o, ?_⟩
      rw [legOf_cons_of_lt _ _ (by simp)]; exact hD0

end BGNd

end Percolation.Literature

end
