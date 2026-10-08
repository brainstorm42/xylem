import Percolation.Literature.FlatGeom
import Percolation.Util.Linter

/-!
# The flat gait, IX: extended legs and the frame of an invariant state

From the invariant `FlatInv` of the flat gait
(`FlatInv.lean`; Grimmett, *Percolation*, 2nd ed. (1999), §7.3, case `H < L`) we extract the
**extended legs** — a leg together with the plate it starts from is again a diagonal leg
(`diagLeg_snoc`), and the three stretches of the trunk glue into one (`diagLeg_append`) — and the
**frame** of a state: the riser, the preamble extended by the riser's head, the jog extended by
the turn plate `γ_J`, the trunk extended by `T₀`, the branches extended by `γ₁`, `γ₂`, and the
four turns with the axes of their start plates (`FlatInv.frame_*`).

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §7.3 pp. 171–174.
-/

noncomputable section

namespace Percolation.Literature

open LatticeModels Contour
open scoped Classical

namespace BGNd

variable {d : ℕ} [NeZero d]

/-! ## `legOf` of appended lists -/

/-- The oldest record of a list extended by an older one is the added one. [folklore] -/
theorem legOf_snoc_zero (l : List (BrickRec d)) (s : BrickRec d) : legOf (l ++ [s]) 0 = s.1 := by
  unfold legOf recOf; simp

/-- The later records of a list extended by an older one are those of the list. [folklore] -/
theorem legOf_append_singleton_succ (l : List (BrickRec d)) (s : BrickRec d) (k : ℕ) : legOf (l ++ [s]) (k + 1) = legOf l k := by
  unfold legOf recOf; simp

/-- The records of an appended list, oldest first: first those of the older part. [folklore] -/
theorem legOf_append_of_lt (l₂ l₁ : List (BrickRec d)) {k : ℕ} (hk : k < l₁.length) : legOf (l₂ ++ l₁) k = legOf l₁ k := by
  unfold legOf recOf
  rw [List.reverse_append, List.getElem?_append_left (by simpa using hk)]

/-- The records of an appended list, oldest first: then those of the newer part. [folklore] -/
theorem legOf_append_of_ge (l₂ l₁ : List (BrickRec d)) (k : ℕ) : legOf (l₂ ++ l₁) (l₁.length + k) = legOf l₂ k := by
  unfold legOf recOf
  rw [List.reverse_append, List.getElem?_append_right (by simp)]
  simp

/-! ## Extending diagonal legs -/

section Extend

variable {hd : 3 ≤ d} {Y : FlatLayout} {e : MDir} {σ : Fin 2 → ℤˣ} {zmode : Option Bool}

omit [NeZero d] in
/-- The alternating index from the other start. [folklore] -/
theorem qAt_oth (q : Fin 2) (k : ℕ) : qAt (oth q) k = oth (qAt q k) := by
  unfold qAt; split_ifs <;> simp

omit [NeZero d] in
/-- The alternating index is additive. [folklore] -/
theorem qAt_add (q : Fin 2) (n j : ℕ) : qAt q (n + j) = qAt (qAt q n) j := by
  have key : ∀ q' : Fin 2, qAt q' j = if j % 2 = 0 then q' else oth q' := fun q' => rfl
  rw [key]
  unfold qAt
  rcases Nat.mod_two_eq_zero_or_one n with hn | hn <;> rcases Nat.mod_two_eq_zero_or_one j with hj | hj
  · rw [if_pos (show (n + j) % 2 = 0 by omega), if_pos hn, if_pos hj]
  · rw [if_neg (show ¬((n + j) % 2 = 0) by omega), if_pos hn, if_neg (show ¬(j % 2 = 0) by omega)]
  · rw [if_neg (show ¬((n + j) % 2 = 0) by omega), if_neg (show ¬(n % 2 = 0) by omega), if_pos hj]
  · rw [if_pos (show (n + j) % 2 = 0 by omega), if_neg (show ¬(n % 2 = 0) by omega), if_neg (show ¬(j % 2 = 0) by omega), oth_oth]

/-- **A leg together with the plate it starts from is a leg** (one hop longer, starting from the
other index). [folklore] -/
theorem diagLeg_snoc {q : Fin 2} {l : List (BrickRec d)} (h : DiagLeg hd Y e σ zmode q l) {s : BrickRec d}
    (hs : DHop hd Y e σ zmode q s.1 (legOf l 0)) : DiagLeg hd Y e σ zmode (oth q) (l ++ [s]) := by
  refine ⟨by simp, by rw [legOf_snoc_zero]; exact hs.srcAxis, by rw [legOf_snoc_zero]; exact hs.srcSign, fun k hk => ?_⟩
  rw [List.length_append, List.length_singleton] at hk
  rcases k with _ | k
  · rw [legOf_snoc_zero, show (0 : ℕ) + 1 = 1 from rfl, legOf_append_singleton_succ, qAt_oth, qAt_succ, qAt_zero, oth_oth]
    exact hs
  · rw [legOf_append_singleton_succ, show k + 1 + 1 = (k + 1) + 1 from rfl, legOf_append_singleton_succ, qAt_oth,
      show qAt q (k + 1 + 1) = oth (qAt q (k + 1)) from qAt_succ q (k + 1), oth_oth]
    exact h.chain k (by omega)

/-- **Two consecutive stretches of a leg are one leg.** [folklore] -/
theorem diagLeg_append {q₁ q₂ : Fin 2} {l₁ l₂ : List (BrickRec d)} (h₂ : DiagLeg hd Y e σ zmode q₂ l₂) (h₁ : DiagLeg hd Y e σ zmode q₁ l₁)
    (hs : DHop hd Y e σ zmode q₂ (legOf l₁ (l₁.length - 1)) (legOf l₂ 0)) : DiagLeg hd Y e σ zmode q₁ (l₂ ++ l₁) := by
  have hlen : 0 < l₁.length := List.length_pos_of_ne_nil h₁.ne
  -- the index of the first new plate is the alternating index at `l₁.length`
  have hq : q₂ = qAt q₁ l₁.length := by
    have h1 := hs.srcAxis
    have h2 := (h₁.axis_sign (k := l₁.length - 1) (by omega)).1
    rw [h2] at h1
    have := pl_injective hd h1
    rw [show l₁.length = (l₁.length - 1) + 1 by omega, qAt_succ, this, oth_oth]
  refine ⟨by simp [h₁.ne], by rw [legOf_append_of_lt _ _ hlen]; exact h₁.axis0, by rw [legOf_append_of_lt _ _ hlen]; exact h₁.sign0, fun k hk => ?_⟩
  rw [List.length_append] at hk
  by_cases hk1 : k + 1 < l₁.length
  · rw [legOf_append_of_lt _ _ (by omega), legOf_append_of_lt _ _ hk1]; exact h₁.chain k hk1
  · by_cases hk2 : k + 1 = l₁.length
    · have e1 : legOf (l₂ ++ l₁) (k + 1) = legOf l₂ 0 := by rw [show k + 1 = l₁.length + 0 by omega, legOf_append_of_ge]
      rw [legOf_append_of_lt _ _ (by omega), e1, hk2, ← hq, show k = l₁.length - 1 by omega]
      exact hs
    · obtain ⟨j, rfl⟩ : ∃ j, k = l₁.length + j := ⟨k - l₁.length, by omega⟩
      rw [legOf_append_of_ge, show l₁.length + j + 1 = l₁.length + (j + 1) by ring, legOf_append_of_ge, qAt_add, ← hq]
      exact h₂.chain j (by omega)

end Extend

/-! ## The frame of an invariant state -/

section Frame

variable (hd : 3 ≤ d) (Y : FlatLayout) (a : Site 2) (e : MDir) (τ : TTok d)
variable {hd Y a e τ}

omit [NeZero d] in
/-- The head of a nonempty segment and the decomposition. [folklore] -/
theorem exists_head_of_ne_nil {l : List (BrickRec d)} (h : l ≠ []) : ∃ r tl, l = r :: tl ∧ l.head? = some r := by
  obtain ⟨r, tl, rfl⟩ := List.exists_cons_of_ne_nil h; exact ⟨r, tl, rfl, rfl⟩

/-- The last record of a nonempty segment as `legOf`. [folklore] -/
theorem legOf_last_of_head {l : List (BrickRec d)} {r : BrickRec d} (h : l.head? = some r) : legOf l (l.length - 1) = r.1 := by
  obtain ⟨tl, hl⟩ : ∃ tl, l = r :: tl := by
    rcases hh : l with _ | ⟨r0, tl⟩
    · rw [hh] at h; simp at h
    · rw [hh] at h; simp only [List.head?_cons, Option.some.injEq] at h; subst h; exact ⟨tl, rfl⟩
  rw [hl]; exact legOf_cons_length r tl

/-- **Frame, preamble**: the preamble extended by the riser's head is a diagonal leg of the signs
of `e`. [folklore] -/
theorem FlatInv.frame_pre {st : FS d} (hI : FlatInv hd Y a e τ st) (h2 : st.segs 2 ≠ []) :
    ∃ s, (st.segs 1).head? = some s ∧ ∃ q, DiagLeg hd Y e (dsg e) none q (st.segs 2 ++ [s]) := by
  have hK : SegOK hd Y e τ (eJOf hd Y a e τ st) 2 (st.segs 2) (st.segs (startOf 2)) := hI.segOK 2
  simp only [startOf, Matrix.cons_val] at hK
  obtain ⟨s, hs, q, hD, hD0⟩ := hK h2
  exact ⟨s, hs, oth q, diagLeg_snoc hD hD0⟩

/-- **Frame, jog turn**: the turn towards the jog off the preamble's head, a plate of the kept axis. [folklore] -/
theorem FlatInv.frame_turnJ {st : FS d} (hI : FlatInv hd Y a e τ st) (h3 : st.segs 3 ≠ []) :
    ∃ s, (st.segs 2).head? = some s ∧ 2 ≤ (st.segs 2).length ∧
      Turn hd Y e (dsg e) (dsg (eJOf hd Y a e τ st)) (pJ e (eJOf hd Y a e τ st)) s.1 (st.segs 3) := by
  have hK : SegOK hd Y e τ (eJOf hd Y a e τ st) 3 (st.segs 3) (st.segs (startOf 3)) := hI.segOK 3
  simp only [startOf, Matrix.cons_val] at hK
  obtain ⟨s, hs, hT⟩ := hK h3
  have hc := hI.order 3 2 (by decide) h3
  obtain ⟨r, tl, hl, hh⟩ := exists_head_of_ne_nil (l := st.segs 2) (by intro h; rw [h] at hc; simp [complete'] at hc)
  rw [hh] at hs; simp only [Option.mem_def, Option.some.injEq] at hs; subst hs
  simp only [complete', kindOf, Matrix.cons_val, hl] at hc
  exact ⟨r, hh, by rw [hl]; have := hc.1; omega, hT⟩

/-- **Frame, jog**: the jog extended by the turn plate `γ_J` is a diagonal leg of the signs of the
jog direction, and the turn is complete. [folklore] -/
theorem FlatInv.frame_jog {st : FS d} (hI : FlatInv hd Y a e τ st) (h4 : st.segs 4 ≠ []) :
    ∃ γ, (st.segs 3).head? = some γ ∧ (st.segs 3).length = 2 ∧
      DiagLeg hd Y e (dsg (eJOf hd Y a e τ st)) none (oth (pJ e (eJOf hd Y a e τ st))) (st.segs 4 ++ [γ]) := by
  have hK : SegOK hd Y e τ (eJOf hd Y a e τ st) 4 (st.segs 4) (st.segs (startOf 4)) := hI.segOK 4
  simp only [startOf, Matrix.cons_val] at hK
  obtain ⟨s, hs, hD, hD0⟩ := hK h4
  have hc := hI.order 4 3 (by decide) h4
  obtain ⟨r, tl, hl, hh⟩ := exists_head_of_ne_nil (l := st.segs 3) (by intro h; rw [h] at hc; simp [complete'] at hc)
  rw [hh] at hs; simp only [Option.mem_def, Option.some.injEq] at hs; subst hs
  obtain ⟨_, _, _, hT⟩ := hI.frame_turnJ (by rw [hl]; simp)
  have hlen : (st.segs 3).length = 2 := by
    have := hT.len; simp only [complete', kindOf, Matrix.cons_val, hl] at hc; rw [hl] at this ⊢; simp at this hc ⊢; omega
  exact ⟨r, hh, hlen, diagLeg_snoc hD hD0⟩

/-- **Frame, trunk turn**: the turn back towards `e` off the jog's head, a plate of the kept axis. [folklore] -/
theorem FlatInv.frame_turnT {st : FS d} (hI : FlatInv hd Y a e τ st) (h5 : st.segs 5 ≠ []) :
    ∃ s, (st.segs 4).head? = some s ∧ s.1.a = pl hd (pJ e (eJOf hd Y a e τ st)) ∧
      Turn hd Y e (dsg (eJOf hd Y a e τ st)) (dsg e) (pJ e (eJOf hd Y a e τ st)) s.1 (st.segs 5) := by
  have hK : SegOK hd Y e τ (eJOf hd Y a e τ st) 5 (st.segs 5) (st.segs (startOf 5)) := hI.segOK 5
  simp only [startOf, Matrix.cons_val] at hK
  obtain ⟨s, hs, hT⟩ := hK h5
  exact ⟨s, hs, hT.sAxis, hT⟩

/-- **Frame, trunk**: the three stretches of the trunk, extended by the turn plate `T₀`, form one
diagonal leg of the signs of `e`; the turn is complete. [folklore] -/
theorem FlatInv.frame_trunk {st : FS d} (hI : FlatInv hd Y a e τ st) (h6 : st.segs 6 ≠ []) :
    ∃ T₀, (st.segs 5).head? = some T₀ ∧ (st.segs 5).length = 2 ∧
      DiagLeg hd Y e (dsg e) none (oth (pJ e (eJOf hd Y a e τ st))) (st.segs 10 ++ st.segs 8 ++ st.segs 6 ++ [T₀]) := by
  set ej := eJOf hd Y a e τ st
  have hK6 : SegOK hd Y e τ ej 6 (st.segs 6) (st.segs (startOf 6)) := hI.segOK 6
  simp only [startOf, Matrix.cons_val] at hK6
  obtain ⟨s, hs, hD6, hD60⟩ := hK6 h6
  have hc := hI.order 6 5 (by decide) h6
  obtain ⟨r, tl, hl, hh⟩ := exists_head_of_ne_nil (l := st.segs 5) (by intro h; rw [h] at hc; simp [complete'] at hc)
  rw [hh] at hs; simp only [Option.mem_def, Option.some.injEq] at hs; subst hs
  obtain ⟨_, _, _, hT⟩ := hI.frame_turnT (by rw [hl]; simp)
  have hlen : (st.segs 5).length = 2 := by
    have := hT.len; simp only [complete', kindOf, Matrix.cons_val, hl] at hc; rw [hl] at this ⊢; simp at this hc ⊢; omega
  refine ⟨r, hh, hlen, ?_⟩
  -- the first stretch, extended by `T₀`
  have hE6 : DiagLeg hd Y e (dsg e) none (oth (pJ e ej)) (st.segs 6 ++ [r]) := diagLeg_snoc hD6 hD60
  -- the second stretch
  have hE8 : DiagLeg hd Y e (dsg e) none (oth (pJ e ej)) (st.segs 8 ++ (st.segs 6 ++ [r])) := by
    by_cases h8 : st.segs 8 = []
    · rw [h8, List.nil_append]; exact hE6
    · have hK8 : SegOK hd Y e τ ej 8 (st.segs 8) (st.segs (startOf 8)) := hI.segOK 8
      simp only [startOf, Matrix.cons_val] at hK8
      obtain ⟨s8, hs8, q8, hD8, hD80⟩ := hK8 h8
      obtain ⟨r6, tl6, hl6, hh6⟩ := exists_head_of_ne_nil h6
      rw [hh6] at hs8; simp only [Option.mem_def, Option.some.injEq] at hs8; subst hs8
      refine diagLeg_append hD8 hE6 ?_
      have : legOf (st.segs 6 ++ [r]) ((st.segs 6 ++ [r]).length - 1) = r6.1 := by
        rw [hl6, List.cons_append, show (r6 :: (tl6 ++ [r])).length - 1 = (tl6 ++ [r]).length by simp]
        exact legOf_cons_length r6 (tl6 ++ [r])
      rw [this]; exact hD80
  -- the third stretch
  by_cases h10 : st.segs 10 = []
  · rw [h10, List.nil_append, List.append_assoc]; exact hE8
  · have hK10 : SegOK hd Y e τ ej 10 (st.segs 10) (st.segs (startOf 10)) := hI.segOK 10
    simp only [startOf, Matrix.cons_val] at hK10
    obtain ⟨s10, hs10, q10, hD10, hD100⟩ := hK10 h10
    have h8 : st.segs 8 ≠ [] := by
      have hc8 := hI.order 10 8 (by decide) h10
      intro h; rw [h] at hc8; simp [complete'] at hc8
    obtain ⟨r8, tl8, hl8, hh8⟩ := exists_head_of_ne_nil h8
    rw [hh8] at hs10; simp only [Option.mem_def, Option.some.injEq] at hs10; subst hs10
    rw [show st.segs 10 ++ st.segs 8 ++ st.segs 6 ++ [r] = st.segs 10 ++ (st.segs 8 ++ (st.segs 6 ++ [r])) by simp]
    refine diagLeg_append hD10 hE8 ?_
    have : legOf (st.segs 8 ++ (st.segs 6 ++ [r])) ((st.segs 8 ++ (st.segs 6 ++ [r])).length - 1) = r8.1 := by
      rw [hl8, List.cons_append, show (r8 :: (tl8 ++ (st.segs 6 ++ [r]))).length - 1 = (tl8 ++ (st.segs 6 ++ [r])).length by simp]
      exact legOf_cons_length r8 _
    rw [this]; exact hD100

/-- **Frame, forks**: the fork towards branch `i` off the head of the trunk stretch before it, a
plate of the kept axis, the stretch having at least three plates. [folklore] -/
theorem FlatInv.frame_fork {st : FS d} (hI : FlatInv hd Y a e τ st) :
    (st.segs 7 ≠ [] → ∃ s, (st.segs 6).head? = some s ∧ 3 ≤ (st.segs 6).length ∧ s.1.a = pl hd (p1 e) ∧
        Turn hd Y e (dsg e) (dsg (eB1 e)) (p1 e) s.1 (st.segs 7)) ∧
      (st.segs 9 ≠ [] → ∃ s, (st.segs 8).head? = some s ∧ 3 ≤ (st.segs 8).length ∧ s.1.a = pl hd (p2 e) ∧
        Turn hd Y e (dsg e) (dsg (eB2 e)) (p2 e) s.1 (st.segs 9)) := by
  constructor
  · intro h7
    have hK : SegOK hd Y e τ (eJOf hd Y a e τ st) 7 (st.segs 7) (st.segs (startOf 7)) := hI.segOK 7
    simp only [startOf, Matrix.cons_val] at hK
    obtain ⟨s, hs, hT⟩ := hK h7
    have hc := hI.order 7 6 (by decide) h7
    obtain ⟨r, tl, hl, hh⟩ := exists_head_of_ne_nil (l := st.segs 6) (by intro h; rw [h] at hc; simp [complete'] at hc)
    rw [hh] at hs; simp only [Option.mem_def, Option.some.injEq] at hs; subst hs
    simp only [complete', kindOf, Matrix.cons_val, hl, minLenOf] at hc
    exact ⟨r, hh, by rw [hl]; simpa using hc.1, hT.sAxis, hT⟩
  · intro h9
    have hK : SegOK hd Y e τ (eJOf hd Y a e τ st) 9 (st.segs 9) (st.segs (startOf 9)) := hI.segOK 9
    simp only [startOf, Matrix.cons_val] at hK
    obtain ⟨s, hs, hT⟩ := hK h9
    have hc := hI.order 9 8 (by decide) h9
    obtain ⟨r, tl, hl, hh⟩ := exists_head_of_ne_nil (l := st.segs 8) (by intro h; rw [h] at hc; simp [complete'] at hc)
    rw [hh] at hs; simp only [Option.mem_def, Option.some.injEq] at hs; subst hs
    simp only [complete', kindOf, Matrix.cons_val, hl, minLenOf] at hc
    exact ⟨r, hh, by rw [hl]; simpa using hc.1, hT.sAxis, hT⟩

/-- **Frame, branches**: branch `i` extended by its turn plate `γᵢ` is a diagonal leg of the signs
of its direction; the fork is complete. [folklore] -/
theorem FlatInv.frame_branch {st : FS d} (hI : FlatInv hd Y a e τ st) :
    (st.segs 11 ≠ [] → ∃ γ, (st.segs 7).head? = some γ ∧ (st.segs 7).length = 2 ∧
        DiagLeg hd Y e (dsg (eB1 e)) none (oth (p1 e)) (st.segs 11 ++ [γ])) ∧
      (st.segs 12 ≠ [] → ∃ γ, (st.segs 9).head? = some γ ∧ (st.segs 9).length = 2 ∧
        DiagLeg hd Y e (dsg (eB2 e)) none (oth (p2 e)) (st.segs 12 ++ [γ])) := by
  constructor
  · intro h11
    have hK : SegOK hd Y e τ (eJOf hd Y a e τ st) 11 (st.segs 11) (st.segs (startOf 11)) := hI.segOK 11
    simp only [startOf, Matrix.cons_val] at hK
    obtain ⟨s, hs, hD, hD0⟩ := hK h11
    have hc := hI.order 11 7 (by decide) h11
    obtain ⟨r, tl, hl, hh⟩ := exists_head_of_ne_nil (l := st.segs 7) (by intro h; rw [h] at hc; simp [complete'] at hc)
    rw [hh] at hs; simp only [Option.mem_def, Option.some.injEq] at hs; subst hs
    obtain ⟨_, _, _, _, hT⟩ := hI.frame_fork.1 (by rw [hl]; simp)
    have hlen : (st.segs 7).length = 2 := by
      have := hT.len; simp only [complete', kindOf, Matrix.cons_val, hl] at hc; rw [hl] at this ⊢; simp at this hc ⊢; omega
    exact ⟨r, hh, hlen, diagLeg_snoc hD hD0⟩
  · intro h12
    have hK : SegOK hd Y e τ (eJOf hd Y a e τ st) 12 (st.segs 12) (st.segs (startOf 12)) := hI.segOK 12
    simp only [startOf, Matrix.cons_val] at hK
    obtain ⟨s, hs, hD, hD0⟩ := hK h12
    have hc := hI.order 12 9 (by decide) h12
    obtain ⟨r, tl, hl, hh⟩ := exists_head_of_ne_nil (l := st.segs 9) (by intro h; rw [h] at hc; simp [complete'] at hc)
    rw [hh] at hs; simp only [Option.mem_def, Option.some.injEq] at hs; subst hs
    obtain ⟨_, _, _, _, hT⟩ := hI.frame_fork.2 (by rw [hl]; simp)
    have hlen : (st.segs 9).length = 2 := by
      have := hT.len; simp only [complete', kindOf, Matrix.cons_val, hl] at hc; rw [hl] at this ⊢; simp at this hc ⊢; omega
    exact ⟨r, hh, hlen, diagLeg_snoc hD hD0⟩

end Frame

end BGNd

end Percolation.Literature

end
