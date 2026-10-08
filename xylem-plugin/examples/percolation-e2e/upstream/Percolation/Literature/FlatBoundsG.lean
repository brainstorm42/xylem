import Percolation.Literature.FlatBoundsC
import Percolation.Util.Linter

/-!
# The flat gait, XIX–XXII

This module gathers 4 consecutive parts of the flat-gait development, in order:
XIX: bounds, IV — the turn back, the trunk, the forks, the branches ·
XX: bounds, V — absolute windows of the entry side ·
XXI: bounds, VI — absolute windows of the trunk ·
XXII: bounds, VII — forks, branches, the plate count, the quantitative separation.
Part 1 follows; the later parts keep their own headers below.

# Part 1 (The flat gait, XIX): bounds, IV — the turn back, the trunk, the forks, the branches

Relative plane windows of the later segments of the
flat gait (Grimmett, *Percolation*, 2nd ed. (1999), §7.3 pp. 171–174, case `H < L`): the turn back
(`FlatInv.win_GT`), the trunk as one diagonal leg off `T₀` (`FlatInv.win_T`), the forks
(`FlatInv.win_G1`, `FlatInv.win_G2`), and the branches, which advance laterally while their
forward coordinate drifts (`FlatInv.win_B1`, `FlatInv.win_B2`); and the stopping rules of the three
trunk stretches and of the branches at proper stages (`FlatInv.T1_stage`, `FlatInv.T2_stage`,
`FlatInv.T3_stage`, `FlatInv.B1_stage`, `FlatInv.B2_stage`) with the heads' stops
(`T_heads`).

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §7.3 pp. 171–174.
-/

noncomputable section

namespace Percolation.Literature

open LatticeModels Contour
open scoped Classical

namespace BGNd

variable {d : ℕ} [NeZero d] {hd : 3 ≤ d} {Y : FlatLayout} {a : Site 2} {e : MDir} {τ : TTok d} {st : FS d}

/-! ## The turn back and the trunk -/

/-- **The turn back's window** relative to the jog's head `J`, read along `e`. [folklore] -/
theorem FlatInv.win_GT (hI : FlatInv hd Y a e τ st) (hY : Y.OK) {J : BrickRec d} (hJ : (st.segs 4).head? = some J) :
    (∀ h0 : 0 < (st.segs 5).length,
        (Y.H : ℤ) + 1 ≤ upar hd (dsg e) (legOf (st.segs 5) 0).b - upar hd (dsg e) J.1.b ∧
        upar hd (dsg e) (legOf (st.segs 5) 0).b - upar hd (dsg e) J.1.b ≤ (Y.H : ℤ) + 1 + Y.Lp ∧
        |vperp hd (dsg e) (legOf (st.segs 5) 0).b - vperp hd (dsg e) J.1.b| ≤ (Y.H : ℤ) + 1 + Y.Lp) ∧
      (∀ h1 : 1 < (st.segs 5).length,
        Y.U + Y.m + 1 ≤ upar hd (dsg e) (legOf (st.segs 5) 1).b - upar hd (dsg e) (legOf (st.segs 5) 0).b ∧
        upar hd (dsg e) (legOf (st.segs 5) 1).b - upar hd (dsg e) (legOf (st.segs 5) 0).b ≤ Y.U + Y.H - Y.m - 1 ∧
        |vperp hd (dsg e) (legOf (st.segs 5) 1).b - vperp hd (dsg e) (legOf (st.segs 5) 0).b| ≤ Y.U - Y.m - 1) := by
  by_cases h5 : st.segs 5 = []
  · rw [h5]; exact ⟨fun h => absurd h (by simp), fun h => absurd h (by simp)⟩
  obtain ⟨J', hJ', -, hT⟩ := hI.frame_turnT h5
  have hJJ : J' = J := by rw [hJ] at hJ'; simpa using hJ'.symm
  subst hJJ
  exact hT.win' hY

/-- **The trunk's window** relative to the turn back's hop `T₀`: the three stretches form one
diagonal leg off `T₀`; after `j` hops the forward coordinate has advanced by between `j (U+m+1)`
and `j (U+H-m-1)` and the lateral one deviates by at most `j (H-2m-2)/2 + (U-m-1)`. [folklore] -/
theorem FlatInv.win_T (hI : FlatInv hd Y a e τ st) (hY : Y.OK) {T₀ : BrickRec d} (hT₀ : (st.segs 5).head? = some T₀) {j : ℕ}
    (hj : j < (st.segs 10 ++ st.segs 8 ++ st.segs 6 ++ [T₀]).length) :
    (j : ℤ) * (Y.U + Y.m + 1) ≤ upar hd (dsg e) (legOf (st.segs 10 ++ st.segs 8 ++ st.segs 6 ++ [T₀]) j).b - upar hd (dsg e) T₀.1.b ∧
      upar hd (dsg e) (legOf (st.segs 10 ++ st.segs 8 ++ st.segs 6 ++ [T₀]) j).b - upar hd (dsg e) T₀.1.b ≤ (j : ℤ) * (Y.U + Y.H - Y.m - 1) ∧
      2 * |vperp hd (dsg e) (legOf (st.segs 10 ++ st.segs 8 ++ st.segs 6 ++ [T₀]) j).b - vperp hd (dsg e) T₀.1.b| ≤
        (j : ℤ) * ((Y.H : ℤ) - 2 * Y.m - 2) + 2 * (Y.U - Y.m - 1) := by
  by_cases h6 : st.segs 6 = []
  · -- only `T₀`
    have h8 : st.segs 8 = [] := by
      by_contra h; have := hI.order 8 6 (by decide) h; rw [h6] at this; simp [complete'] at this
    have h10 : st.segs 10 = [] := by
      by_contra h; have := hI.order 10 6 (by decide) h; rw [h6] at this; simp [complete'] at this
    rw [h6, h8, h10] at hj ⊢
    simp at hj; subst hj
    have : legOf ([] ++ [] ++ [] ++ [T₀]) 0 = T₀.1 := legOf_snoc_zero _ _
    rw [this]; simp
    obtain ⟨hU, -, -, hLp0, hULp, -, -, -, hm0⟩ := hY.facts
    linarith
  obtain ⟨T₀', hT₀', -, hTE⟩ := hI.frame_trunk h6
  have hTT : T₀' = T₀ := by rw [hT₀] at hT₀'; simpa using hT₀'.symm
  subst hTT
  have h0 : legOf (st.segs 10 ++ st.segs 8 ++ st.segs 6 ++ [T₀']) 0 = T₀'.1 := legOf_snoc_zero _ _
  have hm := hTE.mono (k := 0) (k' := j) (Nat.zero_le _) hj 0
  have hv := hTE.vperp_dev' hY hj
  rw [h0] at hm hv
  push_cast at hm
  simp only [sub_zero] at hm
  exact ⟨hm.2.1, hm.2.2, hv⟩

/-! ## The forks and the branches -/

/-- **The first fork's window** relative to the first stretch's head `r6`, read along `e`. [folklore] -/
theorem FlatInv.win_G1 (hI : FlatInv hd Y a e τ st) (hY : Y.OK) {r6 : BrickRec d} (hr6 : (st.segs 6).head? = some r6) :
    (∀ h0 : 0 < (st.segs 7).length,
        (Y.H : ℤ) + 1 - Y.Lp ≤ upar hd (dsg e) (legOf (st.segs 7) 0).b - upar hd (dsg e) r6.1.b ∧
        upar hd (dsg e) (legOf (st.segs 7) 0).b - upar hd (dsg e) r6.1.b ≤ (Y.H : ℤ) + 1 ∧
        |vperp hd (dsg e) (legOf (st.segs 7) 0).b - vperp hd (dsg e) r6.1.b| ≤ (Y.H : ℤ) + 1 + Y.Lp) ∧
      (∀ h1 : 1 < (st.segs 7).length,
        (Y.m : ℤ) + 1 - Y.U ≤ upar hd (dsg e) (legOf (st.segs 7) 1).b - upar hd (dsg e) (legOf (st.segs 7) 0).b ∧
        upar hd (dsg e) (legOf (st.segs 7) 1).b - upar hd (dsg e) (legOf (st.segs 7) 0).b ≤ (Y.H : ℤ) - Y.m - 1 - Y.U ∧
        |vperp hd (dsg e) (legOf (st.segs 7) 1).b - vperp hd (dsg e) (legOf (st.segs 7) 0).b| ≤ Y.U + Y.H - Y.m - 1) := by
  by_cases h7 : st.segs 7 = []
  · rw [h7]; exact ⟨fun h => absurd h (by simp), fun h => absurd h (by simp)⟩
  obtain ⟨s, hs, -, -, hT⟩ := hI.frame_fork.1 h7
  have hss : s = r6 := by rw [hr6] at hs; simpa using hs.symm
  subst hss
  obtain ⟨⟨hflip1, -⟩, -⟩ := flip_keep_B e
  have hp1 : p1 e = 1 := by unfold p1 keepIdx; rw [(flipIdx_eB e).1]; rfl
  rw [hp1] at hT
  exact hT.win hY hflip1

/-- **The second fork's window** relative to the second stretch's head `r8`, read along `e`. [folklore] -/
theorem FlatInv.win_G2 (hI : FlatInv hd Y a e τ st) (hY : Y.OK) {r8 : BrickRec d} (hr8 : (st.segs 8).head? = some r8) :
    (∀ h0 : 0 < (st.segs 9).length,
        (Y.H : ℤ) + 1 - Y.Lp ≤ upar hd (dsg e) (legOf (st.segs 9) 0).b - upar hd (dsg e) r8.1.b ∧
        upar hd (dsg e) (legOf (st.segs 9) 0).b - upar hd (dsg e) r8.1.b ≤ (Y.H : ℤ) + 1 ∧
        |vperp hd (dsg e) (legOf (st.segs 9) 0).b - vperp hd (dsg e) r8.1.b| ≤ (Y.H : ℤ) + 1 + Y.Lp) ∧
      (∀ h1 : 1 < (st.segs 9).length,
        (Y.m : ℤ) + 1 - Y.U ≤ upar hd (dsg e) (legOf (st.segs 9) 1).b - upar hd (dsg e) (legOf (st.segs 9) 0).b ∧
        upar hd (dsg e) (legOf (st.segs 9) 1).b - upar hd (dsg e) (legOf (st.segs 9) 0).b ≤ (Y.H : ℤ) - Y.m - 1 - Y.U ∧
        |vperp hd (dsg e) (legOf (st.segs 9) 1).b - vperp hd (dsg e) (legOf (st.segs 9) 0).b| ≤ Y.U + Y.H - Y.m - 1) := by
  by_cases h9 : st.segs 9 = []
  · rw [h9]; exact ⟨fun h => absurd h (by simp), fun h => absurd h (by simp)⟩
  obtain ⟨s, hs, -, -, hT⟩ := hI.frame_fork.2 h9
  have hss : s = r8 := by rw [hr8] at hs; simpa using hs.symm
  subst hss
  obtain ⟨-, hflip2, -⟩ := flip_keep_B e
  have hp2 : p2 e = 0 := by unfold p2 keepIdx; rw [(flipIdx_eB e).2]; rfl
  rw [hp2] at hT
  exact hT.win hY hflip2

/-- **The first branch's window** relative to the first fork's hop `γ₁`: the lateral coordinate
(read along `e`) decreases by between `(k+1)(U+m+1)` and `(k+1)(U+H-m-1)` after `k + 1` hops,
the forward one deviates by at most `(k+1)(H-2m-2)/2 + (U-m-1)`. [folklore] -/
theorem FlatInv.win_B1 (hI : FlatInv hd Y a e τ st) (hY : Y.OK) {γ : BrickRec d} (hγ : (st.segs 7).head? = some γ) {k : ℕ} (hk : k < (st.segs 11).length) :
    ((k : ℤ) + 1) * (Y.U + Y.m + 1) ≤ vperp hd (dsg e) γ.1.b - vperp hd (dsg e) (legOf (st.segs 11) k).b ∧
      vperp hd (dsg e) γ.1.b - vperp hd (dsg e) (legOf (st.segs 11) k).b ≤ ((k : ℤ) + 1) * (Y.U + Y.H - Y.m - 1) ∧
      2 * |upar hd (dsg e) (legOf (st.segs 11) k).b - upar hd (dsg e) γ.1.b| ≤ ((k : ℤ) + 1) * ((Y.H : ℤ) - 2 * Y.m - 2) + 2 * (Y.U - Y.m - 1) := by
  obtain ⟨γ', hγ', -, hBE⟩ := hI.frame_branch.1 (List.ne_nil_of_length_pos (by omega))
  have hgg : γ' = γ := by rw [hγ] at hγ'; simpa using hγ'.symm
  subst hgg
  obtain ⟨⟨hflip1, hkeep1⟩, -⟩ := flip_keep_B e
  change dsg (eB1 e) 0 = -dsg e 0 at hflip1
  have conv := fun b => upar_vperp_flip0 hd (σ := dsg e) (σ' := dsg (eB1 e)) hflip1 hkeep1 b
  have hk' : k + 1 < (st.segs 11 ++ [γ']).length := by simp; omega
  have hm := hBE.mono (k := 0) (k' := k + 1) (by omega) hk' 0
  have hv := hBE.vperp_dev' hY hk'
  rw [legOf_append_singleton_succ, legOf_snoc_zero] at hm hv
  rw [(conv _).1, (conv _).1] at hm
  rw [(conv _).2, (conv _).2, show -upar hd (dsg e) (legOf (st.segs 11) k).b - -upar hd (dsg e) γ'.1.b =
    -(upar hd (dsg e) (legOf (st.segs 11) k).b - upar hd (dsg e) γ'.1.b) by ring, abs_neg] at hv
  push_cast at hm hv ⊢
  simp only [sub_zero] at hm
  exact ⟨by linarith [hm.2.1], by linarith [hm.2.2], hv⟩

/-- **The second branch's window** relative to the second fork's hop `γ₂`: the lateral coordinate
increases. [folklore] -/
theorem FlatInv.win_B2 (hI : FlatInv hd Y a e τ st) (hY : Y.OK) {γ : BrickRec d} (hγ : (st.segs 9).head? = some γ) {k : ℕ} (hk : k < (st.segs 12).length) :
    ((k : ℤ) + 1) * (Y.U + Y.m + 1) ≤ vperp hd (dsg e) (legOf (st.segs 12) k).b - vperp hd (dsg e) γ.1.b ∧
      vperp hd (dsg e) (legOf (st.segs 12) k).b - vperp hd (dsg e) γ.1.b ≤ ((k : ℤ) + 1) * (Y.U + Y.H - Y.m - 1) ∧
      2 * |upar hd (dsg e) (legOf (st.segs 12) k).b - upar hd (dsg e) γ.1.b| ≤ ((k : ℤ) + 1) * ((Y.H : ℤ) - 2 * Y.m - 2) + 2 * (Y.U - Y.m - 1) := by
  obtain ⟨γ', hγ', -, hBE⟩ := hI.frame_branch.2 (List.ne_nil_of_length_pos (by omega))
  have hgg : γ' = γ := by rw [hγ] at hγ'; simpa using hγ'.symm
  subst hgg
  obtain ⟨-, hflip2, hkeep2⟩ := flip_keep_B e
  change dsg (eB2 e) 1 = -dsg e 1 at hflip2
  have conv := fun b => upar_vperp_flip1 hd (σ := dsg e) (σ' := dsg (eB2 e)) hkeep2 hflip2 b
  have hk' : k + 1 < (st.segs 12 ++ [γ']).length := by simp; omega
  have hm := hBE.mono (k := 0) (k' := k + 1) (by omega) hk' 0
  have hv := hBE.vperp_dev' hY hk'
  rw [legOf_append_singleton_succ, legOf_snoc_zero] at hm hv
  rw [(conv _).1, (conv _).1] at hm
  rw [(conv _).2, (conv _).2] at hv
  push_cast at hm hv ⊢
  simp only [sub_zero] at hm
  exact ⟨by linarith [hm.2.1], by linarith [hm.2.2], hv⟩

/-! ## The stopping rules of the stretches and of the branches -/

/-- **The first stretch at a proper stage**: a plate before the head, beyond the second, past the
first take-off line has the wrong axis. [folklore] -/
theorem FlatInv.T1_stage (hI : FlatInv hd Y a e τ st) {j : ℕ} (hj : j + 1 < (st.segs 6).length) (hj2 : 2 ≤ j)
    (hpass : fpassed hd Y a e (eB1 e) (legOf (st.segs 6) j).b) : (legOf (st.segs 6) j).a ≠ pl hd (p1 e) := by
  intro hax
  obtain ⟨r, tl, hr, hl, hnc⟩ := hI.stage 6 hj
  simp only [complete', kindOf, Fin.isValue, Matrix.cons_val, minLenOf, legStop, legAxisOf, hl, hr, not_and] at hnc
  refine hnc (by simp; omega) ?_ (fun q hq => by simp only [Option.some.injEq] at hq; rw [← hq]; exact hax)
  simp only [Fin.isValue, show (6 : Fin 13) = 4 ↔ False by decide, if_false, if_true]
  exact hpass

/-- **The second stretch at a proper stage.** [folklore] -/
theorem FlatInv.T2_stage (hI : FlatInv hd Y a e τ st) {j : ℕ} (hj : j + 1 < (st.segs 8).length) (hj2 : 2 ≤ j)
    (hpass : fpassed hd Y a e (eB2 e) (legOf (st.segs 8) j).b) : (legOf (st.segs 8) j).a ≠ pl hd (p2 e) := by
  intro hax
  obtain ⟨r, tl, hr, hl, hnc⟩ := hI.stage 8 hj
  simp only [complete', kindOf, Fin.isValue, Matrix.cons_val, minLenOf, legStop, legAxisOf, hl, hr, not_and] at hnc
  refine hnc (by simp; omega) ?_ (fun q hq => by simp only [Option.some.injEq] at hq; rw [← hq]; exact hax)
  simp only [Fin.isValue, show (8 : Fin 13) = 4 ↔ False by decide, show (8 : Fin 13) = 6 ↔ False by decide, if_false, if_true]
  exact hpass

/-- **The third stretch at a proper stage**: a plate before the head has room. [folklore] -/
theorem FlatInv.T3_stage (hI : FlatInv hd Y a e τ st) {j : ℕ} (hj : j + 1 < (st.segs 10).length) :
    froom hd Y a e e (legOf (st.segs 10) j).b := by
  obtain ⟨r, tl, hr, hl, hnc⟩ := hI.stage 10 hj
  simp only [complete', kindOf, Fin.isValue, Matrix.cons_val, minLenOf, legStop, legAxisOf, hl, hr, not_and, fdirOf] at hnc
  by_contra hroom
  exact hnc (by simp) (by
    simp only [Fin.isValue, show (10 : Fin 13) = 4 ↔ False by decide, show (10 : Fin 13) = 6 ↔ False by decide,
      show (10 : Fin 13) = 8 ↔ False by decide, if_false]
    exact hroom) (fun q hq => by simp at hq)

/-- **The first branch at a proper stage**: a plate before the head has room. [folklore] -/
theorem FlatInv.B1_stage (hI : FlatInv hd Y a e τ st) {j : ℕ} (hj : j + 1 < (st.segs 11).length) :
    froom hd Y a e (eB1 e) (legOf (st.segs 11) j).b := by
  obtain ⟨r, tl, hr, hl, hnc⟩ := hI.stage 11 hj
  simp only [complete', kindOf, Fin.isValue, Matrix.cons_val, minLenOf, legStop, legAxisOf, hl, hr, not_and, fdirOf] at hnc
  by_contra hroom
  exact hnc (by simp) (by
    simp only [Fin.isValue, show (11 : Fin 13) = 4 ↔ False by decide, show (11 : Fin 13) = 6 ↔ False by decide,
      show (11 : Fin 13) = 8 ↔ False by decide, if_false]
    exact hroom) (fun q hq => by simp at hq)

/-- **The second branch at a proper stage**: a plate before the head has room. [folklore] -/
theorem FlatInv.B2_stage (hI : FlatInv hd Y a e τ st) {j : ℕ} (hj : j + 1 < (st.segs 12).length) :
    froom hd Y a e (eB2 e) (legOf (st.segs 12) j).b := by
  obtain ⟨r, tl, hr, hl, hnc⟩ := hI.stage 12 hj
  simp only [complete', kindOf, Fin.isValue, Matrix.cons_val, minLenOf, legStop, legAxisOf, hl, hr, not_and, fdirOf] at hnc
  by_contra hroom
  exact hnc (by simp) (by
    simp only [Fin.isValue, show (12 : Fin 13) = 4 ↔ False by decide, show (12 : Fin 13) = 6 ↔ False by decide,
      show (12 : Fin 13) = 8 ↔ False by decide, if_false]
    exact hroom) (fun q hq => by simp at hq)

/-- **The heads' stops**: once complete, the first stretch's head is past the first take-off line
with at least three plates, the second stretch's past the second, the third has no room; the
branches' heads have no room. [folklore] -/
theorem T_heads (hd : 3 ≤ d) (Y : FlatLayout) (a : Site 2) (e : MDir) (τ : TTok d) (st : FS d) :
    (complete' hd Y a e τ (eJOf hd Y a e τ st) 6 (st.segs 6) → 3 ≤ (st.segs 6).length ∧
        fpassed hd Y a e (eB1 e) (legOf (st.segs 6) ((st.segs 6).length - 1)).b) ∧
      (complete' hd Y a e τ (eJOf hd Y a e τ st) 8 (st.segs 8) → 3 ≤ (st.segs 8).length ∧
        fpassed hd Y a e (eB2 e) (legOf (st.segs 8) ((st.segs 8).length - 1)).b) ∧
      (complete' hd Y a e τ (eJOf hd Y a e τ st) 10 (st.segs 10) → ¬froom hd Y a e e (legOf (st.segs 10) ((st.segs 10).length - 1)).b) ∧
      (complete' hd Y a e τ (eJOf hd Y a e τ st) 11 (st.segs 11) → ¬froom hd Y a e (eB1 e) (legOf (st.segs 11) ((st.segs 11).length - 1)).b) ∧
      (complete' hd Y a e τ (eJOf hd Y a e τ st) 12 (st.segs 12) → ¬froom hd Y a e (eB2 e) (legOf (st.segs 12) ((st.segs 12).length - 1)).b) := by
  have key : ∀ (i : Fin 13) (l : List (BrickRec d)) (r : BrickRec d) (tl : List (BrickRec d)), l = r :: tl → legOf l (l.length - 1) = r.1 :=
    fun i l r tl hl => by rw [hl]; exact legOf_cons_length r tl
  refine ⟨fun hc => ?_, fun hc => ?_, fun hc => ?_, fun hc => ?_, fun hc => ?_⟩
  · rcases hh : st.segs 6 with _ | ⟨r, tl⟩
    · simp [complete', kindOf, hh] at hc
    · simp only [complete', kindOf, Fin.isValue, Matrix.cons_val, hh, minLenOf, legStop,
        show (6 : Fin 13) = 4 ↔ False by decide, if_false, if_true, true_or] at hc
      rw [← hh] at hc ⊢; rw [key 6 _ r tl hh]; exact ⟨hc.1, hc.2.1⟩
  · rcases hh : st.segs 8 with _ | ⟨r, tl⟩
    · simp [complete', kindOf, hh] at hc
    · simp only [complete', kindOf, Fin.isValue, Matrix.cons_val, hh, minLenOf, legStop,
        show (8 : Fin 13) = 4 ↔ False by decide, show (8 : Fin 13) = 6 ↔ False by decide, if_false, if_true, or_true] at hc
      rw [← hh] at hc ⊢; rw [key 8 _ r tl hh]; exact ⟨hc.1, hc.2.1⟩
  · rcases hh : st.segs 10 with _ | ⟨r, tl⟩
    · simp [complete', kindOf, hh] at hc
    · simp only [complete', kindOf, Fin.isValue, Matrix.cons_val, hh, minLenOf, legStop, fdirOf,
        show (10 : Fin 13) = 4 ↔ False by decide, show (10 : Fin 13) = 6 ↔ False by decide, show (10 : Fin 13) = 8 ↔ False by decide,
        if_false] at hc
      rw [← hh] at hc ⊢; rw [key 10 _ r tl hh]; exact hc.2.1
  · rcases hh : st.segs 11 with _ | ⟨r, tl⟩
    · simp [complete', kindOf, hh] at hc
    · simp only [complete', kindOf, Fin.isValue, Matrix.cons_val, hh, minLenOf, legStop, fdirOf,
        show (11 : Fin 13) = 4 ↔ False by decide, show (11 : Fin 13) = 6 ↔ False by decide, show (11 : Fin 13) = 8 ↔ False by decide,
        if_false] at hc
      rw [← hh] at hc ⊢; rw [key 11 _ r tl hh]; exact hc.2.1
  · rcases hh : st.segs 12 with _ | ⟨r, tl⟩
    · simp [complete', kindOf, hh] at hc
    · simp only [complete', kindOf, Fin.isValue, Matrix.cons_val, hh, minLenOf, legStop, fdirOf,
        show (12 : Fin 13) = 4 ↔ False by decide, show (12 : Fin 13) = 6 ↔ False by decide, show (12 : Fin 13) = 8 ↔ False by decide,
        if_false] at hc
      rw [← hh] at hc ⊢; rw [key 12 _ r tl hh]; exact hc.2.1

end BGNd

end Percolation.Literature

end

/-!
# Part 2 (The flat gait, XX): bounds, V — absolute windows of the entry side

Chaining the relative windows of the flat gait
(Grimmett, *Percolation*, 2nd ed. (1999), §7.3 pp. 171–174, case `H < L`) from the token: with
`S`, `V` the token's forward and lateral diagonal coordinates (read along `e`), the riser's head is
at `S + [U, 215 U]` and `V ± 107 U` (`FlatInv.abs_R`), the preamble at `S + [2U, 399 U]`,
`V ± 120 U` with head beyond `S + 163 U` (`FlatInv.abs_P`), the jog turn at `S + [161 U, 400 U]`,
`V ± 123 U` (`FlatInv.abs_GJ`), the jog at `S + [95 U, 466 U]` between its start and `19 U`
beyond the target lane (`FlatInv.abs_J`), and the turn back at `S + [95 U, 469 U]` within `22 U`
of the lane (`FlatInv.abs_GT`).

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §7.3 pp. 171–174.
-/

noncomputable section

namespace Percolation.Literature

open LatticeModels Contour
open scoped Classical

namespace BGNd

variable {d : ℕ} [NeZero d] {hd : 3 ≤ d} {Y : FlatLayout} {a : Site 2} {e : MDir} {τ : TTok d} {st : FS d}

/-- A later nonempty segment forces an earlier one to be complete and nonempty with a head. [folklore] -/
theorem FlatInv.head_of_later (hI : FlatInv hd Y a e τ st) {i j : Fin 13} (hij : j < i) (hi : st.segs i ≠ []) :
    complete' hd Y a e τ (eJOf hd Y a e τ st) j (st.segs j) ∧ ∃ r, (st.segs j).head? = some r := by
  have hc := hI.order i j hij hi
  refine ⟨hc, ?_⟩
  rcases hh : st.segs j with _ | ⟨r, tl⟩
  · rw [hh] at hc; simp [complete'] at hc
  · exact ⟨r, rfl⟩

/-! ## The riser's head, the preamble, the jog turn -/

/-- **The riser's head**, once the preamble has started. [folklore] -/
theorem FlatInv.abs_R (hI : FlatInv hd Y a e τ st) (hY : Y.OK) (hτ : FTAdm hd Y a e τ) {R : BrickRec d} (hR : (st.segs 1).head? = some R)
    (hc : complete' hd Y a e τ (eJOf hd Y a e τ st) 1 (st.segs 1)) :
    upar hd (dsg e) τ.pos + Y.U ≤ upar hd (dsg e) R.1.b ∧ upar hd (dsg e) R.1.b ≤ upar hd (dsg e) τ.pos + 215 * Y.U ∧
      |vperp hd (dsg e) R.1.b - vperp hd (dsg e) τ.pos| ≤ 107 * Y.U := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  have hlast := legOf_last_of_head hR
  have h1 : st.segs 1 ≠ [] := by intro h; rw [h] at hR; simp at hR
  have hlen := hI.riser_len_le hY hτ
  have hk : (st.segs 1).length - 1 < (st.segs 1).length := by have := List.length_pos_of_ne_nil h1; omega
  obtain ⟨-, hu, hv, -⟩ := hI.win_riser hY hτ hk
  have hlo := hI.riser_head_upar hY hτ hc
  rw [hlast] at hu hv hlo
  have hcast : (((st.segs 1).length - 1 : ℕ) : ℤ) + 1 ≤ 106 := by
    have h0 : 1 ≤ (st.segs 1).length := List.length_pos_of_ne_nil h1
    push_cast [Nat.cast_sub h0]; linarith [show ((st.segs 1).length : ℤ) ≤ 106 by exact_mod_cast hlen]
  have hH8 : 8 * ((Y.H : ℤ) + 1) ≤ Y.U := hflat
  have hkU := mul_le_mul_of_nonneg_right hcast hU.le
  refine ⟨hlo, by linarith, ?_⟩
  calc |vperp hd (dsg e) R.1.b - vperp hd (dsg e) τ.pos| ≤ ((((st.segs 1).length - 1 : ℕ) : ℤ) + 1) * Y.U + Y.H := hv
    _ ≤ 107 * Y.U := by linarith

/-- **The preamble's plates**, and its head once complete. [folklore] -/
theorem FlatInv.abs_P (hI : FlatInv hd Y a e τ st) (hY : Y.OK) (hτ : FTAdm hd Y a e τ) :
    (∀ r ∈ st.segs 2, upar hd (dsg e) τ.pos + 2 * Y.U ≤ upar hd (dsg e) r.1.b ∧ upar hd (dsg e) r.1.b ≤ upar hd (dsg e) τ.pos + 399 * Y.U ∧
        |vperp hd (dsg e) r.1.b - vperp hd (dsg e) τ.pos| ≤ 120 * Y.U) ∧
      (∀ P, (st.segs 2).head? = some P → complete' hd Y a e τ (eJOf hd Y a e τ st) 2 (st.segs 2) →
        upar hd (dsg e) τ.pos + 163 * Y.U ≤ upar hd (dsg e) P.1.b) := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  by_cases h2 : st.segs 2 = []
  · rw [h2]; exact ⟨fun r hr => absurd hr (by simp), fun P hP => by simp at hP⟩
  obtain ⟨hc1, R, hR⟩ := hI.head_of_later (i := 2) (j := 1) (by decide) h2
  obtain ⟨hRlo, hRhi, hRv⟩ := hI.abs_R hY hτ hR hc1
  have hlenP := hI.pre_len.1
  have plate : ∀ k, (hk : k < (st.segs 2).length) →
      upar hd (dsg e) τ.pos + 2 * Y.U ≤ upar hd (dsg e) (legOf (st.segs 2) k).b ∧ upar hd (dsg e) (legOf (st.segs 2) k).b ≤ upar hd (dsg e) τ.pos + 399 * Y.U ∧
      |vperp hd (dsg e) (legOf (st.segs 2) k).b - vperp hd (dsg e) τ.pos| ≤ 120 * Y.U ∧
      ((k : ℤ) + 1) * (Y.U + Y.m + 1) ≤ upar hd (dsg e) (legOf (st.segs 2) k).b - upar hd (dsg e) R.1.b := by
    intro k hk
    obtain ⟨hlo, hhi, hv⟩ := hI.win_pre hY hR hk
    have hk1 : (0 : ℤ) ≤ k := by positivity
    have hk2 : (k : ℤ) ≤ 162 := by have := Nat.cast_le (α := ℤ).2 (show k ≤ 162 by omega); simpa using this
    have hH2 : 0 ≤ (Y.H : ℤ) - 2 * Y.m - 2 := by linarith
    refine ⟨by nlinarith, by nlinarith, ?_, hlo⟩
    have hv' : |vperp hd (dsg e) (legOf (st.segs 2) k).b - vperp hd (dsg e) R.1.b| ≤ 81 * ((Y.H : ℤ) - 2 * Y.m - 2) + 2 * (Y.U - Y.m - 1) := by nlinarith
    calc |vperp hd (dsg e) (legOf (st.segs 2) k).b - vperp hd (dsg e) τ.pos|
        = |(vperp hd (dsg e) (legOf (st.segs 2) k).b - vperp hd (dsg e) R.1.b) + (vperp hd (dsg e) R.1.b - vperp hd (dsg e) τ.pos)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
      _ ≤ _ := by linarith
  constructor
  · intro r hr
    obtain ⟨k, hk, hkr⟩ := exists_legOf_of_mem hr
    rw [← hkr]; exact ⟨(plate k hk).1, (plate k hk).2.1, (plate k hk).2.2.1⟩
  · intro P hP hc
    have hlast := legOf_last_of_head hP
    have h162 := hI.pre_len.2 hc
    have hk : (st.segs 2).length - 1 < (st.segs 2).length := by omega
    have := (plate _ hk).2.2.2
    rw [hlast] at this
    have hcast : (162 : ℤ) ≤ (((st.segs 2).length - 1 : ℕ) : ℤ) + 1 := by
      push_cast [Nat.cast_sub (show 1 ≤ (st.segs 2).length by omega)]; linarith [show (162 : ℤ) ≤ (st.segs 2).length by exact_mod_cast h162]
    nlinarith

/-- **The jog turn's plates.** [folklore] -/
theorem FlatInv.abs_GJ (hI : FlatInv hd Y a e τ st) (hY : Y.OK) (hτ : FTAdm hd Y a e τ) :
    ∀ r ∈ st.segs 3, upar hd (dsg e) τ.pos + 161 * Y.U ≤ upar hd (dsg e) r.1.b ∧ upar hd (dsg e) r.1.b ≤ upar hd (dsg e) τ.pos + 400 * Y.U ∧
      |vperp hd (dsg e) r.1.b - vperp hd (dsg e) τ.pos| ≤ 123 * Y.U := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  intro r hr
  have h3 : st.segs 3 ≠ [] := List.ne_nil_of_mem hr
  obtain ⟨hc2, P, hP⟩ := hI.head_of_later (i := 3) (j := 2) (by decide) h3
  obtain ⟨hPall, hPhead⟩ := hI.abs_P hY hτ
  obtain ⟨-, hPhi, hPv⟩ := hPall P (List.mem_of_mem_head? hP)
  have hPlo := hPhead P hP hc2
  obtain ⟨hw0, hw1⟩ := hI.win_GJ hY hP
  obtain ⟨k, hk, hkr⟩ := exists_legOf_of_mem hr
  rw [← hkr]
  obtain ⟨_, _, _, hT⟩ := hI.frame_turnJ h3
  have hlen := hT.len
  have hk2 : k < 2 := by omega
  obtain ⟨a0, b0, c0⟩ := hw0 (by omega)
  have hH8 : 8 * ((Y.H : ℤ) + 1) ≤ Y.U := hflat
  interval_cases k
  · refine ⟨by linarith, by linarith, ?_⟩
    calc |vperp hd (dsg e) (legOf (st.segs 3) 0).b - vperp hd (dsg e) τ.pos|
        = |(vperp hd (dsg e) (legOf (st.segs 3) 0).b - vperp hd (dsg e) P.1.b) + (vperp hd (dsg e) P.1.b - vperp hd (dsg e) τ.pos)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
      _ ≤ _ := by linarith
  · obtain ⟨a1, b1, c1⟩ := hw1 hk
    refine ⟨by linarith, by linarith, ?_⟩
    calc |vperp hd (dsg e) (legOf (st.segs 3) 1).b - vperp hd (dsg e) τ.pos|
        = |(vperp hd (dsg e) (legOf (st.segs 3) 1).b - vperp hd (dsg e) (legOf (st.segs 3) 0).b) +
            ((vperp hd (dsg e) (legOf (st.segs 3) 0).b - vperp hd (dsg e) P.1.b) + (vperp hd (dsg e) P.1.b - vperp hd (dsg e) τ.pos))| := by ring_nf
      _ ≤ _ := abs_add_le _ _
      _ ≤ |vperp hd (dsg e) (legOf (st.segs 3) 1).b - vperp hd (dsg e) (legOf (st.segs 3) 0).b| +
            (|vperp hd (dsg e) (legOf (st.segs 3) 0).b - vperp hd (dsg e) P.1.b| + |vperp hd (dsg e) P.1.b - vperp hd (dsg e) τ.pos|) := by
          linarith [abs_add_le (vperp hd (dsg e) (legOf (st.segs 3) 0).b - vperp hd (dsg e) P.1.b) (vperp hd (dsg e) P.1.b - vperp hd (dsg e) τ.pos)]
      _ ≤ _ := by linarith

/-! ## The jog and the turn back -/

/-- **The jog's plates**: forward within `S + [95 U, 466 U]`; laterally between the token's
coordinate `± 123 U` and `19 U` beyond the target lane; the head of the complete jog within
`19 U` of the lane. [folklore] -/
theorem FlatInv.abs_J (hI : FlatInv hd Y a e τ st) (hY : Y.OK) (hτ : FTAdm hd Y a e τ) :
    (∀ r ∈ st.segs 4, upar hd (dsg e) τ.pos + 95 * Y.U ≤ upar hd (dsg e) r.1.b ∧ upar hd (dsg e) r.1.b ≤ upar hd (dsg e) τ.pos + 466 * Y.U ∧
        min (Uc hd (latDir e true).1 τ.pos - 123 * Y.U) (Y.lane (ftgt a e) e - 19 * Y.U) ≤ Uc hd (latDir e true).1 r.1.b ∧
        Uc hd (latDir e true).1 r.1.b ≤ max (Uc hd (latDir e true).1 τ.pos + 123 * Y.U) (Y.lane (ftgt a e) e + 19 * Y.U)) ∧
      (∀ J, (st.segs 4).head? = some J → complete' hd Y a e τ (eJOf hd Y a e τ st) 4 (st.segs 4) →
        |Uc hd (latDir e true).1 J.1.b - Y.lane (ftgt a e) e| ≤ 19 * Y.U) := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  by_cases h4 : st.segs 4 = []
  · rw [h4]; exact ⟨fun r hr => absurd hr (by simp), fun J hJ => by simp at hJ⟩
  obtain ⟨hc3, γ, hγ⟩ := hI.head_of_later (i := 4) (j := 3) (by decide) h4
  obtain ⟨hγlo, hγhi, hγv⟩ := hI.abs_GJ hY hτ γ (List.mem_of_mem_head? hγ)
  have hlenJ := hI.J_len hY hτ
  have hsj : (sgOf (eJOf hd Y a e τ st) : ℤ) = 1 ∨ (sgOf (eJOf hd Y a e τ st) : ℤ) = -1 := by
    rcases Int.units_eq_one_or (sgOf (eJOf hd Y a e τ st)) with h' | h' <;> simp [h']
  have hs1 : |(sgOf e : ℤ)| = 1 := by rcases Int.units_eq_one_or (sgOf e) with h' | h' <;> simp [h']
  have hγlat : |Uc hd (latDir e true).1 γ.1.b - Uc hd (latDir e true).1 τ.pos| ≤ 123 * Y.U := by
    rw [Uc_lat_eq_vperp, Uc_lat_eq_vperp, ← mul_sub, abs_mul, hs1, one_mul]; exact hγv
  have hH8 : 8 * ((Y.H : ℤ) + 1) ≤ Y.U := hflat
  constructor
  · intro r hr
    obtain ⟨k, hk, hkr⟩ := exists_legOf_of_mem hr
    rw [← hkr]
    obtain ⟨-, -, hw⟩ := hI.win_J hY hγ hk
    obtain ⟨hg1, hg2⟩ := hI.J_gap hY hτ hγ hk
    unfold jgap at hg1 hg2
    have hk2 : (k : ℤ) + 1 ≤ 1021 := by have := Nat.cast_le (α := ℤ).2 (show k + 1 ≤ 1021 by omega); push_cast at this; exact this
    have hH2 : 0 ≤ (Y.H : ℤ) - 2 * Y.m - 2 := by linarith
    have hkk := mul_le_mul_of_nonneg_right hk2 hH2
    have hw' : |upar hd (dsg e) (legOf (st.segs 4) k).b - upar hd (dsg e) γ.1.b| ≤ 511 * ((Y.H : ℤ) - 2 * Y.m - 2) + (Y.U - Y.m - 1) := by linarith
    rw [abs_le] at hw' hγlat
    refine ⟨by linarith, by linarith, ?_, ?_⟩
    · rw [min_le_iff]
      rcases hsj with h1 | h1 <;> rw [h1] at hg1 hg2
      · left; linarith
      · right; linarith
    · rw [le_max_iff]
      rcases hsj with h1 | h1 <;> rw [h1] at hg1 hg2
      · right; linarith
      · left; linarith
  · intro J hJ hc
    have hlast := legOf_last_of_head hJ
    have hk : (st.segs 4).length - 1 < (st.segs 4).length := by have := List.length_pos_of_ne_nil h4; omega
    obtain ⟨-, hg2⟩ := hI.J_gap hY hτ hγ hk
    rw [hlast] at hg2
    unfold jgap at hg2
    -- the head fits
    have hfit : (sgOf (eJOf hd Y a e τ st) : ℤ) * (Y.lane (ftgt a e) e - Uc hd (latDir e true).1 J.1.b) ≤ Y.U := by
      obtain ⟨tl, hl⟩ : ∃ tl, st.segs 4 = J :: tl := by
        rcases hh : st.segs 4 with _ | ⟨r0, tl⟩
        · exact absurd hh h4
        · rw [hh] at hJ; simp only [List.head?_cons, Option.some.injEq] at hJ; subst hJ; exact ⟨tl, rfl⟩
      simp only [complete', kindOf, Fin.isValue, Matrix.cons_val, hl, minLenOf, legStop, if_true, ffitsJ] at hc
      exact hc.2.1
    rw [abs_le]
    rcases hsj with h1 | h1 <;> rw [h1] at hfit hg2 <;> constructor <;> linarith

/-- **The turn back's plates** (and the jog's head before them): forward within
`S + [95 U, 469 U]`, laterally within `22 U` of the target lane. [folklore] -/
theorem FlatInv.abs_GT (hI : FlatInv hd Y a e τ st) (hY : Y.OK) (hτ : FTAdm hd Y a e τ) :
    ∀ r ∈ st.segs 5, upar hd (dsg e) τ.pos + 95 * Y.U ≤ upar hd (dsg e) r.1.b ∧ upar hd (dsg e) r.1.b ≤ upar hd (dsg e) τ.pos + 469 * Y.U ∧
      |Uc hd (latDir e true).1 r.1.b - Y.lane (ftgt a e) e| ≤ 22 * Y.U := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  intro r hr
  have h5 : st.segs 5 ≠ [] := List.ne_nil_of_mem hr
  obtain ⟨hc4, J, hJ⟩ := hI.head_of_later (i := 5) (j := 4) (by decide) h5
  obtain ⟨hJall, hJhead⟩ := hI.abs_J hY hτ
  obtain ⟨hJlo, hJhi, -, -⟩ := hJall J (List.mem_of_mem_head? hJ)
  have hJlat := hJhead J hJ hc4
  obtain ⟨hw0, hw1⟩ := hI.win_GT hY hJ
  obtain ⟨k, hk, hkr⟩ := exists_legOf_of_mem hr
  rw [← hkr]
  obtain ⟨_, _, _, hT⟩ := hI.frame_turnT h5
  have hlen := hT.len
  have hk2 : k < 2 := by omega
  obtain ⟨a0, b0, c0⟩ := hw0 (by omega)
  have hH8 : 8 * ((Y.H : ℤ) + 1) ≤ Y.U := hflat
  have hs1 : |(sgOf e : ℤ)| = 1 := by rcases Int.units_eq_one_or (sgOf e) with h' | h' <;> simp [h']
  have lat0 : |Uc hd (latDir e true).1 (legOf (st.segs 5) 0).b - Uc hd (latDir e true).1 J.1.b| ≤ (Y.H : ℤ) + 1 + Y.Lp := by
    rw [Uc_lat_eq_vperp, Uc_lat_eq_vperp, ← mul_sub, abs_mul, hs1, one_mul]; exact c0
  interval_cases k
  · refine ⟨by linarith, by linarith, ?_⟩
    calc |Uc hd (latDir e true).1 (legOf (st.segs 5) 0).b - Y.lane (ftgt a e) e|
        = |(Uc hd (latDir e true).1 (legOf (st.segs 5) 0).b - Uc hd (latDir e true).1 J.1.b) + (Uc hd (latDir e true).1 J.1.b - Y.lane (ftgt a e) e)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
      _ ≤ _ := by linarith
  · obtain ⟨a1, b1, c1⟩ := hw1 hk
    have lat1 : |Uc hd (latDir e true).1 (legOf (st.segs 5) 1).b - Uc hd (latDir e true).1 (legOf (st.segs 5) 0).b| ≤ Y.U - Y.m - 1 := by
      rw [Uc_lat_eq_vperp, Uc_lat_eq_vperp, ← mul_sub, abs_mul, hs1, one_mul]; exact c1
    refine ⟨by linarith, by linarith, ?_⟩
    calc |Uc hd (latDir e true).1 (legOf (st.segs 5) 1).b - Y.lane (ftgt a e) e|
        = |(Uc hd (latDir e true).1 (legOf (st.segs 5) 1).b - Uc hd (latDir e true).1 (legOf (st.segs 5) 0).b) +
            ((Uc hd (latDir e true).1 (legOf (st.segs 5) 0).b - Uc hd (latDir e true).1 J.1.b) + (Uc hd (latDir e true).1 J.1.b - Y.lane (ftgt a e) e))| := by ring_nf
      _ ≤ _ := abs_add_le _ _
      _ ≤ |Uc hd (latDir e true).1 (legOf (st.segs 5) 1).b - Uc hd (latDir e true).1 (legOf (st.segs 5) 0).b| +
            (|Uc hd (latDir e true).1 (legOf (st.segs 5) 0).b - Uc hd (latDir e true).1 J.1.b| + |Uc hd (latDir e true).1 J.1.b - Y.lane (ftgt a e) e|) := by
          linarith [abs_add_le (Uc hd (latDir e true).1 (legOf (st.segs 5) 0).b - Uc hd (latDir e true).1 J.1.b) (Uc hd (latDir e true).1 J.1.b - Y.lane (ftgt a e) e)]
      _ ≤ _ := by linarith

end BGNd

end Percolation.Literature

end

/-!
# Part 3 (The flat gait, XXI): bounds, VI — absolute windows of the trunk

The trunk of the flat gait (Grimmett, *Percolation*,
2nd ed. (1999), §7.3 pp. 171–174, case `H < L`) in absolute terms. A combinatorial lemma on the
take-off rule (`pass_bound`: a stretch whose plates past the take-off line must, from the third
plate on and before the head, have the wrong axis, overshoots the line by less than three hops)
bounds the first two stretches; the third has room before its head. Hence every trunk plate is
before `D - 2U + H` beyond the target cell's centre (`FlatInv.trunk_hi`), the trunk has at most
`8097` plates (`FlatInv.trunk_len`), and lies within `530 U` of the target lane laterally and beyond
`S + 97 U` (`FlatInv.abs_T`).

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §7.3 pp. 171–174.
-/

noncomputable section

namespace Percolation.Literature

open LatticeModels Contour
open scoped Classical

namespace BGNd

variable {d : ℕ} [NeZero d] {hd : 3 ≤ d} {Y : FlatLayout} {a : Site 2} {e : MDir} {τ : TTok d} {st : FS d}

/-! ## Cell constants -/

section Cell

variable (Y : FlatLayout) (a : Site 2) (e : MDir)

omit [NeZero d] in
/-- The lateral directions' own lateral axis is `e`'s axis. [folklore] -/
theorem latDir_latDir_fst (b b' : Bool) : (latDir (latDir e b) b').1 = e.1 := by
  unfold latDir; apply Fin.ext; simp; have := e.1.isLt; omega

omit [NeZero d] in
/-- The signs of the lateral directions. [folklore] -/
theorem sgOf_eB (e : MDir) : (sgOf (eB1 e) : ℤ) = -(sgOf e : ℤ) ∧ (sgOf (eB2 e) : ℤ) = (sgOf e : ℤ) := by
  unfold eB1 eB2 sgOf latDir; cases e.2 <;> simp

omit [NeZero d] in
/-- **The take-off lanes along `e`**: `s · lane(c, e_{B1}) = s · ctr - Λ + s · cpar · Λ_J` and
`s · lane(c, e_{B2}) = s · ctr + Λ + s · cpar · Λ_J`, with `cpar ∈ {0, 1}`. [folklore] -/
theorem sLane_eB :
    (sgOf e : ℤ) * Y.lane (ftgt a e) (eB1 e) = (sgOf e : ℤ) * Y.ctr (ftgt a e) e.1 - Y.lam + (sgOf e : ℤ) * (TallLayout.cpar (ftgt a e) * Y.lamJ) ∧
      (sgOf e : ℤ) * Y.lane (ftgt a e) (eB2 e) = (sgOf e : ℤ) * Y.ctr (ftgt a e) e.1 + Y.lam + (sgOf e : ℤ) * (TallLayout.cpar (ftgt a e) * Y.lamJ) ∧
      0 ≤ TallLayout.cpar (ftgt a e) ∧ TallLayout.cpar (ftgt a e) ≤ 1 := by
  have hss : (sgOf e : ℤ) * (sgOf e : ℤ) = 1 := by rcases Int.units_eq_one_or (sgOf e) with h' | h' <;> simp [h']
  obtain ⟨h1, h2⟩ := sgOf_eB e
  unfold FlatLayout.lane FlatLayout.nu
  rw [show (latDir (eB1 e) true).1 = e.1 from latDir_latDir_fst e _ _, show (latDir (eB2 e) true).1 = e.1 from latDir_latDir_fst e _ _, h1, h2]
  refine ⟨by linear_combination (-Y.lam) * hss, by linear_combination Y.lam * hss, by unfold TallLayout.cpar; omega, by unfold TallLayout.cpar; omega⟩

omit [NeZero d] in
/-- **The trunk lane along `e`'s lateral axis**: `s · lane(c, e) = s · ctr_lat + Λ + s · cpar · Λ_J`. [folklore] -/
theorem sLane_e : (sgOf e : ℤ) * Y.lane (ftgt a e) e = (sgOf e : ℤ) * Y.ctr (ftgt a e) (latDir e true).1 + Y.lam + (sgOf e : ℤ) * (TallLayout.cpar (ftgt a e) * Y.lamJ) := by
  have hss : (sgOf e : ℤ) * (sgOf e : ℤ) = 1 := by rcases Int.units_eq_one_or (sgOf e) with h' | h' <;> simp [h']
  unfold FlatLayout.lane FlatLayout.nu
  linear_combination Y.lam * hss

omit [NeZero d] in
/-- The take-off and room predicates along `e`. [folklore] -/
theorem fpassed_iff (hd : 3 ≤ d) (e' : MDir) (b : Site d) :
    fpassed hd Y a e e' b ↔ (sgOf e : ℤ) * Y.lane (ftgt a e) e' - (sgOf e : ℤ) * Y.U ≤ upar hd (dsg e) b := by
  unfold fpassed; rw [← upar_dsg, mul_sub]

omit [NeZero d] in
/-- Room along `e`. [folklore] -/
theorem froom_e_iff (hd : 3 ≤ d) (b : Site d) : froom hd Y a e e b ↔ upar hd (dsg e) b - (sgOf e : ℤ) * Y.ctr (ftgt a e) e.1 < Y.Df - 3 * Y.U := by
  unfold froom; rw [← upar_dsg, mul_sub]

omit [NeZero d] in
/-- Room along the lateral directions. [folklore] -/
theorem froom_eB_iff (hd : 3 ≤ d) (b : Site d) :
    (froom hd Y a e (eB1 e) b ↔ (sgOf e : ℤ) * Y.ctr (ftgt a e) (latDir e true).1 - (sgOf e : ℤ) * Uc hd (latDir e true).1 b < Y.Df - 3 * Y.U) ∧
      (froom hd Y a e (eB2 e) b ↔ (sgOf e : ℤ) * Uc hd (latDir e true).1 b - (sgOf e : ℤ) * Y.ctr (ftgt a e) (latDir e true).1 < Y.Df - 3 * Y.U) := by
  obtain ⟨h1, h2⟩ := sgOf_eB e
  unfold froom
  rw [h1, h2, show (eB1 e).1 = (latDir e true).1 from rfl, show (eB2 e).1 = (latDir e true).1 from rfl]
  constructor
  · constructor <;> intro h <;> linarith
  · constructor <;> intro h <;> linarith

end Cell

/-! ## The take-off rule overshoots by less than three hops -/

omit [NeZero d] in
/-- **A stretch overshoots its take-off line by less than three hops.** With `u` the forward
coordinates of its plates (non-decreasing, by at most `δ` a hop), `ax` the kept-axis predicate
(alternating), the rule "a plate before the head, from the third on, past the line has the wrong
axis", and a first plate before the line, every plate is before `thr + 3δ`. [folklore] -/
theorem pass_bound {n : ℕ} {u : ℕ → ℤ} {ax : ℕ → Prop} {thr δ : ℤ} (hδ : 0 ≤ δ)
    (hmono : ∀ j, j + 1 < n → u j ≤ u (j + 1) ∧ u (j + 1) ≤ u j + δ) (halt : ∀ j, j + 1 < n → ax j ∨ ax (j + 1))
    (hstage : ∀ j, j + 1 < n → 2 ≤ j → thr ≤ u j → ¬ax j) (h0 : 0 < n → u 0 < thr) : ∀ j < n, u j < thr + 3 * δ := by
  -- monotonicity over ranges
  have mono' : ∀ i j, i ≤ j → j < n → u i ≤ u j ∧ u j ≤ u i + (j - i : ℕ) * δ := by
    intro i j hij hj
    induction j with
    | zero => have : i = 0 := by omega
              subst this; simp
    | succ j ih =>
      rcases Nat.eq_or_lt_of_le hij with rfl | hlt
      · simp
      · have := ih (by omega) (by omega)
        have hs := hmono j hj
        rw [show j + 1 - i = (j - i) + 1 by omega]; push_cast
        constructor <;> nlinarith [this.1, this.2, hs.1, hs.2]
  intro j hj
  by_contra hge
  push Not at hge
  -- the least passed index `i₀ ≤ j`, at least `1`
  have hex : ∃ i, i ≤ j ∧ thr ≤ u i := ⟨j, le_rfl, by linarith⟩
  classical
  let i₀ := Nat.find hex
  have hi₀ : i₀ ≤ j ∧ thr ≤ u i₀ := Nat.find_spec hex
  have hmin : ∀ i < i₀, ¬(i ≤ j ∧ thr ≤ u i) := fun i hi => Nat.find_min hex hi
  have hi₀1 : 1 ≤ i₀ := by
    by_contra h; have : i₀ = 0 := by omega
    rw [this] at hi₀; linarith [h0 (by omega), hi₀.2]
  have hprev : u (i₀ - 1) < thr := by
    by_contra h; push Not at h; exact hmin (i₀ - 1) (by omega) ⟨by omega, h⟩
  have hui₀ : u i₀ < thr + δ := by have := (hmono (i₀ - 1) (by omega)).2; rw [show i₀ - 1 + 1 = i₀ by omega] at this; linarith
  -- `j ≥ i₀ + 3`
  have hj3 : i₀ + 3 ≤ j := by
    by_contra h; push Not at h
    have := (mono' i₀ j hi₀.1 hj).2
    have hcast : ((j - i₀ : ℕ) : ℤ) ≤ 2 := by have := Nat.cast_le (α := ℤ).2 (show j - i₀ ≤ 2 by omega); simpa using this
    nlinarith
  -- plates `M`, `M + 1` with `M = max i₀ 2` are before the head, past the line: both wrong axis
  set M := max i₀ 2 with hM
  have hM1 : M + 1 + 1 < n := by omega
  have hpM : thr ≤ u M := le_trans hi₀.2 (mono' i₀ M (le_max_left _ _) (by omega)).1
  have hpM1 : thr ≤ u (M + 1) := le_trans hi₀.2 (mono' i₀ (M + 1) (by omega) (by omega)).1
  have h1 := hstage M (by omega) (le_max_right _ _) hpM
  have h2 := hstage (M + 1) hM1 (by omega) hpM1
  rcases halt M (by omega) with h | h
  · exact h1 h
  · exact h2 h

/-! ## The trunk's upper bound -/

/-- **Every plate of the trunk is before `D - 2U + H` beyond the target cell's centre** along `e`;
the first stretch before `Λ` less the lane tolerance, the second before `Λ` more. [folklore] -/
theorem FlatInv.trunk_hi (hI : FlatInv hd Y a e τ st) (hY : Y.OK) (hτ : FTAdm hd Y a e τ) :
    (∀ r ∈ st.segs 6, upar hd (dsg e) r.1.b < (sgOf e : ℤ) * Y.lane (ftgt a e) (eB1 e) - (sgOf e : ℤ) * Y.U + 3 * (Y.U + Y.H - Y.m - 1)) ∧
      (∀ r ∈ st.segs 8, upar hd (dsg e) r.1.b < (sgOf e : ℤ) * Y.lane (ftgt a e) (eB2 e) - (sgOf e : ℤ) * Y.U + 3 * (Y.U + Y.H - Y.m - 1)) ∧
      (∀ r ∈ st.segs 10, upar hd (dsg e) r.1.b < (sgOf e : ℤ) * Y.ctr (ftgt a e) e.1 + Y.Df - 2 * Y.U + Y.H) := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  obtain ⟨hSlo, hShi, -⟩ := hτ.windows
  obtain ⟨hL1, hL2, hc0, hc1⟩ := sLane_eB Y a e
  have hs : (sgOf e : ℤ) = 1 ∨ (sgOf e : ℤ) = -1 := by rcases Int.units_eq_one_or (sgOf e) with h' | h' <;> simp [h']
  have hcp : -Y.lamJ ≤ (sgOf e : ℤ) * (TallLayout.cpar (ftgt a e) * Y.lamJ) ∧ (sgOf e : ℤ) * (TallLayout.cpar (ftgt a e) * Y.lamJ) ≤ Y.lamJ := by
    have hJ : 0 ≤ Y.lamJ := by unfold FlatLayout.lamJ; positivity
    have hprod : 0 ≤ TallLayout.cpar (ftgt a e) * Y.lamJ ∧ TallLayout.cpar (ftgt a e) * Y.lamJ ≤ Y.lamJ :=
      ⟨mul_nonneg hc0 hJ, mul_le_of_le_one_left hJ hc1⟩
    rcases hs with h | h <;> rw [h] <;> constructor <;> linarith [hprod.1, hprod.2]
  have hD : Y.Df = 4096 * Y.U := rfl
  have hΛ : Y.lam = 1280 * Y.U := rfl
  have hΛJ : Y.lamJ = 256 * Y.U := rfl
  -- generic: a stretch `segs i` (`i = 6, 8`) as a diagonal leg hopped off the head `s₀` of its start
  have stretch : ∀ (i : Fin 13) (l : List (BrickRec d)) (s₀ : BrickRec d) (q : Fin 2), DiagLeg hd Y e (dsg e) none q l →
      DHop hd Y e (dsg e) none q s₀.1 (legOf l 0) →
      (∀ j, j + 1 < l.length → upar hd (dsg e) (legOf l j).b ≤ upar hd (dsg e) (legOf l (j + 1)).b ∧
        upar hd (dsg e) (legOf l (j + 1)).b ≤ upar hd (dsg e) (legOf l j).b + (Y.U + Y.H - Y.m - 1)) ∧
      (∀ p : Fin 2, ∀ j, j + 1 < l.length → (legOf l j).a = pl hd p ∨ (legOf l (j + 1)).a = pl hd p) ∧
      (0 < l.length → upar hd (dsg e) (legOf l 0).b ≤ upar hd (dsg e) s₀.1.b + (Y.U + Y.H - Y.m - 1)) := by
    intro i l s₀ q hD hD0
    refine ⟨fun j hj => ?_, fun p j hj => ?_, fun h0 => ?_⟩
    · have := hD.upar_step hj; constructor <;> linarith [this.1, this.2]
    · have ha1 := (hD.axis_sign (k := j) (by omega)).1
      have ha2 := (hD.axis_sign (k := j + 1) hj).1
      rw [qAt_succ] at ha2
      rcases eq_or_eq_oth p (qAt q j) with hp | hp
      · left; rw [ha1, hp]
      · right; rw [ha2, hp]
    · have hE := diagLeg_snoc hD hD0
      have := hE.upar_step (k := 0) (by simp; omega)
      rw [show (0 : ℕ) + 1 = 1 from rfl, show (1 : ℕ) = 0 + 1 from rfl, legOf_append_singleton_succ, legOf_snoc_zero] at this
      linarith [this.2]
  -- the first stretch
  have hT1 : ∀ r ∈ st.segs 6, upar hd (dsg e) r.1.b < (sgOf e : ℤ) * Y.lane (ftgt a e) (eB1 e) - (sgOf e : ℤ) * Y.U + 3 * (Y.U + Y.H - Y.m - 1) := by
    intro r hr
    have h6 : st.segs 6 ≠ [] := List.ne_nil_of_mem hr
    have hK : SegOK hd Y e τ (eJOf hd Y a e τ st) 6 (st.segs 6) (st.segs (startOf 6)) := hI.segOK 6
    simp only [SegOK, startOf, Fin.isValue, Matrix.cons_val] at hK
    obtain ⟨T₀, hT₀, hD, hD0⟩ := hK h6
    simp only [Option.mem_def] at hT₀
    obtain ⟨mono, alt, start⟩ := stretch 6 _ T₀ _ hD hD0
    obtain ⟨-, hT0hi, -⟩ := hI.abs_GT hY hτ T₀ (List.mem_of_mem_head? hT₀)
    obtain ⟨k, hk, hkr⟩ := exists_legOf_of_mem hr
    rw [← hkr]
    have hp1 : p1 e = 1 := by unfold p1 keepIdx; rw [(flipIdx_eB e).1]; rfl
    refine pass_bound (u := fun j => upar hd (dsg e) (legOf (st.segs 6) j).b) (ax := fun j => (legOf (st.segs 6) j).a = pl hd (p1 e))
      (by linarith) mono (alt (p1 e)) (fun j hj hj2 hp => hI.T1_stage hj hj2 ((fpassed_iff Y a e hd _ _).2 hp)) (fun h0 => ?_) k hk
    have := start h0
    rcases hs with h | h <;> rw [h] at hcp hL1 hShi ⊢ <;> linarith [hL1, hcp.1, hcp.2, hShi, hT0hi]
  -- the second stretch
  have hT2 : ∀ r ∈ st.segs 8, upar hd (dsg e) r.1.b < (sgOf e : ℤ) * Y.lane (ftgt a e) (eB2 e) - (sgOf e : ℤ) * Y.U + 3 * (Y.U + Y.H - Y.m - 1) := by
    intro r hr
    have h8 : st.segs 8 ≠ [] := List.ne_nil_of_mem hr
    have hK : SegOK hd Y e τ (eJOf hd Y a e τ st) 8 (st.segs 8) (st.segs (startOf 8)) := hI.segOK 8
    simp only [SegOK, startOf, Fin.isValue, Matrix.cons_val] at hK
    obtain ⟨r6, hr6, q, hD, hD0⟩ := hK h8
    simp only [Option.mem_def] at hr6
    obtain ⟨mono, alt, start⟩ := stretch 8 _ r6 _ hD hD0
    have hr6hi := hT1 r6 (List.mem_of_mem_head? hr6)
    obtain ⟨k, hk, hkr⟩ := exists_legOf_of_mem hr
    rw [← hkr]
    refine pass_bound (u := fun j => upar hd (dsg e) (legOf (st.segs 8) j).b) (ax := fun j => (legOf (st.segs 8) j).a = pl hd (p2 e))
      (by linarith) mono (alt (p2 e)) (fun j hj hj2 hp => hI.T2_stage hj hj2 ((fpassed_iff Y a e hd _ _).2 hp)) (fun h0 => ?_) k hk
    have := start h0
    have hH8 : 8 * ((Y.H : ℤ) + 1) ≤ Y.U := hflat
    rcases hs with h | h <;> rw [h] at hcp hr6hi hL1 hL2 ⊢ <;> linarith [hL1, hL2, hcp.1, hcp.2, hr6hi]
  refine ⟨hT1, hT2, fun r hr => ?_⟩
  -- the third stretch: room before the head
  have h10 : st.segs 10 ≠ [] := List.ne_nil_of_mem hr
  have hK : SegOK hd Y e τ (eJOf hd Y a e τ st) 10 (st.segs 10) (st.segs (startOf 10)) := hI.segOK 10
  simp only [SegOK, startOf, Fin.isValue, Matrix.cons_val] at hK
  obtain ⟨r8, hr8, q, hD, hD0⟩ := hK h10
  simp only [Option.mem_def] at hr8
  obtain ⟨mono, -, start⟩ := stretch 10 _ r8 _ hD hD0
  have hr8hi := hT2 r8 (List.mem_of_mem_head? hr8)
  obtain ⟨k, hk, hkr⟩ := exists_legOf_of_mem hr
  rw [← hkr]
  have hH8 : 8 * ((Y.H : ℤ) + 1) ≤ Y.U := hflat
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · have := start hk
    rcases hs with h | h <;> rw [h] at hcp hr8hi hL2 ⊢ <;> linarith [hL2, hcp.1, hcp.2, hr8hi]
  · by_cases hlast : k + 1 < (st.segs 10).length
    · have := (froom_e_iff Y a e hd _).1 (hI.T3_stage hlast); linarith
    · have hroom := (froom_e_iff Y a e hd _).1 (hI.T3_stage (j := k - 1) (by omega))
      have := (mono (k - 1) (by omega)).2
      rw [show k - 1 + 1 = k by omega] at this
      linarith

/-! ## The trunk's length and absolute window -/

/-- **The trunk has at most `8097` plates.** [cite: GrimmettPercolation1999, §7.3 p. 174 (the bound `R`)] -/
theorem FlatInv.trunk_len (hI : FlatInv hd Y a e τ st) (hY : Y.OK) (hτ : FTAdm hd Y a e τ) :
    (st.segs 10 ++ st.segs 8 ++ st.segs 6).length ≤ 8097 := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  by_cases h6 : st.segs 6 = []
  · have h8 : st.segs 8 = [] := by
      by_contra h; have := hI.order 8 6 (by decide) h; rw [h6] at this; simp [complete'] at this
    have h10 : st.segs 10 = [] := by
      by_contra h; have := hI.order 10 6 (by decide) h; rw [h6] at this; simp [complete'] at this
    rw [h6, h8, h10]; simp
  obtain ⟨hc5, T₀, hT₀⟩ := hI.head_of_later (i := 6) (j := 5) (by decide) h6
  obtain ⟨hT0lo, -, -⟩ := hI.abs_GT hY hτ T₀ (List.mem_of_mem_head? hT₀)
  obtain ⟨hSlo, -, -⟩ := hτ.windows
  obtain ⟨h1, h2, h3⟩ := hI.trunk_hi hY hτ
  obtain ⟨hL1, hL2, hc0, hc1⟩ := sLane_eB Y a e
  set l := st.segs 10 ++ st.segs 8 ++ st.segs 6 with hl
  set n := l.length with hn
  have hnpos : 0 < n := by rw [hn, hl]; simp; right; right; exact List.length_pos_of_ne_nil h6
  -- the last plate of the trunk
  have hmem : recOf l (n - 1) ∈ l := recOf_mem (by omega)
  obtain ⟨hlo, -, -⟩ := hI.win_T hY hT₀ (j := n) (by rw [List.length_append, List.length_singleton, ← hl]; omega)
  have hidx : legOf (st.segs 10 ++ st.segs 8 ++ st.segs 6 ++ [T₀]) n = (recOf l (n - 1)).1 := by
    rw [← hl, show n = (n - 1) + 1 by omega, legOf_append_singleton_succ]; rfl
  rw [hidx] at hlo
  -- it is before `D - 2U + H` beyond the centre
  have hs : (sgOf e : ℤ) = 1 ∨ (sgOf e : ℤ) = -1 := by rcases Int.units_eq_one_or (sgOf e) with h' | h' <;> simp [h']
  have hJ : 0 ≤ Y.lamJ := by unfold FlatLayout.lamJ; positivity
  have hprod : 0 ≤ TallLayout.cpar (ftgt a e) * Y.lamJ ∧ TallLayout.cpar (ftgt a e) * Y.lamJ ≤ Y.lamJ := ⟨mul_nonneg hc0 hJ, mul_le_of_le_one_left hJ hc1⟩
  have hD : Y.Df = 4096 * Y.U := rfl
  have hΛ : Y.lam = 1280 * Y.U := rfl
  have hΛJ : Y.lamJ = 256 * Y.U := rfl
  have hhi : upar hd (dsg e) (recOf l (n - 1)).1.b < (sgOf e : ℤ) * Y.ctr (ftgt a e) e.1 + Y.Df - 2 * Y.U + Y.H := by
    rw [hl] at hmem
    simp only [List.mem_append] at hmem
    rcases hmem with (hm | hm) | hm
    · exact h3 _ hm
    · have := h2 _ hm
      rcases hs with h | h <;> rw [h] at hL2 this ⊢ <;> linarith [hprod.1, hprod.2]
    · have := h1 _ hm
      rcases hs with h | h <;> rw [h] at hL1 this ⊢ <;> linarith [hprod.1, hprod.2]
  -- so `n (U + m + 1) < 2 D + H - 95 U`
  by_contra hlen
  push Not at hlen
  have hcast : (8098 : ℤ) ≤ n := by exact_mod_cast hlen
  have hnU : 8098 * (Y.U + Y.m + 1) ≤ (n : ℤ) * (Y.U + Y.m + 1) := mul_le_mul_of_nonneg_right hcast (by linarith)
  have hH8 : 8 * ((Y.H : ℤ) + 1) ≤ Y.U := hflat
  linarith

/-- **The trunk's plates**: beyond `S + 96 U` along `e`, before `D - 2U + H` beyond the centre,
within `530 U` of the target lane laterally. [folklore] -/
theorem FlatInv.abs_T (hI : FlatInv hd Y a e τ st) (hY : Y.OK) (hτ : FTAdm hd Y a e τ) :
    ∀ r ∈ st.segs 10 ++ st.segs 8 ++ st.segs 6,
      upar hd (dsg e) τ.pos + 96 * Y.U ≤ upar hd (dsg e) r.1.b ∧
      upar hd (dsg e) r.1.b < (sgOf e : ℤ) * Y.ctr (ftgt a e) e.1 + Y.Df - 2 * Y.U + Y.H ∧
      |Uc hd (latDir e true).1 r.1.b - Y.lane (ftgt a e) e| ≤ 530 * Y.U := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  intro r hr
  have h6 : st.segs 6 ≠ [] := by
    intro h6
    have h8 : st.segs 8 = [] := by
      by_contra h; have := hI.order 8 6 (by decide) h; rw [h6] at this; simp [complete'] at this
    have h10 : st.segs 10 = [] := by
      by_contra h; have := hI.order 10 6 (by decide) h; rw [h6] at this; simp [complete'] at this
    rw [h6, h8, h10] at hr; simp at hr
  obtain ⟨hc5, T₀, hT₀⟩ := hI.head_of_later (i := 6) (j := 5) (by decide) h6
  obtain ⟨hT0lo, -, hT0lat⟩ := hI.abs_GT hY hτ T₀ (List.mem_of_mem_head? hT₀)
  obtain ⟨h1, h2, h3⟩ := hI.trunk_hi hY hτ
  obtain ⟨hL1, hL2, hc0, hc1⟩ := sLane_eB Y a e
  have hlen := hI.trunk_len hY hτ
  obtain ⟨k, hk, hkr⟩ := exists_recOf_of_mem hr
  have hj : k + 1 < (st.segs 10 ++ st.segs 8 ++ st.segs 6 ++ [T₀]).length := by rw [List.length_append, List.length_singleton]; omega
  obtain ⟨hlo, -, hlat⟩ := hI.win_T hY hT₀ hj
  have hidx : legOf (st.segs 10 ++ st.segs 8 ++ st.segs 6 ++ [T₀]) (k + 1) = r.1 := by
    rw [legOf_append_singleton_succ]; unfold legOf; rw [hkr]
  rw [hidx] at hlo hlat
  have hs : (sgOf e : ℤ) = 1 ∨ (sgOf e : ℤ) = -1 := by rcases Int.units_eq_one_or (sgOf e) with h' | h' <;> simp [h']
  have hs1 : |(sgOf e : ℤ)| = 1 := by rcases hs with h' | h' <;> simp [h']
  have hJ : 0 ≤ Y.lamJ := by unfold FlatLayout.lamJ; positivity
  have hprod : 0 ≤ TallLayout.cpar (ftgt a e) * Y.lamJ ∧ TallLayout.cpar (ftgt a e) * Y.lamJ ≤ Y.lamJ := ⟨mul_nonneg hc0 hJ, mul_le_of_le_one_left hJ hc1⟩
  have hD : Y.Df = 4096 * Y.U := rfl
  have hΛ : Y.lam = 1280 * Y.U := rfl
  have hΛJ : Y.lamJ = 256 * Y.U := rfl
  refine ⟨by push_cast at hlo; nlinarith [hlo, hT0lo, hm0, hU], ?_, ?_⟩
  · simp only [List.mem_append] at hr
    rcases hr with (hm | hm) | hm
    · exact h3 _ hm
    · have := h2 _ hm
      rcases hs with h | h <;> rw [h] at hL2 this ⊢ <;> linarith [hprod.1, hprod.2]
    · have := h1 _ hm
      rcases hs with h | h <;> rw [h] at hL1 this ⊢ <;> linarith [hprod.1, hprod.2]
  · have hk2 : (k : ℤ) + 1 ≤ 8097 := by
      have : k + 1 ≤ 8097 := by omega
      exact_mod_cast this
    have hH2 : 0 ≤ (Y.H : ℤ) - 2 * Y.m - 2 := by linarith
    have hlat' : |vperp hd (dsg e) r.1.b - vperp hd (dsg e) T₀.1.b| ≤ 4049 * ((Y.H : ℤ) - 2 * Y.m - 2) + (Y.U - Y.m - 1) := by
      push_cast at hlat; nlinarith
    have hlatU : |Uc hd (latDir e true).1 r.1.b - Uc hd (latDir e true).1 T₀.1.b| ≤ 4049 * ((Y.H : ℤ) - 2 * Y.m - 2) + (Y.U - Y.m - 1) := by
      rw [Uc_lat_eq_vperp, Uc_lat_eq_vperp, ← mul_sub, abs_mul, hs1, one_mul]; exact hlat'
    have hH8 : 8 * ((Y.H : ℤ) + 1) ≤ Y.U := hflat
    calc |Uc hd (latDir e true).1 r.1.b - Y.lane (ftgt a e) e|
        = |(Uc hd (latDir e true).1 r.1.b - Uc hd (latDir e true).1 T₀.1.b) + (Uc hd (latDir e true).1 T₀.1.b - Y.lane (ftgt a e) e)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
      _ ≤ _ := by linarith

end BGNd

end Percolation.Literature

end

/-!
# Part 4 (The flat gait, XXII): bounds, VII — forks, branches, the plate count, the quantitative separation

The last absolute windows of the flat gait (Grimmett,
*Percolation*, 2nd ed. (1999), §7.3 pp. 171–174, case `H < L`): the forks (`FlatInv.abs_G1`,
`FlatInv.abs_G2`), the branches with their lengths (`FlatInv.abs_B1`, `FlatInv.abs_B2`); the total number of plates is below the budget `R = 2¹⁵`
(`FlatInv.all_length_lt`); and the branches are far beyond the entry side in the forward diagonal
coordinate, which discharges the quantitative input of the disjointness analysis
(`FlatInv.psiFar`, hence `FlatInv.pairwise'`).

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §7.3 pp. 171–174.
-/

noncomputable section

namespace Percolation.Literature

open LatticeModels Contour
open scoped Classical

namespace BGNd

variable {d : ℕ} [NeZero d] {hd : 3 ≤ d} {Y : FlatLayout} {a : Site 2} {e : MDir} {τ : TTok d} {st : FS d}

/-! ## The forks -/

/-- **The stretches' heads at the forks**: past their take-off lines, by less than three hops. [folklore] -/
theorem FlatInv.abs_r68 (hI : FlatInv hd Y a e τ st) (hY : Y.OK) (hτ : FTAdm hd Y a e τ) :
    (∀ r6, (st.segs 6).head? = some r6 → st.segs 7 ≠ [] →
        (sgOf e : ℤ) * Y.lane (ftgt a e) (eB1 e) - (sgOf e : ℤ) * Y.U ≤ upar hd (dsg e) r6.1.b ∧
        upar hd (dsg e) r6.1.b < (sgOf e : ℤ) * Y.lane (ftgt a e) (eB1 e) - (sgOf e : ℤ) * Y.U + 3 * (Y.U + Y.H - Y.m - 1) ∧
        |Uc hd (latDir e true).1 r6.1.b - Y.lane (ftgt a e) e| ≤ 530 * Y.U) ∧
      (∀ r8, (st.segs 8).head? = some r8 → st.segs 9 ≠ [] →
        (sgOf e : ℤ) * Y.lane (ftgt a e) (eB2 e) - (sgOf e : ℤ) * Y.U ≤ upar hd (dsg e) r8.1.b ∧
        upar hd (dsg e) r8.1.b < (sgOf e : ℤ) * Y.lane (ftgt a e) (eB2 e) - (sgOf e : ℤ) * Y.U + 3 * (Y.U + Y.H - Y.m - 1) ∧
        |Uc hd (latDir e true).1 r8.1.b - Y.lane (ftgt a e) e| ≤ 530 * Y.U) := by
  obtain ⟨h1, h2, -⟩ := hI.trunk_hi hY hτ
  obtain ⟨hh6, hh8, -⟩ := T_heads hd Y a e τ st
  constructor
  · intro r6 hr6 h7
    obtain ⟨hc6, -⟩ := hI.head_of_later (i := 7) (j := 6) (by decide) h7
    have hmem : r6 ∈ st.segs 6 := List.mem_of_mem_head? hr6
    obtain ⟨-, hpass⟩ := hh6 hc6
    rw [legOf_last_of_head hr6, fpassed_iff] at hpass
    obtain ⟨-, -, hlat⟩ := hI.abs_T hY hτ r6 (by simp [hmem])
    exact ⟨hpass, h1 r6 hmem, hlat⟩
  · intro r8 hr8 h9
    obtain ⟨hc8, -⟩ := hI.head_of_later (i := 9) (j := 8) (by decide) h9
    have hmem : r8 ∈ st.segs 8 := List.mem_of_mem_head? hr8
    obtain ⟨-, hpass⟩ := hh8 hc8
    rw [legOf_last_of_head hr8, fpassed_iff] at hpass
    obtain ⟨-, -, hlat⟩ := hI.abs_T hY hτ r8 (by simp [hmem])
    exact ⟨hpass, h2 r8 hmem, hlat⟩

/-- **The first fork's plates**: along `e` within `[-2U, 4U]` of the first take-off line,
laterally within `534 U` of the target lane. [folklore] -/
theorem FlatInv.abs_G1 (hI : FlatInv hd Y a e τ st) (hY : Y.OK) (hτ : FTAdm hd Y a e τ) :
    ∀ r ∈ st.segs 7, (sgOf e : ℤ) * Y.lane (ftgt a e) (eB1 e) - (sgOf e : ℤ) * Y.U - 2 * Y.U ≤ upar hd (dsg e) r.1.b ∧
      upar hd (dsg e) r.1.b ≤ (sgOf e : ℤ) * Y.lane (ftgt a e) (eB1 e) - (sgOf e : ℤ) * Y.U + 4 * Y.U ∧
      |Uc hd (latDir e true).1 r.1.b - Y.lane (ftgt a e) e| ≤ 534 * Y.U := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  intro r hr
  have h7 : st.segs 7 ≠ [] := List.ne_nil_of_mem hr
  obtain ⟨-, r6, hr6⟩ := hI.head_of_later (i := 7) (j := 6) (by decide) h7
  obtain ⟨h6lo, h6hi, h6lat⟩ := (hI.abs_r68 hY hτ).1 r6 hr6 h7
  obtain ⟨hw0, hw1⟩ := hI.win_G1 hY hr6
  obtain ⟨_, _, _, _, hT⟩ := hI.frame_fork.1 h7
  have hlen := hT.len
  obtain ⟨k, hk, hkr⟩ := exists_legOf_of_mem hr
  rw [← hkr]
  have hk2 : k < 2 := by omega
  obtain ⟨a0, b0, c0⟩ := hw0 (by omega)
  have hs1 : |(sgOf e : ℤ)| = 1 := by rcases Int.units_eq_one_or (sgOf e) with h' | h' <;> simp [h']
  have hH8 : 8 * ((Y.H : ℤ) + 1) ≤ Y.U := hflat
  have lat0 : |Uc hd (latDir e true).1 (legOf (st.segs 7) 0).b - Uc hd (latDir e true).1 r6.1.b| ≤ (Y.H : ℤ) + 1 + Y.Lp := by
    rw [Uc_lat_eq_vperp, Uc_lat_eq_vperp, ← mul_sub, abs_mul, hs1, one_mul]; exact c0
  rw [abs_le] at lat0 h6lat ⊢
  interval_cases k
  · exact ⟨by linarith, by linarith, by constructor <;> linarith⟩
  · obtain ⟨a1, b1, c1⟩ := hw1 hk
    have lat1 : |Uc hd (latDir e true).1 (legOf (st.segs 7) 1).b - Uc hd (latDir e true).1 (legOf (st.segs 7) 0).b| ≤ Y.U + Y.H - Y.m - 1 := by
      rw [Uc_lat_eq_vperp, Uc_lat_eq_vperp, ← mul_sub, abs_mul, hs1, one_mul]; exact c1
    rw [abs_le] at lat1
    exact ⟨by linarith, by linarith, by constructor <;> linarith⟩

/-- **The second fork's plates.** [folklore] -/
theorem FlatInv.abs_G2 (hI : FlatInv hd Y a e τ st) (hY : Y.OK) (hτ : FTAdm hd Y a e τ) :
    ∀ r ∈ st.segs 9, (sgOf e : ℤ) * Y.lane (ftgt a e) (eB2 e) - (sgOf e : ℤ) * Y.U - 2 * Y.U ≤ upar hd (dsg e) r.1.b ∧
      upar hd (dsg e) r.1.b ≤ (sgOf e : ℤ) * Y.lane (ftgt a e) (eB2 e) - (sgOf e : ℤ) * Y.U + 4 * Y.U ∧
      |Uc hd (latDir e true).1 r.1.b - Y.lane (ftgt a e) e| ≤ 534 * Y.U := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  intro r hr
  have h9 : st.segs 9 ≠ [] := List.ne_nil_of_mem hr
  obtain ⟨-, r8, hr8⟩ := hI.head_of_later (i := 9) (j := 8) (by decide) h9
  obtain ⟨h8lo, h8hi, h8lat⟩ := (hI.abs_r68 hY hτ).2 r8 hr8 h9
  obtain ⟨hw0, hw1⟩ := hI.win_G2 hY hr8
  obtain ⟨_, _, _, _, hT⟩ := hI.frame_fork.2 h9
  have hlen := hT.len
  obtain ⟨k, hk, hkr⟩ := exists_legOf_of_mem hr
  rw [← hkr]
  have hk2 : k < 2 := by omega
  obtain ⟨a0, b0, c0⟩ := hw0 (by omega)
  have hs1 : |(sgOf e : ℤ)| = 1 := by rcases Int.units_eq_one_or (sgOf e) with h' | h' <;> simp [h']
  have hH8 : 8 * ((Y.H : ℤ) + 1) ≤ Y.U := hflat
  have lat0 : |Uc hd (latDir e true).1 (legOf (st.segs 9) 0).b - Uc hd (latDir e true).1 r8.1.b| ≤ (Y.H : ℤ) + 1 + Y.Lp := by
    rw [Uc_lat_eq_vperp, Uc_lat_eq_vperp, ← mul_sub, abs_mul, hs1, one_mul]; exact c0
  rw [abs_le] at lat0 h8lat ⊢
  interval_cases k
  · exact ⟨by linarith, by linarith, by constructor <;> linarith⟩
  · obtain ⟨a1, b1, c1⟩ := hw1 hk
    have lat1 : |Uc hd (latDir e true).1 (legOf (st.segs 9) 1).b - Uc hd (latDir e true).1 (legOf (st.segs 9) 0).b| ≤ Y.U + Y.H - Y.m - 1 := by
      rw [Uc_lat_eq_vperp, Uc_lat_eq_vperp, ← mul_sub, abs_mul, hs1, one_mul]; exact c1
    rw [abs_le] at lat1
    exact ⟨by linarith, by linarith, by constructor <;> linarith⟩

/-! ## The branches -/

/-- Consecutive plates of the first branch: the lateral coordinate decreases by at most `U + H - m - 1`. [folklore] -/
theorem FlatInv.B1_step (hI : FlatInv hd Y a e τ st) {j : ℕ} (hj : j + 1 < (st.segs 11).length) :
    vperp hd (dsg e) (legOf (st.segs 11) j).b - vperp hd (dsg e) (legOf (st.segs 11) (j + 1)).b ≤ Y.U + Y.H - Y.m - 1 := by
  obtain ⟨γ, -, -, hBE⟩ := hI.frame_branch.1 (List.ne_nil_of_length_pos (by omega))
  obtain ⟨⟨hflip1, hkeep1⟩, -⟩ := flip_keep_B e
  change dsg (eB1 e) 0 = -dsg e 0 at hflip1
  have conv := fun b => upar_vperp_flip0 hd (σ := dsg e) (σ' := dsg (eB1 e)) hflip1 hkeep1 b
  have := hBE.upar_step (k := j + 1) (by simp; omega)
  rw [legOf_append_singleton_succ, legOf_append_singleton_succ, (conv _).1, (conv _).1] at this
  linarith [this.2]

/-- Consecutive plates of the second branch: the lateral coordinate increases by at most `U + H - m - 1`. [folklore] -/
theorem FlatInv.B2_step (hI : FlatInv hd Y a e τ st) {j : ℕ} (hj : j + 1 < (st.segs 12).length) :
    vperp hd (dsg e) (legOf (st.segs 12) (j + 1)).b - vperp hd (dsg e) (legOf (st.segs 12) j).b ≤ Y.U + Y.H - Y.m - 1 := by
  obtain ⟨γ, -, -, hBE⟩ := hI.frame_branch.2 (List.ne_nil_of_length_pos (by omega))
  obtain ⟨-, hflip2, hkeep2⟩ := flip_keep_B e
  change dsg (eB2 e) 1 = -dsg e 1 at hflip2
  have conv := fun b => upar_vperp_flip1 hd (σ := dsg e) (σ' := dsg (eB2 e)) hkeep2 hflip2 b
  have := hBE.upar_step (k := j + 1) (by simp; omega)
  rw [legOf_append_singleton_succ, legOf_append_singleton_succ, (conv _).1, (conv _).1] at this
  linarith [this.2]

/-- **The first branch**: at most `6165` plates; laterally (read along `e`) strictly decreasing
from the first fork's hop and above `ctr_lat · s - D + 2U - H + m + 1`; along `e` within `[-389 U, 391 U]` of
the first take-off line. [folklore] -/
theorem FlatInv.abs_B1 (hI : FlatInv hd Y a e τ st) (hY : Y.OK) (hτ : FTAdm hd Y a e τ) :
    (st.segs 11).length ≤ 6165 ∧
      ∀ r ∈ st.segs 11,
        (sgOf e : ℤ) * Y.ctr (ftgt a e) (latDir e true).1 - Y.Df + 2 * Y.U - Y.H + Y.m + 1 < vperp hd (dsg e) r.1.b ∧
        vperp hd (dsg e) r.1.b + Y.U ≤ (sgOf e : ℤ) * Y.lane (ftgt a e) e + 534 * Y.U ∧
        (sgOf e : ℤ) * Y.lane (ftgt a e) (eB1 e) - (sgOf e : ℤ) * Y.U - 389 * Y.U ≤ upar hd (dsg e) r.1.b ∧
        upar hd (dsg e) r.1.b ≤ (sgOf e : ℤ) * Y.lane (ftgt a e) (eB1 e) - (sgOf e : ℤ) * Y.U + 391 * Y.U := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  by_cases h11 : st.segs 11 = []
  · rw [h11]; exact ⟨by simp, fun r hr => absurd hr (by simp)⟩
  obtain ⟨γ, hγ, hlen7, -⟩ := hI.frame_branch.1 h11
  obtain ⟨hγlo, hγhi, hγlat⟩ := hI.abs_G1 hY hτ γ (List.mem_of_mem_head? hγ)
  have hs : (sgOf e : ℤ) = 1 ∨ (sgOf e : ℤ) = -1 := by rcases Int.units_eq_one_or (sgOf e) with h' | h' <;> simp [h']
  have hs1 : |(sgOf e : ℤ)| = 1 := by rcases hs with h' | h' <;> simp [h']
  have hss : (sgOf e : ℤ) * (sgOf e : ℤ) = 1 := by rcases hs with h' | h' <;> rw [h'] <;> norm_num
  have hsL := sLane_e Y a e
  obtain ⟨hL1, -, hc0, hc1⟩ := sLane_eB Y a e
  have hJ : 0 ≤ Y.lamJ := by unfold FlatLayout.lamJ; positivity
  have hprod : 0 ≤ TallLayout.cpar (ftgt a e) * Y.lamJ ∧ TallLayout.cpar (ftgt a e) * Y.lamJ ≤ Y.lamJ := ⟨mul_nonneg hc0 hJ, mul_le_of_le_one_left hJ hc1⟩
  have hD : Y.Df = 4096 * Y.U := rfl
  have hΛ : Y.lam = 1280 * Y.U := rfl
  have hΛJ : Y.lamJ = 256 * Y.U := rfl
  have hH8 : 8 * ((Y.H : ℤ) + 1) ≤ Y.U := hflat
  -- `γ` laterally: `vperp(γ) ≤ s · lane + 534 U`
  have hγv : vperp hd (dsg e) γ.1.b ≤ (sgOf e : ℤ) * Y.lane (ftgt a e) e + 534 * Y.U ∧
      (sgOf e : ℤ) * Y.lane (ftgt a e) e - 534 * Y.U ≤ vperp hd (dsg e) γ.1.b := by
    have e1 : vperp hd (dsg e) γ.1.b - (sgOf e : ℤ) * Y.lane (ftgt a e) e = (sgOf e : ℤ) * (Uc hd (latDir e true).1 γ.1.b - Y.lane (ftgt a e) e) := by
      rw [Uc_lat_eq_vperp]; linear_combination (-(vperp hd (dsg e) γ.1.b)) * hss
    have : |vperp hd (dsg e) γ.1.b - (sgOf e : ℤ) * Y.lane (ftgt a e) e| ≤ 534 * Y.U := by rw [e1, abs_mul, hs1, one_mul]; exact hγlat
    rw [abs_le] at this; constructor <;> linarith
  -- every plate: decreasing laterally, room before the head
  have plate : ∀ k, (hk : k < (st.segs 11).length) →
      ((k : ℤ) + 1) * (Y.U + Y.m + 1) ≤ vperp hd (dsg e) γ.1.b - vperp hd (dsg e) (legOf (st.segs 11) k).b ∧
      (sgOf e : ℤ) * Y.ctr (ftgt a e) (latDir e true).1 - Y.Df + 2 * Y.U - Y.H + Y.m + 1 < vperp hd (dsg e) (legOf (st.segs 11) k).b ∧
      2 * |upar hd (dsg e) (legOf (st.segs 11) k).b - upar hd (dsg e) γ.1.b| ≤ ((k : ℤ) + 1) * ((Y.H : ℤ) - 2 * Y.m - 2) + 2 * (Y.U - Y.m - 1) := by
    intro k hk
    obtain ⟨hlo, hhi, hu⟩ := hI.win_B1 hY hγ hk
    refine ⟨hlo, ?_, hu⟩
    have room : ∀ j, (hj : j + 1 < (st.segs 11).length) → (sgOf e : ℤ) * Y.ctr (ftgt a e) (latDir e true).1 - Y.Df + 3 * Y.U < vperp hd (dsg e) (legOf (st.segs 11) j).b := by
      intro j hj
      have := ((froom_eB_iff Y a e hd _).1).1 (hI.B1_stage hj)
      rw [Uc_lat_eq_vperp, ← mul_assoc, hss, one_mul] at this; linarith
    by_cases hlast : k + 1 < (st.segs 11).length
    · linarith [room k hlast]
    · rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · push_cast at hhi; rcases hs with h | h <;> rw [h] at hsL hγv ⊢ <;> linarith [hγv.2, hprod.1, hprod.2]
      · have hr := room (k - 1) (by omega)
        obtain ⟨hlo', -, -⟩ := hI.win_B1 hY hγ (k := k - 1) (by omega)
        have hstep := hI.B1_step (j := k - 1) (by omega)
        rw [show k - 1 + 1 = k by omega] at hstep
        linarith
  have hlen : (st.segs 11).length ≤ 6165 := by
    by_contra hlen
    push Not at hlen
    have hk : 6165 < (st.segs 11).length := hlen
    obtain ⟨hlo, hroom, -⟩ := plate 6165 hk
    push_cast at hlo
    have h6 : 6166 * Y.U ≤ (6165 + 1) * (Y.U + (Y.m : ℤ) + 1) := by linarith
    rcases hs with h | h <;> rw [h] at hsL hγv hroom <;> linarith [hγv.1, hprod.1, hprod.2, hroom, hlo]
  refine ⟨hlen, fun r hr => ?_⟩
  obtain ⟨k, hk, hkr⟩ := exists_legOf_of_mem hr
  rw [← hkr]
  obtain ⟨hlo, hroom, hu⟩ := plate k hk
  have hk2 : (k : ℤ) + 1 ≤ 6165 := by have : k + 1 ≤ 6165 := by omega
                                      exact_mod_cast this
  have hH2 : 0 ≤ (Y.H : ℤ) - 2 * Y.m - 2 := by linarith
  have hkk := mul_le_mul_of_nonneg_right hk2 hH2
  have hu' : |upar hd (dsg e) (legOf (st.segs 11) k).b - upar hd (dsg e) γ.1.b| ≤ 3083 * ((Y.H : ℤ) - 2 * Y.m - 2) + (Y.U - Y.m - 1) := by linarith
  rw [abs_le] at hu'
  have hk0 : (0 : ℤ) ≤ k := by positivity
  have hkU : Y.U ≤ ((k : ℤ) + 1) * (Y.U + Y.m + 1) := by
    calc Y.U = 1 * Y.U := by ring
      _ ≤ ((k : ℤ) + 1) * (Y.U + Y.m + 1) := mul_le_mul (by linarith) (by linarith) hU.le (by linarith)
  refine ⟨hroom, by linarith [hγv.1, hlo], by linarith, by linarith⟩

/-- **The second branch**: at most `3605` plates; laterally increasing from the second fork's hop
and below `ctr_lat · s + D - 2U + H - m - 1`; along `e` within `[-230 U, 232 U]` of the second take-off line. [folklore] -/
theorem FlatInv.abs_B2 (hI : FlatInv hd Y a e τ st) (hY : Y.OK) (hτ : FTAdm hd Y a e τ) :
    (st.segs 12).length ≤ 3605 ∧
      ∀ r ∈ st.segs 12,
        vperp hd (dsg e) r.1.b < (sgOf e : ℤ) * Y.ctr (ftgt a e) (latDir e true).1 + Y.Df - 2 * Y.U + Y.H - Y.m - 1 ∧
        (sgOf e : ℤ) * Y.lane (ftgt a e) e - 534 * Y.U ≤ vperp hd (dsg e) r.1.b - Y.U ∧
        (sgOf e : ℤ) * Y.lane (ftgt a e) (eB2 e) - (sgOf e : ℤ) * Y.U - 230 * Y.U ≤ upar hd (dsg e) r.1.b ∧
        upar hd (dsg e) r.1.b ≤ (sgOf e : ℤ) * Y.lane (ftgt a e) (eB2 e) - (sgOf e : ℤ) * Y.U + 232 * Y.U := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  by_cases h12 : st.segs 12 = []
  · rw [h12]; exact ⟨by simp, fun r hr => absurd hr (by simp)⟩
  obtain ⟨γ, hγ, hlen9, -⟩ := hI.frame_branch.2 h12
  obtain ⟨hγlo, hγhi, hγlat⟩ := hI.abs_G2 hY hτ γ (List.mem_of_mem_head? hγ)
  have hs : (sgOf e : ℤ) = 1 ∨ (sgOf e : ℤ) = -1 := by rcases Int.units_eq_one_or (sgOf e) with h' | h' <;> simp [h']
  have hs1 : |(sgOf e : ℤ)| = 1 := by rcases hs with h' | h' <;> simp [h']
  have hss : (sgOf e : ℤ) * (sgOf e : ℤ) = 1 := by rcases hs with h' | h' <;> rw [h'] <;> norm_num
  have hsL := sLane_e Y a e
  obtain ⟨-, hL2, hc0, hc1⟩ := sLane_eB Y a e
  have hJ : 0 ≤ Y.lamJ := by unfold FlatLayout.lamJ; positivity
  have hprod : 0 ≤ TallLayout.cpar (ftgt a e) * Y.lamJ ∧ TallLayout.cpar (ftgt a e) * Y.lamJ ≤ Y.lamJ := ⟨mul_nonneg hc0 hJ, mul_le_of_le_one_left hJ hc1⟩
  have hD : Y.Df = 4096 * Y.U := rfl
  have hΛ : Y.lam = 1280 * Y.U := rfl
  have hΛJ : Y.lamJ = 256 * Y.U := rfl
  have hH8 : 8 * ((Y.H : ℤ) + 1) ≤ Y.U := hflat
  have hγv : vperp hd (dsg e) γ.1.b ≤ (sgOf e : ℤ) * Y.lane (ftgt a e) e + 534 * Y.U ∧
      (sgOf e : ℤ) * Y.lane (ftgt a e) e - 534 * Y.U ≤ vperp hd (dsg e) γ.1.b := by
    have e1 : vperp hd (dsg e) γ.1.b - (sgOf e : ℤ) * Y.lane (ftgt a e) e = (sgOf e : ℤ) * (Uc hd (latDir e true).1 γ.1.b - Y.lane (ftgt a e) e) := by
      rw [Uc_lat_eq_vperp]; linear_combination (-(vperp hd (dsg e) γ.1.b)) * hss
    have : |vperp hd (dsg e) γ.1.b - (sgOf e : ℤ) * Y.lane (ftgt a e) e| ≤ 534 * Y.U := by rw [e1, abs_mul, hs1, one_mul]; exact hγlat
    rw [abs_le] at this; constructor <;> linarith
  have plate : ∀ k, (hk : k < (st.segs 12).length) →
      ((k : ℤ) + 1) * (Y.U + Y.m + 1) ≤ vperp hd (dsg e) (legOf (st.segs 12) k).b - vperp hd (dsg e) γ.1.b ∧
      vperp hd (dsg e) (legOf (st.segs 12) k).b < (sgOf e : ℤ) * Y.ctr (ftgt a e) (latDir e true).1 + Y.Df - 2 * Y.U + Y.H - Y.m - 1 ∧
      2 * |upar hd (dsg e) (legOf (st.segs 12) k).b - upar hd (dsg e) γ.1.b| ≤ ((k : ℤ) + 1) * ((Y.H : ℤ) - 2 * Y.m - 2) + 2 * (Y.U - Y.m - 1) := by
    intro k hk
    obtain ⟨hlo, hhi, hu⟩ := hI.win_B2 hY hγ hk
    refine ⟨hlo, ?_, hu⟩
    have room : ∀ j, (hj : j + 1 < (st.segs 12).length) → vperp hd (dsg e) (legOf (st.segs 12) j).b < (sgOf e : ℤ) * Y.ctr (ftgt a e) (latDir e true).1 + Y.Df - 3 * Y.U := by
      intro j hj
      have := ((froom_eB_iff Y a e hd _).2).1 (hI.B2_stage hj)
      rw [Uc_lat_eq_vperp, ← mul_assoc, hss, one_mul] at this; linarith
    by_cases hlast : k + 1 < (st.segs 12).length
    · linarith [room k hlast]
    · rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · push_cast at hhi; rcases hs with h | h <;> rw [h] at hsL hγv ⊢ <;> linarith [hγv.1, hprod.1, hprod.2]
      · have hr := room (k - 1) (by omega)
        have hstep := hI.B2_step (j := k - 1) (by omega)
        rw [show k - 1 + 1 = k by omega] at hstep
        linarith
  have hlen : (st.segs 12).length ≤ 3605 := by
    by_contra hlen
    push Not at hlen
    have hk : 3605 < (st.segs 12).length := hlen
    obtain ⟨hlo, hroom, -⟩ := plate 3605 hk
    push_cast at hlo
    have h6 : 3606 * Y.U ≤ (3605 + 1) * (Y.U + (Y.m : ℤ) + 1) := by linarith
    rcases hs with h | h <;> rw [h] at hsL hγv hroom <;> linarith [hγv.2, hprod.1, hprod.2, hroom, hlo]
  refine ⟨hlen, fun r hr => ?_⟩
  obtain ⟨k, hk, hkr⟩ := exists_legOf_of_mem hr
  rw [← hkr]
  obtain ⟨hlo, hroom, hu⟩ := plate k hk
  have hk2 : (k : ℤ) + 1 ≤ 3605 := by have : k + 1 ≤ 3605 := by omega
                                      exact_mod_cast this
  have hH2 : 0 ≤ (Y.H : ℤ) - 2 * Y.m - 2 := by linarith
  have hkk := mul_le_mul_of_nonneg_right hk2 hH2
  have hu' : |upar hd (dsg e) (legOf (st.segs 12) k).b - upar hd (dsg e) γ.1.b| ≤ 1803 * ((Y.H : ℤ) - 2 * Y.m - 2) + (Y.U - Y.m - 1) := by linarith
  rw [abs_le] at hu'
  have hk0 : (0 : ℤ) ≤ k := by positivity
  have hkU : Y.U ≤ ((k : ℤ) + 1) * (Y.U + Y.m + 1) := by
    calc Y.U = 1 * Y.U := by ring
      _ ≤ ((k : ℤ) + 1) * (Y.U + Y.m + 1) := mul_le_mul (by linarith) (by linarith) hU.le (by linarith)
  refine ⟨hroom, by linarith [hγv.2, hlo], by linarith, by linarith⟩

/-! ## The plate count -/

omit [NeZero d] in
/-- The number of records is the sum of the segments' lengths. [folklore] -/
theorem FS.all_length (st : FS d) : st.all.length = (st.segs 0).length + (st.segs 1).length + (st.segs 2).length + (st.segs 3).length +
    (st.segs 4).length + (st.segs 5).length + (st.segs 6).length + (st.segs 7).length + (st.segs 8).length + (st.segs 9).length +
    (st.segs 10).length + (st.segs 11).length + (st.segs 12).length := by
  have h13 : List.finRange 13 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] := by decide
  unfold FS.all
  rw [h13]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append]
  omega

/-- **An attempt places fewer than `R = 2¹⁵` plates.** [cite: GrimmettPercolation1999, §7.3 p. 174 (the bound `R`)] -/
theorem FlatInv.all_length_lt (hI : FlatInv hd Y a e τ st) (hY : Y.OK) (hτ : FTAdm hd Y a e τ) : st.all.length < FlatLayout.Rmax := by
  have h0 : (st.segs 0).length ≤ 3 := by
    have hS : SegOK hd Y e τ (eJOf hd Y a e τ st) 0 (st.segs 0) (st.segs (startOf 0)) := hI.segOK 0
    simp only [SegOK, startOf, Fin.isValue, Matrix.cons_val] at hS
    by_cases hne : st.segs 0 = []
    · rw [hne]; simp
    · exact (hS hne).2.2
  have h1 := hI.riser_len_le hY hτ
  have h2 := hI.pre_len.1
  have hturn : ∀ i : Fin 13, (i = 3 ∨ i = 5 ∨ i = 7 ∨ i = 9) → (st.segs i).length ≤ 2 := by
    intro i hi
    by_cases hne : st.segs i = []
    · rw [hne]; simp
    rcases hi with rfl | rfl | rfl | rfl
    · obtain ⟨_, _, _, hT⟩ := hI.frame_turnJ hne; exact hT.len
    · obtain ⟨_, _, _, hT⟩ := hI.frame_turnT hne; exact hT.len
    · obtain ⟨_, _, _, _, hT⟩ := hI.frame_fork.1 hne; exact hT.len
    · obtain ⟨_, _, _, _, hT⟩ := hI.frame_fork.2 hne; exact hT.len
  have h3 := hturn 3 (by simp); have h5 := hturn 5 (by simp); have h7 := hturn 7 (by simp); have h9 := hturn 9 (by simp)
  have h4 := hI.J_len hY hτ
  have hT := hI.trunk_len hY hτ
  simp only [List.length_append] at hT
  have h11 := (hI.abs_B1 hY hτ).1
  have h12 := (hI.abs_B2 hY hτ).1
  rw [FS.all_length]
  unfold FlatLayout.Rmax
  omega

/-! ## The quantitative separation of the branches from the entry side -/

/-- **The branches are more than `4U` beyond the entry side** in the forward diagonal coordinate. [folklore] -/
theorem FlatInv.psiFar (hI : FlatInv hd Y a e τ st) (hY : Y.OK) (hτ : FTAdm hd Y a e τ) : PsiFar hd Y e st := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  obtain ⟨-, hShi, -⟩ := hτ.windows
  obtain ⟨hL1, hL2, hc0, hc1⟩ := sLane_eB Y a e
  have hs : (sgOf e : ℤ) = 1 ∨ (sgOf e : ℤ) = -1 := by rcases Int.units_eq_one_or (sgOf e) with h' | h' <;> simp [h']
  have hJ : 0 ≤ Y.lamJ := by unfold FlatLayout.lamJ; positivity
  have hprod : 0 ≤ TallLayout.cpar (ftgt a e) * Y.lamJ ∧ TallLayout.cpar (ftgt a e) * Y.lamJ ≤ Y.lamJ := ⟨mul_nonneg hc0 hJ, mul_le_of_le_one_left hJ hc1⟩
  have hD : Y.Df = 4096 * Y.U := rfl
  have hΛ : Y.lam = 1280 * Y.U := rfl
  have hΛJ : Y.lamJ = 256 * Y.U := rfl
  -- the entry side is before `S + 466 U`
  have hx : ∀ x : BrickRec d, (((((x ∈ st.segs 0 ∨ x ∈ st.segs 1) ∨ x ∈ st.segs 2) ∨ x ∈ st.segs 3) ∨ x ∈ st.segs 4) ∨ x ∈ st.segs 5) →
      upar hd (dsg e) x.1.b ≤ upar hd (dsg e) τ.pos + 469 * Y.U := by
    intro x hx
    rcases hx with ((((hx | hx) | hx) | hx) | hx) | hx
    · -- the lead-in: behind the riser's start, which is at most `2U + 2H` beyond the token… if the
      -- riser is empty we bound by the lead-in leg directly
      have hS : SegOK hd Y e τ (eJOf hd Y a e τ st) 0 (st.segs 0) (st.segs (startOf 0)) := hI.segOK 0
      simp only [SegOK, startOf, Fin.isValue, Matrix.cons_val] at hS
      obtain ⟨hD, hfirst, hlen3⟩ := hS (List.ne_nil_of_mem hx)
      obtain ⟨k, hk, hkr⟩ := exists_legOf_of_mem hx
      rw [← hkr]
      have hm := (hD.mono (k := 0) (k' := k) (Nat.zero_le _) hk 0).2.2
      rw [hfirst] at hm
      have hk3 : (k : ℤ) - 0 ≤ 2 := by have := Nat.cast_le (α := ℤ).2 (show k ≤ 2 by omega); simpa using this
      have hδ : 0 ≤ Y.U + Y.H - Y.m - 1 := by linarith
      have := mul_le_mul_of_nonneg_right hk3 hδ
      change upar hd (dsg e) (legOf (st.segs 0) k).b - upar hd (dsg e) τ.pos ≤ _ at hm
      simp only [Nat.cast_zero, sub_zero] at hm this
      linarith
    · obtain ⟨k, hk, hkr⟩ := exists_legOf_of_mem hx
      rw [← hkr]
      obtain ⟨-, hu, -⟩ := hI.win_riser hY hτ hk
      have hlen := hI.riser_len_le hY hτ
      have : (k : ℤ) + 1 ≤ 106 := by have := Nat.cast_le (α := ℤ).2 (show k + 1 ≤ 106 by omega); push_cast at this; exact this
      have := mul_le_mul_of_nonneg_right this hU.le
      have hH8 : 8 * ((Y.H : ℤ) + 1) ≤ Y.U := hflat
      linarith
    · exact ((hI.abs_P hY hτ).1 x hx).2.1.trans (by linarith)
    · exact (hI.abs_GJ hY hτ x hx).2.1.trans (by linarith)
    · exact ((hI.abs_J hY hτ).1 x hx).2.1.trans (by linarith)
    · exact (hI.abs_GT hY hτ x hx).2.1
  -- the branches are beyond `thr₁ - 389 U ≥ s·ctr - Λ - Λ_J - U - 389 U`
  intro y hy x hx'
  have hxx := hx x hx'
  rcases hy with hy | hy
  · obtain ⟨-, -, hlo, -⟩ := (hI.abs_B1 hY hτ).2 y hy
    rcases hs with h | h <;> rw [h] at hL1 hlo hShi <;> linarith [hprod.1, hprod.2]
  · obtain ⟨-, -, hlo, -⟩ := (hI.abs_B2 hY hτ).2 y hy
    rcases hs with h | h <;> rw [h] at hL2 hlo hShi <;> linarith [hprod.1, hprod.2]

/-- **All plates of an invariant state of an admissible attempt are pairwise disjoint.**
[cite: GrimmettPercolation1999, §7.3 pp. 172–174 (C)] -/
theorem FlatInv.pairwise' (hI : FlatInv hd Y a e τ st) (hY : Y.OK) (hτ : FTAdm hd Y a e τ) :
    st.all.Pairwise (fun r r' => PlateDisj Y.L Y.H r.1 r'.1) :=
  hI.pairwise hY (hI.psiFar hY hτ)

end BGNd

end Percolation.Literature

end
