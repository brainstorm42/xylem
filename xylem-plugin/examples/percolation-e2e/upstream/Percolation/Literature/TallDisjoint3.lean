import Percolation.Literature.TallDisjoint2
import Percolation.Util.Linter

/-!
# The tall gait, XIII (end): the trunk and the branches; all bricks pairwise disjoint

End of `TallDisjoint.lean` (Grimmett, *Percolation*,
2nd ed. (1999), §7.3 p. 173 (C)): the branch bricks and branch legs are disjoint from the trunk by
the turn estimates of `GaitKinematics.lean` (the trunk is pre- and post-steered on the windows around
the branch points, which are `2P'` apart), the two branch sides are apart along `e`, and finally
**all bricks recorded in a run state are pairwise box-disjoint** (`pairwise_disjoint_all`).

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
/-- If `p` fails below `K ≤ N` then `K ≤ firstIdx p N`. [folklore] -/
theorem le_firstIdx_of {p : ℕ → Prop} {N K : ℕ} (hK : K ≤ N) (h : ∀ k < K, ¬p k) : K ≤ firstIdx p N := by
  by_contra hlt
  push Not at hlt
  have hspec : p (firstIdx p N) ∨ firstIdx p N = N := by
    unfold firstIdx; exact Nat.find_spec (⟨N, Or.inr rfl⟩ : ∃ k, p k ∨ k = N)
  rcases hspec with hp | hp
  · exact h _ hlt hp
  · omega

/-- **The two branch points are at least `2P'` apart.** [folklore] -/
theorem n1_add_le_n2 (hY : Y.OK) (hτ : TAdm hd Y a e τ) {st : RS d} (hI : TallInv hd Y hL hH a e τ st) (hT : st.sT ≠ []) :
    n1Of hd Y a e st.sT + 2 * Y.Pw ≤ n2Of hd Y a e st.sT := by
  obtain ⟨hLp0, hLpP, hLeq, hell, hmH, hP8, hPw, hΔw, hΔ0, hρv, hρp, hlam, hlamJ, hWl, hDh, hN1, hPe, hP2, hP3, hNL, hP32, hP64,
    hPwe, hRpos⟩ := hY.facts
  obtain ⟨-, hNT, hn1, -⟩ := trunk_feasible Y hd hL hH a e τ hY hτ hI hT
  set b := (legOf st.sT 0).b (axOf hd e) with hb
  set n₁ := n1Of hd Y a e st.sT with hn₁
  have hs : (sgOf e : ℤ) * (sgOf e : ℤ) = 1 := by rcases Int.units_eq_one_or (sgOf e) with h | h <;> simp [h]
  -- the lanes: `s (lane₂ - lane₁) = 2Λ`
  have hlanes : (sgOf e : ℤ) * (brLane Y a e (-br1Sign e) - brLane Y a e (br1Sign e)) = 2 * Y.lam := by
    rw [brLane_eq, brLane_eq]
    unfold br1Sign
    rcases Int.units_eq_one_or (sgOf e) with h | h <;> simp [h] <;> ring
  -- not passed at `n₁ - 1`
  have hnp := not_of_lt_firstIdx (p := fun k => passed Y e (tgtCell a e) (br1Sign e) (b + (sgOf e : ℤ) * (k * Y.ell)))
    (N := Y.Rmax) (k := n₁ - 1) (by show n₁ - 1 < n1Of hd Y a e st.sT; omega)
  rw [passed_iff, ← brLane] at hnp
  push Not at hnp
  obtain ⟨-, hlegNT, -, hn2le⟩ := trunk_feasible Y hd hL hH a e τ hY hτ hI hT
  have h12 := n1Of_le_n2Of Y hd a e st.sT
  apply le_firstIdx_of
  · -- `n₁ + 2P' ≤ Rmax`
    have hn1NT : n₁ ≤ Y.NT := h12.trans (hn2le.trans hlegNT)
    unfold TallLayout.NT at hn1NT; unfold TallLayout.Rmax TallLayout.Pw
    have hP := hY.hP
    have h3 : 8 * 8 * 8 ≤ Y.P ^ 3 := by
      have : 8 ^ 3 ≤ Y.P ^ 3 := Nat.pow_le_pow_left hP 3
      simpa using this
    have h4 : Y.P ≤ Y.P ^ 3 := by
      calc Y.P = Y.P ^ 1 := (pow_one _).symm
        _ ≤ Y.P ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
    omega
  · intro k hk hpk
    rw [passed_iff, ← brLane] at hpk
    have hk' : (k : ℤ) ≤ ((n₁ - 1 : ℕ) : ℤ) + 2 * Y.Pw := by
      have h1 : ((n₁ - 1 : ℕ) : ℤ) = n₁ - 1 := by push_cast [Nat.cast_sub hn1]; ring
      have : (k : ℤ) < n₁ + 2 * Y.Pw := by exact_mod_cast hk
      rw [h1]; omega
    have hl0 : (0 : ℤ) ≤ Y.ell := by linarith
    have hkl : (k : ℤ) * Y.ell ≤ ((n₁ - 1 : ℕ) : ℤ) * Y.ell + 2 * Y.Pw * Y.ell := by
      have := mul_le_mul_of_nonneg_right hk' hl0
      linarith only [this]
    have e1 : (sgOf e : ℤ) * (b + (sgOf e : ℤ) * (k * Y.ell) - brLane Y a e (-br1Sign e)) =
        (sgOf e : ℤ) * (b + (sgOf e : ℤ) * (((n₁ - 1 : ℕ) : ℤ) * Y.ell) - brLane Y a e (br1Sign e)) +
          ((sgOf e : ℤ) * (sgOf e : ℤ)) * (k * Y.ell - ((n₁ - 1 : ℕ) : ℤ) * Y.ell) -
          (sgOf e : ℤ) * (brLane Y a e (-br1Sign e) - brLane Y a e (br1Sign e)) := by ring
    rw [e1, hs, hlanes] at hpk
    linarith only [hpk, hnp, hkl, hPwe, hlam, hP2, hPe, hP64, hell, hmH]

/-- **The trunk is steered around its branch points** as the turn estimates require: towards the
first branch before it and away after it (once `γ₁` is placed), towards the second before it and away
after it (once `γ₂` is placed). [folklore] -/
theorem trunk_windows (hY : Y.OK) (hτ : TAdm hd Y a e τ) {st : RS d} (hI : TallInv hd Y hL hH a e τ st) (hT : st.sT ≠ []) :
    (n1Of hd Y a e st.sT < st.sT.length →
      Steered (latOf hd e) (br1Sign e : ℤ) (n1Of hd Y a e st.sT - Y.Pw) (n1Of hd Y a e st.sT) (legOf st.sT) ∧
      Steered (latOf hd e) (-(br1Sign e : ℤ)) (n1Of hd Y a e st.sT) (min (n1Of hd Y a e st.sT + Y.Pw) (st.sT.length - 1)) (legOf st.sT)) ∧
    (n2Of hd Y a e st.sT < st.sT.length →
      Steered (latOf hd e) ((-br1Sign e : ℤˣ) : ℤ) (n2Of hd Y a e st.sT - Y.Pw) (n2Of hd Y a e st.sT) (legOf st.sT) ∧
      Steered (latOf hd e) (-((-br1Sign e : ℤˣ) : ℤ)) (n2Of hd Y a e st.sT) (min (n2Of hd Y a e st.sT + Y.Pw) (st.sT.length - 1)) (legOf st.sT)) := by
  have h12 := n1_add_le_n2 Y hd hL hH a e τ hY hτ hI hT
  set n₁ := n1Of hd Y a e st.sT
  set n₂ := n2Of hd Y a e st.sT
  have hst := hI.invT.steer
  refine ⟨fun hn1 => ⟨fun k hk0 hk1 => ?_, fun k hk0 hk1 => ?_⟩, fun hn2 => ⟨fun k hk0 hk1 => ?_, fun k hk0 hk1 => ?_⟩⟩
  · have h := hst k (by omega)
    have : trunkForce Y e n₁ n₂ k = (br1Sign e : ℤ) := by
      unfold trunkForce; simp only; rw [if_pos ⟨hk1, by omega⟩]
    rw [this] at h; exact h
  · have h := hst k (by omega)
    have : trunkForce Y e n₁ n₂ k = -(br1Sign e : ℤ) := by
      unfold trunkForce; simp only; rw [if_neg (by omega), if_pos ⟨hk0, by omega⟩]
    rw [this] at h; exact h
  · have h := hst k (by omega)
    have : trunkForce Y e n₁ n₂ k = -(br1Sign e : ℤ) := by
      unfold trunkForce; simp only; rw [if_neg (by omega), if_neg (by omega), if_pos ⟨hk1, by omega⟩]
    rw [this] at h; simpa using h
  · have h := hst k (by omega)
    have : trunkForce Y e n₁ n₂ k = (br1Sign e : ℤ) := by
      unfold trunkForce; simp only; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos ⟨hk0, by omega⟩]
    rw [this] at h; simpa using h

/-- **A branch brick and its leg are disjoint from the trunk.** [cite: GrimmettPercolation1999, §7.3 pp. 172–173 (B)–(D)] -/
theorem disjoint_T_branch (hY : Y.OK) (hτ : TAdm hd Y a e τ) {st : RS d} (hI : TallInv hd Y hL hH a e τ st)
    {w : ℤˣ} {g : BrickRec d} {sB : List (BrickRec d)} {D : Prop} (hB : InvB hd Y hL hH a e w (some g) sB D)
    (hg : n1Of hd Y a e st.sT < st.sT.length ∧ w = br1Sign e ∧
        IsTurn Y.m Y.L Y.H (axOf hd e) (sgOf e) (latOf hd e) w (legOf st.sT (n1Of hd Y a e st.sT)) g.1 ∨
      n2Of hd Y a e st.sT < st.sT.length ∧ w = -br1Sign e ∧
        IsTurn Y.m Y.L Y.H (axOf hd e) (sgOf e) (latOf hd e) w (legOf st.sT (n2Of hd Y a e st.sT)) g.1)
    {k : ℕ} (hk : k < st.sT.length) {j : ℕ} (hj : j ≤ sB.length) :
    Disjoint (boxOf Y.L Y.H (legOf st.sT k)) (boxOf Y.L Y.H (legOf (sB ++ [g]) j)) := by
  obtain ⟨hLp0, hLpP, hLeq, hell, hmH, -, -, -, -, -, -, -, -, -, -, -, hPe, -, -, -, -, -, hPwe, -⟩ := hY.facts
  have hT : st.sT ≠ [] := List.ne_nil_of_length_pos (by omega)
  obtain ⟨hw12, hw34⟩ := trunk_windows Y hd hL hH a e τ hY hτ hI hT
  have hgT := hI.invT.grown hT
  have hleg := hgT.isLeg
  have hturnT := hI.invT.turn hT
  rw [hturnT.axis, hturnT.sign] at hleg
  have hP' : 2 * (Y.L : ℤ) + Y.H + 2 ≤ (Y.Pw : ℤ) * ((Y.H : ℤ) + 1) := by
    have : (Y.Pw : ℤ) * ((Y.H : ℤ) + 1) = Y.Pw * Y.ell := by rw [hell]
    rw [this]; linarith only [hPwe, hLpP, hPe, hLeq, hLp0, hell, hmH]
  -- the child leg `γ' = legOf (sB ++ [g])`
  have hγ0 : legOf (sB ++ [g]) 0 = g.1 := legOf_append_singleton_zero sB g
  rcases hg with ⟨hn, rfl, hturn⟩ | ⟨hn, rfl, hturn⟩
  · have hcl : IsLeg Y.m Y.L Y.H (latOf hd e) (br1Sign e) sB.length (legOf (sB ++ [g])) := by
      by_cases hsB : sB = []
      · subst hsB
        refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => absurd hk (by simp), fun k hk => absurd hk (by simp)⟩ <;>
          (have : k = 0 := by simpa using hk) <;> subst this <;> rw [hγ0]
        exacts [hturn.axis, hturn.sign]
      · have hgl := (hB.grown g rfl hsB).isLeg
        rw [hγ0, hturn.axis, hturn.sign] at hgl
        simpa using hgl
    obtain ⟨w1, w2⟩ := hw12 hn
    exact IsTurn.disjoint_boxOf_child_leg hleg (by omega) hturn hγ0 hcl (fun j' hj' => hB.lng g rfl j' hj') w1 w2 hP' (by omega) hj
  · have hcl : IsLeg Y.m Y.L Y.H (latOf hd e) (-br1Sign e) sB.length (legOf (sB ++ [g])) := by
      by_cases hsB : sB = []
      · subst hsB
        refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => absurd hk (by simp), fun k hk => absurd hk (by simp)⟩ <;>
          (have : k = 0 := by simpa using hk) <;> subst this <;> rw [hγ0]
        exacts [hturn.axis, hturn.sign]
      · have hgl := (hB.grown g rfl hsB).isLeg
        rw [hγ0, hturn.axis, hturn.sign] at hgl
        simpa using hgl
    obtain ⟨w3, w4⟩ := hw34 hn
    exact IsTurn.disjoint_boxOf_child_leg hleg (by omega) hturn hγ0 hcl (fun j' hj' => hB.lng g rfl j' hj') w3 w4 hP' (by omega) hj

/-- **The two branch sides are disjoint** (apart along `e`). [cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
theorem disjoint_sides (hY : Y.OK) (hτ : TAdm hd Y a e τ) {st : RS d} (hI : TallInv hd Y hL hH a e τ st)
    {r : BrickRec d} (hr : r ∈ st.g1.toList ∨ r ∈ st.sB1) {r' : BrickRec d} (hr' : r' ∈ st.g2.toList ∨ r' ∈ st.sB2) :
    Disjoint (boxOf Y.L Y.H r.1) (boxOf Y.L Y.H r'.1) := by
  obtain ⟨hLp0, hLpP, hLeq, hell, hmH, -, -, -, -, -, -, hlam, -, -, -, -, hPe, hP2, -, -, -, hP64, -⟩ := hY.facts
  obtain ⟨hNR, hNJ⟩ := sched_bounds Y hd hL hH a e τ hY hτ hI
  obtain ⟨-, -, -, -, -, -, hallR⟩ := all_length_lt Y hd hL hH a e τ hY hτ hI
  have hlenT : st.sT.length ≤ Y.Rmax := by
    have : st.sT.length ≤ st.all.length := by simp only [RS.all, List.length_append]; omega
    omega
  have hs1 : (sgOf e : ℤ) = 1 ∨ (sgOf e : ℤ) = -1 := by rcases Int.units_eq_one_or (sgOf e) with h | h <;> simp [h]
  have hs : (sgOf e : ℤ) * (sgOf e : ℤ) = 1 := by rcases hs1 with h | h <;> simp [h]
  -- the side-`i` records: base `s (b_e - laneᵢ) ∈ [-L', ℓ + H + L']`, axis `f`
  have hside : ∀ (w : ℤˣ) (go : Option (BrickRec d)) (sB : List (BrickRec d)) (D : Prop) (x : BrickRec d),
      InvB hd Y hL hH a e w go sB D →
      (∀ g, go = some g → brIdx Y a e w ((legOf st.sT 0).b (axOf hd e)) < st.sT.length ∧
        IsTurn Y.m Y.L Y.H (axOf hd e) (sgOf e) (latOf hd e) w (legOf st.sT (brIdx Y a e w ((legOf st.sT 0).b (axOf hd e)))) g.1 ∧
        |g.1.b (ax0 hd) - Y.zOf e| ≤ Y.ρv ∧ ∀ j, j ≠ axOf hd e → j ≠ latOf hd e → j ≠ ax0 hd → |g.1.b j| ≤ Y.Lp) →
      (x ∈ go.toList ∨ x ∈ sB) →
      x.1.a = latOf hd e ∧ -Y.Lp ≤ (sgOf e : ℤ) * (x.1.b (axOf hd e) - brLane Y a e w) ∧
        (sgOf e : ℤ) * (x.1.b (axOf hd e) - brLane Y a e w) ≤ Y.ell + Y.H + Y.Lp := by
    intro w go sB D x hB hgs hx
    obtain ⟨g, hgo⟩ : ∃ g, go = some g := by
      rcases hx with hx | hx
      · cases go with
        | none => exact absurd hx (by simp)
        | some g => exact ⟨g, rfl⟩
      · exact Option.ne_none_iff_exists'.1 (hB.prev (List.ne_nil_of_mem hx))
    have hg := hgs g hgo
    have hT : st.sT ≠ [] := List.ne_nil_of_length_pos (by omega)
    obtain ⟨-, -, hn1, -⟩ := trunk_feasible Y hd hL hH a e τ hY hτ hI hT
    have h12 := n1Of_le_n2Of Y hd a e st.sT
    have hn1' : 1 ≤ brIdx Y a e w ((legOf st.sT 0).b (axOf hd e)) := by
      rcases Int.units_eq_one_or w with rfl | rfl <;> rcases Int.units_eq_one_or (br1Sign e) with h | h
      · rw [← h]; exact hn1
      · have : -br1Sign e = 1 := by rw [h]; simp
        rw [← this]; exact hn1.trans h12
      · have : -br1Sign e = -1 := by rw [h]
        rw [← this]; exact hn1.trans h12
      · rw [← h]; exact hn1
    obtain ⟨hgax, hgs', -, -, hg0, hg1, -, -⟩ := boundsG Y hd hL hH a e τ hY hI hNR hNJ hlenT hg rfl hn1'
    subst hgo
    have hx' : x ∈ sB ++ [g] := by
      rcases hx with hx | hx
      · simp only [Option.toList_some, List.mem_singleton] at hx; subst hx; simp
      · exact List.mem_append_left _ hx
    obtain ⟨k, hk, rfl⟩ := exists_recOf_of_mem hx'
    have hk' : k ≤ sB.length := by simp at hk; omega
    obtain ⟨-, hlng, -, -⟩ := boundsB Y hd hL hH a e hB hgax hgs' hk'
    have hl := abs_le.1 hlng
    have hax : (legOf (sB ++ [g]) k).a = latOf hd e := by
      rcases Nat.eq_zero_or_pos k with rfl | hpos
      · rw [legOf_append_singleton_zero]; exact hgax
      · have hne : sB ≠ [] := List.ne_nil_of_length_pos (by omega)
        have := ((hB.grown g rfl hne).axis_sign (k := k) hk).1
        rw [legOf_append_singleton_zero] at this; rw [this]; exact hgax
    have hrl : (recOf (sB ++ [g]) k).1 = legOf (sB ++ [g]) k := rfl
    rw [hrl]
    refine ⟨hax, ?_, ?_⟩ <;>
      rcases hs1 with h | h <;> rw [h] at hg0 hg1 ⊢ <;> linarith only [hl.1, hl.2, hg0, hg1]
  have hlanes : (sgOf e : ℤ) * (brLane Y a e (-br1Sign e) - brLane Y a e (br1Sign e)) = 2 * Y.lam := by
    rw [brLane_eq, brLane_eq]; unfold br1Sign
    rcases Int.units_eq_one_or (sgOf e) with h | h <;> simp [h] <;> ring
  obtain ⟨hax1, h1lo, h1hi⟩ := hside (br1Sign e) st.g1 st.sB1 _ r hI.invB1 (fun g hg => hI.invT.g1_some g hg) hr
  obtain ⟨hax2, h2lo, h2hi⟩ := hside (-br1Sign e) st.g2 st.sB2 _ r' hI.invB2 (fun g hg => hI.invT.g2_some g hg) hr'
  rw [Set.disjoint_left]
  intro w hw hw'
  obtain ⟨h3, h2⟩ := box_trans hw (i := axOf hd e) (by rw [hax1]; exact (latOf_ne_axOf hd e).symm)
  obtain ⟨h5, h4⟩ := box_trans hw' (i := axOf hd e) (by rw [hax2]; exact (latOf_ne_axOf hd e).symm)
  rcases hs1 with h | h <;> rw [h] at h1lo h1hi h2lo h2hi hlanes <;>
    linarith only [h2, h3, h4, h5, h1lo, h1hi, h2lo, h2hi, hlanes, hlam, hP2, hPe, hP64, hLeq, hLpP, hell, hmH, hLp0]

end BGNd

end Percolation.Literature

end

namespace Percolation.Literature.BGNd

open LatticeModels Contour
open scoped Classical

variable {d : ℕ} [NeZero d]
variable (Y : TallLayout) (hd : 3 ≤ d) (hL : Y.m + 1 ≤ Y.L) (hH : 2 * Y.m + 2 ≤ Y.H) (a : Site 2) (e : MDir) (τ : TTok d)

/-- Box-disjointness of two records. [folklore] -/
def BoxDisj (L H : ℕ) (r r' : BrickRec d) : Prop := Disjoint (boxOf L H r.1) (boxOf L H r'.1)

omit [NeZero d] in
/-- `BoxDisj` is symmetric. [folklore] -/
theorem BoxDisj.symm {L H : ℕ} {r r' : BrickRec d} (h : BoxDisj L H r r') : BoxDisj L H r' r := Disjoint.symm h

/-- The `k`-th element of the reversed list is `recOf l k`. [folklore] -/
theorem getElem_reverse_eq_recOf (l : List (BrickRec d)) {k : ℕ} (hk : k < l.reverse.length) : l.reverse[k] = recOf l k := by
  unfold recOf; rw [List.getElem?_eq_getElem hk]; rfl

/-- **A grown list is pairwise box-disjoint.** [cite: GrimmettPercolation1999, §7.3 p. 172 (A)] -/
theorem pairwise_of_grown {m L H : ℕ} {hL : m + 1 ≤ L} {hH : 2 * m + 2 ≤ H} {l : List (BrickRec d)} (hg : Grown hL hH l) :
    l.Pairwise (BoxDisj L H) := by
  have : l.reverse.Pairwise (BoxDisj L H) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    rw [getElem_reverse_eq_recOf l hi, getElem_reverse_eq_recOf l hj]
    exact disjoint_of_grown hg (Nat.ne_of_lt hij) (by simpa using hi) (by simpa using hj)
  rw [List.pairwise_reverse] at this
  exact this.imp fun h => h.symm

/-- A branch leg with its branch brick is pairwise box-disjoint. [folklore] -/
theorem pairwise_branch {w : ℤˣ} {go : Option (BrickRec d)} {sB : List (BrickRec d)} {D : Prop} (hB : InvB hd Y hL hH a e w go sB D) :
    (go.toList ++ sB).Pairwise (BoxDisj Y.L Y.H) := by
  cases hgo : go with
  | none =>
    rw [hgo] at hB
    have : sB = [] := by by_contra h; exact hB.prev h rfl
    subst this; simp
  | some g =>
    rw [hgo] at hB
    by_cases hsB : sB = []
    · subst hsB; simp
    · have hp := pairwise_of_grown (hB.grown g rfl hsB)
      rw [List.pairwise_append] at hp ⊢
      refine ⟨List.pairwise_singleton _ _, hp.1, fun x hx y hy => ?_⟩
      simp only [Option.toList_some, List.mem_singleton] at hx; subst hx
      exact (hp.2.2 y hy x (List.mem_singleton_self _)).symm

/-- **All bricks recorded in a run state are pairwise box-disjoint.** [cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
theorem pairwise_disjoint_all (hY : Y.OK) (hτ : TAdm hd Y a e τ) {st : RS d} (hI : TallInv hd Y hL hH a e τ st) :
    st.all.Pairwise (BoxDisj Y.L Y.H) := by
  -- the pair lemmas, by membership
  have hAR : ∀ x ∈ st.sA, ∀ y ∈ st.sR, BoxDisj Y.L Y.H x y := fun x hx y hy => by
    obtain ⟨j, hj, rfl⟩ := exists_recOf_of_mem hx; obtain ⟨k, hk, rfl⟩ := exists_recOf_of_mem hy
    exact disjoint_A_R Y hd hL hH a e τ hY hI hj hk
  have hAJ : ∀ x ∈ st.sA, ∀ y ∈ st.sJ, BoxDisj Y.L Y.H x y := fun x hx y hy => by
    obtain ⟨j, hj, rfl⟩ := exists_recOf_of_mem hx; obtain ⟨k, hk, rfl⟩ := exists_recOf_of_mem hy
    exact disjoint_A_J Y hd hL hH a e τ hY hτ hI hj hk
  have hRJ : ∀ x ∈ st.sR, ∀ y ∈ st.sJ, BoxDisj Y.L Y.H x y := fun x hx y hy => by
    obtain ⟨j, hj, rfl⟩ := exists_recOf_of_mem hx; obtain ⟨k, hk, rfl⟩ := exists_recOf_of_mem hy
    exact disjoint_R_J Y hd hL hH a e τ hY hτ hI hj hk
  have hAT : ∀ x ∈ st.sA, ∀ y ∈ st.sT, BoxDisj Y.L Y.H x y := fun x hx y hy => by
    obtain ⟨j, hj, rfl⟩ := exists_recOf_of_mem hx; obtain ⟨k, hk, rfl⟩ := exists_recOf_of_mem hy
    exact disjoint_A_T Y hd hL hH a e τ hY hτ hI hj hk
  have hRJT : ∀ x, x ∈ st.sR ∨ x ∈ st.sJ → ∀ y ∈ st.sT, BoxDisj Y.L Y.H x y := fun x hx y hy => by
    obtain ⟨k, hk, rfl⟩ := exists_recOf_of_mem hy
    exact disjoint_RJ_T Y hd hL hH a e τ hY hτ hI hx hk
  have hEB : ∀ x, x ∈ st.sA ∨ x ∈ st.sR ∨ x ∈ st.sJ → ∀ y, InBranch st y → BoxDisj Y.L Y.H x y := fun x hx y hy =>
    disjoint_entry_branch Y hd hL hH a e τ hY hτ hI hx hy
  have hTB1 : ∀ x ∈ st.sT, ∀ y, y ∈ st.g1.toList ∨ y ∈ st.sB1 → BoxDisj Y.L Y.H x y := fun x hx y hy => by
    obtain ⟨k, hk, rfl⟩ := exists_recOf_of_mem hx
    obtain ⟨g, hg1⟩ : ∃ g, st.g1 = some g := by
      rcases hy with hy | hy
      · cases h : st.g1 with
        | none => rw [h] at hy; exact absurd hy (by simp)
        | some g => exact ⟨g, rfl⟩
      · exact Option.ne_none_iff_exists'.1 (hI.invB1.prev (List.ne_nil_of_mem hy))
    have hy' : y ∈ st.sB1 ++ [g] := by
      rcases hy with hy | hy
      · rw [hg1] at hy; simp only [Option.toList_some, List.mem_singleton] at hy; subst hy; simp
      · exact List.mem_append_left _ hy
    obtain ⟨j, hj, rfl⟩ := exists_recOf_of_mem hy'
    have hB := hI.invB1; rw [hg1] at hB
    obtain ⟨hn, hturn, -, -⟩ := hI.invT.g1_some g hg1
    exact disjoint_T_branch Y hd hL hH a e τ hY hτ hI hB (Or.inl ⟨hn, rfl, hturn⟩) hk (by simpa using hj)
  have hTB2 : ∀ x ∈ st.sT, ∀ y, y ∈ st.g2.toList ∨ y ∈ st.sB2 → BoxDisj Y.L Y.H x y := fun x hx y hy => by
    obtain ⟨k, hk, rfl⟩ := exists_recOf_of_mem hx
    obtain ⟨g, hg2⟩ : ∃ g, st.g2 = some g := by
      rcases hy with hy | hy
      · cases h : st.g2 with
        | none => rw [h] at hy; exact absurd hy (by simp)
        | some g => exact ⟨g, rfl⟩
      · exact Option.ne_none_iff_exists'.1 (hI.invB2.prev (List.ne_nil_of_mem hy))
    have hy' : y ∈ st.sB2 ++ [g] := by
      rcases hy with hy | hy
      · rw [hg2] at hy; simp only [Option.toList_some, List.mem_singleton] at hy; subst hy; simp
      · exact List.mem_append_left _ hy
    obtain ⟨j, hj, rfl⟩ := exists_recOf_of_mem hy'
    have hB := hI.invB2; rw [hg2] at hB
    obtain ⟨hn, hturn, -, -⟩ := hI.invT.g2_some g hg2
    exact disjoint_T_branch Y hd hL hH a e τ hY hτ hI hB (Or.inr ⟨hn, rfl, hturn⟩) hk (by simpa using hj)
  have hS : ∀ x, x ∈ st.g1.toList ∨ x ∈ st.sB1 → ∀ y, y ∈ st.g2.toList ∨ y ∈ st.sB2 → BoxDisj Y.L Y.H x y := fun x hx y hy =>
    disjoint_sides Y hd hL hH a e τ hY hτ hI hx hy
  have hside1 := pairwise_branch Y hd hL hH a e hI.invB1
  have hside2 := pairwise_branch Y hd hL hH a e hI.invB2
  rw [List.pairwise_append] at hside1 hside2
  -- within segments
  have hPA : st.sA.Pairwise (BoxDisj Y.L Y.H) := by
    by_cases h : st.sA = []
    · rw [h]; simp
    · exact pairwise_of_grown (hI.invA.grown h)
  have hPR : st.sR.Pairwise (BoxDisj Y.L Y.H) := by
    by_cases h : st.sR = []
    · rw [h]; simp
    · exact pairwise_of_grown (hI.invR.grown h)
  have hPJ : st.sJ.Pairwise (BoxDisj Y.L Y.H) := by
    by_cases h : st.sJ = []
    · rw [h]; simp
    · exact pairwise_of_grown (hI.invJ.grown h)
  have hPT : st.sT.Pairwise (BoxDisj Y.L Y.H) := by
    by_cases h : st.sT = []
    · rw [h]; simp
    · exact pairwise_of_grown (hI.invT.grown h)
  -- assemble along `all = sA ++ sR ++ sJ ++ sT ++ g1 ++ g2 ++ sB1 ++ sB2`
  unfold RS.all
  simp only [List.pairwise_append, List.mem_append]
  refine ⟨⟨⟨⟨⟨⟨⟨hPA, hPR, hAR⟩, hPJ, ?_⟩, hPT, ?_⟩, hside1.1, ?_⟩, hside2.1, ?_⟩, hside1.2.1, ?_⟩, hside2.2.1, ?_⟩
  · rintro x (hx | hx) y hy
    exacts [hAJ x hx y hy, hRJ x hx y hy]
  · rintro x ((hx | hx) | hx) y hy
    exacts [hAT x hx y hy, hRJT x (Or.inl hx) y hy, hRJT x (Or.inr hx) y hy]
  · rintro x (((hx | hx) | hx) | hx) y hy
    exacts [hEB x (Or.inl hx) y (Or.inl hy), hEB x (Or.inr (Or.inl hx)) y (Or.inl hy), hEB x (Or.inr (Or.inr hx)) y (Or.inl hy),
      hTB1 x hx y (Or.inl hy)]
  · rintro x ((((hx | hx) | hx) | hx) | hx) y hy
    exacts [hEB x (Or.inl hx) y (Or.inr (Or.inl hy)), hEB x (Or.inr (Or.inl hx)) y (Or.inr (Or.inl hy)),
      hEB x (Or.inr (Or.inr hx)) y (Or.inr (Or.inl hy)), hTB2 x hx y (Or.inl hy), hS x (Or.inl hx) y (Or.inl hy)]
  · rintro x (((((hx | hx) | hx) | hx) | hx) | hx) y hy
    exacts [hEB x (Or.inl hx) y (Or.inr (Or.inr (Or.inl hy))), hEB x (Or.inr (Or.inl hx)) y (Or.inr (Or.inr (Or.inl hy))),
      hEB x (Or.inr (Or.inr hx)) y (Or.inr (Or.inr (Or.inl hy))), hTB1 x hx y (Or.inr hy), hside1.2.2 x hx y hy,
      (hS y (Or.inr hy) x (Or.inl hx)).symm]
  · rintro x ((((((hx | hx) | hx) | hx) | hx) | hx) | hx) y hy
    exacts [hEB x (Or.inl hx) y (Or.inr (Or.inr (Or.inr hy))), hEB x (Or.inr (Or.inl hx)) y (Or.inr (Or.inr (Or.inr hy))),
      hEB x (Or.inr (Or.inr hx)) y (Or.inr (Or.inr (Or.inr hy))), hTB2 x hx y (Or.inr hy), hS x (Or.inl hx) y (Or.inr hy),
      hside2.2.2 x hx y hy, hS x (Or.inr hx) y (Or.inr hy)]

end Percolation.Literature.BGNd
