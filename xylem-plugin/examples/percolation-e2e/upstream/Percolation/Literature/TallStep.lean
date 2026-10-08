import Percolation.Literature.TallInvB
import Percolation.Util.Linter

/-!
# The tall gait, IX: every placement of the plan preserves the invariant

Dispatch of the decision function `step`
(`TallRoute.lean`) to the fourteen preservation lemmas of `TallInvA2` – `TallInvB`: if the run state
satisfies `TallInv`, all its records are good, and its riser and jog are shorter than the brick
budget, then filing the record of the emitted act preserves `TallInv` (Grimmett, *Percolation*,
2nd ed. (1999), §7.3, Lemma (7.52)). Also: the first branch point precedes the second
(`n1Of_le_n2Of`).

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §7.3 pp. 172–174.
-/

noncomputable section

namespace Percolation.Literature

open LatticeModels Contour
open scoped Classical

namespace BGNd

variable {d : ℕ} [NeZero d]

/-- `firstIdx` is monotone in the predicate (reversed). [folklore] -/
theorem firstIdx_mono {p q : ℕ → Prop} (N : ℕ) (h : ∀ k, q k → p k) : firstIdx p N ≤ firstIdx q N := by
  by_contra hlt
  push Not at hlt
  have hq : q (firstIdx q N) ∨ firstIdx q N = N := by
    unfold firstIdx
    exact Nat.find_spec (⟨N, Or.inr rfl⟩ : ∃ k, q k ∨ k = N)
  rcases hq with hq | hq
  · exact not_of_lt_firstIdx hlt (h _ hq)
  · have := firstIdx_le p N; omega

variable (Y : TallLayout) (hd : 3 ≤ d) (hL : Y.m + 1 ≤ Y.L) (hH : 2 * Y.m + 2 ≤ Y.H) (a : Site 2) (e : MDir) (τ : TTok d)

namespace TallLayout
/-- `Λ ≥ 0`. [folklore] -/
theorem lam_nonneg (Y : TallLayout) : 0 ≤ Y.lam := by unfold lam; positivity
end TallLayout

omit [NeZero d] hd in
/-- The second branch lane is passed only after the first. [folklore] -/
theorem passed_of_passed_neg (c : Site 2) (b : ℤ) (h : passed Y e c (-br1Sign e) b) : passed Y e c (br1Sign e) b := by
  have hlam := Y.lam_nonneg
  unfold passed at h ⊢
  unfold br1Sign at h ⊢
  have hs : (sgOf e : ℤ) = 1 ∨ (sgOf e : ℤ) = -1 := by rcases Int.units_eq_one_or (sgOf e) with h' | h' <;> simp [h']
  unfold TallLayout.lane TallLayout.nu at h ⊢
  rcases hs with hs | hs
  · have h1 : sgOf e = 1 := Units.ext hs
    simp only [h1, neg_neg, Units.val_one, Units.val_neg, show ((-1 : ℤ) = 1) = False by simp, decide_false,
      decide_true, mul_zero, zero_add] at h ⊢
    simp only [latDir, Bool.false_eq_true, ↓reduceIte] at h ⊢
    rcases h with h | h
    · left; constructor <;> [linarith [h.1]; exact h.2]
    · exact absurd h.2 (by norm_num)
  · have h1 : sgOf e = -1 := Units.ext hs
    simp only [h1, neg_neg, Units.val_one, Units.val_neg, show ((-1 : ℤ) = 1) = False by simp, decide_false,
      decide_true, mul_zero, zero_add] at h ⊢
    simp only [latDir, Bool.false_eq_true, ↓reduceIte] at h ⊢
    rcases h with h | h
    · exact absurd h.2 (by norm_num)
    · right; constructor <;> [linarith [h.1]; exact h.2]

/-- **The first branch point precedes the second.** [folklore] -/
theorem n1Of_le_n2Of (sT : List (BrickRec d)) : n1Of hd Y a e sT ≤ n2Of hd Y a e sT := by
  unfold n1Of n2Of brIdx
  exact firstIdx_mono _ fun k hk => passed_of_passed_neg Y e _ _ hk

/-- Along a grown list, the axis coordinate advances by `k ℓ`. [folklore] -/
theorem Grown.b_axis {m L H : ℕ} {hL : m + 1 ≤ L} {hH : 2 * m + 2 ≤ H} {l : List (BrickRec d)} (hg : Grown hL hH l) {k : ℕ}
    (hk : k < l.length) :
    (legOf l k).b (legOf l 0).a = (legOf l 0).b (legOf l 0).a + ((legOf l 0).s : ℤ) * ((H : ℤ) + 1) * k := by
  have := hg.isLeg.b_axis (Nat.zero_le k) (by omega)
  simpa using this

/-- **Every placement of the plan preserves the invariant.** [cite: GrimmettPercolation1999, §7.3 pp. 172–174] -/
theorem tallInv_update (hY : Y.OK) (hτ : TAdm hd Y a e τ) {st : RS d} (hI : TallInv hd Y hL hH a e τ st)
    (hgood : ∀ r ∈ st.all, GoodRec Y.m Y.L Y.H r) (hlenR : st.sR.length ≤ Y.Rmax) (hlenJ : st.sJ.length ≤ Y.Rmax)
    {act : Act d} {slot : Slot} {ph' : Phase} (hs : step hd Y a e τ st = some (act, slot, ph')) (o : Finset (Sym2 (Site d))) :
    TallInv hd Y hL hH a e τ { st.put slot (placeOf hd Y hL hH e τ act, o) with ph := ph' } := by
  have hall : ∀ r, r ∈ st.sA ∨ r ∈ st.sR ∨ r ∈ st.sJ ∨ r ∈ st.sT ∨ r ∈ st.g1.toList ∨ r ∈ st.g2.toList ∨ r ∈ st.sB1 ∨ r ∈ st.sB2 →
      GoodRec Y.m Y.L Y.H r := by
    intro r hr; apply hgood; simp only [RS.all, List.mem_append]; tauto
  rcases hph : st.ph with _ | _ | _ | _ | _ | _ | _
  · -- segment A
    obtain ⟨hR, hJ, hT, h1, h2⟩ := phaseOf_eq_segA (hI.ph_eq ▸ hph)
    unfold step at hs
    cases hA : st.sA with
    | nil =>
      simp only [hph, hA] at hs
      simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl, rfl⟩ := hs
      exact tallInv_first hd Y hL hH a e τ hY hτ hI hph hA o
    | cons r₀ tl =>
      simp only [hph, hA] at hs
      have hg0 : GoodRec Y.m Y.L Y.H r₀ := hall r₀ (Or.inl (by rw [hA]; exact List.mem_cons_self))
      by_cases hlen : (r₀ :: tl).length ≤ Y.Pw
      · rw [if_pos hlen] at hs
        simp only [Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨rfl, rfl, rfl⟩ := hs
        exact tallInv_topA hd Y hL hH a e τ hY hI hph hA hlen hg0 o rfl
      · rw [if_neg hlen] at hs
        have hlen' : (r₀ :: tl).length = Y.Pw + 1 := by
          have := hI.invA.len; rw [hA] at this; omega
        by_cases hu : riseDir Y e τ = 0
        · rw [if_pos hu] at hs
          simp only [Option.some.injEq, Prod.mk.injEq] at hs
          obtain ⟨rfl, rfl, rfl⟩ := hs
          exact tallInv_turnAJ hd Y hL hH a e τ hY hI hph hA hlen' hu hg0 o
        · rw [if_neg hu] at hs
          simp only [Option.some.injEq, Prod.mk.injEq] at hs
          obtain ⟨rfl, rfl, rfl⟩ := hs
          exact tallInv_turnAR hd Y hL hH a e τ hY hI hph hA hlen' hu hg0 o
  · -- the riser
    obtain ⟨hRne, hJ, hT, h1, h2⟩ := phaseOf_eq_segR (hI.ph_eq ▸ hph)
    obtain ⟨rk, tl, hRl⟩ := List.exists_cons_of_ne_nil hRne
    unfold step at hs
    simp only [hph, hRl, getLast?_eq_recOf (List.cons_ne_nil rk tl)] at hs
    have hg0 : GoodRec Y.m Y.L Y.H rk := hall rk (Or.inr (Or.inl (by rw [hRl]; exact List.mem_cons_self)))
    have hIR := hI.invR; rw [hRl] at hIR
    have hne := List.cons_ne_nil rk tl
    set n := riserLen Y e τ ((recOf (rk :: tl) 0).1.b (ax0 hd)) with hn
    have hn' : n = riserLen Y e τ ((legOf (rk :: tl) 0).b (ax0 hd)) := rfl
    simp only [List.length_cons, Nat.add_sub_cancel] at hs
    by_cases hturn : n ≤ tl.length
    · rw [if_pos hturn] at hs
      simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl, rfl⟩ := hs
      -- the riser turns exactly at `n`, where the window fits
      have hsch := hIR.sched
      have hkn : tl.length = n := by
        rcases Nat.eq_zero_or_pos tl.length with h0 | hpos
        · omega
        · have := hsch (tl.length - 1) (by simp; omega); omega
      have hnlt : n < Y.Rmax := by rw [← hkn]; rw [hRl] at hlenR; simp at hlenR; omega
      have hfit0 := of_firstIdx_lt (p := fun k => fits Y ((legOf (rk :: tl) 0).b (ax0 hd) + riseDir Y e τ * (k * Y.ell))
        (riseDir Y e τ) (Y.zOf e)) (N := Y.Rmax) hnlt
      -- the current base along the axis
      have hb := (hIR.grown hne).b_axis (k := tl.length) (by simp)
      have ht := hIR.turn hne
      rw [ht.axis, ht.sign, legOf_cons_length] at hb
      have hu : riseDir Y e τ ≠ 0 := fun h => absurd (hIR.nil h) hne
      rw [riseUnit_val Y e τ hu, hkn] at hb
      have hfit : fits Y (rk.1.b (ax0 hd)) (riseDir Y e τ) (Y.zOf e) := by
        rw [hb]
        have : (legOf (rk :: tl) 0).b (ax0 hd) + riseDir Y e τ * ((Y.H : ℤ) + 1) * n =
            (legOf (rk :: tl) 0).b (ax0 hd) + riseDir Y e τ * (n * Y.ell) := by unfold TallLayout.ell; push_cast; ring
        rw [this]; exact hfit0
      exact tallInv_turnRJ Y hd hL hH a e τ hY hI hph hRl (by rw [← hn', hkn]) hfit hg0 o
    · rw [if_neg hturn] at hs
      simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl, rfl⟩ := hs
      exact tallInv_topR Y hd hL hH a e τ hY hI hph hRl (by rw [← hn']; omega) hg0 o rfl
  · -- the jog
    obtain ⟨hJne, hT, h1, h2⟩ := phaseOf_eq_segJ (hI.ph_eq ▸ hph)
    obtain ⟨rk, tl, hJl⟩ := List.exists_cons_of_ne_nil hJne
    unfold step at hs
    simp only [hph, hJl, getLast?_eq_recOf (List.cons_ne_nil rk tl)] at hs
    have hg0 : GoodRec Y.m Y.L Y.H rk := hall rk (Or.inr (Or.inr (Or.inl (by rw [hJl]; exact List.mem_cons_self))))
    have hIJ := hI.invJ; rw [hJl] at hIJ
    have hne := List.cons_ne_nil rk tl
    set n := jogLen Y a e ((recOf (rk :: tl) 0).1.b (latOf hd e)) with hn
    have hn' : n = jogLen Y a e ((legOf (rk :: tl) 0).b (latOf hd e)) := rfl
    simp only [List.length_cons, Nat.add_sub_cancel] at hs
    by_cases hturn : n ≤ tl.length
    · rw [if_pos hturn] at hs
      simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl, rfl⟩ := hs
      have hsch := hIJ.sched
      have hkn : tl.length = n := by
        rcases Nat.eq_zero_or_pos tl.length with h0 | hpos
        · omega
        · have := hsch (tl.length - 1) (by simp; omega); omega
      have hnlt : n < Y.Rmax := by rw [← hkn]; rw [hJl] at hlenJ; simp at hlenJ; omega
      have hfit0 := of_firstIdx_lt (p := fun k => fits Y ((legOf (rk :: tl) 0).b (latOf hd e) + (jogDir a e : ℤ) * (k * Y.ell))
        (jogDir a e) (Y.lane (tgtCell a e) e)) (N := Y.Rmax) hnlt
      have hb := (hIJ.grown hne).b_axis (k := tl.length) (by simp)
      have ht := hIJ.turn hne
      rw [ht.axis, ht.sign, legOf_cons_length, hkn] at hb
      have hfit : fits Y (rk.1.b (latOf hd e)) (jogDir a e) (Y.lane (tgtCell a e) e) := by
        rw [hb]
        have : (legOf (rk :: tl) 0).b (latOf hd e) + (jogDir a e : ℤ) * ((Y.H : ℤ) + 1) * n =
            (legOf (rk :: tl) 0).b (latOf hd e) + (jogDir a e : ℤ) * (n * Y.ell) := by unfold TallLayout.ell; push_cast; ring
        rw [this]; exact hfit0
      exact tallInv_turnJT Y hd hL hH a e τ hY hI hph hJl (by rw [← hn', hkn]) hfit hg0 o
    · rw [if_neg hturn] at hs
      simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl, rfl⟩ := hs
      exact tallInv_topJ Y hd hL hH a e τ hY hI hph hJl (by rw [← hn']; omega) hg0 o
  · -- the trunk
    obtain ⟨hTne, h1, h2⟩ := phaseOf_eq_segT (hI.ph_eq ▸ hph)
    obtain ⟨rk, tl, hTl⟩ := List.exists_cons_of_ne_nil hTne
    unfold step at hs
    simp only [hph, hTl, getLast?_eq_recOf (List.cons_ne_nil rk tl)] at hs
    have hg0 : GoodRec Y.m Y.L Y.H rk := hall rk (Or.inr (Or.inr (Or.inr (Or.inl (by rw [hTl]; exact List.mem_cons_self)))))
    have hIT := hI.invT; rw [hTl] at hIT
    have hne := List.cons_ne_nil rk tl
    simp only [List.length_cons, Nat.add_sub_cancel] at hs
    have hn1 : brIdx Y a e (br1Sign e) ((recOf (rk :: tl) 0).1.b (axOf hd e)) = n1Of hd Y a e (rk :: tl) := rfl
    have hn2 : brIdx Y a e (-br1Sign e) ((recOf (rk :: tl) 0).1.b (axOf hd e)) = n2Of hd Y a e (rk :: tl) := rfl
    have hy0 : (recOf (rk :: tl) 0).1.b (latOf hd e) = (legOf (rk :: tl) 0).b (latOf hd e) := rfl
    have hnE : legLen Y a e e ((recOf (rk :: tl) 0).1.b (axOf hd e)) = legLen Y a e e ((legOf (rk :: tl) 0).b (axOf hd e)) := rfl
    rw [hn1, hn2, hy0, hnE] at hs
    by_cases hc1 : st.g1 = none ∧ n1Of hd Y a e (rk :: tl) ≤ tl.length
    · rw [if_pos hc1] at hs
      simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl, rfl⟩ := hs
      exact tallInv_gamma1 Y hd hL hH a e τ hY hI hph hTl hc1.1 hc1.2 (n1Of_le_n2Of Y hd a e _) hg0 o
    · rw [if_neg hc1] at hs
      by_cases hc2 : st.g1 ≠ none ∧ st.g2 = none ∧ n2Of hd Y a e (rk :: tl) ≤ tl.length
      · rw [if_pos hc2] at hs
        simp only [Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨rfl, rfl, rfl⟩ := hs
        exact tallInv_gamma2 Y hd hL hH a e τ hY hI hph hTl hc2.1 hc2.2.1 hc2.2.2 hg0 o
      · rw [if_neg hc2] at hs
        by_cases hroom : tl.length < legLen Y a e e ((legOf (rk :: tl) 0).b (axOf hd e))
        · rw [if_pos hroom] at hs
          simp only [Option.some.injEq, Prod.mk.injEq] at hs
          obtain ⟨rfl, rfl, rfl⟩ := hs
          refine tallInv_topT Y hd hL hH a e τ hY hI hph hTl hroom (fun hg => ?_) (fun hg hg' => ?_) hg0 o rfl
          · by_contra h; exact hc1 ⟨hg, by omega⟩
          · by_contra h; exact hc2 ⟨hg, hg', by omega⟩
        · rw [if_neg hroom] at hs
          cases hg1 : st.g1 with
          | none => rw [hg1] at hs; exact absurd hs (by simp)
          | some g =>
            rw [hg1] at hs
            simp only at hs
            by_cases hr0 : st.g2 ≠ none ∧ 0 < legLen Y a e (latDir e (decide ((br1Sign e : ℤ) = 1))) (g.1.b (latOf hd e))
            · rw [if_pos hr0] at hs
              simp only [Option.some.injEq, Prod.mk.injEq] at hs
              obtain ⟨rfl, rfl, rfl⟩ := hs
              have hgg : GoodRec Y.m Y.L Y.H g := hall g (by simp [hg1])
              exact tallInv_startB1 Y hd hL hH a e τ hY hI hph hTl (by omega) hg1 hr0.1 hr0.2 hgg o
            · rw [if_neg hr0] at hs; exact absurd hs (by simp)
  · -- the first branch
    obtain ⟨hB1ne, h2⟩ := phaseOf_eq_segB1 (hI.ph_eq ▸ hph)
    obtain ⟨rk, tl, hBl⟩ := List.exists_cons_of_ne_nil hB1ne
    obtain ⟨g, hg1⟩ := Option.ne_none_iff_exists'.1 (hI.invB1.prev (by rw [hBl]; exact List.cons_ne_nil _ _))
    unfold step at hs
    simp only [hph, hBl, hg1] at hs
    have hg0 : GoodRec Y.m Y.L Y.H rk := hall rk (by rw [hBl]; simp)
    by_cases hroom : (rk :: tl).length < legLen Y a e (latDir e (decide ((br1Sign e : ℤ) = 1))) (g.1.b (latOf hd e))
    · rw [if_pos hroom] at hs
      simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl, rfl⟩ := hs
      exact tallInv_topB1 Y hd hL hH a e τ hY hI hph hBl hg1 hroom hg0 o
    · rw [if_neg hroom] at hs
      cases hg2 : st.g2 with
      | none => rw [hg2] at hs; exact absurd hs (by simp)
      | some g' =>
        rw [hg2] at hs
        simp only at hs
        by_cases hr0 : 0 < legLen Y a e (latDir e (decide ((br1Sign e : ℤ) ≠ 1))) (g'.1.b (latOf hd e))
        · rw [if_pos hr0] at hs
          simp only [Option.some.injEq, Prod.mk.injEq] at hs
          obtain ⟨rfl, rfl, rfl⟩ := hs
          have hgg : GoodRec Y.m Y.L Y.H g' := hall g' (by simp [hg2])
          exact tallInv_startB2 Y hd hL hH a e τ hY hI hph hBl hg1 (by omega) hg2 hr0 hgg o
        · rw [if_neg hr0] at hs; exact absurd hs (by simp)
  · -- the second branch
    have hB2ne := phaseOf_eq_segB2 (hI.ph_eq ▸ hph)
    obtain ⟨rk, tl, hBl⟩ := List.exists_cons_of_ne_nil hB2ne
    obtain ⟨g, hg2⟩ := Option.ne_none_iff_exists'.1 (hI.invB2.prev (by rw [hBl]; exact List.cons_ne_nil _ _))
    unfold step at hs
    simp only [hph, hBl, hg2] at hs
    have hg0 : GoodRec Y.m Y.L Y.H rk := hall rk (by rw [hBl]; simp)
    by_cases hroom : (rk :: tl).length < legLen Y a e (latDir e (decide ((br1Sign e : ℤ) ≠ 1))) (g.1.b (latOf hd e))
    · rw [if_pos hroom] at hs
      simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl, rfl⟩ := hs
      exact tallInv_topB2 Y hd hL hH a e τ hY hI hph hBl hg2 hroom hg0 o
    · rw [if_neg hroom] at hs; exact absurd hs (by simp)
  · exact absurd (hI.ph_eq ▸ hph : phaseOf st = Phase.done) (by
      unfold phaseOf; split_ifs <;> simp)

end BGNd

end Percolation.Literature

end
