import Percolation.Literature.TallInvA
import Percolation.Util.Linter

/-!
# The tall gait, IV (cont.): preservation of the invariant along segment `A`

The three kinds of placements made in phase `A` of the
plan (`TallRoute.lean`) — the brick on the token (`tallInv_first`), a pre-steered top step
(`tallInv_topA`), and the turn into the riser or the jog (`tallInv_turnAR`, `tallInv_turnAJ`) —
preserve `TallInv` (Grimmett, *Percolation*, 2nd ed. (1999), §7.3 (A), (B), (D)); with the helpers
`legOf_head`, `Grown.axis_sign`, `InvA.of_full`, `riseUnit_val`.

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §7.3 pp. 172–174.
-/

noncomputable section

namespace Percolation.Literature

open LatticeModels Contour
open scoped Classical

namespace BGNd

variable {d : ℕ} [NeZero d]
variable (hd : 3 ≤ d) (Y : TallLayout) (hL : Y.m + 1 ≤ Y.L) (hH : 2 * Y.m + 2 ≤ Y.H) (a : Site 2) (e : MDir) (τ : TTok d)

/-- The newest record of a nonempty list is its `(length - 1)`-st oldest placement. [folklore] -/
theorem legOf_head (r₀ : BrickRec d) (tl : List (BrickRec d)) : legOf (r₀ :: tl) ((r₀ :: tl).length - 1) = r₀.1 := by
  rw [List.length_cons, Nat.add_sub_cancel]; exact legOf_cons_length r₀ tl

omit hd Y hL hH a e τ in
/-- Axis and sign along a grown list are those of its oldest placement. [folklore] -/
theorem Grown.axis_sign {m L H : ℕ} {hL : m + 1 ≤ L} {hH : 2 * m + 2 ≤ H} {l : List (BrickRec d)} (hg : Grown hL hH l)
    {k : ℕ} (hk : k < l.length) : (legOf l k).a = (legOf l 0).a ∧ (legOf l k).s = (legOf l 0).s :=
  ⟨hg.isLeg.axis k (by omega), hg.isLeg.sign k (by omega)⟩

/-- **The first brick preserves the invariant.** [cite: GrimmettPercolation1999, §7.3 p. 172 (A)] -/
theorem tallInv_first (hY : Y.OK) (hτ : TAdm hd Y a e τ) {st : RS d} (hI : TallInv hd Y hL hH a e τ st)
    (hph : st.ph = Phase.segA) (hA : st.sA = []) (o : Finset (Sym2 (Site d))) :
    TallInv hd Y hL hH a e τ { st.put Slot.toA (⟨axOf hd e, sgOf e, τ.pos⟩, o) with ph := Phase.segA } := by
  obtain ⟨hR, hJ, hT, h1, h2⟩ := phaseOf_eq_segA (hI.ph_eq ▸ hph)
  obtain ⟨hg1, hg2⟩ := hI.invT.gnil hT
  have hLp := hY.Lp_nonneg
  set r : BrickRec d := (⟨axOf hd e, sgOf e, τ.pos⟩, o) with hr
  have hleg0 : legOf [r] 0 = r.1 := legOf_cons_length r []
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [RS.put, hA]; exact (phaseOf_of_nil (by simpa using hR) (by simpa using hJ) (by simpa using hT)
      (by simpa using h1) (by simpa using h2)).symm
  · simp only [RS.put, hA, hR, hJ]
    exact
    { len := by simp
      full := by simp
      grown := fun _ => grown_singleton hL hH r
      zero := fun _ => hleg0
      lat := fun _ k hk => by
        have : k = 0 := by simpa using hk
        subst this; rw [hleg0, hr]; simp [hLp]
      lat0 := fun _ k hk => by
        have : k = 0 := by simpa using hk
        subst this; rw [hleg0, hr]; simp
      latst := fun _ k _ hk => absurd hk (by simp)
      oth := fun k hk j hj1 hj2 hj3 => by
        have : k = 0 := by simpa using hk
        subst this; rw [hleg0, hr]; exact hτ.other j hj1 hj2 hj3
      ht0 := fun hu k hk => by
        have : k = 0 := by simpa using hk
        subst this; rw [hleg0, hr]; simp only
        have hh := hτ.height
        have hz : Y.zOf (τ.src.getD e) = Y.zOf e := by
          unfold riseDir at hu
          cases hsrc : τ.src with
          | none => rfl
          | some d' =>
            rw [hsrc] at hu; simp only at hu
            simp only [Option.getD_some]
            split_ifs at hu with h1 h2 <;> omega
        rwa [hz] at hh
      ht := fun _ k hk => by
        have : k = 0 := by simpa using hk
        subst this; rw [hleg0, hr]; simp
      steer := fun _ k _ hk => absurd hk (by simp) }
  · simp only [RS.put, hR, hJ]; exact invR_nil hd Y hL hH a e τ _ (by simp)
  · simp only [RS.put, hR, hJ, hT]; exact invJ_nil hd Y hL hH a e τ _ _ (by simp)
  · simp only [RS.put, hJ, hT, hg1, hg2, h1]; exact invT_nil hd Y hL hH a e _ (by simp)
  · simp [RS.put, h1]
  · simp only [RS.put, hg1, h1]; exact invB_nil hd Y hL hH a e _
  · simp only [RS.put, hg2, h2]; exact invB_nil hd Y hL hH a e _
  · simp [RS.put, h2]
  · simp [RS.put, h1]

/-- **A pre-steered top step of segment `A` preserves the invariant.** [cite: GrimmettPercolation1999, §7.3 pp. 172–173 (A), (D)] -/
theorem tallInv_topA (hY : Y.OK) {st : RS d} (hI : TallInv hd Y hL hH a e τ st)
    (hph : st.ph = Phase.segA) {r₀ : BrickRec d} {tl : List (BrickRec d)} (hA : st.sA = r₀ :: tl)
    (hlen : (r₀ :: tl).length ≤ Y.Pw) (hgood : GoodRec Y.m Y.L Y.H r₀) (o : Finset (Sym2 (Site d))) {sg : Fin d → Bool}
    (hsg : sg = if riseDir Y e τ = 0 then force (toward (nomA hd Y e τ) r₀.1.b) (latOf hd e) (jogDir a e)
      else force (toward (nomA hd Y e τ) r₀.1.b) (ax0 hd) (riseDir Y e τ)) :
    TallInv hd Y hL hH a e τ { st.put Slot.toA (tStep hL hH r₀ sg, o) with ph := Phase.segA } := by
  obtain ⟨hR, hJ, hT, h1, h2⟩ := phaseOf_eq_segA (hI.ph_eq ▸ hph)
  have hsg0 : riseDir Y e τ = 0 → sg = force (toward (nomA hd Y e τ) r₀.1.b) (latOf hd e) (jogDir a e) := fun hu => by
    rw [hsg, if_pos hu]
  have hsg1 : riseDir Y e τ ≠ 0 → sg = force (toward (nomA hd Y e τ) r₀.1.b) (ax0 hd) (riseDir Y e τ) := fun hu => by
    rw [hsg, if_neg hu]
  have hv : (jogDir a e : ℤ) = 1 ∨ (jogDir a e : ℤ) = -1 := by
    rcases Int.units_eq_one_or (jogDir a e) with h | h <;> simp [h]
  obtain ⟨hg1, hg2⟩ := hI.invT.gnil hT
  have hLp := hY.Lp_nonneg
  have hIA := hI.invA
  rw [hA] at hIA
  set r : BrickRec d := (tStep hL hH r₀ sg, o) with hr
  have hne : (r₀ :: tl) ≠ [] := List.cons_ne_nil _ _
  -- the old newest brick and its axis
  have hold : legOf (r₀ :: tl) tl.length = r₀.1 := legOf_cons_length r₀ tl
  have hzero := hIA.zero hne
  have hax0 : r₀.1.a = axOf hd e := by
    have := (hIA.grown hne).axis_sign (k := tl.length) (by simp)
    rw [hold, hzero] at this; exact this.1
  have hnew : legOf (r :: r₀ :: tl) (r₀ :: tl).length = r.1 := legOf_cons_length r _
  have hkeep : ∀ k < (r₀ :: tl).length, legOf (r :: r₀ :: tl) k = legOf (r₀ :: tl) k := fun k hk => legOf_cons_of_lt r _ hk
  have haf : latOf hd e ≠ r₀.1.a := by rw [hax0]; exact latOf_ne_axOf hd e
  have ha0 : ax0 hd ≠ r₀.1.a := by rw [hax0]; exact (axOf_ne_ax0 hd e).symm
  -- requests
  have hsg_oth : ∀ j, j ≠ latOf hd e → j ≠ ax0 hd → sg j = toward (nomA hd Y e τ) r₀.1.b j := by
    intro j hj1 hj2
    by_cases hu : riseDir Y e τ = 0
    · rw [hsg0 hu]; exact force_of_ne _ hj1 _
    · rw [hsg1 hu]; exact force_of_ne _ hj2 _
  have e1 : legOf (r :: r₀ :: tl) tl.length = r₀.1 := by rw [hkeep tl.length (by simp), hold]
  have e2 : legOf (r :: r₀ :: tl) (tl.length + 1) = r.1 := hnew
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [RS.put]; exact (phaseOf_of_nil (by simpa using hR) (by simpa using hJ) (by simpa using hT)
      (by simpa using h1) (by simpa using h2)).symm
  · simp only [RS.put, hA, hR, hJ]
    exact
    { len := by rw [List.length_cons]; omega
      full := by simp
      grown := fun _ => grown_cons hL hH (hIA.grown hne) rfl hgood sg o
      zero := fun _ => by rw [hkeep 0 (by simp)]; exact hzero
      lat := fun hu k hk => by
        rw [List.length_cons] at hk
        rcases Nat.lt_or_ge k (r₀ :: tl).length with hlt | hge
        · rw [hkeep k hlt]; exact hIA.lat hu k hlt
        · have hk' : k = (r₀ :: tl).length := by omega
          rw [hk', hnew, hr]
          have hreq : sg (latOf hd e) = toward (nomA hd Y e τ) r₀.1.b (latOf hd e) := by
            rw [hsg1 hu]; exact force_of_ne _ (latOf_ne_ax0 hd e) _
          have h1 := abs_sub_le_of_toward hL hH hgood haf hreq
          have hnom : nomA hd Y e τ (latOf hd e) = τ.pos (latOf hd e) := by simp [nomA]
          rw [hnom] at h1
          refine le_trans h1 (max_le ?_ le_rfl)
          have := hIA.lat hu tl.length (by simp)
          rwa [hold] at this
      lat0 := fun hu k hk => by
        rw [List.length_cons] at hk
        rcases Nat.lt_or_ge k (r₀ :: tl).length with hlt | hge
        · rw [hkeep k hlt]; exact hIA.lat0 hu k hlt
        · have hk' : k = (r₀ :: tl).length := by omega
          rw [hk', hnew, hr]
          have hreq : sg (latOf hd e) = decide (0 ≤ (jogDir a e : ℤ)) := by
            rw [hsg0 hu]; exact force_self _ _ _
          have h1 := forced_nonneg hL hH hgood haf hv hreq
          have h0 := hIA.lat0 hu tl.length (by simp)
          rw [hold] at h0
          have hsplit : (jogDir a e : ℤ) * ((tStep hL hH r₀ sg).b (latOf hd e) - τ.pos (latOf hd e)) =
              (jogDir a e : ℤ) * ((tStep hL hH r₀ sg).b (latOf hd e) - r₀.1.b (latOf hd e)) +
                (jogDir a e : ℤ) * (r₀.1.b (latOf hd e) - τ.pos (latOf hd e)) := by ring
          simp only [List.length_cons]; push_cast
          rw [hsplit]
          have hLp' : Y.Lp = (Y.L : ℤ) - Y.m - 1 := rfl
          constructor <;> nlinarith [h1.1, h1.2, h0.1, h0.2]
      latst := fun hu k _ hk => by
        simp only [List.length_cons, Nat.add_sub_cancel] at hk
        rcases Nat.lt_or_ge (k + 1) (r₀ :: tl).length with hlt | hge
        · rw [hkeep k (by omega), hkeep (k + 1) hlt]
          exact hIA.latst hu k (Nat.zero_le _) (by simp only [List.length_cons, Nat.add_sub_cancel] at hlt ⊢; omega)
        · have hk' : k = tl.length := by simp only [List.length_cons] at hge hk; omega
          subst hk'
          rw [e1, e2, hr]
          have hreq : sg (latOf hd e) = decide (0 ≤ (jogDir a e : ℤ)) := by
            rw [hsg0 hu]; exact force_self _ _ _
          exact (forced_nonneg hL hH hgood haf hv hreq).1
      oth := fun k hk j hj1 hj2 hj3 => by
        rw [List.length_cons] at hk
        rcases Nat.lt_or_ge k (r₀ :: tl).length with hlt | hge
        · rw [hkeep k hlt]; exact hIA.oth k hlt j hj1 hj2 hj3
        · have hk' : k = (r₀ :: tl).length := by omega
          rw [hk', hnew, hr]
          have hja : j ≠ r₀.1.a := by rw [hax0]; exact hj1
          have h1 := abs_sub_le_of_toward hL hH hgood hja (hsg_oth j hj2 hj3)
          have hnom : nomA hd Y e τ j = 0 := by simp [nomA, hj2, hj3]
          rw [hnom, sub_zero] at h1
          refine le_trans h1 (max_le ?_ le_rfl)
          have := hIA.oth tl.length (by simp) j hj1 hj2 hj3
          rwa [hold, ← sub_zero (r₀.1.b j)] at this
      ht0 := fun hu k hk => by
        rw [List.length_cons] at hk
        rcases Nat.lt_or_ge k (r₀ :: tl).length with hlt | hge
        · rw [hkeep k hlt]; exact hIA.ht0 hu k hlt
        · have hk' : k = (r₀ :: tl).length := by omega
          rw [hk', hnew, hr]
          have hreq : sg (ax0 hd) = toward (nomA hd Y e τ) r₀.1.b (ax0 hd) := by
            rw [hsg0 hu]; exact force_of_ne _ (latOf_ne_ax0 hd e).symm _
          have h1 := abs_sub_le_of_toward hL hH hgood ha0 hreq
          have hnom : nomA hd Y e τ (ax0 hd) = Y.zOf e := by simp [nomA, (latOf_ne_ax0 hd e).symm]
          rw [hnom] at h1
          refine le_trans h1 (max_le ?_ hY.Lp_le_ρv)
          have := hIA.ht0 hu tl.length (by simp)
          rwa [hold] at this
      ht := fun hu k hk => by
        rw [List.length_cons] at hk
        rcases Nat.lt_or_ge k (r₀ :: tl).length with hlt | hge
        · rw [hkeep k hlt]; exact hIA.ht hu k hlt
        · have hk' : k = (r₀ :: tl).length := by omega
          rw [hk', hnew, hr]
          have hreq : sg (ax0 hd) = decide (0 ≤ riseDir Y e τ) := by
            rw [hsg1 hu]; exact force_self _ _ _
          have hw : riseDir Y e τ = 1 ∨ riseDir Y e τ = -1 := (riseDir_cases Y e τ).resolve_left hu
          have h1 := forced_nonneg hL hH hgood ha0 hw hreq
          have h0 := hIA.ht hu tl.length (by simp)
          rw [hold] at h0
          have hsplit : riseDir Y e τ * ((tStep hL hH r₀ sg).b (ax0 hd) - τ.pos (ax0 hd)) =
              riseDir Y e τ * ((tStep hL hH r₀ sg).b (ax0 hd) - r₀.1.b (ax0 hd)) +
                riseDir Y e τ * (r₀.1.b (ax0 hd) - τ.pos (ax0 hd)) := by ring
          simp only [List.length_cons]; push_cast
          rw [hsplit]
          have hLp' : Y.Lp = (Y.L : ℤ) - Y.m - 1 := rfl
          constructor <;> nlinarith [h1.1, h1.2, h0.1, h0.2]
      steer := fun hu k _ hk => by
        simp only [List.length_cons, Nat.add_sub_cancel] at hk
        rcases Nat.lt_or_ge (k + 1) (r₀ :: tl).length with hlt | hge
        · rw [hkeep k (by omega), hkeep (k + 1) hlt]
          exact hIA.steer hu k (Nat.zero_le _) (by simp only [List.length_cons, Nat.add_sub_cancel] at hlt ⊢; omega)
        · have hk' : k = tl.length := by simp only [List.length_cons] at hge hk; omega
          subst hk'
          rw [e1, e2, hr]
          have hreq : sg (ax0 hd) = decide (0 ≤ riseDir Y e τ) := by
            rw [hsg1 hu]; exact force_self _ _ _
          have hw : riseDir Y e τ = 1 ∨ riseDir Y e τ = -1 := (riseDir_cases Y e τ).resolve_left hu
          exact (forced_nonneg hL hH hgood ha0 hw hreq).1 }
  · simp only [RS.put, hR, hJ]; exact invR_nil hd Y hL hH a e τ _ (by simp)
  · simp only [RS.put, hR, hJ, hT]; exact invJ_nil hd Y hL hH a e τ _ _ (by simp)
  · simp only [RS.put, hJ, hT, hg1, hg2, h1]; exact invT_nil hd Y hL hH a e _ (by simp)
  · simp [RS.put, h1]
  · simp only [RS.put, hg1, h1]; exact invB_nil hd Y hL hH a e _
  · simp only [RS.put, hg2, h2]; exact invB_nil hd Y hL hH a e _
  · simp [RS.put, h2]
  · simp [RS.put, h1]

end BGNd

end Percolation.Literature

end

namespace Percolation.Literature.BGNd

open LatticeModels Contour
open scoped Classical

variable {d : ℕ} [NeZero d]
variable (hd : 3 ≤ d) (Y : TallLayout) (hL : Y.m + 1 ≤ Y.L) (hH : 2 * Y.m + 2 ≤ Y.H) (a : Site 2) (e : MDir) (τ : TTok d)

/-- Changing the completion flag of the `A`-invariant. [folklore] -/
theorem InvA.of_full {sA : List (BrickRec d)} {D D' : Prop} (h : InvA hd Y hL hH a e τ sA D) (hfull : D' → sA.length = Y.Pw + 1) :
    InvA hd Y hL hH a e τ sA D' :=
  ⟨h.len, hfull, h.grown, h.zero, h.lat, h.lat0, h.latst, h.oth, h.ht0, h.ht, h.steer⟩

omit [NeZero d] in
/-- The riser unit agrees with the riser direction when there is a riser. [folklore] -/
theorem riseUnit_val (hu : riseDir Y e τ ≠ 0) : (riseUnit Y e τ : ℤ) = riseDir Y e τ := by
  unfold riseUnit
  rcases (riseDir_cases Y e τ).resolve_left hu with h | h <;> simp [h]

/-- `nForcedR n 0 = 0`. [folklore] -/
@[simp] theorem nForcedR_zero (n : ℕ) : nForcedR Y n 0 = 0 := by simp [nForcedR]

/-- **The turn into the riser preserves the invariant.** [cite: GrimmettPercolation1999, §7.3 pp. 172–173 (B)] -/
theorem tallInv_turnAR (hY : Y.OK) {st : RS d} (hI : TallInv hd Y hL hH a e τ st)
    (hph : st.ph = Phase.segA) {r₀ : BrickRec d} {tl : List (BrickRec d)} (hA : st.sA = r₀ :: tl)
    (hlen : (r₀ :: tl).length = Y.Pw + 1) (hu : riseDir Y e τ ≠ 0) (hgood : GoodRec Y.m Y.L Y.H r₀) (o : Finset (Sym2 (Site d))) :
    TallInv hd Y hL hH a e τ
      { st.put Slot.toR (sStep hL hH r₀ (ax0 hd) (if riseDir Y e τ = 1 then 1 else -1) (toward (nomA hd Y e τ) r₀.1.b), o) with
        ph := Phase.segR } := by
  obtain ⟨hR, hJ, hT, h1, h2⟩ := phaseOf_eq_segA (hI.ph_eq ▸ hph)
  obtain ⟨hg1, hg2⟩ := hI.invT.gnil hT
  have hLp := hY.Lp_nonneg
  have hIA := hI.invA
  rw [hA] at hIA
  set u' : ℤˣ := if riseDir Y e τ = 1 then 1 else -1 with hu'
  set r : BrickRec d := (sStep hL hH r₀ (ax0 hd) u' (toward (nomA hd Y e τ) r₀.1.b), o) with hr
  have hne : (r₀ :: tl) ≠ [] := List.cons_ne_nil _ _
  have hold : legOf (r₀ :: tl) tl.length = r₀.1 := legOf_cons_length r₀ tl
  have hzero := hIA.zero hne
  have haxs := (hIA.grown hne).axis_sign (k := tl.length) (by simp)
  rw [hold, hzero] at haxs
  obtain ⟨hax0, hs0⟩ := haxs
  simp only at hax0 hs0
  have hPw : Y.Pw = tl.length := by simp only [List.length_cons] at hlen; omega
  have hleg0 : legOf [r] 0 = r.1 := legOf_cons_length r []
  have ha0 : ax0 hd ≠ r₀.1.a := by rw [hax0]; exact (axOf_ne_ax0 hd e).symm
  have haf : latOf hd e ≠ r₀.1.a := by rw [hax0]; exact latOf_ne_axOf hd e
  have huu : u' = riseUnit Y e τ := by
    rw [hu']; unfold riseUnit
    rcases (riseDir_cases Y e τ).resolve_left hu with h | h <;> simp [h]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [RS.put]
    exact (phaseOf_of_R (by simp) (by simpa using hJ) (by simpa using hT) (by simpa using h1) (by simpa using h2)).symm
  · simp only [RS.put, hA, hJ]
    exact hIA.of_full hd Y hL hH a e τ fun _ => hlen
  · simp only [RS.put, hA, hR, hJ]
    exact
    { nil := fun h => absurd h hu
      prev := fun _ => hlen
      grown := fun _ => grown_singleton hL hH r
      turn := fun _ => by
        rw [hPw, hold, hleg0, hr, ← huu, ← hax0, ← hs0]
        exact isTurn_sStep hL hH hgood ha0 u' _
      sched := fun k hk => absurd hk (by simp)
      done := fun h => absurd h (by simp)
      fwd := fun k _ hk => absurd hk (by simp)
      lat := fun k hk => by
        have : k = 0 := by simpa using hk
        subst this
        rw [hleg0, hr, nForcedR_zero, Nat.cast_zero, zero_mul, add_zero]
        have h1 := abs_sub_le_of_toward_side hL hH hgood ha0 u' (nom := nomA hd Y e τ) haf (latOf_ne_ax0 hd e) rfl
        have hnom : nomA hd Y e τ (latOf hd e) = τ.pos (latOf hd e) := by simp [nomA]
        rw [hnom] at h1
        refine le_trans h1 (max_le ?_ le_rfl)
        have := hIA.lat hu tl.length (by simp)
        rwa [hold] at this
      latst := fun k _ hk => absurd hk (by simp)
      oth := fun k hk j hj1 hj2 hj3 => by
        have : k = 0 := by simpa using hk
        subst this
        rw [hleg0, hr]
        have hja : j ≠ r₀.1.a := by rw [hax0]; exact hj1
        have h1 := abs_sub_le_of_toward_side hL hH hgood ha0 u' (nom := nomA hd Y e τ) hja hj3 rfl
        have hnom : nomA hd Y e τ j = 0 := by simp [nomA, hj2, hj3]
        rw [hnom, sub_zero] at h1
        refine le_trans h1 (max_le ?_ le_rfl)
        have := hIA.oth tl.length (by simp) j hj1 hj2 hj3
        rwa [hold, ← sub_zero (r₀.1.b j)] at this }
  · simp only [RS.put, hA, hJ, hT]; exact invJ_nil hd Y hL hH a e τ _ _ (by simp)
  · simp only [RS.put, hJ, hT, hg1, hg2, h1]; exact invT_nil hd Y hL hH a e _ (by simp)
  · simp [RS.put, h1]
  · simp only [RS.put, hg1, h1]; exact invB_nil hd Y hL hH a e _
  · simp only [RS.put, hg2, h2]; exact invB_nil hd Y hL hH a e _
  · simp [RS.put, h2]
  · simp [RS.put, h1]

/-- **The turn into the jog, when there is no riser, preserves the invariant.** [cite: GrimmettPercolation1999, §7.3 pp. 172–173 (B)] -/
theorem tallInv_turnAJ (hY : Y.OK) {st : RS d} (hI : TallInv hd Y hL hH a e τ st)
    (hph : st.ph = Phase.segA) {r₀ : BrickRec d} {tl : List (BrickRec d)} (hA : st.sA = r₀ :: tl)
    (hlen : (r₀ :: tl).length = Y.Pw + 1) (hu : riseDir Y e τ = 0) (hgood : GoodRec Y.m Y.L Y.H r₀) (o : Finset (Sym2 (Site d))) :
    TallInv hd Y hL hH a e τ
      { st.put Slot.toJ (sStep hL hH r₀ (latOf hd e) (jogDir a e)
          (force (toward (nomT hd Y e (Y.lane (tgtCell a e) e)) r₀.1.b) (axOf hd e) (sgOf e)), o) with
        ph := Phase.segJ } := by
  obtain ⟨hR, hJ, hT, h1, h2⟩ := phaseOf_eq_segA (hI.ph_eq ▸ hph)
  obtain ⟨hg1, hg2⟩ := hI.invT.gnil hT
  have hLp := hY.Lp_nonneg
  have hIA := hI.invA
  rw [hA] at hIA
  set y := Y.lane (tgtCell a e) e with hy
  set sg := force (toward (nomT hd Y e y) r₀.1.b) (axOf hd e) (sgOf e) with hsg
  set r : BrickRec d := (sStep hL hH r₀ (latOf hd e) (jogDir a e) sg, o) with hr
  have hne : (r₀ :: tl) ≠ [] := List.cons_ne_nil _ _
  have hold : legOf (r₀ :: tl) tl.length = r₀.1 := legOf_cons_length r₀ tl
  have hzero := hIA.zero hne
  have haxs := (hIA.grown hne).axis_sign (k := tl.length) (by simp)
  rw [hold, hzero] at haxs
  obtain ⟨hax0, hs0⟩ := haxs
  simp only at hax0 hs0
  have hleg0 : legOf [r] 0 = r.1 := legOf_cons_length r []
  have ha0 : ax0 hd ≠ r₀.1.a := by rw [hax0]; exact (axOf_ne_ax0 hd e).symm
  have haf : latOf hd e ≠ r₀.1.a := by rw [hax0]; exact latOf_ne_axOf hd e
  have hEL : entryLast Y e τ (r₀ :: tl) [] = r₀.1 := by
    unfold entryLast; rw [if_pos hu, List.length_cons, Nat.add_sub_cancel, hold]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [RS.put]
    exact (phaseOf_of_J (by simp) (by simpa using hT) (by simpa using h1) (by simpa using h2)).symm
  · simp only [RS.put, hA, hR]
    exact hIA.of_full hd Y hL hH a e τ fun _ => hlen
  · simp only [RS.put, hA, hR]; exact invR_nil hd Y hL hH a e τ _ fun _ => hu
  · simp only [RS.put, hA, hR, hJ, hT]
    exact
    { prevA := fun _ => hlen
      prevR := fun _ h => absurd hu h
      grown := fun _ => grown_singleton hL hH r
      turn := fun _ => by
        rw [if_pos hu, if_pos hu, hEL, hleg0, hr, ← hax0, ← hs0]
        exact isTurn_sStep hL hH hgood haf (jogDir a e) _
      sched := fun k hk => absurd hk (by simp)
      done := fun h => absurd h (by simp)
      fwd := fun k _ hk => absurd hk (by simp)
      fwd0 := fun _ => by
        rw [hEL, hleg0, hr]
        have := (isTurn_sStep hL hH hgood haf (jogDir a e) sg).longit.1
        rw [hax0, hs0] at this
        have hm : (0 : ℤ) ≤ Y.m + 1 := by positivity
        simpa using le_trans (by positivity) this
      ht := fun k hk => by
        have : k = 0 := by simpa using hk
        subst this
        rw [hleg0, hr]
        have hreq : sg (ax0 hd) = toward (nomT hd Y e y) r₀.1.b (ax0 hd) := by
          rw [hsg]; exact force_of_ne _ (axOf_ne_ax0 hd e).symm _
        have h1 := abs_sub_le_of_toward_side hL hH hgood haf (jogDir a e) (nom := nomT hd Y e y) ha0 (latOf_ne_ax0 hd e).symm hreq
        have hnom : nomT hd Y e y (ax0 hd) = Y.zOf e := by simp [nomT, (latOf_ne_ax0 hd e).symm]
        rw [hnom] at h1
        refine le_trans h1 (max_le ?_ hY.Lp_le_ρv)
        have := hIA.ht0 hu tl.length (by simp)
        rwa [hold] at this
      oth := fun k hk j hj1 hj2 hj3 => by
        have : k = 0 := by simpa using hk
        subst this
        rw [hleg0, hr]
        have hja : j ≠ r₀.1.a := by rw [hax0]; exact hj1
        have hreq : sg j = toward (nomT hd Y e y) r₀.1.b j := by rw [hsg]; exact force_of_ne _ hj1 _
        have h1 := abs_sub_le_of_toward_side hL hH hgood haf (jogDir a e) (nom := nomT hd Y e y) hja hj2 hreq
        have hnom : nomT hd Y e y j = 0 := by simp [nomT, hj2, hj3]
        rw [hnom, sub_zero] at h1
        refine le_trans h1 (max_le ?_ le_rfl)
        have := hIA.oth tl.length (by simp) j hj1 hj2 hj3
        rwa [hold, ← sub_zero (r₀.1.b j)] at this }
  · simp only [RS.put, hJ, hT, hg1, hg2, h1]; exact invT_nil hd Y hL hH a e _ (by simp)
  · simp [RS.put, h1]
  · simp only [RS.put, hg1, h1]; exact invB_nil hd Y hL hH a e _
  · simp only [RS.put, hg2, h2]; exact invB_nil hd Y hL hH a e _
  · simp [RS.put, h2]
  · simp [RS.put, h1]

end Percolation.Literature.BGNd
