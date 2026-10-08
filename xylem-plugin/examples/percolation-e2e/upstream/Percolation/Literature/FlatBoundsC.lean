import Percolation.Literature.FlatDisjF
import Percolation.Util.Linter

/-!
# The flat gait, XVI–XVIII

This module gathers 3 consecutive parts of the flat-gait development, in order:
XVI: bounds, I — the riser, the heights, the idle coordinates ·
XVII: bounds, II — the lateral drift of a diagonal leg; plane windows ·
XVIII: bounds, III — the jog.
Part 1 follows; the later parts keep their own headers below.

# Part 1 (The flat gait, XVI): bounds, I — the riser, the heights, the idle coordinates

Quantitative consequences of the invariant of the flat
gait (Grimmett, *Percolation*, 2nd ed. (1999), §7.3 pp. 171–174, case `H < L`): the token is within
`3W + ρ_v` of the nominal height and the riser starts off the lead-in's head, at most `2L'` beyond
the token in height (`FlatInv.rstart_facts`), so the riser has at most `106` plates
(`FlatInv.riser_len_le`) and ends less than `U + H + 2L'` beyond the nominal height
(`FlatInv.riser_end`); its plates lie between the token's height and `U + H + 2L'` beyond the nominal
one (`FlatInv.riser_z`), and advance in the plane by at most `U` a hop (`Riser.plane_ub`); every
later plate is within `U + H + 2L' - 1` of the nominal height (`FlatInv.z_after`); every idle
coordinate of every plate is within `L'` of `0` (`FlatInv.idle_all`).

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §7.3 pp. 171–174.
-/

noncomputable section

namespace Percolation.Literature

open LatticeModels Contour
open scoped Classical

namespace BGNd

variable {d : ℕ} [NeZero d] {hd : 3 ≤ d} {Y : FlatLayout} {a : Site 2} {e : MDir} {τ : TTok d} {st : FS d}

/-! ## The riser's plane advance -/

/-- **Along a riser each plane coordinate advances by at most `U` a hop.** [folklore] -/
theorem Riser.plane_ub (hY : Y.OK) {σ : Fin 2 → ℤˣ} {u : ℤˣ} {q₀ : Fin 2} {s : BrickPos d} {l : List (BrickRec d)}
    (h : Riser hd Y σ u q₀ s l) {k : ℕ} (hk : k < l.length) (i : Fin 2) :
    ox hd σ i (legOf l k).b ≤ ox hd σ i s.b + ((k : ℤ) + 1) * Y.U := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  -- one hop: at most `U` along either plane coordinate
  have hss : ∀ w : ℤˣ, (w : ℤ) * (w : ℤ) = 1 := fun w => by rcases Int.units_eq_one_or w with h' | h' <;> simp [h']
  have one : ∀ k, (hk : k < l.length) → ox hd σ i (legOf l k).b ≤ ox hd σ i (if k = 0 then s else legOf l (k - 1)).b + Y.U := by
    intro k hk
    rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · -- a vertical plate: `VHop` off the previous plane plate (or the start)
      have hv : VHop hd Y (σ (oth (qAt q₀ j))) u (qAt q₀ j) (if j + j = 0 then s else legOf l (j + j - 1)) (legOf l (j + j)) := by
        rcases Nat.eq_zero_or_pos j with rfl | hj
        · simpa using h.start hk
        · have := h.up (j - 1) (by omega)
          rw [show j - 1 + 1 = j by omega, show 2 * (j - 1) + 1 = j + j - 1 by omega, show 2 * (j - 1) + 2 = j + j by omega] at this
          simpa [show j + j ≠ 0 by omega, show j ≠ 0 by omega] using this
      set P := (if j + j = 0 then s else legOf l (j + j - 1)) with hP
      have hPa : P.s = σ (qAt q₀ j) := by
        rcases Nat.eq_zero_or_pos j with rfl | hj
        · simp [hP, h.sSign]
        · simp only [hP, show j + j ≠ 0 by omega, if_false]
          have := (h.axis_sign (k := j + j - 1) (by omega)).2 (by omega)
          rw [show (j + j - 1) / 2 + 1 = j by omega] at this; exact this.2
      by_cases hi : i = qAt q₀ j
      · subst hi; have := hv.drift; rw [hPa] at this; unfold ox; nlinarith [this.1, this.2, hHU]
      · have hi' : i = oth (qAt q₀ j) := (eq_or_eq_oth i (qAt q₀ j)).resolve_left hi
        subst hi'; have := hv.push; unfold ox; nlinarith [this.1, this.2, hULp]
    · -- a landing: `PHop`
      have hp := h.land j hk
      simp only [show 2 * j + 1 ≠ 0 by omega, if_false, show 2 * j + 1 - 1 = 2 * j by omega]
      by_cases hi : i = qAt q₀ (j + 1)
      · subst hi; unfold ox; rw [hp.face, mul_add, ← mul_assoc, hss, one_mul]
      · have hi' : i = oth (qAt q₀ (j + 1)) := (eq_or_eq_oth i (qAt q₀ (j + 1))).resolve_left hi
        subst hi'; have := hp.push; unfold ox; nlinarith [this.1, this.2, hULp]
  induction k with
  | zero => have := one 0 hk; simp at this; simpa using this
  | succ k ih =>
    have := one (k + 1) hk
    simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel] at this
    have ih' := ih (by omega)
    push_cast at ih' ⊢; linarith

/-! ## The token's height and the riser direction -/

omit [NeZero d] in
/-- Layers differ by at most three pitches. [folklore] -/
theorem zOf_sub_zOf_abs (Y : FlatLayout) (e e' : MDir) : |Y.zOf e - Y.zOf e'| ≤ 3 * Y.Wl := by
  unfold FlatLayout.zOf TallLayout.layerIdx
  have hW : 0 ≤ Y.Wl := by unfold FlatLayout.Wl FlatLayout.U; positivity
  have h1 : (↑(2 * e.1.val + if e.2 then 0 else 1) : ℤ) ≤ 3 := by
    have := e.1.isLt; split_ifs <;> push_cast <;> omega
  have h2 : (↑(2 * e'.1.val + if e'.2 then 0 else 1) : ℤ) ≤ 3 := by
    have := e'.1.isLt; split_ifs <;> push_cast <;> omega
  have h3 : (0 : ℤ) ≤ ↑(2 * e.1.val + if e.2 then 0 else 1) := by positivity
  have h4 : (0 : ℤ) ≤ ↑(2 * e'.1.val + if e'.2 then 0 else 1) := by positivity
  rw [← sub_mul, abs_mul, abs_of_nonneg hW]
  apply mul_le_mul_of_nonneg_right _ hW
  rw [abs_le]; constructor <;> linarith

omit [NeZero d] in
/-- **The token is within `3W + ρ_v` of the nominal height.** [folklore] -/
theorem FTAdm.abs_zN_sub (hτ : FTAdm hd Y a e τ) : |zN Y e - τ.pos (ax0 hd)| ≤ 3 * Y.Wl + Y.ρv := by
  obtain ⟨d', hd'⟩ := Option.ne_none_iff_exists'.1 hτ.src_some
  have h1 := hτ.height d' hd'
  have h2 := zOf_sub_zOf_abs Y e d'
  unfold zN
  calc |Y.zOf e - τ.pos (ax0 hd)| = |(Y.zOf e - Y.zOf d') - (τ.pos (ax0 hd) - Y.zOf d')| := by ring_nf
    _ ≤ |Y.zOf e - Y.zOf d'| + |τ.pos (ax0 hd) - Y.zOf d'| := abs_sub _ _
    _ ≤ _ := by linarith

omit [NeZero d] in
/-- **The riser climbs towards the nominal height**: `u (z_N - z₀) = |z_N - z₀|`. [folklore] -/
theorem friseDir_mul_eq_abs (hd : 3 ≤ d) (Y : FlatLayout) (e : MDir) (τ : TTok d) :
    (friseDir hd Y e τ : ℤ) * (zN Y e - τ.pos (ax0 hd)) = |zN Y e - τ.pos (ax0 hd)| := by
  unfold friseDir
  split_ifs with h
  · rw [Units.val_one, one_mul, abs_of_pos (by linarith)]
  · rw [Units.val_neg, Units.val_one, neg_one_mul, abs_of_nonpos (by linarith)]

/-! ## The riser: length, end, heights -/

/-- The riser of an invariant state, off the lead-in's head. [folklore] -/
theorem FlatInv.riser (hI : FlatInv hd Y a e τ st) (h1 : st.segs 1 ≠ []) :
    Riser hd Y (dsg e) (friseDir hd Y e τ) (plIdx hd τ.ax) (rstart hd e τ (st.segs 0)) (st.segs 1) := by
  have hK : SegOK hd Y e τ (eJOf hd Y a e τ st) 1 (st.segs 1) (st.segs (startOf 1)) := hI.segOK 1
  simp only [SegOK, startOf, Fin.isValue, Matrix.cons_val] at hK
  exact hK h1

/-- **The riser's start, the lead-in's head**: the token's axis and sign; in height between the
token and `2L'` beyond it along the riser's direction; in the plane at least `U + m + 1` and
together at most `2U + 2H` beyond the token along both oriented coordinates, within `H` laterally;
idle coordinates within `L'`. [folklore] -/
theorem FlatInv.rstart_facts (hI : FlatInv hd Y a e τ st) (hY : Y.OK) (hτ : FTAdm hd Y a e τ) (h1 : st.segs 1 ≠ []) :
    (rstart hd e τ (st.segs 0)).a = pl hd (plIdx hd τ.ax) ∧ (rstart hd e τ (st.segs 0)).s = dsg e (plIdx hd τ.ax) ∧
      0 ≤ (friseDir hd Y e τ : ℤ) * ((rstart hd e τ (st.segs 0)).b (ax0 hd) - τ.pos (ax0 hd)) ∧
      (friseDir hd Y e τ : ℤ) * ((rstart hd e τ (st.segs 0)).b (ax0 hd) - τ.pos (ax0 hd)) ≤ 2 * Y.Lp ∧
      (∀ i, ox hd (dsg e) i τ.pos + (Y.U + Y.m + 1) ≤ ox hd (dsg e) i (rstart hd e τ (st.segs 0)).b) ∧
      upar hd (dsg e) (rstart hd e τ (st.segs 0)).b ≤ upar hd (dsg e) τ.pos + 2 * Y.U + 2 * Y.H ∧
      |(ox hd (dsg e) 0 (rstart hd e τ (st.segs 0)).b - ox hd (dsg e) 1 (rstart hd e τ (st.segs 0)).b) - (ox hd (dsg e) 0 τ.pos - ox hd (dsg e) 1 τ.pos)| ≤ Y.H ∧
      (∀ i, Idle hd i → |(rstart hd e τ (st.segs 0)).b i| ≤ Y.Lp) := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  have hc0 := hI.order 1 0 (by decide) h1
  obtain ⟨A, tlA, hl0, hh0⟩ := exists_head_of_ne_nil (l := st.segs 0) (by intro h; rw [h] at hc0; simp [complete'] at hc0)
  have hK0 : SegOK hd Y e τ (eJOf hd Y a e τ st) 0 (st.segs 0) (st.segs (startOf 0)) := hI.segOK 0
  simp only [SegOK, startOf, Fin.isValue, Matrix.cons_val] at hK0
  obtain ⟨hD, hfirst, hlen3⟩ := hK0 (by rw [hl0]; simp)
  simp only [complete', kindOf, Fin.isValue, Matrix.cons_val, hl0] at hc0
  have hlen : (st.segs 0).length = 3 := by rw [hl0] at hlen3 ⊢; simp at hc0 hlen3 ⊢; omega
  have hrs : rstart hd e τ (st.segs 0) = legOf (st.segs 0) 2 := by
    rw [show (2 : ℕ) = (st.segs 0).length - 1 by omega, legOf_last_of_head hh0]; simp [rstart, hh0]
  rw [hrs]
  have hfp : (firstPlate hd e τ).b = τ.pos := rfl
  obtain ⟨ha2, hs2⟩ := hD.axis_sign (k := 2) (by omega)
  have hq2 : qAt (plIdx hd τ.ax) 2 = plIdx hd τ.ax := by rw [show qAt (plIdx hd τ.ax) 2 = qAt (plIdx hd τ.ax) (0 + 2) from rfl, qAt_add_two, qAt_zero]
  rw [hq2] at ha2 hs2
  -- the two hops
  obtain ⟨f1, d1, d1'⟩ := hD.step (k := 0) (by omega)
  obtain ⟨f2, d2, d2'⟩ := hD.step (k := 1) (by omega)
  have hq1 : qAt (plIdx hd τ.ax) 1 = oth (plIdx hd τ.ax) := by rw [show qAt (plIdx hd τ.ax) 1 = qAt (plIdx hd τ.ax) (0 + 1) from rfl, qAt_succ, qAt_zero]
  simp only [show (0 : ℕ) + 1 = 1 from rfl, hq1, qAt_zero, hfirst, hfp] at f1 d1 d1'
  simp only [show (1 : ℕ) + 1 = 2 from rfl, hq2, hq1] at f2 d2 d2'
  have hz := hD.height_dir (u := friseDir hd Y e τ) rfl (k := 0) (k' := 2) (by omega) (by omega)
  rw [hfirst, hfp] at hz
  have hidle := hD.idle_le (by rw [hfirst]; exact fun i hi => hτ.idle i hi) (k := 2) (by omega)
  refine ⟨ha2, hs2, hz.1, by have := hz.2; push_cast at this; linarith, fun i => ?_, ?_, ?_, hidle⟩
  · rcases eq_or_eq_oth i (plIdx hd τ.ax) with hi | hi <;> rw [hi] <;> linarith
  · unfold upar
    rcases Fin.exists_fin_two.1 ⟨plIdx hd τ.ax, rfl⟩ with hq | hq <;> rw [hq] at f1 d1 d1' f2 d2 d2' <;>
      simp only [show oth (0 : Fin 2) = 1 from rfl, show oth (1 : Fin 2) = 0 from rfl] at f1 d1 d1' f2 d2 d2' <;> linarith
  · rcases Fin.exists_fin_two.1 ⟨plIdx hd τ.ax, rfl⟩ with hq | hq <;> rw [hq] at f1 d1 d1' f2 d2 d2' <;>
      simp only [show oth (0 : Fin 2) = 1 from rfl, show oth (1 : Fin 2) = 0 from rfl] at f1 d1 d1' f2 d2 d2' <;> rw [abs_le] <;> constructor <;> linarith

/-- **A landing of the riser that is not its head does not fit**: the riser was not complete
before its last record. [folklore] -/
theorem FlatInv.riser_land_not_fit (hI : FlatInv hd Y a e τ st) {j : ℕ} (hj : 2 * j + 2 < (st.segs 1).length) :
    0 < (friseDir hd Y e τ : ℤ) * (zN Y e - (legOf (st.segs 1) (2 * j + 1)).b (ax0 hd)) := by
  -- the stage of the riser of length `2j + 2` is a proper suffix with a landing head
  set l := st.segs 1 with hl
  have hsuf : l.drop (l.length - (2 * j + 2)) <:+ l := List.drop_suffix _ _
  have hlen : (l.drop (l.length - (2 * j + 2))).length = 2 * j + 2 := by rw [List.length_drop]; omega
  have hne : l.drop (l.length - (2 * j + 2)) ≠ l := by
    intro h; have := congrArg List.length h; rw [hlen] at this; omega
  have hnc := hI.nostop 1 _ hsuf hne
  -- its head is the landing `legOf l (2j+1)`
  obtain ⟨r, tl, hrt⟩ : ∃ r tl, l.drop (l.length - (2 * j + 2)) = r :: tl := by
    rcases hh : l.drop (l.length - (2 * j + 2)) with _ | ⟨r, tl⟩
    · rw [hh] at hlen; simp at hlen
    · exact ⟨r, tl, rfl⟩
  have hln : l.length - (2 * j + 2) < l.length := by omega
  have hr : r.1 = legOf l (2 * j + 1) := by
    have h1 : l[l.length - (2 * j + 2)]? = some r := by rw [← List.head?_drop, hrt]; rfl
    rw [List.getElem?_eq_getElem hln, Option.some.injEq] at h1
    unfold legOf recOf
    rw [List.getElem?_reverse (by omega), show l.length - 1 - (2 * j + 1) = l.length - (2 * j + 2) by omega,
      List.getElem?_eq_getElem hln, h1]
    rfl
  have hR := hI.riser (by rw [← hl]; exact List.ne_nil_of_length_pos (by omega))
  rw [← hl] at hR
  have hax := ((hR.axis_sign (k := 2 * j + 1) (by omega)).2 (by omega)).1
  simp only [complete', kindOf, Fin.isValue, Matrix.cons_val, hrt, hr, ffitsR, not_and, not_le] at hnc
  exact hnc (by rw [hax]; exact pl_ne_ax0 hd _)

/-- **The riser has at most `106` plates.** [cite: GrimmettPercolation1999, §7.3 p. 174 (the bound `R`)] -/
theorem FlatInv.riser_len_le (hI : FlatInv hd Y a e τ st) (hY : Y.OK) (hτ : FTAdm hd Y a e τ) : (st.segs 1).length ≤ 106 := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  by_contra hlen
  push Not at hlen
  have h1 : st.segs 1 ≠ [] := List.ne_nil_of_length_pos (by omega)
  -- the landing `legOf l 103 = legOf l (2·51+1)` is not the head and does not fit
  have hnf := hI.riser_land_not_fit (j := 51) (by omega)
  -- but it is at least `52 (U + m + 1)` above the start along `u`, and the start is at most `52 U` below `zN`
  have hlev := ((hI.riser h1).level.1 51 (by omega)).1
  obtain ⟨-, -, hs0, -, -⟩ := hI.rstart_facts hY hτ h1
  have habs := hτ.abs_zN_sub
  have hu := friseDir_mul_eq_abs hd Y e τ
  unfold FlatLayout.Wl FlatLayout.ρv at habs
  push_cast at hlev
  nlinarith [hlev, habs, hu, hnf, hm0, hU, hs0]

/-- **The riser ends less than `U + H + 2L'` beyond the nominal height** (along `u`), once
complete (the start being at most `2L'` beyond the token, which is not beyond `z_N`). [folklore] -/
theorem FlatInv.riser_end (hI : FlatInv hd Y a e τ st) (hY : Y.OK) (hτ : FTAdm hd Y a e τ) (hc : complete' hd Y a e τ (eJOf hd Y a e τ st) 1 (st.segs 1)) :
    0 ≤ (friseDir hd Y e τ : ℤ) * ((legOf (st.segs 1) ((st.segs 1).length - 1)).b (ax0 hd) - zN Y e) ∧
      (friseDir hd Y e τ : ℤ) * ((legOf (st.segs 1) ((st.segs 1).length - 1)).b (ax0 hd) - zN Y e) < Y.U + Y.H + 2 * Y.Lp := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  set l := st.segs 1 with hl
  obtain ⟨r, tl, hrt, -⟩ : ∃ r tl, l = r :: tl ∧ l.head? = some r := by
    rcases hh : l with _ | ⟨r, tl⟩
    · simp [complete', kindOf, hh] at hc
    · exact ⟨r, tl, rfl, rfl⟩
  have h1 : st.segs 1 ≠ [] := by rw [← hl, hrt]; simp
  simp only [complete', kindOf, Fin.isValue, Matrix.cons_val, hrt, ffitsR] at hc
  obtain ⟨hax, hfit⟩ := hc
  have hR := hI.riser h1
  obtain ⟨-, -, hs0, hs1, -⟩ := hI.rstart_facts hY hτ h1
  rw [← hl] at hR
  have hlast : legOf l (l.length - 1) = r.1 := by rw [hrt]; exact legOf_cons_length r tl
  -- the head is a landing: odd index
  have hodd : (l.length - 1) % 2 = 1 := by
    by_contra h0
    have := ((hR.axis_sign (k := l.length - 1) (by rw [hrt]; simp)).1 (by omega)).1
    rw [hlast] at this; exact hax this
  have hlpos : 0 < l.length := by rw [hrt]; simp
  obtain ⟨j, hj⟩ : ∃ j, l.length = 2 * j + 2 := ⟨(l.length - 1) / 2, by omega⟩
  have hidx : l.length - 1 = 2 * j + 1 := by omega
  rw [hidx] at hlast ⊢
  rw [← hlast] at hfit
  have hu := friseDir_mul_eq_abs hd Y e τ
  have huu : (friseDir hd Y e τ : ℤ) * (friseDir hd Y e τ : ℤ) = 1 := by
    rcases Int.units_eq_one_or (friseDir hd Y e τ) with h' | h' <;> simp [h']
  refine ⟨by nlinarith [hfit], ?_⟩
  -- the pair climbs by less than `U + H` above the previous landing (or the start), which did not fit
  have hz2 := hR.uz.1 j (by omega)
  have hz3 := (hR.uz.2 j (by omega)).2
  rcases Nat.eq_zero_or_pos j with rfl | hjpos
  · -- first pair: previous is the start, at most `2L'` beyond the token, `u (zN - z₀) ≥ 0`
    simp only [Riser.prev, if_true] at hz2
    have h0 : 0 ≤ (friseDir hd Y e τ : ℤ) * (zN Y e - τ.pos (ax0 hd)) := by rw [hu]; exact abs_nonneg _
    nlinarith [hz2, hz3, h0, hm0, hs1]
  · have hprev : Riser.prev (rstart hd e τ (st.segs 0)) l j = legOf l (2 * (j - 1) + 1) := by
      unfold Riser.prev; rw [if_neg (by omega)]; congr 1; omega
    rw [hprev] at hz2
    have hnf := hI.riser_land_not_fit (j := j - 1) (by rw [← hl]; omega)
    rw [← hl] at hnf
    nlinarith [hz2, hz3, hnf, hm0, hLp0]

/-- **Heights along the riser**: every plate is at least `U` beyond the token along `u`, and less
than `|z_N - z₀| + U + H + 2L'` beyond it. [folklore] -/
theorem FlatInv.riser_z (hI : FlatInv hd Y a e τ st) (hY : Y.OK) (hτ : FTAdm hd Y a e τ) {k : ℕ} (hk : k < (st.segs 1).length) :
    Y.U ≤ (friseDir hd Y e τ : ℤ) * ((legOf (st.segs 1) k).b (ax0 hd) - τ.pos (ax0 hd)) ∧
      (friseDir hd Y e τ : ℤ) * ((legOf (st.segs 1) k).b (ax0 hd) - τ.pos (ax0 hd)) < |zN Y e - τ.pos (ax0 hd)| + Y.U + Y.H + 2 * Y.Lp := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  have h1 : st.segs 1 ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hR := hI.riser h1
  obtain ⟨-, -, hs0, hs1, -⟩ := hI.rstart_facts hY hτ h1
  have hu := friseDir_mul_eq_abs hd Y e τ
  -- the vertical plate `2j` and the landing `2j+1` of pair `j`
  have pair : ∀ j, (hj : 2 * j < (st.segs 1).length) →
      Y.U ≤ (friseDir hd Y e τ : ℤ) * ((legOf (st.segs 1) (2 * j)).b (ax0 hd) - τ.pos (ax0 hd)) ∧
      (friseDir hd Y e τ : ℤ) * ((legOf (st.segs 1) (2 * j)).b (ax0 hd) - τ.pos (ax0 hd)) ≤ |zN Y e - τ.pos (ax0 hd)| + Y.U + 2 * Y.Lp := by
    intro j hj
    have hz2 := hR.uz.1 j hj
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · simp only [Riser.prev, if_true] at hz2
      constructor <;> nlinarith [hz2, abs_nonneg (zN Y e - τ.pos (ax0 hd)), hs0, hs1]
    · have hprev : Riser.prev (rstart hd e τ (st.segs 0)) (st.segs 1) j = legOf (st.segs 1) (2 * (j - 1) + 1) := by
        unfold Riser.prev; rw [if_neg (by omega)]; congr 1; omega
      rw [hprev] at hz2
      have hnf := hI.riser_land_not_fit (j := j - 1) (by omega)
      have hlev := (hR.level.1 (j - 1) (by omega)).1
      constructor <;> nlinarith [hz2, hnf, hlev, hm0, hU, hu, hs0, hs1, hLp0]
  rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · have := pair j (by omega); rw [← two_mul]
    exact ⟨this.1, by linarith⟩
  · have hp := pair j (by omega)
    have hz3 := hR.uz.2 j hk
    constructor <;> nlinarith [hp.1, hp.2, hz3.1, hz3.2, hm0]

/-! ## Propagating a bound through a segment -/

section Propagate

variable {σ σ' : Fin 2 → ℤˣ} {q p : Fin 2} {s : BrickPos d} {l : List (BrickRec d)}

/-- **Heights along a turn** stay within `Z ≥ L'` of the nominal height if the start is. [folklore] -/
theorem Turn.height (h : Turn hd Y e σ σ' p s l) {Z : ℤ} (hZ : Y.Lp ≤ Z) (h0 : |s.b (ax0 hd) - zN Y e| ≤ Z) {k : ℕ} (hk : k < l.length) :
    |(legOf l k).b (ax0 hd) - zN Y e| ≤ Z := by
  have hlen := h.len
  have h0' : |(legOf l 0).b (ax0 hd) - zN Y e| ≤ Z := ((h.h0 (by omega)).zt).trans (max_le h0 hZ)
  have hk2 : k < 2 := by omega
  interval_cases k
  · exact h0'
  · exact ((h.h1 (by omega)).zt rfl).trans (max_le h0' hZ)

/-- **Idle coordinates along a turn** stay within `L'`. [folklore] -/
theorem Turn.idle_le (h : Turn hd Y e σ σ' p s l) (h0 : ∀ i, Idle hd i → |s.b i| ≤ Y.Lp) {k : ℕ} (hk : k < l.length) :
    ∀ i, Idle hd i → |(legOf l k).b i| ≤ Y.Lp := by
  have hlen := h.len
  have h0' : ∀ i, Idle hd i → |(legOf l 0).b i| ≤ Y.Lp := fun i hi => ((h.h0 (by omega)).idle i hi).trans (max_le (h0 i hi) le_rfl)
  have hk2 : k < 2 := by omega
  interval_cases k
  · exact h0'
  · intro i hi; exact ((h.h1 (by omega)).idle i hi).trans (max_le (h0' i hi) le_rfl)

/-- **Heights along a leg hopped off a start** within `Z ≥ L'` of the nominal height. [folklore] -/
theorem DiagLeg.height_of_start (h : DiagLeg hd Y e σ none q l) (h0 : DHop hd Y e σ none q s (legOf l 0)) {Z : ℤ} (hZ : Y.Lp ≤ Z)
    (hs : |s.b (ax0 hd) - zN Y e| ≤ Z) {k : ℕ} (hk : k < l.length) : |(legOf l k).b (ax0 hd) - zN Y e| ≤ Z :=
  h.height hZ ((h0.zt rfl).trans (max_le hs hZ)) hk

/-- **Idle coordinates along a leg hopped off a start** within `L'`. [folklore] -/
theorem DiagLeg.idle_of_start (h : DiagLeg hd Y e σ none q l) (h0 : DHop hd Y e σ none q s (legOf l 0))
    (hs : ∀ i, Idle hd i → |s.b i| ≤ Y.Lp) {k : ℕ} (hk : k < l.length) : ∀ i, Idle hd i → |(legOf l k).b i| ≤ Y.Lp :=
  h.idle_le (fun i hi => (h0.idle i hi).trans (max_le (hs i hi) le_rfl)) hk

/-- **Idle coordinates along a riser** stay within `L'`. [folklore] -/
theorem Riser.idle_le {u : ℤˣ} {q₀ : Fin 2} (h : Riser hd Y σ u q₀ s l) (h0 : ∀ i, Idle hd i → |s.b i| ≤ Y.Lp) {k : ℕ} (hk : k < l.length) :
    ∀ i, Idle hd i → |(legOf l k).b i| ≤ Y.Lp := by
  induction k with
  | zero => intro i hi; exact ((h.start hk).idle i hi).trans (max_le (h0 i hi) le_rfl)
  | succ k ih =>
    intro i hi
    have ih' := ih (by omega) i hi
    rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · -- `k + 1 = 2j + 1`: a landing
      have := h.land j (by omega)
      rw [show j + j = 2 * j by ring] at ih' ⊢
      exact (this.idle i hi).trans (max_le ih' le_rfl)
    · -- `k + 1 = 2j + 2`: a vertical plate
      have := h.up j (by omega)
      exact (this.idle i hi).trans (max_le ih' le_rfl)

end Propagate

/-! ## Heights after the riser, idle coordinates everywhere -/

/-- A property of plates propagated through the segments after the riser: if it holds for the head
of a segment's start segment, it holds along the segment. [folklore] -/
theorem FlatInv.propagate (hI : FlatInv hd Y a e τ st) {P : BrickPos d → Prop}
    (hturn : ∀ {σ σ' : Fin 2 → ℤˣ} {p : Fin 2} {s : BrickPos d} {l : List (BrickRec d)}, Turn hd Y e σ σ' p s l → P s → ∀ k < l.length, P (legOf l k))
    (hleg : ∀ {σ : Fin 2 → ℤˣ} {q : Fin 2} {s : BrickPos d} {l : List (BrickRec d)}, DiagLeg hd Y e σ none q l → DHop hd Y e σ none q s (legOf l 0) → P s →
      ∀ k < l.length, P (legOf l k))
    (h1 : complete' hd Y a e τ (eJOf hd Y a e τ st) 1 (st.segs 1) → ∀ s₀, (st.segs 1).head? = some s₀ → P s₀.1) (k : Fin 13) (hk2 : 2 ≤ k.val) :
    ∀ r ∈ st.segs k, P r.1 := by
  -- strong induction on the segment index
  suffices H : ∀ n (k : Fin 13), k.val = n → 2 ≤ n → ∀ r ∈ st.segs k, P r.1 from H k.val k rfl hk2
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro k hkn hn r hr
    have hne : st.segs k ≠ [] := List.ne_nil_of_mem hr
    -- the start segment is earlier, complete, hence nonempty, and satisfies `P` at its head
    have hso : (startOf k).val < k.val ∧ 1 ≤ (startOf k).val := by
      have hk13 := k.isLt
      rcases k with ⟨kv, _⟩
      simp only at hkn hk13 ⊢; subst hkn
      interval_cases kv <;> simp [startOf]
    have hcs := hI.order k (startOf k) (Fin.lt_def.2 hso.1) hne
    obtain ⟨s₀, tl, hl₀, hh₀⟩ : ∃ s₀ tl, st.segs (startOf k) = s₀ :: tl ∧ (st.segs (startOf k)).head? = some s₀ := by
      rcases hl : st.segs (startOf k) with _ | ⟨s₀, tl⟩
      · rw [hl] at hcs; simp [complete'] at hcs
      · exact ⟨s₀, tl, rfl, rfl⟩
    have hPs : P s₀.1 := by
      by_cases h1s : (startOf k).val = 1
      · have : startOf k = 1 := Fin.ext h1s
        rw [this] at hh₀ hcs; exact h1 hcs s₀ hh₀
      · exact ih (startOf k).val (by omega) (startOf k) rfl (by omega) s₀ (by rw [hl₀]; simp)
    -- the segment's structure
    obtain ⟨j, hj, hjr⟩ := exists_legOf_of_mem hr
    rw [← hjr]
    have hK := hI.segOK k
    have hk13 := k.isLt
    rcases k with ⟨kv, _⟩
    simp only at hkn hk13 hK hh₀ hne hj ⊢; subst hkn
    interval_cases kv <;> simp only [SegOK, startOf, Fin.isValue] at hK hh₀ <;> rw [hh₀] at hK
    · obtain ⟨s, hs, q, hD, hD0⟩ := hK hne; simp at hs; subst hs; exact hleg hD hD0 hPs j hj
    · obtain ⟨s, hs, hT⟩ := hK hne; simp at hs; subst hs; exact hturn hT hPs j hj
    · obtain ⟨s, hs, hD, hD0⟩ := hK hne; simp at hs; subst hs; exact hleg hD hD0 hPs j hj
    · obtain ⟨s, hs, hT⟩ := hK hne; simp at hs; subst hs; exact hturn hT hPs j hj
    · obtain ⟨s, hs, hD, hD0⟩ := hK hne; simp at hs; subst hs; exact hleg hD hD0 hPs j hj
    · obtain ⟨s, hs, hT⟩ := hK hne; simp at hs; subst hs; exact hturn hT hPs j hj
    · obtain ⟨s, hs, q, hD, hD0⟩ := hK hne; simp at hs; subst hs; exact hleg hD hD0 hPs j hj
    · obtain ⟨s, hs, hT⟩ := hK hne; simp at hs; subst hs; exact hturn hT hPs j hj
    · obtain ⟨s, hs, q, hD, hD0⟩ := hK hne; simp at hs; subst hs; exact hleg hD hD0 hPs j hj
    · obtain ⟨s, hs, hD, hD0⟩ := hK hne; simp at hs; subst hs; exact hleg hD hD0 hPs j hj
    · obtain ⟨s, hs, hD, hD0⟩ := hK hne; simp at hs; subst hs; exact hleg hD hD0 hPs j hj

/-- **After the riser every plate is within `U + H - 1` of the nominal height.** [folklore] -/
theorem FlatInv.z_after (hI : FlatInv hd Y a e τ st) (hY : Y.OK) (hτ : FTAdm hd Y a e τ) (k : Fin 13) (hk2 : 2 ≤ k.val) :
    ∀ r ∈ st.segs k, |r.1.b (ax0 hd) - zN Y e| ≤ Y.U + Y.H + 2 * Y.Lp - 1 := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  have hZ : Y.Lp ≤ Y.U + Y.H + 2 * Y.Lp - 1 := by linarith
  by_cases h2 : st.segs 2 = []
  · -- nothing after the riser yet
    intro r hr
    have hne : st.segs k ≠ [] := List.ne_nil_of_mem hr
    rcases Nat.eq_or_lt_of_le hk2 with h | h
    · have : k = 2 := Fin.ext h.symm
      rw [this, h2] at hr; simp at hr
    · have := hI.order k 2 (Fin.lt_def.2 (by simpa using h)) hne
      rw [h2] at this; simp [complete'] at this
  · -- the riser is complete: its head is within `U + H - 1`
    have hc1 := hI.order 2 1 (by decide) h2
    have hend := hI.riser_end hY hτ hc1
    refine hI.propagate (P := fun β => |β.b (ax0 hd) - zN Y e| ≤ Y.U + Y.H + 2 * Y.Lp - 1)
      (fun hT hs k hk => hT.height hZ hs hk) (fun hD hD0 hs k hk => hD.height_of_start hD0 hZ hs hk) ?_ k hk2
    intro _ s₀ hs₀
    obtain ⟨tl, hl⟩ : ∃ tl, st.segs 1 = s₀ :: tl := by
      rcases hh : st.segs 1 with _ | ⟨r0, tl⟩
      · rw [hh] at hs₀; simp at hs₀
      · rw [hh] at hs₀; simp only [List.head?_cons, Option.some.injEq] at hs₀; subst hs₀; exact ⟨tl, rfl⟩
    have hlast : legOf (st.segs 1) ((st.segs 1).length - 1) = s₀.1 := by rw [hl]; exact legOf_cons_length s₀ tl
    rw [← hlast]
    have huu : ∀ x : ℤ, |x| = |(friseDir hd Y e τ : ℤ) * x| := fun x => by
      rcases Int.units_eq_one_or (friseDir hd Y e τ) with h' | h' <;> simp [h']
    rw [huu, abs_le]; constructor <;> nlinarith [hend.1, hend.2]

/-- **Every idle coordinate of every plate is within `L'` of `0`.** [folklore] -/
theorem FlatInv.idle_all (hI : FlatInv hd Y a e τ st) (hτ : FTAdm hd Y a e τ) {r : BrickRec d} (hr : r ∈ st.all) :
    ∀ i, Idle hd i → |r.1.b i| ≤ Y.Lp := by
  have h0 : ∀ i, Idle hd i → |(firstPlate hd e τ).b i| ≤ Y.Lp := fun i hi => hτ.idle i hi
  have hA : ∀ r ∈ st.segs 0, ∀ i, Idle hd i → |r.1.b i| ≤ Y.Lp := by
    intro r hr
    have hS : SegOK hd Y e τ (eJOf hd Y a e τ st) 0 (st.segs 0) (st.segs (startOf 0)) := hI.segOK 0
    simp only [SegOK, startOf, Fin.isValue, Matrix.cons_val] at hS
    obtain ⟨hD, hfirst, -⟩ := hS (List.ne_nil_of_mem hr)
    obtain ⟨j, hj, hjr⟩ := exists_legOf_of_mem hr
    rw [← hjr]; exact hD.idle_le (by rw [hfirst]; exact h0) hj
  have hR : ∀ r ∈ st.segs 1, ∀ i, Idle hd i → |r.1.b i| ≤ Y.Lp := by
    intro r hr
    have h1 : st.segs 1 ≠ [] := List.ne_nil_of_mem hr
    have hs0 : ∀ i, Idle hd i → |(rstart hd e τ (st.segs 0)).b i| ≤ Y.Lp := by
      have hc0 := hI.order 1 0 (by decide) h1
      obtain ⟨A, tlA, hl0, hh0⟩ := exists_head_of_ne_nil (l := st.segs 0) (by intro h; rw [h] at hc0; simp [complete'] at hc0)
      have : rstart hd e τ (st.segs 0) = A.1 := by simp [rstart, hh0]
      rw [this]; exact hA A (by rw [hl0]; simp)
    obtain ⟨j, hj, hjr⟩ := exists_legOf_of_mem hr
    rw [← hjr]; exact (hI.riser h1).idle_le hs0 hj
  unfold FS.all at hr
  simp only [List.mem_flatMap, List.mem_finRange, true_and] at hr
  obtain ⟨k, hk⟩ := hr
  by_cases hk0 : k = 0
  · subst hk0; exact hA r hk
  by_cases hk1 : k = 1
  · subst hk1; exact hR r hk
  have hk2 : 2 ≤ k.val := by
    have : k.val ≠ 0 := fun h => hk0 (Fin.ext h)
    have : k.val ≠ 1 := fun h => hk1 (Fin.ext h)
    omega
  refine hI.propagate (P := fun β => ∀ i, Idle hd i → |β.b i| ≤ Y.Lp)
    (fun hT hs k hk => hT.idle_le hs hk) (fun hD hD0 hs k hk => hD.idle_of_start hD0 hs hk) ?_ k hk2 r hk
  intro _ s₀ hs₀
  exact hR s₀ (List.mem_of_mem_head? hs₀)

end BGNd

end Percolation.Literature

end

/-!
# Part 2 (The flat gait, XVII): bounds, II — the lateral drift of a diagonal leg; plane windows

The second half of the quantitative analysis of the
flat gait (Grimmett, *Percolation*, 2nd ed. (1999), §7.3 pp. 171–174, case `H < L`). Along a
diagonal leg the forward diagonal coordinate `upar` advances by `U + t` a hop (`t < H` the forced
drift), while the lateral one `vperp` changes by `±(U - t)` with alternating signs, so that over a
pair of hops it drifts by less than `H` (`DiagLeg.vperp_dev`): the lateral drift of a leg of `k`
hops is at most `k H / 2 + U`. With the sign relations of the jog and of the branches
(`upar_vperp_flip0`, `upar_vperp_flip1`) this controls every segment; we derive the plane windows
of the token, the riser and the preamble here (`FTAdm.windows`, `FlatInv.win_riser`,
`FlatInv.win_pre`, `FlatInv.pre_len`).

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §7.3 pp. 171–174.
-/

noncomputable section

namespace Percolation.Literature

open LatticeModels Contour
open scoped Classical

namespace BGNd

variable {d : ℕ} [NeZero d] {hd : 3 ≤ d} {Y : FlatLayout} {a : Site 2} {e : MDir} {τ : TTok d} {st : FS d}

/-! ## The lateral diagonal coordinate -/

/-- **The lateral diagonal coordinate** read along the signs `σ`: `ox₀ - ox₁`. [folklore] -/
def vperp (hd : 3 ≤ d) (σ : Fin 2 → ℤˣ) (b : Site d) : ℤ := ox hd σ 0 b - ox hd σ 1 b

omit [NeZero d] in
/-- The lateral coordinate of the target cell's frame: `Uc_lat = s · vperp`. [folklore] -/
theorem Uc_lat_eq_vperp (hd : 3 ≤ d) (e : MDir) (b : Site d) : Uc hd (latDir e true).1 b = (sgOf e : ℤ) * vperp hd (dsg e) b := by
  rw [Uc_lat_dsg]; rfl

omit [NeZero d] in
/-- **Flipping the sign of index `0`** (the first branch): forward and lateral coordinates swap with
a sign. [folklore] -/
theorem upar_vperp_flip0 (hd : 3 ≤ d) {σ σ' : Fin 2 → ℤˣ} (h0 : σ' 0 = -σ 0) (h1 : σ' 1 = σ 1) (b : Site d) :
    upar hd σ' b = -vperp hd σ b ∧ vperp hd σ' b = -upar hd σ b := by
  unfold upar vperp ox; rw [h0, h1]; push_cast; constructor <;> ring

omit [NeZero d] in
/-- **Flipping the sign of index `1`** (the jog with kept index `0`, the second branch). [folklore] -/
theorem upar_vperp_flip1 (hd : 3 ≤ d) {σ σ' : Fin 2 → ℤˣ} (h0 : σ' 0 = σ 0) (h1 : σ' 1 = -σ 1) (b : Site d) :
    upar hd σ' b = vperp hd σ b ∧ vperp hd σ' b = upar hd σ b := by
  unfold upar vperp ox; rw [h0, h1]; push_cast; constructor <;> ring

/-! ## The lateral drift of a diagonal leg -/

section Drift

variable {σ : Fin 2 → ℤˣ} {q₀ : Fin 2} {l : List (BrickRec d)}

/-- **One hop changes the lateral coordinate by at most `U - m - 1`.** [folklore] -/
theorem DiagLeg.vperp_one (hY : Y.OK) (h : DiagLeg hd Y e σ none q₀ l) {k : ℕ} (hk : k + 1 < l.length) :
    |vperp hd σ (legOf l (k + 1)).b - vperp hd σ (legOf l k).b| ≤ Y.U - Y.m - 1 := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  obtain ⟨h1, h2, h3⟩ := h.step hk
  unfold vperp
  rcases Fin.exists_fin_two.1 ⟨qAt q₀ k, rfl⟩ with hq | hq
  · rw [qAt_succ, hq] at h1; rw [hq] at h2 h3; simp only [show oth (0 : Fin 2) = 1 from rfl] at h1
    rw [abs_le]; constructor <;> linarith
  · rw [qAt_succ, hq] at h1; rw [hq] at h2 h3; simp only [show oth (1 : Fin 2) = 0 from rfl] at h1
    rw [abs_le]; constructor <;> linarith

/-- **A pair of hops changes the lateral coordinate by at most `H - 2m - 2`**: the two hops push it
opposite ways by `U - t₁` and `U - t₂`. [folklore] -/
theorem DiagLeg.vperp_pair (h : DiagLeg hd Y e σ none q₀ l) {k : ℕ} (hk : k + 2 < l.length) :
    |vperp hd σ (legOf l (k + 2)).b - vperp hd σ (legOf l k).b| ≤ (Y.H : ℤ) - 2 * Y.m - 2 := by
  obtain ⟨h1, h2, h3⟩ := h.step (k := k) (by omega)
  obtain ⟨h1', h2', h3'⟩ := h.step (k := k + 1) hk
  rw [show k + 1 + 1 = k + 2 from rfl] at h1' h2' h3'
  unfold vperp
  rcases Fin.exists_fin_two.1 ⟨qAt q₀ k, rfl⟩ with hq | hq
  · have hq1 : qAt q₀ (k + 1) = 1 := by rw [qAt_succ, hq]; rfl
    have hq2 : qAt q₀ (k + 2) = 0 := by rw [show k + 2 = k + 1 + 1 from rfl, qAt_succ, hq1]; rfl
    rw [hq1] at h1 h2' h3'; rw [hq] at h2 h3; rw [hq2] at h1'
    rw [abs_le]; constructor <;> linarith
  · have hq1 : qAt q₀ (k + 1) = 0 := by rw [qAt_succ, hq]; rfl
    have hq2 : qAt q₀ (k + 2) = 1 := by rw [show k + 2 = k + 1 + 1 from rfl, qAt_succ, hq1]; rfl
    rw [hq1] at h1 h2' h3'; rw [hq] at h2 h3; rw [hq2] at h1'
    rw [abs_le]; constructor <;> linarith

/-- **The lateral drift of a diagonal leg**: after `2n` hops at most `n (H - 2m - 2)`, after `2n + 1`
at most `n (H - 2m - 2) + (U - m - 1)`. [folklore] -/
theorem DiagLeg.vperp_dev (hY : Y.OK) (h : DiagLeg hd Y e σ none q₀ l) (n : ℕ) :
    (2 * n < l.length → |vperp hd σ (legOf l (2 * n)).b - vperp hd σ (legOf l 0).b| ≤ (n : ℤ) * ((Y.H : ℤ) - 2 * Y.m - 2)) ∧
      (2 * n + 1 < l.length →
        |vperp hd σ (legOf l (2 * n + 1)).b - vperp hd σ (legOf l 0).b| ≤ (n : ℤ) * ((Y.H : ℤ) - 2 * Y.m - 2) + (Y.U - Y.m - 1)) := by
  induction n with
  | zero => exact ⟨fun _ => by simp, fun h1 => by simpa using h.vperp_one hY (k := 0) h1⟩
  | succ n ih =>
    have hev : 2 * (n + 1) < l.length → |vperp hd σ (legOf l (2 * (n + 1))).b - vperp hd σ (legOf l 0).b| ≤
        ((n : ℤ) + 1) * ((Y.H : ℤ) - 2 * Y.m - 2) := by
      intro hk
      have h1 := ih.1 (by omega)
      have h2 := h.vperp_pair (k := 2 * n) (by omega)
      rw [show 2 * (n + 1) = 2 * n + 2 by ring]
      calc |vperp hd σ (legOf l (2 * n + 2)).b - vperp hd σ (legOf l 0).b|
          = |(vperp hd σ (legOf l (2 * n + 2)).b - vperp hd σ (legOf l (2 * n)).b) + (vperp hd σ (legOf l (2 * n)).b - vperp hd σ (legOf l 0).b)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
        _ ≤ _ := by linarith
    refine ⟨hev, fun hk => ?_⟩
    push_cast
    have h1 := hev (by omega)
    have h2 := h.vperp_one hY (k := 2 * (n + 1)) hk
    calc |vperp hd σ (legOf l (2 * (n + 1) + 1)).b - vperp hd σ (legOf l 0).b|
        = |(vperp hd σ (legOf l (2 * (n + 1) + 1)).b - vperp hd σ (legOf l (2 * (n + 1))).b) + (vperp hd σ (legOf l (2 * (n + 1))).b - vperp hd σ (legOf l 0).b)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
      _ ≤ _ := by linarith

/-- **The lateral drift, uniform form**: `2 |Δ vperp| ≤ k (H - 2m - 2) + 2 (U - m - 1)`. [folklore] -/
theorem DiagLeg.vperp_dev' (hY : Y.OK) (h : DiagLeg hd Y e σ none q₀ l) {k : ℕ} (hk : k < l.length) :
    2 * |vperp hd σ (legOf l k).b - vperp hd σ (legOf l 0).b| ≤ (k : ℤ) * ((Y.H : ℤ) - 2 * Y.m - 2) + 2 * (Y.U - Y.m - 1) := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  rcases Nat.even_or_odd k with ⟨n, rfl⟩ | ⟨n, rfl⟩
  · have := (h.vperp_dev hY n).1 (by omega); rw [← two_mul] at *; push_cast; nlinarith [this, hmH, hULp, hLp0]
  · have := (h.vperp_dev hY n).2 hk; push_cast; nlinarith [this, hmH, hULp, hLp0]

end Drift

/-! ## The windows of the token -/

omit [NeZero d] in
/-- The step of a macro-direction along its own axis. [folklore] -/
theorem stepVec_apply_fst (e : MDir) : stepVec e e.1 = (sgOf e : ℤ) := by
  unfold stepVec sgOf
  cases e.2 <;> simp

omit [NeZero d] in
/-- **The token's diagonal coordinates** relative to the target cell: the forward one is between
`D + 2U` and `D + 1` before the centre, the lateral one within `ρ_p` of the source lane. [folklore] -/
theorem FTAdm.windows (hτ : FTAdm hd Y a e τ) :
    -(Y.Df + 2 * Y.U) ≤ upar hd (dsg e) τ.pos - (sgOf e : ℤ) * Y.ctr (ftgt a e) e.1 ∧
      upar hd (dsg e) τ.pos - (sgOf e : ℤ) * Y.ctr (ftgt a e) e.1 ≤ -(Y.Df + 1) ∧
      |(sgOf e : ℤ) * vperp hd (dsg e) τ.pos - Y.lane a e| ≤ Y.ρp := by
  obtain ⟨h1, h2⟩ := hτ.longit
  have h3 := hτ.lateral
  rw [Uc_lat_eq_vperp] at h3
  have hctr : Y.ctr (ftgt a e) e.1 = Y.ctr a e.1 + (sgOf e : ℤ) * (2 * Y.Df) := by
    unfold FlatLayout.ctr ftgt
    rw [Pi.add_apply, stepVec_apply_fst]; ring
  have hss : (sgOf e : ℤ) * (sgOf e : ℤ) = 1 := by rcases Int.units_eq_one_or (sgOf e) with h' | h' <;> simp [h']
  rw [← upar_dsg, hctr]
  have e1 : (sgOf e : ℤ) * Uc hd e.1 τ.pos - (sgOf e : ℤ) * (Y.ctr a e.1 + (sgOf e : ℤ) * (2 * Y.Df)) =
      (sgOf e : ℤ) * (Uc hd e.1 τ.pos - Y.ctr a e.1) - 2 * Y.Df := by linear_combination (-(2 * Y.Df)) * hss
  rw [e1]
  exact ⟨by linarith, by linarith, h3⟩

omit [NeZero d] in
/-- **The target lane is within `Λ_J` of the source lane** (the parity offset flips). [folklore] -/
theorem lane_ftgt_abs (Y : FlatLayout) (a : Site 2) (e : MDir) : |Y.lane (ftgt a e) e - Y.lane a e| ≤ Y.lamJ := by
  unfold FlatLayout.lane ftgt
  have hlat : (latDir e true).1 ≠ e.1 := by
    unfold latDir; intro h; have := congrArg Fin.val h; simp at this; have := e.1.isLt; omega
  have hctr : Y.ctr (a + stepVec e) (latDir e true).1 = Y.ctr a (latDir e true).1 := by
    unfold FlatLayout.ctr; rw [Pi.add_apply]
    have : stepVec e (latDir e true).1 = 0 := by
      unfold stepVec; cases e.2 <;> simp [Pi.single_eq_of_ne hlat]
    rw [this, add_zero]
  rw [hctr]
  have hJ : 0 ≤ Y.lamJ := by unfold FlatLayout.lamJ FlatLayout.U; positivity
  have hc1 : 0 ≤ TallLayout.cpar (a + stepVec e) ∧ TallLayout.cpar (a + stepVec e) ≤ 1 := by unfold TallLayout.cpar; omega
  have hc2 : 0 ≤ TallLayout.cpar a ∧ TallLayout.cpar a ≤ 1 := by unfold TallLayout.cpar; omega
  rw [show Y.ctr a (latDir e true).1 + Y.nu e + TallLayout.cpar (a + stepVec e) * Y.lamJ - (Y.ctr a (latDir e true).1 + Y.nu e + TallLayout.cpar a * Y.lamJ)
    = (TallLayout.cpar (a + stepVec e) - TallLayout.cpar a) * Y.lamJ by ring, abs_mul, abs_of_nonneg hJ]
  have : |TallLayout.cpar (a + stepVec e) - TallLayout.cpar a| ≤ 1 := by rw [abs_le]; omega
  nlinarith

/-! ## The windows of the riser and of the preamble -/

/-- **The riser's plane window**: the forward coordinate between the token's and `2 (k+1) U`
beyond, the lateral one within `(k+1) U` of the token's. [folklore] -/
theorem FlatInv.win_riser (hI : FlatInv hd Y a e τ st) (hY : Y.OK) (hτ : FTAdm hd Y a e τ) {k : ℕ} (hk : k < (st.segs 1).length) :
    upar hd (dsg e) τ.pos + 2 * Y.U ≤ upar hd (dsg e) (legOf (st.segs 1) k).b ∧
      upar hd (dsg e) (legOf (st.segs 1) k).b ≤ upar hd (dsg e) τ.pos + 2 * ((k : ℤ) + 1) * Y.U + 2 * Y.U + 2 * Y.H ∧
      |vperp hd (dsg e) (legOf (st.segs 1) k).b - vperp hd (dsg e) τ.pos| ≤ ((k : ℤ) + 1) * Y.U + Y.H ∧
      (∀ i, ox hd (dsg e) i τ.pos + (Y.U + Y.m + 1) ≤ ox hd (dsg e) i (legOf (st.segs 1) k).b) := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  have h1 : st.segs 1 ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hR := hI.riser h1
  obtain ⟨-, -, -, -, hsox, hsup, hsv, -⟩ := hI.rstart_facts hY hτ h1
  have l0 := (hR.plane hk 0).1; have l1 := (hR.plane hk 1).1
  have u0 := hR.plane_ub hY hk 0; have u1 := hR.plane_ub hY hk 1
  have s0 := hsox 0; have s1 := hsox 1
  have hsv' := abs_le.1 hsv
  unfold upar at hsup ⊢; unfold vperp
  refine ⟨by linarith, by linarith, ?_, fun i => ?_⟩
  · rw [abs_le]; constructor <;> linarith
  · rcases Fin.exists_fin_two.1 ⟨i, rfl⟩ with hi | hi <;> rw [hi] <;> linarith [(hR.plane hk i).1]

/-- **The riser's head is at least `U` beyond the token** in the forward coordinate, once the
riser is complete (its head is a landing). [folklore] -/
theorem FlatInv.riser_head_upar (hI : FlatInv hd Y a e τ st) (hY : Y.OK) (hτ : FTAdm hd Y a e τ) (hc : complete' hd Y a e τ (eJOf hd Y a e τ st) 1 (st.segs 1)) :
    upar hd (dsg e) τ.pos + Y.U ≤ upar hd (dsg e) (legOf (st.segs 1) ((st.segs 1).length - 1)).b := by
  obtain ⟨hU, -⟩ := hY.facts
  obtain ⟨r, tl, hrt⟩ : ∃ r tl, st.segs 1 = r :: tl := by
    rcases hh : st.segs 1 with _ | ⟨r, tl⟩
    · simp [complete', kindOf, hh] at hc
    · exact ⟨r, tl, rfl⟩
  have := (hI.win_riser hY hτ (k := (st.segs 1).length - 1) (by rw [hrt]; simp)).1
  linarith

/-- **The preamble's plane window** relative to the riser's head `R`: after `k + 1` hops the
forward coordinate has advanced by between `(k+1)(U+m+1)` and `(k+1)(U+H-m-1)`, the lateral one
deviates by at most `k (H-2m-2)/2 + 2 (U-m-1)`. [folklore] -/
theorem FlatInv.win_pre (hI : FlatInv hd Y a e τ st) (hY : Y.OK) {R : BrickRec d} (hR : (st.segs 1).head? = some R) {k : ℕ} (hk : k < (st.segs 2).length) :
    ((k : ℤ) + 1) * (Y.U + Y.m + 1) ≤ upar hd (dsg e) (legOf (st.segs 2) k).b - upar hd (dsg e) R.1.b ∧
      upar hd (dsg e) (legOf (st.segs 2) k).b - upar hd (dsg e) R.1.b ≤ ((k : ℤ) + 1) * (Y.U + Y.H - Y.m - 1) ∧
      2 * |vperp hd (dsg e) (legOf (st.segs 2) k).b - vperp hd (dsg e) R.1.b| ≤ (k : ℤ) * ((Y.H : ℤ) - 2 * Y.m - 2) + 4 * (Y.U - Y.m - 1) := by
  have h2 : st.segs 2 ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hK : SegOK hd Y e τ (eJOf hd Y a e τ st) 2 (st.segs 2) (st.segs (startOf 2)) := hI.segOK 2
  simp only [SegOK, startOf, Fin.isValue, Matrix.cons_val] at hK
  obtain ⟨s, hs, q, hD, hD0⟩ := hK h2
  have hsR : s = R := by rw [hR] at hs; simpa using hs.symm
  subst hsR
  -- the extended leg `segs 2 ++ [R]`
  have hE := diagLeg_snoc hD hD0
  have hk' : k + 1 < (st.segs 2 ++ [s]).length := by simp; omega
  have hm := hE.mono (k := 0) (k' := k + 1) (by omega) hk' 0
  rw [legOf_append_singleton_succ, legOf_snoc_zero] at hm
  have hv := hE.vperp_dev' hY hk'
  rw [legOf_append_singleton_succ, legOf_snoc_zero] at hv
  push_cast at hm hv ⊢
  simp only [sub_zero] at hm
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  exact ⟨by linarith [hm.2.1], by linarith [hm.2.2], by nlinarith [hv, hHU, hm0, hmH]⟩

/-- **The preamble has at most `163` plates**, and at least `162` once complete. [folklore] -/
theorem FlatInv.pre_len (hI : FlatInv hd Y a e τ st) :
    (st.segs 2).length ≤ 163 ∧ (complete' hd Y a e τ (eJOf hd Y a e τ st) 2 (st.segs 2) → 162 ≤ (st.segs 2).length) := by
  constructor
  · by_contra hlen
    push Not at hlen
    -- the stages of lengths `162` and `163` are proper and incomplete, but one of their heads has the kept axis
    have h2 : st.segs 2 ≠ [] := List.ne_nil_of_length_pos (by omega)
    have hK : SegOK hd Y e τ (eJOf hd Y a e τ st) 2 (st.segs 2) (st.segs (startOf 2)) := hI.segOK 2
    simp only [SegOK, startOf, Fin.isValue, Matrix.cons_val] at hK
    obtain ⟨s, -, q, hD, -⟩ := hK h2
    set l := st.segs 2 with hl
    have stage : ∀ n, (hn : n + 1 < l.length) → ¬(162 ≤ n + 1 ∧ (legOf l n).a = pl hd (pJ e (eJOf hd Y a e τ st))) := by
      intro n hn ⟨h162, hax⟩
      have hsuf : l.drop (l.length - (n + 1)) <:+ l := List.drop_suffix _ _
      have hlen : (l.drop (l.length - (n + 1))).length = n + 1 := by rw [List.length_drop]; omega
      have hne : l.drop (l.length - (n + 1)) ≠ l := by
        intro h; have := congrArg List.length h; rw [hlen] at this; omega
      have hnc := hI.nostop 2 _ hsuf hne
      obtain ⟨r, tl, hrt⟩ : ∃ r tl, l.drop (l.length - (n + 1)) = r :: tl := by
        rcases hh : l.drop (l.length - (n + 1)) with _ | ⟨r, tl⟩
        · rw [hh] at hlen; simp at hlen
        · exact ⟨r, tl, rfl⟩
      have hln : l.length - (n + 1) < l.length := by omega
      have hr : r.1 = legOf l n := by
        have h1 : l[l.length - (n + 1)]? = some r := by rw [← List.head?_drop, hrt]; rfl
        rw [List.getElem?_eq_getElem hln, Option.some.injEq] at h1
        unfold legOf recOf
        rw [List.getElem?_reverse (by omega), show l.length - 1 - n = l.length - (n + 1) by omega, List.getElem?_eq_getElem hln, h1]
        rfl
      simp only [complete', kindOf, Fin.isValue, Matrix.cons_val, hrt, not_and] at hnc
      refine hnc (by rw [← hrt, hlen]; exact h162) ?_
      rw [hr]; exact hax
    -- axes alternate: one of the plates `161`, `162` has the kept axis
    have ha1 := (hD.axis_sign (k := 161) (by omega)).1
    have ha2 := (hD.axis_sign (k := 162) (by omega)).1
    rw [show (162 : ℕ) = 161 + 1 from rfl, qAt_succ] at ha2
    rcases eq_or_eq_oth (pJ e (eJOf hd Y a e τ st)) (qAt q 161) with hp | hp
    · exact stage 161 (by omega) ⟨by norm_num, by rw [ha1, hp]⟩
    · exact stage 162 (by omega) ⟨by norm_num, by rw [ha2, hp]⟩
  · intro hc
    rcases hh : st.segs 2 with _ | ⟨r, tl⟩
    · simp [complete', kindOf, hh] at hc
    · simp only [complete', kindOf, Fin.isValue, Matrix.cons_val, hh] at hc; rw [← hh]; rw [← hh] at hc; exact hc.1

/-! ## The window of a turn -/

section TurnWin

variable {σ σ' : Fin 2 → ℤˣ} {p : Fin 2} {s : BrickPos d} {l : List (BrickRec d)}

/-- **The window of a turn, read in the old frame `σ`**: the top stacking is `H + 1` on along the
kept coordinate and pushed back by at most `L'` along the flipped one; the hop is `U` back along
the flipped one and drifts on by `t ∈ [m+1, H-m-1]` along the kept one. [folklore] -/
theorem Turn.win (hY : Y.OK) (h : Turn hd Y e σ σ' p s l) (hflip : σ' (oth p) = -σ (oth p)) :
    (∀ h0 : 0 < l.length, (Y.H : ℤ) + 1 - Y.Lp ≤ upar hd σ (legOf l 0).b - upar hd σ s.b ∧ upar hd σ (legOf l 0).b - upar hd σ s.b ≤ (Y.H : ℤ) + 1 ∧
        |vperp hd σ (legOf l 0).b - vperp hd σ s.b| ≤ (Y.H : ℤ) + 1 + Y.Lp) ∧
      (∀ h1 : 1 < l.length, (Y.m : ℤ) + 1 - Y.U ≤ upar hd σ (legOf l 1).b - upar hd σ (legOf l 0).b ∧
        upar hd σ (legOf l 1).b - upar hd σ (legOf l 0).b ≤ (Y.H : ℤ) - Y.m - 1 - Y.U ∧
        |vperp hd σ (legOf l 1).b - vperp hd σ (legOf l 0).b| ≤ Y.U + Y.H - Y.m - 1) := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  have hss : ∀ w : ℤˣ, (w : ℤ) * (w : ℤ) = 1 := fun w => by rcases Int.units_eq_one_or w with h' | h' <;> simp [h']
  constructor
  · intro h0
    have hT := h.h0 h0
    have hf : ox hd σ p (legOf l 0).b = ox hd σ p s.b + ((Y.H : ℤ) + 1) := by
      unfold ox; rw [hT.face, h.sSign, mul_add, ← mul_assoc, hss, one_mul]
    have hp1 := hT.push.1; have hp2 := hT.push.2
    rw [hflip] at hp1 hp2; simp only [Units.val_neg, neg_mul] at hp1 hp2
    have hpu : ox hd σ (oth p) (legOf l 0).b - ox hd σ (oth p) s.b ≤ 0 ∧ -Y.Lp ≤ ox hd σ (oth p) (legOf l 0).b - ox hd σ (oth p) s.b := by
      unfold ox; constructor <;> nlinarith [hp1, hp2, mul_sub (σ (oth p) : ℤ) ((legOf l 0).b (pl hd (oth p))) (s.b (pl hd (oth p)))]
    unfold upar vperp
    rcases Fin.exists_fin_two.1 ⟨p, rfl⟩ with hp | hp <;> simp only [hp, show oth (0 : Fin 2) = 1 from rfl, show oth (1 : Fin 2) = 0 from rfl] at hf hpu ⊢
    · refine ⟨by linarith, by linarith, ?_⟩; rw [abs_le]; constructor <;> linarith
    · refine ⟨by linarith, by linarith, ?_⟩; rw [abs_le]; constructor <;> linarith
  · intro h1
    have hD := h.h1 h1
    have hf : ox hd σ (oth p) (legOf l 1).b = ox hd σ (oth p) (legOf l 0).b - Y.U := by
      unfold ox; rw [hD.face, hflip]; simp only [Units.val_neg, neg_mul, mul_add, mul_neg, ← mul_assoc, hss, one_mul]; ring
    have hd1 := hD.drift.1; have hd2 := hD.drift.2
    rw [oth_oth, h.keep] at hd1 hd2
    have hdr : (Y.m : ℤ) + 1 ≤ ox hd σ p (legOf l 1).b - ox hd σ p (legOf l 0).b ∧ ox hd σ p (legOf l 1).b - ox hd σ p (legOf l 0).b ≤ (Y.H : ℤ) - Y.m - 1 := by
      unfold ox; constructor <;> nlinarith [hd1, hd2, mul_sub (σ p : ℤ) ((legOf l 1).b (pl hd p)) ((legOf l 0).b (pl hd p))]
    unfold upar vperp
    rcases Fin.exists_fin_two.1 ⟨p, rfl⟩ with hp | hp <;> simp only [hp, show oth (0 : Fin 2) = 1 from rfl, show oth (1 : Fin 2) = 0 from rfl] at hf hdr ⊢
    · refine ⟨by linarith, by linarith, ?_⟩; rw [abs_le]; constructor <;> linarith
    · refine ⟨by linarith, by linarith, ?_⟩; rw [abs_le]; constructor <;> linarith

/-- **The window of a turn, read in the new frame `σ'`**: the top stacking is `H + 1` on along the
kept coordinate and at most `L'` on along the flipped one; the hop is `U + t` on. [folklore] -/
theorem Turn.win' (hY : Y.OK) (h : Turn hd Y e σ σ' p s l) :
    (∀ h0 : 0 < l.length, (Y.H : ℤ) + 1 ≤ upar hd σ' (legOf l 0).b - upar hd σ' s.b ∧ upar hd σ' (legOf l 0).b - upar hd σ' s.b ≤ (Y.H : ℤ) + 1 + Y.Lp ∧
        |vperp hd σ' (legOf l 0).b - vperp hd σ' s.b| ≤ (Y.H : ℤ) + 1 + Y.Lp) ∧
      (∀ h1 : 1 < l.length, Y.U + Y.m + 1 ≤ upar hd σ' (legOf l 1).b - upar hd σ' (legOf l 0).b ∧
        upar hd σ' (legOf l 1).b - upar hd σ' (legOf l 0).b ≤ Y.U + Y.H - Y.m - 1 ∧
        |vperp hd σ' (legOf l 1).b - vperp hd σ' (legOf l 0).b| ≤ Y.U - Y.m - 1) := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  -- the frames agree on `p`
  have ep : ∀ b : Site d, ox hd σ' p b = ox hd σ p b := fun b => by unfold ox; rw [h.keep]
  constructor
  · intro h0
    have hT := h.h0 h0
    have hss : ∀ w : ℤˣ, (w : ℤ) * (w : ℤ) = 1 := fun w => by rcases Int.units_eq_one_or w with h' | h' <;> simp [h']
    have hf : ox hd σ p (legOf l 0).b = ox hd σ p s.b + ((Y.H : ℤ) + 1) := by
      unfold ox; rw [hT.face, h.sSign, mul_add, ← mul_assoc, hss, one_mul]
    have hp1 := hT.push.1; have hp2 := hT.push.2
    have hpu : 0 ≤ ox hd σ' (oth p) (legOf l 0).b - ox hd σ' (oth p) s.b ∧ ox hd σ' (oth p) (legOf l 0).b - ox hd σ' (oth p) s.b ≤ Y.Lp := by
      unfold ox; constructor <;> nlinarith [hp1, hp2, mul_sub (σ' (oth p) : ℤ) ((legOf l 0).b (pl hd (oth p))) (s.b (pl hd (oth p)))]
    rw [← ep, ← ep] at hf
    unfold upar vperp
    rcases Fin.exists_fin_two.1 ⟨p, rfl⟩ with hp | hp <;> simp only [hp, show oth (0 : Fin 2) = 1 from rfl, show oth (1 : Fin 2) = 0 from rfl] at hf hpu ⊢
    · refine ⟨by linarith, by linarith, ?_⟩; rw [abs_le]; constructor <;> linarith
    · refine ⟨by linarith, by linarith, ?_⟩; rw [abs_le]; constructor <;> linarith
  · intro h1
    have hD := h.h1 h1
    have hss : ∀ w : ℤˣ, (w : ℤ) * (w : ℤ) = 1 := fun w => by rcases Int.units_eq_one_or w with h' | h' <;> simp [h']
    have hf : ox hd σ' (oth p) (legOf l 1).b = ox hd σ' (oth p) (legOf l 0).b + Y.U := by
      unfold ox; rw [hD.face, mul_add, ← mul_assoc, hss, one_mul]
    have hd1 := hD.drift.1; have hd2 := hD.drift.2
    rw [oth_oth] at hd1 hd2
    have hdr : (Y.m : ℤ) + 1 ≤ ox hd σ' p (legOf l 1).b - ox hd σ' p (legOf l 0).b ∧ ox hd σ' p (legOf l 1).b - ox hd σ' p (legOf l 0).b ≤ (Y.H : ℤ) - Y.m - 1 := by
      unfold ox; constructor <;> nlinarith [hd1, hd2, mul_sub (σ' p : ℤ) ((legOf l 1).b (pl hd p)) ((legOf l 0).b (pl hd p))]
    unfold upar vperp
    rcases Fin.exists_fin_two.1 ⟨p, rfl⟩ with hp | hp <;> simp only [hp, show oth (0 : Fin 2) = 1 from rfl, show oth (1 : Fin 2) = 0 from rfl] at hf hdr ⊢
    · refine ⟨by linarith, by linarith, ?_⟩; rw [abs_le]; constructor <;> linarith
    · refine ⟨by linarith, by linarith, ?_⟩; rw [abs_le]; constructor <;> linarith

end TurnWin

end BGNd

end Percolation.Literature

end

/-!
# Part 3 (The flat gait, XVIII): bounds, III — the jog

The windows of the jog turn and of the jog of the flat
gait (Grimmett, *Percolation*, 2nd ed. (1999), §7.3 pp. 171–174, case `H < L`): the jog advances
towards the target lane by `U + t` a hop while its forward coordinate drifts by less than `H` a
pair (`FlatInv.win_J`); it starts at most `Λ_J + ρ_p + 123 U` before the lane
(`FlatInv.J_gap_init`), so it has at most `1021` plates (`FlatInv.J_len`), and all its plates are
between its start and `19 U` beyond the lane (`FlatInv.J_gap`).

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §7.3 pp. 171–174.
-/

noncomputable section

namespace Percolation.Literature

open LatticeModels Contour
open scoped Classical

namespace BGNd

variable {d : ℕ} [NeZero d] {hd : 3 ≤ d} {Y : FlatLayout} {a : Site 2} {e : MDir} {τ : TTok d} {st : FS d}

/-! ## The jog direction -/

omit [NeZero d] in
/-- **The jog heads for the target lane**: from the riser's head `R`, the signed gap to the lane is
its absolute value. [folklore] -/
theorem eJOf_gap_eq_abs {R : BrickRec d} (hR : (st.segs 1).head? = some R) :
    (sgOf (eJOf hd Y a e τ st) : ℤ) * (Y.lane (ftgt a e) e - Uc hd (latDir e true).1 R.1.b) = |Y.lane (ftgt a e) e - Uc hd (latDir e true).1 R.1.b| := by
  unfold eJOf; rw [hR]; simp only [sgOf_latDir]
  split_ifs with h
  · simp only [decide_eq_true_eq] at h; rw [Units.val_one, one_mul, abs_of_nonneg (by linarith)]
  · simp only [decide_eq_true_eq, not_le] at h; rw [Units.val_neg, Units.val_one, neg_one_mul, abs_of_neg (by linarith)]

omit [NeZero d] in
/-- The forward coordinate of the jog's frame is `s_j · Uc_lat`. [folklore] -/
theorem upar_ej (hd : 3 ≤ d) (Y : FlatLayout) (a : Site 2) (e : MDir) (τ : TTok d) (st : FS d) (b : Site d) :
    upar hd (dsg (eJOf hd Y a e τ st)) b = (sgOf (eJOf hd Y a e τ st) : ℤ) * Uc hd (latDir e true).1 b := by
  rw [← upar_dsg]; rfl

omit [NeZero d] in
/-- The lateral coordinate of the jog's frame is `±` the forward one of `e`'s. [folklore] -/
theorem vperp_ej_abs (hd : 3 ≤ d) (Y : FlatLayout) (a : Site 2) (e : MDir) (τ : TTok d) (st : FS d) (b b' : Site d) :
    |vperp hd (dsg (eJOf hd Y a e τ st)) b - vperp hd (dsg (eJOf hd Y a e τ st)) b'| = |upar hd (dsg e) b - upar hd (dsg e) b'| := by
  obtain ⟨hflipJ, hkeepJ, -⟩ := flip_keep_J hd Y a e τ st
  rcases Fin.exists_fin_two.1 ⟨pJ e (eJOf hd Y a e τ st), rfl⟩ with hp | hp <;> rw [hp] at hflipJ hkeepJ
  · have h := fun b => (upar_vperp_flip1 hd (σ := dsg e) (σ' := dsg (eJOf hd Y a e τ st)) hkeepJ hflipJ b).2
    rw [h, h]
  · have h := fun b => (upar_vperp_flip0 hd (σ := dsg e) (σ' := dsg (eJOf hd Y a e τ st)) hflipJ hkeepJ b).2
    rw [h, h, show -upar hd (dsg e) b - -upar hd (dsg e) b' = -(upar hd (dsg e) b - upar hd (dsg e) b') by ring, abs_neg]

/-! ## The jog turn and the jog -/

/-- **The jog turn's window** relative to the preamble's head `P`. [folklore] -/
theorem FlatInv.win_GJ (hI : FlatInv hd Y a e τ st) (hY : Y.OK) {P : BrickRec d} (hP : (st.segs 2).head? = some P) :
    (∀ h0 : 0 < (st.segs 3).length,
        (Y.H : ℤ) + 1 - Y.Lp ≤ upar hd (dsg e) (legOf (st.segs 3) 0).b - upar hd (dsg e) P.1.b ∧
        upar hd (dsg e) (legOf (st.segs 3) 0).b - upar hd (dsg e) P.1.b ≤ (Y.H : ℤ) + 1 ∧
        |vperp hd (dsg e) (legOf (st.segs 3) 0).b - vperp hd (dsg e) P.1.b| ≤ (Y.H : ℤ) + 1 + Y.Lp) ∧
      (∀ h1 : 1 < (st.segs 3).length,
        (Y.m : ℤ) + 1 - Y.U ≤ upar hd (dsg e) (legOf (st.segs 3) 1).b - upar hd (dsg e) (legOf (st.segs 3) 0).b ∧
        upar hd (dsg e) (legOf (st.segs 3) 1).b - upar hd (dsg e) (legOf (st.segs 3) 0).b ≤ (Y.H : ℤ) - Y.m - 1 - Y.U ∧
        |vperp hd (dsg e) (legOf (st.segs 3) 1).b - vperp hd (dsg e) (legOf (st.segs 3) 0).b| ≤ Y.U + Y.H - Y.m - 1) := by
  by_cases h3 : st.segs 3 = []
  · rw [h3]; exact ⟨fun h => absurd h (by simp), fun h => absurd h (by simp)⟩
  obtain ⟨P', hP', -, hT⟩ := hI.frame_turnJ h3
  have hPP : P' = P := by rw [hP] at hP'; simpa using hP'.symm
  subst hPP
  obtain ⟨hflipJ, -, -⟩ := flip_keep_J hd Y a e τ st
  exact hT.win hY hflipJ

/-- **The jog's window** relative to the jog turn's hop `γ`: towards the lane by between
`(k+1)(U+m+1)` and `(k+1)(U+H-m-1)` after `k + 1` hops, the forward coordinate within
`(k+1)(H-2m-2)/2 + (U-m-1)`. [folklore] -/
theorem FlatInv.win_J (hI : FlatInv hd Y a e τ st) (hY : Y.OK) {γ : BrickRec d} (hγ : (st.segs 3).head? = some γ) {k : ℕ} (hk : k < (st.segs 4).length) :
    ((k : ℤ) + 1) * (Y.U + Y.m + 1) ≤ (sgOf (eJOf hd Y a e τ st) : ℤ) * (Uc hd (latDir e true).1 (legOf (st.segs 4) k).b - Uc hd (latDir e true).1 γ.1.b) ∧
      (sgOf (eJOf hd Y a e τ st) : ℤ) * (Uc hd (latDir e true).1 (legOf (st.segs 4) k).b - Uc hd (latDir e true).1 γ.1.b) ≤ ((k : ℤ) + 1) * (Y.U + Y.H - Y.m - 1) ∧
      2 * |upar hd (dsg e) (legOf (st.segs 4) k).b - upar hd (dsg e) γ.1.b| ≤ ((k : ℤ) + 1) * ((Y.H : ℤ) - 2 * Y.m - 2) + 2 * (Y.U - Y.m - 1) := by
  obtain ⟨γ', hγ', -, hJE⟩ := hI.frame_jog (List.ne_nil_of_length_pos (by omega))
  have hgg : γ' = γ := by rw [hγ] at hγ'; simpa using hγ'.symm
  subst hgg
  have hk' : k + 1 < (st.segs 4 ++ [γ']).length := by simp; omega
  have hm := hJE.mono (k := 0) (k' := k + 1) (by omega) hk' 0
  have hv := hJE.vperp_dev' hY hk'
  rw [legOf_append_singleton_succ, legOf_snoc_zero] at hm hv
  rw [upar_ej, upar_ej, ← mul_sub] at hm
  rw [vperp_ej_abs] at hv
  push_cast at hm hv ⊢
  simp only [sub_zero] at hm
  exact ⟨hm.2.1, hm.2.2, hv⟩

/-- **The jog starts at most `Λ_J + ρ_p + 123 U` before the target lane** (signed gap from its
turn's hop `γ`). [folklore] -/
theorem FlatInv.J_gap_init (hI : FlatInv hd Y a e τ st) (hY : Y.OK) (hτ : FTAdm hd Y a e τ) {γ : BrickRec d}
    (hγ : (st.segs 3).head? = some γ) (hlen3 : (st.segs 3).length = 2) :
    -(16 * Y.U) ≤ (sgOf (eJOf hd Y a e τ st) : ℤ) * (Y.lane (ftgt a e) e - Uc hd (latDir e true).1 γ.1.b) ∧
      (sgOf (eJOf hd Y a e τ st) : ℤ) * (Y.lane (ftgt a e) e - Uc hd (latDir e true).1 γ.1.b) ≤ Y.lamJ + Y.ρp + 123 * Y.U := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  set ej := eJOf hd Y a e τ st with hej
  have h3 : st.segs 3 ≠ [] := by intro h; rw [h] at hlen3; simp at hlen3
  -- the riser's head, the preamble's head
  have hc2 := hI.order 3 2 (by decide) h3
  have h2 : st.segs 2 ≠ [] := by intro h; rw [h] at hc2; simp [complete'] at hc2
  have hc1 := hI.order 2 1 (by decide) h2
  have h1 : st.segs 1 ≠ [] := by intro h; rw [h] at hc1; simp [complete'] at hc1
  obtain ⟨R, tl1, hl1, hR⟩ := exists_head_of_ne_nil h1
  obtain ⟨P, tl2, hl2, hP⟩ := exists_head_of_ne_nil h2
  -- (1) from `R` the signed gap is the absolute one
  have hg0 := eJOf_gap_eq_abs (hd := hd) (Y := Y) (a := a) (e := e) (τ := τ) hR
  rw [← hej] at hg0
  -- (2) `|lane(c,e) - Uc_lat(R)| ≤ Λ_J + ρ_p + 106 U`
  have hlane := lane_ftgt_abs Y a e
  obtain ⟨-, -, htok⟩ := hτ.windows
  have hRk : (st.segs 1).length - 1 < (st.segs 1).length := by rw [hl1]; simp
  have hwr := (hI.win_riser hY hτ hRk).2.2.1
  have hRlast : legOf (st.segs 1) ((st.segs 1).length - 1) = R.1 := by rw [hl1]; exact legOf_cons_length R tl1
  rw [hRlast] at hwr
  have hlenR := hI.riser_len_le hY hτ
  have hwr' : |vperp hd (dsg e) R.1.b - vperp hd (dsg e) τ.pos| ≤ 106 * Y.U + Y.H := by
    refine hwr.trans ?_
    have : ((st.segs 1).length - 1 : ℕ) + (1 : ℤ) ≤ 106 := by
      have h0 : 1 ≤ (st.segs 1).length := by rw [hl1]; simp
      push_cast [Nat.cast_sub h0]; linarith [show ((st.segs 1).length : ℤ) ≤ 106 by exact_mod_cast hlenR]
    nlinarith
  -- (3) `|Uc_lat(γ) - Uc_lat(R)| ≤ 16 U`: preamble drift, the turn
  have hPk : (st.segs 2).length - 1 < (st.segs 2).length := by rw [hl2]; simp
  have hwp := (hI.win_pre hY hR hPk).2.2
  have hPlast : legOf (st.segs 2) ((st.segs 2).length - 1) = P.1 := by rw [hl2]; exact legOf_cons_length P tl2
  rw [hPlast] at hwp
  have hlenP := hI.pre_len.1
  have hwp' : |vperp hd (dsg e) P.1.b - vperp hd (dsg e) R.1.b| ≤ 81 * ((Y.H : ℤ) - 2 * Y.m - 2) + 2 * (Y.U - Y.m - 1) := by
    have : (((st.segs 2).length - 1 : ℕ) : ℤ) ≤ 162 := by
      have h0 : 1 ≤ (st.segs 2).length := by rw [hl2]; simp
      push_cast [Nat.cast_sub h0]; linarith [show ((st.segs 2).length : ℤ) ≤ 163 by exact_mod_cast hlenP]
    have hH2 : 0 ≤ (Y.H : ℤ) - 2 * Y.m - 2 := by linarith
    nlinarith
  obtain ⟨hw0, hw1⟩ := hI.win_GJ hY hP
  obtain ⟨-, -, hv0⟩ := hw0 (by omega)
  obtain ⟨-, -, hv1⟩ := hw1 (by omega)
  obtain ⟨tl3, hl3⟩ : ∃ tl, st.segs 3 = γ :: tl := by
    rcases hh : st.segs 3 with _ | ⟨r0, tl⟩
    · exact absurd hh h3
    · rw [hh] at hγ; simp only [List.head?_cons, Option.some.injEq] at hγ; subst hγ; exact ⟨tl, rfl⟩
  have htl3 : tl3.length = 1 := by rw [hl3] at hlen3; simp at hlen3; omega
  have hγ1 : legOf (st.segs 3) 1 = γ.1 := by rw [hl3]; exact legOf_head' htl3
  rw [hγ1] at hv1
  -- assemble along `s`: `Uc_lat = s · vperp`
  have hs1 : |(sgOf e : ℤ)| = 1 := by rcases Int.units_eq_one_or (sgOf e) with h' | h' <;> simp [h']
  set v0 := vperp hd (dsg e) τ.pos with hv0d
  set vR := vperp hd (dsg e) R.1.b with hvRd
  set vP := vperp hd (dsg e) P.1.b with hvPd
  set vT := vperp hd (dsg e) (legOf (st.segs 3) 0).b with hvTd
  set vG := vperp hd (dsg e) γ.1.b with hvGd
  have hRG : |vR - vG| ≤ (81 * ((Y.H : ℤ) - 2 * Y.m - 2) + 2 * (Y.U - Y.m - 1)) + ((Y.H : ℤ) + 1 + Y.Lp) + (Y.U + Y.H - Y.m - 1) := by
    have e2 : vR - vG = (vR - vP) + (vP - vT) + (vT - vG) := by ring
    rw [e2]
    refine (abs_add_le _ _).trans ?_
    have t4 := abs_add_le (vR - vP) (vP - vT)
    rw [abs_sub_comm] at hwp' hv0 hv1
    linarith
  have hin : |v0 - vG| ≤ 106 * Y.U + Y.H + ((81 * ((Y.H : ℤ) - 2 * Y.m - 2) + 2 * (Y.U - Y.m - 1)) + ((Y.H : ℤ) + 1 + Y.Lp) + (Y.U + Y.H - Y.m - 1)) := by
    have e2 : v0 - vG = (v0 - vR) + (vR - vG) := by ring
    rw [e2]
    refine (abs_add_le _ _).trans ?_
    rw [abs_sub_comm] at hwr'
    linarith
  have key : |Y.lane (ftgt a e) e - Uc hd (latDir e true).1 γ.1.b| ≤ Y.lamJ + Y.ρp + 123 * Y.U := by
    have e1 : Y.lane (ftgt a e) e - Uc hd (latDir e true).1 γ.1.b =
        (Y.lane (ftgt a e) e - Y.lane a e) + (Y.lane a e - (sgOf e : ℤ) * v0) + (sgOf e : ℤ) * (v0 - vG) := by
      rw [Uc_lat_eq_vperp]; ring
    rw [e1]
    refine (abs_add_le _ _).trans ?_
    have t1 := abs_add_le (Y.lane (ftgt a e) e - Y.lane a e) (Y.lane a e - (sgOf e : ℤ) * v0)
    rw [abs_mul, hs1, one_mul]
    rw [abs_sub_comm] at htok
    have hH8 : 8 * ((Y.H : ℤ) + 1) ≤ Y.U := hflat
    linarith
  constructor
  · -- from `R` the gap is nonnegative, and `γ` is within `16 U` of `R` laterally
    have e3 : (sgOf ej : ℤ) * (Y.lane (ftgt a e) e - Uc hd (latDir e true).1 γ.1.b) =
        (sgOf ej : ℤ) * (Y.lane (ftgt a e) e - Uc hd (latDir e true).1 R.1.b) + (sgOf ej : ℤ) * (sgOf e : ℤ) * (vR - vG) := by
      rw [Uc_lat_eq_vperp, Uc_lat_eq_vperp]; ring
    rw [e3, hg0]
    have hb : |(sgOf ej : ℤ) * (sgOf e : ℤ) * (vR - vG)| = |vR - vG| := by
      rw [abs_mul, abs_mul, hs1]; have : |(sgOf ej : ℤ)| = 1 := by rcases Int.units_eq_one_or (sgOf ej) with h' | h' <;> simp [h']
      rw [this]; ring
    have hH8 : 8 * ((Y.H : ℤ) + 1) ≤ Y.U := hflat
    have := neg_abs_le ((sgOf ej : ℤ) * (sgOf e : ℤ) * (vR - vG))
    rw [hb] at this
    linarith [abs_nonneg (Y.lane (ftgt a e) e - Uc hd (latDir e true).1 R.1.b)]
  · calc (sgOf ej : ℤ) * (Y.lane (ftgt a e) e - Uc hd (latDir e true).1 γ.1.b)
        ≤ |(sgOf ej : ℤ) * (Y.lane (ftgt a e) e - Uc hd (latDir e true).1 γ.1.b)| := le_abs_self _
      _ = |Y.lane (ftgt a e) e - Uc hd (latDir e true).1 γ.1.b| := by
          rw [abs_mul]; have : |(sgOf ej : ℤ)| = 1 := by rcases Int.units_eq_one_or (sgOf ej) with h' | h' <;> simp [h']
          rw [this, one_mul]
      _ ≤ _ := key

/-! ## Stages and the stopping rule -/

/-- **A proper stage of a segment is incomplete**, with its head identified. [folklore] -/
theorem FlatInv.stage (hI : FlatInv hd Y a e τ st) (i : Fin 13) {n : ℕ} (hn : n + 1 < (st.segs i).length) :
    ∃ r tl, r.1 = legOf (st.segs i) n ∧ (r :: tl).length = n + 1 ∧ ¬complete' hd Y a e τ (eJOf hd Y a e τ st) i (r :: tl) := by
  set l := st.segs i with hl
  have hsuf : l.drop (l.length - (n + 1)) <:+ l := List.drop_suffix _ _
  have hlen : (l.drop (l.length - (n + 1))).length = n + 1 := by rw [List.length_drop]; omega
  have hne : l.drop (l.length - (n + 1)) ≠ l := by
    intro h; have := congrArg List.length h; rw [hlen] at this; omega
  have hnc := hI.nostop i _ hsuf hne
  obtain ⟨r, tl, hrt⟩ : ∃ r tl, l.drop (l.length - (n + 1)) = r :: tl := by
    rcases hh : l.drop (l.length - (n + 1)) with _ | ⟨r, tl⟩
    · rw [hh] at hlen; simp at hlen
    · exact ⟨r, tl, rfl⟩
  have hln : l.length - (n + 1) < l.length := by omega
  have hr : r.1 = legOf l n := by
    have h1 : l[l.length - (n + 1)]? = some r := by rw [← List.head?_drop, hrt]; rfl
    rw [List.getElem?_eq_getElem hln, Option.some.injEq] at h1
    unfold legOf recOf
    rw [List.getElem?_reverse (by omega), show l.length - 1 - n = l.length - (n + 1) by omega, List.getElem?_eq_getElem hln, h1]
    rfl
  rw [hrt] at hlen hnc
  exact ⟨r, tl, hr, hlen, hnc⟩

/-- **The jog has at most `1021` plates.** [cite: GrimmettPercolation1999, §7.3 p. 174 (the bound `R`)] -/
theorem FlatInv.J_len (hI : FlatInv hd Y a e τ st) (hY : Y.OK) (hτ : FTAdm hd Y a e τ) : (st.segs 4).length ≤ 1021 := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  by_contra hlen
  push Not at hlen
  set ej := eJOf hd Y a e τ st with hej
  obtain ⟨γ, hγ, hlen3, hJE⟩ := hI.frame_jog (List.ne_nil_of_length_pos (by omega))
  rw [← hej] at hJE
  obtain ⟨-, hgap⟩ := hI.J_gap_init hY hτ hγ hlen3
  rw [← hej] at hgap
  -- plates `1019`, `1020` fit
  have fits : ∀ n, 1018 ≤ n → (hn : n < (st.segs 4).length) → ffitsJ hd Y a e ej (legOf (st.segs 4) n).b := by
    intro n hn17 hn
    have hw := (hI.win_J hY hγ hn).1
    rw [← hej] at hw
    unfold ffitsJ
    rw [show ej.1 = (latDir e true).1 from rfl]
    have : (1019 : ℤ) ≤ (n : ℤ) + 1 := by exact_mod_cast (show 1019 ≤ n + 1 by omega)
    unfold FlatLayout.lamJ FlatLayout.ρp at hgap
    nlinarith [hw, hgap, hm0, hU]
  -- the stages of lengths `1020`, `1021` are proper and incomplete: wrong axis twice
  have stage : ∀ n, 1018 ≤ n → (hn : n + 1 < (st.segs 4).length) → (legOf (st.segs 4) n).a ≠ pl hd (pJ e ej) := by
    intro n hn17 hn hax
    obtain ⟨r, tl, hr, hl, hnc⟩ := hI.stage 4 hn
    rw [← hej] at hnc
    simp only [complete', kindOf, Fin.isValue, Matrix.cons_val, minLenOf, legStop, legAxisOf, hl, hr, not_and] at hnc
    exact hnc (by simp) (by simp [fits n hn17 (by omega)]) (fun q hq => by
      simp only [Option.some.injEq] at hq; rw [← hq]; exact hax)
  have ha1 := (hJE.axis_sign (k := 1020) (by simp; omega)).1
  have ha2 := (hJE.axis_sign (k := 1021) (by simp; omega)).1
  rw [legOf_append_singleton_succ] at ha1 ha2
  rw [show (1021 : ℕ) = 1020 + 1 from rfl, qAt_succ] at ha2
  rcases eq_or_eq_oth (pJ e ej) (qAt (oth (pJ e ej)) 1020) with hp | hp
  · exact stage 1019 (by norm_num) (by omega) (by rw [ha1, ← hp])
  · exact stage 1020 (by norm_num) (by omega) (by rw [ha2, ← hp])

/-- **The signed gap of a base point to the target lane**, along the jog. [folklore] -/
def jgap (hd : 3 ≤ d) (Y : FlatLayout) (a : Site 2) (e : MDir) (τ : TTok d) (st : FS d) (b : Site d) : ℤ :=
  (sgOf (eJOf hd Y a e τ st) : ℤ) * (Y.lane (ftgt a e) e - Uc hd (latDir e true).1 b)

/-- **The gap decreases along the jog**, by between `U + m + 1` and `U + H - m - 1` a hop; the
first plate is that much nearer than the jog turn's hop. [folklore] -/
theorem FlatInv.jgap_mono (hI : FlatInv hd Y a e τ st) (hY : Y.OK) {γ : BrickRec d} (hγ : (st.segs 3).head? = some γ) :
    (∀ k, (hk : k < (st.segs 4).length) →
        ((k : ℤ) + 1) * (Y.U + Y.m + 1) ≤ jgap hd Y a e τ st γ.1.b - jgap hd Y a e τ st (legOf (st.segs 4) k).b ∧
        jgap hd Y a e τ st γ.1.b - jgap hd Y a e τ st (legOf (st.segs 4) k).b ≤ ((k : ℤ) + 1) * (Y.U + Y.H - Y.m - 1)) ∧
      (∀ k k', k ≤ k' → (hk' : k' < (st.segs 4).length) →
        ((k' : ℤ) - k) * (Y.U + Y.m + 1) ≤ jgap hd Y a e τ st (legOf (st.segs 4) k).b - jgap hd Y a e τ st (legOf (st.segs 4) k').b ∧
        jgap hd Y a e τ st (legOf (st.segs 4) k).b - jgap hd Y a e τ st (legOf (st.segs 4) k').b ≤ ((k' : ℤ) - k) * (Y.U + Y.H - Y.m - 1)) := by
  constructor
  · intro k hk
    have hw := hI.win_J hY hγ hk
    unfold jgap
    constructor <;> nlinarith [hw.1, hw.2.1]
  · intro k k' hkk hk'
    obtain ⟨γ', hγ', -, hJE⟩ := hI.frame_jog (List.ne_nil_of_length_pos (by omega))
    have hm := hJE.mono (k := k + 1) (k' := k' + 1) (by omega) (by simp; omega) 0
    rw [legOf_append_singleton_succ, legOf_append_singleton_succ, upar_ej, upar_ej] at hm
    unfold jgap
    push_cast at hm ⊢
    constructor <;> nlinarith [hm.2.1, hm.2.2]

/-- **The stopping rule of the jog at a proper stage**: a plate before the head that is within `U`
of the lane (or beyond) has the flipped axis. [folklore] -/
theorem FlatInv.J_stage (hI : FlatInv hd Y a e τ st) {j : ℕ} (hj : j + 1 < (st.segs 4).length)
    (hfit : jgap hd Y a e τ st (legOf (st.segs 4) j).b ≤ Y.U) : (legOf (st.segs 4) j).a ≠ pl hd (pJ e (eJOf hd Y a e τ st)) := by
  intro hax
  obtain ⟨r, tl, hr, hl, hnc⟩ := hI.stage 4 hj
  simp only [complete', kindOf, Fin.isValue, Matrix.cons_val, minLenOf, legStop, legAxisOf, hl, hr, not_and] at hnc
  refine hnc (by simp) ?_ (fun q hq => by simp only [Option.some.injEq] at hq; rw [← hq]; exact hax)
  simp only [Fin.isValue, if_true, ffitsJ]
  exact hfit

/-- **Axes alternate along the jog.** [folklore] -/
theorem FlatInv.J_alt (hI : FlatInv hd Y a e τ st) {j : ℕ} (hj : j + 1 < (st.segs 4).length) :
    (legOf (st.segs 4) j).a = pl hd (pJ e (eJOf hd Y a e τ st)) ∨ (legOf (st.segs 4) (j + 1)).a = pl hd (pJ e (eJOf hd Y a e τ st)) := by
  obtain ⟨γ', -, -, hJE⟩ := hI.frame_jog (List.ne_nil_of_length_pos (by omega))
  have ha1 := (hJE.axis_sign (k := j + 1) (by simp; omega)).1
  have ha2 := (hJE.axis_sign (k := j + 2) (by simp; omega)).1
  rw [legOf_append_singleton_succ] at ha1 ha2
  rw [show j + 2 = j + 1 + 1 from rfl, qAt_succ] at ha2
  rcases eq_or_eq_oth (pJ e (eJOf hd Y a e τ st)) (qAt (oth (pJ e (eJOf hd Y a e τ st))) (j + 1)) with hp | hp
  · left; rw [ha1, ← hp]
  · right; rw [ha2, ← hp]

/-- **The head of the complete jog is at most `18 U + 2 H` beyond the lane.** [folklore] -/
theorem FlatInv.J_gap_head (hI : FlatInv hd Y a e τ st) (hY : Y.OK) (hτ : FTAdm hd Y a e τ) {γ : BrickRec d} (hγ : (st.segs 3).head? = some γ)
    (h4 : st.segs 4 ≠ []) : -(18 * Y.U + 2 * Y.H) ≤ jgap hd Y a e τ st (legOf (st.segs 4) ((st.segs 4).length - 1)).b := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  obtain ⟨γ', hγ', hlen3, -⟩ := hI.frame_jog h4
  have hgg : γ' = γ := by rw [hγ] at hγ'; simpa using hγ'.symm
  subst hgg
  obtain ⟨hgap0, -⟩ := hI.J_gap_init hY hτ hγ hlen3
  change -(16 * Y.U) ≤ jgap hd Y a e τ st γ'.1.b at hgap0
  obtain ⟨hgk, hmono⟩ := hI.jgap_mono hY hγ
  set n := (st.segs 4).length - 1 with hn
  have hlen : 0 < (st.segs 4).length := List.length_pos_of_ne_nil h4
  have h0 := hgk 0 hlen; push_cast at h0
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · rw [hn0]; linarith [h0.2]
  · rcases le_or_gt (jgap hd Y a e τ st (legOf (st.segs 4) (n - 1)).b) Y.U with hfit | hnfit
    · -- the previous plate fits but has the wrong axis
      have hax := hI.J_stage (j := n - 1) (by omega) hfit
      rcases Nat.eq_zero_or_pos (n - 1) with hn1 | hn1
      · have hm := (hmono 0 n (by omega) (by omega)).2
        have : (n : ℤ) = 1 := by exact_mod_cast (show n = 1 by omega)
        rw [this] at hm; push_cast at hm; linarith [h0.2]
      · -- two back has the kept axis, so it does not fit
        have hax2 : (legOf (st.segs 4) (n - 2)).a = pl hd (pJ e (eJOf hd Y a e τ st)) := by
          rcases hI.J_alt (j := n - 2) (by omega) with h | h
          · exact h
          · rw [show n - 2 + 1 = n - 1 by omega] at h; exact absurd h hax
        have hnf : Y.U < jgap hd Y a e τ st (legOf (st.segs 4) (n - 2)).b := by
          by_contra hle; push Not at hle; exact hI.J_stage (j := n - 2) (by omega) hle hax2
        have hm := (hmono (n - 2) n (by omega) (by omega)).2
        have : (n : ℤ) - ((n - 2 : ℕ) : ℤ) = 2 := by push_cast [Nat.cast_sub (show 2 ≤ n by omega)]; ring
        rw [this] at hm; linarith
    · have hm := (hmono (n - 1) n (by omega) (by omega)).2
      have : (n : ℤ) - ((n - 1 : ℕ) : ℤ) = 1 := by push_cast [Nat.cast_sub (show 1 ≤ n by omega)]; ring
      rw [this] at hm; linarith

/-- **The jog's gap to the lane**: every plate is at least `U + m + 1` nearer than the jog turn's
hop, and — once the jog is complete — at most `19 U` beyond the lane. [folklore] -/
theorem FlatInv.J_gap (hI : FlatInv hd Y a e τ st) (hY : Y.OK) (hτ : FTAdm hd Y a e τ) {γ : BrickRec d} (hγ : (st.segs 3).head? = some γ)
    {k : ℕ} (hk : k < (st.segs 4).length) :
    jgap hd Y a e τ st (legOf (st.segs 4) k).b + Y.U + Y.m + 1 ≤ jgap hd Y a e τ st γ.1.b ∧
      -(19 * Y.U) ≤ jgap hd Y a e τ st (legOf (st.segs 4) k).b := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  obtain ⟨hgk, hmono⟩ := hI.jgap_mono hY hγ
  have h1 := (hgk k hk).1
  have hhead := hI.J_gap_head hY hτ hγ (List.ne_nil_of_length_pos (by omega))
  have hm := (hmono k ((st.segs 4).length - 1) (by omega) (by omega)).1
  have hkk : (0 : ℤ) ≤ (((st.segs 4).length - 1 : ℕ) : ℤ) - k := by
    have : k ≤ (st.segs 4).length - 1 := by omega
    have := Nat.cast_le (α := ℤ).2 this; linarith
  constructor
  · nlinarith [h1, hm0, hU]
  · nlinarith [hhead, hm, hkk, hm0, hU, hHU, hflat]

end BGNd

end Percolation.Literature

end
