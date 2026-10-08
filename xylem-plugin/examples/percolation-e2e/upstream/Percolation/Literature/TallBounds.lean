import Percolation.Literature.TallGeom
import Percolation.Util.Linter

/-!
# The tall gait, XI: absolute positions of the bricks of each segment

From the invariant `TallInv` and an admissible token,
bounds on the base centres of the bricks of segments `A`, `R`, `J`, `T`, of the branch bricks and
of the branch legs, in terms of the token's position, the lanes and the layers (Grimmett,
*Percolation*, 2nd ed. (1999), §7.3, proof of Lemma (7.52), the tube estimates behind (7.54)–(7.55)).

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §7.3 pp. 170–174.
-/

noncomputable section

namespace Percolation.Literature

open LatticeModels Contour
open scoped Classical

namespace BGNd

variable {d : ℕ} [NeZero d]
variable (Y : TallLayout) (hd : 3 ≤ d) (hL : Y.m + 1 ≤ Y.L) (hH : 2 * Y.m + 2 ≤ Y.H) (a : Site 2) (e : MDir) (τ : TTok d)

/-- From a one-sided monotone bound to an absolute one. [folklore] -/
theorem abs_le_of_sign_mul {w x B : ℤ} (hw : w = 1 ∨ w = -1) (h0 : 0 ≤ w * x) (h1 : w * x ≤ B) : |x| ≤ B := by
  rcases hw with rfl | rfl <;> rw [abs_le] <;> constructor <;> linarith

/-- **Positions along segment `A`.** [cite: GrimmettPercolation1999, §7.3 pp. 172–173] -/
theorem boundsA (hY : Y.OK) {st : RS d} (hI : TallInv hd Y hL hH a e τ st) {k : ℕ} (hk : k < st.sA.length) :
    (legOf st.sA k).b (axOf hd e) = τ.pos (axOf hd e) + (sgOf e : ℤ) * Y.ell * k ∧
      |(legOf st.sA k).b (latOf hd e) - τ.pos (latOf hd e)| ≤ Y.Lp + Y.Δw ∧
      (riseDir Y e τ = 0 → |(legOf st.sA k).b (ax0 hd) - Y.zOf e| ≤ Y.ρv) ∧
      (riseDir Y e τ ≠ 0 → 0 ≤ riseDir Y e τ * ((legOf st.sA k).b (ax0 hd) - τ.pos (ax0 hd)) ∧
        riseDir Y e τ * ((legOf st.sA k).b (ax0 hd) - τ.pos (ax0 hd)) ≤ Y.Δw) ∧
      ∀ j, j ≠ axOf hd e → j ≠ latOf hd e → j ≠ ax0 hd → |(legOf st.sA k).b j| ≤ Y.Lp := by
  obtain ⟨hLp0, -, -, hell, -, -, hPw, -, hΔ0, -⟩ := hY.facts
  have hA := hI.invA
  have hne : st.sA ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hz := hA.zero hne
  have hg := hA.grown hne
  have hkPw : (k : ℤ) ≤ Y.Pw := by have := hA.len; exact_mod_cast (by omega : k ≤ Y.Pw)
  have hkΔ : (k : ℤ) * Y.Lp ≤ Y.Δw := by
    unfold TallLayout.Δw; exact mul_le_mul_of_nonneg_right hkPw hLp0
  refine ⟨?_, ?_, ?_, ?_, fun j hj1 hj2 hj3 => hA.oth k hk j hj1 hj2 hj3⟩
  · have := hg.isLeg.b_axis (Nat.zero_le k) (by omega)
    rw [hz] at this; simp only at this
    rw [this]; unfold TallLayout.ell; push_cast; ring
  · by_cases hu : riseDir Y e τ = 0
    · have h0 := hA.lat0 hu k hk
      have hv : (jogDir a e : ℤ) = 1 ∨ (jogDir a e : ℤ) = -1 := by
        rcases Int.units_eq_one_or (jogDir a e) with h | h <;> simp [h]
      have := abs_le_of_sign_mul hv h0.1 (le_trans h0.2 hkΔ)
      linarith
    · have := hA.lat hu k hk; linarith
  · intro hu; exact hA.ht0 hu k hk
  · intro hu
    have h0 := hA.ht hu k hk
    exact ⟨h0.1, le_trans h0.2 hkΔ⟩

/-- Every riser index is at most the riser length. [folklore] -/
theorem le_riserLen {st : RS d} (hI : TallInv hd Y hL hH a e τ st) {k : ℕ} (hk : k < st.sR.length) :
    k ≤ riserLen Y e τ ((legOf st.sR 0).b (ax0 hd)) := by
  have hs := hI.invR.sched
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · exact Nat.zero_le _
  · have := hs (k - 1) (by omega); omega

/-- **Positions along the riser.** [cite: GrimmettPercolation1999, §7.3 pp. 172–173] -/
theorem boundsR (hY : Y.OK) {st : RS d} (hI : TallInv hd Y hL hH a e τ st) {k : ℕ} (hk : k < st.sR.length) :
    (legOf st.sR k).b (ax0 hd) = (legOf st.sR 0).b (ax0 hd) + riseDir Y e τ * Y.ell * k ∧
      (legOf st.sR 0).b (ax0 hd) = (legOf st.sA Y.Pw).b (ax0 hd) + riseDir Y e τ * ((Y.L : ℤ) + 1) ∧
      (Y.Pw : ℤ) * Y.ell + Y.m + 1 ≤ (sgOf e : ℤ) * ((legOf st.sR k).b (axOf hd e) - τ.pos (axOf hd e)) ∧
      (sgOf e : ℤ) * ((legOf st.sR k).b (axOf hd e) - τ.pos (axOf hd e)) ≤ (Y.Pw : ℤ) * Y.ell + Y.H - Y.m - 1 + k * Y.Lp ∧
      |(legOf st.sR k).b (latOf hd e) - τ.pos (latOf hd e)| ≤ Y.Lp + Y.Δw ∧
      ∀ j, j ≠ axOf hd e → j ≠ latOf hd e → j ≠ ax0 hd → |(legOf st.sR k).b j| ≤ Y.Lp := by
  obtain ⟨hLp0, -, hLeq, hell, -, -, hPw, -, hΔ0, -⟩ := hY.facts
  have hR := hI.invR
  have hne : st.sR ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hu : riseDir Y e τ ≠ 0 := fun h => hne (hR.nil h)
  have hg := hR.grown hne
  have ht := hR.turn hne
  have hlenA := hR.prev hne
  have hAPw : Y.Pw < st.sA.length := by omega
  obtain ⟨hAe, -, -, -, -⟩ := boundsA Y hd hL hH a e τ hY hI hAPw
  have huval := riseUnit_val Y e τ hu
  refine ⟨?_, ?_, ?_, ?_, ?_, fun j hj1 hj2 hj3 => hR.oth k hk j hj1 hj2 hj3⟩
  · have := hg.isLeg.b_axis (Nat.zero_le k) (by omega)
    rw [ht.axis, ht.sign, huval] at this
    rw [this]; unfold TallLayout.ell; push_cast; ring
  · have := ht.face; rw [huval] at this; exact this
  · -- forward: the turn's offset, then monotone
    have hlo := ht.longit.1
    have hmono := hR.fwd.mono (Nat.zero_le 0) (Nat.zero_le k) (by omega)
    have e1 : (sgOf e : ℤ) * ((legOf st.sR k).b (axOf hd e) - τ.pos (axOf hd e)) =
        (sgOf e : ℤ) * ((legOf st.sR k).b (axOf hd e) - (legOf st.sR 0).b (axOf hd e)) +
          (sgOf e : ℤ) * ((legOf st.sR 0).b (axOf hd e) - (legOf st.sA Y.Pw).b (axOf hd e)) +
          (sgOf e : ℤ) * ((legOf st.sA Y.Pw).b (axOf hd e) - τ.pos (axOf hd e)) := by ring
    have hs : (sgOf e : ℤ) * (sgOf e : ℤ) = 1 := by rcases Int.units_eq_one_or (sgOf e) with h | h <;> simp [h]
    have e3 : (sgOf e : ℤ) * ((legOf st.sA Y.Pw).b (axOf hd e) - τ.pos (axOf hd e)) = Y.ell * Y.Pw := by
      rw [hAe]
      have : (sgOf e : ℤ) * (τ.pos (axOf hd e) + (sgOf e : ℤ) * Y.ell * Y.Pw - τ.pos (axOf hd e)) =
          ((sgOf e : ℤ) * (sgOf e : ℤ)) * (Y.ell * Y.Pw) := by ring
      rw [this, hs, one_mul]
    rw [e1, e3]; nlinarith
  · have hhi := ht.longit.2
    have hwob := hg.isLeg.abs_b_sub_le (i := axOf hd e) (by rw [ht.axis]; exact axOf_ne_ax0 hd e) (Nat.zero_le k) (by omega)
    have hwob' := (abs_le.1 hwob)
    have e1 : (sgOf e : ℤ) * ((legOf st.sR k).b (axOf hd e) - τ.pos (axOf hd e)) =
        (sgOf e : ℤ) * ((legOf st.sR k).b (axOf hd e) - (legOf st.sR 0).b (axOf hd e)) +
          (sgOf e : ℤ) * ((legOf st.sR 0).b (axOf hd e) - (legOf st.sA Y.Pw).b (axOf hd e)) +
          (sgOf e : ℤ) * ((legOf st.sA Y.Pw).b (axOf hd e) - τ.pos (axOf hd e)) := by ring
    have hs : (sgOf e : ℤ) * (sgOf e : ℤ) = 1 := by rcases Int.units_eq_one_or (sgOf e) with h | h <;> simp [h]
    have e3 : (sgOf e : ℤ) * ((legOf st.sA Y.Pw).b (axOf hd e) - τ.pos (axOf hd e)) = Y.ell * Y.Pw := by
      rw [hAe]
      have : (sgOf e : ℤ) * (τ.pos (axOf hd e) + (sgOf e : ℤ) * Y.ell * Y.Pw - τ.pos (axOf hd e)) =
          ((sgOf e : ℤ) * (sgOf e : ℤ)) * (Y.ell * Y.Pw) := by ring
      rw [this, hs, one_mul]
    rw [e1, e3]
    have hsb : (sgOf e : ℤ) * ((legOf st.sR k).b (axOf hd e) - (legOf st.sR 0).b (axOf hd e)) ≤ k * Y.Lp := by
      have hLp : Y.Lp = (Y.L : ℤ) - Y.m - 1 := rfl
      rw [hLp]
      rcases Int.units_eq_one_or (sgOf e) with h | h <;> simp [h] <;> nlinarith [hwob'.1, hwob'.2]
    nlinarith
  · have hlat := hR.lat k hk
    have hkn := le_riserLen Y hd hL hH a e τ hI hk
    have hcnt := nForcedR_le Y _ k hkn
    have : (nForcedR Y (riserLen Y e τ ((legOf st.sR 0).b (ax0 hd))) k : ℤ) * Y.Lp ≤ Y.Δw := by
      unfold TallLayout.Δw; exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcnt) hLp0
    linarith

end BGNd

end Percolation.Literature

end

namespace Percolation.Literature.BGNd

open LatticeModels Contour
open scoped Classical

variable {d : ℕ} [NeZero d]
variable (Y : TallLayout) (hd : 3 ≤ d) (hL : Y.m + 1 ≤ Y.L) (hH : 2 * Y.m + 2 ≤ Y.H) (a : Site 2) (e : MDir) (τ : TTok d)

/-- Every jog index is at most the jog length. [folklore] -/
theorem le_jogLen {st : RS d} (hI : TallInv hd Y hL hH a e τ st) {k : ℕ} (hk : k < st.sJ.length) :
    k ≤ jogLen Y a e ((legOf st.sJ 0).b (latOf hd e)) := by
  have hs := hI.invJ.sched
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · exact Nat.zero_le _
  · have := hs (k - 1) (by omega); omega

/-- **The last brick of the entry segment**: forward and lateral position. [folklore] -/
theorem bounds_entryLast (hY : Y.OK) {st : RS d} (hI : TallInv hd Y hL hH a e τ st) (hJ : st.sJ ≠ [])
    (hNR : st.sR ≠ [] → riserLen Y e τ ((legOf st.sR 0).b (ax0 hd)) ≤ Y.N₁) :
    (Y.Pw : ℤ) * Y.ell ≤ (sgOf e : ℤ) * ((entryLast Y e τ st.sA st.sR).b (axOf hd e) - τ.pos (axOf hd e)) ∧
      (sgOf e : ℤ) * ((entryLast Y e τ st.sA st.sR).b (axOf hd e) - τ.pos (axOf hd e)) ≤
        (Y.Pw : ℤ) * Y.ell + Y.H + Y.N₁ * Y.Lp ∧
      |(entryLast Y e τ st.sA st.sR).b (latOf hd e) - τ.pos (latOf hd e)| ≤ Y.Lp + Y.Δw := by
  obtain ⟨hLp0, -, -, hell, hmH, -, hPw, -, hΔ0, -⟩ := hY.facts
  have hlenA := hI.invJ.prevA hJ
  unfold entryLast
  by_cases hu : riseDir Y e τ = 0
  · rw [if_pos hu]
    have hk : st.sA.length - 1 < st.sA.length := by omega
    obtain ⟨hAe, hAf, -, -, -⟩ := boundsA Y hd hL hH a e τ hY hI hk
    have hPw' : ((st.sA.length - 1 : ℕ) : ℤ) = Y.Pw := by rw [hlenA]; simp
    rw [hAe, hPw']
    have hs : (sgOf e : ℤ) * (sgOf e : ℤ) = 1 := by rcases Int.units_eq_one_or (sgOf e) with h | h <;> simp [h]
    have e1 : (sgOf e : ℤ) * (τ.pos (axOf hd e) + (sgOf e : ℤ) * Y.ell * Y.Pw - τ.pos (axOf hd e)) =
        ((sgOf e : ℤ) * (sgOf e : ℤ)) * (Y.ell * Y.Pw) := by ring
    rw [e1, hs, one_mul]
    refine ⟨by nlinarith, ?_, hAf⟩
    have : (0 : ℤ) ≤ Y.N₁ * Y.Lp := by positivity
    have : (0 : ℤ) ≤ Y.H := by positivity
    nlinarith
  · rw [if_neg hu]
    obtain ⟨hRne, hdone⟩ := hI.invJ.prevR hJ hu
    have hk : st.sR.length - 1 < st.sR.length := by have := List.length_pos_of_ne_nil hRne; omega
    obtain ⟨-, -, hlo, hhi, hlat, -⟩ := boundsR Y hd hL hH a e τ hY hI hk
    have hkn := le_riserLen Y hd hL hH a e τ hI hk
    have hN := hNR hRne
    have hkN : ((st.sR.length - 1 : ℕ) : ℤ) ≤ Y.N₁ := by exact_mod_cast hkn.trans hN
    refine ⟨by linarith, ?_, hlat⟩
    have : ((st.sR.length - 1 : ℕ) : ℤ) * Y.Lp ≤ Y.N₁ * Y.Lp := mul_le_mul_of_nonneg_right hkN hLp0
    have hm0 : (0 : ℤ) ≤ Y.m := by positivity
    linarith

/-- **Positions along the jog.** [cite: GrimmettPercolation1999, §7.3 pp. 172–173] -/
theorem boundsJ (hY : Y.OK) {st : RS d} (hI : TallInv hd Y hL hH a e τ st)
    (hNR : st.sR ≠ [] → riserLen Y e τ ((legOf st.sR 0).b (ax0 hd)) ≤ Y.N₁) {k : ℕ} (hk : k < st.sJ.length) :
    (legOf st.sJ k).b (latOf hd e) = (legOf st.sJ 0).b (latOf hd e) + (jogDir a e : ℤ) * Y.ell * k ∧
      (legOf st.sJ 0).b (latOf hd e) = (entryLast Y e τ st.sA st.sR).b (latOf hd e) + (jogDir a e : ℤ) * ((Y.L : ℤ) + 1) ∧
      0 ≤ (sgOf e : ℤ) * ((legOf st.sJ k).b (axOf hd e) - (legOf st.sJ 0).b (axOf hd e)) ∧
      (sgOf e : ℤ) * ((legOf st.sJ k).b (axOf hd e) - (legOf st.sJ 0).b (axOf hd e)) ≤ k * Y.Lp ∧
      (Y.Pw : ℤ) * Y.ell ≤ (sgOf e : ℤ) * ((legOf st.sJ 0).b (axOf hd e) - τ.pos (axOf hd e)) ∧
      (sgOf e : ℤ) * ((legOf st.sJ 0).b (axOf hd e) - τ.pos (axOf hd e)) ≤ (Y.Pw : ℤ) * Y.ell + Y.H + Y.N₁ * Y.Lp + Y.ell + Y.Lp ∧
      |(legOf st.sJ k).b (ax0 hd) - Y.zOf e| ≤ Y.ρv ∧
      ∀ j, j ≠ axOf hd e → j ≠ latOf hd e → j ≠ ax0 hd → |(legOf st.sJ k).b j| ≤ Y.Lp := by
  obtain ⟨hLp0, -, hLeq, hell, hmH, -, hPw, -, hΔ0, -⟩ := hY.facts
  have hJI := hI.invJ
  have hne : st.sJ ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hg := hJI.grown hne
  have ht := hJI.turn hne
  obtain ⟨hElo, hEhi, -⟩ := bounds_entryLast Y hd hL hH a e τ hY hI hne hNR
  refine ⟨?_, ht.face, ?_, ?_, ?_, ?_, hJI.ht k hk, fun j hj1 hj2 hj3 => hJI.oth k hk j hj1 hj2 hj3⟩
  · have := hg.isLeg.b_axis (Nat.zero_le k) (by omega)
    rw [ht.axis, ht.sign] at this
    rw [this]; unfold TallLayout.ell; push_cast; ring
  · exact hJI.fwd.mono (Nat.zero_le 0) (Nat.zero_le k) (by omega)
  · have hwob := hg.isLeg.abs_b_sub_le (i := axOf hd e) (by rw [ht.axis]; exact (latOf_ne_axOf hd e).symm) (Nat.zero_le k) (by omega)
    have hwob' := abs_le.1 hwob
    have hLp : Y.Lp = (Y.L : ℤ) - Y.m - 1 := rfl
    rw [hLp]
    rcases Int.units_eq_one_or (sgOf e) with h | h <;> simp [h] <;> nlinarith [hwob'.1, hwob'.2]
  · have h0 := hJI.fwd0 hne; linarith
  · -- the turn adds at most `max(H - m - 1, L')` forward
    have hfw : (sgOf e : ℤ) * ((legOf st.sJ 0).b (axOf hd e) - (entryLast Y e τ st.sA st.sR).b (axOf hd e)) ≤ Y.ell + Y.Lp := by
      by_cases hu : riseDir Y e τ = 0
      · -- off `A`: the old axis, offset at most `H - m - 1`
        have := ht.longit.2
        rw [if_pos hu, if_pos hu] at this
        have hm0 : (0 : ℤ) ≤ Y.m := by positivity
        linarith
      · -- off `R`: a remaining coordinate, wobble at most `L'`
        have := ht.other (axOf hd e) (by rw [if_neg hu]; exact axOf_ne_ax0 hd e) (latOf_ne_axOf hd e).symm
        have h' := abs_le.1 this
        have hLp : Y.Lp = (Y.L : ℤ) - Y.m - 1 := rfl
        have hl1 : (1 : ℤ) ≤ Y.ell := by unfold TallLayout.ell; push_cast; omega
        rcases Int.units_eq_one_or (sgOf e) with h | h <;> simp [h] <;> linarith [h'.1, h'.2]
    linarith

/-- **Positions along the trunk.** [cite: GrimmettPercolation1999, §7.3 pp. 172–174] -/
theorem boundsT (hY : Y.OK) {st : RS d} (hI : TallInv hd Y hL hH a e τ st)
    (hNR : st.sR ≠ [] → riserLen Y e τ ((legOf st.sR 0).b (ax0 hd)) ≤ Y.N₁)
    (hNJ : st.sJ ≠ [] → jogLen Y a e ((legOf st.sJ 0).b (latOf hd e)) ≤ Y.N₁) {k : ℕ} (hk : k < st.sT.length) :
    (legOf st.sT k).b (axOf hd e) = (legOf st.sT 0).b (axOf hd e) + (sgOf e : ℤ) * Y.ell * k ∧
      (Y.Pw : ℤ) * Y.ell + Y.L + 1 ≤ (sgOf e : ℤ) * ((legOf st.sT 0).b (axOf hd e) - τ.pos (axOf hd e)) ∧
      (sgOf e : ℤ) * ((legOf st.sT 0).b (axOf hd e) - τ.pos (axOf hd e)) ≤
        (Y.Pw : ℤ) * Y.ell + Y.H + 2 * Y.N₁ * Y.Lp + Y.ell + Y.Lp + Y.L + 1 ∧
      |(legOf st.sT 0).b (latOf hd e) - Y.lane (tgtCell a e) e| ≤ Y.ell ∧
      |(legOf st.sT k).b (latOf hd e) - Y.lane (tgtCell a e) e| ≤ Y.ell + Y.Lp + 4 * Y.Δw ∧
      |(legOf st.sT k).b (ax0 hd) - Y.zOf e| ≤ Y.ρv ∧
      ∀ j, j ≠ axOf hd e → j ≠ latOf hd e → j ≠ ax0 hd → |(legOf st.sT k).b j| ≤ Y.Lp := by
  obtain ⟨hLp0, -, hLeq, hell, hmH, -, hPw, -, hΔ0, -⟩ := hY.facts
  have hTI := hI.invT
  have hne : st.sT ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hg := hTI.grown hne
  have ht := hTI.turn hne
  obtain ⟨hJne, hJdone⟩ := hTI.prev hne
  have hkJ : st.sJ.length - 1 < st.sJ.length := by have := List.length_pos_of_ne_nil hJne; omega
  obtain ⟨-, -, hJlo, hJhi, hJ0lo, hJ0hi, -, -⟩ := boundsJ Y hd hL hH a e τ hY hI hNR hkJ
  have hkn := le_jogLen Y hd hL hH a e τ hI hkJ
  have hN := hNJ hJne
  have hkN : ((st.sJ.length - 1 : ℕ) : ℤ) ≤ Y.N₁ := by exact_mod_cast hkn.trans hN
  have hface := ht.face
  have hfit := hTI.fit hne
  refine ⟨?_, ?_, ?_, hfit, ?_, hTI.ht k hk, fun j hj1 hj2 hj3 => hTI.oth k hk j hj1 hj2 hj3⟩
  · have := hg.isLeg.b_axis (Nat.zero_le k) (by omega)
    rw [ht.axis, ht.sign] at this
    rw [this]; unfold TallLayout.ell; push_cast; ring
  · have hs : (sgOf e : ℤ) * (sgOf e : ℤ) = 1 := by rcases Int.units_eq_one_or (sgOf e) with h | h <;> simp [h]
    have e1 : (sgOf e : ℤ) * ((legOf st.sT 0).b (axOf hd e) - τ.pos (axOf hd e)) =
        (sgOf e : ℤ) * ((legOf st.sJ (st.sJ.length - 1)).b (axOf hd e) - (legOf st.sJ 0).b (axOf hd e)) +
          (sgOf e : ℤ) * ((legOf st.sJ 0).b (axOf hd e) - τ.pos (axOf hd e)) + ((sgOf e : ℤ) * (sgOf e : ℤ)) * ((Y.L : ℤ) + 1) := by
      rw [hface]; ring
    rw [e1, hs]; nlinarith
  · have hs : (sgOf e : ℤ) * (sgOf e : ℤ) = 1 := by rcases Int.units_eq_one_or (sgOf e) with h | h <;> simp [h]
    have e1 : (sgOf e : ℤ) * ((legOf st.sT 0).b (axOf hd e) - τ.pos (axOf hd e)) =
        (sgOf e : ℤ) * ((legOf st.sJ (st.sJ.length - 1)).b (axOf hd e) - (legOf st.sJ 0).b (axOf hd e)) +
          (sgOf e : ℤ) * ((legOf st.sJ 0).b (axOf hd e) - τ.pos (axOf hd e)) + ((sgOf e : ℤ) * (sgOf e : ℤ)) * ((Y.L : ℤ) + 1) := by
      rw [hface]; ring
    rw [e1, hs]
    have : ((st.sJ.length - 1 : ℕ) : ℤ) * Y.Lp ≤ Y.N₁ * Y.Lp := mul_le_mul_of_nonneg_right hkN hLp0
    nlinarith
  · have hlat := hTI.lat k hk
    have hcnt := nForced_le Y e (n1Of hd Y a e st.sT) (n2Of hd Y a e st.sT) k
    have : (nForced Y e (n1Of hd Y a e st.sT) (n2Of hd Y a e st.sT) k : ℤ) * Y.Lp ≤ 4 * Y.Δw := by
      unfold TallLayout.Δw
      have : (nForced Y e (n1Of hd Y a e st.sT) (n2Of hd Y a e st.sT) k : ℤ) ≤ 4 * Y.Pw := by exact_mod_cast hcnt
      nlinarith
    have h1 := abs_le.1 hlat; have h2 := abs_le.1 hfit
    rw [abs_le]; constructor <;> linarith

end Percolation.Literature.BGNd

namespace Percolation.Literature.BGNd

open LatticeModels Contour
open scoped Classical

variable {d : ℕ} [NeZero d]
variable (Y : TallLayout) (hd : 3 ≤ d) (hL : Y.m + 1 ≤ Y.L) (hH : 2 * Y.m + 2 ≤ Y.H) (a : Site 2) (e : MDir) (τ : TTok d)

omit [NeZero d] in
/-- **Passing a lane, uniformly in the direction of travel**: `s (b - lane) ≥ -(m+1)`. [folklore] -/
theorem passed_iff (c : Site 2) (v : ℤˣ) (b : ℤ) :
    passed Y e c v b ↔ -((Y.m : ℤ) + 1) ≤ (sgOf e : ℤ) * (b - Y.lane c (latDir e (decide ((v : ℤ) = 1)))) := by
  unfold passed
  rcases Int.units_eq_one_or (sgOf e) with h | h <;> simp [h] <;> constructor <;> intro h' <;> linarith

/-- The lane of the lateral port of sign `w` of the target cell. [folklore] -/
def brLane (w : ℤˣ) : ℤ := Y.lane (tgtCell a e) (latDir e (decide ((w : ℤ) = 1)))

omit [NeZero d] in
/-- The lateral port lanes in coordinates: `X_e + (±Λ) + parity · Λ_J`. [folklore] -/
theorem brLane_eq (w : ℤˣ) :
    brLane Y a e w = Y.ctr (tgtCell a e) e.1 + (if (w : ℤ) = 1 then Y.lam else -Y.lam) + TallLayout.cpar (tgtCell a e) * Y.lamJ := by
  unfold brLane TallLayout.lane TallLayout.nu latDir
  have : (⟨1 - (1 - e.1.val), by have := e.1.isLt; omega⟩ : Fin 2) = e.1 := by
    apply Fin.ext; simp only; have := e.1.isLt; omega
  simp only [this, decide_eq_true_eq]

/-- **Positions of a branch brick.** [cite: GrimmettPercolation1999, §7.3 pp. 172–174] -/
theorem boundsG (hY : Y.OK) {st : RS d} (hI : TallInv hd Y hL hH a e τ st)
    (hNR : st.sR ≠ [] → riserLen Y e τ ((legOf st.sR 0).b (ax0 hd)) ≤ Y.N₁)
    (hNJ : st.sJ ≠ [] → jogLen Y a e ((legOf st.sJ 0).b (latOf hd e)) ≤ Y.N₁) (hlen : st.sT.length ≤ Y.Rmax)
    {w : ℤˣ} {g : BrickRec d} {n : ℕ}
    (hg : n < st.sT.length ∧ IsTurn Y.m Y.L Y.H (axOf hd e) (sgOf e) (latOf hd e) w (legOf st.sT n) g.1 ∧
      |g.1.b (ax0 hd) - Y.zOf e| ≤ Y.ρv ∧ ∀ j, j ≠ axOf hd e → j ≠ latOf hd e → j ≠ ax0 hd → |g.1.b j| ≤ Y.Lp)
    (hn : n = brIdx Y a e w ((legOf st.sT 0).b (axOf hd e))) (hn1 : 1 ≤ n) :
    g.1.a = latOf hd e ∧ g.1.s = w ∧
      g.1.b (latOf hd e) = (legOf st.sT n).b (latOf hd e) + (w : ℤ) * ((Y.L : ℤ) + 1) ∧
      |(legOf st.sT n).b (latOf hd e) - Y.lane (tgtCell a e) e| ≤ Y.ell + Y.Lp + 4 * Y.Δw ∧
      0 ≤ (sgOf e : ℤ) * (g.1.b (axOf hd e) - brLane Y a e w) ∧
      (sgOf e : ℤ) * (g.1.b (axOf hd e) - brLane Y a e w) ≤ Y.ell + Y.H ∧
      |g.1.b (ax0 hd) - Y.zOf e| ≤ Y.ρv ∧ ∀ j, j ≠ axOf hd e → j ≠ latOf hd e → j ≠ ax0 hd → |g.1.b j| ≤ Y.Lp := by
  obtain ⟨hLp0, -, hLeq, hell, hmH, -, hPw, -, hΔ0, -⟩ := hY.facts
  obtain ⟨hnlt, hturn, hht, hoth⟩ := hg
  obtain ⟨hTe, -, -, -, hTlat, -, -⟩ := boundsT Y hd hL hH a e τ hY hI hNR hNJ hnlt
  obtain ⟨hTe', -, -, -, -, -, -⟩ := boundsT Y hd hL hH a e τ hY hI hNR hNJ (show n - 1 < st.sT.length by omega)
  refine ⟨hturn.axis, hturn.sign, hturn.face, hTlat, ?_, ?_, hht, hoth⟩
  · -- passed at `n`
    have hp : passed Y e (tgtCell a e) w ((legOf st.sT 0).b (axOf hd e) + (sgOf e : ℤ) * (n * Y.ell)) := by
      have := of_firstIdx_lt (p := fun k => passed Y e (tgtCell a e) w ((legOf st.sT 0).b (axOf hd e) + (sgOf e : ℤ) * (k * Y.ell)))
        (N := Y.Rmax) (by rw [← brIdx, ← hn]; omega)
      rw [← brIdx, ← hn] at this; exact this
    rw [passed_iff] at hp
    have hlo := hturn.longit.1
    have e1 : (legOf st.sT 0).b (axOf hd e) + (sgOf e : ℤ) * (n * Y.ell) = (legOf st.sT n).b (axOf hd e) := by rw [hTe]; ring
    rw [e1] at hp
    unfold brLane
    have hm0 : (0 : ℤ) ≤ Y.m := by positivity
    nlinarith
  · -- not passed at `n - 1`
    have hnp : ¬passed Y e (tgtCell a e) w ((legOf st.sT 0).b (axOf hd e) + (sgOf e : ℤ) * ((n - 1 : ℕ) * Y.ell)) := by
      have := not_of_lt_firstIdx (p := fun k => passed Y e (tgtCell a e) w ((legOf st.sT 0).b (axOf hd e) + (sgOf e : ℤ) * (k * Y.ell)))
        (N := Y.Rmax) (k := n - 1) (by rw [← brIdx, ← hn]; omega)
      exact this
    rw [passed_iff] at hnp
    push Not at hnp
    have hhi := hturn.longit.2
    have e1 : (legOf st.sT 0).b (axOf hd e) + (sgOf e : ℤ) * ((n - 1 : ℕ) * Y.ell) = (legOf st.sT n).b (axOf hd e) - (sgOf e : ℤ) * Y.ell := by
      rw [hTe]; push_cast [Nat.cast_sub hn1]; ring
    rw [e1] at hnp
    unfold brLane
    have hs : (sgOf e : ℤ) * (sgOf e : ℤ) = 1 := by rcases Int.units_eq_one_or (sgOf e) with h | h <;> simp [h]
    have e2 : (sgOf e : ℤ) * ((legOf st.sT n).b (axOf hd e) - (sgOf e : ℤ) * Y.ell - Y.lane (tgtCell a e) (latDir e (decide ((w : ℤ) = 1)))) =
        (sgOf e : ℤ) * ((legOf st.sT n).b (axOf hd e) - Y.lane (tgtCell a e) (latDir e (decide ((w : ℤ) = 1)))) -
          ((sgOf e : ℤ) * (sgOf e : ℤ)) * Y.ell := by ring
    rw [e2, hs] at hnp
    have hm0 : (0 : ℤ) ≤ Y.m := by positivity
    nlinarith

/-- **Positions along a branch leg.** [cite: GrimmettPercolation1999, §7.3 pp. 172–174] -/
theorem boundsB {w : ℤˣ} {g : BrickRec d} {sB : List (BrickRec d)} {D : Prop}
    (h : InvB hd Y hL hH a e w (some g) sB D) (hgax : g.1.a = latOf hd e) (hgs : g.1.s = w) {k : ℕ} (hk : k ≤ sB.length) :
    (legOf (sB ++ [g]) k).b (latOf hd e) = g.1.b (latOf hd e) + (w : ℤ) * Y.ell * k ∧
      |(legOf (sB ++ [g]) k).b (axOf hd e) - g.1.b (axOf hd e)| ≤ Y.Lp ∧
      |(legOf (sB ++ [g]) k).b (ax0 hd) - Y.zOf e| ≤ Y.ρv ∧
      ∀ j, j ≠ axOf hd e → j ≠ latOf hd e → j ≠ ax0 hd → |(legOf (sB ++ [g]) k).b j| ≤ Y.Lp := by
  refine ⟨?_, h.lng g rfl k hk, h.ht g rfl k hk, fun j hj1 hj2 hj3 => h.oth g rfl k hk j hj1 hj2 hj3⟩
  have h0 := legOf_append_singleton_zero sB g
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · rw [h0]; simp
  · have hne : sB ≠ [] := List.ne_nil_of_length_pos (by omega)
    have hg' := h.grown g rfl hne
    have := hg'.isLeg.b_axis (Nat.zero_le k) (by simp; omega)
    rw [h0, hgax, hgs] at this
    rw [this]; unfold TallLayout.ell; push_cast; ring

end Percolation.Literature.BGNd
