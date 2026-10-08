import Percolation.Literature.FlatFrame
import Percolation.Util.Linter

/-!
# The flat gait, X: plates of one structure are disjoint

The support boxes of the plates of one structure of
the flat gait (Grimmett, *Percolation*, 2nd ed. (1999), §7.3 pp. 172–174 (A)–(D), case `H < L`)
are pairwise disjoint: along a **diagonal leg** (`DiagLeg.disj`: consecutive plates through the
face, two hops on by the common axis coordinate, three hops on through the face coordinate of the
middle hop, four or more hops on by the older plate's axis coordinate), in a **turn** and against
its start plate (`Turn.disj_start_top`, `Turn.disj_start_hop`, `Turn.disj_top_hop`), and along a
**riser** together with its start plate (`Riser.disj`, by the oriented height for plates two or
more levels apart and by the plane coordinates for neighbours).

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §7.3 pp. 172–174, (A)–(D), Fig. 7.11.
-/

noncomputable section

namespace Percolation.Literature

open LatticeModels Contour
open scoped Classical

namespace BGNd

variable {d : ℕ} [NeZero d]

/-- Two placements have disjoint support boxes. [folklore] -/
def PlateDisj (L H : ℕ) (β β' : BrickPos d) : Prop := Disjoint (boxOf L H β) (boxOf L H β')

omit [NeZero d] in
/-- `PlateDisj` is symmetric. [folklore] -/
theorem PlateDisj.symm {L H : ℕ} {β β' : BrickPos d} (h : PlateDisj L H β β') : PlateDisj L H β' β := Disjoint.symm h

/-! ## Diagonal legs -/

section Diag

variable {hd : 3 ≤ d} {Y : FlatLayout} {e : MDir} {σ : Fin 2 → ℤˣ} {zmode : Option Bool} {q₀ : Fin 2} {l : List (BrickRec d)}

/-- The unit square of a sign is `1`. [folklore] -/
theorem units_sq (u : ℤˣ) : (u : ℤ) * (u : ℤ) = 1 := by rcases Int.units_eq_one_or u with h | h <;> simp [h]

/-- **The plates of a diagonal leg are pairwise disjoint.** [cite: GrimmettPercolation1999, §7.3 pp. 172–174 (B), (D)] -/
theorem DiagLeg.disj (hY : Y.OK) (h : DiagLeg hd Y e σ zmode q₀ l) {k k' : ℕ} (hkk : k < k') (hk' : k' < l.length) :
    PlateDisj Y.L Y.H (legOf l k) (legOf l k') := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  obtain ⟨hak, hsk⟩ := h.axis_sign (k := k) (by omega)
  obtain ⟨hak', hsk'⟩ := h.axis_sign (k := k') hk'
  obtain ⟨g2, g3, g4⟩ := h.gaps (k := k)
  unfold PlateDisj
  -- the oriented centres along an index `j` are `ox σ j`
  have oxe : ∀ (j : Fin 2) (β : BrickPos d), (σ j : ℤ) * β.b (pl hd j) = ox hd σ j β.b := fun _ _ => rfl
  rcases Nat.lt_or_ge k' (k + 4) with hlt | hge
  · -- one, two or three hops on
    have hcases : k' = k + 1 ∨ k' = k + 2 ∨ k' = k + 3 := by omega
    rcases hcases with rfl | rfl | rfl
    · -- through the face: wide behind thin, in the new axis coordinate
      have hst := (h.step (k := k) hk').1
      apply sep_wf (σ (qAt q₀ (k + 1))) (by rw [hak', hak]; exact pl_ne_pl hd (by rw [qAt_succ]; exact oth_ne _)) hsk'
      rw [hak', oxe, oxe, hst, hUe]; linarith
    · -- same axis: thin behind thin, gap `U + t ≥ H + 1`
      have hg := g2 hk'
      rw [qAt_add_two] at hak' hsk'
      apply sep_ff (σ (qAt q₀ k)) (by rw [hak', hak]) hsk hsk'
      rw [hak', oxe, oxe]; linarith
    · -- three hops on: wide behind thin, in the middle face coordinate, gap `2U + m + 1`
      have hg := (g3 hk').1
      have e3 : qAt q₀ (k + 3) = qAt q₀ (k + 1) := by rw [show k + 3 = k + 1 + 2 by ring, qAt_add_two]
      rw [e3] at hak' hsk'
      apply sep_wf (σ (qAt q₀ (k + 1))) (by rw [hak', hak, qAt_succ]; exact pl_ne_pl hd (oth_ne _)) hsk'
      rw [hak', oxe, oxe]; linarith
  · -- four or more hops on: in the older plate's axis coordinate, gap `≥ 2U + 2m + 2`
    have hg4 : 2 * Y.U + 2 * Y.m + 2 ≤ ox hd σ (qAt q₀ k) (legOf l k').b - ox hd σ (qAt q₀ k) (legOf l k).b := by
      have h4 := g4 (by omega) (qAt q₀ k)
      have hmono := (h.mono (k := k + 4) (k' := k') hge hk' (qAt q₀ k)).1
      linarith
    by_cases hax : (legOf l k').a = pl hd (qAt q₀ k)
    · -- same axis: thin behind thin
      have hs' : (legOf l k').s = σ (qAt q₀ k) := by
        rw [hak'] at hax; have := pl_injective hd hax; rw [hsk', this]
      apply sep_ff (σ (qAt q₀ k)) (by rw [hax, hak]) hsk hs'
      rw [hax, oxe, oxe]; linarith
    · -- thin behind wide
      apply sep_fw (σ (qAt q₀ k)) (by rw [hak]; exact fun h' => hax h'.symm) hsk
      rw [hak, oxe, oxe]; linarith

/-- **The records of a diagonal leg are pairwise disjoint.** [folklore] -/
theorem DiagLeg.pairwise (hY : Y.OK) (h : DiagLeg hd Y e σ zmode q₀ l) : l.Pairwise (fun r r' => PlateDisj Y.L Y.H r.1 r'.1) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  -- `l[i]` is newer than `l[j]`: `l[i] = recOf l (len-1-i)`
  have key : ∀ i (hi : i < l.length), (l[i]).1 = legOf l (l.length - 1 - i) := by
    intro i hi
    unfold legOf recOf
    rw [List.getElem?_reverse (by omega), show l.length - 1 - (l.length - 1 - i) = i by omega, List.getElem?_eq_getElem hi]
    rfl
  rw [key i hi, key j hj]
  exact (h.disj hY (k := l.length - 1 - j) (k' := l.length - 1 - i) (by omega) (by omega)).symm

end Diag

/-! ## Turns -/

section Turn

variable {hd : 3 ≤ d} {Y : FlatLayout} {e : MDir} {σ σ' : Fin 2 → ℤˣ} {p : Fin 2} {s : BrickPos d} {l : List (BrickRec d)}

/-- **The top stacking of a turn is disjoint from the start plate** (same axis, exactly `H + 1` on). [folklore] -/
theorem Turn.disj_start_top (h : Turn hd Y e σ σ' p s l) (h0 : 0 < l.length) : PlateDisj Y.L Y.H s (legOf l 0) := by
  have hT := h.h0 h0
  apply sep_ff (σ p) (by rw [hT.axis, h.sAxis]) h.sSign (by rw [hT.sign, h.sSign])
  rw [hT.axis, hT.face, h.sSign, mul_add, ← mul_assoc, units_sq, one_mul]; linarith

/-- **The hop of a turn is disjoint from the top stacking** (through its face). [folklore] -/
theorem Turn.disj_top_hop (hY : Y.OK) (h : Turn hd Y e σ σ' p s l) (h1 : 1 < l.length) : PlateDisj Y.L Y.H (legOf l 0) (legOf l 1) := by
  obtain ⟨hU, hUe, -⟩ := hY.facts
  have hT := h.h0 (by omega); have hD := h.h1 h1
  apply sep_wf (σ' (oth p)) (by rw [hD.axis, hT.axis]; exact pl_ne_pl hd (oth_ne p)) hD.sign
  rw [hD.axis, hD.face, mul_add, ← mul_assoc, units_sq, one_mul, hUe]; linarith

/-- **The hop of a turn is disjoint from the start plate**: the top stacking was pushed towards the
new side. [folklore] -/
theorem Turn.disj_start_hop (hY : Y.OK) (h : Turn hd Y e σ σ' p s l) (h1 : 1 < l.length) : PlateDisj Y.L Y.H s (legOf l 1) := by
  obtain ⟨hU, hUe, -⟩ := hY.facts
  have hT := h.h0 (by omega); have hD := h.h1 h1
  apply sep_wf (σ' (oth p)) (by rw [hD.axis, h.sAxis]; exact pl_ne_pl hd (oth_ne p)) hD.sign
  rw [hD.axis, hD.face, mul_add, ← mul_assoc, units_sq, one_mul, hUe]
  have := hT.push.1
  nlinarith [this, mul_sub (σ' (oth p) : ℤ) ((legOf l 0).b (pl hd (oth p))) (s.b (pl hd (oth p)))]

end Turn

/-! ## Risers -/

section Riser

variable {hd : 3 ≤ d} {Y : FlatLayout} {σ : Fin 2 → ℤˣ} {u : ℤˣ} {q₀ : Fin 2} {s : BrickPos d} {l : List (BrickRec d)}

/-- The plate a horizontal plate of a riser stands on: the start, or the previous landing. [folklore] -/
def Riser.prev (s : BrickPos d) (l : List (BrickRec d)) (j : ℕ) : BrickPos d := if j = 0 then s else legOf l (2 * j - 1)

/-- **Levels of a riser, locally**: each horizontal plate is exactly `U` above the plate it stands
on, and each landing `t ∈ [m+1, H-m-1]` above its horizontal plate (heights read along `u`). [folklore] -/
theorem Riser.uz (h : Riser hd Y σ u q₀ s l) :
    (∀ j, 2 * j < l.length → (u : ℤ) * (legOf l (2 * j)).b (ax0 hd) = (u : ℤ) * (Riser.prev s l j).b (ax0 hd) + Y.U) ∧
      (∀ j, 2 * j + 1 < l.length → (Y.m : ℤ) + 1 ≤ (u : ℤ) * ((legOf l (2 * j + 1)).b (ax0 hd) - (legOf l (2 * j)).b (ax0 hd)) ∧
        (u : ℤ) * ((legOf l (2 * j + 1)).b (ax0 hd) - (legOf l (2 * j)).b (ax0 hd)) ≤ (Y.H : ℤ) - Y.m - 1) := by
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · have := h.level.2 j hj; unfold Riser.prev; exact this
  · have hl := (h.land j hj).drift
    have hs : (legOf l (2 * j)).s = u := ((h.axis_sign (k := 2 * j) (by omega)).1 (by omega)).2
    rw [hs] at hl; exact hl

/-- **Levels of a riser, globally**: the oriented heights of the horizontal plates increase by at
least `U + m + 1` a pair. [folklore] -/
theorem Riser.uz_mono (h : Riser hd Y σ u q₀ s l) {j j' : ℕ} (hjj : j ≤ j') (hj' : 2 * j' < l.length) :
    (u : ℤ) * (legOf l (2 * j)).b (ax0 hd) + ((j' : ℤ) - j) * (Y.U + Y.m + 1) ≤ (u : ℤ) * (legOf l (2 * j')).b (ax0 hd) := by
  induction j' with
  | zero => have : j = 0 := by omega
            subst this; simp
  | succ j' ih =>
    rcases Nat.eq_or_lt_of_le hjj with rfl | hlt
    · simp
    · have ih' := ih (by omega) (by omega)
      obtain ⟨hV, hP⟩ := h.uz
      have h1 := hV (j' + 1) hj'
      unfold Riser.prev at h1; rw [if_neg (by omega), show 2 * (j' + 1) - 1 = 2 * j' + 1 by omega] at h1
      have h2 := (hP j' (by omega)).1
      push_cast at ih' ⊢
      nlinarith [ih', h1, h2, mul_sub (u : ℤ) ((legOf l (2 * j' + 1)).b (ax0 hd)) ((legOf l (2 * j')).b (ax0 hd))]

/-- The start plate is a plane plate of index `q₀`: in particular not horizontal. [folklore] -/
theorem Riser.start_ne_ax0 (h : Riser hd Y σ u q₀ s l) : ax0 hd ≠ s.a := by rw [h.sAxis]; exact (pl_ne_ax0 hd _).symm

/-- **The plates of a riser are pairwise disjoint, and disjoint from the start plate.**
[cite: GrimmettPercolation1999, §7.3 pp. 172–173 (B), (D)] -/
theorem Riser.disj (hY : Y.OK) (h : Riser hd Y σ u q₀ s l) :
    (∀ k, (hk : k < l.length) → PlateDisj Y.L Y.H s (legOf l k)) ∧
      ∀ k k', k < k' → (hk' : k' < l.length) → PlateDisj Y.L Y.H (legOf l k) (legOf l k') := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  obtain ⟨hV, hP⟩ := h.uz
  have uu : (u : ℤ) * (u : ℤ) = 1 := units_sq u
  -- axes and signs
  have axV : ∀ j, (hj : 2 * j < l.length) → (legOf l (2 * j)).a = ax0 hd ∧ (legOf l (2 * j)).s = u := fun j hj =>
    (h.axis_sign (k := 2 * j) hj).1 (by omega)
  have axP : ∀ j, (hj : 2 * j + 1 < l.length) → (legOf l (2 * j + 1)).a = pl hd (qAt q₀ (j + 1)) ∧ (legOf l (2 * j + 1)).s = σ (qAt q₀ (j + 1)) :=
    fun j hj => by have := (h.axis_sign (k := 2 * j + 1) hj).2 (by omega); rwa [show (2 * j + 1) / 2 + 1 = j + 1 by omega] at this
  -- the oriented height of a landing exceeds that of its horizontal plate by `t`
  have uzP : ∀ j, (hj : 2 * j + 1 < l.length) → (u : ℤ) * (legOf l (2 * j + 1)).b (ax0 hd) = (u : ℤ) * (legOf l (2 * j)).b (ax0 hd) +
      (u : ℤ) * ((legOf l (2 * j + 1)).b (ax0 hd) - (legOf l (2 * j)).b (ax0 hd)) := fun j hj => by ring
  -- (1) the start plate against every plate
  have hstart : ∀ k, (hk : k < l.length) → PlateDisj Y.L Y.H s (legOf l k) := by
    intro k hk
    unfold PlateDisj
    rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
    · -- a horizontal plate: thin above (along `u`), at least `U` above the start
      have hk2 : k = 2 * j := by omega
      subst hk2
      obtain ⟨ha, hs⟩ := axV j hk
      apply sep_wf u (by rw [ha]; exact h.start_ne_ax0) hs
      rw [ha]
      have h0 := hV 0 (by omega); unfold Riser.prev at h0; rw [if_pos rfl] at h0
      have hmono := h.uz_mono (j := 0) (j' := j) (Nat.zero_le _) hk
      simp only [Nat.mul_zero, CharP.cast_eq_zero, sub_zero] at hmono h0
      have hprod : (0 : ℤ) * (Y.U + Y.m + 1) ≤ (j : ℤ) * (Y.U + Y.m + 1) := mul_le_mul_of_nonneg_right (by positivity) (by linarith)
      linarith
    · have hk2 : k = 2 * j + 1 := by omega
      subst hk2
      obtain ⟨ha, hs⟩ := axP j hk
      rcases Nat.eq_zero_or_pos j with rfl | hjpos
      · -- the first landing: through the other plane face, pushed forwards off the start
        have hp := h.land 0 hk
        have hv := h.start (by omega)
        simp only [Nat.mul_zero, Nat.zero_add] at hp ha hs ⊢
        rw [show qAt q₀ 1 = oth q₀ by rw [show (1 : ℕ) = 0 + 1 from rfl, qAt_succ, qAt_zero]] at hp ha hs
        apply sep_wf (σ (oth q₀)) (by rw [ha, h.sAxis]; exact pl_ne_pl hd (oth_ne q₀)) hs
        rw [ha, hp.face, mul_add, ← mul_assoc, units_sq, one_mul, hUe]
        have := hv.push.1
        nlinarith [this, mul_sub (σ (oth q₀) : ℤ) ((legOf l 0).b (pl hd (oth q₀))) (s.b (pl hd (oth q₀)))]
      · -- later landings: at least `2U` above along `u`
        apply sep_ww u (ax0 hd) h.start_ne_ax0 (by rw [ha]; exact (pl_ne_ax0 hd _).symm)
        have h0 := hV 0 (by omega); unfold Riser.prev at h0; rw [if_pos rfl] at h0
        have hmono := h.uz_mono (j := 0) (j' := j) (Nat.zero_le _) (by omega)
        have ht := (hP j hk).1
        simp only [Nat.mul_zero, CharP.cast_eq_zero, sub_zero] at hmono h0
        have hj1 : (1 : ℤ) ≤ j := by exact_mod_cast hjpos
        have hprod : (1 : ℤ) * (Y.U + Y.m + 1) ≤ (j : ℤ) * (Y.U + Y.m + 1) := mul_le_mul_of_nonneg_right hj1 (by linarith)
        have e1 := mul_sub (u : ℤ) ((legOf l (2 * j + 1)).b (ax0 hd)) ((legOf l (2 * j)).b (ax0 hd))
        linarith
  refine ⟨hstart, fun k k' hkk hk' => ?_⟩
  unfold PlateDisj
  rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩ <;> rcases Nat.even_or_odd k' with ⟨j', hj'⟩ | ⟨j', hj'⟩
  · -- two horizontal plates: thin above thin along `u`
    have hk2 : k = 2 * j := by omega
    have hk2' : k' = 2 * j' := by omega
    subst hk2 hk2'
    obtain ⟨ha, hs⟩ := axV j (by omega); obtain ⟨ha', hs'⟩ := axV j' hk'
    apply sep_ff u (by rw [ha', ha]) hs hs'
    rw [ha']
    have hmono := h.uz_mono (j := j) (j' := j') (by omega) hk'
    have hjj : (j : ℤ) + 1 ≤ (j' : ℤ) := by exact_mod_cast (show j + 1 ≤ j' by omega)
    have hprod : (1 : ℤ) * (Y.U + Y.m + 1) ≤ ((j' : ℤ) - j) * (Y.U + Y.m + 1) := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    linarith
  · -- a horizontal plate `V_j` and a later landing `P_j'`
    have hk2 : k = 2 * j := by omega
    have hk2' : k' = 2 * j' + 1 := by omega
    subst hk2 hk2'
    obtain ⟨ha, hs⟩ := axV j (by omega); obtain ⟨ha', hs'⟩ := axP j' hk'
    have hp := h.land j' hk'
    rcases Nat.lt_or_ge j' (j + 2) with hlt | hge
    · have hjj : j' = j ∨ j' = j + 1 := by omega
      rcases hjj with rfl | rfl
      · -- its own landing: through the face
        apply sep_wf (σ (qAt q₀ (j' + 1))) (by rw [ha', ha]; exact pl_ne_ax0 hd _) hs'
        rw [ha', hp.face, mul_add, ← mul_assoc, units_sq, one_mul, hUe]; linarith
      · -- the next landing: through the other plane face, after two forward pushes
        have hv := h.up j (by omega)
        have hp0 := h.land j (by omega)
        rw [show 2 * (j + 1) = 2 * j + 2 by ring] at ha' hs' hp ⊢
        have e2 : qAt q₀ (j + 1 + 1) = oth (qAt q₀ (j + 1)) := qAt_succ _ _
        rw [e2] at ha' hs' hp
        apply sep_wf (σ (oth (qAt q₀ (j + 1)))) (by rw [ha', ha]; exact pl_ne_ax0 hd _) hs'
        rw [ha', hp.face, mul_add, ← mul_assoc, units_sq, one_mul, hUe]
        have h1 := hv.push.1; have h2 := hp0.push.1
        nlinarith [h1, h2, mul_sub (σ (oth (qAt q₀ (j + 1))) : ℤ) ((legOf l (2 * j + 2)).b (pl hd (oth (qAt q₀ (j + 1))))) ((legOf l (2 * j + 1)).b (pl hd (oth (qAt q₀ (j + 1))))),
          mul_sub (σ (oth (qAt q₀ (j + 1))) : ℤ) ((legOf l (2 * j + 1)).b (pl hd (oth (qAt q₀ (j + 1))))) ((legOf l (2 * j)).b (pl hd (oth (qAt q₀ (j + 1)))))]
    · -- two or more pairs up: thin above, along `u`, by more than `U + H + 1`
      apply sep_fw u (by rw [ha, ha']; exact (pl_ne_ax0 hd _).symm) hs
      rw [ha]
      have hmono := h.uz_mono (j := j + 1) (j' := j') (by omega) (by omega)
      have hv1 := hV (j + 1) (by omega); unfold Riser.prev at hv1; rw [if_neg (by omega), show 2 * (j + 1) - 1 = 2 * j + 1 by omega] at hv1
      have ht := (hP j (by omega)).1; have ht' := (hP j' hk').1
      have hjj : (j : ℤ) + 2 ≤ (j' : ℤ) := by exact_mod_cast (show j + 2 ≤ j' by omega)
      push_cast at hmono
      have hprod : (1 : ℤ) * (Y.U + Y.m + 1) ≤ ((j' : ℤ) - (j + 1)) * (Y.U + Y.m + 1) := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      have e1 := mul_sub (u : ℤ) ((legOf l (2 * j + 1)).b (ax0 hd)) ((legOf l (2 * j)).b (ax0 hd))
      have e2 := mul_sub (u : ℤ) ((legOf l (2 * j' + 1)).b (ax0 hd)) ((legOf l (2 * j')).b (ax0 hd))
      linarith
  · -- a landing `P_j` and a later horizontal plate `V_j'` (`j < j'`)
    have hk2 : k = 2 * j + 1 := by omega
    have hk2' : k' = 2 * j' := by omega
    subst hk2 hk2'
    obtain ⟨ha, hs⟩ := axP j (by omega); obtain ⟨ha', hs'⟩ := axV j' hk'
    -- `V_j'` is at least `U` above `P_j` along `u` (exactly `U` if `j' = j + 1`)
    apply sep_wf u (by rw [ha', ha]; exact (pl_ne_ax0 hd _).symm) hs'
    rw [ha']
    have hv1 := hV (j + 1) (by omega); unfold Riser.prev at hv1; rw [if_neg (by omega), show 2 * (j + 1) - 1 = 2 * j + 1 by omega] at hv1
    have hmono := h.uz_mono (j := j + 1) (j' := j') (by omega) hk'
    have hjj : (j : ℤ) + 1 ≤ (j' : ℤ) := by exact_mod_cast (show j + 1 ≤ j' by omega)
    push_cast at hmono
    have hprod : (0 : ℤ) * (Y.U + Y.m + 1) ≤ ((j' : ℤ) - (j + 1)) * (Y.U + Y.m + 1) := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    linarith
  · -- two landings `P_j`, `P_j'` (`j < j'`)
    have hk2 : k = 2 * j + 1 := by omega
    have hk2' : k' = 2 * j' + 1 := by omega
    subst hk2 hk2'
    obtain ⟨ha, hs⟩ := axP j (by omega); obtain ⟨ha', hs'⟩ := axP j' hk'
    rcases Nat.lt_or_ge j' (j + 2) with hlt | hge
    · -- the next landing: through the other plane face, pushed forwards
      have hj1 : j' = j + 1 := by omega
      subst hj1
      have hv := h.up j (by omega)
      have hp := h.land (j + 1) hk'
      rw [show 2 * (j + 1) = 2 * j + 2 by ring] at ha' hs' hp ⊢
      have e2 : qAt q₀ (j + 1 + 1) = oth (qAt q₀ (j + 1)) := qAt_succ _ _
      rw [e2] at ha' hs' hp
      rw [show 2 * j + 2 + 1 = 2 * j + 3 by ring] at ha' hs' hp ⊢
      apply sep_wf (σ (oth (qAt q₀ (j + 1)))) (by rw [ha', ha]; exact pl_ne_pl hd (oth_ne _)) hs'
      rw [ha', hp.face, mul_add, ← mul_assoc, units_sq, one_mul, hUe]
      have h1 := hv.push.1
      nlinarith [h1, mul_sub (σ (oth (qAt q₀ (j + 1))) : ℤ) ((legOf l (2 * j + 2)).b (pl hd (oth (qAt q₀ (j + 1))))) ((legOf l (2 * j + 1)).b (pl hd (oth (qAt q₀ (j + 1)))))]
    · -- two or more pairs up: both wide in the height, more than `2U` apart along `u`
      apply sep_ww u (ax0 hd) (by rw [ha]; exact (pl_ne_ax0 hd _).symm) (by rw [ha']; exact (pl_ne_ax0 hd _).symm)
      have hmono := h.uz_mono (j := j + 1) (j' := j') (by omega) (by omega)
      have hv1 := hV (j + 1) (by omega); unfold Riser.prev at hv1; rw [if_neg (by omega), show 2 * (j + 1) - 1 = 2 * j + 1 by omega] at hv1
      have ht' := (hP j' hk').1
      have hjj : (j : ℤ) + 2 ≤ (j' : ℤ) := by exact_mod_cast (show j + 2 ≤ j' by omega)
      push_cast at hmono
      have hprod : (1 : ℤ) * (Y.U + Y.m + 1) ≤ ((j' : ℤ) - (j + 1)) * (Y.U + Y.m + 1) :=
        mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      have e1 := mul_sub (u : ℤ) ((legOf l (2 * j' + 1)).b (ax0 hd)) ((legOf l (2 * j')).b (ax0 hd))
      linarith

end Riser

end BGNd

end Percolation.Literature

end
