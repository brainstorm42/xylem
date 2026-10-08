import Percolation.Literature.FlatDisjA
import Percolation.Util.Linter

/-!
# The flat gait, XI–XIII

This module gathers 3 consecutive parts of the flat-gait development, in order:
XI: the entry structures are disjoint from one another ·
XII: forks — the flipped coordinate, the two sides, the continuing trunk ·
XIII: assembling disjointness, I — the entry and the jog.
Part 1 follows; the later parts keep their own headers below.

# Part 1 (The flat gait, XI): the entry structures are disjoint from one another

Cross-structure disjointness at the entry of a cell in
the flat gait (Grimmett, *Percolation*, 2nd ed. (1999), §7.3 pp. 172–174, case `H < L`): every
plate of the riser (and the first plate) lies behind the riser's head in both oriented plane
coordinates (`Riser.plane_le_head`); the preamble's plates are thin-forwards beyond it
(`disj_entry_pre`); the two plates of the turn towards the jog clear the preamble and the entry
(`disj_turn_top_of_le`, `disj_turnhop_prev`, `disj_turnhop_of_le`), the top stacking by the kept
coordinate, the hop by the flipped coordinate against the last two plates and by the kept
coordinate against everything older.

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §7.3 pp. 172–174, (A)–(D), Fig. 7.11.
-/

noncomputable section

namespace Percolation.Literature

open LatticeModels Contour
open scoped Classical

namespace BGNd

variable {d : ℕ} [NeZero d] {hd : 3 ≤ d} {Y : FlatLayout} {e : MDir}

/-! ## The entry lies behind the riser's head -/

section Entry

variable {σ : Fin 2 → ℤˣ} {u : ℤˣ} {q₀ : Fin 2} {s : BrickPos d} {l : List (BrickRec d)}

/-- **Along a riser both oriented plane coordinates are monotone.** [folklore] -/
theorem Riser.plane_mono (h : Riser hd Y σ u q₀ s l) {k k' : ℕ} (hkk : k ≤ k') (hk' : k' < l.length) (i : Fin 2) :
    ox hd σ i (legOf l k).b ≤ ox hd σ i (legOf l k').b := by
  induction k' with
  | zero => have : k = 0 := by omega
            subst this; exact le_rfl
  | succ k' ih =>
    rcases Nat.eq_or_lt_of_le hkk with rfl | hlt
    · exact le_rfl
    · have := (h.plane hk' i).2 (by omega)
      rw [Nat.add_sub_cancel] at this
      exact (ih (by omega) (by omega)).trans this

/-- **Every plate of a riser, and its start, lies behind the head** in both oriented plane
coordinates. [folklore] -/
theorem Riser.plane_le_head (h : Riser hd Y σ u q₀ s l) (hl : 0 < l.length) (i : Fin 2) :
    ox hd σ i s.b ≤ ox hd σ i (legOf l (l.length - 1)).b ∧ ∀ k, k < l.length → ox hd σ i (legOf l k).b ≤ ox hd σ i (legOf l (l.length - 1)).b :=
  ⟨(h.plane (k := l.length - 1) (by omega) i).1, fun k hk => h.plane_mono (by omega) (by omega) i⟩

/-- **Behind a landing head through the axis `q`**, every older plate of the riser and the start
is at least `U` behind along `q`. [folklore] -/
theorem Riser.plane_le_head_land (h : Riser hd Y σ u q₀ s l) {j : ℕ} (hlen : l.length = 2 * j + 2) :
    ox hd σ (qAt q₀ (j + 1)) s.b + Y.U ≤ ox hd σ (qAt q₀ (j + 1)) (legOf l (2 * j + 1)).b ∧
      ∀ k, k ≤ 2 * j → ox hd σ (qAt q₀ (j + 1)) (legOf l k).b + Y.U ≤ ox hd σ (qAt q₀ (j + 1)) (legOf l (2 * j + 1)).b := by
  have hf := h.land_face (j := j) (by omega)
  have hv := h.plane_le_head (by omega) (qAt q₀ (j + 1))
  constructor
  · have := (h.plane (k := 2 * j) (by omega) (qAt q₀ (j + 1))).1; linarith
  · intro k hk; have := h.plane_mono (k := k) (k' := 2 * j) hk (by omega) (qAt q₀ (j + 1)); linarith

end Entry

/-! ## The preamble against the entry -/

section Pre

variable {σ : Fin 2 → ℤˣ} {zmode : Option Bool} {q₁ : Fin 2} {pe : List (BrickRec d)}

/-- **A plate whose axis coordinate is at least `U` beyond a plate `X` of the entry is disjoint
from `X`** — `X` being wide in that coordinate, or thin with the same sign. [folklore] -/
theorem disj_of_axis_beyond (hY : Y.OK) {X P : BrickPos d} {q : Fin 2} (haP : P.a = pl hd q) (hsP : P.s = σ q)
    (hX : X.a ≠ pl hd q ∨ (X.a = pl hd q ∧ X.s = σ q)) (h : ox hd σ q X.b + Y.U ≤ ox hd σ q P.b) : PlateDisj Y.L Y.H X P := by
  obtain ⟨hU, hUe, -, -, -, hHU, -⟩ := hY.facts
  unfold PlateDisj
  rcases hX with hX | ⟨hXa, hXs⟩
  · apply sep_wf (σ q) (by rw [haP]; exact fun h' => hX h'.symm) hsP
    rw [haP]; unfold ox at h; linarith
  · apply sep_ff (σ q) (by rw [haP, hXa]) hXs hsP
    rw [haP]; unfold ox at h; linarith

/-- **The preamble is disjoint from the entry**: a plate of the extended preamble other than its
start is thin-forwards at least `U` beyond every plate lying behind the start in both oriented
plane coordinates (and being wide, or thin with the sign of `σ`, in each). [folklore] -/
theorem disj_entry_pre (hY : Y.OK) (hP : DiagLeg hd Y e σ zmode q₁ pe) {X : BrickPos d}
    (hXle : ∀ i : Fin 2, ox hd σ i X.b ≤ ox hd σ i (legOf pe 0).b)
    (hXax : ∀ i : Fin 2, X.a ≠ pl hd i ∨ (X.a = pl hd i ∧ X.s = σ i)) {k : ℕ} (hk : k + 1 < pe.length) :
    PlateDisj Y.L Y.H X (legOf pe (k + 1)) := by
  obtain ⟨ha, hs⟩ := hP.axis_sign (k := k + 1) hk
  have hst := (hP.step (k := k) hk).1
  have hmono := (hP.mono (k := 0) (k' := k) (Nat.zero_le _) (by omega) (qAt q₁ (k + 1))).1
  exact disj_of_axis_beyond hY ha hs (hXax _) (by have := hXle (qAt q₁ (k + 1)); linarith)

end Pre

/-! ## A turn against the structures behind its start -/

section TurnBack

variable {σ σ' : Fin 2 → ℤˣ} {p : Fin 2} {s : BrickPos d} {l : List (BrickRec d)}

/-- **The top stacking of a turn is disjoint from every plate at least `U` behind the start along
the kept coordinate** (wide, or thin with the sign of `σ`). [folklore] -/
theorem disj_turn_top_of_le (hY : Y.OK) (h : Turn hd Y e σ σ' p s l) (h0 : 0 < l.length) {X : BrickPos d}
    (hX : X.a ≠ pl hd p ∨ (X.a = pl hd p ∧ X.s = σ p)) (hle : ox hd σ p X.b + Y.U ≤ ox hd σ p s.b) :
    PlateDisj Y.L Y.H X (legOf l 0) := by
  obtain ⟨hU, hUe, -, -, -, hHU, -, -, hm0⟩ := hY.facts
  have hT := h.h0 h0
  have hface : ox hd σ p (legOf l 0).b = ox hd σ p s.b + ((Y.H : ℤ) + 1) := by
    unfold ox; rw [hT.face, h.sSign, mul_add, ← mul_assoc, units_sq, one_mul]
  have hH0 : (0 : ℤ) ≤ Y.H := by positivity
  exact disj_of_axis_beyond hY hT.axis (by rw [hT.sign, h.sSign]) hX (by linarith)

/-- **The hop of a turn is disjoint from the plate the start was entered from** (a plate of the
flipped axis with the old sign, at most `t ≤ U` behind along the flipped coordinate, read the new
way): thin-backwards behind thin-forwards. [folklore] -/
theorem disj_turnhop_prev (hY : Y.OK) (h : Turn hd Y e σ σ' p s l) (h1 : 1 < l.length) (hflip : σ' (oth p) = -σ (oth p))
    {X : BrickPos d} (hXa : X.a = pl hd (oth p)) (hXs : X.s = σ (oth p))
    (hle : ox hd σ' (oth p) X.b ≤ ox hd σ' (oth p) s.b + Y.U) : PlateDisj Y.L Y.H X (legOf l 1) := by
  obtain ⟨hU, hUe, -⟩ := hY.facts
  have hT := h.h0 (by omega); have hD := h.h1 h1
  unfold PlateDisj
  apply sep_bf (σ' (oth p)) (by rw [hD.axis, hXa]) (by rw [hXs, hflip, neg_neg]) hD.sign
  rw [hD.axis, hD.face, mul_add, ← mul_assoc, units_sq, one_mul, hUe]
  have hpush := hT.push.1
  unfold ox at hle
  nlinarith [hle, hpush, hUe, mul_sub (σ' (oth p) : ℤ) ((legOf l 0).b (pl hd (oth p))) (s.b (pl hd (oth p)))]

/-- **The hop of a turn is disjoint from every plate well behind the start along the kept
coordinate**: a thin plate (of axis `p`, sign `σ p`) at least `U` behind, or a wide plate at least
`2U` behind. [folklore] -/
theorem disj_turnhop_of_le (hY : Y.OK) (h : Turn hd Y e σ σ' p s l) (h1 : 1 < l.length) {X : BrickPos d}
    (hX : (X.a = pl hd p ∧ X.s = σ p ∧ ox hd σ p X.b + Y.U ≤ ox hd σ p s.b) ∨ (X.a ≠ pl hd p ∧ ox hd σ p X.b + 2 * Y.U ≤ ox hd σ p s.b)) :
    PlateDisj Y.L Y.H X (legOf l 1) := by
  obtain ⟨hU, hUe, -, -, -, hHU, -, -, hm0⟩ := hY.facts
  have hT := h.h0 (by omega); have hD := h.h1 h1
  -- the hop's kept coordinate: that of the top stacking plus a drift `t ≥ m + 1`
  have hface : ox hd σ p (legOf l 0).b = ox hd σ p s.b + ((Y.H : ℤ) + 1) := by
    unfold ox; rw [hT.face, h.sSign, mul_add, ← mul_assoc, units_sq, one_mul]
  have hdrift : (Y.m : ℤ) + 1 ≤ ox hd σ p (legOf l 1).b - ox hd σ p (legOf l 0).b := by
    have := hD.drift.1; rw [oth_oth, h.keep] at this; unfold ox
    linarith [this, mul_sub (σ p : ℤ) ((legOf l 1).b (pl hd p)) ((legOf l 0).b (pl hd p))]
  have hγa : (legOf l 1).a = pl hd (oth p) := hD.axis
  unfold PlateDisj
  rcases hX with ⟨hXa, hXs, hle⟩ | ⟨hXa, hle⟩
  · -- thin behind wide: more than `U + H + 1` apart
    apply sep_fw (σ p) (by rw [hXa, hγa]; exact pl_ne_pl hd (oth_ne p).symm) hXs
    rw [hXa]; unfold ox at hface hdrift hle; nlinarith [hface, hdrift, hle, hUe, hm0]
  · -- wide behind wide: more than `2U` apart
    apply sep_ww (σ p) (pl hd p) (fun h' => hXa h'.symm) (by rw [hγa]; exact pl_ne_pl hd (oth_ne p).symm)
    unfold ox at hface hdrift hle; nlinarith [hface, hdrift, hle, hUe, hm0]

end TurnBack

/-! ## The leg after a turn against the structures behind the turn -/

section LegAfter

variable {σ σ' : Fin 2 → ℤˣ} {p : Fin 2} {s : BrickPos d} {l je : List (BrickRec d)}

/-- **The kept coordinate along the leg after a turn**: the first plate of the leg is thin-forwards
at `ox σ p s + H + 1 + t + U`, and every plate of the leg from the second on has kept coordinate at
least `ox σ p s + H + 1 + U + 2m + 2`; all have at least `ox σ p s + H + 1 + U + m + 1`. Here the
leg `je` is extended by the turn's hop `γ = legOf l 1 = legOf je 0`, of signs `σ'`, first index
`oth p`. [folklore] -/
theorem leg_after_turn_kept (hY : Y.OK) (h : Turn hd Y e σ σ' p s l) (hl : l.length = 2) (hJ : DiagLeg hd Y e σ' none (oth p) je)
    (h0 : legOf je 0 = legOf l 1) {k : ℕ} (hk : k + 1 < je.length) :
    ox hd σ p s.b + ((Y.H : ℤ) + 1) + Y.U + Y.m + 1 ≤ ox hd σ p (legOf je (k + 1)).b ∧
      (k = 0 → (legOf je 1).a = pl hd p ∧ (legOf je 1).s = σ p ∧ ox hd σ p (legOf je 1).b = ox hd σ p (legOf je 0).b + Y.U) ∧
      (1 ≤ k → ox hd σ p s.b + ((Y.H : ℤ) + 1) + Y.U + 2 * Y.m + 2 ≤ ox hd σ p (legOf je (k + 1)).b) := by
  obtain ⟨hU, hUe, -, -, -, hHU, -, -, hm0⟩ := hY.facts
  have hT := h.h0 (by omega); have hD := h.h1 (by omega)
  -- `σ' p = σ p`, so the kept coordinate read along `σ'` is `ox σ p`
  have oxe : ∀ b : Site d, ox hd σ' p b = ox hd σ p b := fun b => by unfold ox; rw [h.keep]
  have hface : ox hd σ p (legOf l 0).b = ox hd σ p s.b + ((Y.H : ℤ) + 1) := by
    unfold ox; rw [hT.face, h.sSign, mul_add, ← mul_assoc, units_sq, one_mul]
  have hdrift : (Y.m : ℤ) + 1 ≤ ox hd σ p (legOf l 1).b - ox hd σ p (legOf l 0).b := by
    have := hD.drift.1; rw [oth_oth, h.keep] at this; unfold ox
    linarith [this, mul_sub (σ p : ℤ) ((legOf l 1).b (pl hd p)) ((legOf l 0).b (pl hd p))]
  -- the first hop of the leg: into `p`, `+U`
  have e1 : qAt (oth p) 1 = p := by rw [show qAt (oth p) 1 = qAt (oth p) (0 + 1) from rfl, qAt_succ, qAt_zero, oth_oth]
  have hst := (hJ.step (k := 0) (by omega)).1
  rw [show (0 : ℕ) + 1 = 1 from rfl, e1, oxe, oxe, h0] at hst
  obtain ⟨ha1, hs1⟩ := hJ.axis_sign (k := 1) (by omega)
  rw [e1] at ha1 hs1; rw [h.keep] at hs1
  refine ⟨?_, fun hk0 => ⟨ha1, hs1, by rw [h0]; exact hst⟩, fun hk1 => ?_⟩
  · have hmono := (hJ.mono (k := 1) (k' := k + 1) (by omega) hk p).1
    rw [oxe, oxe] at hmono; linarith
  · -- from the second plate on: one more drift `≥ m + 1` along `p` (the hop into `oth p` off plate `1`)
    have e2 : qAt (oth p) 2 = oth p := by rw [show qAt (oth p) 2 = qAt (oth p) (0 + 2) from rfl, qAt_add_two, qAt_zero]
    have hst2 := (hJ.step_either (k := 1) (by omega) p).2 (by rw [show (1 : ℕ) + 1 = 2 from rfl, e2]; exact (oth_ne p).symm)
    rw [oxe, oxe] at hst2
    have hmono := (hJ.mono (k := 2) (k' := k + 1) (by omega) hk p).1
    rw [oxe, oxe] at hmono; linarith

/-- **The leg after a turn is disjoint from every plate behind the turn's start along the kept
coordinate** (wide, or thin with the old kept sign, at least `U` behind — or the start itself). [folklore] -/
theorem disj_leg_after_turn_of_le (hY : Y.OK) (h : Turn hd Y e σ σ' p s l) (hl : l.length = 2) (hJ : DiagLeg hd Y e σ' none (oth p) je)
    (h0 : legOf je 0 = legOf l 1) {X : BrickPos d} (hX : X.a ≠ pl hd p ∨ (X.a = pl hd p ∧ X.s = σ p))
    (hle : ox hd σ p X.b + Y.U ≤ ox hd σ p s.b ∨ X = s) {k : ℕ} (hk : k + 1 < je.length) : PlateDisj Y.L Y.H X (legOf je (k + 1)) := by
  obtain ⟨hU, hUe, -, -, -, hHU, -, -, hm0⟩ := hY.facts
  obtain ⟨hall, h1, h2⟩ := leg_after_turn_kept hY h hl hJ h0 hk
  obtain ⟨hak, hsk⟩ := hJ.axis_sign (k := k + 1) hk
  have hH0 : (0 : ℤ) ≤ Y.H := by positivity
  have hXle : ox hd σ p X.b ≤ ox hd σ p s.b := by
    rcases hle with hle | rfl
    · linarith
    · exact le_rfl
  -- a wide plate is not the start, hence at least `U` behind it
  have hXle' : X.a ≠ pl hd p → ox hd σ p X.b + Y.U ≤ ox hd σ p s.b := fun hXa => by
    rcases hle with hle | rfl
    · exact hle
    · exact absurd h.sAxis hXa
  unfold PlateDisj
  by_cases hax : (legOf je (k + 1)).a = pl hd p
  · -- a thin plate of the leg (axis `p`, sign `σ' p = σ p`)
    have hs' : (legOf je (k + 1)).s = σ p := by
      rw [hak] at hax; have := pl_injective hd hax; rw [hsk, this, h.keep]
    rcases hX with hX | ⟨hXa, hXs⟩
    · apply sep_wf (σ p) (by rw [hax]; exact fun h' => hX h'.symm) hs'
      rw [hax]; unfold ox at hall hXle; linarith
    · apply sep_ff (σ p) (by rw [hax, hXa]) hXs hs'
      rw [hax]; unfold ox at hall hXle; linarith
  · -- a wide plate of the leg: not the first, so `k ≥ 1`
    have hk1 : 1 ≤ k := by
      by_contra h'; have : k = 0 := by omega
      subst this; exact hax (h1 rfl).1
    have h2' := h2 hk1
    rcases hX with hX | ⟨hXa, hXs⟩
    · have hle2 := hXle' hX
      apply sep_ww (σ p) (pl hd p) (fun h' => hX h'.symm) (fun h' => hax h'.symm)
      unfold ox at h2' hle2; linarith
    · apply sep_fw (σ p) (by rw [hXa]; exact fun h' => hax h'.symm) hXs
      rw [hXa]; unfold ox at h2' hXle; linarith

/-- **The leg after a turn is disjoint from the turn's top stacking**: the first plate thin-forwards
beyond it along `p`, the second thin-forwards beyond it along the flipped coordinate (read the new
way), the rest far beyond along `p`. [folklore] -/
theorem disj_leg_after_turn_top (hY : Y.OK) (h : Turn hd Y e σ σ' p s l) (hl : l.length = 2) (hJ : DiagLeg hd Y e σ' none (oth p) je)
    (h0 : legOf je 0 = legOf l 1) {k : ℕ} (hk : k + 1 < je.length) : PlateDisj Y.L Y.H (legOf l 0) (legOf je (k + 1)) := by
  obtain ⟨hU, hUe, -, -, -, hHU, -, -, hm0⟩ := hY.facts
  have hT := h.h0 (by omega); have hD := h.h1 (by omega)
  obtain ⟨hall, h1, h2⟩ := leg_after_turn_kept hY h hl hJ h0 hk
  obtain ⟨hak, hsk⟩ := hJ.axis_sign (k := k + 1) hk
  have hface : ox hd σ p (legOf l 0).b = ox hd σ p s.b + ((Y.H : ℤ) + 1) := by
    unfold ox; rw [hT.face, h.sSign, mul_add, ← mul_assoc, units_sq, one_mul]
  have hra : (legOf l 0).a = pl hd p := hT.axis
  have hrs : (legOf l 0).s = σ p := by rw [hT.sign, h.sSign]
  unfold PlateDisj
  rcases Nat.lt_trichotomy k 1 with hk0 | rfl | hk2
  · -- the first plate: thin behind thin along `p`, gap `t + U ≥ H + 1`
    have : k = 0 := by omega
    subst this
    obtain ⟨ha1, hs1, he1⟩ := h1 rfl
    have hdrift : (Y.m : ℤ) + 1 ≤ ox hd σ p (legOf l 1).b - ox hd σ p (legOf l 0).b := by
      have := hD.drift.1; rw [oth_oth, h.keep] at this; unfold ox
      linarith [this, mul_sub (σ p : ℤ) ((legOf l 1).b (pl hd p)) ((legOf l 0).b (pl hd p))]
    apply sep_ff (σ p) (by rw [ha1, hra]) hrs hs1
    rw [ha1]; rw [h0] at he1; unfold ox at he1 hdrift; linarith
  · -- the second plate: thin-forwards along the flipped coordinate, `2U + t` beyond the top stacking
    obtain ⟨ha2, hs2⟩ := hJ.axis_sign (k := 2) hk
    have e2 : qAt (oth p) 2 = oth p := by rw [show qAt (oth p) 2 = qAt (oth p) (0 + 2) from rfl, qAt_add_two, qAt_zero]
    rw [e2] at ha2 hs2
    have hst2 := (hJ.step (k := 1) hk).1
    rw [show (1 : ℕ) + 1 = 2 from rfl, e2] at hst2
    have e1 : qAt (oth p) 1 = p := by rw [show qAt (oth p) 1 = qAt (oth p) (0 + 1) from rfl, qAt_succ, qAt_zero, oth_oth]
    have hdr1 := ((hJ.step_either (k := 0) (by omega) (oth p)).2 (by rw [show (0 : ℕ) + 1 = 1 from rfl, e1]; exact oth_ne p)).1
    rw [show (0 : ℕ) + 1 = 1 from rfl, h0] at hdr1
    have hγ : ox hd σ' (oth p) (legOf l 1).b = ox hd σ' (oth p) (legOf l 0).b + Y.U := by
      unfold ox; rw [hD.face, mul_add, ← mul_assoc, units_sq, one_mul]
    apply sep_wf (σ' (oth p)) (by rw [ha2, hra]; exact pl_ne_pl hd (oth_ne p)) hs2
    rw [ha2]; unfold ox at hst2 hdr1 hγ; linarith
  · -- later plates: far beyond along `p`
    have h2' := h2 (by omega)
    by_cases hax : (legOf je (k + 1)).a = pl hd p
    · have hs' : (legOf je (k + 1)).s = σ p := by
        rw [hak] at hax; have := pl_injective hd hax; rw [hsk, this, h.keep]
      apply sep_ff (σ p) (by rw [hax, hra]) hrs hs'
      rw [hax]; unfold ox at h2' hface; linarith
    · apply sep_fw (σ p) (by rw [hra]; exact fun h' => hax h'.symm) hrs
      rw [hra]; unfold ox at h2' hface
      -- the plate is wide and `k ≥ 2`: one more `U` along `p` than the bound for `k ≥ 1`
      have hk3 : 2 ≤ k := by omega
      have hst3 := (hJ.step_either (k := 2) (by omega) p)
      have hmono := (hJ.mono (k := 3) (k' := k + 1) (by omega) hk p).1
      have oxe : ∀ b : Site d, ox hd σ' p b = ox hd σ p b := fun b => by unfold ox; rw [h.keep]
      rw [oxe, oxe] at hmono
      -- plate `3` has axis `p`: the hop into it is `+U` along `p`
      have e3 : qAt (oth p) 3 = p := by
        rw [show qAt (oth p) 3 = qAt (oth p) (1 + 2) from rfl, qAt_add_two, show qAt (oth p) 1 = qAt (oth p) (0 + 1) from rfl, qAt_succ, qAt_zero, oth_oth]
      have h3 := hst3.1 (by rw [show (2 : ℕ) + 1 = 3 from rfl, e3])
      rw [oxe, oxe, show (2 : ℕ) + 1 = 3 from rfl] at h3
      obtain ⟨-, -, h22⟩ := leg_after_turn_kept hY h hl hJ h0 (k := 1) (by omega)
      have h22' := h22 le_rfl
      rw [show (1 : ℕ) + 1 = 2 from rfl] at h22'
      unfold ox at hmono h3 h22'
      nlinarith [hmono, h3, h22', hUe, hm0, hHU]

end LegAfter

end BGNd

end Percolation.Literature

end

/-!
# Part 2 (The flat gait, XII): forks — the flipped coordinate, the two sides, the continuing trunk

Cross-structure disjointness around a fork of the flat
gait (Grimmett, *Percolation*, 2nd ed. (1999), §7.3 pp. 172–174 (C), Fig. 7.11, case `H < L`):
the two plates of a turn against plates far behind the start along the *flipped* coordinate
(`disj_turntop_flipped`, `disj_turnhop_flipped`); the **two sides of a fork** — every plate on the
branch side has its flipped-coordinate profile below the start's, every plate of the continuing
trunk above it (`disj_across`); and the first plates of the **continuing trunk** against the two
plates of the fork (`disj_cont_forktop`, `disj_cont_forkhop`).

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §7.3 pp. 172–174, (C), Fig. 7.11.
-/

noncomputable section

namespace Percolation.Literature

open LatticeModels Contour
open scoped Classical

namespace BGNd

variable {d : ℕ} [NeZero d] {hd : 3 ≤ d} {Y : FlatLayout} {e : MDir}

/-! ## A turn against plates far behind along the flipped coordinate -/

section Flipped

variable {σ σ' : Fin 2 → ℤˣ} {p : Fin 2} {s : BrickPos d} {l : List (BrickRec d)}

/-- **The top stacking of a turn is disjoint from every plate far enough behind the start along the
flipped coordinate** (read the old way; `2U + L'` for a wide plate, `U + H + 1 + L'` for a thin one
with the old sign): the top stacking is wide there, pushed back by at most `L'`. [folklore] -/
theorem disj_turntop_flipped (hY : Y.OK) (h : Turn hd Y e σ σ' p s l) (h0 : 0 < l.length) (hflip : σ' (oth p) = -σ (oth p))
    {X : BrickPos d} (hX : X.a ≠ pl hd (oth p) ∨ (X.a = pl hd (oth p) ∧ X.s = σ (oth p)))
    (hle : (X.a ≠ pl hd (oth p) → ox hd σ (oth p) X.b + 2 * Y.U + Y.Lp < ox hd σ (oth p) s.b) ∧
      (X.a = pl hd (oth p) → ox hd σ (oth p) X.b + Y.U + Y.H + 1 + Y.Lp < ox hd σ (oth p) s.b)) : PlateDisj Y.L Y.H X (legOf l 0) := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, -, -, hm0⟩ := hY.facts
  have hT := h.h0 h0
  -- the push, read the old way: between `-L'` and `0`
  have hpush : ox hd σ (oth p) s.b - Y.Lp ≤ ox hd σ (oth p) (legOf l 0).b := by
    have := hT.push.2; rw [hflip] at this; unfold ox
    simp only [Units.val_neg, neg_mul] at this; linarith [mul_sub (σ (oth p) : ℤ) ((legOf l 0).b (pl hd (oth p))) (s.b (pl hd (oth p)))]
  have hra : (legOf l 0).a = pl hd p := hT.axis
  unfold PlateDisj
  rcases hX with hX | ⟨hXa, hXs⟩
  · have hle' := hle.1 hX
    apply sep_ww (σ (oth p)) (pl hd (oth p)) (fun h' => hX h'.symm) (by rw [hra]; exact pl_ne_pl hd (oth_ne p))
    unfold ox at hpush hle'; linarith
  · have hle' := hle.2 hXa
    apply sep_fw (σ (oth p)) (by rw [hXa, hra]; exact pl_ne_pl hd (oth_ne p)) hXs
    rw [hXa]; unfold ox at hpush hle'; linarith

/-- **The hop of a turn is disjoint from every plate far enough behind the start along the flipped
coordinate** (read the old way; `2U + H + 1 + L'` for a wide plate, `U + 2H + 2 + L'` for a thin
one): the hop is thin-backwards there, `U` behind the top stacking. [folklore] -/
theorem disj_turnhop_flipped (hY : Y.OK) (h : Turn hd Y e σ σ' p s l) (h1 : 1 < l.length) (hflip : σ' (oth p) = -σ (oth p))
    {X : BrickPos d} (hX : X.a ≠ pl hd (oth p) ∨ (X.a = pl hd (oth p) ∧ X.s = σ (oth p)))
    (hle : (X.a ≠ pl hd (oth p) → ox hd σ (oth p) X.b + 2 * Y.U + Y.H + 1 + Y.Lp < ox hd σ (oth p) s.b) ∧
      (X.a = pl hd (oth p) → ox hd σ (oth p) X.b + Y.U + 2 * Y.H + 2 + Y.Lp < ox hd σ (oth p) s.b)) : PlateDisj Y.L Y.H X (legOf l 1) := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, -, -, hm0⟩ := hY.facts
  have hT := h.h0 (by omega); have hD := h.h1 h1
  have hpush : ox hd σ (oth p) s.b - Y.Lp ≤ ox hd σ (oth p) (legOf l 0).b := by
    have := hT.push.2; rw [hflip] at this; unfold ox
    simp only [Units.val_neg, neg_mul] at this; linarith [mul_sub (σ (oth p) : ℤ) ((legOf l 0).b (pl hd (oth p))) (s.b (pl hd (oth p)))]
  have hγ : ox hd σ (oth p) (legOf l 1).b = ox hd σ (oth p) (legOf l 0).b - Y.U := by
    unfold ox; rw [hD.face, hflip]; simp only [Units.val_neg, neg_mul, mul_add, mul_neg, ← mul_assoc, units_sq, one_mul]; ring
  have hγa : (legOf l 1).a = pl hd (oth p) := hD.axis
  have hγs : (legOf l 1).s = -σ (oth p) := by rw [hD.sign, hflip]
  unfold PlateDisj
  rcases hX with hX | ⟨hXa, hXs⟩
  · have hle' := hle.1 hX
    apply sep_wb (σ (oth p)) (by rw [hγa]; exact fun h' => hX h'.symm) hγs
    rw [hγa]; unfold ox at hpush hle' hγ; linarith
  · have hle' := hle.2 hXa
    apply sep_fb (σ (oth p)) (by rw [hγa, hXa]) hXs hγs
    rw [hγa]; unfold ox at hpush hle' hγ; linarith

end Flipped

/-! ## The two sides of a fork -/

section Across

/-- **The two sides of a fork are disjoint**: along a coordinate `i` read along `w`, a plate whose
profile is below a level `A` (wide with centre `≤ A - U`, or thin-backwards with centre `≤ A`) and
a plate whose profile is above it (thin-forwards with centre `≥ A + U`, or wide with centre
`> A + U`). [folklore] -/
theorem disj_across (hY : Y.OK) (w : ℤˣ) (i : Fin d) (A : ℤ) {β β' : BrickPos d}
    (hβ : (β.a ≠ i ∧ (w : ℤ) * β.b i + Y.U ≤ A) ∨ (β.a = i ∧ β.s = -w ∧ (w : ℤ) * β.b i ≤ A))
    (hβ' : (β'.a = i ∧ β'.s = w ∧ A + Y.U ≤ (w : ℤ) * β'.b i) ∨ (β'.a ≠ i ∧ A + Y.U < (w : ℤ) * β'.b i)) :
    PlateDisj Y.L Y.H β β' := by
  obtain ⟨hU, hUe, -⟩ := hY.facts
  unfold PlateDisj
  rcases hβ with ⟨ha, hle⟩ | ⟨ha, hs, hle⟩ <;> rcases hβ' with ⟨ha', hs', hle'⟩ | ⟨ha', hle'⟩
  · apply sep_wf w (by rw [ha']; exact fun h' => ha h'.symm) hs'; rw [ha']; linarith
  · apply sep_ww w i (fun h' => ha h'.symm) (fun h' => ha' h'.symm); linarith
  · apply sep_bf w (by rw [ha', ha]) hs hs'; rw [ha']; linarith
  · apply sep_bw w (by rw [ha]; exact fun h' => ha' h'.symm) hs; rw [ha]; linarith

end Across

/-! ## The continuing trunk against the fork's plates -/

section Cont

variable {σ σ' : Fin 2 → ℤˣ} {p : Fin 2} {s : BrickPos d} {l c : List (BrickRec d)}

/-- **The continuing trunk after a fork against the fork's top stacking.** The trunk `c` continues
off the fork's start `s = legOf c 0` (axis `p`) with the old signs: its first plate is thin-forwards
along the flipped coordinate at `+U`, its second thin-forwards along `p` at `+U + t ≥ +2H + 2`
(flat plates), the later ones at least `2U + t` on along the flipped coordinate. [folklore] -/
theorem disj_cont_forktop (hY : Y.OK) (h : Turn hd Y e σ σ' p s l) (h0 : 0 < l.length) (hflip : σ' (oth p) = -σ (oth p))
    (hC : DiagLeg hd Y e σ none p c) (hc0 : legOf c 0 = s) {k : ℕ} (hk : k + 1 < c.length) :
    PlateDisj Y.L Y.H (legOf l 0) (legOf c (k + 1)) := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  have hT := h.h0 h0
  have hra : (legOf l 0).a = pl hd p := hT.axis
  have hrs : (legOf l 0).s = σ p := by rw [hT.sign, h.sSign]
  -- the top stacking: `+ (H+1)` along `p`, pushed back by at most `L'` along `oth p`
  have hface : ox hd σ p (legOf l 0).b = ox hd σ p s.b + ((Y.H : ℤ) + 1) := by
    unfold ox; rw [hT.face, h.sSign, mul_add, ← mul_assoc, units_sq, one_mul]
  have hpush : ox hd σ (oth p) (legOf l 0).b ≤ ox hd σ (oth p) s.b := by
    have := hT.push.1; rw [hflip] at this; unfold ox
    simp only [Units.val_neg, neg_mul] at this; linarith [mul_sub (σ (oth p) : ℤ) ((legOf l 0).b (pl hd (oth p))) (s.b (pl hd (oth p)))]
  -- the trunk: first hop into `oth p` (`+U`), second into `p` (`+U`) after a drift `t`
  have e1 : qAt p 1 = oth p := by rw [show qAt p 1 = qAt p (0 + 1) from rfl, qAt_succ, qAt_zero]
  have e2 : qAt p 2 = p := by rw [show qAt p 2 = qAt p (0 + 2) from rfl, qAt_add_two, qAt_zero]
  have hst1 := (hC.step (k := 0) (by omega)).1
  rw [show (0 : ℕ) + 1 = 1 from rfl, e1, hc0] at hst1
  obtain ⟨hak, hsk⟩ := hC.axis_sign (k := k + 1) hk
  unfold PlateDisj
  rcases Nat.lt_trichotomy k 1 with hk0 | rfl | hk2
  · have : k = 0 := by omega
    subst this
    rw [show (0 : ℕ) + 1 = 1 from rfl, e1] at hak hsk
    apply sep_wf (σ (oth p)) (by rw [hak, hra]; exact pl_ne_pl hd (oth_ne p)) hsk
    rw [hak]; unfold ox at hst1 hpush; linarith
  · -- the second plate: thin behind thin along `p`, gap `U + t - (H+1) ≥ H + 1`
    rw [show (1 : ℕ) + 1 = 2 from rfl, e2] at hak hsk
    have hst2 := (hC.step (k := 1) hk).1
    rw [show (1 : ℕ) + 1 = 2 from rfl, e2] at hst2
    have hdr := ((hC.step_either (k := 0) (by omega) p).2 (by rw [show (0 : ℕ) + 1 = 1 from rfl, e1]; exact (oth_ne p).symm)).1
    rw [show (0 : ℕ) + 1 = 1 from rfl, hc0] at hdr
    apply sep_ff (σ p) (by rw [hak, hra]) hrs hsk
    rw [hak]; unfold ox at hst2 hdr hface; nlinarith [hst2, hdr, hface, hflat, hm0, hHU]
  · -- later plates: along `oth p`, at least `2U + t` beyond the start
    have hst3 := (hC.step (k := 2) (by omega)).1
    have e3 : qAt p 3 = oth p := by rw [show qAt p 3 = qAt p (1 + 2) from rfl, qAt_add_two, e1]
    rw [show (2 : ℕ) + 1 = 3 from rfl, e3] at hst3
    have hdr2 := ((hC.step_either (k := 1) (by omega) (oth p)).2 (by rw [show (1 : ℕ) + 1 = 2 from rfl, e2]; exact oth_ne p)).1
    have hmono := (hC.mono (k := 3) (k' := k + 1) (by omega) hk (oth p)).1
    by_cases hax : (legOf c (k + 1)).a = pl hd (oth p)
    · have hs' : (legOf c (k + 1)).s = σ (oth p) := by
        rw [hak] at hax; have := pl_injective hd hax; rw [hsk, this]
      apply sep_wf (σ (oth p)) (by rw [hax, hra]; exact pl_ne_pl hd (oth_ne p)) hs'
      rw [hax]; unfold ox at hst1 hst3 hdr2 hmono hpush; linarith
    · -- wide along `oth p`: index `k + 1 ≥ 4` is even… its centre is a drift beyond plate `3`
      have hk4 : 3 ≤ k := by
        by_contra h'; have : k = 2 := by omega
        subst this; rw [show (2 : ℕ) + 1 = 3 from rfl, e3] at hak; exact hax hak
      have hdr4 := ((hC.step_either (k := 3) (by omega) (oth p)).2 (by
        rw [show (3 : ℕ) + 1 = 4 from rfl, show qAt p 4 = qAt p (2 + 2) from rfl, qAt_add_two, e2]; exact oth_ne p)).1
      have hmono4 := (hC.mono (k := 4) (k' := k + 1) (by omega) hk (oth p)).1
      apply sep_ww (σ (oth p)) (pl hd (oth p)) (by rw [hra]; exact pl_ne_pl hd (oth_ne p)) (fun h' => hax h'.symm)
      unfold ox at hst1 hst3 hdr2 hdr4 hmono4 hpush; linarith

/-- **The continuing trunk after a fork against the fork's hop** `γ` (thin-backwards along the
flipped coordinate, `U` behind the top stacking): the trunk's first plate thin-forwards beyond, the
others wide or thin beyond. [folklore] -/
theorem disj_cont_forkhop (hY : Y.OK) (h : Turn hd Y e σ σ' p s l) (h1 : 1 < l.length) (hflip : σ' (oth p) = -σ (oth p))
    (hC : DiagLeg hd Y e σ none p c) (hc0 : legOf c 0 = s) {k : ℕ} (hk : k + 1 < c.length) :
    PlateDisj Y.L Y.H (legOf l 1) (legOf c (k + 1)) := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  have hT := h.h0 (by omega); have hD := h.h1 h1
  have hpush : ox hd σ (oth p) (legOf l 0).b ≤ ox hd σ (oth p) s.b := by
    have := hT.push.1; rw [hflip] at this; unfold ox
    simp only [Units.val_neg, neg_mul] at this; linarith [mul_sub (σ (oth p) : ℤ) ((legOf l 0).b (pl hd (oth p))) (s.b (pl hd (oth p)))]
  have hγ : ox hd σ (oth p) (legOf l 1).b = ox hd σ (oth p) (legOf l 0).b - Y.U := by
    unfold ox; rw [hD.face, hflip]; simp only [Units.val_neg, neg_mul, mul_add, mul_neg, ← mul_assoc, units_sq, one_mul]; ring
  have hγa : (legOf l 1).a = pl hd (oth p) := hD.axis
  have hγs : (legOf l 1).s = -σ (oth p) := by rw [hD.sign, hflip]
  -- the trunk is thin-forwards at `≥ +U` or wide at `> +U` along `oth p`, relative to the start
  have e1 : qAt p 1 = oth p := by rw [show qAt p 1 = qAt p (0 + 1) from rfl, qAt_succ, qAt_zero]
  have e2 : qAt p 2 = p := by rw [show qAt p 2 = qAt p (0 + 2) from rfl, qAt_add_two, qAt_zero]
  have hst1 := (hC.step (k := 0) (by omega)).1
  rw [show (0 : ℕ) + 1 = 1 from rfl, e1, hc0] at hst1
  obtain ⟨hak, hsk⟩ := hC.axis_sign (k := k + 1) hk
  refine disj_across hY (σ (oth p)) (pl hd (oth p)) (ox hd σ (oth p) s.b) (Or.inr ⟨hγa, hγs, ?_⟩) ?_
  · unfold ox at hpush hγ ⊢; linarith
  · by_cases hax : (legOf c (k + 1)).a = pl hd (oth p)
    · have hs' : (legOf c (k + 1)).s = σ (oth p) := by
        rw [hak] at hax; have := pl_injective hd hax; rw [hsk, this]
      refine Or.inl ⟨hax, hs', ?_⟩
      have hmono := (hC.mono (k := 1) (k' := k + 1) (by omega) hk (oth p)).1
      unfold ox at hst1 hmono ⊢; linarith
    · refine Or.inr ⟨hax, ?_⟩
      have hk1 : 1 ≤ k := by
        by_contra h'; have : k = 0 := by omega
        subst this; rw [show (0 : ℕ) + 1 = 1 from rfl, e1] at hak; exact hax hak
      have hdr2 := ((hC.step_either (k := 1) (by omega) (oth p)).2 (by rw [show (1 : ℕ) + 1 = 2 from rfl, e2]; exact oth_ne p)).1
      have hmono := (hC.mono (k := 2) (k' := k + 1) (by omega) hk (oth p)).1
      unfold ox at hst1 hdr2 hmono ⊢; linarith

end Cont

end BGNd

end Percolation.Literature

end

/-!
# Part 3 (The flat gait, XIII): assembling disjointness, I — the entry and the jog

From the invariant of a run state of the flat gait
(`FlatInv`; Grimmett, *Percolation*, 2nd ed. (1999), §7.3 pp. 171–174, case `H < L`) we derive that
the plates of the later segment of each pair among: lead-in, riser, preamble, turn towards the jog,
jog, turn back, first trunk stretch — are disjoint from those of the earlier one, by instantiating
the structural lemmas of `FlatDisjA`–`FlatDisjC` on the frame of the state (`FlatFrame.lean`). The
profiles used: every entry plate lies behind the riser's head (`FlatInv.prof_entry`), every plate of
a feeding leg is behind or on the leg's head (`DiagLeg.prof_feed`), and every plate before the trunk
turn is far behind the jog's head along the kept coordinate or on the extended jog
(`FlatInv.far_beforeT`).

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §7.3 pp. 171–174.
-/

noncomputable section

namespace Percolation.Literature

open LatticeModels Contour
open scoped Classical

namespace BGNd

variable {d : ℕ} [NeZero d] {hd : 3 ≤ d} {Y : FlatLayout} {a : Site 2} {e : MDir} {τ : TTok d}

/-- The axis class of a plate along the plane index `i` for the signs `σ`: wide there, or thin with
the sign `σ i`. [folklore] -/
def AxCl (hd : 3 ≤ d) (σ : Fin 2 → ℤˣ) (i : Fin 2) (X : BrickPos d) : Prop := X.a ≠ pl hd i ∨ (X.a = pl hd i ∧ X.s = σ i)

/-- A plate of a diagonal leg is in the axis class of its signs along every index. [folklore] -/
theorem DiagLeg.axCl {σ : Fin 2 → ℤˣ} {zmode : Option Bool} {q₀ : Fin 2} {l : List (BrickRec d)} (h : DiagLeg hd Y e σ zmode q₀ l)
    {k : ℕ} (hk : k < l.length) (i : Fin 2) : AxCl hd σ i (legOf l k) := by
  obtain ⟨ha, hs⟩ := h.axis_sign hk
  by_cases hi : i = qAt q₀ k
  · right; rw [hi]; exact ⟨ha, hs⟩
  · left; rw [ha]; exact fun h' => hi (pl_injective hd h').symm

/-- A record of a list is `legOf` at some index. [folklore] -/
theorem exists_legOf_of_mem {l : List (BrickRec d)} {r : BrickRec d} (hr : r ∈ l) : ∃ k < l.length, legOf l k = r.1 := by
  obtain ⟨k, hk, hkr⟩ := exists_recOf_of_mem hr; exact ⟨k, hk, by unfold legOf; rw [hkr]⟩

/-- **The height along a leg with a requested direction** `u` (up iff `b`): non-decreasing along
`u`, by at most `L'` a hop. [folklore] -/
theorem DiagLeg.height_dir {σ : Fin 2 → ℤˣ} {b : Bool} {q₀ : Fin 2} {l : List (BrickRec d)} (h : DiagLeg hd Y e σ (some b) q₀ l)
    {u : ℤˣ} (hu : b = decide ((u : ℤ) = 1)) {k k' : ℕ} (hkk : k ≤ k') (hk' : k' < l.length) :
    0 ≤ (u : ℤ) * ((legOf l k').b (ax0 hd) - (legOf l k).b (ax0 hd)) ∧ (u : ℤ) * ((legOf l k').b (ax0 hd) - (legOf l k).b (ax0 hd)) ≤ ((k' : ℤ) - k) * Y.Lp := by
  induction k' with
  | zero => have : k = 0 := by omega
            subst this; simp
  | succ k' ih =>
    rcases Nat.eq_or_lt_of_le hkk with rfl | hlt
    · simp
    · have ih' := ih (by omega) (by omega)
      have hc := h.chain k' hk'
      have step : 0 ≤ (u : ℤ) * ((legOf l (k' + 1)).b (ax0 hd) - (legOf l k').b (ax0 hd)) ∧
          (u : ℤ) * ((legOf l (k' + 1)).b (ax0 hd) - (legOf l k').b (ax0 hd)) ≤ Y.Lp := by
        rcases Int.units_eq_one_or u with rfl | rfl
        · have hb : b = true := by rw [hu]; decide
          subst hb; have := hc.zup rfl; simp only [Units.val_one, one_mul]; exact this
        · have hb : b = false := by rw [hu]; decide
          subst hb; have := hc.zdn rfl; simp only [Units.val_neg, Units.val_one, neg_mul, one_mul, neg_sub]
          constructor <;> linarith [this.1, this.2]
      push_cast
      constructor <;> nlinarith [ih'.1, ih'.2, step.1, step.2]

section Entry

/-- **Profile of the entry**: the first plate and every plate of the riser are in the axis class of
`dsg e` along both indices and lie behind the riser's head in both oriented plane coordinates;
moreover, if the head landed through the plane axis `i`, every other entry plate is at least `U`
behind it along `i`. [folklore] -/
theorem FlatInv.prof_entry {st : FS d} (hI : FlatInv hd Y a e τ st) {X : BrickRec d}
    (hX : X ∈ st.segs 0 ∨ X ∈ st.segs 1) {Rend : BrickRec d} (hR : (st.segs 1).head? = some Rend) (i : Fin 2) :
    AxCl hd (dsg e) i X.1 ∧ ox hd (dsg e) i X.1.b ≤ ox hd (dsg e) i Rend.1.b ∧
      (Rend.1.a = pl hd i → X ≠ Rend → ox hd (dsg e) i X.1.b + Y.U ≤ ox hd (dsg e) i Rend.1.b) := by
  obtain ⟨tl1, hl1⟩ : ∃ tl, st.segs 1 = Rend :: tl := by
    rcases hl : st.segs 1 with _ | ⟨r1, tl1⟩
    · rw [hl] at hR; simp at hR
    · rw [hl] at hR; simp only [List.head?_cons, Option.some.injEq] at hR; subst hR; exact ⟨tl1, rfl⟩
  have h1ne : st.segs 1 ≠ [] := by rw [hl1]; simp
  have hK1 : SegOK hd Y e τ (eJOf hd Y a e τ st) 1 (st.segs 1) (st.segs (startOf 1)) := hI.segOK 1
  simp only [SegOK, startOf, Fin.isValue, Matrix.cons_val] at hK1
  have hRis : Riser hd Y (dsg e) (friseDir hd Y e τ) (plIdx hd τ.ax) (rstart hd e τ (st.segs 0)) (st.segs 1) := hK1 h1ne
  have hlen : (st.segs 1).length = tl1.length + 1 := by rw [hl1]; rfl
  have hRe : Rend.1 = legOf (st.segs 1) ((st.segs 1).length - 1) := by rw [hl1]; exact (legOf_cons_length Rend tl1).symm
  -- the lead-in: a diagonal leg whose head is the riser's start
  have hc0 := hI.order 1 0 (by decide) h1ne
  obtain ⟨A, tlA, hl0, hh0⟩ := exists_head_of_ne_nil (l := st.segs 0) (by intro h; rw [h] at hc0; simp [complete'] at hc0)
  have hK0 : SegOK hd Y e τ (eJOf hd Y a e τ st) 0 (st.segs 0) (st.segs (startOf 0)) := hI.segOK 0
  simp only [SegOK, startOf, Fin.isValue, Matrix.cons_val] at hK0
  obtain ⟨hD0, -, -⟩ := hK0 (by rw [hl0]; simp)
  have hrs : rstart hd e τ (st.segs 0) = legOf (st.segs 0) ((st.segs 0).length - 1) := by
    rw [legOf_last_of_head hh0]; simp [rstart, hh0]
  -- the landing case for the head
  have hland : ∀ i, Rend.1.a = pl hd i → ∃ j, (st.segs 1).length = 2 * j + 2 ∧ qAt (plIdx hd τ.ax) (j + 1) = i := by
    intro i hi
    rcases Nat.even_or_odd tl1.length with ⟨j, hj⟩ | ⟨j, hj⟩
    · exfalso
      have := ((hRis.axis_sign (k := tl1.length) (by omega)).1 (by omega)).1
      rw [hl1, legOf_cons_length] at this; rw [this] at hi; exact absurd hi (pl_ne_ax0 hd i).symm
    · refine ⟨j, by omega, ?_⟩
      have := ((hRis.axis_sign (k := tl1.length) (by omega)).2 (by omega)).1
      rw [hl1, legOf_cons_length, hi] at this
      rw [show tl1.length / 2 + 1 = j + 1 by omega] at this
      exact (pl_injective hd this).symm
  rcases hX with hX | hX
  · -- a plate of the lead-in: behind its head, the riser's start
    obtain ⟨k, hk, hkX⟩ := exists_legOf_of_mem hX
    rw [← hkX]
    have hmono := (hD0.mono (k := k) (k' := (st.segs 0).length - 1) (by omega) (by omega) i).1
    rw [← hrs] at hmono
    refine ⟨?_, ?_, fun hi _ => ?_⟩
    · obtain ⟨ha, hs⟩ := hD0.axis_sign hk
      by_cases hi : i = qAt (plIdx hd τ.ax) k
      · right; rw [hi]; exact ⟨ha, hs⟩
      · left; rw [ha]; exact fun h' => hi (pl_injective hd h').symm
    · rw [hRe]; exact hmono.trans (hRis.plane_le_head (by omega) i).1
    · obtain ⟨j, hj, hq⟩ := hland i hi
      have := (hRis.plane_le_head_land hj).1
      rw [hq] at this; rw [hRe, hj, show 2 * j + 2 - 1 = 2 * j + 1 by omega]; linarith
  · obtain ⟨k, hk, hkX⟩ := exists_recOf_of_mem hX
    have hkX' : legOf (st.segs 1) k = X.1 := by unfold legOf; rw [hkX]
    rw [← hkX']
    refine ⟨?_, ?_, fun hi hne => ?_⟩
    · rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
      · left; rw [((hRis.axis_sign hk).1 (by omega)).1]; exact (pl_ne_ax0 hd i).symm
      · obtain ⟨ha, hs⟩ := (hRis.axis_sign hk).2 (by omega)
        by_cases hi : i = qAt (plIdx hd τ.ax) (k / 2 + 1)
        · right; rw [hi]; exact ⟨ha, hs⟩
        · left; rw [ha]; exact fun h' => hi (pl_injective hd h').symm
    · rw [hRe]; exact (hRis.plane_le_head (by omega) i).2 k hk
    · obtain ⟨j, hj, hq⟩ := hland i hi
      have hk' : k ≤ 2 * j := by
        by_contra h'
        have hk2 : k = (st.segs 1).length - 1 := by omega
        apply hne
        rw [← hkX, hk2, hl1]; exact recOf_cons_pred_length Rend tl1
      have := (hRis.plane_le_head_land hj).2 k hk'
      rw [hq] at this; rw [hRe, hj, show 2 * j + 2 - 1 = 2 * j + 1 by omega]; exact this

end Entry

/-! ## The leg that feeds a turn, seen from the turn's start -/

section Feed

variable {σ : Fin 2 → ℤˣ} {zmode : Option Bool} {q₀ : Fin 2} {le : List (BrickRec d)}

/-- **Profile of a leg from its last plate** `s = legOf le (len - 1)`, a plate of axis `p`: the plate
before it has the other axis, the old sign, kept coordinate exactly `U` behind and flipped
coordinate at most `H - m - 1` ahead (read either way); every older plate is, along the kept
coordinate, at least `U + m + 1` behind, and at least `2U + m + 1` behind if wide. [folklore] -/
theorem DiagLeg.prof_feed (hY : Y.OK) (h : DiagLeg hd Y e σ zmode q₀ le) {p : Fin 2} (hsa : (legOf le (le.length - 1)).a = pl hd p)
    {k : ℕ} (hk : k < le.length) :
    (k = le.length - 1) ∨
      (k = le.length - 2 ∧ (legOf le k).a = pl hd (oth p) ∧ (legOf le k).s = σ (oth p) ∧
        ox hd σ p (legOf le k).b + Y.U = ox hd σ p (legOf le (le.length - 1)).b ∧
        |(legOf le (le.length - 1)).b (pl hd (oth p)) - (legOf le k).b (pl hd (oth p))| ≤ (Y.H : ℤ) - Y.m - 1) ∨
      (k ≤ le.length - 3 ∧ AxCl hd σ p (legOf le k) ∧ ox hd σ p (legOf le k).b + Y.U + Y.m + 1 ≤ ox hd σ p (legOf le (le.length - 1)).b ∧
        ((legOf le k).a ≠ pl hd p → ox hd σ p (legOf le k).b + 2 * Y.U + Y.m + 1 ≤ ox hd σ p (legOf le (le.length - 1)).b)) := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  set n := le.length - 1 with hn
  have hlen : le.length = n + 1 := by have := List.length_pos_of_ne_nil h.ne; omega
  -- the last index is `p`
  have hqn : qAt q₀ n = p := by
    have := (h.axis_sign (k := n) (by omega)).1; rw [hsa] at this; exact (pl_injective hd this).symm
  rcases Nat.lt_trichotomy k (n - 1) with hlt | heq | hgt
  · -- older plates: `k ≤ n - 2`
    right; right
    have hn2 : 2 ≤ n := by omega
    -- the hop into `n` is `+U` along `p`, the hop into `n - 1` a drift `≥ m + 1` along `p`
    have hstn := (h.step (k := n - 1) (by omega)).1
    rw [show n - 1 + 1 = n by omega, hqn] at hstn
    have hq1 : qAt q₀ (n - 1) = oth p := by
      have := qAt_succ q₀ (n - 1); rw [show n - 1 + 1 = n by omega, hqn] at this
      rw [← oth_oth (qAt q₀ (n - 1)), ← this]
    have hdr := ((h.step_either (k := n - 2) (by omega) p).2 (by rw [show n - 2 + 1 = n - 1 by omega, hq1]; exact (oth_ne p).symm)).1
    rw [show n - 2 + 1 = n - 1 by omega] at hdr
    have hmono := (h.mono (k := k) (k' := n - 2) (by omega) (by omega) p).1
    refine ⟨by omega, h.axCl hk p, by linarith, fun hax => ?_⟩
    -- a wide plate has index of the parity of `n - 1`, hence `k ≤ n - 3`, and the hop into `n - 2` is `+U` along `p`
    have hq2 : qAt q₀ (n - 2) = p := by
      have := qAt_add_two q₀ (n - 2); rw [show n - 2 + 2 = n by omega, hqn] at this; exact this.symm
    have hpar : k % 2 ≠ n % 2 := by
      intro hpe; apply hax; rw [(h.axis_sign hk).1, ← hqn]; congr 1
      unfold qAt; rw [hpe]
    have hk3 : k ≤ n - 3 := by omega
    have hn3 : 3 ≤ n := by omega
    have hst2 := (h.step (k := n - 3) (by omega)).1
    rw [show n - 3 + 1 = n - 2 by omega, hq2] at hst2
    have hmono3 := (h.mono (k := k) (k' := n - 3) hk3 (by omega) p).1
    linarith
  · -- the plate before the last (if `n = 0` it is the last)
    by_cases hn0 : n = 0
    · left; omega
    right; left
    subst heq
    have hn1 : 1 ≤ n := by omega
    obtain ⟨ha, hs⟩ := h.axis_sign (k := n - 1) (by omega)
    have hq1 : qAt q₀ (n - 1) = oth p := by
      have := qAt_succ q₀ (n - 1); rw [show n - 1 + 1 = n by omega, hqn] at this
      rw [← oth_oth (qAt q₀ (n - 1)), ← this]
    rw [hq1] at ha hs
    have hstn := (h.step (k := n - 1) (by omega))
    rw [show n - 1 + 1 = n by omega, hqn, hq1] at hstn
    obtain ⟨h1, h2, h3⟩ := hstn
    refine ⟨by omega, ha, hs, by linarith, ?_⟩
    rw [abs_le]; unfold ox at h2 h3
    have := mul_sub (σ (oth p) : ℤ) ((legOf le n).b (pl hd (oth p))) ((legOf le (n - 1)).b (pl hd (oth p)))
    rcases Int.units_eq_one_or (σ (oth p)) with hu | hu <;> rw [hu] at h2 h3 this <;> push_cast at h2 h3 this <;> constructor <;> nlinarith [h2, h3, this, hm0]
  · left; omega

end Feed

/-! ## Generic assembly: a turn and the leg after it, against the feeding leg and far plates -/

section Generic

variable {σ σ' : Fin 2 → ℤˣ} {zmode : Option Bool} {q₀ : Fin 2} {p : Fin 2} {le l je : List (BrickRec d)}

/-- A plate is **far behind** the start `s` of a turn along the kept index `p`: in the axis class,
at least `U` behind, and at least `2U` behind if wide. [folklore] -/
def FarB (hd : 3 ≤ d) (Y : FlatLayout) (σ : Fin 2 → ℤˣ) (p : Fin 2) (s X : BrickPos d) : Prop :=
  AxCl hd σ p X ∧ ox hd σ p X.b + Y.U ≤ ox hd σ p s.b ∧ (X.a ≠ pl hd p → ox hd σ p X.b + 2 * Y.U ≤ ox hd σ p s.b)

/-- **A far plate is disjoint from both plates of a turn.** [folklore] -/
theorem disj_far_turn (hY : Y.OK) (hT : Turn hd Y e σ σ' p (legOf le (le.length - 1)) l) {X : BrickPos d}
    (hX : FarB hd Y σ p (legOf le (le.length - 1)) X) {j : ℕ} (hj : j < l.length) : PlateDisj Y.L Y.H X (legOf l j) := by
  have hl2 := hT.len
  have hj2 : j < 2 := by omega
  obtain ⟨hcl, h1, h2⟩ := hX
  interval_cases j
  · exact disj_turn_top_of_le hY hT hj hcl h1
  · refine disj_turnhop_of_le hY hT hj ?_
    rcases hcl with hw | ⟨ha, hs⟩
    · exact Or.inr ⟨hw, h2 hw⟩
    · exact Or.inl ⟨ha, hs, h1⟩

/-- **A plate of the feeding leg is disjoint from both plates of the turn off its last plate.** [folklore] -/
theorem disj_feed_turn (hY : Y.OK) (hle : DiagLeg hd Y e σ zmode q₀ le) (hT : Turn hd Y e σ σ' p (legOf le (le.length - 1)) l)
    (hflip : σ' (oth p) = -σ (oth p)) {k : ℕ} (hk : k < le.length) {j : ℕ} (hj : j < l.length) : PlateDisj Y.L Y.H (legOf le k) (legOf l j) := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  have hl2 := hT.len
  have hj2 : j < 2 := by omega
  rcases hle.prof_feed hY hT.sAxis hk with hlast | ⟨_, ha, hs, hox, habs⟩ | ⟨_, hcl, h1, h2⟩
  · rw [hlast]
    interval_cases j
    · exact hT.disj_start_top hj
    · exact hT.disj_start_hop hY hj
  · interval_cases j
    · exact disj_turn_top_of_le hY hT hj (Or.inl (by rw [ha]; exact pl_ne_pl hd (oth_ne p))) (le_of_eq hox)
    · refine disj_turnhop_prev hY hT hj hflip ha hs ?_
      unfold ox; have := abs_le.1 habs
      rcases Int.units_eq_one_or (σ' (oth p)) with hu | hu <;> rw [hu] <;> push_cast <;> nlinarith [this.1, this.2, hHU, hm0]
  · exact disj_far_turn hY hT ⟨hcl, by linarith, fun hw => by have := h2 hw; linarith⟩ hj

/-- **A far plate, or a plate of the feeding leg, is disjoint from the leg after the turn.** [folklore] -/
theorem disj_farfeed_legafter (hY : Y.OK) (hle : DiagLeg hd Y e σ zmode q₀ le) (hT : Turn hd Y e σ σ' p (legOf le (le.length - 1)) l)
    (hl : l.length = 2) (hJ : DiagLeg hd Y e σ' none (oth p) je) (h0 : legOf je 0 = legOf l 1) {X : BrickPos d}
    (hX : FarB hd Y σ p (legOf le (le.length - 1)) X ∨ ∃ k < le.length, X = legOf le k) {k : ℕ} (hk : k + 1 < je.length) :
    PlateDisj Y.L Y.H X (legOf je (k + 1)) := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  rcases hX with ⟨hcl, h1, -⟩ | ⟨k', hk', rfl⟩
  · exact disj_leg_after_turn_of_le hY hT hl hJ h0 hcl (Or.inl h1) hk
  · rcases hle.prof_feed hY hT.sAxis hk' with hlast | ⟨_, ha, hs, hox, -⟩ | ⟨_, hcl, h1, -⟩
    · rw [hlast]; exact disj_leg_after_turn_of_le hY hT hl hJ h0 (Or.inr ⟨hT.sAxis, hT.sSign⟩) (Or.inr rfl) hk
    · exact disj_leg_after_turn_of_le hY hT hl hJ h0 (Or.inl (by rw [ha]; exact pl_ne_pl hd (oth_ne p))) (Or.inl (le_of_eq hox)) hk
    · exact disj_leg_after_turn_of_le hY hT hl hJ h0 hcl (Or.inl (by linarith)) hk

/-- **Transporting farness along the feeding leg**: a plate far behind (or at most level with, if
thin) the first plate of the feeding leg is far behind its last plate, provided the leg has at
least three plates. [folklore] -/
theorem farB_of_le_first (hY : Y.OK) (hle : DiagLeg hd Y e σ zmode q₀ le) (hsa : (legOf le (le.length - 1)).a = pl hd p) (h3 : 3 ≤ le.length)
    {X : BrickPos d} (hcl : AxCl hd σ p X)
    (hle0 : ox hd σ p X.b + Y.U ≤ ox hd σ p (legOf le 0).b ∨ (X.a = pl hd p ∧ ox hd σ p X.b ≤ ox hd σ p (legOf le 0).b) ∨
      ((legOf le 0).a ≠ pl hd p ∧ ox hd σ p X.b ≤ ox hd σ p (legOf le 0).b)) :
    FarB hd Y σ p (legOf le (le.length - 1)) X := by
  obtain ⟨hU, -, -, -, -, -, -, -, hm0⟩ := hY.facts
  rcases hle.prof_feed hY hsa (k := 0) (by omega) with h | ⟨h, -⟩ | ⟨-, -, h1, h2⟩
  · omega
  · omega
  · refine ⟨hcl, ?_, fun hw => ?_⟩
    · rcases hle0 with h | ⟨-, h⟩ | ⟨-, h⟩ <;> linarith
    · rcases hle0 with h | ⟨ha, -⟩ | ⟨hw0, h⟩
      · linarith
      · exact absurd ha hw
      · have := h2 hw0; linarith

end Generic

/-! ## The frames, packaged from the turn's side -/

section Frames

omit [NeZero d] in
/-- Farness is monotone in the start. [folklore] -/
theorem FarB.mono {σ : Fin 2 → ℤˣ} {p : Fin 2} {s s' X : BrickPos d} (h : FarB hd Y σ p s X) (hss : ox hd σ p s.b ≤ ox hd σ p s'.b) :
    FarB hd Y σ p s' X :=
  ⟨h.1, h.2.1.trans (by linarith), fun hw => (h.2.2 hw).trans (by linarith)⟩

/-- **A plate of a feeding leg is far behind any plate at least `U` beyond the leg's last plate**
along the kept coordinate. [folklore] -/
theorem farB_feed_of_next (hY : Y.OK) {σ : Fin 2 → ℤˣ} {zmode : Option Bool} {q₀ p : Fin 2} {le : List (BrickRec d)}
    (hle : DiagLeg hd Y e σ zmode q₀ le) (hsa : (legOf le (le.length - 1)).a = pl hd p) (hss : (legOf le (le.length - 1)).s = σ p)
    {s' : BrickPos d} (hs' : ox hd σ p (legOf le (le.length - 1)).b + Y.U ≤ ox hd σ p s'.b) {k : ℕ} (hk : k < le.length) :
    FarB hd Y σ p s' (legOf le k) := by
  obtain ⟨hU, -, -, -, -, -, -, -, hm0⟩ := hY.facts
  rcases hle.prof_feed hY hsa hk with hlast | ⟨_, ha, hs, hox, -⟩ | ⟨_, hcl, h1, h2⟩
  · rw [hlast]; exact ⟨Or.inr ⟨hsa, hss⟩, hs', fun hw => absurd hsa hw⟩
  · exact ⟨Or.inl (by rw [ha]; exact pl_ne_pl hd (oth_ne p)), by linarith, fun _ => by linarith⟩
  · exact ⟨hcl, by linarith, fun hw => by have := h2 hw; linarith⟩

variable {st : FS d}

/-- The last record of `l ++ [s]` at index `length - 1` is the head of a nonempty `l`. [folklore] -/
theorem legOf_append_singleton_last {l : List (BrickRec d)} {r : BrickRec d} {tl : List (BrickRec d)} (hl : l = r :: tl) (s : BrickRec d) :
    legOf (l ++ [s]) ((l ++ [s]).length - 1) = r.1 := by
  rw [hl, List.cons_append, show (r :: (tl ++ [s])).length - 1 = (tl ++ [s]).length by simp]
  exact legOf_cons_length r (tl ++ [s])

/-- **The jog frame**: when the turn towards the jog has begun — the riser's head `Rend`, the
extended preamble `PE` (a diagonal leg of the signs of `e`, at least three plates, ending on the
kept axis at the preamble's head), and the turn off its last plate. [folklore] -/
theorem FlatInv.jframe (hI : FlatInv hd Y a e τ st) (h3 : st.segs 3 ≠ []) :
    ∃ Rend, (st.segs 1).head? = some Rend ∧ ∃ q, DiagLeg hd Y e (dsg e) none q (st.segs 2 ++ [Rend]) ∧
      3 ≤ (st.segs 2 ++ [Rend]).length ∧ (∀ k, (hk : k < (st.segs 2).length) → legOf (st.segs 2 ++ [Rend]) (k + 1) = legOf (st.segs 2) k) ∧
      legOf (st.segs 2 ++ [Rend]) 0 = Rend.1 ∧
      Turn hd Y e (dsg e) (dsg (eJOf hd Y a e τ st)) (pJ e (eJOf hd Y a e τ st))
        (legOf (st.segs 2 ++ [Rend]) ((st.segs 2 ++ [Rend]).length - 1)) (st.segs 3) := by
  obtain ⟨rP, hrP, hlen2, hT⟩ := hI.frame_turnJ h3
  obtain ⟨rP', tl2, hl2, hh2⟩ := exists_head_of_ne_nil (l := st.segs 2) (by intro h; rw [h] at hlen2; simp at hlen2)
  rw [hh2] at hrP; simp only [Option.some.injEq] at hrP; subst hrP
  obtain ⟨Rend, hRend, q, hPE⟩ := hI.frame_pre (by rw [hl2]; simp)
  refine ⟨Rend, hRend, q, hPE, by simp; omega, fun k hk => legOf_append_singleton_succ _ _ k, legOf_snoc_zero _ _, ?_⟩
  rw [legOf_append_singleton_last hl2]; exact hT

/-- **Entry plates other than the riser's head are far behind the preamble's head.** [folklore] -/
theorem FlatInv.farB_entry (hI : FlatInv hd Y a e τ st) (hY : Y.OK) {Rend : BrickRec d}
    (hR : (st.segs 1).head? = some Rend) {q : Fin 2} (hPE : DiagLeg hd Y e (dsg e) none q (st.segs 2 ++ [Rend]))
    (h3 : 3 ≤ (st.segs 2 ++ [Rend]).length) {p : Fin 2} (hsa : (legOf (st.segs 2 ++ [Rend]) ((st.segs 2 ++ [Rend]).length - 1)).a = pl hd p)
    {X : BrickRec d} (hX : X ∈ st.segs 0 ∨ X ∈ st.segs 1) (hne : X ≠ Rend) :
    FarB hd Y (dsg e) p (legOf (st.segs 2 ++ [Rend]) ((st.segs 2 ++ [Rend]).length - 1)) X.1 := by
  obtain ⟨hcl, hle, hland⟩ := hI.prof_entry hX hR p
  have h0 : legOf (st.segs 2 ++ [Rend]) 0 = Rend.1 := legOf_snoc_zero _ _
  refine farB_of_le_first hY hPE hsa h3 hcl ?_
  rw [h0]
  by_cases hRa : Rend.1.a = pl hd p
  · exact Or.inl (hland hRa hne)
  · exact Or.inr (Or.inr ⟨hRa, hle⟩)

/-- **The trunk-turn frame**: when the turn back has begun — the jog frame, the extended jog `JE`
(a diagonal leg of the jog's signs off `γ_J`, ending on the kept axis at the jog's head, at least
`U` beyond the preamble's head along the kept coordinate), and the turn off its last plate. [folklore] -/
theorem FlatInv.tframe (hI : FlatInv hd Y a e τ st) (h5 : st.segs 5 ≠ []) :
    ∃ γ, (st.segs 3).head? = some γ ∧ (st.segs 3).length = 2 ∧ legOf (st.segs 3) 1 = γ.1 ∧
      DiagLeg hd Y e (dsg (eJOf hd Y a e τ st)) none (oth (pJ e (eJOf hd Y a e τ st))) (st.segs 4 ++ [γ]) ∧
      2 ≤ (st.segs 4 ++ [γ]).length ∧ (∀ k, (hk : k < (st.segs 4).length) → legOf (st.segs 4 ++ [γ]) (k + 1) = legOf (st.segs 4) k) ∧
      legOf (st.segs 4 ++ [γ]) 0 = γ.1 ∧
      (legOf (st.segs 4 ++ [γ]) ((st.segs 4 ++ [γ]).length - 1)).a = pl hd (pJ e (eJOf hd Y a e τ st)) ∧
      (legOf (st.segs 4 ++ [γ]) ((st.segs 4 ++ [γ]).length - 1)).s = dsg (eJOf hd Y a e τ st) (pJ e (eJOf hd Y a e τ st)) ∧
      Turn hd Y e (dsg (eJOf hd Y a e τ st)) (dsg e) (pJ e (eJOf hd Y a e τ st))
        (legOf (st.segs 4 ++ [γ]) ((st.segs 4 ++ [γ]).length - 1)) (st.segs 5) := by
  obtain ⟨rJ, hrJ, hax, hT⟩ := hI.frame_turnT h5
  obtain ⟨tl4, hl4⟩ : ∃ tl, st.segs 4 = rJ :: tl := by
    rcases hl : st.segs 4 with _ | ⟨r0, tl⟩
    · rw [hl] at hrJ; simp at hrJ
    · rw [hl] at hrJ; simp only [List.head?_cons, Option.some.injEq] at hrJ; subst hrJ; exact ⟨tl, rfl⟩
  obtain ⟨γ, hγ, hlen3, hJE⟩ := hI.frame_jog (by rw [hl4]; simp)
  have hlast : legOf (st.segs 4 ++ [γ]) ((st.segs 4 ++ [γ]).length - 1) = rJ.1 := legOf_append_singleton_last hl4 γ
  obtain ⟨tl3, hl3⟩ : ∃ tl, st.segs 3 = γ :: tl := by
    rcases hl : st.segs 3 with _ | ⟨r0, tl⟩
    · rw [hl] at hγ; simp at hγ
    · rw [hl] at hγ; simp only [List.head?_cons, Option.some.injEq] at hγ; subst hγ; exact ⟨tl, rfl⟩
  have hh3 : (st.segs 3).head? = some γ := by rw [hl3]; rfl
  have htl3 : tl3.length = 1 := by rw [hl3] at hlen3; simp at hlen3; omega
  have hsign : rJ.1.s = dsg (eJOf hd Y a e τ st) (pJ e (eJOf hd Y a e τ st)) := by
    obtain ⟨ha, hs⟩ := hJE.axis_sign (k := (st.segs 4 ++ [γ]).length - 1) (by simp)
    rw [hlast] at ha hs; rw [hax] at ha
    rw [hs, ← pl_injective hd ha]
  refine ⟨γ, hh3, hlen3, by rw [hl3]; exact legOf_head' htl3, hJE, by rw [hl4]; simp, fun k hk => legOf_append_singleton_succ _ _ k,
    legOf_snoc_zero _ _, by rw [hlast]; exact hax, by rw [hlast]; exact hsign, by rw [hlast]; exact hT⟩

end Frames

/-! ## Conclusion for the segments up to the first trunk stretch -/

section Conclusion

variable {st : FS d}

omit [NeZero d] in
/-- Farness only depends on the kept sign. [folklore] -/
theorem FarB.congr {σ σ' : Fin 2 → ℤˣ} {p : Fin 2} (hσ : σ' p = σ p) {s X : BrickPos d} (h : FarB hd Y σ p s X) : FarB hd Y σ' p s X := by
  obtain ⟨hcl, h1, h2⟩ := h
  have oxe : ∀ b : Site d, ox hd σ' p b = ox hd σ p b := fun b => by unfold ox; rw [hσ]
  refine ⟨?_, by rw [oxe, oxe]; exact h1, fun hw => by rw [oxe, oxe]; exact h2 hw⟩
  rcases hcl with h | ⟨ha, hs⟩
  · exact Or.inl h
  · exact Or.inr ⟨ha, by rw [hs, hσ]⟩

/-- The flipped index of the jog turn. [folklore] -/
theorem oth_pJ (e ej : MDir) : oth (pJ e ej) = flipIdx e ej := by unfold pJ keepIdx; exact oth_oth _

omit [NeZero d] in
/-- The jog direction is lateral. [folklore] -/
theorem eJOf_eq_latDir (hd : 3 ≤ d) (Y : FlatLayout) (a : Site 2) (e : MDir) (τ : TTok d) (st : FS d) :
    ∃ b, eJOf hd Y a e τ st = latDir e b := ⟨_, rfl⟩

/-- **Riser against the first plate.** [folklore] -/
theorem FlatInv.disj_seg1 (hI : FlatInv hd Y a e τ st) (hY : Y.OK) {x y : BrickRec d} (hx : x ∈ st.segs 0) (hy : y ∈ st.segs 1) :
    PlateDisj Y.L Y.H x.1 y.1 := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  have h1ne : st.segs 1 ≠ [] := List.ne_nil_of_mem hy
  have hK1 : SegOK hd Y e τ (eJOf hd Y a e τ st) 1 (st.segs 1) (st.segs (startOf 1)) := hI.segOK 1
  simp only [SegOK, startOf, Fin.isValue, Matrix.cons_val] at hK1
  have hRis : Riser hd Y (dsg e) (friseDir hd Y e τ) (plIdx hd τ.ax) (rstart hd e τ (st.segs 0)) (st.segs 1) := hK1 h1ne
  -- the lead-in, its head the riser's start
  obtain ⟨A, tlA, hl0, hh0⟩ := exists_head_of_ne_nil (l := st.segs 0) (List.ne_nil_of_mem hx)
  have hK0 : SegOK hd Y e τ (eJOf hd Y a e τ st) 0 (st.segs 0) (st.segs (startOf 0)) := hI.segOK 0
  simp only [SegOK, startOf, Fin.isValue, Matrix.cons_val] at hK0
  obtain ⟨hD0, -, -⟩ := hK0 (by rw [hl0]; simp)
  have hrs : rstart hd e τ (st.segs 0) = legOf (st.segs 0) ((st.segs 0).length - 1) := by
    rw [legOf_last_of_head hh0]; simp [rstart, hh0]
  obtain ⟨k, hk, hky⟩ := exists_legOf_of_mem hy
  rw [← hky]
  obtain ⟨j, hj, hjx⟩ := exists_legOf_of_mem hx
  rw [← hjx]
  rcases Nat.lt_or_ge j ((st.segs 0).length - 1) with hjlt | hjge
  swap
  · -- the start plate itself
    have : j = (st.segs 0).length - 1 := by omega
    rw [this, ← hrs]; exact (hRis.disj hY).1 k hk
  -- an earlier plate of the lead-in: behind the start in the plane, not beyond it in height
  have hmono : ∀ i, ox hd (dsg e) i (legOf (st.segs 0) j).b ≤ ox hd (dsg e) i (rstart hd e τ (st.segs 0)).b := fun i => by
    rw [hrs]; exact (hD0.mono (k := j) (k' := (st.segs 0).length - 1) (by omega) (by omega) i).1
  have hz0 := (hD0.height_dir (u := friseDir hd Y e τ) rfl (k := j) (k' := (st.segs 0).length - 1) (by omega) (by omega)).1
  rw [← hrs] at hz0
  obtain ⟨hxa, hxs⟩ := hD0.axis_sign hj
  rcases Nat.even_or_odd k with ⟨i, hi⟩ | ⟨i, hi⟩
  · -- a horizontal plate of the riser: beyond the start, hence beyond `x`, in height
    obtain ⟨hya, hys⟩ := (hRis.axis_sign hk).1 (by omega)
    have hV := hRis.uz.1 i (by omega)
    have hVm := hRis.uz_mono (j := 0) (j' := i) (Nat.zero_le _) (by omega)
    have hV0 := hRis.uz.1 0 (by omega)
    simp only [Riser.prev, if_true, Nat.mul_zero] at hV0 hVm
    rw [show i + i = 2 * i by ring] at hi
    rw [hi] at hya hys ⊢
    unfold PlateDisj
    refine sep_wf (friseDir hd Y e τ) (β := legOf (st.segs 0) j) (β' := legOf (st.segs 1) (2 * i)) (by rw [hya, hxa]; exact (pl_ne_ax0 hd _).symm) hys ?_
    rw [hya]
    push_cast at hVm
    have hUm : 0 ≤ (i : ℤ) * (Y.U + Y.m + 1) := by positivity
    linarith [hV0, hVm, hz0]
  · -- a landing of the riser, through the plane axis `q'`: `U` beyond the start along `q'`
    obtain ⟨hya, hys⟩ := (hRis.axis_sign hk).2 (by omega)
    have hface := hRis.land_face (j := i) (by omega)
    have hpl := (hRis.plane (k := 2 * i) (by omega) (qAt (plIdx hd τ.ax) (i + 1))).1
    rw [hi] at hya hys ⊢
    rw [show (2 * i + 1) / 2 + 1 = i + 1 by omega] at hya hys
    refine disj_of_axis_beyond hY hya hys ?_ ?_
    · by_cases hq : qAt (plIdx hd τ.ax) j = qAt (plIdx hd τ.ax) (i + 1)
      · right; rw [← hq]; exact ⟨hxa, hxs⟩
      · left; rw [hxa]; exact fun h' => hq (pl_injective hd h')
    · have := hmono (qAt (plIdx hd τ.ax) (i + 1)); linarith

/-- **Preamble against the entry.** [folklore] -/
theorem FlatInv.disj_seg2 (hI : FlatInv hd Y a e τ st) (hY : Y.OK) {x y : BrickRec d}
    (hx : x ∈ st.segs 0 ∨ x ∈ st.segs 1) (hy : y ∈ st.segs 2) : PlateDisj Y.L Y.H x.1 y.1 := by
  obtain ⟨Rend, hR, q, hPE⟩ := hI.frame_pre (List.ne_nil_of_mem hy)
  obtain ⟨k, hk, hky⟩ := exists_legOf_of_mem hy
  rw [← hky, ← legOf_append_singleton_succ (st.segs 2) Rend k]
  refine disj_entry_pre hY hPE (fun i' => ?_) (fun i' => (hI.prof_entry hx hR i').1) (by simp; exact hk)
  rw [legOf_snoc_zero]; exact (hI.prof_entry hx hR i').2.1

omit [NeZero d] in
/-- The sign relations of the jog turn and of the turn back. [folklore] -/
theorem flip_keep_J (hd : 3 ≤ d) (Y : FlatLayout) (a : Site 2) (e : MDir) (τ : TTok d) (st : FS d) :
    dsg (eJOf hd Y a e τ st) (oth (pJ e (eJOf hd Y a e τ st))) = -dsg e (oth (pJ e (eJOf hd Y a e τ st))) ∧
      dsg (eJOf hd Y a e τ st) (pJ e (eJOf hd Y a e τ st)) = dsg e (pJ e (eJOf hd Y a e τ st)) ∧
      dsg e (oth (pJ e (eJOf hd Y a e τ st))) = -dsg (eJOf hd Y a e τ st) (oth (pJ e (eJOf hd Y a e τ st))) := by
  obtain ⟨bj, hbj⟩ := eJOf_eq_latDir hd Y a e τ st
  have h1 : dsg (eJOf hd Y a e τ st) (oth (pJ e (eJOf hd Y a e τ st))) = -dsg e (oth (pJ e (eJOf hd Y a e τ st))) := by
    rw [oth_pJ, hbj]; exact (dsg_lat e bj).2
  refine ⟨h1, by rw [hbj]; exact (dsg_lat e bj).1, by rw [h1, neg_neg]⟩

/-- **Jog turn against the preamble and the entry.** [folklore] -/
theorem FlatInv.disj_seg3 (hI : FlatInv hd Y a e τ st) (hY : Y.OK) {x y : BrickRec d}
    (hx : (x ∈ st.segs 0 ∨ x ∈ st.segs 1) ∨ x ∈ st.segs 2) (hy : y ∈ st.segs 3) : PlateDisj Y.L Y.H x.1 y.1 := by
  obtain ⟨hflipJ, -, -⟩ := flip_keep_J hd Y a e τ st
  obtain ⟨Rend, hR, q, hPE, h3, hsucc, h0, hT⟩ := hI.jframe (List.ne_nil_of_mem hy)
  obtain ⟨jj, hjj, hjy⟩ := exists_legOf_of_mem hy
  rw [← hjy]
  rcases hx with hx | hx
  · by_cases hxR : x = Rend
    · subst hxR; rw [← h0]; exact disj_feed_turn hY hPE hT hflipJ (by simp) hjj
    · exact disj_far_turn hY hT (hI.farB_entry hY hR hPE h3 hT.sAxis hx hxR) hjj
  · obtain ⟨k, hk, hkx⟩ := exists_legOf_of_mem hx
    rw [← hkx, ← hsucc k hk]
    exact disj_feed_turn hY hPE hT hflipJ (by simp; exact hk) hjj

/-- **Jog against the turn, the preamble and the entry.** [folklore] -/
theorem FlatInv.disj_seg4 (hI : FlatInv hd Y a e τ st) (hY : Y.OK) {x y : BrickRec d}
    (hx : ((x ∈ st.segs 0 ∨ x ∈ st.segs 1) ∨ x ∈ st.segs 2) ∨ x ∈ st.segs 3) (hy : y ∈ st.segs 4) : PlateDisj Y.L Y.H x.1 y.1 := by
  obtain ⟨γ, hγ, hlen3, hJE⟩ := hI.frame_jog (List.ne_nil_of_mem hy)
  have h3ne : st.segs 3 ≠ [] := by intro h; rw [h] at hlen3; simp at hlen3
  obtain ⟨Rend, hR, q, hPE, h3, hsucc, h0, hT⟩ := hI.jframe h3ne
  obtain ⟨tl3, hl3⟩ : ∃ tl, st.segs 3 = γ :: tl := by
    rcases hl : st.segs 3 with _ | ⟨r0, tl⟩
    · rw [hl] at hγ; simp at hγ
    · rw [hl] at hγ; simp only [List.head?_cons, Option.some.injEq] at hγ; subst hγ; exact ⟨tl, rfl⟩
  have htl3 : tl3.length = 1 := by rw [hl3] at hlen3; simp at hlen3; omega
  have hJE0 : legOf (st.segs 4 ++ [γ]) 0 = legOf (st.segs 3) 1 := by
    rw [legOf_snoc_zero, hl3]; exact (legOf_head' htl3).symm
  obtain ⟨k, hk, hky⟩ := exists_legOf_of_mem hy
  rw [← hky, ← legOf_append_singleton_succ (st.segs 4) γ k]
  have hk' : k + 1 < (st.segs 4 ++ [γ]).length := by simp; exact hk
  rcases hx with (hx | hx) | hx
  · by_cases hxR : x = Rend
    · subst hxR; exact disj_farfeed_legafter hY hPE hT hlen3 hJE hJE0 (Or.inr ⟨0, by simp, h0.symm⟩) hk'
    · exact disj_farfeed_legafter hY hPE hT hlen3 hJE hJE0 (Or.inl (hI.farB_entry hY hR hPE h3 hT.sAxis hx hxR)) hk'
  · obtain ⟨m, hm, hmx⟩ := exists_legOf_of_mem hx
    rw [← hmx, ← hsucc m hm]
    exact disj_farfeed_legafter hY hPE hT hlen3 hJE hJE0 (Or.inr ⟨m + 1, by simp; exact hm, rfl⟩) hk'
  · obtain ⟨m, hm, hmx⟩ := exists_legOf_of_mem hx
    rw [← hmx]
    rw [hlen3] at hm
    interval_cases m
    · exact disj_leg_after_turn_top hY hT hlen3 hJE hJE0 hk'
    · rw [← hJE0]; exact hJE.disj hY (by omega) hk'

/-- **Before the trunk turn**: a plate of the entry, the preamble, or the jog turn's top stacking is
far behind the jog's head along the kept coordinate; a plate of the extended jog is on it. [folklore] -/
theorem FlatInv.far_beforeT (hI : FlatInv hd Y a e τ st) (hY : Y.OK) (h5 : st.segs 5 ≠ []) {γ : BrickRec d}
    (hlen3 : (st.segs 3).length = 2) (h31 : legOf (st.segs 3) 1 = γ.1)
    (hJE : DiagLeg hd Y e (dsg (eJOf hd Y a e τ st)) none (oth (pJ e (eJOf hd Y a e τ st))) (st.segs 4 ++ [γ]))
    {x : BrickRec d} (hx : (((x ∈ st.segs 0 ∨ x ∈ st.segs 1) ∨ x ∈ st.segs 2) ∨ x ∈ st.segs 3) ∨ x ∈ st.segs 4) :
    FarB hd Y (dsg (eJOf hd Y a e τ st)) (pJ e (eJOf hd Y a e τ st)) (legOf (st.segs 4 ++ [γ]) ((st.segs 4 ++ [γ]).length - 1)) x.1 ∨
      ∃ k < (st.segs 4 ++ [γ]).length, x.1 = legOf (st.segs 4 ++ [γ]) k := by
  obtain ⟨-, hkeepJ, -⟩ := flip_keep_J hd Y a e τ st
  have h3ne : st.segs 3 ≠ [] := by intro h; rw [h] at hlen3; simp at hlen3
  obtain ⟨Rend, hR, q, hPE, h3, hsucc, h0, hTJ⟩ := hI.jframe h3ne
  have hJE0 : legOf (st.segs 4 ++ [γ]) 0 = legOf (st.segs 3) 1 := by rw [legOf_snoc_zero, h31]
  have h4ne : st.segs 4 ≠ [] := by
    have := hI.order 5 4 (by decide) h5; intro h; rw [h] at this; simp [complete'] at this
  have h2 : 2 ≤ (st.segs 4 ++ [γ]).length := by
    obtain ⟨r, tl, hl, -⟩ := exists_head_of_ne_nil h4ne; rw [hl]; simp
  -- the preamble's head is at least `U` behind the jog's head along the kept coordinate
  have hm0 := hY.facts.2.2.2.2.2.2.2.2; have hH0 : (0 : ℤ) ≤ Y.H := by positivity
  have hkept := (leg_after_turn_kept hY hTJ hlen3 hJE hJE0 (k := (st.segs 4 ++ [γ]).length - 2) (by omega)).1
  rw [show (st.segs 4 ++ [γ]).length - 2 + 1 = (st.segs 4 ++ [γ]).length - 1 by omega] at hkept
  have hstep : ox hd (dsg e) (pJ e (eJOf hd Y a e τ st)) (legOf (st.segs 2 ++ [Rend]) ((st.segs 2 ++ [Rend]).length - 1)).b + Y.U ≤
      ox hd (dsg e) (pJ e (eJOf hd Y a e τ st)) (legOf (st.segs 4 ++ [γ]) ((st.segs 4 ++ [γ]).length - 1)).b := by linarith
  rcases hx with ((hx | hx) | hx) | hx
  · left; refine FarB.congr hkeepJ ?_
    by_cases hxR : x = Rend
    · subst hxR; rw [← h0]; exact farB_feed_of_next hY hPE hTJ.sAxis hTJ.sSign hstep (by simp)
    · have hU := hY.facts.1
      exact (hI.farB_entry hY hR hPE h3 hTJ.sAxis hx hxR).mono (by linarith)
  · left; refine FarB.congr hkeepJ ?_
    obtain ⟨m, hm, hmx⟩ := exists_legOf_of_mem hx
    rw [← hmx, ← hsucc m hm]; exact farB_feed_of_next hY hPE hTJ.sAxis hTJ.sSign hstep (by simp; exact hm)
  · obtain ⟨m, hm, hmx⟩ := exists_legOf_of_mem hx
    rw [← hmx]
    rw [hlen3] at hm
    interval_cases m
    · left
      have hT0 := hTJ.h0 (by omega)
      refine FarB.congr hkeepJ ⟨Or.inr ⟨hT0.axis, by rw [hT0.sign, hTJ.sSign]⟩, ?_, fun hw => absurd hT0.axis hw⟩
      have hface : ox hd (dsg e) (pJ e (eJOf hd Y a e τ st)) (legOf (st.segs 3) 0).b =
          ox hd (dsg e) (pJ e (eJOf hd Y a e τ st)) (legOf (st.segs 2 ++ [Rend]) ((st.segs 2 ++ [Rend]).length - 1)).b + ((Y.H : ℤ) + 1) := by
        unfold ox; rw [hT0.face, hTJ.sSign, mul_add, ← mul_assoc, units_sq, one_mul]
      linarith
    · right; exact ⟨0, by simp, by rw [h31, legOf_snoc_zero]⟩
  · right
    obtain ⟨m, hm, hmx⟩ := exists_legOf_of_mem hx
    exact ⟨m + 1, by simp; exact hm, by rw [legOf_append_singleton_succ, hmx]⟩

/-- **Trunk turn against the jog side and the entry.** [folklore] -/
theorem FlatInv.disj_seg5 (hI : FlatInv hd Y a e τ st) (hY : Y.OK) {x y : BrickRec d}
    (hx : (((x ∈ st.segs 0 ∨ x ∈ st.segs 1) ∨ x ∈ st.segs 2) ∨ x ∈ st.segs 3) ∨ x ∈ st.segs 4) (hy : y ∈ st.segs 5) :
    PlateDisj Y.L Y.H x.1 y.1 := by
  obtain ⟨-, -, hflipT⟩ := flip_keep_J hd Y a e τ st
  have h5 : st.segs 5 ≠ [] := List.ne_nil_of_mem hy
  obtain ⟨γ, hγ, hlen3, h31, hJE, h2, hsuccJ, hJ0, hax, hsx, hT⟩ := hI.tframe h5
  obtain ⟨jj, hjj, hjy⟩ := exists_legOf_of_mem hy
  rw [← hjy]
  rcases hI.far_beforeT hY h5 hlen3 h31 hJE hx with hfar | ⟨k, hk, hkx⟩
  · exact disj_far_turn hY hT hfar hjj
  · rw [hkx]; exact disj_feed_turn hY hJE hT hflipT hk hjj

/-- **First trunk stretch against everything before.** [folklore] -/
theorem FlatInv.disj_seg6 (hI : FlatInv hd Y a e τ st) (hY : Y.OK) {x y : BrickRec d}
    (hx : ((((x ∈ st.segs 0 ∨ x ∈ st.segs 1) ∨ x ∈ st.segs 2) ∨ x ∈ st.segs 3) ∨ x ∈ st.segs 4) ∨ x ∈ st.segs 5) (hy : y ∈ st.segs 6) :
    PlateDisj Y.L Y.H x.1 y.1 := by
  obtain ⟨T₀, hT₀, hlen5, hTE⟩ := hI.frame_trunk (List.ne_nil_of_mem hy)
  have h5ne : st.segs 5 ≠ [] := by intro h; rw [h] at hlen5; simp at hlen5
  obtain ⟨γ, hγ, hlen3, h31, hJE, h2, hsuccJ, hJ0, hax, hsx, hT⟩ := hI.tframe h5ne
  obtain ⟨tl5, hl5⟩ : ∃ tl, st.segs 5 = T₀ :: tl := by
    rcases hl : st.segs 5 with _ | ⟨r0, tl⟩
    · rw [hl] at hT₀; simp at hT₀
    · rw [hl] at hT₀; simp only [List.head?_cons, Option.some.injEq] at hT₀; subst hT₀; exact ⟨tl, rfl⟩
  have htl5 : tl5.length = 1 := by rw [hl5] at hlen5; simp at hlen5; omega
  have hTE' : st.segs 10 ++ st.segs 8 ++ st.segs 6 ++ [T₀] = (st.segs 10 ++ st.segs 8) ++ (st.segs 6 ++ [T₀]) := by simp
  rw [hTE'] at hTE
  have hTE0 : legOf ((st.segs 10 ++ st.segs 8) ++ (st.segs 6 ++ [T₀])) 0 = legOf (st.segs 5) 1 := by
    rw [legOf_append_of_lt _ _ (by simp), legOf_snoc_zero, hl5]; exact (legOf_head' htl5).symm
  obtain ⟨k, hk, hky⟩ := exists_legOf_of_mem hy
  have hyk : y.1 = legOf ((st.segs 10 ++ st.segs 8) ++ (st.segs 6 ++ [T₀])) (k + 1) := by
    rw [legOf_append_of_lt _ _ (by simp; omega), legOf_append_singleton_succ, hky]
  rw [hyk]
  have hk' : k + 1 < ((st.segs 10 ++ st.segs 8) ++ (st.segs 6 ++ [T₀])).length := by simp; omega
  rcases hx with hx | hx
  · exact disj_farfeed_legafter hY hJE hT hlen5 hTE hTE0 (hI.far_beforeT hY h5ne hlen3 h31 hJE hx) hk'
  · obtain ⟨m, hm, hmx⟩ := exists_legOf_of_mem hx
    rw [← hmx]
    rw [hlen5] at hm
    interval_cases m
    · exact disj_leg_after_turn_top hY hT hlen5 hTE hTE0 hk'
    · rw [← hTE0]; exact hTE.disj hY (by omega) hk'

end Conclusion

end BGNd

end Percolation.Literature

end
