import Percolation.Literature.FlatLegs
import Percolation.Util.Linter

/-!
# The flat gait, V: risers and turns

The two vertical structures of the flat gait (Grimmett,
*Percolation*, 2nd ed. (1999), §7.3 pp. 172–174 (B)–(D), case `H < L`): a **riser** (`Riser`:
up / down hops alternating with landing hops into alternating plane axes, off a plane start plate)
and the **turn** of Grimmett's (C), Fig. 7.11 (`Turn`: a top stacking off the leg's head pushed
towards the new side, then a hop through the new side face), with their growth lemmas and
kinematic consequences: along a riser the oriented height advances by `U + t` a pair and both
oriented plane coordinates are monotone (`Riser.level`, `Riser.plane`, `Riser.land_face`); the
axes and signs of a turn's plates (`Turn.axis_sign`).

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §7.3 pp. 172–174, (A)–(D), Fig. 7.11.
-/

noncomputable section

namespace Percolation.Literature

open LatticeModels Contour
open scoped Classical

namespace BGNd

variable {d : ℕ} [NeZero d] (hd : 3 ≤ d) (Y : FlatLayout)

/-! ## Risers -/

section Riser

/-- **A riser** of direction `u = ±1`, plane signs `σ`, off the plane start plate `s` of index `q₀`:
plates alternate horizontal (`VHop` off the previous plane plate, the first off `s`) and plane
(`PHop` into the alternating index). [cite: GrimmettPercolation1999, §7.3 pp. 172–173 (B)] -/
structure Riser (σ : Fin 2 → ℤˣ) (u : ℤˣ) (q₀ : Fin 2) (s : BrickPos d) (l : List (BrickRec d)) : Prop where
  sAxis : s.a = pl hd q₀
  sSign : s.s = σ q₀
  start : 0 < l.length → VHop hd Y (σ (oth q₀)) u q₀ s (legOf l 0)
  up : ∀ j, 2 * j + 2 < l.length → VHop hd Y (σ (oth (qAt q₀ (j + 1)))) u (qAt q₀ (j + 1)) (legOf l (2 * j + 1)) (legOf l (2 * j + 2))
  land : ∀ j, 2 * j + 1 < l.length → PHop hd Y (σ (oth (qAt q₀ (j + 1)))) (σ (qAt q₀ (j + 1))) (qAt q₀ (j + 1)) (legOf l (2 * j)) (legOf l (2 * j + 1))

variable {hd Y} {σ : Fin 2 → ℤˣ} {u : ℤˣ} {q₀ : Fin 2} {s : BrickPos d} {l : List (BrickRec d)}

/-- The empty riser. [folklore] -/
theorem riser_nil (hd : 3 ≤ d) (Y : FlatLayout) (ha : s.a = pl hd q₀) (hs : s.s = σ q₀) : Riser hd Y σ u q₀ s [] :=
  ⟨ha, hs, fun h => absurd h (by simp), fun j h => absurd h (by simp), fun j h => absurd h (by simp)⟩

/-- **Growing a riser by an up / down hop** (even length). [cite: GrimmettPercolation1999, §7.3 pp. 172–173 (B)] -/
theorem riser_cons_up (h : Riser hd Y σ u q₀ s l) {j : ℕ} (hlen : l.length = 2 * j) {r : BrickRec d}
    (hr : VHop hd Y (σ (oth (qAt q₀ j))) u (qAt q₀ j) (if j = 0 then s else legOf l (2 * j - 1)) r.1) : Riser hd Y σ u q₀ s (r :: l) := by
  refine ⟨h.sAxis, h.sSign, fun _ => ?_, fun j' hj' => ?_, fun j' hj' => ?_⟩
  · rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp only [if_true] at hr
      have : l = [] := List.eq_nil_of_length_eq_zero hlen
      subst this
      have := legOf_cons_length r ([] : List (BrickRec d)); rw [List.length_nil] at this; rw [this, qAt_zero] at *; exact hr
    · rw [legOf_cons_of_lt _ _ (by omega)]; exact h.start (by omega)
  · simp only [List.length_cons] at hj'
    by_cases hlt : 2 * j' + 2 < l.length
    · rw [legOf_cons_of_lt _ _ (by omega), legOf_cons_of_lt _ _ hlt]; exact h.up j' hlt
    · have hj : j' + 1 = j := by omega
      have : 2 * j' + 2 = l.length := by omega
      rw [legOf_cons_of_lt _ _ (by omega), this, legOf_cons_length]
      subst hj; rw [if_neg (by omega), show 2 * (j' + 1) - 1 = 2 * j' + 1 by omega] at hr; exact hr
  · simp only [List.length_cons] at hj'
    have hlt : 2 * j' + 1 < l.length := by omega
    rw [legOf_cons_of_lt _ _ (by omega), legOf_cons_of_lt _ _ hlt]; exact h.land j' hlt

/-- **Growing a riser by a landing hop** (odd length). [cite: GrimmettPercolation1999, §7.3 pp. 172–173 (B)] -/
theorem riser_cons_land (h : Riser hd Y σ u q₀ s l) {j : ℕ} (hlen : l.length = 2 * j + 1) {r : BrickRec d}
    (hr : PHop hd Y (σ (oth (qAt q₀ (j + 1)))) (σ (qAt q₀ (j + 1))) (qAt q₀ (j + 1)) (legOf l (2 * j)) r.1) : Riser hd Y σ u q₀ s (r :: l) := by
  refine ⟨h.sAxis, h.sSign, fun _ => ?_, fun j' hj' => ?_, fun j' hj' => ?_⟩
  · rw [legOf_cons_of_lt _ _ (by omega)]; exact h.start (by omega)
  · simp only [List.length_cons] at hj'
    have hlt : 2 * j' + 2 < l.length := by omega
    rw [legOf_cons_of_lt _ _ (by omega), legOf_cons_of_lt _ _ hlt]; exact h.up j' hlt
  · simp only [List.length_cons] at hj'
    by_cases hlt : 2 * j' + 1 < l.length
    · rw [legOf_cons_of_lt _ _ (by omega), legOf_cons_of_lt _ _ hlt]; exact h.land j' hlt
    · have hj : j' = j := by omega
      subst hj
      rw [legOf_cons_of_lt _ _ (by omega), ← hlen, legOf_cons_length]; exact hr

/-- **Axes and signs along a riser.** [folklore] -/
theorem Riser.axis_sign (h : Riser hd Y σ u q₀ s l) {k : ℕ} (hk : k < l.length) :
    (k % 2 = 0 → (legOf l k).a = ax0 hd ∧ (legOf l k).s = u) ∧
      (k % 2 = 1 → (legOf l k).a = pl hd (qAt q₀ (k / 2 + 1)) ∧ (legOf l k).s = σ (qAt q₀ (k / 2 + 1))) := by
  constructor
  · intro he
    obtain ⟨j, rfl⟩ : ∃ j, k = 2 * j := ⟨k / 2, by omega⟩
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · have := h.start (by omega); exact ⟨this.axis, this.sign⟩
    · have := h.up (j - 1) (by omega)
      rw [show 2 * (j - 1) + 2 = 2 * j by omega] at this; exact ⟨this.axis, this.sign⟩
  · intro ho
    obtain ⟨j, rfl⟩ : ∃ j, k = 2 * j + 1 := ⟨k / 2, by omega⟩
    have := h.land j hk
    rw [show (2 * j + 1) / 2 = j by omega]; exact ⟨this.axis, this.sign⟩

/-- **Levels along a riser**: the oriented height `u z` of the `j`-th landing is at least
`(j + 1)(U + m + 1)` and at most `(j + 1)(U + H - m - 1)` above the start's, and the `j`-th horizontal
plate is exactly `U` above the plate it left. [folklore] -/
theorem Riser.level (h : Riser hd Y σ u q₀ s l) :
    (∀ j, 2 * j + 1 < l.length →
      ((j : ℤ) + 1) * (Y.U + Y.m + 1) ≤ (u : ℤ) * ((legOf l (2 * j + 1)).b (ax0 hd) - s.b (ax0 hd)) ∧
        (u : ℤ) * ((legOf l (2 * j + 1)).b (ax0 hd) - s.b (ax0 hd)) ≤ ((j : ℤ) + 1) * (Y.U + Y.H - Y.m - 1)) ∧
      (∀ j, 2 * j < l.length →
        (u : ℤ) * (legOf l (2 * j)).b (ax0 hd) = (u : ℤ) * (if j = 0 then s else legOf l (2 * j - 1)).b (ax0 hd) + Y.U) := by
  have huu : (u : ℤ) * (u : ℤ) = 1 := by rcases Int.units_eq_one_or u with h' | h' <;> simp [h']
  have hV : ∀ j, 2 * j < l.length → (u : ℤ) * (legOf l (2 * j)).b (ax0 hd) = (u : ℤ) * (if j = 0 then s else legOf l (2 * j - 1)).b (ax0 hd) + Y.U := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · rw [if_pos rfl, (h.start hj).face, mul_add, ← mul_assoc, huu, one_mul]
    · rw [if_neg (by omega)]
      have := (h.up (j - 1) (by omega)).face
      rw [show 2 * (j - 1) + 2 = 2 * j by omega, show 2 * (j - 1) + 1 = 2 * j - 1 by omega] at this
      rw [this, mul_add, ← mul_assoc, huu, one_mul]
  refine ⟨fun j hj => ?_, hV⟩
  induction j with
  | zero =>
    have h0 := hV 0 (by omega); rw [if_pos rfl] at h0
    have hl := h.land 0 hj
    have hd' := hl.drift; rw [(h.start (by omega)).sign] at hd'
    simp only [Nat.mul_zero, CharP.cast_eq_zero, zero_add, one_mul] at h0 hd' ⊢
    constructor <;> linarith only [h0, hd'.1, hd'.2, mul_sub (u : ℤ) ((legOf l 1).b (ax0 hd)) ((legOf l 0).b (ax0 hd)),
      mul_sub (u : ℤ) ((legOf l 1).b (ax0 hd)) (s.b (ax0 hd)), mul_sub (u : ℤ) ((legOf l 0).b (ax0 hd)) (s.b (ax0 hd))]
  | succ j ih =>
    obtain ⟨i1, i2⟩ := ih (by omega)
    have hv := hV (j + 1) (by omega); rw [if_neg (by omega), show 2 * (j + 1) - 1 = 2 * j + 1 by omega] at hv
    have hl := h.land (j + 1) hj
    have hd' := hl.drift
    rw [show 2 * (j + 1) + 1 = 2 * j + 3 by ring] at hd' ⊢
    rw [show 2 * (j + 1) = 2 * j + 2 by ring] at hv hd'
    rw [(h.up j (by omega)).sign] at hd'
    push_cast
    constructor <;> nlinarith only [i1, i2, hv, hd'.1, hd'.2, mul_sub (u : ℤ) ((legOf l (2*j+3)).b (ax0 hd)) ((legOf l (2*j+2)).b (ax0 hd)),
      mul_sub (u : ℤ) ((legOf l (2*j+3)).b (ax0 hd)) (s.b (ax0 hd)), mul_sub (u : ℤ) ((legOf l (2*j+1)).b (ax0 hd)) (s.b (ax0 hd)),
      mul_sub (u : ℤ) ((legOf l (2*j+2)).b (ax0 hd)) ((legOf l (2*j+1)).b (ax0 hd))]

/-- **The plane coordinates along a riser are monotone** (oriented by `σ`): every plate is at least
where the start is, and a landing plate is exactly `U` beyond its horizontal plate through its face. [folklore] -/
theorem Riser.plane (h : Riser hd Y σ u q₀ s l) {k : ℕ} (hk : k < l.length) (i : Fin 2) :
    ox hd σ i s.b ≤ ox hd σ i (legOf l k).b ∧ (0 < k → ox hd σ i (legOf l (k - 1)).b ≤ ox hd σ i (legOf l k).b) := by
  have hm : (0 : ℤ) ≤ Y.m := by positivity
  have hU : 0 ≤ Y.U := by unfold FlatLayout.U; positivity
  -- one step monotonicity
  have step : ∀ k, (hk : k < l.length) → ox hd σ i (if k = 0 then s else legOf l (k - 1)).b ≤ ox hd σ i (legOf l k).b := by
    intro k hk
    unfold ox
    rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
    · -- up hop off a plane plate of index `qAt j`
      have hj' : k = 2 * j := by omega
      subst hj'
      have hv : VHop hd Y (σ (oth (qAt q₀ j))) u (qAt q₀ j) (if 2 * j = 0 then s else legOf l (2 * j - 1)) (legOf l (2 * j)) := by
        rcases Nat.eq_zero_or_pos j with rfl | hpos
        · simpa using h.start hk
        · rw [if_neg (by omega)]
          have := h.up (j - 1) (by omega)
          rwa [show 2 * (j - 1) + 2 = 2 * j by omega, show 2 * (j - 1) + 1 = 2 * j - 1 by omega, show j - 1 + 1 = j by omega] at this
      have hsrcS : (if 2 * j = 0 then s else legOf l (2 * j - 1)).s = σ (qAt q₀ j) := by
        rcases Nat.eq_zero_or_pos j with rfl | hpos
        · simpa using h.sSign
        · rw [if_neg (by omega)]
          have := (h.land (j - 1) (by omega)).sign
          rwa [show 2 * (j - 1) + 1 = 2 * j - 1 by omega, show j - 1 + 1 = j by omega] at this
      rcases eq_or_eq_oth i (qAt q₀ j) with rfl | rfl
      · have := hv.drift.1; rw [hsrcS] at this; nlinarith only [this, hm]
      · have := hv.push.1; nlinarith only [this]
    · have hj' : k = 2 * j + 1 := by omega
      subst hj'
      rw [if_neg (by omega), show 2 * j + 1 - 1 = 2 * j by omega]
      have hp := h.land j hk
      rcases eq_or_eq_oth i (qAt q₀ (j + 1)) with rfl | rfl
      · have := hp.face
        have hss : (σ (qAt q₀ (j + 1)) : ℤ) * (σ (qAt q₀ (j + 1)) : ℤ) = 1 := by
          rcases Int.units_eq_one_or (σ (qAt q₀ (j + 1))) with h' | h' <;> simp [h']
        rw [this, mul_add, ← mul_assoc, hss, one_mul]; linarith only [hU]
      · have := hp.push.1; nlinarith only [this]
  induction k with
  | zero => have := step 0 hk; simp only [if_true] at this; exact ⟨this, fun h => absurd h (lt_irrefl 0)⟩
  | succ k ih =>
    have := step (k + 1) hk; rw [if_neg (by omega), Nat.add_sub_cancel] at this
    exact ⟨(ih (by omega)).1.trans this, fun _ => this⟩

/-- The exact advance of a landing plate through its face. [folklore] -/
theorem Riser.land_face (h : Riser hd Y σ u q₀ s l) {j : ℕ} (hj : 2 * j + 1 < l.length) :
    ox hd σ (qAt q₀ (j + 1)) (legOf l (2 * j + 1)).b = ox hd σ (qAt q₀ (j + 1)) (legOf l (2 * j)).b + Y.U := by
  have hp := h.land j hj
  have hss : (σ (qAt q₀ (j + 1)) : ℤ) * (σ (qAt q₀ (j + 1)) : ℤ) = 1 := by
    rcases Int.units_eq_one_or (σ (qAt q₀ (j + 1))) with h' | h' <;> simp [h']
  unfold ox; rw [hp.face, mul_add, ← mul_assoc, hss, one_mul]

end Riser

/-! ## Turns -/

section Turn

variable (e : MDir)

/-- **A turn** of old signs `σ` into new signs `σ'` (equal on the kept index `p`, opposite on the
flipped index `oth p`), off the plane plate `s` of index `p`: a top stacking off `s` pushed towards
the new side, then a hop through the new side face. [cite: GrimmettPercolation1999, §7.3 pp. 172–173 (A)–(C), Fig. 7.11] -/
structure Turn (σ σ' : Fin 2 → ℤˣ) (p : Fin 2) (s : BrickPos d) (l : List (BrickRec d)) : Prop where
  sAxis : s.a = pl hd p
  sSign : s.s = σ p
  keep : σ' p = σ p
  len : l.length ≤ 2
  h0 : 0 < l.length → THop hd Y e (σ' (oth p)) p s (legOf l 0)
  h1 : 1 < l.length → DHop hd Y e σ' none (oth p) (legOf l 0) (legOf l 1)

variable {hd Y e} {σ σ' : Fin 2 → ℤˣ} {p : Fin 2} {s : BrickPos d} {l : List (BrickRec d)}

/-- The empty turn. [folklore] -/
theorem turn_nil (hd : 3 ≤ d) (Y : FlatLayout) (e : MDir) (ha : s.a = pl hd p) (hs : s.s = σ p) (hk : σ' p = σ p) : Turn hd Y e σ σ' p s [] :=
  ⟨ha, hs, hk, by simp, fun h => absurd h (by simp), fun h => absurd h (by simp)⟩

/-- **Growing a turn by its top stacking.** [cite: GrimmettPercolation1999, §7.3 p. 172 (A)] -/
theorem turn_cons_top (h : Turn hd Y e σ σ' p s []) {r : BrickRec d} (hr : THop hd Y e (σ' (oth p)) p s r.1) : Turn hd Y e σ σ' p s [r] :=
  ⟨h.sAxis, h.sSign, h.keep, by simp, fun _ => by
    have := legOf_cons_length r ([] : List (BrickRec d)); rw [List.length_nil] at this; rw [this]; exact hr,
    fun h' => absurd h' (by simp)⟩

/-- **Growing a turn by its hop through the new side face.** [cite: GrimmettPercolation1999, §7.3 pp. 172–173 (B)–(C)] -/
theorem turn_cons_hop {r' : BrickRec d} (h : Turn hd Y e σ σ' p s [r']) {r : BrickRec d} (hr : DHop hd Y e σ' none (oth p) r'.1 r.1) :
    Turn hd Y e σ σ' p s [r, r'] := by
  have e0 : legOf [r, r'] 0 = r'.1 := by
    rw [show [r, r'] = r :: [r'] from rfl, legOf_cons_of_lt _ _ (by simp)]
    have := legOf_cons_length r' ([] : List (BrickRec d)); rwa [List.length_nil] at this
  have e1 : legOf [r, r'] 1 = r.1 := by
    have := legOf_cons_length r [r']; exact this
  refine ⟨h.sAxis, h.sSign, h.keep, by simp, fun _ => ?_, fun _ => ?_⟩
  · rw [e0]; have := h.h0 (by simp); have e0' := legOf_cons_length r' ([] : List (BrickRec d)); rw [List.length_nil] at e0'; rwa [e0'] at this
  · rw [e0, e1]; exact hr

/-- **Axes and signs in a turn**: the top stacking has the start's, the hop the flipped axis with
the new sign. [folklore] -/
theorem Turn.axis_sign (h : Turn hd Y e σ σ' p s l) :
    (0 < l.length → (legOf l 0).a = pl hd p ∧ (legOf l 0).s = σ p) ∧
      (1 < l.length → (legOf l 1).a = pl hd (oth p) ∧ (legOf l 1).s = σ' (oth p)) :=
  ⟨fun hk => ⟨(h.h0 hk).axis, by rw [(h.h0 hk).sign, h.sSign]⟩, fun hk => ⟨(h.h1 hk).axis, (h.h1 hk).sign⟩⟩

end Turn

end BGNd

end Percolation.Literature

end
