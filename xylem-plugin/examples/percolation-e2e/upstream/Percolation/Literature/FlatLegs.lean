import Percolation.Literature.FlatRouteB
import Percolation.Util.Linter

/-!
# The flat gait, IV: diagonal legs

A **diagonal leg** of the flat gait (Grimmett,
*Percolation*, 2nd ed. (1999), §7.3 pp. 172–174 (B), (D), case `H < L`): a nonempty list of plates,
newest first, each the diagonal hop (`DHop`) of its predecessor, the plane axes alternating (`qAt`).
We record this as `DiagLeg` and draw the kinematic consequences used everywhere below: axes and
signs of the plates (`DiagLeg.axis_sign`); both oriented plane coordinates are monotone
(`DiagLeg.mono`); the forward coordinate `u_∥ = σ₀ x₀ + σ₁ x₁` advances by `U + t`, `t ∈ [m+1,
H-m-1]`, at every hop (`DiagLeg.upar_step`); the gaps after two, three and four hops
(`DiagLeg.gaps`) that separate the plates of a leg; the height stays within `max(initial deviation,
L')` of the nominal height, or climbs by at most `L'` a hop; idle coordinates stay within `L'`
(`DiagLeg.idle_le`).

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §7.3 pp. 172–174, (B), (D).
-/

noncomputable section

namespace Percolation.Literature

open LatticeModels Contour
open scoped Classical

namespace BGNd

variable {d : ℕ}

/-! ## Alternating plane axes -/

/-- The plane index of the `k`-th plate of a diagonal leg whose first plate has index `q₀`. [folklore] -/
def qAt (q₀ : Fin 2) (k : ℕ) : Fin 2 := if k % 2 = 0 then q₀ else oth q₀

/-- Consecutive plates have the other index. [folklore] -/
theorem qAt_succ (q₀ : Fin 2) (k : ℕ) : qAt q₀ (k + 1) = oth (qAt q₀ k) := by
  unfold qAt
  rcases Nat.mod_two_eq_zero_or_one k with h | h
  · rw [if_neg (show ¬((k + 1) % 2 = 0) by omega), if_pos h]
  · rw [if_pos (show (k + 1) % 2 = 0 by omega), if_neg (show ¬(k % 2 = 0) by omega), oth_oth]

/-- In `Fin 2`, not the other index means the index. [folklore] -/
theorem eq_of_ne_oth {j x : Fin 2} (h : j ≠ oth x) : j = x := by
  by_contra h'; exact h (oth_eq_iff.2 h').symm

/-- In `Fin 2`, every index is `x` or `oth x`. [folklore] -/
theorem eq_or_eq_oth (j x : Fin 2) : j = x ∨ j = oth x := by
  by_cases h : j = oth x
  · exact Or.inr h
  · exact Or.inl (eq_of_ne_oth h)

/-- The first index. [folklore] -/
@[simp] theorem qAt_zero (q₀ : Fin 2) : qAt q₀ 0 = q₀ := by unfold qAt; simp

/-- Two hops on, the same index. [folklore] -/
theorem qAt_add_two (q₀ : Fin 2) (k : ℕ) : qAt q₀ (k + 2) = qAt q₀ k := by
  rw [show k + 2 = k + 1 + 1 by ring, qAt_succ, qAt_succ, oth_oth]

/-! ## Diagonal legs -/

section Diag

variable [NeZero d] (hd : 3 ≤ d) (Y : FlatLayout) (e : MDir)

/-- The oriented plane coordinates of a base along the signs `σ`. [folklore] -/
def ox (σ : Fin 2 → ℤˣ) (j : Fin 2) (b : Site d) : ℤ := (σ j : ℤ) * b (pl hd j)

/-- The forward diagonal coordinate `u_∥ = σ₀ x₀ + σ₁ x₁`. [folklore] -/
def upar (σ : Fin 2 → ℤˣ) (b : Site d) : ℤ := ox hd σ 0 b + ox hd σ 1 b

/-- **A diagonal leg** of signs `σ`, height mode `zmode`, first index `q₀`: nonempty, first plate of
axis `q₀` and sign `σ q₀`, each later plate the diagonal hop of its predecessor into the alternating
index. [cite: GrimmettPercolation1999, §7.3 pp. 172–174 (B)] -/
structure DiagLeg (σ : Fin 2 → ℤˣ) (zmode : Option Bool) (q₀ : Fin 2) (l : List (BrickRec d)) : Prop where
  ne : l ≠ []
  axis0 : (legOf l 0).a = pl hd q₀
  sign0 : (legOf l 0).s = σ q₀
  chain : ∀ k, k + 1 < l.length → DHop hd Y e σ zmode (qAt q₀ (k + 1)) (legOf l k) (legOf l (k + 1))

variable {hd Y e}
variable {σ : Fin 2 → ℤˣ} {zmode : Option Bool} {q₀ : Fin 2} {l : List (BrickRec d)}

/-- A singleton is a diagonal leg. [folklore] -/
theorem diagLeg_singleton (hd : 3 ≤ d) (Y : FlatLayout) (e : MDir) {r : BrickRec d} (ha : r.1.a = pl hd q₀) (hs : r.1.s = σ q₀) :
    DiagLeg hd Y e σ zmode q₀ [r] :=
  ⟨List.cons_ne_nil _ _, by have := legOf_cons_length r []; rw [List.length_nil] at this; rw [this]; exact ha,
    by have := legOf_cons_length r []; rw [List.length_nil] at this; rw [this]; exact hs, fun k hk => absurd hk (by simp)⟩

/-- **Growing a diagonal leg** by the diagonal hop of its newest plate. [cite: GrimmettPercolation1999, §7.3 pp. 172–174 (B)] -/
theorem diagLeg_cons (h : DiagLeg hd Y e σ zmode q₀ l) {r : BrickRec d}
    (hr : DHop hd Y e σ zmode (qAt q₀ l.length) (legOf l (l.length - 1)) r.1) : DiagLeg hd Y e σ zmode q₀ (r :: l) := by
  have hlen : 0 < l.length := List.length_pos_of_ne_nil h.ne
  refine ⟨List.cons_ne_nil _ _, ?_, ?_, fun k hk => ?_⟩
  · rw [legOf_cons_of_lt _ _ hlen]; exact h.axis0
  · rw [legOf_cons_of_lt _ _ hlen]; exact h.sign0
  · simp only [List.length_cons] at hk
    by_cases hk' : k + 1 < l.length
    · rw [legOf_cons_of_lt _ _ (by omega), legOf_cons_of_lt _ _ hk']; exact h.chain k hk'
    · have hk1 : k + 1 = l.length := by omega
      have hk0 : k = l.length - 1 := by omega
      rw [legOf_cons_of_lt _ _ (by omega), hk1, legOf_cons_length, hk0]; exact hr

/-- **Axes and signs along a diagonal leg.** [folklore] -/
theorem DiagLeg.axis_sign (h : DiagLeg hd Y e σ zmode q₀ l) {k : ℕ} (hk : k < l.length) :
    (legOf l k).a = pl hd (qAt q₀ k) ∧ (legOf l k).s = σ (qAt q₀ k) := by
  induction k with
  | zero => rw [qAt_zero]; exact ⟨h.axis0, h.sign0⟩
  | succ k _ => have hc := h.chain k hk; exact ⟨hc.axis, hc.sign⟩

/-- One hop: the oriented coordinate of the new axis advances by exactly `U`, the other by
`t ∈ [m+1, H-m-1]`. [folklore] -/
theorem DiagLeg.step (h : DiagLeg hd Y e σ zmode q₀ l) {k : ℕ} (hk : k + 1 < l.length) :
    ox hd σ (qAt q₀ (k + 1)) (legOf l (k + 1)).b = ox hd σ (qAt q₀ (k + 1)) (legOf l k).b + Y.U ∧
      (Y.m : ℤ) + 1 ≤ ox hd σ (qAt q₀ k) (legOf l (k + 1)).b - ox hd σ (qAt q₀ k) (legOf l k).b ∧
      ox hd σ (qAt q₀ k) (legOf l (k + 1)).b - ox hd σ (qAt q₀ k) (legOf l k).b ≤ (Y.H : ℤ) - Y.m - 1 := by
  have hc := h.chain k hk
  have hss : (σ (qAt q₀ (k + 1)) : ℤ) * (σ (qAt q₀ (k + 1)) : ℤ) = 1 := by
    rcases Int.units_eq_one_or (σ (qAt q₀ (k + 1))) with h' | h' <;> simp [h']
  unfold ox
  refine ⟨?_, ?_, ?_⟩
  · rw [hc.face, mul_add, ← mul_assoc, hss, one_mul]
  · have := hc.drift.1; rw [qAt_succ, oth_oth] at this; linarith only [this, mul_sub (σ (qAt q₀ k) : ℤ) ((legOf l (k+1)).b (pl hd (qAt q₀ k))) ((legOf l k).b (pl hd (qAt q₀ k)))]
  · have := hc.drift.2; rw [qAt_succ, oth_oth] at this; linarith only [this, mul_sub (σ (qAt q₀ k) : ℤ) ((legOf l (k+1)).b (pl hd (qAt q₀ k))) ((legOf l k).b (pl hd (qAt q₀ k)))]

/-- One hop, for either index: the oriented coordinate advances by `U` or by `t ∈ [m+1, H-m-1]`. [folklore] -/
theorem DiagLeg.step_either (h : DiagLeg hd Y e σ zmode q₀ l) {k : ℕ} (hk : k + 1 < l.length) (j : Fin 2) :
    (j = qAt q₀ (k + 1) → ox hd σ j (legOf l (k + 1)).b = ox hd σ j (legOf l k).b + Y.U) ∧
      (j ≠ qAt q₀ (k + 1) → (Y.m : ℤ) + 1 ≤ ox hd σ j (legOf l (k + 1)).b - ox hd σ j (legOf l k).b ∧
        ox hd σ j (legOf l (k + 1)).b - ox hd σ j (legOf l k).b ≤ (Y.H : ℤ) - Y.m - 1) := by
  obtain ⟨h1, h2, h3⟩ := h.step hk
  refine ⟨fun hj => by rw [hj]; exact h1, fun hj => ?_⟩
  have : j = qAt q₀ k := by rw [qAt_succ] at hj; exact eq_of_ne_oth hj
  rw [this]; exact ⟨h2, h3⟩

/-- **The forward coordinate advances by `U + t` at every hop.** [folklore] -/
theorem DiagLeg.upar_step (h : DiagLeg hd Y e σ zmode q₀ l) {k : ℕ} (hk : k + 1 < l.length) :
    Y.U + Y.m + 1 ≤ upar hd σ (legOf l (k + 1)).b - upar hd σ (legOf l k).b ∧
      upar hd σ (legOf l (k + 1)).b - upar hd σ (legOf l k).b ≤ Y.U + Y.H - Y.m - 1 := by
  obtain ⟨h1, h2, h3⟩ := h.step hk
  unfold upar
  rcases Fin.exists_fin_two.1 ⟨qAt q₀ k, rfl⟩ with hq | hq
  · rw [qAt_succ, hq] at h1; rw [hq] at h2 h3; simp only [show oth 0 = 1 from rfl] at h1
    constructor <;> linarith only [h1, h2, h3]
  · rw [qAt_succ, hq] at h1; rw [hq] at h2 h3; simp only [show oth 1 = 0 from rfl] at h1
    constructor <;> linarith only [h1, h2, h3]

/-- **Both oriented plane coordinates are monotone along a leg**, and the forward coordinate
advances by between `(k' - k)(U + m + 1)` and `(k' - k)(U + H - m - 1)`. [folklore] -/
theorem DiagLeg.mono (h : DiagLeg hd Y e σ zmode q₀ l) {k k' : ℕ} (hkk : k ≤ k') (hk' : k' < l.length) (j : Fin 2) :
    ox hd σ j (legOf l k).b ≤ ox hd σ j (legOf l k').b ∧
      ((k' : ℤ) - k) * (Y.U + Y.m + 1) ≤ upar hd σ (legOf l k').b - upar hd σ (legOf l k).b ∧
      upar hd σ (legOf l k').b - upar hd σ (legOf l k).b ≤ ((k' : ℤ) - k) * (Y.U + Y.H - Y.m - 1) := by
  induction k' with
  | zero =>
    have : k = 0 := by omega
    subst this; simp
  | succ k' ih =>
    rcases Nat.eq_or_lt_of_le hkk with rfl | hlt
    · simp
    · obtain ⟨ih1, ih2, ih3⟩ := ih (by omega) (by omega)
      obtain ⟨hu1, hu2⟩ := h.upar_step (by omega : k' + 1 < l.length)
      obtain ⟨he1, he2⟩ := h.step_either (by omega : k' + 1 < l.length) j
      have hU : 0 ≤ Y.U := by unfold FlatLayout.U; positivity
      have hj : ox hd σ j (legOf l k').b ≤ ox hd σ j (legOf l (k' + 1)).b := by
        by_cases hq : j = qAt q₀ (k' + 1)
        · have := he1 hq; linarith only [this, hU]
        · have := (he2 hq).1; have : (0:ℤ) ≤ Y.m := by positivity
          linarith
      push_cast
      refine ⟨ih1.trans hj, ?_, ?_⟩ <;> nlinarith only [ih2, ih3, hu1, hu2]

/-- **The gaps**: two hops on, the axis coordinate has advanced by at least `U + m + 1`; three hops
on, the other coordinate by at least `2U + m + 1` and the axis coordinate by at least `U + 2m + 2`;
four hops on, both by at least `2U + 2m + 2`. [folklore] -/
theorem DiagLeg.gaps (h : DiagLeg hd Y e σ zmode q₀ l) {k : ℕ} :
    (k + 2 < l.length → Y.U + Y.m + 1 ≤ ox hd σ (qAt q₀ k) (legOf l (k + 2)).b - ox hd σ (qAt q₀ k) (legOf l k).b) ∧
      (k + 3 < l.length →
        2 * Y.U + Y.m + 1 ≤ ox hd σ (qAt q₀ (k + 1)) (legOf l (k + 3)).b - ox hd σ (qAt q₀ (k + 1)) (legOf l k).b ∧
          Y.U + 2 * Y.m + 2 ≤ ox hd σ (qAt q₀ k) (legOf l (k + 3)).b - ox hd σ (qAt q₀ k) (legOf l k).b) ∧
      (k + 4 < l.length → ∀ j : Fin 2, 2 * Y.U + 2 * Y.m + 2 ≤ ox hd σ j (legOf l (k + 4)).b - ox hd σ j (legOf l k).b) := by
  have hU : 0 ≤ Y.U := by unfold FlatLayout.U; positivity
  have hm : (0 : ℤ) ≤ Y.m := by positivity
  -- one hop from index `i`: `+U` for the new axis `qAt (i+1)`, `≥ m+1` for the old one `qAt i`
  have A : ∀ {i : ℕ} (hi : i + 1 < l.length), ox hd σ (qAt q₀ (i + 1)) (legOf l (i + 1)).b = ox hd σ (qAt q₀ (i + 1)) (legOf l i).b + Y.U ∧
      Y.m + 1 ≤ ox hd σ (qAt q₀ i) (legOf l (i + 1)).b - ox hd σ (qAt q₀ i) (legOf l i).b := fun hi =>
    ⟨(h.step hi).1, (h.step hi).2.1⟩
  have e2 : qAt q₀ (k + 2) = qAt q₀ k := qAt_add_two q₀ k
  have e3 : qAt q₀ (k + 3) = qAt q₀ (k + 1) := by rw [show k + 3 = k + 1 + 2 by ring, qAt_add_two]
  have e4 : qAt q₀ (k + 4) = qAt q₀ k := by rw [show k + 4 = k + 2 + 2 by ring, qAt_add_two, qAt_add_two]
  have eB : qAt q₀ (k + 1) = oth (qAt q₀ k) := qAt_succ q₀ k
  refine ⟨fun hk => ?_, fun hk => ?_, fun hk j => ?_⟩
  · obtain ⟨-, b1⟩ := A (i := k) (by omega)
    obtain ⟨a2, -⟩ := A (i := k + 1) (by omega)
    rw [e2] at a2
    linarith only [a2, b1]
  · obtain ⟨a1, b1⟩ := A (i := k) (by omega)
    obtain ⟨a2, b2⟩ := A (i := k + 1) (by omega)
    obtain ⟨a3, b3⟩ := A (i := k + 2) (by omega)
    rw [show k + 2 + 1 = k + 3 by ring] at a3 b3
    rw [e3] at a3; rw [e2] at a2 b3
    exact ⟨by linarith only [a1, b2, a3], by linarith only [b1, a2, b3]⟩
  · obtain ⟨a1, b1⟩ := A (i := k) (by omega)
    obtain ⟨a2, b2⟩ := A (i := k + 1) (by omega)
    obtain ⟨a3, b3⟩ := A (i := k + 2) (by omega)
    obtain ⟨a4, b4⟩ := A (i := k + 3) (by omega)
    rw [show k + 2 + 1 = k + 3 by ring] at a3 b3
    rw [show k + 3 + 1 = k + 4 by ring] at a4 b4
    rw [e3] at a3 b4; rw [e2] at a2 b3; rw [e4] at a4
    rcases eq_or_eq_oth j (qAt q₀ k) with rfl | rfl
    · linarith only [b1, a2, b3, a4, hU, hm]
    · rw [← eB]; linarith only [a1, b2, a3, b4, hU, hm]

/-- **The height along a leg** (mode towards): within `max(initial deviation, L')` of the nominal height. [folklore] -/
theorem DiagLeg.height (h : DiagLeg hd Y e σ none q₀ l) {Z : ℤ} (hZ : Y.Lp ≤ Z) (h0 : |(legOf l 0).b (ax0 hd) - zN Y e| ≤ Z)
    {k : ℕ} (hk : k < l.length) : |(legOf l k).b (ax0 hd) - zN Y e| ≤ Z := by
  induction k with
  | zero => exact h0
  | succ k ih => exact ((h.chain k hk).zt rfl).trans (max_le (ih (by omega)) hZ)

/-- **Idle coordinates along a leg** stay within `L'` once they are. [folklore] -/
theorem DiagLeg.idle_le (h : DiagLeg hd Y e σ zmode q₀ l) (h0 : ∀ i, Idle hd i → |(legOf l 0).b i| ≤ Y.Lp) {k : ℕ} (hk : k < l.length) :
    ∀ i, Idle hd i → |(legOf l k).b i| ≤ Y.Lp := by
  induction k with
  | zero => exact h0
  | succ k ih => intro i hi; exact ((h.chain k hk).idle i hi).trans (max_le (ih (by omega) i hi) le_rfl)

end Diag

end BGNd

end Percolation.Literature

end
