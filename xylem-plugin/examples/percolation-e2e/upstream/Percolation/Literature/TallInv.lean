import Percolation.Literature.TallRoute
import Percolation.Util.Linter

/-!
# The tall gait, II: legs read off the run state, and the steering lemmas

Book-keeping for the plan `TallRoute.lean` of the block
construction of Grimmett, *Percolation*, 2nd ed. (1999), §7.3, Lemma (7.52): the segments of the run
state are lists of records, newest first; `legOf l` reads such a list as a sequence of placements
`ℕ → BrickPos d` (oldest first), to which the kinematics of `GaitKinematics.lean` apply. We prove the
list lemmas (`legOf_cons_of_lt`, `legOf_cons_length`), the effect of the requested signs
(`toward`, `force`) on one top or side step — a free coordinate moves towards its nominal value,
so its deviation never exceeds `max(previous deviation, L - m - 1)` (`abs_sub_le_of_toward`,
`abs_sub_le_of_toward_side`), a forced one moves in the forced direction (`forced_nonneg`,
`forced_nonneg_side`) — and package "the list is a leg grown by top steps off good records" as
`Grown` (`grown_singleton`, `grown_cons`), whose consequence here is that the placements form an
`IsLeg` (`Grown.isLeg`); the steering and deviation consequences are drawn in the sequel
(`TallInvariant.lean` ff.).

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §7.3 pp. 172–173, (A), (D).
-/

noncomputable section

namespace Percolation.Literature

open LatticeModels Contour
open scoped Classical

namespace BGNd

variable {d : ℕ} [NeZero d]

/-! ## Lists of records as legs -/

/-- The `k`-th oldest record of a list of records kept newest first (junk beyond the length). [folklore] -/
def recOf (l : List (BrickRec d)) (k : ℕ) : BrickRec d := (l.reverse[k]?).getD (⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩, 1, 0⟩, ∅)

/-- The `k`-th oldest placement. [folklore] -/
def legOf (l : List (BrickRec d)) (k : ℕ) : BrickPos d := (recOf l k).1

/-- Older entries are unchanged by a new record. [folklore] -/
theorem recOf_cons_of_lt (r : BrickRec d) (l : List (BrickRec d)) {k : ℕ} (hk : k < l.length) : recOf (r :: l) k = recOf l k := by
  unfold recOf
  rw [List.reverse_cons, List.getElem?_append_left (by simpa using hk)]

/-- The new record is the `length`-th oldest. [folklore] -/
theorem recOf_cons_length (r : BrickRec d) (l : List (BrickRec d)) : recOf (r :: l) l.length = r := by
  unfold recOf
  rw [List.reverse_cons, List.getElem?_append_right (by simp)]
  simp

/-- The newest record is the `(length - 1)`-th oldest. [folklore] -/
theorem recOf_cons_pred_length (r : BrickRec d) (l : List (BrickRec d)) : recOf (r :: l) ((r :: l).length - 1) = r := by
  rw [List.length_cons, Nat.add_sub_cancel]
  exact recOf_cons_length r l

/-- Older placements are unchanged by a new record. [folklore] -/
theorem legOf_cons_of_lt (r : BrickRec d) (l : List (BrickRec d)) {k : ℕ} (hk : k < l.length) : legOf (r :: l) k = legOf l k := by
  unfold legOf; rw [recOf_cons_of_lt r l hk]

/-- The new placement. [folklore] -/
theorem legOf_cons_length (r : BrickRec d) (l : List (BrickRec d)) : legOf (r :: l) l.length = r.1 := by
  unfold legOf; rw [recOf_cons_length]

/-- Every record of the list is some `recOf l k`, `k < length`. [folklore] -/
theorem exists_recOf_of_mem {l : List (BrickRec d)} {r : BrickRec d} (hr : r ∈ l) : ∃ k < l.length, recOf l k = r := by
  have hr' : r ∈ l.reverse := List.mem_reverse.2 hr
  obtain ⟨k, hk, hkr⟩ := List.getElem_of_mem hr'
  refine ⟨k, by simpa using hk, ?_⟩
  unfold recOf
  rw [List.getElem?_eq_getElem hk, hkr]
  rfl

/-- Conversely `recOf l k ∈ l` for `k < length`. [folklore] -/
theorem recOf_mem {l : List (BrickRec d)} {k : ℕ} (hk : k < l.length) : recOf l k ∈ l := by
  have hk' : k < l.reverse.length := by simpa using hk
  unfold recOf
  rw [List.getElem?_eq_getElem hk']
  exact List.mem_reverse.1 (List.getElem_mem hk')

/-! ## The effect of the requested signs on one top step -/

section Toward

variable {m L H : ℕ} (hL : m + 1 ≤ L) (hH : 2 * m + 2 ≤ H)

/-- **A free coordinate moves towards its nominal value**: after a top step requested by `toward nom`
(possibly overridden elsewhere), in a coordinate `i ≠ axis` where the request is `toward`'s, the
deviation from `nom i` is at most `max(previous deviation, L - m - 1)`.
[cite: GrimmettPercolation1999, §7.3 p. 173 (D)] -/
theorem abs_sub_le_of_toward {r : BrickRec d} (h : GoodRec m L H r) {sg : Fin d → Bool} {nom : Site d} {i : Fin d}
    (hi : i ≠ r.1.a) (hsg : sg i = toward nom r.1.b i) :
    |(tStep hL hH r sg).b i - nom i| ≤ max |r.1.b i - nom i| ((L : ℤ) - m - 1) := by
  obtain ⟨habs, hpos, hneg⟩ := (tStep_rel hL hH h sg).2 i hi
  have habs' := abs_le.1 habs
  rw [hsg] at hpos hneg
  unfold toward at hpos hneg
  by_cases hle : r.1.b i ≤ nom i
  · have h0 := hpos (by simpa using hle)
    rw [abs_le]
    constructor
    · have : -(max |r.1.b i - nom i| ((L : ℤ) - m - 1)) ≤ -|r.1.b i - nom i| := neg_le_neg (le_max_left _ _)
      refine le_trans this ?_
      have := neg_abs_le (r.1.b i - nom i)
      linarith
    · exact le_trans (by linarith) (le_max_right _ _)
  · have h0 := hneg (by simpa using hle)
    push Not at hle
    rw [abs_le]
    constructor
    · have : -(max |r.1.b i - nom i| ((L : ℤ) - m - 1)) ≤ -((L : ℤ) - m - 1) := neg_le_neg (le_max_right _ _)
      refine le_trans this ?_
      linarith
    · refine le_trans ?_ (le_max_left _ _)
      have := le_abs_self (r.1.b i - nom i)
      linarith

/-- **A forced coordinate moves in the forced direction** (by at most `L - m - 1`). [cite: GrimmettPercolation1999, §7.3 p. 173 (D)] -/
theorem forced_nonneg {r : BrickRec d} (h : GoodRec m L H r) {sg : Fin d → Bool} {i : Fin d} (hi : i ≠ r.1.a) {w : ℤ}
    (hw : w = 1 ∨ w = -1) (hsg : sg i = decide (0 ≤ w)) :
    0 ≤ w * ((tStep hL hH r sg).b i - r.1.b i) ∧ w * ((tStep hL hH r sg).b i - r.1.b i) ≤ (L : ℤ) - m - 1 := by
  obtain ⟨habs, hpos, hneg⟩ := (tStep_rel hL hH h sg).2 i hi
  have habs' := abs_le.1 habs
  rw [hsg] at hpos hneg
  rcases hw with rfl | rfl
  · have := hpos (by decide)
    constructor <;> linarith
  · have := hneg (by decide)
    constructor <;> linarith

omit [NeZero d] in
/-- The request of `force sg i v` in coordinate `i`. [folklore] -/
@[simp] theorem force_self (sg : Fin d → Bool) (i : Fin d) (v : ℤ) : force sg i v i = decide (0 ≤ v) := by
  simp [force]

omit [NeZero d] in
/-- The request of `force sg i v` elsewhere. [folklore] -/
theorem force_of_ne (sg : Fin d → Bool) {i j : Fin d} (h : j ≠ i) (v : ℤ) : force sg i v j = sg j := by
  simp [force, h]

/-- The side-step analogue of `abs_sub_le_of_toward`, for a coordinate other than the old and the
new axis. [cite: GrimmettPercolation1999, §7.3 p. 173 (D)] -/
theorem abs_sub_le_of_toward_side {r : BrickRec d} (h : GoodRec m L H r) {i : Fin d} (hi : i ≠ r.1.a) (u : ℤˣ)
    {sg : Fin d → Bool} {nom : Site d} {j : Fin d} (hj : j ≠ r.1.a) (hji : j ≠ i) (hsg : sg j = toward nom r.1.b j) :
    |(sStep hL hH r i u sg).b j - nom j| ≤ max |r.1.b j - nom j| ((L : ℤ) - m - 1) := by
  obtain ⟨-, -, hoth, -, -⟩ := sideExit_spec hL hH h hi u sg
  obtain ⟨habs, hpos, hneg⟩ := hoth j hj hji
  rw [sStep_b]
  have habs' := abs_le.1 habs
  rw [hsg] at hpos hneg
  unfold toward at hpos hneg
  by_cases hle : r.1.b j ≤ nom j
  · have h0 := hpos (by simpa using hle)
    rw [abs_le]
    constructor
    · have : -(max |r.1.b j - nom j| ((L : ℤ) - m - 1)) ≤ -|r.1.b j - nom j| := neg_le_neg (le_max_left _ _)
      refine le_trans this ?_
      have := neg_abs_le (r.1.b j - nom j)
      linarith
    · exact le_trans (by linarith) (le_max_right _ _)
  · have h0 := hneg (by simpa using hle)
    push Not at hle
    rw [abs_le]
    constructor
    · have : -(max |r.1.b j - nom j| ((L : ℤ) - m - 1)) ≤ -((L : ℤ) - m - 1) := neg_le_neg (le_max_right _ _)
      refine le_trans this ?_
      linarith
    · refine le_trans ?_ (le_max_left _ _)
      have := le_abs_self (r.1.b j - nom j)
      linarith

/-- The side-step analogue of `forced_nonneg`. [cite: GrimmettPercolation1999, §7.3 p. 173 (D)] -/
theorem forced_nonneg_side {r : BrickRec d} (h : GoodRec m L H r) {i : Fin d} (hi : i ≠ r.1.a) (u : ℤˣ)
    {sg : Fin d → Bool} {j : Fin d} (hj : j ≠ r.1.a) (hji : j ≠ i) {w : ℤ} (hw : w = 1 ∨ w = -1) (hsg : sg j = decide (0 ≤ w)) :
    0 ≤ w * ((sStep hL hH r i u sg).b j - r.1.b j) ∧ w * ((sStep hL hH r i u sg).b j - r.1.b j) ≤ (L : ℤ) - m - 1 := by
  obtain ⟨-, -, hoth, -, -⟩ := sideExit_spec hL hH h hi u sg
  obtain ⟨habs, hpos, hneg⟩ := hoth j hj hji
  rw [sStep_b]
  have habs' := abs_le.1 habs
  rw [hsg] at hpos hneg
  rcases hw with rfl | rfl
  · have := hpos (by decide)
    constructor <;> linarith
  · have := hneg (by decide)
    constructor <;> linarith

end Toward

/-! ## Grown legs -/

section Grown

variable {m L H : ℕ} (hL : m + 1 ≤ L) (hH : 2 * m + 2 ≤ H)

/-- **A list grown by top steps**: nonempty, every older record good, and each record's placement the
top step off the previous record for SOME request. [cite: GrimmettPercolation1999, §7.3 p. 172 (A)] -/
def Grown (l : List (BrickRec d)) : Prop :=
  l ≠ [] ∧ (∀ k, k + 1 < l.length → GoodRec m L H (recOf l k)) ∧
    ∀ k, k + 1 < l.length → ∃ sg, legOf l (k + 1) = tStep hL hH (recOf l k) sg

/-- A singleton is grown. [folklore] -/
theorem grown_singleton (r : BrickRec d) : Grown hL hH [r] :=
  ⟨List.cons_ne_nil _ _, fun k hk => absurd hk (by simp), fun k hk => absurd hk (by simp)⟩

/-- Growing by one top step off the newest record, which is good. [folklore] -/
theorem grown_cons {l : List (BrickRec d)} (hg : Grown hL hH l) {r₀ : BrickRec d} (h0 : l.head? = some r₀) (hgood : GoodRec m L H r₀)
    (sg : Fin d → Bool) (o : Finset (Sym2 (Site d))) : Grown hL hH ((tStep hL hH r₀ sg, o) :: l) := by
  obtain ⟨hne, hgoods, hsteps⟩ := hg
  have hlast : recOf l (l.length - 1) = r₀ := by
    obtain ⟨r₁, l', rfl⟩ := List.exists_cons_of_ne_nil hne
    simp only [List.head?_cons, Option.some.injEq] at h0
    subst h0
    exact recOf_cons_pred_length r₁ l'
  have hlen : 0 < l.length := List.length_pos_of_ne_nil hne
  refine ⟨List.cons_ne_nil _ _, fun k hk => ?_, fun k hk => ?_⟩
  · rw [List.length_cons] at hk
    rw [recOf_cons_of_lt _ _ (by omega)]
    rcases Nat.lt_or_ge (k + 1) l.length with hlt | hge
    · exact hgoods k hlt
    · have : k = l.length - 1 := by omega
      rw [this, hlast]; exact hgood
  · rw [List.length_cons] at hk
    rcases Nat.lt_or_ge (k + 1) l.length with hlt | hge
    · rw [legOf_cons_of_lt _ _ hlt, recOf_cons_of_lt _ _ (by omega)]
      exact hsteps k hlt
    · have hk' : k = l.length - 1 := by omega
      refine ⟨sg, ?_⟩
      rw [recOf_cons_of_lt _ _ (by omega), hk', hlast, show l.length - 1 + 1 = l.length by omega, legOf_cons_length]

/-- **A grown list is a leg** along the axis and direction of its oldest placement. [cite: GrimmettPercolation1999, §7.3 p. 172 (A)] -/
theorem Grown.isLeg {l : List (BrickRec d)} (hg : Grown hL hH l) :
    IsLeg m L H (legOf l 0).a (legOf l 0).s (l.length - 1) (legOf l) := by
  obtain ⟨hne, hgoods, hsteps⟩ := hg
  choose! sg hsg using hsteps
  have := isLeg_of_tSteps hL hH (n := l.length - 1) (β := legOf l) (o := fun k => (recOf l k).2) (sg := sg)
    (fun k hk => by have := hgoods k (by omega); exact this) (fun k hk => by have := hsg k (by omega); exact this)
  exact this

end Grown

end BGNd

end Percolation.Literature

end
