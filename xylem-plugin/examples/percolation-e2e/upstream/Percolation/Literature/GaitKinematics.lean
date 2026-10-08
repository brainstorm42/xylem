import Percolation.Literature.HalfSpaceHighDimPlaced
import Percolation.Util.Linter

/-!
# Kinematics of stacked bricks: coordinate intervals of support boxes, legs and turns

Elementary geometry for the block construction of
Lemma (7.52) of Grimmett, *Percolation*, 2nd ed. (1999), §7.3, pp. 169–176 ((A) top stacking,
(B) side stacking, (C) "the intersection of a new brick with the region considered so far must be
limited to a subset of its underside", (D) steering): the support of a placed clean brick
(`HalfSpaceHighDimPlaced.lean`) lies in the box `boxOf L H β` of doubled midpoints, a product of
integer intervals; two supports are disjoint as soon as their boxes are separated along ONE
coordinate. This file records the intervals and proves the separation facts used by the gaits:

* `BGNd.lo β i`, `BGNd.hi β i` — the coordinate intervals of `boxOf L H β`, `mem_boxOf_iff_coord`,
  `disjoint_boxOf_of_sep`;
* **legs** (top stackings along a fixed axis and direction, Grimmett (A)): `BGNd.IsLeg` — consecutive
  base centres differ by exactly `H + 1` along the axis and by at most `L' = L - m - 1` transversally;
  the boxes of a leg are pairwise disjoint (`IsLeg.disjoint_boxOf`);

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §7.3 pp. 172–174, (A)–(D).
-/

noncomputable section

namespace Percolation.Literature

open LatticeModels

namespace BGNd

variable {d : ℕ} [NeZero d] {m L H : ℕ}

/-! ## Coordinate intervals of support boxes -/

/-- The lower end of the `i`-th coordinate interval of `boxOf L H β`. [folklore] -/
def lo (L H : ℕ) (β : BrickPos d) (i : Fin d) : ℤ :=
  if i = β.a then (if β.s = 1 then 2 * β.b i + 1 else 2 * β.b i - 2 * H - 2) else 2 * β.b i - 2 * L - 2

/-- The upper end of the `i`-th coordinate interval of `boxOf L H β`. [folklore] -/
def hi (L H : ℕ) (β : BrickPos d) (i : Fin d) : ℤ :=
  if i = β.a then (if β.s = 1 then 2 * β.b i + 2 * H + 2 else 2 * β.b i - 1) else 2 * β.b i + 2 * L + 2

omit [NeZero d] in
/-- **The box is the product of its coordinate intervals.** [folklore] -/
theorem mem_boxOf_iff_coord {β : BrickPos d} {w : Site d} :
    w ∈ boxOf L H β ↔ ∀ i, lo L H β i ≤ w i ∧ w i ≤ hi L H β i := by
  rw [mem_boxOf]
  constructor
  · rintro ⟨hax, hoth⟩ i
    unfold lo hi
    by_cases hia : i = β.a
    · subst hia
      simp only [↓reduceIte]
      rcases Int.units_eq_one_or β.s with h | h <;> simp only [h, Units.val_one, Units.val_neg, one_mul, neg_mul,
        ↓reduceIte] at hax ⊢
      · constructor <;> omega
      · have : ((-1 : ℤˣ) = 1) = False := by decide
        simp only [this, ↓reduceIte]
        constructor <;> omega
    · simp only [hia, ↓reduceIte]
      have := abs_le.1 (hoth i hia)
      constructor <;> omega
  · intro h
    refine ⟨?_, fun i hia => ?_⟩
    · have h0 := h β.a
      unfold lo hi at h0
      simp only [↓reduceIte] at h0
      rcases Int.units_eq_one_or β.s with hs | hs <;> simp only [hs, Units.val_one, Units.val_neg, one_mul, neg_mul,
        ↓reduceIte] at h0 ⊢
      · constructor <;> omega
      · have : ((-1 : ℤˣ) = 1) = False := by decide
        simp only [this, ↓reduceIte] at h0
        constructor <;> omega
    · have h1 := h i
      unfold lo hi at h1
      simp only [hia, ↓reduceIte] at h1
      exact abs_le.2 ⟨by omega, by omega⟩

omit [NeZero d] in
/-- **Separation along one coordinate gives disjoint boxes.** [folklore] -/
theorem disjoint_boxOf_of_sep {β β' : BrickPos d} {L' H' : ℕ} (i : Fin d) (h : hi L H β i < lo L' H' β' i) :
    Disjoint (boxOf L H β) (boxOf L' H' β') := by
  rw [Set.disjoint_left]
  intro w hw hw'
  have h1 := (mem_boxOf_iff_coord.1 hw i).2
  have h2 := (mem_boxOf_iff_coord.1 hw' i).1
  omega

omit [NeZero d] in
/-- Symmetric form. [folklore] -/
theorem disjoint_boxOf_of_sep' {β β' : BrickPos d} {L' H' : ℕ} (i : Fin d) (h : hi L' H' β' i < lo L H β i) :
    Disjoint (boxOf L H β) (boxOf L' H' β') :=
  (disjoint_boxOf_of_sep i h).symm

omit [NeZero d] in
/-- The axis interval of a brick of direction `+1`. [folklore] -/
theorem lo_hi_axis_pos {β : BrickPos d} (hs : β.s = 1) :
    lo L H β β.a = 2 * β.b β.a + 1 ∧ hi L H β β.a = 2 * β.b β.a + 2 * H + 2 := by
  simp [lo, hi, hs]

omit [NeZero d] in
/-- The axis interval of a brick of direction `-1`. [folklore] -/
theorem lo_hi_axis_neg {β : BrickPos d} (hs : β.s = -1) :
    lo L H β β.a = 2 * β.b β.a - 2 * H - 2 ∧ hi L H β β.a = 2 * β.b β.a - 1 := by
  have : ((-1 : ℤˣ) = 1) = False := by decide
  simp [lo, hi, hs, this]

omit [NeZero d] in
/-- The transverse intervals. [folklore] -/
theorem lo_hi_of_ne {β : BrickPos d} {i : Fin d} (hi' : i ≠ β.a) :
    lo L H β i = 2 * β.b i - 2 * L - 2 ∧ hi L H β i = 2 * β.b i + 2 * L + 2 := by
  simp [lo, hi, hi']

/-! ## Legs -/

/-- **A leg**: the placements `β 0, …, β n` are top stackings along the axis `ax` in the direction
`sg`: all have axis `ax` and sign `sg`, consecutive base centres differ by exactly `H + 1` along the
axis and by at most `L - m - 1` in every other coordinate (Grimmett (A), (D)).
[cite: GrimmettPercolation1999, §7.3 p. 172 (A), p. 173 (D)] -/
structure IsLeg (m L H : ℕ) (ax : Fin d) (sg : ℤˣ) (n : ℕ) (β : ℕ → BrickPos d) : Prop where
  axis : ∀ k ≤ n, (β k).a = ax
  sign : ∀ k ≤ n, (β k).s = sg
  step : ∀ k < n, (β (k + 1)).b ax = (β k).b ax + (sg : ℤ) * ((H : ℤ) + 1)
  wobble : ∀ k < n, ∀ i, i ≠ ax → |(β (k + 1)).b i - (β k).b i| ≤ (L : ℤ) - m - 1

namespace IsLeg

variable {ax : Fin d} {sg : ℤˣ} {n : ℕ} {β : ℕ → BrickPos d}

omit [NeZero d] in
/-- Along a leg the axis coordinate moves by `(k' - k)(H + 1)`. [folklore] -/
theorem b_axis (h : IsLeg m L H ax sg n β) {k k' : ℕ} (hkk' : k ≤ k') (hk' : k' ≤ n) :
    (β k').b ax = (β k).b ax + (sg : ℤ) * ((H : ℤ) + 1) * ((k' : ℤ) - k) := by
  induction k' with
  | zero =>
    have : k = 0 := by omega
    subst this; simp
  | succ k' ih =>
    rcases Nat.eq_or_lt_of_le hkk' with rfl | hlt
    · simp
    · rw [h.step k' (by omega), ih (by omega) (by omega)]
      push_cast; ring

omit [NeZero d] in
/-- Along a leg a transverse coordinate moves by at most `(k' - k)(L - m - 1)`. [folklore] -/
theorem abs_b_sub_le (h : IsLeg m L H ax sg n β) {i : Fin d} (hi' : i ≠ ax) {k k' : ℕ} (hkk' : k ≤ k') (hk' : k' ≤ n) :
    |(β k').b i - (β k).b i| ≤ ((k' : ℤ) - k) * ((L : ℤ) - m - 1) := by
  induction k' with
  | zero =>
    have : k = 0 := by omega
    subst this; simp
  | succ k' ih =>
    rcases Nat.eq_or_lt_of_le hkk' with rfl | hlt
    · simp
    · have h1 := ih (by omega) (by omega)
      have h2 := h.wobble k' (by omega) i hi'
      calc |(β (k' + 1)).b i - (β k).b i| = |((β (k' + 1)).b i - (β k').b i) + ((β k').b i - (β k).b i)| := by ring_nf
        _ ≤ |(β (k' + 1)).b i - (β k').b i| + |(β k').b i - (β k).b i| := abs_add_le _ _
        _ ≤ ((L : ℤ) - m - 1) + ((k' : ℤ) - k) * ((L : ℤ) - m - 1) := add_le_add h2 h1
        _ = (((k' + 1 : ℕ) : ℤ) - k) * ((L : ℤ) - m - 1) := by push_cast; ring

omit [NeZero d] in
/-- **The boxes of a leg are pairwise disjoint** (separated along the axis). [cite: GrimmettPercolation1999, §7.3 p. 172 (A)] -/
theorem disjoint_boxOf (h : IsLeg m L H ax sg n β) {j k : ℕ} (hjk : j < k) (hk : k ≤ n) :
    Disjoint (boxOf L H (β j)) (boxOf L H (β k)) := by
  have hja := h.axis j (by omega); have hka := h.axis k hk
  have hjs := h.sign j (by omega); have hks := h.sign k hk
  have hb := h.b_axis hjk.le hk
  have hkj : (1 : ℤ) ≤ (k : ℤ) - j := by have : j + 1 ≤ k := hjk; omega
  rcases Int.units_eq_one_or sg with hs | hs
  · -- moving up: `β j` lies below `β k`
    refine disjoint_boxOf_of_sep ax ?_
    have h1 := (lo_hi_axis_pos (L := L) (H := H) (hjs.trans hs)).2
    have h2 := (lo_hi_axis_pos (L := L) (H := H) (hks.trans hs)).1
    rw [hja] at h1; rw [hka] at h2
    rw [h1, h2, hb, hs]
    push_cast
    nlinarith
  · refine disjoint_boxOf_of_sep' ax ?_
    have h1 := (lo_hi_axis_neg (L := L) (H := H) (hjs.trans hs)).1
    have h2 := (lo_hi_axis_neg (L := L) (H := H) (hks.trans hs)).2
    rw [hja] at h1; rw [hka] at h2
    rw [h1, h2, hb, hs]
    push_cast
    nlinarith

end IsLeg

/-! ## Turns -/

/-- **A turn off the `n`-th brick of a leg towards the face `x_f = u`**: the child placement `γ`
(the first brick of the side pile) has axis `f ≠ ax`, sign `u`, base centre one step outside that
face (`γ.b f = β_n.b f + u(L+1)`), at longitudinal position `sg(γ.b ax - β_n.b ax) ∈ [m+1, H-m-1]`
and otherwise within `L - m - 1` of `β_n.b` (Grimmett (B)). [cite: GrimmettPercolation1999, §7.3 pp. 172–173 (B)] -/
structure IsTurn (m L H : ℕ) (ax : Fin d) (sg : ℤˣ) (f : Fin d) (u : ℤˣ) (βn γ : BrickPos d) : Prop where
  ne : f ≠ ax
  axis : γ.a = f
  sign : γ.s = u
  face : γ.b f = βn.b f + (u : ℤ) * ((L : ℤ) + 1)
  longit : (m : ℤ) + 1 ≤ (sg : ℤ) * (γ.b ax - βn.b ax) ∧ (sg : ℤ) * (γ.b ax - βn.b ax) ≤ (H : ℤ) - m - 1
  other : ∀ i, i ≠ ax → i ≠ f → |γ.b i - βn.b i| ≤ (L : ℤ) - m - 1

/-- **Steering towards / away from a face** on a window of a leg: the `f`-coordinate of the base
centres is monotone in the direction `u` (`+u`: towards) for the steps `k → k+1`, `k ∈ [k₀, k₁)`
(Grimmett (D): "By judicious choices of the particular subfacets of the tops of the bricks, we may
control such deviations"). [cite: GrimmettPercolation1999, §7.3 p. 173 (D)] -/
def Steered (f : Fin d) (u : ℤ) (k₀ k₁ : ℕ) (β : ℕ → BrickPos d) : Prop :=
  ∀ k, k₀ ≤ k → k < k₁ → 0 ≤ u * ((β (k + 1)).b f - (β k).b f)

omit [NeZero d] in
/-- On a steered window the `f`-coordinate is monotone. [folklore] -/
theorem Steered.mono {f : Fin d} {u : ℤ} {k₀ k₁ : ℕ} {β : ℕ → BrickPos d} (h : Steered f u k₀ k₁ β) {j k : ℕ}
    (hj : k₀ ≤ j) (hjk : j ≤ k) (hk : k ≤ k₁) : 0 ≤ u * ((β k).b f - (β j).b f) := by
  induction k with
  | zero =>
    have : j = 0 := by omega
    subst this; simp
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le hjk with rfl | hlt
    · simp
    · have h1 := ih (by omega) (by omega)
      have h2 := h k (by omega) (by omega)
      have : u * ((β (k + 1)).b f - (β j).b f) = u * ((β (k + 1)).b f - (β k).b f) + u * ((β k).b f - (β j).b f) := by ring
      rw [this]
      exact add_nonneg h2 h1

namespace IsTurn

variable {ax f : Fin d} {sg u : ℤˣ} {n : ℕ} {β : ℕ → BrickPos d} {γ : BrickPos d}

omit [NeZero d] in
/-- **The child leg is disjoint from the parent leg.** If `γ = γ' 0, …, γ' n'` is a leg along `(f, u)`
whose base centres stay within `L - m - 1` of `γ.b ax` along the parent axis, then every `γ' j` is
box-disjoint from every brick of the parent leg, given the same steering and
`P'(H+1) ≥ 2L + H + 2`. [cite: GrimmettPercolation1999, §7.3 pp. 172–173 (B)–(D)] -/
theorem disjoint_boxOf_child_leg {N P' n' : ℕ} {γ' : ℕ → BrickPos d} (hl : IsLeg m L H ax sg N β) (hn : n ≤ N)
    (ht : IsTurn m L H ax sg f u (β n) γ) (hγ0 : γ' 0 = γ) (hcl : IsLeg m L H f u n' γ')
    (hdev : ∀ j ≤ n', |(γ' j).b ax - γ.b ax| ≤ (L : ℤ) - m - 1)
    (hpre : Steered f (u : ℤ) (n - P') n β) (hpost : Steered f (-(u : ℤ)) n (min (n + P') N) β)
    (hP' : 2 * (L : ℤ) + H + 2 ≤ (P' : ℤ) * ((H : ℤ) + 1)) {k : ℕ} (hk : k ≤ N) {j : ℕ} (hj : j ≤ n') :
    Disjoint (boxOf L H (β k)) (boxOf L H (γ' j)) := by
  have hka := hl.axis k hk
  have hja := hcl.axis j hj; have hjs := hcl.sign j hj
  have hjf := hcl.b_axis (Nat.zero_le j) hj
  rw [hγ0] at hjf
  by_cases hnear : n - P' ≤ k ∧ k ≤ n + P'
  · -- near the turn: the child leg is beyond the face, `β k` behind it
    have hbeh : 0 ≤ (u : ℤ) * ((β n).b f - (β k).b f) := by
      rcases le_or_gt k n with hkn | hnk
      · have := hpre.mono hnear.1 hkn le_rfl; linarith
      · have := hpost.mono le_rfl hnk.le (by rw [le_min_iff]; exact ⟨hnear.2, hk⟩); linarith
    have hfa : f ≠ (β k).a := by rw [hka]; exact ht.ne
    obtain ⟨hκlo, hκhi⟩ := lo_hi_of_ne (L := L) (H := H) (β := β k) hfa
    rcases Int.units_eq_one_or u with hu | hu
    · refine disjoint_boxOf_of_sep f ?_
      rw [hκhi, ← hja, (lo_hi_axis_pos (L := L) (H := H) (hjs.trans hu)).1, hja, hjf, ht.face, hu]
      rw [hu] at hbeh; push_cast at hbeh ⊢
      nlinarith
    · refine disjoint_boxOf_of_sep' f ?_
      rw [hκlo, ← hja, (lo_hi_axis_neg (L := L) (H := H) (hjs.trans hu)).2, hja, hjf, ht.face, hu]
      rw [hu] at hbeh; push_cast at hbeh ⊢
      nlinarith
  · -- far from the turn: separated along the parent axis
    rw [not_and_or, not_le, not_le] at hnear
    have hks := hl.sign k hk
    have haxf : ax ≠ (γ' j).a := by rw [hja]; exact Ne.symm ht.ne
    obtain ⟨hγlo, hγhi⟩ := lo_hi_of_ne (L := L) (H := H) (β := γ' j) haxf
    obtain ⟨hlong1, hlong2⟩ := ht.longit
    have hdj := abs_le.1 (hdev j hj)
    rcases hnear with hlt | hgt
    · have hb := hl.b_axis (show k ≤ n by omega) hn
      have hdist : (P' : ℤ) + 1 ≤ (n : ℤ) - k := by omega
      rcases Int.units_eq_one_or sg with hs | hs
      · refine disjoint_boxOf_of_sep ax ?_
        rw [← hka, (lo_hi_axis_pos (L := L) (H := H) (hks.trans hs)).2, hka, hγlo]
        rw [hs] at hb hlong1; push_cast at hb hlong1 ⊢
        nlinarith
      · refine disjoint_boxOf_of_sep' ax ?_
        rw [← hka, (lo_hi_axis_neg (L := L) (H := H) (hks.trans hs)).1, hka, hγhi]
        rw [hs] at hb hlong1; push_cast at hb hlong1 ⊢
        nlinarith
    · have hb := hl.b_axis (show n ≤ k by omega) hk
      have hdist : (P' : ℤ) + 1 ≤ (k : ℤ) - n := by omega
      rcases Int.units_eq_one_or sg with hs | hs
      · refine disjoint_boxOf_of_sep' ax ?_
        rw [← hka, (lo_hi_axis_pos (L := L) (H := H) (hks.trans hs)).1, hka, hγhi]
        rw [hs] at hb hlong2; push_cast at hb hlong2 ⊢
        nlinarith
      · refine disjoint_boxOf_of_sep ax ?_
        rw [← hka, (lo_hi_axis_neg (L := L) (H := H) (hks.trans hs)).2, hka, hγlo]
        rw [hs] at hb hlong2; push_cast at hb hlong2 ⊢
        nlinarith

end IsTurn

end BGNd

end Percolation.Literature

end
