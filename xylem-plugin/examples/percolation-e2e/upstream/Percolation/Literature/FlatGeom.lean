import Percolation.Literature.FlatStep
import Percolation.Util.Linter

/-!
# The flat gait, VIII: layout arithmetic and oriented separation of plates

Two toolkits for the geometry of the flat gait
(Grimmett, *Percolation*, 2nd ed. (1999), §7.3, case `H < L`). (1) The arithmetic of admissible
layouts (`FlatLayout.OK.facts`: `U = L + 1 = L' + m + 2`, `H + 1 ≤ U`, …) and the diagonal
coordinates in terms of the oriented plane coordinates (`upar_dsg`, `Uc_lat_dsg`). (2) **Oriented
separation**: the ends of the coordinate intervals of a support box read along an orientation
`w = ±1` (`olo`, `ohi`, from `lo`, `hi` of `GaitKinematics.lean`; `olo_ohi_trans`, `olo_ohi_fwd`,
`olo_ohi_bwd`), the criterion
`ohi β i < olo β' i → Disjoint` (`osep`), and its six instances by the kinds of the two plates in
that coordinate — transverse (wide, `±U`), axis forwards (thin, `(0, H+1]`), axis backwards —
in terms of the oriented centres (`sep_ww`, `sep_wf`, `sep_ff`, `sep_fw`, `sep_bw`, `sep_bf`, `sep_wb`, `sep_fb`), and the
coarse criterion `sep_any` (centres more than `2U` apart along any coordinate).

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §7.3 pp. 172–174.
-/

noncomputable section

namespace Percolation.Literature

open LatticeModels Contour
open scoped Classical

namespace BGNd

variable {d : ℕ}

/-! ## Layout arithmetic -/

namespace FlatLayout.OK

variable {Y : FlatLayout} (hY : Y.OK)
include hY

/-- **The arithmetic of an admissible layout.** [folklore] -/
theorem facts : 0 < Y.U ∧ Y.U = (Y.L : ℤ) + 1 ∧ Y.Lp = (Y.L : ℤ) - Y.m - 1 ∧ 0 ≤ Y.Lp ∧ Y.U = Y.Lp + Y.m + 2 ∧
    (Y.H : ℤ) + 1 ≤ Y.U ∧ 2 * (Y.m : ℤ) + 2 ≤ Y.H ∧ 8 * ((Y.H : ℤ) + 1) ≤ Y.U ∧ (0 : ℤ) ≤ Y.m := by
  have hL := hY.hL; have hH := hY.hH; have hf := hY.flat
  have hL' : (Y.m : ℤ) + 1 ≤ Y.L := by exact_mod_cast hL
  have hH' : 2 * (Y.m : ℤ) + 2 ≤ Y.H := by exact_mod_cast hH
  unfold FlatLayout.U FlatLayout.Lp at *
  refine ⟨by positivity, rfl, rfl, by linarith, by ring, by linarith, hH', hf, by positivity⟩

end FlatLayout.OK

/-! ## Diagonal coordinates -/

section Diag

variable (hd : 3 ≤ d)

/-- **The forward diagonal coordinate is the oriented sum**: `s · u_∥ = σ₀ x₀ + σ₁ x₁`. [folklore] -/
theorem upar_dsg (e : MDir) (b : Site d) : (sgOf e : ℤ) * Uc hd e.1 b = upar hd (dsg e) b := by
  unfold upar ox Uc dsg
  have hs : (sgOf e : ℤ) * (sgOf e : ℤ) = 1 := by rcases Int.units_eq_one_or (sgOf e) with h | h <;> simp [h]
  rcases Fin.exists_fin_two.1 ⟨e.1, rfl⟩ with h | h <;> simp [h] <;> ring

/-- **The lateral diagonal coordinate is the oriented difference**: `u_⊥ = s (σ₀ x₀ - σ₁ x₁)`. [folklore] -/
theorem Uc_lat_dsg (e : MDir) (b : Site d) : Uc hd (latDir e true).1 b = (sgOf e : ℤ) * (ox hd (dsg e) 0 b - ox hd (dsg e) 1 b) := by
  unfold ox Uc dsg latDir
  have hs : (sgOf e : ℤ) * (sgOf e : ℤ) = 1 := by rcases Int.units_eq_one_or (sgOf e) with h | h <;> simp [h]
  rcases Fin.exists_fin_two.1 ⟨e.1, rfl⟩ with h | h <;> simp [h]
  · linear_combination (-b (pl hd 0) + b (pl hd 1)) * hs
  · linear_combination (-b (pl hd 1) - b (pl hd 0)) * hs

end Diag

/-! ## Oriented separation -/

section OSep

variable {L H : ℕ}

/-- The lower end of the `i`-th interval of the box of `β`, read along the orientation `w`. [folklore] -/
def olo (L H : ℕ) (w : ℤˣ) (β : BrickPos d) (i : Fin d) : ℤ := if w = 1 then lo L H β i else -hi L H β i

/-- The upper end of the `i`-th interval of the box of `β`, read along the orientation `w`. [folklore] -/
def ohi (L H : ℕ) (w : ℤˣ) (β : BrickPos d) (i : Fin d) : ℤ := if w = 1 then hi L H β i else -lo L H β i

/-- **Oriented separation**: if, along some coordinate read along `w`, the box of `β` ends before the
box of `β'` begins, the boxes are disjoint. [folklore] -/
theorem osep [NeZero d] {β β' : BrickPos d} (w : ℤˣ) (i : Fin d) (h : ohi L H w β i < olo L H w β' i) :
    Disjoint (boxOf L H β) (boxOf L H β') := by
  unfold ohi olo at h
  rcases Int.units_eq_one_or w with rfl | rfl
  · simp only [if_true] at h
    exact disjoint_boxOf_of_sep i h
  · have : ((-1 : ℤˣ) = 1) = False := by decide
    simp only [this, if_false] at h
    exact disjoint_boxOf_of_sep' i (by linarith)

/-- **The oriented interval of a transverse coordinate**: `[2c - 2L - 2, 2c + 2L + 2]`, `c = w b_i`. [folklore] -/
theorem olo_ohi_trans (w : ℤˣ) {β : BrickPos d} {i : Fin d} (hi : i ≠ β.a) :
    olo L H w β i = 2 * ((w : ℤ) * β.b i) - 2 * L - 2 ∧ ohi L H w β i = 2 * ((w : ℤ) * β.b i) + 2 * L + 2 := by
  obtain ⟨h1, h2⟩ := lo_hi_of_ne (L := L) (H := H) hi
  unfold olo ohi
  rcases Int.units_eq_one_or w with rfl | rfl
  · simp [h1, h2]
  · have : ((-1 : ℤˣ) = 1) = False := by decide
    simp only [this, if_false, h1, h2, Units.val_neg, Units.val_one]; constructor <;> ring

/-- **The oriented interval of the axis coordinate of a plate pointing forwards** (`β.s = w`):
`[2c + 1, 2c + 2H + 2]`. [folklore] -/
theorem olo_ohi_fwd (w : ℤˣ) {β : BrickPos d} (hs : β.s = w) :
    olo L H w β β.a = 2 * ((w : ℤ) * β.b β.a) + 1 ∧ ohi L H w β β.a = 2 * ((w : ℤ) * β.b β.a) + 2 * H + 2 := by
  unfold olo ohi
  rcases Int.units_eq_one_or w with rfl | rfl
  · obtain ⟨h1, h2⟩ := lo_hi_axis_pos (L := L) (H := H) hs
    simp [h1, h2]
  · obtain ⟨h1, h2⟩ := lo_hi_axis_neg (L := L) (H := H) hs
    have : ((-1 : ℤˣ) = 1) = False := by decide
    simp only [this, if_false, h1, h2, Units.val_neg, Units.val_one]; constructor <;> ring

/-- **The oriented interval of the axis coordinate of a plate pointing backwards** (`β.s = -w`):
`[2c - 2H - 2, 2c - 1]`. [folklore] -/
theorem olo_ohi_bwd (w : ℤˣ) {β : BrickPos d} (hs : β.s = -w) :
    olo L H w β β.a = 2 * ((w : ℤ) * β.b β.a) - 2 * H - 2 ∧ ohi L H w β β.a = 2 * ((w : ℤ) * β.b β.a) - 1 := by
  unfold olo ohi
  rcases Int.units_eq_one_or w with rfl | rfl
  · obtain ⟨h1, h2⟩ := lo_hi_axis_neg (L := L) (H := H) hs
    simp [h1, h2]
  · rw [neg_neg] at hs
    obtain ⟨h1, h2⟩ := lo_hi_axis_pos (L := L) (H := H) hs
    have : ((-1 : ℤˣ) = 1) = False := by decide
    simp only [this, if_false, h1, h2, Units.val_neg, Units.val_one]; constructor <;> ring

variable [NeZero d]

/-- **Wide behind wide**: two plates transverse in coordinate `i`, oriented centres more than
`2U = 2L + 2` apart. [folklore] -/
theorem sep_ww (w : ℤˣ) (i : Fin d) {β β' : BrickPos d} (hi : i ≠ β.a) (hi' : i ≠ β'.a)
    (h : 2 * (L : ℤ) + 2 < (w : ℤ) * β'.b i - (w : ℤ) * β.b i) : Disjoint (boxOf L H β) (boxOf L H β') := by
  apply osep w i; rw [(olo_ohi_trans w hi).2, (olo_ohi_trans w hi').1]; linarith

/-- **Wide behind thin-forwards**: `β` transverse, `β'` with axis `i` pointing along `w`, centres at
least `U = L + 1` apart. [folklore] -/
theorem sep_wf (w : ℤˣ) {β β' : BrickPos d} (hi : β'.a ≠ β.a) (hs' : β'.s = w)
    (h : (L : ℤ) + 1 ≤ (w : ℤ) * β'.b β'.a - (w : ℤ) * β.b β'.a) : Disjoint (boxOf L H β) (boxOf L H β') := by
  apply osep w β'.a; rw [(olo_ohi_trans w hi).2, (olo_ohi_fwd w hs').1]; linarith

/-- **Thin-forwards behind thin-forwards**: both with axis `i` along `w`, centres at least `H + 1`
apart. [folklore] -/
theorem sep_ff (w : ℤˣ) {β β' : BrickPos d} (ha : β'.a = β.a) (hs : β.s = w) (hs' : β'.s = w)
    (h : (H : ℤ) + 1 ≤ (w : ℤ) * β'.b β'.a - (w : ℤ) * β.b β'.a) : Disjoint (boxOf L H β) (boxOf L H β') := by
  apply osep w β'.a
  have := (olo_ohi_fwd (L := L) (H := H) w hs).2; rw [← ha] at this
  rw [this, (olo_ohi_fwd w hs').1]; linarith

/-- **Thin-forwards behind wide**: `β` with axis `i` along `w`, `β'` transverse, centres more than
`U + H + 1` apart. [folklore] -/
theorem sep_fw (w : ℤˣ) {β β' : BrickPos d} (hi' : β.a ≠ β'.a) (hs : β.s = w)
    (h : (L : ℤ) + H + 2 < (w : ℤ) * β'.b β.a - (w : ℤ) * β.b β.a) : Disjoint (boxOf L H β) (boxOf L H β') := by
  apply osep w β.a; rw [(olo_ohi_fwd w hs).2, (olo_ohi_trans w hi').1]; linarith

/-- **Thin-backwards behind wide**: `β` with axis `i` against `w`, `β'` transverse, centres at least
`U` apart. [folklore] -/
theorem sep_bw (w : ℤˣ) {β β' : BrickPos d} (hi' : β.a ≠ β'.a) (hs : β.s = -w)
    (h : (L : ℤ) + 1 ≤ (w : ℤ) * β'.b β.a - (w : ℤ) * β.b β.a) : Disjoint (boxOf L H β) (boxOf L H β') := by
  apply osep w β.a; rw [(olo_ohi_bwd w hs).2, (olo_ohi_trans w hi').1]; linarith

/-- **Thin-backwards behind thin-forwards**: same axis, `β` against `w`, `β'` along `w`, the centre
of `β'` not behind that of `β`. [folklore] -/
theorem sep_bf (w : ℤˣ) {β β' : BrickPos d} (ha : β'.a = β.a) (hs : β.s = -w) (hs' : β'.s = w)
    (h : (w : ℤ) * β.b β'.a ≤ (w : ℤ) * β'.b β'.a) : Disjoint (boxOf L H β) (boxOf L H β') := by
  apply osep w β'.a
  have := (olo_ohi_bwd (L := L) (H := H) w hs).2; rw [← ha] at this
  rw [this, (olo_ohi_fwd w hs').1]; linarith

/-- **Wide behind thin-backwards**: `β` transverse, `β'` with axis `i` against `w`, centres more than
`U + H + 1` apart. [folklore] -/
theorem sep_wb (w : ℤˣ) {β β' : BrickPos d} (hi : β'.a ≠ β.a) (hs' : β'.s = -w)
    (h : (L : ℤ) + H + 2 < (w : ℤ) * β'.b β'.a - (w : ℤ) * β.b β'.a) : Disjoint (boxOf L H β) (boxOf L H β') := by
  apply osep w β'.a; rw [(olo_ohi_trans w hi).2, (olo_ohi_bwd w hs').1]; linarith

/-- **Thin-forwards behind thin-backwards** (same axis, opposite signs, facing each other): centres
more than `2H + 2` apart. [folklore] -/
theorem sep_fb (w : ℤˣ) {β β' : BrickPos d} (ha : β'.a = β.a) (hs : β.s = w) (hs' : β'.s = -w)
    (h : 2 * (H : ℤ) + 2 < (w : ℤ) * β'.b β'.a - (w : ℤ) * β.b β'.a) : Disjoint (boxOf L H β) (boxOf L H β') := by
  apply osep w β'.a
  have := (olo_ohi_fwd (L := L) (H := H) w hs).2; rw [← ha] at this
  rw [this, (olo_ohi_bwd w hs').1]; linarith

/-- **Any two plates whose oriented centres along some coordinate differ by more than `2U`** are
disjoint, whatever their kinds there (since `U ≥ H + 1`). [folklore] -/
theorem sep_any (hUH : (H : ℤ) + 1 ≤ (L : ℤ) + 1) (w : ℤˣ) (i : Fin d) {β β' : BrickPos d}
    (h : 2 * (L : ℤ) + 2 < (w : ℤ) * β'.b i - (w : ℤ) * β.b i) : Disjoint (boxOf L H β) (boxOf L H β') := by
  apply osep w i
  have hH0 : (0 : ℤ) ≤ H := by positivity
  -- upper end of `β` is at most `2c + 2L + 2`, lower end of `β'` at least `2c' - 2L - 2`
  have h1 : ohi L H w β i ≤ 2 * ((w : ℤ) * β.b i) + 2 * L + 2 := by
    by_cases hi : i = β.a
    · subst hi
      rcases Int.units_eq_one_or β.s with hs | hs <;> [skip; skip]
      · by_cases hw : w = 1
        · subst hw; rw [(olo_ohi_fwd 1 hs).2]; push_cast; linarith
        · have hw' : w = -1 := (Int.units_eq_one_or w).resolve_left hw
          subst hw'; rw [(olo_ohi_bwd (-1) (by rw [hs]; decide)).2]; linarith
      · by_cases hw : w = 1
        · subst hw; rw [(olo_ohi_bwd 1 (by rw [hs])).2]; linarith
        · have hw' : w = -1 := (Int.units_eq_one_or w).resolve_left hw
          subst hw'; rw [(olo_ohi_fwd (-1) hs).2]; push_cast; linarith
    · rw [(olo_ohi_trans w hi).2]
  have h2 : 2 * ((w : ℤ) * β'.b i) - 2 * L - 2 ≤ olo L H w β' i := by
    by_cases hi : i = β'.a
    · subst hi
      rcases Int.units_eq_one_or β'.s with hs | hs
      · by_cases hw : w = 1
        · subst hw; rw [(olo_ohi_fwd 1 hs).1]; linarith
        · have hw' : w = -1 := (Int.units_eq_one_or w).resolve_left hw
          subst hw'; rw [(olo_ohi_bwd (-1) (by rw [hs]; decide)).1]; push_cast; linarith
      · by_cases hw : w = 1
        · subst hw; rw [(olo_ohi_bwd 1 (by rw [hs])).1]; push_cast; linarith
        · have hw' : w = -1 := (Int.units_eq_one_or w).resolve_left hw
          subst hw'; rw [(olo_ohi_fwd (-1) hs).1]; linarith
    · rw [(olo_ohi_trans w hi).1]
  linarith

end OSep

end BGNd

end Percolation.Literature

end
