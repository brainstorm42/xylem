import Percolation.Literature.FlatRoute
import Percolation.Util.Linter

/-!
# The flat gait, II: kinematics of a hop

The effect of one hop (side stacking, Grimmett,
*Percolation*, 2nd ed. (1999), §7.3 pp. 172–173 (B), (D)) requested by `hreq`: the new plate has the
face axis and sign, sits exactly `U = L + 1` beyond the face, is displaced by an uncontrolled
`t ∈ [m + 1, H - m - 1]` along the old axis (`isTurn_sStep`), and in every other coordinate by at
most `L'`, forwards along a plane axis (`hop_plane`), upwards / downwards / towards the nominal
height (`hop_z_up`, `hop_z_down`, `hop_z_toward`), and towards `0` elsewhere (`hop_idle`). Also
the algebra of the plane axes (`pl`, `oth`, `plIdx`) and the box of a plate in doubled coordinates.

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §7.3 pp. 172–173, (B), (D).
-/

noncomputable section

namespace Percolation.Literature

open LatticeModels Contour
open scoped Classical

namespace BGNd

variable {d : ℕ}

/-! ## The plane axes -/

section Axes

variable (hd : 3 ≤ d)

/-- `oth` is an involution. [folklore] -/
@[simp] theorem oth_oth (j : Fin 2) : oth (oth j) = j := by
  apply Fin.ext; simp only [oth]; have := j.isLt; omega

/-- `oth j ≠ j`. [folklore] -/
theorem oth_ne (j : Fin 2) : oth j ≠ j := by
  intro h; have := congrArg Fin.val h; simp only [oth] at this; have := j.isLt; omega

/-- The two plane indices. [folklore] -/
theorem oth_eq_iff {j k : Fin 2} : oth j = k ↔ k ≠ j := by
  constructor
  · rintro rfl; exact oth_ne j
  · intro h; apply Fin.ext; simp only [oth]; have := j.isLt; have := k.isLt
    have : k.val ≠ j.val := fun h' => h (Fin.ext h'); omega

/-- The plane axes are injective in the index. [folklore] -/
theorem pl_injective : Function.Injective (pl hd : Fin 2 → Fin d) := by
  intro j k h; unfold pl axOf at h; have := congrArg Fin.val h; simp at this; exact Fin.ext this

/-- The two plane axes differ. [folklore] -/
theorem pl_ne_pl {j k : Fin 2} (h : j ≠ k) : pl hd j ≠ pl hd k := fun h' => h (pl_injective hd h')

/-- A plane axis is not the vertical axis. [folklore] -/
theorem pl_ne_ax0 (j : Fin 2) : pl hd j ≠ ax0 hd := axOf_ne_ax0 hd _

/-- The index of a plane axis. [folklore] -/
@[simp] theorem plIdx_pl (j : Fin 2) : plIdx hd (pl hd j) = j := by
  unfold plIdx
  by_cases h : j = 1
  · subst h; simp
  · rw [if_neg (pl_ne_pl hd h)]
    have := j.isLt; apply Fin.ext; simp; omega

end Axes

/-! ## The requests -/

section Req

variable (hd : 3 ≤ d) (Y : FlatLayout) (e : MDir)

/-- The request along a plane axis: forwards. [folklore] -/
theorem hreq_pl (σ : Fin 2 → ℤˣ) (zmode : Option Bool) (b : Site d) (q : Fin 2) :
    hreq hd Y e σ zmode b (pl hd q) = decide (0 ≤ (σ q : ℤ)) := by
  unfold hreq
  by_cases h : q = 0
  · subst h; simp
  · have h1 : q = 1 := by have := q.isLt; apply Fin.ext; have : q.val ≠ 0 := fun h' => h (Fin.ext h'); simp; omega
    subst h1
    rw [if_neg (pl_ne_pl hd (by decide)), if_pos rfl]

/-- The request of the height: as prescribed. [folklore] -/
theorem hreq_ax0_some (σ : Fin 2 → ℤˣ) (up : Bool) (b : Site d) : hreq hd Y e σ (some up) b (ax0 hd) = up := by
  unfold hreq
  rw [if_neg (pl_ne_ax0 hd 0).symm, if_neg (pl_ne_ax0 hd 1).symm, if_pos rfl]

/-- The request of the height: towards the nominal height. [folklore] -/
theorem hreq_ax0_none (σ : Fin 2 → ℤˣ) (b : Site d) : hreq hd Y e σ none b (ax0 hd) = toward (fun _ => zN Y e) b (ax0 hd) := by
  unfold hreq toward
  rw [if_neg (pl_ne_ax0 hd 0).symm, if_neg (pl_ne_ax0 hd 1).symm, if_pos rfl]

/-- The request elsewhere: towards `0`. [folklore] -/
theorem hreq_idle (σ : Fin 2 → ℤˣ) (zmode : Option Bool) (b : Site d) {i : Fin d} (h0 : i ≠ pl hd 0) (h1 : i ≠ pl hd 1) (hz : i ≠ ax0 hd) :
    hreq hd Y e σ zmode b i = toward 0 b i := by
  unfold hreq toward; rw [if_neg h0, if_neg h1, if_neg hz]; rfl

end Req

/-! ## The kinematics of a hop -/

section Hop

variable [NeZero d] (hd : 3 ≤ d) (Y : FlatLayout) (hL : Y.m + 1 ≤ Y.L) (hH : 2 * Y.m + 2 ≤ Y.H) (e : MDir)

omit [NeZero d] in
/-- The layout's `U` and `L'` in the kinematic lemmas. [folklore] -/
theorem U_eq : Y.U = (Y.L : ℤ) + 1 := rfl
omit [NeZero d] in
/-- The layout's `U` and `L'` in the kinematic lemmas. [folklore] -/
theorem Lp_eq : Y.Lp = (Y.L : ℤ) - Y.m - 1 := rfl

/-- **A hop is a turn**: face, axis, sign, exact displacement `U` through the face, drift along the
old axis, play `L'` elsewhere. [cite: GrimmettPercolation1999, §7.3 pp. 172–173 (B)] -/
theorem hop_isTurn {r : BrickRec d} (hg : GoodRec Y.m Y.L Y.H r) {j : Fin d} (hj : j ≠ r.1.a) (u : ℤˣ) (σ : Fin 2 → ℤˣ)
    (zmode : Option Bool) :
    IsTurn Y.m Y.L Y.H r.1.a r.1.s j u r.1 (sStep hL hH r j u (hreq hd Y e σ zmode r.1.b)) :=
  isTurn_sStep hL hH hg hj u _

/-- **A plane coordinate other than the old and new axes moves forwards**, by at most `L'`.
[cite: GrimmettPercolation1999, §7.3 p. 173 (D)] -/
theorem hop_plane {r : BrickRec d} (hg : GoodRec Y.m Y.L Y.H r) {j : Fin d} (hj : j ≠ r.1.a) (u : ℤˣ) (σ : Fin 2 → ℤˣ)
    (zmode : Option Bool) {q : Fin 2} (hq1 : pl hd q ≠ r.1.a) (hq2 : pl hd q ≠ j) :
    0 ≤ (σ q : ℤ) * ((sStep hL hH r j u (hreq hd Y e σ zmode r.1.b)).b (pl hd q) - r.1.b (pl hd q)) ∧
      (σ q : ℤ) * ((sStep hL hH r j u (hreq hd Y e σ zmode r.1.b)).b (pl hd q) - r.1.b (pl hd q)) ≤ Y.Lp := by
  have hw : (σ q : ℤ) = 1 ∨ (σ q : ℤ) = -1 := by rcases Int.units_eq_one_or (σ q) with h | h <;> simp [h]
  exact forced_nonneg_side hL hH hg hj u hq1 hq2 hw (hreq_pl hd Y e σ zmode r.1.b q)

/-- **The height, when requested up**, rises by at most `L'`. [folklore] -/
theorem hop_z_up {r : BrickRec d} (hg : GoodRec Y.m Y.L Y.H r) {j : Fin d} (hj : j ≠ r.1.a) (u : ℤˣ) (σ : Fin 2 → ℤˣ)
    (h1 : ax0 hd ≠ r.1.a) (h2 : ax0 hd ≠ j) :
    0 ≤ (sStep hL hH r j u (hreq hd Y e σ (some true) r.1.b)).b (ax0 hd) - r.1.b (ax0 hd) ∧
      (sStep hL hH r j u (hreq hd Y e σ (some true) r.1.b)).b (ax0 hd) - r.1.b (ax0 hd) ≤ Y.Lp := by
  have hsg : hreq hd Y e σ (some true) r.1.b (ax0 hd) = decide (0 ≤ (1 : ℤ)) := by rw [hreq_ax0_some]; decide
  have := forced_nonneg_side hL hH hg hj u h1 h2 (w := 1) (Or.inl rfl) hsg
  rw [Lp_eq]; simpa using this

/-- **The height, when requested down**, sinks by at most `L'`. [folklore] -/
theorem hop_z_down {r : BrickRec d} (hg : GoodRec Y.m Y.L Y.H r) {j : Fin d} (hj : j ≠ r.1.a) (u : ℤˣ) (σ : Fin 2 → ℤˣ)
    (h1 : ax0 hd ≠ r.1.a) (h2 : ax0 hd ≠ j) :
    0 ≤ r.1.b (ax0 hd) - (sStep hL hH r j u (hreq hd Y e σ (some false) r.1.b)).b (ax0 hd) ∧
      r.1.b (ax0 hd) - (sStep hL hH r j u (hreq hd Y e σ (some false) r.1.b)).b (ax0 hd) ≤ Y.Lp := by
  have hsg : hreq hd Y e σ (some false) r.1.b (ax0 hd) = decide (0 ≤ (-1 : ℤ)) := by rw [hreq_ax0_some]; decide
  have := forced_nonneg_side hL hH hg hj u h1 h2 (w := -1) (Or.inr rfl) hsg
  rw [Lp_eq]; constructor <;> linarith [this.1, this.2]

/-- **The height, when requested towards the nominal height**, deviates by at most `max(previous, L')`. [folklore] -/
theorem hop_z_toward {r : BrickRec d} (hg : GoodRec Y.m Y.L Y.H r) {j : Fin d} (hj : j ≠ r.1.a) (u : ℤˣ) (σ : Fin 2 → ℤˣ)
    (h1 : ax0 hd ≠ r.1.a) (h2 : ax0 hd ≠ j) :
    |(sStep hL hH r j u (hreq hd Y e σ none r.1.b)).b (ax0 hd) - zN Y e| ≤ max |r.1.b (ax0 hd) - zN Y e| Y.Lp := by
  rw [Lp_eq]; exact abs_sub_le_of_toward_side hL hH hg hj u (nom := fun _ => zN Y e) h1 h2 (hreq_ax0_none hd Y e σ r.1.b)

/-- **An idle coordinate stays within `max(previous, L')` of `0`.** [folklore] -/
theorem hop_idle {r : BrickRec d} (hg : GoodRec Y.m Y.L Y.H r) {j : Fin d} (hj : j ≠ r.1.a) (u : ℤˣ) (σ : Fin 2 → ℤˣ)
    (zmode : Option Bool) {i : Fin d} (hi1 : i ≠ r.1.a) (hi2 : i ≠ j) (h0 : i ≠ pl hd 0) (h1 : i ≠ pl hd 1) (hz : i ≠ ax0 hd) :
    |(sStep hL hH r j u (hreq hd Y e σ zmode r.1.b)).b i| ≤ max |r.1.b i| Y.Lp := by
  have := abs_sub_le_of_toward_side hL hH hg hj u (nom := 0) hi1 hi2 (hreq_idle hd Y e σ zmode r.1.b h0 h1 hz)
  rw [Lp_eq]; simpa only [Pi.zero_apply, sub_zero] using this

end Hop

end BGNd

end Percolation.Literature

end
