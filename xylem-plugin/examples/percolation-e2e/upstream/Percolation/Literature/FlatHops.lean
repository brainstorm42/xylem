import Percolation.Literature.FlatKin
import Percolation.Util.Linter

/-!
# The flat gait, III: the four kinds of steps

The plan of the flat gait (Grimmett, *Percolation*, 2nd
ed. (1999), §7.3 pp. 172–174 (B)–(D), case `H < L`) uses three kinds of hops, whose kinematic
content we package as relations between the old and the new plate: a **diagonal hop** `DHop`
(plane plate to plane plate of the other plane axis: exact `U` through the face, forward drift
along the old axis, height towards the nominal height or upwards, idle coordinates towards `0`),
an **up/down hop** `VHop` (plane plate to horizontal plate: exact `±U` in height, forward drift
along the old axis, the other plane coordinate pushed along a prescribed sign), and a **landing
hop** `PHop` (horizontal plate to plane plate: exact `U` through the face, vertical drift along the
old sign, the other plane coordinate pushed along a prescribed sign), and a **top stacking**
`THop` (same axis and sign, exact `H + 1` along the axis, the other plane coordinate pushed along
a prescribed sign, height towards the nominal height; Grimmett's (A)). Each is derived from
`sStep` / `tStep` with the requests `hreq` (`dHop_sStep`, `vHop_sStep`, `pHop_sStep`, `tHop_tStep`).

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §7.3 pp. 172–173, (B), (D).
-/

noncomputable section

namespace Percolation.Literature

open LatticeModels Contour
open scoped Classical

namespace BGNd

variable {d : ℕ}

section Hops

variable (hd : 3 ≤ d) (Y : FlatLayout) (e : MDir)

/-- An idle coordinate: neither a plane axis nor the vertical axis. [folklore] -/
def Idle (i : Fin d) : Prop := i ≠ pl hd 0 ∧ i ≠ pl hd 1 ∧ i ≠ ax0 hd

/-- **A diagonal hop** of signs `σ` into the plane axis `q`, with height mode `zmode`. [cite: GrimmettPercolation1999, §7.3 pp. 172–173 (B), (D)] -/
structure DHop (σ : Fin 2 → ℤˣ) (zmode : Option Bool) (q : Fin 2) (β β' : BrickPos d) : Prop where
  srcAxis : β.a = pl hd (oth q)
  srcSign : β.s = σ (oth q)
  axis : β'.a = pl hd q
  sign : β'.s = σ q
  face : β'.b (pl hd q) = β.b (pl hd q) + (σ q : ℤ) * Y.U
  drift : (Y.m : ℤ) + 1 ≤ (σ (oth q) : ℤ) * (β'.b (pl hd (oth q)) - β.b (pl hd (oth q))) ∧
    (σ (oth q) : ℤ) * (β'.b (pl hd (oth q)) - β.b (pl hd (oth q))) ≤ (Y.H : ℤ) - Y.m - 1
  zt : zmode = none → |β'.b (ax0 hd) - zN Y e| ≤ max |β.b (ax0 hd) - zN Y e| Y.Lp
  zup : zmode = some true → 0 ≤ β'.b (ax0 hd) - β.b (ax0 hd) ∧ β'.b (ax0 hd) - β.b (ax0 hd) ≤ Y.Lp
  zdn : zmode = some false → 0 ≤ β.b (ax0 hd) - β'.b (ax0 hd) ∧ β.b (ax0 hd) - β'.b (ax0 hd) ≤ Y.Lp
  idle : ∀ i, Idle hd i → |β'.b i| ≤ max |β.b i| Y.Lp

/-- **An up / down hop** (`u = ±1`) off a plane plate of axis `q`, the other plane coordinate
pushed along `ρ`. [cite: GrimmettPercolation1999, §7.3 pp. 172–173 (B), (D)] -/
structure VHop (ρ : ℤˣ) (u : ℤˣ) (q : Fin 2) (β β' : BrickPos d) : Prop where
  srcAxis : β.a = pl hd q
  axis : β'.a = ax0 hd
  sign : β'.s = u
  face : β'.b (ax0 hd) = β.b (ax0 hd) + (u : ℤ) * Y.U
  drift : (Y.m : ℤ) + 1 ≤ (β.s : ℤ) * (β'.b (pl hd q) - β.b (pl hd q)) ∧ (β.s : ℤ) * (β'.b (pl hd q) - β.b (pl hd q)) ≤ (Y.H : ℤ) - Y.m - 1
  push : 0 ≤ (ρ : ℤ) * (β'.b (pl hd (oth q)) - β.b (pl hd (oth q))) ∧ (ρ : ℤ) * (β'.b (pl hd (oth q)) - β.b (pl hd (oth q))) ≤ Y.Lp
  idle : ∀ i, Idle hd i → |β'.b i| ≤ max |β.b i| Y.Lp

/-- **A landing hop** off a horizontal plate into the plane axis `q` with sign `w`, the other plane
coordinate pushed along `ρ`. [cite: GrimmettPercolation1999, §7.3 pp. 172–173 (B), (D)] -/
structure PHop (ρ : ℤˣ) (w : ℤˣ) (q : Fin 2) (β β' : BrickPos d) : Prop where
  srcAxis : β.a = ax0 hd
  axis : β'.a = pl hd q
  sign : β'.s = w
  face : β'.b (pl hd q) = β.b (pl hd q) + (w : ℤ) * Y.U
  drift : (Y.m : ℤ) + 1 ≤ (β.s : ℤ) * (β'.b (ax0 hd) - β.b (ax0 hd)) ∧ (β.s : ℤ) * (β'.b (ax0 hd) - β.b (ax0 hd)) ≤ (Y.H : ℤ) - Y.m - 1
  push : 0 ≤ (ρ : ℤ) * (β'.b (pl hd (oth q)) - β.b (pl hd (oth q))) ∧ (ρ : ℤ) * (β'.b (pl hd (oth q)) - β.b (pl hd (oth q))) ≤ Y.Lp
  idle : ∀ i, Idle hd i → |β'.b i| ≤ max |β.b i| Y.Lp

/-- **A top stacking** off a plane plate of axis `p`, the other plane coordinate pushed along
`ρ`, the height towards the nominal height. [cite: GrimmettPercolation1999, §7.3 p. 172 (A), p. 173 (D)] -/
structure THop (ρ : ℤˣ) (p : Fin 2) (β β' : BrickPos d) : Prop where
  srcAxis : β.a = pl hd p
  axis : β'.a = pl hd p
  sign : β'.s = β.s
  face : β'.b (pl hd p) = β.b (pl hd p) + (β.s : ℤ) * ((Y.H : ℤ) + 1)
  push : 0 ≤ (ρ : ℤ) * (β'.b (pl hd (oth p)) - β.b (pl hd (oth p))) ∧ (ρ : ℤ) * (β'.b (pl hd (oth p)) - β.b (pl hd (oth p))) ≤ Y.Lp
  zt : |β'.b (ax0 hd) - zN Y e| ≤ max |β.b (ax0 hd) - zN Y e| Y.Lp
  idle : ∀ i, Idle hd i → |β'.b i| ≤ max |β.b i| Y.Lp

end Hops

/-! ## Deriving the hop facts from `sStep` and `tStep` -/

section Derive

variable [NeZero d] (hd : 3 ≤ d) (Y : FlatLayout) (hL : Y.m + 1 ≤ Y.L) (hH : 2 * Y.m + 2 ≤ Y.H) (e : MDir)

/-- **The diagonal hop requested by the plan is a diagonal hop.** [cite: GrimmettPercolation1999, §7.3 pp. 172–173 (B), (D)] -/
theorem dHop_sStep {r : BrickRec d} (hg : GoodRec Y.m Y.L Y.H r) (σ : Fin 2 → ℤˣ) (zmode : Option Bool)
    {q : Fin 2} (ha : r.1.a = pl hd (oth q)) (hs : r.1.s = σ (oth q)) :
    DHop hd Y e σ zmode q r.1 (sStep hL hH r (pl hd q) (σ q) (hreq hd Y e σ zmode r.1.b)) := by
  have hj : pl hd q ≠ r.1.a := by rw [ha]; exact pl_ne_pl hd (oth_ne q).symm
  have hT := hop_isTurn hd Y hL hH e hg hj (σ q) σ zmode
  have h0a : ax0 hd ≠ r.1.a := by rw [ha]; exact (pl_ne_ax0 hd _).symm
  have h0j : ax0 hd ≠ pl hd q := (pl_ne_ax0 hd _).symm
  refine ⟨ha, hs, hT.axis, hT.sign, by rw [hT.face, U_eq], ?_, ?_, ?_, ?_, ?_⟩
  · have := hT.longit; rw [ha, hs] at this; exact this
  · intro hz; subst hz; exact hop_z_toward hd Y hL hH e hg hj (σ q) σ h0a h0j
  · intro hz; subst hz; exact hop_z_up hd Y hL hH e hg hj (σ q) σ h0a h0j
  · intro hz; subst hz; exact hop_z_down hd Y hL hH e hg hj (σ q) σ h0a h0j
  · intro i ⟨hi0, hi1, hiz⟩
    have hia : i ≠ r.1.a := by rw [ha]; rcases Fin.exists_fin_two.1 ⟨oth q, rfl⟩ with h | h <;> rw [h] <;> assumption
    have hij : i ≠ pl hd q := by rcases Fin.exists_fin_two.1 ⟨q, rfl⟩ with h | h <;> rw [h] <;> assumption
    exact hop_idle hd Y hL hH e hg hj (σ q) σ zmode hia hij hi0 hi1 hiz

/-- **The up / down hop requested by the plan is an up / down hop.** [cite: GrimmettPercolation1999, §7.3 pp. 172–173 (B), (D)] -/
theorem vHop_sStep {r : BrickRec d} (hg : GoodRec Y.m Y.L Y.H r) (σ : Fin 2 → ℤˣ) (zmode : Option Bool) (u : ℤˣ) {q : Fin 2}
    (ha : r.1.a = pl hd q) :
    VHop hd Y (σ (oth q)) u q r.1 (sStep hL hH r (ax0 hd) u (hreq hd Y e σ zmode r.1.b)) := by
  have hj : ax0 hd ≠ r.1.a := by rw [ha]; exact (pl_ne_ax0 hd _).symm
  have hT := hop_isTurn hd Y hL hH e hg hj u σ zmode
  refine ⟨ha, hT.axis, hT.sign, by rw [hT.face, U_eq], ?_, ?_, ?_⟩
  · have := hT.longit; rw [ha] at this; exact this
  · have h1 : pl hd (oth q) ≠ r.1.a := by rw [ha]; exact pl_ne_pl hd (oth_ne q)
    exact hop_plane hd Y hL hH e hg hj u σ zmode h1 (pl_ne_ax0 hd _)
  · intro i ⟨hi0, hi1, hiz⟩
    have hia : i ≠ r.1.a := by rw [ha]; rcases Fin.exists_fin_two.1 ⟨q, rfl⟩ with h | h <;> rw [h] <;> assumption
    exact hop_idle hd Y hL hH e hg hj u σ zmode hia hiz hi0 hi1 hiz

/-- **The landing hop requested by the plan is a landing hop.** [cite: GrimmettPercolation1999, §7.3 pp. 172–173 (B), (D)] -/
theorem pHop_sStep {r : BrickRec d} (hg : GoodRec Y.m Y.L Y.H r) (σ : Fin 2 → ℤˣ) (zmode : Option Bool) (q : Fin 2) (w : ℤˣ)
    (ha : r.1.a = ax0 hd) :
    PHop hd Y (σ (oth q)) w q r.1 (sStep hL hH r (pl hd q) w (hreq hd Y e σ zmode r.1.b)) := by
  have hj : pl hd q ≠ r.1.a := by rw [ha]; exact pl_ne_ax0 hd _
  have hT := hop_isTurn hd Y hL hH e hg hj w σ zmode
  refine ⟨ha, hT.axis, hT.sign, by rw [hT.face, U_eq], ?_, ?_, ?_⟩
  · have := hT.longit; rw [ha] at this; exact this
  · have h1 : pl hd (oth q) ≠ r.1.a := by rw [ha]; exact pl_ne_ax0 hd _
    exact hop_plane hd Y hL hH e hg hj w σ zmode h1 (pl_ne_pl hd (oth_ne q))
  · intro i ⟨hi0, hi1, hiz⟩
    have hia : i ≠ r.1.a := by rw [ha]; exact hiz
    have hij : i ≠ pl hd q := by rcases Fin.exists_fin_two.1 ⟨q, rfl⟩ with h | h <;> rw [h] <;> assumption
    exact hop_idle hd Y hL hH e hg hj w σ zmode hia hij hi0 hi1 hiz

/-- **The top stacking requested by the plan is a top stacking.** [cite: GrimmettPercolation1999, §7.3 p. 172 (A), p. 173 (D)] -/
theorem tHop_tStep {r : BrickRec d} (hg : GoodRec Y.m Y.L Y.H r) (σ : Fin 2 → ℤˣ) {p : Fin 2} (ha : r.1.a = pl hd p) :
    THop hd Y e (σ (oth p)) p r.1 (tStep hL hH r (hreq hd Y e σ none r.1.b)) := by
  obtain ⟨hface, hoth⟩ := tStep_rel hL hH hg (hreq hd Y e σ none r.1.b)
  have h1 : pl hd (oth p) ≠ r.1.a := by rw [ha]; exact pl_ne_pl hd (oth_ne p)
  have h0 : ax0 hd ≠ r.1.a := by rw [ha]; exact (pl_ne_ax0 hd _).symm
  refine ⟨ha, by rw [tStep_a, ha], tStep_s hL hH r _, ?_, ?_, ?_, ?_⟩
  · rw [← ha]; exact hface
  · have hw : (σ (oth p) : ℤ) = 1 ∨ (σ (oth p) : ℤ) = -1 := by rcases Int.units_eq_one_or (σ (oth p)) with h' | h' <;> simp [h']
    have := forced_nonneg hL hH hg h1 hw (hreq_pl hd Y e σ none r.1.b (oth p))
    rw [Lp_eq]; exact this
  · rw [Lp_eq]; exact abs_sub_le_of_toward hL hH hg (nom := fun _ => zN Y e) h0 (hreq_ax0_none hd Y e σ r.1.b)
  · intro i ⟨hi0, hi1, hiz⟩
    have hia : i ≠ r.1.a := by rw [ha]; rcases Fin.exists_fin_two.1 ⟨p, rfl⟩ with h' | h' <;> rw [h'] <;> assumption
    have := abs_sub_le_of_toward hL hH hg (nom := 0) hia (hreq_idle hd Y e σ none r.1.b hi0 hi1 hiz)
    rw [Lp_eq]; simpa only [Pi.zero_apply, sub_zero] using this

end Derive

end BGNd

end Percolation.Literature

end
