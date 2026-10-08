import Percolation.Literature.TallStep
import Percolation.Util.Linter

/-!
# The tall gait, X: layout arithmetic and absolute positions of the segments

Quantitative consequences of the invariant `TallInv` of
the plan of the block construction (Grimmett, *Percolation*, 2nd ed. (1999), §7.3, Lemma (7.52)):
the linear inequalities between the layout constants (`TallLayout.OK.facts`), the relation between
the source cell, the target cell and their lanes, and absolute bounds on the base centres of the
bricks of each segment in terms of the token's position.

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §7.3 pp. 170–174.
-/

noncomputable section

namespace Percolation.Literature

open LatticeModels Contour
open scoped Classical

namespace BGNd

variable {d : ℕ} [NeZero d]

namespace TallLayout

variable {Y : TallLayout}

/-- **The layout inequalities**, linearised: with the atoms `ℓ, Pℓ, P²ℓ, P³ℓ, L', m` every bound
used below is linear. [folklore] -/
theorem OK.facts (h : Y.OK) :
    0 ≤ Y.Lp ∧ Y.Lp + 1 ≤ (Y.P : ℤ) * Y.ell ∧ (Y.L : ℤ) = Y.Lp + Y.m + 1 ∧ (Y.H : ℤ) + 1 = Y.ell ∧
      2 * (Y.m : ℤ) + 2 ≤ Y.H ∧ (8 : ℤ) ≤ Y.P ∧ (Y.Pw : ℤ) = 4 * Y.P + 4 ∧
      Y.Δw ≤ 4 * ((Y.P : ℤ) ^ 2 * Y.ell) + 4 * ((Y.P : ℤ) * Y.ell) ∧ 0 ≤ Y.Δw ∧
      Y.ρv = Y.ell + Y.Lp ∧ Y.ρp = 4 * Y.ell + 4 * Y.Δw + 4 * Y.Lp ∧
      Y.lam = 256 * ((Y.P : ℤ) ^ 2 * Y.ell) ∧ Y.lamJ = 64 * ((Y.P : ℤ) ^ 2 * Y.ell) ∧ Y.Wl = 16 * ((Y.P : ℤ) ^ 2 * Y.ell) ∧
      Y.Dh = 1024 * ((Y.P : ℤ) ^ 3 * Y.ell) ∧ (Y.N₁ : ℤ) = 128 * (Y.P : ℤ) ^ 2 + 8 ∧
      8 * (Y.ell : ℤ) ≤ (Y.P : ℤ) * Y.ell ∧ 8 * ((Y.P : ℤ) * Y.ell) ≤ (Y.P : ℤ) ^ 2 * Y.ell ∧
      8 * ((Y.P : ℤ) ^ 2 * Y.ell) ≤ (Y.P : ℤ) ^ 3 * Y.ell ∧ (Y.N₁ : ℤ) * Y.Lp ≤ 128 * ((Y.P : ℤ) ^ 3 * Y.ell) + 8 * ((Y.P : ℤ) * Y.ell) ∧
      8 * (Y.P : ℤ) ^ 2 ≤ (Y.P : ℤ) ^ 3 ∧ (64 : ℤ) ≤ (Y.P : ℤ) ^ 2 ∧
      (Y.Pw : ℤ) * Y.ell = 4 * ((Y.P : ℤ) * Y.ell) + 4 * Y.ell ∧ 0 < Y.Rmax := by
  obtain ⟨hL, hH, htall, hP⟩ := h
  have hell : (Y.ell : ℤ) = Y.H + 1 := by unfold ell; push_cast; ring
  have hLp : Y.Lp = (Y.L : ℤ) - Y.m - 1 := rfl
  have hPw : (Y.Pw : ℤ) = 4 * Y.P + 4 := by unfold Pw; push_cast; ring
  have hΔ : Y.Δw = Y.Pw * Y.Lp := rfl
  have hP' : (8 : ℤ) ≤ Y.P := by exact_mod_cast hP
  have hH0 : (0 : ℤ) ≤ Y.H := by positivity
  have hell1 : (1 : ℤ) ≤ Y.ell := by rw [hell]; omega
  have hLp0 : 0 ≤ Y.Lp := by rw [hLp]; omega
  have hLpP : Y.Lp + 1 ≤ (Y.P : ℤ) * Y.ell := by rw [hLp]; linarith
  have hPe : 8 * (Y.ell : ℤ) ≤ (Y.P : ℤ) * Y.ell := by nlinarith
  have hP2 : 8 * ((Y.P : ℤ) * Y.ell) ≤ (Y.P : ℤ) ^ 2 * Y.ell := by nlinarith
  have hP3 : 8 * ((Y.P : ℤ) ^ 2 * Y.ell) ≤ (Y.P : ℤ) ^ 3 * Y.ell := by nlinarith
  have hΔw : Y.Δw ≤ 4 * ((Y.P : ℤ) ^ 2 * Y.ell) + 4 * ((Y.P : ℤ) * Y.ell) := by
    rw [hΔ, hPw]
    have : (4 * (Y.P : ℤ) + 4) * Y.Lp ≤ (4 * (Y.P : ℤ) + 4) * ((Y.P : ℤ) * Y.ell) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have hN : (Y.N₁ : ℤ) = 128 * (Y.P : ℤ) ^ 2 + 8 := by unfold N₁; push_cast; ring
  have hNL : (Y.N₁ : ℤ) * Y.Lp ≤ 128 * ((Y.P : ℤ) ^ 3 * Y.ell) + 8 * ((Y.P : ℤ) * Y.ell) := by
    rw [hN]
    have : (128 * (Y.P : ℤ) ^ 2 + 8) * Y.Lp ≤ (128 * (Y.P : ℤ) ^ 2 + 8) * ((Y.P : ℤ) * Y.ell) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    nlinarith
  have hDh : Y.Dh = 1024 * ((Y.P : ℤ) ^ 3 * Y.ell) := by unfold Dh; ring
  have hlam : Y.lam = 256 * ((Y.P : ℤ) ^ 2 * Y.ell) := by unfold lam; ring
  have hlamJ : Y.lamJ = 64 * ((Y.P : ℤ) ^ 2 * Y.ell) := by unfold lamJ; ring
  have hWl : Y.Wl = 16 * ((Y.P : ℤ) ^ 2 * Y.ell) := by unfold Wl; ring
  refine ⟨hLp0, hLpP, by rw [hLp]; ring, by rw [hell], by exact_mod_cast hH, hP', hPw, hΔw,
    by rw [hΔ]; exact mul_nonneg (by positivity) hLp0,
    rfl, rfl, hlam, hlamJ, hWl, hDh, hN, hPe, hP2, hP3, hNL, by nlinarith, by nlinarith, by rw [hPw]; ring, ?_⟩
  unfold Rmax; have : 0 < Y.P := by omega
  positivity

end TallLayout

/-! ## Cells and lanes -/

section Cells

variable (Y : TallLayout) (a : Site 2) (e : MDir)

omit [NeZero d] in
/-- The step of a macro-direction in coordinates. [folklore] -/
theorem stepVec_apply (e : MDir) (i : Fin 2) : stepVec e i = if i = e.1 then (sgOf e : ℤ) else 0 := by
  unfold stepVec sgOf
  by_cases hi : i = e.1
  · subst hi; cases e.2 <;> simp
  · have : (Pi.single e.1 (1 : ℤ) : Site 2) i = 0 := Pi.single_eq_of_ne hi _
    cases h2 : e.2 <;> simp [hi]

omit [NeZero d] in
/-- The centre of the target cell along `e`: one cell further. [folklore] -/
theorem ctr_tgtCell_fst : Y.ctr (tgtCell a e) e.1 = Y.ctr a e.1 + (sgOf e : ℤ) * (2 * Y.Dh) := by
  unfold TallLayout.ctr tgtCell
  rw [Pi.add_apply, stepVec_apply, if_pos rfl]; ring

omit [NeZero d] in
/-- The centre of the target cell across `e`: unchanged. [folklore] -/
theorem ctr_tgtCell_snd : Y.ctr (tgtCell a e) ⟨1 - e.1.val, by have := e.1.isLt; omega⟩ = Y.ctr a ⟨1 - e.1.val, by have := e.1.isLt; omega⟩ := by
  unfold TallLayout.ctr tgtCell
  rw [Pi.add_apply, stepVec_apply, if_neg]
  · ring
  · intro h; have := congrArg Fin.val h; simp at this; have := e.1.isLt; omega

omit [NeZero d] in
/-- The parity flips between a cell and its neighbour. [folklore] -/
theorem cpar_tgtCell : TallLayout.cpar (tgtCell a e) = 1 - TallLayout.cpar a := by
  unfold TallLayout.cpar tgtCell
  simp only [Pi.add_apply, stepVec_apply]
  have h01 : ((0 : Fin 2) = e.1) ∨ ((1 : Fin 2) = e.1) := by
    rcases Fin.eq_zero_or_eq_succ e.1 with h | ⟨j, hj⟩
    · exact Or.inl h.symm
    · right; rw [hj]; exact congrArg Fin.succ (Fin.fin_one_eq_zero j).symm |>.trans rfl
  have hs : (sgOf e : ℤ) = 1 ∨ (sgOf e : ℤ) = -1 := by rcases Int.units_eq_one_or (sgOf e) with h | h <;> simp [h]
  rcases h01 with h | h <;> rcases hs with hs | hs <;>
    simp only [← h, ↓reduceIte, show ((1 : Fin 2) = 0) = False by decide, show ((0 : Fin 2) = 1) = False by decide, hs] <;> omega

omit [NeZero d] in
/-- **The trunk lane of the target cell is the entry lane shifted by `v Λ_J`.** [folklore] -/
theorem lane_tgtCell : Y.lane (tgtCell a e) e = Y.lane a e + (jogDir a e : ℤ) * Y.lamJ := by
  unfold TallLayout.lane jogDir
  rw [ctr_tgtCell_snd, cpar_tgtCell]
  have hp : TallLayout.cpar a = 0 ∨ TallLayout.cpar a = 1 := by
    unfold TallLayout.cpar; omega
  rcases hp with h | h <;> simp [h]

end Cells

/-! ## Counting forced steps -/

section Counts

variable (Y : TallLayout) (e : MDir)

/-- At most `P'` riser steps are forced before the turn. [folklore] -/
theorem nForcedR_le (n k : ℕ) (hk : k ≤ n) : nForcedR Y n k ≤ Y.Pw := by
  have : ∀ k, nForcedR Y n k ≤ k - (n - Y.Pw) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [nForcedR_succ]; split_ifs with h <;> omega
  have := this k; omega

/-- At most `4P'` trunk steps are forced. [folklore] -/
theorem nForced_le (n₁ n₂ k : ℕ) : nForced Y e n₁ n₂ k ≤ 4 * Y.Pw := by
  have : ∀ k, nForced Y e n₁ n₂ k ≤ min (k - (n₁ - Y.Pw)) (2 * Y.Pw) + min (k - (n₂ - Y.Pw)) (2 * Y.Pw) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [nForced_succ]
      by_cases h : trunkForce Y e n₁ n₂ k ≠ 0
      · rw [if_pos h]
        have hk : (k < n₁ ∧ n₁ ≤ k + Y.Pw) ∨ (n₁ ≤ k ∧ k < n₁ + Y.Pw) ∨ (k < n₂ ∧ n₂ ≤ k + Y.Pw) ∨ (n₂ ≤ k ∧ k < n₂ + Y.Pw) := by
          by_contra hno
          apply h
          unfold trunkForce
          simp only
          rw [if_neg (fun h' => hno (Or.inl h')), if_neg (fun h' => hno (Or.inr (Or.inl h'))),
            if_neg (fun h' => hno (Or.inr (Or.inr (Or.inl h')))), if_neg (fun h' => hno (Or.inr (Or.inr (Or.inr h'))))]
        rcases hk with hk | hk | hk | hk <;> omega
      · rw [if_neg h]; omega
  have := this k; omega

end Counts

end BGNd

end Percolation.Literature

end
