import Percolation.Literature.TallInit
import Percolation.Util.Linter

/-!
# The tall gait, XVI: the block kit of the tall gait

The data of the block kit (`BlockKit.lean`) realised by
the tall gait: tokens `TTok`, admissibility `TAdm`, the macro-cell map `cellOf`, the zones `zoneF`,
the plan `tallNext` / `tallFinish`, the brick budget `R = 2¹³ P³`, and the initial structure `U₀`,
`initTok` (Grimmett, *Percolation*, 2nd ed. (1999), §7.3, proof of Lemma (7.52)).

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §7.3 pp. 169–176.
-/

noncomputable section

namespace Percolation.Literature

open LatticeModels Contour
open scoped Classical

namespace BGNd

variable {d : ℕ} [NeZero d]

/-- **The direction of a token**, read off its axis and the side of its cell's centre it lies on
(meaningful for admissible tokens: `dirOf τ = e` when `TAdm a e τ`). [folklore] -/
def dirOf (Y : TallLayout) (hd : 3 ≤ d) (τ : TTok d) : MDir :=
  (⟨(τ.ax.val - 1) % 2, Nat.mod_lt _ Nat.two_pos⟩,
    decide (Y.ctr (Y.cellOf hd τ.pos) ⟨(τ.ax.val - 1) % 2, Nat.mod_lt _ Nat.two_pos⟩ < τ.pos τ.ax))

/-- **The provenance reported to the renormalisation**: the token's source direction, except that
the nominal provenance `rev e` of the initial tokens (never the provenance of a token handed on by a
run, whose onward directions exclude the reverse) is reported as none. [folklore] -/
def srcDirK (Y : TallLayout) (hd : 3 ≤ d) (τ : TTok d) : Option MDir :=
  match τ.src with
  | none => none
  | some d' => if d' = rev (dirOf Y hd τ) then none else some d'

/-- **The block kit of the tall gait.** Admissible tokens are the geometrically admissible ones with a
source layer. [cite: GrimmettPercolation1999, §7.3 pp. 169–176] -/
def tallKit (Y : TallLayout) (hd : 3 ≤ d) (hY : Y.OK) : Kit d where
  Tok := TTok d
  anchor := TTok.pos
  ax := TTok.ax
  srcDir := srcDirK Y hd
  init := initTok Y hd
  U₀ := U0 Y hd
  Adm := fun a e τ => TAdm hd Y a e τ ∧ τ.src ≠ none
  cell := Y.cellOf hd
  zone := fun a e τ => zoneF Y hd a e τ
  next := fun a e τ => tallNext hd Y hY.hL hY.hH a e τ
  finish := fun a e τ => tallFinish hd Y hY.hL hY.hH a e τ
  R := Y.Rmax

section Simp

variable (Y : TallLayout) (hd : 3 ≤ d) (hY : Y.OK)

/-- Unfolding the kit. [folklore] -/
@[simp] theorem tallKit_Tok : (tallKit Y hd hY).Tok = TTok d := rfl
/-- Unfolding the kit. [folklore] -/
@[simp] theorem tallKit_R : (tallKit Y hd hY).R = Y.Rmax := rfl
/-- Unfolding the kit. [folklore] -/
theorem tallKit_next (a : Site 2) (e : MDir) (τ : TTok d) (h : BrickHist d) :
    (tallKit Y hd hY).next a e τ h = tallNext hd Y hY.hL hY.hH a e τ h := rfl
/-- Unfolding the kit. [folklore] -/
theorem tallKit_finish (a : Site 2) (e : MDir) (τ : TTok d) (h : BrickHist d) :
    (tallKit Y hd hY).finish a e τ h = tallFinish hd Y hY.hL hY.hH a e τ h := rfl
/-- Unfolding the kit. [folklore] -/
theorem tallKit_zone (a : Site 2) (e : MDir) (τ : TTok d) : (tallKit Y hd hY).zone a e τ = zoneF Y hd a e τ := rfl
/-- Unfolding the kit. [folklore] -/
theorem tallKit_Adm (a : Site 2) (e : MDir) (τ : TTok d) : (tallKit Y hd hY).Adm a e τ ↔ TAdm hd Y a e τ ∧ τ.src ≠ none := Iff.rfl
/-- Unfolding the kit. [folklore] -/
theorem tallKit_srcDir (τ : TTok d) : (tallKit Y hd hY).srcDir τ = srcDirK Y hd τ := rfl
/-- Unfolding the kit. [folklore] -/
theorem tallKit_init (e : MDir) : (tallKit Y hd hY).init e = initTok Y hd e := rfl
/-- Unfolding the kit. [folklore] -/
theorem tallKit_U0 : (tallKit Y hd hY).U₀ = U0 Y hd := rfl

end Simp

end BGNd

end Percolation.Literature

end
