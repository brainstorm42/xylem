import Percolation.Literature.TallInv
import Percolation.Util.Linter

/-!
# The flat gait: the plate-hopping plan of the block construction when `L + 1 > 8 (H + 1)`

Grimmett, *Percolation*, 2nd ed. (1999), §7.3, proof of
Lemma (7.52), case `H < L` ("we have no control over the aspect ratio of the basic brick, and
consequently two cases with somewhat different geometries need to be considered", Fig. 7.12): when
the brick `B(L, H)` is a flat *plate*, top stackings advance too slowly, and the construction
proceeds by **side stackings only** (Grimmett's (B)): a *hop* from a plate of axis `q` through its
face `x_j = b_j ± (L + 1)` lands a plate of axis `j`, displaced by exactly `L + 1` along `j` and by
an uncontrolled `t ∈ [m + 1, H - m - 1]` along `q`. Alternating the two plane axes gives a
*diagonal leg*, monotone in both plane coordinates; the renormalised lattice is therefore indexed
by the two **diagonals** `u₁ = x₁ + x₂`, `u₂ = x₁ - x₂` of the plane. Changes of direction, and
forks, are made by Grimmett's (C) (Fig. 7.11): one *top stacking* off the leg's head, pushed
towards the new side, then a hop through the side face on the new side — while, at a fork, the
old leg simply continues through the opposite side face of its head; layers are joined by
*risers* (up, forward, up, …).

This file fixes the layout (`FlatLayout`: unit `U = L + 1`, half cell `D = 2¹² U`, lanes `Λ = 1280
U`, parity offset `Λ_J = 768 U`, layer pitch `W = 16 U`, budget `R = 2¹⁵`), the diagonal
coordinates, cells, lanes and layers, the admissibility windows of tokens, and the plan as a
sequence of thirteen homogeneous **segments** (`Kind`: first plate, riser, preamble, turn, leg) with
their start records, directions and stopping rules, the exit tokens and the outcome.

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §7.3 pp. 170–176, Figs. 7.11, 7.12.
* D. J. Barsky, G. R. Grimmett, C. M. Newman, *Percolation in half-spaces: equality of critical
  densities and continuity of the percolation probability*, PTRF 90 (1991) 111–148, §5.
-/

noncomputable section

namespace Percolation.Literature

open LatticeModels Contour
open scoped Classical

namespace BGNd

variable {d : ℕ}

/-! ## Layout -/

/-- **Layout constants of the flat gait** for plates `B(L, H)`, in the unit `U = L + 1`. [cite: GrimmettPercolation1999, §7.3 p. 170 (7.54), H < L] -/
structure FlatLayout where
  /-- seed radius -/
  m : ℕ
  /-- plate half-width -/
  L : ℕ
  /-- plate thickness -/
  H : ℕ

namespace FlatLayout

variable (Y : FlatLayout)

/-- The hop `U = L + 1`. [folklore] -/
def U : ℤ := Y.L + 1
/-- The free play `L' = L - m - 1` of a transverse coordinate in one step. [folklore] -/
def Lp : ℤ := (Y.L : ℤ) - Y.m - 1
/-- Half the cell size, `D = 2¹² U`. [folklore] -/
def Df : ℤ := 4096 * Y.U
/-- The lane offset `Λ`. [folklore] -/
def lam : ℤ := 1280 * Y.U
/-- The parity offset of the lanes `Λ_J`. [folklore] -/
def lamJ : ℤ := 256 * Y.U
/-- The layer pitch `W`. [folklore] -/
def Wl : ℤ := 16 * Y.U
/-- The lateral window of a token, `ρ_p`. [folklore] -/
def ρp : ℤ := 640 * Y.U
/-- The vertical window of a token, `ρ_v`. [folklore] -/
def ρv : ℤ := 4 * Y.U
/-- The plate budget `R = 2¹⁵`. [folklore] -/
def Rmax : ℕ := 2 ^ 15

/-- The layer of a macro-direction. [folklore] -/
def zOf (e : MDir) : ℤ := TallLayout.layerIdx e * Y.Wl
/-- The centre of a cell along a diagonal coordinate. [folklore] -/
def ctr (c : Site 2) (i : Fin 2) : ℤ := c i * (2 * Y.Df)
/-- The lane offset of a direction: `±Λ`. [folklore] -/
def nu (e : MDir) : ℤ := (sgOf e : ℤ) * Y.lam
/-- The lane of the trunk of direction `e` in cell `c`, in the perpendicular diagonal coordinate. [folklore] -/
def lane (c : Site 2) (e : MDir) : ℤ := Y.ctr c (latDir e true).1 + Y.nu e + TallLayout.cpar c * Y.lamJ

/-- **Admissible layouts**: the seed fits, and the regime is flat, `8 (H + 1) ≤ L + 1`. [folklore] -/
structure OK (Y : FlatLayout) : Prop where
  hL : Y.m + 1 ≤ Y.L
  hH : 2 * Y.m + 2 ≤ Y.H
  flat : 8 * ((Y.H : ℤ) + 1) ≤ (Y.L : ℤ) + 1

end FlatLayout

/-! ## Plane axes, diagonal coordinates, fine directions -/

/-- The other plane index. [folklore] -/
def oth (j : Fin 2) : Fin 2 := ⟨1 - j.val, Nat.lt_of_le_of_lt (Nat.sub_le 1 j.val) Nat.one_lt_two⟩

section Axes

variable (hd : 3 ≤ d)

/-- The two fine plane axes `1, 2`, indexed by `Fin 2`. [folklore] -/
def pl (j : Fin 2) : Fin d := axOf hd (j, true)

/-- The two diagonal coordinates `u₀ = x₁ + x₂`, `u₁ = x₁ - x₂`. [folklore] -/
def Uc (i : Fin 2) (x : Site d) : ℤ := x (pl hd 0) + (if i = 0 then 1 else -1) * x (pl hd 1)

/-- The fine signs of a macro-direction: `(s, s)` along `u₀`, `(s, -s)` along `u₁`. [folklore] -/
def dsg (e : MDir) : Fin 2 → ℤˣ := fun j => if e.1 = 0 then sgOf e else if j = 0 then sgOf e else -sgOf e

/-- The plane index of a fine axis (junk `0` off the plane). [folklore] -/
def plIdx (i : Fin d) : Fin 2 := if i = pl hd 1 then 1 else 0

end Axes

/-! ## Cells, tokens -/

namespace FlatLayout

variable (Y : FlatLayout) (hd : 3 ≤ d)

/-- The macro-cell of a fine vertex: floor division of the diagonal coordinates shifted by `D`. [folklore] -/
def cellOf (x : Site d) : Site 2 := fun i => (Uc hd i x + Y.Df) / (2 * Y.Df)

end FlatLayout

/-! ## Program state -/

/-- **The kinds of segments**: the first plate; a riser; a preamble ending on a plate of the given
plane axis; a turn off a plate of plane axis `p` (a top stacking pushed towards the new side, then
a hop through the new side face); a diagonal leg. [folklore] -/
inductive Kind
  | first | rise | pre (p : Fin 2) | turn (p : Fin 2) | leg
  deriving DecidableEq

/-- **The run state of the flat gait**: the records of the thirteen segments, newest first. [folklore] -/
structure FS (d : ℕ) where
  /-- the segments -/
  segs : Fin 13 → List (BrickRec d)

namespace FS

/-- The initial state. [folklore] -/
def init : FS d := ⟨fun _ => []⟩

/-- Filing a record into a segment. [folklore] -/
def put (st : FS d) (i : Fin 13) (r : BrickRec d) : FS d := ⟨Function.update st.segs i (r :: st.segs i)⟩

/-- All records. [folklore] -/
def all (st : FS d) : List (BrickRec d) := (List.finRange 13).flatMap st.segs

end FS

/-! ## The plan -/

section Plan

variable [NeZero d] (hd : 3 ≤ d) (Y : FlatLayout) (hL : Y.m + 1 ≤ Y.L) (hH : 2 * Y.m + 2 ≤ Y.H) (a : Site 2) (e : MDir) (τ : TTok d)

/-- The target cell. [folklore] -/
def ftgt : Site 2 := a + stepVec e

/-- **The macro-direction of the jog**, decided when the riser is complete: along the perpendicular
diagonal, towards the target lane from the riser's head (from the token if the riser is empty). [folklore] -/
def eJOf (st : FS d) : MDir :=
  latDir e (decide (Uc hd (latDir e true).1 (match (st.segs 1).head? with | some r => r.1.b | none => τ.pos) ≤ Y.lane (ftgt a e) e))

variable (ej : MDir)
/-- The first lateral direction met by the trunk (lane on the near side): sign `-s`. [folklore] -/
def eB1 : MDir := latDir e (!e.2)
/-- The second lateral direction: sign `s`. [folklore] -/
def eB2 : MDir := latDir e e.2

/-- The plane index whose fine sign differs between `e` and a lateral direction `e'`. [folklore] -/
def flipIdx (e' : MDir) : Fin 2 := if sgOf e' = sgOf e then 1 else 0

/-- The nominal height after the riser: the layer of `e`. [folklore] -/
def zN : ℤ := Y.zOf e

/-- The riser direction: towards the layer of `e` from the token's actual height (`-1` when level,
so that the riser, which always places at least one pair, overshoots by less than `U + H`). [folklore] -/
def friseDir : ℤˣ := if τ.pos (ax0 hd) < zN Y e then 1 else -1

/-- **The requests of a hop**: plane coordinates pushed along the fine signs `σ`, the height up /
down as prescribed or towards the nominal height, every other coordinate towards `0`. [cite: GrimmettPercolation1999, §7.3 p. 173 (D)] -/
def hreq (σ : Fin 2 → ℤˣ) (zmode : Option Bool) (b : Site d) : Fin d → Bool := fun i =>
  if i = pl hd 0 then decide (0 ≤ (σ 0 : ℤ)) else if i = pl hd 1 then decide (0 ≤ (σ 1 : ℤ))
  else if i = ax0 hd then (match zmode with | some up => up | none => decide (b (ax0 hd) ≤ zN Y e))
  else decide (b i ≤ 0)

/-- A hop off the record `r` through the face of axis `j` with sign `u`. [folklore] -/
def hop (σ : Fin 2 → ℤˣ) (zmode : Option Bool) (r : BrickRec d) (j : Fin d) (u : ℤˣ) : Act d :=
  Act.side r j u (hreq hd Y e σ zmode r.1.b)

/-- The next hop of a diagonal leg of signs `σ` off `r`: through the other plane axis. [folklore] -/
def diagHop (σ : Fin 2 → ℤˣ) (zmode : Option Bool) (r : BrickRec d) : Act d :=
  let q := oth (plIdx hd r.1.a)
  hop hd Y e σ zmode r (pl hd q) (σ q)

/-! ### The thirteen segments -/

/-- The non-flipped plane axis of the turn towards `e'`. [folklore] -/
def keepIdx (e' : MDir) : Fin 2 := oth (flipIdx e e')

/-- The kinds: `A₀`; riser; preamble; turn towards the jog; jog; turn back; trunk 1; fork 1;
trunk 2; fork 2; trunk 3; branch 1; branch 2. [folklore] -/
def kindOf : Fin 13 → Kind :=
  ![Kind.first, Kind.rise, Kind.pre (keepIdx e ej), Kind.turn (keepIdx e ej), Kind.leg, Kind.turn (keepIdx e ej), Kind.leg,
    Kind.turn (keepIdx e (eB1 e)), Kind.leg, Kind.turn (keepIdx e (eB2 e)), Kind.leg, Kind.leg, Kind.leg]

/-- The travel direction of each segment (for turns: the new direction). [folklore] -/
def fdirOf : Fin 13 → MDir :=
  ![e, e, e, ej, ej, e, e, eB1 e, e, eB2 e, e, eB1 e, eB2 e]

/-- The segment a segment starts from (off its head; segment `0` starts on the token; the trunk
continues off its own previous stretch, not off the fork). [folklore] -/
def startOf : Fin 13 → Fin 13 :=
  ![0, 0, 1, 2, 3, 4, 5, 6, 6, 8, 8, 7, 9]

/-- The plane axis a leg must end on, if any (so that the next turn is off a plate of the kept
axis). [folklore] -/
def legAxisOf : Fin 13 → Option (Fin 2) :=
  ![none, none, none, none, some (keepIdx e ej), none, some (keepIdx e (eB1 e)), none, some (keepIdx e (eB2 e)), none, none, none, none]

/-- **Room to continue** a leg of direction `e*` in the target cell: the head's diagonal coordinate
is more than `3U` before the far face. [folklore] -/
def froom (e' : MDir) (b : Site d) : Prop :=
  (sgOf e' : ℤ) * (Uc hd e'.1 b - Y.ctr (ftgt a e) e'.1) < Y.Df - 3 * Y.U

/-- The trunk has reached the take-off line of the branch towards `e'` (its port lane, less `U`). [folklore] -/
def fpassed (e' : MDir) (b : Site d) : Prop :=
  (sgOf e : ℤ) * (Y.lane (ftgt a e) e' - Y.U) ≤ (sgOf e : ℤ) * Uc hd e.1 b

/-- The jog has reached the target lane (within `U` before it, or beyond). [folklore] -/
def ffitsJ (b : Site d) : Prop :=
  (sgOf (ej) : ℤ) * (Y.lane (ftgt a e) e - Uc hd (ej).1 b) ≤ Y.U

/-- The riser has reached the nominal height. [folklore] -/
def ffitsR (b : Site d) : Prop := (friseDir hd Y e τ : ℤ) * (zN Y e - b (ax0 hd)) ≤ 0

/-- **The stopping rule of a leg**, by segment: jog — target lane; trunk 1, 2 — take-off lines;
trunk 3 and the branches — room. [folklore] -/
def legStop (i : Fin 13) (b : Site d) : Prop :=
  if i = 4 then ffitsJ hd Y a e ej b
  else if i = 6 then fpassed hd Y a e (eB1 e) b
  else if i = 8 then fpassed hd Y a e (eB2 e) b
  else ¬froom hd Y a e (fdirOf e ej i) b

/-- The least number of plates of a leg that feeds a fork (so that the fork's plates clear the
structures behind): `3` for trunks 1 and 2. [folklore] -/
def minLenOf (i : Fin 13) : ℕ := if i = 6 ∨ i = 8 then 3 else 1

/-- The start record of a segment in a state: the head of its start segment. [folklore] -/
def startRec (st : FS d) (i : Fin 13) : Option (BrickRec d) := (st.segs (startOf i)).head?

/-- The placement of an act: the first plate stands on the token's seed with the token's axis. [folklore] -/
def fplaceOf : Act d → BrickPos d
  | Act.first => ⟨τ.ax, dsg e (plIdx hd τ.ax), τ.pos⟩
  | Act.top r sg => tStep hL hH r sg
  | Act.side r i u sg => sStep hL hH r i u sg

/-- **The exit token beyond the last plate of a leg** of direction `e*`: the base of the next hop
(through the other plane axis), with source `e`. [folklore] -/
def fexitTok (e' : MDir) (r : BrickRec d) : TTok d :=
  let q := oth (plIdx hd r.1.a)
  ⟨sideExit hL hH r (pl hd q) (dsg e' q) (hreq hd Y e (dsg e') none r.1.b), pl hd q, some e⟩

end Plan

end BGNd

end Percolation.Literature

end
