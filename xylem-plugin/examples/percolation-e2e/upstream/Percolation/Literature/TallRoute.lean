import Percolation.Literature.GaitSteps
import Percolation.Util.Linter

/-!
# The tall gait: the brick-stacking plan of the block construction when `L + 1 ≤ P (H + 1)`

The deterministic plan of one attempt of the block
construction of Lemma (7.52) of Grimmett, *Percolation*, 2nd ed. (1999), §7.3, pp. 169–176, in the
regime of bricks `B(L,H)` which are not too flat (`L + 1 ≤ P (H + 1)`), for `ℤ^d`, `d ≥ 3`: top
stackings ((A) p. 172) travel along the axes — each brick advances by exactly `H + 1` — side
stackings ((B)) turn and branch, and the subfacets requested ((D)) steer. One attempt along the
directed macro-edge `(a, e)` of the renormalised planar lattice (cells of side `D` in the plane of
the fine axes `1, 2`; four *layers* along the fine axis `0`, one per incoming direction, so that the
structures of the four attempts that may target a cell never meet; two *lanes* per axis and a
*parity offset* for the ports) consists of the segments

* `A`: the brick on the token's seed and a short leg along `e` (pre-steered vertically);
* `R` (if the layer changes): a turn up or down and a vertical leg — the *riser* — of adaptive length;
* `J`: a turn sideways and a lateral leg — the *jog* — of adaptive length, re-centring the attempt on
  the trunk lane of the target cell (top stackings cannot correct lateral deviations, (D));
* `T`: a turn forward and the *trunk* along `e` across the target cell to its far face, off which two
  side bricks `γ₁, γ₂` are placed towards the two lateral faces as the trunk passes their lanes
  (pre- and post-steered, (B)–(D));
* `B1, B2`: the *branch* legs from `γ₁, γ₂` to the lateral faces;

and hands on three tokens: the open seed squares beyond the last bricks of `T, B1, B2`, one step
inside the target cell before each of its three onward faces.

This file DEFINES the plan as a program: layout constants (`TallLayout`), tokens (`TTok`), the
program state (`RS`, a decomposition of the history into the segments above), the decision function
`step` (the next act, where its record goes, the next phase), the placements `placeOf`, the fold
`foldState`, and finally `tallNext` / `tallFinish`, the `next` / `finish` of a block kit
(`BlockKit.lean`). Its properties are proved in the sequel.

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §7.3 pp. 169–176, (A)–(D).
* D. J. Barsky, G. R. Grimmett, C. M. Newman, *Probab. Theory Related Fields* 90 (1991), 111–148, §3.
-/

noncomputable section

namespace Percolation.Literature

open LatticeModels Contour
open scoped Classical

namespace BGNd

variable {d : ℕ}

/-! ## Axes and macro-directions -/

/-- The sign of a macro-direction. [folklore] -/
def sgOf (e : MDir) : ℤˣ := if e.2 then 1 else -1

/-- The lateral macro-direction of sign `b`. [folklore] -/
def latDir (e : MDir) (b : Bool) : MDir := (⟨1 - e.1.val, by have := e.1.isLt; omega⟩, b)

/-- Auxiliary fact `sgOf_latDir`. [folklore] -/
@[simp] theorem sgOf_latDir (e : MDir) (b : Bool) : sgOf (latDir e b) = if b then 1 else -1 := rfl

/-- Auxiliary fact `sgOf_val`. [folklore] -/
theorem sgOf_val (e : MDir) : (sgOf e : ℤ) = if e.2 then 1 else -1 := by
  unfold sgOf; split_ifs <;> rfl

section Axes

variable (hd : 3 ≤ d)
include hd

/-- The vertical fine axis `0` (layers). [cite: GrimmettPercolation1999, §7.3 p. 170] -/
def ax0 : Fin d := ⟨0, by omega⟩

/-- The fine axis of a macro-direction: macro-axis `i ↦` fine axis `i + 1`. [cite: GrimmettPercolation1999, §7.3 p. 170] -/
def axOf (e : MDir) : Fin d := ⟨e.1.val + 1, by have := e.1.isLt; omega⟩

/-- The lateral fine axis of a macro-direction: the other plane axis. [folklore] -/
def latOf (e : MDir) : Fin d := ⟨2 - e.1.val, by have := e.1.isLt; omega⟩

/-- Auxiliary fact `axOf_ne_ax0`. [folklore] -/
theorem axOf_ne_ax0 (e : MDir) : axOf hd e ≠ ax0 hd := by
  unfold axOf ax0; intro h; have := Fin.mk.inj_iff.1 h; omega

/-- Auxiliary fact `latOf_ne_ax0`. [folklore] -/
theorem latOf_ne_ax0 (e : MDir) : latOf hd e ≠ ax0 hd := by
  have := e.1.isLt
  unfold latOf ax0; intro h; have := Fin.mk.inj_iff.1 h; omega

/-- Auxiliary fact `latOf_ne_axOf`. [folklore] -/
theorem latOf_ne_axOf (e : MDir) : latOf hd e ≠ axOf hd e := by
  have := e.1.isLt
  unfold latOf axOf; intro h; have := Fin.mk.inj_iff.1 h; omega

/-- Auxiliary fact `axOf_latDir`. [folklore] -/
theorem axOf_latDir (e : MDir) (b : Bool) : axOf hd (latDir e b) = latOf hd e := by
  have := e.1.isLt
  unfold latOf axOf latDir; apply Fin.ext; simp only; omega

/-- Auxiliary fact `latOf_latDir`. [folklore] -/
theorem latOf_latDir (e : MDir) (b : Bool) : latOf hd (latDir e b) = axOf hd e := by
  have := e.1.isLt
  unfold latOf axOf latDir; apply Fin.ext; simp only; omega

end Axes

/-! ## Layout -/

/-- **Layout constants of the tall gait** for bricks `B(L,H)` with regime parameter `P`: step
`ℓ = H + 1`, steering window `P' = 4P + 4`, lane offsets `Λ = 256 P² ℓ` and parity offset
`Λ_J = 64 P² ℓ`, layer pitch `W = 16 P² ℓ`, half cell size `D/2 = 2¹⁰ P³ ℓ`, and the brick budget
`R = 2¹³ P³`. [cite: GrimmettPercolation1999, §7.3 pp. 170–171] -/
structure TallLayout where
  /-- seed radius -/
  m : ℕ
  /-- brick half-width -/
  L : ℕ
  /-- brick height -/
  H : ℕ
  /-- regime parameter: `L + 1 ≤ P (H + 1)` -/
  P : ℕ

namespace TallLayout

variable (Y : TallLayout)

/-- The step of a top stacking, `ℓ = H + 1`. [folklore] -/
def ell : ℕ := Y.H + 1
/-- The steering window `P' = 4P + 4`. [folklore] -/
def Pw : ℕ := 4 * Y.P + 4
/-- The lane offset `Λ`. [folklore] -/
def lam : ℤ := 256 * Y.P ^ 2 * Y.ell
/-- The parity offset of the lanes `Λ_J`. [folklore] -/
def lamJ : ℤ := 64 * Y.P ^ 2 * Y.ell
/-- The layer pitch `W`. [folklore] -/
def Wl : ℤ := 16 * Y.P ^ 2 * Y.ell
/-- Half the cell size. [folklore] -/
def Dh : ℤ := 2 ^ 10 * Y.P ^ 3 * Y.ell
/-- The brick budget of an attempt. [folklore] -/
def Rmax : ℕ := 2 ^ 13 * Y.P ^ 3
/-- The transverse wobble of one top stacking, `L' = L - m - 1`. [folklore] -/
def Lp : ℤ := (Y.L : ℤ) - Y.m - 1
/-- The drift of a steering window, `Δ_w = P' L'`. [folklore] -/
def Δw : ℤ := Y.Pw * Y.Lp
/-- The vertical tolerance `ρ_v = ℓ + L'`. [folklore] -/
def ρv : ℤ := Y.ell + Y.Lp
/-- The port tolerance `ρ_p = 4ℓ + 4Δ_w + 4L'`. [folklore] -/
def ρp : ℤ := 4 * Y.ell + 4 * Y.Δw + 4 * Y.Lp
/-- A bound for the lengths of risers and jogs, `N₁ = 128 P² + 8`. [folklore] -/
def N₁ : ℕ := 128 * Y.P ^ 2 + 8

/-- The layer index of a macro-direction (E, W, N, S ↦ 0, 1, 2, 3). [folklore] -/
def layerIdx (e : MDir) : ℕ := 2 * e.1.val + (if e.2 then 0 else 1)

/-- The nominal base height of the layer of a macro-direction. [folklore] -/
def zOf (e : MDir) : ℤ := layerIdx e * Y.Wl

/-- The lane of a macro-direction (`±Λ` by sign). [folklore] -/
def nu (e : MDir) : ℤ := if e.2 then Y.lam else -Y.lam

/-- The parity of a cell. [folklore] -/
def cpar (c : Site 2) : ℤ := (c 0 + c 1) % 2

/-- The centre coordinate of a cell along the fine axis of macro-axis `i`. [folklore] -/
def ctr (c : Site 2) (i : Fin 2) : ℤ := c i * (2 * Y.Dh)

/-- **The trunk lane** of direction `e` in cell `c` (lateral coordinate): centre + `ν(e)` + parity
offset. Exit ports of `c` sit on this lane; entries into `c + e'` arrive on `c`'s lanes and jog by
`±Λ_J` onto those of `c + e'`. [folklore] -/
def lane (c : Site 2) (e : MDir) : ℤ := Y.ctr c ⟨1 - e.1.val, by have := e.1.isLt; omega⟩ + Y.nu e + cpar c * Y.lamJ

/-- The macro-cell of a fine vertex (floor division of the plane coordinates shifted by `D/2`). [folklore] -/
def cellOf (hd : 3 ≤ d) (x : Site d) : Site 2 := fun i => (x (axOf hd (i, true)) + Y.Dh) / (2 * Y.Dh)

end TallLayout

/-! ## Tokens -/

/-- **Tokens of the tall gait**: the centre of an open seed square, its axis, and the direction of the
attempt that produced it (`none` initially). [cite: GrimmettPercolation1999, §7.3 p. 174] -/
structure TTok (d : ℕ) where
  /-- centre of the seed square -/
  pos : Site d
  /-- axis orthogonal to the seed square -/
  ax : Fin d
  /-- producing direction -/
  src : Option MDir

/-! ## Program state -/

/-- The phases of an attempt. [folklore] -/
inductive Phase
  | segA | segR | segJ | segT | segB1 | segB2 | done
  deriving DecidableEq

/-- Where the record of the act just emitted is filed. [folklore] -/
inductive Slot
  | toA | toR | toJ | toT | toG1 | toG2 | toB1 | toB2
  deriving DecidableEq

/-- **The run state**: the history decomposed into segments (each newest first), the two branch
bricks, and the phase. [folklore] -/
structure RS (d : ℕ) where
  /-- segment `A` (newest first) -/
  sA : List (BrickRec d)
  /-- the riser -/
  sR : List (BrickRec d)
  /-- the jog -/
  sJ : List (BrickRec d)
  /-- the trunk -/
  sT : List (BrickRec d)
  /-- the first branch brick -/
  g1 : Option (BrickRec d)
  /-- the second branch brick -/
  g2 : Option (BrickRec d)
  /-- the first branch leg (beyond `γ₁`) -/
  sB1 : List (BrickRec d)
  /-- the second branch leg -/
  sB2 : List (BrickRec d)
  /-- the phase -/
  ph : Phase

namespace RS

/-- The initial state. [folklore] -/
def init : RS d := ⟨[], [], [], [], none, none, [], [], Phase.segA⟩

/-- Filing a record. [folklore] -/
def put (st : RS d) : Slot → BrickRec d → RS d
  | Slot.toA, r => { st with sA := r :: st.sA }
  | Slot.toR, r => { st with sR := r :: st.sR }
  | Slot.toJ, r => { st with sJ := r :: st.sJ }
  | Slot.toT, r => { st with sT := r :: st.sT }
  | Slot.toG1, r => { st with g1 := some r }
  | Slot.toG2, r => { st with g2 := some r }
  | Slot.toB1, r => { st with sB1 := r :: st.sB1 }
  | Slot.toB2, r => { st with sB2 := r :: st.sB2 }

/-- All records held by the state. [folklore] -/
def all (st : RS d) : List (BrickRec d) :=
  st.sA ++ st.sR ++ st.sJ ++ st.sT ++ st.g1.toList ++ st.g2.toList ++ st.sB1 ++ st.sB2

end RS

/-- **Acts**: place the first brick on the token's seed, or a top / side step off a record.
[cite: GrimmettPercolation1999, §7.3 pp. 172–173 (A), (B)] -/
inductive Act (d : ℕ)
  | first
  | top (r : BrickRec d) (sg : Fin d → Bool)
  | side (r : BrickRec d) (i : Fin d) (u : ℤˣ) (sg : Fin d → Bool)

/-! ## The plan -/

section Plan

variable [NeZero d] (hd : 3 ≤ d) (Y : TallLayout) (hL : Y.m + 1 ≤ Y.L) (hH : 2 * Y.m + 2 ≤ Y.H) (a : Site 2) (e : MDir) (τ : TTok d)

/-- The placement of an act. [folklore] -/
def placeOf : Act d → BrickPos d
  | Act.first => ⟨axOf hd e, sgOf e, τ.pos⟩
  | Act.top r sg => tStep hL hH r sg
  | Act.side r i u sg => sStep hL hH r i u sg

/-- The target cell. [folklore] -/
def tgtCell : Site 2 := a + stepVec e

/-- The riser direction: up, down, or none (`0`), from the token's layer to the layer of `e`. [folklore] -/
def riseDir : ℤ :=
  match τ.src with
  | none => 0
  | some d' => if Y.zOf d' < Y.zOf e then 1 else if Y.zOf e < Y.zOf d' then -1 else 0

omit [NeZero d] in
/-- The riser direction is `0`, `1` or `-1`. [folklore] -/
theorem riseDir_cases : riseDir Y e τ = 0 ∨ riseDir Y e τ = 1 ∨ riseDir Y e τ = -1 := by
  unfold riseDir
  cases τ.src with
  | none => exact Or.inl rfl
  | some d' => simp only; split_ifs <;> simp

/-- The jog direction: towards the trunk lane of the target cell (parity). [folklore] -/
def jogDir : ℤˣ := if TallLayout.cpar (tgtCell a e) = 1 then 1 else -1

/-- The sign of the first branch (the lateral port met first along the trunk): `-s`. [folklore] -/
def br1Sign : ℤˣ := -sgOf e

/-- **Requested signs for a free step**: move towards the nominal value in every coordinate. [cite: GrimmettPercolation1999, §7.3 p. 173 (D)] -/
def toward (nom : Site d) (b : Site d) : Fin d → Bool := fun i => decide (b i ≤ nom i)

/-- Overriding the request in one coordinate. [folklore] -/
def force (sg : Fin d → Bool) (i : Fin d) (v : ℤ) : Fin d → Bool := Function.update sg i (decide (0 ≤ v))

/-- The nominal point of the entry segments `A`, `R`: lateral = the token's lateral position, height =
the layer of `e` (used only when there is no riser), other coordinates `0`. [folklore] -/
def nomA : Site d := fun i => if i = latOf hd e then τ.pos (latOf hd e) else if i = ax0 hd then Y.zOf e else 0

/-- The nominal point on the trunk side: height = layer of `e`, lateral = `y` (given), others `0`. [folklore] -/
def nomT (y : ℤ) : Site d := fun i => if i = latOf hd e then y else if i = ax0 hd then Y.zOf e else 0

/-- The side-exit window of a brick of axis `i`, sign `u`, base `b`, fits the band `[z - ℓ, z + ℓ]`:
time to turn. [folklore] -/
def fits (b : ℤ) (u : ℤ) (z : ℤ) : Prop :=
  z - Y.ell ≤ b + u * (Y.m + 1) ∧ b + u * (Y.m + 1) ≤ z + Y.ell ∧
    z - Y.ell ≤ b + u * (Y.H - Y.m - 1) ∧ b + u * (Y.H - Y.m - 1) ≤ z + Y.ell

/-- The trunk may be extended off a brick based at `b` (along `e`): the next brick's exit plane stays
within the cell. [folklore] -/
def roomT (c : Site 2) (e' : MDir) (b : ℤ) : Prop :=
  (sgOf e' : ℤ) * (b + (sgOf e' : ℤ) * Y.ell - Y.ctr c e'.1) ≤ Y.Dh - 1 - Y.ell

/-- The trunk has reached the lane of the lateral port of sign `v`: `s (b - X) ≥ v' Λ - P'ℓ/…`; we
branch off the first trunk brick whose base has passed `X + (lane offset of that port) - s(m+1)`,
so that the branch sits near the port lane. [folklore] -/
def passed (c : Site 2) (v : ℤˣ) (b : ℤ) : Prop :=
  Y.lane c (latDir e (decide ((v : ℤ) = 1))) ≤ (sgOf e : ℤ) * 0 + b + (sgOf e : ℤ) * (Y.m + 1) ∧ (sgOf e : ℤ) = 1 ∨
    b - (Y.m + 1) ≤ Y.lane c (latDir e (decide ((v : ℤ) = 1))) ∧ (sgOf e : ℤ) = -1

/-- The first index `k ≤ N` satisfying `p` (or `N`). [folklore] -/
def firstIdx (p : ℕ → Prop) (N : ℕ) : ℕ := Nat.find (⟨N, Or.inr rfl⟩ : ∃ k, p k ∨ k = N)

/-- **Schedules.** All decisions along a segment depend on the index of the brick within the segment
and on the segment's first brick only (a top stacking advances by exactly `ℓ`): the riser turns at
`riserLen`, the jog at `jogLen`, the trunk places its branch bricks at the indices `brIdx w`, and a
leg along `e'` (the trunk or a branch) ends at `legLen`. [folklore] -/
def riserLen (b₀ : ℤ) : ℕ := firstIdx (fun k => fits Y (b₀ + riseDir Y e τ * (k * Y.ell)) (riseDir Y e τ) (Y.zOf e)) Y.Rmax

/-- The jog turns forward at this index (lateral window fits the trunk lane band). [folklore] -/
def jogLen (bf : ℤ) : ℕ :=
  firstIdx (fun k => fits Y (bf + (jogDir a e : ℤ) * (k * Y.ell)) (jogDir a e) (Y.lane (tgtCell a e) e)) Y.Rmax

/-- The trunk places the branch brick of lateral sign `w` off its brick of this index. [folklore] -/
def brIdx (w : ℤˣ) (be : ℤ) : ℕ := firstIdx (fun k => passed Y e (tgtCell a e) w (be + (sgOf e : ℤ) * (k * Y.ell))) Y.Rmax

/-- A leg along `e'` from base coordinate `b` has room for bricks of index `< legLen`. [folklore] -/
def legLen (e' : MDir) (b : ℤ) : ℕ := firstIdx (fun k => ¬roomT Y (tgtCell a e) e' (b + (sgOf e' : ℤ) * (k * Y.ell))) Y.Rmax

/-- The steering request of the trunk at index `k`: towards `v₁` on `[n₁ - P', n₁)`, away on
`[n₁, n₁ + P')`, towards `-v₁` on `[n₂ - P', n₂)`, away on `[n₂, n₂ + P')`, free (`0`) otherwise.
[cite: GrimmettPercolation1999, §7.3 p. 173 (D)] -/
def trunkForce (n₁ n₂ k : ℕ) : ℤ :=
  let v₁ : ℤ := (br1Sign e : ℤ)
  if k < n₁ ∧ n₁ ≤ k + Y.Pw then v₁
  else if n₁ ≤ k ∧ k < n₁ + Y.Pw then -v₁
  else if k < n₂ ∧ n₂ ≤ k + Y.Pw then -v₁
  else if n₂ ≤ k ∧ k < n₂ + Y.Pw then v₁
  else 0

/-- The number of forced trunk steps before index `k`. [folklore] -/
def nForced (n₁ n₂ k : ℕ) : ℕ := ((List.range k).filter fun j => trunkForce Y e n₁ n₂ j ≠ 0).length

/-- The number of forced (pre-steered) riser steps before index `k`, for a riser turning at `n`. [folklore] -/
def nForcedR (n k : ℕ) : ℕ := ((List.range k).filter fun j => n ≤ j + Y.Pw).length

/-- **The decision function**: the next act, the slot of its record, and the next phase; `none` when
the attempt is complete (or stuck). Decisions are by phase, by the index of the newest brick within
its segment, and by the schedules of the segment's first brick. [cite: GrimmettPercolation1999, §7.3 pp. 171–174] -/
def step (st : RS d) : Option (Act d × Slot × Phase) :=
  let c := tgtCell a e
  let ae := axOf hd e
  let af := latOf hd e
  let a0 := ax0 hd
  let s : ℤˣ := sgOf e
  let u : ℤ := riseDir Y e τ
  let v : ℤˣ := jogDir a e
  let y : ℤ := Y.lane c e
  let v₁ : ℤˣ := br1Sign e
  match st.ph with
  | Phase.segA =>
    match st.sA with
    | [] => some (Act.first, Slot.toA, Phase.segA)
    | r :: _ =>
      if st.sA.length ≤ Y.Pw then
        -- pre-steer: vertically towards the riser if there is one, else sideways towards the jog
        let sg₀ := toward (nomA hd Y e τ) r.1.b
        some (Act.top r (if u = 0 then force sg₀ af v else force sg₀ a0 u), Slot.toA, Phase.segA)
      else if u = 0 then
        some (Act.side r af v (force (toward (nomT hd Y e y) r.1.b) ae s), Slot.toJ, Phase.segJ)
      else
        some (Act.side r a0 (if u = 1 then 1 else -1) (toward (nomA hd Y e τ) r.1.b), Slot.toR, Phase.segR)
  | Phase.segR =>
    match st.sR, st.sR.getLast? with
    | r :: _, some r₀ =>
      let k := st.sR.length - 1
      let n := riserLen Y e τ (r₀.1.b a0)
      if n ≤ k then
        some (Act.side r af v (force (toward (nomT hd Y e y) r.1.b) ae s), Slot.toJ, Phase.segJ)
      else
        -- forced forward along `e` (whole riser); pre-steered towards the jog side on the last `P'` bricks
        let sg₀ := force (toward (nomA hd Y e τ) r.1.b) ae s
        some (Act.top r (if n ≤ k + Y.Pw then force sg₀ af v else sg₀), Slot.toR, Phase.segR)
    | _, _ => none
  | Phase.segJ =>
    match st.sJ, st.sJ.getLast? with
    | r :: _, some r₀ =>
      let k := st.sJ.length - 1
      if jogLen Y a e (r₀.1.b af) ≤ k then
        some (Act.side r ae s (toward (nomT hd Y e y) r.1.b), Slot.toT, Phase.segT)
      else
        some (Act.top r (force (toward (nomT hd Y e y) r.1.b) ae s), Slot.toJ, Phase.segJ)
    | _, _ => none
  | Phase.segT =>
    match st.sT, st.sT.getLast? with
    | r :: _, some r₀ =>
      let k := st.sT.length - 1
      let y₀ : ℤ := r₀.1.b af
      let n₁ := brIdx Y a e v₁ (r₀.1.b ae)
      let n₂ := brIdx Y a e (-v₁) (r₀.1.b ae)
      let nE := legLen Y a e e (r₀.1.b ae)
      if st.g1 = none ∧ n₁ ≤ k then
        some (Act.side r af v₁ (toward (nomT hd Y e y₀) r.1.b), Slot.toG1, Phase.segT)
      else if st.g1 ≠ none ∧ st.g2 = none ∧ n₂ ≤ k then
        some (Act.side r af (-v₁) (toward (nomT hd Y e y₀) r.1.b), Slot.toG2, Phase.segT)
      else if k < nE then
        let w := trunkForce Y e n₁ n₂ k
        let sg₀ := toward (nomT hd Y e y₀) r.1.b
        some (Act.top r (if w = 0 then sg₀ else force sg₀ af w), Slot.toT, Phase.segT)
      else
        match st.g1 with
        | none => none
        | some g =>
          if st.g2 ≠ none ∧ 0 < legLen Y a e (latDir e (decide ((v₁ : ℤ) = 1))) (g.1.b af) then
            some (Act.top g (toward (Function.update (nomT hd Y e y) ae (g.1.b ae)) g.1.b), Slot.toB1, Phase.segB1)
          else none
    | _, _ => none
  | Phase.segB1 =>
    match st.sB1, st.g1 with
    | r :: _, some g =>
      if st.sB1.length < legLen Y a e (latDir e (decide ((v₁ : ℤ) = 1))) (g.1.b af) then
        some (Act.top r (toward (Function.update (nomT hd Y e y) ae (g.1.b ae)) r.1.b), Slot.toB1, Phase.segB1)
      else
        match st.g2 with
        | none => none
        | some g' =>
          if 0 < legLen Y a e (latDir e (decide ((v₁ : ℤ) ≠ 1))) (g'.1.b af) then
            some (Act.top g' (toward (Function.update (nomT hd Y e y) ae (g'.1.b ae)) g'.1.b), Slot.toB2, Phase.segB2)
          else none
    | _, _ => none
  | Phase.segB2 =>
    match st.sB2, st.g2 with
    | r :: _, some g =>
      if st.sB2.length < legLen Y a e (latDir e (decide ((v₁ : ℤ) ≠ 1))) (g.1.b af) then
        some (Act.top r (toward (Function.update (nomT hd Y e y) ae (g.1.b ae)) r.1.b), Slot.toB2, Phase.segB2)
      else none
    | _, _ => none
  | Phase.done => none

/-- Updating the state by the record of the act just emitted. [folklore] -/
def update (st : RS d) (r : BrickRec d) : RS d :=
  match step hd Y a e τ st with
  | none => st
  | some (_, slot, ph') => { st.put slot r with ph := ph' }

/-- **The state of a history** (newest record first): fold from the oldest record. [folklore] -/
def foldState (h : BrickHist d) : RS d := h.foldr (fun r st => update hd Y a e τ st r) RS.init

omit [NeZero d] in
/-- Unfolding the state of a longer history. [folklore] -/
theorem foldState_cons (r : BrickRec d) (h : BrickHist d) :
    foldState hd Y a e τ (r :: h) = update hd Y a e τ (foldState hd Y a e τ h) r := rfl

/-- **The plan of the tall gait**: the next placement. [cite: GrimmettPercolation1999, §7.3 pp. 171–174] -/
def tallNext (h : BrickHist d) : Option (BrickPos d) :=
  (step hd Y a e τ (foldState hd Y a e τ h)).map fun x => placeOf hd Y hL hH e τ x.1

/-- The exit token beyond the last brick of a leg (its top exit, steering immaterial), with source `e`. [folklore] -/
def exitTok (r : BrickRec d) : TTok d := ⟨topExit hL hH r (toward (nomT hd Y e (Y.lane (tgtCell a e) e)) r.1.b), r.1.a, some e⟩

/-- **The outcome of the tall gait**: when the second branch is complete, the three exit tokens
(straight: beyond the trunk; lateral: beyond the branches); the token towards the source is never
used and set to the straight one. [cite: GrimmettPercolation1999, §7.3 p. 174] -/
def tallFinish (h : BrickHist d) : Option (MDir → TTok d) :=
  let st := foldState hd Y a e τ h
  match st.ph, step hd Y a e τ st, st.sT, st.sB1, st.sB2 with
  | Phase.segB2, none, rT :: _, r1 :: _, r2 :: _ =>
    some fun e' =>
      if e' = latDir e (decide ((br1Sign e : ℤ) = 1)) then exitTok hd Y hL hH a e r1
      else if e' = latDir e (decide ((br1Sign e : ℤ) ≠ 1)) then exitTok hd Y hL hH a e r2
      else exitTok hd Y hL hH a e rT
  | _, _, _, _, _ => none

end Plan

end BGNd

end Percolation.Literature

end
