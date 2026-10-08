import Percolation.Literature.TallInv
import Percolation.Util.Linter

/-!
# The tall gait, III: the invariant of the run state

The invariant `BGNd.TallInv` of the run state of the
plan `TallRoute.lean` (block construction of Grimmett, *Percolation*, 2nd ed. (1999), §7.3, Lemma
(7.52)): for each segment, the list is grown by top steps, its first brick is the prescribed turn
off the previous segment, its length respects the schedule, the forced windows are steered, and
every brick obeys the positional bounds (height within `ρ_v` of its layer, lateral within the tube,
remaining coordinates within `L'`). This file only STATES things: token admissibility `TAdm`, the
phase read off the segments (`phaseOf`), the per-segment invariants `InvA`, `InvR`, `InvJ`, `InvT`,
`InvB` (with the auxiliary `riseUnit`, `entryLast`, `n1Of`, `n2Of`) and their conjunction `TallInv`,
plus two list lemmas. The invariant is established for the initial state and shown preserved by each
kind of act in the sequel (`TallInvA.lean` … `TallStep.lean`).

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §7.3 pp. 172–174, (A)–(D).
-/

noncomputable section

namespace Percolation.Literature

open LatticeModels Contour
open scoped Classical

namespace BGNd

variable {d : ℕ} [NeZero d]

/-- The oldest record is the last element. [folklore] -/
theorem getLast?_eq_recOf {l : List (BrickRec d)} (hl : l ≠ []) : l.getLast? = some (recOf l 0) := by
  rw [List.getLast?_eq_getElem?]
  unfold recOf
  rw [List.getElem?_reverse (by have := List.length_pos_of_ne_nil hl; omega)]
  have hlen := List.length_pos_of_ne_nil hl
  rw [Nat.sub_zero, List.getElem?_eq_getElem (by omega)]
  rfl

section Inv

variable (hd : 3 ≤ d) (Y : TallLayout) (hL : Y.m + 1 ≤ Y.L) (hH : 2 * Y.m + 2 ≤ Y.H) (a : Site 2) (e : MDir) (τ : TTok d)

/-- **Admissible tokens** for the attempt along `(a, e)`: the seed is orthogonal to `e`, one step
inside the cell `a` before its face towards `e` (within `ℓ` of the last plane), laterally within
`ρ_p` of the lane, vertically within `ρ_v` of its layer, and within `L'` of `0` in the remaining
coordinates; initial tokens only at the origin cell. [cite: GrimmettPercolation1999, §7.3 p. 174] -/
structure TAdm : Prop where
  ax_eq : τ.ax = axOf hd e
  longit : Y.Dh - Y.ell ≤ (sgOf e : ℤ) * (τ.pos (axOf hd e) - Y.ctr a e.1) ∧ (sgOf e : ℤ) * (τ.pos (axOf hd e) - Y.ctr a e.1) ≤ Y.Dh - 1
  lateral : |τ.pos (latOf hd e) - Y.lane a e| ≤ Y.ρp
  height : |τ.pos (ax0 hd) - Y.zOf (τ.src.getD e)| ≤ Y.ρv
  other : ∀ j, j ≠ axOf hd e → j ≠ latOf hd e → j ≠ ax0 hd → |τ.pos j| ≤ Y.Lp
  src_none : τ.src = none → a = 0

/-- The riser direction as a unit (junk `1` when there is no riser). [folklore] -/
def riseUnit : ℤˣ := if riseDir Y e τ = -1 then -1 else 1

/-- **The phase is determined by which segments have been started.** [folklore] -/
def phaseOf (st : RS d) : Phase :=
  if st.sB2 ≠ [] then Phase.segB2 else if st.sB1 ≠ [] then Phase.segB1 else if st.sT ≠ [] then Phase.segT
  else if st.sJ ≠ [] then Phase.segJ else if st.sR ≠ [] then Phase.segR else Phase.segA

/-- Invariant of segment `A` (the brick on the token and the pre-steered entry leg). [cite: GrimmettPercolation1999, §7.3 pp. 172–173] -/
structure InvA (sA : List (BrickRec d)) (doneA : Prop) : Prop where
  len : sA.length ≤ Y.Pw + 1
  full : doneA → sA.length = Y.Pw + 1
  grown : sA ≠ [] → Grown hL hH sA
  zero : sA ≠ [] → legOf sA 0 = ⟨axOf hd e, sgOf e, τ.pos⟩
  lat : riseDir Y e τ ≠ 0 → ∀ k < sA.length, |(legOf sA k).b (latOf hd e) - τ.pos (latOf hd e)| ≤ Y.Lp
  lat0 : riseDir Y e τ = 0 → ∀ k < sA.length,
    0 ≤ (jogDir a e : ℤ) * ((legOf sA k).b (latOf hd e) - τ.pos (latOf hd e)) ∧
      (jogDir a e : ℤ) * ((legOf sA k).b (latOf hd e) - τ.pos (latOf hd e)) ≤ k * Y.Lp
  latst : riseDir Y e τ = 0 → Steered (latOf hd e) (jogDir a e) 0 (sA.length - 1) (legOf sA)
  oth : ∀ k < sA.length, ∀ j, j ≠ axOf hd e → j ≠ latOf hd e → j ≠ ax0 hd → |(legOf sA k).b j| ≤ Y.Lp
  ht0 : riseDir Y e τ = 0 → ∀ k < sA.length, |(legOf sA k).b (ax0 hd) - Y.zOf e| ≤ Y.ρv
  ht : riseDir Y e τ ≠ 0 → ∀ k < sA.length,
    0 ≤ riseDir Y e τ * ((legOf sA k).b (ax0 hd) - τ.pos (ax0 hd)) ∧
      riseDir Y e τ * ((legOf sA k).b (ax0 hd) - τ.pos (ax0 hd)) ≤ k * Y.Lp
  steer : riseDir Y e τ ≠ 0 → Steered (ax0 hd) (riseDir Y e τ) 0 (sA.length - 1) (legOf sA)

/-- Invariant of the riser `R`. [cite: GrimmettPercolation1999, §7.3 pp. 172–173] -/
structure InvR (sA sR : List (BrickRec d)) (doneR : Prop) : Prop where
  nil : riseDir Y e τ = 0 → sR = []
  prev : sR ≠ [] → sA.length = Y.Pw + 1
  grown : sR ≠ [] → Grown hL hH sR
  turn : sR ≠ [] → IsTurn Y.m Y.L Y.H (axOf hd e) (sgOf e) (ax0 hd) (riseUnit Y e τ) (legOf sA Y.Pw) (legOf sR 0)
  sched : ∀ k, k + 1 < sR.length → k < riserLen Y e τ ((legOf sR 0).b (ax0 hd))
  done : doneR → riseDir Y e τ ≠ 0 → sR ≠ [] ∧ riserLen Y e τ ((legOf sR 0).b (ax0 hd)) ≤ sR.length - 1
  fwd : Steered (axOf hd e) (sgOf e) 0 (sR.length - 1) (legOf sR)
  lat : ∀ k < sR.length, |(legOf sR k).b (latOf hd e) - τ.pos (latOf hd e)| ≤
    Y.Lp + nForcedR Y (riserLen Y e τ ((legOf sR 0).b (ax0 hd))) k * Y.Lp
  latst : Steered (latOf hd e) (jogDir a e) (riserLen Y e τ ((legOf sR 0).b (ax0 hd)) - Y.Pw) (sR.length - 1) (legOf sR)
  oth : ∀ k < sR.length, ∀ j, j ≠ axOf hd e → j ≠ latOf hd e → j ≠ ax0 hd → |(legOf sR k).b j| ≤ Y.Lp

/-- The last brick of the entry segment (`A` if there is no riser, else `R`), off which the jog turns. [folklore] -/
def entryLast (sA sR : List (BrickRec d)) : BrickPos d :=
  if riseDir Y e τ = 0 then legOf sA (sA.length - 1) else legOf sR (sR.length - 1)

/-- Invariant of the jog `J`. [cite: GrimmettPercolation1999, §7.3 pp. 172–173] -/
structure InvJ (sA sR sJ : List (BrickRec d)) (doneJ : Prop) : Prop where
  prevA : sJ ≠ [] → sA.length = Y.Pw + 1
  prevR : sJ ≠ [] → riseDir Y e τ ≠ 0 → sR ≠ [] ∧ riserLen Y e τ ((legOf sR 0).b (ax0 hd)) ≤ sR.length - 1
  grown : sJ ≠ [] → Grown hL hH sJ
  turn : sJ ≠ [] → IsTurn Y.m Y.L Y.H (if riseDir Y e τ = 0 then axOf hd e else ax0 hd)
    (if riseDir Y e τ = 0 then sgOf e else riseUnit Y e τ) (latOf hd e) (jogDir a e) (entryLast Y e τ sA sR) (legOf sJ 0)
  sched : ∀ k, k + 1 < sJ.length → k < jogLen Y a e ((legOf sJ 0).b (latOf hd e))
  done : doneJ → sJ ≠ [] ∧ jogLen Y a e ((legOf sJ 0).b (latOf hd e)) ≤ sJ.length - 1
  fwd : Steered (axOf hd e) (sgOf e) 0 (sJ.length - 1) (legOf sJ)
  fwd0 : sJ ≠ [] → 0 ≤ (sgOf e : ℤ) * ((legOf sJ 0).b (axOf hd e) - (entryLast Y e τ sA sR).b (axOf hd e))
  ht : ∀ k < sJ.length, |(legOf sJ k).b (ax0 hd) - Y.zOf e| ≤ Y.ρv
  oth : ∀ k < sJ.length, ∀ j, j ≠ axOf hd e → j ≠ latOf hd e → j ≠ ax0 hd → |(legOf sJ k).b j| ≤ Y.Lp

/-- The first branch index of a trunk started at `T₀`. [folklore] -/
def n1Of (sT : List (BrickRec d)) : ℕ := brIdx Y a e (br1Sign e) ((legOf sT 0).b (axOf hd e))
/-- The second branch index. [folklore] -/
def n2Of (sT : List (BrickRec d)) : ℕ := brIdx Y a e (-br1Sign e) ((legOf sT 0).b (axOf hd e))

/-- Invariant of the trunk `T` and the two branch bricks. [cite: GrimmettPercolation1999, §7.3 pp. 172–174] -/
structure InvT (sJ sT : List (BrickRec d)) (g1 g2 : Option (BrickRec d)) (doneT : Prop) : Prop where
  prev : sT ≠ [] → sJ ≠ [] ∧ jogLen Y a e ((legOf sJ 0).b (latOf hd e)) ≤ sJ.length - 1
  gnil : sT = [] → g1 = none ∧ g2 = none
  grown : sT ≠ [] → Grown hL hH sT
  turn : sT ≠ [] → IsTurn Y.m Y.L Y.H (latOf hd e) (jogDir a e) (axOf hd e) (sgOf e) (legOf sJ (sJ.length - 1)) (legOf sT 0)
  fit : sT ≠ [] → |(legOf sT 0).b (latOf hd e) - Y.lane (tgtCell a e) e| ≤ Y.ell
  sched : ∀ k, k + 1 < sT.length → k < legLen Y a e e ((legOf sT 0).b (axOf hd e))
  done : doneT → sT ≠ [] ∧ legLen Y a e e ((legOf sT 0).b (axOf hd e)) ≤ sT.length - 1 ∧ g1 ≠ none
  lat : ∀ k < sT.length, |(legOf sT k).b (latOf hd e) - (legOf sT 0).b (latOf hd e)| ≤
    Y.Lp + nForced Y e (n1Of hd Y a e sT) (n2Of hd Y a e sT) k * Y.Lp
  steer : ∀ k, k + 1 < sT.length →
    0 ≤ trunkForce Y e (n1Of hd Y a e sT) (n2Of hd Y a e sT) k * ((legOf sT (k + 1)).b (latOf hd e) - (legOf sT k).b (latOf hd e))
  ht : ∀ k < sT.length, |(legOf sT k).b (ax0 hd) - Y.zOf e| ≤ Y.ρv
  oth : ∀ k < sT.length, ∀ j, j ≠ axOf hd e → j ≠ latOf hd e → j ≠ ax0 hd → |(legOf sT k).b j| ≤ Y.Lp
  g1_none : g1 = none → sT.length ≤ n1Of hd Y a e sT + 1
  g1_some : ∀ g, g1 = some g → n1Of hd Y a e sT < sT.length ∧
    IsTurn Y.m Y.L Y.H (axOf hd e) (sgOf e) (latOf hd e) (br1Sign e) (legOf sT (n1Of hd Y a e sT)) g.1 ∧
      |g.1.b (ax0 hd) - Y.zOf e| ≤ Y.ρv ∧ ∀ j, j ≠ axOf hd e → j ≠ latOf hd e → j ≠ ax0 hd → |g.1.b j| ≤ Y.Lp
  g2_none : g2 = none → g1 ≠ none → sT.length ≤ n2Of hd Y a e sT + 1
  g2_g1 : g2 ≠ none → g1 ≠ none
  g2_some : ∀ g, g2 = some g → n2Of hd Y a e sT < sT.length ∧
    IsTurn Y.m Y.L Y.H (axOf hd e) (sgOf e) (latOf hd e) (-br1Sign e) (legOf sT (n2Of hd Y a e sT)) g.1 ∧
      |g.1.b (ax0 hd) - Y.zOf e| ≤ Y.ρv ∧ ∀ j, j ≠ axOf hd e → j ≠ latOf hd e → j ≠ ax0 hd → |g.1.b j| ≤ Y.Lp

/-- Invariant of a branch leg `sB` grown from the branch brick `g` towards the lateral direction of sign `w`. [cite: GrimmettPercolation1999, §7.3 pp. 172–174] -/
structure InvB (w : ℤˣ) (g : Option (BrickRec d)) (sB : List (BrickRec d)) (doneB : Prop) : Prop where
  prev : sB ≠ [] → g ≠ none
  grown : ∀ r, g = some r → sB ≠ [] → Grown hL hH (sB ++ [r])
  sched : ∀ r, g = some r → ∀ k, k < sB.length → k < legLen Y a e (latDir e (decide ((w : ℤ) = 1))) (r.1.b (latOf hd e))
  done : ∀ r, g = some r → doneB → sB ≠ [] ∧ legLen Y a e (latDir e (decide ((w : ℤ) = 1))) (r.1.b (latOf hd e)) ≤ sB.length
  lng : ∀ r, g = some r → ∀ k ≤ sB.length, |(legOf (sB ++ [r]) k).b (axOf hd e) - r.1.b (axOf hd e)| ≤ Y.Lp
  ht : ∀ r, g = some r → ∀ k ≤ sB.length, |(legOf (sB ++ [r]) k).b (ax0 hd) - Y.zOf e| ≤ Y.ρv
  oth : ∀ r, g = some r → ∀ k ≤ sB.length, ∀ j, j ≠ axOf hd e → j ≠ latOf hd e → j ≠ ax0 hd →
    |(legOf (sB ++ [r]) k).b j| ≤ Y.Lp

/-- **The invariant of the run state.** [cite: GrimmettPercolation1999, §7.3 pp. 172–174] -/
structure TallInv (st : RS d) : Prop where
  ph_eq : st.ph = phaseOf st
  invA : InvA hd Y hL hH a e τ st.sA (st.sR ≠ [] ∨ st.sJ ≠ [])
  invR : InvR hd Y hL hH a e τ st.sA st.sR (st.sJ ≠ [])
  invJ : InvJ hd Y hL hH a e τ st.sA st.sR st.sJ (st.sT ≠ [])
  invT : InvT hd Y hL hH a e st.sJ st.sT st.g1 st.g2 (st.sB1 ≠ [])
  trunk_done_B1 : st.sB1 ≠ [] → st.sT ≠ []
  invB1 : InvB hd Y hL hH a e (br1Sign e) st.g1 st.sB1 (st.sB2 ≠ [])
  invB2 : InvB hd Y hL hH a e (-br1Sign e) st.g2 st.sB2 False
  B2_prev : st.sB2 ≠ [] → st.sB1 ≠ [] ∧
    ∀ r, st.g1 = some r → legLen Y a e (latDir e (decide ((br1Sign e : ℤ) = 1))) (r.1.b (latOf hd e)) ≤ st.sB1.length
  B1_g2 : st.sB1 ≠ [] → st.g2 ≠ none

end Inv

end BGNd

end Percolation.Literature

end
