import Percolation.Literature.FlatHops
import Percolation.Util.Linter

/-!
# The flat gait, III b: the plan with a diagonal lead-in

The plan of the flat gait (`FlatRoute.lean`; Grimmett,
*Percolation*, 2nd ed. (1999), §7.3 pp. 171–174, case `H < L`) with one amendment: the first
segment is a **three-plate diagonal lead-in** — the first plate on the token, then two diagonal hops
forwards (the height requested in the riser's direction) — and the riser starts from its last
plate, which has the token's axis again. Two forced forward drifts then separate every later plate
from the plate behind the token (the last plate of the attempt that handed the token on) along the
token's axis, which the first vertical plate of a riser standing directly on the token would not
be. The amended completeness test (`complete'`), current segment (`firstInc'`, `curOf'`), acts
(`segAct'`), step, state and plan (`fstep'`, `fupdate'`, `ffold'`, `flatNext'`) and outcome
(`flatFinish'`) supersede the unprimed ones of `FlatRoute.lean`.

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §7.3 pp. 171–174.
-/

noncomputable section

namespace Percolation.Literature

open LatticeModels Contour
open scoped Classical

namespace BGNd

variable {d : ℕ} [NeZero d] (hd : 3 ≤ d) (Y : FlatLayout) (hL : Y.m + 1 ≤ Y.L) (hH : 2 * Y.m + 2 ≤ Y.H) (a : Site 2) (e : MDir) (τ : TTok d)
variable (ej : MDir)

/-- **A segment is complete** (amended): the lead-in needs three plates; otherwise as `complete`. [folklore] -/
def complete' (i : Fin 13) (l : List (BrickRec d)) : Prop :=
  match kindOf e ej i, l with
  | _, [] => False
  | Kind.first, _ :: _ => 3 ≤ l.length
  | Kind.rise, r :: _ => r.1.a ≠ ax0 hd ∧ ffitsR hd Y e τ r.1.b
  | Kind.pre p, r :: _ => 162 ≤ l.length ∧ r.1.a = pl hd p
  | Kind.turn _, _ :: _ => 2 ≤ l.length
  | Kind.leg, r :: _ => minLenOf i ≤ l.length ∧ legStop hd Y a e ej i r.1.b ∧ ∀ q, legAxisOf e ej i = some q → r.1.a = pl hd q

/-- The first incomplete segment from index `k` on, if any. [folklore] -/
def firstInc' (st : FS d) (k : ℕ) : Option (Fin 13) :=
  if h : k < 13 then (if complete' hd Y a e τ ej ⟨k, h⟩ (st.segs ⟨k, h⟩) then firstInc' st (k + 1) else some ⟨k, h⟩) else none
  termination_by 13 - k

/-- The current segment: the first incomplete one, if any. [folklore] -/
def curOf' (st : FS d) : Option (Fin 13) := firstInc' hd Y a e τ ej st 0

/-- [cite: GrimmettPercolation1999, §7.3 pp. 172–174 (A)–(D), Fig. 7.11] -/
def segAct' (i : Fin 13) (l : List (BrickRec d)) (s₀ : Option (BrickRec d)) : Option (Act d) :=
  let σ := dsg (fdirOf e ej i)
  let zb : Bool := decide ((friseDir hd Y e τ : ℤ) = 1)
  match kindOf e ej i, l, s₀ with
  | Kind.first, [], _ => some Act.first
  | Kind.first, [r], _ => some (diagHop hd Y e σ (some zb) r)
  | Kind.first, [r, _], _ => some (diagHop hd Y e σ (some zb) r)
  | Kind.first, _ :: _ :: _ :: _, _ => none
  -- riser: up from a plane plate, forward (alternating plane axis) from a horizontal one
  | Kind.rise, [], some r => some (hop hd Y e σ none r (ax0 hd) (friseDir hd Y e τ))
  | Kind.rise, r :: tl, s => if r.1.a = ax0 hd then
        let prev := match tl with | r' :: _ => some r' | [] => s
        match prev with
        | some r' => some (hop hd Y e σ none r (pl hd (oth (plIdx hd r'.1.a))) (σ (oth (plIdx hd r'.1.a))))
        | none => none
      else some (hop hd Y e σ none r (ax0 hd) (friseDir hd Y e τ))
  -- preamble and legs: diagonal hops
  | Kind.pre _, [], some r => some (diagHop hd Y e σ none r)
  | Kind.pre _, r :: _, _ => some (diagHop hd Y e σ none r)
  | Kind.leg, [], some r => some (diagHop hd Y e σ none r)
  | Kind.leg, r :: _, _ => some (diagHop hd Y e σ none r)
  -- turn: a top stacking pushed towards the new side, then a hop through the new side face
  | Kind.turn _, [], some r => some (Act.top r (hreq hd Y e σ none r.1.b))
  | Kind.turn p, [r'], _ => some (hop hd Y e σ none r' (pl hd (oth p)) (σ (oth p)))
  | Kind.turn _, _ :: _ :: _, _ => none
  | _, [], none => none

/-- **One step of the plan**: the act of the current segment and where to file its record. [cite: GrimmettPercolation1999, §7.3 pp. 171–174] -/
def fstep' (st : FS d) : Option (Act d × Fin 13) :=
  let ej := eJOf hd Y a e τ st
  match curOf' hd Y a e τ ej st with
  | none => none
  | some i => (segAct' hd Y e τ ej i (st.segs i) (startRec st i)).map fun act => (act, i)

/-- Updating the state by the record of the act just emitted. [folklore] -/
def fupdate' (st : FS d) (r : BrickRec d) : FS d :=
  match fstep' hd Y a e τ st with
  | none => st
  | some (_, i) => st.put i r

/-- **The state of a history** (newest record first). [folklore] -/
def ffold' (h : BrickHist d) : FS d := h.foldr (fun r st => fupdate' hd Y a e τ st r) FS.init

omit [NeZero d] in
/-- Unfolding the state of a longer history. [folklore] -/
theorem ffold'_cons (r : BrickRec d) (h : BrickHist d) : ffold' hd Y a e τ (r :: h) = fupdate' hd Y a e τ (ffold' hd Y a e τ h) r := rfl

/-- **The plan of the flat gait**: the next placement. [cite: GrimmettPercolation1999, §7.3 pp. 171–174] -/
def flatNext' (h : BrickHist d) : Option (BrickPos d) :=
  (fstep' hd Y a e τ (ffold' hd Y a e τ h)).map fun x => fplaceOf hd Y hL hH e τ x.1

/-- **The outcome of the flat gait**: when every segment is complete, the three exit tokens
(straight: beyond trunk 3; lateral: beyond the branches); the token towards the source is the
straight one (never used). [cite: GrimmettPercolation1999, §7.3 p. 174] -/
def flatFinish' (h : BrickHist d) : Option (MDir → TTok d) :=
  let st := ffold' hd Y a e τ h
  match curOf' hd Y a e τ (eJOf hd Y a e τ st) st, st.segs 10, st.segs 11, st.segs 12 with
  | none, rT :: _, r1 :: _, r2 :: _ =>
    some fun e' => if e' = eB1 e then fexitTok hd Y hL hH e (eB1 e) r1
      else if e' = eB2 e then fexitTok hd Y hL hH e (eB2 e) r2 else fexitTok hd Y hL hH e e rT
  | _, _, _, _ => none

end BGNd

end Percolation.Literature

end
