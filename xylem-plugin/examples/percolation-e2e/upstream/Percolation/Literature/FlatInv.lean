import Percolation.Literature.FlatRise
import Percolation.Util.Linter

/-!
# The flat gait, VI: the invariant of the run state

The invariant `FlatInv` of the run state `FS` of the
flat gait (`FlatRoute.lean`; Grimmett, *Percolation*, 2nd ed. (1999), §7.3 pp. 171–174, case
`H < L`): the segments are filled in order (a nonempty segment has all earlier segments complete);
segment `0` is the lead-in, a diagonal leg of at most three plates from the first plate on the
token; segment `1` is a riser off its head; the preamble and
the jog, trunk and branch segments are diagonal legs of the prescribed signs, each starting by the
prescribed hop off the head of the prescribed earlier segment; the
turn segments are turns (Grimmett's (C)) off the heads of the legs before them. This file states
the invariant (`SegOK`, `FlatInv`), the token admissibility `FTAdm`, and proves the frame facts
about the directions (`flipIdx_eB`, `dsg_lat`, `latDir_fst_ne`, `oth_p1_p2`) and the invariant of
the initial state (`segOK_nil`, `flatInv_init`).

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §7.3 pp. 171–174.
-/

noncomputable section

namespace Percolation.Literature

open LatticeModels Contour
open scoped Classical

namespace BGNd

variable {d : ℕ}

/-! ## Directions: kept and flipped indices -/

section Dirs

/-- The flipped index of the first lateral direction is `0`, of the second `1`. [folklore] -/
theorem flipIdx_eB (e : MDir) : flipIdx e (eB1 e) = 0 ∧ flipIdx e (eB2 e) = 1 := by
  unfold flipIdx eB1 eB2 sgOf latDir
  obtain ⟨i, b⟩ := e
  cases b <;> simp

/-- **The fine signs of a lateral direction**: equal to those of `e` on the kept index, opposite on
the flipped index. [folklore] -/
theorem dsg_lat (e : MDir) (b : Bool) :
    dsg (latDir e b) (keepIdx e (latDir e b)) = dsg e (keepIdx e (latDir e b)) ∧
      dsg (latDir e b) (flipIdx e (latDir e b)) = -dsg e (flipIdx e (latDir e b)) := by
  unfold keepIdx flipIdx dsg latDir sgOf oth
  obtain ⟨i, c⟩ := e
  fin_cases i <;> cases b <;> cases c <;> decide

/-- The macro-axis of a lateral direction is the other one. [folklore] -/
theorem latDir_fst_ne (e : MDir) (b : Bool) : (latDir e b).1 ≠ e.1 := by
  simp only [latDir]; intro h; have := congrArg Fin.val h; simp at this; have := e.1.isLt; omega

end Dirs

/-! ## Admissible tokens -/

section Adm

variable (hd : 3 ≤ d) (Y : FlatLayout) (a : Site 2) (e : MDir) (τ : TTok d)

/-- **Admissible tokens** for the attempt `(a, e)` of the flat gait: the axis is a plane axis; the
forward diagonal coordinate is in the window `[D - 2U, D - 1]` before the face of the target cell;
the lateral one within `ρ_p` of the lane; the height within `ρ_v` of the source layer; idle
coordinates within `L'`; a source is recorded. [cite: GrimmettPercolation1999, §7.3 pp. 171–174] -/
structure FTAdm : Prop where
  ax_plane : τ.ax = pl hd 0 ∨ τ.ax = pl hd 1
  longit : Y.Df - 2 * Y.U ≤ (sgOf e : ℤ) * (Uc hd e.1 τ.pos - Y.ctr a e.1) ∧ (sgOf e : ℤ) * (Uc hd e.1 τ.pos - Y.ctr a e.1) ≤ Y.Df - 1
  lateral : |Uc hd (latDir e true).1 τ.pos - Y.lane a e| ≤ Y.ρp
  height : ∀ d', τ.src = some d' → |τ.pos (ax0 hd) - Y.zOf d'| ≤ Y.ρv
  idle : ∀ i, Idle hd i → |τ.pos i| ≤ Y.Lp
  src_some : τ.src ≠ none

end Adm

/-! ## The invariant -/

section Inv

variable [NeZero d] (hd : 3 ≤ d) (Y : FlatLayout) (a : Site 2) (e : MDir) (τ : TTok d) (ej : MDir)

/-- The first plate: on the token's seed, with the token's axis and the fine sign of `e`. [folklore] -/
def firstPlate : BrickPos d := ⟨τ.ax, dsg e (plIdx hd τ.ax), τ.pos⟩

/-- The riser direction as a Boolean height request: up iff the riser climbs. [folklore] -/
def zbOf : Bool := decide ((friseDir hd Y e τ : ℤ) = 1)

/-- The start plate of the riser: the head of the lead-in (the first plate if the lead-in is empty). [folklore] -/
def rstart (ls : List (BrickRec d)) : BrickPos d := match ls.head? with | some s => s.1 | none => firstPlate hd e τ

/-- The kept index of the jog turn towards `ej`. [folklore] -/
def pJ : Fin 2 := keepIdx e ej
/-- The kept index of the first fork. [folklore] -/
def p1 : Fin 2 := keepIdx e (eB1 e)
/-- The kept index of the second fork. [folklore] -/
def p2 : Fin 2 := keepIdx e (eB2 e)

omit [NeZero d] in
/-- The flipped indices of the forks. [folklore] -/
theorem oth_p1_p2 : oth (p1 e) = flipIdx e (eB1 e) ∧ oth (p2 e) = flipIdx e (eB2 e) := ⟨oth_oth _, oth_oth _⟩

/-- **The invariant of one segment**, in terms of its records `l` and the records `ls` of the
segment it starts from (both newest first). [cite: GrimmettPercolation1999, §7.3 pp. 171–174] -/
def SegOK (k : Fin 13) (l ls : List (BrickRec d)) : Prop :=
  match k.val with
  | 0 => l ≠ [] → DiagLeg hd Y e (dsg e) (some (zbOf hd Y e τ)) (plIdx hd τ.ax) l ∧ legOf l 0 = firstPlate hd e τ ∧ l.length ≤ 3
  | 1 => l ≠ [] → Riser hd Y (dsg e) (friseDir hd Y e τ) (plIdx hd τ.ax) (rstart hd e τ ls) l
  | 2 => l ≠ [] → ∃ s ∈ ls.head?, ∃ q, DiagLeg hd Y e (dsg e) none q l ∧ DHop hd Y e (dsg e) none q s.1 (legOf l 0)
  | 3 => l ≠ [] → ∃ s ∈ ls.head?, Turn hd Y e (dsg e) (dsg ej) (pJ e ej) s.1 l
  | 4 => l ≠ [] → ∃ s ∈ ls.head?, DiagLeg hd Y e (dsg ej) none (pJ e ej) l ∧ DHop hd Y e (dsg ej) none (pJ e ej) s.1 (legOf l 0)
  | 5 => l ≠ [] → ∃ s ∈ ls.head?, Turn hd Y e (dsg ej) (dsg e) (pJ e ej) s.1 l
  | 6 => l ≠ [] → ∃ s ∈ ls.head?, DiagLeg hd Y e (dsg e) none (pJ e ej) l ∧ DHop hd Y e (dsg e) none (pJ e ej) s.1 (legOf l 0)
  | 7 => l ≠ [] → ∃ s ∈ ls.head?, Turn hd Y e (dsg e) (dsg (eB1 e)) (p1 e) s.1 l
  | 8 => l ≠ [] → ∃ s ∈ ls.head?, ∃ q, DiagLeg hd Y e (dsg e) none q l ∧ DHop hd Y e (dsg e) none q s.1 (legOf l 0)
  | 9 => l ≠ [] → ∃ s ∈ ls.head?, Turn hd Y e (dsg e) (dsg (eB2 e)) (p2 e) s.1 l
  | 10 => l ≠ [] → ∃ s ∈ ls.head?, ∃ q, DiagLeg hd Y e (dsg e) none q l ∧ DHop hd Y e (dsg e) none q s.1 (legOf l 0)
  | 11 => l ≠ [] → ∃ s ∈ ls.head?, DiagLeg hd Y e (dsg (eB1 e)) none (p1 e) l ∧ DHop hd Y e (dsg (eB1 e)) none (p1 e) s.1 (legOf l 0)
  | 12 => l ≠ [] → ∃ s ∈ ls.head?, DiagLeg hd Y e (dsg (eB2 e)) none (p2 e) l ∧ DHop hd Y e (dsg (eB2 e)) none (p2 e) s.1 (legOf l 0)
  | _ => True

/-- **The invariant of the run state of the flat gait**: segments are filled in order, and every
segment satisfies its invariant relative to its start segment (the lead-in: a diagonal leg of at most
three plates off the first plate, `rstart` its head; the riser off `rstart`). [cite: GrimmettPercolation1999, §7.3 pp. 171–174] -/
structure FlatInv (st : FS d) : Prop where
  /-- segments are filled in order -/
  order : ∀ i j : Fin 13, j < i → st.segs i ≠ [] → complete' hd Y a e τ (eJOf hd Y a e τ st) j (st.segs j)
  /-- every segment satisfies its invariant -/
  segOK : ∀ k : Fin 13, SegOK hd Y e τ (eJOf hd Y a e τ st) k (st.segs k) (st.segs (startOf k))
  /-- no segment was complete before its last record: every proper earlier stage is incomplete -/
  nostop : ∀ (k : Fin 13) (l : List (BrickRec d)), l <:+ st.segs k → l ≠ st.segs k → ¬complete' hd Y a e τ (eJOf hd Y a e τ st) k l

/-- **An empty segment satisfies its invariant.** [folklore] -/
theorem segOK_nil (ej : MDir) (k : Fin 13) (ls : List (BrickRec d)) : SegOK hd Y e τ ej k [] ls := by
  unfold SegOK
  have hk := k.isLt
  rcases k with ⟨k, _⟩
  simp only
  interval_cases k
  all_goals exact fun h => absurd rfl h

/-- **The initial state satisfies the invariant.** [folklore] -/
theorem flatInv_init : FlatInv hd Y a e τ FS.init :=
  ⟨fun _ _ _ h => absurd rfl h, fun k => segOK_nil hd Y e τ _ k _, fun _ _ hl hne => absurd (List.suffix_nil.1 hl) hne⟩

end Inv

end BGNd

end Percolation.Literature

end
