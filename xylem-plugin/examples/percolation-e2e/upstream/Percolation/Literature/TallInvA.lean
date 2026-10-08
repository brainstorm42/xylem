import Percolation.Literature.TallInvariant
import Percolation.Util.Linter

/-!
# The tall gait, IV: admissible layouts, the phase of small states, the initial invariant

For the invariant `TallInv` (`TallInvariant.lean`) of
the plan of the block construction (Grimmett, *Percolation*, 2nd ed. (1999), §7.3, Lemma (7.52)):
the admissible layouts `TallLayout.OK` (`m + 1 ≤ L`, `2m + 2 ≤ H`, tall regime `L + 1 ≤ P (H+1)`, `8
≤ P`) with the first arithmetic facts, the phase read off states whose later segments are empty
(`phaseOf_eq_segA`, `phaseOf_of_nil`, `phaseOf_of_R`, `phaseOf_of_J`), the invariants of empty
segments (`invR_nil`, `invJ_nil`, `invT_nil`, `invB_nil`, `invB_single`), and the invariant of the
initial state (`tallInv_init`). Preservation by the placements follows in `TallInvA2.lean` ff.

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §7.3 pp. 172–174.
-/

noncomputable section

namespace Percolation.Literature

open LatticeModels Contour
open scoped Classical

namespace BGNd

variable {d : ℕ} [NeZero d]

namespace TallLayout

/-- **Usable layouts**: seeds fit in bricks (`m + 1 ≤ L`, `2m + 2 ≤ H`), the regime is tall
(`L + 1 ≤ P ℓ`), and `P ≥ 8`. [cite: GrimmettPercolation1999, §7.3 p. 170] -/
structure OK (Y : TallLayout) : Prop where
  hL : Y.m + 1 ≤ Y.L
  hH : 2 * Y.m + 2 ≤ Y.H
  tall : (Y.L : ℤ) + 1 ≤ Y.P * Y.ell
  hP : 8 ≤ Y.P

variable {Y : TallLayout}

/-- Auxiliary fact `OK.Lp_nonneg`. [folklore] -/
theorem OK.Lp_nonneg (h : Y.OK) : 0 ≤ Y.Lp := by
  have := h.hL; unfold Lp; omega

/-- Auxiliary fact `OK.Lp_le_ρv`. [folklore] -/
theorem OK.Lp_le_ρv (h : Y.OK) : Y.Lp ≤ Y.ρv := by
  unfold ρv ell; have := h.Lp_nonneg; push_cast; omega

end TallLayout

section A

variable (hd : 3 ≤ d) (Y : TallLayout) (hL : Y.m + 1 ≤ Y.L) (hH : 2 * Y.m + 2 ≤ Y.H) (a : Site 2) (e : MDir) (τ : TTok d)

/-! ## The phase -/

omit [NeZero d] in
/-- In phase `A` no later segment has been started. [folklore] -/
theorem phaseOf_eq_segA {st : RS d} (h : phaseOf st = Phase.segA) :
    st.sR = [] ∧ st.sJ = [] ∧ st.sT = [] ∧ st.sB1 = [] ∧ st.sB2 = [] := by
  unfold phaseOf at h
  by_cases h2 : st.sB2 ≠ [] <;> by_cases h1 : st.sB1 ≠ [] <;> by_cases hT : st.sT ≠ [] <;> by_cases hJ : st.sJ ≠ [] <;>
    by_cases hR : st.sR ≠ [] <;> simp_all

omit [NeZero d] in
/-- The phase of a state with only segment `A` started. [folklore] -/
theorem phaseOf_of_nil {st : RS d} (hR : st.sR = []) (hJ : st.sJ = []) (hT : st.sT = []) (h1 : st.sB1 = []) (h2 : st.sB2 = []) :
    phaseOf st = Phase.segA := by
  simp [phaseOf, hR, hJ, hT, h1, h2]

omit [NeZero d] in
/-- The phase of a state in the riser. [folklore] -/
theorem phaseOf_of_R {st : RS d} (hR : st.sR ≠ []) (hJ : st.sJ = []) (hT : st.sT = []) (h1 : st.sB1 = []) (h2 : st.sB2 = []) :
    phaseOf st = Phase.segR := by
  simp [phaseOf, hR, hJ, hT, h1, h2]

omit [NeZero d] in
/-- The phase of a state in the jog. [folklore] -/
theorem phaseOf_of_J {st : RS d} (hJ : st.sJ ≠ []) (hT : st.sT = []) (h1 : st.sB1 = []) (h2 : st.sB2 = []) :
    phaseOf st = Phase.segJ := by
  simp [phaseOf, hJ, hT, h1, h2]

/-! ## Empty segments -/

/-- The riser invariant of an empty riser. [folklore] -/
theorem invR_nil (sA : List (BrickRec d)) {doneR : Prop} (h : doneR → riseDir Y e τ = 0) :
    InvR hd Y hL hH a e τ sA [] doneR where
  nil _ := rfl
  prev h := absurd rfl h
  grown h := absurd rfl h
  turn h := absurd rfl h
  sched k hk := absurd hk (by simp)
  done hd' hu := absurd (h hd') hu
  fwd k _ hk := absurd hk (by simp)
  lat k hk := absurd hk (by simp)
  latst k _ hk := absurd hk (by simp)
  oth k hk := absurd hk (by simp)

/-- The jog invariant of an empty jog. [folklore] -/
theorem invJ_nil (sA sR : List (BrickRec d)) {doneJ : Prop} (h : ¬doneJ) : InvJ hd Y hL hH a e τ sA sR [] doneJ where
  prevA h' := absurd rfl h'
  prevR h' := absurd rfl h'
  grown h' := absurd rfl h'
  turn h' := absurd rfl h'
  sched k hk := absurd hk (by simp)
  done hd' := absurd hd' h
  fwd k _ hk := absurd hk (by simp)
  fwd0 h' := absurd rfl h'
  ht k hk := absurd hk (by simp)
  oth k hk := absurd hk (by simp)

/-- The trunk invariant of an empty trunk. [folklore] -/
theorem invT_nil (sJ : List (BrickRec d)) {doneT : Prop} (h : ¬doneT) : InvT hd Y hL hH a e sJ [] none none doneT where
  prev h' := absurd rfl h'
  gnil _ := ⟨rfl, rfl⟩
  grown h' := absurd rfl h'
  turn h' := absurd rfl h'
  fit h' := absurd rfl h'
  sched k hk := absurd hk (by simp)
  done hd' := absurd hd' h
  lat k hk := absurd hk (by simp)
  steer k hk := absurd hk (by simp)
  ht k hk := absurd hk (by simp)
  oth k hk := absurd hk (by simp)
  g1_none _ := by simp
  g1_some g hg := absurd hg (by simp)
  g2_none _ h' := absurd rfl h'
  g2_g1 h' := absurd rfl h'
  g2_some g hg := absurd hg (by simp)

/-- The branch invariant before the branch brick is placed. [folklore] -/
theorem invB_nil (w : ℤˣ) {doneB : Prop} : InvB hd Y hL hH a e w none [] doneB where
  prev h := absurd rfl h
  grown r hr := absurd hr (by simp)
  sched r hr := absurd hr (by simp)
  done r hr := absurd hr (by simp)
  lng r hr := absurd hr (by simp)
  ht r hr := absurd hr (by simp)
  oth r hr := absurd hr (by simp)

/-- The branch invariant of a branch brick with an empty branch leg. [folklore] -/
theorem invB_single (w : ℤˣ) {g : BrickRec d} {doneB : Prop} (h : ¬doneB) (hht : |g.1.b (ax0 hd) - Y.zOf e| ≤ Y.ρv)
    (hoth : ∀ j, j ≠ axOf hd e → j ≠ latOf hd e → j ≠ ax0 hd → |g.1.b j| ≤ Y.Lp) (hLp : 0 ≤ Y.Lp) :
    InvB hd Y hL hH a e w (some g) [] doneB where
  prev h' := absurd rfl h'
  grown r _ h' := absurd rfl h'
  sched r _ k hk := absurd hk (by simp)
  done r _ hd' := absurd hd' h
  lng r hr k hk := by
    cases hr; have : k = 0 := by simpa using hk
    subst this
    rw [List.nil_append, show legOf [g] 0 = g.1 from legOf_cons_length g [], sub_self, abs_zero]
    exact hLp
  ht r hr k hk := by
    cases hr; have : k = 0 := by simpa using hk
    subst this
    rw [List.nil_append, show legOf [g] 0 = g.1 from legOf_cons_length g []]
    exact hht
  oth r hr k hk := by
    cases hr; have : k = 0 := by simpa using hk
    subst this
    rw [List.nil_append, show legOf [g] 0 = g.1 from legOf_cons_length g []]
    exact hoth

/-! ## The initial state -/

/-- **The invariant holds initially.** [folklore] -/
theorem tallInv_init : TallInv hd Y hL hH a e τ RS.init where
  ph_eq := by simp [RS.init, phaseOf]
  invA :=
    { len := by simp [RS.init]
      full := by simp [RS.init]
      grown := fun h => absurd rfl h
      zero := fun h => absurd rfl h
      lat := fun _ k hk => absurd hk (by simp [RS.init])
      lat0 := fun _ k hk => absurd hk (by simp [RS.init])
      latst := fun _ k _ hk => absurd hk (by simp [RS.init])
      oth := fun k hk => absurd hk (by simp [RS.init])
      ht0 := fun _ k hk => absurd hk (by simp [RS.init])
      ht := fun _ k hk => absurd hk (by simp [RS.init])
      steer := fun _ k _ hk => absurd hk (by simp [RS.init]) }
  invR := invR_nil hd Y hL hH a e τ _ (by simp [RS.init])
  invJ := invJ_nil hd Y hL hH a e τ _ _ (by simp [RS.init])
  invT := invT_nil hd Y hL hH a e _ (by simp [RS.init])
  trunk_done_B1 := by simp [RS.init]
  invB1 := invB_nil hd Y hL hH a e _
  invB2 := invB_nil hd Y hL hH a e _
  B2_prev := by simp [RS.init]
  B1_g2 := by simp [RS.init]

end A

end BGNd

end Percolation.Literature

end
