import Percolation.Literature.BlockKit
import Percolation.Literature.GaitKinematics
import Percolation.Util.Linter

/-!
# Steps of a brick-stacking plan: reading exits off a good record, top steps and side steps

The block construction of Lemma (7.52) of Grimmett,
*Percolation*, 2nd ed. (1999), §7.3, pp. 172–174, places each new brick on a seed found by the
previous one: "(A) … we may choose such a `y_j` according to some fixed ordering of all available such
vertices", "(B) Side stacking", "(D) Steering … by judicious choices of the particular subfacets".
This file turns the exit lemmas of `HalfSpaceHighDimPlaced.lean` into DETERMINISTIC functions of a
good record `(β, o)` (a placement and the open edges observed on its support), as needed by the plans
of a block kit (`BlockKit.lean`):

* `BGNd.topExit r sg`, `BGNd.sideExit r i u sg` — the centre of an open exit seed square of the
  requested kind (top: sign pattern `sg` of the transverse offsets; side: face `x_i = u`, sign pattern
  `sg` of the remaining offsets), chosen by `Classical.choose` from the exit lemmas applied to the
  observed configuration `↑o`; their specifications `topExit_spec`, `sideExit_spec` (position,
  openness of the seed in `↑o`, and an open path in `↑o` from the entry square of `β`);
* `BGNd.tStep r sg`, `BGNd.sStep r i u sg` — the next placement (top stacking: same axis and sign,
  based on the top exit; side stacking: axis `i`, sign `u`, based on the side exit);
* the kinematic relations they satisfy: `tStep` realises the step and wobble of a leg (`IsLeg`) with
  the requested signs (hence `Steered` windows), `sStep` realises a turn (`IsTurn`);
* monotonicity in the configuration: seeds open and paths present in `↑o = ω ∩ supp` are so in `ω`.

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §7.3 pp. 172–174, (A), (B), (D).
-/

noncomputable section

namespace Percolation.Literature

open LatticeModels
open scoped Classical

namespace BGNd

variable {d : ℕ} [NeZero d] {m L H : ℕ}

/-! ## Observed configurations -/

/-- The configuration read off a record: its observed open edges. [folklore] -/
abbrev cfgOf (r : BrickRec d) : BondConfig (Site d) := (↑r.2 : Set (Sym2 (Site d)))

omit [NeZero d] in
/-- An actual observation is part of the configuration: `↑(ω ∩ D) ⊆ ω`. [folklore] -/
theorem cfgOf_obs_subset (β : BrickPos d) (ω : BondConfig (Site d)) (D : Finset (Sym2 (Site d))) :
    cfgOf (β, obs ω D) ⊆ ω := by
  intro z hz
  change z ∈ (↑(obs ω D) : Set (Sym2 (Site d))) at hz
  rw [Finset.mem_coe, mem_obs_iff] at hz
  exact hz.2

omit [NeZero d] in
/-- Seeds are monotone in the configuration. [folklore] -/
theorem IsSeed.mono {ω ω' : BondConfig (Site d)} (h : ω ⊆ ω') {Q : Set (Site d)} (hQ : IsSeed ω Q) : IsSeed ω' Q :=
  fun _ hu _ hv hadj => h (hQ hu hv hadj)

omit [NeZero d] in
/-- Open paths are monotone in the configuration. [folklore] -/
theorem reachable_mono {ω ω' : BondConfig (Site d)} (h : ω ⊆ ω') {x y : Site d} (hxy : (openGraph ω).Reachable x y) :
    (openGraph ω').Reachable x y := by
  refine hxy.mono fun u v huv => ?_
  rw [openGraph_adj] at huv ⊢
  exact ⟨h huv.1, huv.2⟩

/-! ## Exits read off a good record -/

section Exits

variable (hL : m + 1 ≤ L) (hH : 2 * m + 2 ≤ H)
include hL hH

/-- **The top exit** of a good record for the requested sign pattern: the centre of an open seed square
beyond the top (junk `β.b` for a bad record). [cite: GrimmettPercolation1999, §7.3 p. 172 (A)] -/
def topExit (r : BrickRec d) (sg : Fin d → Bool) : Site d :=
  if h : GoodRec m L H r then Classical.choose (exists_top_exit' hL hH (placedC_subset_placedT m L H r.1 h) sg) else r.1.b

/-- **Specification of the top exit.** [cite: GrimmettPercolation1999, §7.3 p. 172 (A)] -/
theorem topExit_spec {r : BrickRec d} (h : GoodRec m L H r) (sg : Fin d → Bool) :
    topExit hL hH r sg r.1.a = r.1.b r.1.a + (r.1.s : ℤ) * ((H : ℤ) + 1) ∧
      (∀ i, i ≠ r.1.a → |topExit hL hH r sg i - r.1.b i| ≤ (L : ℤ) - m - 1 ∧
        (sg i = true → 0 ≤ topExit hL hH r sg i - r.1.b i) ∧ (sg i = false → topExit hL hH r sg i - r.1.b i ≤ 0)) ∧
      IsSeed (cfgOf r) (square r.1.a m (topExit hL hH r sg)) ∧
      ∃ y ∈ square r.1.a m r.1.b, (openGraph (cfgOf r)).Reachable y (topExit hL hH r sg) := by
  unfold topExit
  rw [dif_pos h]
  exact Classical.choose_spec (exists_top_exit' hL hH (placedC_subset_placedT m L H r.1 h) sg)

/-- **The side exit** of a good record through the face `x_i = u` (`i ≠ β.a`) for the requested sign
pattern of the remaining offsets (junk for a bad record or `i = β.a`).
[cite: GrimmettPercolation1999, §7.3 pp. 172–173 (B)] -/
def sideExit (r : BrickRec d) (i : Fin d) (u : ℤˣ) (sg : Fin d → Bool) : Site d :=
  if h : GoodRec m L H r ∧ i ≠ r.1.a then Classical.choose (exists_side_exit' hL hH h.1 h.2 u sg) else r.1.b

/-- **Specification of the side exit.** [cite: GrimmettPercolation1999, §7.3 pp. 172–173 (B)] -/
theorem sideExit_spec {r : BrickRec d} (h : GoodRec m L H r) {i : Fin d} (hi : i ≠ r.1.a) (u : ℤˣ) (sg : Fin d → Bool) :
    sideExit hL hH r i u sg i = r.1.b i + (u : ℤ) * ((L : ℤ) + 1) ∧
      ((m : ℤ) + 1 ≤ (r.1.s : ℤ) * (sideExit hL hH r i u sg r.1.a - r.1.b r.1.a) ∧
        (r.1.s : ℤ) * (sideExit hL hH r i u sg r.1.a - r.1.b r.1.a) ≤ (H : ℤ) - m - 1) ∧
      (∀ j, j ≠ r.1.a → j ≠ i → |sideExit hL hH r i u sg j - r.1.b j| ≤ (L : ℤ) - m - 1 ∧
        (sg j = true → 0 ≤ sideExit hL hH r i u sg j - r.1.b j) ∧ (sg j = false → sideExit hL hH r i u sg j - r.1.b j ≤ 0)) ∧
      IsSeed (cfgOf r) (square i m (sideExit hL hH r i u sg)) ∧
      ∃ y ∈ square r.1.a m r.1.b, (openGraph (cfgOf r)).Reachable y (sideExit hL hH r i u sg) := by
  unfold sideExit
  rw [dif_pos ⟨h, hi⟩]
  exact Classical.choose_spec (exists_side_exit' hL hH h hi u sg)

/-! ## Steps -/

/-- **Top step**: the brick of the same axis and direction based on the top exit (Grimmett (A)). [cite: GrimmettPercolation1999, §7.3 p. 172 (A)] -/
def tStep (r : BrickRec d) (sg : Fin d → Bool) : BrickPos d := ⟨r.1.a, r.1.s, topExit hL hH r sg⟩

/-- **Side step**: the brick of axis `i` and direction `u` based on the side exit (Grimmett (B)).
[cite: GrimmettPercolation1999, §7.3 pp. 172–173 (B)] -/
def sStep (r : BrickRec d) (i : Fin d) (u : ℤˣ) (sg : Fin d → Bool) : BrickPos d := ⟨i, u, sideExit hL hH r i u sg⟩

/-- Axis, sign and base of a top step. [folklore] -/
@[simp] theorem tStep_a (r : BrickRec d) (sg : Fin d → Bool) : (tStep hL hH r sg).a = r.1.a := rfl
/-- Axis, sign and base of a top step. [folklore] -/
@[simp] theorem tStep_s (r : BrickRec d) (sg : Fin d → Bool) : (tStep hL hH r sg).s = r.1.s := rfl
/-- Axis, sign and base of a top step. [folklore] -/
@[simp] theorem tStep_b (r : BrickRec d) (sg : Fin d → Bool) : (tStep hL hH r sg).b = topExit hL hH r sg := rfl
/-- Axis, sign and base of a side step. [folklore] -/
@[simp] theorem sStep_a (r : BrickRec d) (i : Fin d) (u : ℤˣ) (sg : Fin d → Bool) : (sStep hL hH r i u sg).a = i := rfl
/-- Axis, sign and base of a side step. [folklore] -/
@[simp] theorem sStep_s (r : BrickRec d) (i : Fin d) (u : ℤˣ) (sg : Fin d → Bool) : (sStep hL hH r i u sg).s = u := rfl
/-- Axis, sign and base of a side step. [folklore] -/
@[simp] theorem sStep_b (r : BrickRec d) (i : Fin d) (u : ℤˣ) (sg : Fin d → Bool) :
    (sStep hL hH r i u sg).b = sideExit hL hH r i u sg := rfl

/-- **A top step is a step of a leg**: along the axis by exactly `s(H+1)`, transversally by at most
`L - m - 1`, in the requested directions. [cite: GrimmettPercolation1999, §7.3 p. 172 (A), p. 173 (D)] -/
theorem tStep_rel {r : BrickRec d} (h : GoodRec m L H r) (sg : Fin d → Bool) :
    (tStep hL hH r sg).b r.1.a = r.1.b r.1.a + (r.1.s : ℤ) * ((H : ℤ) + 1) ∧
      ∀ i, i ≠ r.1.a → |(tStep hL hH r sg).b i - r.1.b i| ≤ (L : ℤ) - m - 1 ∧
        (sg i = true → 0 ≤ (tStep hL hH r sg).b i - r.1.b i) ∧ (sg i = false → (tStep hL hH r sg).b i - r.1.b i ≤ 0) := by
  obtain ⟨h1, h2, -, -⟩ := topExit_spec hL hH h sg
  exact ⟨h1, h2⟩

/-- **A side step is a turn** off the brick of the record. [cite: GrimmettPercolation1999, §7.3 pp. 172–173 (B)] -/
theorem isTurn_sStep {r : BrickRec d} (h : GoodRec m L H r) {i : Fin d} (hi : i ≠ r.1.a) (u : ℤˣ) (sg : Fin d → Bool) :
    IsTurn m L H r.1.a r.1.s i u r.1 (sStep hL hH r i u sg) := by
  obtain ⟨h1, h2, h3, -, -⟩ := sideExit_spec hL hH h hi u sg
  exact ⟨hi, rfl, rfl, h1, h2, fun j hj hji => (h3 j hj hji).1⟩

/-- The entry square of the next brick after a top step is open in the observed configuration (hence
in any configuration containing it). [cite: GrimmettPercolation1999, §7.3 p. 172 (A)] -/
theorem isSeed_tStep {r : BrickRec d} (h : GoodRec m L H r) (sg : Fin d → Bool) :
    IsSeed (cfgOf r) (square (tStep hL hH r sg).a m (tStep hL hH r sg).b) :=
  (topExit_spec hL hH h sg).2.2.1

/-- The same for a side step. [cite: GrimmettPercolation1999, §7.3 pp. 172–173 (B)] -/
theorem isSeed_sStep {r : BrickRec d} (h : GoodRec m L H r) {i : Fin d} (hi : i ≠ r.1.a) (u : ℤˣ) (sg : Fin d → Bool) :
    IsSeed (cfgOf r) (square (sStep hL hH r i u sg).a m (sStep hL hH r i u sg).b) :=
  (sideExit_spec hL hH h hi u sg).2.2.2.1

/-- **Connectivity of a top step**: if the entry square of `β` is open in `ω ⊇ ↑o`, the base centre of
the next brick is joined to the base centre of `β` by an open path of `ω`.
[cite: GrimmettPercolation1999, §7.3 p. 172 (A)] -/
theorem reachable_tStep {r : BrickRec d} (h : GoodRec m L H r) (sg : Fin d → Bool) {ω : BondConfig (Site d)}
    (hω : cfgOf r ⊆ ω) (hpre : IsSeed ω (square r.1.a m r.1.b)) :
    (openGraph ω).Reachable r.1.b (tStep hL hH r sg).b := by
  obtain ⟨-, -, -, y, hy, hreach⟩ := topExit_spec hL hH h sg
  exact (reachable_of_isSeed_square hpre (self_mem_square _ _ _) hy).trans (reachable_mono hω hreach)

/-- **Connectivity of a side step.** [cite: GrimmettPercolation1999, §7.3 pp. 172–173 (B)] -/
theorem reachable_sStep {r : BrickRec d} (h : GoodRec m L H r) {i : Fin d} (hi : i ≠ r.1.a) (u : ℤˣ) (sg : Fin d → Bool)
    {ω : BondConfig (Site d)} (hω : cfgOf r ⊆ ω) (hpre : IsSeed ω (square r.1.a m r.1.b)) :
    (openGraph ω).Reachable r.1.b (sStep hL hH r i u sg).b := by
  obtain ⟨-, -, -, -, y, hy, hreach⟩ := sideExit_spec hL hH h hi u sg
  exact (reachable_of_isSeed_square hpre (self_mem_square _ _ _) hy).trans (reachable_mono hω hreach)

end Exits

/-! ## Legs produced by top steps -/

/-- **Iterated top steps form a leg.** If `β (k+1) = tStep (β k, o k)` with good records for `k < n`,
then `β 0, …, β n` is a leg along the axis and direction of `β 0`.
[cite: GrimmettPercolation1999, §7.3 p. 172 (A)] -/
theorem isLeg_of_tSteps (hL : m + 1 ≤ L) (hH : 2 * m + 2 ≤ H) {n : ℕ} {β : ℕ → BrickPos d} {o : ℕ → Finset (Sym2 (Site d))}
    {sg : ℕ → Fin d → Bool} (hgood : ∀ k < n, GoodRec m L H (β k, o k))
    (hstep : ∀ k < n, β (k + 1) = tStep hL hH (β k, o k) (sg k)) :
    IsLeg m L H (β 0).a (β 0).s n β := by
  have hax : ∀ k ≤ n, (β k).a = (β 0).a ∧ (β k).s = (β 0).s := by
    intro k hk
    induction k with
    | zero => exact ⟨rfl, rfl⟩
    | succ k ih =>
      have := ih (by omega)
      rw [hstep k (by omega), tStep_a, tStep_s]
      exact this
  refine ⟨fun k hk => (hax k hk).1, fun k hk => (hax k hk).2, fun k hk => ?_, fun k hk i hi => ?_⟩
  · have hrel := (tStep_rel hL hH (hgood k hk) (sg k)).1
    rw [hstep k hk]
    have h1 := (hax k hk.le).1; have h2 := (hax k hk.le).2
    simp only at hrel
    rw [h1, h2] at hrel
    exact hrel
  · have h1 := (hax k hk.le).1
    have hrel := ((tStep_rel hL hH (hgood k hk) (sg k)).2 i (by simp only; rw [h1]; exact hi)).1
    rw [hstep k hk]
    exact hrel

end BGNd

end Percolation.Literature

end
