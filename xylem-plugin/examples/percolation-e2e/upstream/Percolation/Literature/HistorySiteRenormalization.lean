import Percolation.Literature.DynamicSiteRenormalization
import Percolation.Util.Linter

/-!
# Dynamic renormalization, vertex form, driven by the whole history: Kozma–Nitzan's exploration process

The probabilistic skeleton of the exploration process
of G. Kozma, S. Nitzan, *A reduction of the `θ(p_c) = 0` problem to a conjectured inequality*,
arXiv:2401.12397 (2024), §4, pp. 25–31 (proof of Theorem 6):

> "A (supercritical, two-dimensional) exploration process is a couple of sequences of random
> subsets `G_i ⊆ X_i ⊂ ℤ²` with the following properties: (1) `X₁ = {0}`. (2) `G_i ⊆ G_j` and
> `X_i ⊆ X_j` for all `j > i`. (3) If there exists a `v ∈ ℤ² \ X_i` neighbouring `G_i` then the
> first of the `v` satisfying this property … has `X_{i+1} = X_i ∪ {v}` and `G_{i+1} ⊆ G_i ∪ {v}` …
> (4) … `P(v ∈ G_{i+1} | G₁, …, G_i, X₁, …, X_i) > p`. (5) `P(G₁ = {0}) > 0`. It is well-known and
> easy to see that if `(G_i, X_i)` is an exploration process then `P(lim |G_i| = ∞) > 0`. We skip
> the details, but remark that [Grimmett–Marstrand, Lemma 1] is similar." (p. 25)

proved here in the following form. The process is an adaptive exploration of a bond configuration on
an arbitrary countable graph (`AdaptiveProbing.lean`: every step reveals a set of fresh edges
chosen, together with its success criterion, as a function of the ENTIRE history — in Kozma–Nitzan's
process the examination of `v` reveals the boxes `E_{w,v}`, `H^{j_x}_{v,x}` and its success is the
conditional statement (30), a function of everything revealed so far, `ω|_{E_i}`), and the macro
bookkeeping is that of Grimmett's Lemma (7.24) algorithm (each macro-VERTEX of `ℤ²` is examined at
most once, from the earliest occupied neighbour; success occupies it, failure blocks it for ever:
KN's `G_i` = occupied, `X_i` = occupied ∪ blocked).

The hypotheses (`HSiteScheme.Lawful`) are those of: `fresh` (every probe avoids `U₀` and the edges
revealed before), `probes` (along the run on every configuration of edges of `G`, a probe is made
whenever a candidate vertex exists — so an explorer may refuse impossible histories), `fail` (after
EVERY history with a candidate at which a probe is made, the probe fails with probability `≤ ε`;
this is KN's (4) = (28), "uniformly in the past", made unconditional by freshness and the product
structure). The conclusion (`measure_initEvent_inter_finite_le`,
`measureReal_le_three_mul_of_subset`) is reached by the Peierls argument of
`DynamicSiteRenormalization.lean` (a dual circuit around a finite final cluster has a blocked
endpoint on each edge; designated sets of blocked vertices; `ε ≤ 2⁻³²`) instead of the domination by
site percolation KN allude to; so KN's "`p > p_c(ℤ², site)`" becomes the explicit "`ε ≤ 2⁻³²`",
which is how the lemma is used (the `ε` of the process is at our disposal, p. 25: "if `ε` is
sufficiently small"). What occupied vertices certify is left to the user, who is given the
provenance of determined vertices (`exists_probe_of_det`).

## References

* G. Kozma, S. Nitzan, arXiv:2401.12397 (2024), §4 p. 25 (exploration processes), pp. 26–31.
* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §7.2 pp. 154–155 (the algorithm of Lemma
  (7.24)), §1.4 pp. 15–18 (Peierls' argument) [GrimmettPercolation1999].
* G. R. Grimmett, J. M. Marstrand, Proc. Roy. Soc. London A 430 (1990) 439–457, Lemma 1.
-/

noncomputable section

namespace Percolation.Literature

open MeasureTheory ProbabilityTheory Contour ProbeHistory GadgetSystem
open scoped ENNReal Classical

/-- A **history-driven site renormalisation scheme** over bond configurations on `V`: an adaptive
explorer, the initial edge set `U₀` (required open), and the success criterion of the probe made
after a history, as the examination of the target of the directed macro-edge `e` it is labelled with
(assigned by the replay `mstOf`), reading the open edges it observes (Kozma–Nitzan 2024, pp. 26–27:
`(E_i, G_i, X_i)`, "declare `v` good … if all connections to all `x ∈ X` are good").
[cite: KozmaNitzan2024, §4 pp. 25–27] -/
structure HSiteScheme (V : Type*) where
  /-- the fine exploration: the next adaptive probe after each history -/
  E : AExplorer V
  /-- the initial edges, all required to be open -/
  U₀ : Finset (Sym2 V)
  /-- success of the probe made after history `h` as the examination along the directed macro-edge
  `e`, reading the open edges `o` -/
  succ : ProbeHistory V → LatticeModels.Site 2 × MDir → Finset (Sym2 V) → Prop

namespace HSiteScheme

variable {V : Type*}

/-! ## The macro-state replayed from a history -/

/-- The macro-state (Grimmett's `S_t = (A_t, B_t)`; KN's `G_i` and `X_i \ G_i`): occupied and blocked
macro-vertices. [cite: KozmaNitzan2024, §4 p. 25] -/
structure HState where
  /-- occupied macro-vertices (`G_i`) -/
  occ : Finset (LatticeModels.Site 2)
  /-- blocked macro-vertices (`X_i \ G_i`) -/
  blk : Finset (LatticeModels.Site 2)

/-- The initial macro-state: the origin occupied (`G₁ = X₁ = {0}`). [cite: KozmaNitzan2024, §4 p. 25 (1)] -/
def HState.start : HState := ⟨{0}, ∅⟩

/-- A macro-vertex is determined: occupied or blocked (`X_i`). [cite: KozmaNitzan2024, §4 p. 25] -/
def HState.Det (st : HState) (x : LatticeModels.Site 2) : Prop := x ∈ st.occ ∨ x ∈ st.blk

/-- A directed macro-edge is a candidate: source occupied, target undetermined ("a
`v ∈ ℤ² \ X_i` neighbouring `G_i`", p. 25 (3)). [cite: KozmaNitzan2024, §4 p. 25 (3)] -/
def HState.Cand (st : HState) (e : LatticeModels.Site 2 × MDir) : Prop :=
  e.1 ∈ st.occ ∧ ¬st.Det (tgt e)

/-- The candidate of least code ("the first of the `v` … in lexicographic order … Any deterministic,
predefined order on `ℤ²` would have worked equally well", p. 25), if any. [cite: KozmaNitzan2024, §4 p. 25 (3) and Remark] -/
def HState.choice (st : HState) : Option (LatticeModels.Site 2 × MDir) :=
  if h : ∃ n, ∃ e, st.Cand e ∧ Encodable.encode e = n then
    some (Classical.choose (Nat.find_spec h))
  else none

/-- The chosen edge is a candidate. [folklore] -/
theorem HState.cand_of_choice {st : HState} {e : LatticeModels.Site 2 × MDir} (h : st.choice = some e) :
    st.Cand e := by
  unfold HState.choice at h
  split_ifs at h with hex
  cases h
  exact (Classical.choose_spec (Nat.find_spec hex)).1

/-- If nothing is chosen there is no candidate. [folklore] -/
theorem HState.not_cand_of_choice_eq_none {st : HState} (h : st.choice = none) (e : LatticeModels.Site 2 × MDir) :
    ¬st.Cand e := by
  intro hc
  have hex : ∃ n, ∃ e, st.Cand e ∧ Encodable.encode e = n := ⟨Encodable.encode e, e, hc, rfl⟩
  unfold HState.choice at h
  rw [dif_pos hex] at h
  simp at h

/-- The update of the macro-state by the outcome (`ok` = success) of the examination along `e`: the
target is occupied or blocked (`G_{i+1} = G_i ∪ {v}` or `G_i`; `X_{i+1} = X_i ∪ {v}`).
[cite: KozmaNitzan2024, §4 p. 25 (3)] -/
def HState.update (st : HState) (e : LatticeModels.Site 2 × MDir) (ok : Prop) : HState :=
  if ok then ⟨insert (tgt e) st.occ, st.blk⟩ else ⟨st.occ, insert (tgt e) st.blk⟩

/-- **Replay**: the macro-state after a history (newest entry first), for a success criterion
`succ`. A recorded probe is the examination along the chosen edge of the state replayed from the
older part; it occupies the target iff `succ` holds, and blocks it otherwise. [cite: KozmaNitzan2024, §4 pp. 25–27] -/
def mstOf (succ : ProbeHistory V → LatticeModels.Site 2 × MDir → Finset (Sym2 V) → Prop) : ProbeHistory V → HState
  | [] => HState.start
  | none :: h => mstOf succ h
  | some r :: h =>
    match (mstOf succ h).choice with
    | none => mstOf succ h
    | some e => (mstOf succ h).update e (succ h e r.2)

/-- Replay of the empty history. [folklore] -/
@[simp] theorem mstOf_nil (succ : ProbeHistory V → LatticeModels.Site 2 × MDir → Finset (Sym2 V) → Prop) :
    mstOf succ [] = HState.start := rfl

/-- A `none` step does not change the replayed state. [folklore] -/
@[simp] theorem mstOf_cons_none (succ : ProbeHistory V → LatticeModels.Site 2 × MDir → Finset (Sym2 V) → Prop)
    (h : ProbeHistory V) : mstOf succ (none :: h) = mstOf succ h := rfl

variable (S : HSiteScheme V)

/-- The macro-state of the scheme after a history: `mstOf S.succ`. [folklore] -/
abbrev mst (h : ProbeHistory V) : HState := mstOf S.succ h

/-- The macro-state after `n` steps of the run on `ω`. [folklore] -/
abbrev stN (n : ℕ) (ω : BondConfig V) : HState := S.mst (S.E.hist n ω)

/-! ## Elementary properties of the update -/

section Update

variable (st : HState) (e : LatticeModels.Site 2 × MDir) (ok : Prop)

/-- A successful update occupies the target. [folklore] -/
theorem HState.update_of_ok (h : ok) : st.update e ok = ⟨insert (tgt e) st.occ, st.blk⟩ := by
  unfold HState.update; rw [if_pos h]

/-- A failed update blocks the target. [folklore] -/
theorem HState.update_of_not_ok (h : ¬ok) : st.update e ok = ⟨st.occ, insert (tgt e) st.blk⟩ := by
  unfold HState.update; rw [if_neg h]

/-- Occupied vertices stay occupied. [folklore] -/
theorem HState.occ_subset_update : st.occ ⊆ (st.update e ok).occ := by
  unfold HState.update; split_ifs
  · exact Finset.subset_insert _ _
  · exact subset_rfl

/-- Blocked vertices stay blocked. [folklore] -/
theorem HState.blk_subset_update : st.blk ⊆ (st.update e ok).blk := by
  unfold HState.update; split_ifs
  · exact subset_rfl
  · exact Finset.subset_insert _ _

/-- Determined vertices stay determined. [folklore] -/
theorem HState.det_update_of_det {x : LatticeModels.Site 2} (hx : st.Det x) : (st.update e ok).Det x := by
  rcases hx with hx | hx
  · exact Or.inl (st.occ_subset_update e ok hx)
  · exact Or.inr (st.blk_subset_update e ok hx)

/-- The target becomes determined. [folklore] -/
theorem HState.det_update_tgt : (st.update e ok).Det (tgt e) := by
  unfold HState.update; split_ifs
  · exact Or.inl (Finset.mem_insert_self _ _)
  · exact Or.inr (Finset.mem_insert_self _ _)

/-- After the update the determined vertices are the old ones and the target. [folklore] -/
theorem HState.det_update_iff {x : LatticeModels.Site 2} : (st.update e ok).Det x ↔ x = tgt e ∨ st.Det x := by
  constructor
  · intro hx
    unfold HState.update at hx
    split_ifs at hx
    · rcases hx with hx | hx
      · rcases Finset.mem_insert.1 hx with rfl | hx
        · exact Or.inl rfl
        · exact Or.inr (Or.inl hx)
      · exact Or.inr (Or.inr hx)
    · rcases hx with hx | hx
      · exact Or.inr (Or.inl hx)
      · rcases Finset.mem_insert.1 hx with rfl | hx
        · exact Or.inl rfl
        · exact Or.inr (Or.inr hx)
  · rintro (rfl | hx)
    · exact st.det_update_tgt e ok
    · exact st.det_update_of_det e ok hx

/-- The occupied set after the update. [folklore] -/
theorem HState.occ_update_subset : (st.update e ok).occ ⊆ insert (tgt e) st.occ := by
  unfold HState.update; split_ifs
  · exact subset_rfl
  · exact Finset.subset_insert _ _

end Update

/-! ## Combinatorial invariants -/

section Invariants

/-- The invariants of the macro-state: the origin is occupied; no vertex is both occupied and
blocked; every blocked vertex is adjacent to an occupied one. [cite: GrimmettPercolation1999, §7.2 p. 154] -/
structure HState.Inv (st : HState) : Prop where
  zero_mem : (0 : LatticeModels.Site 2) ∈ st.occ
  disj : ∀ x ∈ st.occ, x ∉ st.blk
  blk_adj : ∀ x ∈ st.blk, ∃ a ∈ st.occ, ∃ d : MDir, x = a + stepVec d

/-- The initial state satisfies the invariants. [folklore] -/
theorem HState.Inv.start : HState.start.Inv where
  zero_mem := Finset.mem_singleton_self _
  disj := by simp [HState.start]
  blk_adj := by simp [HState.start]

/-- The invariants are preserved by an examination along a candidate edge. [folklore] -/
theorem HState.Inv.update {st : HState} (hI : st.Inv) {e : LatticeModels.Site 2 × MDir} (he : st.Cand e)
    (ok : Prop) : (st.update e ok).Inv := by
  obtain ⟨he1, he2⟩ := he
  have ht1 : tgt e ∉ st.occ := fun h => he2 (Or.inl h)
  have ht2 : tgt e ∉ st.blk := fun h => he2 (Or.inr h)
  by_cases hok : ok
  · rw [st.update_of_ok e ok hok]
    refine ⟨Finset.mem_insert_of_mem hI.zero_mem, ?_, ?_⟩
    · intro x hx hxb
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact ht2 hxb
      · exact hI.disj x hx hxb
    · intro x hx
      obtain ⟨a, ha, d, rfl⟩ := hI.blk_adj x hx
      exact ⟨a, Finset.mem_insert_of_mem ha, d, rfl⟩
  · rw [st.update_of_not_ok e ok hok]
    refine ⟨hI.zero_mem, ?_, ?_⟩
    · intro x hx hxb
      rcases Finset.mem_insert.1 hxb with rfl | hxb
      · exact ht1 hx
      · exact hI.disj x hx hxb
    · intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact ⟨e.1, he1, e.2, rfl⟩
      · exact hI.blk_adj x hx

/-- Every replayed state satisfies the invariants. [folklore] -/
theorem inv_mstOf (succ : ProbeHistory V → LatticeModels.Site 2 × MDir → Finset (Sym2 V) → Prop) :
    ∀ h : ProbeHistory V, (mstOf succ h).Inv
  | [] => HState.Inv.start
  | none :: h => inv_mstOf succ h
  | some r :: h => by
    show (match (mstOf succ h).choice with
      | none => mstOf succ h
      | some e => (mstOf succ h).update e (succ h e r.2)).Inv
    cases hc : (mstOf succ h).choice with
    | none => exact inv_mstOf succ h
    | some e => exact (inv_mstOf succ h).update (HState.cand_of_choice hc) _

/-- Every replayed state of the scheme satisfies the invariants. [folklore] -/
theorem inv_mst (h : ProbeHistory V) : (S.mst h).Inv := inv_mstOf S.succ h

/-- With no candidate left, every neighbour of an occupied vertex is determined.
[cite: GrimmettPercolation1999, §7.2 p. 154] -/
theorem HState.closed_of_choice {st : HState} (hc : st.choice = none) {u : LatticeModels.Site 2} (hu : u ∈ st.occ)
    (d : MDir) : st.Det (u + stepVec d) := by
  by_contra hcon
  exact HState.not_cand_of_choice_eq_none hc (u, d) ⟨hu, hcon⟩

end Invariants

/-! ## The run on a configuration -/

section Run

/-- One step of the replayed state along the run, when no probe is made. [folklore] -/
theorem stN_succ_of_next_none {n : ℕ} {ω : BondConfig V} (hD : S.E.next (S.E.hist n ω) = none) :
    S.stN (n + 1) ω = S.stN n ω := by
  show S.mst (S.E.hist (n + 1) ω) = S.mst (S.E.hist n ω)
  rw [AExplorer.hist_succ, S.E.step_of_none hD]
  rfl

/-- One step of the replayed state along the run, when a probe `P` is made. [folklore] -/
theorem stN_succ_of_next_some {n : ℕ} {ω : BondConfig V} {P : AProbe V} (hD : S.E.next (S.E.hist n ω) = some P) :
    S.stN (n + 1) ω = (match (S.stN n ω).choice with
      | none => S.stN n ω
      | some e => (S.stN n ω).update e (S.succ (S.E.hist n ω) e (P.read ω))) := by
  show S.mst (S.E.hist (n + 1) ω) = _
  rw [AExplorer.hist_succ, S.E.step_of_some hD]
  rfl

/-- Occupied vertices stay occupied along the run (`G_i ⊆ G_j`). [cite: KozmaNitzan2024, §4 p. 25 (2)] -/
theorem occ_stN_mono (ω : BondConfig V) : Monotone fun n => (S.stN n ω).occ := by
  refine monotone_nat_of_le_succ fun n => ?_
  show (S.stN n ω).occ ⊆ (S.stN (n + 1) ω).occ
  cases hD : S.E.next (S.E.hist n ω) with
  | none => rw [S.stN_succ_of_next_none hD]
  | some P =>
    rw [S.stN_succ_of_next_some hD]
    cases hc : (S.stN n ω).choice with
    | none => exact le_rfl
    | some e => exact HState.occ_subset_update _ _ _

/-- Blocked vertices stay blocked along the run (`X_i ⊆ X_j`). [cite: KozmaNitzan2024, §4 p. 25 (2)] -/
theorem blk_stN_mono (ω : BondConfig V) : Monotone fun n => (S.stN n ω).blk := by
  refine monotone_nat_of_le_succ fun n => ?_
  show (S.stN n ω).blk ⊆ (S.stN (n + 1) ω).blk
  cases hD : S.E.next (S.E.hist n ω) with
  | none => rw [S.stN_succ_of_next_none hD]
  | some P =>
    rw [S.stN_succ_of_next_some hD]
    cases hc : (S.stN n ω).choice with
    | none => exact le_rfl
    | some e => exact HState.blk_subset_update _ _ _

/-- Determined vertices stay determined along the run. [folklore] -/
theorem det_stN_mono (ω : BondConfig V) {m n : ℕ} (hmn : m ≤ n) {x : LatticeModels.Site 2}
    (hx : (S.stN m ω).Det x) : (S.stN n ω).Det x := by
  rcases hx with hx | hx
  · exact Or.inl (S.occ_stN_mono ω hmn hx)
  · exact Or.inr (S.blk_stN_mono ω hmn hx)

/-- Once no edge can be chosen, the state is frozen. [folklore] -/
theorem stN_eq_of_choice_eq_none {N : ℕ} {ω : BondConfig V} (hc : (S.stN N ω).choice = none) :
    ∀ n, N ≤ n → S.stN n ω = S.stN N ω := by
  intro n hn
  induction n with
  | zero => rw [Nat.le_zero.1 hn]
  | succ n ih =>
    rcases Nat.lt_or_eq_of_le hn with hlt | heq
    · have h' := ih (Nat.lt_succ_iff.1 hlt)
      cases hD : S.E.next (S.E.hist n ω) with
      | none => rw [S.stN_succ_of_next_none hD, h']
      | some P =>
        rw [S.stN_succ_of_next_some hD, h', hc]
    · rw [← heq]

/-- While edges keep being chosen and probes keep being made, the determined set keeps growing.
[cite: GrimmettPercolation1999, §7.2 p. 154] -/
theorem le_card_det (ω : BondConfig V) (n : ℕ)
    (h : ∀ k < n, (S.stN k ω).choice ≠ none ∧ S.E.next (S.E.hist k ω) ≠ none) :
    n + 1 ≤ ((S.stN n ω).occ ∪ (S.stN n ω).blk).card := by
  induction n with
  | zero => simp [stN, mst, HState.start]
  | succ n ih =>
    have ih' := ih fun k hk => h k (Nat.lt_succ_of_lt hk)
    obtain ⟨hc, hD⟩ := h n (Nat.lt_succ_self n)
    obtain ⟨P, hP⟩ := Option.ne_none_iff_exists'.1 hD
    obtain ⟨e, he⟩ := Option.ne_none_iff_exists'.1 hc
    set st := S.stN n ω with hst
    obtain ⟨-, he2⟩ := HState.cand_of_choice he
    have hnot : tgt e ∉ st.occ ∪ st.blk := by rw [Finset.mem_union]; exact he2
    have hins : insert (tgt e) (st.occ ∪ st.blk) ⊆ (S.stN (n + 1) ω).occ ∪ (S.stN (n + 1) ω).blk := by
      rw [S.stN_succ_of_next_some hP, ← hst, he]
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact Finset.mem_union.2 (st.det_update_tgt e _)
      · exact Finset.mem_union.2 (st.det_update_of_det e _ (Finset.mem_union.1 hx))
    calc n + 1 + 1 ≤ (st.occ ∪ st.blk).card + 1 := Nat.succ_le_succ ih'
      _ = (insert (tgt e) (st.occ ∪ st.blk)).card := (Finset.card_insert_of_notMem hnot).symm
      _ ≤ _ := Finset.card_le_card hins

/-- The final occupied macro-cluster of the run (`lim G_i`). [cite: KozmaNitzan2024, §4 p. 25] -/
def occFinal (ω : BondConfig V) : Set (LatticeModels.Site 2) := ⋃ n, ↑(S.stN n ω).occ

/-- **Termination**: if a probe is made whenever a candidate exists, and the final cluster is finite,
then at some time no edge can be chosen any more. [cite: GrimmettPercolation1999, §7.2 p. 154] -/
theorem exists_choice_eq_none {ω : BondConfig V}
    (hprobes : ∀ n, (S.stN n ω).choice ≠ none → S.E.next (S.E.hist n ω) ≠ none)
    (hfin : (S.occFinal ω).Finite) : ∃ N, (S.stN N ω).choice = none := by
  by_contra hne
  push Not at hne
  set F : Finset (LatticeModels.Site 2) :=
    hfin.toFinset ∪ (hfin.toFinset ×ˢ (Finset.univ : Finset MDir)).image fun q => q.1 + stepVec q.2 with hF
  have hsub : ∀ n, (S.stN n ω).occ ∪ (S.stN n ω).blk ⊆ F := by
    intro n x hx
    rw [hF, Finset.mem_union]
    rcases Finset.mem_union.1 hx with hx | hx
    · exact Or.inl (hfin.mem_toFinset.2 (Set.mem_iUnion.2 ⟨n, hx⟩))
    · obtain ⟨a, ha, d, rfl⟩ := (S.inv_mst _).blk_adj x hx
      refine Or.inr (Finset.mem_image.2 ⟨(a, d), Finset.mem_product.2 ⟨?_, Finset.mem_univ _⟩, rfl⟩)
      exact hfin.mem_toFinset.2 (Set.mem_iUnion.2 ⟨n, ha⟩)
  have h1 := S.le_card_det ω F.card fun k _ => ⟨hne k, hprobes k (hne k)⟩
  have h2 := Finset.card_le_card (hsub F.card)
  omega

/-- The macro bond configuration at a state: an edge of `ℤ²` is open unless one of its endpoints is
blocked. [cite: GrimmettPercolation1999, §7.2 p. 155] -/
def HState.macroConfig (st : HState) : BondConfig (LatticeModels.Site 2) :=
  {x | x ∈ (LatticeModels.zdGraph 2).edgeSet ∧ ∀ v ∈ st.blk, ¬(v ∈ x)}

/-- With no candidate left, the open macro-cluster of the origin consists of occupied vertices.
[cite: GrimmettPercolation1999, §7.2 p. 155] -/
theorem HState.Inv.openCluster_subset {st : HState} (hI : st.Inv) (hc : st.choice = none) :
    openCluster st.macroConfig 0 ⊆ ↑st.occ := by
  have hclosed : ∀ u v : LatticeModels.Site 2, u ∈ st.occ → (openGraph st.macroConfig).Adj u v → v ∈ st.occ := by
    intro u v hu hadj
    rw [openGraph_adj] at hadj
    obtain ⟨⟨hedge, hnot⟩, -⟩ := hadj
    obtain ⟨d, rfl⟩ := (zdGraph_adj_iff_stepVec u v).1 (by simpa using hedge)
    rcases HState.closed_of_choice hc hu d with h | h
    · exact h
    · exact absurd (Sym2.mem_mk_right _ _) (hnot _ h)
  have key : ∀ (u w : LatticeModels.Site 2) (W : (openGraph st.macroConfig).Walk u w), u ∈ st.occ → w ∈ st.occ := by
    intro u w W
    induction W with
    | nil => exact id
    | @cons a b _ hadj W' ih => exact fun hu => ih (hclosed a b hu hadj)
  intro v hv
  obtain ⟨W⟩ := hv
  exact key 0 v W hI.zero_mem

/-- **The dual circuit of blocked vertices**: if probes are made whenever possible and the final
cluster is finite then, at a terminal time `N`, some dual circuit of `ℤ²` of length `n ≥ 1` through
a plaquette `(k,0)`, `k < n`, crosses `n` distinct macro-edges each having a blocked endpoint.
[cite: GrimmettPercolation1999, §7.2 p. 155 and §1.4 p. 16] -/
theorem exists_dualCircuit_blk {ω : BondConfig V}
    (hprobes : ∀ n, (S.stN n ω).choice ≠ none → S.E.next (S.E.hist n ω) ≠ none)
    (hfin : (S.occFinal ω).Finite) :
    ∃ N, (S.stN N ω).choice = none ∧ ∃ n k : ℕ, k < n ∧ ∃ (w : Fin n → MDir) (m : ℕ), m ≤ n ∧
      (dualEdges (Pi.single 0 (k : ℤ) - wordPos w m) w).card = n ∧
      ∀ x ∈ dualEdges (Pi.single 0 (k : ℤ) - wordPos w m) w,
        x ∈ (LatticeModels.zdGraph 2).edgeSet ∧ ∃ v ∈ (S.stN N ω).blk, v ∈ x := by
  obtain ⟨N, hN⟩ := S.exists_choice_eq_none hprobes hfin
  have hI := S.inv_mst (S.E.hist N ω)
  have hCfin : (openCluster (S.stN N ω).macroConfig 0).Finite :=
    (S.stN N ω).occ.finite_toSet.subset (hI.openCluster_subset hN)
  obtain ⟨n, k, hkn, a, w, -, ⟨m, hmn, hpos⟩, hcard, hdisj, -, -⟩ := Contour.exists_dualCircuit _ hCfin
  have ha : a = Pi.single 0 (k : ℤ) - wordPos w m := by rw [← hpos, add_sub_cancel_right]
  subst ha
  refine ⟨N, hN, n, k, hkn, w, m, hmn, hcard, fun x hx => ?_⟩
  have hxE : x ∈ (LatticeModels.zdGraph 2).edgeSet := dualEdges_subset_edgeSet _ _ hx
  have hxω : x ∉ (S.stN N ω).macroConfig := fun hm => Set.disjoint_left.1 hdisj hx hm
  simp only [HState.macroConfig, Set.mem_setOf_eq, not_and, not_forall, not_not, exists_prop] at hxω
  exact ⟨hxE, hxω hxE⟩

/-- **Provenance of determined vertices**: every determined macro-vertex other than the origin was
the target of an examination made along the run — at some earlier time `m`, the chosen edge `e` had
target `b` and a probe `P` was made; `b` is occupied iff that probe's observation satisfied `succ`.
[folklore] -/
theorem exists_probe_of_det (ω : BondConfig V) : ∀ (n : ℕ) (b : LatticeModels.Site 2),
    (S.stN n ω).Det b → b = 0 ∨ ∃ m < n, ∃ e P, (S.stN m ω).choice = some e ∧ tgt e = b ∧
      S.E.next (S.E.hist m ω) = some P ∧ (b ∈ (S.stN n ω).occ ↔ S.succ (S.E.hist m ω) e (P.read ω))
  | 0, b, hb => by
    left
    rcases hb with hb | hb
    · simpa [stN, mst, HState.start] using hb
    · simp [stN, mst, HState.start] at hb
  | n + 1, b, hb => by
    have hI := S.inv_mst (S.E.hist n ω)
    cases hD : S.E.next (S.E.hist n ω) with
    | none =>
      rw [S.stN_succ_of_next_none hD] at hb ⊢
      rcases exists_probe_of_det ω n b hb with h | ⟨m, hm, rest⟩
      · exact Or.inl h
      · exact Or.inr ⟨m, Nat.lt_succ_of_lt hm, rest⟩
    | some P =>
      have hst := S.stN_succ_of_next_some hD
      cases hc : (S.stN n ω).choice with
      | none =>
        rw [hc] at hst
        rw [hst] at hb ⊢
        rcases exists_probe_of_det ω n b hb with h | ⟨m, hm, rest⟩
        · exact Or.inl h
        · exact Or.inr ⟨m, Nat.lt_succ_of_lt hm, rest⟩
      | some e =>
        rw [hc] at hst
        simp only at hst
        obtain ⟨he1, he2⟩ := HState.cand_of_choice hc
        by_cases hbt : b = tgt e
        · subst hbt
          right
          refine ⟨n, Nat.lt_succ_self n, e, P, hc, rfl, hD, ?_⟩
          rw [hst]
          by_cases hok : S.succ (S.E.hist n ω) e (P.read ω)
          · rw [HState.update_of_ok _ _ _ hok]
            simp only [Finset.mem_insert, true_or, hok]
          · rw [HState.update_of_not_ok _ _ _ hok]
            simp only [hok, iff_false]
            exact fun h => he2 (Or.inl h)
        · -- `b` was determined before, with the same occupancy
          have hb' : (S.stN n ω).Det b := by
            rw [hst] at hb
            rcases (HState.det_update_iff _ _ _).1 hb with h | h
            · exact absurd h hbt
            · exact h
          have hocc : b ∈ (S.stN (n + 1) ω).occ ↔ b ∈ (S.stN n ω).occ := by
            rw [hst]
            constructor
            · intro h
              rcases Finset.mem_insert.1 (HState.occ_update_subset _ _ _ h) with h' | h'
              · exact absurd h' hbt
              · exact h'
            · intro h; exact HState.occ_subset_update _ _ _ h
          rcases exists_probe_of_det ω n b hb' with h | ⟨m, hm, e', P', hc', ht', hD', hiff⟩
          · exact Or.inl h
          · exact Or.inr ⟨m, Nat.lt_succ_of_lt hm, e', P', hc', ht', hD', hocc.trans hiff⟩

end Run

/-! ## Scores read off the history -/

section Scores

variable (X : Finset (LatticeModels.Site 2))

/-- The examination made after `h` is designated (for the set `X` of macro-vertices): its target lies
in `X`. [cite: GrimmettPercolation1999, §7.2 p. 155] -/
def desigOf (h : ProbeHistory V) : Prop :=
  match (S.mst h).choice with
  | none => False
  | some e => tgt e ∈ X

/-- The examination made after `h`, with observation `o`, succeeds (trivially so if no edge is chosen).
[cite: KozmaNitzan2024, §4 p. 27 (v is good)] -/
def succOf (h : ProbeHistory V) (o : Finset (Sym2 V)) : Prop :=
  match (S.mst h).choice with
  | none => True
  | some e => S.succ h e o

variable {X}

/-- **The scores along the run**: the number of designated failures is the number of blocked
vertices in `X`, and a designated success is an occupied vertex of `X` other than the origin.
[folklore] -/
theorem scores_hist (ω : BondConfig V) : ∀ n : ℕ,
    nfail S.succOf (S.desigOf X) (S.E.hist n ω) = ((S.stN n ω).blk.filter fun v => v ∈ X).card ∧
      (AnySucc S.succOf (S.desigOf X) (S.E.hist n ω) ↔ ∃ v ∈ (S.stN n ω).occ, v ≠ 0 ∧ v ∈ X)
  | 0 => by simp [stN, mst, HState.start]
  | n + 1 => by
    obtain ⟨ih1, ih2⟩ := scores_hist ω n
    cases hD : S.E.next (S.E.hist n ω) with
    | none =>
      rw [AExplorer.hist_succ, S.E.step_of_none hD, nfail_cons_none, anySucc_cons_none, S.stN_succ_of_next_none hD]
      exact ⟨ih1, ih2⟩
    | some P =>
      have hst := S.stN_succ_of_next_some hD
      have hrec : (P.record ω).2 = P.read ω := rfl
      rw [AExplorer.hist_succ, S.E.step_of_some hD, nfail_cons_some, anySucc_cons_some, hst, ih1, hrec]
      rcases Option.eq_none_or_eq_some ((S.stN n ω).choice) with hc | ⟨e, hc⟩
      · have hc' : (S.mst (S.E.hist n ω)).choice = none := hc
        have hdes : ¬S.desigOf X (S.E.hist n ω) := by simp only [desigOf, hc']; exact id
        rw [hc]
        simp only [hdes, false_and, if_false, add_zero, false_or]
        exact ⟨trivial, ih2⟩
      · have hc' : (S.mst (S.E.hist n ω)).choice = some e := hc
        set st := S.stN n ω with hst'
        obtain ⟨he1, he2⟩ := HState.cand_of_choice hc
        have hI := S.inv_mst (S.E.hist n ω)
        have htb : tgt e ∉ st.blk := fun h => he2 (Or.inr h)
        have hto : tgt e ∉ st.occ := fun h => he2 (Or.inl h)
        have ht0 : tgt e ≠ 0 := fun h => hto (h ▸ hI.zero_mem)
        have hdes : S.desigOf X (S.E.hist n ω) ↔ tgt e ∈ X := by simp only [desigOf, hc']
        have hsuc : ∀ o, S.succOf (S.E.hist n ω) o ↔ S.succ (S.E.hist n ω) e o := by
          intro o; simp only [succOf, hc']
        rw [hc]
        simp only [hdes, hsuc]
        by_cases hok : S.succ (S.E.hist n ω) e (P.read ω)
        · rw [st.update_of_ok e _ hok]
          refine ⟨by simp [hok], ?_⟩
          simp only [hok, and_true, Finset.mem_insert]
          rw [ih2]
          constructor
          · rintro (hX | ⟨v, hv, hv0, hvX⟩)
            · exact ⟨tgt e, Or.inl rfl, ht0, hX⟩
            · exact ⟨v, Or.inr hv, hv0, hvX⟩
          · rintro ⟨v, hv, hv0, hvX⟩
            rcases hv with rfl | hv
            · exact Or.inl hvX
            · exact Or.inr ⟨v, hv, hv0, hvX⟩
        · rw [st.update_of_not_ok e _ hok]
          refine ⟨?_, ?_⟩
          · rw [Finset.filter_insert]
            by_cases hX : tgt e ∈ X
            · rw [if_pos hX, Finset.card_insert_of_notMem (fun hm => htb (Finset.mem_filter.1 hm).1)]
              simp [hX, hok]
            · rw [if_neg hX]; simp [hX]
          · simp only [hok, and_false, false_or]
            exact ih2

/-- **At a terminal time a blocked set is fully charged**: if `X` consists of blocked vertices at a
terminal time `N`, then at all later times there are `|X|` designated failures and no designated
success. [cite: GrimmettPercolation1999, §7.2 p. 155] -/
theorem scores_terminal {ω : BondConfig V} {N : ℕ} (hN : (S.stN N ω).choice = none)
    (hX : X ⊆ (S.stN N ω).blk) {n' : ℕ} (hn' : N ≤ n') :
    X.card ≤ nfail S.succOf (S.desigOf X) (S.E.hist n' ω) ∧ ¬AnySucc S.succOf (S.desigOf X) (S.E.hist n' ω) := by
  obtain ⟨h1, h2⟩ := S.scores_hist (X := X) ω n'
  rw [h1, h2, S.stN_eq_of_choice_eq_none hN n' hn']
  have hI := S.inv_mst (S.E.hist N ω)
  constructor
  · exact Finset.card_le_card fun v hv => Finset.mem_filter.2 ⟨hX hv, hv⟩
  · rintro ⟨v, hv, -, hvX⟩
    exact hI.disj v hv (hX hvX)

end Scores

/-! ## The main estimate -/

section Main

variable (G : SimpleGraph V) (p : unitInterval)

/-- **Lawful schemes** (the hypotheses (1)–(5) of KN's exploration process, p. 25, in this library's
form): the probes avoid `U₀` and everything revealed before; along the run on every configuration
consisting of edges of `G` (`P_p`-almost every one), a probe is made whenever a candidate exists;
and after every history with a candidate at which a probe IS made, the probe fails with probability
at most `ε` ((4) = (28): "`P(v ∈ G_{i+1} | G₁, …, G_i, X₁, …, X_i) > p`").
[cite: KozmaNitzan2024, §4 p. 25 (Definition of an exploration process)] -/
structure Lawful (S : HSiteScheme V) (G : SimpleGraph V) (p : unitInterval) (ε : ℝ) : Prop where
  fresh : S.E.Fresh (↑S.U₀ : Set (Sym2 V))
  probes : ∀ ω : BondConfig V, ω ⊆ G.edgeSet → ∀ n, (S.stN n ω).choice ≠ none → S.E.next (S.E.hist n ω) ≠ none
  fail : ∀ h P e, S.E.next h = some P → (S.mst h).choice = some e →
    (bondPercolation G p).real {ω | ¬S.succ h e (P.read ω)} ≤ ε

variable {S G p}
variable {ε : ℝ}

/-- The initial event `A₀ = {U₀ open}` ((5): "`P(G₁ = {0}) > 0`"; KN p. 27: "`G₀ = {(0,0)}` if all
edges of `Q_{(0,0)}` are open"). [cite: KozmaNitzan2024, §4 p. 25 (5), p. 27] -/
def initEvent (S : HSiteScheme V) : Set (BondConfig V) := {ω | (↑S.U₀ : Set (Sym2 V)) ⊆ ω}

/-- `A₀` is determined by `U₀`. [folklore] -/
theorem determinedBy_initEvent : DeterminedBy (initEvent S) (↑S.U₀ : Set (Sym2 V)) := by
  rw [determinedBy_iff]
  intro ω ω' h
  simp only [initEvent, Set.mem_setOf_eq]
  constructor
  · intro hs e he; exact ((Set.ext_iff.1 h e).1 ⟨hs he, he⟩).1
  · intro hs e he; exact ((Set.ext_iff.1 h e).2 ⟨hs he, he⟩).1

/-- `A₀` is measurable. [folklore] -/
theorem measurableSet_initEvent : MeasurableSet (initEvent S) :=
  measurableSet_of_isLocalEvent_holds ⟨_, determinedBy_initEvent⟩

/-- The probability of `A₀` is `p^{|U₀|} > 0` when `U₀ ⊆ E(G)` and `p > 0`. [cite: GrimmettPercolation1999, §7.2 p. 156] -/
theorem initEvent_pos (hU : (↑S.U₀ : Set (Sym2 V)) ⊆ G.edgeSet) (hp : 0 < (p : ℝ)) :
    0 < (bondPercolation G p).real (initEvent S) := by
  rw [initEvent, bondPercolation_real_setOf_subset G p S.U₀ hU]
  exact pow_pos hp _

/-- The event that, from time `N` on, at least `k` designated examinations (for `X`) have failed and
none has succeeded, within `A₀`. [folklore] -/
def charged (S : HSiteScheme V) (X : Finset (LatticeModels.Site 2)) (k N : ℕ) : Set (BondConfig V) :=
  ⋂ n' : ℕ, ⋂ (_ : N ≤ n'), (initEvent S ∩
    {ω | k ≤ nfail S.succOf (S.desigOf X) (S.E.hist n' ω) ∧ ¬AnySucc S.succOf (S.desigOf X) (S.E.hist n' ω)})

/-- `charged` is monotone in the starting time. [folklore] -/
theorem charged_mono (X : Finset (LatticeModels.Site 2)) (k : ℕ) : Monotone (charged S X k) := by
  intro N N' hNN' ω hω
  simp only [charged, Set.mem_iInter] at hω ⊢
  exact fun n' hn' => hω n' (hNN'.trans hn')

/-- **The supermartingale bound per designated set**: `P_p(⋃_N charged X k N) ≤ (2⁻³²)ᵏ P_p(A₀)` when
examinations fail with probability at most `ε ≤ 2⁻³²` (`AExplorer.measureReal_inter_le_nfail_le`).
[cite: GrimmettPercolation1999, §7.2 p. 155] -/
theorem measure_iUnion_charged_le [Countable V] (hL : S.Lawful G p ε) (hε : ε ≤ (1 / 2) ^ 32)
    (X : Finset (LatticeModels.Site 2)) (k : ℕ) :
    bondPercolation G p (⋃ N, charged S X k N) ≤
      ENNReal.ofReal (((1 / 2 : ℝ) ^ 32) ^ k * (bondPercolation G p).real (initEvent S)) := by
  set μ := bondPercolation G p with hμ
  have hfail : ∀ h D, S.E.next h = some D → S.desigOf X h →
      μ.real {ω | ¬S.succOf h (D.read ω)} ≤ 1 - (1 - (1 / 2) ^ 32) := by
    intro h D hD hdes
    cases hc : (S.mst h).choice with
    | none => simp [desigOf, hc] at hdes
    | some e =>
      have hset : {ω | ¬S.succOf h (D.read ω)} = {ω | ¬S.succ h e (D.read ω)} := by
        ext ω; simp [succOf, hc]
      rw [hset]
      have := hL.fail h D e hD hc
      linarith
  have hT2 : ∀ N, μ (charged S X k N) ≤ ENNReal.ofReal (((1 / 2 : ℝ) ^ 32) ^ k * μ.real (initEvent S)) := by
    intro N
    have h := S.E.measureReal_inter_le_nfail_le G p S.succOf (S.desigOf X) hL.fresh determinedBy_initEvent
      measurableSet_initEvent (q := 1 - (1 / 2) ^ 32) (by norm_num) (by norm_num) hfail N k
    have hsub : charged S X k N ⊆ initEvent S ∩
        {ω | k ≤ nfail S.succOf (S.desigOf X) (S.E.hist N ω) ∧ ¬AnySucc S.succOf (S.desigOf X) (S.E.hist N ω)} := by
      intro ω hω
      simp only [charged, Set.mem_iInter] at hω
      exact hω N le_rfl
    calc μ (charged S X k N) ≤ μ (initEvent S ∩ {ω | k ≤ nfail S.succOf (S.desigOf X) (S.E.hist N ω) ∧
          ¬AnySucc S.succOf (S.desigOf X) (S.E.hist N ω)}) := measure_mono hsub
      _ = ENNReal.ofReal (μ.real (initEvent S ∩ {ω | k ≤ nfail S.succOf (S.desigOf X) (S.E.hist N ω) ∧
          ¬AnySucc S.succOf (S.desigOf X) (S.E.hist N ω)})) := (ofReal_measureReal (measure_ne_top _ _)).symm
      _ ≤ ENNReal.ofReal (((1 / 2 : ℝ) ^ 32) ^ k * μ.real (initEvent S)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have h' : (1 - (1 - (1 / 2 : ℝ) ^ 32)) = (1 / 2) ^ 32 := by ring
          rw [h'] at h
          exact h
  rw [(charged_mono (S := S) X k).measure_iUnion]
  exact iSup_le hT2

/-- **Cover**: on `A₀` and for a configuration of edges of `G`, if the final macro-cluster is finite
then some dual circuit (indexed by its length `n`, the plaquette `(k,0)`, `k < n`, the position
`m ≤ n` of that plaquette, and the word `w`) carries a designated set `X` of blocked vertices, fully
charged from some time on. [cite: GrimmettPercolation1999, §7.2 p. 155 and §1.4 p. 16] -/
theorem initEvent_inter_finite_subset (hL : S.Lawful G p ε) :
    initEvent S ∩ {ω | (S.occFinal ω).Finite} ∩ {ω | ω ⊆ G.edgeSet} ⊆
      ⋃ n : ℕ, ⋃ k ∈ Finset.range n, ⋃ m ∈ Finset.range (n + 1),
        ⋃ w ∈ (Finset.univ.filter fun w : Fin n → MDir =>
            (dualEdges (Pi.single 0 (k : ℤ) - wordPos w m) w).card = n),
          ⋃ X ∈ SiteGadgetSystem.desigSets (dualEdges (Pi.single 0 (k : ℤ) - wordPos w m) w) n,
            ⋃ N, charged S X X.card N := by
  rintro ω ⟨⟨hA, hfin⟩, hωE⟩
  obtain ⟨N, hN, n, k, hkn, w, m, hmn, hcard, hcov⟩ := S.exists_dualCircuit_blk (hL.probes ω hωE) hfin
  set Γ := dualEdges (Pi.single 0 (k : ℤ) - wordPos w m) w with hΓ
  set X := (SiteGadgetSystem.vertsOf Γ).filter fun v => v ∈ (S.stN N ω).blk with hX
  have hXblk : X ⊆ (S.stN N ω).blk := fun v hv => (Finset.mem_filter.1 hv).2
  have hXmem : X ∈ SiteGadgetSystem.desigSets Γ n := by
    rw [SiteGadgetSystem.desigSets, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.filter_subset _ _, ?_⟩
    rw [← hcard]
    refine SiteGadgetSystem.card_le_four_mul_card (fun x hx => (hcov x hx).1) fun x hx => ?_
    obtain ⟨-, v, hv, hvx⟩ := hcov x hx
    exact ⟨v, Finset.mem_filter.2 ⟨SiteGadgetSystem.mem_vertsOf.2 ⟨x, hx, hvx⟩, hv⟩, hvx⟩
  refine Set.mem_iUnion.2 ⟨n, Set.mem_biUnion (Finset.mem_range.2 hkn)
    (Set.mem_biUnion (Finset.mem_range.2 (Nat.lt_succ_of_le hmn))
      (Set.mem_biUnion (x := w) (by simp [← hΓ, hcard])
        (Set.mem_biUnion hXmem (Set.mem_iUnion.2 ⟨N, ?_⟩))))⟩
  simp only [charged, Set.mem_iInter]
  intro n' hn'
  exact ⟨hA, S.scores_terminal hN hXblk hn'⟩

/-- **A supercritical exploration process percolates** (Kozma–Nitzan 2024, p. 25: "if `(G_i, X_i)`
is an exploration process then `P(lim |G_i| = ∞) > 0`", with the explicit threshold `ε ≤ 2⁻³²` for
the failure probability in place of "`p > p_c(ℤ², site)`"): for a lawful scheme,
`P_p(A₀ ∩ {final macro-cluster finite}) ≤ ⅔ P_p(A₀)`, by the Peierls sum `Σₙ n(n+1)4ⁿ 64⁻ⁿ ≤ ⅔`
over dual circuits and their designated blocked sets (as in `DynamicSiteRenormalization.lean`).
[cite: KozmaNitzan2024, §4 p. 25] -/
theorem measure_initEvent_inter_finite_le [Countable V] (hL : S.Lawful G p ε) (hε : ε ≤ (1 / 2) ^ 32) :
    bondPercolation G p (initEvent S ∩ {ω | (S.occFinal ω).Finite}) ≤
      ENNReal.ofReal (2 / 3 * (bondPercolation G p).real (initEvent S)) := by
  classical
  set μ := bondPercolation G p with hμ
  set A := μ.real (initEvent S) with hAdef
  let Γ : (n : ℕ) → ℕ → ℕ → (Fin n → MDir) → Finset (Sym2 (LatticeModels.Site 2)) := fun n k m w =>
    dualEdges (Pi.single 0 (k : ℤ) - wordPos w m) w
  let good : (n : ℕ) → ℕ → ℕ → Finset (Fin n → MDir) := fun n k m =>
    Finset.univ.filter fun w => (Γ n k m w).card = n
  let T : Finset (LatticeModels.Site 2) → Set (BondConfig V) := fun X => ⋃ N, charged S X X.card N
  let W : ℕ → Set (BondConfig V) := fun n =>
    ⋃ k ∈ Finset.range n, ⋃ m ∈ Finset.range (n + 1), ⋃ w ∈ good n k m,
      ⋃ X ∈ SiteGadgetSystem.desigSets (Γ n k m w) n, T X
  have hA0 : 0 ≤ A := measureReal_nonneg
  have hT : ∀ X, μ (T X) ≤ ENNReal.ofReal (((1 / 2 : ℝ) ^ 32) ^ X.card * A) :=
    fun X => measure_iUnion_charged_le hL hε X X.card
  have hTX : ∀ (n : ℕ) (X : Finset (LatticeModels.Site 2)), n ≤ 4 * X.card →
      μ (T X) ≤ ENNReal.ofReal ((1 / 256 : ℝ) ^ n * A) := by
    intro n X hX
    refine (hT X).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ hA0))
    calc ((1 / 2 : ℝ) ^ 32) ^ X.card = (1 / 2) ^ (32 * X.card) := by rw [pow_mul]
      _ ≤ (1 / 2) ^ (8 * n) := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = (1 / 256) ^ n := by rw [pow_mul]; norm_num
  have hGX : ∀ (n k m : ℕ) (w : Fin n → MDir), w ∈ good n k m →
      μ (⋃ X ∈ SiteGadgetSystem.desigSets (Γ n k m w) n, T X) ≤ ENNReal.ofReal ((1 / 64 : ℝ) ^ n * A) := by
    intro n k m w hw
    have hcard : (Γ n k m w).card = n := (Finset.mem_filter.1 hw).2
    calc μ (⋃ X ∈ SiteGadgetSystem.desigSets (Γ n k m w) n, T X)
        ≤ ∑ X ∈ SiteGadgetSystem.desigSets (Γ n k m w) n, μ (T X) := measure_biUnion_finset_le _ _
      _ ≤ ∑ X ∈ SiteGadgetSystem.desigSets (Γ n k m w) n, ENNReal.ofReal ((1 / 256 : ℝ) ^ n * A) := by
          refine Finset.sum_le_sum fun X hX => hTX n X ?_
          exact (Finset.mem_filter.1 hX).2
      _ = ((SiteGadgetSystem.desigSets (Γ n k m w) n).card : ℝ≥0∞) * ENNReal.ofReal ((1 / 256 : ℝ) ^ n * A) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((4 ^ n : ℕ) : ℝ≥0∞) * ENNReal.ofReal ((1 / 256 : ℝ) ^ n * A) := by
          gcongr; exact_mod_cast SiteGadgetSystem.card_desigSets_le hcard
      _ = ENNReal.ofReal ((1 / 64 : ℝ) ^ n * A) := by
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          push_cast
          rw [← mul_assoc, ← mul_pow]
          norm_num
  have hW : ∀ n, μ (W n) ≤ ENNReal.ofReal (1 / 2 * (1 / 4) ^ n * A) := by
    intro n
    calc μ (W n)
        ≤ ∑ k ∈ Finset.range n, μ (⋃ m ∈ Finset.range (n + 1), ⋃ w ∈ good n k m,
            ⋃ X ∈ SiteGadgetSystem.desigSets (Γ n k m w) n, T X) :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ k ∈ Finset.range n, ∑ m ∈ Finset.range (n + 1), μ (⋃ w ∈ good n k m,
            ⋃ X ∈ SiteGadgetSystem.desigSets (Γ n k m w) n, T X) := by
          gcongr; exact measure_biUnion_finset_le _ _
      _ ≤ ∑ k ∈ Finset.range n, ∑ m ∈ Finset.range (n + 1), ∑ w ∈ good n k m,
            μ (⋃ X ∈ SiteGadgetSystem.desigSets (Γ n k m w) n, T X) := by
          gcongr; exact measure_biUnion_finset_le _ _
      _ ≤ ∑ k ∈ Finset.range n, ∑ m ∈ Finset.range (n + 1), ∑ w ∈ good n k m,
            ENNReal.ofReal ((1 / 64 : ℝ) ^ n * A) := by
          gcongr with k _ m _ w hw; exact hGX n k m w hw
      _ ≤ ∑ k ∈ Finset.range n, ∑ m ∈ Finset.range (n + 1), ∑ w : Fin n → MDir,
            ENNReal.ofReal ((1 / 64 : ℝ) ^ n * A) := by
          gcongr; exact Finset.subset_univ _
      _ = ENNReal.ofReal (((n * ((n + 1) * (2 * 2) ^ n) : ℕ) : ℝ) * ((1 / 64 : ℝ) ^ n * A)) := by
          rw [Finset.sum_const, Finset.sum_const, Finset.sum_const, Finset.card_range,
            Finset.card_range, Finset.card_univ, Fintype.card_fun, Fintype.card_prod,
            Fintype.card_fin, Fintype.card_fin, Fintype.card_bool, smul_smul, smul_smul, nsmul_eq_mul,
            ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, Nat.mul_assoc]
      _ ≤ ENNReal.ofReal (1 / 2 * (1 / 4) ^ n * A) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 := mul_le_mul_of_nonneg_right (peierls_term_le n) hA0
          have h2 : (((n * ((n + 1) * (2 * 2) ^ n) : ℕ) : ℝ) * ((1 / 64 : ℝ) ^ n * A)) =
              (n : ℝ) * (n + 1) * 4 ^ n * (1 - 63 / 64) ^ n * A := by
            push_cast; ring
          rw [h2]
          exact h1
  have hsum : (∑' n, ENNReal.ofReal (1 / 2 * (1 / 4 : ℝ) ^ n * A)) = ENNReal.ofReal (2 / 3 * A) := by
    have hg : Summable fun n : ℕ => (1 / 2 : ℝ) * (1 / 4) ^ n * A :=
      ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _).mul_right _
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hg, tsum_mul_right, tsum_mul_left,
      tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  have hcover : initEvent S ∩ {ω | (S.occFinal ω).Finite} ∩ {ω | ω ⊆ G.edgeSet} ⊆ ⋃ n, W n :=
    initEvent_inter_finite_subset hL
  have hae : (initEvent S ∩ {ω | (S.occFinal ω).Finite} : Set (BondConfig V)) ≤ᵐ[μ]
      (initEvent S ∩ {ω | (S.occFinal ω).Finite} ∩ {ω | ω ⊆ G.edgeSet} : Set (BondConfig V)) := by
    filter_upwards [(setBernoulli_ae_subset : ∀ᵐ ω ∂μ, ω ⊆ G.edgeSet)] with ω hωE
    exact fun hω => ⟨hω, hωE⟩
  exact (measure_mono_ae hae).trans ((measure_mono hcover).trans
    ((measure_iUnion_le W).trans ((ENNReal.tsum_le_tsum hW).trans hsum.le)))

/-- **The macro-cluster is infinite with positive probability**: for a lawful scheme with
`ε ≤ 2⁻³²` and ANY event `T` containing `A₀ ∩ {final macro-cluster infinite}`, `P_p(T) ≥ P_p(A₀)/3`.
[cite: KozmaNitzan2024, §4 p. 25 ("P(lim |G_i| = ∞) > 0")] -/
theorem measureReal_le_three_mul_of_subset [Countable V] (hL : S.Lawful G p ε) (hε : ε ≤ (1 / 2) ^ 32)
    {T : Set (BondConfig V)} (hT : initEvent S ∩ {ω | (S.occFinal ω).Infinite} ⊆ T) :
    (bondPercolation G p).real (initEvent S) ≤ 3 * (bondPercolation G p).real T := by
  set μ := bondPercolation G p with hμ
  have hsplit : μ (initEvent S) ≤ μ T + ENNReal.ofReal (2 / 3 * μ.real (initEvent S)) :=
    calc μ (initEvent S) ≤ μ (initEvent S ∩ {ω | (S.occFinal ω).Infinite}) + μ (initEvent S \ {ω | (S.occFinal ω).Infinite}) :=
        measure_le_inter_add_sdiff _ _ _
      _ ≤ μ T + μ (initEvent S ∩ {ω | (S.occFinal ω).Finite}) := by
        refine add_le_add (measure_mono hT) (measure_mono ?_)
        rintro ω ⟨hA, hinf⟩
        exact ⟨hA, Set.not_infinite.1 hinf⟩
      _ ≤ μ T + ENNReal.ofReal (2 / 3 * μ.real (initEvent S)) :=
        add_le_add le_rfl (measure_initEvent_inter_finite_le hL hε)
  have h1 : μ.real (initEvent S) ≤ μ.real T + 2 / 3 * μ.real (initEvent S) := by
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, ENNReal.ofReal_ne_top⟩) hsplit
    rw [ENNReal.toReal_add (measure_ne_top _ _) ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal (by positivity)] at this
    exact this
  change μ.real (initEvent S) ≤ 3 * μ.real T
  linarith

end Main

end HSiteScheme

end Percolation.Literature
