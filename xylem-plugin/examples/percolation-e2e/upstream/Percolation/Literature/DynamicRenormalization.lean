import Percolation.Literature.AdaptiveProbing
import Percolation.Literature.MacroRenormalization
import Percolation.Util.Linter

/-!
# Dynamic renormalization with adaptive attempts: a gadget system percolates

This is the form of `MacroRenormalization.lean`
(Grimmett, *Percolation*, 2nd ed. (1999), §7.3, proof of Lemma (7.52), pp. 169–176) needed by an
actual brick construction. There, an attempt along a directed macro-edge `(a, d)` is itself a
dynamic examination (bricks stacked one by one), the set of edges it examines depends on the
configuration, and the next attempt starts at the seed where this one stopped — at a position
known only at run time. The static axiom of `MacroRenormalization.lean` ("regions of distinct
directed macro-edges are disjoint for all admissible tokens") cannot then hold between an attempt
and the attempts it enables: the a-priori region of the parent contains every possible position of
its last brick, next to which the child starts. Grimmett's requirement (C), p. 173, is indeed
dynamic: "the intersection of a new brick with the region considered SO FAR must be limited to a
subset of its underside".

Accordingly an **adaptive gadget system** (`AGadgetSystem`) specifies, for the attempt along
`(a, d)` from the token `τ`: an a-priori envelope `zone a d τ`; the configuration-dependent set
`reveal a d τ ω ⊆ zone a d τ` of edges examined, *local* in the sense of `AdaptiveProbing.lean`;
the outcome `result a d τ o` read off the open edges `o` observed; and the provenance
`srcDir τ'` of a token (the direction of the attempt that produced it). The axioms
(`AGadgetSystem.Lawful`) require: (i) STATIC disjointness of the envelopes of two attempts from
admissible tokens along distinct directed macro-edges `(a,d)`, `(a',d')` with `a' ≠ a + d` (the
earlier attempt starts at an occupied macro-vertex, the new one targets an unoccupied one), UNLESS
`(a', d')` is the parent edge of `τ` (`a' + d' = a`, `srcDir τ = d'`); (ii) DYNAMIC disjointness
for the parent: the edges an attempt actually examines avoid the envelopes of the attempts from
the tokens it returns (a field of the structure, `parent_disjoint`); (iii) envelopes of attempts
towards macro-vertices other than the origin avoid `U₀`; (iv) an attempt from an admissible token
fails with probability at most `ε`; and the admissibility/connectivity axioms of
`MacroRenormalization.lean`, read with the adaptive outcome. The macro-lattice is explored edge by
edge exactly as there, each attempt being one ADAPTIVE probe (`AdaptiveProbing.lean`); the replay
of a history checks the recorded examined sets against the envelopes and against (ii), so that
freshness holds along every history (`fresh_explorer`), and the Peierls estimate over dual circuits
(`ε ≤ 1/64`) gives `θ_{x₀}(p) > 0` (`AGadgetSystem.theta_pos`) verbatim.

## References

* G. Grimmett, *Percolation*, 2nd ed., Grundlehren 321, Springer 1999, §7.2 pp. 152–157, §7.3
  pp. 169–176, §1.4 pp. 15–18 (Peierls' argument).
* D. J. Barsky, G. R. Grimmett, C. M. Newman, Dynamic renormalization and continuity of the
  percolation transition in orthants, in *Spatial Stochastic Processes*, Birkhäuser 1991, 37–55.
-/

noncomputable section

namespace Percolation.Literature

open MeasureTheory ProbabilityTheory Contour ProbeHistory
open scoped ENNReal Classical

/-- An **adaptive gadget system** over bond configurations on `V`, indexed by the directed edges of
the square macro-lattice: tokens (with an anchor vertex and a provenance direction), the initial
open edge set `U₀` and initial tokens, admissibility, the a-priori envelope of an attempt, the
configuration-dependent set of edges it examines (inside the envelope, local), its outcome as a
function of the open edges observed, and the dynamic disjointness of the examined edges from the
envelopes of the attempts it enables. (Grimmett 1999, §7.3 pp. 171–174, (C) p. 173.)
[cite: GrimmettPercolation1999, §7.3 pp. 171–174] -/
structure AGadgetSystem (V : Type*) where
  /-- tokens: the data handed from a successful attempt to the attempts it enables -/
  Tok : Type
  /-- the vertex of `V` a token certifies as reached -/
  anchor : Tok → V
  /-- the direction of the attempt that produced the token (`none` for initial tokens) -/
  srcDir : Tok → Option MDir
  /-- the initial edges, all required to be open (Grimmett's set `E`, (7.55)) -/
  U₀ : Finset (Sym2 V)
  /-- the initial tokens at the macro-origin, one per direction -/
  init : MDir → Tok
  /-- admissibility of a token for the attempt along the directed macro-edge `(a, d)` -/
  Adm : LatticeModels.Site 2 → MDir → Tok → Prop
  /-- the a-priori envelope of the attempt along `(a, d)` from the token `τ` -/
  zone : LatticeModels.Site 2 → MDir → Tok → Finset (Sym2 V)
  /-- the edges examined by the attempt on the configuration `ω` -/
  reveal : LatticeModels.Site 2 → MDir → Tok → BondConfig V → Finset (Sym2 V)
  /-- the examined edges lie in the envelope -/
  reveal_subset : ∀ a d τ ω, reveal a d τ ω ⊆ zone a d τ
  /-- locality of the examined set -/
  reveal_local : ∀ a d τ (ω ω' : BondConfig V), (∀ e ∈ reveal a d τ ω, (e ∈ ω ↔ e ∈ ω')) →
    reveal a d τ ω' = reveal a d τ ω
  /-- the outcome of the attempt given the open edges observed -/
  result : LatticeModels.Site 2 → MDir → Tok → Finset (Sym2 V) → Option (MDir → Tok)
  /-- dynamic disjointness (Grimmett's (C)): the edges examined by a successful attempt avoid the
  envelopes of the onward attempts from the tokens it returns -/
  parent_disjoint : ∀ a d τ (ω : BondConfig V) (f : MDir → Tok),
    result a d τ (obs ω (reveal a d τ ω)) = some f → ∀ d', d' ≠ rev d →
      Disjoint (reveal a d τ ω) (zone (a + stepVec d) d' (f d'))

namespace AGadgetSystem

export GadgetSystem (tgt tgt_tgt_rev stepVec_injective_two eq_or_rev_of_edge_eq mem_openCluster_trans)

variable {V : Type*} (S : AGadgetSystem V)

/-- The adaptive probe of the attempt along `(a, d)` from `τ`. [folklore] -/
def probe (a : LatticeModels.Site 2) (d : MDir) (τ : S.Tok) : AProbe V :=
  ⟨S.zone a d τ, S.reveal a d τ, S.reveal_subset a d τ, S.reveal_local a d τ⟩

/-- The probe examines `reveal`. [folklore] -/
@[simp] theorem reveal_probe (a : LatticeModels.Site 2) (d : MDir) (τ : S.Tok) (ω : BondConfig V) :
    (S.probe a d τ).reveal ω = S.reveal a d τ ω := rfl

/-- The probe's envelope is the zone. [folklore] -/
@[simp] theorem env_probe (a : LatticeModels.Site 2) (d : MDir) (τ : S.Tok) : (S.probe a d τ).env = S.zone a d τ := rfl

/-- The probe reads the open examined edges. [folklore] -/
theorem read_probe (a : LatticeModels.Site 2) (d : MDir) (τ : S.Tok) (ω : BondConfig V) :
    (S.probe a d τ).read ω = obs ω (S.reveal a d τ ω) := rfl

/-! ## The macro-state and its replay from a probing history -/

/-- The state of the macro-exploration: occupied macro-vertices, their tokens, the directed
macro-edges examined so far and those among them that failed. [cite: GrimmettPercolation1999, §7.3 p. 171] -/
structure MState where
  /-- occupied macro-vertices -/
  occ : Finset (LatticeModels.Site 2)
  /-- the tokens held at macro-vertices (meaningful on `occ` only) -/
  tok : LatticeModels.Site 2 → MDir → S.Tok
  /-- examined directed macro-edges -/
  exam : Finset (LatticeModels.Site 2 × MDir)
  /-- examined directed macro-edges whose attempt failed -/
  fails : Finset (LatticeModels.Site 2 × MDir)

/-- The initial state: the origin occupied with the initial tokens. [cite: GrimmettPercolation1999, §7.3 p. 171] -/
def MState.start : S.MState := ⟨{0}, fun _ d => S.init d, ∅, ∅⟩

variable {S}

/-- A directed macro-edge is a candidate for the next attempt: its source is occupied, its target is
not, and it has not been examined. [cite: GrimmettPercolation1999, §7.3 p. 171] -/
def MState.Cand (st : S.MState) (e : LatticeModels.Site 2 × MDir) : Prop :=
  e.1 ∈ st.occ ∧ tgt e ∉ st.occ ∧ e ∉ st.exam

/-- The next directed macro-edge to attempt: the candidate of least code (`Encodable.encode`, the
"predetermined ordering" of Grimmett p. 171), if any. [cite: GrimmettPercolation1999, §7.3 p. 171] -/
def MState.choice (st : S.MState) : Option (LatticeModels.Site 2 × MDir) :=
  if h : ∃ n, ∃ e, st.Cand e ∧ Encodable.encode e = n then
    some (Classical.choose (Nat.find_spec h))
  else none

/-- The chosen edge is a candidate. [folklore] -/
theorem MState.cand_of_choice {st : S.MState} {e : LatticeModels.Site 2 × MDir} (h : st.choice = some e) : st.Cand e := by
  unfold MState.choice at h
  split_ifs at h with hex
  cases h
  exact (Classical.choose_spec (Nat.find_spec hex)).1

/-- If there is no chosen edge, there is no candidate. [folklore] -/
theorem MState.not_cand_of_choice_eq_none {st : S.MState} (h : st.choice = none) (e : LatticeModels.Site 2 × MDir) :
    ¬st.Cand e := by
  intro hc
  have hex : ∃ n, ∃ e, st.Cand e ∧ Encodable.encode e = n := ⟨Encodable.encode e, e, hc, rfl⟩
  unfold MState.choice at h
  rw [dif_pos hex] at h
  simp at h

/-- The update of the state by the outcome of the attempt along `e` with observation `o`.
[cite: GrimmettPercolation1999, §7.3 p. 174] -/
def MState.update (st : S.MState) (e : LatticeModels.Site 2 × MDir) (o : Finset (Sym2 V)) : S.MState :=
  match S.result e.1 e.2 (st.tok e.1 e.2) o with
  | none => ⟨st.occ, st.tok, insert e st.exam, insert e st.fails⟩
  | some f => ⟨insert (tgt e) st.occ, Function.update st.tok (tgt e) f, insert e st.exam, st.fails⟩

/-- The probe the state would make next. [folklore] -/
def MState.nextProbe (st : S.MState) : Option (AProbe V) :=
  st.choice.map fun e => S.probe e.1 e.2 (st.tok e.1 e.2)

/-- A record `r` is acceptable for the attempt along `e` from `τ`: its examined set lies in the
envelope, its observation in its examined set, and — if the attempt succeeds on it — its examined
set avoids the envelopes of the onward attempts (the dynamic condition (C)). [cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
def RecOK (e : LatticeModels.Site 2 × MDir) (τ : S.Tok) (r : ProbeRecord V) : Prop :=
  r.1 ⊆ S.zone e.1 e.2 τ ∧ r.2 ⊆ r.1 ∧
    ∀ f, S.result e.1 e.2 τ r.2 = some f → ∀ d', d' ≠ rev e.2 → Disjoint r.1 (S.zone (tgt e) d' (f d'))

/-- The actual record of an attempt is acceptable. [folklore] -/
theorem recOK_record (e : LatticeModels.Site 2 × MDir) (τ : S.Tok) (ω : BondConfig V) :
    RecOK e τ ((S.probe e.1 e.2 τ).record ω) :=
  ⟨S.reveal_subset _ _ _ ω, obs_subset _ _, fun f hf d' hd' => S.parent_disjoint e.1 e.2 τ ω f hf d' hd'⟩

variable (S)

/-- Replay of a probing history (newest entry first): the macro-state it leads to, or `none` if the
history is not one this exploration can produce (an unacceptable record). [folklore] -/
def replay : ProbeHistory V → Option S.MState
  | [] => some (MState.start S)
  | none :: h => replay h
  | some r :: h =>
    (replay h).bind fun st =>
      match st.choice with
      | none => none
      | some e => if RecOK e (st.tok e.1 e.2) r then some (st.update e r.2) else none

/-- **The macro-explorer**: after a history, make the adaptive probe of the chosen directed
macro-edge. [cite: GrimmettPercolation1999, §7.3 p. 171] -/
def explorer : AExplorer V :=
  ⟨fun h => (S.replay h).bind fun st => st.nextProbe⟩

/-- One step of the macro-exploration on `ω`: attempt the chosen edge, if any.
[cite: GrimmettPercolation1999, §7.3 p. 171] -/
def stepSt (st : S.MState) (ω : BondConfig V) : S.MState :=
  match st.choice with
  | none => st
  | some e => st.update e (obs ω (S.reveal e.1 e.2 (st.tok e.1 e.2) ω))

/-- The macro-state after `n` steps of the exploration on `ω`. [cite: GrimmettPercolation1999, §7.3 p. 171] -/
def stN : ℕ → BondConfig V → S.MState
  | 0, _ => MState.start S
  | n + 1, ω => S.stepSt (stN n ω) ω

/-- Unfolding one step. [folklore] -/
theorem stN_succ (n : ℕ) (ω : BondConfig V) : S.stN (n + 1) ω = S.stepSt (S.stN n ω) ω := rfl

/-- The replay of the actual history is the directly defined state. [folklore] -/
theorem replay_hist (n : ℕ) (ω : BondConfig V) : S.replay (S.explorer.hist n ω) = some (S.stN n ω) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [AExplorer.hist_succ]
    have hnext : S.explorer.next (S.explorer.hist n ω) = (S.stN n ω).nextProbe := by
      show ((S.replay (S.explorer.hist n ω)).bind fun st => st.nextProbe) = _
      rw [ih]; rfl
    cases hc : (S.stN n ω).choice with
    | none =>
      have hnone : S.explorer.next (S.explorer.hist n ω) = none := by
        rw [hnext, MState.nextProbe, hc]; rfl
      rw [S.explorer.step_of_none hnone, replay, ih, stN_succ, stepSt, hc]
    | some e =>
      have hsome : S.explorer.next (S.explorer.hist n ω) =
          some (S.probe e.1 e.2 ((S.stN n ω).tok e.1 e.2)) := by
        rw [hnext, MState.nextProbe, hc]; rfl
      rw [S.explorer.step_of_some hsome, replay, ih, stN_succ, stepSt, hc]
      simp only [Option.bind_some, hc]
      rw [if_pos (recOK_record e _ ω)]
      rfl

/-- The next probe of the macro-explorer on the actual history. [folklore] -/
theorem next_hist (n : ℕ) (ω : BondConfig V) :
    S.explorer.next (S.explorer.hist n ω) = (S.stN n ω).nextProbe := by
  show ((S.replay (S.explorer.hist n ω)).bind fun st => st.nextProbe) = _
  rw [replay_hist]; rfl

/-- One step of the directly defined state when an edge is chosen. [folklore] -/
theorem stN_succ_of_choice {n : ℕ} {ω : BondConfig V} {e : LatticeModels.Site 2 × MDir} (hc : (S.stN n ω).choice = some e) :
    S.stN (n + 1) ω = (S.stN n ω).update e (obs ω (S.reveal e.1 e.2 ((S.stN n ω).tok e.1 e.2) ω)) := by
  rw [stN_succ, stepSt, hc]

/-- One step of the directly defined state when no edge is chosen. [folklore] -/
theorem stN_succ_of_none {n : ℕ} {ω : BondConfig V} (hc : (S.stN n ω).choice = none) :
    S.stN (n + 1) ω = S.stN n ω := by
  rw [stN_succ, stepSt, hc]

/-! ## Elementary properties of the update -/

section Update

variable {S}
variable (st : S.MState) (e : LatticeModels.Site 2 × MDir) (o : Finset (Sym2 V))

/-- The update after a failed attempt. [folklore] -/
theorem MState.update_of_none (h : S.result e.1 e.2 (st.tok e.1 e.2) o = none) :
    st.update e o = ⟨st.occ, st.tok, insert e st.exam, insert e st.fails⟩ := by
  rw [MState.update, h]

/-- The update after a successful attempt. [folklore] -/
theorem MState.update_of_some {f : MDir → S.Tok} (h : S.result e.1 e.2 (st.tok e.1 e.2) o = some f) :
    st.update e o = ⟨insert (tgt e) st.occ, Function.update st.tok (tgt e) f, insert e st.exam, st.fails⟩ := by
  rw [MState.update, h]

/-- Occupied vertices stay occupied. [folklore] -/
theorem MState.occ_subset_update : st.occ ⊆ (st.update e o).occ := by
  cases h : S.result e.1 e.2 (st.tok e.1 e.2) o with
  | none => rw [st.update_of_none e o h]
  | some f => rw [st.update_of_some e o h]; exact Finset.subset_insert _ _

/-- The examined set gains exactly the attempted edge. [folklore] -/
@[simp] theorem MState.exam_update : (st.update e o).exam = insert e st.exam := by
  cases h : S.result e.1 e.2 (st.tok e.1 e.2) o with
  | none => rw [st.update_of_none e o h]
  | some f => rw [st.update_of_some e o h]

/-- Failed edges stay failed. [folklore] -/
theorem MState.fails_subset_update : st.fails ⊆ (st.update e o).fails := by
  cases h : S.result e.1 e.2 (st.tok e.1 e.2) o with
  | none => rw [st.update_of_none e o h]; exact Finset.subset_insert _ _
  | some f => rw [st.update_of_some e o h]

/-- Tokens away from the target are unchanged. [folklore] -/
theorem MState.tok_update_of_ne {a : LatticeModels.Site 2} (ha : a ≠ tgt e) : (st.update e o).tok a = st.tok a := by
  cases h : S.result e.1 e.2 (st.tok e.1 e.2) o with
  | none => rw [st.update_of_none e o h]
  | some f => rw [st.update_of_some e o h]; exact Function.update_of_ne ha _ _

end Update

/-! ## Combinatorial invariants of reachable states -/

section Invariants

variable {S}

/-- The invariants of the macro-state maintained by the exploration: the origin is occupied;
examined edges start at occupied vertices; failed edges were examined; a successful edge has an
occupied target; an edge and its reversal are never both examined.
[cite: GrimmettPercolation1999, §7.3 p. 171] -/
structure MState.Inv (st : S.MState) : Prop where
  zero_mem : (0 : LatticeModels.Site 2) ∈ st.occ
  exam_src : ∀ e ∈ st.exam, e.1 ∈ st.occ
  fails_sub : st.fails ⊆ st.exam
  succ_tgt : ∀ e ∈ st.exam, e ∉ st.fails → tgt e ∈ st.occ
  no_rev : ∀ e ∈ st.exam, (tgt e, rev e.2) ∉ st.exam

/-- The initial state satisfies the invariants. [folklore] -/
theorem MState.Inv.start : (MState.start S).Inv where
  zero_mem := Finset.mem_singleton_self _
  exam_src := by simp [MState.start]
  fails_sub := by simp [MState.start]
  succ_tgt := by simp [MState.start]
  no_rev := by simp [MState.start]

/-- The invariants are preserved by an attempt along a candidate edge. [folklore] -/
theorem MState.Inv.update {st : S.MState} (hI : st.Inv) {e : LatticeModels.Site 2 × MDir} (he : st.Cand e)
    (o : Finset (Sym2 V)) : (st.update e o).Inv := by
  obtain ⟨he1, he2, he3⟩ := he
  -- the reversed edge from the target has not been examined, and no examined edge reverses to `e`
  have hrev1 : (tgt e, rev e.2) ∉ st.exam := fun hm => he2 (hI.exam_src _ hm)
  have hrev2 : ∀ e' ∈ st.exam, (tgt e', rev e'.2) ≠ e := by
    rintro e' he' rfl
    exact he2 (by rw [tgt_tgt_rev]; exact hI.exam_src e' he')
  cases h : S.result e.1 e.2 (st.tok e.1 e.2) o with
  | none =>
    rw [st.update_of_none e o h]
    refine ⟨hI.zero_mem, ?_, ?_, ?_, ?_⟩
    · intro e' he'
      rcases Finset.mem_insert.1 he' with rfl | he'
      · exact he1
      · exact hI.exam_src e' he'
    · exact Finset.insert_subset_insert _ hI.fails_sub
    · intro e' he' hnf
      rcases Finset.mem_insert.1 he' with rfl | he'
      · exact absurd (Finset.mem_insert_self _ _) hnf
      · exact hI.succ_tgt e' he' fun hf => hnf (Finset.mem_insert_of_mem hf)
    · intro e' he'
      rcases Finset.mem_insert.1 he' with rfl | he'
      · rw [Finset.mem_insert, not_or]
        exact ⟨fun hq => rev_ne_self e'.2 (congrArg Prod.snd hq), hrev1⟩
      · rw [Finset.mem_insert, not_or]
        exact ⟨hrev2 e' he', hI.no_rev e' he'⟩
  | some f =>
    rw [st.update_of_some e o h]
    refine ⟨Finset.mem_insert_of_mem hI.zero_mem, ?_, ?_, ?_, ?_⟩
    · intro e' he'
      rcases Finset.mem_insert.1 he' with rfl | he'
      · exact Finset.mem_insert_of_mem he1
      · exact Finset.mem_insert_of_mem (hI.exam_src e' he')
    · exact hI.fails_sub.trans (Finset.subset_insert _ _)
    · intro e' he' hnf
      rcases Finset.mem_insert.1 he' with rfl | he'
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (hI.succ_tgt e' he' hnf)
    · intro e' he'
      rcases Finset.mem_insert.1 he' with rfl | he'
      · rw [Finset.mem_insert, not_or]
        exact ⟨fun hq => rev_ne_self e'.2 (congrArg Prod.snd hq), hrev1⟩
      · rw [Finset.mem_insert, not_or]
        exact ⟨hrev2 e' he', hI.no_rev e' he'⟩

/-- With no candidate left, every macro-edge out of an occupied vertex either leads to an occupied
vertex or has failed. [cite: GrimmettPercolation1999, §7.3 p. 171] -/
theorem MState.Inv.closed {st : S.MState} (hI : st.Inv) (hc : st.choice = none) {u : LatticeModels.Site 2} (hu : u ∈ st.occ)
    (d : MDir) : u + stepVec d ∈ st.occ ∨ (u, d) ∈ st.fails := by
  by_contra hcon
  rw [not_or] at hcon
  refine MState.not_cand_of_choice_eq_none hc (u, d) ⟨hu, hcon.1, fun hex => ?_⟩
  by_cases hf : (u, d) ∈ st.fails
  · exact hcon.2 hf
  · exact hcon.1 (hI.succ_tgt _ hex hf)

end Invariants

/-! ## Admissibility and provenance of the tokens in play -/

section Admissibility

variable {S}

/-- The axioms on admissibility and provenance: initial tokens are admissible with no provenance,
and a successful attempt from an admissible token returns admissible tokens for the onward
directions, of provenance the direction of the attempt. [cite: GrimmettPercolation1999, §7.3 pp. 172–174] -/
structure AdmAxioms (S : AGadgetSystem V) : Prop where
  adm_init : ∀ d, S.Adm 0 d (S.init d)
  src_init : ∀ d, S.srcDir (S.init d) = none
  adm_result : ∀ {a : LatticeModels.Site 2} {d : MDir} {τ : S.Tok} {o : Finset (Sym2 V)} {f : MDir → S.Tok},
    S.Adm a d τ → S.result a d τ o = some f → ∀ d', d' ≠ rev d → S.Adm (a + stepVec d) d' (f d')
  src_result : ∀ {a : LatticeModels.Site 2} {d : MDir} {τ : S.Tok} {o : Finset (Sym2 V)} {f : MDir → S.Tok},
    S.Adm a d τ → S.result a d τ o = some f → ∀ d', S.srcDir (f d') = some d

/-- Every token that can still be used is admissible. [folklore] -/
def MState.AdmInv (st : S.MState) : Prop :=
  ∀ a ∈ st.occ, ∀ d, a + stepVec d ∉ st.occ → S.Adm a d (st.tok a d)

/-- The initial state holds admissible tokens. [folklore] -/
theorem AdmAxioms.admInv_start (hS : AdmAxioms S) : (MState.start S).AdmInv := by
  intro a ha d _
  rw [MState.start, Finset.mem_singleton] at ha
  subst ha
  exact hS.adm_init d

/-- Admissibility is preserved by an attempt along a candidate edge. [folklore] -/
theorem AdmAxioms.admInv_update (hS : AdmAxioms S) {st : S.MState} (hA : st.AdmInv) {e : LatticeModels.Site 2 × MDir}
    (he : st.Cand e) (o : Finset (Sym2 V)) : (st.update e o).AdmInv := by
  obtain ⟨he1, he2, he3⟩ := he
  have hτ : S.Adm e.1 e.2 (st.tok e.1 e.2) := hA e.1 he1 e.2 he2
  cases h : S.result e.1 e.2 (st.tok e.1 e.2) o with
  | none => rw [st.update_of_none e o h]; exact hA
  | some f =>
    rw [st.update_of_some e o h]
    intro a ha d hd
    simp only [Finset.mem_insert, not_or] at ha hd
    rcases ha with rfl | ha
    · show S.Adm (tgt e) d (Function.update st.tok (tgt e) f (tgt e) d)
      rw [Function.update_self]
      refine hS.adm_result hτ h d fun hdr => hd.2 ?_
      rw [hdr, tgt, add_assoc, stepVec_rev, add_neg_cancel, add_zero]
      exact he1
    · have hne : a ≠ tgt e := fun hq => he2 (hq ▸ ha)
      show S.Adm a d (Function.update st.tok (tgt e) f a d)
      rw [Function.update_of_ne hne]
      exact hA a ha d hd.2

/-- The admissible token attempted along the chosen edge. [folklore] -/
theorem MState.AdmInv.adm_of_choice {st : S.MState} (hA : st.AdmInv) {e : LatticeModels.Site 2 × MDir} (hc : st.choice = some e) :
    S.Adm e.1 e.2 (st.tok e.1 e.2) :=
  hA e.1 (MState.cand_of_choice hc).1 e.2 (MState.cand_of_choice hc).2.1

/-- **Provenance invariant**: a token in play of provenance `d⁻` at the macro-vertex `a` was
returned by a successful examined attempt into `a` along `d⁻`. [folklore] -/
def MState.SrcInv (st : S.MState) : Prop :=
  ∀ a ∈ st.occ, ∀ d d', S.srcDir (st.tok a d) = some d' →
    ∃ e ∈ st.exam, e ∉ st.fails ∧ tgt e = a ∧ e.2 = d'

/-- The initial state satisfies the provenance invariant. [folklore] -/
theorem AdmAxioms.srcInv_start (hS : AdmAxioms S) : (MState.start S).SrcInv := by
  intro a ha d d' hsrc
  simp only [MState.start, Finset.mem_singleton] at ha hsrc
  rw [hS.src_init] at hsrc
  cases hsrc

/-- The provenance invariant is preserved by an attempt along a candidate edge. [folklore] -/
theorem AdmAxioms.srcInv_update (hS : AdmAxioms S) {st : S.MState} (hI : st.Inv) (hA : st.AdmInv) (hsrc : st.SrcInv)
    {e : LatticeModels.Site 2 × MDir} (he : st.Cand e) (o : Finset (Sym2 V)) : (st.update e o).SrcInv := by
  obtain ⟨he1, he2, he3⟩ := he
  have hτ : S.Adm e.1 e.2 (st.tok e.1 e.2) := hA e.1 he1 e.2 he2
  have hold : ∀ a ∈ st.occ, ∀ d d', S.srcDir (st.tok a d) = some d' →
      ∃ e' ∈ insert e st.exam, e' ∉ insert e st.fails ∧ tgt e' = a ∧ e'.2 = d' := by
    intro a ha d d' hs
    obtain ⟨e', he', hnf, ht, hd⟩ := hsrc a ha d d' hs
    refine ⟨e', Finset.mem_insert_of_mem he', ?_, ht, hd⟩
    rw [Finset.mem_insert, not_or]
    exact ⟨fun hq => he3 (hq ▸ he'), hnf⟩
  cases h : S.result e.1 e.2 (st.tok e.1 e.2) o with
  | none =>
    rw [st.update_of_none e o h]
    exact hold
  | some f =>
    rw [st.update_of_some e o h]
    intro a ha d d' hs
    simp only [Finset.mem_insert] at ha
    rcases ha with rfl | ha
    · simp only [Function.update_self] at hs
      rw [hS.src_result hτ h d] at hs
      simp only [Option.some.injEq] at hs
      subst hs
      refine ⟨e, Finset.mem_insert_self _ _, fun hf => he3 (hI.fails_sub hf), rfl, rfl⟩
    · have hne : a ≠ tgt e := fun hq => he2 (hq ▸ ha)
      simp only [Function.update_of_ne hne] at hs
      obtain ⟨e', he', hnf, ht, hd⟩ := hold a ha d d' hs
      refine ⟨e', he', ?_, ht, hd⟩
      rw [Finset.mem_insert, not_or] at hnf
      exact hnf.2

end Admissibility

/-! ## Well-formed histories: what the replay guarantees -/

section Replay

variable {S}

/-- A state is *reachable*: it satisfies the invariants, holds admissible tokens, and satisfies the
provenance invariant. [folklore] -/
structure MState.Reach (st : S.MState) : Prop where
  inv : st.Inv
  adm : st.AdmInv
  src : st.SrcInv

/-- What the replay records about a record `r` of a replayable history leading to `st`: it is an
acceptable record of an examined edge `e` from an admissible token `τ`; if the attempt failed on it,
`e` has failed; if it succeeded with tokens `f`, the target is occupied and holds the tokens `f`.
[folklore] -/
def RecSpec (st : S.MState) (r : ProbeRecord V) : Prop :=
  ∃ e ∈ st.exam, ∃ τ : S.Tok, S.Adm e.1 e.2 τ ∧ RecOK e τ r ∧
    (S.result e.1 e.2 τ r.2 = none → e ∈ st.fails) ∧
    (∀ f, S.result e.1 e.2 τ r.2 = some f → tgt e ∈ st.occ ∧ st.tok (tgt e) = f)

/-- `RecSpec` is preserved by an update along a candidate edge. [folklore] -/
theorem recSpec_update {st : S.MState} {e : LatticeModels.Site 2 × MDir} (he : st.Cand e) (o : Finset (Sym2 V))
    {r : ProbeRecord V} (hr : RecSpec st r) : RecSpec (st.update e o) r := by
  obtain ⟨e', he', τ, hτ, hok, hnone, hsome⟩ := hr
  obtain ⟨-, he2, -⟩ := he
  refine ⟨e', by rw [MState.exam_update]; exact Finset.mem_insert_of_mem he', τ, hτ, hok,
    fun hn => st.fails_subset_update e o (hnone hn), fun f hf => ?_⟩
  obtain ⟨htgt, htok⟩ := hsome f hf
  have hne : tgt e' ≠ tgt e := fun hq => he2 (hq ▸ htgt)
  rw [st.tok_update_of_ne e o hne]
  exact ⟨st.occ_subset_update e o htgt, htok⟩

/-- Replayed states are reachable, and every record of a replayable history satisfies `RecSpec`.
[folklore] -/
theorem replay_spec (hS : AdmAxioms S) :
    ∀ (h : ProbeHistory V) (st : S.MState), S.replay h = some st →
      st.Reach ∧ ∀ r : ProbeRecord V, some r ∈ h → RecSpec st r
  | [], st, hst => by
    simp only [replay, Option.some.injEq] at hst
    subst hst
    exact ⟨⟨MState.Inv.start, hS.admInv_start, hS.srcInv_start⟩, fun r hr => by simp at hr⟩
  | none :: h, st, hst => by
    rw [replay] at hst
    obtain ⟨hR, hrec⟩ := replay_spec hS h st hst
    exact ⟨hR, fun r hr => hrec r (by simpa using hr)⟩
  | some r :: h, st, hst => by
    rw [replay] at hst
    cases hh : S.replay h with
    | none => rw [hh] at hst; simp at hst
    | some st' =>
      rw [hh, Option.bind_some] at hst
      obtain ⟨hR', hrec'⟩ := replay_spec hS h st' hh
      cases hc : st'.choice with
      | none => rw [hc] at hst; simp at hst
      | some e =>
        rw [hc] at hst
        simp only at hst
        split_ifs at hst with hok
        simp only [Option.some.injEq] at hst
        subst hst
        have hcand := MState.cand_of_choice hc
        refine ⟨⟨hR'.inv.update hcand r.2, hS.admInv_update hR'.adm hcand r.2,
          hS.srcInv_update hR'.inv hR'.adm hR'.src hcand r.2⟩, fun r' hr' => ?_⟩
        rcases List.mem_cons.1 hr' with hr' | hr'
        · simp only [Option.some.injEq] at hr'
          subst hr'
          refine ⟨e, by simp, st'.tok e.1 e.2, hR'.adm.adm_of_choice hc, hok, fun hn => ?_, fun f hf => ?_⟩
          · rw [st'.update_of_none e _ hn]; exact Finset.mem_insert_self _ _
          · rw [st'.update_of_some e _ hf]
            exact ⟨Finset.mem_insert_self _ _, Function.update_self _ _ _⟩
        · exact recSpec_update hcand r.2 (hrec' r' hr')

/-- The directly defined states are reachable. [folklore] -/
theorem reach_stN (hS : AdmAxioms S) (n : ℕ) (ω : BondConfig V) : (S.stN n ω).Reach :=
  (replay_spec hS _ _ (S.replay_hist n ω)).1

/-- **Freshness of the macro-explorer.** If the envelopes of attempts from admissible tokens along
distinct directed macro-edges `(a,d)`, `(a',d')` with `a' ≠ a + d` are disjoint unless `(a',d')`
is the parent edge of the token attempted along `(a,d)`, and envelopes of attempts towards
macro-vertices other than the origin avoid `U₀`, then every probe's envelope avoids `U₀` and the
edges examined by all earlier probes — Grimmett's (C), p. 173, along every history; the parent
record is handled by the dynamic condition checked at replay. [cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
theorem fresh_explorer (hS : AdmAxioms S)
    (hdisj : ∀ {a : LatticeModels.Site 2} {d : MDir} {τ : S.Tok} {a' : LatticeModels.Site 2} {d' : MDir} {τ' : S.Tok},
      S.Adm a d τ → S.Adm a' d' τ' → (a, d) ≠ (a', d') → a' ≠ tgt (a, d) →
        ¬(tgt (a', d') = a ∧ S.srcDir τ = some d') → Disjoint (S.zone a d τ) (S.zone a' d' τ'))
    (hU : ∀ {a : LatticeModels.Site 2} {d : MDir} {τ : S.Tok}, S.Adm a d τ → tgt (a, d) ≠ 0 → Disjoint (S.zone a d τ) S.U₀) :
    S.explorer.Fresh (↑S.U₀ : Set (Sym2 V)) := by
  intro h D hD
  change ((S.replay h).bind fun st => st.nextProbe) = some D at hD
  cases hh : S.replay h with
  | none => rw [hh] at hD; simp at hD
  | some st =>
    rw [hh, Option.bind_some, MState.nextProbe] at hD
    cases hc : st.choice with
    | none => rw [hc] at hD; simp at hD
    | some e =>
      rw [hc, Option.map_some, Option.some.injEq] at hD
      subst hD
      obtain ⟨hR, hrec⟩ := replay_spec hS h st hh
      have hadm := hR.adm.adm_of_choice hc
      obtain ⟨he1, he2, he3⟩ := MState.cand_of_choice hc
      have htgt0 : tgt (e.1, e.2) ≠ 0 := fun hq => he2 (by rw [show tgt e = 0 from hq]; exact hR.inv.zero_mem)
      refine ⟨by rw [env_probe]; exact Finset.disjoint_coe.2 (hU hadm htgt0), ?_⟩
      rw [env_probe, Finset.disjoint_left]
      intro x hx hxs
      obtain ⟨r, hr, hxr⟩ := mem_supp_iff.1 hxs
      obtain ⟨e', he', τ', hτ', hok, hnone, hsome⟩ := hrec r hr
      by_cases hpar : tgt (e'.1, e'.2) = e.1 ∧ S.srcDir (st.tok e.1 e.2) = some e'.2
      · -- the parent record: the attempt succeeded and returned the token in play
        obtain ⟨hte, hsrc⟩ := hpar
        have hte' : tgt e' = e.1 := hte
        obtain ⟨f, hf⟩ : ∃ f, S.result e'.1 e'.2 τ' r.2 = some f := by
          by_contra hcon
          push Not at hcon
          have hn : S.result e'.1 e'.2 τ' r.2 = none := by
            cases hq : S.result e'.1 e'.2 τ' r.2 with
            | none => rfl
            | some f => exact absurd hq (hcon f)
          have hfail := hnone hn
          obtain ⟨e'', he'', hnf, ht, hd⟩ := hR.src e.1 he1 e.2 e'.2 hsrc
          have heq : e'' = e' := by
            have h1 : e''.1 = e'.1 := by
              have := ht.trans hte'.symm
              rw [tgt, tgt, hd] at this
              exact add_right_cancel this
            exact Prod.ext h1 hd
          exact hnf (heq ▸ hfail)
        obtain ⟨-, htok⟩ := hsome f hf
        have hdr : e.2 ≠ rev e'.2 := by
          intro hq
          apply he2
          have : tgt e = e'.1 := by
            rw [tgt, hq, ← hte', tgt, add_assoc, stepVec_rev, add_neg_cancel, add_zero]
          rw [this]
          exact hR.inv.exam_src e' he'
        have hdz := hok.2.2 f hf e.2 hdr
        rw [hte'] at hdz
        have hτeq : st.tok e.1 e.2 = f e.2 := by rw [← hte', htok]
        rw [hτeq] at hx
        exact Finset.disjoint_left.1 hdz hxr hx
      · have hne : (e.1, e.2) ≠ (e'.1, e'.2) := by
          intro hq
          have : e = e' := Prod.ext (congrArg Prod.fst hq) (congrArg Prod.snd hq)
          exact he3 (this ▸ he')
        have hsrc : e'.1 ≠ tgt (e.1, e.2) := fun hq => he2 (show tgt e ∈ st.occ from hq ▸ hR.inv.exam_src e' he')
        exact Finset.disjoint_left.1 (hdisj hadm hτ' hne hsrc hpar) hx (hok.1 hxr)

end Replay

/-! ## The run on a configuration: monotonicity, termination, the final macro-cluster -/

section Run

variable {S}

/-- The observation component of the record of an attempt. [folklore] -/
theorem record_probe_snd (a : LatticeModels.Site 2) (d : MDir) (τ : S.Tok) (ω : BondConfig V) :
    ((S.probe a d τ).record ω).2 = obs ω (S.reveal a d τ ω) := rfl

/-- Once no edge can be chosen, the state is frozen. [folklore] -/
theorem stN_eq_of_choice_eq_none {N : ℕ} {ω : BondConfig V} (hc : (S.stN N ω).choice = none) :
    ∀ n, N ≤ n → S.stN n ω = S.stN N ω := by
  intro n hn
  induction n with
  | zero => rw [Nat.le_zero.1 hn]
  | succ n ih =>
    rcases Nat.lt_or_eq_of_le hn with hlt | heq
    · have h' := ih (Nat.lt_succ_iff.1 hlt)
      rw [stN_succ, h', stepSt, hc]
    · rw [← heq]

/-- While edges keep being chosen, the examined set keeps growing: after `n` productive steps it has
at least `n` elements. [folklore] -/
theorem le_card_exam (ω : BondConfig V) (n : ℕ) (h : ∀ k < n, (S.stN k ω).choice ≠ none) :
    n ≤ (S.stN n ω).exam.card := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    have ih' := ih fun k hk => h k (Nat.lt_succ_of_lt hk)
    cases hc : (S.stN n ω).choice with
    | none => exact absurd hc (h n (Nat.lt_succ_self n))
    | some e =>
      rw [S.stN_succ_of_choice hc, MState.exam_update,
        Finset.card_insert_of_notMem (MState.cand_of_choice hc).2.2]
      exact Nat.succ_le_succ ih'

/-- The final occupied macro-cluster of the run. [cite: GrimmettPercolation1999, §7.3 p. 176] -/
def occFinal (S : AGadgetSystem V) (ω : BondConfig V) : Set (LatticeModels.Site 2) := ⋃ n, ↑(S.stN n ω).occ

/-- **Termination**: if the final cluster is finite, at some time no edge can be chosen any more
(each productive step examines a new edge out of the finite cluster). [cite: GrimmettPercolation1999, §7.2 p. 153] -/
theorem exists_choice_eq_none (hS : AdmAxioms S) {ω : BondConfig V} (hfin : (occFinal S ω).Finite) :
    ∃ N, (S.stN N ω).choice = none := by
  by_contra hne
  push Not at hne
  set F : Finset (LatticeModels.Site 2 × MDir) := hfin.toFinset ×ˢ Finset.univ with hF
  have hsub : ∀ n, (S.stN n ω).exam ⊆ F := by
    intro n e he
    rw [hF, Finset.mem_product]
    refine ⟨hfin.mem_toFinset.2 ?_, Finset.mem_univ _⟩
    exact Set.mem_iUnion.2 ⟨n, (reach_stN hS n ω).inv.exam_src e he⟩
  have h1 := le_card_exam ω (F.card + 1) fun k _ => hne k
  have h2 := Finset.card_le_card (hsub (F.card + 1))
  omega

/-- The macro bond configuration at a state: an edge of `ℤ²` is *open* unless an attempt along it
has failed. [cite: GrimmettPercolation1999, §7.3 p. 176] -/
def MState.macroConfig (st : S.MState) : BondConfig (LatticeModels.Site 2) :=
  {x | x ∈ (LatticeModels.zdGraph 2).edgeSet ∧ ∀ e ∈ st.fails, x ≠ s(e.1, tgt e)}

/-- With no candidate left, the open macro-cluster of the origin consists of occupied vertices.
[cite: GrimmettPercolation1999, §7.3 p. 176] -/
theorem MState.Inv.openCluster_subset {st : S.MState} (hI : st.Inv) (hc : st.choice = none) :
    openCluster st.macroConfig 0 ⊆ ↑st.occ := by
  -- the occupied set is closed under open macro-edges
  have hclosed : ∀ u v : LatticeModels.Site 2, u ∈ st.occ → (openGraph st.macroConfig).Adj u v → v ∈ st.occ := by
    intro u v hu hadj
    rw [openGraph_adj] at hadj
    obtain ⟨⟨hedge, hnot⟩, -⟩ := hadj
    obtain ⟨d, rfl⟩ := (zdGraph_adj_iff_stepVec u v).1 (by simpa using hedge)
    rcases hI.closed hc hu d with h | h
    · exact h
    · exact absurd rfl (hnot _ h)
  -- walk induction from the origin
  have key : ∀ (u w : LatticeModels.Site 2) (W : (openGraph st.macroConfig).Walk u w), u ∈ st.occ → w ∈ st.occ := by
    intro u w W
    induction W with
    | nil => exact id
    | @cons a b _ hadj W' ih => exact fun hu => ih (hclosed a b hu hadj)
  intro v hv
  obtain ⟨W⟩ := hv
  exact key 0 v W hI.zero_mem

/-- **The dual circuit of failed attempts**: if the final cluster is finite then, at a terminal
time `N`, some dual circuit of `ℤ²` of length `n ≥ 1` through a plaquette `(k,0)`, `k < n`, crosses
`n` distinct macro-edges along each of which an attempt has failed (Grimmett 1999, p. 176 with
§1.4 (1.17)). [cite: GrimmettPercolation1999, §7.3 p. 176] -/
theorem exists_dualCircuit_fails (hS : AdmAxioms S) {ω : BondConfig V} (hfin : (occFinal S ω).Finite) :
    ∃ N, (S.stN N ω).choice = none ∧ ∃ n k : ℕ, k < n ∧ ∃ (w : Fin n → MDir) (m : ℕ), m ≤ n ∧
      (dualEdges (Pi.single 0 (k : ℤ) - wordPos w m) w).card = n ∧
      ∀ x ∈ dualEdges (Pi.single 0 (k : ℤ) - wordPos w m) w, ∃ e ∈ (S.stN N ω).fails, x = s(e.1, tgt e) := by
  obtain ⟨N, hN⟩ := exists_choice_eq_none hS hfin
  have hI := (reach_stN hS N ω).inv
  have hCfin : (openCluster (S.stN N ω).macroConfig 0).Finite :=
    (S.stN N ω).occ.finite_toSet.subset (hI.openCluster_subset hN)
  obtain ⟨n, k, hkn, a, w, -, ⟨m, hmn, hpos⟩, hcard, hdisj, -, -⟩ := Contour.exists_dualCircuit _ hCfin
  have ha : a = Pi.single 0 (k : ℤ) - wordPos w m := by rw [← hpos, add_sub_cancel_right]
  subst ha
  refine ⟨N, hN, n, k, hkn, w, m, hmn, hcard, fun x hx => ?_⟩
  have hxE : x ∈ (LatticeModels.zdGraph 2).edgeSet := dualEdges_subset_edgeSet _ _ hx
  have hxω : x ∉ (S.stN N ω).macroConfig := fun hm => Set.disjoint_left.1 hdisj hx hm
  simp only [MState.macroConfig, Set.mem_setOf_eq, not_and, not_forall, not_not, exists_prop] at hxω
  exact hxω hxE

end Run

/-! ## Connectivity: anchors in play are joined to `x₀` -/

section Connectivity

variable {S}

/-- The connectivity axioms, relative to a token precondition `Pre τ ω` (e.g. "the seed square of
`τ` is open in `ω`", established by the attempt that produced `τ`): initial tokens satisfy `Pre`
and have anchors joined to `x₀` when `U₀` is open; a successful attempt from a token satisfying
`Pre` returns tokens satisfying `Pre` whose anchors are joined to the anchor of its own token, and
places them in the cell of the target macro-vertex. [cite: GrimmettPercolation1999, §7.3 pp. 172–176] -/
structure ConnAxioms (S : AGadgetSystem V) (x₀ : V) (cell : V → LatticeModels.Site 2) (Pre : S.Tok → BondConfig V → Prop) : Prop where
  conn_init : ∀ ω : BondConfig V, (↑S.U₀ : Set (Sym2 V)) ⊆ ω → ∀ d,
    Pre (S.init d) ω ∧ S.anchor (S.init d) ∈ openCluster ω x₀
  conn_result : ∀ {a : LatticeModels.Site 2} {d : MDir} {τ : S.Tok} {f : MDir → S.Tok} (ω : BondConfig V),
    S.Adm a d τ → Pre τ ω → S.result a d τ (obs ω (S.reveal a d τ ω)) = some f →
      ∀ d', d' ≠ rev d → Pre (f d') ω ∧ S.anchor (f d') ∈ openCluster ω (S.anchor τ)
  cell_result : ∀ {a : LatticeModels.Site 2} {d : MDir} {τ : S.Tok} {o : Finset (Sym2 V)} {f : MDir → S.Tok},
    S.Adm a d τ → S.result a d τ o = some f → ∀ d', d' ≠ rev d → cell (S.anchor (f d')) = a + stepVec d

/-- The connectivity invariant of the run on `ω`: every usable token's anchor is joined to `x₀`,
and every occupied macro-vertex other than the origin contains (in its cell) a vertex joined to
`x₀`. [folklore] -/
structure MState.ConnInv (x₀ : V) (cell : V → LatticeModels.Site 2) (Pre : S.Tok → BondConfig V → Prop) (ω : BondConfig V)
    (st : S.MState) : Prop where
  tok_conn : ∀ a ∈ st.occ, ∀ d, a + stepVec d ∉ st.occ →
    Pre (st.tok a d) ω ∧ S.anchor (st.tok a d) ∈ openCluster ω x₀
  occ_cell : ∀ b ∈ st.occ, b ≠ 0 → ∃ v ∈ openCluster ω x₀, cell v = b

/-- The connectivity invariant holds along the run when `U₀` is open. [folklore] -/
theorem connInv_stN {x₀ : V} {cell : V → LatticeModels.Site 2} {Pre : S.Tok → BondConfig V → Prop} (hS : AdmAxioms S)
    (hC : ConnAxioms S x₀ cell Pre) {ω : BondConfig V} (hω : (↑S.U₀ : Set (Sym2 V)) ⊆ ω) :
    ∀ n, (S.stN n ω).ConnInv x₀ cell Pre ω := by
  intro n
  induction n with
  | zero =>
    refine ⟨fun a ha d _ => ?_, fun b hb hb0 => ?_⟩
    · simp only [stN, MState.start, Finset.mem_singleton] at ha ⊢
      subst ha
      exact hC.conn_init ω hω d
    · simp only [stN, MState.start, Finset.mem_singleton] at hb
      exact absurd hb hb0
  | succ n ih =>
    cases hc : (S.stN n ω).choice with
    | none => rw [S.stN_succ_of_none hc]; exact ih
    | some e =>
      rw [S.stN_succ_of_choice hc]
      set st := S.stN n ω with hst
      set o := obs ω (S.reveal e.1 e.2 (st.tok e.1 e.2) ω) with ho
      obtain ⟨he1, he2, he3⟩ := MState.cand_of_choice hc
      have hadm : S.Adm e.1 e.2 (st.tok e.1 e.2) := (reach_stN hS n ω).adm.adm_of_choice hc
      obtain ⟨hpre, hτ⟩ := ih.tok_conn e.1 he1 e.2 he2
      cases h : S.result e.1 e.2 (st.tok e.1 e.2) o with
      | none => rw [st.update_of_none e o h]; exact ⟨ih.tok_conn, ih.occ_cell⟩
      | some f =>
        rw [st.update_of_some e o h]
        have hrev : ∀ d, tgt e + stepVec d ∉ insert (tgt e) st.occ → d ≠ rev e.2 := by
          intro d hd hdr
          apply hd
          rw [hdr, tgt, add_assoc, stepVec_rev, add_neg_cancel, add_zero]
          exact Finset.mem_insert_of_mem he1
        refine ⟨fun a ha d hd => ?_, fun b hb hb0 => ?_⟩
        · rcases Finset.mem_insert.1 ha with rfl | ha
          · show Pre (Function.update st.tok (tgt e) f (tgt e) d) ω ∧
              S.anchor (Function.update st.tok (tgt e) f (tgt e) d) ∈ openCluster ω x₀
            rw [Function.update_self]
            obtain ⟨hpre', hconn⟩ := hC.conn_result ω hadm hpre h d (hrev d hd)
            exact ⟨hpre', mem_openCluster_trans hτ hconn⟩
          · have hne : a ≠ tgt e := fun hq => he2 (hq ▸ ha)
            show Pre (Function.update st.tok (tgt e) f a d) ω ∧
              S.anchor (Function.update st.tok (tgt e) f a d) ∈ openCluster ω x₀
            rw [Function.update_of_ne hne]
            exact ih.tok_conn a ha d fun hm => hd (Finset.mem_insert_of_mem hm)
        · rcases Finset.mem_insert.1 hb with rfl | hb
          · have hne : e.2 ≠ rev e.2 := fun hq => rev_ne_self e.2 hq.symm
            refine ⟨S.anchor (f e.2), mem_openCluster_trans hτ (hC.conn_result ω hadm hpre h e.2 hne).2, ?_⟩
            exact hC.cell_result hadm h e.2 hne
          · exact ih.occ_cell b hb hb0

/-- **An infinite macro-cluster forces percolation at `x₀`** (Grimmett 1999, p. 176: "The
existence of such an infinite cluster implies that the vertex `(0,-N,0)` lies in an infinite open
path"). [cite: GrimmettPercolation1999, §7.3 p. 176] -/
theorem percolatesAt_of_occFinal_infinite {x₀ : V} {cell : V → LatticeModels.Site 2} {Pre : S.Tok → BondConfig V → Prop}
    (hS : AdmAxioms S) (hC : ConnAxioms S x₀ cell Pre)
    {ω : BondConfig V} (hω : (↑S.U₀ : Set (Sym2 V)) ⊆ ω) (hinf : (occFinal S ω).Infinite) :
    ω ∈ percolatesAt x₀ := by
  -- choose, for each occupied `b ≠ 0`, a vertex of its cell joined to `x₀`
  have hch : ∀ b : LatticeModels.Site 2, b ∈ occFinal S ω → b ≠ 0 → ∃ v ∈ openCluster ω x₀, cell v = b := by
    intro b hb hb0
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hb
    exact (connInv_stN hS hC hω n).occ_cell b hn hb0
  show (openCluster ω x₀).Infinite
  intro hfinC
  apply hinf
  -- `occFinal \ {0}` injects into the finite cluster via the chosen vertices
  have hsub : occFinal S ω ⊆ insert 0 (cell '' openCluster ω x₀) := by
    intro b hb
    by_cases hb0 : b = 0
    · exact Or.inl hb0
    · obtain ⟨v, hv, hvb⟩ := hch b hb hb0
      exact Or.inr ⟨v, hv, hvb⟩
  exact ((hfinC.image cell).insert 0).subset hsub

end Connectivity

/-! ## Scores: designated probes and successes read off the history -/

section Scores

variable (Γ : Finset (Sym2 (LatticeModels.Site 2)))

/-- The probe made after history `h` is *designated* (for the fixed set `Γ` of macro-edges, later
the edges crossed by a dual circuit): the attempted macro-edge lies in `Γ`.
[cite: GrimmettPercolation1999, §7.3 p. 176] -/
def desigOf (h : ProbeHistory V) : Prop :=
  match S.replay h with
  | none => False
  | some st =>
    match st.choice with
    | none => False
    | some e => s(e.1, tgt e) ∈ Γ

/-- The probe made after history `h`, with observation `o`, *succeeds*: the attempt returns tokens.
[cite: GrimmettPercolation1999, §7.3 p. 174] -/
def succOf (h : ProbeHistory V) (o : Finset (Sym2 V)) : Prop :=
  match S.replay h with
  | none => True
  | some st =>
    match st.choice with
    | none => True
    | some e => S.result e.1 e.2 (st.tok e.1 e.2) o ≠ none

variable {S Γ}

/-- `desigOf` on the actual history. [folklore] -/
theorem desigOf_hist {n : ℕ} {ω : BondConfig V} {e : LatticeModels.Site 2 × MDir} (hc : (S.stN n ω).choice = some e) :
    S.desigOf Γ (S.explorer.hist n ω) ↔ s(e.1, tgt e) ∈ Γ := by
  simp only [desigOf, replay_hist, hc]

/-- `succOf` on the actual history. [folklore] -/
theorem succOf_hist {n : ℕ} {ω : BondConfig V} {e : LatticeModels.Site 2 × MDir} (hc : (S.stN n ω).choice = some e)
    (o : Finset (Sym2 V)) :
    S.succOf (S.explorer.hist n ω) o ↔ S.result e.1 e.2 ((S.stN n ω).tok e.1 e.2) o ≠ none := by
  simp only [succOf, replay_hist, hc]

/-- **The scores along the run**: the number of designated failures is the number of failed edges
in `Γ`, and a designated success is a successful examined edge in `Γ`. [folklore] -/
theorem scores_hist (hS : AdmAxioms S) (ω : BondConfig V) : ∀ n : ℕ,
    nfail (S.succOf) (S.desigOf Γ) (S.explorer.hist n ω) =
        ((S.stN n ω).fails.filter fun e => s(e.1, tgt e) ∈ Γ).card ∧
      (AnySucc (S.succOf) (S.desigOf Γ) (S.explorer.hist n ω) ↔
        ∃ e ∈ (S.stN n ω).exam, e ∉ (S.stN n ω).fails ∧ s(e.1, tgt e) ∈ Γ)
  | 0 => by simp [stN, MState.start]
  | n + 1 => by
    obtain ⟨ih1, ih2⟩ := scores_hist hS ω n
    rw [AExplorer.hist_succ]
    cases hc : (S.stN n ω).choice with
    | none =>
      have hnone : S.explorer.next (S.explorer.hist n ω) = none := by
        rw [next_hist, MState.nextProbe, hc]; rfl
      rw [S.explorer.step_of_none hnone, nfail_cons_none, anySucc_cons_none, S.stN_succ_of_none hc]
      exact ⟨ih1, ih2⟩
    | some e =>
      set st := S.stN n ω with hst
      set D := S.probe e.1 e.2 (st.tok e.1 e.2) with hD
      have hsome : S.explorer.next (S.explorer.hist n ω) = some D := by
        rw [next_hist, MState.nextProbe, ← hst, hc]; rfl
      obtain ⟨he1, he2, he3⟩ := MState.cand_of_choice hc
      have hef : e ∉ st.fails := fun hf => he3 ((reach_stN hS n ω).inv.fails_sub hf)
      rw [S.explorer.step_of_some hsome, nfail_cons_some, anySucc_cons_some, S.stN_succ_of_choice hc, ih1,
        desigOf_hist hc, succOf_hist hc, record_probe_snd]
      cases hr : S.result e.1 e.2 (st.tok e.1 e.2) (obs ω (S.reveal e.1 e.2 (st.tok e.1 e.2) ω)) with
      | none =>
        rw [st.update_of_none e _ hr]
        refine ⟨?_, ?_⟩
        · rw [Finset.filter_insert]
          by_cases hΓ : s(e.1, tgt e) ∈ Γ
          · rw [if_pos hΓ, Finset.card_insert_of_notMem (fun hm => hef (Finset.mem_filter.1 hm).1)]
            simp [hΓ]
          · rw [if_neg hΓ]; simp [hΓ]
        · simp only [ne_eq, not_true_eq_false, and_false, false_or, Finset.mem_insert]
          rw [ih2]
          constructor
          · rintro ⟨e', he', hnf, hΓ⟩
            exact ⟨e', Or.inr he', not_or.2 ⟨fun hq => he3 (hq ▸ he'), hnf⟩, hΓ⟩
          · rintro ⟨e', he', hnf, hΓ⟩
            rw [not_or] at hnf
            rcases he' with rfl | he'
            · exact absurd rfl hnf.1
            · exact ⟨e', he', hnf.2, hΓ⟩
      | some f =>
        rw [st.update_of_some e _ hr]
        refine ⟨by simp, ?_⟩
        simp only [ne_eq, reduceCtorEq, not_false_eq_true, and_true, Finset.mem_insert]
        rw [ih2]
        constructor
        · rintro (hΓ | ⟨e', he', hnf, hΓ⟩)
          · exact ⟨e, Or.inl rfl, hef, hΓ⟩
          · exact ⟨e', Or.inr he', hnf, hΓ⟩
        · rintro ⟨e', he', hnf, hΓ⟩
          rcases he' with rfl | he'
          · exact Or.inl hΓ
          · exact Or.inr ⟨e', he', hnf, hΓ⟩

/-- **At a terminal time the circuit is fully charged**: with `Γ` a set of `n` macro-edges each
carrying a failed attempt, there are at least `n` designated failures and no designated success,
then and at all later times. [cite: GrimmettPercolation1999, §7.3 p. 176] -/
theorem scores_terminal (hS : AdmAxioms S) {ω : BondConfig V} {N : ℕ} (hN : (S.stN N ω).choice = none)
    {n : ℕ} (hcard : Γ.card = n) (hcov : ∀ x ∈ Γ, ∃ e ∈ (S.stN N ω).fails, x = s(e.1, tgt e))
    {n' : ℕ} (hn' : N ≤ n') :
    n ≤ nfail (S.succOf) (S.desigOf Γ) (S.explorer.hist n' ω) ∧
      ¬AnySucc (S.succOf) (S.desigOf Γ) (S.explorer.hist n' ω) := by
  obtain ⟨h1, h2⟩ := scores_hist (Γ := Γ) hS ω n'
  rw [h1, h2, stN_eq_of_choice_eq_none hN n' hn']
  have hI := (reach_stN hS N ω).inv
  constructor
  · -- `Γ` is covered by the image of the failed edges in `Γ`
    calc n = Γ.card := hcard.symm
      _ ≤ (((S.stN N ω).fails.filter fun e => s(e.1, tgt e) ∈ Γ).image fun e => s(e.1, tgt e)).card := by
          refine Finset.card_le_card fun x hx => ?_
          obtain ⟨e, he, rfl⟩ := hcov x hx
          exact Finset.mem_image.2 ⟨e, Finset.mem_filter.2 ⟨he, hx⟩, rfl⟩
      _ ≤ _ := Finset.card_image_le
  · rintro ⟨e, he, hnf, hΓ⟩
    obtain ⟨e', he', hee'⟩ := hcov _ hΓ
    rcases eq_or_rev_of_edge_eq hee' with rfl | rfl
    · exact hnf he'
    · exact hI.no_rev e he (hI.fails_sub he')

end Scores

/-! ## The main theorem: a lawful gadget system percolates -/

section Main

variable (G : SimpleGraph V) (p : unitInterval)

/-- **Lawful adaptive gadget systems** (the hypotheses of the dynamic renormalization of
Grimmett 1999, §7.3 pp. 171–176, for adaptive attempts): admissibility/provenance and connectivity
axioms; STATIC disjointness of the envelopes of a new attempt `(a, d, τ)` and an earlier one
`(a', d', τ')` — distinct edges, `a'` not the (unoccupied) target of `(a, d)` — unless `(a', d')`
is the parent edge of `τ` (the parent is covered by the dynamic field `parent_disjoint`);
envelopes of attempts not targeting the origin avoid `U₀`; and the failure bound `ε` for an
attempt from an admissible token (cf. (7.56), p. 174). [cite: GrimmettPercolation1999, §7.3 pp. 171–176] -/
structure Lawful (S : AGadgetSystem V) (G : SimpleGraph V) (p : unitInterval) (ε : ℝ) (x₀ : V)
    (cell : V → LatticeModels.Site 2) (Pre : S.Tok → BondConfig V → Prop) : Prop where
  adm : AdmAxioms S
  conn : ConnAxioms S x₀ cell Pre
  disjoint_zone : ∀ {a : LatticeModels.Site 2} {d : MDir} {τ : S.Tok} {a' : LatticeModels.Site 2} {d' : MDir} {τ' : S.Tok},
    S.Adm a d τ → S.Adm a' d' τ' → (a, d) ≠ (a', d') → a' ≠ tgt (a, d) →
      ¬(tgt (a', d') = a ∧ S.srcDir τ = some d') → Disjoint (S.zone a d τ) (S.zone a' d' τ')
  disjoint_U₀ : ∀ {a : LatticeModels.Site 2} {d : MDir} {τ : S.Tok}, S.Adm a d τ → tgt (a, d) ≠ 0 → Disjoint (S.zone a d τ) S.U₀
  prob_fail : ∀ {a : LatticeModels.Site 2} {d : MDir} {τ : S.Tok}, S.Adm a d τ →
    (bondPercolation G p).real {ω | S.result a d τ (obs ω (S.reveal a d τ ω)) = none} ≤ ε

variable {S G p}
variable {ε : ℝ} {x₀ : V} {cell : V → LatticeModels.Site 2} {Pre : S.Tok → BondConfig V → Prop}

/-- The initial event `A₀ = {U₀ open}`. [cite: GrimmettPercolation1999, §7.3 p. 171 (7.55)] -/
def initEvent (S : AGadgetSystem V) : Set (BondConfig V) := {ω | (↑S.U₀ : Set (Sym2 V)) ⊆ ω}

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

/-- The event that, from time `N` on, at least `k` designated probes (for `Γ`) have failed and none
has succeeded, within `A₀`. [folklore] -/
def charged (S : AGadgetSystem V) (Γ : Finset (Sym2 (LatticeModels.Site 2))) (k N : ℕ) : Set (BondConfig V) :=
  ⋂ n' : ℕ, ⋂ (_ : N ≤ n'), (initEvent S ∩
    {ω | k ≤ nfail S.succOf (S.desigOf Γ) (S.explorer.hist n' ω) ∧
      ¬AnySucc S.succOf (S.desigOf Γ) (S.explorer.hist n' ω)})

/-- `charged` is monotone in the starting time. [folklore] -/
theorem charged_mono (Γ : Finset (Sym2 (LatticeModels.Site 2))) (k : ℕ) : Monotone (charged S Γ k) := by
  intro N N' hNN' ω hω
  simp only [charged, Set.mem_iInter] at hω ⊢
  exact fun n' hn' => hω n' (hNN'.trans hn')

/-- **The supermartingale bound per circuit**: `P_p(⋃_N charged Γ k N) ≤ ε₀ᵏ P_p(A₀)` with `ε₀ = 1/64`
 when attempts fail with probability at most `ε ≤ 1/64`. [cite: GrimmettPercolation1999, §7.3 p.
 176]
-/
theorem measure_iUnion_charged_le [Countable V] (hL : S.Lawful G p ε x₀ cell Pre) (hε : ε ≤ 1 / 64)
    (Γ : Finset (Sym2 (LatticeModels.Site 2))) (k : ℕ) :
    bondPercolation G p (⋃ N, charged S Γ k N) ≤
      ENNReal.ofReal ((1 / 64 : ℝ) ^ k * (bondPercolation G p).real (initEvent S)) := by
  set μ := bondPercolation G p with hμ
  have hE := fresh_explorer hL.adm hL.disjoint_zone hL.disjoint_U₀
  have hfail : ∀ h D, S.explorer.next h = some D → S.desigOf Γ h →
      μ.real {ω | ¬S.succOf h (D.read ω)} ≤ 1 - 63 / 64 := by
    intro h D hD _
    change ((S.replay h).bind fun st => st.nextProbe) = some D at hD
    cases hh : S.replay h with
    | none => rw [hh] at hD; simp at hD
    | some st =>
      rw [hh, Option.bind_some, MState.nextProbe] at hD
      cases hc : st.choice with
      | none => rw [hc] at hD; simp at hD
      | some e =>
        rw [hc, Option.map_some, Option.some.injEq] at hD
        subst hD
        have hadm := (replay_spec hL.adm h st hh).1.adm.adm_of_choice hc
        have hset : {ω | ¬S.succOf h ((S.probe e.1 e.2 (st.tok e.1 e.2)).read ω)} =
            {ω | S.result e.1 e.2 (st.tok e.1 e.2) (obs ω (S.reveal e.1 e.2 (st.tok e.1 e.2) ω)) = none} := by
          ext ω; simp [succOf, hh, hc, read_probe]
        rw [hset]
        linarith [hL.prob_fail hadm]
  have hT2 : ∀ N, μ (charged S Γ k N) ≤ ENNReal.ofReal ((1 / 64 : ℝ) ^ k * μ.real (initEvent S)) := by
    intro N
    have h := S.explorer.measureReal_inter_le_nfail_le G p S.succOf (S.desigOf Γ) hE determinedBy_initEvent
      measurableSet_initEvent (q := 63 / 64) (by norm_num) (by norm_num) hfail N k
    have hsub : charged S Γ k N ⊆ initEvent S ∩
        {ω | k ≤ nfail S.succOf (S.desigOf Γ) (S.explorer.hist N ω) ∧
          ¬AnySucc S.succOf (S.desigOf Γ) (S.explorer.hist N ω)} := by
      intro ω hω
      simp only [charged, Set.mem_iInter] at hω
      exact hω N le_rfl
    calc μ (charged S Γ k N) ≤ μ (initEvent S ∩ {ω | k ≤ nfail S.succOf (S.desigOf Γ) (S.explorer.hist N ω) ∧
          ¬AnySucc S.succOf (S.desigOf Γ) (S.explorer.hist N ω)}) := measure_mono hsub
      _ = ENNReal.ofReal (μ.real (initEvent S ∩ {ω | k ≤ nfail S.succOf (S.desigOf Γ) (S.explorer.hist N ω) ∧
          ¬AnySucc S.succOf (S.desigOf Γ) (S.explorer.hist N ω)})) := (ofReal_measureReal (measure_ne_top _ _)).symm
      _ ≤ ENNReal.ofReal ((1 / 64 : ℝ) ^ k * μ.real (initEvent S)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          norm_num at h ⊢
          exact h
  rw [(charged_mono (S := S) Γ k).measure_iUnion]
  exact iSup_le hT2

/-- **Cover**: on `A₀`, if `x₀` does not percolate then the final macro-cluster is finite, and some
dual circuit (indexed as in `theta_zd_pos_of_le` by its length `n`, the plaquette `(k,0)`, `k < n`,
the position `m ≤ n` of that plaquette, and the word `w`) is fully charged with `n` failures from
some time on. [cite: GrimmettPercolation1999, §7.3 p. 176] -/
theorem initEvent_diff_percolatesAt_subset (hL : S.Lawful G p ε x₀ cell Pre) :
    initEvent S \ percolatesAt x₀ ⊆
      ⋃ n : ℕ, ⋃ k ∈ Finset.range n, ⋃ m ∈ Finset.range (n + 1),
        ⋃ w ∈ (Finset.univ.filter fun w : Fin n → MDir =>
            (dualEdges (Pi.single 0 (k : ℤ) - wordPos w m) w).card = n),
          ⋃ N, charged S (dualEdges (Pi.single 0 (k : ℤ) - wordPos w m) w) n N := by
  rintro ω ⟨hA, hnp⟩
  have hfin : (occFinal S ω).Finite := by
    by_contra hinf
    exact hnp (percolatesAt_of_occFinal_infinite hL.adm hL.conn hA hinf)
  obtain ⟨N, hN, n, k, hkn, w, m, hmn, hcard, hcov⟩ := exists_dualCircuit_fails hL.adm hfin
  refine Set.mem_iUnion.2 ⟨n, Set.mem_biUnion (Finset.mem_range.2 hkn)
    (Set.mem_biUnion (Finset.mem_range.2 (Nat.lt_succ_of_le hmn))
      (Set.mem_biUnion (x := w) (by simp [hcard]) (Set.mem_iUnion.2 ⟨N, ?_⟩)))⟩
  simp only [charged, Set.mem_iInter]
  intro n' hn'
  exact ⟨hA, scores_terminal hL.adm hN hcard hcov hn'⟩

/-- **Dynamic renormalization percolates.** For a lawful gadget system whose attempts fail with
probability at most `ε ≤ 1/64`, and whose initial event `A₀ = {U₀ open}` has positive probability,
`P_p(A₀, x₀ ↮ ∞) ≤ ⅔ P_p(A₀)` by the Peierls sum `Σₙ n(n+1)4ⁿ 64⁻ⁿ ≤ ⅔` over charged dual circuits,
whence `θ_{x₀}(p) > 0` (Grimmett 1999, p. 176: "If `π^R > p_c^site`, there exists a strictly positive
probability that `0` lies in an infinite cluster of occupied vertices … The existence of such an
infinite cluster implies that the vertex … lies in an infinite open path").
[cite: GrimmettPercolation1999, §7.3 p. 176] -/
theorem theta_pos [Countable V] (hL : S.Lawful G p ε x₀ cell Pre) (hε : ε ≤ 1 / 64)
    (hA₀ : 0 < (bondPercolation G p).real (initEvent S)) : 0 < theta G x₀ p := by
  classical
  set μ := bondPercolation G p with hμ
  -- the Peierls sum over charged circuits
  let Γ : (n : ℕ) → ℕ → ℕ → (Fin n → MDir) → Finset (Sym2 (LatticeModels.Site 2)) := fun n k m w =>
    dualEdges (Pi.single 0 (k : ℤ) - wordPos w m) w
  let good : (n : ℕ) → ℕ → ℕ → Finset (Fin n → MDir) := fun n k m =>
    Finset.univ.filter fun w => (Γ n k m w).card = n
  let T : (n : ℕ) → ℕ → ℕ → (Fin n → MDir) → Set (BondConfig V) := fun n k m w => ⋃ N, charged S (Γ n k m w) n N
  let W : ℕ → Set (BondConfig V) := fun n =>
    ⋃ k ∈ Finset.range n, ⋃ m ∈ Finset.range (n + 1), ⋃ w ∈ good n k m, T n k m w
  have hT : ∀ n k m w, μ (T n k m w) ≤ ENNReal.ofReal ((1 / 64 : ℝ) ^ n * μ.real (initEvent S)) :=
    fun n k m w => measure_iUnion_charged_le hL hε _ n
  have hW : ∀ n, μ (W n) ≤ ENNReal.ofReal (1 / 2 * (1 / 4) ^ n * μ.real (initEvent S)) := by
    intro n
    calc μ (W n)
        ≤ ∑ k ∈ Finset.range n, μ (⋃ m ∈ Finset.range (n + 1), ⋃ w ∈ good n k m, T n k m w) :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ k ∈ Finset.range n, ∑ m ∈ Finset.range (n + 1), μ (⋃ w ∈ good n k m, T n k m w) := by
          gcongr; exact measure_biUnion_finset_le _ _
      _ ≤ ∑ k ∈ Finset.range n, ∑ m ∈ Finset.range (n + 1), ∑ w ∈ good n k m, μ (T n k m w) := by
          gcongr; exact measure_biUnion_finset_le _ _
      _ ≤ ∑ k ∈ Finset.range n, ∑ m ∈ Finset.range (n + 1), ∑ w ∈ good n k m,
            ENNReal.ofReal ((1 / 64 : ℝ) ^ n * μ.real (initEvent S)) := by
          gcongr with k _ m _ w _; exact hT n k m w
      _ ≤ ∑ k ∈ Finset.range n, ∑ m ∈ Finset.range (n + 1), ∑ w : Fin n → MDir,
            ENNReal.ofReal ((1 / 64 : ℝ) ^ n * μ.real (initEvent S)) := by
          gcongr; exact Finset.subset_univ _
      _ = ENNReal.ofReal (((n * ((n + 1) * (2 * 2) ^ n) : ℕ) : ℝ) * ((1 / 64 : ℝ) ^ n * μ.real (initEvent S))) := by
          rw [Finset.sum_const, Finset.sum_const, Finset.sum_const, Finset.card_range,
            Finset.card_range, Finset.card_univ, Fintype.card_fun, Fintype.card_prod,
            Fintype.card_fin, Fintype.card_fin, Fintype.card_bool, smul_smul, smul_smul, nsmul_eq_mul,
            ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, Nat.mul_assoc]
      _ ≤ ENNReal.ofReal (1 / 2 * (1 / 4) ^ n * μ.real (initEvent S)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 := mul_le_mul_of_nonneg_right (peierls_term_le n) (measureReal_nonneg (μ := μ) (s := initEvent S))
          have h2 : (((n * ((n + 1) * (2 * 2) ^ n) : ℕ) : ℝ) * ((1 / 64 : ℝ) ^ n * μ.real (initEvent S))) =
              (n : ℝ) * (n + 1) * 4 ^ n * (1 - 63 / 64) ^ n * μ.real (initEvent S) := by
            push_cast; ring
          rw [h2]
          exact h1
  have hsum : (∑' n, ENNReal.ofReal (1 / 2 * (1 / 4 : ℝ) ^ n * μ.real (initEvent S))) =
      ENNReal.ofReal (2 / 3 * μ.real (initEvent S)) := by
    have hg : Summable fun n : ℕ => (1 / 2 : ℝ) * (1 / 4) ^ n * μ.real (initEvent S) :=
      ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _).mul_right _
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hg, tsum_mul_right, tsum_mul_left,
      tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  have hcover : initEvent S \ percolatesAt x₀ ⊆ ⋃ n, W n := initEvent_diff_percolatesAt_subset hL
  have hbad : μ (initEvent S \ percolatesAt x₀) ≤ ENNReal.ofReal (2 / 3 * μ.real (initEvent S)) :=
    (measure_mono hcover).trans ((measure_iUnion_le W).trans ((ENNReal.tsum_le_tsum hW).trans hsum.le))
  -- conclusion
  have hsplit : μ (initEvent S) ≤ μ (percolatesAt x₀) + ENNReal.ofReal (2 / 3 * μ.real (initEvent S)) :=
    calc μ (initEvent S) ≤ μ (initEvent S ∩ percolatesAt x₀) + μ (initEvent S \ percolatesAt x₀) :=
        measure_le_inter_add_sdiff _ _ _
      _ ≤ μ (percolatesAt x₀) + ENNReal.ofReal (2 / 3 * μ.real (initEvent S)) :=
        add_le_add (measure_mono Set.inter_subset_right) hbad
  rw [theta, ← hμ]
  by_contra hθ
  have hθ0 : μ.real (percolatesAt x₀) = 0 := le_antisymm (not_lt.1 hθ) measureReal_nonneg
  have hP0 : μ (percolatesAt x₀) = 0 := (measureReal_eq_zero_iff (measure_ne_top _ _)).1 hθ0
  rw [hP0, zero_add, ← ofReal_measureReal (measure_ne_top _ _)] at hsplit
  have := ENNReal.ofReal_le_ofReal_iff (by positivity) |>.1 hsplit
  linarith

/-- The probability of the initial event is `p^{|U₀|} > 0` when `U₀` consists of edges of `G` and
`p > 0` (Grimmett (7.55)). [cite: GrimmettPercolation1999, §7.3 p. 171 (7.55)] -/
theorem initEvent_pos (hU : (↑S.U₀ : Set (Sym2 V)) ⊆ G.edgeSet) (hp : 0 < (p : ℝ)) :
    0 < (bondPercolation G p).real (initEvent S) := by
  rw [initEvent, bondPercolation_real_setOf_subset G p S.U₀ hU]
  exact pow_pos hp _

/-- **Dynamic renormalization percolates** (real-parameter form): a lawful gadget system with
failure bound `ε ≤ 1/64`, initial edges in `G` and `p > 0` gives `θ_{x₀}(p) > 0`.
[cite: GrimmettPercolation1999, §7.3 p. 176] -/
theorem theta_pos_of_lawful [Countable V] (hL : S.Lawful G p ε x₀ cell Pre) (hε : ε ≤ 1 / 64)
    (hU : (↑S.U₀ : Set (Sym2 V)) ⊆ G.edgeSet) (hp : 0 < (p : ℝ)) : 0 < theta G x₀ p :=
  theta_pos hL hε (initEvent_pos hU hp)

end Main

end AGadgetSystem

end Percolation.Literature
