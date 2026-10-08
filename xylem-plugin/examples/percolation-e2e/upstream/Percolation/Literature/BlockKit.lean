import Percolation.Literature.DynamicRenormalization
import Percolation.Literature.HalfSpaceHighDimPlaced
import Percolation.Util.Linter

/-!
# Block kits: from a deterministic brick-stacking plan to a lawful adaptive gadget system

The block construction of Barsky, Grimmett and Newman
(Grimmett, *Percolation*, 2nd ed. (1999), §7.3, proof of Lemma (7.52), pp. 169–176) stacks rotated
translates of the brick `B(L,H)` of Lemma (7.36) one after the other, each placed according to the
open paths found so far ((A) top stacking, (B) side stacking, (C) branching, (D) steering,
pp. 172–174), so as to occupy, tube after tube, the vertices of a renormalised planar lattice; the
probabilistic skeleton of this — an adaptive gadget system on the macro-lattice `ℤ²` percolates
when its attempts are lawful and fail rarely — is `AGadgetSystem.theta_pos_of_lawful`
(`DynamicRenormalization.lean`). This file separates what remains into GEOMETRY and BOOK-KEEPING:

* a **block kit** (`BGNd.Kit`) is the geometric data of such a construction: tokens (a seed square
  of radius `m` — its centre `anchor` and orientation `ax` — together with the provenance
  `srcDir`), the initial open set `U₀` and initial tokens, admissibility, the macro-cell map, the
  reserved zones, and a DETERMINISTIC PLAN: given the history of the attempt so far (the placements
  made and the open edges observed on their supports), the next placement of a clean brick
  (`HalfSpaceHighDimPlaced.lean`) or the end of the attempt, and the tokens handed on at the end;
* the book-keeping is done here once and for all: the **guarded run** of a plan on a configuration
  (`Kit.run`: a brick is placed only while all earlier bricks were clean-good, its support avoids
  the supports examined so far and lies in the zone, and at most `R` bricks are placed), its
  locality (`Kit.run_eq_of_agree`) and determination by the examined edges
  (`Kit.determinedBy_run`), the guarded outcome (`Kit.gfinish`: tokens are handed on only if they
  are admissible, correctly sourced, in the right cell, and their zones avoid the examined edges),
  whence an adaptive gadget system `Kit.system` satisfying the structural axioms by construction;
* **the failure bound** `Kit.prob_not_allGood_le`: the guarded run places a brick which is not
  clean-good with probability at most `R (1 - π)`, `π = P_p(goodC)` — each new brick is examined on
  fresh edges, so the conditional-independence decomposition
  `bondPercolation_real_inter_memDep_le` (`FiniteEnergy.lean`) applies brick by brick (Grimmett
  (7.56): "each new step … results in an occupied vertex with conditional probability at least
  `π^R`"; the union bound `1 - π^R ≤ R(1-π)` is what is used);
* `Kit.Good` — the obligations left to a concrete kit, all about its own geometry: static
  disjointness of zones, the initial structure, and, along every all-good guarded run from an
  admissible token, that the plan's guards pass and the outcome hands on well-placed tokens whose
  seed squares are open and joined to the entry seed;
* `Kit.theta_pos` — **a good kit with `R(1 - P_p(goodC)) ≤ 1/64` gives `θ(p) > 0`** for bond
  percolation on `ℤ^d` at the base vertex.

## References

* G. Grimmett, *Percolation*, 2nd ed., Grundlehren 321, Springer 1999, §7.3 pp. 169–176.
* D. J. Barsky, G. R. Grimmett, C. M. Newman, *Dynamic renormalization and continuity of the
  percolation transition in orthants*, in *Spatial Stochastic Processes*, Birkhäuser 1991, 37–55.
-/

noncomputable section

namespace Percolation.Literature

open _root_.MeasureTheory _root_.ProbabilityTheory LatticeModels unitInterval ProbeHistory Contour
open scoped _root_.ENNReal Classical

namespace BGNd

variable {d : ℕ} [NeZero d]

/-! ## Brick histories -/

/-- The record of one placed brick: its placement and the open edges observed on its support.
[cite: GrimmettPercolation1999, §7.4 p. 176] -/
abbrev BrickRec (d : ℕ) : Type := BrickPos d × Finset (Sym2 (Site d))

/-- The history of an attempt: the records of the bricks placed so far, newest first. [folklore] -/
abbrev BrickHist (d : ℕ) : Type := List (BrickRec d)

section Hist

variable (m L H : ℕ)

/-- The edges examined by the bricks of a history: the union of their supports. [folklore] -/
def histSupp (h : BrickHist d) : Finset (Sym2 (Site d)) := h.foldr (fun r acc => suppP m L H r.1 ∪ acc) ∅

/-- The empty history examined nothing. [folklore] -/
@[simp] theorem histSupp_nil : histSupp m L H ([] : BrickHist d) = ∅ := rfl

/-- A new brick adds its support. [folklore] -/
@[simp] theorem histSupp_cons (r : BrickRec d) (h : BrickHist d) :
    histSupp m L H (r :: h) = suppP m L H r.1 ∪ histSupp m L H h := rfl

/-- Membership in the examined set. [folklore] -/
theorem mem_histSupp_iff {h : BrickHist d} {e : Sym2 (Site d)} : e ∈ histSupp m L H h ↔ ∃ r ∈ h, e ∈ suppP m L H r.1 := by
  induction h with
  | nil => simp
  | cons r h ih =>
    rw [histSupp_cons, Finset.mem_union, ih]
    constructor
    · rintro (he | ⟨r', hr', he⟩)
      exacts [⟨r, List.mem_cons_self, he⟩, ⟨r', List.mem_cons_of_mem _ hr', he⟩]
    · rintro ⟨r', hr', he⟩
      rcases List.mem_cons.1 hr' with rfl | hr'
      exacts [Or.inl he, Or.inr ⟨r', hr', he⟩]

/-- A record is *good*: read as a configuration, its observation lies in the placed clean good event
of its brick (for an actual observation `ω ∩ supp`, this says `ω` itself is in the event, which is
determined by the support). [cite: GrimmettPercolation1999, §7.3 p. 172 (A)] -/
def GoodRec (r : BrickRec d) : Prop := ((↑r.2 : Set (Sym2 (Site d))) : BondConfig (Site d)) ∈ placedC m L H r.1

/-- All recorded bricks are good. [folklore] -/
def AllGood (h : BrickHist d) : Prop := ∀ r ∈ h, GoodRec m L H r

/-- The empty history is all good. [folklore] -/
@[simp] theorem allGood_nil : AllGood m L H ([] : BrickHist d) := fun _ hr => absurd hr List.not_mem_nil

/-- `AllGood` of a longer history. [folklore] -/
theorem allGood_cons {r : BrickRec d} {h : BrickHist d} : AllGood m L H (r :: h) ↔ GoodRec m L H r ∧ AllGood m L H h := by
  simp [AllGood]

variable {m L H}

/-- **A good actual record means the configuration is in the placed event** (the event is
determined by the support, on which `ω` and `ω ∩ supp` agree). [folklore] -/
theorem goodRec_obs_iff (hH : 1 ≤ H) (hmL : m < L) (β : BrickPos d) (ω : BondConfig (Site d)) :
    GoodRec m L H (β, obs ω (suppP m L H β)) ↔ ω ∈ placedC m L H β := by
  have hdet := determinedBy_placedC_suppP hH hmL β (d := d)
  rw [determinedBy_iff] at hdet
  refine hdet _ _ ?_
  rw [coe_obs, Set.inter_assoc, Set.inter_self]

end Hist

omit [NeZero d] in
/-- A set of configurations not depending on the configuration is determined by anything. [folklore] -/
theorem determinedBy_setOf_const (P : Prop) (F : Set (Sym2 (Site d))) :
    DeterminedBy {_ω : BondConfig (Site d) | P} F := by
  rw [determinedBy_iff]; intro ω ω' _; exact Iff.rfl

omit [NeZero d] in
/-- The empty event is determined by anything. [folklore] -/
theorem determinedBy_empty' (F : Set (Sym2 (Site d))) : DeterminedBy (∅ : Set (BondConfig (Site d))) F := by
  rw [determinedBy_iff]; intro ω ω' _; exact Iff.rfl

/-! ## Kits -/

/-- A **block kit**: the geometric data of a brick-stacking block construction over the clean bricks
`B(L,H)` with seeds of radius `m` in `ℤ^d` (Grimmett 1999, §7.3 pp. 170–174): tokens and their
seed squares, provenance, initial structure, admissibility, macro-cells, reserved zones, and the
deterministic stacking plan with its outcome and length bound. [cite: GrimmettPercolation1999, §7.3 pp. 170–174] -/
structure Kit (d : ℕ) where
  /-- tokens: what a successful attempt hands to the attempts it enables -/
  Tok : Type
  /-- the centre of the token's seed square -/
  anchor : Tok → Site d
  /-- the axis orthogonal to the token's seed square -/
  ax : Tok → Fin d
  /-- the direction of the attempt that produced the token (`none` for initial tokens) -/
  srcDir : Tok → Option MDir
  /-- the initial tokens at the macro-origin -/
  init : MDir → Tok
  /-- the initial edges, all required to be open -/
  U₀ : Finset (Sym2 (Site d))
  /-- admissibility of a token for the attempt along the directed macro-edge `(a, e)` -/
  Adm : Site 2 → MDir → Tok → Prop
  /-- the macro-cell of a vertex -/
  cell : Site d → Site 2
  /-- the reserved zone of the attempt along `(a, e)` from the token `τ` -/
  zone : Site 2 → MDir → Tok → Finset (Sym2 (Site d))
  /-- the plan: the next placement given the history of the attempt, or its end -/
  next : Site 2 → MDir → Tok → BrickHist d → Option (BrickPos d)
  /-- the tokens handed on at the end of the attempt, one per onward direction, or failure -/
  finish : Site 2 → MDir → Tok → BrickHist d → Option (MDir → Tok)
  /-- the maximal number of bricks of an attempt (Grimmett's `R`) -/
  R : ℕ

namespace Kit

variable (K : Kit d) (m L H : ℕ)

/-- The precondition of a token: its seed square is open. [cite: GrimmettPercolation1999, §7.3 p. 172] -/
def Pre (τ : K.Tok) (ω : BondConfig (Site d)) : Prop := IsSeed ω (square (K.ax τ) m (K.anchor τ))

/-! ### The guarded run -/

/-- **The guarded next placement**: while fewer than `R` bricks were placed and all were good, the
planned brick — provided its support avoids the edges examined so far and lies in the zone
(Grimmett 1999, p. 173 (C)). [cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
def gnext (a : Site 2) (e : MDir) (τ : K.Tok) (h : BrickHist d) : Option (BrickPos d) :=
  if h.length < K.R ∧ AllGood m L H h then
    match K.next a e τ h with
    | none => none
    | some β => if Disjoint (suppP m L H β) (histSupp m L H h) ∧ suppP m L H β ⊆ K.zone a e τ then some β else none
  else none

/-- The guarded placement's support is fresh and in the zone. [folklore] -/
theorem gnext_spec {a : Site 2} {e : MDir} {τ : K.Tok} {h : BrickHist d} {β : BrickPos d}
    (hβ : K.gnext m L H a e τ h = some β) :
    h.length < K.R ∧ AllGood m L H h ∧ K.next a e τ h = some β ∧
      Disjoint (suppP m L H β) (histSupp m L H h) ∧ suppP m L H β ⊆ K.zone a e τ := by
  unfold gnext at hβ
  split_ifs at hβ with h1
  · cases hn : K.next a e τ h with
    | none => rw [hn] at hβ; exact absurd hβ (by simp)
    | some β' =>
      rw [hn] at hβ
      simp only at hβ
      split_ifs at hβ with h2
      cases hβ
      exact ⟨h1.1, h1.2, rfl, h2.1, h2.2⟩

/-- **The guarded run** of the attempt along `(a, e)` from `τ` on the configuration `ω`: the history
after `n` guarded placements. [cite: GrimmettPercolation1999, §7.3 pp. 171–174] -/
def run (a : Site 2) (e : MDir) (τ : K.Tok) : ℕ → BondConfig (Site d) → BrickHist d
  | 0, _ => []
  | n + 1, ω =>
    match K.gnext m L H a e τ (run a e τ n ω) with
    | none => run a e τ n ω
    | some β => (β, obs ω (suppP m L H β)) :: run a e τ n ω

variable {a : Site 2} {e : MDir} {τ : K.Tok}

/-- Unfolding a step on which no brick is placed. [folklore] -/
theorem run_succ_of_none {n : ℕ} {ω : BondConfig (Site d)} (h : K.gnext m L H a e τ (K.run m L H a e τ n ω) = none) :
    K.run m L H a e τ (n + 1) ω = K.run m L H a e τ n ω := by
  rw [run, h]

/-- Unfolding a step on which a brick is placed. [folklore] -/
theorem run_succ_of_some {n : ℕ} {ω : BondConfig (Site d)} {β : BrickPos d}
    (h : K.gnext m L H a e τ (K.run m L H a e τ n ω) = some β) :
    K.run m L H a e τ (n + 1) ω = (β, obs ω (suppP m L H β)) :: K.run m L H a e τ n ω := by
  rw [run, h]

/-- Every record of the run is an actual observation: `r.2 = ω ∩ supp`. [folklore] -/
theorem run_obs {n : ℕ} {ω : BondConfig (Site d)} {r : BrickRec d} (hr : r ∈ K.run m L H a e τ n ω) :
    r.2 = obs ω (suppP m L H r.1) := by
  induction n with
  | zero => exact absurd hr List.not_mem_nil
  | succ n ih =>
    cases h : K.gnext m L H a e τ (K.run m L H a e τ n ω) with
    | none => rw [K.run_succ_of_none m L H h] at hr; exact ih hr
    | some β =>
      rw [K.run_succ_of_some m L H h] at hr
      rcases List.mem_cons.1 hr with rfl | hr
      · rfl
      · exact ih hr

/-- The examined edges of the run lie in the zone. [folklore] -/
theorem histSupp_run_subset_zone (n : ℕ) (ω : BondConfig (Site d)) :
    histSupp m L H (K.run m L H a e τ n ω) ⊆ K.zone a e τ := by
  induction n with
  | zero => simp [run]
  | succ n ih =>
    cases h : K.gnext m L H a e τ (K.run m L H a e τ n ω) with
    | none => rwa [K.run_succ_of_none m L H h]
    | some β =>
      rw [K.run_succ_of_some m L H h, histSupp_cons]
      exact Finset.union_subset (K.gnext_spec m L H h).2.2.2.2 ih

/-- **Locality of the run**: configurations agreeing on the edges examined by the run of `ω` have
the same run. [cite: GrimmettPercolation1999, §7.4 p. 176] -/
theorem run_eq_of_agree {n : ℕ} {ω ω' : BondConfig (Site d)}
    (hag : ∀ z ∈ histSupp m L H (K.run m L H a e τ n ω), (z ∈ ω ↔ z ∈ ω')) :
    K.run m L H a e τ n ω' = K.run m L H a e τ n ω := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases h : K.gnext m L H a e τ (K.run m L H a e τ n ω) with
    | none =>
      rw [K.run_succ_of_none m L H h] at hag ⊢
      have ih' := ih hag
      rw [run, ih', h]
    | some β =>
      rw [K.run_succ_of_some m L H h] at hag ⊢
      rw [histSupp_cons] at hag
      have ih' := ih fun z hz => hag z (Finset.mem_union_right _ hz)
      rw [run, ih', h]
      simp only
      congr 2
      exact obs_congr fun z hz => (hag z (Finset.mem_union_left _ hz)).symm

/-- `{run n = h}` is determined by the edges examined in `h`. [folklore] -/
theorem determinedBy_run (n : ℕ) (h : BrickHist d) :
    DeterminedBy {ω | K.run m L H a e τ n ω = h} (↑(histSupp m L H h) : Set (Sym2 (Site d))) := by
  rw [determinedBy_iff]
  intro ω ω' hωω'
  have hag : ∀ z ∈ histSupp m L H h, (z ∈ ω ↔ z ∈ ω') := fun z hz => by
    constructor
    · intro hm; exact ((Set.ext_iff.1 hωω' z).1 ⟨hm, hz⟩).1
    · intro hm; exact ((Set.ext_iff.1 hωω' z).2 ⟨hm, hz⟩).1
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hω; subst hω; exact K.run_eq_of_agree m L H hag
  · intro hω'; subst hω'; exact K.run_eq_of_agree m L H fun z hz => (hag z hz).symm

/-- `{run n = h}` is measurable. [folklore] -/
theorem measurableSet_run_eq (n : ℕ) (h : BrickHist d) : MeasurableSet {ω | K.run m L H a e τ n ω = h} :=
  measurableSet_of_isLocalEvent_holds ⟨_, K.determinedBy_run m L H n h⟩

/-- The run of the observed configuration `ω ∩ reveal` is the run of `ω`. [folklore] -/
theorem run_coe_obs (n : ℕ) (ω : BondConfig (Site d)) {D : Finset (Sym2 (Site d))}
    (hD : histSupp m L H (K.run m L H a e τ n ω) ⊆ D) :
    K.run m L H a e τ n ((↑(obs ω D) : Set (Sym2 (Site d))) : BondConfig (Site d)) = K.run m L H a e τ n ω := by
  refine K.run_eq_of_agree m L H fun z hz => ?_
  rw [Finset.mem_coe, mem_obs_iff]
  exact ⟨fun hzω => ⟨hD hz, hzω⟩, fun h => h.2⟩

/-! ### The guarded outcome and the gadget system -/

/-- The edges examined by the whole attempt. [cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
def reveal (a : Site 2) (e : MDir) (τ : K.Tok) (ω : BondConfig (Site d)) : Finset (Sym2 (Site d)) :=
  histSupp m L H (K.run m L H a e τ K.R ω)

/-- The guard on the handed-on tokens: all correctly sourced, and, for every onward direction,
admissible, anchored in the target cell, with zone avoiding the examined edges. [folklore] -/
def FinishOK (a : Site 2) (e : MDir) (h : BrickHist d) (f : MDir → K.Tok) : Prop :=
  (∀ e', K.srcDir (f e') = some e) ∧ ∀ e', e' ≠ rev e →
    K.Adm (a + stepVec e) e' (f e') ∧ K.cell (K.anchor (f e')) = a + stepVec e ∧
      Disjoint (histSupp m L H h) (K.zone (a + stepVec e) e' (f e'))

/-- **The guarded outcome** of a history: the plan's tokens, handed on only if the history is all
good and the tokens pass the guard `FinishOK` (Grimmett's (C), dynamically).
[cite: GrimmettPercolation1999, §7.3 pp. 173–174] -/
def gfinish (a : Site 2) (e : MDir) (τ : K.Tok) (h : BrickHist d) : Option (MDir → K.Tok) :=
  match K.finish a e τ h with
  | none => none
  | some f => if AllGood m L H h ∧ K.FinishOK m L H a e h f then some f else none

/-- What a successful guarded outcome guarantees. [folklore] -/
theorem gfinish_spec {h : BrickHist d} {f : MDir → K.Tok} (hf : K.gfinish m L H a e τ h = some f) :
    K.finish a e τ h = some f ∧ AllGood m L H h ∧ K.FinishOK m L H a e h f := by
  unfold gfinish at hf
  cases hfin : K.finish a e τ h with
  | none => rw [hfin] at hf; exact absurd hf (by simp)
  | some f' =>
    rw [hfin] at hf
    simp only at hf
    split_ifs at hf with hc
    cases hf
    exact ⟨rfl, hc.1, hc.2⟩

/-- The guarded outcome succeeds when the plan's outcome passes the guards. [folklore] -/
theorem gfinish_eq_some {h : BrickHist d} {f : MDir → K.Tok} (hfin : K.finish a e τ h = some f) (hg : AllGood m L H h)
    (hc : K.FinishOK m L H a e h f) : K.gfinish m L H a e τ h = some f := by
  unfold gfinish
  rw [hfin]
  simp only
  rw [if_pos ⟨hg, hc⟩]

/-- The outcome read off the observed open edges: the guarded outcome of the run of the observed
configuration. [cite: GrimmettPercolation1999, §7.3 p. 174] -/
def result (a : Site 2) (e : MDir) (τ : K.Tok) (o : Finset (Sym2 (Site d))) : Option (MDir → K.Tok) :=
  K.gfinish m L H a e τ (K.run m L H a e τ K.R ((↑o : Set (Sym2 (Site d))) : BondConfig (Site d)))

/-- On an actual observation the outcome is that of the actual run. [folklore] -/
theorem result_obs_reveal (ω : BondConfig (Site d)) :
    K.result m L H a e τ (obs ω (K.reveal m L H a e τ ω)) = K.gfinish m L H a e τ (K.run m L H a e τ K.R ω) := by
  rw [result, reveal, K.run_coe_obs m L H K.R ω subset_rfl]

/-- **The adaptive gadget system of a kit**: zones, the examined edges of the guarded run, the
guarded outcome; the structural axioms (examined edges in the zone, locality, dynamic disjointness
from the onward zones) hold by construction. [cite: GrimmettPercolation1999, §7.3 pp. 171–174] -/
def system : AGadgetSystem (Site d) where
  Tok := K.Tok
  anchor := K.anchor
  srcDir := K.srcDir
  U₀ := K.U₀
  init := K.init
  Adm := K.Adm
  zone := K.zone
  reveal := K.reveal m L H
  reveal_subset a e τ ω := K.histSupp_run_subset_zone m L H K.R ω
  reveal_local a e τ ω ω' hag := by
    change histSupp m L H (K.run m L H a e τ K.R ω') = histSupp m L H (K.run m L H a e τ K.R ω)
    rw [K.run_eq_of_agree m L H hag]
  result := K.result m L H
  parent_disjoint a e τ ω f hf e' he' := by
    change K.result m L H a e τ (obs ω (K.reveal m L H a e τ ω)) = some f at hf
    rw [K.result_obs_reveal] at hf
    exact ((K.gfinish_spec m L H hf).2.2.2 e' he').2.2

/-! ### The failure bound -/

section Prob

variable (p : unitInterval)

/-- The event "the `(n+1)`-st step places a brick which is not clean-good". [folklore] -/
def badStep (a : Site 2) (e : MDir) (τ : K.Tok) (n : ℕ) : Set (BondConfig (Site d)) :=
  {ω | ∃ β, K.gnext m L H a e τ (K.run m L H a e τ n ω) = some β ∧ ω ∉ placedC m L H β}

/-- **One step fails rarely**: `P_p(badStep n) ≤ 1 - P_p(goodC)`. Decompose along the history
`h = run n ω` (determined by its examined edges): the new brick's event is determined by its
support, which is fresh, so `P(run n = h, brick not good) = P(run n = h) (1 - P(goodC))`
(`bondPercolation_real_inter_memDep_le`, `prob_placedC`). [cite: GrimmettPercolation1999, §7.3 p. 172 (A), (7.56)] -/
theorem prob_badStep_le (hH : 1 ≤ H) (hmL : m < L) (n : ℕ) :
    (bondPercolation (zdGraph d) p).real (K.badStep m L H a e τ n) ≤
      1 - (bondPercolation (zdGraph d) p).real (goodC d m L H) := by
  set μ := bondPercolation (zdGraph d) p with hμ
  set A : Set (BondConfig (Site d)) := {ω | K.gnext m L H a e τ (K.run m L H a e τ n ω) ≠ none} with hA
  set Ψ : BondConfig (Site d) → BrickHist d := fun ω => K.run m L H a e τ n ω with hΨ
  set E : BrickHist d → Set (BondConfig (Site d)) := fun h =>
    match K.gnext m L H a e τ h with
    | none => ∅
    | some β => (placedC m L H β)ᶜ with hE
  set T : BrickHist d → Set (Sym2 (Site d)) := fun h =>
    match K.gnext m L H a e τ h with
    | none => ∅
    | some β => ↑(suppP m L H β) with hT
  have hpiece : ∀ h, A ∩ Ψ ⁻¹' {h} = {ω | K.run m L H a e τ n ω = h} ∩ {_ω | K.gnext m L H a e τ h ≠ none} := by
    intro h; ext ω
    simp only [hA, hΨ, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2⟩; subst h2; exact ⟨rfl, h1⟩
    · rintro ⟨h1, h2⟩; subst h1; exact ⟨h2, rfl⟩
  have hsub : K.badStep m L H a e τ n ⊆ A ∩ {ω | ω ∈ E (Ψ ω)} := by
    rintro ω ⟨β, hβ, hbad⟩
    refine ⟨by simp [hA, hβ], ?_⟩
    simp only [Set.mem_setOf_eq, hE, hΨ, hβ]
    exact hbad
  have hle := bondPercolation_real_inter_memDep_le (zdGraph d) p (A := A) (fun h => ↑(histSupp m L H h)) T Ψ E
    (fun h => by rw [hpiece]; exact (K.determinedBy_run m L H n h).inter (determinedBy_setOf_const _ _))
    (fun h => by rw [hpiece]; exact (K.measurableSet_run_eq m L H n h).inter (MeasurableSet.const _))
    (fun h => by
      simp only [hE, hT]
      cases K.gnext m L H a e τ h with
      | none => exact determinedBy_empty' _
      | some β => exact (determinedBy_placedC_suppP hH hmL β).compl)
    (fun h => by
      simp only [hE]
      cases K.gnext m L H a e τ h with
      | none => exact MeasurableSet.empty
      | some β => exact (measurableSet_placedC hH hmL β).compl)
    (fun ω hω => by
      simp only [hT, hΨ]
      cases hg : K.gnext m L H a e τ (K.run m L H a e τ n ω) with
      | none => exact disjoint_bot_right
      | some β => exact Finset.disjoint_coe.2 (K.gnext_spec m L H hg).2.2.2.1.symm)
    (q := 1 - μ.real (goodC d m L H))
    (fun ω hω => by
      simp only [hE, hΨ]
      cases hg : K.gnext m L H a e τ (K.run m L H a e τ n ω) with
      | none => simp only [measureReal_empty]; exact sub_nonneg.2 measureReal_le_one
      | some β =>
        simp only
        rw [probReal_compl_eq_one_sub (measurableSet_placedC hH hmL β), prob_placedC])
  calc μ.real (K.badStep m L H a e τ n) ≤ μ.real (A ∩ {ω | ω ∈ E (Ψ ω)}) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ (1 - μ.real (goodC d m L H)) * μ.real A := hle
    _ ≤ 1 - μ.real (goodC d m L H) := mul_le_of_le_one_right (sub_nonneg.2 measureReal_le_one) measureReal_le_one

/-- A run which is not all good made a bad step. [folklore] -/
theorem exists_badStep_of_not_allGood (hH : 1 ≤ H) (hmL : m < L) {N : ℕ} {ω : BondConfig (Site d)}
    (hbad : ¬AllGood m L H (K.run m L H a e τ N ω)) : ∃ n < N, ω ∈ K.badStep m L H a e τ n := by
  induction N with
  | zero => exact absurd (allGood_nil (d := d) m L H) (by simp [run] at hbad)
  | succ N ih =>
    cases hg : K.gnext m L H a e τ (K.run m L H a e τ N ω) with
    | none =>
      rw [K.run_succ_of_none m L H hg] at hbad
      obtain ⟨n, hn, hω⟩ := ih hbad
      exact ⟨n, by omega, hω⟩
    | some β =>
      rw [K.run_succ_of_some m L H hg, allGood_cons] at hbad
      have hgood := (K.gnext_spec m L H hg).2.1
      have hrec : ¬GoodRec m L H (β, obs ω (suppP m L H β)) := fun h => hbad ⟨h, hgood⟩
      rw [goodRec_obs_iff hH hmL] at hrec
      exact ⟨N, N.lt_succ_self, β, hg, hrec⟩

/-- **The failure bound**: the guarded run of length `R` is not all good with probability at most
`R (1 - P_p(goodC))` (Grimmett (7.56): an attempt of at most `R` bricks; here by the union bound
over its steps). [cite: GrimmettPercolation1999, §7.3 p. 174 (7.56)] -/
theorem prob_not_allGood_le (hH : 1 ≤ H) (hmL : m < L) :
    (bondPercolation (zdGraph d) p).real {ω | ¬AllGood m L H (K.run m L H a e τ K.R ω)} ≤
      K.R * (1 - (bondPercolation (zdGraph d) p).real (goodC d m L H)) := by
  have hsub : {ω | ¬AllGood m L H (K.run m L H a e τ K.R ω)} ⊆ ⋃ n ∈ Finset.range K.R, K.badStep m L H a e τ n := by
    intro ω hω
    obtain ⟨n, hn, hω⟩ := K.exists_badStep_of_not_allGood m L H hH hmL hω
    exact Set.mem_biUnion (Finset.mem_range.2 hn) hω
  calc (bondPercolation (zdGraph d) p).real {ω | ¬AllGood m L H (K.run m L H a e τ K.R ω)}
      ≤ (bondPercolation (zdGraph d) p).real (⋃ n ∈ Finset.range K.R, K.badStep m L H a e τ n) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ n ∈ Finset.range K.R, (bondPercolation (zdGraph d) p).real (K.badStep m L H a e τ n) :=
        measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _n ∈ Finset.range K.R, (1 - (bondPercolation (zdGraph d) p).real (goodC d m L H)) :=
        Finset.sum_le_sum fun n _ => K.prob_badStep_le m L H p hH hmL n
    _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end Prob

/-! ### Good kits and the percolation theorem -/

/-- **The obligations of a kit** (all about its own geometry), for the graph `ℤ^d`, the base vertex
`x₀` and the guarded runs of its plan: admissibility and provenance of the initial tokens; static
disjointness of the zones (as in `AGadgetSystem.Lawful`); zones of attempts not targeting the origin
avoid `U₀`; the initial edges are lattice edges and, when open, make the initial seeds open and join
their centres to `x₀`; and along every all-good guarded run of length `R` from an admissible token:
the plan's outcome is defined and passes the guards (**completeness**), and — if the token's seed is
open — the tokens handed on have open seeds joined to the token's centre (**connectivity**).
[cite: GrimmettPercolation1999, §7.3 pp. 171–176] -/
structure Good (x₀ : Site d) : Prop where
  adm_init : ∀ e, K.Adm 0 e (K.init e)
  src_init : ∀ e, K.srcDir (K.init e) = none
  disjoint_zone : ∀ {a : Site 2} {e : MDir} {τ : K.Tok} {a' : Site 2} {e' : MDir} {τ' : K.Tok},
    K.Adm a e τ → K.Adm a' e' τ' → (a, e) ≠ (a', e') → a' ≠ a + stepVec e →
      ¬(a' + stepVec e' = a ∧ K.srcDir τ = some e') → Disjoint (K.zone a e τ) (K.zone a' e' τ')
  disjoint_U₀ : ∀ {a : Site 2} {e : MDir} {τ : K.Tok}, K.Adm a e τ → a + stepVec e ≠ 0 → Disjoint (K.zone a e τ) K.U₀
  U₀_subset : (↑K.U₀ : Set (Sym2 (Site d))) ⊆ (zdGraph d).edgeSet
  conn_init : ∀ ω : BondConfig (Site d), (↑K.U₀ : Set (Sym2 (Site d))) ⊆ ω → ∀ e,
    K.Pre m (K.init e) ω ∧ K.anchor (K.init e) ∈ openCluster ω x₀
  complete : ∀ {a : Site 2} {e : MDir} {τ : K.Tok} (ω : BondConfig (Site d)), K.Adm a e τ →
    AllGood m L H (K.run m L H a e τ K.R ω) → K.gfinish m L H a e τ (K.run m L H a e τ K.R ω) ≠ none
  connect : ∀ {a : Site 2} {e : MDir} {τ : K.Tok} (ω : BondConfig (Site d)) {f : MDir → K.Tok}, K.Adm a e τ → K.Pre m τ ω →
    K.gfinish m L H a e τ (K.run m L H a e τ K.R ω) = some f → ∀ e', e' ≠ rev e →
      K.Pre m (f e') ω ∧ K.anchor (f e') ∈ openCluster ω (K.anchor τ)

variable {K} {x₀ : Site d}

/-- **A good kit gives a lawful gadget system** with failure bound `R (1 - P_p(goodC))`.
[cite: GrimmettPercolation1999, §7.3 pp. 171–176] -/
theorem lawful_of_good (hK : K.Good m L H x₀) (hH : 1 ≤ H) (hmL : m < L) (p : unitInterval) :
    (K.system m L H).Lawful (zdGraph d) p (K.R * (1 - (bondPercolation (zdGraph d) p).real (goodC d m L H))) x₀ K.cell
      (K.Pre m) where
  adm :=
    { adm_init := hK.adm_init
      src_init := hK.src_init
      adm_result := by
        intro a e τ o f _ hf e' he'
        exact ((K.gfinish_spec m L H hf).2.2.2 e' he').1
      src_result := by
        intro a e τ o f _ hf e'
        exact (K.gfinish_spec m L H hf).2.2.1 e' }
  conn :=
    { conn_init := hK.conn_init
      conn_result := by
        intro a e τ f ω hadm hpre hf e' he'
        change K.result m L H a e τ (obs ω (K.reveal m L H a e τ ω)) = some f at hf
        rw [K.result_obs_reveal] at hf
        exact hK.connect ω hadm hpre hf e' he'
      cell_result := by
        intro a e τ o f _ hf e' he'
        exact ((K.gfinish_spec m L H hf).2.2.2 e' he').2.1 }
  disjoint_zone := hK.disjoint_zone
  disjoint_U₀ := hK.disjoint_U₀
  prob_fail := by
    intro a e τ hadm
    change (bondPercolation (zdGraph d) p).real {ω | K.result m L H a e τ (obs ω (K.reveal m L H a e τ ω)) = none} ≤ _
    refine le_trans (measureReal_mono fun ω hω => ?_) (K.prob_not_allGood_le m L H p hH hmL)
    simp only [Set.mem_setOf_eq] at hω ⊢
    rw [K.result_obs_reveal] at hω
    intro hgood
    exact hK.complete ω hadm hgood hω

/-- **A good block kit percolates.** If the kit is good, `L > m`, `H ≥ 1`, `p > 0` and
`R (1 - P_p(goodC)) ≤ 1/64` (bricks are clean-good with probability close enough to `1`, Grimmett's
(7.53) with `ν = 1/(64R)`), then the base vertex `x₀` lies in an infinite open cluster of `ℤ^d`
with positive probability: `θ_{x₀}(p) > 0` (`AGadgetSystem.theta_pos_of_lawful`).
[cite: GrimmettPercolation1999, Lemma (7.52) p. 169, proof pp. 169–176] -/
theorem theta_pos (hK : K.Good m L H x₀) (hH : 1 ≤ H) (hmL : m < L) (p : unitInterval) (hp : 0 < (p : ℝ))
    (hν : K.R * (1 - (bondPercolation (zdGraph d) p).real (goodC d m L H)) ≤ 1 / 64) :
    0 < theta (zdGraph d) x₀ p :=
  AGadgetSystem.theta_pos_of_lawful (lawful_of_good m L H hK hH hmL p) hν hK.U₀_subset hp

end Kit

end BGNd

end Percolation.Literature

end
