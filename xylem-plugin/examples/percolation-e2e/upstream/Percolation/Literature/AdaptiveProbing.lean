import Percolation.Literature.SequentialProbing
import Percolation.Util.Linter

/-!
# Sequential fresh probing with adaptive probes

`SequentialProbing.lean` treats explorations whose
every step examines a finite edge set `D` fixed by the history. In the block construction of
Barsky, Grimmett and Newman (Grimmett, *Percolation*, 2nd ed. (1999), §7.3 pp. 171–176) one step of
the renormalized process — an attempt to occupy a macro-vertex — is itself a dynamic exploration
(bricks stacked one after the other, each placed according to the open paths found so far), and
the set of edges it actually examines depends on the configuration; only an a-priori *envelope*
(the "region reserved" for the attempt) is fixed in advance, and the next attempt starts exactly
where the previous one stopped (p. 173 (C): "the intersection of a new brick with the region
considered so far must be limited to a subset of its underside" — a condition on the region
considered SO FAR, not on envelopes). This file PROVES the estimates of `SequentialProbing.lean`
in that generality:

* `AExplorer V` — the next adaptive probe as a function of the history of records;
  `AExplorer.Fresh U₀`: every envelope avoids `U₀` and the edges REVEALED (not the envelopes) by
  the earlier probes.

Records, histories, observations and scores (`ProbeRecord`, `ProbeHistory`, `obs`, `supp`,
`AllSucc`, `nfail`, `AnySucc`) are those of `SequentialProbing.lean`.

## References

* G. Grimmett, *Percolation*, 2nd ed., Grundlehren 321, Springer 1999, §7.2 pp. 152–157, §7.3
  pp. 169–176 ((A)–(C) p. 172–173, (7.56) p. 176), §7.4 p. 176.
* D. J. Barsky, G. R. Grimmett, C. M. Newman, Dynamic renormalization and continuity of the
  percolation transition in orthants, in *Spatial Stochastic Processes*, Birkhäuser 1991, 37–55.
-/

noncomputable section

namespace Percolation.Literature

open MeasureTheory ProbabilityTheory ProbeHistory
open scoped ENNReal Classical

variable {V : Type*}

/-! ## Adaptive probes -/

/-- An **adaptive probe**: an envelope, and the configuration-dependent set of edges actually
examined, inside the envelope and *local* (configurations agreeing on the examined set examine the
same set). [cite: GrimmettPercolation1999, §7.3 p. 173 (C), §7.4 p. 176] -/
structure AProbe (V : Type*) where
  /-- the envelope: all edges the probe may examine -/
  env : Finset (Sym2 V)
  /-- the edges examined on the configuration `ω` -/
  reveal : BondConfig V → Finset (Sym2 V)
  /-- the examined edges lie in the envelope -/
  reveal_subset : ∀ ω, reveal ω ⊆ env
  /-- locality: the examined set is determined by the states of the examined edges -/
  reveal_local : ∀ ω ω' : BondConfig V, (∀ e ∈ reveal ω, (e ∈ ω ↔ e ∈ ω')) → reveal ω' = reveal ω

namespace AProbe

/-- The open edges observed by the probe. [folklore] -/
def read (P : AProbe V) (ω : BondConfig V) : Finset (Sym2 V) := obs ω (P.reveal ω)

/-- The record of the probe: examined edges and the open ones among them. [folklore] -/
def record (P : AProbe V) (ω : BondConfig V) : ProbeRecord V := (P.reveal ω, P.read ω)

/-- Configurations agreeing on the examined set have the same record. [folklore] -/
theorem record_congr (P : AProbe V) {ω ω' : BondConfig V} (h : ∀ e ∈ P.reveal ω, (e ∈ ω ↔ e ∈ ω')) :
    P.record ω' = P.record ω := by
  have hrev : P.reveal ω' = P.reveal ω := P.reveal_local ω ω' h
  simp only [record, read, hrev]
  rw [obs_congr (ω := ω') (ω' := ω) fun e he => (h e he).symm]

/-- Configurations agreeing on the envelope have the same record. [folklore] -/
theorem record_congr_env (P : AProbe V) {ω ω' : BondConfig V} (h : ∀ e ∈ P.env, (e ∈ ω ↔ e ∈ ω')) :
    P.record ω' = P.record ω :=
  P.record_congr fun e he => h e (P.reveal_subset ω he)

/-- An event read off the record of an adaptive probe is determined by its envelope. [folklore] -/
theorem determinedBy_setOf_record (P : AProbe V) (ψ : ProbeRecord V → Prop) :
    DeterminedBy {ω : BondConfig V | ψ (P.record ω)} (↑P.env : Set (Sym2 V)) := by
  rw [determinedBy_iff]
  intro ω ω' hωω'
  simp only [Set.mem_setOf_eq]
  rw [P.record_congr_env (ω := ω) (ω' := ω') fun e he => ?_]
  constructor
  · intro hm; exact ((Set.ext_iff.1 hωω' e).1 ⟨hm, he⟩).1
  · intro hm; exact ((Set.ext_iff.1 hωω' e).2 ⟨hm, he⟩).1

/-- An event read off the observation of an adaptive probe is determined by its envelope. [folklore] -/
theorem determinedBy_setOf_read (P : AProbe V) (ψ : Finset (Sym2 V) → Prop) :
    DeterminedBy {ω : BondConfig V | ψ (P.read ω)} (↑P.env : Set (Sym2 V)) :=
  P.determinedBy_setOf_record fun r => ψ r.2

/-- An event read off the record is measurable. [folklore] -/
theorem measurableSet_setOf_record (P : AProbe V) (ψ : ProbeRecord V → Prop) :
    MeasurableSet {ω : BondConfig V | ψ (P.record ω)} :=
  measurableSet_of_isLocalEvent_holds ⟨P.env, P.determinedBy_setOf_record ψ⟩

/-- An event read off the observation is measurable. [folklore] -/
theorem measurableSet_setOf_read (P : AProbe V) (ψ : Finset (Sym2 V) → Prop) :
    MeasurableSet {ω : BondConfig V | ψ (P.read ω)} :=
  P.measurableSet_setOf_record fun r => ψ r.2

end AProbe

/-! ## Explorers and their histories -/

/-- An **adaptive explorer**: the next adaptive probe as a function of the probing history
(`none`: no probe is made). (Grimmett 1999, §7.3 p. 171: "The algorithm to be followed …"; each
step is an attempt, itself a dynamic examination, pp. 172–174.) [cite: GrimmettPercolation1999, §7.3 pp. 171–174] -/
structure AExplorer (V : Type*) where
  /-- the next probe, given the history (newest probe first) -/
  next : ProbeHistory V → Option (AProbe V)

namespace AExplorer

variable (E : AExplorer V)

/-- The step recorded after history `h` on the configuration `ω`. [folklore] -/
def step (h : ProbeHistory V) (ω : BondConfig V) : Option (ProbeRecord V) :=
  (E.next h).map fun P => P.record ω

/-- The history after `n` steps of the explorer on `ω` (newest first). [cite: GrimmettPercolation1999, §7.3 p. 171] -/
def hist : ℕ → BondConfig V → ProbeHistory V
  | 0, _ => []
  | n + 1, ω => E.step (hist n ω) ω :: hist n ω

/-- The initial history is empty. [folklore] -/
@[simp] theorem hist_zero (ω : BondConfig V) : E.hist 0 ω = [] := rfl

/-- One more step of the history. [folklore] -/
theorem hist_succ (n : ℕ) (ω : BondConfig V) : E.hist (n + 1) ω = E.step (E.hist n ω) ω :: E.hist n ω := rfl

/-- The history after `n` steps has length `n`. [folklore] -/
@[simp] theorem length_hist (n : ℕ) (ω : BondConfig V) : (E.hist n ω).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [hist_succ, List.length_cons, ih]

/-- No probe is recorded when the explorer stops. [folklore] -/
theorem step_of_none {h : ProbeHistory V} (hD : E.next h = none) (ω : BondConfig V) : E.step h ω = none := by
  simp [step, hD]

/-- The recorded probe: examined edges and observation. [folklore] -/
theorem step_of_some {h : ProbeHistory V} {P : AProbe V} (hD : E.next h = some P) (ω : BondConfig V) :
    E.step h ω = some (P.record ω) := by
  simp [step, hD]

/-- **The exploration does not look ahead**: configurations agreeing on the supports recorded in
`h` have history `h` simultaneously. [cite: GrimmettPercolation1999, §7.4 p. 176] -/
theorem hist_eq_of_agree {n : ℕ} {h : ProbeHistory V} {ω ω' : BondConfig V}
    (hag : ∀ e ∈ supp h, (e ∈ ω ↔ e ∈ ω')) (hω : E.hist n ω = h) : E.hist n ω' = h := by
  induction n generalizing h with
  | zero => rw [← hω]; rfl
  | succ n ih =>
    rw [hist_succ] at hω ⊢
    subst hω
    have htail : E.hist n ω' = E.hist n ω := ih (fun e he => hag e (supp_subset_cons _ _ he)) rfl
    rw [htail]
    congr 1
    cases hD : E.next (E.hist n ω) with
    | none => rw [E.step_of_none hD, E.step_of_none hD]
    | some P =>
      rw [E.step_of_some hD, E.step_of_some hD]
      congr 1
      refine P.record_congr fun e he => hag e ?_
      rw [E.step_of_some hD, supp_cons_some]
      exact Finset.mem_union_left _ he

/-- `{hist n = h}` is determined by the supports recorded in `h`. [cite: GrimmettPercolation1999, §7.4 p. 176] -/
theorem determinedBy_hist (n : ℕ) (h : ProbeHistory V) :
    DeterminedBy {ω | E.hist n ω = h} (↑(supp h) : Set (Sym2 V)) := by
  rw [determinedBy_iff]
  intro ω ω' hωω'
  have hag : ∀ e ∈ supp h, (e ∈ ω ↔ e ∈ ω') := fun e he => by
    constructor
    · intro hm; exact ((Set.ext_iff.1 hωω' e).1 ⟨hm, he⟩).1
    · intro hm; exact ((Set.ext_iff.1 hωω' e).2 ⟨hm, he⟩).1
  exact ⟨fun hω => E.hist_eq_of_agree hag hω, fun hω' => E.hist_eq_of_agree (fun e he => (hag e he).symm) hω'⟩

/-- `{hist n = h}` is measurable (a local event). [folklore] -/
theorem measurableSet_hist_eq (n : ℕ) (h : ProbeHistory V) : MeasurableSet {ω | E.hist n ω = h} :=
  measurableSet_of_isLocalEvent_holds ⟨_, E.determinedBy_hist n h⟩

/-- Any event read off the history is measurable (countably many histories). [folklore] -/
theorem measurableSet_setOf_hist [Countable V] (n : ℕ) (P : ProbeHistory V → BondConfig V → Prop)
    (hP : ∀ h, MeasurableSet {ω | P h ω}) : MeasurableSet {ω | P (E.hist n ω) ω} := by
  have : {ω | P (E.hist n ω) ω} = ⋃ h : ProbeHistory V, {ω | E.hist n ω = h} ∩ {ω | P h ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
    exact ⟨fun hω => ⟨_, rfl, hω⟩, fun ⟨h, hh, hω⟩ => hh ▸ hω⟩
  rw [this]
  exact MeasurableSet.iUnion fun h => (E.measurableSet_hist_eq n h).inter (hP h)

/-- Any property of the history defines a measurable event. [folklore] -/
theorem measurableSet_setOf_hist' [Countable V] (n : ℕ) (P : ProbeHistory V → Prop) :
    MeasurableSet {ω | P (E.hist n ω)} :=
  E.measurableSet_setOf_hist n (fun h _ => P h) fun h => by
    by_cases hP : P h
    · simp only [hP, Set.setOf_true]; exact MeasurableSet.univ
    · simp only [hP, Set.setOf_false]; exact MeasurableSet.empty

/-- **Freshness**: the envelope of every probe avoids the initial edge set `U₀` and the edges
examined by all earlier probes. (Grimmett 1999, p. 173 (C): "at every stage the intersection of a
new brick with the region considered so far must be limited to a subset of its underside".)
[cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
def Fresh (U₀ : Set (Sym2 V)) : Prop :=
  ∀ h P, E.next h = some P → Disjoint (↑P.env : Set (Sym2 V)) U₀ ∧ Disjoint P.env (supp h)

/-! ## The product formula and the conditional step -/

section Measure

variable [Countable V] (G : SimpleGraph V) (p : unitInterval)

/-- **Product formula.** For `A₀` determined by `U₀`, a history `h` whose next probe is `D`,
and any property `ψ` of its observation:
`P_p(A₀ ∩ {hist n = h} ∩ {ψ(read)}) = P_p(A₀ ∩ {hist n = h}) · P_p(ψ(read))` — the new probe
is independent of the past (its envelope is disjoint from the edges determining the past).
[cite: GrimmettPercolation1999, §7.3 p. 172 (A)] -/
theorem measure_inter_hist_inter_read {U₀ : Set (Sym2 V)} (hE : E.Fresh U₀) {A₀ : Set (BondConfig V)}
    (hA : DeterminedBy A₀ U₀) (hAm : MeasurableSet A₀) (n : ℕ) {h : ProbeHistory V}
    {D : AProbe V} (hD : E.next h = some D) (ψ : Finset (Sym2 V) → Prop) :
    bondPercolation G p (A₀ ∩ {ω | E.hist n ω = h} ∩ {ω | ψ (D.read ω)}) =
      bondPercolation G p (A₀ ∩ {ω | E.hist n ω = h}) * bondPercolation G p {ω | ψ (D.read ω)} := by
  obtain ⟨hDU, hDh⟩ := hE h D hD
  refine bondPercolation_inter_of_disjoint G p (S := U₀ ∪ ↑(supp h)) (T := ↑D.env) ?_ ?_
    (D.determinedBy_setOf_read ψ) (hAm.inter (E.measurableSet_hist_eq n h)) (D.measurableSet_setOf_read ψ)
  · exact Disjoint.union_left hDU.symm (Finset.disjoint_coe.2 hDh.symm)
  · exact (hA.mono Set.subset_union_left).inter ((E.determinedBy_hist n h).mono Set.subset_union_right)

/-- **Conditional step, upper bound.** If after every history satisfying `Φ` the next probe's
outcome lies in `ψ` with probability at most `c`, then
`P_p(A₀ ∩ {Φ(hist n)} ∩ {next outcome in ψ}) ≤ c · P_p(A₀ ∩ {Φ(hist n)} ∩ {a probe is made})`.
[cite: GrimmettPercolation1999, §7.3 p. 176 (7.56)] -/
theorem measure_inter_setOf_step_le {U₀ : Set (Sym2 V)} (hE : E.Fresh U₀) {A₀ : Set (BondConfig V)}
    (hA : DeterminedBy A₀ U₀) (hAm : MeasurableSet A₀) (n : ℕ) (Φ : ProbeHistory V → Prop)
    (ψ : ProbeHistory V → Finset (Sym2 V) → Prop) (c : ℝ≥0∞)
    (hc : ∀ h D, E.next h = some D → Φ h → bondPercolation G p {ω | ψ h (D.read ω)} ≤ c) :
    bondPercolation G p (A₀ ∩ {ω | Φ (E.hist n ω) ∧ ∃ D, E.next (E.hist n ω) = some D ∧ ψ (E.hist n ω) (D.read ω)})
      ≤ c * bondPercolation G p (A₀ ∩ {ω | Φ (E.hist n ω) ∧ E.next (E.hist n ω) ≠ none}) := by
  classical
  set μ := bondPercolation G p with hμ
  set X : ProbeHistory V → Set (BondConfig V) := fun h =>
    (A₀ ∩ {ω | E.hist n ω = h}) ∩ {ω | Φ h ∧ ∃ D, E.next h = some D ∧ ψ h (D.read ω)} with hX
  set Y : ProbeHistory V → Set (BondConfig V) := fun h =>
    (A₀ ∩ {ω | E.hist n ω = h}) ∩ {_ω | Φ h ∧ E.next h ≠ none} with hY
  have hXeq : A₀ ∩ {ω | Φ (E.hist n ω) ∧ ∃ D, E.next (E.hist n ω) = some D ∧ ψ (E.hist n ω) (D.read ω)} = ⋃ h, X h := by
    ext ω
    simp only [hX, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iUnion]
    exact ⟨fun ⟨hA, hΦ⟩ => ⟨_, ⟨hA, rfl⟩, hΦ⟩, fun ⟨h, ⟨hA, hh⟩, hΦ⟩ => ⟨hA, hh ▸ hΦ⟩⟩
  have hYeq : A₀ ∩ {ω | Φ (E.hist n ω) ∧ E.next (E.hist n ω) ≠ none} = ⋃ h, Y h := by
    ext ω
    simp only [hY, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iUnion]
    exact ⟨fun ⟨hA, hΦ⟩ => ⟨_, ⟨hA, rfl⟩, hΦ⟩, fun ⟨h, ⟨hA, hh⟩, hΦ⟩ => ⟨hA, hh ▸ hΦ⟩⟩
  have hdisj : ∀ Z : ProbeHistory V → Set (BondConfig V),
      Pairwise (Function.onFun Disjoint fun h => (A₀ ∩ {ω | E.hist n ω = h}) ∩ Z h) := by
    intro Z h h' hne
    exact Set.disjoint_left.2 fun ω hω hω' => hne (hω.1.2.symm.trans hω'.1.2)
  have hXm : ∀ h, MeasurableSet (X h) := by
    intro h
    refine (hAm.inter (E.measurableSet_hist_eq n h)).inter ?_
    cases hD : E.next h with
    | none =>
      have : {ω : BondConfig V | Φ h ∧ ∃ D, (none : Option (AProbe V)) = some D ∧ ψ h (D.read ω)} = ∅ := by
        ext ω; simp
      rw [this]; exact MeasurableSet.empty
    | some D =>
      have : {ω : BondConfig V | Φ h ∧ ∃ D', some D = some D' ∧ ψ h (D'.read ω)} = {ω | Φ h ∧ ψ h (D.read ω)} := by
        ext ω; simp
      rw [this]
      exact D.measurableSet_setOf_read fun o => Φ h ∧ ψ h o
  have hYm : ∀ h, MeasurableSet (Y h) := fun h =>
    (hAm.inter (E.measurableSet_hist_eq n h)).inter (MeasurableSet.const _)
  rw [hXeq, hYeq, measure_iUnion (hdisj _) hXm, measure_iUnion (hdisj _) hYm, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun h => ?_
  change μ (X h) ≤ c * μ (Y h)
  rcases Option.eq_none_or_eq_some (E.next h) with hD | ⟨D, hD⟩
  · have : X h = ∅ := by
      ext ω; simp [hX, hD]
    rw [this, measure_empty]
    exact zero_le
  · by_cases hΦ : Φ h
    · have hXh : X h = (A₀ ∩ {ω | E.hist n ω = h}) ∩ {ω | ψ h (D.read ω)} := by
        ext ω; simp [hX, hD, hΦ]
      have hYh : Y h = A₀ ∩ {ω | E.hist n ω = h} := by
        ext ω; simp [hY, hD, hΦ]
      rw [hXh, hYh, E.measure_inter_hist_inter_read G p hE hA hAm n hD (ψ h), mul_comm]
      exact mul_le_mul_left (hc h D hD hΦ) _
    · have : X h = ∅ := by
        ext ω; simp [hX, hΦ]
      rw [this, measure_empty]
      exact zero_le

/-! ## Success runs -/

/-- Real-valued form of the conditional step (upper bound). [cite: GrimmettPercolation1999, §7.3 p. 176 (7.56)] -/
theorem measureReal_inter_setOf_step_le {U₀ : Set (Sym2 V)} (hE : E.Fresh U₀) {A₀ : Set (BondConfig V)}
    (hA : DeterminedBy A₀ U₀) (hAm : MeasurableSet A₀) (n : ℕ) (Φ : ProbeHistory V → Prop)
    (ψ : ProbeHistory V → Finset (Sym2 V) → Prop) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ h D, E.next h = some D → Φ h → (bondPercolation G p).real {ω | ψ h (D.read ω)} ≤ c) :
    (bondPercolation G p).real
        (A₀ ∩ {ω | Φ (E.hist n ω) ∧ ∃ D, E.next (E.hist n ω) = some D ∧ ψ (E.hist n ω) (D.read ω)})
      ≤ c * (bondPercolation G p).real (A₀ ∩ {ω | Φ (E.hist n ω) ∧ E.next (E.hist n ω) ≠ none}) := by
  have h := E.measure_inter_setOf_step_le G p hE hA hAm n Φ ψ (ENNReal.ofReal c) fun h D hD hΦ => by
    rw [← ENNReal.ofReal_toReal (measure_ne_top (bondPercolation G p) {ω | ψ h (D.read ω)})]
    exact ENNReal.ofReal_le_ofReal (hc h D hD hΦ)
  simp only [measureReal_def]
  calc _ ≤ (ENNReal.ofReal c * bondPercolation G p (A₀ ∩ {ω | Φ (E.hist n ω) ∧ E.next (E.hist n ω) ≠ none})).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) h
    _ = _ := by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc0]

/-! ## Designated failures: the Peierls input for adaptive processes -/

section Designated

variable {U₀ : Set (Sym2 V)} {A₀ : Set (BondConfig V)}
  (succ : ProbeHistory V → Finset (Sym2 V) → Prop) (desig : ProbeHistory V → Prop)

/-- The level sets of the number of designated failures before any designated success. [folklore] -/
def levelSet (n j : ℕ) : Set (BondConfig V) :=
  {ω | nfail succ desig (E.hist n ω) = j ∧ ¬AnySucc succ desig (E.hist n ω)}

/-- **The supermartingale.** With `c = (1-q)⁻¹`, `Σ_j c^j P_p(A₀ ∩ {j designated failures, no
designated success, at time n}) ≤ P_p(A₀)`, when every designated probe fails with probability
at most `1 - q`. [cite: GrimmettPercolation1999, §7.2 p. 156 (Lemma 7.24), §7.3 p. 176] -/
theorem sum_pow_mul_measureReal_levelSet_le (hE : E.Fresh U₀) (hA : DeterminedBy A₀ U₀) (hAm : MeasurableSet A₀)
    {q : ℝ} (hq1 : q < 1)
    (hfail : ∀ h D, E.next h = some D → desig h → (bondPercolation G p).real {ω | ¬succ h (D.read ω)} ≤ 1 - q)
    (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), ((1 - q)⁻¹) ^ j * (bondPercolation G p).real (A₀ ∩ E.levelSet succ desig n j)
      ≤ (bondPercolation G p).real A₀ := by
  set μ := bondPercolation G p with hμ
  set c : ℝ := (1 - q)⁻¹ with hc
  have hq' : 0 < 1 - q := by linarith
  have hc0 : 0 ≤ c := inv_nonneg.2 hq'.le
  have hcq : c * (1 - q) = 1 := inv_mul_cancel₀ hq'.ne'
  induction n with
  | zero =>
    have h0 : A₀ ∩ E.levelSet succ desig 0 0 = A₀ := by
      ext ω; simp [levelSet]
    simp [h0]
  | succ n ih =>
    -- the three pieces of the level sets at time `n`
    set U : ℕ → Set (BondConfig V) := fun j => A₀ ∩ {ω | (nfail succ desig (E.hist n ω) = j ∧
        ¬AnySucc succ desig (E.hist n ω)) ∧ (E.next (E.hist n ω) = none ∨ ¬desig (E.hist n ω))} with hU
    set Gd : ℕ → Set (BondConfig V) := fun j => A₀ ∩ {ω | ((nfail succ desig (E.hist n ω) = j ∧
        ¬AnySucc succ desig (E.hist n ω)) ∧ desig (E.hist n ω)) ∧ E.next (E.hist n ω) ≠ none} with hGd
    set F : ℕ → Set (BondConfig V) := fun j => A₀ ∩ {ω | ((nfail succ desig (E.hist n ω) = j ∧
        ¬AnySucc succ desig (E.hist n ω)) ∧ desig (E.hist n ω)) ∧
        ∃ D, E.next (E.hist n ω) = some D ∧ ¬succ (E.hist n ω) (D.read ω)} with hF
    have hUm : ∀ j, MeasurableSet (U j) := fun j => hAm.inter (E.measurableSet_setOf_hist' n fun h =>
      (nfail succ desig h = j ∧ ¬AnySucc succ desig h) ∧ (E.next h = none ∨ ¬desig h))
    have hGm : ∀ j, MeasurableSet (Gd j) := fun j => hAm.inter (E.measurableSet_setOf_hist' n fun h =>
      ((nfail succ desig h = j ∧ ¬AnySucc succ desig h) ∧ desig h) ∧ E.next h ≠ none)
    -- partition of the level set at time `n`
    have hUG : ∀ j, μ.real (U j) + μ.real (Gd j) = μ.real (A₀ ∩ E.levelSet succ desig n j) := by
      intro j
      have hdisj : Disjoint (U j) (Gd j) := Set.disjoint_left.2 fun ω hU' hG' => by
        rcases hU'.2.2 with h1 | h1
        · exact hG'.2.2 h1
        · exact h1 hG'.2.1.2
      have hunion : U j ∪ Gd j = A₀ ∩ E.levelSet succ desig n j := by
        ext ω
        simp only [hU, hGd, levelSet, Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq]
        constructor
        · rintro (⟨hA, hl, -⟩ | ⟨hA, ⟨hl, -⟩, -⟩) <;> exact ⟨hA, hl⟩
        · rintro ⟨hA, hl⟩
          by_cases hd : E.next (E.hist n ω) = none ∨ ¬desig (E.hist n ω)
          · exact Or.inl ⟨hA, hl, hd⟩
          · push Not at hd
            exact Or.inr ⟨hA, ⟨hl, hd.2⟩, hd.1⟩
      rw [← hunion, measureReal_union hdisj (hGm j)]
    -- the conditional step
    have hFG : ∀ j, μ.real (F j) ≤ (1 - q) * μ.real (Gd j) := fun j =>
      E.measureReal_inter_setOf_step_le G p hE hA hAm n
        (fun h => (nfail succ desig h = j ∧ ¬AnySucc succ desig h) ∧ desig h) (fun h o => ¬succ h o) hq'.le
        fun h D hD hΦ => hfail h D hD hΦ.2
    -- the level sets at time `n + 1`
    have hstep : ∀ j, μ.real (A₀ ∩ E.levelSet succ desig (n + 1) j) ≤
        μ.real (U j) + (if j = 0 then 0 else μ.real (F (j - 1))) := by
      intro j
      have hsub : A₀ ∩ E.levelSet succ desig (n + 1) j ⊆ U j ∪ (if j = 0 then ∅ else F (j - 1)) := by
        rintro ω ⟨hA, hω⟩
        simp only [levelSet, Set.mem_setOf_eq, hist_succ] at hω
        rcases Option.eq_none_or_eq_some (E.next (E.hist n ω)) with hD | ⟨D, hD⟩
        · rw [E.step_of_none hD, nfail_cons_none, anySucc_cons_none] at hω
          exact Or.inl ⟨hA, hω, Or.inl hD⟩
        · rw [E.step_of_some hD, nfail_cons_some, anySucc_cons_some, not_or] at hω
          obtain ⟨hnf, hds, hns⟩ := hω
          by_cases hd : desig (E.hist n ω)
          · have hsc : ¬succ (E.hist n ω) (D.read ω) := fun h' => hds ⟨hd, h'⟩
            rw [if_pos ⟨hd, hsc⟩] at hnf
            have hj : j ≠ 0 := by omega
            refine Or.inr ?_
            rw [if_neg hj]
            exact ⟨hA, ⟨⟨by omega, hns⟩, hd⟩, D, hD, hsc⟩
          · rw [if_neg (fun h' => hd h'.1)] at hnf
            exact Or.inl ⟨hA, ⟨by omega, hns⟩, Or.inr hd⟩
      refine (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans ?_)
      split_ifs <;> simp
    -- the top level set at time `n` is empty
    have hUtop : μ.real (U (n + 1)) = 0 := by
      have : U (n + 1) = ∅ := by
        ext ω
        simp only [hU, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro _ hω
        have := nfail_le_length (succ := succ) (desig := desig) (E.hist n ω)
        rw [length_hist] at this
        omega
      rw [this, measureReal_empty]
    -- the computation
    calc ∑ j ∈ Finset.range (n + 1 + 1), c ^ j * μ.real (A₀ ∩ E.levelSet succ desig (n + 1) j)
        ≤ ∑ j ∈ Finset.range (n + 1 + 1), c ^ j * (μ.real (U j) + if j = 0 then 0 else μ.real (F (j - 1))) :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hstep j) (pow_nonneg hc0 j)
      _ = ∑ j ∈ Finset.range (n + 1 + 1), c ^ j * μ.real (U j) +
            ∑ j ∈ Finset.range (n + 1 + 1), c ^ j * (if j = 0 then 0 else μ.real (F (j - 1))) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun j _ => by ring
      _ = (∑ j ∈ Finset.range (n + 1), c ^ j * μ.real (U j) + c ^ (n + 1) * μ.real (U (n + 1))) +
            ∑ j ∈ Finset.range (n + 1), c ^ (j + 1) * μ.real (F j) := by
          have hsumF : ∑ j ∈ Finset.range (n + 1 + 1), c ^ j * (if j = 0 then 0 else μ.real (F (j - 1))) =
              ∑ j ∈ Finset.range (n + 1), c ^ (j + 1) * μ.real (F j) := by
            rw [Finset.sum_range_succ']
            simp
          rw [Finset.sum_range_succ, hsumF]
      _ ≤ ∑ j ∈ Finset.range (n + 1), c ^ j * μ.real (U j) +
            ∑ j ∈ Finset.range (n + 1), c ^ (j + 1) * ((1 - q) * μ.real (Gd j)) := by
          rw [hUtop, mul_zero, add_zero]
          exact add_le_add le_rfl (Finset.sum_le_sum fun j _ =>
            mul_le_mul_of_nonneg_left (hFG j) (pow_nonneg hc0 _))
      _ = ∑ j ∈ Finset.range (n + 1), c ^ j * μ.real (A₀ ∩ E.levelSet succ desig n j) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← hUG j, pow_succ]
          calc c ^ j * μ.real (U j) + c ^ j * c * ((1 - q) * μ.real (Gd j))
              = c ^ j * μ.real (U j) + c ^ j * (c * (1 - q)) * μ.real (Gd j) := by ring
            _ = _ := by rw [hcq]; ring
      _ ≤ μ.real A₀ := ih

/-- **Peierls input for adaptive processes.** If every designated probe fails with probability
at most `1 - q` (`q < 1`), then for all `n, k`:
`P_p(A₀ ∩ {at time n: at least k designated probes failed and none succeeded}) ≤ (1-q)ᵏ P_p(A₀)`
(Grimmett 1999, p. 176: "each new step of this process results in an occupied vertex with
conditional probability at least `π^{125}` … this holds just as in Lemma (7.24)").
[cite: GrimmettPercolation1999, §7.3 p. 176, §7.2 Lemma (7.24)] -/
theorem measureReal_inter_le_nfail_le (hE : E.Fresh U₀) (hA : DeterminedBy A₀ U₀) (hAm : MeasurableSet A₀)
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hfail : ∀ h D, E.next h = some D → desig h → (bondPercolation G p).real {ω | ¬succ h (D.read ω)} ≤ 1 - q)
    (n k : ℕ) :
    (bondPercolation G p).real (A₀ ∩ {ω | k ≤ nfail succ desig (E.hist n ω) ∧ ¬AnySucc succ desig (E.hist n ω)})
      ≤ (1 - q) ^ k * (bondPercolation G p).real A₀ := by
  set μ := bondPercolation G p with hμ
  set c : ℝ := (1 - q)⁻¹ with hc
  have hq' : 0 < 1 - q := by linarith
  have hc1 : 1 ≤ c := (one_le_inv₀ hq').2 (by linarith)
  have hc0 : 0 ≤ c := zero_le_one.trans hc1
  have hcq : (1 - q) * c = 1 := mul_inv_cancel₀ hq'.ne'
  set T := (Finset.range (n + 1)).filter (k ≤ ·) with hT
  have hsub : A₀ ∩ {ω | k ≤ nfail succ desig (E.hist n ω) ∧ ¬AnySucc succ desig (E.hist n ω)} ⊆
      ⋃ j ∈ T, A₀ ∩ E.levelSet succ desig n j := by
    rintro ω ⟨hA, hk, hns⟩
    simp only [hT, Set.mem_iUnion, Finset.mem_filter, Finset.mem_range, exists_prop]
    refine ⟨nfail succ desig (E.hist n ω), ⟨?_, hk⟩, hA, rfl, hns⟩
    have := nfail_le_length (succ := succ) (desig := desig) (E.hist n ω)
    rw [length_hist] at this
    omega
  have hweight : ∀ j ∈ T, μ.real (A₀ ∩ E.levelSet succ desig n j) ≤
      (1 - q) ^ k * (c ^ j * μ.real (A₀ ∩ E.levelSet succ desig n j)) := by
    intro j hj
    have hkj : k ≤ j := (Finset.mem_filter.1 hj).2
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hkj
    have h1 : 1 ≤ (1 - q) ^ k * c ^ (k + i) := by
      rw [pow_add, ← mul_assoc, ← mul_pow, hcq, one_pow, one_mul]
      exact one_le_pow₀ hc1
    calc μ.real (A₀ ∩ E.levelSet succ desig n (k + i)) = 1 * μ.real (A₀ ∩ E.levelSet succ desig n (k + i)) :=
          (one_mul _).symm
      _ ≤ ((1 - q) ^ k * c ^ (k + i)) * μ.real (A₀ ∩ E.levelSet succ desig n (k + i)) :=
          mul_le_mul_of_nonneg_right h1 measureReal_nonneg
      _ = _ := by ring
  calc μ.real (A₀ ∩ {ω | k ≤ nfail succ desig (E.hist n ω) ∧ ¬AnySucc succ desig (E.hist n ω)})
      ≤ μ.real (⋃ j ∈ T, A₀ ∩ E.levelSet succ desig n j) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ j ∈ T, μ.real (A₀ ∩ E.levelSet succ desig n j) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ j ∈ T, (1 - q) ^ k * (c ^ j * μ.real (A₀ ∩ E.levelSet succ desig n j)) := Finset.sum_le_sum hweight
    _ = (1 - q) ^ k * ∑ j ∈ T, c ^ j * μ.real (A₀ ∩ E.levelSet succ desig n j) := by rw [Finset.mul_sum]
    _ ≤ (1 - q) ^ k * ∑ j ∈ Finset.range (n + 1), c ^ j * μ.real (A₀ ∩ E.levelSet succ desig n j) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun j _ _ => mul_nonneg (pow_nonneg hc0 j) measureReal_nonneg) (pow_nonneg hq'.le k)
    _ ≤ (1 - q) ^ k * μ.real A₀ :=
        mul_le_mul_of_nonneg_left (E.sum_pow_mul_measureReal_levelSet_le G p succ desig hE hA hAm hq1 hfail n)
          (pow_nonneg hq'.le k)

end Designated

end Measure

end AExplorer

end Percolation.Literature
