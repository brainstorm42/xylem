import Percolation.Literature.FiniteEnergy
import Percolation.Util.Linter

/-!
# Sequential fresh probing of a bond configuration: the probabilistic core of dynamic renormalization

In a *dynamic renormalization* (block construction) one
examines regions of space one after the other, the choice of the next region depending on what has
been seen so far, and one arranges that each new step succeed with conditional probability close to
`1`; see G. Grimmett, *Percolation*, 2nd ed. (1999), §7.2 (proof of Theorem (7.2), Lemmas (7.17),
(7.24)) and §7.3 (proof of Lemma (7.52), p. 171: "there is conditional probability strictly
exceeding `p_c^site` that an examined vertex is occupied"; (7.56): "each new step of this process
results in an occupied vertex with conditional probability at least `π^{125}`"), and §7.4 p. 176
("The events `E_R` have been defined in terms of the states of edges encountered earlier, and it is
in this sense that the process is 'dynamic'").

All statements are about `bondPercolation G p` (`BernoulliPercolation.lean`); events determined
by finitely many edges are measurable by `measurableSet_of_isLocalEvent_holds`.

## References

* G. Grimmett, *Percolation*, 2nd ed., Grundlehren 321, Springer 1999, §7.2 pp. 152–157
  (Lemmas (7.17), (7.24)), §7.3 pp. 169–176 (proof of Lemma (7.52)), §7.4 p. 176.
* D. J. Barsky, G. R. Grimmett, C. M. Newman, Dynamic renormalization and continuity of the
  percolation transition in orthants, in *Spatial Stochastic Processes*, Birkhäuser 1991,
  pp. 37–55 (the construction Grimmett refers to).
-/

noncomputable section

namespace Percolation.Literature

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

variable {V : Type*}

/-! ## Probe records and histories -/

/-- The record of one probe: its finite support and the open edges observed in it. [folklore] -/
abbrev ProbeRecord (V : Type*) := Finset (Sym2 V) × Finset (Sym2 V)

/-- A probing history, newest step first; a step is `none` when no probe was made at that time.
[folklore] -/
abbrev ProbeHistory (V : Type*) := List (Option (ProbeRecord V))

/-- The open edges of `ω` lying in the finite edge set `D` (what a probe of support `D` sees).
[cite: GrimmettPercolation1999, §7.4 p. 176] -/
def obs (ω : BondConfig V) (D : Finset (Sym2 V)) : Finset (Sym2 V) := D.filter (· ∈ ω)

/-- Membership in the observation. [folklore] -/
theorem mem_obs_iff {ω : BondConfig V} {D : Finset (Sym2 V)} {e : Sym2 V} :
    e ∈ obs ω D ↔ e ∈ D ∧ e ∈ ω := by
  simp [obs, Finset.mem_filter]

/-- The observation is `ω ∩ D`. [folklore] -/
theorem coe_obs (ω : BondConfig V) (D : Finset (Sym2 V)) : (↑(obs ω D) : Set (Sym2 V)) = ω ∩ ↑D := by
  ext e
  simp [mem_obs_iff, and_comm]

/-- The observation lies in the support. [folklore] -/
theorem obs_subset (ω : BondConfig V) (D : Finset (Sym2 V)) : obs ω D ⊆ D := fun _ he =>
  (mem_obs_iff.1 he).1

/-- Configurations agreeing on `D` are seen identically by a probe of support `D`. [folklore] -/
theorem obs_congr {ω ω' : BondConfig V} {D : Finset (Sym2 V)} (h : ∀ e ∈ D, (e ∈ ω ↔ e ∈ ω')) :
    obs ω D = obs ω' D := by
  ext e
  simp only [mem_obs_iff]
  exact ⟨fun ⟨hD, hω⟩ => ⟨hD, (h e hD).1 hω⟩, fun ⟨hD, hω⟩ => ⟨hD, (h e hD).2 hω⟩⟩

namespace ProbeHistory

/-- The union of the supports of the probes recorded in a history. [folklore] -/
def supp (h : ProbeHistory V) : Finset (Sym2 V) := (h.filterMap id).toFinset.biUnion Prod.fst

/-- Membership in the union of supports. [folklore] -/
theorem mem_supp_iff {h : ProbeHistory V} {e : Sym2 V} :
    e ∈ supp h ↔ ∃ r : ProbeRecord V, some r ∈ h ∧ e ∈ r.1 := by
  simp only [supp, Finset.mem_biUnion, List.mem_toFinset, List.mem_filterMap, id]
  constructor
  · rintro ⟨r, ⟨a, ha, rfl⟩, he⟩; exact ⟨r, ha, he⟩
  · rintro ⟨r, hr, he⟩; exact ⟨r, ⟨some r, hr, rfl⟩, he⟩

/-- The empty history has empty support. [folklore] -/
@[simp] theorem supp_nil : supp ([] : ProbeHistory V) = ∅ := by
  ext e; simp [mem_supp_iff]

/-- A `none` step adds no support. [folklore] -/
@[simp] theorem supp_cons_none (h : ProbeHistory V) : supp (none :: h) = supp h := by
  ext e; simp [mem_supp_iff]

/-- A probe adds its support. [folklore] -/
@[simp] theorem supp_cons_some (r : ProbeRecord V) (h : ProbeHistory V) :
    supp (some r :: h) = r.1 ∪ supp h := by
  ext e
  simp only [mem_supp_iff, List.mem_cons, Option.some.injEq, Finset.mem_union]
  constructor
  · rintro ⟨r', hr' | hr', he⟩
    · subst hr'; exact Or.inl he
    · exact Or.inr ⟨r', hr', he⟩
  · rintro (he | ⟨r', hr', he⟩)
    · exact ⟨r, Or.inl rfl, he⟩
    · exact ⟨r', Or.inr hr', he⟩

/-- Supports grow along the history. [folklore] -/
theorem supp_subset_cons (s : Option (ProbeRecord V)) (h : ProbeHistory V) : supp h ⊆ supp (s :: h) := by
  intro e he
  rw [mem_supp_iff] at he ⊢
  obtain ⟨r, hr, he⟩ := he
  exact ⟨r, List.mem_cons_of_mem _ hr, he⟩

/-! ### Scores of a history: successes and designated failures -/

section Scores

variable (succ : ProbeHistory V → Finset (Sym2 V) → Prop) (desig : ProbeHistory V → Prop)

/-- Every probe recorded in the history succeeded (`succ h o`: the probe made after history `h`
with observed open edges `o` counts as a success). [cite: GrimmettPercolation1999, §7.3 p. 172 (A)] -/
def AllSucc : ProbeHistory V → Prop
  | [] => True
  | none :: h => AllSucc h
  | some r :: h => succ h r.2 ∧ AllSucc h

/-- The number of *designated* probes of the history that failed (`desig h`: the probe made after
history `h` is designated). [cite: GrimmettPercolation1999, §7.2 p. 156 (Lemma 7.24)] -/
def nfail : ProbeHistory V → ℕ
  | [] => 0
  | none :: h => nfail h
  | some r :: h => nfail h + (if desig h ∧ ¬succ h r.2 then 1 else 0)

/-- Some designated probe of the history succeeded. [cite: GrimmettPercolation1999, §7.2 p. 156 (Lemma 7.24)] -/
def AnySucc : ProbeHistory V → Prop
  | [] => False
  | none :: h => AnySucc h
  | some r :: h => (desig h ∧ succ h r.2) ∨ AnySucc h

variable {succ desig}

/-- `AllSucc` of the empty history. [folklore] -/
@[simp] theorem allSucc_nil : AllSucc succ [] := trivial
/-- `AllSucc` is unchanged by a `none` step. [folklore] -/
@[simp] theorem allSucc_cons_none (h : ProbeHistory V) : AllSucc succ (none :: h) ↔ AllSucc succ h := Iff.rfl
/-- `AllSucc` after a probe. [folklore] -/
@[simp] theorem allSucc_cons_some (r : ProbeRecord V) (h : ProbeHistory V) :
    AllSucc succ (some r :: h) ↔ succ h r.2 ∧ AllSucc succ h := Iff.rfl
/-- `nfail` of the empty history. [folklore] -/
@[simp] theorem nfail_nil : nfail succ desig [] = 0 := rfl
/-- `nfail` is unchanged by a `none` step. [folklore] -/
@[simp] theorem nfail_cons_none (h : ProbeHistory V) : nfail succ desig (none :: h) = nfail succ desig h := rfl
/-- `nfail` after a probe. [folklore] -/
theorem nfail_cons_some (r : ProbeRecord V) (h : ProbeHistory V) :
    nfail succ desig (some r :: h) = nfail succ desig h + (if desig h ∧ ¬succ h r.2 then 1 else 0) := rfl
/-- `AnySucc` of the empty history. [folklore] -/
@[simp] theorem anySucc_nil : ¬AnySucc succ desig [] := fun h => h
/-- `AnySucc` is unchanged by a `none` step. [folklore] -/
@[simp] theorem anySucc_cons_none (h : ProbeHistory V) : AnySucc succ desig (none :: h) ↔ AnySucc succ desig h :=
  Iff.rfl
/-- `AnySucc` after a probe. [folklore] -/
@[simp] theorem anySucc_cons_some (r : ProbeRecord V) (h : ProbeHistory V) :
    AnySucc succ desig (some r :: h) ↔ (desig h ∧ succ h r.2) ∨ AnySucc succ desig h := Iff.rfl

/-- At most one designated failure per step. [folklore] -/
theorem nfail_le_length (h : ProbeHistory V) : nfail succ desig h ≤ h.length := by
  induction h with
  | nil => simp
  | cons s h ih =>
    cases s with
    | none => simp only [nfail_cons_none, List.length_cons]; omega
    | some r =>
      rw [nfail_cons_some, List.length_cons]
      split_ifs <;> omega

end Scores

end ProbeHistory

open ProbeHistory

/-! ## Explorers and their histories -/

namespace Explorer

/-! ## The product formula and the conditional step -/

section Measure

variable [Countable V] (G : SimpleGraph V) (p : unitInterval)

/-! ## Designated failures: the Peierls input for adaptive processes -/

section Designated

variable {U₀ : Set (Sym2 V)} {A₀ : Set (BondConfig V)}
  (succ : ProbeHistory V → Finset (Sym2 V) → Prop) (desig : ProbeHistory V → Prop)

end Designated

end Measure

end Explorer

end Percolation.Literature
