/-
Margin-CVaR wrapper — obligation E1, the margin/self-occlusion instantiation of the
SEALED Rockafellar–Uryasev inf-form (CvarInfForm.lean).

Ledger row E1 (ARCHIVED source, see PROVENANCE at the foot of this header) reads:
"**Probabilistic margin / self-occlusion** term composes with the CVaR scorer — **[NEW]**
(rides on A1) + **[WALL]** for the geometry", cheapest reduction "reuse A1". The task card
(also ARCHIVED) splits the row explicitly and scopes this file to the half that is a
theorem:

  ✅ IN SCOPE — the risk wrapper. Same CVaR algebra as A1 (sealed as `CvarInfForm`); E1
     RIDES it, instantiating the sealed inf-form with the margin loss.
  ⛔ NOT IN SCOPE — the margin / self-occlusion GEOMETRY. Which clearance or occlusion
     functional `m` measures is a scorer term validated IN THE PIPELINE, not a theorem.
     It is a dashed wall on the risk chart and it stays one. `m` is left fully abstract
     here — no formula, no regularity, no bound is assumed of it. The two halves are named
     separately and are never blurred into "E1 done".

Because every theorem in CvarInfForm is stated for an ARBITRARY sample `Z : Fin q → ℝ` with
no distinctness hypothesis, this is pure RE-INSTANTIATION — not re-proof — exactly as
`CvarStateCost.lean` re-instantiates the same engine at a state cost.

SIGN CONVENTION. `m : S → ℝ` is a MARGIN (clearance): larger is safer. CVaR is a tail
measure of a LOSS, so the induced loss is the negated margin, `marginLoss m x k = -m (x k)`.
Small margins are large losses and land in the tail the scorer constrains.

  E1.1 `cvarMargin_obj_convexOn`     — the SAA objective is convex in `τ`
                                       (from `cvarObj_convexOn`, RU-2000 Thm 1).
  E1.2 `cvarMargin_min_at_scenario`  — its minimizer over `τ ∈ ℝ` is attained at a
                                       scenario's margin loss `-m (x k)`
                                       (from `cvarObj_min_at_sample`, RU-2002 Prop. 8).
  E1.3 `cvarMargin_eq_obj_scenario`  — hence the defined margin CVaR equals the objective
                                       at that scenario (from `cvarSAA_eq_obj_sample`).

COMPOSITION (the word the ledger row actually uses). The three facts above transfer the
engine; they do not yet say the margin term COMPOSES with the scorer in a usable direction.
The composition content is monotonicity of the wrapper in its loss:

  E1.4 `cvarSAA_mono`                — `Z ≤ Z'` pointwise ⟹ `cvarSAA α Z ≤ cvarSAA α Z'`.
                                       MOVED to CvarInfForm (see below); still used here.
  E1.5 `cvarMargin_antitone`         — a uniformly LARGER margin gives a SMALLER risk. This
                                       is the direction a planner optimises in.
  E1.6 `cvarMargin_le_cvarMarginOcclusion` — a nonnegative self-occlusion penalty `o ≥ 0`
                                       composed into the loss only ever RAISES the risk.
  E1.7 `cvarMarginOcclusion_eq_obj_scenario` — the composite loss inherits E1.3.

SCOPE NOTE ON E1.4 (UPDATED). Monotonicity is also one of the four Artzner coherence axioms.
It was originally proved here only as the composition tool E1 needs, with the standalone
coherence bundle (ledger row A2) explicitly disclaimed. That bundle is now PROVED in
`CvarInfForm.lean` (`cvarSAA_mono`, `cvarSAA_translation`, `cvarSAA_posHomogeneous`,
`cvarSAA_subadditive`), and `cvarObj_mono`/`cvarSAA_mono` moved there with it. This module
imports the engine, so every use below resolves unchanged.

THE CHANCE-CONSTRAINT BRIDGE (new, and the reason the quartet now adds up to a planning
result). E1.1–E1.7 are all about the SHAPE of the objective. They do not say what a
particular optimized NUMBER buys. These do:

  E1.8 `cvarSAA_lt_imp_violation_count`     — `cvarSAA α Z < c` caps the number of scenarios
                                              exceeding `c` at `q(1−α)`.
  E1.9 `cvarMargin_lt_imp_clearance_count`  — hence `cvarMargin α m x < −δ` caps the number
                                              of scenarios with clearance below `δ`.

E1.9 is the theorem an inspection planner's guarantee would actually cite. It is a
DETERMINISTIC statement about the solved sample, not a distributional one: it reads a count
off the SAA value instead of estimating a quantile, so it does not touch the DKW /
quantile-concentration wall recorded on the risk chart. Lifting the sampled count to a
population probability remains a separate open obligation and is NOT claimed here.

ATOM-SAFETY (obligation A5, carried into E1). `marginLoss m x` is an arbitrary `Fin q → ℝ` —
two scenarios may share a margin (an occlusion plateau, or a batch of scenarios all pinned at
a contact threshold). The sealed theorems assume no ties, so the atom case is handled BY
CONSTRUCTION, exactly as in `CvarStateCost`.

E1.1–E1.3 and E1.7 are direct applications of a sealed CvarInfForm theorem. E1.8 is the only
theorem in this file with real proof content: a contrapositive with a case split on `τ ≤ c`
and a `Finset.sum` lower bound restricted to the violating scenarios. Definitions verbatim
from CvarInfForm; no new axioms, no `sorry`.

PROVENANCE — every path below was resolved against the live tree before it was written here.

* Sealed engine: `Ctrllib/CvarInfForm.lean` (LIVE) · sibling instantiation:
  `Ctrllib/CvarStateCost.lean` (LIVE).
* Ledger row E1, obligations doc — ARCHIVED, no live copy:
  the corresponding archived source (not bundled)
  the corresponding local note
  (NOTE: under `risk_aware_planning/`, not `ctrllib/`; the old relative citation
  the corresponding local note pointed at nothing resolvable.)
* Task card — ARCHIVED, no live copy:
  the corresponding archived source (not bundled)
  the corresponding local note
* SymPy pin for the sealed engine, `the corresponding private check` — ARCHIVED, NOT mirrored into the live
  proof evidence directory:
  the corresponding archived source (not bundled)
  the corresponding local note
  It covers the CVaR algebra E1.1–E1.7 reuse unchanged. It does NOT cover E1.8/E1.9, which
  add new arithmetic; those have their own pin, `the corresponding private check` (see below).
* Numeric pin for E1.8/E1.9 and the A2 bundle: `pins/the corresponding private check` in this
  repository. HOUSE-DISCIPLINE FLAG: the house location for pins is the proof evidence directory
  above, which is read-only to the agent that wrote this. The pin is filed here for review
  and should be mirrored there by the chair.
* Human derivation page: wiki dir the corresponding derivation record (not bundled)
  — no the corresponding local note page filed yet, and this module has no catalog row.
-/
import Ctrllib.CvarInfForm

open scoped BigOperators

namespace Ctrllib

variable {q : ℕ} {S : Type*}

/-! ### The margin loss and its CVaR wrapper -/

/-- The **margin loss sample**: the negated margin `m` evaluated at each of the `q` scenario
states `x k`. `m` is a clearance — larger is safer — so the loss the tail measure sees is
`-m`. This is the Phase-E loss `Z`, identical in role to the Phase-A view score and the
Phase-B state cost, differing only in what is measured. Left fully general in `m` and `S`:
the margin / self-occlusion geometry is a pipeline concern, not a theorem (task card,
"NOT in scope"). -/
def marginLoss (m : S → ℝ) (x : Fin q → S) : Fin q → ℝ := fun k => -m (x k)

/-- **Margin CVaR**: the Rockafellar–Uryasev inf-form of `CvarInfForm` instantiated at the
margin loss. This is the risk functional the margin/self-occlusion scorer is composed with
(obligation E1). -/
noncomputable def cvarMargin (α : ℝ) (m : S → ℝ) (x : Fin q → S) : ℝ :=
  cvarSAA α (marginLoss m x)

/-- The **composite margin/occlusion loss**: the margin loss raised by a self-occlusion
penalty `o`. Both `m` and `o` stay abstract — this file fixes only how the two terms enter
the loss (additively, `o` a penalty), never what they measure. -/
def marginOcclusionLoss (m o : S → ℝ) (x : Fin q → S) : Fin q → ℝ :=
  fun k => -m (x k) + o (x k)

/-- **Composite margin/occlusion CVaR**: the same sealed inf-form at the composite loss. -/
noncomputable def cvarMarginOcclusion (α : ℝ) (m o : S → ℝ) (x : Fin q → S) : ℝ :=
  cvarSAA α (marginOcclusionLoss m o x)

/-! ### E1.1–E1.3 — the sealed engine, re-instantiated -/

/-- **E1.1 — convexity of the margin SAA objective** (`cvarMargin_obj_convexOn`). Direct
instantiation of `cvarObj_convexOn` at `Z := marginLoss m x`: the objective is convex in the
auxiliary variable `τ`, so the sampled margin-CVaR constraint is a convex program (the LP
reduction). -/
theorem cvarMargin_obj_convexOn (α : ℝ) (m : S → ℝ) (x : Fin q → S)
    (hq : 0 < q) (hα : α < 1) :
    ConvexOn ℝ Set.univ (cvarObj α (marginLoss m x)) :=
  cvarObj_convexOn α (marginLoss m x) hq hα

/-- **E1.2 — the minimizer is a scenario's margin loss** (`cvarMargin_min_at_scenario`).
Direct instantiation of `cvarObj_min_at_sample`: the global minimum over `τ ∈ ℝ` is attained
at `-m (x k)`, the margin loss of one scenario (the VaR breakpoint). Atom-safe — no
distinctness hypothesis on the scenarios. -/
theorem cvarMargin_min_at_scenario (α : ℝ) (m : S → ℝ) (x : Fin q → S)
    (hq : 0 < q) (hα0 : 0 ≤ α) (hα : α < 1) :
    ∃ k, ∀ τ, cvarObj α (marginLoss m x) (-m (x k)) ≤ cvarObj α (marginLoss m x) τ :=
  cvarObj_min_at_sample α (marginLoss m x) hq hα0 hα

/-- **E1.3 — the margin CVaR is attained at a scenario** (`cvarMargin_eq_obj_scenario`).
Direct instantiation of `cvarSAA_eq_obj_sample`: the defined `cvarMargin α m x` equals the
objective evaluated at a scenario's margin loss `-m (x k)` — the RU-2002 Prop. 8 closed-form
shape, a finite computable value, not a continuum infimum. -/
theorem cvarMargin_eq_obj_scenario (α : ℝ) (m : S → ℝ) (x : Fin q → S)
    (hq : 0 < q) (hα0 : 0 ≤ α) (hα : α < 1) :
    ∃ k, cvarMargin α m x = cvarObj α (marginLoss m x) (-m (x k)) :=
  cvarSAA_eq_obj_sample α (marginLoss m x) hq hα0 hα

/-! ### E1.4–E1.7 — composition: the wrapper is monotone in the loss -/

/-! **E1.4 — the composition tool, now on the engine.** `cvarObj_mono` and `cvarSAA_mono`
were originally proved here as the monotonicity E1 needs. They are general facts about
`cvarSAA`, and monotonicity is one of the four Artzner coherence axioms, so both now live in
`CvarInfForm.lean` alongside the rest of the A2 bundle (`cvarSAA_translation`,
`cvarSAA_posHomogeneous`, `cvarSAA_subadditive`). Nothing downstream changes: this module
imports the engine, so `cvarSAA_mono` resolves exactly as before. -/

/-- **E1.5 — a larger margin is a smaller risk** (`cvarMargin_antitone`). If every scenario's
margin under `m` is at most its margin under `m'`, the margin CVaR under `m'` is at most that
under `m`. This is the direction a risk-aware planner optimises in, and it is what makes the
composition of a margin term with the CVaR scorer meaningful rather than merely typed. -/
theorem cvarMargin_antitone (α : ℝ) {m m' : S → ℝ} (x : Fin q → S)
    (hq : 0 < q) (hα0 : 0 ≤ α) (hα : α < 1) (hm : ∀ k, m (x k) ≤ m' (x k)) :
    cvarMargin α m' x ≤ cvarMargin α m x :=
  cvarSAA_mono α hq hα0 hα fun k => by
    simp only [marginLoss]; linarith [hm k]

/-- **E1.6 — a self-occlusion penalty only raises the risk**
(`cvarMargin_le_cvarMarginOcclusion`). Composing a nonnegative occlusion term `o` into the
loss gives a margin CVaR at least that of the bare margin. The GEOMETRY of `o` — what
self-occlusion actually costs — is the pipeline half of E1 and is not touched: only `o ≥ 0`
on the sampled scenarios is used. -/
theorem cvarMargin_le_cvarMarginOcclusion (α : ℝ) (m o : S → ℝ) (x : Fin q → S)
    (hq : 0 < q) (hα0 : 0 ≤ α) (hα : α < 1) (ho : ∀ k, 0 ≤ o (x k)) :
    cvarMargin α m x ≤ cvarMarginOcclusion α m o x :=
  cvarSAA_mono α hq hα0 hα fun k => by
    simp only [marginLoss, marginOcclusionLoss]; linarith [ho k]

/-- **E1.7 — the composite loss inherits attainment** (`cvarMarginOcclusion_eq_obj_scenario`).
The sealed `cvarSAA_eq_obj_sample` at `Z := marginOcclusionLoss m o x`: the composite
margin/occlusion CVaR is again the objective at one scenario's composite loss. Composition
does not leave the sealed engine. -/
theorem cvarMarginOcclusion_eq_obj_scenario (α : ℝ) (m o : S → ℝ) (x : Fin q → S)
    (hq : 0 < q) (hα0 : 0 ≤ α) (hα : α < 1) :
    ∃ k, cvarMarginOcclusion α m o x
        = cvarObj α (marginOcclusionLoss m o x) (-m (x k) + o (x k)) :=
  cvarSAA_eq_obj_sample α (marginOcclusionLoss m o x) hq hα0 hα

/-! ### E1.8–E1.9 — the chance-constraint bridge: what the optimized number BUYS

Everything above is about the SHAPE of the objective (convex, attained, monotone). None of
it says what a particular optimized VALUE means for safety. The two theorems below close
that gap: they convert the scalar an SAA planner minimises into a hard, deterministic CAP on
how many sampled scenarios may violate a threshold. No estimation, no concentration
inequality, no quantile — the count is read off the value.
-/

/-- **E1.8 — the SAA counting bound** (`cvarSAA_lt_imp_violation_count`). If the sampled CVaR
of a loss `Z` is strictly below a level `c`, then strictly fewer than `q(1−α)` of the `q`
scenarios can exceed `c`:

    `cvarSAA α Z < c  ⟹  |{k : c < Z k}| ≤ q(1−α)`.

Stated on the sealed engine, for an arbitrary sample `Z` — no distinctness hypothesis, so it
is atom-safe by construction like the rest of the file.

PROOF (contrapositive). Suppose `N := |{k : c < Z k}| > q(1−α)`, i.e. `β := N/(q(1−α)) > 1`.
Fix any `τ`.
* If `τ ≤ c`: keep only the violating scenarios in the sum. Each contributes
  `(Z k − τ)⁺ = Z k − τ ≥ c − τ ≥ 0`, so `cvarObj α Z τ ≥ τ + β(c − τ) = βc + (1−β)τ`, and
  because `1 − β < 0` with `τ ≤ c` this is `≥ βc + (1−β)c = c`.
* If `τ > c`: every summand is nonnegative, so `cvarObj α Z τ ≥ τ > c`.

So `c` bounds the objective below over all of `ℝ`, and `le_ciInf` lifts that to the infimum:
`c ≤ cvarSAA α Z`, contradicting the hypothesis. Note the argument never needs `BddBelow` as
a side condition — the uniform bound it constructs IS the boundedness witness.

HYPOTHESIS NOTE. `_hα0 : 0 ≤ α` is carried for signature uniformity with the rest of the
CVaR family but is NOT used: only `α < 1` (so the weight `1/(q(1−α))` is positive) and
`0 < q` are needed. The underscore records that honestly rather than implying a dependence
the proof does not have. -/
theorem cvarSAA_lt_imp_violation_count (α : ℝ) (Z : Fin q → ℝ) {c : ℝ}
    (hq : 0 < q) (_hα0 : 0 ≤ α) (hα : α < 1) (hlt : cvarSAA α Z < c) :
    ((Finset.univ.filter (fun k => c < Z k)).card : ℝ) ≤ (q : ℝ) * (1 - α) := by
  by_contra hcon₀
  have hcon := not_le.mp hcon₀
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have h1a : (0 : ℝ) < 1 - α := by linarith
  have hden : (0 : ℝ) < (q : ℝ) * (1 - α) := mul_pos hq' h1a
  have hw : (0 : ℝ) < 1 / ((q : ℝ) * (1 - α)) := div_pos one_pos hden
  set P : Finset (Fin q) := Finset.univ.filter (fun k => c < Z k) with hP
  -- `β := (1/(q(1−α))) · N` exceeds 1 exactly because the violation count exceeds `q(1−α)`
  have hβ : 1 < (1 / ((q : ℝ) * (1 - α))) * (P.card : ℝ) := by
    have h := (one_lt_div hden).mpr hcon
    calc (1 : ℝ) < (P.card : ℝ) / ((q : ℝ) * (1 - α)) := h
      _ = (1 / ((q : ℝ) * (1 - α))) * (P.card : ℝ) := by ring
  -- `c` is a uniform lower bound for the objective over all `τ`
  have key : ∀ τ, c ≤ cvarObj α Z τ := by
    intro τ
    rcases le_or_gt τ c with hτ | hτ
    · -- τ ≤ c: the violating scenarios alone already carry the sum past `c`
      have hviol : (P.card : ℝ) * (c - τ) ≤ ∑ k ∈ P, max (Z k - τ) 0 := by
        have h1 : ∑ _k ∈ P, (c - τ) ≤ ∑ k ∈ P, max (Z k - τ) 0 := by
          refine Finset.sum_le_sum (fun k hk => ?_)
          have hck : c < Z k := by
            have := (Finset.mem_filter.mp (hP ▸ hk)).2
            simpa using this
          exact le_trans (by linarith : c - τ ≤ Z k - τ) (le_max_left _ _)
        rwa [Finset.sum_const, nsmul_eq_mul] at h1
      have hrest : ∑ k ∈ P, max (Z k - τ) 0 ≤ ∑ k, max (Z k - τ) 0 :=
        Finset.sum_le_sum_of_subset_of_nonneg (by rw [hP]; exact Finset.filter_subset _ _)
          (fun k _ _ => le_max_right _ _)
      have hsum : (P.card : ℝ) * (c - τ) ≤ ∑ k, max (Z k - τ) 0 := le_trans hviol hrest
      have hscaled := mul_le_mul_of_nonneg_left hsum (le_of_lt hw)
      have hprod : (0 : ℝ) ≤ ((1 / ((q : ℝ) * (1 - α))) * (P.card : ℝ) - 1) * (c - τ) :=
        mul_nonneg (by linarith) (by linarith)
      simp only [cvarObj]
      nlinarith [hscaled, hprod]
    · -- τ > c: every summand is nonnegative, so the objective is already above `τ`
      have hsum0 : (0 : ℝ) ≤ ∑ k, max (Z k - τ) 0 :=
        Finset.sum_nonneg (fun k _ => le_max_right _ _)
      have := mul_nonneg (le_of_lt hw) hsum0
      simp only [cvarObj]
      linarith
  have hge : c ≤ cvarSAA α Z := le_ciInf key
  linarith

/-- **E1.9 — the clearance guarantee a planner actually cites**
(`cvarMargin_lt_imp_clearance_count`). If the optimizer drives the margin CVaR below `−δ`,
then at most `q(1−α)` of the `q` sampled scenarios have clearance smaller than `δ`:

    `cvarMargin α m x < −δ  ⟹  |{k : m (x k) < δ}| ≤ q(1−α)`.

This is E1.8 at `Z := marginLoss m x` and `c := −δ`, using the sign convention of this file
(`marginLoss = −m`, so "loss above `−δ`" is exactly "clearance below `δ`").

WHAT IT IS AND IS NOT. It is a deterministic statement about the SAMPLE the planner solved
on: the scalar it minimised certifies a count, with no distributional assumption and no
appeal to quantile concentration. It is NOT a statement about the underlying distribution —
lifting the sampled count to a population probability is a separate (and still open)
obligation, and nothing here should be read as supplying it. The margin geometry `m` remains
fully abstract, per the file's standing scope note. -/
theorem cvarMargin_lt_imp_clearance_count (α : ℝ) (m : S → ℝ) (x : Fin q → S) {δ : ℝ}
    (hq : 0 < q) (hα0 : 0 ≤ α) (hα : α < 1) (hlt : cvarMargin α m x < -δ) :
    ((Finset.univ.filter (fun k => m (x k) < δ)).card : ℝ) ≤ (q : ℝ) * (1 - α) := by
  have hlt' : cvarSAA α (marginLoss m x) < -δ := hlt
  have h := cvarSAA_lt_imp_violation_count α (marginLoss m x) hq hα0 hα hlt'
  have hset : (Finset.univ.filter (fun k => -δ < marginLoss m x k))
            = (Finset.univ.filter (fun k => m (x k) < δ)) := by
    ext k
    simp [marginLoss]
  rwa [hset] at h

end Ctrllib

#print axioms Ctrllib.cvarMargin_obj_convexOn
#print axioms Ctrllib.cvarMargin_min_at_scenario
#print axioms Ctrllib.cvarMargin_eq_obj_scenario
#print axioms Ctrllib.cvarMargin_antitone
#print axioms Ctrllib.cvarMargin_le_cvarMarginOcclusion
#print axioms Ctrllib.cvarMarginOcclusion_eq_obj_scenario
#print axioms Ctrllib.cvarSAA_lt_imp_violation_count
#print axioms Ctrllib.cvarMargin_lt_imp_clearance_count
