/-
State-cost CVaR — obligation B3, the state-cost instantiation of the SEALED
Rockafellar–Uryasev inf-form (CvarInfForm.lean).

The risk-aware GUIDANCE layer (the corresponding local note row B3) applies the
same CVaR tail measure to a STATE cost instead of the Phase-A view score: the risk
functional is identical, only the loss `Z` changes. Because every theorem in
CvarInfForm is stated for an ARBITRARY sample `Z : Fin q → ℝ` with no distinctness
hypothesis, this is pure RE-INSTANTIATION — not re-proof.

Given a state-cost function `J : S → ℝthe corresponding local noteq` scenario states
`x : Fin q → S`, the loss sample is `stateLoss J x = fun k => J (x k)`. Instantiating
the sealed CvarInfForm theorems with `Z := stateLoss J x` transfers all three
structural facts a risk-aware planner consumes:

  B3.1 `cvarState_obj_convexOn`    — the SAA objective is convex in `τ`
                                     (from `cvarObj_convexOn`, RU-2000 Thm 1).
  B3.2 `cvarState_min_at_scenario` — its minimizer over `τ ∈ ℝ` is attained at a
                                     scenario's state cost `J (x k)`
                                     (from `cvarObj_min_at_sample`, RU-2002 Prop. 8).
  B3.3 `cvarState_eq_obj_scenario` — hence the defined state-cost CVaR equals the
                                     objective at that scenario
                                     (from `cvarSAA_eq_obj_sample`).

ATOM-SAFETY (obligation A5, carried into B3). `stateLoss J x` is an arbitrary
`Fin q → ℝ` — two scenarios may share a state cost (a probability mass, e.g. at a
saturated / constraint-violation cost). The sealed theorems assume no ties, so the
atom case is handled BY CONSTRUCTION: the inf-form never forms the ambiguous
conditional expectation that a naive tail average would. Nothing in that argument
depends on the loss being a view score, so it transfers verbatim to the state cost.

No new mathematics: every proof is a direct application of a sealed CvarInfForm
theorem. Definitions verbatim from CvarInfForm; no new axioms, no `sorry`. Numeric
behavior is identical to the sealed engine — the CVaR algebra is unchanged — so the
CvarInfForm SymPy pin (the corresponding private check) covers it; this module adds no arithmetic.

Human derivation + provenance: wiki dir the corresponding derivation record (not bundled)
(no the corresponding local note page filed yet).
Sealed engine: Ctrllib/CvarInfForm.lean (no the corresponding local note page filed yet).
-/
import Ctrllib.CvarInfForm

namespace Ctrllib

variable {q : ℕ} {S : Type*}

/-- The **state-cost loss sample**: the state cost `J` evaluated at each of the `q`
scenario states `x k`. This is the Phase-B loss `Z` — identical in role to the
Phase-A view score, differing only in what is measured. Left fully general in `J`
and `S`; the corpus fixes no state-cost formula. -/
def stateLoss (J : S → ℝ) (x : Fin q → S) : Fin q → ℝ := fun k => J (x k)

/-- **State-cost CVaR**: the Rockafellar–Uryasev inf-form of `CvarInfForm`
instantiated at the state-cost loss. This is the risk functional the risk-aware
guidance layer constrains (obligation B3). -/
noncomputable def cvarState (α : ℝ) (J : S → ℝ) (x : Fin q → S) : ℝ :=
  cvarSAA α (stateLoss J x)

/-- **B3.1 — convexity of the state-cost SAA objective** (`cvarState_obj_convexOn`).
Direct instantiation of `cvarObj_convexOn` at `Z := stateLoss J x`: the objective is
convex in the auxiliary variable `τ`, so the sampled state-cost CVaR constraint is a
convex program (the LP reduction). -/
theorem cvarState_obj_convexOn (α : ℝ) (J : S → ℝ) (x : Fin q → S)
    (hq : 0 < q) (hα : α < 1) :
    ConvexOn ℝ Set.univ (cvarObj α (stateLoss J x)) :=
  cvarObj_convexOn α (stateLoss J x) hq hα

/-- **B3.2 — the minimizer is a scenario's state cost** (`cvarState_min_at_scenario`).
Direct instantiation of `cvarObj_min_at_sample`: the global minimum over `τ ∈ ℝ` is
attained at `J (x k)`, the state cost of one scenario (the VaR breakpoint). Atom-safe
— no distinctness hypothesis on the scenarios. -/
theorem cvarState_min_at_scenario (α : ℝ) (J : S → ℝ) (x : Fin q → S)
    (hq : 0 < q) (hα0 : 0 ≤ α) (hα : α < 1) :
    ∃ k, ∀ τ, cvarObj α (stateLoss J x) (J (x k)) ≤ cvarObj α (stateLoss J x) τ :=
  cvarObj_min_at_sample α (stateLoss J x) hq hα0 hα

/-- **B3.3 — the state-cost CVaR is attained at a scenario** (`cvarState_eq_obj_scenario`).
Direct instantiation of `cvarSAA_eq_obj_sample`: the defined `cvarState α J x` equals
the objective evaluated at a scenario's state cost `J (x k)` — the RU-2002 Prop. 8
closed-form shape, a finite computable value, not a continuum infimum. -/
theorem cvarState_eq_obj_scenario (α : ℝ) (J : S → ℝ) (x : Fin q → S)
    (hq : 0 < q) (hα0 : 0 ≤ α) (hα : α < 1) :
    ∃ k, cvarState α J x = cvarObj α (stateLoss J x) (J (x k)) :=
  cvarSAA_eq_obj_sample α (stateLoss J x) hq hα0 hα

end Ctrllib

#print axioms Ctrllib.cvarState_obj_convexOn
#print axioms Ctrllib.cvarState_min_at_scenario
#print axioms Ctrllib.cvarState_eq_obj_scenario
