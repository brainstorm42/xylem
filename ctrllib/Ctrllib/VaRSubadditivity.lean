/-
VaR fails subadditivity — the coherence counterexample (risk obligation A2).

Artzner, Delbaen, Eber & Heath, *Coherent Measures of Risk*, Math. Finance
9(3):203–228, 1999 (bibkey `artzner1999coherent`) axiomatize a COHERENT risk
measure by four axioms; Axiom S is **subadditivity** ρ(X+Y) ≤ ρ(X)+ρ(Y). The
paper proves Value-at-Risk (VaR) violates S (§3.3), which is why the thesis'
risk layer uses CVaR (coherent) rather than VaR. This module seals that
failure by a finite `decide` computation on Artzner's i.i.d. loss-pair example.

The example (the corresponding local note §3.2, carried in-corpus by dixit2023risk
Def. 1 / majumdar2017how; numbers pinned by
the corresponding local note): two INDEPENDENT identical
defaultable bonds, each a loss of 100 with probability 1/25 = 0.04 and 0 with
probability 24/25 = 0.96, at confidence α = 19/20 = 0.95. Each bond alone has
VaR 0; their independent sum has VaR 100 > 0 + 0 — pooling two independent
risks RAISED the measured risk (the "diversification penalty" that makes VaR
incoherent). CVaR, being coherent, cannot do this.

Honest scope: this is a CONCRETE counterexample on a finite discrete law, not
a theory of risk measures. It refutes the universal subadditivity of VaR; it
does not develop VaR/CVaR in general (Mathlib has neither — proof-obligations
row A2). Probabilities are exact integer counts over a common total, so every
comparison is ℤ/ℕ arithmetic the kernel reduces under `decide` (ℚ would stall
on irreducible `Rat.blt`; `native_decide` is barred — it adds `ofReduceBool`).

Human derivation: wiki dir the corresponding derivation record (not bundled)
(no the corresponding local note page filed yet). This file is the tracked build copy;
legacy prose mirrors were retired with the vault.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic.NormNum

namespace Ctrllib

/-- A finite loss law as a list of `(value, integer count)` atoms; the
probability of an atom is its `count / totalMass`. A **list (multiset), not a
`Finset`**: the independent convolution below creates coincident-value atoms
whose masses must ADD (a `Finset` of pairs would collapse them and lose mass).
Values are `ℤ` — a loss/net-worth may be signed (Artzner 1999). [obligation A2] -/
abbrev FinLaw := List (ℤ × ℕ)

/-- Total count of a law; the probability denominator. -/
def totalMass (d : FinLaw) : ℕ := (d.map Prod.snd).sum

/-- CDF numerator: the count mass at or below `z`, i.e. `totalMass · F(z)` where
`F(z) = P(value ≤ z)` is the (empirical) cumulative distribution function. -/
def cumMass (d : FinLaw) (z : ℤ) : ℕ :=
  ((d.filter (fun p => decide (p.1 ≤ z))).map Prod.snd).sum

/-- The chance-constraint test `F(z) ≥ αnum/αden`, cleared of division by exact
cross-multiplication: `cumMass · αden ≥ αnum · totalMass` (both denominators
positive). This is the `F(z) ≥ α` inside the VaR quantile. -/
def reachesLevel (αnum αden : ℕ) (d : FinLaw) (z : ℤ) : Bool :=
  decide (αnum * totalMass d ≤ cumMass d z * αden)

/-- **Value-at-Risk** at confidence `α = αnum/αden`: the lower quantile
`inf{ z : F(z) ≥ α }` (value_at_risk topic; Artzner 1999 §3 audits VaR). For a
finite law `F` is a right-continuous step function jumping only at support
atoms, so that infimum is attained at the least atom whose CDF reaches `α` —
which is what is computed here. The `[] => 0` branch is unreachable junk: for
`α ≤ 1` the top atom always has `F = 1 ≥ α`, so the crossing set is nonempty. -/
def VaR (αnum αden : ℕ) (d : FinLaw) : ℤ :=
  match (d.map Prod.fst).filter (fun z => reachesLevel αnum αden d z) with
  | []      => 0
  | z :: zs => zs.foldl (fun m x => if x ≤ m then x else m) z

/-- Law of `X + Y` for **independent** `X, Y`: the joint outcomes are the
product, values add, counts multiply (independence). Coincident sum-values stay
as separate atoms — their masses add in `cumMass`. This is the convolution
underlying Artzner 1999 §3.3's i.i.d. loss-pair counterexample. -/
def indepSumLaw (dx dy : FinLaw) : FinLaw :=
  dx.flatMap (fun a => dy.map (fun b => (a.1 + b.1, a.2 * b.2)))

/-- Artzner's defaultable bond: loss `100` with count `1`, loss `0` with count
`24` — i.e. default probability `1/25 = 0.04`. Pinned by `the corresponding private check`. -/
def bond : FinLaw := [(0, 24), (100, 1)]

/-- Each single bond has `VaR₀.₉₅ = 0`: `F(0) = 24/25 = 0.96 ≥ 0.95`. -/
theorem var_bond_eq_zero : VaR 19 20 bond = 0 := by decide

/-- The independent sum of the two bonds has `VaR₀.₉₅ = 100`: its law is
`0 @ 576/625`, `100 @ 48/625`, `200 @ 1/625`, so `F(0) = 0.9216 < 0.95` but
`F(100) = 0.9984 ≥ 0.95`. -/
theorem var_indepSum_eq_hundred : VaR 19 20 (indepSumLaw bond bond) = 100 := by decide

/-- **Obligation A2 — VaR fails subadditivity (concrete witness).** There exist
a confidence level and two loss laws whose sum-of-VaRs is strictly below the
VaR-of-the-(independent)-sum: `0 = VaR(X)+VaR(Y) < VaR(X+Y) = 100`. VaR
therefore violates Axiom S of Artzner 1999, so it is not coherent. -/
theorem var_subadditivity_fails :
    ∃ (αnum αden : ℕ) (X Y : FinLaw),
      VaR αnum αden X + VaR αnum αden Y < VaR αnum αden (indepSumLaw X Y) :=
  ⟨19, 20, bond, bond, by decide⟩

/-- The same failure as the negation of the universal subadditivity axiom:
VaR does **not** satisfy `VaR(X+Y) ≤ VaR(X) + VaR(Y)` for all laws. -/
theorem var_not_subadditive :
    ¬ ∀ (αnum αden : ℕ) (X Y : FinLaw),
        VaR αnum αden (indepSumLaw X Y) ≤ VaR αnum αden X + VaR αnum αden Y :=
  fun h => absurd (h 19 20 bond bond) (by decide)

end Ctrllib

#print axioms Ctrllib.var_bond_eq_zero
#print axioms Ctrllib.var_indepSum_eq_hundred
#print axioms Ctrllib.var_subadditivity_fails
#print axioms Ctrllib.var_not_subadditive
