import Percolation.Literature.TwoClusterGibbsCovariance
import Percolation.Util.Linter

/-!
# Marker dominance with an avoided set: definitions of the `T_A` functionals

The objects of the proof of the averaged inequality `T_A ≥ 0`, written for an avoided SET `X` in the
"same weights, deleted pairs" bookkeeping (sum level, `BHK2006.weight`): `delE w B φ = Σ_η weight(w)
η φ(η ∖ B)` (expectation in `G − B`), `cut X ω` (pairs meeting the open vertex cluster of `X`),
`avoidEv r T = {r ↮ T}`, and, with `K̄ = cut X ω`: `taC` (`c_K = Cov_{G−K̄}(g(C_s), 1{s↔y})`), `taN`
(`μ_{G−K̄}(s↮y)`), `taNW` (`μ_{G−K̄}(s↮y, y↔z)`), `taB = Σ_ω w 1_{s↮X} c`, `taA = Σ_ω w 1_{s↮X}
(taNW/taN) c`, `tab = μ(y↮s, y↮X)`, `taa = μ(y↮s, y↮X, y↔z)`, `taQ = taA·tab − taa·taB` (`= b·T_A`).
[cite: VandenbergHaggstromKahn2005, §1 pp. 3–5 (induced model on `G − Z`) — bookkeeping]
-/

noncomputable section

namespace Percolation.Continuity

open MeasureTheory Set Percolation.Literature.LatticeModels Percolation.Literature
open scoped Classical

variable {V : Type*}

namespace HullPort

open BHK2006 DecisionTree

section TA

variable [Fintype V]

/-- `E_w[φ(η ∖ B)]`: expectation of `φ` for percolation with the pairs of `B` deleted ("in `G − B`"). [folklore] -/
def delE (w : Sym2 V → ℝ) (B : Set (Sym2 V)) (φ : Set (Sym2 V) → ℝ) : ℝ := ∑ η, weight w η * φ (η \ B)

/-- The pairs meeting the open vertex cluster of the set `X` in `ω` (= `A_X(ω)` of `TwoClusterGibbsCovariance`,
`= barOf X (setCl ω X)`). [folklore] -/
def cut (X : Set V) (ω : Set (Sym2 V)) : Set (Sym2 V) := {e | ∃ v ∈ e, ∃ x ∈ X, (openGraph ω).Reachable x v}

/-- `{r ↮ T}`: the root `r` is joined to no vertex of `T`. [folklore] -/
def avoidEv (r : V) (T : Set V) : Set (Set (Sym2 V)) := {ω | ∀ t ∈ T, ¬ (openGraph ω).Reachable r t}

/-- `c(ω) = Cov_{G − cut_X(ω)}(g(C_s), 1{s ↔ y})` (`c_K` with `K = C_X(ω)`). [folklore] -/
def taC (w : Sym2 V → ℝ) (s y : V) (X : Set V) (g : Set (Sym2 V) → ℝ) (ω : Set (Sym2 V)) : ℝ :=
  delE w (cut X ω) (fun η => g (openEdgeCluster η s) * ind (openConn s y) η) -
    delE w (cut X ω) (fun η => g (openEdgeCluster η s)) * delE w (cut X ω) (ind (openConn s y))

/-- `μ_{G − cut_X(ω)}(s ↮ y)` (`P_K(N)`). [folklore] -/
def taN (w : Sym2 V → ℝ) (s y : V) (X : Set V) (ω : Set (Sym2 V)) : ℝ :=
  delE w (cut X ω) (ind (openConn s y : Set (BondConfig V))ᶜ)

/-- `μ_{G − cut_X(ω)}(s ↮ y, y ↔ z)` (`P_K(W ∩ N)`). [folklore] -/
def taNW (w : Sym2 V → ℝ) (s y z : V) (X : Set V) (ω : Set (Sym2 V)) : ℝ :=
  delE w (cut X ω) (ind ((openConn s y : Set (BondConfig V))ᶜ ∩ openConn y z))

/-- `B = Σ_K m(K) c_K = Σ_ω w(ω) 1{s ↮ X} c(ω)`. [folklore] -/
def taB (w : Sym2 V → ℝ) (s y : V) (X : Set V) (g : Set (Sym2 V) → ℝ) : ℝ :=
  ∑ ω, weight w ω * (ind (avoidEv s X) ω * taC w s y X g ω)

/-- `A = Σ_K m(K) P_K(W∩N) ψ_K = Σ_ω w(ω) 1{s ↮ X} (taNW/taN)(ω) c(ω)`. [folklore] -/
def taA (w : Sym2 V → ℝ) (s y z : V) (X : Set V) (g : Set (Sym2 V) → ℝ) : ℝ :=
  ∑ ω, weight w ω * (ind (avoidEv s X) ω * (taNW w s y z X ω / taN w s y X ω * taC w s y X g ω))

/-- `b = μ(y ↮ s, y ↮ X)`. [folklore] -/
def tab (w : Sym2 V → ℝ) (s y : V) (X : Set V) : ℝ := ∑ ω, weight w ω * ind (avoidEv y (insert s X)) ω

/-- `a = μ(y ↮ s, y ↮ X, y ↔ z)`. [folklore] -/
def taa (w : Sym2 V → ℝ) (s y z : V) (X : Set V) : ℝ :=
  ∑ ω, weight w ω * ind (avoidEv y (insert s X) ∩ openConn y z) ω

/-- `Q = A·b − a·B` (`= b · T_A`). [folklore] -/
def taQ (w : Sym2 V → ℝ) (s y z : V) (X : Set V) (g : Set (Sym2 V) → ℝ) : ℝ :=
  taA w s y z X g * tab w s y X - taa w s y z X * taB w s y X g

end TA

end HullPort

end Percolation.Continuity
