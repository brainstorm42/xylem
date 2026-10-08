import Percolation.Literature.Basic
import Percolation.Literature.LatticeModels.LatticeGraph
import Percolation.Util.Linter

/-!
# The two-point connectivity function of bond percolation on `ℤ^d` (Grimmett 1999, §8.3, §8.5)

Statements about the two-point function
`τ_p(x, y) = P_p(x ↔ y) = (bondPercolation (zdGraph d) p).real (openConn x y)` of
nearest-neighbour bond percolation on `ℤ^d`:

* `Grimmett1999_prob_exists_percolatesAt` — the zero–one law for the existence of an infinite
  open cluster (Grimmett 1999 §1.4, Thm (1.11), p. 14: `ψ(p) = P_p(∃` infinite open cluster`)`
  is `0` if `θ(p) = 0` and `1` if `θ(p) > 0`; Kolmogorov zero–one law + translation invariance).

All four are theorems in print for every `d` and every `p` (Thm (8.1) is stated for all `p`;
where `θ(p) = 0` the second is trivial). Their specialisations to `d = 3`, `x = 0` are recorded
at the end of the file.

## Sources

G. Grimmett, *Percolation*, 2nd ed., Springer 1999: Thm (1.11) §1.4 (zero–one law for
`ψ(p)`), Thm (8.1) p. 198 (uniqueness), §8.3
pp. 203–204 (continuity of `τ_p`), §8.5 p. 213 (`τ_p ≥ θ²`). M. Aizenman, H. Kesten,
C. M. Newman, Comm. Math. Phys. 111 (1987) 505–531; R. M. Burton, M. Keane, Comm. Math. Phys.
121 (1989) 501–505.

## Prerequisites

Mathlib has no percolation theory.
-/

noncomputable section

namespace Percolation.Literature

open MeasureTheory

/-- **Uniqueness of the infinite open cluster on `ℤ^d`** (Aizenman–Kesten–Newman 1987;
Burton–Keane 1989; Grimmett 1999, Thm (8.1): "If `p` is such that `θ(p) > 0`, there exists
almost surely exactly one infinite open cluster"; together with `θ(p) = 0 ⇒` a.s. none): for
every `d` and every `p ∈ [0, 1]`, `P_p`-almost surely the number of infinite open clusters of
nearest-neighbour bond percolation on `ℤ^d` is at most one. [cite: GrimmettPercolation1999, Thm (8.1)] -/
def Grimmett1999_numInfiniteClusters_le_one : Prop :=
  ∀ (d : ℕ) (p : unitInterval),
    ∀ᵐ ω ∂(bondPercolation (LatticeModels.zdGraph d) p), numInfiniteClusters ω ≤ 1

/-- **Zero–one law for the existence of an infinite open cluster** (Grimmett 1999, §1.4,
Thm (1.11): "The probability `ψ(p)` that there exists an infinite open cluster satisfies
`ψ(p) = 0` if `θ(p) = 0`, `ψ(p) = 1` if `θ(p) > 0`"; proof pp. 19–20: `{∃` infinite cluster`}` is a
tail event of the independent edge variables, so `ψ ∈ {0, 1}` by Kolmogorov's zero–one law;
`ψ(p) ≥ θ(p) > 0` forces `1`, and `ψ(p) ≤ Σ_x θ_x(p) = 0` by translation invariance forces `0`).
For nearest-neighbour bond percolation on `ℤ^d`, every `d` and every `p ∈ [0, 1]`.
[cite: GrimmettPercolation1999, §1.4 Thm (1.11)] -/
def Grimmett1999_prob_exists_percolatesAt : Prop :=
  ∀ (d : ℕ) (p : unitInterval),
    (theta (LatticeModels.zdGraph d) (0 : LatticeModels.Site d) p = 0 →
      (bondPercolation (LatticeModels.zdGraph d) p).real {ω | ∃ x : LatticeModels.Site d, ω ∈ percolatesAt x} = 0) ∧
    (0 < theta (LatticeModels.zdGraph d) (0 : LatticeModels.Site d) p →
      (bondPercolation (LatticeModels.zdGraph d) p).real {ω | ∃ x : LatticeModels.Site d, ω ∈ percolatesAt x} = 1)

end Percolation.Literature
