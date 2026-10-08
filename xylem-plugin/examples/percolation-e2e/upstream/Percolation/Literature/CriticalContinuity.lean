import Percolation.Literature.Basic
import Percolation.Literature.BernoulliPercolation
import Percolation.Literature.LatticeModels.LatticeGraph
import Percolation.Util.Linter

/-!
# Continuity of the percolation probability at criticality (`θ(p_c) = 0`)

The statement `θ(p_c) = 0` for Bernoulli **bond** percolation on the nearest-neighbour hypercubic
lattice `ℤ^d`, and its case `d = 3`.  The model is that of `Literature/Basic.lean`: the lattice `zdGraph d`
(vertices `Fin d → ℤ`, nearest-neighbour edges), the measure `bondPercolation (zdGraph d) p` (each edge
open with probability `p`, independently), the percolation probability
`theta (zdGraph d) 0 p = P_p(|C(0)| = ∞)` and the critical probability
`criticalProb (zdGraph d) 0 = inf {p ∈ [0,1] | θ(p) > 0}`.  This file defines

* `criticalProbI d : unitInterval` — `p_c(ℤ^d)` as a point of `[0, 1]` (`criticalProb_mem_Icc`), so
  that it can be fed to `theta`;
* `PercolationContinuity d` — the statement `θ(p_c(ℤ^d)) = 0` ("no infinite cluster at criticality";
  equivalently, continuity of `p ↦ θ(p)` on `[0,1]`, since `θ` is continuous on `[0, p_c)` and, by the
  theorem of van den Berg and Keane (1984), on `(p_c, 1]`);
* `PercolationContinuityZ3 := PercolationContinuity 3` — the case `d = 3`;

Status.  In print (Fitzner–van der Hofstad 2017, §1.1) `θ(p_c) = 0` is known for `d = 2` (Harris
1960, Kesten 1980) and for `d ≥ 11` (lace expansion: Hara–Slade 1990/1994 for `d ≥ 19`,
Fitzner–van der Hofstad 2017 for `d ≥ 11`); the cases `3 ≤ d ≤ 10` were open — "arguably the holy
grail of percolation theory".  In this development `PercolationContinuity d` is proved for every
`d ≥ 2`: `CSH.percolationContinuity_allDimensions` (and `CSH.percolationContinuity_three` for
`d = 3`), from Kozma–Nitzan's Conjecture 3 — itself derived there from a new hierarchy of conditioned
covariance inequalities on finite weighted graphs — combined with Kozma–Nitzan's Theorem 6
(`KozmaNitzan2024_thm6_holds`).  Those theorems live downstream of this file, which only states the
`Prop`; nothing here asserts it.

Design: everything is stated over the existing definitions (`theta`, `criticalProb`, `zdGraph`,
`unitInterval` parameters, `Measure.real` probabilities); no new model definitions are needed.
Mathlib has no percolation material beyond `ProbabilityTheory.setBernoulli`.

## References

* R. Fitzner, R. van der Hofstad, *Mean-field behavior for nearest-neighbor percolation in
  `d > 10`*, Electron. J. Probab. 22 (2017), no. 43, 1–65: §1.1 ((1.5)–(1.6), the discussion
  "continuity of `p ↦ θ(p)` … is equivalent to the statement that `θ(p_c(d)) = 0`"), Thm. 1.1,
  Cor. 1.3.
* T. Hara, G. Slade, *Mean-field critical behaviour for percolation in high dimensions*, Comm.
  Math. Phys. 128 (1990), 333–391.
* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §1.4 (Theorem: `0 < p_c(d) < 1` for
  `d ≥ 2`; `θ`, `p_c`), §8.3.
* T. E. Harris, Proc. Cambridge Philos. Soc. 56 (1960), 13–20; H. Kesten, Comm. Math. Phys. 74
  (1980), 41–59 (`d = 2`).
* J. van den Berg, M. Keane, *On the continuity of the percolation probability function*, Contemp.
  Math. 26 (1984), 61–65 (`θ` is continuous on `(p_c, 1]`; Grimmett 1999, §8.3).
-/

noncomputable section

namespace Percolation.Literature

open MeasureTheory LatticeModels

/-! ### `p_c` as a point of `[0, 1]` and the continuity statement -/

/-- The critical probability `p_c(ℤ^d)` of bond percolation on `ℤ^d` (at the origin), as an
element of `unitInterval` (it lies in `[0, 1]` by `criticalProb_mem_Icc`), so that it can be fed
to `theta`. [cite: GrimmettPercolation1999, §1.4] -/
def criticalProbI (d : ℕ) : unitInterval :=
  ⟨criticalProb (zdGraph d) (0 : Site d), criticalProb_mem_Icc _ _⟩

/-- `criticalProbI` unfolds to `criticalProb`. [folklore] -/
@[simp] theorem coe_criticalProbI (d : ℕ) :
    (criticalProbI d : ℝ) = criticalProb (zdGraph d) (0 : Site d) := rfl

/-- **Continuity of the percolation probability at `p_c` on `ℤ^d`**: `θ(p_c(ℤ^d)) = 0`, i.e.
at the critical parameter the origin is almost surely in a finite open cluster (Bernoulli bond
percolation on the nearest-neighbour lattice `zdGraph d`; `θ = theta (zdGraph d) 0`, the probability
that the open cluster of the origin is infinite; `p_c = criticalProbI d = inf {p ∈ [0,1] | θ(p) > 0}`).
Since `θ` is continuous on `[0, p_c)` and on `(p_c, 1]` (van den Berg–Keane 1984), this is equivalent
to continuity of `p ↦ θ(p)` on `[0, 1]`.  Known for `d = 2` (Harris 1960, Kesten 1980) and for `d ≥ 11` (lace
expansion) before this work; proved for all `d ≥ 2` in `CSH.percolationContinuity_allDimensions`
(Kozma–Nitzan's Conjecture 3, obtained there from the conditioned slack hierarchy, combined with
Kozma–Nitzan's Theorem 6 `KozmaNitzan2024_thm6_holds`), downstream of this file.  This `def` only
states the proposition; the cases `3 ≤ d ≤ 10` had been open.
[cite: FitznerVanDerHofstad2017, §1.1 (discussion of (1.5)–(1.6))] -/
def PercolationContinuity (d : ℕ) : Prop :=
  theta (zdGraph d) (0 : Site d) (criticalProbI d) = 0

/-- **`θ(p_c) = 0` on `ℤ³`**: for Bernoulli bond percolation on the nearest-neighbour cubic lattice
`ℤ³`, the percolation probability vanishes at the critical point,
`θ(p_c(ℤ³)) = P_{p_c}(|C(0)| = ∞) = 0`.  The case `d = 3` of `PercolationContinuity` (by definition
`PercolationContinuity 3`), which was open in print together with all of `3 ≤ d ≤ 10` ("arguably the
holy grail of percolation theory", Fitzner–van der Hofstad 2017, §1.1) and is proved in this development
as `CSH.percolationContinuity_three`, the instance `d = 3` of `CSH.percolationContinuity_allDimensions`
(downstream of this file).  This `def` only states the proposition.
[cite: FitznerVanDerHofstad2017, §1.1 (discussion of (1.5)–(1.6))] -/
def PercolationContinuityZ3 : Prop :=
  PercolationContinuity 3

/-! ### Related statements: `0 < p_c < 1`, the high-dimensional case, the planar case -/

/-- **The planar case** `d = 2`: Kesten's theorem `p_c(ℤ²) = 1/2` (`kesten_criticalProb_Z2`) and
Harris' theorem `θ(1/2) = 0` (`harris_theta_half`), both stated in `BernoulliPercolation.lean` and
proved in this library (`kesten_criticalProb_Z2_holds`, `harris_theta_half_holds`), give
`PercolationContinuity 2`. [cite: GrimmettPercolation1999, §1.4 and §11] -/
theorem percolationContinuity_two (hK : kesten_criticalProb_Z2) (hH : harris_theta_half) :
    PercolationContinuity 2 := by
  have hK' : criticalProb (zdGraph 2) 0 = 1 / 2 := hK
  have : criticalProbI 2 = half := Subtype.ext (by simp [criticalProbI, half, hK'])
  rw [PercolationContinuity, this]
  exact hH

end Percolation.Literature
