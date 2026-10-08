import Mathlib
import Percolation.Continuity.MainTheorem

/-!
# Proved solution

Same declarations as `Challenge.lean` — the definitions are repeated verbatim (Comparator requires
every constant reachable from the compared statements to be identical in both modules) — with the
two theorems now proved by importing the library `Percolation` in this repository. The main
theorem there is

  `Percolation.Continuity.CSH.percolationContinuity_allDimensions
     (d : ℕ) (hd : 2 ≤ d) : Percolation.Literature.PercolationContinuity d`

and `Percolation.Literature.PercolationContinuity d` unfolds, definition by definition
(`theta`, `bondPercolation`, `percolatesAt`, `openCluster`, `openGraph`, `criticalProbI`,
`criticalProb`, `zdGraph`, `Site`), to the same term as `BondPercolation.PercolationContinuity d`
below, so the transport is by definitional unfolding (`bridge`, proved by `Iff.rfl`; no
mathematical content).
-/

namespace BondPercolation

open MeasureTheory

/-! ### The hypercubic lattice -/

/-- A site (vertex) of the `d`-dimensional hypercubic lattice `ℤ^d`: an integer vector with `d`
coordinates, encoded as a function `Fin d → ℤ`. The origin is the zero function `0`. -/
abbrev Site (d : ℕ) : Type := Fin d → ℤ

/-- The nearest-neighbour graph on `ℤ^d`: sites `x` and `y` are adjacent iff `y = x + eᵢ` or
`x = y + eᵢ` for some unit coordinate vector `eᵢ` (they differ by `±1` in exactly one coordinate
and agree in all others). Encoded as Mathlib's Hasse diagram `SimpleGraph.hasse` of the
coordinatewise partial order on `Fin d → ℤ`: its adjacency is the symmetrised covering relation
`x ⋖ y ∨ y ⋖ x`, and in the product order on `Fin d → ℤ` one has `x ⋖ y` iff `y = x + eᵢ` for some
`i` (Mathlib: `Pi.covBy_iff_exists_right_eq`, `Order.covBy_iff_add_one_eq`). -/
noncomputable abbrev zdGraph (d : ℕ) : SimpleGraph (Site d) := SimpleGraph.hasse (Site d)

/-! ### Bernoulli bond percolation on a simple graph -/

section Bond

variable {V : Type*}

/-- A bond configuration on the vertex type `V`: the set of *open* edges, as a set of unordered
pairs `ω ⊆ Sym2 V` (Grimmett's `ω ∈ {0,1}^E`, identified with `{e | ω(e) = 1}`). -/
abbrev BondConfig (V : Type*) : Type _ := Set (Sym2 V)

/-- Bernoulli bond percolation `P_p` on the graph `G` with edge density `p ∈ [0, 1]`: the
probability measure on bond configurations under which each edge of `G` is open independently
with probability `p` and every pair that is not an edge of `G` is closed. It is Mathlib's product
Bernoulli measure on sets, `ProbabilityTheory.setBernoulli G.edgeSet p` (notation
`setBer(G.edgeSet, p)`). -/
noncomputable def bondPercolation (G : SimpleGraph V) (p : unitInterval) :
    Measure (BondConfig V) :=
  ProbabilityTheory.setBernoulli G.edgeSet p

/-- The open graph of a configuration `ω`: the simple graph on `V` whose edges are the open pairs,
i.e. `x ∼ y` iff `x ≠ y` and `s(x, y) ∈ ω` (Mathlib's `SimpleGraph.fromEdgeSet ω`). -/
def openGraph (ω : BondConfig V) : SimpleGraph V := SimpleGraph.fromEdgeSet ω

/-- The open cluster `C(x)` of the vertex `x` in the configuration `ω`: the set of vertices joined
to `x` by a (possibly empty) path of open edges. It always contains `x`. -/
def openCluster (ω : BondConfig V) (x : V) : Set V := {y | (openGraph ω).Reachable x y}

/-- The percolation event at `x`, `{|C(x)| = ∞}`: the set of configurations in which the open
cluster of `x` is an infinite set of vertices. -/
def percolatesAt (x : V) : Set (BondConfig V) := {ω | (openCluster ω x).Infinite}

/-- The percolation probability `θ_x(p) := P_p(|C(x)| = ∞)`: the `bondPercolation G p`-measure of
the event `percolatesAt x`, as a real number (Grimmett 1999, (1.9)). -/
noncomputable def theta (G : SimpleGraph V) (x : V) (p : unitInterval) : ℝ :=
  (bondPercolation G p).real (percolatesAt x)

/-- The critical probability `p_c := inf {p ∈ [0, 1] | θ_x(p) > 0}` of bond percolation on `G` at
the vertex `x` (Grimmett 1999, (1.11), where it is written equivalently as `sup {p | θ_x(p) = 0}`).
Convention: the infimum is taken over `{p ∈ [0, 1] | θ_x(p) > 0} ∪ {1}`, so that `p_c = 1` when
`θ_x` vanishes identically on `[0, 1]` (without the extra point the real infimum of the empty set
would be the junk value `0`); when some `p` has `θ_x(p) > 0` the extra point changes nothing,
because such `p` are at most `1`. -/
noncomputable def criticalProb (G : SimpleGraph V) (x : V) : ℝ :=
  sInf ({p : ℝ | ∃ h : p ∈ unitInterval, 0 < theta G x ⟨p, h⟩} ∪ {1})

/-- `0 ≤ p_c ≤ 1`: the set whose infimum defines `p_c` is a nonempty subset of `[0, 1]`
containing `1`. (Needed only to regard `p_c` as a point of `[0, 1]` below.) -/
theorem criticalProb_mem_Icc (G : SimpleGraph V) (x : V) :
    criticalProb G x ∈ Set.Icc (0 : ℝ) 1 :=
  have h0 : ∀ p ∈ ({p : ℝ | ∃ h : p ∈ unitInterval, 0 < theta G x ⟨p, h⟩} ∪ {1}), (0 : ℝ) ≤ p :=
    fun _ hp => Or.elim hp (fun hl => Exists.elim hl fun h _ => h.1)
      fun h1 => le_of_le_of_eq zero_le_one (Set.mem_singleton_iff.mp h1).symm
  ⟨le_csInf ⟨1, Or.inr rfl⟩ h0, csInf_le ⟨0, h0⟩ (Or.inr rfl)⟩

end Bond

/-! ### The statement on `ℤ^d` -/

/-- The critical probability `p_c(ℤ^d)` of nearest-neighbour bond percolation on `ℤ^d`, measured
at the origin `0`, regarded as a point of the unit interval `[0, 1]` (it lies there by
`criticalProb_mem_Icc`) so that it can be substituted for the parameter `p` of `theta`. -/
noncomputable def criticalProbI (d : ℕ) : unitInterval :=
  ⟨criticalProb (zdGraph d) (0 : Site d), criticalProb_mem_Icc _ _⟩

/-- **Continuity of the percolation probability at criticality on `ℤ^d`**: the proposition
`θ_0(p_c(ℤ^d)) = 0`, i.e. for nearest-neighbour Bernoulli bond percolation on `ℤ^d` at its
critical parameter `p_c = inf {p | θ_0(p) > 0}`, the probability that the open cluster of the
origin is infinite equals `0`. -/
def PercolationContinuity (d : ℕ) : Prop :=
  theta (zdGraph d) (0 : Site d) (criticalProbI d) = 0

/-- The statement of `Challenge.lean` and the statement proved by the development are the same
proposition: both sides unfold to literally the same term over Mathlib. -/
theorem bridge (d : ℕ) :
    PercolationContinuity d ↔ Percolation.Literature.PercolationContinuity d :=
  Iff.rfl

/-- **Main theorem.** For every dimension `d ≥ 2`, nearest-neighbour Bernoulli bond percolation
on `ℤ^d` has no infinite open cluster at the origin at criticality, almost surely:
`θ(p_c) = P_{p_c}(|C(0)| = ∞) = 0`. -/
theorem percolation_continuity (d : ℕ) (hd : 2 ≤ d) : PercolationContinuity d :=
  (bridge d).mpr
    (Percolation.Continuity.CSH.percolationContinuity_allDimensions d hd)

/-- **The three-dimensional case.** `θ(p_c) = 0` for nearest-neighbour Bernoulli bond
percolation on `ℤ³` (the case `d = 3` of `percolation_continuity`, stated separately because it
is the form in which the problem is most often quoted). -/
theorem percolation_continuity_Z3 : PercolationContinuity 3 :=
  percolation_continuity 3 (by norm_num)

end BondPercolation
