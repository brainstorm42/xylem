import Mathlib

/-!
# Continuity of the percolation probability at the critical point on `ℤ^d`

This module is the statement surface of the submission: it defines, from Mathlib alone, the
standard objects of nearest-neighbour Bernoulli **bond** percolation on the hypercubic lattice
`ℤ^d`, and states the two compared theorems. Everything below the definitions is proved in
`Solution.lean` by importing the formalisation shipped in this repository (library
`Percolation`); the definitions here are verbatim copies (same bodies, fresh namespace
`BondPercolation`) of the ones the library uses, so that the comparison is definitional.

## The model (Grimmett, *Percolation*, 2nd ed., Springer 1999, §§1.3–1.4)

* The vertex set of `ℤ^d` is `Site d := Fin d → ℤ`; the nearest-neighbour graph `zdGraph d` joins
  two sites iff they differ by `±1` in exactly one coordinate.
* A *bond configuration* is a set `ω ⊆ Sym2 V` of unordered pairs, the *open* edges. The
  percolation measure `bondPercolation G p` with parameter `p ∈ [0, 1]` is Mathlib's product
  Bernoulli measure `ProbabilityTheory.setBernoulli G.edgeSet p` on `Set (Sym2 V)`: each edge of
  `G` is open independently with probability `p`, and pairs that are not edges of `G` are never
  open.
* The *open cluster* `C(x)` of a vertex `x` in `ω` is the set of vertices joined to `x` by a path
  of open edges; `percolatesAt x` is the event `{|C(x)| = ∞}`.
* The *percolation probability* is `θ_x(p) := P_p(|C(x)| = ∞)` (`theta G x p`, a real number), and
  the *critical probability* is `p_c := inf {p ∈ [0, 1] | θ_x(p) > 0}` (`criticalProb G x`), with
  the harmless convention that the infimum is taken over that set together with the point `1`, so
  that `p_c = 1` (rather than the junk value `sInf ∅ = 0` of `ℝ`) if `θ_x` vanishes identically.
  Since `θ_x` is non-decreasing in `p`, this is the same number as Grimmett's
  `p_c = sup {p | θ_x(p) = 0}` ((1.11) there); that equality is a standard fact and is *not* part
  of the compared statement, which uses the infimum form literally.

## The claim

`PercolationContinuity d` is the proposition `θ_0(p_c) = 0` for bond percolation on `ℤ^d` at the
origin: at the critical parameter there is almost surely no infinite open cluster containing the
origin. The compared theorems assert it for every `d ≥ 2` (`percolation_continuity`) and, as the
named special case, for `d = 3` (`percolation_continuity_Z3`).

Context, not part of the formal claim: `θ(p_c) = 0` was known for `d = 2` (Harris 1960, Kesten
1980) and for `d ≥ 11` (lace expansion: Hara–Slade 1990; Fitzner–van der Hofstad 2017); the
cases `3 ≤ d ≤ 10` were open (see e.g. Fitzner–van der Hofstad, *Electron. J. Probab.* 22 (2017),
§1.1, and Duminil-Copin, *Sixty years of percolation*, Proc. ICM 2018, Conjecture 1). Because
`θ` vanishes on `[0, p_c)` and is continuous on `(p_c, 1]` (Grimmett 1999, §8.3), the statement is
equivalent to continuity of `p ↦ θ(p)` on `[0, 1]`; that equivalence is likewise standard and not
part of the compared statement. For `d ≥ 2` one has `0 < p_c(ℤ^d) < 1` (Grimmett 1999, §1.4), so
the statement concerns a non-degenerate parameter; for `d = 1` it is false (`p_c = 1`,
`θ(1) = 1`), which is why the hypothesis `2 ≤ d` is present. Nothing is asserted about site
percolation, other lattices, or slabs.
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

/-- **Main theorem.** For every dimension `d ≥ 2`, nearest-neighbour Bernoulli bond percolation
on `ℤ^d` has no infinite open cluster at the origin at criticality, almost surely:
`θ(p_c) = P_{p_c}(|C(0)| = ∞) = 0`. -/
theorem percolation_continuity (d : ℕ) (hd : 2 ≤ d) : PercolationContinuity d := by
  sorry

/-- **The three-dimensional case.** `θ(p_c) = 0` for nearest-neighbour Bernoulli bond
percolation on `ℤ³` (the case `d = 3` of `percolation_continuity`, stated separately because it
is the form in which the problem is most often quoted). -/
theorem percolation_continuity_Z3 : PercolationContinuity 3 := by
  sorry

end BondPercolation
