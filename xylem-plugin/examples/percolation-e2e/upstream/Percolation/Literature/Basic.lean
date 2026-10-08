import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Order.Interval.Set.ProjIcc
import Mathlib.Probability.Distributions.SetBernoulli
import Mathlib.Probability.ProductMeasure
import Mathlib.Topology.UnitInterval
import Percolation.Literature.LatticeModels.LatticeGraph
import Percolation.Literature.LatticeModels.ThermodynamicLimit
import Percolation.Util.Linter

/-!
# Bernoulli bond and site percolation

Bernoulli percolation on a simple graph `G` on `V` (Grimmett, *Percolation*, 2nd ed. (1999),
§§1.3–1.4):

* **Monotone coupling** (Grimmett 1999, §1.3, p. 11): i.i.d. uniform labels `U e ∈ [0, 1]` under
  `labelMeasure V`, and `configOfLabels p U G = {e ∈ E(G) | U e ≤ p}` has law `bondPercolation G p`
  (`map_configOfLabels`), whence `theta_mono`.

Design choices.
* The parameter is `p : unitInterval` as in `setBernoulli`; we never `open unitInterval`.
  The constant `half : unitInterval` (`p = 1/2`) is shared by the percolation files; Mathlib has no
  named constant for it.
* Probabilities are real numbers via `Measure.real`.
* `criticalProb G x := sInf ({p | 0 < θ(p)} ∪ {1})`: Grimmett's `p_c = sup {p | θ(p) = 0}` lies
  in `[0, 1]`; since `sInf ∅ = 0` in `ℝ`, the bare `sInf {p | 0 < θ(p)}` would give `p_c = 0`
  when `θ ≡ 0` (e.g. `x` in a finite component of `G`), whereas the correct value is `1`. Adding
  `1` to the set fixes this and makes `criticalProb_mem_Icc` a lemma.
* `siteOpenGraph G ω := G ⊓ SimpleGraph.fromRel (fun x y => x ∈ ω ∧ y ∈ ω)`; the site cluster of a
  closed vertex is `∅` (Grimmett 1999, §1.6).
* `labelMeasure` is `Measure.infinitePi` of Lebesgue measure restricted to `[0, 1]` on `ℝ`
  (a probability measure since `volume (Icc 0 1) = 1`).

Mathlib anchors used rather than re-defined: `ProbabilityTheory.setBernoulli` (notation
`setBer(u, p)`, `setBernoulli_zero`, `setBernoulli_real_singleton`), `SimpleGraph.fromEdgeSet`,
`SimpleGraph.fromRel`, `SimpleGraph.Reachable`, `SimpleGraph.induce`,
`SimpleGraph.ConnectedComponent.supp`, `Set.encard`, `MeasureTheory.Measure.infinitePi`,
`MeasureTheory.Measure.real`, `Set.projIcc`. Mathlib has no percolation-specific declarations
(no `theta`, `p_c`, open cluster), hence the definitions below.
-/

namespace Percolation.Literature

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal

/-! ### The parameter `p = 1/2` -/

/-- The point `1/2` of the unit interval, the self-dual parameter of bond percolation on `ℤ²`
and site percolation on the triangular lattice. (Grimmett 1999, §1.4; Mathlib has no named
constant.) [cite: GrimmettPercolation1999, §1.4] -/
noncomputable def half : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩

/-- `(half : ℝ) = 1/2`. (Grimmett 1999, §1.4.) [cite: GrimmettPercolation1999, §1.4] -/
@[simp] theorem coe_half : ((half : unitInterval) : ℝ) = 1 / 2 := rfl

/-! ### Bond percolation -/

section Bond

variable {V : Type*}

/-- A bond configuration on the vertex type `V`: the set of *open* edges, `ω ⊆ Sym2 V`
(Grimmett 1999, §1.3, (1.3) p. 11: `ω ∈ {0,1}^E` identified with `K(ω) = {e | ω(e) = 1}`).
[cite: GrimmettPercolation1999, §1.3 (1.3) p. 11] -/
abbrev BondConfig (V : Type*) : Type _ := Set (Sym2 V)

/-- Bernoulli bond percolation on `G` with edge density `p`: the product measure `P_p` on
`BondConfig V` under which each edge of `G` is open independently with probability `p` and
non-edges are closed; Mathlib's `setBer(G.edgeSet, p)`. (Grimmett 1999, §1.3.) [cite: GrimmettPercolation1999, §1.3] -/
noncomputable def bondPercolation (G : SimpleGraph V) (p : unitInterval) :
    Measure (BondConfig V) :=
  setBer(G.edgeSet, p)

/-- `bondPercolation G p` is a probability measure (Mathlib's instance for `setBernoulli`).
(Grimmett 1999, §1.3.) [cite: GrimmettPercolation1999, §1.3] -/
instance instIsProbabilityMeasureBondPercolation (G : SimpleGraph V) (p : unitInterval) :
    IsProbabilityMeasure (bondPercolation G p) := by
  unfold bondPercolation; infer_instance

/-- The open subgraph of a bond configuration `ω`: `x ∼ y` iff `x ≠ y` and `s(x, y) ∈ ω`
(Mathlib's `SimpleGraph.fromEdgeSet`). (Grimmett 1999, §1.3.) [cite: GrimmettPercolation1999, §1.3] -/
def openGraph (ω : BondConfig V) : SimpleGraph V := SimpleGraph.fromEdgeSet ω

/-- Adjacency in the open graph. (Grimmett 1999, §1.3.) [cite: GrimmettPercolation1999, §1.3] -/
@[simp] theorem openGraph_adj (ω : BondConfig V) (x y : V) :
    (openGraph ω).Adj x y ↔ s(x, y) ∈ ω ∧ x ≠ y :=
  SimpleGraph.fromEdgeSet_adj ω

/-- The open cluster `C(x)` of `x` in the configuration `ω`: the vertices joined to `x` by an
open path. (Grimmett 1999, §1.3.) [cite: GrimmettPercolation1999, §1.3] -/
def openCluster (ω : BondConfig V) (x : V) : Set V := {y | (openGraph ω).Reachable x y}

/-- `x ∈ C(x)`. (Grimmett 1999, §1.3.) [cite: GrimmettPercolation1999, §1.3] -/
@[simp] theorem mem_openCluster_self (ω : BondConfig V) (x : V) : x ∈ openCluster ω x :=
  SimpleGraph.Reachable.refl x

/-- The event `{x ↔ y}` that `x` and `y` are joined by an open path. (Grimmett 1999, §1.3.) [cite: GrimmettPercolation1999, §1.3] -/
def openConn (x y : V) : Set (BondConfig V) := {ω | (openGraph ω).Reachable x y}

/-- The event `{x ↔ y in S}` that `x` and `y` are joined by an open path using only vertices of
`S` (in particular `x, y ∈ S`). (Grimmett 1999, §1.3.) [cite: GrimmettPercolation1999, §1.3] -/
def openConnIn (S : Set V) (x y : V) : Set (BondConfig V) :=
  {ω | ∃ (hx : x ∈ S) (hy : y ∈ S), ((openGraph ω).induce S).Reachable ⟨x, hx⟩ ⟨y, hy⟩}

/-- The event `{|C(x)| = ∞}` that the open cluster of `x` is infinite ("percolation occurs at
`x`"). (Grimmett 1999, §1.4.) [cite: GrimmettPercolation1999, §1.4] -/
def percolatesAt (x : V) : Set (BondConfig V) := {ω | (openCluster ω x).Infinite}

/-- The one-arm event `{0 ↔ ∂B(n)}` on `ℤ^d`: the origin is joined inside the box `B(n)` by an
open path to some vertex of the inner vertex boundary of `B(n)`. (Grimmett 1999: the box `B(n)`,
§1.4 p. 13; the event `A_n = {0 ↔ ∂B(n)}`, §3.2 p. 61 and §5.2.)
[cite: GrimmettPercolation1999, §1.4 p. 13 (the box B(n)) and §3.2 p. 61 (the event A_n)] -/
def siteToBoundary (d n : ℕ) : Set (BondConfig (LatticeModels.Site d)) :=
  {ω | ∃ y ∈ LatticeModels.innerBoundary (LatticeModels.zdGraph d) (LatticeModels.box d n), ω ∈ openConnIn (↑(LatticeModels.box d n)) 0 y}

/-- The percolation probability `θ_x(p) = P_p(|C(x)| = ∞)`. (Grimmett 1999, §1.4, (1.6), p. 13.)
[cite: GrimmettPercolation1999, §1.4 (1.6) p. 13] -/
noncomputable def theta (G : SimpleGraph V) (x : V) (p : unitInterval) : ℝ :=
  (bondPercolation G p).real (percolatesAt x)

/-- The critical probability `p_c = sup {p | θ_x(p) = 0} = inf {p | θ_x(p) > 0}`
(Grimmett 1999, §1.4, (1.8), p. 13). Convention: the infimum is taken over `{p | 0 < θ_x(p)} ∪ {1}`,
so that `p_c = 1` when `θ_x ≡ 0` (e.g. `x` in a finite component); without the `∪ {1}` the real
`sInf ∅ = 0` would give the wrong value. [cite: GrimmettPercolation1999, §1.4 (1.8) p. 13] -/
noncomputable def criticalProb (G : SimpleGraph V) (x : V) : ℝ :=
  sInf ({p : ℝ | ∃ h : p ∈ unitInterval, 0 < theta G x ⟨p, h⟩} ∪ {1})

/-- `0 ≤ p_c ≤ 1`. (Grimmett 1999, §1.4.) [cite: GrimmettPercolation1999, §1.4] -/
theorem criticalProb_mem_Icc (G : SimpleGraph V) (x : V) : criticalProb G x ∈ Set.Icc 0 1 := by
  have h0 : ∀ p ∈ ({p : ℝ | ∃ h : p ∈ unitInterval, 0 < theta G x ⟨p, h⟩} ∪ {1}), 0 ≤ p := by
    rintro p (⟨h, -⟩ | h)
    · exact h.1
    · rw [Set.mem_singleton_iff] at h
      rw [h]; exact zero_le_one
  exact ⟨le_csInf ⟨1, Or.inr rfl⟩ h0, csInf_le ⟨0, h0⟩ (Or.inr rfl)⟩

/-- The number of infinite open clusters of `ω`, as an extended natural number
(Grimmett 1999, §1.4 and §8.2 (uniqueness of the infinite cluster)).
[cite: GrimmettPercolation1999, §1.4 and §8.2 (uniqueness of the infinite cluster)] -/
noncomputable def numInfiniteClusters (ω : BondConfig V) : ℕ∞ :=
  {C : (openGraph ω).ConnectedComponent | C.supp.Infinite}.encard

/-- The event `{x ↔ y}` is measurable (a countable union over finite paths of cylinder events;
`V` countable). (Grimmett 1999, §1.3.) [cite: GrimmettPercolation1999, §1.3] -/
def measurableSet_openConn : Prop :=
  ∀ [Countable V] (x y : V),
    MeasurableSet (openConn x y : Set (BondConfig V))

/-- The event `{|C(x)| = ∞}` is measurable (`V` countable, `G` irrelevant).
(Grimmett 1999, §1.4.) [cite: GrimmettPercolation1999, §1.4] -/
def measurableSet_percolatesAt : Prop :=
  ∀ [Countable V] (x : V),
    MeasurableSet (percolatesAt x : Set (BondConfig V))

/-- At `p = 0` every edge is closed, so `θ_x(0) = 0` (`V` countable, so that singletons of
`BondConfig V` are measurable). (Grimmett 1999, §1.4.) [cite: GrimmettPercolation1999, §1.4] -/
theorem theta_bot [Countable V] (G : SimpleGraph V) (x : V) : theta G x 0 = 0 := by
  have hx : (∅ : BondConfig V) ∉ percolatesAt x := by
    have : openCluster (∅ : BondConfig V) x = {x} := by
      ext y
      simp only [openCluster, Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · intro h
        have hbot : openGraph (∅ : BondConfig V) = ⊥ := SimpleGraph.fromEdgeSet_empty
        rw [hbot, SimpleGraph.reachable_bot] at h
        exact h.symm
      · rintro rfl; rfl
    simp [percolatesAt, this]
  simp only [theta, bondPercolation, setBernoulli_zero, measureReal_def, Measure.dirac_apply,
    Set.indicator_of_notMem hx, ENNReal.toReal_zero]

/-- `θ_x` is non-decreasing in `p` (monotone coupling). (Grimmett 1999, §1.4 and Thm. 2.1.) [cite: GrimmettPercolation1999, §1.4 and Thm. 2.1] -/
def theta_mono : Prop :=
  ∀ [Countable V] (G : SimpleGraph V) (x : V),
    Monotone (theta G x)

/-- Below `p_c` there is a.s. no infinite cluster at `x`: `θ_x(p) = 0` for `p < p_c`.
(Grimmett 1999, §1.4, (1.8), p. 13: `p_c = sup {p : θ(p) = 0}`.) [cite: GrimmettPercolation1999, §1.4 (1.8) p. 13] -/
def theta_eq_zero_of_lt_criticalProb : Prop :=
  ∀ [Countable V] (G : SimpleGraph V) (x : V) (p : unitInterval) (hp : (p : ℝ) < criticalProb G x),
    theta G x p = 0

/-- Proof of `theta_eq_zero_of_lt_criticalProb`: if `θ_x(p) > 0` then `p` lies in the set
whose infimum is `p_c`, so `p_c ≤ p`; and `θ ≥ 0` is a probability. No coupling is needed.
(Grimmett 1999, §1.4, immediate from the definition (1.8), p. 13.) [cite: GrimmettPercolation1999, §1.4 (1.8) p. 13] -/
theorem theta_eq_zero_of_lt_criticalProb_holds : theta_eq_zero_of_lt_criticalProb (V := V) := by
  intro _ G x p hp
  by_contra hne
  have hpos : 0 < theta G x p := lt_of_le_of_ne measureReal_nonneg (Ne.symm hne)
  have hle : criticalProb G x ≤ p := by
    refine csInf_le ⟨0, ?_⟩ (Or.inl ⟨p.2, by simpa using hpos⟩)
    rintro q (⟨hq, -⟩ | hq)
    · exact hq.1
    · rw [Set.mem_singleton_iff] at hq
      rw [hq]; exact zero_le_one
  exact absurd hp (not_lt.mpr hle)

end Bond

/-! ### Site percolation -/

section SitePerc

variable {V : Type*}

/-- A site configuration on `V`: the set of *open* vertices. (Grimmett 1999, §1.6.) [cite: GrimmettPercolation1999, §1.6] -/
abbrev SiteConfig (V : Type*) : Type _ := Set V

/-- Bernoulli site percolation on the vertex type `V` with density `p`: every vertex is open
independently with probability `p`; Mathlib's `setBer(Set.univ, p)`. (Grimmett 1999, §1.6.) [cite: GrimmettPercolation1999, §1.6] -/
noncomputable def sitePercolation (V : Type*) (p : unitInterval) : Measure (SiteConfig V) :=
  setBer((Set.univ : Set V), p)

end SitePerc

/-! ### The monotone coupling -/

section Coupling

variable {V : Type*}

/-- The law of i.i.d. uniform `[0, 1]` labels `(U_e)_{e ∈ Sym2 V}`: the infinite product of
Lebesgue measure restricted to `[0, 1]`. (Grimmett 1999, §1.3, p. 11.) [cite: GrimmettPercolation1999, §1.3 p. 11] -/
noncomputable def labelMeasure (V : Type*) : Measure (Sym2 V → ℝ) :=
  Measure.infinitePi fun _ : Sym2 V => (volume.restrict (Set.Icc (0 : ℝ) 1))

/-- The configuration `η_p = {e ∈ E(G) | U_e ≤ p}` obtained from labels `U` at level `p`; it is
increasing in `p`, which couples all `P_p` monotonically. (Grimmett 1999, §1.3, p. 11.) [cite: GrimmettPercolation1999, §1.3 p. 11] -/
def configOfLabels (p : ℝ) (U : Sym2 V → ℝ) (G : SimpleGraph V) : BondConfig V :=
  {e | e ∈ G.edgeSet ∧ U e ≤ p}

/-- `configOfLabels` is monotone in the level `p`. (Grimmett 1999, §1.3.) [cite: GrimmettPercolation1999, §1.3] -/
theorem configOfLabels_mono (U : Sym2 V → ℝ) (G : SimpleGraph V) :
    Monotone fun p => configOfLabels p U G :=
  fun _ _ hpq _ ⟨he, hU⟩ => ⟨he, hU.trans hpq⟩

/-- Under i.i.d. uniform labels, `η_p` has law `P_p`. (Grimmett 1999, §1.3, p. 11.) [cite: GrimmettPercolation1999, §1.3 p. 11] -/
def map_configOfLabels : Prop :=
  ∀ [Countable V] (G : SimpleGraph V) (p : unitInterval),
    (labelMeasure V).map (configOfLabels (p : ℝ) · G) = bondPercolation G p

end Coupling

end Percolation.Literature
