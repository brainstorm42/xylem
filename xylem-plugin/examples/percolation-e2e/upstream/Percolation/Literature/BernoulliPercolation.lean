import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Probability.Distributions.SetBernoulli
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.InfinitePi
import Percolation.Literature.Basic
import Percolation.Literature.LatticeModels.LatticeGraph
import Percolation.Literature.LatticeModels.ThermodynamicLimit
import Percolation.Util.Linter

/-!
# Bernoulli bond percolation: basic statements

Throughout `G : SimpleGraph V`, `p : unitInterval` and `bondPercolation G p = setBer(G.edgeSet, p)`
is Bernoulli bond percolation (`Literature/Basic.lean`, Mathlib's
`ProbabilityTheory.setBernoulli`), a product measure on `BondConfig V = Set (Sym2 V)`;
`openGraph`, `openCluster`, `theta`, `criticalProb`, `numInfiniteClusters`, `siteToBoundary`,
`half` are those of `Literature/Basic.lean`; `zdGraph d` is the hypercubic lattice `ℤ^d` (`LatticeGraph.lean`).

## Contents

* The measure (Grimmett, *Percolation* (1999), §1.3; Broadbent–Hammersley 1957): the one-edge
  marginals
  `P_p(e open) = p` (`bondPercolation_cylinder`), the finite-cylinder product formula
  `P_p(F ⊆ ω) = p^{|F|}` (`bondPercolation_real_setOf_subset`), independence of the edge
  indicator events (`bondPercolation_indep`, Mathlib's `ProbabilityTheory.iIndepSet`), and the
  identification of the open cluster `C(x)` with the support of the connected component of `x`
  in the open graph (`openCluster_eq_supp`).

## Design choices

* Probabilities are real numbers via `Measure.real`; the parameter is
  `p : unitInterval` (never `open unitInterval`).
* Independence of distinct edges is Mathlib's `iIndepSet` of the family of events
  `{ω | e ∈ ω}` indexed by *all* `e : Sym2 V` (non-edges give a.s.-empty events, which are
  harmlessly independent of everything); the finite product formula is stated separately for
  finite sets of edges of `G`.
* The dual configuration on `(ℤ²)*` belongs to planar duality (`Crossings.lean`) and is not
  restated here.
* Mathlib has `setBernoulli` and its singleton/count API but no marginal, independence or
  percolation-specific lemmas (`theta`, `p_c`, clusters).
-/

namespace Percolation.Literature

open MeasureTheory ProbabilityTheory LatticeModels
open scoped ProbabilityTheory ENNReal

variable {V : Type*}

/-! ### The Bernoulli bond percolation measure -/

/-- **Finite-dimensional cylinder probabilities of `P_p`** (Grimmett,
*Percolation* (1999), §1.3; Broadbent–Hammersley, *Proc. Camb. Phil. Soc.* 53 (1957)). For a
finite set `F` of edges of `G`, the probability that all edges of `F` are open is `p ^ |F|`. [folklore] -/
theorem bondPercolation_real_setOf_subset (G : SimpleGraph V) (p : unitInterval)
    (F : Finset (Sym2 V)) (hF : (F : Set (Sym2 V)) ⊆ G.edgeSet) :
    (bondPercolation G p).real {ω | (F : Set (Sym2 V)) ⊆ ω} = (p : ℝ) ^ F.card := by
  classical
  have hpre : (fun q : Sym2 V → Prop => {i | q i}) ⁻¹' {ω : BondConfig V | (F : Set (Sym2 V)) ⊆ ω}
      = Set.pi (F : Set (Sym2 V)) (fun _ => {True}) := by
    ext q
    simp [Set.subset_def, Set.mem_pi]
  rw [measureReal_def, bondPercolation, setBernoulli_apply', hpre,
    Measure.infinitePi_pi _ (fun _ _ => MeasurableSet.of_discrete)]
  have h1 : ∀ e ∈ F, (unitInterval.toNNReal p • Measure.dirac (e ∈ G.edgeSet) +
      unitInterval.toNNReal (unitInterval.symm p) • Measure.dirac False : Measure Prop) {True}
      = unitInterval.toNNReal p := by
    intro e he
    have heT : (e ∈ G.edgeSet) = True := propext ⟨fun _ => trivial, fun _ => hF he⟩
    simp [heT]
  rw [Finset.prod_congr rfl h1, Finset.prod_const, ENNReal.toReal_pow, ENNReal.coe_toReal]
  rfl

/-- **One-edge marginals of Bernoulli bond percolation** (Grimmett, *Percolation* (1999), §1.3). Every edge `e` of `G` is open with probability exactly `p` under `P_p`. [folklore] -/
theorem bondPercolation_cylinder (G : SimpleGraph V) (p : unitInterval)
    {e : Sym2 V} (he : e ∈ G.edgeSet) :
    (bondPercolation G p).real {ω | e ∈ ω} = p := by
  have h := bondPercolation_real_setOf_subset G p {e} (by simpa using he)
  simpa using h

/-- **Independence of distinct edges** (Grimmett, *Percolation* (1999), §1.3: `P_p` is the product
measure `∏_e μ_e`). The events `{e open}`, `e : Sym2 V`, are mutually
independent under `P_p` (Mathlib's `ProbabilityTheory.iIndepSet`); for non-edges of `G` the
event is a.s. empty. [cite: GrimmettPercolation1999, §1.3 (product measure)] -/
def bondPercolation_indep : Prop :=
  ∀ [Countable V] (G : SimpleGraph V) (p : unitInterval),
    iIndepSet (fun e : Sym2 V => {ω : BondConfig V | e ∈ ω}) (bondPercolation G p)

/-- **Open clusters are the connected components of the open subgraph** (Grimmett,
*Percolation* (1999), §1.3). The open cluster `C(x)` of `ω` is the vertex set of the
connected component of `x` in `openGraph ω` (Mathlib's `SimpleGraph.ConnectedComponent.supp`). [folklore] -/
theorem openCluster_eq_supp (ω : BondConfig V) (x : V) :
    openCluster ω x = ((openGraph ω).connectedComponentMk x).supp := by
  ext y
  simp only [openCluster, Set.mem_setOf_eq, SimpleGraph.ConnectedComponent.mem_supp_iff,
    SimpleGraph.ConnectedComponent.eq]
  exact SimpleGraph.reachable_comm

/-! ### The critical probability -/

/-- **Supercritical phase** (Grimmett, *Percolation* (1999), §1.4, (1.8) p. 13). Above `p_c`
percolation occurs with positive probability: `θ_x(p) > 0` for `p > p_c`. [folklore] -/
def theta_pos_of_criticalProb_lt : Prop :=
  ∀ [Countable V] (G : SimpleGraph V) (x : V) (p : unitInterval) (h : criticalProb G x < p),
    0 < theta G x p

/-! ### Kesten's theorem -/

/-- **Kesten's theorem** (Kesten, *Comm. Math. Phys.* 74 (1980) 41, Thm. 1;
lower bound `p_c ≥ 1/2` by Harris, *Proc. Camb. Phil. Soc.* 56 (1960) 13). The critical
probability of bond percolation on the square lattice is `p_c(ℤ²) = 1/2`. [cite: KestenCMP1980, Thm. 1] [cite: HarrisPCPS1960] -/
def kesten_criticalProb_Z2 : Prop :=
  criticalProb (zdGraph 2) 0 = 1 / 2

/-- **No percolation at criticality on `ℤ²`** (Harris, *Proc. Camb. Phil. Soc.*
56 (1960) 13; Grimmett, *Percolation* (1999), Thm. 11.12 with Lemma 11.12). `θ(1/2) = 0` for
bond percolation on `ℤ²`. [cite: HarrisPCPS1960, main theorem] [cite: GrimmettPercolation1999, Thm. 11.12] -/
def harris_theta_half : Prop :=
  theta (zdGraph 2) (0 : Site 2) half = 0

/-! ### Sharpness of the phase transition -/

/-- **Sharpness of the percolation transition, subcritical exponential decay** (Menshikov, *Soviet Math. Dokl.* 33 (1986) 856; Aizenman–Barsky, *Comm. Math. Phys.* 108 (1987)
489; Duminil-Copin–Tassion, *Comm. Math. Phys.* 343 (2016) 725, Thm. 1.1(1)). On `ℤ^d`,
`d ≥ 2`, for every `p < p_c` there is `c = c(p) > 0` with `P_p(0 ↔ ∂B(n)) ≤ e^{-c n}` for all
`n`. [cite: DuminilCopinTassionCMP2016, Thm. 1.1 (1)] -/
def perc_sharpness : Prop :=
  ∀ {d : ℕ} (hd : 2 ≤ d) (p : unitInterval) (hp : (p : ℝ) < criticalProb (zdGraph d) 0),
    ∃ c > 0, ∀ n : ℕ, (bondPercolation (zdGraph d) p).real (siteToBoundary d n) ≤
      Real.exp (-c * n)

/-! ### Proof of `bondPercolation_indep` (Grimmett 1999, §1.3, p. 10: `P_p = ∏_e μ_e`) -/

/-- The edge indicators `ω ↦ (e ∈ ω)`, `e : Sym2 V`, are mutually independent random variables
(values in `Prop`) under `P_p = bondPercolation G p`. Proof: `setBer(E(G), p)` is the image under
the measurable equivalence `setOf : (Sym2 V → Prop) ≃ Set (Sym2 V)` of the product measure
`Measure.infinitePi μ` of the one-edge laws `μ_e = p δ_{e ∈ E(G)} + (1 - p) δ_False`, so the
joint law of the indicators is `infinitePi μ` and each marginal is `μ_e`
(`Measure.infinitePi_map_eval`); conclude by Mathlib's
`iIndepFun_iff_map_fun_eq_infinitePi_map`. (Grimmett, *Percolation* (1999), §1.3, p. 10:
"we take product measure with density `p` on `(Ω, 𝓕)` ... `P_p = ∏_{e ∈ 𝔼^d} μ_e`".) [cite: GrimmettPercolation1999, §1.3 p. 10 (product measure)] -/
theorem bondPercolation_iIndepFun_mem [Countable V] (G : SimpleGraph V) (p : unitInterval) :
    iIndepFun (fun (e : Sym2 V) (ω : BondConfig V) => e ∈ ω) (bondPercolation G p) := by
  -- the one-edge laws `μ_e` (Bernoulli(`p`) on edges of `G`, `δ_False` on non-edges)
  set μ : Sym2 V → Measure Prop := fun i =>
    unitInterval.toNNReal p • Measure.dirac (i ∈ G.edgeSet) +
      unitInterval.toNNReal (unitInterval.symm p) • Measure.dirac False
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (fun e => measurable_set_mem e)]
  have hS : Measurable fun q : Sym2 V → Prop => {i | q i} := measurable_setOf
  -- joint law of the indicators: `setOf⁻¹ ∘ setOf = id`
  have h1 : (bondPercolation G p).map (fun (ω : BondConfig V) (e : Sym2 V) => e ∈ ω) =
      Measure.infinitePi μ := by
    rw [bondPercolation, setBernoulli_eq_map, Measure.map_map (by fun_prop) hS]
    exact Measure.map_id
  rw [h1]
  congrm Measure.infinitePi fun e => ?_
  -- marginal at `e`: `eval e ∘ setOf`, whose law is `μ e`
  rw [bondPercolation, setBernoulli_eq_map, Measure.map_map (measurable_set_mem e) hS]
  exact (Measure.infinitePi_map_eval μ e).symm

/-- Proof of the statement `bondPercolation_indep`: the events
`{e open} = {ω | e ∈ ω}`, `e : Sym2 V`, are mutually independent under `P_p` (Mathlib's
`iIndepSet`). From `bondPercolation_iIndepFun_mem` via Mathlib's `iIndep_comap_mem_iff`
(`iIndepSet f μ ↔ iIndep (fun i ↦ comap (· ∈ f i) ⊤) μ`, and `iIndepFun` of `Prop`-valued maps
is by definition `iIndep` of the comaps of `⊤ = MeasurableSpace Prop`). (Grimmett, *Percolation*
(1999), §1.3, p. 10, `P_p = ∏_e μ_e`.) [cite: GrimmettPercolation1999, §1.3 p. 10 (product measure)] -/
theorem bondPercolation_indep_holds : bondPercolation_indep (V := V) := by
  intro _ G p
  rw [← iIndep_comap_mem_iff]
  exact bondPercolation_iIndepFun_mem G p

end Percolation.Literature
