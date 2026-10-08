import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.ProjIcc
import Percolation.Literature.BondPercolationSymmetry
import Percolation.Literature.Crossings
import Percolation.Literature.FiniteEnergy
import Percolation.Literature.PercolationEvents
import Percolation.Literature.PercolationProofs
import Percolation.Literature.RussoFormula
import Percolation.Literature.SharpnessDCT
import Percolation.Literature.SiteMonotonicity
import Percolation.Literature.SitePaths
import Percolation.Util.Linter

/-!
# Sharpness of the phase transition for Bernoulli percolation on `ℤ^d`: the proofs (Duminil-Copin–Tassion 2016)

Source:

* H. Duminil-Copin, V. Tassion, *A new proof of the sharpness of the phase transition for Bernoulli
  percolation on `ℤ^d`*, L'Enseignement Math. 62 (2016) 199–206 [DuminilCopinTassionEM2016], §2;
* the `ℤ^d`, nearest-neighbour case of Duminil-Copin–Tassion, *Comm. Math. Phys.* 343 (2016)
  725–745 [DuminilCopinTassionCMP2016], Thm. 1.1.

## Part I. Toolbox (Grimmett, *Percolation* (1999), §§1.3, 2.1–2.2 [GrimmettPercolation1999])

* `mem_openConnIn_iff_pathIn`: `{x ⟷ y in S} = openConnIn S x y` in terms of the relational paths
  `PathIn (openGraph ω) S x y` of `SitePaths.lean`; transport of paths (`pathIn_map`,
  `pathIn_congrGraph`, `pathIn_induction`);
* finite dependence (`determinedBy_openConnIn`: `{x ⟷ y in S}` depends on the pairs of
  Mathlib's `Set.sym2 S`; `determinedBy_siteToBoundary`), measurability;
* `real_inter_of_determinedBy_disjoint`: events determined by disjoint finite sets of pairs are
  independent under `P_p` — the finite-support corollary of this library's
  `Percolation.Literature.bondPercolation_real_inter_of_disjoint` (`FiniteEnergy.lean`);
* `real_mono_of_isUpperSet` (monotone coupling `map_configOfLabels_holds`) and
  `DCT16_phi_mono_holds`;
* `real_mono_of_forall_subset_edgeSet`: inclusions of events need only be checked on `ω ⊆ E(G)`
  (`P_p`-a.s., Mathlib's `setBernoulli_ae_subset`);
* one-arm events: `siteToBoundary` via paths, `armEvent v n` and translation invariance
  (`real_armEvent`), first exit (`armEvent_of_pathIn`), `real_siteToBoundary_antitone`,
  `real_siteToBoundary_one_lt_one` (`P_p[0 ⟷ ∂Λ_1] < 1` for `p < 1`), and the limit `n → ∞`
  (`le_theta_of_forall_le_real_siteToBoundary`, continuity of the measure from above).

The increasing property of `{x ⟷ y in S}` is this library's
`Percolation.Literature.isUpperSet_openConnIn` (`Crossings.lean`), and the almost sure
support `ω ⊆ E(G)` is Mathlib's `ProbabilityTheory.setBernoulli_ae_subset`, used directly. Also used
from this library rather than re-proved: independence of events with disjoint supports
(`bondPercolation_real_inter_of_disjoint`) and `P_p(all edges of K closed) ≥ (1-p)^{|K|}`
(`le_bondPercolation_real_forall_notMem`), both `FiniteEnergy.lean`; the one-edge events
`determinedBy_mem` / `(determinedBy_mem e).compl` and `DeterminedBy.iUnion`
(`SiteMonotonicity.lean`, `PercolationEvents.lean`).

## Part II. The exploration argument (§2.1, proof of item 1)

Choose `L` with `S ⊆ Λ_L` and let `N > L`; assume `0 ⟷ ∂Λ_N` and let `𝒞 = {z : 0 ⟷ z in S}`
(`clusterSet`). Following an open path from `0` to `∂Λ_N ∌ S` up to its last visit to `𝒞`
(`PathIn.last_exit`) yields a boundary edge `{x, y}` of `S` with `0 ⟷ x in S`, `{x, y}` open and
`y ⟷ ∂Λ_N in Λ_N ∖ 𝒞` (`exists_decomposition`). Union bound and decomposition according to
`𝒞 = C` (`real_siteToBoundary_le_sum`); the three events are determined by the pairwise disjoint
sets of pairs `clusterPairs S C`, `{{x, y}}`, pairs inside `Λ_N ∖ C`, hence independent
(`real_inter_three`); the last one is contained in the translate by `y ∈ Λ_{L+1}` of
`{0 ⟷ ∂Λ_m}`, `N = m + L + 1` (`armEvent_of_mem_exitEvent`), of probability `P_p[0 ⟷ ∂Λ_m]`.
Resumming over `C` (`sum_real_clusterEvent`) gives `P_p[0 ⟷ ∂Λ_{m+L+1}] ≤ φ_p(S) P_p[0 ⟷ ∂Λ_m]`
(`real_siteToBoundary_le_phi_mul`), whence `P_p[0 ⟷ ∂Λ_{k(L+1)}] ≤ φ_p(S)^k`
(`real_siteToBoundary_mul_le_pow`) and, with the monotonicity in `n` and `P_p[0 ⟷ ∂Λ_1] < 1`,
`DCT16_expDecay_of_phi_lt_one_holds`.

## Part III. Lemma 2.1

By Russo's formula (`russo_formula_sum_holds`),
`θ_n' = Σ_e P_p[e pivotal] = 1/(1-p) Σ_e P_p[e pivotal, e closed]` (`real_pivotal_closed`). With
`𝒮 = {z ∈ Λ_n : z ⟷̸ ∂Λ_n}` (`blockSet`): on `{0 ⟷ x in S} ∩ {𝒮 = S}`, a boundary edge `{x, y}` of
`S` is closed and pivotal (`subset_pivotal`); regrouping the triples `(S, x, y)` by edge
(`sum_le_sum_pivotal`), the independence of `{0 ⟷ x in S}` (pairs inside `S`) and `{𝒮 = S}`
(pairs of `Λ_n` not inside `S`, `determinedBy_blockEvent`, "exploring from the outside") and the
partition `Σ_{0 ∈ S ⊆ Λ_n} P_p[𝒮 = S] = 1 - θ_n` (`sum_real_blockEvent`) give
`DCT16_lemma21_holds`.

## Part IV. Integration of (2.1) (§2.2) and assembly

`θ_n` is a polynomial in the parameter (`continuous_thetaN`); if `φ_q(S) ≥ 1` for all `S ∋ 0` and
`q ≥ p₁` then `g(q) = (1 - θ_n(q)) q/(1-q)` has `g' ≤ 0` on `(p₁, 1)` by Lemma 2.1, so
`θ_n(p) ≥ (p - p₁)/(p(1 - p₁))` (`thetaN_ge`), and `n → ∞` gives
`DCT16_meanField_of_phi_ge_one_holds`. Finally `DCT16.perc_sharpness_holds` is
`perc_sharpness_of_DCT16` applied to the three discharged steps.

## Part V. `p̃_c = p_c` and the mean-field bound (Thm. 1.1, first assertion and item 2)

For `p_c < p < 1` and every `p₁ ∈ (p_c, p)`, `φ_q ≥ 1` for `q ≥ p₁` by the definition of `p̃_c =
p_c`, whence `θ(p) ≥ (p - p₁)/(p(1-p₁))` and `p₁ ↓ p_c`; at `p = 1`, `θ(1) = 1`.

Mathlib anchors: `Relation.ReflTransGen`, `SimpleGraph.induce`, `Finset.sym2`,
`ProbabilityTheory.setBernoulli_ae_subset`, `MeasureTheory.measure_iInter_eq_iInf_measure_iInter_le`,
`Finset.sum_sigma`, `Finset.sum_fiberwise_of_maps_to`, `antitoneOn_of_deriv_nonpos`,
`HasDerivAt.fun_div`, `continuous_projIcc`. Tree anchors: `PathIn` (`SitePaths.lean`),
`DeterminedBy`, `IsPivotal` (`PercolationEvents.lean`), `isUpperSet_openConnIn` (`Crossings.lean`),
`bondPercolation_real_inter_of_disjoint`, `le_bondPercolation_real_forall_notMem`
(`FiniteEnergy.lean`), `determinedBy_mem` (`SiteMonotonicity.lean`),
`map_configOfLabels_holds` (`PercolationProofs.lean`), `BondConfig.relabel`, `bondPercolation_real_preimage_shift`
(`BondPercolationSymmetry.lean`), `russo_formula_sum_holds`, `Russo.determinedBy_isPivotal`,
`Russo.measureReal_eq_cylPoly` (`RussoFormula.lean`), `exists_eq_of_mem_innerBoundary_box`
(`SiteConnectionTools.lean`).
-/

namespace Percolation.Literature.DCT16

open MeasureTheory ProbabilityTheory LatticeModels Filter
open scoped ENNReal Topology

/-! ### `openConnIn` in terms of `PathIn` -/

section Paths

variable {V : Type*}

/-- A witness of `ω ∈ {x ⟷ y in S}` is an open path inside `S`. [folklore] -/
theorem pathIn_of_mem_openConnIn {S : Set V} {x y : V} {ω : BondConfig V}
    (h : ω ∈ openConnIn S x y) : PathIn (openGraph ω) S x y := by
  obtain ⟨hx, hy, hr⟩ := h
  rw [SimpleGraph.reachable_iff_reflTransGen] at hr
  suffices key : ∀ b : S, Relation.ReflTransGen ((openGraph ω).induce S).Adj ⟨x, hx⟩ b →
      PathIn (openGraph ω) S x b.1 from key ⟨y, hy⟩ hr
  intro b hb
  induction hb with
  | refl => exact PathIn.refl hx
  | @tail c e _ hce ih =>
    simp only [SimpleGraph.comap_adj, Function.Embedding.coe_subtype] at hce
    exact ih.tail hce e.2

/-- An open path inside `S` witnesses `ω ∈ {x ⟷ y in S}`. [folklore] -/
theorem mem_openConnIn_of_pathIn {S : Set V} {x y : V} {ω : BondConfig V}
    (h : PathIn (openGraph ω) S x y) : ω ∈ openConnIn S x y := by
  obtain ⟨hx, hr⟩ := h
  induction hr with
  | refl => exact ⟨hx, hx, SimpleGraph.Reachable.refl _⟩
  | @tail b c _ hbc ih =>
    obtain ⟨_, hb, hreach⟩ := ih
    refine ⟨hx, hbc.2, hreach.trans (SimpleGraph.Adj.reachable (?_ : ((openGraph ω).induce S).Adj
      ⟨b, hb⟩ ⟨c, hbc.2⟩))⟩
    simp only [SimpleGraph.comap_adj, Function.Embedding.coe_subtype]
    exact hbc.1

/-- **`{x ⟷ y in S}` in terms of paths**: `ω ∈ openConnIn S x y` iff there is an open path of
vertices of `S` from `x` to `y` (Duminil-Copin–Tassion 2016, §1, definition of
`x ⟷ y in S`). [cite: DuminilCopinTassionEM2016, §1 (Notation)] -/
theorem mem_openConnIn_iff_pathIn {S : Set V} {x y : V} {ω : BondConfig V} :
    ω ∈ openConnIn S x y ↔ PathIn (openGraph ω) S x y :=
  ⟨pathIn_of_mem_openConnIn, mem_openConnIn_of_pathIn⟩

/-- Transport of a path along a map sending the ambient set into another set and the used edges to
edges. [folklore] -/
theorem pathIn_map {W : Type*} {G : SimpleGraph V} {G' : SimpleGraph W} (f : V → W) {A : Set V}
    {B : Set W} (hAB : ∀ a ∈ A, f a ∈ B)
    (hadj : ∀ a b, a ∈ A → b ∈ A → G.Adj a b → G'.Adj (f a) (f b)) {u v : V}
    (h : PathIn G A u v) : PathIn G' B (f u) (f v) := by
  obtain ⟨hu, hr⟩ := h
  refine ⟨hAB u hu, ?_⟩
  induction hr with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hub hbc ih =>
    have hb : b ∈ A := PathIn.right_mem (show PathIn G A u b from ⟨hu, hub⟩)
    exact ih.tail ⟨hadj b c hb hbc.2 hbc.1, hAB c hbc.2⟩

/-- Change of the ambient graph: a `G`-path inside `A` is a `G'`-path inside `A` as soon as the
`G`-edges between vertices of `A` are `G'`-edges. [folklore] -/
theorem pathIn_congrGraph {G G' : SimpleGraph V} {A : Set V}
    (hadj : ∀ a b, a ∈ A → b ∈ A → G.Adj a b → G'.Adj a b) {u v : V} (h : PathIn G A u v) :
    PathIn G' A u v :=
  pathIn_map id (fun _ h => h) hadj h

/-- All vertices of a path from `u` satisfy any property of `u` that propagates along the edges of
the path; in particular the endpoint does. [folklore] -/
theorem pathIn_induction {G : SimpleGraph V} {A : Set V} {u v : V} (P : V → Prop)
    (h : PathIn G A u v) (hu : P u) (hstep : ∀ a b, a ∈ A → b ∈ A → P a → G.Adj a b → P b) :
    P v := by
  obtain ⟨huA, hr⟩ := h
  induction hr with
  | refl => exact hu
  | @tail b c hub hbc ih =>
    exact hstep b c (PathIn.right_mem (show PathIn G A u b from ⟨huA, hub⟩)) hbc.2 ih hbc.1

/-- A path inside `A` is in particular a walk of the graph: its endpoints are reachable. [folklore] -/
theorem reachable_of_pathIn {G : SimpleGraph V} {A : Set V} {u v : V} (h : PathIn G A u v) :
    G.Reachable u v := by
  obtain ⟨-, hr⟩ := h
  induction hr with
  | refl => exact SimpleGraph.Reachable.refl _
  | tail _ hbc ih => exact ih.trans hbc.1.reachable

end Paths

/-! ### Finite dependence of connection events -/

section Determined

variable {V : Type*}

/-- Configurations agreeing on a set of pairs `K` have the same open edges in `K`. [folklore] -/
theorem openGraph_adj_congr {ω ω' : BondConfig V} {K : Set (Sym2 V)} (h : ω ∩ K = ω' ∩ K)
    {a b : V} (hab : s(a, b) ∈ K) : (openGraph ω).Adj a b ↔ (openGraph ω').Adj a b := by
  have key : s(a, b) ∈ ω ↔ s(a, b) ∈ ω' :=
    ⟨fun h1 => (((Set.ext_iff.1 h) _).1 ⟨h1, hab⟩).1, fun h1 => (((Set.ext_iff.1 h) _).2 ⟨h1, hab⟩).1⟩
  rw [openGraph_adj, openGraph_adj, key]

/-- Paths inside `S` only see the pairs inside `S` (Mathlib's `Set.sym2 S`): configurations
agreeing on `S.sym2` have the same paths inside `S`. [folklore] -/
theorem pathIn_congr_of_inter_eq {ω ω' : BondConfig V} {S : Set V} {K : Set (Sym2 V)}
    (hK : S.sym2 ⊆ K) (h : ω ∩ K = ω' ∩ K) {u v : V} (hp : PathIn (openGraph ω) S u v) :
    PathIn (openGraph ω') S u v :=
  pathIn_congrGraph (fun _ _ ha hb hab =>
    (openGraph_adj_congr h (hK (Set.mk_mem_sym2_iff.2 ⟨ha, hb⟩))).1 hab) hp

/-- **`{x ⟷ y in S}` is determined by the pairs inside `S`** (Grimmett 1999, §2.2: an event
"defined in terms of the states of edges" in a region). [cite: GrimmettPercolation1999, §2.2] -/
theorem determinedBy_openConnIn (S : Set V) (x y : V) {K : Set (Sym2 V)} (hK : S.sym2 ⊆ K) :
    DeterminedBy (openConnIn S x y) K := by
  rw [determinedBy_iff]
  intro ω ω' h
  simp only [mem_openConnIn_iff_pathIn]
  exact ⟨pathIn_congr_of_inter_eq hK h, pathIn_congr_of_inter_eq hK h.symm⟩

/-- `{x ⟷ y in S}` is measurable for finite `S`. [cite: GrimmettPercolation1999, §2.2] -/
theorem measurableSet_openConnIn (S : Finset V) (x y : V) :
    MeasurableSet (openConnIn (↑S : Set V) x y : Set (BondConfig V)) :=
  (determinedBy_openConnIn (↑S) x y (K := ↑S.sym2) (by rw [Finset.coe_sym2])).measurableSet_of_finset

end Determined

/-! ### Independence of events determined by disjoint finite sets of pairs -/

section Indep

variable {V : Type*}

/-- **Disjoint-support independence** (Grimmett 1999, §2.2; the product structure of `P_p`,
§1.3): events determined by disjoint finite sets of pairs are independent under
`P_p = bondPercolation G p`, `P_p(A ∩ B) = P_p(A) P_p(B)`. This is the independence invoked in
Duminil-Copin–Tassion 2016, §2.1 ("the three events depend on different sets of edges and are
therefore independent") and in the proof of Lemma 2.1. It is the finite-support case of the
tree's `bondPercolation_real_inter_of_disjoint` (`FiniteEnergy.lean`, arbitrary disjoint edge
sets, measurability assumed), measurability being automatic for finitely determined events.
[cite: GrimmettPercolation1999, §2.2] -/
theorem real_inter_of_determinedBy_disjoint [Countable V] (G : SimpleGraph V) (p : unitInterval)
    {A B : Set (BondConfig V)} {F K : Finset (Sym2 V)} (hA : DeterminedBy A ↑F)
    (hB : DeterminedBy B ↑K) (hFK : Disjoint F K) :
    (bondPercolation G p).real (A ∩ B) =
      (bondPercolation G p).real A * (bondPercolation G p).real B :=
  bondPercolation_real_inter_of_disjoint G p (Finset.disjoint_coe.2 hFK) hA hB
    hA.measurableSet_of_finset hB.measurableSet_of_finset

end Indep

/-! ### Monotonicity in `p`, one-edge probabilities, almost sure support -/

section Mono

variable {V : Type*}

/-- **`P_p(A) ≤ P_q(A)` for `p ≤ q` and `A` increasing measurable** (Grimmett 1999, Thm. 2.1, via
the monotone coupling `map_configOfLabels_holds`). [cite: GrimmettPercolation1999, Thm. 2.1] -/
theorem real_mono_of_isUpperSet [Countable V] (G : SimpleGraph V) {A : Set (BondConfig V)}
    (hA : IsUpperSet A) (hAm : MeasurableSet A) {p q : unitInterval} (hpq : p ≤ q) :
    (bondPercolation G p).real A ≤ (bondPercolation G q).real A := by
  have := isProbabilityMeasure_labelMeasure V
  rw [← map_configOfLabels_holds G p, ← map_configOfLabels_holds G q, measureReal_def,
    measureReal_def, Measure.map_apply (measurable_configOfLabels _ G) hAm,
    Measure.map_apply (measurable_configOfLabels _ G) hAm]
  refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono fun U hU => ?_)
  exact hA (configOfLabels_mono U G (Subtype.coe_le_coe.2 hpq)) hU

/-- **Discharge of `DCT16_phi_mono`**: `φ_p(S) ≤ φ_q(S)` for `p ≤ q`, term by term from
`real_mono_of_isUpperSet` (the events `{0 ⟷ x in S}` are increasing and local).
[cite: DuminilCopinTassionEM2016, §2.1] -/
theorem DCT16_phi_mono_holds : DCT16_phi_mono := by
  intro d S p q hpq
  rw [DCT16.phi_def, DCT16.phi_def]
  refine mul_le_mul (Subtype.coe_le_coe.2 hpq) ?_
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => measureReal_nonneg) q.2.1
  refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
  exact real_mono_of_isUpperSet (zdGraph d) (isUpperSet_openConnIn _ _ _)
    (measurableSet_openConnIn S 0 x) hpq

/-- `P_p(e closed) = 1 - p` for an edge `e` of `G`. (Grimmett 1999, §1.3.) [cite: GrimmettPercolation1999, §1.3] -/
theorem real_notMem (G : SimpleGraph V) (p : unitInterval) {e : Sym2 V} (he : e ∈ G.edgeSet) :
    (bondPercolation G p).real {ω | e ∉ ω} = 1 - p := by
  have h : {ω : BondConfig V | e ∉ ω} = {ω | e ∈ ω}ᶜ := rfl
  rw [h, measureReal_compl (measurableSet_mem e), probReal_univ, bondPercolation_cylinder G p he]

/-- **Inclusions of events up to the null set of configurations using non-edges**: if every
`ω ⊆ E(G)` lying in `A` lies in `B`, then `P_p(A) ≤ P_p(B)`. [folklore] -/
theorem real_mono_of_forall_subset_edgeSet [Countable V] (G : SimpleGraph V) (p : unitInterval)
    {A B : Set (BondConfig V)} (h : ∀ ω, ω ⊆ G.edgeSet → ω ∈ A → ω ∈ B) :
    (bondPercolation G p).real A ≤ (bondPercolation G p).real B := by
  refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_)
  filter_upwards [(setBernoulli_ae_subset : ∀ᵐ ω ∂bondPercolation G p, ω ⊆ G.edgeSet)] with ω hω
    using h ω hω

/-- Equality version of `real_mono_of_forall_subset_edgeSet`. [folklore] -/
theorem real_congr_of_forall_subset_edgeSet [Countable V] (G : SimpleGraph V) (p : unitInterval)
    {A B : Set (BondConfig V)} (h : ∀ ω, ω ⊆ G.edgeSet → (ω ∈ A ↔ ω ∈ B)) :
    (bondPercolation G p).real A = (bondPercolation G p).real B :=
  le_antisymm (real_mono_of_forall_subset_edgeSet G p fun ω hω => (h ω hω).1)
    (real_mono_of_forall_subset_edgeSet G p fun ω hω => (h ω hω).2)

/-- For `ω ⊆ E(G)`, open edges are edges of `G`. [folklore] -/
theorem adj_of_openGraph_adj {G : SimpleGraph V} {ω : BondConfig V} (hω : ω ⊆ G.edgeSet) {a b : V}
    (h : (openGraph ω).Adj a b) : G.Adj a b := by
  rw [openGraph_adj] at h
  exact hω h.1

end Mono

/-! ### Boxes and their boundaries in `ℤ^d` -/

section Boxes

variable {d : ℕ}

/-- Neighbours in `ℤ^d` differ by at most `1` in each coordinate. [folklore] -/
theorem abs_sub_le_one_of_adj {x y : Site d} (h : (zdGraph d).Adj x y) (j : Fin d) :
    |x j - y j| ≤ 1 := by
  obtain ⟨i, h | h⟩ := (zdGraph_adj_iff x y).1 h
  · have hyj : y j = x j + (Pi.single i (1 : ℤ) : Site d) j := by rw [h]; rfl
    rcases eq_or_ne j i with rfl | hji
    · simp at hyj; rw [abs_le]; omega
    · simp [hji] at hyj; rw [abs_le]; omega
  · have hxj : x j = y j + (Pi.single i (1 : ℤ) : Site d) j := by rw [h]; rfl
    rcases eq_or_ne j i with rfl | hji
    · simp at hxj; rw [abs_le]; omega
    · simp [hji] at hxj; rw [abs_le]; omega

/-- A neighbour of a site of `Λ_n` lies in `Λ_{n+1}`. [folklore] -/
theorem mem_box_succ_of_adj {n : ℕ} {x y : Site d} (hx : x ∈ box d n) (h : (zdGraph d).Adj x y) :
    y ∈ box d (n + 1) := by
  rw [mem_box] at hx ⊢
  intro i
  have h1 := abs_sub_le_one_of_adj h i
  have h2 := hx i
  rw [abs_le] at h1
  push_cast
  omega

/-- A site of `Λ_n` with a coordinate of absolute value `n` lies on `∂Λ_n` (move that coordinate
outwards). [folklore] -/
theorem mem_innerBoundary_box_of_natAbs_eq {n : ℕ} {x : Site d} (hx : x ∈ box d n) {i : Fin d}
    (hi : (x i).natAbs = n) : x ∈ innerBoundary (zdGraph d) (box d n) := by
  rw [mem_innerBoundary_iff]
  refine ⟨hx, ?_⟩
  rcases le_or_gt 0 (x i) with hpos | hneg
  · refine ⟨x + Pi.single i 1, ?_, (zdGraph_adj_iff _ _).2 ⟨i, Or.inl rfl⟩⟩
    rw [mem_box, not_forall]
    exact ⟨i, by simp; omega⟩
  · refine ⟨x - Pi.single i 1, ?_, (zdGraph_adj_iff _ _).2 ⟨i, Or.inr (by simp)⟩⟩
    rw [mem_box, not_forall]
    exact ⟨i, by simp; omega⟩

/-- A site of `∂Λ_n` has a coordinate of absolute value `n`. [folklore] -/
theorem exists_natAbs_eq_of_mem_innerBoundary_box {n : ℕ} {x : Site d}
    (hx : x ∈ innerBoundary (zdGraph d) (box d n)) : ∃ i, (x i).natAbs = n := by
  obtain ⟨i, hi | hi⟩ := exists_eq_of_mem_innerBoundary_box hx <;> exact ⟨i, by rw [hi]; simp⟩

/-- `∂Λ_n ∩ Λ_m = ∅` for `m < n`. [folklore] -/
theorem notMem_box_of_mem_innerBoundary_box {m n : ℕ} (hmn : m < n) {x : Site d}
    (hx : x ∈ innerBoundary (zdGraph d) (box d n)) : x ∉ box d m := by
  obtain ⟨i, hi⟩ := exists_natAbs_eq_of_mem_innerBoundary_box hx
  rw [mem_box, not_forall]
  exact ⟨i, by omega⟩

/-- A finite set of sites lies in some box. [folklore] -/
theorem exists_subset_box (S : Finset (Site d)) : ∃ n, S ⊆ box d n := by
  refine ⟨S.sup fun y => Finset.univ.sup fun i => (y i).natAbs, fun y hy => ?_⟩
  rw [mem_box]
  intro i
  have h1 : (y i).natAbs ≤ Finset.univ.sup fun i => (y i).natAbs :=
    Finset.le_sup (f := fun i => (y i).natAbs) (Finset.mem_univ i)
  have h2 : (Finset.univ.sup fun i => (y i).natAbs) ≤
      S.sup fun y => Finset.univ.sup fun i => (y i).natAbs :=
    Finset.le_sup (f := fun y : Site d => Finset.univ.sup fun i => (y i).natAbs) hy
  omega

/-- Translation is an automorphism of `ℤ^d`: `x - v ∼ y - v ↔ x ∼ y`. [folklore] -/
theorem zdGraph_adj_sub_iff (v x y : Site d) :
    (zdGraph d).Adj (x - v) (y - v) ↔ (zdGraph d).Adj x y := by
  simpa [sub_eq_add_neg] using zdGraph_adj_shift_iff (-v) x y

end Boxes

/-! ### The one-arm events `{v ⟷ v + ∂Λ_n in v + Λ_n}` -/

section Arm

variable {d : ℕ}

/-- `{0 ⟷ ∂Λ_n}` in terms of paths: `ω ∈ siteToBoundary d n` iff some site of `∂Λ_n` is reached
from `0` by an open path inside `Λ_n`. [cite: DuminilCopinTassionEM2016, §1 (Notation)] -/
theorem mem_siteToBoundary_iff {n : ℕ} {ω : BondConfig (Site d)} :
    ω ∈ siteToBoundary d n ↔
      ∃ y ∈ innerBoundary (zdGraph d) (box d n), PathIn (openGraph ω) ↑(box d n) 0 y := by
  simp only [siteToBoundary, Set.mem_setOf_eq, mem_openConnIn_iff_pathIn]

/-- `{0 ⟷ ∂Λ_n}` is increasing. (Grimmett 1999, §2.1.) [cite: GrimmettPercolation1999, §2.1] -/
theorem isUpperSet_siteToBoundary (d n : ℕ) : IsUpperSet (siteToBoundary d n) := by
  rintro ω ω' hle ⟨y, hy, hω⟩
  exact ⟨y, hy, isUpperSet_openConnIn _ _ _ hle hω⟩

/-- `{0 ⟷ ∂Λ_n}` is determined by the pairs inside `Λ_n`. [cite: GrimmettPercolation1999, §2.2] -/
theorem determinedBy_siteToBoundary (d n : ℕ) :
    DeterminedBy (siteToBoundary d n) (↑((box d n).sym2) : Set (Sym2 (Site d))) := by
  have h : siteToBoundary d n =
      ⋃ y ∈ innerBoundary (zdGraph d) (box d n), openConnIn (↑(box d n)) (0 : Site d) y := by
    ext ω; simp [siteToBoundary]
  rw [h]
  exact DeterminedBy.iUnion fun y => DeterminedBy.iUnion fun _ =>
    determinedBy_openConnIn (↑(box d n)) (0 : Site d) y (K := ↑(box d n).sym2)
      (by rw [Finset.coe_sym2])

/-- `{0 ⟷ ∂Λ_n}` is measurable. [cite: GrimmettPercolation1999, §2.2] -/
theorem measurableSet_siteToBoundary (d n : ℕ) : MeasurableSet (siteToBoundary d n) :=
  (determinedBy_siteToBoundary d n).measurableSet_of_finset

/-- `armEvent 0 n = {0 ⟷ ∂Λ_n}`. [folklore] -/
theorem armEvent_zero (d n : ℕ) : armEvent (0 : Site d) n = siteToBoundary d n := by
  ext ω
  simp only [armEvent, sub_zero, Set.mem_setOf_eq, Finset.setOf_mem, siteToBoundary]

/-- The translated arm event is the pull-back of `{0 ⟷ ∂Λ_n}` under the shift of configurations
by `-v`. [cite: GrimmettPercolation1999, §1.6 (translation invariance)] -/
theorem preimage_shift_siteToBoundary (v : Site d) (n : ℕ) :
    BondConfig.relabel (sym2Equiv (Site.shift (-v))) ⁻¹' siteToBoundary d n = armEvent v n := by
  ext ω
  simp only [Set.mem_preimage, mem_siteToBoundary_iff, armEvent, Set.mem_setOf_eq,
    mem_openConnIn_iff_pathIn]
  have hadj : ∀ a b : Site d,
      (openGraph (BondConfig.relabel (sym2Equiv (Site.shift (-v))) ω)).Adj (a - v) (b - v) ↔
        (openGraph ω).Adj a b := by
    intro a b
    have := openGraph_relabel_adj_iff (Site.shift (-v)) ω a b
    simpa [sub_eq_add_neg] using this
  constructor
  · rintro ⟨y, hy, hpath⟩
    refine ⟨y + v, by simpa using hy, ?_⟩
    have := pathIn_map (G' := openGraph ω) (fun z => z + v) (B := {z | z - v ∈ box d n})
      (fun a ha => by simp only [Set.mem_setOf_eq, add_sub_cancel_right]; exact ha)
      (fun a b _ _ hab => by rw [← hadj]; simpa using hab) hpath
    simpa using this
  · rintro ⟨a, ha, hpath⟩
    refine ⟨a - v, ha, ?_⟩
    have := pathIn_map (G' := openGraph (BondConfig.relabel (sym2Equiv (Site.shift (-v))) ω))
      (fun z => z - v) (B := (↑(box d n) : Set (Site d)))
      (fun a ha => by simpa using ha) (fun a b _ _ hab => (hadj a b).2 hab) hpath
    simpa using this

/-- **Translation invariance of the one-arm probability**: `P_p(v ⟷ v + ∂Λ_n in v + Λ_n) =
P_p(0 ⟷ ∂Λ_n)`. (Grimmett 1999, §1.6; Duminil-Copin–Tassion 2016, §2.1.) [cite: GrimmettPercolation1999, §1.6] -/
theorem real_armEvent (p : unitInterval) (v : Site d) (n : ℕ) :
    (bondPercolation (zdGraph d) p).real (armEvent v n) =
      (bondPercolation (zdGraph d) p).real (siteToBoundary d n) := by
  rw [← preimage_shift_siteToBoundary, bondPercolation_real_preimage_shift]

/-- **First exit produces an arm.** If `ω ⊆ E(ℤ^d)` and an open path inside some set runs from `v`
to a site `z` which is not in the interior of `v + Λ_m` (i.e. `z - v ∉ Λ_m` or `z - v ∈ ∂Λ_m`),
then `ω ∈ armEvent v m`: stop the path at its first exit from `v + Λ_m`
(Duminil-Copin–Tassion 2016, §2.1, the bound `P_p[y ⟷ ∂Λ_{kL}] ≤ P_p[0 ⟷ ∂Λ_{(k-1)L}]`).
[cite: DuminilCopinTassionEM2016, §2.1] -/
theorem armEvent_of_pathIn {ω : BondConfig (Site d)} (hω : ω ⊆ (zdGraph d).edgeSet)
    {A : Set (Site d)} {v z : Site d} {m : ℕ} (h : PathIn (openGraph ω) A v z)
    (hz : z - v ∉ box d m ∨ z - v ∈ innerBoundary (zdGraph d) (box d m)) :
    ω ∈ armEvent v m := by
  have hv : v ∈ {w : Site d | w - v ∈ box d m} := by simp
  -- the exit case, common to both alternatives
  have hexit : ∀ a b, a ∈ {w : Site d | w - v ∈ box d m} → b ∉ {w : Site d | w - v ∈ box d m} →
      (openGraph ω).Adj a b → PathIn (openGraph ω) ({w | w - v ∈ box d m} ∩ A) v a →
      ω ∈ armEvent v m := by
    intro a b ha hb hab hpa
    refine ⟨a, mem_innerBoundary_iff.2 ⟨ha, b - v, hb, ?_⟩,
      mem_openConnIn_of_pathIn (hpa.mono Set.inter_subset_left)⟩
    rw [zdGraph_adj_sub_iff]
    exact adj_of_openGraph_adj hω hab
  rcases hz with hz | hz
  · obtain ⟨a, b, ha, hb, -, hab, hpa⟩ := h.exit hv hz
    exact hexit a b ha hb hab hpa
  · rcases h.exit_or hv with h' | ⟨a, b, ha, hb, -, hab, hpa⟩
    · exact ⟨z, hz, mem_openConnIn_of_pathIn (h'.mono Set.inter_subset_left)⟩
    · exact hexit a b ha hb hab hpa

/-- **`n ↦ P_p[0 ⟷ ∂Λ_n]` is non-increasing**: for `m ≤ n`, an open path from `0` to `∂Λ_n`
passes through `∂Λ_m` (first exit from `Λ_m`; valid for `ω ⊆ E(ℤ^d)`, i.e. almost surely).
(Duminil-Copin–Tassion 2016, §2.1, "`P_p[0 ⟷ ∂Λ_n] ≤ P_p[0 ⟷ ∂Λ_{kL}]` for `n ≥ kL`", implicit in
"this proves the desired exponential decay".) [cite: DuminilCopinTassionEM2016, §2.1] -/
theorem real_siteToBoundary_antitone (p : unitInterval) {m n : ℕ} (hmn : m ≤ n) :
    (bondPercolation (zdGraph d) p).real (siteToBoundary d n) ≤
      (bondPercolation (zdGraph d) p).real (siteToBoundary d m) := by
  refine real_mono_of_forall_subset_edgeSet (zdGraph d) p fun ω hω h => ?_
  rw [← armEvent_zero]
  rw [mem_siteToBoundary_iff] at h
  obtain ⟨y, hy, hpath⟩ := h
  refine armEvent_of_pathIn hω hpath ?_
  rcases hmn.lt_or_eq with hlt | rfl
  · exact Or.inl (by rw [sub_zero]; exact notMem_box_of_mem_innerBoundary_box hlt hy)
  · exact Or.inr (by rw [sub_zero]; exact hy)

/-- **`⋂ₙ {0 ⟷ ∂Λ_n} ⊆ {|C(0)| = ∞}`**: if `0` is joined to sites of every sphere `∂Λ_n`, its
cluster is unbounded, hence infinite. (Grimmett 1999, §1.4, `θ(p) = lim P_p(0 ⟷ ∂B(n))`.)
[cite: GrimmettPercolation1999, §1.4] -/
theorem iInter_siteToBoundary_subset_percolatesAt (d : ℕ) :
    ⋂ n, siteToBoundary d n ⊆ percolatesAt (0 : Site d) := by
  intro ω hω
  rw [Set.mem_iInter] at hω
  intro hfin
  -- the finite cluster lies in some box
  obtain ⟨N, hN⟩ := exists_subset_box hfin.toFinset
  obtain ⟨y, hy, hpath⟩ := mem_siteToBoundary_iff.1 (hω (N + 1))
  have hyC : y ∈ openCluster ω 0 := reachable_of_pathIn hpath
  exact notMem_box_of_mem_innerBoundary_box (Nat.lt_succ_self N) hy (hN (hfin.mem_toFinset.2 hyC))

/-- If all edges at `0` are closed (and `ω ⊆ E(ℤ^d)`), `0` is not joined to `∂Λ_1`: an open path
from `0` to a site of `∂Λ_1 ∌ 0` would start with an open edge at `0`. [folklore] -/
theorem not_mem_siteToBoundary_one {ω : BondConfig (Site d)} (hω : ω ⊆ (zdGraph d).edgeSet)
    (hcl : ∀ u ∈ (zdGraph d).neighborFinset 0, s((0 : Site d), u) ∉ ω) :
    ω ∉ siteToBoundary d 1 := by
  rw [mem_siteToBoundary_iff]
  rintro ⟨y, hy, hpath⟩
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact notMem_box_of_mem_innerBoundary_box Nat.zero_lt_one hy (zero_mem_box d 0)
  refine hy0 (pathIn_induction (fun z => z = (0 : Site d)) hpath rfl ?_)
  rintro a b - - rfl hab
  have h1 : s((0 : Site d), b) ∈ ω := ((openGraph_adj ω 0 b).1 hab).1
  have h2 : b ∈ (zdGraph d).neighborFinset 0 := by simpa using adj_of_openGraph_adj hω hab
  exact absurd h1 (hcl b h2)

/-- **`P_p[0 ⟷ ∂Λ_1] ≤ 1 - (1 - p)^{2d} < 1` for `p < 1`**: with probability at least
`(1-p)^{deg 0}` all edges at the origin are closed (`le_bondPercolation_real_forall_notMem`,
`FiniteEnergy.lean`). (Needed to start the exponential decay of Duminil-Copin–Tassion 2016, §2.1,
at `n = 1`.) [folklore] -/
theorem real_siteToBoundary_one_lt_one (p : unitInterval) (hp : (p : ℝ) < 1) :
    (bondPercolation (zdGraph d) p).real (siteToBoundary d 1) < 1 := by
  classical
  set K : Finset (Sym2 (Site d)) := ((zdGraph d).neighborFinset 0).image fun u => s((0 : Site d), u)
    with hK
  have hle : (bondPercolation (zdGraph d) p).real (siteToBoundary d 1) ≤
      (bondPercolation (zdGraph d) p).real {ω | ∀ e ∈ K, e ∉ ω}ᶜ := by
    refine real_mono_of_forall_subset_edgeSet (zdGraph d) p fun ω hω h => ?_
    rw [Set.mem_compl_iff, Set.mem_setOf_eq]
    intro hcl
    refine not_mem_siteToBoundary_one hω (fun u hu => hcl _ ?_) h
    rw [hK, Finset.mem_image]
    exact ⟨u, hu, rfl⟩
  rw [measureReal_compl (measurableSet_forall_notMem K), probReal_univ] at hle
  have hpos : (0 : ℝ) < (1 - p) ^ K.card := pow_pos (by linarith) _
  have hge := le_bondPercolation_real_forall_notMem (zdGraph d) p K
  linarith

/-- **Passage to the limit `n → ∞`**: if `c ≤ P_p[0 ⟷ ∂Λ_n]` for all `n`, then `c ≤ θ(p)`, since
`{|C(0)| = ∞} ⊇ ⋂ₙ {0 ⟷ ∂Λ_n}` and, the events being (a.s.) non-increasing in `n`,
`P_p(⋂ₙ {0 ⟷ ∂Λ_n}) = infₙ P_p[0 ⟷ ∂Λ_n]` (continuity of the measure from above).
(Duminil-Copin–Tassion 2016, §2.2: "by letting `n` tend to infinity"; Grimmett 1999, §1.4.)
[cite: DuminilCopinTassionEM2016, §2.2] -/
theorem le_theta_of_forall_le_real_siteToBoundary (p : unitInterval) {c : ℝ}
    (h : ∀ n, c ≤ (bondPercolation (zdGraph d) p).real (siteToBoundary d n)) :
    c ≤ theta (zdGraph d) 0 p := by
  set μ := bondPercolation (zdGraph d) p with hμ
  have hmeas : ∀ n, NullMeasurableSet (siteToBoundary d n) μ :=
    fun n => (measurableSet_siteToBoundary d n).nullMeasurableSet
  -- `μ (⋂ n, A n) = ⨅ i, μ (⋂ j ≤ i, A j)` and each term is at least `μ (A i) ≥ c`
  have hkey : ENNReal.ofReal c ≤ μ (⋂ n, siteToBoundary d n) := by
    rw [measure_iInter_eq_iInf_measure_iInter_le hmeas ⟨0, measure_ne_top _ _⟩]
    refine le_iInf fun i => ?_
    calc ENNReal.ofReal c ≤ μ (siteToBoundary d i) := by
          rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
          exact ENNReal.ofReal_le_ofReal (h i)
      _ ≤ μ (⋂ j ≤ i, siteToBoundary d j) := by
          -- first exit from `Λ_j`, `j ≤ i`, valid for `ω ⊆ E(ℤ^d)`
          have hsub : ∀ ω : BondConfig (Site d), ω ⊆ (zdGraph d).edgeSet →
              ω ∈ siteToBoundary d i → ω ∈ ⋂ j ≤ i, siteToBoundary d j := by
            intro ω hω hωi
            simp only [Set.mem_iInter]
            intro j hj
            rw [← armEvent_zero] at hωi ⊢
            obtain ⟨y, hy, hpath⟩ := hωi
            rw [sub_zero] at hy
            refine armEvent_of_pathIn hω (pathIn_of_mem_openConnIn hpath) ?_
            rcases hj.lt_or_eq with hlt | rfl
            · exact Or.inl (by rw [sub_zero]; exact notMem_box_of_mem_innerBoundary_box hlt hy)
            · exact Or.inr (by rw [sub_zero]; exact hy)
          refine measure_mono_ae ?_
          filter_upwards [(setBernoulli_ae_subset :
            ∀ᵐ ω ∂bondPercolation (zdGraph d) p, ω ⊆ (zdGraph d).edgeSet)] with ω hω using hsub ω hω
  have hle : μ (⋂ n, siteToBoundary d n) ≤ μ (percolatesAt 0) :=
    measure_mono (iInter_siteToBoundary_subset_percolatesAt d)
  rw [theta, ← hμ, measureReal_def, ← ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)]
  exact hkey.trans hle

end Arm

/-! ## Part II. The exploration argument (§2.1): discharge of `DCT16_expDecay_of_phi_lt_one` -/

variable {d : ℕ}

/-! ### The cluster of the origin inside `S` and the three events of the decomposition -/

section Events

/-- Membership in `𝒞(ω)` in terms of open paths inside `S`. [cite: DuminilCopinTassionEM2016, §2.1] -/
theorem mem_clusterSet_iff {S : Finset (Site d)} {ω : BondConfig (Site d)} {z : Site d} :
    z ∈ clusterSet S ω ↔ PathIn (openGraph ω) ↑S 0 z := by
  rw [clusterSet, Set.mem_setOf_eq, mem_openConnIn_iff_pathIn]

/-- `𝒞(ω) ⊆ S`. [folklore] -/
theorem clusterSet_subset (S : Finset (Site d)) (ω : BondConfig (Site d)) :
    clusterSet S ω ⊆ ↑S := fun _ hz => (mem_clusterSet_iff.1 hz).right_mem

/-- `𝒞(ω)` is the coercion of the finset `{z ∈ S | z ∈ 𝒞(ω)}`. [folklore] -/
theorem coe_filter_clusterSet (S : Finset (Site d)) (ω : BondConfig (Site d))
    [DecidablePred (· ∈ clusterSet S ω)] :
    (↑(S.filter (· ∈ clusterSet S ω)) : Set (Site d)) = clusterSet S ω := by
  ext z
  simp only [Finset.coe_filter, Set.mem_setOf_eq, and_iff_right_iff_imp]
  exact fun hz => clusterSet_subset S ω hz

/-- A pair of sites of `S` one of which lies in `C` belongs to `clusterPairs S C`. [folklore] -/
theorem mk_mem_clusterPairs {S C : Finset (Site d)} {a b : Site d} (ha : a ∈ S) (hb : b ∈ S)
    (h : a ∈ C ∨ b ∈ C) : s(a, b) ∈ clusterPairs S C := by
  simp only [clusterPairs, Finset.mem_sdiff, Finset.mk_mem_sym2_iff]
  refine ⟨⟨ha, hb⟩, ?_⟩
  rintro ⟨⟨-, hac⟩, ⟨-, hbc⟩⟩
  exact h.elim hac hbc

/-- A path stays inside the cluster of its starting point. [folklore] -/
theorem pathIn_restrict_cluster {V : Type*} {G : SimpleGraph V} {A : Set V} {u v : V}
    (h : PathIn G A u v) : PathIn G (A ∩ {z | PathIn G A u z}) u v := by
  obtain ⟨hu, hr⟩ := h
  refine ⟨⟨hu, PathIn.refl hu⟩, ?_⟩
  induction hr with
  | refl => exact Relation.ReflTransGen.refl
  | tail hub hbc ih => exact ih.tail ⟨hbc.1, hbc.2, ⟨hu, hub.tail hbc⟩⟩

/-- **`{𝒞 = C}` is determined by the pairs inside `S` touching `C`** (for `0 ∈ S`, `C ⊆ S`):
if `𝒞(ω) = C` then the open paths from `0` inside `S` use only edges inside `C`, and the edges from
`C` to `S ∖ C` decide whether the cluster grows; both kinds of pairs touch `C`.
(Duminil-Copin–Tassion 2016, §2.1: the events "depend on different sets of edges".)
[cite: DuminilCopinTassionEM2016, §2.1] -/
theorem determinedBy_clusterEvent {S C : Finset (Site d)} (h0 : (0 : Site d) ∈ S) :
    DeterminedBy (clusterEvent S C) (↑(clusterPairs S C) : Set (Sym2 (Site d))) := by
  rw [determinedBy_iff]
  suffices key : ∀ ω ω' : BondConfig (Site d),
      ω ∩ ↑(clusterPairs S C) = ω' ∩ ↑(clusterPairs S C) →
        ω ∈ clusterEvent S C → ω' ∈ clusterEvent S C from
    fun ω ω' h => ⟨key ω ω' h, key ω' ω h.symm⟩
  intro ω ω' hag hC
  simp only [clusterEvent, Set.mem_setOf_eq] at hC ⊢
  ext z
  constructor
  · -- a path of `ω'` inside `S` from `0` stays in `C`
    intro hz
    rw [mem_clusterSet_iff] at hz
    refine pathIn_induction (fun w => w ∈ (↑C : Set (Site d))) hz ?_ ?_
    · rw [← hC, mem_clusterSet_iff]; exact PathIn.refl h0
    · intro a b haS hbS haC hab
      have haC' : a ∈ C := haC
      have hab' : (openGraph ω).Adj a b :=
        (openGraph_adj_congr hag (Finset.mem_coe.2 (mk_mem_clusterPairs haS hbS (Or.inl haC')))).2
          hab
      have ha : a ∈ clusterSet S ω := by rw [hC]; exact haC
      rw [mem_clusterSet_iff] at ha
      have hb : b ∈ clusterSet S ω := mem_clusterSet_iff.2 (ha.tail hab' hbS)
      rwa [hC] at hb
  · -- a path of `ω` inside `𝒞(ω) = C` is a path of `ω'`
    intro hz
    rw [← hC, mem_clusterSet_iff] at hz
    rw [mem_clusterSet_iff]
    have hz' := pathIn_restrict_cluster hz
    refine (pathIn_congrGraph (G' := openGraph ω') ?_ hz').mono Set.inter_subset_left
    intro a b ha hb hab
    have haC : a ∈ C := by
      have : a ∈ clusterSet S ω := mem_clusterSet_iff.2 ha.2
      rw [hC] at this; exact this
    exact (openGraph_adj_congr hag (Finset.mem_coe.2 (mk_mem_clusterPairs ha.1 hb.1 (Or.inl haC)))).1
      hab

/-- `{𝒞 = C}` is measurable. [folklore] -/
theorem measurableSet_clusterEvent {S C : Finset (Site d)} (h0 : (0 : Site d) ∈ S) :
    MeasurableSet (clusterEvent S C) :=
  (determinedBy_clusterEvent (C := C) h0).measurableSet_of_finset

/-- `{y ⟷ ∂Λ_N in Λ_N ∖ C}` is determined by the pairs inside `Λ_N ∖ C`. [cite: DuminilCopinTassionEM2016, §2.1] -/
theorem determinedBy_exitEvent (N : ℕ) (C : Finset (Site d)) (y : Site d) :
    DeterminedBy (exitEvent N C y) (↑((box d N \ C).sym2) : Set (Sym2 (Site d))) := by
  have h : exitEvent N C y = ⋃ z ∈ innerBoundary (zdGraph d) (box d N),
      openConnIn ((↑(box d N) : Set (Site d)) \ ↑C) y z := by
    ext ω; simp [exitEvent]
  rw [h]
  refine DeterminedBy.iUnion fun z => DeterminedBy.iUnion fun _ => determinedBy_openConnIn _ y z ?_
  rw [Finset.coe_sym2, Finset.coe_sdiff]

/-- For `ω ⊆ E(ℤ^d)` and `y ∈ Λ_{L+1}`, the event `{y ⟷ ∂Λ_{m+L+1} in Λ_{m+L+1} ∖ C}` forces the
translated arm event `{y ⟷ y + ∂Λ_m in y + Λ_m}`: a site of `∂Λ_{m+L+1}` is not in the interior of
`y + Λ_m` (Duminil-Copin–Tassion 2016, §2.1, "since `y ∈ Λ_L`, one can bound
`P_p[y ⟷ ∂Λ_{kL} off 𝒞]` by `P_p[0 ⟷ ∂Λ_{(k-1)L}]`"). [cite: DuminilCopinTassionEM2016, §2.1] -/
theorem armEvent_of_mem_exitEvent {m L : ℕ} {C : Finset (Site d)} {y : Site d}
    (hy : y ∈ box d (L + 1)) {ω : BondConfig (Site d)} (hω : ω ⊆ (zdGraph d).edgeSet)
    (h : ω ∈ exitEvent (m + L + 1) C y) : ω ∈ armEvent y m := by
  obtain ⟨z, hz, hpath⟩ := h
  rw [mem_openConnIn_iff_pathIn] at hpath
  refine armEvent_of_pathIn hω hpath ?_
  by_cases hzy : z - y ∈ box d m
  · right
    obtain ⟨i, hi⟩ := exists_natAbs_eq_of_mem_innerBoundary_box hz
    refine mem_innerBoundary_box_of_natAbs_eq hzy (i := i) ?_
    have h1 := (mem_box.1 hy) i
    have h2 := (mem_box.1 hzy) i
    simp only [Pi.sub_apply] at h2 ⊢
    omega
  · exact Or.inl hzy

end Events

/-! ### The decomposition of `{0 ⟷ ∂Λ_N}` along the last visit to `𝒞` -/

section Decomposition

open Classical in
/-- **The exploration step** (Duminil-Copin–Tassion 2016, §2.1). Let `0 ∈ S ⊆ Λ_L`, `L < N`,
`ω ⊆ E(ℤ^d)` and `0 ⟷ ∂Λ_N`. Then there are `x ∈ S`, a neighbour `y ∉ S` of `x` and `C ⊆ S`
containing `x` such that `𝒞(ω) = C`, `{x, y}` is open and `y ⟷ ∂Λ_N in Λ_N ∖ C`: follow an open
path from `0` to `∂Λ_N` (which avoids `S`, as `S ∩ ∂Λ_N = ∅`) up to its last visit `x` to `𝒞(ω)`.
[cite: DuminilCopinTassionEM2016, §2.1] -/
theorem exists_decomposition {S : Finset (Site d)} (h0 : (0 : Site d) ∈ S) {L N : ℕ}
    (hSL : S ⊆ box d L) (hLN : L < N) {ω : BondConfig (Site d)}
    (hω : ω ⊆ (zdGraph d).edgeSet) (hωN : ω ∈ siteToBoundary d N) :
    ∃ x ∈ S, ∃ y ∈ (zdGraph d).neighborFinset x, y ∉ S ∧ ∃ C ∈ S.powerset, x ∈ C ∧
      ω ∈ clusterEvent S C ∧ s(x, y) ∈ ω ∧ ω ∈ exitEvent N C y := by
  rw [mem_siteToBoundary_iff] at hωN
  obtain ⟨z, hz, hpath⟩ := hωN
  have h0cl : (0 : Site d) ∈ clusterSet S ω := mem_clusterSet_iff.2 (PathIn.refl h0)
  have hzS : z ∉ S := fun hzS => notMem_box_of_mem_innerBoundary_box hLN hz (hSL hzS)
  have hzcl : z ∉ clusterSet S ω := fun hzcl => hzS (clusterSet_subset S ω hzcl)
  obtain ⟨a, b, hacl, -, hbcl, hab, hpath'⟩ := hpath.last_exit h0cl hzcl
  have haS : a ∈ S := clusterSet_subset S ω hacl
  have hbS : b ∉ S := fun hbS =>
    hbcl (mem_clusterSet_iff.2 ((mem_clusterSet_iff.1 hacl).tail hab hbS))
  set C : Finset (Site d) := S.filter (· ∈ clusterSet S ω) with hCdef
  have hC : clusterSet S ω = ↑C := (coe_filter_clusterSet S ω).symm
  refine ⟨a, haS, b, ?_, hbS, C, ?_, ?_, hC, ((openGraph_adj ω a b).1 hab).1, z, hz, ?_⟩
  · simpa using adj_of_openGraph_adj hω hab
  · exact Finset.mem_powerset.2 (Finset.filter_subset _ _)
  · exact Finset.mem_filter.2 ⟨haS, hacl⟩
  · rw [mem_openConnIn_iff_pathIn, ← hC]
    exact hpath'

/-- **Union bound over the decomposition** (Duminil-Copin–Tassion 2016, §2.1, "using first the
union bound, and then a decomposition with respect to possible values of `𝒞`"): for
`0 ∈ S ⊆ Λ_L`, `L < N`,
`P_p[0 ⟷ ∂Λ_N] ≤ Σ_{x ∈ S} Σ_{y ∼ x, y ∉ S} Σ_{x ∈ C ⊆ S} P_p[{𝒞 = C} ∩ {xy open} ∩ {y ⟷ ∂Λ_N in Λ_N ∖ C}]`.
[cite: DuminilCopinTassionEM2016, §2.1] -/
theorem real_siteToBoundary_le_sum (p : unitInterval) {S : Finset (Site d)} (h0 : (0 : Site d) ∈ S)
    {L N : ℕ} (hSL : S ⊆ box d L) (hLN : L < N) :
    (bondPercolation (zdGraph d) p).real (siteToBoundary d N) ≤
      ∑ x ∈ S, ∑ y ∈ (zdGraph d).neighborFinset x with y ∉ S, ∑ C ∈ S.powerset with x ∈ C,
        (bondPercolation (zdGraph d) p).real
          (clusterEvent S C ∩ {ω | s(x, y) ∈ ω} ∩ exitEvent N C y) := by
  set μ := bondPercolation (zdGraph d) p with hμ
  calc μ.real (siteToBoundary d N)
      ≤ μ.real (⋃ x ∈ S, ⋃ y ∈ ((zdGraph d).neighborFinset x).filter (· ∉ S),
          ⋃ C ∈ S.powerset.filter (x ∈ ·),
            (clusterEvent S C ∩ {ω | s(x, y) ∈ ω} ∩ exitEvent N C y)) := by
        refine real_mono_of_forall_subset_edgeSet (zdGraph d) p fun ω hω hωN => ?_
        obtain ⟨x, hx, y, hy, hyS, C, hC, hxC, h1, h2, h3⟩ :=
          exists_decomposition h0 hSL hLN hω hωN
        simp only [Set.mem_iUnion, Finset.mem_filter, exists_prop]
        exact ⟨x, hx, y, ⟨hy, hyS⟩, C, ⟨hC, hxC⟩, ⟨h1, h2⟩, h3⟩
    _ ≤ ∑ x ∈ S, μ.real (⋃ y ∈ ((zdGraph d).neighborFinset x).filter (· ∉ S),
          ⋃ C ∈ S.powerset.filter (x ∈ ·),
            (clusterEvent S C ∩ {ω | s(x, y) ∈ ω} ∩ exitEvent N C y)) :=
        measureReal_biUnion_finset_le _ _
    _ ≤ ∑ x ∈ S, ∑ y ∈ (zdGraph d).neighborFinset x with y ∉ S, μ.real
          (⋃ C ∈ S.powerset.filter (x ∈ ·),
            (clusterEvent S C ∩ {ω | s(x, y) ∈ ω} ∩ exitEvent N C y)) :=
        Finset.sum_le_sum fun x _ => measureReal_biUnion_finset_le _ _
    _ ≤ _ := Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
        measureReal_biUnion_finset_le _ _

/-- **Independence of the three events** (Duminil-Copin–Tassion 2016, §2.1: "the three events
depend on different sets of edges and are therefore independent"): for `x ∈ C ⊆ S ∌ y`, `x ∼ y`,
`P_p[{𝒞 = C} ∩ {xy open} ∩ {y ⟷ ∂Λ_N in Λ_N ∖ C}] = P_p[𝒞 = C] · p · P_p[y ⟷ ∂Λ_N in Λ_N ∖ C]`.
[cite: DuminilCopinTassionEM2016, §2.1] -/
theorem real_inter_three (p : unitInterval) {S C : Finset (Site d)} (h0 : (0 : Site d) ∈ S)
    {x y : Site d} (hxC : x ∈ C) (hyS : y ∉ S) (hxy : (zdGraph d).Adj x y) (N : ℕ) :
    (bondPercolation (zdGraph d) p).real (clusterEvent S C ∩ {ω | s(x, y) ∈ ω} ∩ exitEvent N C y) =
      (bondPercolation (zdGraph d) p).real (clusterEvent S C) * p *
        (bondPercolation (zdGraph d) p).real (exitEvent N C y) := by
  classical
  have hE : s(x, y) ∈ (zdGraph d).edgeSet := hxy
  -- determining sets
  have hA : DeterminedBy (clusterEvent S C) ↑(clusterPairs S C) := determinedBy_clusterEvent h0
  have hB : DeterminedBy {ω : BondConfig (Site d) | s(x, y) ∈ ω} ↑({s(x, y)} : Finset _) := by
    rw [Finset.coe_singleton]; exact determinedBy_mem _
  have hAB : DeterminedBy (clusterEvent S C ∩ {ω | s(x, y) ∈ ω})
      ↑(clusterPairs S C ∪ {s(x, y)}) := by
    rw [Finset.coe_union]
    exact (hA.mono Set.subset_union_left).inter (hB.mono Set.subset_union_right)
  have hD : DeterminedBy (exitEvent N C y) ↑((box d N \ C).sym2) := determinedBy_exitEvent N C y
  -- disjointness
  have hdisj1 : Disjoint (clusterPairs S C) {s(x, y)} := by
    rw [Finset.disjoint_singleton_right]
    intro h
    simp only [clusterPairs, Finset.mem_sdiff, Finset.mk_mem_sym2_iff] at h
    exact hyS h.1.2
  have hdisj2 : Disjoint (clusterPairs S C ∪ {s(x, y)}) ((box d N \ C).sym2) := by
    rw [Finset.disjoint_left]
    rintro e he he'
    rcases Finset.mem_union.1 he with he | he
    · induction e using Sym2.ind with
      | h a b =>
        obtain ⟨he1, he2⟩ := Finset.mem_sdiff.1 he
        rw [Finset.mk_mem_sym2_iff] at he1 he2
        obtain ⟨ha', hb'⟩ := Finset.mk_mem_sym2_iff.1 he'
        rw [Finset.mem_sdiff] at ha' hb'
        exact he2 ⟨Finset.mem_sdiff.2 ⟨he1.1, ha'.2⟩, Finset.mem_sdiff.2 ⟨he1.2, hb'.2⟩⟩
    · rw [Finset.mem_singleton] at he
      subst he
      simp only [Finset.mk_mem_sym2_iff, Finset.mem_sdiff] at he'
      exact he'.1.2 hxC
  rw [real_inter_of_determinedBy_disjoint (zdGraph d) p hAB hD hdisj2,
    real_inter_of_determinedBy_disjoint (zdGraph d) p hA hB hdisj1,
    bondPercolation_cylinder (zdGraph d) p hE]

open Classical in
/-- **Resummation over the values of `𝒞`**: `Σ_{C ⊆ S, x ∈ C} P_p[𝒞 = C] = P_p[0 ⟷ x in S]`
(the events `{𝒞 = C}` partition `{x ∈ 𝒞} = {0 ⟷ x in S}`). (Duminil-Copin–Tassion 2016, §2.1,
passage from the decomposed sum to `φ_p(S)`.) [cite: DuminilCopinTassionEM2016, §2.1] -/
theorem sum_real_clusterEvent (p : unitInterval) {S : Finset (Site d)} (h0 : (0 : Site d) ∈ S)
    {x : Site d} (hx : x ∈ S) :
    ∑ C ∈ S.powerset with x ∈ C, (bondPercolation (zdGraph d) p).real (clusterEvent S C) =
      (bondPercolation (zdGraph d) p).real (openConnIn (↑S : Set (Site d)) 0 x) := by
  have hunion : openConnIn (↑S : Set (Site d)) 0 x =
      ⋃ C ∈ S.powerset.filter (fun C => x ∈ C), clusterEvent S C := by
    ext ω
    simp only [Set.mem_iUnion, Finset.mem_filter, Finset.mem_powerset, exists_prop]
    constructor
    · intro hω
      refine ⟨S.filter (· ∈ clusterSet S ω), ⟨Finset.filter_subset _ _, ?_⟩,
        (coe_filter_clusterSet S ω).symm⟩
      exact Finset.mem_filter.2 ⟨hx, hω⟩
    · rintro ⟨C, ⟨-, hxC⟩, hC⟩
      have : x ∈ clusterSet S ω := by
        rw [show clusterSet S ω = ↑C from hC]; exact hxC
      exact this
  rw [hunion, measureReal_biUnion_finset]
  · intro C _ C' _ hCC'
    refine Set.disjoint_left.2 fun ω h h' => hCC' ?_
    exact Finset.coe_injective (h.symm.trans h')
  · intro C _
    exact measurableSet_clusterEvent h0

end Decomposition

/-! ### The one-step inequality and its iteration -/

section Iterate

/-- **One step** (Duminil-Copin–Tassion 2016, §2.1): for `0 ∈ S ⊆ Λ_L` and every `m`,
`P_p[0 ⟷ ∂Λ_{m+L+1}] ≤ φ_p(S) · P_p[0 ⟷ ∂Λ_m]` (the printed `P_p[0 ⟷ ∂Λ_{kL'}] ≤ φ_p(S)
P_p[0 ⟷ ∂Λ_{(k-1)L'}]` with `L' = L + 1`, `S ⊆ Λ_{L'-1}`). [cite: DuminilCopinTassionEM2016, §2.1] -/
theorem real_siteToBoundary_le_phi_mul (p : unitInterval) {S : Finset (Site d)}
    (h0 : (0 : Site d) ∈ S) {L : ℕ} (hSL : S ⊆ box d L) (m : ℕ) :
    (bondPercolation (zdGraph d) p).real (siteToBoundary d (m + L + 1)) ≤
      DCT16.phi p S * (bondPercolation (zdGraph d) p).real (siteToBoundary d m) := by
  set μ := bondPercolation (zdGraph d) p with hμ
  set a := μ.real (siteToBoundary d m) with ha
  have hLN : L < m + L + 1 := by omega
  refine (real_siteToBoundary_le_sum p h0 hSL hLN).trans ?_
  -- termwise: independence, `P(xy open) = p`, and the translated arm bound
  have hterm : ∀ x ∈ S, ∀ y ∈ ((zdGraph d).neighborFinset x).filter (· ∉ S),
      ∀ C ∈ S.powerset.filter (x ∈ ·), μ.real (clusterEvent S C ∩ {ω | s(x, y) ∈ ω} ∩ exitEvent (m + L + 1) C y) ≤
        μ.real (clusterEvent S C) * (p * a) := by
    intro x hx y hy C hC
    rw [Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hy
    rw [Finset.mem_filter] at hC
    rw [hμ, real_inter_three p h0 hC.2 hy.2 hy.1, mul_assoc]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ p.2.1) measureReal_nonneg
    rw [ha, hμ, ← real_armEvent p y m]
    have hyL : y ∈ box d (L + 1) := mem_box_succ_of_adj (hSL hx) hy.1
    exact real_mono_of_forall_subset_edgeSet (zdGraph d) p fun ω hω h =>
      armEvent_of_mem_exitEvent hyL hω h
  calc ∑ x ∈ S, ∑ y ∈ (zdGraph d).neighborFinset x with y ∉ S, ∑ C ∈ S.powerset with x ∈ C,
        μ.real (clusterEvent S C ∩ {ω | s(x, y) ∈ ω} ∩ exitEvent (m + L + 1) C y)
      ≤ ∑ x ∈ S, ∑ y ∈ (zdGraph d).neighborFinset x with y ∉ S, ∑ C ∈ S.powerset with x ∈ C,
        μ.real (clusterEvent S C) * (p * a) :=
        Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun y hy =>
          Finset.sum_le_sum fun C hC => hterm x hx y hy C hC
    _ = ∑ x ∈ S, ∑ y ∈ (zdGraph d).neighborFinset x with y ∉ S,
        μ.real (openConnIn (↑S : Set (Site d)) 0 x) * (p * a) := by
        refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y _ => ?_
        rw [← Finset.sum_mul, sum_real_clusterEvent p h0 hx]
    _ = DCT16.phi p S * a := by
        rw [DCT16.phi_def]
        simp only [← Finset.sum_mul]
        ring

/-- **Iteration** (Duminil-Copin–Tassion 2016, §2.1, "which by induction gives
`P_p[0 ⟷ ∂Λ_{kL}] ≤ φ_p(S)^{k-1}`"): for `0 ∈ S ⊆ Λ_L`, `P_p[0 ⟷ ∂Λ_{k(L+1)}] ≤ φ_p(S)^k`.
[cite: DuminilCopinTassionEM2016, §2.1] -/
theorem real_siteToBoundary_mul_le_pow (p : unitInterval) {S : Finset (Site d)}
    (h0 : (0 : Site d) ∈ S) {L : ℕ} (hSL : S ⊆ box d L) (k : ℕ) :
    (bondPercolation (zdGraph d) p).real (siteToBoundary d (k * (L + 1))) ≤ DCT16.phi p S ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := real_siteToBoundary_le_phi_mul p h0 hSL (k * (L + 1))
    rw [show k * (L + 1) + L + 1 = (k + 1) * (L + 1) by ring] at h
    refine h.trans ?_
    rw [pow_succ']
    exact mul_le_mul_of_nonneg_left ih (DCT16.phi_nonneg p S)

end Iterate

/-! ### Exponential decay -/

section Decay

/-- Elementary: `n ≤ 2 (L+1) max(1, ⌊n/(L+1)⌋)`. [folklore] -/
theorem le_two_mul_max_div (n L : ℕ) : n ≤ 2 * (L + 1) * max 1 (n / (L + 1)) := by
  set q := n / (L + 1) with hq
  have h1 : n < q * (L + 1) + (L + 1) := Nat.lt_div_mul_add (Nat.succ_pos L)
  rcases Nat.eq_zero_or_pos q with hq0 | hqpos
  · rw [hq0] at h1 ⊢
    rw [show max 1 0 = 1 from rfl]
    omega
  · have hmax : max 1 q = q := max_eq_right hqpos
    rw [hmax]
    have : L + 1 ≤ q * (L + 1) := Nat.le_mul_of_pos_left (L + 1) hqpos
    nlinarith

/-- **Discharge of `DCT16_expDecay_of_phi_lt_one`** (Duminil-Copin–Tassion 2016, §2.1, proof of
item 1 of Thm. 1.1): if `0 ∈ S`, `φ_p(S) < 1` and `p < 1` then `P_p[0 ⟷ ∂Λ_n] ≤ e^{-cn}` for all
`n`, for some `c = c(p) > 0`. From `real_siteToBoundary_mul_le_pow` (`≤ φ_p(S)^{⌊n/L'⌋}` with
`S ⊆ Λ_{L'-1}`), the monotonicity of `n ↦ P_p[0 ⟷ ∂Λ_n]` and `P_p[0 ⟷ ∂Λ_1] < 1`: with
`M = max(φ_p(S), P_p[0 ⟷ ∂Λ_1]) < 1` one has `P_p[0 ⟷ ∂Λ_n] ≤ M^{max(1, ⌊n/L'⌋)} ≤ M^{n/(2L')}`.
[cite: DuminilCopinTassionEM2016, §2.1] -/
theorem DCT16_expDecay_of_phi_lt_one_holds : DCT16_expDecay_of_phi_lt_one := by
  intro d p S h0 hφ hp1
  set μ := bondPercolation (zdGraph d) p with hμ
  set a : ℕ → ℝ := fun n => μ.real (siteToBoundary d n) with ha
  obtain ⟨L, hSL⟩ := exists_subset_box S
  set φ := DCT16.phi p S with hφdef
  have hφ0 : 0 ≤ φ := DCT16.phi_nonneg p S
  have ha1 : a 1 < 1 := real_siteToBoundary_one_lt_one p hp1
  have ha0 : ∀ n, 0 ≤ a n := fun n => measureReal_nonneg
  have hanti : ∀ {m n}, m ≤ n → a n ≤ a m := fun hmn => real_siteToBoundary_antitone p hmn
  have hpow : ∀ k, a (k * (L + 1)) ≤ φ ^ k := real_siteToBoundary_mul_le_pow p h0 hSL
  set M := max φ (a 1) with hM
  have hM0 : 0 ≤ M := le_max_of_le_left hφ0
  have hM1 : M < 1 := max_lt hφ ha1
  -- `a n ≤ M ^ max 1 ⌊n/(L+1)⌋` for `n ≥ 1`
  have hbound : ∀ n, 1 ≤ n → a n ≤ M ^ max 1 (n / (L + 1)) := by
    intro n hn
    rcases le_or_gt (n / (L + 1)) 1 with hle | hlt
    · rw [max_eq_left hle, pow_one]
      exact (hanti hn).trans (le_max_right _ _)
    · rw [max_eq_right hlt.le]
      calc a n ≤ a (n / (L + 1) * (L + 1)) := hanti (Nat.div_mul_le_self n (L + 1))
        _ ≤ φ ^ (n / (L + 1)) := hpow _
        _ ≤ M ^ (n / (L + 1)) := pow_le_pow_left₀ hφ0 (le_max_left _ _) _
  rcases hM0.eq_or_lt with hM00 | hMpos
  · -- `M = 0`: then `a n = 0` for `n ≥ 1`
    refine ⟨1, one_pos, fun n => ?_⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [Nat.cast_zero, mul_zero, Real.exp_zero]; exact measureReal_le_one
    · have := hbound n hn
      rw [← hM00, zero_pow (by omega)] at this
      exact this.trans (Real.exp_pos _).le
  · -- `M > 0`: `c = -log M / (2 (L+1))`
    have hlog : Real.log M < 0 := Real.log_neg hMpos hM1
    refine ⟨-Real.log M / (2 * (L + 1)), div_pos (by linarith) (by positivity), fun n => ?_⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [Nat.cast_zero, mul_zero, Real.exp_zero]; exact measureReal_le_one
    · refine (hbound n hn).trans ?_
      rw [← Real.exp_log hMpos, ← Real.exp_nat_mul, Real.exp_log hMpos, Real.exp_le_exp]
      have hq : (n : ℝ) ≤ 2 * (L + 1) * (max 1 (n / (L + 1)) : ℕ) := by
        exact_mod_cast le_two_mul_max_div n L
      have hL : (0 : ℝ) < 2 * (L + 1) := by positivity
      have h2 : (n : ℝ) / (2 * (L + 1)) ≤ (max 1 (n / (L + 1)) : ℕ) := by
        rw [div_le_iff₀ hL]; linarith
      have key := mul_le_mul_of_nonpos_right h2 hlog.le
      have h3 : (n : ℝ) / (2 * (L + 1)) * Real.log M = -(-Real.log M / (2 * (L + 1)) * n) := by
        ring
      linarith [key, h3]

end Decay

/-! ## Part III. The differential inequality (Lemma 2.1): discharge of `DCT16_lemma21` -/

/-! ### The random set `𝒮` of sites not joined to `∂Λ_n` -/

section Block

variable {n : ℕ}

/-- `z ⟷ ∂Λ_n` in terms of paths. [folklore] -/
theorem bdryConn_iff {ω : BondConfig (Site d)} {z : Site d} :
    BdryConn n ω z ↔
      ∃ w ∈ innerBoundary (zdGraph d) (box d n), PathIn (openGraph ω) ↑(box d n) z w := by
  simp only [BdryConn, mem_openConnIn_iff_pathIn]

/-- Sites of `∂Λ_n` are joined to `∂Λ_n`. [folklore] -/
theorem bdryConn_of_mem_innerBoundary {ω : BondConfig (Site d)} {z : Site d}
    (hz : z ∈ innerBoundary (zdGraph d) (box d n)) : BdryConn n ω z :=
  bdryConn_iff.2 ⟨z, hz, PathIn.refl (Finset.mem_coe.2 (mem_innerBoundary_iff.1 hz).1)⟩

/-- `⟷ ∂Λ_n` propagates backwards along open edges inside `Λ_n`. [folklore] -/
theorem BdryConn.of_adj {ω : BondConfig (Site d)} {a b : Site d} (hb : BdryConn n ω b)
    (ha : a ∈ box d n) (hab : (openGraph ω).Adj a b) : BdryConn n ω a := by
  obtain ⟨w, hw, hp⟩ := bdryConn_iff.1 hb
  exact bdryConn_iff.2 ⟨w, hw, (PathIn.of_adj (Finset.mem_coe.2 ha) hp.left_mem hab).trans hp⟩

/-- `𝒮(ω) ⊆ Λ_n`. [folklore] -/
theorem blockSet_subset (ω : BondConfig (Site d)) : blockSet n ω ⊆ box d n :=
  fun _ hz => (mem_blockSet_iff.1 hz).1

/-- `0 ∈ 𝒮(ω) ↔ 0 ⟷̸ ∂Λ_n`. [cite: DuminilCopinTassionEM2016, §2.2 (proof of Lemma 2.1)] -/
theorem zero_mem_blockSet_iff {ω : BondConfig (Site d)} :
    (0 : Site d) ∈ blockSet n ω ↔ ω ∉ siteToBoundary d n := by
  rw [mem_blockSet_iff, mem_siteToBoundary_iff_bdryConn]
  simp

/-- A pair of sites of `Λ_n` not both in `S` is a pair of `Λ_n` "not inside `S`". [folklore] -/
theorem mk_mem_sym2_sdiff {S : Finset (Site d)} {a b : Site d} (ha : a ∈ box d n) (hb : b ∈ box d n)
    (h : a ∉ S ∨ b ∉ S) : s(a, b) ∈ (box d n).sym2 \ S.sym2 := by
  rw [Finset.mem_sdiff, Finset.mk_mem_sym2_iff, Finset.mk_mem_sym2_iff]
  exact ⟨⟨ha, hb⟩, fun h' => h.elim (fun h => h h'.1) (fun h => h h'.2)⟩

/-- **`{𝒮 = S}` is determined by the pairs of `Λ_n` not inside `S`** ("exploring from the outside
the set of vertices connected to the boundary", Duminil-Copin–Tassion 2016, proof of Lemma 2.1):
on `{𝒮 = S}`, an open path to `∂Λ_n` never enters `S`, so it only uses pairs not inside `S`, and
conversely such paths certify `𝒮 = S`. [cite: DuminilCopinTassionEM2016, §2.2 (proof of Lemma 2.1)] -/
theorem determinedBy_blockEvent (n : ℕ) (S : Finset (Site d)) :
    DeterminedBy (blockEvent n S) (↑((box d n).sym2 \ S.sym2) : Set (Sym2 (Site d))) := by
  rw [determinedBy_iff]
  suffices key : ∀ ω ω' : BondConfig (Site d),
      ω ∩ ↑((box d n).sym2 \ S.sym2) = ω' ∩ ↑((box d n).sym2 \ S.sym2) →
        ω ∈ blockEvent n S → ω' ∈ blockEvent n S from
    fun ω ω' h => ⟨key ω ω' h, key ω' ω h.symm⟩
  intro ω ω' hag hS
  simp only [blockEvent, Set.mem_setOf_eq] at hS ⊢
  -- sites joined to the boundary in `ω` are outside `S = 𝒮(ω)`
  have hout : ∀ a, a ∈ box d n → BdryConn n ω a → a ∉ S := by
    intro a ha hca haS
    rw [← hS, mem_blockSet_iff] at haS
    exact haS.2 hca
  -- open edges of `Λ_n` at such sites are common to `ω` and `ω'`
  have hedge : ∀ a b, a ∈ box d n → b ∈ box d n → BdryConn n ω a →
      ((openGraph ω).Adj b a ↔ (openGraph ω').Adj b a) := fun a b ha hb hca =>
    openGraph_adj_congr hag (Finset.mem_coe.2 (mk_mem_sym2_sdiff hb ha (Or.inr (hout a ha hca))))
  have hiff : ∀ z, z ∈ box d n → (BdryConn n ω z ↔ BdryConn n ω' z) := by
    intro z _
    constructor
    · intro h
      obtain ⟨w, hw, hp⟩ := bdryConn_iff.1 h
      refine (pathIn_induction (fun v => BdryConn n ω v ∧ BdryConn n ω' v) hp.symm
        ⟨bdryConn_of_mem_innerBoundary hw, bdryConn_of_mem_innerBoundary hw⟩ ?_).2
      rintro a b ha hb ⟨hca, hca'⟩ hab
      exact ⟨hca.of_adj hb hab.symm, hca'.of_adj hb ((hedge a b ha hb hca).1 hab.symm)⟩
    · intro h
      obtain ⟨w, hw, hp⟩ := bdryConn_iff.1 h
      refine pathIn_induction (fun v => BdryConn n ω v) hp.symm (bdryConn_of_mem_innerBoundary hw) ?_
      intro a b ha hb hca hab
      exact hca.of_adj hb ((hedge a b ha hb hca).2 hab.symm)
  ext z
  rw [mem_blockSet_iff, ← hS, mem_blockSet_iff]
  exact ⟨fun ⟨hz, h⟩ => ⟨hz, fun h' => h ((hiff z hz).1 h')⟩,
    fun ⟨hz, h⟩ => ⟨hz, fun h' => h ((hiff z hz).2 h')⟩⟩

/-- `{𝒮 = S}` is measurable. [folklore] -/
theorem measurableSet_blockEvent (n : ℕ) (S : Finset (Site d)) : MeasurableSet (blockEvent n S) :=
  (determinedBy_blockEvent n S).measurableSet_of_finset

/-- **The events `{𝒮 = S}`, `0 ∈ S ⊆ Λ_n`, partition `{0 ⟷̸ ∂Λ_n}`** ("when `0` is not connected to
`∂Λ_n`, the set `𝒮` is always a subset of `Λ_n` containing the origin. By summing over the possible
values for `𝒮`, we obtain ...", Duminil-Copin–Tassion 2016, proof of Lemma 2.1):
`Σ_{0 ∈ S ⊆ Λ_n} P_p[𝒮 = S] = 1 - P_p[0 ⟷ ∂Λ_n]`. [cite: DuminilCopinTassionEM2016, §2.2 (proof of Lemma 2.1)] -/
theorem sum_real_blockEvent (p : unitInterval) (n : ℕ) :
    ∑ S ∈ originSets d n, (bondPercolation (zdGraph d) p).real (blockEvent n S) =
      1 - (bondPercolation (zdGraph d) p).real (siteToBoundary d n) := by
  have hunion : (siteToBoundary d n)ᶜ = ⋃ S ∈ originSets d n, blockEvent n S := by
    ext ω
    simp only [Set.mem_compl_iff, Set.mem_iUnion, exists_prop, blockEvent, Set.mem_setOf_eq,
      mem_originSets]
    constructor
    · intro h
      exact ⟨blockSet n ω, ⟨blockSet_subset ω, zero_mem_blockSet_iff.2 h⟩, rfl⟩
    · rintro ⟨S, ⟨-, h0⟩, rfl⟩
      exact zero_mem_blockSet_iff.1 h0
  rw [show (1 : ℝ) - (bondPercolation (zdGraph d) p).real (siteToBoundary d n) =
      (bondPercolation (zdGraph d) p).real (siteToBoundary d n)ᶜ by
    rw [measureReal_compl (measurableSet_siteToBoundary d n), probReal_univ], hunion,
    measureReal_biUnion_finset]
  · intro S _ S' _ hSS'
    exact Set.disjoint_left.2 fun ω h h' => hSS' (h.symm.trans h')
  · exact fun S _ => measurableSet_blockEvent n S

end Block

/-! ### Boundary edges of `𝒮` are closed pivotal edges -/

section Pivotal

variable {n : ℕ}

/-- **Duminil-Copin–Tassion 2016, proof of Lemma 2.1, the key inclusion.** Let `0 ∈ S ⊆ Λ_n`,
`x ∈ S`, `y ∉ S` a neighbour of `x`. On `{0 ⟷ x in S} ∩ {𝒮 = S}` the edge `{x, y}` is closed and
pivotal for `{0 ⟷ ∂Λ_n}`: `y ∈ Λ_n` is joined to `∂Λ_n` (as `y ∉ 𝒮`; `y ∉ Λ_n` would put `x` on
`∂Λ_n`), so opening `{x, y}` joins `0 ⟷ x ⟷ y ⟷ ∂Λ_n`, while `0 ∈ 𝒮` says `0 ⟷̸ ∂Λ_n`.
[cite: DuminilCopinTassionEM2016, §2.2 (proof of Lemma 2.1)] -/
theorem subset_pivotal {S : Finset (Site d)} (hS : S ∈ originSets d n) {x y : Site d} (hx : x ∈ S)
    (hy : y ∈ (zdGraph d).neighborFinset x) (hyS : y ∉ S) :
    openConnIn (↑S : Set (Site d)) 0 x ∩ blockEvent n S ⊆
      {ω | s(x, y) ∈ (zdGraph d).edgeSet ∧ IsPivotal (siteToBoundary d n) s(x, y) ω ∧
        s(x, y) ∉ ω} := by
  rintro ω ⟨hconn, hblock⟩
  rw [mem_originSets] at hS
  rw [SimpleGraph.mem_neighborFinset] at hy
  simp only [blockEvent, Set.mem_setOf_eq] at hblock
  have hxb : x ∈ box d n ∧ ¬BdryConn n ω x := by rw [← mem_blockSet_iff, hblock]; exact hx
  have hyb : y ∈ box d n ∧ BdryConn n ω y := by
    have hy' : ¬(y ∈ box d n ∧ ¬BdryConn n ω y) := by rw [← mem_blockSet_iff, hblock]; exact hyS
    by_cases hyn : y ∈ box d n
    · exact ⟨hyn, by tauto⟩
    · exact absurd (bdryConn_of_mem_innerBoundary (mem_innerBoundary_iff.2 ⟨hxb.1, y, hyn, hy⟩))
        hxb.2
  have h0 : ¬BdryConn n ω 0 := by
    have := hS.2; rw [← hblock, mem_blockSet_iff] at this; exact this.2
  have hclosed : s(x, y) ∉ ω := fun h =>
    hxb.2 (hyb.2.of_adj hxb.1 ((openGraph_adj ω x y).2 ⟨h, hy.ne⟩))
  refine ⟨hy, Or.inl ⟨?_, ?_⟩, hclosed⟩
  · -- opening `{x, y}` connects `0` to `∂Λ_n`
    rw [mem_siteToBoundary_iff]
    obtain ⟨w, hw, hyw⟩ := bdryConn_iff.1 hyb.2
    have hmono : ∀ a b, (openGraph ω).Adj a b → (openGraph (insert s(x, y) ω)).Adj a b :=
      fun a b hab => openGraph_mono (Set.subset_insert _ _) hab
    have h0x : PathIn (openGraph (insert s(x, y) ω)) ↑(box d n) 0 x :=
      pathIn_map id (fun a ha => Finset.mem_coe.2 (hS.1 ha)) (fun a b _ _ hab => hmono a b hab)
        (pathIn_of_mem_openConnIn hconn)
    have hxy : (openGraph (insert s(x, y) ω)).Adj x y :=
      (openGraph_adj _ x y).2 ⟨Set.mem_insert _ _, hy.ne⟩
    have hyw' : PathIn (openGraph (insert s(x, y) ω)) ↑(box d n) y w :=
      pathIn_congrGraph (fun a b _ _ hab => hmono a b hab) hyw
    exact ⟨w, hw, (h0x.tail hxy (Finset.mem_coe.2 hyb.1)).trans hyw'⟩
  · rw [Set.sdiff_singleton_eq_self hclosed]
    exact h0

/-- **`P_p[e pivotal, e closed] = (1 - p) P_p[e pivotal]`**: pivotality of `e` for `{0 ⟷ ∂Λ_n}`
depends only on the other pairs of `Λ_n` (`Russo.determinedBy_isPivotal`), so it is independent
of the state of `e` (Duminil-Copin–Tassion 2016, proof of Lemma 2.1, first display:
`d/dp P_p[0 ⟷ ∂Λ_n] = 1/(1-p) Σ_e P_p[e pivotal, 0 ⟷̸ ∂Λ_n]`). [cite: DuminilCopinTassionEM2016, §2.2 (proof of Lemma 2.1)] -/
theorem real_pivotal_closed (p : unitInterval) (n : ℕ) (e : Sym2 (Site d)) :
    (bondPercolation (zdGraph d) p).real
        {ω | e ∈ (zdGraph d).edgeSet ∧ IsPivotal (siteToBoundary d n) e ω ∧ e ∉ ω} =
      (1 - p) * (bondPercolation (zdGraph d) p).real
        {ω | e ∈ (zdGraph d).edgeSet ∧ IsPivotal (siteToBoundary d n) e ω} := by
  classical
  by_cases he : e ∈ (zdGraph d).edgeSet
  · have h1 : {ω : BondConfig (Site d) | e ∈ (zdGraph d).edgeSet ∧
        IsPivotal (siteToBoundary d n) e ω ∧ e ∉ ω} =
        {ω | IsPivotal (siteToBoundary d n) e ω} ∩ {ω | e ∉ ω} := by
      ext ω; simp [he]
    have h2 : {ω : BondConfig (Site d) | e ∈ (zdGraph d).edgeSet ∧
        IsPivotal (siteToBoundary d n) e ω} = {ω | IsPivotal (siteToBoundary d n) e ω} := by
      ext ω; simp [he]
    have hA : DeterminedBy {ω | IsPivotal (siteToBoundary d n) e ω} ↑(((box d n).sym2).erase e) :=
      Russo.determinedBy_isPivotal (determinedBy_siteToBoundary d n) e
    have hB : DeterminedBy {ω : BondConfig (Site d) | e ∉ ω} ↑({e} : Finset (Sym2 (Site d))) := by
      rw [Finset.coe_singleton]; exact (determinedBy_mem e).compl
    have hdisj : Disjoint (((box d n).sym2).erase e) {e} := by
      rw [Finset.disjoint_singleton_right]; exact Finset.notMem_erase e _
    rw [h1, h2, real_inter_of_determinedBy_disjoint (zdGraph d) p hA hB hdisj,
      real_notMem (zdGraph d) p he, mul_comm]
  · have h1 : {ω : BondConfig (Site d) | e ∈ (zdGraph d).edgeSet ∧
        IsPivotal (siteToBoundary d n) e ω ∧ e ∉ ω} = ∅ := by
      ext ω; simp [he]
    have h2 : {ω : BondConfig (Site d) | e ∈ (zdGraph d).edgeSet ∧
        IsPivotal (siteToBoundary d n) e ω} = ∅ := by
      ext ω; simp [he]
    rw [h1, h2]; simp

/-- **Regrouping the boundary edges of `𝒮` by edge** (Duminil-Copin–Tassion 2016, proof of
Lemma 2.1, second display, `≥`): the events `{0 ⟷ x in S} ∩ {𝒮 = S}` attached to distinct triples
`(S, x, y)` (`0 ∈ S ⊆ Λ_n`, `x ∈ S`, `y ∼ x`, `y ∉ S`) with the same edge `{x, y}` are pairwise
disjoint pieces of `{{x,y} pivotal and closed}` (`subset_pivotal`; triples with `y ∉ Λ_n` give the
empty event), hence
`Σ_S Σ_{x ∈ S} Σ_{y ∼ x, y ∉ S} P_p[0 ⟷ x in S, 𝒮 = S] ≤ Σ_{e ⊆ Λ_n} P_p[e pivotal, e closed]`.
[cite: DuminilCopinTassionEM2016, §2.2 (proof of Lemma 2.1)] -/
theorem sum_le_sum_pivotal (p : unitInterval) (n : ℕ) :
    ∑ S ∈ originSets d n, ∑ x ∈ S, ∑ y ∈ (zdGraph d).neighborFinset x with y ∉ S,
        (bondPercolation (zdGraph d) p).real (openConnIn (↑S : Set (Site d)) 0 x ∩ blockEvent n S) ≤
      ∑ e ∈ (box d n).sym2, (bondPercolation (zdGraph d) p).real
        {ω | e ∈ (zdGraph d).edgeSet ∧ IsPivotal (siteToBoundary d n) e ω ∧ e ∉ ω} := by
  classical
  set μ := bondPercolation (zdGraph d) p with hμ
  -- the triples `(S, x, y)` as a sigma finset
  set T : Finset ((Σ _ : Finset (Site d), Σ _ : Site d, Site d)) :=
    (originSets d n).sigma fun S => S.sigma fun x =>
      ((zdGraph d).neighborFinset x).filter (· ∉ S) with hT
  set f : (Σ _ : Finset (Site d), Σ _ : Site d, Site d) → ℝ :=
    fun t => μ.real (openConnIn (↑t.1 : Set (Site d)) 0 t.2.1 ∩ blockEvent n t.1) with hf
  set g : (Σ _ : Finset (Site d), Σ _ : Site d, Site d) → Sym2 (Site d) := fun t => s(t.2.1, t.2.2) with hg
  have hmemT : ∀ t ∈ T, t.1 ∈ originSets d n ∧ t.2.1 ∈ t.1 ∧
      t.2.2 ∈ (zdGraph d).neighborFinset t.2.1 ∧ t.2.2 ∉ t.1 := by
    rintro ⟨S, x, y⟩ ht
    simp only [hT, Finset.mem_sigma, Finset.mem_filter] at ht
    exact ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2⟩
  have hsum : ∑ S ∈ originSets d n, ∑ x ∈ S, ∑ y ∈ (zdGraph d).neighborFinset x with y ∉ S,
      μ.real (openConnIn (↑S : Set (Site d)) 0 x ∩ blockEvent n S) = ∑ t ∈ T, f t := by
    rw [hT, Finset.sum_sigma]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [Finset.sum_sigma]
  rw [hsum, ← Finset.sum_filter_add_sum_filter_not T (fun t => g t ∈ (box d n).sym2)]
  -- triples whose edge leaves `Λ_n` contribute nothing
  have hzero : ∑ t ∈ T with ¬g t ∈ (box d n).sym2, f t = 0 := by
    refine Finset.sum_eq_zero fun t ht => ?_
    rw [Finset.mem_filter] at ht
    obtain ⟨hS, hx, hy, hyS⟩ := hmemT t ht.1
    have hyn : t.2.2 ∉ box d n := by
      intro hyn
      exact ht.2 (Finset.mk_mem_sym2_iff.2 ⟨(mem_originSets.1 hS).1 hx, hyn⟩)
    have hempty : openConnIn (↑t.1 : Set (Site d)) 0 t.2.1 ∩ blockEvent n t.1 = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun ω hω => hyn ?_
      -- as in `subset_pivotal`: `y ∉ Λ_n` would put `x ∈ 𝒮` on `∂Λ_n`
      obtain ⟨-, hblock⟩ := hω
      simp only [blockEvent, Set.mem_setOf_eq] at hblock
      have hxb : t.2.1 ∈ box d n ∧ ¬BdryConn n ω t.2.1 := by
        rw [← mem_blockSet_iff, hblock]; exact hx
      by_contra hyn
      exact hxb.2 (bdryConn_of_mem_innerBoundary (mem_innerBoundary_iff.2
        ⟨hxb.1, t.2.2, hyn, (SimpleGraph.mem_neighborFinset _ _ _).1 hy⟩))
    simp only [hf, hempty, measureReal_empty]
  rw [hzero, add_zero, ← Finset.sum_fiberwise_of_maps_to (g := g) (t := (box d n).sym2)
    (fun t ht => (Finset.mem_filter.1 ht).2)]
  refine Finset.sum_le_sum fun e he => ?_
  -- one fibre: disjoint pieces of `{e pivotal, closed}`
  set Te := (T.filter fun t => g t ∈ (box d n).sym2).filter fun t => g t = e with hTe
  have hTe_mem : ∀ t ∈ Te, t ∈ T ∧ g t = e := fun t ht => by
    simp only [hTe, Finset.mem_filter] at ht
    exact ⟨ht.1.1, ht.2⟩
  have hdisj : Set.PairwiseDisjoint (↑Te : Set ((Σ _ : Finset (Site d), Σ _ : Site d, Site d)))
      (fun t : (Σ _ : Finset (Site d), Σ _ : Site d, Site d) => openConnIn (↑t.1 : Set (Site d)) 0 t.2.1 ∩ blockEvent n t.1) := by
    rintro t ht t' ht' hne
    obtain ⟨htT, hte⟩ := hTe_mem t ht
    obtain ⟨ht'T, ht'e⟩ := hTe_mem t' ht'
    obtain ⟨-, hx, -, hyS⟩ := hmemT t htT
    obtain ⟨-, hx', -, hyS'⟩ := hmemT t' ht'T
    refine Set.disjoint_left.2 fun ω hω hω' => hne ?_
    have hSS : t.1 = t'.1 := hω.2.symm.trans hω'.2
    have hg' : s(t.2.1, t.2.2) = s(t'.2.1, t'.2.2) := hte.trans ht'e.symm
    rcases Sym2.eq_iff.1 hg' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rcases t with ⟨S, x, y⟩
      rcases t' with ⟨S', x', y'⟩
      simp only at hSS h1 h2
      subst hSS h1 h2
      rfl
    · exact absurd (h1 ▸ hx) (hSS ▸ hyS')
  calc ∑ t ∈ Te, f t = μ.real (⋃ t ∈ Te, openConnIn (↑t.1 : Set (Site d)) 0 t.2.1 ∩ blockEvent n t.1) := by
        rw [measureReal_biUnion_finset hdisj]
        intro t ht
        obtain ⟨htT, -⟩ := hTe_mem t ht
        obtain ⟨hS, -, -, -⟩ := hmemT t htT
        exact (measurableSet_openConnIn _ _ _).inter (measurableSet_blockEvent n _)
    _ ≤ μ.real {ω | e ∈ (zdGraph d).edgeSet ∧ IsPivotal (siteToBoundary d n) e ω ∧ e ∉ ω} := by
        refine measureReal_mono (Set.iUnion₂_subset fun t ht => ?_)
        obtain ⟨htT, hte⟩ := hTe_mem t ht
        obtain ⟨hS, hx, hy, hyS⟩ := hmemT t htT
        rw [← hte]
        exact subset_pivotal hS hx hy hyS

end Pivotal

/-! ### Conclusion of Lemma 2.1 -/

section Conclusion

/-- **Discharge of `DCT16_lemma21`** (Duminil-Copin–Tassion 2016, Lemma 2.1): for `n ≥ 1` and
`p ∈ (0, 1)`, `θ_n = P_·[0 ⟷ ∂Λ_n]` is differentiable at `p` (Russo's formula) with derivative
`≥ 1/(p(1-p)) · inf_{0 ∈ S ⊆ Λ_n} φ_p(S) · (1 - θ_n(p))`. Assembled from `russo_formula_sum_holds`,
`real_pivotal_closed`, `sum_le_sum_pivotal`, the independence of `{0 ⟷ x in S}` and `{𝒮 = S}`
(`real_inter_of_determinedBy_disjoint` with `determinedBy_openConnIn`, `determinedBy_blockEvent`)
and `sum_real_blockEvent`. [cite: DuminilCopinTassionEM2016, Lemma 2.1] -/
theorem DCT16_lemma21_holds : DCT16_lemma21 := by
  intro d n _hn p hp
  classical
  set q : unitInterval := Set.projIcc 0 1 zero_le_one p with hqdef
  have hqp : (q : ℝ) = p := by rw [hqdef, Set.projIcc_of_mem _ ⟨hp.1.le, hp.2.le⟩]
  set μ := bondPercolation (zdGraph d) q with hμ
  set A := siteToBoundary d n with hA
  set F : Finset (Sym2 (Site d)) := (box d n).sym2 with hF
  have hderiv := russo_formula_sum_holds (zdGraph d) (isUpperSet_siteToBoundary d n) F
    (determinedBy_siteToBoundary d n) p hp
  refine ⟨_, hderiv, ?_⟩
  set D := ∑ e ∈ F, μ.real {ω | e ∈ (zdGraph d).edgeSet ∧ IsPivotal A e ω} with hD
  set m := (originSets d n).inf' (originSets_nonempty d n) (fun S => DCT16.phi q S) with hm
  have hp0 : (0 : ℝ) < p := hp.1
  have hp1 : (0 : ℝ) < 1 - p := by linarith [hp.2]
  -- (i) `Σ_e P[e pivotal, closed] = (1 - p) D`
  have h1 : ∑ e ∈ F, μ.real {ω | e ∈ (zdGraph d).edgeSet ∧ IsPivotal A e ω ∧ e ∉ ω} = (1 - p) * D := by
    rw [hD, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [hμ, hA, real_pivotal_closed q n e, hqp]
  -- (ii) the lower bound by the boundary edges of `𝒮`
  have h2 := sum_le_sum_pivotal (d := d) q n
  -- (iii) independence and `φ`
  have h3 : ∀ S ∈ originSets d n, ∑ x ∈ S, ∑ y ∈ (zdGraph d).neighborFinset x with y ∉ S,
      μ.real (openConnIn (↑S : Set (Site d)) 0 x ∩ blockEvent n S) =
        μ.real (blockEvent n S) * (DCT16.phi q S / p) := by
    intro S hS
    have hind : ∀ x ∈ S, μ.real (openConnIn (↑S : Set (Site d)) 0 x ∩ blockEvent n S) =
        μ.real (openConnIn (↑S : Set (Site d)) 0 x) * μ.real (blockEvent n S) := by
      intro x _
      refine real_inter_of_determinedBy_disjoint (zdGraph d) q
        (determinedBy_openConnIn (↑S : Set (Site d)) 0 x (K := ↑S.sym2) (by rw [Finset.coe_sym2]))
        (determinedBy_blockEvent n S) Finset.disjoint_sdiff
    rw [DCT16.phi_def, hqp, mul_div_cancel_left₀ _ hp0.ne', Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hind x hx, mul_comm]
  -- (iv) `inf ≤ φ_q(S)` termwise and the partition `Σ_S P[𝒮 = S] = 1 - θ_n`
  have h4 : m / p * (1 - μ.real A) ≤
      ∑ S ∈ originSets d n, μ.real (blockEvent n S) * (DCT16.phi q S / p) := by
    rw [hA, hμ, ← sum_real_blockEvent q n, Finset.mul_sum]
    refine Finset.sum_le_sum fun S hS => ?_
    rw [mul_comm]
    refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right ?_ hp0.le) measureReal_nonneg
    exact Finset.inf'_le _ hS
  have key : m / p * (1 - μ.real A) ≤ (1 - p) * D := by
    refine h4.trans ?_
    rw [← h1, ← Finset.sum_congr rfl h3]
    exact h2
  have hθ : DCT16.thetaN d n p = μ.real A := rfl
  rw [hθ]
  calc 1 / (p * (1 - p)) * m * (1 - μ.real A) = m / p * (1 - μ.real A) / (1 - p) := by
        field_simp
    _ ≤ (1 - p) * D / (1 - p) := div_le_div_of_nonneg_right key hp1.le
    _ = D := by field_simp

end Conclusion

/-! ## Part IV. Integration of (2.1) (§2.2): discharge of `DCT16_meanField_of_phi_ge_one`, and `perc_sharpness` -/

/-- `θ_n(q) = P_q[0 ⟷ ∂Λ_n]` is a polynomial in the parameter (the cylinder expansion
`Russo.measureReal_eq_cylPoly` of the local event `{0 ⟷ ∂Λ_n}`), in particular continuous on `ℝ`
(with the constant extension outside `[0, 1]`). (Grimmett 1999, §2.2; Russo 1981, proof of
Prop. 1: "a polynomial".) [cite: GrimmettPercolation1999, §2.2] -/
theorem continuous_thetaN (d n : ℕ) : Continuous (DCT16.thetaN d n) := by
  classical
  have h : DCT16.thetaN d n = fun q => Russo.cylPoly (zdGraph d).edgeSet ((box d n).sym2)
      (siteToBoundary d n) (Set.projIcc 0 1 zero_le_one q) := by
    funext q
    unfold DCT16.thetaN
    rw [bondPercolation]
    exact Russo.measureReal_eq_cylPoly (determinedBy_siteToBoundary d n) _ _
  rw [h]
  have hc : Continuous (Russo.cylPoly (zdGraph d).edgeSet ((box d n).sym2) (siteToBoundary d n)) :=
    continuous_iff_continuousAt.2 fun q => (Russo.hasDerivAt_cylPoly _ _ _ q).continuousAt
  exact hc.comp (continuous_subtype_val.comp continuous_projIcc)

/-- `0 ≤ θ_n(q) ≤ 1`. [folklore] -/
theorem thetaN_mem_Icc (d n : ℕ) (q : ℝ) : DCT16.thetaN d n q ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨measureReal_nonneg, measureReal_le_one⟩

/-- **Integration of (2.1)** (Duminil-Copin–Tassion 2016, §2.2): if `φ_q(S) ≥ 1` for all finite
`S ∋ 0` and all `q ≥ p₁`, then for `n ≥ 1` and `p₁ < p < 1`,
`P_p[0 ⟷ ∂Λ_n] ≥ (p - p₁)/(p(1 - p₁))`. Proof: `g(q) = (1 - θ_n(q)) q/(1-q)` is non-increasing on
`[p₁, 1)` since, by Lemma 2.1, `g'(q) = -θ_n'(q) q/(1-q) + (1 - θ_n(q))/(1-q)² ≤ 0`.
[cite: DuminilCopinTassionEM2016, §2.2] -/
theorem thetaN_ge (p₁ : unitInterval)
    (hφ : ∀ q : unitInterval, p₁ ≤ q → ∀ S : Finset (Site d), (0 : Site d) ∈ S → 1 ≤ DCT16.phi q S)
    {n : ℕ} (hn : 1 ≤ n) {p : ℝ} (hp₁p : (p₁ : ℝ) < p) (hp1 : p < 1) :
    (p - p₁) / (p * (1 - p₁)) ≤ DCT16.thetaN d n p := by
  set f := DCT16.thetaN d n with hf
  have hp₁0 : (0 : ℝ) ≤ p₁ := p₁.2.1
  have hp₁1 : (p₁ : ℝ) < 1 := hp₁p.trans hp1
  have hf01 : ∀ q, 0 ≤ f q ∧ f q ≤ 1 := fun q => thetaN_mem_Icc d n q
  -- Lemma 2.1 on `(p₁, 1)`: `f' ≥ (1 - f)/(q(1-q))`
  have hder : ∀ q ∈ Set.Ioo (p₁ : ℝ) 1, ∃ D, HasDerivAt f D q ∧ (1 - f q) / (q * (1 - q)) ≤ D := by
    intro q hq
    have hq01 : q ∈ Set.Ioo (0 : ℝ) 1 := ⟨hp₁0.trans_lt hq.1, hq.2⟩
    obtain ⟨D, hD, hbound⟩ := DCT16_lemma21_holds (d := d) n hn q hq01
    refine ⟨D, hD, le_trans ?_ hbound⟩
    have hm : 1 ≤ (originSets d n).inf' (originSets_nonempty d n)
        (fun S => DCT16.phi (Set.projIcc 0 1 zero_le_one q) S) := by
      refine Finset.le_inf' _ _ fun S hS => hφ _ ?_ S (mem_originSets.1 hS).2
      change (p₁ : ℝ) ≤ ((Set.projIcc 0 1 zero_le_one q : unitInterval) : ℝ)
      rw [Set.projIcc_of_mem _ ⟨hq01.1.le, hq01.2.le⟩]
      exact hq.1.le
    have hpos : 0 < 1 / (q * (1 - q)) := by
      have := hq01.1; have : 0 < 1 - q := by linarith [hq01.2]
      positivity
    have hu : 0 ≤ 1 - f q := by linarith [(hf01 q).2]
    calc (1 - f q) / (q * (1 - q)) = 1 / (q * (1 - q)) * 1 * (1 - f q) := by ring
      _ ≤ 1 / (q * (1 - q)) * (originSets d n).inf' (originSets_nonempty d n)
            (fun S => DCT16.phi (Set.projIcc 0 1 zero_le_one q) S) * (1 - f q) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm hpos.le) hu
  -- `g(q) = (1 - f q) q/(1-q)` and its derivative
  set g : ℝ → ℝ := fun q => (1 - f q) * (q / (1 - q)) with hg
  have hg_der : ∀ q ∈ Set.Ioo (p₁ : ℝ) 1, ∃ g', HasDerivAt g g' q ∧ g' ≤ 0 := by
    intro q hq
    obtain ⟨D, hD, hDb⟩ := hder q hq
    have hq0 : 0 < q := hp₁0.trans_lt hq.1
    have hq1 : 0 < 1 - q := by linarith [hq.2]
    have h1 : HasDerivAt (fun y => 1 - f y) (-D) q := hD.const_sub 1
    have h2 : HasDerivAt (fun y : ℝ => y / (1 - y)) ((1 * (1 - q) - q * -1) / (1 - q) ^ 2) q :=
      (hasDerivAt_id' q).fun_div ((hasDerivAt_id' q).const_sub 1) hq1.ne'
    refine ⟨_, h1.fun_mul h2, ?_⟩
    have hu : 0 ≤ 1 - f q := by linarith [(hf01 q).2]
    have h3 : (1 - f q) / (q * (1 - q)) * (q / (1 - q)) ≤ D * (q / (1 - q)) :=
      mul_le_mul_of_nonneg_right hDb (div_nonneg hq0.le hq1.le)
    have h4 : (1 - f q) / (q * (1 - q)) * (q / (1 - q)) =
        (1 - f q) * ((1 * (1 - q) - q * -1) / (1 - q) ^ 2) := by
      field_simp
      ring
    linarith [h3, h4]
  -- `g` is non-increasing on `[p₁, 1)`
  have hanti : AntitoneOn g (Set.Ico (p₁ : ℝ) 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ico _ _)
    · have hcf : Continuous f := continuous_thetaN d n
      refine ((continuous_const.sub hcf).continuousOn).mul ?_
      exact continuousOn_id.div (continuousOn_const.sub continuousOn_id)
        fun x hx => by have := hx.2; exact fun h => by linarith
    · rw [interior_Ico]
      intro q hq
      obtain ⟨g', hg', -⟩ := hg_der q hq
      exact hg'.differentiableAt.differentiableWithinAt
    · rw [interior_Ico]
      intro q hq
      obtain ⟨g', hg', hle⟩ := hg_der q hq
      rw [hg'.deriv]
      exact hle
  have hkey : g p ≤ g p₁ := hanti ⟨le_rfl, hp₁1⟩ ⟨hp₁p.le, hp1⟩ hp₁p.le
  -- `g p₁ ≤ p₁/(1-p₁)`
  have hgp₁ : g p₁ ≤ p₁ / (1 - p₁) := by
    simp only [hg]
    have h1 : 1 - f p₁ ≤ 1 := by linarith [(hf01 p₁).1]
    have h2 : 0 ≤ (p₁ : ℝ) / (1 - p₁) := div_nonneg hp₁0 (by linarith)
    nlinarith
  -- unwind
  have hp0 : 0 < p := hp₁0.trans_lt hp₁p
  have h1p : 0 < 1 - p := by linarith
  have h1p₁ : 0 < 1 - (p₁ : ℝ) := by linarith
  have h : (1 - f p) * p / (1 - p) ≤ p₁ / (1 - p₁) := by
    have := hkey.trans hgp₁
    simp only [hg] at this
    rwa [← mul_div_assoc] at this
  rw [div_le_div_iff₀ h1p h1p₁] at h
  rw [div_le_iff₀ (mul_pos hp0 h1p₁)]
  nlinarith [h, (hf01 p).1]

/-- **Discharge of `DCT16_meanField_of_phi_ge_one`** (Duminil-Copin–Tassion 2016, §2.2, item 2
of Thm. 1.1 from Lemma 2.1): if `φ_q(S) ≥ 1` for all finite `S ∋ 0` and all `q ≥ p₁`, then
`θ(p) ≥ (p - p₁)/(p(1 - p₁))` for `p₁ < p < 1` (`thetaN_ge` for every `n ≥ 1`, and `n → ∞` by
`le_theta_of_forall_le_real_siteToBoundary`). [cite: DuminilCopinTassionEM2016, §2.2] -/
theorem DCT16_meanField_of_phi_ge_one_holds : DCT16_meanField_of_phi_ge_one := by
  intro d p₁ hφ p hp₁p hp1
  refine le_theta_of_forall_le_real_siteToBoundary p fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · calc ((p : ℝ) - p₁) / (p * (1 - p₁))
        ≤ (bondPercolation (zdGraph d) p).real (siteToBoundary d 1) := by
          rw [← DCT16.thetaN_coe]; exact thetaN_ge p₁ hφ le_rfl hp₁p hp1
      _ ≤ (bondPercolation (zdGraph d) p).real (siteToBoundary d 0) :=
          real_siteToBoundary_antitone p (Nat.zero_le 1)
  · rw [← DCT16.thetaN_coe]
    exact thetaN_ge p₁ hφ hn hp₁p hp1

/-- [cite: DuminilCopinTassionEM2016, Thm. 1.1(1)] [cite: DuminilCopinTassionCMP2016, Thm. 1.1] -/
theorem perc_sharpness_holds : perc_sharpness :=
  perc_sharpness_of_DCT16 DCT16_phi_mono_holds DCT16_expDecay_of_phi_lt_one_holds
    DCT16_meanField_of_phi_ge_one_holds

/-! ## Part V. `p̃_c = p_c` and the mean-field bound (Thm. 1.1, first assertion and item 2) -/

section TildeEq

/-- A walk of the graph is a path inside `Set.univ`. [folklore] -/
theorem pathIn_univ_of_reachable {V : Type*} {G : SimpleGraph V} {u v : V} (h : G.Reachable u v) :
    PathIn G Set.univ u v := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  refine ⟨Set.mem_univ u, ?_⟩
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail ⟨hbc, Set.mem_univ _⟩

/-- **`{|C(0)| = ∞} ⊆ {0 ⟷ ∂Λ_n}` almost surely**: an infinite open cluster leaves the finite box
`Λ_n`, and an open path from `0` to a site outside `Λ_n` passes through `∂Λ_n` (first exit; valid
for `ω ⊆ E(ℤ^d)`). Hence `θ(p) ≤ P_p[0 ⟷ ∂Λ_n]` for every `n`. (Grimmett 1999, §1.4,
`θ(p) ≤ P_p(0 ⟷ ∂B(n))`.) [cite: GrimmettPercolation1999, §1.4] -/
theorem theta_le_real_siteToBoundary (p : unitInterval) (n : ℕ) :
    theta (zdGraph d) 0 p ≤ (bondPercolation (zdGraph d) p).real (siteToBoundary d n) := by
  refine real_mono_of_forall_subset_edgeSet (zdGraph d) p fun ω hω h => ?_
  obtain ⟨z, hz, hzn⟩ : ∃ z ∈ openCluster ω 0, z ∉ box d n := by
    by_contra hcon
    push Not at hcon
    exact h ((box d n).finite_toSet.subset fun z hz => Finset.mem_coe.2 (hcon z hz))
  rw [← armEvent_zero]
  exact armEvent_of_pathIn hω (pathIn_univ_of_reachable hz) (Or.inl (by rwa [sub_zero]))

end TildeEq

end Percolation.Literature.DCT16
