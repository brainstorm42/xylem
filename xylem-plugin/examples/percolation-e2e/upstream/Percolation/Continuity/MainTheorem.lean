import Percolation.Continuity.AdditiveGluing.CSHHtwBridge
import Percolation.Continuity.AdditiveGluing.CSHInduction
import Percolation.Continuity.CSH.AdditiveGluingOfCSH
import Percolation.Continuity.CSH.UnfoldMain
import Percolation.Util.Linter

/-!
# θ(p_c) = 0 on ℤ^d for every d ≥ 2: the conditioned slack hierarchy holds, hence additive gluing, hence Kozma–Nitzan's Conjecture 3, hence continuity by their Theorem 6

This file combines the parts of the argument into its main theorems.  It contains no definitions; every theorem below is a
closed term whose only axioms are the three standard ones (`propext`, `Classical.choice`, `Quot.sound`).

* `CSH.cshHolds` — **the conditioned slack hierarchy** (the statement `CSH.CSHHolds`, whose file defines the level forms).  On a
  finite vertex set whose pairs all carry weights in the open interval `(0,1)`, fix an *owner* `x`, an *avoided set* `Y`, a list
  `D = (d_1,…,d_k)` of distinct *decoys* and two *observers* `o ≠ v`, the named vertices pairwise distinct and outside `Y`.  Then for
  every increasing real function `f` of sets of pairs, the level form of the conditioned covariance function
  `u ↦ Cov(f(𝒞_x), 1{u ∈ C_x} | x ↮ Y)` (`𝒞_x` the open edge cluster of the owner) is nonnegative.  At level `k = 0` this reads
  `Cov(f(𝒞_x), 1{o ∈ C_x} | x ↮ Y) ≥ P(o ↔ v | v ↮ {x} ∪ Y) · Cov(f(𝒞_x), 1{v ∈ C_x} | x ↮ Y)`; for `Y = ∅` and `f = 1{v ∈ ·}` that
  is the Harris inequality `P(o ↔ {x,v}, x ↔ v) ≥ P(o ↔ {x,v}) · P(x ↔ v)`.  PROOF: strong induction on the number `k` of decoys
  (`CSH.cshHolds_of_unfold`).  Conditionally on the open cluster of `Y` (the *world*), the cluster of `x` is a percolation cluster
  in the graph with that cluster deleted; the induction step `CSH.within_nonneg_of_hpart` rewrites the world-averaged margin as a sum
  of margins of lower level, one for each decoy and nonnegative by the induction hypothesis, plus a horizontal term, and
  `CSH.hpart_nonneg` bounds the horizontal term from below by zero: world by world it is the set form of level zero, and the
  correction coming from replacing each world's own observer constant by the global one is nonnegative on average by the two-source
  inequality `CovTau.htw_world`.
* `CSH.cshAll` — the same statement for vertex type `Fin n` and a `Finset` avoided set (the hypothesis shape of
  `CSH.additiveGluing_of_csh`).
* `CSH.additiveGluing_holds` — **additive gluing** on every finite graph with pair weights in `[0,1]`: if `t ≥ 0` and
  `P(a ↔ b) ≥ 1 − t` for every `a ∈ A`, then `P(o ↔ b) ≥ P(o ↔ A) − t`.  Obtained from the hierarchy through the chain
  CSH ⟹ (S5D) ⟹ (S5) ⟹ (GEN) ⟹ (AG-loc) ⟹ additive gluing (`CSH.surplusMargin_nonneg_of_csh`, `CSH.additiveGluing_of_csh`), the
  hypothesis "weights in `(0,1)`" being removed at the end by continuity in the weights.  Here, for a relay set `T`, observers `o, v`
  and an increasing `F` of vertex sets with surplus `Sur_u(T)` (`CSH.surplus`: the excess of `E[F(C_u); u ↔ T]` over the mean of `F` at
  the first relay of `u`), (S5) is the surplus transfer inequality `P(v ↮ T) · Sur_o(T) ≥ P(o ↔ v, v ↮ T) · Sur_v(T)`, (S5D) its version
  with a list of decoys discounted from both sides (`CSH.surplusMargin`), (GEN) the first-relay bound `E[F(C_o); o ↔ A] ≥ Σ_a P(P^o_a) E F(C_a)`
  (`P^o_a` = "`a` is the first relay of `o`"), and (AG-loc) the union bound localised on the first relay,
  `P(o ↔ A, o ↮ b) ≤ Σ_a P(P^o_a) P(a ↮ b)`.  This is the ADDITIVE form of Kozma–Nitzan's
  Conjecture 1: their Conjecture 1 is the multiplicative inequality `P(o ↔ b) ≥ P(o ↔ A) · min_{a ∈ A} P(a ↔ b)`, which implies the
  additive form (`P(o ↔ A)(1 − t) ≥ P(o ↔ A) − t`); `additiveGluing_holds` is not Conjecture 1 itself.
* `CSH.kozmaNitzan_conjecture3_holds` — **Kozma–Nitzan's Conjecture 3** (`KozmaNitzan2024_conjecture3`; for every `ε > 0` there is
  `δ > 0` such that `P(o ↔ A) > 1 − δ` and `P(a ↔ b) > 1 − δ` for all `a ∈ A` force `P(o ↔ b) > 1 − ε`, uniformly in the graph and in
  `|A|`): additive gluing with `t = δ = ε/2`.
* `CSH.percolationContinuity_allDimensions` — **`θ(p_c) = 0` for nearest-neighbour Bernoulli bond percolation on `ℤ^d`, every
  `d ≥ 2`** (`PercolationContinuity d`): Conjecture 3 combined with the theorem of Kozma and Nitzan that Conjecture 3 implies
  `θ(p_c) = 0` on `ℤ^d` for all `d ≥ 2` (`KozmaNitzan2024_thm6_holds`, proved in `KozmaNitzanTheorem6SlabCritical`).  Before this work
  the conclusion was known for `d = 2` (Harris, Kesten) and for `d ≥ 11` (the lace expansion: Hara–Slade, Fitzner–van der Hofstad); the
  cases `3 ≤ d ≤ 10` were open.
* `CSH.percolationContinuity_three` — the case `d = 3`, `θ(p_c(ℤ³)) = 0`.

What is new here: the hierarchy `CSH.cshHolds` and the chain from it to additive gluing and Conjecture 3.  What is not: the step from
Conjecture 3 to `θ(p_c) = 0` is the theorem of Kozma and Nitzan, and the published correlation inequalities listed below are the inputs
of the proof of the hierarchy.  The statement proved, `PercolationContinuity d := theta (zdGraph d) 0 (criticalProbI d) = 0`, is the
one of `CriticalContinuity` (`θ` = probability that the open cluster of the origin is infinite, `p_c = inf {p ∈ [0,1] | θ(p) > 0}`),
used unchanged.

Inputs: [cite: HarrisPCPS1960] (the Harris inequality) · [cite: VandenbergHaggstromKahn2005, Thms. 1.1–1.5 (pp. 6–8), §2.1 (pp. 9–13)]
(conditional association of one and two clusters; the two-cluster resampling) · [cite: AhlswedeDaykin1978] (the four functions theorem,
through Mathlib's `four_functions_theorem_univ`) · [cite: Gladkov2024, Thm. 3.2] (decision-tree form of the Harris–Kleitman inequality)
· [cite: KozmaNitzan2024, Conj. 1 (p. 3), Conj. 3 (p. 15), Conj. 4 (p. 32), Thm. 6 (p. 15)] (the conjectures, and the reduction of
`θ(p_c) = 0` to Conjecture 3).
-/

noncomputable section

namespace Percolation.Continuity

open MeasureTheory Set Percolation.Literature.LatticeModels Percolation.Literature
open scoped Classical
open Percolation.Continuity.Statements

namespace CSH

variable {V : Type*} [Fintype V]

/-- **The conditioned slack hierarchy holds.** Let `V` be a finite vertex type and `w` a weight function with `0 < w e < 1` on
every unordered pair; let `x` be an owner, `Y` an avoided set with `x ∉ Y`, `D` a list of distinct decoys and `o ≠ v` two observers,
with `o, v` and every decoy outside `{x} ∪ Y` and every decoy different from `o` and `v`.  Then `CSH.CSHHolds w x Y D o v`: for every
monotone real function `f` of sets of pairs the CSH margin `CSH.cshMargin w x Y D o v f` — the level form
`sl^k[κ](o) − p · sl^k[κ](v)` of the conditioned covariance function `κ(u) = Cov(f(𝒞_x), 1{u ∈ C_x} | x ↮ Y)` (carried
denominator-free, multiplied by `P(x ↮ Y)²`), in which the decoys `d_1, …, d_k` are discounted successively at the rates
`c_j(u) = P(u ∈ C_{d_j} | d_j ↮ {x} ∪ Y ∪ {d_1,…,d_{j-1}})` and `p = P(o ∈ C_v | v ↮ {x} ∪ Y ∪ D)` — is nonnegative.
Levels `k = 0` and `k = 1` are the inequalities `κ(o) ≥ p · κ(v)` and `κ(o) − c(o)κ(d) ≥ p · [κ(v) − c(v)κ(d)]`.

This family of inequalities is new; it is the object from which the gluing inequalities of Kozma and Nitzan are derived in this
development (`CSH.additiveGluing_holds`, `CSH.kozmaNitzan_conjecture3_holds`).  Proof: strong induction on the number of decoys,
`CSH.cshHolds_of_unfold`, with the induction step supplied by the world-by-world unfolding `CSH.within_nonneg_of_hpart` (lower levels
by the induction hypothesis) and the horizontal estimate `CSH.hpart_nonneg` (set form of level zero in each world, plus the two-source
inequality `CovTau.htw_world` for the averaged observer-constant correction).
Inputs: [cite: HarrisPCPS1960] (Harris inequality) · [cite: VandenbergHaggstromKahn2005, §2.1 (pp. 9–13)] (conditional association,
Thms. 1.1–1.5, and the two-cluster resampling of §2.1) · [cite: AhlswedeDaykin1978] (four functions theorem) · [cite: Gladkov2024, Thm. 3.2]
(decision-tree Harris–Kleitman inequality). -/
theorem cshHolds (w : Sym2 V → unitInterval) (hw : ∀ e, 0 < w e ∧ w e < 1) (x : V) (Y : Set V) (D : List V) (o v : V)
    (hxY : x ∉ Y) (ho : o ∉ insert x Y) (hv : v ∉ insert x Y) (hov : o ≠ v) (hnd : D.Nodup)
    (hdis : ∀ d ∈ D, d ∉ insert x Y ∧ d ≠ o ∧ d ≠ v) : CSHHolds w x Y D o v := by
  refine cshHolds_of_unfold w hw ?_ x Y D o v hxY ho hv hov hnd hdis
  intro x Y D o v _hxY _ho hv _hov _hne hnd hdis hIH g hg hg0
  have hD' : ∀ d ∈ D, d ≠ x ∧ d ∉ Y ∧ d ≠ o ∧ d ≠ v := fun d hd => by
    obtain ⟨h1, h2, h3⟩ := hdis d hd
    rw [mem_insert_iff, not_or] at h1
    exact ⟨h1.1, h1.2, h2, h3⟩
  refine within_nonneg_of_hpart w hw x Y D o v hnd hD' hg hIH ?_
  have hv' : v ≠ x ∧ v ∉ Y := by rwa [mem_insert_iff, not_or] at hv
  have hvS : v ∉ insert x D.toFinset := by
    rw [Finset.mem_insert, List.mem_toFinset, not_or]
    exact ⟨hv'.1, fun h => (hdis v h).2.2 rfl⟩
  have hS : ((↑(insert x D.toFinset) : Set V) ∪ Y) = insert x Y ∪ {d | d ∈ D} := by
    ext u
    simp only [Finset.coe_insert, mem_union, mem_insert_iff, Finset.mem_coe, List.mem_toFinset, mem_setOf_eq]
    tauto
  have key := hpart_nonneg w hw x Y (insert x D.toFinset) (Finset.mem_insert_self x _) o v hvS hv'.2 g hg hg0
  rw [hS] at key
  -- the two statements agree up to the (subsingleton) decidability instances inside the world weights
  convert key using 20

/-- **The conditioned slack hierarchy, `Fin n` form.** The statement of `CSH.cshHolds` for vertex type `Fin n`, a `Finset`
avoided set `Y` and the side conditions spelled out one by one (`o ≠ v`, `x ∉ Y`, `o ≠ x`, `v ≠ x`, `o ∉ Y`, `v ∉ Y`, `D` without
duplicates, every decoy different from `x, o, v` and outside `Y`): for all pair weights in `(0,1)`, `CSH.CSHHolds w x ↑Y D o v`.
This is exactly the hypothesis under which `CSH.additiveGluing_of_csh`, `CSH.conjecture3_of_csh` and
`CSH.percolationContinuity_of_csh` derive the gluing inequalities and `θ(p_c) = 0`; it is `CSH.cshHolds` with the hypotheses
repackaged, nothing more.  Inputs: those of `CSH.cshHolds`, [cite: VandenbergHaggstromKahn2005, §2.1 (pp. 9–13)]. -/
theorem cshAll : ∀ (n : ℕ) (w : Sym2 (Fin n) → unitInterval), (∀ e, 0 < w e ∧ w e < 1) →
    ∀ (o v x : Fin n) (Y : Finset (Fin n)) (D : List (Fin n)),
    o ≠ v → x ∉ Y → o ≠ x → v ≠ x → o ∉ Y → v ∉ Y → D.Nodup → (∀ d ∈ D, d ≠ x ∧ d ∉ Y ∧ d ≠ o ∧ d ≠ v) →
    CSHHolds w x (↑Y : Set (Fin n)) D o v := by
  intro n w hw o v x Y D hov hxY hox hvx hoY hvY hD hdis
  refine cshHolds w hw x (↑Y : Set (Fin n)) D o v (fun h => hxY (Finset.mem_coe.1 h)) ?_ ?_ hov hD ?_
  · simp only [mem_insert_iff, Finset.mem_coe, not_or]; exact ⟨hox, hoY⟩
  · simp only [mem_insert_iff, Finset.mem_coe, not_or]; exact ⟨hvx, hvY⟩
  · intro d hd
    obtain ⟨h1, h2, h3, h4⟩ := hdis d hd
    exact ⟨by simp only [mem_insert_iff, Finset.mem_coe, not_or]; exact ⟨h1, h2⟩, h3, h4⟩

/-- **Additive gluing, on every finite weighted graph.**  `Percolation.Continuity.Statements.AdditiveGluing`: for every `n`, every weight
function `w : Sym2 (Fin n) → [0,1]` (product Bernoulli measure `prodBernoulli w`; a pair of weight `0` is an absent edge), every
finite set `A` of vertices (the relays), all vertices `o, b` and every `t ≥ 0`, if `P(a ↔ b) ≥ 1 − t` for every `a ∈ A` then
`P(o ↔ b) ≥ P(o ↔ A) − t`; equivalently, for `A ≠ ∅`, `P(o ↮ b) ≤ P(o ↮ A) + max_{a ∈ A} P(a ↮ b)`.  For `|A| = 1` this is the union
bound; the content is that the bound does not deteriorate with `|A|`.

What is new: the inequality itself (not previously in print) and its proof from the conditioned slack hierarchy `CSH.cshAll` via
`CSH.additiveGluing_of_csh` (CSH ⟹ surplus transfer with decoys ⟹ surplus transfer (S5) ⟹ the first-relay bound (GEN) ⟹ the union
bound localised on the first relay ⟹ additive gluing; weights in `(0,1)` first, then all of `[0,1]` by continuity).  Relation to
Kozma–Nitzan's Conjecture 1: this is the ADDITIVE form.  Conjecture 1 is the multiplicative inequality
`P(o ↔ b) ≥ P(o ↔ A) · min_{a ∈ A} P(a ↔ b)`; since `P(o ↔ A)(1 − t) ≥ P(o ↔ A) − t`, Conjecture 1 implies additive gluing, and
`additiveGluing_holds` is therefore a consequence-shaped statement of Conjecture 1, not Conjecture 1 itself.  It suffices for
Conjecture 3 (`CSH.kozmaNitzan_conjecture3_holds`) and hence for `θ(p_c) = 0`.
Inputs: those of `CSH.cshHolds`; the statement is the additive weakening of [cite: KozmaNitzan2024, Conj. 1 (p. 3)]. -/
theorem additiveGluing_holds : Percolation.Continuity.Statements.AdditiveGluing :=
  additiveGluing_of_csh cshAll

/-- **Kozma–Nitzan's Conjecture 3 is a theorem.**  `KozmaNitzan2024_conjecture3`: for every `ε > 0` there is `δ > 0` (namely
`δ = ε/2`) such that for every `n`, every weight function `w : Sym2 (Fin n) → [0,1]`, every finite set `A` of vertices and all
vertices `o, b`, if `P(o ↔ A) > 1 − δ` and `P(a ↔ b) > 1 − δ` for every `a ∈ A`, then `P(o ↔ b) > 1 − ε` — with `δ` independent of the
graph and of `|A|`, which is the whole content.  Stated by Kozma and Nitzan as an open conjecture (the weakest of their gluing
conjectures, "we were not able to prove or disprove" the stronger Conjecture 1); proved here from additive gluing
`CSH.additiveGluing_holds` with `t = ε/2` (`CSH.conjecture3_of_csh`).  It is, letter for letter, the hypothesis of Kozma–Nitzan's
Theorem 6 as formalised in `KozmaNitzan2024_thm6`.
Inputs: those of `CSH.cshHolds`; statement [cite: KozmaNitzan2024, Conjecture 3 (p. 15)]. -/
theorem kozmaNitzan_conjecture3_holds : KozmaNitzan2024_conjecture3 :=
  conjecture3_of_csh cshAll

/-- **`θ(p_c) = 0` on `ℤ^d` for every `d ≥ 2`.** For nearest-neighbour Bernoulli bond percolation on the hypercubic lattice `ℤ^d`
(`zdGraph d`: vertices `Fin d → ℤ`, edges between points at distance `1`; measure `bondPercolation (zdGraph d) p`, each edge open with
probability `p` independently), write `θ(p)` for the probability that the open cluster of the origin is infinite and
`p_c = inf {p ∈ [0,1] | θ(p) > 0}`.  Then `θ(p_c) = 0` (`PercolationContinuity d`, i.e. `theta (zdGraph d) 0 (criticalProbI d) = 0`):
at the critical point there is almost surely no infinite open cluster; equivalently `p ↦ θ(p)` is continuous on `[0,1]`.

Status: a long-standing conjecture for general `d`; known before this work for `d = 2` (Harris 1960, Kesten 1980) and for `d ≥ 11`
(lace expansion: Hara–Slade for `d ≥ 19`, Fitzner–van der Hofstad for `d ≥ 11`); the cases `3 ≤ d ≤ 10` were open.  Proof here:
Kozma–Nitzan's Conjecture 3 (`CSH.kozmaNitzan_conjecture3_holds`, new) combined with their Theorem 6 "Conjecture 3 implies
`θ(p_c) = 0` on `ℤ^d` for every `d ≥ 2`" (`KozmaNitzan2024_thm6_holds`, a formalisation of the published argument: `d = 2` from
`p_c(ℤ²) = 1/2` and `θ(1/2) = 0`; `d ≥ 3` by the one-step renormalisation into a slab together with the absence of percolation at
`p_c(ℤ^d)` in half-spaces).  No lace expansion, no numerics.  The statement `PercolationContinuity` and the definitions of `θ` and
`p_c` it unfolds to are used exactly as defined in `CriticalContinuity` / `Basic`.
Inputs: [cite: KozmaNitzan2024, Thm. 6 with Conj. 3 (p. 15)] · [cite: HarrisPCPS1960] and [cite: KestenCMP1980] (`d = 2`) ·
[cite: BarskyGrimmettNewman1991, Thm. 1.1] with [cite: GrimmettMarstrand1990] (no percolation at `p_c` in half-spaces, `d ≥ 3`) ·
the inputs of `CSH.cshHolds`. -/
theorem percolationContinuity_allDimensions (d : ℕ) (hd : 2 ≤ d) : PercolationContinuity d :=
  percolationContinuity_of_csh cshAll d hd

/-- **`θ(p_c) = 0` on `ℤ³`.** For nearest-neighbour Bernoulli bond percolation on the cubic lattice `ℤ³`, the percolation
probability vanishes at the critical point: `θ(p_c(ℤ³)) = P_{p_c}(|C(0)| = ∞) = 0`.  The instance `d = 3` of
`CSH.percolationContinuity_allDimensions` — the first of the previously open dimensions `3 ≤ d ≤ 10`; the type of this theorem
is by definition `PercolationContinuity 3`, i.e. `theta (zdGraph 3) 0 (criticalProbI 3) = 0`.  Inputs: those of
`CSH.percolationContinuity_allDimensions`, [cite: KozmaNitzan2024, Thm. 6 with Conj. 3 (p. 15)]; the question is recorded in
[cite: GrimmettPercolation1999, §8.3] and [cite: FitznerVanDerHofstad2017, §1.1]. -/
theorem percolationContinuity_three : Percolation.Literature.PercolationContinuity 3 :=
  percolationContinuity_allDimensions 3 (by norm_num)

end CSH

end Percolation.Continuity
