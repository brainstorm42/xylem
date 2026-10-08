import Percolation.Literature.DynamicRenormalization
import Percolation.Util.Linter

/-!
# Dynamic renormalization, vertex form: the algorithm of Lemma (7.24) on `ℤ²` percolates

The probabilistic skeleton of the block construction
of Grimmett and Marstrand (Grimmett, *Percolation*, 2nd ed. (1999), §7.2, proof of Theorem (7.2),
pp. 155–162), separated from all geometry and proved, in the form of its printed driver, the
algorithm of Lemma (7.24), pp. 154–155:

> "Let `{Z(x) : x ∈ F}` be random variables taking values in `{0, 1}`. We construct a connected
> subset of `F` in the following recursive manner … Having defined `S₁, S₂, …, S_t = (A_t, B_t)`,
> … let `f` be the earliest edge … with the property that one endvertex lies in `A_t` and the
> other endvertex, `x_{t+1}` say, lies outside `A_t ∪ B_t`. We declare
> `S_{t+1} = (A_t ∪ {x_{t+1}}, B_t)` if `Z(x_{t+1}) = 1`, `(A_t, B_t ∪ {x_{t+1}})` if `Z(x_{t+1}) = 0`
> … (7.24) Lemma. Suppose there exists a constant `γ` such that `γ > p_c^site(F)` and
> `P(Z(x_{t+1}) = 1 | S₁, …, S_t) ≥ γ` for all `t`. Then `P(|A_∞| = ∞) > 0`."

Here `F = ℤ²` (the macro-lattice of site-boxes `B_x`, `x ∈ F`, p. 155, for a planar `F`), and
`Z(x_{t+1})` is the outcome of ONE adaptive fresh probe of a bond configuration on an arbitrary
countable graph (`AdaptiveProbing.lean`): the *examination* of the macro-vertex `x_{t+1} = a + d`
from its occupied neighbour `a` (holding a token `τ`: the seeds reached when `a` was occupied),
told the set `D` of directions towards the neighbours of `x_{t+1}` not yet determined (the
"branching out" of p. 161 is only needed towards those). A **site gadget system**
(`SiteGadgetSystem`) specifies envelope, examined edges (local), outcome, and the dynamic
disjointness of p. 162 ("these seeds have not been examined previously"): the edges an examination
reveals avoid the envelopes of the examinations it enables (`parent_disjoint`). The conditional
hypothesis (7.25) then takes the unconditional form `Lawful.prob_fail` (an examination from an
admissible token fails with probability `≤ ε`), by freshness and the product formula of
`AdaptiveProbing.lean` (`fresh_explorer`: STATIC disjointness of envelopes is only required of
pairs of examinations that can both occur and are not parent and child, see there).

The conclusion is reached, instead of by the stochastic domination of Lemma (7.24) (whose proof the
book omits, p. 155), by Peierls' argument on the macro-lattice, as in `MacroRenormalization.lean`:
declare a macro-edge of `ℤ²` closed iff one of its endpoints is BLOCKED (`x ∈ B_∞`); if `A_∞` is
finite it is, at a terminal time, the open cluster of the origin, so `Contour.exists_dualCircuit`
(`DualContours.lean`) gives a dual circuit of length `n` all of whose `n` edges have a blocked
endpoint; the set `X` of these blocked endpoints has `n ≤ 4|X|` and consists of targets of failed
examinations, none successful, so the supermartingale estimate
`AExplorer.measureReal_inter_le_nfail_le` bounds its probability by `ε^{|X|} P_p(A₀)`; summing over
the `≤ 4ⁿ` subsets `X` of the `≤ 2n` vertices of the circuit and over circuits (Peierls' count
`n(n+1)4ⁿ`, `peierls_term_le`) gives `P_p(A₀, |A_∞| < ∞) ≤ ⅔ P_p(A₀)` once `ε ≤ 2⁻³²`. So the
printed hypothesis "`γ > p_c^site(F)`" is replaced by the explicit, stronger "`1 - γ ≤ 2⁻³²`", which
is how the lemma is used on p. 162 (`ε` of (7.26) is at our disposal).

## Contents

* invariants (`MState.Inv`, `AdmAxioms`, `MState.AdmInv`, `RecSpec`, `replay_spec`) and
  **`fresh_explorer`**;
* the run: `occFinal` (`A_∞`), termination `exists_choice_eq_none`, `MState.macroConfig`,
  **`exists_dualCircuit_blk`**;

This file is the vertex-based counterpart of `DynamicRenormalization.lean` (directed-edge
attempts, Barsky–Grimmett–Newman), whose organisation and several proofs it follows verbatim; it
exists because in Grimmett–Marstrand's construction a failed examination pollutes its site-box,
which must therefore never be examined again (as in Lemma (7.24)), whereas directed-edge attempts
re-enter an unoccupied cell from every occupied neighbour. Not here: any geometry of `ℤ³`, seeds,
sprinkling (Lemmas (7.9), (7.17)) — the instance for `F = ℤ² × {0}` is built elsewhere.

## References

* G. Grimmett, *Percolation*, 2nd ed., Grundlehren 321, Springer 1999, §7.2: Lemma (7.24) and the
  algorithm before it, pp. 154–155; the construction, pp. 155–162 ((7.26), (7.33)); §1.4 pp. 15–18
  (Peierls' argument, (1.17)).
* G. R. Grimmett, J. M. Marstrand, *The supercritical phase of percolation is well behaved*,
  Proc. Roy. Soc. London Ser. A 430 (1990) 439–457 (proof of Lemma (7.24)).
-/

noncomputable section

namespace Percolation.Literature

open MeasureTheory ProbabilityTheory Contour ProbeHistory
open scoped ENNReal Classical

/-- A **site gadget system** over bond configurations on `V`: the vertex-based block construction
of Grimmett 1999, §7.2 (proof of Theorem (7.2), pp. 155–162, run by the algorithm of Lemma (7.24),
pp. 154–155). A macro-vertex `x = a + d` of `ℤ²` is *examined* once, from an occupied neighbour `a`
holding the token `τ`, with the set `D` of directions out of `x` towards the neighbours of `x` not
yet determined; the examination is an adaptive probe (envelope `zone`, examined edges `reveal`,
local), and its outcome `result` is either failure (`x` is blocked for ever) or a token for `x`.
The field `parent_disjoint` is Grimmett's dynamic condition: the edges an examination reveals avoid
the envelopes of the later examinations it enables (out of `x`, in the directions of `D`).
[cite: GrimmettPercolation1999, §7.2 pp. 154–156] -/
structure SiteGadgetSystem (V : Type*) where
  /-- tokens: the data held by an occupied macro-vertex (seeds reached, local information) -/
  Tok : Type
  /-- the initial edges, all required to be open ("the first step is successful", p. 156) -/
  U₀ : Finset (Sym2 V)
  /-- the token of the macro-origin when `U₀` is open -/
  init : Tok
  /-- admissibility of the token held at `a` for examining `a + d` -/
  Adm : LatticeModels.Site 2 → MDir → Tok → Prop
  /-- the envelope of the examination of `a + d` from `(a, τ)` with onward directions `D` -/
  zone : LatticeModels.Site 2 → MDir → Tok → Finset MDir → Finset (Sym2 V)
  /-- the edges it examines on the configuration `ω` -/
  reveal : LatticeModels.Site 2 → MDir → Tok → Finset MDir → BondConfig V → Finset (Sym2 V)
  /-- the examined edges lie in the envelope -/
  reveal_subset : ∀ a d τ D ω, reveal a d τ D ω ⊆ zone a d τ D
  /-- locality of the examined set -/
  reveal_local : ∀ a d τ D (ω ω' : BondConfig V), (∀ e ∈ reveal a d τ D ω, (e ∈ ω ↔ e ∈ ω')) →
    reveal a d τ D ω' = reveal a d τ D ω
  /-- the outcome: `none` (blocked) or the token of the newly occupied macro-vertex -/
  result : LatticeModels.Site 2 → MDir → Tok → Finset MDir → Finset (Sym2 V) → Option Tok
  /-- dynamic disjointness: the edges examined by a successful examination avoid the envelopes of
  the examinations out of the new vertex in the directions of `D` -/
  parent_disjoint : ∀ a d τ D (ω : BondConfig V) (τ' : Tok),
    result a d τ D (obs ω (reveal a d τ D ω)) = some τ' → ∀ d' ∈ D, ∀ D',
      Disjoint (reveal a d τ D ω) (zone (a + stepVec d) d' τ' D')

namespace SiteGadgetSystem

export GadgetSystem (tgt tgt_tgt_rev stepVec_injective_two eq_or_rev_of_edge_eq mem_openCluster_trans)

variable {V : Type*} (S : SiteGadgetSystem V)

/-- The adaptive probe of the examination of `a + d` from `(a, τ)` with onward directions `D`. [folklore] -/
def probe (a : LatticeModels.Site 2) (d : MDir) (τ : S.Tok) (D : Finset MDir) : AProbe V :=
  ⟨S.zone a d τ D, S.reveal a d τ D, S.reveal_subset a d τ D, S.reveal_local a d τ D⟩

/-- The probe examines `reveal`. [folklore] -/
@[simp] theorem reveal_probe (a : LatticeModels.Site 2) (d : MDir) (τ : S.Tok) (D : Finset MDir) (ω : BondConfig V) :
    (S.probe a d τ D).reveal ω = S.reveal a d τ D ω := rfl

/-- The probe's envelope is the zone. [folklore] -/
@[simp] theorem env_probe (a : LatticeModels.Site 2) (d : MDir) (τ : S.Tok) (D : Finset MDir) :
    (S.probe a d τ D).env = S.zone a d τ D := rfl

/-- The probe reads the open examined edges. [folklore] -/
theorem read_probe (a : LatticeModels.Site 2) (d : MDir) (τ : S.Tok) (D : Finset MDir) (ω : BondConfig V) :
    (S.probe a d τ D).read ω = obs ω (S.reveal a d τ D ω) := rfl

/-! ## The macro-state and its replay from a probing history -/

variable {S}

variable (S)

/-! ## Connectivity, abstractly: what occupied vertices certify -/

section Connectivity

variable {S}

variable {x₀ : V} {cell : V → LatticeModels.Site 2} {Conn : BondConfig V → V → V → Prop}
  {anchor : S.Tok → V} {Pre : S.Tok → BondConfig V → Prop}

end Connectivity

/-! ## Vertices of macro-edges -/

section Ends

/-- The vertices of a finite set of macro-edges (`Sym2.toFinset` of each edge). [folklore] -/
def vertsOf (Γ : Finset (Sym2 (LatticeModels.Site 2))) : Finset (LatticeModels.Site 2) := Γ.biUnion Sym2.toFinset

/-- Membership in `vertsOf`. [folklore] -/
theorem mem_vertsOf {Γ : Finset (Sym2 (LatticeModels.Site 2))} {v : LatticeModels.Site 2} :
    v ∈ vertsOf Γ ↔ ∃ x ∈ Γ, v ∈ x := by
  simp [vertsOf, Sym2.mem_toFinset]

/-- `n` macro-edges have at most `2n` vertices. [folklore] -/
theorem card_vertsOf_le (Γ : Finset (Sym2 (LatticeModels.Site 2))) : (vertsOf Γ).card ≤ 2 * Γ.card := by
  calc (vertsOf Γ).card ≤ ∑ x ∈ Γ, x.toFinset.card := Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ Γ, 2 := Finset.sum_le_sum fun x _ => by rw [Sym2.card_toFinset]; split_ifs <;> norm_num
    _ = 2 * Γ.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- A vertex of `ℤ²` lies on at most four of the edges of any set of edges of `𝕃²`. [folklore] -/
theorem card_filter_mem_le_four {Γ : Finset (Sym2 (LatticeModels.Site 2))}
    (hΓ : ∀ x ∈ Γ, x ∈ (LatticeModels.zdGraph 2).edgeSet) (v : LatticeModels.Site 2) :
    (Γ.filter fun x => v ∈ x).card ≤ 4 := by
  have hsub : (Γ.filter fun x => v ∈ x) ⊆ (Finset.univ : Finset MDir).image fun d => s(v, v + stepVec d) := by
    intro x hx
    obtain ⟨hxΓ, hvx⟩ := Finset.mem_filter.1 hx
    have hxE := hΓ x hxΓ
    induction x using Sym2.ind with
    | _ a b =>
      rw [SimpleGraph.mem_edgeSet] at hxE
      rcases Sym2.mem_iff.1 hvx with rfl | rfl
      · obtain ⟨d, rfl⟩ := (zdGraph_adj_iff_stepVec _ _).1 hxE
        exact Finset.mem_image.2 ⟨d, Finset.mem_univ _, rfl⟩
      · obtain ⟨d, rfl⟩ := (zdGraph_adj_iff_stepVec _ _).1 hxE.symm
        exact Finset.mem_image.2 ⟨d, Finset.mem_univ _, Sym2.eq_swap⟩
  calc (Γ.filter fun x => v ∈ x).card ≤ ((Finset.univ : Finset MDir).image fun d => s(v, v + stepVec d)).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset MDir).card := Finset.card_image_le
    _ = 4 := by simp

/-- If every edge of `Γ` (edges of `𝕃²`) has an endpoint in `X`, then `|Γ| ≤ 4 |X|`. [folklore] -/
theorem card_le_four_mul_card {Γ : Finset (Sym2 (LatticeModels.Site 2))} {X : Finset (LatticeModels.Site 2)}
    (hΓ : ∀ x ∈ Γ, x ∈ (LatticeModels.zdGraph 2).edgeSet) (hcov : ∀ x ∈ Γ, ∃ v ∈ X, v ∈ x) :
    Γ.card ≤ 4 * X.card := by
  have hsub : Γ ⊆ X.biUnion fun v => Γ.filter fun x => v ∈ x := by
    intro x hx
    obtain ⟨v, hv, hvx⟩ := hcov x hx
    exact Finset.mem_biUnion.2 ⟨v, hv, Finset.mem_filter.2 ⟨hx, hvx⟩⟩
  calc Γ.card ≤ (X.biUnion fun v => Γ.filter fun x => v ∈ x).card := Finset.card_le_card hsub
    _ ≤ ∑ v ∈ X, (Γ.filter fun x => v ∈ x).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ X, 4 := Finset.sum_le_sum fun v _ => card_filter_mem_le_four hΓ v
    _ = 4 * X.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

end Ends

/-! ## The main theorem: a lawful site gadget system has an infinite macro-cluster -/

section Main

variable (G : SimpleGraph V) (p : unitInterval)

variable {S G p}
variable {ε : ℝ} {x₀ : V} {cell : V → LatticeModels.Site 2} {Conn : BondConfig V → V → V → Prop}
  {anchor : S.Tok → V} {Pre : S.Tok → BondConfig V → Prop}

/-- The designated sets attached to a set `Γ` of `n` macro-edges: the sets `X` of vertices of `Γ`
with `n ≤ 4|X|`. [folklore] -/
def desigSets (Γ : Finset (Sym2 (LatticeModels.Site 2))) (n : ℕ) : Finset (Finset (LatticeModels.Site 2)) :=
  (vertsOf Γ).powerset.filter fun X => n ≤ 4 * X.card

/-- There are at most `4ⁿ` designated sets for `n` macro-edges. [folklore] -/
theorem card_desigSets_le {Γ : Finset (Sym2 (LatticeModels.Site 2))} {n : ℕ} (hcard : Γ.card = n) :
    (desigSets Γ n).card ≤ 4 ^ n := by
  calc (desigSets Γ n).card ≤ (vertsOf Γ).powerset.card := Finset.card_filter_le _ _
    _ = 2 ^ (vertsOf Γ).card := Finset.card_powerset _
    _ ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (hcard ▸ card_vertsOf_le Γ)
    _ = 4 ^ n := by rw [pow_mul]; norm_num

end Main

end SiteGadgetSystem

end Percolation.Literature
