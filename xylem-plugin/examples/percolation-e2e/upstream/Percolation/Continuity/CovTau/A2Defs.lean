import Percolation.Continuity.AdditiveGluing.SandwichPrelim
import Percolation.Literature.ConditionalPositiveAssociationProofs
import Percolation.Literature.TwoClusterConditionalAssociation
import Percolation.Util.Linter

/-!
# The functionals of the two-source inequality (A2) behind the conditioned covariance transfer COV(τ) — finite-sum framework

Context. The proof runs a van den Berg–Häggström–Kahn-type induction on the vertex set for a
TWO-SOURCE inequality (A2) `E(N)·Y(N') ≤ M(N ∪ N')·X(N ∩ N')` between four functionals of "source
sets" `N, N'` of vertices, exactly in the style of this library's proof of
[VandenbergHaggstromKahn2005, Thm. 1.1] (`BHK2006.core`, file
`ConditionalPositiveAssociationProofs.lean`: percolation restricted to a vertex set `U`, clusters
`rC U s ω`, avoidance events `rD U s X`, the random neighbour set `rS U Z ω`, the star decomposition
`step_sum`, Ahlswede–Daykin).

THIS FILE sets up the functionals in that finite-sum framework (`μ` = the product weight `BHK2006.weight w` on
`Set (Sym2 V)`, percolation restricted to `U : Finset V` through `ω ∩ edgesIn U`) and records their elementary
properties; the induction itself is in the companion files.  For `U : Finset V`, owner `x`, observers `o, v`,
an increasing nonnegative `Ψ : Set V → ℝ` and a source set `N : Set V`:
* `CovTau.sC U N ω` — the vertex cluster of the SET `N` in `G[U]`; `CovTau.rest U N ω = U ∖ sC U N ω`;
* `CovTau.Ef w U x o v N = μ(o ↔ v, v ↮ x, v ↮ N)` (all in `G[U]`);  `CovTau.Mf w U x v N = μ(v ↮ x, v ↮ N)`;
* `CovTau.tf w U x Ψ = E Ψ(C_x)`, `CovTau.cf w U x v = μ(x ↔ v)`, `CovTau.Bf w U x v Ψ = Cov(Ψ(C_x), 1{v ∈ C_x})`
  (`≥ 0`, Harris), `CovTau.qf w U x o v = μ(o ↔ v | v ↮ x)` (`Ef ∅ / Mf ∅`);
* `CovTau.Yf w U x v Ψ N = E[ B_{G[U ∖ C_N]} ; x ∉ C_N ]` and `CovTau.Xf w U x o v Ψ N = E[ q_{G[U∖C_N]}·B_{G[U∖C_N]} ; x ∉ C_N ]`
  — the functionals `Y`, `X` (`B(W) := Cov_{G∖W}`, `q(W) := μ_{G∖W}(o↔v | v↮x)`).
Lemmas: nonnegativity, `Ef ≤ Mf`, antitonicity of `Ef`, `Mf` in the source set, the vanishing cases
(`v ∈ N` or `v = x` ⇒ `Ef = 0`; `x ∈ N` ⇒ `Yf = Xf = 0`; `x ∉ U` or `v ∉ U` or `v = x` ⇒ `Bf = 0`), and `N ⊆ sC U N ω`,
`x ∉ sC U N ω ↔ ω ∈ rD U x N`.
[cite: VandenbergHaggstromKahn2005, Thm. 1.1 (pp. 3–5)] [cite: KozmaNitzan2024, Conj. 1 (p. 3)]
-/

noncomputable section

namespace Percolation.Continuity.CovTau

open Percolation.Literature
open Percolation.Literature.BHK2006
open Percolation.Literature.DecisionTree (ind ind_of_mem ind_of_not_mem ind_nonneg)
open scoped Classical

variable {V : Type*}

/-! ### Set clusters in `G[U]` -/

/-- The vertex cluster `C_N` of the source SET `N` in the percolation restricted to `U`: the vertices joined to
some `z ∈ N` by an open path inside `U` (every `z ∈ N` belongs to it).
[cite: VandenbergHaggstromKahn2005, §1 p. 3 (clusters of the restricted model)] -/
def sC (U : Finset V) (N : Set V) (ω : Set (Sym2 V)) : Set V :=
  {u | ∃ z ∈ N, (openGraph (ω ∩ edgesIn U)).Reachable z u}

/-- The vertex set `U ∖ C_N` of the "world" left after deleting the cluster of `N` (a `Finset`).
[cite: VandenbergHaggstromKahn2005, §1 p. 4 (the induced model on `G` minus a vertex set)] -/
def rest (U : Finset V) (N : Set V) (ω : Set (Sym2 V)) : Finset V := U.filter fun u => u ∉ sC U N ω

/-- `1{o ∈ C_v}` as a (monotone) function of the open EDGE cluster of `v`. [folklore] -/
def oInd (o v : V) (C : Set (Sym2 V)) : ℝ := ind {C : Set (Sym2 V) | o = v ∨ ∃ e ∈ C, o ∈ e} C

/-- Unfolding of membership in the set cluster. [folklore] -/
theorem mem_sC {U : Finset V} {N : Set V} {ω : Set (Sym2 V)} {u : V} :
    u ∈ sC U N ω ↔ ∃ z ∈ N, (openGraph (ω ∩ edgesIn U)).Reachable z u := Iff.rfl

/-- Every source vertex lies in the set cluster. [folklore] -/
theorem subset_sC (U : Finset V) (N : Set V) (ω : Set (Sym2 V)) : N ⊆ sC U N ω :=
  fun z hz => ⟨z, hz, SimpleGraph.Reachable.refl z⟩

/-- The set cluster is monotone in the source set. [folklore] -/
theorem sC_mono_set (U : Finset V) {N N' : Set V} (h : N ⊆ N') (ω : Set (Sym2 V)) : sC U N ω ⊆ sC U N' ω :=
  fun _ ⟨z, hz, hr⟩ => ⟨z, h hz, hr⟩

/-- The cluster of the empty source set is empty. [folklore] -/
theorem sC_empty (U : Finset V) (ω : Set (Sym2 V)) : sC U (∅ : Set V) ω = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ ⟨_, hz, _⟩ => hz

/-- `rest U ∅ ω = U`. [folklore] -/
theorem rest_empty (U : Finset V) (ω : Set (Sym2 V)) : rest U (∅ : Set V) ω = U := by
  simp [rest, sC_empty]

/-- `rest U N ω ⊆ U`. [folklore] -/
theorem rest_subset (U : Finset V) (N : Set V) (ω : Set (Sym2 V)) : rest U N ω ⊆ U := Finset.filter_subset _ _

/-- Membership in `rest`. [folklore] -/
theorem mem_rest {U : Finset V} {N : Set V} {ω : Set (Sym2 V)} {u : V} :
    u ∈ rest U N ω ↔ u ∈ U ∧ u ∉ sC U N ω := Finset.mem_filter

/-- `x ∉ C_N` iff `x ↮ N` (the avoidance event `rD U x N`). [folklore] -/
theorem not_mem_sC_iff (U : Finset V) (N : Set V) (ω : Set (Sym2 V)) (x : V) :
    x ∉ sC U N ω ↔ ω ∈ rD U x N := by
  simp only [mem_sC, not_exists, not_and, rD, Set.mem_setOf_eq]
  exact ⟨fun h z hz hr => h z hz hr.symm, fun h z hz hr => h z hz hr.symm⟩

/-- The singleton cluster `sC U {x}` is the vertex cluster of `x`. [folklore] -/
theorem mem_sC_singleton {U : Finset V} {ω : Set (Sym2 V)} {x u : V} :
    u ∈ sC U ({x} : Set V) ω ↔ (openGraph (ω ∩ edgesIn U)).Reachable x u := by
  simp [mem_sC]

/-- `oInd` is an indicator: nonnegative. [folklore] -/
theorem oInd_nonneg (o v : V) (C : Set (Sym2 V)) : 0 ≤ oInd o v C := ind_nonneg _ _

/-- `oInd ≤ 1`. [folklore] -/
theorem oInd_le_one (o v : V) (C : Set (Sym2 V)) : oInd o v C ≤ 1 := ind_le_one _ _

/-- `oInd o v` is monotone in the edge set. [folklore] -/
theorem oInd_mono (o v : V) : Monotone (oInd o v) := by
  intro C C' h
  by_cases hC : C ∈ {C : Set (Sym2 V) | o = v ∨ ∃ e ∈ C, o ∈ e}
  · have hC' : C' ∈ {C : Set (Sym2 V) | o = v ∨ ∃ e ∈ C, o ∈ e} := by
      rcases hC with h1 | ⟨e, he, hoe⟩
      · exact Or.inl h1
      · exact Or.inr ⟨e, h he, hoe⟩
    simp only [oInd, ind_of_mem hC, ind_of_mem hC', le_refl]
  · simp only [oInd, ind_of_not_mem hC]; exact ind_nonneg _ _

variable [Fintype V]

end Percolation.Continuity.CovTau
