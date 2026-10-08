import Percolation.Continuity.CovTau.MetaA2Anti
import Percolation.Continuity.CovTau.StarBridgeS
import Percolation.Util.Linter

/-!
# "A2^H" and its diagonal (Htw) — UNCONDITIONAL

The generic two-source induction META-A2 (`CovTau.metaA2`, `Continuity/CovTau/MetaA2Anti.lean`; avoided SET `A`, arbitrary
nonnegative pure world functional `F`) is run with
* `A = S`, a marker set with `x ∈ S` (the owner) and `v ∉ S`, and
* `F(U') = H_{G[U']}(v) = Cov_{G[U']}(g(C_x), 1{v ↔ S})` (`CovTau.BfS`, `Continuity/CovTau/StarBridgeS.lean`)
  for a monotone edge-cluster functional `g ≥ 0`;
its two one-source inputs (★^H) and `Y^H ≤ H` are `CovTauStarN.yS_mul_mS_le` /
`CovTauStarN.yS_le_bS` (Gladkov's decision-tree Harris inequality along the exploration of `C_N` + van den
Berg–Häggström–Kahn's Theorem 1.4 with the set `S`).  RESULTS (no hypotheses beyond `x ∈ S`, `v ∉ S`, `g` monotone `≥ 0`,
normalised weights in `[0,1]`):
* `CovTau.a2H` — A2^H: `E_S(N)·Y^H(N') ≤ M_S(N ∪ N')·X^H(N ∩ N')` for all `N, N' ⊆ U`, every world `G[U]`;
* `CovTau.p1H` — its diagonal, display (Htw):
  `μ_U(o ↔ v, v ↮ S ∪ Y)·E_U[1{x ∉ C_Y}·H_{U ∖ C_Y}(v)] ≤ μ_U(v ↮ S ∪ Y)·E_U[1{x ∉ C_Y}·q_S(U ∖ C_Y)·H_{U ∖ C_Y}(v)]`,
  `q_S(U') = μ_{U'}(o ↔ v | v ↮ S)`;
* `CovTau.p1H_univ` — the same at `U = univ` (the whole graph), the form consumed downstream (Lemma H:
  Hpart ≥ 0 = world-wise set-4PT + (Htw)).
[cite: VandenbergHaggstromKahn2005, Thm. 1.1 (pp. 3–5), Thm. 1.3 (p. 6), Thm. 1.4 (p. 7)] [cite:
Gladkov2024, Thm. 3.2 (p. 4)] [cite: KozmaNitzan2024, Conj. 1 (p. 3)]
-/

noncomputable section

namespace Percolation.Continuity.CovTau

open Percolation.Literature
open Percolation.Literature.BHK2006
open Percolation.Literature.DecisionTree (ind ind_of_mem ind_of_not_mem ind_nonneg)
open scoped Classical

variable {V : Type*} [Fintype V]

/-- **A2^H, unconditional**: for a marker set `S ∋ x` with `v ∉ S`, a monotone edge-cluster functional `g ≥ 0`
and the world functional `H_{G[U']}(v) = Cov_{G[U']}(g(C_x), 1{v ↔ S})`, for all `N, N' ⊆ U`:
`E_S(N)·Y^H(N') ≤ M_S(N ∪ N')·X^H(N ∩ N')`.
[cite: VandenbergHaggstromKahn2005, Thm. 1.1 (pp. 3–5), Thm. 1.4 (p. 7)] [cite: Gladkov2024, Thm. 3.2 (p. 4)] -/
theorem a2H (w : Sym2 V → ℝ) (hw0 : ∀ e, 0 ≤ w e) (hw1 : ∀ e, w e ≤ 1) (hm : ∑ ω, weight w ω = 1)
    {x v : V} {S : Set V} (hxS : x ∈ S) (hvS : v ∉ S) (o : V) {g : Set (Sym2 V) → ℝ} (hg : Monotone g)
    (hg0 : ∀ C, 0 ≤ g C) (U : Finset V) {N N' : Set V} (hNU : N ⊆ ↑U) (hN'U : N' ⊆ ↑U) :
    Eav w U S o v N * Yw w U x (fun U' => BfS w U' x S v g) N' ≤
      Mav w U S v (N ∪ N') * Xw w U x S o v (fun U' => BfS w U' x S v g) (N ∩ N') :=
  metaA2 w hw0 hw1 hm x o v S (F := fun U' => BfS w U' x S v g)
    (fun U' => BfS_nonneg hw0 hw1 hm U' x S v hg hg0) (fun _ hv => BfS_eq_zero_of_not_mem w x hv hvS g) U
    (fun U' _ N _ => CovTauStarN.yS_mul_mS_le w hw0 hw1 hxS hvS hg hg0 U' N)
    (fun U' _ u => CovTauStarN.yS_le_bS w hw0 hw1 x hvS hg hg0 U' {u}) hNU hN'U

/-- **(Htw) = the diagonal of A2^H, unconditional**: for `Y ⊆ U`,
`E_S(Y)·Y^H(Y) ≤ M_S(Y)·X^H(Y)`, i.e.
`μ_U(o↔v, v↮S∪Y)·E_U[1{x∉C_Y} H_{U∖C_Y}(v)] ≤ μ_U(v↮S∪Y)·E_U[1{x∉C_Y} q_S(U∖C_Y) H_{U∖C_Y}(v)]`.
[cite: VandenbergHaggstromKahn2005, Thm. 1.1 (pp. 3–5), Thm. 1.4 (p. 7)] [cite: Gladkov2024, Thm. 3.2 (p. 4)] -/
theorem p1H (w : Sym2 V → ℝ) (hw0 : ∀ e, 0 ≤ w e) (hw1 : ∀ e, w e ≤ 1) (hm : ∑ ω, weight w ω = 1)
    {x v : V} {S : Set V} (hxS : x ∈ S) (hvS : v ∉ S) (o : V) {g : Set (Sym2 V) → ℝ} (hg : Monotone g)
    (hg0 : ∀ C, 0 ≤ g C) (U : Finset V) {Y : Set V} (hY : Y ⊆ ↑U) :
    Eav w U S o v Y * Yw w U x (fun U' => BfS w U' x S v g) Y ≤
      Mav w U S v Y * Xw w U x S o v (fun U' => BfS w U' x S v g) Y := by
  have h := a2H w hw0 hw1 hm hxS hvS o hg hg0 U hY hY
  simpa only [Set.union_self, Set.inter_self] using h

/-- **(Htw) on the whole graph** (`U = univ`): for every marker set `S ∋ x` with `v ∉ S`, every source set `Y`, every
monotone edge-cluster functional `g ≥ 0`,
`E_S(Y)·Y^H(Y) ≤ M_S(Y)·X^H(Y)` in `G = G[univ]`. [cite: VandenbergHaggstromKahn2005, Thm. 1.1 (pp. 3–5)]
[cite: Gladkov2024, Thm. 3.2 (p. 4)] -/
theorem p1H_univ (w : Sym2 V → ℝ) (hw0 : ∀ e, 0 ≤ w e) (hw1 : ∀ e, w e ≤ 1) (hm : ∑ ω, weight w ω = 1)
    {x v : V} {S : Set V} (hxS : x ∈ S) (hvS : v ∉ S) (o : V) {g : Set (Sym2 V) → ℝ} (hg : Monotone g)
    (hg0 : ∀ C, 0 ≤ g C) (Y : Set V) :
    Eav w Finset.univ S o v Y * Yw w Finset.univ x (fun U' => BfS w U' x S v g) Y ≤
      Mav w Finset.univ S v Y * Xw w Finset.univ x S o v (fun U' => BfS w U' x S v g) Y :=
  p1H w hw0 hw1 hm hxS hvS o hg hg0 Finset.univ (by simp)

end Percolation.Continuity.CovTau
