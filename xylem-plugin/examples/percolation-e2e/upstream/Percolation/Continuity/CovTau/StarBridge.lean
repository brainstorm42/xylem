import Percolation.Continuity.CovTau.A2Defs
import Percolation.Continuity.CovTau.StarNReal
import Percolation.Util.Linter

/-!
# Weight sums over configurations restricted to a vertex set as expectations on the weighted cube

The dictionary between the finite weight-sum framework (`BHK2006.weight`, configurations `Set (Sym2 V)` restricted to
`pairsIn U`) and the expectations `ED` on the weighted cube of `DecisionTreeWeighted.lean`, used by the one-source bounds of
the conditioned covariance transfer: the marginal identity `ED_inter_eq` (integrating out unused coordinates), `sum_weight_mul_eq_ED`
and `sum_weight_restrict` (a weight sum is an `ED`-expectation, also after restriction to `pairsIn U`), the pair sets `pairsIn`,
`srcF` and their membership lemmas, and the rewriting of restricted clusters and avoidance indicators (`mem_sC_iff_mem_reached`,
`rest_eq_sdiff`, `ind_rD_eq`).
[cite: VandenbergHaggstromKahn2005, Thm. 1.1 (pp. 3–5), Thm. 1.4 (p. 7), eq. (6)] [cite: Gladkov2024, Thm. 3.2 (p. 4)]
-/

noncomputable section

namespace Percolation.Continuity

namespace CovTauStarN

open Finset MeasureTheory Percolation.Literature Percolation.Literature.DecisionTree
open Percolation.Literature.BHK2006 (weight edgesIn rC rD weight_nonneg)
open SetClusterExploration TreeHarris CovTau
open scoped Classical

/-! ### The marginal identity and the dictionary `G[U]` ↔ coordinates `pairsIn U` -/

section Marginal

variable {ι : Type*} [DecidableEq ι]

/-- **Marginal identity**: for `E ⊆ D`, the `D`-expectation of a function of `K ∩ E` is the `E`-expectation
(integrating out the coordinates of `D ∖ E`). [folklore] -/
theorem ED_inter_eq {D E : Finset ι} (hED : E ⊆ D) (p : ι → ℝ) (φ : Finset ι → ℝ) :
    ED D p (fun K => φ (K ∩ E)) = ED E p φ := by
  have key : ∀ X : Finset ι, Disjoint X E → ED (E ∪ X) p (fun K => φ (K ∩ E)) = ED E p φ := by
    intro X
    induction X using Finset.induction_on with
    | empty =>
        intro _
        rw [Finset.union_empty]
        exact ED_congr_on E p fun K hK => by rw [Finset.inter_eq_left.2 (Finset.mem_powerset.1 hK)]
    | @insert e X heX ih =>
        intro hdisj
        rw [Finset.disjoint_insert_left] at hdisj
        have hnot : e ∉ E ∪ X := by rw [Finset.mem_union, not_or]; exact ⟨hdisj.1, heX⟩
        have hins : ∀ S : Finset ι, insert e S ∩ E = S ∩ E := fun S => by
          ext i
          simp only [Finset.mem_inter, Finset.mem_insert]
          constructor
          · rintro ⟨rfl | hi, hiE⟩
            · exact absurd hiE hdisj.1
            · exact ⟨hi, hiE⟩
          · rintro ⟨hi, hiE⟩; exact ⟨Or.inr hi, hiE⟩
        rw [Finset.union_insert, ED_insert p hnot]
        simp only [hins]
        rw [ih hdisj.2]; ring
  rw [← Finset.union_sdiff_of_subset hED]
  exact key (D \ E) Finset.sdiff_disjoint

variable [Fintype ι]

/-- A `weight`-sum over `Set ι` is an `ED univ`-expectation. [folklore] -/
theorem sum_weight_mul_eq_ED (w : ι → ℝ) (g : Set ι → ℝ) :
    ∑ ω, weight w ω * g ω = ED Finset.univ w (fun K => g ↑K) := by
  unfold ED
  rw [Finset.powerset_univ]
  exact (Fintype.sum_equiv (Fintype.finsetEquivSet (α := ι)) _ _ fun K => by
    rw [Fintype.finsetEquivSet_apply, weight_coe_eq_wtW]).symm

end Marginal

section Dictionary

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The pairs inside `U` as a finite set of coordinates (`= BHK2006.edgesIn U`). [folklore] -/
def pairsIn (U : Finset V) : Finset (Sym2 V) := Finset.univ.filter fun e => e ∈ edgesIn U

omit [DecidableEq V] in
/-- Membership in `pairsIn`. [folklore] -/
theorem mem_pairsIn {U : Finset V} {e : Sym2 V} : e ∈ pairsIn U ↔ e ∈ edgesIn U := by
  simp [pairsIn]

/-- `↑(K ∩ pairsIn U) = ↑K ∩ edgesIn U`. [folklore] -/
theorem coe_inter_pairsIn (U : Finset V) (K : Finset (Sym2 V)) :
    (↑(K ∩ pairsIn U) : Set (Sym2 V)) = ↑K ∩ edgesIn U := by
  ext e; simp [pairsIn]

omit [DecidableEq V] in
/-- For `K ⊆ pairsIn U`: `↑K ∩ edgesIn U = ↑K`. [folklore] -/
theorem coe_inter_edgesIn_of_subset {U : Finset V} {K : Finset (Sym2 V)} (hK : K ⊆ pairsIn U) :
    (↑K : Set (Sym2 V)) ∩ edgesIn U = ↑K :=
  Set.inter_eq_left.2 fun _ he => mem_pairsIn.1 (hK (Finset.mem_coe.1 he))

/-- **Restriction**: a `weight`-sum of a function of `ω ∩ edgesIn U` is an `ED (pairsIn U)`-expectation.
[cite: VandenbergHaggstromKahn2005, §1 p. 3 (the restricted model)] -/
theorem sum_weight_restrict (w : Sym2 V → ℝ) (U : Finset V) (g : Set (Sym2 V) → ℝ)
    (hg : ∀ ω, g ω = g (ω ∩ edgesIn U)) :
    ∑ ω, weight w ω * g ω = ED (pairsIn U) w (fun K => g ↑K) := by
  rw [sum_weight_mul_eq_ED]
  have : (fun K : Finset (Sym2 V) => g ↑K) = fun K => (fun K' : Finset (Sym2 V) => g ↑K') (K ∩ pairsIn U) := by
    funext K; dsimp only; rw [coe_inter_pairsIn, ← hg]
  have h2 := ED_inter_eq (Finset.subset_univ (pairsIn U)) w (fun K' : Finset (Sym2 V) => g ↑K')
  rw [← this] at h2
  exact h2

/-- The pairs inside `U ∖ W` are the pairs inside `U` missing `W`. [folklore] -/
theorem pairsIn_sdiff (U W : Finset V) : pairsIn (U \ W) = off W (pairsIn U) := by
  ext e
  rw [mem_pairsIn, mem_off, mem_pairsIn]
  simp only [edgesIn, Set.mem_setOf_eq, Finset.mem_sdiff]
  exact ⟨fun h => ⟨fun v hv => (h v hv).1, fun v hv => (h v hv).2⟩, fun h v hv => ⟨h.1 v hv, h.2 v hv⟩⟩

/-- For `K ⊆ pairsIn U`: `off W K = K ∩ pairsIn (U ∖ W)`. [folklore] -/
theorem off_eq_inter {U : Finset V} (W : Finset V) {K : Finset (Sym2 V)} (hK : K ⊆ pairsIn U) :
    off W K = K ∩ pairsIn (U \ W) := by
  rw [pairsIn_sdiff]
  ext e
  rw [mem_off, Finset.mem_inter, mem_off]
  exact ⟨fun h => ⟨h.1, hK h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩

/-- The source set as a `Finset`. [folklore] -/
def srcF (N : Set V) : Finset V := Finset.univ.filter fun u => u ∈ N

omit [DecidableEq V] in
/-- Membership in `srcF`. [folklore] -/
theorem mem_srcF {N : Set V} {u : V} : u ∈ srcF N ↔ u ∈ N := by simp [srcF]

/-- **Set cluster ↔ reached set**: for `K ⊆ pairsIn U`, `CovTau.sC U N ↑K = SetClusterExploration.reached (pairsIn U) (srcF N) K`.
[folklore] -/
theorem mem_sC_iff_mem_reached {U : Finset V} {N : Set V} {K : Finset (Sym2 V)} (hK : K ⊆ pairsIn U) (u : V) :
    u ∈ sC U N (↑K : Set (Sym2 V)) ↔ u ∈ reached (pairsIn U) (srcF N) K := by
  rw [mem_sC, coe_inter_edgesIn_of_subset hK, mem_reached_iff' hK]
  exact ⟨fun ⟨z, hz, h⟩ => ⟨z, mem_srcF.2 hz, h⟩, fun ⟨z, hz, h⟩ => ⟨z, mem_srcF.1 hz, h⟩⟩

/-- `rest U N ↑K = U ∖ reached` for `K ⊆ pairsIn U`. [folklore] -/
theorem rest_eq_sdiff {U : Finset V} {N : Set V} {K : Finset (Sym2 V)} (hK : K ⊆ pairsIn U) :
    rest U N (↑K : Set (Sym2 V)) = U \ reached (pairsIn U) (srcF N) K := by
  ext u
  rw [mem_rest, Finset.mem_sdiff, mem_sC_iff_mem_reached hK]

/-- `1{x ↮ N in G[U]}` on `K ⊆ pairsIn U` is `1{x ∉ reached}`. [folklore] -/
theorem ind_rD_eq {U : Finset V} (x : V) (N : Set V) {K : Finset (Sym2 V)} (hK : K ⊆ pairsIn U) :
    ind (rD U x N) (↑K : Set (Sym2 V)) = ind {L : Finset (Sym2 V) | x ∉ reached (pairsIn U) (srcF N) L} K := by
  refine BystanderBHK.ind_congr ?_
  rw [← not_mem_sC_iff, Set.mem_setOf_eq, mem_sC_iff_mem_reached hK]

end Dictionary

end CovTauStarN

end Percolation.Continuity

end
