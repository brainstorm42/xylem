import Percolation.Continuity.CovTau.A2Defs
import Percolation.Util.Linter

/-!
# Star decomposition of the (A2) functionals and the product law of the neighbour set

Continues `Continuity/CovTau/A2Defs.lean` (functionals `Ef, Mf, Yf, Xf` of the two-source inequality (A2)
in the finite-sum framework of `BHK2006.core`).

For `Z ⊆ U` and the random set `S = rS U Z ω` of vertices of `U ∖ Z` joined to `Z` by an open edge
([VandenbergHaggstromKahn2005, §1 p. 4, identity (6)]):
* `CovTau.sC_restrict` — the set cluster splits at `Z ⊆ N`: `C^U_N = Z ∪ C^{U∖Z}_{(N∖Z) ∪ S}`; hence
  `CovTau.rest_restrict`: `U ∖ C^U_N = (U∖Z) ∖ C^{U∖Z}_{(N∖Z)∪S}`;
(The product law of `S` — needed because `X` is not monotone in the source set — is in `Continuity/CovTau/A2Push.lean`.)
[cite: VandenbergHaggstromKahn2005, §1 p. 4, identity (6)] [cite: KozmaNitzan2024, Conj. 1 (p. 3)]
-/

noncomputable section

namespace Percolation.Continuity.CovTau

open Percolation.Literature
open Percolation.Literature.BHK2006
open Percolation.Literature.DecisionTree (ind ind_of_mem ind_of_not_mem ind_nonneg)
open scoped Classical

variable {V : Type*}

/-! ### Splitting the set cluster at `Z` -/

/-- Walk splitting: an open path inside `U` from `y` to `c ∉ Z` either avoids `Z` (then `y ∉ Z` and the path lies
in `G[U∖Z]`) or has a last vertex in `Z`, after which it starts at a vertex of `S(ω)` and stays in `G[U∖Z]`.
[cite: VandenbergHaggstromKahn2005, §1 p. 4, identity (6)] -/
theorem reach_split {U Z : Finset V} {ω : Set (Sym2 V)} {y c : V}
    (h : (openGraph (ω ∩ edgesIn U)).Reachable y c) (hc : c ∉ Z) :
    (y ∉ Z ∧ (openGraph (ω ∩ edgesIn (U \ Z))).Reachable y c) ∨
      ∃ n ∈ rS U Z ω, (openGraph (ω ∩ edgesIn (U \ Z))).Reachable n c := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact Or.inl ⟨hc, SimpleGraph.Reachable.refl y⟩
  | @tail b c hyb hbc ih =>
    obtain ⟨hω, ⟨hbU, hcU⟩, hne⟩ := adj_iff.1 hbc
    by_cases hb : b ∈ Z
    · refine Or.inr ⟨c, ⟨Finset.mem_sdiff.2 ⟨hcU, hc⟩, b, hb, ?_⟩, SimpleGraph.Reachable.refl c⟩
      rw [Sym2.eq_swap]; exact hω
    · have hadj : (openGraph (ω ∩ edgesIn (U \ Z))).Adj b c :=
        adj_iff.2 ⟨hω, ⟨Finset.mem_sdiff.2 ⟨hbU, hb⟩, Finset.mem_sdiff.2 ⟨hcU, hc⟩⟩, hne⟩
      rcases ih hb with ⟨hyZ, hr⟩ | ⟨n, hn, hr⟩
      · exact Or.inl ⟨hyZ, hr.trans hadj.reachable⟩
      · exact Or.inr ⟨n, hn, hr.trans hadj.reachable⟩

/-- **The set cluster splits at `Z ⊆ N`**: `C^U_N = Z ∪ C^{U∖Z}_{(N ∖ Z) ∪ S(ω)}`.
[cite: VandenbergHaggstromKahn2005, §1 p. 4, identity (6)] -/
theorem sC_restrict {U Z : Finset V} (hZU : Z ⊆ U) {N : Set V} (hZN : (↑Z : Set V) ⊆ N) (ω : Set (Sym2 V)) :
    sC U N ω = ↑Z ∪ sC (U \ Z) ((N \ ↑Z) ∪ rS U Z ω) ω := by
  ext u
  constructor
  · rintro ⟨y, hyN, hr⟩
    by_cases hu : u ∈ Z
    · exact Or.inl hu
    · rcases reach_split hr hu with ⟨hyZ, hr'⟩ | ⟨n, hn, hr'⟩
      · exact Or.inr ⟨y, Or.inl ⟨hyN, hyZ⟩, hr'⟩
      · exact Or.inr ⟨n, Or.inr hn, hr'⟩
  · rintro (hu | ⟨y, hy, hr⟩)
    · exact subset_sC U N ω (hZN hu)
    · have hr' : (openGraph (ω ∩ edgesIn U)).Reachable y u :=
        hr.mono (openGraph_le (Set.inter_subset_inter_right _ (edgesIn_mono Finset.sdiff_subset)))
      rcases hy with ⟨hyN, -⟩ | ⟨hyUZ, z, hz, hyz⟩
      · exact ⟨y, hyN, hr'⟩
      · obtain ⟨hyU, hyZ⟩ := Finset.mem_sdiff.1 hyUZ
        refine ⟨z, hZN hz, (SimpleGraph.Adj.reachable (adj_iff.2 ⟨?_, ⟨hZU hz, hyU⟩, ?_⟩)).trans hr'⟩
        · rw [Sym2.eq_swap]; exact hyz
        · rintro rfl; exact hyZ hz

/-- Consequently `U ∖ C^U_N = (U ∖ Z) ∖ C^{U∖Z}_{(N∖Z) ∪ S(ω)}`.
[cite: VandenbergHaggstromKahn2005, §1 p. 4, identity (6)] -/
theorem rest_restrict {U Z : Finset V} (hZU : Z ⊆ U) {N : Set V} (hZN : (↑Z : Set V) ⊆ N) (ω : Set (Sym2 V)) :
    rest U N ω = rest (U \ Z) ((N \ ↑Z) ∪ rS U Z ω) ω := by
  ext u
  rw [mem_rest, mem_rest, sC_restrict hZU hZN ω, Finset.mem_sdiff, Set.mem_union, Finset.mem_coe]
  tauto

/-- The set clusters of `G[U ∖ Z]` do not depend on the edges meeting `Z`. [folklore] -/
theorem sC_diff_meeting (U Z : Finset V) (M : Set V) (ω : Set (Sym2 V)) :
    sC (U \ Z) M (ω \ meeting Z) = sC (U \ Z) M ω := by
  simp only [sC, diff_meeting_inter_edgesIn]

/-- The worlds of `G[U ∖ Z]` do not depend on the edges meeting `Z`. [folklore] -/
theorem rest_diff_meeting (U Z : Finset V) (M : Set V) (ω : Set (Sym2 V)) :
    rest (U \ Z) M (ω \ meeting Z) = rest (U \ Z) M ω := by
  ext u; rw [mem_rest, mem_rest, sC_diff_meeting]

variable [Fintype V]

/-! ### The star decomposition (BHK's (6)) for the world functionals -/

/-- **BHK's (6) for world functionals**: for `Z ⊆ U`, `Z ⊆ N`, `x ∉ Z` and any `G : Finset V → ℝ`,
`E[G(U ∖ C_N) ; x ↮ N] = Σ_ω weight(ω) · E'[G((U∖Z) ∖ C'_{(N∖Z)∪S(ω)}) ; x ↮ (N∖Z) ∪ S(ω)]`, primes denoting
`G[U ∖ Z]` with fresh variables. [cite: VandenbergHaggstromKahn2005, §1 p. 4, identity (6)] -/
theorem setStep_sum {U Z : Finset V} (hZU : Z ⊆ U) {x : V} (hx : x ∉ Z) {N : Set V}
    (hZN : (↑Z : Set V) ⊆ N) (w : Sym2 V → ℝ) (hm : ∑ ω, weight w ω = 1) (G : Finset V → ℝ) :
    ∑ ω, weight w ω * (G (rest U N ω) * ind (rD U x N) ω) =
      ∑ ω, weight w ω * ∑ ω', weight w ω' *
        (G (rest (U \ Z) ((N \ ↑Z) ∪ rS U Z ω) ω') * ind (rD (U \ Z) x ((N \ ↑Z) ∪ rS U Z ω)) ω') := by
  set A := meeting Z with hA
  set Φ : Set (Sym2 V) → Set (Sym2 V) → ℝ := fun ζ η =>
    G (rest (U \ Z) ((N \ ↑Z) ∪ rS U Z ζ) η) * ind (rD (U \ Z) x ((N \ ↑Z) ∪ rS U Z ζ)) η with hΦ
  have hind : ∀ (M : Set V) (η : Set (Sym2 V)),
      ind (rD (U \ Z) x M) (η \ meeting Z) = ind (rD (U \ Z) x M) η := by
    intro M η
    by_cases h : η ∈ rD (U \ Z) x M
    · rw [ind_of_mem h, ind_of_mem ((mem_rD_diff_meeting U Z x M η).2 h)]
    · rw [ind_of_not_mem h, ind_of_not_mem fun h' => h ((mem_rD_diff_meeting U Z x M η).1 h')]
  have hind' : ∀ ω : Set (Sym2 V), ind (rD U x N) ω = ind (rD (U \ Z) x ((N \ ↑Z) ∪ rS U Z ω)) ω := by
    intro ω
    by_cases h : ω ∈ rD U x N
    · rw [ind_of_mem h, ind_of_mem ((mem_rD_iff_restrict hZU hx hZN ω).1 h)]
    · rw [ind_of_not_mem h, ind_of_not_mem fun h' => h ((mem_rD_iff_restrict hZU hx hZN ω).2 h')]
  have h1 : ∀ ω, G (rest U N ω) * ind (rD U x N) ω = Φ (ω ∩ A) (ω \ A) := by
    intro ω
    simp only [hΦ, hA, rS_inter_meeting, rest_diff_meeting, hind, ← rest_restrict hZU hZN, hind']
  have h2 : ∀ ω ω', Φ (ω ∩ A) (ω' \ A) =
      G (rest (U \ Z) ((N \ ↑Z) ∪ rS U Z ω) ω') * ind (rD (U \ Z) x ((N \ ↑Z) ∪ rS U Z ω)) ω' := by
    intro ω ω'
    simp only [hΦ, hA, rS_inter_meeting, rest_diff_meeting, hind]
  calc ∑ ω, weight w ω * (G (rest U N ω) * ind (rD U x N) ω)
      = (∑ ω, weight w ω) * ∑ ω, weight w ω * Φ (ω ∩ A) (ω \ A) := by
        rw [hm, one_mul]; simp_rw [h1]
    _ = ∑ ω, weight w ω * ∑ ω', weight w ω' * Φ (ω ∩ A) (ω' \ A) := blockFubini w A Φ
    _ = _ := by simp_rw [h2]

end Percolation.Continuity.CovTau
