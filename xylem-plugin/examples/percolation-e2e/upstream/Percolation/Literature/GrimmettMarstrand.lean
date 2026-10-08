import Percolation.Literature.BondPercolationSymmetry
import Percolation.Literature.CriticalContinuityProofs
import Percolation.Literature.HalfSpace
import Percolation.Literature.InsertionTolerance
import Percolation.Literature.SubgraphMonotonicity
import Percolation.Util.Linter

/-!
# The Grimmett–Marstrand block theorem and `p_c(ℍ) = p_c(ℤ^d)` (Grimmett 1999, Thm. (7.2)(a), §7.3)

> "Let `d ≥ 2`, and let `ℍ = ℤ^{d-1} × ℤ₊` … we write `p_c(ℍ)` for the critical probability of
> `ℍ`. It follows by taking `F = ℍ` in Theorem (7.2) that `p_c(ℍ) = p_c`."

with Theorem (7.2)(a), p. 148 (Grimmett–Marstrand 1990): "Let `d ≥ 2`, and let `F` be an infinite
connected subset of `ℤ^d` with `p_c(F) < 1`.

## Design choices

* "there exists an integer `k`" is `∃ k : ℕ` with `B(0) = {0}` allowed (`2·0·F + B(0) = {0}`,
  of critical value `1`); the assembly treats `k = 0` separately, so nothing is assumed beyond
  the printed sentence.
* `2kF + B(k)` is `{z | ∃ x ∈ F, ∀ i, |zᵢ - 2k xᵢ| ≤ k}` (`B(k) = [-k, k]^d`, Grimmett §1.4).
* Coordinates as in `HalfSpace.lean`: `ℍ = {0 ≤ x₀}` (Grimmett: last coordinate).

## Sources

* G. Grimmett, *Percolation*, 2nd ed., Grundlehren 321, Springer 1999 [GrimmettPercolation1999]:
  §1.4 pp. 13–18 ((1.9), Peierls (1.17)–(1.18)); §1.6 p. 16 (invariance of `P_p`); §2.2
  Thm. (2.8) p. 35 (root-independence of `p_c`); §7.1 p. 146 (`p_c(G)`); §7.2 Thm. (7.2)
  p. 148 and its proof pp. 149–162; §7.3 p. 162 (`p_c(ℍ) = p_c`).
  PDF pages of the held copy = book pages + 13.
* G. R. Grimmett, J. M. Marstrand, *The supercritical phase of percolation is well behaved*,
  Proc. Roy. Soc. London Ser. A 430 (1990) 439–457 [GrimmettMarstrand1990] (the original of
  Thm. (7.2), as credited by Grimmett p. 147).
-/

noncomputable section

namespace Percolation.Literature

open MeasureTheory ProbabilityTheory LatticeModels
open scoped ENNReal

/-! ## `θ` and `p_c` under graph isomorphisms; `p_c` does not depend on the root -/

section General

variable {V W : Type*}

/-- `θ` is invariant under isomorphisms of rooted graphs: `θ_{G'}(φ x, p) = θ_G(x, p)` for
`φ : G ≃g G'` (Grimmett 1999, §1.6, p. 16: invariance of `P_p` under graph automorphisms; here
via the restriction coupling `theta_comap_le` in both directions).
[cite: GrimmettPercolation1999, §1.6 p. 16] -/
theorem theta_iso [Countable V] [Countable W] {G : SimpleGraph V} {G' : SimpleGraph W}
    (φ : G ≃g G') (x : V) (p : unitInterval) : theta G' (φ x) p = theta G x p := by
  have h1 : G = G'.comap φ := by
    ext a b; exact (φ.map_rel_iff).symm
  have h2 : G' = G.comap φ.symm := by
    ext a b; exact (φ.symm.map_rel_iff).symm
  refine le_antisymm ?_ ?_
  · have := theta_comap_le G (f := φ.symm) φ.symm.injective (φ x) p
    rw [← h2, φ.symm_apply_apply] at this
    exact this
  · have := theta_comap_le G' (f := φ) φ.injective x p
    rwa [← h1] at this

/-- **One-edge comparison of `θ` at adjacent roots**: for `x ∼ y`, `p · θ_y(p) ≤ θ_x(p)`.
Grimmett 1999, §2.2 p. 35 (the display before Thm. (2.8)): "`θ(p, x) ≥ P_p({x ↔ y} ∩ {y ↔ ∞})
≥ P_p(x ↔ y) θ(p, y)`" by FKG; here, for an edge `⟨x, y⟩`, by insertion tolerance instead
(opening the edge turns an infinite cluster at `y` into one at `x`,
`bondPercolation_pow_mul_real_preimage_openEdges_le`), which avoids FKG.
[cite: GrimmettPercolation1999, §2.2 p. 35, before Thm. (2.8)] -/
theorem mul_theta_le_theta_of_adj [Countable V] (G : SimpleGraph V) {x y : V} (hxy : G.Adj x y)
    (p : unitInterval) : (p : ℝ) * theta G y p ≤ theta G x p := by
  classical
  have hF : (↑({s(x, y)} : Finset (Sym2 V)) : Set (Sym2 V)) ⊆ G.edgeSet := by
    simp [hxy]
  have key := bondPercolation_pow_mul_real_preimage_openEdges_le G p {s(x, y)} hF
    (measurableSet_percolatesAt_holds x)
  rw [Finset.card_singleton, pow_one] at key
  refine le_trans (mul_le_mul_of_nonneg_left (measureReal_mono ?_) p.2.1) key
  intro ω hω
  simp only [Set.mem_preimage, percolatesAt, Set.mem_setOf_eq, Finset.coe_singleton] at hω ⊢
  refine Set.Infinite.mono ?_ hω
  intro z hz
  have hsub : ω ⊆ openEdges {s(x, y)} ω := subset_openEdges _ _
  have hz' : (openGraph (openEdges {s(x, y)} ω)).Reachable y z := openCluster_mono hsub y hz
  have hadj : (openGraph (openEdges {s(x, y)} ω)).Adj x y := by
    rw [openGraph_adj]
    exact ⟨subset_openEdges_right _ _ (Set.mem_singleton _), hxy.ne⟩
  exact hadj.reachable.trans hz'

/-- Positivity of `θ` passes between adjacent roots ("whence `p_c(x) ≤ p_c(y)`", Grimmett 1999,
p. 35). [cite: GrimmettPercolation1999, §2.2 p. 35, before Thm. (2.8)] -/
theorem theta_pos_of_adj [Countable V] (G : SimpleGraph V) {x y : V} (hxy : G.Adj x y)
    (p : unitInterval) (h : 0 < theta G y p) : 0 < theta G x p := by
  have hp : 0 < (p : ℝ) := by
    rcases eq_or_lt_of_le p.2.1 with h0 | h0
    · exfalso
      have : p = 0 := Subtype.ext h0.symm
      rw [this, theta_bot] at h
      exact lt_irrefl _ h
    · exact h0
  exact lt_of_lt_of_le (mul_pos hp h) (mul_theta_le_theta_of_adj G hxy p)

end General

/-! ## Lattice geometry: reflection, folding onto the half-space, the coordinate plane -/

section Geometry

variable {d : ℕ}

/-! ### Grimmett's thickenings `2kF + B(k)` -/

/-- The translation `x ↦ x + v` as an isomorphism between induced subgraphs of `ℤ^d` whose
vertex sets correspond under it (Grimmett 1999, §1.6 p. 16: `P_p` and hence `p_c` are
invariant under translations). [cite: GrimmettPercolation1999, §1.6 p. 16] -/
def induceShiftIso (v : Site d) {S T : Set (Site d)} (h : ∀ x, x ∈ T ↔ x + v ∈ S) :
    (zdGraph d).induce T ≃g (zdGraph d).induce S where
  toEquiv := (Site.shift v).subtypeEquiv h
  map_rel_iff' {a b} := zdGraph_adj_shift_iff v a.1 b.1

/-- The underlying map of `induceShiftIso`. [folklore] -/
@[simp] theorem coe_induceShiftIso_apply (v : Site d) {S T : Set (Site d)}
    (h : ∀ x, x ∈ T ↔ x + v ∈ S) (a : T) : ((induceShiftIso v h a : S) : Site d) = a + v := rfl

end Geometry

end Percolation.Literature
