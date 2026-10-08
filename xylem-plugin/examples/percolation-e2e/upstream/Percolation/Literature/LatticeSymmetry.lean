import Percolation.Literature.BondPercolationSymmetry
import Percolation.Literature.Crossings
import Percolation.Literature.SiteConnectionTools
import Percolation.Util.Linter

/-!
# Crossing events under the symmetries of `ℤ^d`

Infrastructure for the Russo–Seymour–Welsh decomposition
of `Percolation.Literature.rsw_half` (`RSW.lean`): every step of the printed proofs (Grimmett,
*Percolation* (1999), §11.7; Bollobás–Riordan, *Percolation* (2006), Ch. 3) uses that `P_p` on
`ℤ²` is invariant under translations, the transposition of the axes and reflections, e.g.
"the probability that an `n` by `n` square has an open vertical crossing is just `h_p(n, n)`"
(Bollobás–Riordan, Ch. 3, §3.4, before eq. (12); implicitly also in eq. (2) and Cor. 3(iii)) or
"let `X'(R')` be the event defined analogously to `X(R)` but reflected horizontally" (Ch. 3, proof
of Cor. 5).

The measure-level invariance is in `BondPercolationSymmetry.lean`, which provides the relabelling
`BondConfig.relabel (sym2Equiv φ) : ω ↦ φ '' ω` of bond configurations along a bijection `φ` of the
vertices and, for a graph isomorphism `φ : G ≃g H`, the identity `P_p^G ∘ (φ '' ·)⁻¹ = P_p^H`;
`SiteConnectionTools.lean` provides the automorphisms `zdShiftIso v` (translations) and
`zdSignedPermIso π ε` (signed coordinate permutations) of `ℤ^d`. This file adds the event-level
transport needed by the crossing arguments:

* `relabel_mem_openConnIn`, `relabel_mem_openCrossing`, `preimage_relabel_openCrossing`:
  `φ '' ·` carries `{x ↔ y in S}` to `{φ x ↔ φ y in φ(S)}` and pulls the open crossing event
  `C(φS; φA, φB)` back to `C(S; A, B)`; hence `P_p^H(C(φS; φA, φB)) = P_p^G(C(S; A, B))`
  (`bondPercolation_real_image`).
* The two special signed permutations of `ℤ²`/`ℤ^d` used by the RSW arguments, as abbreviations
  of `zdSignedPermIso`: the transposition of the axes `transposeIso` ("by symmetry
  `P(V(S)) = P(H(S))`") and the reflection in a coordinate hyperplane `reflectIso i` ("reflected
  horizontally", Bollobás–Riordan, Ch. 3, proof of Cor. 5; the reflection `ρ` of Grimmett 1999,
  proof of Lemma 11.73).
* Consequences on `ℤ²`: transposition exchanges `TB([0, n] × [0, m])` and `LR([0, m] × [0, n])`
  (`preimage_relabel_transpose_tbCrossing`), so `P_p(TB([0, n] × [0, m])) = crossingProb p m n`
  (`real_tbCrossing`); translated crossing events are equiprobable (`real_openCrossing_shift`).

Mathlib anchors: `SimpleGraph.Iso`, `SimpleGraph.Hom`, `SimpleGraph.Reachable.map`,
`Equiv.swap`, `Function.update`; anchors in this library: `BondConfig.relabel`, `sym2Equiv`,
`bondPercolation_real_preimage_relabel_iso`, `openGraph_relabel_adj_iff`
(`BondPercolationSymmetry.lean`), `zdShiftIso`, `zdSignedPermIso`, `Site.signedPerm`
(`SiteConnectionTools.lean`), `openConnIn`, `openCrossing`, `lrCrossing`, `tbCrossing`,
`crossingProb` (`Literature/Basic.lean`, `Crossings.lean`). Mathlib has no percolation events.

## References
* B. Bollobás, O. Riordan, *Percolation*, CUP (2006), Ch. 3 [BollobasRiordanPercolation2006].
* G. Grimmett, *Percolation*, 2nd ed., Springer (1999), §1.6, §11.7 [GrimmettPercolation1999].
-/

namespace Percolation.Literature

open MeasureTheory ProbabilityTheory unitInterval
open scoped ENNReal

noncomputable section

/-! ### Transport of connection and crossing events along a bijection of the vertices -/

section Transport

variable {V W : Type*}

/-- The graph homomorphism from the open graph of `ω` induced on `S` to the open graph of
`φ '' ω` induced on `φ(S)`, `v ↦ φ v`. [folklore] -/
def induceOpenHom (φ : V ≃ W) (ω : BondConfig V) (S : Set V) :
    (openGraph ω).induce S →g (openGraph (BondConfig.relabel (sym2Equiv φ) ω)).induce (φ '' S) where
  toFun v := ⟨φ v, Set.mem_image_of_mem _ v.2⟩
  map_rel' := by
    intro a b h
    rw [SimpleGraph.induce_adj] at h ⊢
    change (openGraph (BondConfig.relabel (sym2Equiv φ) ω)).Adj (φ a) (φ b)
    rwa [openGraph_relabel_adj_iff]

/-- Transport of restricted connection events: `{x ↔ y in S}` is carried by `φ '' ·` to
`{φ x ↔ φ y in φ(S)}`. [folklore] -/
theorem relabel_mem_openConnIn (φ : V ≃ W) {ω : BondConfig V} {S : Set V} {x y : V}
    (h : ω ∈ openConnIn S x y) :
    BondConfig.relabel (sym2Equiv φ) ω ∈ openConnIn (φ '' S) (φ x) (φ y) := by
  obtain ⟨hx, hy, hr⟩ := h
  exact ⟨Set.mem_image_of_mem _ hx, Set.mem_image_of_mem _ hy, hr.map (induceOpenHom φ ω S)⟩

/-- Transport of open crossing events: `C(S; A, B)` is carried by `φ '' ·` into
`C(φS; φA, φB)`. [folklore] -/
theorem relabel_mem_openCrossing (φ : V ≃ W) {ω : BondConfig V} {S A B : Set V}
    (h : ω ∈ openCrossing S A B) :
    BondConfig.relabel (sym2Equiv φ) ω ∈ openCrossing (φ '' S) (φ '' A) (φ '' B) := by
  obtain ⟨x, hx, y, hy, hxy⟩ := h
  exact ⟨φ x, Set.mem_image_of_mem _ hx, φ y, Set.mem_image_of_mem _ hy,
    relabel_mem_openConnIn φ hxy⟩

/-- Relabelling along `φ⁻¹` undoes relabelling along `φ`. [folklore] -/
theorem relabel_symm_relabel (φ : V ≃ W) (ω : BondConfig V) :
    BondConfig.relabel (sym2Equiv φ.symm) (BondConfig.relabel (sym2Equiv φ) ω) = ω := by
  rw [← sym2Equiv_symm]
  exact (BondConfig.relabel (sym2Equiv φ)).symm_apply_apply ω

/-- The open crossing event of the image sets pulls back to the open crossing event:
`(φ '' ·)⁻¹(C(φS; φA, φB)) = C(S; A, B)`. [folklore] -/
theorem preimage_relabel_openCrossing (φ : V ≃ W) (S A B : Set V) :
    BondConfig.relabel (sym2Equiv φ) ⁻¹' openCrossing (φ '' S) (φ '' A) (φ '' B) =
      openCrossing S A B := by
  ext ω
  constructor
  · intro h
    have h' := relabel_mem_openCrossing φ.symm h
    simpa only [relabel_symm_relabel, Equiv.symm_image_image] using h'
  · exact relabel_mem_openCrossing φ

/-- Transported open crossing events have the same probability: for a graph isomorphism
`φ : G ≃g H`, `P_p^H(C(φS; φA, φB)) = P_p^G(C(S; A, B))` (`bondPercolation_real_preimage_relabel_iso`
applied to `preimage_relabel_openCrossing`). This is the form in which "`h_p(m, n)` depends only
on the dimensions of the rectangle" and "by symmetry" steps are used (Bollobás–Riordan 2006,
Ch. 3; Grimmett 1999, §1.6, p. 16, invariance of `P_p` under lattice symmetries). [folklore] -/
theorem bondPercolation_real_image {G : SimpleGraph V} {H : SimpleGraph W} (φ : G ≃g H)
    (p : unitInterval) (S A B : Set V) :
    (bondPercolation H p).real (openCrossing (φ '' S) (φ '' A) (φ '' B)) =
      (bondPercolation G p).real (openCrossing S A B) := by
  rw [← bondPercolation_real_preimage_relabel_iso φ p]
  exact congrArg _ (preimage_relabel_openCrossing φ.toEquiv S A B)

end Transport

/-! ### The two signed permutations of `ℤ^d` used by the RSW arguments -/

section ZdSymmetries

variable {d : ℕ}

/-- Reflection of `ℤ^d` in the `i`-th coordinate hyperplane, `x ↦ (x with xᵢ ↦ -xᵢ)`: the signed
coordinate permutation `zdSignedPermIso 1 ε` with `ε = (1, …, -1, …, 1)` (`SiteConnectionTools.lean`).
(Bollobás–Riordan 2006, Ch. 3, proof of Cor. 5, "reflected horizontally"; Grimmett 1999, §11.7,
reflection `ρ` in the proof of Lemma 11.73.) [folklore] -/
abbrev reflectIso (i : Fin d) : LatticeModels.zdGraph d ≃g LatticeModels.zdGraph d :=
  zdSignedPermIso 1 (Function.update 1 i (-1))

/-- The reflected coordinate changes sign (coordinate form of the reflection symmetry of the
lattice). [cite: GrimmettPercolation1999, §11.7, proof of Lemma (11.73), p. 318 (reflection of paths in a lattice line; the coordinate swap is the analogous symmetry)] -/
@[simp] theorem reflectIso_apply_same (i : Fin d) (x : LatticeModels.Site d) : reflectIso i x i = -x i := by
  have : (Equiv.symm (1 : Equiv.Perm (Fin d))) i = i := rfl
  simp [reflectIso, this]

/-- The other coordinates are unchanged by the reflection. [cite: GrimmettPercolation1999, §11.7, proof of Lemma (11.73), p. 318 (reflection of paths in a lattice line; the coordinate swap is the analogous symmetry)] -/
@[simp] theorem reflectIso_apply_of_ne {i j : Fin d} (h : j ≠ i) (x : LatticeModels.Site d) :
    reflectIso i x j = x j := by
  have : (Equiv.symm (1 : Equiv.Perm (Fin d))) j = j := rfl
  simp [reflectIso, Function.update_of_ne h, this]

/-- The transposition `(x₀, x₁) ↦ (x₁, x₀)` of `ℤ²`, an automorphism of the square lattice: the
signed coordinate permutation `zdSignedPermIso (Equiv.swap 0 1) 1` (`SiteConnectionTools.lean`).
(Bollobás–Riordan 2006, Ch. 3, "by symmetry `P(V(S)) = P(H(S))`".) [folklore] -/
abbrev transposeIso : LatticeModels.zdGraph 2 ≃g LatticeModels.zdGraph 2 := zdSignedPermIso (Equiv.swap 0 1) 1

/-- First coordinate of the transpose (coordinate form of the transposition symmetry of `ℤ²`).
[cite: GrimmettPercolation1999, §11.7, proof of Lemma (11.73), p. 318 (reflection of paths in a lattice line; the coordinate swap is the analogous symmetry)] -/
@[simp] theorem transposeIso_apply_zero (x : LatticeModels.Site 2) : transposeIso x 0 = x 1 := by
  simp [transposeIso]

/-- Second coordinate of the transpose. [cite: GrimmettPercolation1999, §11.7, proof of Lemma (11.73), p. 318 (reflection of paths in a lattice line; the coordinate swap is the analogous symmetry)] -/
@[simp] theorem transposeIso_apply_one (x : LatticeModels.Site 2) : transposeIso x 1 = x 0 := by
  simp [transposeIso]

/-- The transposition is an involution. [cite: GrimmettPercolation1999, §11.7, proof of Lemma (11.73), p. 318 (reflection of paths in a lattice line; the coordinate swap is the analogous symmetry)] -/
theorem transposeIso_symm_apply (x : LatticeModels.Site 2) : transposeIso.symm x = transposeIso x := by
  ext i
  change (LatticeModels.Site.signedPerm (Equiv.swap 0 1) 1).symm x i = LatticeModels.Site.signedPerm (Equiv.swap 0 1) 1 x i
  fin_cases i <;> simp

/-- Images under the transposition are preimages. [cite: GrimmettPercolation1999, §11.7, proof of Lemma (11.73), p. 318 (reflection of paths in a lattice line; the coordinate swap is the analogous symmetry)] -/
theorem image_transposeIso (S : Set (LatticeModels.Site 2)) :
    (transposeIso : LatticeModels.Site 2 → LatticeModels.Site 2) '' S = transposeIso ⁻¹' S := by
  rw [show ((transposeIso : LatticeModels.Site 2 → LatticeModels.Site 2) '' S) = transposeIso.toEquiv '' S from rfl,
    Equiv.image_eq_preimage_symm]
  ext x
  simp only [Set.mem_preimage]
  rw [show transposeIso.toEquiv.symm x = transposeIso.symm x from rfl, transposeIso_symm_apply]

/-- The transpose of `[0, m] × [0, n]` is `[0, n] × [0, m]` (the rectangle symmetry behind
`h_p(m, n) ↔ v_p(n, m)`). [cite: GrimmettPercolation1999, §11.7, proof of Lemma (11.73), p. 318 (reflection of paths in a lattice line; the coordinate swap is the analogous symmetry)] -/
theorem preimage_transpose_rectangle (m n : ℕ) :
    (transposeIso : LatticeModels.Site 2 → LatticeModels.Site 2) ⁻¹' ↑(rectangle m n) = ↑(rectangle n m) := by
  ext x; simp only [Set.mem_preimage, Finset.mem_coe, mem_rectangle_iff, transposeIso_apply_zero,
    transposeIso_apply_one]; tauto

/-- The transpose of the left side of `[0, m] × [0, n]` is the bottom side of `[0, n] × [0, m]`.
[cite: GrimmettPercolation1999, §11.7, proof of Lemma (11.73), p. 318 (reflection of paths in a lattice line; the coordinate swap is the analogous symmetry)] -/
theorem preimage_transpose_leftSide (m n : ℕ) :
    (transposeIso : LatticeModels.Site 2 → LatticeModels.Site 2) ⁻¹' ↑(leftSide m n) = ↑(bottomSide n m) := by
  ext x; simp only [Set.mem_preimage, Finset.mem_coe, leftSide, bottomSide, Finset.mem_filter,
    mem_rectangle_iff, transposeIso_apply_zero, transposeIso_apply_one]; tauto

/-- The transpose of the right side of `[0, m] × [0, n]` is the top side of `[0, n] × [0, m]`.
[cite: GrimmettPercolation1999, §11.7, proof of Lemma (11.73), p. 318 (reflection of paths in a lattice line; the coordinate swap is the analogous symmetry)] -/
theorem preimage_transpose_rightSide (m n : ℕ) :
    (transposeIso : LatticeModels.Site 2 → LatticeModels.Site 2) ⁻¹' ↑(rightSide m n) = ↑(topSide n m) := by
  ext x; simp only [Set.mem_preimage, Finset.mem_coe, rightSide, topSide, Finset.mem_filter,
    mem_rectangle_iff, transposeIso_apply_zero, transposeIso_apply_one]; tauto

/-- Transposition exchanges left-right crossings of `[0, m] × [0, n]` and top-bottom crossings
of `[0, n] × [0, m]`: `(transpose '' ·)⁻¹ TB([0, n] × [0, m]) = LR([0, m] × [0, n])`.
(Bollobás–Riordan 2006, Ch. 3, the symmetry behind Cor. 3(iii) and eq. (2).) [folklore] -/
theorem preimage_relabel_transpose_tbCrossing (m n : ℕ) :
    BondConfig.relabel (sym2Equiv transposeIso.toEquiv) ⁻¹' tbCrossing n m = lrCrossing m n := by
  rw [tbCrossing, lrCrossing, ← preimage_transpose_rectangle, ← preimage_transpose_leftSide,
    ← preimage_transpose_rightSide, ← image_transposeIso, ← image_transposeIso,
    ← image_transposeIso]
  exact preimage_relabel_openCrossing transposeIso.toEquiv _ _ _

/-- `P_p(TB([0, n] × [0, m])) = P_p(LR([0, m] × [0, n])) = crossingProb p m n`: vertical
crossings of the transposed rectangle are as likely as horizontal crossings ("the probability that
an `n` by `n` square has an open vertical crossing is just `h_p(n, n)`", Bollobás–Riordan 2006,
Ch. 3, §3.4, before eq. (12); the same symmetry step is implicit in eq. (2) and in Cor. 3(iii), cf.
the docstrings of `Percolation.Literature.crossingProb_glue` and `Percolation.Literature.half_le_crossingProb_self` in
`RSW.lean`). [cite: BollobasRiordanPercolation2006, Ch. 3, §3.4, before eq. (12)] -/
theorem real_tbCrossing (p : unitInterval) (m n : ℕ) :
    (bondPercolation (LatticeModels.zdGraph 2) p).real (tbCrossing n m) = crossingProb p m n := by
  rw [crossingProb, ← preimage_relabel_transpose_tbCrossing,
    bondPercolation_real_preimage_relabel_iso]

/-- Translated open crossing events have the same probability (`h_p(m, n)` depends only on the
dimensions of the rectangle, "where `R` is any `m` by `n` rectangle in `ℤ²`", Bollobás–Riordan
2006, Ch. 3, definition of `h_p(m, n)`; Grimmett 1999, §1.4, p. 13, "the translation invariance of
the lattice and probability measure"). [cite: GrimmettPercolation1999, §1.4 p. 13 (translation invariance of P_p)] -/
theorem real_openCrossing_shift (p : unitInterval) (v : LatticeModels.Site d) (S A B : Set (LatticeModels.Site d)) :
    (bondPercolation (LatticeModels.zdGraph d) p).real (openCrossing ((· + v) '' S) ((· + v) '' A) ((· + v) '' B)) =
      (bondPercolation (LatticeModels.zdGraph d) p).real (openCrossing S A B) :=
  bondPercolation_real_image (zdShiftIso v) p S A B

end ZdSymmetries

end

end Percolation.Literature
