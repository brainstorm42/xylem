import Percolation.Literature.LatticeModels.LatticeGraph
import Percolation.Literature.SitePercolationMeasure
import Percolation.Util.Linter

/-!
# Lattice symmetries of Bernoulli bond percolation (proved tools)

Tools (all proved here), the bond analogue of the site-percolation relabelling lemmas of
`SitePercolationMeasure.lean` / `SiteConnectionTools.lean` (Grimmett, *Percolation*, 2nd ed. (1999),
§1.6, p. 16: `P_p` is a product measure and "is invariant under translations of the lattice"; used
implicitly whenever a crossing / circuit estimate proved for one box is applied to its translates,
e.g. §11.7, Fig. 11.27, four translated rectangles around an annulus).

* `sym2Equiv e : Sym2 V ≃ Sym2 W`, the action of a bijection `e : V ≃ W` on unordered pairs
  (`Sym2.map`; Mathlib has the embedding version `Function.Embedding.sym2Map` but no `Equiv`);
* `BondConfig.relabel e2 : BondConfig V ≃ᵐ BondConfig W` for `e2 : Sym2 V ≃ Sym2 W`, literally
  `SiteConfig.relabel e2` (`BondConfig V = Set (Sym2 V) = SiteConfig (Sym2 V)`), i.e.
  `ω ↦ e2 '' ω`;
* `setBernoulli_map_relabel`: if `e2` maps `E ⊆ Sym2 V` onto `E' ⊆ Sym2 W` then
  `setBer(E, p) ∘ (relabel e2)⁻¹ = setBer(E', p)` (reindexing a product measure,
  `Measure.infinitePi_map_piCongrLeft`);

Mathlib anchors: `Sym2.map`, `Sym2.map_map`, `Sym2.map_id`, `SimpleGraph.Iso.map_mem_edgeSet_iff`,
`ProbabilityTheory.setBernoulli_eq_map`, `MeasureTheory.Measure.infinitePi_map_piCongrLeft`,
`MeasurableEquiv.piCongrLeft`; anchors in this library: `bondPercolation`, `openGraph`, `SiteConfig.relabel`,
`Site.shift`, `zdGraph_adj_shift_iff`. Mathlib has no percolation measures.

## References
* G. Grimmett, *Percolation*, 2nd ed., Springer (1999), §1.6 p. 16 (translation invariance of
  `P_p`), §11.7 (its use for annulus circuits). [GrimmettPercolation1999]
-/

namespace Percolation.Literature

open MeasureTheory ProbabilityTheory unitInterval

noncomputable section

/-! ### Bijections acting on unordered pairs -/

section Sym2

variable {V W : Type*}

/-- The bijection of unordered pairs induced by a bijection of the underlying types,
`s(x, y) ↦ s(e x, e y)` (`Sym2.map e` with inverse `Sym2.map e.symm`). Mathlib only has the
embedding version `Function.Embedding.sym2Map`. [folklore] -/
def sym2Equiv (e : V ≃ W) : Sym2 V ≃ Sym2 W where
  toFun := Sym2.map e
  invFun := Sym2.map e.symm
  left_inv z := by rw [Sym2.map_map, e.symm_comp_self]; exact congrFun Sym2.map_id z
  right_inv z := by rw [Sym2.map_map, e.self_comp_symm]; exact congrFun Sym2.map_id z

/-- `sym2Equiv e` acts as `Sym2.map e`. [folklore] -/
@[simp] theorem sym2Equiv_apply (e : V ≃ W) (z : Sym2 V) : sym2Equiv e z = Sym2.map e z := rfl

/-- The inverse of `sym2Equiv e` is `sym2Equiv e⁻¹`. [folklore] -/
@[simp] theorem sym2Equiv_symm (e : V ≃ W) : (sym2Equiv e).symm = sym2Equiv e.symm := rfl

/-- On a pair: `sym2Equiv e s(x, y) = s(e x, e y)`. [folklore] -/
theorem sym2Equiv_mk (e : V ≃ W) (x y : V) : sym2Equiv e s(x, y) = s(e x, e y) := rfl

/-- A graph isomorphism maps the edge set onto the edge set (Mathlib's
`SimpleGraph.Iso.map_mem_edgeSet_iff`, restated for `sym2Equiv`). [folklore] -/
theorem sym2Equiv_mem_edgeSet_iff {G : SimpleGraph V} {G' : SimpleGraph W} (φ : G ≃g G')
    (z : Sym2 V) : sym2Equiv φ.toEquiv z ∈ G'.edgeSet ↔ z ∈ G.edgeSet := by
  induction z using Sym2.ind with
  | h x y => simp [φ.map_adj_iff]

end Sym2

/-! ### Relabelling bond configurations -/

section Relabel

variable {V W : Type*}

/-- Relabelling of bond configurations along a bijection of pairs `e2 : Sym2 V ≃ Sym2 W`,
`ω ↦ e2 '' ω`, as a measurable equivalence. Since `BondConfig V = Set (Sym2 V)` this is
literally `SiteConfig.relabel e2` (`SitePercolationMeasure.lean`); the abbreviation only fixes
the intended reading. (Grimmett 1999, §1.6.) [cite: GrimmettPercolation1999, §1.6] -/
abbrev BondConfig.relabel (e2 : Sym2 V ≃ Sym2 W) : BondConfig V ≃ᵐ BondConfig W :=
  SiteConfig.relabel e2

/-- `relabel e2 ω = e2 '' ω`. [folklore] -/
theorem BondConfig.relabel_apply (e2 : Sym2 V ≃ Sym2 W) (ω : BondConfig V) :
    BondConfig.relabel e2 ω = e2 '' ω := rfl

/-- `z ∈ relabel e2 ω ↔ e2⁻¹ z ∈ ω`. [folklore] -/
theorem BondConfig.mem_relabel_iff (e2 : Sym2 V ≃ Sym2 W) (ω : BondConfig V) (z : Sym2 W) :
    z ∈ BondConfig.relabel e2 ω ↔ e2.symm z ∈ ω :=
  SiteConfig.mem_relabel_iff e2 ω z

/-- **Reindexing a product Bernoulli measure.** If the bijection of pairs `e2` maps `E` onto `E'`
(`e2 z ∈ E' ↔ z ∈ E`), then the image of `setBer(E, p)` under `ω ↦ e2 '' ω` is `setBer(E', p)`:
the one-coordinate laws `p δ_{z ∈ E} + (1 - p) δ_⊥` are carried to each other and the product
measure is invariant under reindexing (`Measure.infinitePi_map_piCongrLeft`).
(Grimmett 1999, §1.6, invariance of the product measure `P_p`.) [cite: GrimmettPercolation1999, §1.6] -/
theorem setBernoulli_map_relabel (e2 : Sym2 V ≃ Sym2 W) {E : Set (Sym2 V)} {E' : Set (Sym2 W)}
    (hE : ∀ z, e2 z ∈ E' ↔ z ∈ E) (p : unitInterval) :
    (setBer(E, p)).map (BondConfig.relabel e2) = setBer(E', p) := by
  set ν' : Sym2 W → Measure Prop :=
    fun i => toNNReal p • Measure.dirac (i ∈ E') + toNNReal (σ p) • Measure.dirac False
  have hν : (fun z => ν' (e2 z)) = fun z : Sym2 V =>
      toNNReal p • Measure.dirac (z ∈ E) + toNNReal (σ p) • Measure.dirac False := by
    funext z
    simp only [ν', propext (hE z)]
  have hpi := Measure.infinitePi_map_piCongrLeft (X := fun _ : Sym2 W => Prop) ν' e2
  have hcoe : ⇑(MeasurableEquiv.piCongrLeft (fun _ : Sym2 W => Prop) e2) =
      fun χ : Sym2 V → Prop => fun w => χ (e2.symm w) := by
    funext χ w
    rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast, cast_eq]
  have hcomm : (BondConfig.relabel e2) ∘ (fun χ : Sym2 V → Prop => {v | χ v}) =
      (fun χ : Sym2 W → Prop => {w | χ w}) ∘ fun χ : Sym2 V → Prop => fun w => χ (e2.symm w) := by
    funext χ
    ext w
    simp
  rw [setBernoulli_eq_map, setBernoulli_eq_map,
    Measure.map_map (BondConfig.relabel e2).measurable measurable_setOf, hcomm,
    ← Measure.map_map measurable_setOf (by fun_prop), ← hν, ← hcoe, hpi]

/-- Applied form of `setBernoulli_map_relabel`: `setBer(E, p) {ω | e2 '' ω ∈ S} = setBer(E', p) S`
for every `S` (no measurability needed, `relabel e2` being a measurable equivalence). [cite: GrimmettPercolation1999, §1.6] -/
theorem setBernoulli_real_preimage_relabel (e2 : Sym2 V ≃ Sym2 W) {E : Set (Sym2 V)}
    {E' : Set (Sym2 W)} (hE : ∀ z, e2 z ∈ E' ↔ z ∈ E) (p : unitInterval)
    (S : Set (BondConfig W)) :
    (setBer(E, p)).real (BondConfig.relabel e2 ⁻¹' S) = (setBer(E', p)).real S := by
  rw [measureReal_def, measureReal_def, ← MeasurableEquiv.map_apply,
    setBernoulli_map_relabel e2 hE]

end Relabel

/-! ### Graph isomorphisms -/

section Iso

variable {V W : Type*} {G : SimpleGraph V} {G' : SimpleGraph W}

/-- Applied form: `P_p^G {ω | φ '' ω ∈ S} = P_p^{G'}(S)` for every event `S`.
(Grimmett 1999, §1.6.) [cite: GrimmettPercolation1999, §1.6] -/
theorem bondPercolation_real_preimage_relabel_iso (φ : G ≃g G') (p : unitInterval)
    (S : Set (BondConfig W)) :
    (bondPercolation G p).real (BondConfig.relabel (sym2Equiv φ.toEquiv) ⁻¹' S) =
      (bondPercolation G' p).real S :=
  setBernoulli_real_preimage_relabel _ (sym2Equiv_mem_edgeSet_iff φ) p S

/-- The open graph of a relabelled configuration: `φ x ∼ φ y` is open in `φ '' ω` iff `x ∼ y` is
open in `ω` (i.e. `openGraph (φ '' ω) = (openGraph ω).map φ`). [folklore] -/
theorem openGraph_relabel_adj_iff (e : V ≃ W) (ω : BondConfig V) (x y : V) :
    (openGraph (BondConfig.relabel (sym2Equiv e) ω)).Adj (e x) (e y) ↔ (openGraph ω).Adj x y := by
  rw [openGraph_adj, openGraph_adj, BondConfig.mem_relabel_iff, sym2Equiv_symm, sym2Equiv_mk,
    e.symm_apply_apply, e.symm_apply_apply, e.injective.ne_iff]

end Iso

/-! ### Translations of `ℤ^d` -/

section Shift

variable {d : ℕ}

/-- Applied form of translation invariance: `P_p {ω | ω + v ∈ S} = P_p(S)` for every event `S`
of bond percolation on `ℤ^d`. (Grimmett 1999, §1.6.) [cite: GrimmettPercolation1999, §1.6] -/
theorem bondPercolation_real_preimage_shift (v : LatticeModels.Site d) (p : unitInterval)
    (S : Set (BondConfig (LatticeModels.Site d))) :
    (bondPercolation (LatticeModels.zdGraph d) p).real (BondConfig.relabel (sym2Equiv (LatticeModels.Site.shift v)) ⁻¹' S) =
      (bondPercolation (LatticeModels.zdGraph d) p).real S :=
  bondPercolation_real_preimage_relabel_iso (G := LatticeModels.zdGraph d) (G' := LatticeModels.zdGraph d)
    { toEquiv := LatticeModels.Site.shift v, map_rel_iff' := fun {a b} => LatticeModels.zdGraph_adj_shift_iff v a b } p S

end Shift

end

end Percolation.Literature
