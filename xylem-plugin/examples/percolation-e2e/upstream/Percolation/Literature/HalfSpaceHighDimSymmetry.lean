import Percolation.Literature.HalfSpaceHighDimSeeds
import Percolation.Util.Linter

/-!
# Symmetry between the subfacets in `ℤ^d`: (7.51) and the "square-root trick" step of Lemma (7.36)

Seventh step of the bottom-up proof, in every dimension
`d`, of the finite-size criterion of the Barsky–Grimmett–Newman theorem (Grimmett, *Percolation*,
2nd ed. (1999), §7.3, Lemma (7.36) = Barsky–Grimmett–Newman 1991, Prop. 2.1), after its `d = 3`
models `HalfSpaceBrickSymmetry.lean` and `CleanSeeds.lean` ((7.51) for a valid rule). Grimmett,
pp. 168–169:

> "Inequalities (7.49)–(7.50) are not quite good enough for our purpose, since the property of
> being good requires seeds in every 'subfacet' `S_i` of `S` and `T_j` of `T`. This we shall obtain
> by further applications of the FKG inequality. … By symmetry, the `X_j` (respectively `Y_i`)
> have the same distribution … Therefore, `P(X_1 = 0)⁴ = ∏_j P(X_j = 0) ≤ P(X_j = 0 for all j)
> ≤ P(X = 0)` by the FKG inequality and (7.49) … Similarly, (7.51)."

In `ℤ^d` (BGN 1991, p. 127: "by symmetry and the Harris–FKG inequality") the top has `2^{d-1}`
subfacets `T_ρ` and the sides `(d-1)2^{d-1}` subfacets `S_{a,τ}` (`HalfSpaceHighDim.lean`).
Contents (coordinates of `HalfSpace.lean`, vertical axis `0`):

* the signed coordinate permutations `Site.signedPerm π ε` with `π 0 = 0`, `ε 0 = 1` preserve
  the brick, its boundary, top, sides, `B(L,H)*` and `b(0)`, hence linking
  (`BGNd.linked_relabel_signedPerm_iff`); the transpositions of two horizontal axes show that the
  facet counts `V^a` are equidistributed (`BGNd.prob_facetCountLT_eq`);
* the reflections `refl ε` (`π = 1`) also respect a valid seed rule, hence carry `okEventR F` to
  `okEventR (refl ε '' F)` (`BGNd.prob_okEventR_image_refl`); they act transitively on the top
  subfacets (`refl ε '' T_ρ = T_{ρ'}`, flipping the signs `ρ j` where `ε j = -1`) and, for each
  horizontal axis `a`, on the `2^{d-1}` side subfacets `S_{a,τ}` (`BGNd.image_refl_topSubfacet`,
  `BGNd.image_refl_sideSubfacet`), so that the `X_ρ`, and for fixed `a` the `Y_{a,τ}`, are
  equidistributed;
* **(7.51)**: `P(X_ρ = 0)^{2^{d-1}} ≤ P(no linked top vertex has its rule-edges open)` and
  `P(Y_{a,τ} = 0)^{2^{d-1}} ≤ P(no linked vertex of the facets |x_a| = L has its rule-edges open)`
  (`BGNd.prob_compl_okEventR_topSubfacet_pow_le`, `BGNd.prob_compl_okEventR_sideSubfacet_pow_le`),
  whose right-hand sides are estimated in `HalfSpaceHighDimSeeds.lean`.

## References

* G. Grimmett, *Percolation*, 2nd ed., Grundlehren 321, Springer 1999, §7.3, proof of
  Lemma (7.36), pp. 168–169, (7.51).
* D. J. Barsky, G. R. Grimmett, C. M. Newman, Probab. Theory Related Fields 90 (1991) 111–148,
  §2, p. 127.
-/

noncomputable section

namespace Percolation.Literature

open _root_.MeasureTheory _root_.ProbabilityTheory _root_.Filter LatticeModels unitInterval
open scoped _root_.ENNReal _root_.Topology

namespace BGNd

variable {d : ℕ}

/-! ## Signed permutations fixing the vertical axis -/

section SignedPerm

variable [NeZero d] {π : Equiv.Perm (Fin d)} {ε : Fin d → ℤˣ}

/-- A permutation fixing `0` has inverse fixing `0`. [folklore] -/
theorem perm_symm_zero (hπ : π 0 = 0) : π.symm 0 = 0 := by
  rw [← hπ, Equiv.symm_apply_apply, hπ]

/-- The height is preserved: `(φ x) 0 = x 0` for `π 0 = 0`, `ε 0 = 1`. [folklore] -/
theorem signedPerm_apply_zero (hπ : π 0 = 0) (hε : ε 0 = 1) (x : Site d) : Site.signedPerm π ε x 0 = x 0 := by
  rw [Site.signedPerm_apply, perm_symm_zero hπ, hε, Units.val_one, one_mul]

omit [NeZero d] in
/-- Absolute values of coordinates are permuted: `|(φ x) i| = |x (π⁻¹ i)|`. [folklore] -/
theorem abs_signedPerm_apply (x : Site d) (i : Fin d) : |Site.signedPerm π ε x i| = |x (π.symm i)| := by
  rw [Site.signedPerm_apply, BGN.abs_units_mul]

/-- A permutation fixing `0` permutes the horizontal axes (universal form). [folklore] -/
theorem forall_ne_zero_perm_iff (hπ : π 0 = 0) (P : Fin d → Prop) :
    (∀ j : Fin d, j ≠ 0 → P (π.symm j)) ↔ ∀ j : Fin d, j ≠ 0 → P j := by
  constructor
  · intro h j hj
    have := h (π j) (fun h' => hj (by rw [← Equiv.symm_apply_apply π j, h', perm_symm_zero hπ]))
    rwa [Equiv.symm_apply_apply] at this
  · intro h j hj
    exact h _ fun h' => hj (by rw [← Equiv.apply_symm_apply π j, h', hπ])

/-- A permutation fixing `0` permutes the horizontal axes (existential form). [folklore] -/
theorem exists_ne_zero_perm_iff (hπ : π 0 = 0) (P : Fin d → Prop) :
    (∃ j : Fin d, j ≠ 0 ∧ P (π.symm j)) ↔ ∃ j : Fin d, j ≠ 0 ∧ P j := by
  constructor
  · rintro ⟨j, hj, h⟩
    exact ⟨π.symm j, fun h' => hj (by rw [← Equiv.apply_symm_apply π j, h', hπ]), h⟩
  · rintro ⟨j, hj, h⟩
    refine ⟨π j, fun h' => hj (by rw [← Equiv.symm_apply_apply π j, h', perm_symm_zero hπ]), ?_⟩
    rwa [Equiv.symm_apply_apply]

/-- Signed permutations fixing the vertical axis preserve the brick. [folklore] -/
theorem signedPerm_mem_brick (hπ : π 0 = 0) (hε : ε 0 = 1) {L H : ℕ} (x : Site d) :
    Site.signedPerm π ε x ∈ brick d L H ↔ x ∈ brick d L H := by
  simp only [mem_brick, signedPerm_apply_zero hπ hε, abs_signedPerm_apply]
  rw [forall_ne_zero_perm_iff hπ fun j => |x j| ≤ L]

/-- … the sides … [folklore] -/
theorem signedPerm_mem_sides (hπ : π 0 = 0) (hε : ε 0 = 1) {L H : ℕ} (x : Site d) :
    Site.signedPerm π ε x ∈ sides d L H ↔ x ∈ sides d L H := by
  simp only [sides, Set.mem_setOf_eq, signedPerm_mem_brick hπ hε, abs_signedPerm_apply]
  rw [exists_ne_zero_perm_iff hπ fun j => |x j| = L]

/-- … the boundary … [folklore] -/
theorem signedPerm_mem_brickBoundary (hπ : π 0 = 0) (hε : ε 0 = 1) {L H : ℕ} (x : Site d) :
    Site.signedPerm π ε x ∈ brickBoundary d L H ↔ x ∈ brickBoundary d L H := by
  simp only [mem_brickBoundary_iff, signedPerm_mem_brick hπ hε, signedPerm_apply_zero hπ hε,
    abs_signedPerm_apply]
  rw [exists_ne_zero_perm_iff hπ fun j => |x j| = L]

/-- … and are automorphisms of `B(L,H)*`. [folklore] -/
theorem signedPerm_brickStar_adj (hπ : π 0 = 0) (hε : ε 0 = 1) (L H : ℕ) (u v : Site d) :
    (brickStar d L H).Adj (Site.signedPerm π ε u) (Site.signedPerm π ε v) ↔ (brickStar d L H).Adj u v := by
  have hz : (zdGraph d).Adj (Site.signedPerm π ε u) (Site.signedPerm π ε v) ↔ (zdGraph d).Adj u v :=
    (zdSignedPermIso π ε).map_rel_iff'
  simp only [brickStar, starGraph_adj, signedPerm_mem_brick hπ hε, signedPerm_mem_brickBoundary hπ hε, hz]

omit [NeZero d] in
/-- Signed permutations map squares to squares: `φ '' (c + b_k(m)) = φ c + b_{π k}(m)`. [folklore] -/
theorem image_square_signedPerm (π : Equiv.Perm (Fin d)) (ε : Fin d → ℤˣ) (k : Fin d) (m : ℕ) (c : Site d) :
    Site.signedPerm π ε '' square k m c = square (π k) m (Site.signedPerm π ε c) := by
  have key : ∀ y : Site d, Site.signedPerm π ε y ∈ square (π k) m (Site.signedPerm π ε c) ↔ y ∈ square k m c := by
    intro y
    simp only [mem_square, Site.signedPerm_apply, Equiv.symm_apply_apply]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, fun j hj => ?_⟩
      · rcases Int.units_eq_one_or (ε (π k)) with h | h <;> simp [h] at h1 <;> exact h1
      · have := h2 (π j) (fun h => hj (π.injective h))
        rw [Equiv.symm_apply_apply, ← mul_sub, BGN.abs_units_mul] at this
        exact this
    · rintro ⟨h1, h2⟩
      refine ⟨by rw [h1], fun i hi => ?_⟩
      have := h2 (π.symm i) (fun h => hi (by rw [← h, Equiv.apply_symm_apply]))
      rwa [← mul_sub, BGN.abs_units_mul]
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (key z).2 hz
  · intro hy
    refine ⟨(Site.signedPerm π ε).symm y, (key _).1 ?_, Equiv.apply_symm_apply _ _⟩
    rwa [Equiv.apply_symm_apply]

/-- Signed permutations fixing the vertical axis map `b(0)` onto itself. [folklore] -/
theorem image_centralSquare_signedPerm (hπ : π 0 = 0) (m : ℕ) :
    Site.signedPerm π ε '' centralSquare d m = centralSquare d m := by
  rw [centralSquare, image_square_signedPerm, hπ]
  simp

/-- **Linking is carried by the symmetries of the brick.** [folklore] -/
theorem linked_relabel_signedPerm_iff (hπ : π 0 = 0) (hε : ε 0 = 1) (m L H : ℕ) (x : Site d) (ω : BondConfig (Site d)) :
    Linked d m L H (Site.signedPerm π ε x) (BondConfig.relabel (sym2Equiv (Site.signedPerm π ε)) ω) ↔
      Linked d m L H x ω := by
  have hK := signedPerm_brickStar_adj hπ hε L H
  simp only [Linked]
  constructor
  · rintro ⟨y', hy', hxy'⟩
    obtain ⟨y, hy, rfl⟩ : y' ∈ Site.signedPerm π ε '' centralSquare d m := by
      rwa [image_centralSquare_signedPerm hπ]
    rw [openClusterIn_relabel (Site.signedPerm π ε) hK ω y] at hxy'
    exact ⟨y, hy, ((Site.signedPerm π ε).injective.mem_set_image).1 hxy'⟩
  · rintro ⟨y, hy, hxy⟩
    refine ⟨Site.signedPerm π ε y, ?_, ?_⟩
    · rw [← image_centralSquare_signedPerm (ε := ε) hπ m]; exact ⟨y, hy, rfl⟩
    · rw [openClusterIn_relabel (Site.signedPerm π ε) hK ω y]; exact ⟨x, hxy, rfl⟩

/-- The facet statistics are permuted: `φ x ∈ V^a-set(φ·ω) ↔ x ∈ V^{π⁻¹ a}-set(ω)`. [folklore] -/
theorem signedPerm_mem_facetLinked_iff (hπ : π 0 = 0) (hε : ε 0 = 1) (m L H : ℕ) (a : Fin d) (x : Site d)
    (ω : BondConfig (Site d)) :
    Site.signedPerm π ε x ∈ facetLinked d a m L H (BondConfig.relabel (sym2Equiv (Site.signedPerm π ε)) ω) ↔
      x ∈ facetLinked d (π.symm a) m L H ω := by
  simp only [facetLinked, sideLinked, Set.mem_setOf_eq, signedPerm_mem_sides hπ hε, abs_signedPerm_apply]
  exact and_congr (and_congr Iff.rfl (linked_relabel_signedPerm_iff hπ hε m L H x ω)) Iff.rfl

/-- **The facet counts `V^a`, `a ≠ 0`, are equidistributed**: `P(V^a < M) = P(V^b < M)` (the
transposition of the axes `a`, `b`; it does not involve any seed rule).
[cite: GrimmettPercolation1999, §7.3 p. 168 (by symmetry)] -/
theorem prob_facetCountLT_eq {a b : Fin d} (ha : a ≠ 0) (hb : b ≠ 0) (m L H M : ℕ) (p : unitInterval) :
    (bondPercolation (zdGraph d) p).real (facetCountLT d a m L H M) =
      (bondPercolation (zdGraph d) p).real (facetCountLT d b m L H M) := by
  set φ : Site d ≃ Site d := Site.signedPerm (Equiv.swap a b) 1 with hφ
  have hπ : (Equiv.swap a b) 0 = 0 := Equiv.swap_apply_of_ne_of_ne (Ne.symm ha) (Ne.symm hb)
  have hε : (1 : Fin d → ℤˣ) 0 = 1 := rfl
  have hsymm : (Equiv.swap a b).symm a = b := by rw [Equiv.symm_swap, Equiv.swap_apply_left]
  have hpre : BondConfig.relabel (sym2Equiv φ) ⁻¹' facetCountLT d a m L H M = facetCountLT d b m L H M := by
    ext ω
    simp only [Set.mem_preimage, facetCountLT, Set.mem_setOf_eq]
    have himage : facetLinked d a m L H (BondConfig.relabel (sym2Equiv φ) ω) = φ '' facetLinked d b m L H ω := by
      ext x'
      rw [Equiv.image_eq_preimage_symm, Set.mem_preimage, ← hsymm,
        ← signedPerm_mem_facetLinked_iff hπ hε, ← hφ, Equiv.apply_symm_apply]
    have hcard : (facetLinked_finite a m L H (BondConfig.relabel (sym2Equiv φ) ω)).toFinset.card =
        (facetLinked_finite b m L H ω).toFinset.card := by
      rw [← Set.ncard_eq_toFinset_card _ (facetLinked_finite _ m L H _),
        ← Set.ncard_eq_toFinset_card _ (facetLinked_finite _ m L H _), himage,
        Set.ncard_image_of_injective _ φ.injective]
    rw [hcard]
  rw [← hpre]
  exact (bondPercolation_real_preimage_relabel_iso (zdSignedPermIso (Equiv.swap a b) 1) p _).symm

end SignedPerm

/-! ## Reflections, seed rules and the events `okEventR` -/

section Refl

variable [NeZero d] {m L H r K : ℕ} {E : Site d → Finset (Sym2 (Site d))}

/-- Open rule-edges are carried by reflections: `RuleOpen E (refl x) (refl·ω) ↔ RuleOpen E x ω`.
[folklore] -/
theorem ruleOpen_relabel_refl_iff (hV : SeedRuleValid E L H r K) {ε : Fin d → ℤˣ} (hε : ε 0 = 1) (x : Site d)
    (ω : BondConfig (Site d)) :
    RuleOpen E (refl ε x) (BondConfig.relabel (sym2Equiv (refl ε)) ω) ↔ RuleOpen E x ω := by
  simp only [RuleOpen, hV.refl_equiv ε hε x, Finset.coe_map, Set.image_subset_iff, Equiv.coe_toEmbedding]
  constructor
  · intro h e he
    have := h he
    rw [Set.mem_preimage, BondConfig.mem_relabel_iff, Equiv.symm_apply_apply] at this
    exact this
  · intro h e he
    rw [Set.mem_preimage, BondConfig.mem_relabel_iff, Equiv.symm_apply_apply]
    exact h he

/-- Linking is carried by reflections. [folklore] -/
theorem linked_relabel_refl_iff {ε : Fin d → ℤˣ} (hε : ε 0 = 1) (m L H : ℕ) (x : Site d) (ω : BondConfig (Site d)) :
    Linked d m L H (refl ε x) (BondConfig.relabel (sym2Equiv (refl ε)) ω) ↔ Linked d m L H x ω :=
  linked_relabel_signedPerm_iff (π := 1) rfl hε m L H x ω

/-- Reflections carry `okEventR F` to `okEventR (refl '' F)`. [cite: GrimmettPercolation1999, §7.3 p. 168 (by symmetry)] -/
theorem relabel_refl_preimage_okEventR (hV : SeedRuleValid E L H r K) {ε : Fin d → ℤˣ} (hε : ε 0 = 1)
    (F : Set (Site d)) :
    BondConfig.relabel (sym2Equiv (refl ε)) ⁻¹' okEventR d m L H E (refl ε '' F) = okEventR d m L H E F := by
  ext ω
  simp only [Set.mem_preimage, okEventR, Set.mem_setOf_eq]
  constructor
  · rintro ⟨_, ⟨x, hxF, rfl⟩, hl, ho⟩
    exact ⟨x, hxF, (linked_relabel_refl_iff hε m L H x ω).1 hl, (ruleOpen_relabel_refl_iff hV hε x ω).1 ho⟩
  · rintro ⟨x, hxF, hl, ho⟩
    exact ⟨refl ε x, ⟨x, hxF, rfl⟩, (linked_relabel_refl_iff hε m L H x ω).2 hl,
      (ruleOpen_relabel_refl_iff hV hε x ω).2 ho⟩

/-- **By symmetry `P(okEventR (refl '' F)) = P(okEventR F)`.** [cite: GrimmettPercolation1999, §7.3 p. 168 (by symmetry)] -/
theorem prob_okEventR_image_refl (hV : SeedRuleValid E L H r K) {ε : Fin d → ℤˣ} (hε : ε 0 = 1) (F : Set (Site d))
    (p : unitInterval) :
    (bondPercolation (zdGraph d) p).real (okEventR d m L H E (refl ε '' F)) =
      (bondPercolation (zdGraph d) p).real (okEventR d m L H E F) := by
  rw [← relabel_refl_preimage_okEventR (m := m) hV hε F]
  exact (bondPercolation_real_preimage_relabel_iso (zdSignedPermIso 1 ε) p _).symm

/-! ## The subfacets as reflection orbits -/

/-- The sign flip of a half-range label: `b` if `u = 1`, `¬b` if `u = -1`. [folklore] -/
def flipB (u : ℤˣ) (b : Bool) : Bool := if u = 1 then b else !b

/-- Half-ranges under a sign: `HalfRange L b (u t) ↔ HalfRange L (flipB u b) t`. [folklore] -/
theorem halfRange_units_mul (L : ℕ) (b : Bool) (u : ℤˣ) (t : ℤ) :
    HalfRange L b ((u : ℤ) * t) ↔ HalfRange L (flipB u b) t := by
  unfold HalfRange flipB
  rcases Int.units_eq_one_or u with rfl | rfl <;> cases b <;> simp <;> omega

omit [NeZero d] in
/-- Membership in a reflected set. [folklore] -/
theorem mem_image_refl_iff (ε : Fin d → ℤˣ) (A : Set (Site d)) (x : Site d) : x ∈ refl ε '' A ↔ refl ε x ∈ A := by
  rw [Equiv.image_eq_preimage_symm, refl_symm, Set.mem_preimage]

/-- **Reflections permute the top subfacets**: `refl ε '' T_ρ = T_{ρ'}` with
`ρ' j = flipB (ε j) (ρ j)`. [folklore] -/
theorem image_refl_topSubfacet {ε : Fin d → ℤˣ} (hε : ε 0 = 1) (L H : ℕ) (ρ : HAxis d → Bool) :
    refl ε '' topSubfacet d L H ρ = topSubfacet d L H fun j => flipB (ε j.1) (ρ j) := by
  ext x
  rw [mem_image_refl_iff]
  simp only [topSubfacet, Set.mem_setOf_eq, refl_apply, hε, Units.val_one, one_mul, halfRange_units_mul]

/-- **Reflections permute the side subfacets of a fixed axis**: `refl ε '' S_{a,τ} = S_{a,τ'}` with
`τ' j = flipB (ε j) (τ j)`. [folklore] -/
theorem image_refl_sideSubfacet {ε : Fin d → ℤˣ} (hε : ε 0 = 1) (L H : ℕ) (a : HAxis d) (τ : HAxis d → Bool) :
    refl ε '' sideSubfacet d L H a τ = sideSubfacet d L H a fun j => flipB (ε j.1) (τ j) := by
  ext x
  rw [mem_image_refl_iff]
  simp only [sideSubfacet, Set.mem_setOf_eq, refl_apply, hε, Units.val_one, one_mul, halfRange_units_mul]
  refine and_congr_right fun _ => and_congr ?_ Iff.rfl
  unfold flipB
  rcases Int.units_eq_one_or (ε a.1) with h | h <;> rcases Bool.eq_false_or_eq_true (τ a) with hτ | hτ <;>
    simp [h, hτ]
  all_goals omega

/-- The reflection carrying the label `ρ` to `ρ'`: `ε j = 1` where they agree, `-1` elsewhere
(and `ε 0 = 1`). [folklore] -/
def reflOf (ρ ρ' : HAxis d → Bool) : Fin d → ℤˣ := fun j =>
  if h : j = 0 then 1 else if ρ ⟨j, h⟩ = ρ' ⟨j, h⟩ then 1 else -1

/-- `reflOf ρ ρ' 0 = 1`. [folklore] -/
theorem reflOf_zero (ρ ρ' : HAxis d → Bool) : reflOf ρ ρ' 0 = 1 := by simp [reflOf]

/-- `reflOf ρ ρ'` flips `ρ` into `ρ'`. [folklore] -/
theorem flipB_reflOf (ρ ρ' : HAxis d → Bool) (j : HAxis d) : flipB (reflOf ρ ρ' j.1) (ρ j) = ρ' j := by
  unfold flipB reflOf
  simp only [j.2, ↓reduceDIte, Subtype.coe_eta]
  by_cases h : ρ j = ρ' j
  · simp [h]
  · simp only [h, ↓reduceIte]
    revert h; cases ρ j <;> cases ρ' j <;> decide

/-- **The `X_ρ` are equidistributed**: `P(okEventR T_ρ) = P(okEventR T_ρ')`.
[cite: GrimmettPercolation1999, §7.3 p. 168 (by symmetry the X_j have the same distribution)] -/
theorem prob_okEventR_topSubfacet_eq (hV : SeedRuleValid E L H r K) (p : unitInterval) (ρ ρ' : HAxis d → Bool) :
    (bondPercolation (zdGraph d) p).real (okEventR d m L H E (topSubfacet d L H ρ')) =
      (bondPercolation (zdGraph d) p).real (okEventR d m L H E (topSubfacet d L H ρ)) := by
  have h := image_refl_topSubfacet (reflOf_zero ρ ρ') L H ρ
  simp only [flipB_reflOf] at h
  rw [← h, prob_okEventR_image_refl hV (reflOf_zero ρ ρ')]

/-- **The `Y_{a,τ}` of a fixed axis are equidistributed**: `P(okEventR S_{a,τ}) = P(okEventR S_{a,τ'})`.
[cite: GrimmettPercolation1999, §7.3 p. 168 (by symmetry)] -/
theorem prob_okEventR_sideSubfacet_eq (hV : SeedRuleValid E L H r K) (p : unitInterval) (a : HAxis d)
    (τ τ' : HAxis d → Bool) :
    (bondPercolation (zdGraph d) p).real (okEventR d m L H E (sideSubfacet d L H a τ')) =
      (bondPercolation (zdGraph d) p).real (okEventR d m L H E (sideSubfacet d L H a τ)) := by
  have h := image_refl_sideSubfacet (reflOf_zero τ τ') L H a τ
  simp only [flipB_reflOf] at h
  rw [← h, prob_okEventR_image_refl hV (reflOf_zero τ τ')]

/-! ## (7.51): from the whole top / facet family to a single subfacet -/

/-- Every vertex of the top lies in a top subfacet (the one of the signs of its coordinates). [folklore] -/
theorem exists_mem_topSubfacet {L H : ℕ} {x : Site d} (hx : x ∈ top d L H) : ∃ ρ : HAxis d → Bool, x ∈ topSubfacet d L H ρ := by
  refine ⟨fun j => decide (0 ≤ x j.1), hx.2, fun j => ?_⟩
  have := abs_le.1 ((mem_brick.1 hx.1).2 j.1 j.2)
  unfold HalfRange
  by_cases h : 0 ≤ x j.1
  · simp only [h, decide_true, ↓reduceIte, true_and]; omega
  · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]; omega

/-- Every linked vertex of the facets `|x_a| = L` lies in a side subfacet `S_{a,τ}`. [folklore] -/
theorem exists_mem_sideSubfacet {m L H : ℕ} {a : HAxis d} {x : Site d} {ω : BondConfig (Site d)}
    (hx : x ∈ facetLinked d a.1 m L H ω) : ∃ τ : HAxis d → Bool, x ∈ sideSubfacet d L H a τ := by
  obtain ⟨⟨hxs, -⟩, hxa⟩ := hx
  have hb := mem_brick.1 hxs.1
  refine ⟨fun j => if j = a then decide (x a.1 = L) else decide (0 ≤ x j.1), hb.1, ?_, fun j hj => ?_⟩
  · simp only [↓reduceIte]
    rcases (abs_eq (by positivity : (0 : ℤ) ≤ L)).1 hxa with h | h
    · simp [h]
    · rw [h]
      have hL : ¬(-(L : ℤ) = L) ∨ (L : ℤ) = 0 := by omega
      rcases hL with hL | hL
      · simp [hL]
      · simp [hL]
  · simp only [hj, ↓reduceIte]
    have := abs_le.1 (hb.2 j.1 j.2)
    unfold HalfRange
    by_cases h : 0 ≤ x j.1
    · simp only [h, decide_true, ↓reduceIte, true_and]; omega
    · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]; omega

/-- No ok top subfacet means no linked top vertex has its rule-edges open. [folklore] -/
theorem iInter_compl_okEventR_topSubfacet_subset (m L H : ℕ) (E : Site d → Finset (Sym2 (Site d))) :
    (⋂ ρ ∈ (Finset.univ : Finset (HAxis d → Bool)), (okEventR d m L H E (topSubfacet d L H ρ))ᶜ) ⊆
      {ω | ∀ x ∈ topLinked d m L H ω, ¬RuleOpen E x ω} := by
  intro ω hω x hx hopen
  simp only [Set.mem_iInter, Set.mem_compl_iff, Finset.mem_univ, forall_true_left] at hω
  obtain ⟨ρ, hρ⟩ := exists_mem_topSubfacet hx.1
  exact hω ρ ⟨x, hρ, hx.2, hopen⟩

/-- No ok subfacet of the facets `|x_a| = L` means no linked vertex there has its rule-edges open.
[folklore] -/
theorem iInter_compl_okEventR_sideSubfacet_subset (m L H : ℕ) (E : Site d → Finset (Sym2 (Site d))) (a : HAxis d) :
    (⋂ τ ∈ (Finset.univ : Finset (HAxis d → Bool)), (okEventR d m L H E (sideSubfacet d L H a τ))ᶜ) ⊆
      {ω | ∀ x ∈ facetLinked d a.1 m L H ω, ¬RuleOpen E x ω} := by
  intro ω hω x hx hopen
  simp only [Set.mem_iInter, Set.mem_compl_iff, Finset.mem_univ, forall_true_left] at hω
  obtain ⟨τ, hτ⟩ := exists_mem_sideSubfacet hx
  exact hω τ ⟨x, hτ, hx.1.2, hopen⟩

/-- **(7.51), top**: `P(X_ρ = 0)^{2^{d-1}} ≤ P(no linked top vertex has open rule-edges)` for every `ρ`
(FKG for the `2^{d-1}` decreasing events `{X_ρ = 0}` and their common probability).
[cite: GrimmettPercolation1999, §7.3 p. 168 (7.51)] -/
theorem prob_compl_okEventR_topSubfacet_pow_le (hV : SeedRuleValid E L H r K) (p : unitInterval) (ρ : HAxis d → Bool) :
    (bondPercolation (zdGraph d) p).real (okEventR d m L H E (topSubfacet d L H ρ))ᶜ ^ Fintype.card (HAxis d → Bool) ≤
      (bondPercolation (zdGraph d) p).real {ω | ∀ x ∈ topLinked d m L H ω, ¬RuleOpen E x ω} := by
  have hc : ∀ ρ' ∈ (Finset.univ : Finset (HAxis d → Bool)),
      (bondPercolation (zdGraph d) p).real (okEventR d m L H E (topSubfacet d L H ρ'))ᶜ =
        (bondPercolation (zdGraph d) p).real (okEventR d m L H E (topSubfacet d L H ρ))ᶜ := by
    intro ρ' _
    rw [probReal_compl_eq_one_sub (measurableSet_okEventR _ _ _ _ _),
      probReal_compl_eq_one_sub (measurableSet_okEventR _ _ _ _ _), prob_okEventR_topSubfacet_eq hV p ρ ρ']
  have h := prob_pow_le_biInter_of_isLowerSet (zdGraph d) p Finset.univ
    (fun ρ' => (okEventR d m L H E (topSubfacet d L H ρ'))ᶜ) (fun ρ' _ => (isUpperSet_okEventR _ _ _ _ _).compl)
    (fun ρ' _ => (measurableSet_okEventR _ _ _ _ _).compl) hc
  rw [Finset.card_univ] at h
  exact h.trans (measureReal_mono (iInter_compl_okEventR_topSubfacet_subset m L H E))

/-- **(7.51), sides**: `P(Y_{a,τ} = 0)^{2^{d-1}} ≤ P(no linked vertex of the facets |x_a| = L has open
rule-edges)`. [cite: GrimmettPercolation1999, §7.3 p. 169 (7.51)] -/
theorem prob_compl_okEventR_sideSubfacet_pow_le (hV : SeedRuleValid E L H r K) (p : unitInterval) (a : HAxis d)
    (τ : HAxis d → Bool) :
    (bondPercolation (zdGraph d) p).real (okEventR d m L H E (sideSubfacet d L H a τ))ᶜ ^ Fintype.card (HAxis d → Bool) ≤
      (bondPercolation (zdGraph d) p).real {ω | ∀ x ∈ facetLinked d a.1 m L H ω, ¬RuleOpen E x ω} := by
  have hc : ∀ τ' ∈ (Finset.univ : Finset (HAxis d → Bool)),
      (bondPercolation (zdGraph d) p).real (okEventR d m L H E (sideSubfacet d L H a τ'))ᶜ =
        (bondPercolation (zdGraph d) p).real (okEventR d m L H E (sideSubfacet d L H a τ))ᶜ := by
    intro τ' _
    rw [probReal_compl_eq_one_sub (measurableSet_okEventR _ _ _ _ _),
      probReal_compl_eq_one_sub (measurableSet_okEventR _ _ _ _ _), prob_okEventR_sideSubfacet_eq hV p a τ τ']
  have h := prob_pow_le_biInter_of_isLowerSet (zdGraph d) p Finset.univ
    (fun τ' => (okEventR d m L H E (sideSubfacet d L H a τ'))ᶜ) (fun τ' _ => (isUpperSet_okEventR _ _ _ _ _).compl)
    (fun τ' _ => (measurableSet_okEventR _ _ _ _ _).compl) hc
  rw [Finset.card_univ] at h
  exact h.trans (measureReal_mono (iInter_compl_okEventR_sideSubfacet_subset m L H E a))

end Refl

end BGNd

end Percolation.Literature

end
