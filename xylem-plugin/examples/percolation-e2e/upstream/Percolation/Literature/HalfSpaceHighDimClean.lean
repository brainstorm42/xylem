import Percolation.Literature.HalfSpaceHighDimLemma736
import Percolation.Literature.PlacedBricks
import Percolation.Util.Linter

/-!
# The clean seed rule in `ℤ^d` and Lemma (7.36) for clean seeds

The `ℤ^d` version of the clean part of `CleanSeeds.lean`
(Grimmett, *Percolation*, 2nd ed. (1999), §7.3; the seeds of the brick `B(L,H)` of Lemma (7.36)
placed just OUTSIDE its faces, so that stacked bricks examine disjoint edge sets — Grimmett
pp. 172–173, (A)–(C): "the intersection of a new brick with the region considered so far must be
limited to a subset of its underside"). To a vertex `x` of the top the **clean rule** attaches the
vertical edge `{x, x + e₀}` and the horizontal square of radius `m` in the hyperplane just above the
top, centred above `x` with the centre clamped transversally to `[-(L-m-1), L-m-1]`; to `x` on a
side `x_a = ±L` (`a = seedAxis x`, the least such horizontal axis) the outward edge `{x, x ± e_a}`
and the square of radius `m` orthogonal to `a` in the hyperplane just outside that side, centred
next to `x` with the centre clamped in height to `[m+1, H-m-1]` and transversally as before.

* `BGNd.normalSign`, `BGNd.cleanNormal`, `BGNd.cleanCenter`, `BGNd.cleanSquare`, `BGNd.cleanConn`,
  `BGNd.cleanEdges` — the rule — and `BGNd.goodC`, `BGNd.topGoodC` (the clean good / top-good
  events, `goodR`/`topGoodR` of the rule);
* `BGNd.seedRuleValid_cleanEdges` — **the clean rule is valid** (`SeedRuleValid`, separation
  radius `4m+2`, size bound `|B(m)|² + 1`) for `L ≥ m + 1`, `H ≥ 2m + 2`: clean edges are lattice
  edges outside `B(L,H)*`, clean edge sets of far vertices are disjoint, and the rule commutes
  with the horizontal reflections;
* `BGNd.lemma_7_36C` — **Lemma (7.36) for clean seeds in `ℤ^d`, at every density**, from
  `BGNd.lemma_7_36R`: for `d ≥ 2`, `0 < p < 1` with `θ_ℍ(p) > 0`, `η > 0` and any size request
  `Lreq m H₀`, there are `m ≥ 1`, `H₀ ≥ 2m + 2`, `L ≥ max(m + 2, Lreq m H₀)`, `H > H₀` with
  `P_p(goodC on B(L,H)) > 1 - η` and `P_p(topGoodC on B(L,h)) > 1 - η` for all `H₀ < h ≤ H`.

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §7.3, Lemma (7.36) and its proof
  pp. 164–169; (A)–(C) pp. 172–173.
-/

noncomputable section

namespace Percolation.Literature

open _root_.MeasureTheory _root_.ProbabilityTheory _root_.Filter LatticeModels unitInterval
open scoped _root_.ENNReal _root_.Topology

namespace BGNd

variable {d : ℕ}

/-! ## Squares and their edges -/

/-- Every vertex of the square `c + b_k(m)` is within sup-distance `m` of its centre. [folklore] -/
theorem abs_sub_le_of_mem_square {k : Fin d} {m : ℕ} {c y : Site d} (hy : y ∈ square k m c) (i : Fin d) :
    |y i - c i| ≤ m := by
  rw [mem_square] at hy
  by_cases hi : i = k
  · subst hi; rw [hy.1, sub_self, abs_zero]; positivity
  · exact hy.2 i hi

/-- Squares lie in translated boxes: `y ↦ y - c` maps the square into `B(m)`. [folklore] -/
theorem sub_mem_box_of_mem_square {k : Fin d} {m : ℕ} {c y : Site d} (hy : y ∈ square k m c) : y - c ∈ box d m :=
  mem_box_iff_abs.2 fun i => by rw [Pi.sub_apply]; exact abs_sub_le_of_mem_square hy i

/-- Squares are finite. [folklore] -/
theorem square_finite (k : Fin d) (m : ℕ) (c : Site d) : (square k m c).Finite := by
  refine ((box d m).finite_toSet.image fun z => z + c).subset fun y hy => ?_
  exact ⟨y - c, sub_mem_box_of_mem_square hy, sub_add_cancel y c⟩

/-- A square has at most `|B(m)|` vertices. [folklore] -/
theorem ncard_square_le (k : Fin d) (m : ℕ) (c : Site d) : (square k m c).ncard ≤ (box d m).card := by
  classical
  have h := Set.ncard_le_ncard_of_injOn (s := square k m c) (t := (↑(box d m) : Set (Site d))) (fun y : Site d => y - c)
    (fun y hy => Finset.mem_coe.2 (sub_mem_box_of_mem_square hy)) (fun y _ y' _ h => sub_left_injective h)
    (Finset.finite_toSet _)
  rwa [Set.ncard_coe_finset] at h

/-- The lattice edges joining two vertices of the finite set `Q` (`edgesIn (zdGraph d) Λ` at
`Λ = hQ.toFinset`; for a square: the edges whose openness makes it a seed).
[cite: GrimmettPercolation1999, §7.3 p. 163 (seed)] -/
abbrev sqEdges (Q : Set (Site d)) (hQ : Q.Finite) : Finset (Sym2 (Site d)) := edgesIn (zdGraph d) hQ.toFinset

/-- Membership in `sqEdges`, in the two-endpoint form. [folklore] -/
theorem mem_sqEdges_iff {Q : Set (Site d)} {hQ : Q.Finite} {e : Sym2 (Site d)} :
    e ∈ sqEdges Q hQ ↔ ∃ u ∈ Q, ∃ v ∈ Q, (zdGraph d).Adj u v ∧ e = s(u, v) := by
  rw [sqEdges, mem_edgesIn_iff]
  constructor
  · rintro ⟨he, hmem⟩
    induction e using Sym2.ind with
    | _ u v =>
      exact ⟨u, (Set.Finite.mem_toFinset hQ).1 (hmem u (Sym2.mem_mk_left u v)), v,
        (Set.Finite.mem_toFinset hQ).1 (hmem v (Sym2.mem_mk_right u v)), (SimpleGraph.mem_edgeSet _).1 he, rfl⟩
  · rintro ⟨u, hu, v, hv, hadj, rfl⟩
    refine ⟨(SimpleGraph.mem_edgeSet _).2 hadj, fun x hx => ?_⟩
    rw [Set.Finite.mem_toFinset]
    rcases Sym2.mem_iff.1 hx with rfl | rfl
    · exact hu
    · exact hv

/-- The edges of `Q` are lattice edges. [folklore] -/
theorem sqEdges_subset_edgeSet (Q : Set (Site d)) (hQ : Q.Finite) :
    (↑(sqEdges Q hQ) : Set (Sym2 (Site d))) ⊆ (zdGraph d).edgeSet := by
  intro e he
  rw [Finset.mem_coe, mem_sqEdges_iff] at he
  obtain ⟨u, -, v, -, hadj, rfl⟩ := he
  exact (SimpleGraph.mem_edgeSet _).2 hadj

/-- There are at most `|Q|²` edges of `Q`. [folklore] -/
theorem card_sqEdges_le (Q : Set (Site d)) (hQ : Q.Finite) : (sqEdges Q hQ).card ≤ Q.ncard ^ 2 := by
  classical
  have hsub : sqEdges Q hQ ⊆ (hQ.toFinset ×ˢ hQ.toFinset).image fun uv => s(uv.1, uv.2) := by
    intro e he
    obtain ⟨u, hu, v, hv, -, rfl⟩ := mem_sqEdges_iff.1 he
    exact Finset.mem_image.2 ⟨(u, v), Finset.mem_product.2 ⟨(Set.Finite.mem_toFinset hQ).2 hu,
      (Set.Finite.mem_toFinset hQ).2 hv⟩, rfl⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
  rw [Finset.card_product, ← Set.ncard_eq_toFinset_card Q hQ, sq]

/-- Disjoint vertex sets have disjoint edge sets. [folklore] -/
theorem disjoint_sqEdges {Q Q' : Set (Site d)} (hQ : Q.Finite) (hQ' : Q'.Finite) (h : Disjoint Q Q') :
    Disjoint (↑(sqEdges Q hQ) : Set (Sym2 (Site d))) ↑(sqEdges Q' hQ') := by
  rw [Set.disjoint_left]
  intro e he he'
  rw [Finset.mem_coe, mem_sqEdges_iff] at he he'
  obtain ⟨u, hu, v, -, -, rfl⟩ := he
  obtain ⟨u', hu', v', hv', -, heq⟩ := he'
  rw [Sym2.eq_iff] at heq
  rcases heq with ⟨rfl, -⟩ | ⟨rfl, rfl⟩
  · exact h.le_bot ⟨hu, hu'⟩
  · exact h.le_bot ⟨hu, hv'⟩

/-- Lattice automorphisms carry the edges of a finite set to the edges of its image. [folklore] -/
theorem sqEdges_image (φ : zdGraph d ≃g zdGraph d) (Q : Set (Site d)) (hQ : Q.Finite) (hQ' : (φ '' Q).Finite) :
    sqEdges (φ '' Q) hQ' = (sqEdges Q hQ).map (sym2Equiv φ.toEquiv).toEmbedding := by
  ext e
  simp only [Finset.mem_map, Equiv.coe_toEmbedding, mem_sqEdges_iff]
  constructor
  · rintro ⟨_, ⟨u, hu, rfl⟩, _, ⟨v, hv, rfl⟩, hadj, rfl⟩
    exact ⟨s(u, v), ⟨u, hu, v, hv, φ.map_rel_iff'.1 hadj, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨u, hu, v, hv, hadj, rfl⟩, rfl⟩
    exact ⟨φ u, ⟨u, hu, rfl⟩, φ v, ⟨v, hv, rfl⟩, φ.map_rel_iff'.2 hadj, rfl⟩

/-! ## The seed axis -/

section Axis

variable [NeZero d] {L H : ℕ}

/-- The top case of the seed axis. [folklore] -/
theorem seedAxis_of_top {x : Site d} (h0 : x 0 = H) : seedAxis d L H x = 0 := by
  simp [seedAxis, h0]

/-- The side case of the seed axis: for `x ∉ T` on some face `|x_j| = L`, the axis is horizontal
and `|x_{seedAxis}| = L`. [folklore] -/
theorem seedAxis_of_side {x : Site d} (h0 : x 0 ≠ H) (hx : ∃ j : Fin d, j ≠ 0 ∧ |x j| = L) :
    seedAxis d L H x ≠ 0 ∧ |x (seedAxis d L H x)| = L := by
  have hne : (Finset.univ.filter fun j : Fin d => j ≠ 0 ∧ |x j| = L).Nonempty := by
    obtain ⟨j, hj, hjl⟩ := hx
    exact ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, hj, hjl⟩⟩
  have hmem := Finset.min'_mem _ hne
  rw [Finset.mem_filter] at hmem
  simp only [seedAxis, h0, ↓reduceIte, hne, ↓reduceDIte]
  exact hmem.2

/-- When exactly one horizontal face contains `x ∉ T`, the seed axis is its axis. [folklore] -/
theorem seedAxis_eq_of_unique {x : Site d} (h0 : x 0 ≠ H) {a : Fin d} (ha : a ≠ 0) (hxa : |x a| = L)
    (huniq : ∀ j : Fin d, j ≠ 0 → |x j| = L → j = a) : seedAxis d L H x = a := by
  obtain ⟨hk, hkl⟩ := seedAxis_of_side (L := L) h0 ⟨a, ha, hxa⟩
  exact huniq _ hk hkl

/-- The seed axis is invariant under the horizontal reflections (it only depends on `x 0` and the
`|x j|`). [folklore] -/
theorem seedAxis_refl {ε : Fin d → ℤˣ} (hε : ε 0 = 1) (L H : ℕ) (x : Site d) :
    seedAxis d L H (refl ε x) = seedAxis d L H x := by
  have h0 : refl ε x 0 = x 0 := by rw [refl_apply, hε, Units.val_one, one_mul]
  have habs : ∀ j, |refl ε x j| = |x j| := fun j => by rw [refl_apply, BGN.abs_units_mul]
  have hfilter : (Finset.univ.filter fun j : Fin d => j ≠ 0 ∧ |refl ε x j| = L) =
      Finset.univ.filter fun j : Fin d => j ≠ 0 ∧ |x j| = L := by
    refine Finset.filter_congr fun j _ => ?_
    rw [habs]
  simp only [seedAxis, h0, hfilter]

end Axis

/-! ## The clean rule -/

section Clean

variable [NeZero d]

/-- The outward sign of the clean seed of `x`: `+1` above the top, `sign x_a` beside the side
`x_a = ±L` (`a = seedAxis x`). [cite: GrimmettPercolation1999, §7.3 p. 173 (B)] -/
def normalSign (d L H : ℕ) [NeZero d] (x : Site d) : ℤ :=
  if x 0 = H then 1 else Int.sign (x (seedAxis d L H x))

/-- The outward normal step of the clean seed of `x` (along the axis `seedAxis x`).
[cite: GrimmettPercolation1999, §7.3 p. 173 (B)] -/
def cleanNormal (d L H : ℕ) [NeZero d] (x : Site d) : Site d := Pi.single (seedAxis d L H x) (normalSign d L H x)

/-- The centre of the clean seed square of `x`: one step outside the face of `x`, above/beside `x`
but clamped — transversally to `[-(L-m-1), L-m-1]`, in height (for sides) to `[m+1, H-m-1]` — so
that the square faces the face of `x`. [cite: GrimmettPercolation1999, §7.3 p. 173 (B)–(C)] -/
def cleanCenter (d m L H : ℕ) [NeZero d] (x : Site d) : Site d := fun i =>
  if i = seedAxis d L H x then x i + normalSign d L H x
  else if i = 0 then BGN.clampZ ((m : ℤ) + 1) ((H : ℤ) - m - 1) (x 0)
  else BGN.clampZ (-((L : ℤ) - m - 1)) ((L : ℤ) - m - 1) (x i)

/-- The clean seed square of `x`: radius `m`, orthogonal to the axis of the face of `x`, centred at
`cleanCenter`. [cite: GrimmettPercolation1999, §7.3 p. 173 (B)] -/
def cleanSquare (d m L H : ℕ) [NeZero d] (x : Site d) : Set (Site d) :=
  square (seedAxis d L H x) m (cleanCenter d m L H x)

/-- The connecting edge from `x` to its clean seed square. [cite: GrimmettPercolation1999, §7.3 p. 173 (B)] -/
def cleanConn (d L H : ℕ) [NeZero d] (x : Site d) : Sym2 (Site d) := s(x, x + cleanNormal d L H x)

/-- **The clean seed rule**: the connecting edge together with the edges of the clean seed square.
[cite: GrimmettPercolation1999, §7.3 p. 173 (B)–(C)] -/
def cleanEdges (d m L H : ℕ) [NeZero d] (x : Site d) : Finset (Sym2 (Site d)) :=
  insert (cleanConn d L H x) (sqEdges (cleanSquare d m L H x) (square_finite _ _ _))

/-- The clean good event `goodC = goodR (cleanEdges)`: in each top and side subfacet a vertex
joined to `b(0)` in `B(L,H)*` whose connecting edge and clean seed square are open.
[cite: GrimmettPercolation1999, §7.3 p. 164 (good), p. 173 (B)–(C)] -/
def goodC (d m L H : ℕ) [NeZero d] : Set (BondConfig (Site d)) := goodR d m L H (cleanEdges d m L H)

/-- The clean top-good event `topGoodC = topGoodR (cleanEdges)` (top subfacets only; for bricks
used for top stacking). [cite: GrimmettPercolation1999, §7.3 p. 172 (A)] -/
def topGoodC (d m L H : ℕ) [NeZero d] : Set (BondConfig (Site d)) := topGoodR d m L H (cleanEdges d m L H)

variable {m L H : ℕ}

/-- `T ∪ S ⊆ B(L,H)`. [folklore] -/
theorem mem_brick_of_mem_top_union_sides {x : Site d} (hx : x ∈ top d L H ∪ sides d L H) : x ∈ brick d L H := by
  rcases hx with hx | hx
  · exact hx.1
  · exact hx.1

/-- **The two cases of the rule** for `x ∈ T ∪ S` (`L ≥ 1`), with `k = seedAxis x`,
`n = normalSign x`: either `k = 0`, `x₀ = H`, `n = 1`; or `k ≠ 0`, `x₀ ≠ H`, `|x_k| = L`,
`n = ±1` and `x_k + n = n (L + 1)`. [folklore] -/
theorem normalSign_spec (hL : 1 ≤ L) {x : Site d} (hx : x ∈ top d L H ∪ sides d L H) :
    (normalSign d L H x = 1 ∨ normalSign d L H x = -1) ∧
      ((seedAxis d L H x = 0 ∧ x 0 = H ∧ normalSign d L H x = 1) ∨
        (seedAxis d L H x ≠ 0 ∧ x 0 ≠ H ∧ |x (seedAxis d L H x)| = L ∧
          x (seedAxis d L H x) + normalSign d L H x = normalSign d L H x * ((L : ℤ) + 1))) := by
  by_cases h0 : x 0 = H
  · have hk := seedAxis_of_top (L := L) h0
    have hs : normalSign d L H x = 1 := by simp [normalSign, h0]
    exact ⟨Or.inl hs, Or.inl ⟨hk, h0, hs⟩⟩
  · have hside : ∃ j : Fin d, j ≠ 0 ∧ |x j| = L := by
      rcases hx with hx | hx
      · exact absurd hx.2 h0
      · exact hx.2
    obtain ⟨hk, hkl⟩ := seedAxis_of_side (L := L) (H := H) h0 hside
    have hs : normalSign d L H x = Int.sign (x (seedAxis d L H x)) := by simp [normalSign, h0]
    rw [hs]
    rcases (abs_eq (by positivity : (0 : ℤ) ≤ L)).1 hkl with h | h
    · have hsg : Int.sign (x (seedAxis d L H x)) = 1 := Int.sign_eq_one_of_pos (by omega)
      refine ⟨Or.inl hsg, Or.inr ⟨hk, h0, hkl, ?_⟩⟩
      rw [hsg, h]; ring
    · have hsg : Int.sign (x (seedAxis d L H x)) = -1 := Int.sign_eq_neg_one_of_neg (by omega)
      refine ⟨Or.inr hsg, Or.inr ⟨hk, h0, hkl, ?_⟩⟩
      rw [hsg, h]; ring

/-- Coordinates of `x + cleanNormal x`. [folklore] -/
theorem add_cleanNormal_apply (L H : ℕ) (x : Site d) (i : Fin d) :
    (x + cleanNormal d L H x) i = if i = seedAxis d L H x then x i + normalSign d L H x else x i := by
  simp only [cleanNormal, Pi.add_apply, Pi.single_apply]
  split_ifs <;> simp

/-- The centre of the clean square along the normal axis. [folklore] -/
theorem cleanCenter_apply_seedAxis (m L H : ℕ) (x : Site d) :
    cleanCenter d m L H x (seedAxis d L H x) = x (seedAxis d L H x) + normalSign d L H x := by
  simp [cleanCenter]

/-- The height of the centre of a side clean square is the clamped height of `x`. [folklore] -/
theorem cleanCenter_apply_zero_of_ne (m L H : ℕ) {x : Site d} (hk : seedAxis d L H x ≠ 0) :
    cleanCenter d m L H x 0 = BGN.clampZ ((m : ℤ) + 1) ((H : ℤ) - m - 1) (x 0) := by
  simp [cleanCenter, Ne.symm hk]

/-- The transverse coordinates of the centre are the clamped ones of `x`. [folklore] -/
theorem cleanCenter_apply_of_ne (m L H : ℕ) {x : Site d} {i : Fin d} (hik : i ≠ seedAxis d L H x) (hi0 : i ≠ 0) :
    cleanCenter d m L H x i = BGN.clampZ (-((L : ℤ) - m - 1)) ((L : ℤ) - m - 1) (x i) := by
  simp [cleanCenter, hik, hi0]

/-- `x + cleanNormal x` lies outside the brick for `x ∈ T ∪ S`. [folklore] -/
theorem add_cleanNormal_notMem_brick (hL : 1 ≤ L) {x : Site d} (hx : x ∈ top d L H ∪ sides d L H) :
    x + cleanNormal d L H x ∉ brick d L H := by
  intro hb
  rw [mem_brick] at hb
  obtain ⟨hs, hcase⟩ := normalSign_spec hL hx
  have e := add_cleanNormal_apply L H x
  rcases hcase with ⟨hk, h0, hs1⟩ | ⟨hk, -, -, hval⟩
  · have := hb.1.2; rw [e 0, if_pos hk.symm, h0, hs1] at this; omega
  · have := abs_le.1 (hb.2 _ hk); rw [e, if_pos rfl, hval] at this
    rcases hs with h | h <;> rw [h] at this <;> omega

/-- The clean seed square lies outside the brick (for `x ∈ T ∪ S`). [folklore] -/
theorem cleanSquare_disjoint_brick (hL : 1 ≤ L) {x : Site d} (hx : x ∈ top d L H ∪ sides d L H) {y : Site d}
    (hy : y ∈ cleanSquare d m L H x) : y ∉ brick d L H := by
  intro hb
  rw [mem_brick] at hb
  rw [cleanSquare, mem_square] at hy
  have hyk : y (seedAxis d L H x) = x (seedAxis d L H x) + normalSign d L H x := by
    rw [hy.1, cleanCenter_apply_seedAxis]
  obtain ⟨hs, hcase⟩ := normalSign_spec hL hx
  rcases hcase with ⟨hk, h0, hs1⟩ | ⟨hk, -, -, hval⟩
  · rw [hk, h0, hs1] at hyk; have := hb.1.2; omega
  · rw [hval] at hyk
    have := abs_le.1 (hb.2 _ hk); rw [hyk] at this
    rcases hs with h | h <;> rw [h] at this <;> omega

/-- **The centre of the clean square is close to `x`**: `|cleanCenter x i - x i| ≤ m + 1` in every
coordinate, for `x ∈ T ∪ S`, `L ≥ m + 1`, `H ≥ 2m + 2`. [folklore] -/
theorem abs_cleanCenter_sub_le (hL : m + 1 ≤ L) (hH : 2 * m + 2 ≤ H) {x : Site d} (hx : x ∈ top d L H ∪ sides d L H)
    (i : Fin d) : |cleanCenter d m L H x i - x i| ≤ (m : ℤ) + 1 := by
  have hb := mem_brick_of_mem_top_union_sides hx
  rw [mem_brick] at hb
  obtain ⟨hs, -⟩ := normalSign_spec (by omega) hx
  simp only [cleanCenter]
  split_ifs with h1 h2
  · rw [add_sub_cancel_left]; rcases hs with h | h <;> rw [h] <;> simp
  · subst h2
    exact BGN.abs_clampZ_sub_le (by omega) (by positivity) (by linarith [hb.1.1]) (by linarith [hb.1.2])
  · have := abs_le.1 (hb.2 i h2)
    exact BGN.abs_clampZ_sub_le (by omega) (by positivity) (by linarith [this.1]) (by linarith [this.2])

/-- Every vertex of the clean square is within `2m + 1` of `x`. [folklore] -/
theorem abs_sub_le_of_mem_cleanSquare (hL : m + 1 ≤ L) (hH : 2 * m + 2 ≤ H) {x : Site d}
    (hx : x ∈ top d L H ∪ sides d L H) {y : Site d} (hy : y ∈ cleanSquare d m L H x) (i : Fin d) :
    |y i - x i| ≤ 2 * (m : ℤ) + 1 := by
  have h1 := abs_sub_le_of_mem_square hy i
  have h2 := abs_cleanCenter_sub_le hL hH hx i
  calc |y i - x i| = |(y i - cleanCenter d m L H x i) + (cleanCenter d m L H x i - x i)| := by ring_nf
    _ ≤ |y i - cleanCenter d m L H x i| + |cleanCenter d m L H x i - x i| := abs_add_le _ _
    _ ≤ m + (m + 1) := add_le_add h1 h2
    _ = 2 * (m : ℤ) + 1 := by ring

/-- Clean squares of `(4m+2)`-far vertices are disjoint. [folklore] -/
theorem cleanSquare_disjoint_of_far (hL : m + 1 ≤ L) (hH : 2 * m + 2 ≤ H) {x y : Site d}
    (hx : x ∈ top d L H ∪ sides d L H) (hy : y ∈ top d L H ∪ sides d L H) (hfar : Far (4 * m + 2) x y) :
    Disjoint (cleanSquare d m L H x) (cleanSquare d m L H y) := by
  rw [Set.disjoint_left]
  intro z hzx hzy
  obtain ⟨i, hi⟩ := hfar
  have h1 := abs_sub_le_of_mem_cleanSquare hL hH hx hzx i
  have h2 := abs_sub_le_of_mem_cleanSquare hL hH hy hzy i
  rw [abs_sub_comm] at h1
  have key : |x i - y i| ≤ 4 * (m : ℤ) + 2 := by
    calc |x i - y i| = |(x i - z i) + (z i - y i)| := by ring_nf
      _ ≤ |x i - z i| + |z i - y i| := abs_add_le _ _
      _ ≤ (2 * m + 1) + (2 * m + 1) := add_le_add h1 h2
      _ = 4 * (m : ℤ) + 2 := by ring
  push_cast at hi
  omega

/-- The connecting edge is a lattice edge. [folklore] -/
theorem adj_add_cleanNormal (hL : 1 ≤ L) {x : Site d} (hx : x ∈ top d L H ∪ sides d L H) :
    (zdGraph d).Adj x (x + cleanNormal d L H x) := by
  obtain ⟨hs, -⟩ := normalSign_spec hL hx
  rw [zdGraph_adj_iff]
  refine ⟨seedAxis d L H x, ?_⟩
  rcases hs with h | h
  · left; rw [cleanNormal, h]
  · right; rw [cleanNormal, h, add_assoc]
    have : (Pi.single (seedAxis d L H x) (-1 : ℤ) : Site d) + Pi.single (seedAxis d L H x) 1 = 0 := by
      rw [← Pi.single_add]; simp
    rw [this, add_zero]

/-- The connecting edge is not an edge of any clean square (its endpoint `x` lies in the brick). [folklore] -/
theorem cleanConn_notMem_sqEdges (hL : 1 ≤ L) {x y : Site d} (hx : x ∈ top d L H ∪ sides d L H)
    (hy : y ∈ top d L H ∪ sides d L H) :
    cleanConn d L H x ∉ sqEdges (cleanSquare d m L H y) (square_finite _ _ _) := by
  intro hmem
  rw [mem_sqEdges_iff] at hmem
  obtain ⟨u, hu, v, hv, -, he⟩ := hmem
  rw [cleanConn, Sym2.eq_iff] at he
  have hxb := mem_brick_of_mem_top_union_sides hx
  rcases he with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact cleanSquare_disjoint_brick hL hy hu hxb
  · exact cleanSquare_disjoint_brick hL hy hv hxb

/-- Distinct vertices of `T ∪ S` have distinct connecting edges. [folklore] -/
theorem cleanConn_injective (hL : 1 ≤ L) {x y : Site d} (hx : x ∈ top d L H ∪ sides d L H)
    (hy : y ∈ top d L H ∪ sides d L H) (h : cleanConn d L H x = cleanConn d L H y) : x = y := by
  rw [cleanConn, cleanConn, Sym2.eq_iff] at h
  rcases h with ⟨h, -⟩ | ⟨h, -⟩
  · exact h
  · exact absurd (h ▸ mem_brick_of_mem_top_union_sides hx) (add_cleanNormal_notMem_brick hL hy)

/-- **The clean rule separates**: `(4m+2)`-far distinct vertices of `T ∪ S` have disjoint clean
edge sets. [cite: GrimmettPercolation1999, §7.3 p. 165 (disjoint squares)] -/
theorem cleanEdges_disjoint_of_far (hL : m + 1 ≤ L) (hH : 2 * m + 2 ≤ H) {x y : Site d}
    (hx : x ∈ top d L H ∪ sides d L H) (hy : y ∈ top d L H ∪ sides d L H) (hxy : x ≠ y) (hfar : Far (4 * m + 2) x y) :
    Disjoint (cleanEdges d m L H x) (cleanEdges d m L H y) := by
  have hL1 : 1 ≤ L := by omega
  rw [Finset.disjoint_left]
  intro e hex hey
  rw [cleanEdges, Finset.mem_insert] at hex hey
  rcases hex with rfl | hex <;> rcases hey with h | hey
  · exact hxy (cleanConn_injective hL1 hx hy h)
  · exact cleanConn_notMem_sqEdges hL1 hx hy hey
  · exact cleanConn_notMem_sqEdges hL1 hy hx (h ▸ hex)
  · exact Finset.disjoint_left.1 (Finset.disjoint_coe.1 (disjoint_sqEdges (square_finite _ _ _) (square_finite _ _ _)
      (cleanSquare_disjoint_of_far hL hH hx hy hfar))) hex hey

/-- Clean edges are lattice edges. [folklore] -/
theorem cleanEdges_subset_edgeSet (hL : 1 ≤ L) {x : Site d} (hx : x ∈ top d L H ∪ sides d L H) :
    (↑(cleanEdges d m L H x) : Set (Sym2 (Site d))) ⊆ (zdGraph d).edgeSet := by
  intro e he
  rw [Finset.mem_coe, cleanEdges, Finset.mem_insert] at he
  rcases he with rfl | he
  · exact (SimpleGraph.mem_edgeSet _).2 (adj_add_cleanNormal hL hx)
  · exact sqEdges_subset_edgeSet _ _ he

/-- **Clean edges avoid `B(L,H)*`**: every clean edge has an endpoint outside the brick.
[cite: GrimmettPercolation1999, §7.3 p. 168 (iv), p. 173 (C)] -/
theorem cleanEdges_disjoint_brickStar (hL : 1 ≤ L) {x : Site d} (hx : x ∈ top d L H ∪ sides d L H) :
    Disjoint (brickStar d L H).edgeSet (↑(cleanEdges d m L H x) : Set (Sym2 (Site d))) := by
  rw [Set.disjoint_left]
  intro e heK he
  rw [Finset.mem_coe, cleanEdges, Finset.mem_insert] at he
  have hboth : ∀ u v : Site d, s(u, v) ∈ (brickStar d L H).edgeSet → u ∈ brick d L H ∧ v ∈ brick d L H := by
    intro u v h
    rw [SimpleGraph.mem_edgeSet, brickStar, starGraph_adj] at h
    exact ⟨h.2.1, h.2.2.1⟩
  rcases he with rfl | he
  · exact add_cleanNormal_notMem_brick hL hx (hboth _ _ heK).2
  · rw [mem_sqEdges_iff] at he
    obtain ⟨u, hu, v, hv, -, rfl⟩ := he
    exact cleanSquare_disjoint_brick hL hx hu (hboth _ _ heK).1

/-- The size of the clean edge set: at most `|B(m)|² + 1`. [folklore] -/
theorem card_cleanEdges_le (m L H : ℕ) (x : Site d) : (cleanEdges d m L H x).card ≤ (box d m).card ^ 2 + 1 := by
  rw [cleanEdges]
  refine (Finset.card_insert_le _ _).trans (Nat.add_le_add_right ?_ 1)
  exact (card_sqEdges_le _ _).trans (Nat.pow_le_pow_left (ncard_square_le _ _ _) 2)

/-! ### Symmetry of the clean rule under the horizontal reflections -/

/-- The outward sign transforms by the reflection's sign on the seed axis. [folklore] -/
theorem normalSign_refl {ε : Fin d → ℤˣ} (hε : ε 0 = 1) (L H : ℕ) (x : Site d) :
    normalSign d L H (refl ε x) = (ε (seedAxis d L H x) : ℤ) * normalSign d L H x := by
  have h0 : refl ε x 0 = x 0 := by rw [refl_apply, hε, Units.val_one, one_mul]
  simp only [normalSign, seedAxis_refl hε, h0]
  split_ifs with hx0
  · rw [seedAxis_of_top (L := L) hx0, hε]; simp
  · rw [refl_apply, BGN.sign_units_mul]

/-- The centre of the clean square is equivariant: `cleanCenter (refl x) = refl (cleanCenter x)`
(`L ≥ m + 1`). [folklore] -/
theorem cleanCenter_refl {ε : Fin d → ℤˣ} (hε : ε 0 = 1) (hL : m + 1 ≤ L) (x : Site d) :
    cleanCenter d m L H (refl ε x) = refl ε (cleanCenter d m L H x) := by
  have hk := seedAxis_refl hε L H x
  have hs := normalSign_refl hε L H x
  funext i
  simp only [cleanCenter, hk, refl_apply]
  split_ifs with h1 h2
  · subst h1; rw [hs]; ring
  · subst h2; simp [hε]
  · rw [BGN.clampZ_units_mul (by omega)]

/-- The clean square is equivariant: `cleanSquare (refl x) = refl '' cleanSquare x`. [folklore] -/
theorem cleanSquare_refl {ε : Fin d → ℤˣ} (hε : ε 0 = 1) (hL : m + 1 ≤ L) (x : Site d) :
    cleanSquare d m L H (refl ε x) = refl ε '' cleanSquare d m L H x := by
  rw [cleanSquare, cleanSquare, seedAxis_refl hε, cleanCenter_refl hε hL, refl, image_square_signedPerm]
  simp

/-- The normal step is equivariant. [folklore] -/
theorem cleanNormal_refl {ε : Fin d → ℤˣ} (hε : ε 0 = 1) (L H : ℕ) (x : Site d) :
    cleanNormal d L H (refl ε x) = refl ε (cleanNormal d L H x) := by
  funext i
  simp only [cleanNormal, seedAxis_refl hε, normalSign_refl hε, refl_apply, Pi.single_apply]
  split_ifs with h
  · subst h; ring
  · ring

/-- The connecting edge is equivariant. [folklore] -/
theorem cleanConn_refl {ε : Fin d → ℤˣ} (hε : ε 0 = 1) (L H : ℕ) (x : Site d) :
    cleanConn d L H (refl ε x) = sym2Equiv (refl ε) (cleanConn d L H x) := by
  rw [cleanConn, cleanConn, sym2Equiv_mk, cleanNormal_refl hε]
  congr 1
  rw [refl, Site.signedPerm_add]

/-- **The clean rule commutes with the horizontal reflections.** [cite: GrimmettPercolation1999, §7.3 p. 168 (by symmetry)] -/
theorem cleanEdges_refl {ε : Fin d → ℤˣ} (hε : ε 0 = 1) (hL : m + 1 ≤ L) (x : Site d) :
    cleanEdges d m L H (refl ε x) = (cleanEdges d m L H x).map (sym2Equiv (refl ε)).toEmbedding := by
  rw [cleanEdges, cleanEdges, Finset.map_insert, Equiv.coe_toEmbedding, ← cleanConn_refl hε]
  congr 1
  have h := sqEdges_image (zdSignedPermIso 1 ε) (cleanSquare d m L H x) (square_finite _ _ _)
    (by rw [show ((zdSignedPermIso 1 ε) : Site d → Site d) = refl ε from rfl, ← cleanSquare_refl hε hL]
        exact square_finite _ _ _)
  have himg : ((zdSignedPermIso 1 ε) '' cleanSquare d m L H x) = cleanSquare d m L H (refl ε x) := by
    rw [cleanSquare_refl hε hL]; rfl
  simp only [himg] at h
  exact h

/-- **The clean rule is a valid seed rule** on bricks with `L ≥ m + 1`, `H ≥ 2m + 2`, with
separation radius `4m + 2` and size bound `|B(m)|² + 1`. [cite: GrimmettPercolation1999, §7.3 pp. 165, 168, 173] -/
theorem seedRuleValid_cleanEdges (hL : m + 1 ≤ L) (hH : 2 * m + 2 ≤ H) :
    SeedRuleValid (cleanEdges d m L H) L H (4 * m + 2) ((box d m).card ^ 2 + 1) := by
  have hL1 : 1 ≤ L := by omega
  exact ⟨fun x hx => cleanEdges_subset_edgeSet hL1 hx, fun x hx => cleanEdges_disjoint_brickStar hL1 hx,
    card_cleanEdges_le m L H, fun x hx y hy hxy hfar => cleanEdges_disjoint_of_far hL hH hx hy hxy hfar,
    fun ε hε x => cleanEdges_refl hε hL x⟩

end Clean

/-! ## Lemma (7.36) for clean seeds in `ℤ^d` -/

/-- **Lemma (7.36) for clean seeds, in `ℤ^d`, at every density.** For `d ≥ 2`, `p ∈ (0,1)` with
`θ_ℍ(p) > 0`, `η > 0` and any size request `Lreq m H₀`, there are `m ≥ 1`, `H₀ ≥ 2m + 2`,
`L ≥ max(m + 2, Lreq m H₀)`, `H > H₀` with `P_p(goodC on B(L,H)) > 1 - η` and
`P_p(topGoodC on B(L,h)) > 1 - η` for every `H₀ < h ≤ H` (`BGNd.lemma_7_36R` for the clean rule,
valid by `seedRuleValid_cleanEdges`). [cite: GrimmettPercolation1999, Lemma (7.36) pp. 164–169; (B)–(C) p. 173] -/
theorem lemma_7_36C [NeZero d] (hd : 2 ≤ d) (Lreq : ℕ → ℕ → ℕ) (p : unitInterval) (hp0 : 0 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) (hθ : 0 < theta (halfSpaceGraph d) (halfSpaceOrigin d) p) {η : ℝ} (hη : 0 < η) :
    ∃ m H₀ L H : ℕ, 1 ≤ m ∧ 2 * m + 2 ≤ H₀ ∧ H₀ < H ∧ m + 2 ≤ L ∧ Lreq m H₀ ≤ L ∧
      1 - η < (bondPercolation (zdGraph d) p).real (goodC d m L H) ∧
      ∀ h, H₀ < h → h ≤ H → 1 - η < (bondPercolation (zdGraph d) p).real (topGoodC d m L h) := by
  obtain ⟨m, H₀, L, H, hm1, -, -, hHmin, hH₀H, hLmin, hLreq, hgood, htop⟩ :=
    lemma_7_36R hd (fun m L H => cleanEdges d m L H) (fun m => 4 * m + 2) (fun m => (box d m).card ^ 2 + 1)
      (fun m => m + 2) (fun m => 2 * m + 2) Lreq
      (fun m _ _ hL hH => seedRuleValid_cleanEdges (by omega) hH) p hp0 hp1 hθ hη
  exact ⟨m, H₀, L, H, hm1, hHmin, hH₀H, hLmin, hLreq, hgood, htop⟩

end BGNd

end Percolation.Literature

end
