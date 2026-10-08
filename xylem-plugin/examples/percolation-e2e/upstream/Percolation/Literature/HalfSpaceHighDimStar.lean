import Percolation.Literature.ConstrainedClusters
import Percolation.Literature.FiniteEnergy
import Percolation.Literature.HalfSpaceHighDim
import Percolation.Literature.ZeroOneLaw
import Percolation.Util.Linter

/-!
# Seeds of the half-space percolate in `ℍ*`, in `ℤ^d`: the first step of Lemma (7.36) / BGN (2.2)

Grimmett, p. 165:

> "Assume that `θ_ℍ(p_c) > 0`, and let `L` denote the plane `ℤ² × {0}`. The event
> `J = {L ↔ ∞ in ℍ*}` is invariant under shifts of the form `x ↦ x + (i, j, 0)` for `i, j ∈ ℤ`;
> therefore `J` has probability either `0` or `1`, by the zero–one law … Now,
> `P_{p_c}(J) ≥ P_{p_c}(0 ↔ ∞ in ℍ*) ≥ p_c P_{p_c}((0,0,1) ↔ ∞ in ℍ + (0,0,1)) = p_c θ_ℍ(p_c) > 0`,
> whence `P_{p_c}(J) = 1`. Therefore, `P_{p_c}(b(0) ↔ ∞ in ℍ*) → 1` as `m → ∞`."

BGN 1991, p. 121, (2.2a): "choose `k = k(η)` so that `P(b_d(k) ↔ ∞ in ℍ*) > 1 - η²`" (there in
the case where no slab percolates; the present statement is its unconditional form).

In the coordinates of `HalfSpace.lean` the vertical axis is `0`, `ℍ = {x | 0 ≤ x 0}`,
`L = BGNd.plane 0`, `(0,…,0,1) = BGNd.up`, `b(0) = BGNd.centralSquare d m`. Contents (all `d`,
the zero–one law for `d ≥ 2`):

* `BGNd.halfSpaceStar d` — the step graph of `ℍ*` (steps inside `ℍ` not joining two vertices of
  `L`), `BGNd.upperHalfSpace` (`ℍ + up`);
* `BGNd.planePercolates` — `J = {L ↔ ∞ in ℍ*}`, measurable, invariant under horizontal
  translations, of probability `0` or `1` (`ZeroOneLaw.lean`);
* `BGNd.theta_halfSpace_mul_le` — `p · θ_ℍ(p) ≤ P_p(0 ↔ ∞ in ℍ*)`;
* `BGNd.prob_planePercolates_eq_one`, `BGNd.tendsto_prob_centralSquarePercolates` — **(7.37)**:
  `θ_ℍ(p) > 0`, `p > 0` ⇒ `P_p(b(0) ↔ ∞ in ℍ*) → 1` as `m → ∞`, and its `ε`-form.

## References

* G. Grimmett, *Percolation*, 2nd ed., Grundlehren 321, Springer 1999, §7.3, p. 165, (7.37).
* D. J. Barsky, G. R. Grimmett, C. M. Newman, Probab. Theory Related Fields 90 (1991) 111–148,
  §2, (2.2).
-/

noncomputable section

namespace Percolation.Literature

open MeasureTheory ProbabilityTheory Filter LatticeModels
open scoped ENNReal Topology

namespace BGNd

variable {d : ℕ}

/-! ## The half-space `ℍ*` and its translates -/

/-- The vertical unit vector `(0,…,0,1)` of Grimmett (the vertical axis is the coordinate `0`).
[cite: GrimmettPercolation1999, §7.3 p. 165] -/
def up [NeZero d] : Site d := Pi.single 0 1

/-- `up 0 = 1`. [folklore] -/
@[simp] theorem up_apply_zero [NeZero d] : (up : Site d) 0 = 1 := by simp [up]

/-- The horizontal hyperplane at height `h`, `{x | x 0 = h}` (Grimmett's `ℤ² × {h}`; `L` is the
hyperplane at height `0`). [cite: GrimmettPercolation1999, §7.3 p. 165 (L)] -/
def plane [NeZero d] (h : ℤ) : Set (Site d) := {x | x 0 = h}

/-- Membership in a hyperplane. [folklore] -/
@[simp] theorem mem_plane_iff [NeZero d] {h : ℤ} {x : Site d} : x ∈ plane h ↔ x 0 = h := Iff.rfl

/-- Membership in the half-space `ℍ = {0 ≤ x 0}`. [folklore] -/
theorem mem_halfSpace_iff [NeZero d] {x : Site d} : x ∈ halfSpace d ↔ 0 ≤ x 0 := Iff.rfl

/-- The step graph of **`ℍ*`**: nearest-neighbour steps of `ℤ^d` inside `ℍ` using no edge joining
two vertices of the boundary hyperplane `L = {x 0 = 0}` (Grimmett 1999, pp. 164–165:
"`x ↔ y in V*`", `V = ℍ`; BGN 1991, p. 120: "`ℍ*` (i.e., `ℍ` with the bonds in `ℤ^{d-1} × {0}`
removed)"). [cite: GrimmettPercolation1999, §7.3 pp. 164–165 (ℍ*)] -/
def halfSpaceStar (d : ℕ) [NeZero d] : SimpleGraph (Site d) :=
  starGraph (zdGraph d) (halfSpace d) (plane 0)

/-- The shifted half-space `ℍ + up = {x | 1 ≤ x 0}`. [cite: GrimmettPercolation1999, §7.3 p. 165] -/
def upperHalfSpace (d : ℕ) [NeZero d] : Set (Site d) := {x | 1 ≤ x 0}

/-- Membership in the shifted half-space. [folklore] -/
@[simp] theorem mem_upperHalfSpace_iff [NeZero d] {x : Site d} : x ∈ upperHalfSpace d ↔ 1 ≤ x 0 :=
  Iff.rfl

/-- Along an edge of `ℤ^d` the heights differ by at most one. [folklore] -/
theorem zdGraph_adj_apply_zero [NeZero d] {u v : Site d} (h : (zdGraph d).Adj u v) :
    v 0 ≤ u 0 + 1 ∧ u 0 ≤ v 0 + 1 := by
  obtain ⟨i, h | h⟩ := (zdGraph_adj_iff u v).1 h
  · rw [h]
    by_cases hi : i = 0
    · subst hi
      simp only [Pi.add_apply, Pi.single_eq_same]
      omega
    · have h0 : (0 : Fin d) ≠ i := fun h' => hi h'.symm
      simp only [Pi.add_apply, Pi.single_eq_of_ne h0, add_zero]
      omega
  · rw [h]
    by_cases hi : i = 0
    · subst hi
      simp only [Pi.add_apply, Pi.single_eq_same]
      omega
    · have h0 : (0 : Fin d) ≠ i := fun h' => hi h'.symm
      simp only [Pi.add_apply, Pi.single_eq_of_ne h0, add_zero]
      omega

/-- An open path of `ℍ + up` is an open path of `ℍ*` (it stays strictly above `L`).
[cite: GrimmettPercolation1999, §7.3 p. 165] -/
theorem withinGraph_upperHalfSpace_le_halfSpaceStar [NeZero d] :
    withinGraph (zdGraph d) (upperHalfSpace d) ≤ halfSpaceStar d := by
  refine withinGraph_le_starGraph (zdGraph d) (fun x hx => ?_) ?_
  · rw [mem_upperHalfSpace_iff] at hx
    exact mem_halfSpace_iff.2 (by omega)
  · rw [Set.disjoint_left]
    intro x hx hx0
    rw [mem_upperHalfSpace_iff] at hx
    rw [mem_plane_iff] at hx0
    omega

/-- The origin and `up` are neighbours in `ℤ^d`. [folklore] -/
theorem zdGraph_adj_zero_up [NeZero d] : (zdGraph d).Adj 0 (up : Site d) :=
  (zdGraph_adj_iff 0 up).2 ⟨0, Or.inl (by simp [up])⟩

/-- The edge `⟨0, up⟩` is a step of `ℍ*`. [cite: GrimmettPercolation1999, §7.3 p. 165] -/
theorem halfSpaceStar_adj_zero_up [NeZero d] : (halfSpaceStar d).Adj 0 up := by
  refine ⟨zdGraph_adj_zero_up, mem_halfSpace_iff.2 le_rfl, mem_halfSpace_iff.2 (by simp), ?_⟩
  rintro ⟨-, h⟩
  simp at h

/-- `ℍ*` is invariant under horizontal translations. [cite: GrimmettPercolation1999, §7.3 p. 165] -/
theorem halfSpaceStar_adj_shift [NeZero d] {v : Site d} (hv : v 0 = 0) (u w : Site d) :
    (halfSpaceStar d).Adj (Site.shift v u) (Site.shift v w) ↔ (halfSpaceStar d).Adj u w := by
  have hz : (zdGraph d).Adj (u + v) (w + v) ↔ (zdGraph d).Adj u w := zdGraph_adj_shift_iff v u w
  simp only [halfSpaceStar, starGraph_adj, hz, Site.shift_apply,
    mem_halfSpace_iff, mem_plane_iff, Pi.add_apply, hv, add_zero]

/-- Translation by `up` carries `ℍ` onto `ℍ + up`. [cite: GrimmettPercolation1999, §7.3 p. 165] -/
theorem withinGraph_upperHalfSpace_adj_shift_up [NeZero d] (u w : Site d) :
    (withinGraph (zdGraph d) (upperHalfSpace d)).Adj (Site.shift up u) (Site.shift up w) ↔
      (withinGraph (zdGraph d) (halfSpace d)).Adj u w := by
  have hz : (zdGraph d).Adj (u + up) (w + up) ↔ (zdGraph d).Adj u w := zdGraph_adj_shift_iff up u w
  simp only [withinGraph_adj, hz, Site.shift_apply, mem_upperHalfSpace_iff,
    mem_halfSpace_iff, Pi.add_apply, up_apply_zero]
  constructor
  · rintro ⟨h, hu, hw⟩
    exact ⟨h, by omega, by omega⟩
  · rintro ⟨h, hu, hw⟩
    exact ⟨h, by omega, by omega⟩

/-! ## The event `J = {L ↔ ∞ in ℍ*}` -/

/-- The event `J = {L ↔ ∞ in ℍ*}`: some vertex of the hyperplane `L` is the endpoint of an
infinite open path of `ℍ*`. [cite: GrimmettPercolation1999, §7.3 p. 165 (J)] -/
def planePercolates (d : ℕ) [NeZero d] : Set (BondConfig (Site d)) :=
  ⋃ x ∈ plane (d := d) (0 : ℤ), percolatesVia (halfSpaceStar d) x

/-- Membership in `J`. [folklore] -/
theorem mem_planePercolates_iff [NeZero d] {ω : BondConfig (Site d)} :
    ω ∈ planePercolates d ↔ ∃ x ∈ plane (d := d) (0 : ℤ), ω ∈ percolatesVia (halfSpaceStar d) x := by
  simp only [planePercolates, Set.mem_iUnion, exists_prop]

/-- `J` is measurable. [folklore] -/
theorem measurableSet_planePercolates [NeZero d] : MeasurableSet (planePercolates d) :=
  MeasurableSet.biUnion (Set.to_countable _) fun x _ => measurableSet_percolatesVia _ x

/-- **`J` is invariant under horizontal translations** ("invariant under shifts of the form
`x ↦ x + (i, j, 0)`", Grimmett 1999, p. 165). [cite: GrimmettPercolation1999, §7.3 p. 165] -/
theorem relabel_shift_preimage_planePercolates [NeZero d] {v : Site d} (hv : v 0 = 0) :
    BondConfig.relabel (sym2Equiv (Site.shift v)) ⁻¹' planePercolates d = planePercolates d := by
  ext ω
  simp only [Set.mem_preimage, mem_planePercolates_iff, mem_plane_iff]
  constructor
  · rintro ⟨x, hx, hω⟩
    refine ⟨x - v, by simp [Pi.sub_apply, hx, hv], ?_⟩
    have hx' : x = Site.shift v (x - v) := by simp
    rw [hx'] at hω
    exact (relabel_mem_percolatesVia_iff (Site.shift v) (halfSpaceStar_adj_shift hv) ω (x - v)).1 hω
  · rintro ⟨y, hy, hω⟩
    refine ⟨Site.shift v y, by simp [Pi.add_apply, hy, hv], ?_⟩
    exact (relabel_mem_percolatesVia_iff (Site.shift v) (halfSpaceStar_adj_shift hv) ω y).2 hω

/-- **`P_p(J) ∈ {0, 1}`** for `d ≥ 2`, by the zero–one law for translation-invariant events
(`ZeroOneLaw.lean`) applied to a horizontal unit translation. [cite: GrimmettPercolation1999, §7.3 p. 165] -/
theorem prob_planePercolates_zero_or_one [NeZero d] (hd : 2 ≤ d) (p : unitInterval) :
    bondPercolation (zdGraph d) p (planePercolates d) = 0 ∨
      bondPercolation (zdGraph d) p (planePercolates d) = 1 := by
  set a : Fin d := ⟨1, by omega⟩ with ha
  have ha0 : a ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp [ha] at this
  have hv : (Pi.single a 1 : Site d) ≠ 0 := by
    intro h
    have := congrFun h a
    simp at this
  exact bondPercolation_zero_one_of_relabel_shift p hv measurableSet_planePercolates
    (relabel_shift_preimage_planePercolates (by simp [Pi.single_eq_of_ne (Ne.symm ha0)]))

/-! ## `P_p(0 ↔ ∞ in ℍ*) ≥ p θ_ℍ(p)` -/

/-- `θ_ℍ(p) = P_p(0 ↔ ∞ in ℍ)` on the ambient configuration space (`ConstrainedClusters.lean`).
[cite: GrimmettPercolation1999, §7.3 p. 162 (θ_ℍ)] -/
theorem theta_halfSpace_eq_real_percolatesVia [NeZero d] (p : unitInterval) :
    theta (halfSpaceGraph d) (halfSpaceOrigin d) p =
      (bondPercolation (zdGraph d) p).real
        (percolatesVia (withinGraph (zdGraph d) (halfSpace d)) 0) :=
  theta_induce_eq_real_percolatesVia (zdGraph d) (halfSpace d) 0 (zero_mem_halfSpace d) p

/-- Translation invariance: `P_p(up ↔ ∞ in ℍ + up) = θ_ℍ(p)`. [cite: GrimmettPercolation1999, §7.3 p. 165] -/
theorem real_percolatesVia_upperHalfSpace_up [NeZero d] (p : unitInterval) :
    (bondPercolation (zdGraph d) p).real
        (percolatesVia (withinGraph (zdGraph d) (upperHalfSpace d)) up) =
      theta (halfSpaceGraph d) (halfSpaceOrigin d) p := by
  rw [theta_halfSpace_eq_real_percolatesVia,
    ← relabel_preimage_percolatesVia (Site.shift up) withinGraph_upperHalfSpace_adj_shift_up 0,
    bondPercolation_real_preimage_shift]
  simp

/-- The one-edge event `{e open}` is determined by that edge. [folklore] -/
theorem determinedBy_mem_edge (e : Sym2 (Site d)) :
    DeterminedBy {ω : BondConfig (Site d) | e ∈ ω} ({e} : Set (Sym2 (Site d))) := by
  rw [determinedBy_iff]
  intro ω ω' h
  simp only [Set.mem_setOf_eq]
  constructor
  · intro he
    exact ((Set.ext_iff.1 h e).1 ⟨he, rfl⟩).1
  · intro he
    exact ((Set.ext_iff.1 h e).2 ⟨he, rfl⟩).1

/-- The edge `⟨0, up⟩` is not an edge of `ℍ + up`. [folklore] -/
theorem edge_zero_up_notMem [NeZero d] :
    s((0 : Site d), up) ∉ (withinGraph (zdGraph d) (upperHalfSpace d)).edgeSet := by
  intro h
  rw [mem_edgeSet_withinGraph] at h
  have := h.2.1
  simp at this

/-- **`p · θ_ℍ(p) ≤ P_p(0 ↔ ∞ in ℍ*)`** (Grimmett 1999, p. 165:
"`P(0 ↔ ∞ in ℍ*) ≥ p_c P((0,0,1) ↔ ∞ in ℍ + (0,0,1)) = p_c θ_ℍ(p_c)`"): if the edge `⟨0, up⟩`
is open and `up` percolates in the shifted half-space then `0` percolates in `ℍ*`; the two events
are independent (determined by disjoint edge sets), of probabilities `p` and `θ_ℍ(p)`.
[cite: GrimmettPercolation1999, §7.3 p. 165] -/
theorem theta_halfSpace_mul_le [NeZero d] (p : unitInterval) :
    (p : ℝ) * theta (halfSpaceGraph d) (halfSpaceOrigin d) p ≤
      (bondPercolation (zdGraph d) p).real (percolatesVia (halfSpaceStar d) 0) := by
  set A : Set (BondConfig (Site d)) := {ω | s((0 : Site d), up) ∈ ω} with hA
  set B : Set (BondConfig (Site d)) :=
    percolatesVia (withinGraph (zdGraph d) (upperHalfSpace d)) up with hB
  have hPA : (bondPercolation (zdGraph d) p).real A = p :=
    bondPercolation_cylinder (zdGraph d) p ((SimpleGraph.mem_edgeSet _).2 zdGraph_adj_zero_up)
  have hPB : (bondPercolation (zdGraph d) p).real B =
      theta (halfSpaceGraph d) (halfSpaceOrigin d) p :=
    real_percolatesVia_upperHalfSpace_up p
  have hAB : (bondPercolation (zdGraph d) p).real (A ∩ B) =
      (bondPercolation (zdGraph d) p).real A * (bondPercolation (zdGraph d) p).real B :=
    bondPercolation_real_inter_of_disjoint (zdGraph d) p
      (Set.disjoint_singleton_left.2 edge_zero_up_notMem) (determinedBy_mem_edge _)
      (determinedBy_percolatesVia _ _) (measurableSet_mem _) (measurableSet_percolatesVia _ _)
  have hsub : A ∩ B ⊆ percolatesVia (halfSpaceStar d) 0 := fun ω hω =>
    mem_percolatesVia_of_adj withinGraph_upperHalfSpace_le_halfSpaceStar halfSpaceStar_adj_zero_up
      hω.1 hω.2
  calc (p : ℝ) * theta (halfSpaceGraph d) (halfSpaceOrigin d) p
      = (bondPercolation (zdGraph d) p).real (A ∩ B) := by rw [hAB, hPA, hPB]
    _ ≤ (bondPercolation (zdGraph d) p).real (percolatesVia (halfSpaceStar d) 0) :=
        measureReal_mono hsub

/-- **`P_p(J) = 1` when `θ_ℍ(p) > 0` and `p > 0`** (`d ≥ 2`; Grimmett 1999, p. 165: "whence
`P_{p_c}(J) = 1`"). [cite: GrimmettPercolation1999, §7.3 p. 165] -/
theorem prob_planePercolates_eq_one [NeZero d] (hd : 2 ≤ d) (p : unitInterval) (hp : 0 < (p : ℝ))
    (hθ : 0 < theta (halfSpaceGraph d) (halfSpaceOrigin d) p) :
    bondPercolation (zdGraph d) p (planePercolates d) = 1 := by
  have hpos : 0 < (bondPercolation (zdGraph d) p).real (planePercolates d) := by
    calc (0 : ℝ) < (p : ℝ) * theta (halfSpaceGraph d) (halfSpaceOrigin d) p := mul_pos hp hθ
      _ ≤ (bondPercolation (zdGraph d) p).real (percolatesVia (halfSpaceStar d) 0) :=
          theta_halfSpace_mul_le p
      _ ≤ (bondPercolation (zdGraph d) p).real (planePercolates d) :=
          measureReal_mono fun ω hω => mem_planePercolates_iff.2 ⟨0, rfl, hω⟩
  rcases prob_planePercolates_zero_or_one hd p with h0 | h1
  · exfalso
    rw [measureReal_def, h0, ENNReal.toReal_zero] at hpos
    exact lt_irrefl _ hpos
  · exact h1

/-! ## (7.37): `P_p(b(0) ↔ ∞ in ℍ*) → 1` as `m → ∞` -/

/-- The event `{b(0) ↔ ∞ in ℍ*}`: some vertex of the central square `b(0) = b_d(m)` is the
endpoint of an infinite open path of `ℍ*`. [cite: GrimmettPercolation1999, §7.3 p. 165 (7.37)] -/
def centralSquarePercolates (d m : ℕ) [NeZero d] : Set (BondConfig (Site d)) :=
  ⋃ x ∈ centralSquare d m, percolatesVia (halfSpaceStar d) x

/-- Membership in `{b(0) ↔ ∞ in ℍ*}`. [folklore] -/
theorem mem_centralSquarePercolates_iff [NeZero d] {m : ℕ} {ω : BondConfig (Site d)} :
    ω ∈ centralSquarePercolates d m ↔
      ∃ x ∈ centralSquare d m, ω ∈ percolatesVia (halfSpaceStar d) x := by
  simp only [centralSquarePercolates, Set.mem_iUnion, exists_prop]

/-- `{b(0) ↔ ∞ in ℍ*}` is measurable. [folklore] -/
theorem measurableSet_centralSquarePercolates [NeZero d] (m : ℕ) :
    MeasurableSet (centralSquarePercolates d m) :=
  MeasurableSet.biUnion (Set.to_countable _) fun x _ => measurableSet_percolatesVia _ x

/-- Membership in the central square `b(0)`: `y 0 = 0` and `|y j| ≤ m` for `j ≠ 0`. [folklore] -/
theorem mem_centralSquare_iff [NeZero d] {m : ℕ} {y : Site d} :
    y ∈ centralSquare d m ↔ y 0 = 0 ∧ ∀ j, j ≠ 0 → |y j| ≤ m := by
  simp [centralSquare, mem_square]

/-- The central squares increase with `m`. [folklore] -/
theorem centralSquare_mono [NeZero d] {m m' : ℕ} (h : m ≤ m') :
    centralSquare d m ⊆ centralSquare d m' := by
  intro y hy
  rw [mem_centralSquare_iff] at hy ⊢
  exact ⟨hy.1, fun j hj => (hy.2 j hj).trans (by exact_mod_cast h)⟩

/-- The central squares exhaust the hyperplane `L`. [folklore] -/
theorem iUnion_centralSquare [NeZero d] : ⋃ m : ℕ, centralSquare d m = plane 0 := by
  ext y
  simp only [Set.mem_iUnion, mem_centralSquare_iff, mem_plane_iff]
  constructor
  · rintro ⟨_, hy, -⟩
    exact hy
  · intro hy
    refine ⟨Finset.univ.sup fun j => (y j).natAbs, hy, fun j _ => ?_⟩
    have h : (y j).natAbs ≤ Finset.univ.sup fun j => (y j).natAbs :=
      Finset.le_sup (f := fun j => (y j).natAbs) (Finset.mem_univ j)
    calc |y j| = ((y j).natAbs : ℤ) := (Int.natCast_natAbs (y j)).symm
      _ ≤ _ := by exact_mod_cast h

/-- The events `{b(0) ↔ ∞ in ℍ*}` increase with `m`. [folklore] -/
theorem centralSquarePercolates_mono [NeZero d] :
    Monotone fun m => centralSquarePercolates d m := by
  intro m m' h ω hω
  rw [mem_centralSquarePercolates_iff] at hω ⊢
  obtain ⟨x, hx, hω⟩ := hω
  exact ⟨x, centralSquare_mono h hx, hω⟩

/-- `⋃_m {b(0) ↔ ∞ in ℍ*} = J`. [folklore] -/
theorem iUnion_centralSquarePercolates [NeZero d] :
    ⋃ m : ℕ, centralSquarePercolates d m = planePercolates d := by
  ext ω
  simp only [Set.mem_iUnion, mem_centralSquarePercolates_iff, mem_planePercolates_iff,
    ← iUnion_centralSquare]
  constructor
  · rintro ⟨m, x, hx, hω⟩
    exact ⟨x, ⟨m, hx⟩, hω⟩
  · rintro ⟨x, ⟨m, hx⟩, hω⟩
    exact ⟨m, x, hx, hω⟩

/-- **(7.37): `P_p(b(0) ↔ ∞ in ℍ*) → 1` as `m → ∞`**, whenever `d ≥ 2`, `θ_ℍ(p) > 0` and
`p > 0` (Grimmett 1999, p. 165: "Therefore, `P_{p_c}(b(0) ↔ ∞ in ℍ*) → 1` as `m → ∞`, and we
choose `m = m(ε)` such that (7.37) `P_{p_c}(b(0) ↔ ∞ in ℍ*) > 1 - ε²`"; BGN 1991, (2.2a)).
Continuity of measure along `{b(0) ↔ ∞ in ℍ*} ↑ J` and `P_p(J) = 1`.
[cite: GrimmettPercolation1999, §7.3 p. 165 (7.37)] -/
theorem tendsto_prob_centralSquarePercolates [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hp : 0 < (p : ℝ)) (hθ : 0 < theta (halfSpaceGraph d) (halfSpaceOrigin d) p) :
    Tendsto (fun m : ℕ => (bondPercolation (zdGraph d) p).real (centralSquarePercolates d m))
      atTop (𝓝 1) := by
  have h1 : Tendsto (fun m : ℕ => bondPercolation (zdGraph d) p (centralSquarePercolates d m))
      atTop (𝓝 (bondPercolation (zdGraph d) p (⋃ m : ℕ, centralSquarePercolates d m))) :=
    tendsto_measure_iUnion_atTop centralSquarePercolates_mono
  rw [iUnion_centralSquarePercolates, prob_planePercolates_eq_one hd p hp hθ] at h1
  have h2 := (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp h1
  rw [ENNReal.toReal_one] at h2
  exact h2

/-- (7.37) in `ε`-form: for every `ε > 0` there is `m₀` such that
`P_p(b(0) ↔ ∞ in ℍ*) > 1 - ε` for all `m ≥ m₀`. [cite: GrimmettPercolation1999, §7.3 p. 165 (7.37)] -/
theorem exists_prob_centralSquarePercolates_gt [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hp : 0 < (p : ℝ)) (hθ : 0 < theta (halfSpaceGraph d) (halfSpaceOrigin d) p) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ m₀ : ℕ, ∀ m, m₀ ≤ m →
      1 - ε < (bondPercolation (zdGraph d) p).real (centralSquarePercolates d m) := by
  have h := tendsto_prob_centralSquarePercolates hd p hp hθ
  have hev : ∀ᶠ m in atTop,
      1 - ε < (bondPercolation (zdGraph d) p).real (centralSquarePercolates d m) :=
    h.eventually (Ioi_mem_nhds (by linarith))
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.1 hev
  exact ⟨m₀, hm₀⟩

end BGNd

end Percolation.Literature

end
