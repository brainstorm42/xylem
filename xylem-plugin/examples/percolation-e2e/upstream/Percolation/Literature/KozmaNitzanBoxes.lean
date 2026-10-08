import Percolation.Literature.GMFiniteSize
import Percolation.Literature.KozmaNitzanReduction
import Percolation.Util.Linter

/-!
# Kozma–Nitzan, Theorem 6 — toolkit II: boxes of `ℤ^d`, their boundaries, seeds near a contact

Second proofs-only companion of
`KozmaNitzanReduction.lean` (G. Kozma, S. Nitzan, arXiv:2401.12397, §4), used by the proof of the
target lemma (Lemma 10, pp. 17–22). Pure lattice geometry, no probability:

* for a vertex `y` on the inner boundary of a big box `X`, crossed in direction `(i, σ)`, the
  **window** `KNWin`: a `(d-1)`-dimensional plaquette `P ∋` (a short path to) `y` of side `2M+1`
  inside the face of `X`, its inward translate `U`, and the cube `Q = v + Λ_M` of which `U` is the
  outward face, with `Q` inside the shell `S = X⟨-1⟩ \ X⟨-2M-2⟩` (KN pp. 19–21: plaquettes, seeds,
  "`v + [-M,M]^d ⊆ S`", the faces `U(v)`, the point `v(P)` and the face `U(P)`); here, instead of
  tiling `∂X` by plaquettes (p. 19), one plaquette is attached to each contact vertex, and distinct
  contacts far apart get disjoint seed edge sets (`seedEdges_disjoint`);
* staircase lattice paths inside a box (`exists_pathIn_Icc`), used to join `y` to its plaquette and
  to move inside a seed.

## References

* G. Kozma, S. Nitzan, arXiv:2401.12397 (2024), §4 pp. 15–21.
* G. Grimmett, *Percolation*, 2nd ed. (1999), §7.2 (boxes, seeds).
-/

noncomputable section

open MeasureTheory

namespace Percolation.Literature

open LatticeModels SimpleGraph

namespace KozmaNitzan

variable {d : ℕ}

/-! ## Boxes `Icc lo hi` of `ℤ^d` -/

/-- Membership in a box, coordinatewise. [folklore] -/
theorem mem_Icc_iff {lo hi x : Site d} : x ∈ Finset.Icc lo hi ↔ ∀ i, lo i ≤ x i ∧ x i ≤ hi i := by
  rw [Finset.mem_Icc, Pi.le_def, Pi.le_def]
  exact ⟨fun h i => ⟨h.1 i, h.2 i⟩, fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩⟩

/-- The unit vector `e_i`. [folklore] -/
abbrev unitVec (i : Fin d) : Site d := Pi.single i 1

/-- `e_i` has `i`-th coordinate `1`. [folklore] -/
theorem unitVec_apply_self (i : Fin d) : unitVec i i = 1 := by simp [unitVec]

/-- `e_i` has all other coordinates `0`. [folklore] -/
theorem unitVec_apply_of_ne {i j : Fin d} (h : j ≠ i) : unitVec i j = 0 := by simp [unitVec, h]

/-- Adjacency in `ℤ^d`: `y = x + σ e_i` for a direction `i` and a sign `σ = ±1`. [folklore] -/
theorem adj_iff_exists_sign {x y : Site d} :
    (zdGraph d).Adj x y ↔ ∃ (i : Fin d) (σ : ℤ), (σ = 1 ∨ σ = -1) ∧ y = x + σ • unitVec i := by
  rw [zdGraph_adj_iff]
  constructor
  · rintro ⟨i, h | h⟩
    · exact ⟨i, 1, Or.inl rfl, by rw [one_smul]; exact h⟩
    · refine ⟨i, -1, Or.inr rfl, ?_⟩
      rw [h, neg_smul, one_smul, add_neg_cancel_right]
  · rintro ⟨i, σ, hσ | hσ, h⟩
    · exact ⟨i, Or.inl (by rw [h, hσ, one_smul])⟩
    · refine ⟨i, Or.inr ?_⟩
      rw [h, hσ, neg_smul, one_smul, neg_add_cancel_right]

/-- Coordinates of `x + σ e_i`. [folklore] -/
theorem add_smul_unitVec_apply (x : Site d) (σ : ℤ) (i j : Fin d) :
    (x + σ • unitVec i) j = x j + if j = i then σ else 0 := by
  by_cases h : j = i
  · subst h; simp [unitVec]
  · simp [unitVec, h]

/-- Adjacent vertices differ by `1` in exactly one coordinate (in sup-norm they are at distance `1`).
[folklore] -/
theorem abs_sub_le_one_of_adj {x y : Site d} (h : (zdGraph d).Adj x y) (j : Fin d) : |y j - x j| ≤ 1 := by
  obtain ⟨i, σ, hσ, rfl⟩ := adj_iff_exists_sign.1 h
  rw [add_smul_unitVec_apply]
  by_cases hj : j = i
  · rw [if_pos hj]; rcases hσ with rfl | rfl <;> simp
  · rw [if_neg hj]; simp

/-- **Inner vertex boundary of a box**: a vertex of `Icc lo hi` has a neighbour outside iff one of
its coordinates is extreme. [cite: KozmaNitzan2024, §4 p. 15 (∂_iv)] -/
theorem mem_innerBoundary_Icc {lo hi x : Site d} :
    x ∈ innerBoundary (zdGraph d) (Finset.Icc lo hi) ↔
      x ∈ Finset.Icc lo hi ∧ ∃ i, x i = lo i ∨ x i = hi i := by
  rw [mem_innerBoundary_iff]
  refine and_congr_right fun hx => ?_
  rw [mem_Icc_iff] at hx
  constructor
  · rintro ⟨y, hy, hxy⟩
    obtain ⟨i, σ, hσ, rfl⟩ := adj_iff_exists_sign.1 hxy
    rw [mem_Icc_iff] at hy
    push Not at hy
    obtain ⟨j, hj⟩ := hy
    refine ⟨j, ?_⟩
    rw [add_smul_unitVec_apply] at hj
    have hxj := hx j
    by_cases hji : j = i
    · rw [if_pos hji] at hj
      rcases hσ with rfl | rfl <;> omega
    · rw [if_neg hji] at hj; omega
  · rintro ⟨i, hi | hi⟩
    · refine ⟨x + (-1 : ℤ) • unitVec i, ?_, adj_iff_exists_sign.2 ⟨i, -1, Or.inr rfl, rfl⟩⟩
      rw [mem_Icc_iff]; push Not
      refine ⟨i, fun h => ?_⟩
      rw [add_smul_unitVec_apply, if_pos rfl] at h ⊢; omega
    · refine ⟨x + (1 : ℤ) • unitVec i, ?_, adj_iff_exists_sign.2 ⟨i, 1, Or.inl rfl, rfl⟩⟩
      rw [mem_Icc_iff]; push Not
      refine ⟨i, fun h => ?_⟩
      rw [add_smul_unitVec_apply, if_pos rfl]; omega

/-- **Outer vertex boundary of a box**: a vertex outside `Icc lo hi` with a neighbour inside lies in
the enlarged box `Icc (lo - 1) (hi + 1)`, and its neighbour inside is `x - σ e_i` where `i` is the
(unique) coordinate leaving the box. Here: the membership consequences used below.
[cite: KozmaNitzan2024, §4 p. 15 (∂_ev)] -/
theorem mem_Icc_enlarge_one_of_mem_outerBoundary {lo hi x : Site d}
    (hx : x ∈ outerBoundary (zdGraph d) (Finset.Icc lo hi)) :
    x ∈ Finset.Icc (lo - 1) (hi + 1) := by
  rw [mem_outerBoundary_iff] at hx
  obtain ⟨-, y, hy, hxy⟩ := hx
  rw [mem_Icc_iff] at hy ⊢
  intro j
  have h1 := abs_sub_le_one_of_adj hxy j
  have h2 := hy j
  simp only [Pi.sub_apply, Pi.add_apply, Pi.one_apply]
  rw [abs_le] at h1
  omega

/-- Enlarged boxes are nested. [cite: KozmaNitzan2024, §4 p. 15 (B⟨R⟩)] -/
theorem Icc_enlarge_mono {lo hi : Site d} {R R' : ℕ} (h : R ≤ R') :
    Finset.Icc (lo - R) (hi + R) ⊆ Finset.Icc (lo - R') (hi + R') := by
  intro x hx
  rw [mem_Icc_iff] at hx ⊢
  intro i
  have := hx i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply] at this ⊢
  omega

/-- `B ⊆ B⟨R⟩`. [cite: KozmaNitzan2024, §4 p. 15] -/
theorem Icc_subset_enlarge (lo hi : Site d) (R : ℕ) :
    Finset.Icc lo hi ⊆ Finset.Icc (lo - R) (hi + R) := by
  have := Icc_enlarge_mono (lo := lo) (hi := hi) (Nat.zero_le R)
  simpa using this

/-- The outer boundary of `B⟨R⟩` lies in `B⟨R+1⟩`. [folklore] -/
theorem outerBoundary_enlarge_subset (lo hi : Site d) (R : ℕ) :
    outerBoundary (zdGraph d) (Finset.Icc (lo - R) (hi + R)) ⊆ Finset.Icc (lo - (R + 1 : ℕ)) (hi + (R + 1 : ℕ)) := by
  intro x hx
  have := mem_Icc_enlarge_one_of_mem_outerBoundary hx
  rw [mem_Icc_iff] at this ⊢
  intro i
  have h := this i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply, Nat.cast_add,
    Nat.cast_one] at h ⊢
  omega

/-- A vertex of `B⟨R⟩` is not on the inner boundary of `B⟨R+1⟩` … more usefully: every vertex of
`B⟨R⟩` has all its neighbours in `B⟨R+1⟩`, so it is NOT an inner-boundary vertex of any box
containing `B⟨R+1⟩`. [folklore] -/
theorem not_mem_innerBoundary_of_enlarge_succ_subset {lo hi : Site d} {R : ℕ} {D : Finset (Site d)}
    (hD : Finset.Icc (lo - (R + 1 : ℕ)) (hi + (R + 1 : ℕ)) ⊆ D) {x : Site d}
    (hx : x ∈ Finset.Icc (lo - R) (hi + R)) : x ∉ innerBoundary (zdGraph d) D := by
  rw [mem_innerBoundary_iff]
  rintro ⟨-, y, hy, hxy⟩
  apply hy
  apply hD
  rw [mem_Icc_iff] at hx ⊢
  intro j
  have h1 := abs_sub_le_one_of_adj hxy j
  have h2 := hx j
  simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply, Nat.cast_add, Nat.cast_one,
    Pi.one_apply] at h2 ⊢
  rw [abs_le] at h1
  omega

/-! ## Staircase paths inside a box -/

/-- Two vertices of a box are joined by a lattice path inside the box (move one coordinate at a
time). [folklore] -/
theorem exists_pathIn_Icc {lo hi : Site d} {x y : Site d} (hx : x ∈ Finset.Icc lo hi)
    (hy : y ∈ Finset.Icc lo hi) : PathIn (zdGraph d) (↑(Finset.Icc lo hi) : Set (Site d)) x y := by
  -- induction on the `ℓ¹` distance
  suffices H : ∀ (n : ℕ) (x : Site d), x ∈ Finset.Icc lo hi → ∑ i, (y i - x i).natAbs = n →
      PathIn (zdGraph d) (↑(Finset.Icc lo hi) : Set (Site d)) x y from H _ x hx rfl
  intro n
  induction n with
  | zero =>
    intro x hx h0
    have : x = y := by
      funext i
      have := Finset.sum_eq_zero_iff.1 h0 i (Finset.mem_univ i)
      omega
    subst this
    exact PathIn.refl (Finset.mem_coe.2 hx)
  | succ n ih =>
    intro x hx hsum
    -- some coordinate differs
    obtain ⟨i, hne⟩ : ∃ i, y i ≠ x i := by
      by_contra hc
      push Not at hc
      have : ∑ i, (y i - x i).natAbs = 0 := Finset.sum_eq_zero fun i _ => by rw [hc i, sub_self]; rfl
      omega
    have hxmem := mem_Icc_iff.1 hx
    have hymem := mem_Icc_iff.1 hy
    -- step towards `y` in coordinate `i`
    obtain ⟨σ, hσ, hrange, hdec⟩ : ∃ σ : ℤ, (σ = 1 ∨ σ = -1) ∧
        (lo i ≤ x i + σ ∧ x i + σ ≤ hi i) ∧ (y i - (x i + σ)).natAbs + 1 = (y i - x i).natAbs := by
      have h1 := hxmem i; have h2 := hymem i
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact ⟨-1, Or.inr rfl, by omega, by omega⟩
      · exact ⟨1, Or.inl rfl, by omega, by omega⟩
    set x' : Site d := x + σ • unitVec i with hx'
    have hx'i : x' i = x i + σ := by rw [hx', add_smul_unitVec_apply, if_pos rfl]
    have hx'j : ∀ j, j ≠ i → x' j = x j := fun j hj => by
      rw [hx', add_smul_unitVec_apply, if_neg hj, add_zero]
    have hx'mem : x' ∈ Finset.Icc lo hi := by
      rw [mem_Icc_iff]
      intro j
      by_cases hji : j = i
      · subst hji; rw [hx'i]; exact hrange
      · rw [hx'j j hji]; exact hxmem j
    have hadj : (zdGraph d).Adj x x' := adj_iff_exists_sign.2 ⟨i, σ, hσ, rfl⟩
    have hsum' : ∑ j, (y j - x' j).natAbs = n := by
      have key : ∀ j, (y j - x' j).natAbs + (if j = i then 1 else 0) = (y j - x j).natAbs := by
        intro j
        by_cases hji : j = i
        · subst hji; rw [if_pos rfl, hx'i]; exact hdec
        · rw [if_neg hji, hx'j j hji]; simp
      have hs : ∑ j, ((y j - x' j).natAbs + (if j = i then 1 else 0)) = ∑ j, (y j - x j).natAbs :=
        Finset.sum_congr rfl fun j _ => key j
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ i, if_pos (Finset.mem_univ _),
        hsum] at hs
      omega
    exact (PathIn.of_adj (Finset.mem_coe.2 hx) (Finset.mem_coe.2 hx'mem) hadj).trans (ih x' hx'mem hsum')

/-! ## The outer boundary of a box: leaving direction and inner neighbour -/

/-- A vertex of the outer boundary of `Icc Lo Hi` leaves the box through exactly one coordinate
`i`, upwards (`σ = 1`, `x_i = Hi_i + 1`) or downwards (`σ = -1`, `x_i = Lo_i - 1`), all other
coordinates being in range. [cite: KozmaNitzan2024, §4 p. 18 ("each such vertex has exactly one edge connecting it to B⟨j⟩")] -/
theorem exists_dir_of_mem_outerBoundary {Lo Hi x : Site d}
    (hx : x ∈ outerBoundary (zdGraph d) (Finset.Icc Lo Hi)) :
    ∃ q : Fin d × ℤ, (q.2 = 1 ∨ q.2 = -1) ∧
      (q.2 = 1 ∧ x q.1 = Hi q.1 + 1 ∨ q.2 = -1 ∧ x q.1 = Lo q.1 - 1) ∧
      ∀ k, k ≠ q.1 → Lo k ≤ x k ∧ x k ≤ Hi k := by
  rw [mem_outerBoundary_iff] at hx
  obtain ⟨hxX, y, hy, hxy⟩ := hx
  obtain ⟨i, σ, hσ, rfl⟩ := adj_iff_exists_sign.1 hxy.symm
  rw [mem_Icc_iff] at hy hxX
  push Not at hxX
  obtain ⟨j, hj⟩ := hxX
  have hyj := hy j
  rw [add_smul_unitVec_apply] at hj
  by_cases hji : j = i
  · subst hji
    rw [if_pos rfl] at hj
    refine ⟨(j, σ), hσ, ?_, fun k hk => ?_⟩
    · simp only
      rw [add_smul_unitVec_apply, if_pos rfl]
      rcases hσ with rfl | rfl
      · left; constructor; · rfl
        omega
      · right; constructor; · rfl
        omega
    · simp only at hk
      rw [add_smul_unitVec_apply, if_neg hk, add_zero]
      exact hy k
  · rw [if_neg hji] at hj; omega

/-! ## The window attached to an inner-boundary vertex (plaquette, face, cube, seed edges) -/

section Window

variable (Lo Hi : Site d) (M : ℕ) (i : Fin d) (σ : ℤ) (y : Site d)

/-- Clamp an integer into `[a, b]`. [folklore] -/
def clamp (t a b : ℤ) : ℤ := max a (min t b)

/-- The clamped value lies in `[a, b]`. [folklore] -/
theorem clamp_mem {t a b : ℤ} (hab : a ≤ b) : a ≤ clamp t a b ∧ clamp t a b ≤ b := by
  unfold clamp; constructor <;> omega

/-- Clamping a value at distance `≤ m` from `[a, b]` moves it by at most `m`. [folklore] -/
theorem abs_clamp_sub_le {t a b : ℤ} {m : ℤ} (hta : a - m ≤ t) (htb : t ≤ b + m) (hm : 0 ≤ m)
    (hab : a ≤ b) : |clamp t a b - t| ≤ m := by
  unfold clamp; rw [abs_le]; constructor <;> omega

/-- The centre of the window of `y`: `y` itself in direction `i`, and `y_k` clamped into
`[Lo_k + M + 1, Hi_k - M - 1]` in the other directions (so that the plaquette stays at distance
`≥ M + 1` from the lower-dimensional skeleton of the box). [cite: KozmaNitzan2024, §4 p. 21 (choice of v(P), U(P))] -/
def wctr : Site d :=
  Function.update (fun k => clamp (y k) (Lo k + M + 1) (Hi k - M - 1)) i (y i)

/-- The **plaquette** of `y`: the `(d-1)`-dimensional box of half-side `M` around `wctr` inside the
layer `{z_i = y_i}`. [cite: KozmaNitzan2024, §4 p. 19 (plaquettes)] -/
def plaq : Finset (Site d) :=
  Finset.Icc (Function.update (wctr Lo Hi M i y - (M : Site d)) i (y i))
    (Function.update (wctr Lo Hi M i y + (M : Site d)) i (y i))

/-- The **window region**: the `(d-1)`-dimensional box of half-side `M + 1` around `wctr` inside
the layer; it contains `y` and the plaquette, and all its lattice edges are required open in a
seed. [cite: KozmaNitzan2024, §4 p. 19 (seeds)] -/
def wreg : Finset (Site d) :=
  Finset.Icc (Function.update (wctr Lo Hi M i y - ((M + 1 : ℕ) : Site d)) i (y i))
    (Function.update (wctr Lo Hi M i y + ((M + 1 : ℕ) : Site d)) i (y i))

/-- The centre `v(P)` of the cube behind the plaquette: `wctr - σ (M+1) e_i`.
[cite: KozmaNitzan2024, §4 p. 21 (v(P))] -/
def vctr : Site d := wctr Lo Hi M i y - (σ * (M + 1 : ℕ)) • unitVec i

/-- The **cube** `Q = v(P) + Λ_M`. [cite: KozmaNitzan2024, §4 p. 19 ("v + [-M,M]^d ⊆ S")] -/
def cube : Finset (Site d) :=
  Finset.Icc (vctr Lo Hi M i σ y - (M : Site d)) (vctr Lo Hi M i σ y + (M : Site d))

/-- The **face** `U(P)`: the inward translate `plaq - σ e_i` of the plaquette, i.e. the outward
`i`-face of the cube. [cite: KozmaNitzan2024, §4 p. 21 (U(P))] -/
def uface : Finset (Site d) := (plaq Lo Hi M i y).image fun z => z - σ • unitVec i

/-- The **seed edges** of `y` (with its outer neighbour `y + σ e_i`): all lattice edges inside the
window region, the inward edges `{z, z - σ e_i}` from the plaquette, and the contact edge
`{y + σ e_i, y}`. [cite: KozmaNitzan2024, §4 p. 19 ("Call a given plaquette a seed if …")] -/
def seedEdges : Finset (Sym2 (Site d)) :=
  edgesIn (zdGraph d) (wreg Lo Hi M i y) ∪
    ((plaq Lo Hi M i y).image fun z => s(z, z - σ • unitVec i)) ∪ {s(y + σ • unitVec i, y)}

variable {Lo Hi M i σ y}

/-- The window centre agrees with `y` in direction `i`. [folklore] -/
theorem wctr_apply_self : wctr Lo Hi M i y i = y i := by simp [wctr]

/-- The transverse coordinates of the window centre. [folklore] -/
theorem wctr_apply_of_ne {k : Fin d} (hk : k ≠ i) :
    wctr Lo Hi M i y k = clamp (y k) (Lo k + M + 1) (Hi k - M - 1) := by simp [wctr, hk]

/-- Membership in the plaquette. [folklore] -/
theorem mem_plaq_iff {z : Site d} : z ∈ plaq Lo Hi M i y ↔
    z i = y i ∧ ∀ k, k ≠ i → |z k - wctr Lo Hi M i y k| ≤ M := by
  rw [plaq, mem_Icc_iff]
  constructor
  · intro hz
    refine ⟨?_, fun k hk => ?_⟩
    · have := hz i
      simp only [Function.update_self] at this; omega
    · have := hz k
      simp only [Function.update_of_ne hk, Pi.sub_apply, Pi.add_apply, Pi.natCast_apply] at this
      rw [abs_le]; omega
  · rintro ⟨hzi, hzk⟩ k
    rcases eq_or_ne k i with rfl | hk
    · simp only [Function.update_self]; omega
    · have := hzk k hk
      simp only [Function.update_of_ne hk, Pi.sub_apply, Pi.add_apply, Pi.natCast_apply]
      rw [abs_le] at this; omega

/-- Membership in the window region. [folklore] -/
theorem mem_wreg_iff {z : Site d} : z ∈ wreg Lo Hi M i y ↔
    z i = y i ∧ ∀ k, k ≠ i → |z k - wctr Lo Hi M i y k| ≤ (M : ℤ) + 1 := by
  rw [wreg, mem_Icc_iff]
  constructor
  · intro hz
    refine ⟨?_, fun k hk => ?_⟩
    · have := hz i
      simp only [Function.update_self] at this; omega
    · have := hz k
      simp only [Function.update_of_ne hk, Pi.sub_apply, Pi.add_apply, Pi.natCast_apply] at this
      push_cast at this
      rw [abs_le]; omega
  · rintro ⟨hzi, hzk⟩ k
    rcases eq_or_ne k i with rfl | hk
    · simp only [Function.update_self]; omega
    · have := hzk k hk
      simp only [Function.update_of_ne hk, Pi.sub_apply, Pi.add_apply, Pi.natCast_apply]
      push_cast
      rw [abs_le] at this; omega

/-- Membership in the cube. [folklore] -/
theorem mem_cube_iff {z : Site d} :
    z ∈ cube Lo Hi M i σ y ↔ ∀ k, |z k - vctr Lo Hi M i σ y k| ≤ M := by
  rw [cube, mem_Icc_iff]
  refine forall_congr' fun k => ?_
  simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply]
  rw [abs_le]; omega

/-- Membership in the face `U(P)`. [folklore] -/
theorem mem_uface_iff {u : Site d} :
    u ∈ uface Lo Hi M i σ y ↔ u + σ • unitVec i ∈ plaq Lo Hi M i y := by
  rw [uface, Finset.mem_image]
  constructor
  · rintro ⟨z, hz, rfl⟩; rwa [sub_add_cancel]
  · intro hu; exact ⟨u + σ • unitVec i, hu, by rw [add_sub_cancel_right]⟩

/-- Membership in the seed edge set. [folklore] -/
theorem mem_seedEdges_iff {e : Sym2 (Site d)} : e ∈ seedEdges Lo Hi M i σ y ↔
    e ∈ edgesIn (zdGraph d) (wreg Lo Hi M i y) ∨
      (∃ z ∈ plaq Lo Hi M i y, e = s(z, z - σ • unitVec i)) ∨ e = s(y + σ • unitVec i, y) := by
  simp only [seedEdges, Finset.mem_union, Finset.mem_image, Finset.mem_singleton]
  constructor
  · rintro ((h1 | ⟨z, hz, rfl⟩) | h3)
    · exact Or.inl h1
    · exact Or.inr (Or.inl ⟨z, hz, rfl⟩)
    · exact Or.inr (Or.inr h3)
  · rintro (h1 | ⟨z, hz, rfl⟩ | h3)
    · exact Or.inl (Or.inl h1)
    · exact Or.inl (Or.inr ⟨z, hz, rfl⟩)
    · exact Or.inr h3

/-- Coordinates of the cube centre. [folklore] -/
theorem vctr_apply (k : Fin d) :
    vctr Lo Hi M i σ y k = wctr Lo Hi M i y k - if k = i then σ * ((M : ℤ) + 1) else 0 := by
  simp only [vctr, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Nat.cast_add, Nat.cast_one]
  rcases eq_or_ne k i with rfl | hk
  · rw [if_pos rfl, unitVec_apply_self, mul_one]
  · rw [if_neg hk, unitVec_apply_of_ne hk, mul_zero]

/-- The `i`-th coordinate of the cube centre. [folklore] -/
theorem vctr_apply_self : vctr Lo Hi M i σ y i = y i - σ * ((M : ℤ) + 1) := by
  rw [vctr_apply, if_pos rfl, wctr_apply_self]

/-- The transverse coordinates of the cube centre. [folklore] -/
theorem vctr_apply_of_ne {k : Fin d} (hk : k ≠ i) : vctr Lo Hi M i σ y k = wctr Lo Hi M i y k := by
  rw [vctr_apply, if_neg hk, sub_zero]

/-- Standing hypotheses on the window: the box is wide, `σ` is a sign, and `y` lies on the
`(i, σ)`-face of the box. [cite: KozmaNitzan2024, §4 p. 19 (plaquettes on ∂B⟨j⟩, j ≥ 5M)] -/
structure WinHyp (Lo Hi : Site d) (M : ℕ) (i : Fin d) (σ : ℤ) (y : Site d) : Prop where
  wide : ∀ k, Lo k + 2 * M + 2 ≤ Hi k
  sign : σ = 1 ∨ σ = -1
  face : σ = 1 ∧ y i = Hi i ∨ σ = -1 ∧ y i = Lo i
  mem : ∀ k, Lo k ≤ y k ∧ y k ≤ Hi k

variable (h : WinHyp Lo Hi M i σ y)
include h

/-- In the transverse directions the window centre is at distance `≥ M + 1` from the sides.
[folklore] -/
theorem wctr_mem_of_ne {k : Fin d} (hk : k ≠ i) :
    Lo k + M + 1 ≤ wctr Lo Hi M i y k ∧ wctr Lo Hi M i y k ≤ Hi k - M - 1 := by
  rw [wctr_apply_of_ne hk]
  exact clamp_mem (by have := h.wide k; omega)

/-- The window centre is within `M + 1` of `y` in every coordinate. [folklore] -/
theorem abs_wctr_sub_le (k : Fin d) : |wctr Lo Hi M i y k - y k| ≤ (M : ℤ) + 1 := by
  rcases eq_or_ne k i with rfl | hk
  · rw [wctr_apply_self, sub_self, abs_zero]; positivity
  · rw [wctr_apply_of_ne hk]
    have h1 := h.mem k; have h2 := h.wide k
    exact abs_clamp_sub_le (by omega) (by omega) (by positivity) (by omega)

omit h in
/-- The plaquette lies in the window region. [folklore] -/
theorem plaq_subset_wreg : plaq Lo Hi M i y ⊆ wreg Lo Hi M i y := by
  intro z hz
  rw [mem_plaq_iff] at hz
  rw [mem_wreg_iff]
  exact ⟨hz.1, fun k hk => (hz.2 k hk).trans (by omega)⟩

/-- `y` lies in the window region. [folklore] -/
theorem self_mem_wreg : y ∈ wreg Lo Hi M i y := by
  rw [mem_wreg_iff]
  refine ⟨rfl, fun k _ => ?_⟩
  rw [abs_sub_comm]; exact abs_wctr_sub_le h k

/-- The window region lies in the box. [folklore] -/
theorem wreg_subset_Icc : wreg Lo Hi M i y ⊆ Finset.Icc Lo Hi := by
  intro z hz
  rw [mem_wreg_iff] at hz
  rw [mem_Icc_iff]
  intro k
  rcases eq_or_ne k i with rfl | hk
  · have := h.mem k; omega
  · have h1 := hz.2 k hk; have h2 := wctr_mem_of_ne h hk
    rw [abs_le] at h1; omega

/-- No vertex of the window region lies in the shrunken box `Icc (Lo + 1) (Hi - 1)`: the region is
in the face layer. [folklore] -/
theorem not_mem_shrink_of_mem_wreg {z : Site d} (hz : z ∈ wreg Lo Hi M i y) :
    z ∉ Finset.Icc (Lo + 1) (Hi - 1) := by
  rw [mem_wreg_iff] at hz
  rw [mem_Icc_iff]
  intro hz'
  have := hz' i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.one_apply] at this
  rcases h.face with ⟨-, hy⟩ | ⟨-, hy⟩ <;> omega

/-- **The cube lies in the shrunken box** `Icc (Lo+1) (Hi-1)` (first half of "`Q ⊆ S`").
[cite: KozmaNitzan2024, §4 p. 19 ("v + [-M,M]^d ⊆ S")] -/
theorem cube_subset_shrink : cube Lo Hi M i σ y ⊆ Finset.Icc (Lo + 1) (Hi - 1) := by
  intro z hz
  rw [mem_cube_iff] at hz
  rw [mem_Icc_iff]
  intro k
  have hzk := hz k
  rw [abs_le] at hzk
  simp only [Pi.add_apply, Pi.sub_apply, Pi.one_apply]
  rcases eq_or_ne k i with rfl | hk
  · rw [vctr_apply_self] at hzk
    have hw := h.wide k
    rcases h.face with ⟨hs, hy⟩ | ⟨hs, hy⟩
    · rw [hs] at hzk; omega
    · rw [hs] at hzk; omega
  · rw [vctr_apply_of_ne hk] at hzk
    have := wctr_mem_of_ne h hk
    omega

/-- Second half of "`Q ⊆ S`": the cube avoids the doubly shrunken box
`Icc (Lo + (2M+2)) (Hi - (2M+2))`. [cite: KozmaNitzan2024, §4 p. 19 ("v + [-M,M]^d ⊆ S")] -/
theorem not_mem_shrink2_of_mem_cube {z : Site d} (hz : z ∈ cube Lo Hi M i σ y) :
    z ∉ Finset.Icc (Lo + ((2 * M + 2 : ℕ) : Site d)) (Hi - ((2 * M + 2 : ℕ) : Site d)) := by
  rw [mem_cube_iff] at hz
  rw [mem_Icc_iff]
  intro hz'
  have hzi := hz i
  have hz'i := hz' i
  rw [vctr_apply_self, abs_le] at hzi
  simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply] at hz'i
  push_cast at hz'i
  rcases h.face with ⟨hs, hy⟩ | ⟨hs, hy⟩
  · rw [hs] at hzi; omega
  · rw [hs] at hzi; omega

/-- The cube centre lies in the shrunken box. [folklore] -/
theorem vctr_mem_shrink : vctr Lo Hi M i σ y ∈ Finset.Icc (Lo + 1) (Hi - 1) := by
  apply cube_subset_shrink h
  rw [mem_cube_iff]
  intro k; simp

/-- **The face is the outward `i`-face of the cube**: `U(P) = {z ∈ Q : z_i = v_i + σ M}`.
[cite: KozmaNitzan2024, §4 p. 21 (U(P) ∈ U(v(P)))] -/
theorem mem_uface_iff_cube {u : Site d} :
    u ∈ uface Lo Hi M i σ y ↔ u ∈ cube Lo Hi M i σ y ∧ u i = vctr Lo Hi M i σ y i + σ * M := by
  rw [mem_uface_iff, mem_plaq_iff, mem_cube_iff]
  have hui : (u + σ • unitVec i) i = u i + σ := by rw [add_smul_unitVec_apply, if_pos rfl]
  have huk : ∀ k, k ≠ i → (u + σ • unitVec i) k = u k := fun k hk => by
    rw [add_smul_unitVec_apply, if_neg hk, add_zero]
  rw [hui]
  constructor
  · rintro ⟨hi1, hk1⟩
    refine ⟨fun k => ?_, ?_⟩
    · rcases eq_or_ne k i with rfl | hk
      · rw [vctr_apply_self, abs_le]
        rcases h.sign with hs | hs <;> rw [hs] at hi1 ⊢ <;> constructor <;> nlinarith
      · rw [vctr_apply_of_ne hk, ← huk k hk]; exact hk1 k hk
    · rw [vctr_apply_self]
      rcases h.sign with hs | hs <;> rw [hs] at hi1 ⊢ <;> linarith
  · rintro ⟨hk1, hi1⟩
    rw [vctr_apply_self] at hi1
    refine ⟨?_, fun k hk => ?_⟩
    · rcases h.sign with hs | hs <;> rw [hs] at hi1 ⊢ <;> linarith
    · rw [huk k hk, ← vctr_apply_of_ne (Lo := Lo) (Hi := Hi) (M := M) (σ := σ) (y := y) hk]
      exact hk1 k

/-- The face lies in the cube. [folklore] -/
theorem uface_subset_cube : uface Lo Hi M i σ y ⊆ cube Lo Hi M i σ y := fun _ hu =>
  ((mem_uface_iff_cube h).1 hu).1

/-- The face lies in the shrunken box. [folklore] -/
theorem uface_subset_shrink : uface Lo Hi M i σ y ⊆ Finset.Icc (Lo + 1) (Hi - 1) :=
  (uface_subset_cube h).trans (cube_subset_shrink h)

/-! ### Seed edges: what they are made of -/

/-- **Seed edges are lattice edges.** [folklore] -/
theorem seedEdges_subset_edgeSet :
    (↑(seedEdges Lo Hi M i σ y) : Set (Sym2 (Site d))) ⊆ (zdGraph d).edgeSet := by
  intro e he
  rcases mem_seedEdges_iff.1 he with h1 | ⟨z, -, rfl⟩ | rfl
  · exact (mem_edgesIn_iff.1 h1).1
  · rw [SimpleGraph.mem_edgeSet]
    refine adj_iff_exists_sign.2 ⟨i, -σ, ?_, ?_⟩
    · rcases h.sign with hs | hs <;> simp [hs]
    · rw [neg_smul, sub_eq_add_neg]
  · rw [SimpleGraph.mem_edgeSet]
    exact (adj_iff_exists_sign.2 ⟨i, σ, h.sign, rfl⟩).symm

/-- **Every seed edge has an endpoint in the box `Icc Lo Hi`** (so seed events are independent of
everything determined by the pairs outside the box).
[cite: KozmaNitzan2024, §4 p. 19 ("also after conditioning on C(o; G \ B⟨j⟩)")] -/
theorem exists_mem_Icc_of_mem_seedEdges {e : Sym2 (Site d)} (he : e ∈ seedEdges Lo Hi M i σ y) :
    ∃ z ∈ e, z ∈ Finset.Icc Lo Hi := by
  rcases mem_seedEdges_iff.1 he with h1 | ⟨z, hz, rfl⟩ | rfl
  · rw [mem_edgesIn_iff] at h1
    induction e using Sym2.ind with
    | h a b => exact ⟨a, Sym2.mem_mk_left a b, wreg_subset_Icc h (h1.2 a (Sym2.mem_mk_left a b))⟩
  · exact ⟨z, Sym2.mem_mk_left _ _, wreg_subset_Icc h (plaq_subset_wreg hz)⟩
  · exact ⟨y, Sym2.mem_mk_right _ _, wreg_subset_Icc h (self_mem_wreg h)⟩

/-- **No seed edge has both endpoints in the shrunken box** `Icc (Lo+1) (Hi-1)` (so seed events
are not affected by conditioning on the shell).
[cite: KozmaNitzan2024, §4 p. 21 ("P_{K_ξ}(F_P) = P_G(F_P)")] -/
theorem exists_not_mem_shrink_of_mem_seedEdges {e : Sym2 (Site d)}
    (he : e ∈ seedEdges Lo Hi M i σ y) : ∃ z ∈ e, z ∉ Finset.Icc (Lo + 1) (Hi - 1) := by
  rcases mem_seedEdges_iff.1 he with h1 | ⟨z, hz, rfl⟩ | rfl
  · rw [mem_edgesIn_iff] at h1
    induction e using Sym2.ind with
    | h a b => exact ⟨a, Sym2.mem_mk_left a b,
        not_mem_shrink_of_mem_wreg h (h1.2 a (Sym2.mem_mk_left a b))⟩
  · exact ⟨z, Sym2.mem_mk_left _ _, not_mem_shrink_of_mem_wreg h (plaq_subset_wreg hz)⟩
  · exact ⟨y, Sym2.mem_mk_right _ _, not_mem_shrink_of_mem_wreg h (self_mem_wreg h)⟩

/-- A vertex of the window region is within `2M + 3` of the outer contact vertex `y + σ e_i`, in
every coordinate. [folklore] -/
theorem abs_sub_contact_le_of_mem_wreg {w : Site d} (hw : w ∈ wreg Lo Hi M i y) (k : Fin d) :
    |w k - (y + σ • unitVec i) k| ≤ 2 * M + 3 := by
  rw [mem_wreg_iff] at hw
  rw [add_smul_unitVec_apply]
  rcases eq_or_ne k i with rfl | hk
  · rw [if_pos rfl, hw.1, abs_le]
    rcases h.sign with hs | hs <;> rw [hs] <;> omega
  · rw [if_neg hk, add_zero]
    have h1 := hw.2 k hk; have h2 := abs_wctr_sub_le h k
    rw [abs_le] at h1 h2 ⊢; omega

/-- **Locality of the seed edges**: both endpoints of every seed edge are within sup-distance
`2M + 4` of the outer contact vertex `x = y + σ e_i`. [folklore] -/
theorem sub_mem_box_of_mem_seedEdges {e : Sym2 (Site d)} (he : e ∈ seedEdges Lo Hi M i σ y)
    {z : Site d} (hz : z ∈ e) : z - (y + σ • unitVec i) ∈ box d (2 * M + 4) := by
  rw [mem_box]
  intro k
  simp only [Pi.sub_apply]
  push_cast
  rcases mem_seedEdges_iff.1 he with h1 | ⟨w, hw, rfl⟩ | rfl
  · have := abs_sub_contact_le_of_mem_wreg h ((mem_edgesIn_iff.1 h1).2 z hz) k
    rw [abs_le] at this; omega
  · have hw' := abs_sub_contact_le_of_mem_wreg h (plaq_subset_wreg hw) k
    rw [abs_le] at hw'
    rcases Sym2.mem_iff.1 hz with rfl | rfl
    · omega
    · have e1 : (w - σ • unitVec i) k = w k - if k = i then σ else 0 := by
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        rcases eq_or_ne k i with rfl | hk
        · rw [if_pos rfl, unitVec_apply_self, mul_one]
        · rw [if_neg hk, unitVec_apply_of_ne hk, mul_zero]
      rw [e1]
      rcases eq_or_ne k i with rfl | hk
      · rw [if_pos rfl]; rcases h.sign with hs | hs <;> rw [hs] at hw' ⊢ <;> omega
      · rw [if_neg hk]; omega
  · have hy' := abs_sub_contact_le_of_mem_wreg h (self_mem_wreg h) k
    rw [abs_le] at hy'
    rcases Sym2.mem_iff.1 hz with rfl | rfl
    · rw [sub_self]; omega
    · omega

end Window

/-- **Far-apart contacts have disjoint seed edge sets**: if the outer contact vertices
`x = y + σ e_i`, `x' = y' + σ' e_{i'}` satisfy `x' - x ∉ Λ_{2(2M+4)}` then the seed edge sets are
disjoint. [cite: KozmaNitzan2024, §4 p. 19 ("for any two plaquettes the events that they are seeds are independent")] -/
theorem seedEdges_disjoint {Lo Hi : Site d} {M : ℕ} {i i' : Fin d} {σ σ' : ℤ} {y y' : Site d}
    (h : WinHyp Lo Hi M i σ y) (h' : WinHyp Lo Hi M i' σ' y')
    (hfar : (y' + σ' • unitVec i') - (y + σ • unitVec i) ∉ box d (2 * (2 * M + 4))) :
    Disjoint (seedEdges Lo Hi M i σ y) (seedEdges Lo Hi M i' σ' y') := by
  rw [Finset.disjoint_left]
  intro e he he'
  induction e using Sym2.ind with
  | h a b =>
    have ha := sub_mem_box_of_mem_seedEdges h he (Sym2.mem_mk_left a b)
    have ha' := sub_mem_box_of_mem_seedEdges h' he' (Sym2.mem_mk_left a b)
    apply hfar
    rw [mem_box] at ha ha' ⊢
    intro k
    have h1 := ha k; have h2 := ha' k
    simp only [Pi.sub_apply] at h1 h2 ⊢
    push_cast at h1 h2 ⊢
    omega

/-! ## Open seed edges connect the contact vertex to the whole face -/

/-- A lattice path inside `Λ` is an open path as soon as all lattice edges inside `Λ` are open.
[folklore] -/
theorem pathIn_openGraph_of_edgesIn_subset {Λ : Finset (Site d)} {ω : BondConfig (Site d)}
    (hω : ↑(edgesIn (zdGraph d) Λ) ⊆ ω) {a b : Site d}
    (hp : PathIn (zdGraph d) (↑Λ : Set (Site d)) a b) : PathIn (openGraph ω) (↑Λ : Set (Site d)) a b := by
  obtain ⟨ha, hp⟩ := hp
  refine ⟨ha, ?_⟩
  induction hp with
  | refl => exact Relation.ReflTransGen.refl
  | @tail u v huv hv ih =>
    have hu : u ∈ (↑Λ : Set (Site d)) := (show PathIn (zdGraph d) ↑Λ a u from ⟨ha, huv⟩).right_mem
    refine ih.tail ⟨?_, hv.2⟩
    rw [openGraph_adj]
    refine ⟨hω (Finset.mem_coe.2 (mem_edgesIn_iff.2 ⟨hv.1, ?_⟩)), hv.1.ne⟩
    intro z hz
    rcases Sym2.mem_iff.1 hz with rfl | rfl
    · exact Finset.mem_coe.1 hu
    · exact Finset.mem_coe.1 hv.2

/-- **A seed joins its contact vertex to every vertex of its face**: if all seed edges of `y` are
open then `x = y + σ e_i` is joined by an open path to every `u ∈ U(P)` (through `y`, the window
region and the inward edge at `u + σ e_i`).
[cite: KozmaNitzan2024, §4 p. 21 ("P connects to w (as the event that P is a seed implies that all edges from P to U(P) are open)")] -/
theorem openConn_of_seedEdges_subset {Lo Hi : Site d} {M : ℕ} {i : Fin d} {σ : ℤ} {y : Site d}
    (h : WinHyp Lo Hi M i σ y) {ω : BondConfig (Site d)} (hω : ↑(seedEdges Lo Hi M i σ y) ⊆ ω)
    {u : Site d} (hu : u ∈ uface Lo Hi M i σ y) : ω ∈ openConn (y + σ • unitVec i) u := by
  have hsub : ↑(edgesIn (zdGraph d) (wreg Lo Hi M i y)) ⊆ ω := fun e he =>
    hω (Finset.mem_coe.2 (mem_seedEdges_iff.2 (Or.inl (Finset.mem_coe.1 he))))
  have hz : u + σ • unitVec i ∈ plaq Lo Hi M i y := (mem_uface_iff).1 hu
  -- `x ∼ y`
  have h1 : (openGraph ω).Adj (y + σ • unitVec i) y := by
    rw [openGraph_adj]
    refine ⟨hω (Finset.mem_coe.2 (mem_seedEdges_iff.2 (Or.inr (Or.inr rfl)))), ?_⟩
    exact ((adj_iff_exists_sign.2 ⟨i, σ, h.sign, rfl⟩ : (zdGraph d).Adj y _).symm).ne
  -- `y ↝ u + σ e_i` inside the window region
  have h2 : (openGraph ω).Reachable y (u + σ • unitVec i) := by
    refine reachable_of_pathIn' (pathIn_openGraph_of_edgesIn_subset hsub ?_)
    exact exists_pathIn_Icc (self_mem_wreg h) (plaq_subset_wreg hz)
  -- the inward edge
  have h3 : (openGraph ω).Adj (u + σ • unitVec i) u := by
    rw [openGraph_adj]
    constructor
    · have : s(u + σ • unitVec i, u + σ • unitVec i - σ • unitVec i) ∈ seedEdges Lo Hi M i σ y :=
        mem_seedEdges_iff.2 (Or.inr (Or.inl ⟨_, hz, rfl⟩))
      rw [add_sub_cancel_right] at this
      exact hω (Finset.mem_coe.2 this)
    · intro heq
      have := congrFun heq i
      rw [add_smul_unitVec_apply, if_pos rfl] at this
      rcases h.sign with hs | hs <;> rw [hs] at this <;> omega
  exact h1.reachable.trans (h2.trans h3.reachable)
where
  /-- reachability from a `PathIn` of the open graph -/
  reachable_of_pathIn' {ω : BondConfig (Site d)} {A : Set (Site d)} {a b : Site d}
      (hp : PathIn (openGraph ω) A a b) : (openGraph ω).Reachable a b := by
    obtain ⟨-, hp⟩ := hp
    induction hp with
    | refl => exact SimpleGraph.Reachable.refl _
    | tail _ hbc ih => exact ih.trans hbc.1.reachable

/-! ## A crude bound on the number of seed edges -/

/-- The number of lattice edges inside a finite set is at most `2d` times its size. [folklore] -/
theorem card_edgesIn_le (Λ : Finset (Site d)) : (edgesIn (zdGraph d) Λ).card ≤ 2 * d * Λ.card := by
  calc (edgesIn (zdGraph d) Λ).card ≤ (edgesTouching (zdGraph d) Λ).card :=
        Finset.card_le_card (edgesIn_subset_edgesTouching Λ)
    _ ≤ ∑ x ∈ Λ, ((zdGraph d).incidenceFinset x).card := Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ Λ, 2 * d := Finset.sum_le_sum fun x _ => by
        rw [SimpleGraph.card_incidenceFinset_eq_degree]; exact card_neighborFinset_zdGraph_le x
    _ = 2 * d * Λ.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- A box `Icc lo hi` all of whose sides have at most `n` points has at most `n^d` points.
[folklore] -/
theorem card_Icc_le_pow {lo hi : Site d} {n : ℕ} (hn : ∀ k, hi k + 1 - lo k ≤ n) :
    (Finset.Icc lo hi).card ≤ n ^ d := by
  rw [Pi.card_Icc]
  calc ∏ k, (Finset.Icc (lo k) (hi k)).card ≤ ∏ _k : Fin d, n :=
        Finset.prod_le_prod' fun k _ => by rw [Int.card_Icc]; have := hn k; omega
    _ = n ^ d := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- An explicit bound for the number of seed edges, depending only on `d` and `M`.
[cite: KozmaNitzan2024, §4 p. 19 ("at least p^{(d+1)(4M)^{d-1}}")] -/
def seedBound (d M : ℕ) : ℕ := (2 * d + 1) * (2 * M + 3) ^ d + 1

/-- **The seed edge set has at most `seedBound d M` elements.** [cite: KozmaNitzan2024, §4 p. 19] -/
theorem card_seedEdges_le {Lo Hi : Site d} {M : ℕ} {i : Fin d} {σ : ℤ} {y : Site d} :
    (seedEdges Lo Hi M i σ y).card ≤ seedBound d M := by
  have hw : (wreg Lo Hi M i y).card ≤ (2 * M + 3) ^ d := by
    refine card_Icc_le_pow fun k => ?_
    rcases eq_or_ne k i with rfl | hk
    · simp only [Function.update_self]; omega
    · simp only [Function.update_of_ne hk, Pi.add_apply, Pi.sub_apply, Pi.natCast_apply]
      push_cast; omega
  have hp : (plaq Lo Hi M i y).card ≤ (2 * M + 3) ^ d :=
    (Finset.card_le_card plaq_subset_wreg).trans hw
  unfold seedEdges seedBound
  calc _ ≤ (edgesIn (zdGraph d) (wreg Lo Hi M i y) ∪
          ((plaq Lo Hi M i y).image fun z => s(z, z - σ • unitVec i))).card + 1 := by
        refine (Finset.card_union_le _ _).trans ?_
        rw [Finset.card_singleton]
    _ ≤ (edgesIn (zdGraph d) (wreg Lo Hi M i y)).card +
          ((plaq Lo Hi M i y).image fun z => s(z, z - σ • unitVec i)).card + 1 := by
        have := Finset.card_union_le (edgesIn (zdGraph d) (wreg Lo Hi M i y))
          ((plaq Lo Hi M i y).image fun z => s(z, z - σ • unitVec i))
        omega
    _ ≤ 2 * d * (2 * M + 3) ^ d + (2 * M + 3) ^ d + 1 := by
        have h1 := (card_edgesIn_le (wreg Lo Hi M i y)).trans (Nat.mul_le_mul_left _ hw)
        have h2 : ((plaq Lo Hi M i y).image fun z => s(z, z - σ • unitVec i)).card ≤ (2 * M + 3) ^ d :=
          Finset.card_image_le.trans hp
        omega
    _ = (2 * d + 1) * (2 * M + 3) ^ d + 1 := by ring

/-! ## From an outer-boundary contact vertex to its window -/

/-- **Every outer-boundary vertex of a wide box has a window**: `x = y + σ e_i` with
`WinHyp Lo Hi M i σ y`. [cite: KozmaNitzan2024, §4 pp. 19–21] -/
theorem exists_winHyp_of_mem_outerBoundary {Lo Hi : Site d} {M : ℕ}
    (hwide : ∀ k, Lo k + 2 * M + 2 ≤ Hi k) {x : Site d}
    (hx : x ∈ outerBoundary (zdGraph d) (Finset.Icc Lo Hi)) :
    ∃ (i : Fin d) (σ : ℤ) (y : Site d), WinHyp Lo Hi M i σ y ∧ x = y + σ • unitVec i := by
  obtain ⟨⟨i, σ⟩, hσ, hxi, hxk⟩ := exists_dir_of_mem_outerBoundary hx
  simp only at hσ hxi hxk
  refine ⟨i, σ, x - σ • unitVec i, ⟨hwide, hσ, ?_, fun k => ?_⟩, by rw [sub_add_cancel]⟩
  · have e1 : (x - σ • unitVec i) i = x i - σ := by
      simp [Pi.sub_apply, unitVec]
    rw [e1]
    rcases hxi with ⟨hs, hx1⟩ | ⟨hs, hx1⟩
    · left; exact ⟨hs, by rw [hx1, hs]; ring⟩
    · right; exact ⟨hs, by rw [hx1, hs]; ring⟩
  · rcases eq_or_ne k i with rfl | hk
    · have e1 : (x - σ • unitVec k) k = x k - σ := by simp [Pi.sub_apply, unitVec]
      rw [e1]
      have hw := hwide k
      rcases hxi with ⟨hs, hx1⟩ | ⟨hs, hx1⟩ <;> rw [hx1, hs] <;> constructor <;> omega
    · have e1 : (x - σ • unitVec i) k = x k := by simp [Pi.sub_apply, unitVec, hk]
      rw [e1]; exact hxk k hk

/-- Membership in the cube as a translate of `Λ_M`. [folklore] -/
theorem mem_cube_iff_sub_mem_box {Lo Hi : Site d} {M : ℕ} {i : Fin d} {σ : ℤ} {y z : Site d} :
    z ∈ cube Lo Hi M i σ y ↔ z - vctr Lo Hi M i σ y ∈ box d M := by
  rw [mem_cube_iff, mem_box]
  refine forall_congr' fun k => ?_
  rw [Pi.sub_apply, abs_le]

/-- Arithmetic of enlargements: shrinking `B⟨j⟩` by `t ≤ j` gives `B⟨j - t⟩` (lower corner).
[cite: KozmaNitzan2024, §4 p. 15 (B⟨R⟩)] -/
theorem enlarge_lo_add {lo : Site d} {j t : ℕ} (h : t ≤ j) :
    lo - ((j : ℕ) : Site d) + ((t : ℕ) : Site d) = lo - (((j - t : ℕ)) : Site d) := by
  funext k
  simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply]
  push_cast [h]
  ring

/-- Arithmetic of enlargements: shrinking `B⟨j⟩` by `t ≤ j` gives `B⟨j - t⟩` (upper corner).
[cite: KozmaNitzan2024, §4 p. 15 (B⟨R⟩)] -/
theorem enlarge_hi_sub {hi : Site d} {j t : ℕ} (h : t ≤ j) :
    hi + ((j : ℕ) : Site d) - ((t : ℕ) : Site d) = hi + (((j - t : ℕ)) : Site d) := by
  funext k
  simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply]
  push_cast [h]
  ring

end KozmaNitzan

end Percolation.Literature

end
