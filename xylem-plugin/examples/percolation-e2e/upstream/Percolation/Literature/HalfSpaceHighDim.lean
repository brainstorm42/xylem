import Percolation.Literature.HalfSpaceBGN
import Percolation.Literature.HarrisTheorem
import Percolation.Literature.KestenTheoremProofs
import Percolation.Util.Linter

/-!
# The Barsky–Grimmett–Newman theorem `θ_ℍ(p_c) = 0` in every dimension `d ≥ 2`: the block vocabulary of `ℤ^d`, the two lemmas as statements, the assembly and `d = 2` proved

Towards the statement `Percolation.Literature.BarskyGrimmettNewman1991` of
`HalfSpace.lean` — Grimmett, *Percolation*, 2nd ed. (1999), Thm. (7.35), p. 163: "Let `d ≥ 2`. We
have that `θ_ℍ(p_c) = 0`" (`p_c = p_c(ℤ^d)`, §7.2 p. 148) — along its printed proof, §7.3 pp.
163–174, which Grimmett gives "under the assumption that `d = 3`; the proof is simpler when `d = 2`,
and a similar argument is valid when `d > 3`" (p. 163), following Barsky–Grimmett–Newman (1991),
whose §2 is written in `ℤ^d` directly. The sibling file `HalfSpaceBGN.lean` (and its sequels, …)
carries out the case `d = 3` over `Site 3`; this file sets up the same architecture uniformly in the
dimension:

* proved, the case `d = 2` outright (`BarskyGrimmettNewman1991_dim_two`): `θ_ℍ ≤ θ_{ℤ²}`
  (restriction coupling, `theta_induce_le_holds`) and `θ_{ℤ²}(p_c) = 0` (Harris–Kesten:
  `percolationContinuity_two` with `kesten_criticalProb_Z2_holds`, `harris_theta_half_holds`), as
  in Grimmett's notes to §7.3, p. 196: "In the case `d = 2`, earlier results of Harris (1960) and
  Kesten (1980a) imply that `θ_ℍ(p_c) = 0`";

## Coordinates

As in `HalfSpace.lean` / `HalfSpaceBGN.lean`: `ℍ = {x ∈ ℤ^d | 0 ≤ x 0}`, the vertical axis is
the coordinate `0 : Fin d` (Grimmett and BGN use the last coordinate), the horizontal axes are
the `j ≠ 0` (`BGNd.HAxis d`). So `B(L,H) = {x | 0 ≤ x 0 ≤ H, |x j| ≤ L (j ≠ 0)}`, Grimmett's
horizontal square `b_d(m)` is `square 0 m`, and the subfacets of BGN 1991 p. 118,
`T_1 = [0,L]^{d-1} × {H}, …, T_{2^{d-1}} = [-L,0]^{d-1} × {H}` and
`S_1 = {L} × [0,L]^{d-2} × [0,H], …, S_{(d-1)2^{d-1}} = [-L,0]^{d-2} × {-L} × [0,H]`, are
indexed by sign vectors `ρ : HAxis d → Bool` (top) and by pairs `(a, τ)` of a horizontal axis
`a` (the facet `x a = ±L`, sign `τ a`) and a sign vector `τ` (the halves `[0,L]` / `[-L,0]` of
the remaining horizontal coordinates).

## Design choices

* The lemma facts quantify over `d ≥ 3` (Grimmett: `d = 3` and "a similar argument is valid
  when `d > 3`"; BGN 1991 work in `ℤ^d` throughout; the definitions make sense for `d = 2` too,
  where the case is settled here by Harris–Kesten instead) and, for (7.36), over every `p` with
  `θ_ℍ(p) > 0` (Grimmett p. 164: "It is valid for general `p` but we shall require it for
  `p = p_c` only"; BGN 1991 Prop. 2.1 is stated and proved at general `p`, which is what makes
  it independent of the input "`p_c(S_h) > p_c`" of the `p = p_c` proof, (7.38)); `ν` in (7.52)
  may depend on `d`. The per-dimension assembly theorems take the two lemmas at a fixed `d` as
  hypotheses, so they serve `d = 2, 3` as well.

## References

* G. Grimmett, *Percolation*, 2nd ed., Grundlehren 321, Springer 1999, §7.3: Thm. (7.35)
  p. 163, the bricks pp. 163–164, Lemma (7.36) p. 164, Lemma (7.52) p. 169, assembly p. 169,
  notes p. 196 (`d = 2`).
* D. J. Barsky, G. R. Grimmett, C. M. Newman, *Percolation in half-spaces: equality of critical
  densities and continuity of the percolation probability*, Probab. Theory Related Fields 90
  (1991) 111–148: Thm. 1.1 (i) p. 114, Thm. 1.2 (i) p. 116, §2 (bricks in `ℤ^d`, occupied bricks
  p. 119, Prop. 2.1 p. 120) pp. 118–128, §3 (stacking, (i) p. 129: "the event `E₁`, that `B` is an
  occupied brick with attachment site `y_j = y`, is independent of the event `E₂`, that `y + B` is
  an occupied brick") pp. 128–145, §4 (proof of Thm. 1.2 (i), `R = 125` bricks per crossing,
  `1 - ε > λ_c(ℤ²₊)`) pp. 145–147.
-/

noncomputable section

namespace Percolation.Literature

open MeasureTheory ProbabilityTheory LatticeModels
open scoped ENNReal

/-! ## The block construction in `ℤ^d` (Grimmett 1999, pp. 163–164; BGN 1991, §2) -/

namespace BGNd

variable {d : ℕ}

/-- The horizontal axes of `ℤ^d`: the coordinates other than the vertical one `0`.
[cite: BarskyGrimmettNewman1991, §2 p. 118] -/
abbrev HAxis (d : ℕ) [NeZero d] : Type := {j : Fin d // j ≠ 0}

/-- The brick `B(L,H) = [-L,L]^{d-1} × [0,H]` (Grimmett 1999, p. 163; BGN 1991, p. 118,
`B_North(L,H)`), in the coordinates of this file `{x ∈ ℤ^d | 0 ≤ x 0 ≤ H, |x j| ≤ L (j ≠ 0)}`.
[cite: GrimmettPercolation1999, §7.3 p. 163 (B(L,H))] -/
def brick (d L H : ℕ) [NeZero d] : Set (Site d) :=
  {x | (0 ≤ x 0 ∧ x 0 ≤ H) ∧ ∀ j : Fin d, j ≠ 0 → |x j| ≤ L}

/-- The underside `U(L,H) = [-L,L]^{d-1} × {0}` of the brick (BGN's bottom `D`).
[cite: GrimmettPercolation1999, §7.3 p. 163 (U)] -/
def underside (d L H : ℕ) [NeZero d] : Set (Site d) := {x | x ∈ brick d L H ∧ x 0 = 0}

/-- The top `T(L,H) = [-L,L]^{d-1} × {H}` of the brick. [cite: GrimmettPercolation1999, §7.3 p. 163 (T)] -/
def top (d L H : ℕ) [NeZero d] : Set (Site d) := {x | x ∈ brick d L H ∧ x 0 = H}

/-- The sides `S(L,H) = {x ∈ B(L,H) : |x_j| = L for some horizontal j}` of the brick.
[cite: GrimmettPercolation1999, §7.3 p. 163 (S)] -/
def sides (d L H : ℕ) [NeZero d] : Set (Site d) :=
  {x | x ∈ brick d L H ∧ ∃ j : Fin d, j ≠ 0 ∧ |x j| = L}

/-- The half `[0,L]` (`b = true`) or `[-L,0]` (`b = false`) of the range of a horizontal
coordinate, cutting facets into subfacets. [cite: BarskyGrimmettNewman1991, §2 p. 118] -/
def HalfRange (L : ℕ) (b : Bool) (t : ℤ) : Prop :=
  if b then 0 ≤ t ∧ t ≤ L else -(L : ℤ) ≤ t ∧ t ≤ 0

/-- The `2^{d-1}` congruent subfacets of the top, `T_1 = [0,L]^{d-1} × {H}`, …,
`T_{2^{d-1}} = [-L,0]^{d-1} × {H}` (BGN 1991, p. 118; Grimmett's `T_1,…,T_4` for `d = 3`),
indexed by the sign vector `ρ` of the horizontal coordinates.
[cite: BarskyGrimmettNewman1991, §2 p. 118 (T_j)] -/
def topSubfacet (d L H : ℕ) [NeZero d] (ρ : HAxis d → Bool) : Set (Site d) :=
  {x | x 0 = H ∧ ∀ j : HAxis d, HalfRange L (ρ j) (x j.1)}

/-- The `(d-1)2^{d-1}` subfacets of the sides, each congruent to `{L} × [0,L]^{d-2} × [0,H]`:
`S_{a,τ}` lies in the facet `{x a = L}` (`τ a = true`) or `{x a = -L}` (`τ a = false`) of the
horizontal axis `a`, cut along the signs `τ j` of the other horizontal coordinates (BGN 1991,
p. 118, `S_1 = {L} × [0,L]^{d-2} × [0,H], …`; Grimmett's `S_1,…,S_8` for `d = 3`).
[cite: BarskyGrimmettNewman1991, §2 p. 118 (S_i)] -/
def sideSubfacet (d L H : ℕ) [NeZero d] (a : HAxis d) (τ : HAxis d → Bool) : Set (Site d) :=
  {x | (0 ≤ x 0 ∧ x 0 ≤ H) ∧ x a.1 = (if τ a then (L : ℤ) else -(L : ℤ)) ∧
    ∀ j : HAxis d, j ≠ a → HalfRange L (τ j) (x j.1)}

/-- The square `c + b_k(m)` (BGN: hyperblock): the `(d-1)`-dimensional region of radius `m`
centred at `c` and orthogonal to the axis `k` (`b_k(m) = [-m,m]^{k-1} × {0} × [-m,m]^{d-k}`,
Grimmett p. 163, BGN p. 119; Grimmett's last axis is our axis `0`).
[cite: GrimmettPercolation1999, §7.3 p. 163 (b_k(m))] -/
def square (k : Fin d) (m : ℕ) (c : Site d) : Set (Site d) :=
  {y | y k = c k ∧ ∀ j, j ≠ k → |y j - c j| ≤ m}

/-- A square is a *seed* (in the configuration `ω`) if all edges of `ℤ^d` joining pairs of its
vertices are open. [cite: GrimmettPercolation1999, §7.3 p. 163 (seed)] -/
def IsSeed (ω : BondConfig (Site d)) (Q : Set (Site d)) : Prop :=
  ∀ ⦃u⦄, u ∈ Q → ∀ ⦃v⦄, v ∈ Q → (zdGraph d).Adj u v → s(u, v) ∈ ω

/-- The axis of the square `b(x)` associated with `x ∈ S ∪ T` (Grimmett pp. 163–164; BGN
p. 119): horizontal (axis `0`) for `x ∈ T`; for `x ∈ S \ T`, parallel to a facet containing
`x` — our "predetermined rule" takes the least horizontal axis `a` with `|x a| = L` (and the
junk value `0` off `S ∪ T`). [cite: GrimmettPercolation1999, §7.3 pp. 163–164 (b(x))] -/
def seedAxis (d L H : ℕ) [NeZero d] (x : Site d) : Fin d :=
  if x 0 = H then 0 else
    if h : (Finset.univ.filter fun j : Fin d => j ≠ 0 ∧ |x j| = L).Nonempty then
      (Finset.univ.filter fun j : Fin d => j ≠ 0 ∧ |x j| = L).min' h
    else 0

/-- The central square `b(0) = b_d(m)`, the horizontal square of radius `m` centred at the
origin (it lies in the underside hyperplane). [cite: GrimmettPercolation1999, §7.3 p. 164 (b(0))] -/
def centralSquare (d m : ℕ) [NeZero d] : Set (Site d) := square (0 : Fin d) m 0

/-! ### API -/

/-- Membership in the brick. [folklore] -/
@[simp] theorem mem_brick [NeZero d] {L H : ℕ} {x : Site d} :
    x ∈ brick d L H ↔ (0 ≤ x 0 ∧ x 0 ≤ H) ∧ ∀ j : Fin d, j ≠ 0 → |x j| ≤ L := Iff.rfl

/-- Membership in a square. [folklore] -/
@[simp] theorem mem_square {k : Fin d} {m : ℕ} {c y : Site d} :
    y ∈ square k m c ↔ y k = c k ∧ ∀ j, j ≠ k → |y j - c j| ≤ m := Iff.rfl

/-- Unfolding `HalfRange`: either half lies in `[-L, L]`. [folklore] -/
theorem abs_le_of_halfRange {L : ℕ} {b : Bool} {t : ℤ} (h : HalfRange L b t) : |t| ≤ L := by
  unfold HalfRange at h
  split_ifs at h <;> exact abs_le.mpr ⟨by omega, by omega⟩

/-- The centre lies in its square. [folklore] -/
theorem self_mem_square (k : Fin d) (m : ℕ) (c : Site d) : c ∈ square k m c := by
  simp [square]

/-- The side subfacets lie in the brick. [folklore] -/
theorem sideSubfacet_subset_brick [NeZero d] (L H : ℕ) (a : HAxis d) (τ : HAxis d → Bool) :
    sideSubfacet d L H a τ ⊆ brick d L H := by
  rintro x ⟨h0, ha, hrest⟩
  refine ⟨h0, fun j hj => ?_⟩
  by_cases hja : (⟨j, hj⟩ : HAxis d) = a
  · have : x j = if τ a then (L : ℤ) else -(L : ℤ) := by rw [← ha, ← hja]
    rw [this]
    split_ifs <;> simp
  · exact abs_le_of_halfRange (hrest ⟨j, hj⟩ hja)

/-- The top subfacets lie in the brick. [folklore] -/
theorem topSubfacet_subset_brick [NeZero d] (L H : ℕ) (ρ : HAxis d → Bool) :
    topSubfacet d L H ρ ⊆ brick d L H := by
  rintro x ⟨h0, hrest⟩
  refine ⟨⟨by rw [h0]; positivity, by rw [h0]⟩, fun j hj => ?_⟩
  exact abs_le_of_halfRange (hrest ⟨j, hj⟩)

/-- The side subfacets lie in the sides. [folklore] -/
theorem sideSubfacet_subset_sides [NeZero d] (L H : ℕ) (a : HAxis d) (τ : HAxis d → Bool) :
    sideSubfacet d L H a τ ⊆ sides d L H := by
  intro x hx
  refine ⟨sideSubfacet_subset_brick L H a τ hx, a.1, a.2, ?_⟩
  rw [hx.2.1]
  split_ifs <;> simp

/-- The top subfacets lie in the top. [folklore] -/
theorem topSubfacet_subset_top [NeZero d] (L H : ℕ) (ρ : HAxis d → Bool) :
    topSubfacet d L H ρ ⊆ top d L H :=
  fun _ hx => ⟨topSubfacet_subset_brick L H ρ hx, hx.1⟩

/-! ### `{B(L,H) is good}` depends on finitely many edges -/

/-- The brick lies in the box of radius `L + H + m`. [folklore] -/
theorem brick_subset_box [NeZero d] (m L H : ℕ) : brick d L H ⊆ ↑(box d (L + H + m)) := by
  intro x hx
  simp only [mem_brick] at hx
  simp only [Finset.mem_coe, mem_box, Nat.cast_add]
  intro i
  by_cases hi : i = 0
  · subst hi
    constructor <;> linarith [hx.1.1, hx.1.2]
  · have := abs_le.mp (hx.2 i hi)
    constructor <;> linarith [this.1, this.2]

end BGNd

/-! ## The case `d = 2` (Harris–Kesten) and the global assemblies -/

/-- **The case `d = 2` of Theorem (7.35), proved**: `θ_ℍ(p_c(ℤ²)) = 0`. By the restriction
coupling `θ_ℍ(p) ≤ θ_{ℤ²}(p)` (`theta_induce_le_holds`), and `θ_{ℤ²}(p_c) = 0` by Kesten's
`p_c(ℤ²) = 1/2` and Harris' `θ(1/2) = 0` (`percolationContinuity_two` fed with the proved
statements `kesten_criticalProb_Z2_holds`, `harris_theta_half_holds`). Grimmett 1999, notes to §7.3,
p. 196: "In the case `d = 2`, earlier results of Harris (1960) and Kesten (1980a) imply that
`θ_ℍ(p_c) = 0`." [cite: GrimmettPercolation1999, Thm. (7.35) and §7 notes p. 196] -/
theorem BarskyGrimmettNewman1991_dim_two :
    theta (halfSpaceGraph 2) (halfSpaceOrigin 2) (criticalProbI 2) = 0 := by
  have h2 : theta (zdGraph 2) (0 : Site 2) (criticalProbI 2) = 0 :=
    percolationContinuity_two kesten_criticalProb_Z2_holds harris_theta_half_holds
  have hle : theta (halfSpaceGraph 2) (halfSpaceOrigin 2) (criticalProbI 2) ≤
      theta (zdGraph 2) (0 : Site 2) (criticalProbI 2) :=
    theta_induce_le_holds (zdGraph 2) (halfSpace 2) 0 (zero_mem_halfSpace 2) _
  exact le_antisymm (hle.trans_eq h2) measureReal_nonneg

end Percolation.Literature

end
