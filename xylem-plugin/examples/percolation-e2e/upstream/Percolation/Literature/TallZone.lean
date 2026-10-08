import Percolation.Literature.TallDisjoint3
import Percolation.Util.Linter

/-!
# The tall gait, XIV: the reserved zone of an attempt

The zone of the attempt along `(a, e)` from the token
`τ` (Grimmett, *Percolation*, 2nd ed. (1999), §7.3 p. 173 (C): the bricks of a successful step lie in
a prescribed region around the tube) is the set of lattice edges whose doubled midpoint lies in the
union `zoneRegion` of six boxes: the entry leg, the riser column, the jog, the trunk tube, and the
two branch tubes. We define the region, the zone as a `Finset` of edges (`zoneF`), prove that the
support of a placed brick lies in the zone as soon as its box lies in the region
(`suppP_subset_zoneF`), and that **the box of every brick recorded in a run state lies in the
region** (`boxOf_subset_zoneRegion`).

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §7.3 pp. 172–174.
-/

noncomputable section

namespace Percolation.Literature

open LatticeModels Contour
open scoped Classical

namespace BGNd

variable {d : ℕ} [NeZero d]

/-! ## Supports are lattice edges near their box -/

/-- The support of a placed brick consists of lattice edges. [folklore] -/
theorem suppP_subset_edgeSet {m L H : ℕ} (hL : 1 ≤ L) (β : BrickPos d) :
    (↑(suppP m L H β) : Set (Sym2 (Site d))) ⊆ (zdGraph d).edgeSet := by
  intro z hz
  rw [Finset.mem_coe, suppP, Finset.mem_map] at hz
  obtain ⟨z₀, hz₀, rfl⟩ := hz
  rw [Equiv.coe_toEmbedding, sym2Equiv_mem_edgeSet_iff]
  have hz₀' : z₀ ∈ suppC d m L H := by rw [← coe_suppCF]; exact hz₀
  rcases hz₀' with h | h
  · exact SimpleGraph.edgeSet_mono (starGraph_le _ _ _) h
  · simp only [Set.mem_iUnion] at h
    obtain ⟨x, hx, hzx⟩ := h
    exact cleanEdges_subset_edgeSet hL hx.1 hzx

omit [NeZero d] in
/-- The endpoints of a lattice edge are within `1` of half its doubled midpoint. [folklore] -/
theorem abs_two_mul_sub_dmid_le {z : Sym2 (Site d)} (hz : z ∈ (zdGraph d).edgeSet) {x : Site d} (hx : x ∈ z) (i : Fin d) :
    |2 * x i - dmid z i| ≤ 1 := by
  induction z using Sym2.ind with
  | _ u v =>
    rw [SimpleGraph.mem_edgeSet, zdGraph_adj_iff] at hz
    rw [dmid_mk, Pi.add_apply]
    have hnear : |u i - v i| ≤ 1 := by
      obtain ⟨k, hk | hk⟩ := hz
      · rw [hk, Pi.add_apply]
        by_cases hik : i = k
        · subst hik; simp
        · rw [Pi.single_eq_of_ne hik]; simp
      · rw [hk, Pi.add_apply]
        by_cases hik : i = k
        · subst hik; simp
        · rw [Pi.single_eq_of_ne hik]; simp
    have h' := abs_le.1 hnear
    rcases Sym2.mem_iff.1 hx with rfl | rfl <;> rw [abs_le] <;> constructor <;> linarith

/-! ## The region -/

section Region

variable (Y : TallLayout) (hd : 3 ≤ d) (a : Site 2) (e : MDir) (τ : TTok d)

namespace TallLayout
/-- The slack of a box around twice its base, `K₀ = 2L + 2H + 2`. [folklore] -/
def K0 (Y : TallLayout) : ℤ := 2 * Y.L + 2 * Y.H + 2
/-- The vertical slack of the riser column. [folklore] -/
def Cv (Y : TallLayout) : ℤ := 2 * Y.ρv + 2 * Y.Δw + 2 * Y.m + 2 * Y.H + 4
end TallLayout

/-- **The reserved region** of the attempt along `(a, e)` from `τ`, in doubled coordinates: the union
of the entry box `A`, the riser column `R`, the jog box `J`, the trunk tube `T` and the two branch
tubes; all within `L'` of `0` in the remaining coordinates. [cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
def zoneRegion : Set (Site d) :=
  let ae := axOf hd e
  let af := latOf hd e
  let a0 := ax0 hd
  let s : ℤ := (sgOf e : ℤ)
  let v : ℤ := (jogDir a e : ℤ)
  let p := τ.pos
  let Xe := Y.ctr (tgtCell a e) e.1
  let Xf := Y.ctr (tgtCell a e) ⟨1 - e.1.val, by have := e.1.isLt; omega⟩
  let y := Y.lane (tgtCell a e) e
  let zs := Y.zOf (τ.src.getD e)
  let ze := Y.zOf e
  {w | (∀ j, j ≠ ae → j ≠ af → j ≠ a0 → |w j| ≤ 2 * Y.Lp + Y.K0) ∧
    ( -- `A`
      (1 ≤ s * (w ae - 2 * p ae) ∧ s * (w ae - 2 * p ae) ≤ 2 * Y.Pw * Y.ell + 2 * Y.H + 2 ∧
        |w af - 2 * p af| ≤ 2 * Y.Lp + 2 * Y.Δw + Y.K0 ∧ |w a0 - 2 * zs| ≤ 2 * Y.ρv + 2 * Y.Δw + Y.K0) ∨
      -- `R`
      (2 * Y.Pw * Y.ell + 2 * Y.m + 2 - Y.K0 ≤ s * (w ae - 2 * p ae) ∧
        s * (w ae - 2 * p ae) ≤ 2 * Y.Pw * Y.ell + 2 * Y.H + 2 * Y.N₁ * Y.Lp + Y.K0 ∧
        |w af - 2 * p af| ≤ 2 * Y.Lp + 2 * Y.Δw + Y.K0 ∧
        2 * min zs ze - Y.Cv ≤ w a0 ∧ w a0 ≤ 2 * max zs ze + Y.Cv) ∨
      -- `J`
      (2 * Y.Pw * Y.ell - Y.K0 ≤ s * (w ae - 2 * p ae) ∧
        s * (w ae - 2 * p ae) ≤ 2 * Y.Pw * Y.ell + 2 * Y.H + 4 * Y.N₁ * Y.Lp + 2 * Y.ell + 2 * Y.Lp + Y.K0 ∧
        -(2 * Y.Lp + 2 * Y.Δw) ≤ v * (w af - 2 * p af) ∧ v * (w af - 2 * y) ≤ 2 * Y.m + 2 * Y.H + 6 ∧
        |w a0 - 2 * ze| ≤ 2 * Y.ρv + Y.K0) ∨
      -- `T`
      (2 * Y.Pw * Y.ell + 2 * Y.L + 3 ≤ s * (w ae - 2 * p ae) ∧ s * (w ae - 2 * Xe) ≤ 2 * Y.Dh - 2 ∧
        |w af - 2 * y| ≤ 2 * Y.ell + 2 * Y.Lp + 8 * Y.Δw + Y.K0 ∧ |w a0 - 2 * ze| ≤ 2 * Y.ρv + Y.K0) ∨
      -- the branch tubes, `w' = ±1`
      (∃ w' : ℤˣ, -(2 * Y.Lp) - Y.K0 ≤ s * (w ae - 2 * brLane Y a e w') ∧
        s * (w ae - 2 * brLane Y a e w') ≤ 2 * Y.ell + 2 * Y.H + 2 * Y.Lp + Y.K0 ∧
        -(2 * Y.ell + 2 * Y.Lp + 8 * Y.Δw) ≤ (w' : ℤ) * (w af - 2 * y) ∧ (w' : ℤ) * (w af - 2 * Xf) ≤ 2 * Y.Dh - 2 ∧
        |w a0 - 2 * ze| ≤ 2 * Y.ρv + Y.K0))}

end Region

/-! ## Containment of the boxes of a run state -/

section Containment

variable (Y : TallLayout) (hd : 3 ≤ d) (hL : Y.m + 1 ≤ Y.L) (hH : 2 * Y.m + 2 ≤ Y.H) (a : Site 2) (e : MDir) (τ : TTok d)

omit [NeZero d] in
/-- The remaining coordinates of a point of the box of a recorded brick. [folklore] -/
theorem abs_other_le {L H : ℕ} {κ : BrickPos d} {w : Site d} (hw : w ∈ boxOf L H κ) {j : Fin d} {B : ℤ} (hb : |κ.b j| ≤ B) :
    |w j| ≤ 2 * B + (2 * (L : ℤ) + 2 * H + 2) := by
  have h1 := abs_le.1 (box_any hw j)
  have h2 := abs_le.1 hb
  rw [abs_le]; constructor <;> linarith

omit [NeZero d] in
/-- Membership in the region via the `A` box. [folklore] -/
theorem mem_zoneRegion_A {w : Site d} (hoth : ∀ j, j ≠ axOf hd e → j ≠ latOf hd e → j ≠ ax0 hd → |w j| ≤ 2 * Y.Lp + Y.K0)
    (h1 : 1 ≤ (sgOf e : ℤ) * (w (axOf hd e) - 2 * τ.pos (axOf hd e)))
    (h2 : (sgOf e : ℤ) * (w (axOf hd e) - 2 * τ.pos (axOf hd e)) ≤ 2 * Y.Pw * Y.ell + 2 * Y.H + 2)
    (h3 : |w (latOf hd e) - 2 * τ.pos (latOf hd e)| ≤ 2 * Y.Lp + 2 * Y.Δw + Y.K0)
    (h4 : |w (ax0 hd) - 2 * Y.zOf (τ.src.getD e)| ≤ 2 * Y.ρv + 2 * Y.Δw + Y.K0) : w ∈ zoneRegion Y hd a e τ :=
  ⟨hoth, Or.inl ⟨h1, h2, h3, h4⟩⟩

omit [NeZero d] in
/-- Membership in the region via the riser column. [folklore] -/
theorem mem_zoneRegion_R {w : Site d} (hoth : ∀ j, j ≠ axOf hd e → j ≠ latOf hd e → j ≠ ax0 hd → |w j| ≤ 2 * Y.Lp + Y.K0)
    (h1 : 2 * Y.Pw * Y.ell + 2 * Y.m + 2 - Y.K0 ≤ (sgOf e : ℤ) * (w (axOf hd e) - 2 * τ.pos (axOf hd e)))
    (h2 : (sgOf e : ℤ) * (w (axOf hd e) - 2 * τ.pos (axOf hd e)) ≤ 2 * Y.Pw * Y.ell + 2 * Y.H + 2 * Y.N₁ * Y.Lp + Y.K0)
    (h3 : |w (latOf hd e) - 2 * τ.pos (latOf hd e)| ≤ 2 * Y.Lp + 2 * Y.Δw + Y.K0)
    (h4 : 2 * min (Y.zOf (τ.src.getD e)) (Y.zOf e) - Y.Cv ≤ w (ax0 hd))
    (h5 : w (ax0 hd) ≤ 2 * max (Y.zOf (τ.src.getD e)) (Y.zOf e) + Y.Cv) : w ∈ zoneRegion Y hd a e τ :=
  ⟨hoth, Or.inr (Or.inl ⟨h1, h2, h3, h4, h5⟩)⟩

omit [NeZero d] in
/-- Membership in the region via the jog box. [folklore] -/
theorem mem_zoneRegion_J {w : Site d} (hoth : ∀ j, j ≠ axOf hd e → j ≠ latOf hd e → j ≠ ax0 hd → |w j| ≤ 2 * Y.Lp + Y.K0)
    (h1 : 2 * Y.Pw * Y.ell - Y.K0 ≤ (sgOf e : ℤ) * (w (axOf hd e) - 2 * τ.pos (axOf hd e)))
    (h2 : (sgOf e : ℤ) * (w (axOf hd e) - 2 * τ.pos (axOf hd e)) ≤
      2 * Y.Pw * Y.ell + 2 * Y.H + 4 * Y.N₁ * Y.Lp + 2 * Y.ell + 2 * Y.Lp + Y.K0)
    (h3 : -(2 * Y.Lp + 2 * Y.Δw) ≤ (jogDir a e : ℤ) * (w (latOf hd e) - 2 * τ.pos (latOf hd e)))
    (h4 : (jogDir a e : ℤ) * (w (latOf hd e) - 2 * Y.lane (tgtCell a e) e) ≤ 2 * Y.m + 2 * Y.H + 6)
    (h5 : |w (ax0 hd) - 2 * Y.zOf e| ≤ 2 * Y.ρv + Y.K0) : w ∈ zoneRegion Y hd a e τ :=
  ⟨hoth, Or.inr (Or.inr (Or.inl ⟨h1, h2, h3, h4, h5⟩))⟩

omit [NeZero d] in
/-- Membership in the region via the trunk tube. [folklore] -/
theorem mem_zoneRegion_T {w : Site d} (hoth : ∀ j, j ≠ axOf hd e → j ≠ latOf hd e → j ≠ ax0 hd → |w j| ≤ 2 * Y.Lp + Y.K0)
    (h1 : 2 * Y.Pw * Y.ell + 2 * Y.L + 3 ≤ (sgOf e : ℤ) * (w (axOf hd e) - 2 * τ.pos (axOf hd e)))
    (h2 : (sgOf e : ℤ) * (w (axOf hd e) - 2 * Y.ctr (tgtCell a e) e.1) ≤ 2 * Y.Dh - 2)
    (h3 : |w (latOf hd e) - 2 * Y.lane (tgtCell a e) e| ≤ 2 * Y.ell + 2 * Y.Lp + 8 * Y.Δw + Y.K0)
    (h4 : |w (ax0 hd) - 2 * Y.zOf e| ≤ 2 * Y.ρv + Y.K0) : w ∈ zoneRegion Y hd a e τ :=
  ⟨hoth, Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2, h3, h4⟩)))⟩

omit [NeZero d] in
/-- Membership in the region via a branch tube. [folklore] -/
theorem mem_zoneRegion_B {w : Site d} (hoth : ∀ j, j ≠ axOf hd e → j ≠ latOf hd e → j ≠ ax0 hd → |w j| ≤ 2 * Y.Lp + Y.K0)
    (w' : ℤˣ) (h1 : -(2 * Y.Lp) - Y.K0 ≤ (sgOf e : ℤ) * (w (axOf hd e) - 2 * brLane Y a e w'))
    (h2 : (sgOf e : ℤ) * (w (axOf hd e) - 2 * brLane Y a e w') ≤ 2 * Y.ell + 2 * Y.H + 2 * Y.Lp + Y.K0)
    (h3 : -(2 * Y.ell + 2 * Y.Lp + 8 * Y.Δw) ≤ (w' : ℤ) * (w (latOf hd e) - 2 * Y.lane (tgtCell a e) e))
    (h4 : (w' : ℤ) * (w (latOf hd e) - 2 * Y.ctr (tgtCell a e) ⟨1 - e.1.val, by have := e.1.isLt; omega⟩) ≤ 2 * Y.Dh - 2)
    (h5 : |w (ax0 hd) - 2 * Y.zOf e| ≤ 2 * Y.ρv + Y.K0) : w ∈ zoneRegion Y hd a e τ :=
  ⟨hoth, Or.inr (Or.inr (Or.inr (Or.inr ⟨w', h1, h2, h3, h4, h5⟩)))⟩

omit [NeZero d] in
/-- The remaining coordinates, from the invariant's bound `|b_j| ≤ L'`. [folklore] -/
theorem oth_of_bound {L H : ℕ} (hK : Y.K0 = 2 * (L : ℤ) + 2 * H + 2) {κ : BrickPos d} {w : Site d} (hw : w ∈ boxOf L H κ)
    (h : ∀ j, j ≠ axOf hd e → j ≠ latOf hd e → j ≠ ax0 hd → |κ.b j| ≤ Y.Lp) :
    ∀ j, j ≠ axOf hd e → j ≠ latOf hd e → j ≠ ax0 hd → |w j| ≤ 2 * Y.Lp + Y.K0 := by
  intro j hj1 hj2 hj3; rw [hK]; exact abs_other_le hw (h j hj1 hj2 hj3)

/-- **The inequalities of the points of the boxes of `A`.** [cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
theorem boxOf_A_facts (hY : Y.OK) (hτ : TAdm hd Y a e τ) {st : RS d} (hI : TallInv hd Y hL hH a e τ st)
    {k : ℕ} (hk : k < st.sA.length) {w : Site d} (hw : w ∈ boxOf Y.L Y.H (legOf st.sA k)) :
    (∀ j, j ≠ axOf hd e → j ≠ latOf hd e → j ≠ ax0 hd → |w j| ≤ 2 * Y.Lp + Y.K0) ∧
      1 ≤ (sgOf e : ℤ) * (w (axOf hd e) - 2 * τ.pos (axOf hd e)) ∧
      (sgOf e : ℤ) * (w (axOf hd e) - 2 * τ.pos (axOf hd e)) ≤ 2 * Y.Pw * Y.ell + 2 * Y.H + 2 ∧
      |w (latOf hd e) - 2 * τ.pos (latOf hd e)| ≤ 2 * Y.Lp + 2 * Y.Δw + Y.K0 ∧
      |w (ax0 hd) - 2 * Y.zOf (τ.src.getD e)| ≤ 2 * Y.ρv + 2 * Y.Δw + Y.K0 := by
  obtain ⟨hLp0, -, -, hell, hmH, -, -, -, hΔ0, -⟩ := hY.facts
  have hK0 : Y.K0 = 2 * Y.L + 2 * Y.H + 2 := rfl
  have hs1 : (sgOf e : ℤ) = 1 ∨ (sgOf e : ℤ) = -1 := by rcases Int.units_eq_one_or (sgOf e) with h | h <;> simp [h]
  have hl0 : (0 : ℤ) ≤ Y.ell := by linarith
  obtain ⟨hbe, hbf, hh0, hh1, hoth⟩ := boundsA Y hd hL hH a e τ hY hI hk
  have hAne : st.sA ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hax : (legOf st.sA k).a = axOf hd e ∧ (legOf st.sA k).s = sgOf e := by
    have := (hI.invA.grown hAne).axis_sign (k := k) hk; rw [hI.invA.zero hAne] at this; exact this
  refine ⟨oth_of_bound Y hd e hK0 hw hoth, ?_, ?_, ?_, ?_⟩
  · obtain ⟨h1, -⟩ := box_axis hw
    rw [hax.1, hax.2, hbe] at h1
    have hk0 : (0 : ℤ) ≤ Y.ell * k := by positivity
    rcases hs1 with h | h <;> rw [h] at h1 ⊢ <;> linarith only [h1, hk0]
  · obtain ⟨-, h2⟩ := box_axis hw
    rw [hax.1, hax.2, hbe] at h2
    have hkPw : (k : ℤ) ≤ Y.Pw := by have := hI.invA.len; exact_mod_cast (by omega : k ≤ Y.Pw)
    have hkl : Y.ell * (k : ℤ) ≤ Y.Pw * Y.ell := by nlinarith
    rcases hs1 with h | h <;> rw [h] at h2 ⊢ <;> linarith only [h2, hkl]
  · have h := abs_le.1 hbf
    obtain ⟨h3, h2⟩ := box_trans hw (i := latOf hd e) (by rw [hax.1]; exact latOf_ne_axOf hd e)
    rw [hK0, abs_le]; constructor <;> linarith only [h.1, h.2, h2, h3]
  · obtain ⟨h3, h2⟩ := box_trans hw (i := ax0 hd) (by rw [hax.1]; exact (axOf_ne_ax0 hd e).symm)
    have hτh := abs_le.1 hτ.height
    by_cases hu : riseDir Y e τ = 0
    · have h := abs_le.1 (hh0 hu)
      have hz : Y.zOf (τ.src.getD e) = Y.zOf e := by
        unfold riseDir at hu
        cases hsrc : τ.src with
        | none => rfl
        | some d' =>
          rw [hsrc] at hu; simp only at hu
          simp only [Option.getD_some]
          split_ifs at hu with h1 h2 <;> omega
      rw [hz, hK0, abs_le]; constructor <;> linarith only [h.1, h.2, h2, h3, hΔ0]
    · obtain ⟨h4, h5⟩ := hh1 hu
      have hu1 : riseDir Y e τ = 1 ∨ riseDir Y e τ = -1 := (riseDir_cases Y e τ).resolve_left hu
      rw [hK0, abs_le]
      rcases hu1 with h | h <;> rw [h] at h4 h5 <;> constructor <;> linarith only [h4, h5, h2, h3, hτh.1, hτh.2]

/-- **Boxes of `A` lie in the region.** [cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
theorem boxOf_subset_zoneRegion_A (hY : Y.OK) (hτ : TAdm hd Y a e τ) {st : RS d} (hI : TallInv hd Y hL hH a e τ st)
    {k : ℕ} (hk : k < st.sA.length) : boxOf Y.L Y.H (legOf st.sA k) ⊆ zoneRegion Y hd a e τ := by
  intro w hw
  obtain ⟨h0, h1, h2, h3, h4⟩ := boxOf_A_facts Y hd hL hH a e τ hY hτ hI hk hw
  exact mem_zoneRegion_A Y hd a e τ h0 h1 h2 h3 h4

/-- **The riser column, vertically**: every point of the box of a riser brick lies between the two
layers, with slack `C_v`. [folklore] -/
theorem riser_w0_bounds (hY : Y.OK) (hτ : TAdm hd Y a e τ) {st : RS d} (hI : TallInv hd Y hL hH a e τ st)
    {k : ℕ} (hk : k < st.sR.length) {w : Site d} (hw : w ∈ boxOf Y.L Y.H (legOf st.sR k)) :
    2 * min (Y.zOf (τ.src.getD e)) (Y.zOf e) - Y.Cv ≤ w (ax0 hd) ∧ w (ax0 hd) ≤ 2 * max (Y.zOf (τ.src.getD e)) (Y.zOf e) + Y.Cv := by
  obtain ⟨hLp0, -, hLeq, hell, hmH, -, -, -, hΔ0, hρv, -, -, -, hWl, -, -, hPe, hP2, -, -, -, hP64, -⟩ := hY.facts
  have hW0 : 0 < Y.Wl := by rw [hWl]; linarith only [hP64, hP2, hPe, hell, hmH]
  have hCv : Y.Cv = 2 * Y.ρv + 2 * Y.Δw + 2 * Y.m + 2 * Y.H + 4 := rfl
  have hl0 : (0 : ℤ) ≤ Y.ell := by linarith
  have hm0 : (0 : ℤ) ≤ Y.m := by positivity
  have hRne : st.sR ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hu : riseDir Y e τ ≠ 0 := fun h => hRne (hI.invR.nil h)
  obtain ⟨hb0, hR00, -, -, -, -⟩ := boundsR Y hd hL hH a e τ hY hI hk
  obtain ⟨hax, hsx⟩ := hI.invR.axis_sign Y hd hL hH a e τ hRne hk
  have hkn := le_riserLen Y hd hL hH a e τ hI hk
  obtain ⟨h1, h2⟩ := box_axis hw
  rw [hax, hsx, riseUnit_val Y e τ hu] at h1 h2
  have hlenA := hI.invR.prev hRne
  obtain ⟨-, -, -, hAht, -⟩ := boundsA Y hd hL hH a e τ hY hI (show Y.Pw < st.sA.length by omega)
  obtain ⟨hA0, hA1⟩ := hAht hu
  obtain ⟨hdist, -⟩ := riserLen_le_dist Y hd hL hH a e τ hY hτ hI hRne
  have hkl : Y.ell * (k : ℤ) ≤ (riserLen Y e τ ((legOf st.sR 0).b (ax0 hd)) : ℤ) * Y.ell := by
    have : (k : ℤ) ≤ riserLen Y e τ ((legOf st.sR 0).b (ax0 hd)) := by exact_mod_cast hkn
    nlinarith
  have hτh := abs_le.1 hτ.height
  obtain ⟨d', hsrc, hW1, -⟩ := riseDir_layers' Y e τ hY hu
  rw [hsrc, Option.getD_some] at hτh ⊢
  have hu1 : riseDir Y e τ = 1 ∨ riseDir Y e τ = -1 := (riseDir_cases Y e τ).resolve_left hu
  have hk0 : (0 : ℤ) ≤ Y.ell * k := by positivity
  rw [hCv]
  rcases hu1 with h | h <;> rw [h] at h1 h2 hb0 hR00 hA0 hA1 hdist hW1
  · rw [min_eq_left (by linarith only [hW1, hW0]), max_eq_right (by linarith only [hW1, hW0])]
    constructor
    · linarith only [h1, hb0, hR00, hA0, hτh.1, hk0, hLeq, hLp0, hρv, hΔ0, hm0, hmH, hell]
    · linarith only [h2, hb0, hdist, hkl, hρv, hΔ0, hell, hmH, hLp0]
  · rw [min_eq_right (by linarith only [hW1, hW0]), max_eq_left (by linarith only [hW1, hW0])]
    constructor
    · linarith only [h2, hb0, hdist, hkl, hρv, hΔ0, hell, hmH, hLp0]
    · linarith only [h1, hb0, hR00, hA0, hτh.2, hk0, hLeq, hLp0, hρv, hΔ0, hm0, hmH, hell]

/-- **The inequalities of the points of the boxes of the riser.** [cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
theorem boxOf_R_facts (hY : Y.OK) (hτ : TAdm hd Y a e τ) {st : RS d} (hI : TallInv hd Y hL hH a e τ st)
    {k : ℕ} (hk : k < st.sR.length) {w : Site d} (hw : w ∈ boxOf Y.L Y.H (legOf st.sR k)) :
    (∀ j, j ≠ axOf hd e → j ≠ latOf hd e → j ≠ ax0 hd → |w j| ≤ 2 * Y.Lp + Y.K0) ∧
      2 * Y.Pw * Y.ell + 2 * Y.m + 2 - Y.K0 ≤ (sgOf e : ℤ) * (w (axOf hd e) - 2 * τ.pos (axOf hd e)) ∧
      (sgOf e : ℤ) * (w (axOf hd e) - 2 * τ.pos (axOf hd e)) ≤ 2 * Y.Pw * Y.ell + 2 * Y.H + 2 * Y.N₁ * Y.Lp + Y.K0 ∧
      |w (latOf hd e) - 2 * τ.pos (latOf hd e)| ≤ 2 * Y.Lp + 2 * Y.Δw + Y.K0 ∧
      2 * min (Y.zOf (τ.src.getD e)) (Y.zOf e) - Y.Cv ≤ w (ax0 hd) ∧ w (ax0 hd) ≤ 2 * max (Y.zOf (τ.src.getD e)) (Y.zOf e) + Y.Cv := by
  obtain ⟨hLp0, -, hLeq, hell, hmH, -⟩ := hY.facts
  have hK0 : Y.K0 = 2 * Y.L + 2 * Y.H + 2 := rfl
  have hs1 : (sgOf e : ℤ) = 1 ∨ (sgOf e : ℤ) = -1 := by rcases Int.units_eq_one_or (sgOf e) with h | h <;> simp [h]
  have hm0 : (0 : ℤ) ≤ Y.m := by positivity
  have hRne : st.sR ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hNR : st.sR ≠ [] → riserLen Y e τ ((legOf st.sR 0).b (ax0 hd)) ≤ Y.N₁ := fun h => riser_feasible Y hd hL hH a e τ hY hτ hI h
  obtain ⟨-, -, hlo, hhi, hbf, hoth⟩ := boundsR Y hd hL hH a e τ hY hI hk
  obtain ⟨hax, -⟩ := hI.invR.axis_sign Y hd hL hH a e τ hRne hk
  have hkn := le_riserLen Y hd hL hH a e τ hI hk
  have hN := hNR hRne
  have hkN : (k : ℤ) * Y.Lp ≤ Y.N₁ * Y.Lp := mul_le_mul_of_nonneg_right (by exact_mod_cast hkn.trans hN) hLp0
  obtain ⟨h4, h5⟩ := riser_w0_bounds Y hd hL hH a e τ hY hτ hI hk hw
  refine ⟨oth_of_bound Y hd e hK0 hw hoth, ?_, ?_, ?_, h4, h5⟩
  · obtain ⟨h3, h2⟩ := box_trans hw (i := axOf hd e) (by rw [hax]; exact axOf_ne_ax0 hd e)
    rw [hK0]
    rcases hs1 with h | h <;> rw [h] at hlo ⊢ <;> linarith only [hlo, h2, h3]
  · obtain ⟨h3, h2⟩ := box_trans hw (i := axOf hd e) (by rw [hax]; exact axOf_ne_ax0 hd e)
    rw [hK0]
    rcases hs1 with h | h <;> rw [h] at hhi ⊢ <;> linarith only [hhi, h2, h3, hkN, hm0]
  · have h := abs_le.1 hbf
    obtain ⟨h3, h2⟩ := box_trans hw (i := latOf hd e) (by rw [hax]; exact latOf_ne_ax0 hd e)
    rw [hK0, abs_le]; constructor <;> linarith only [h.1, h.2, h2, h3]

/-- **Boxes of the riser lie in the region.** [cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
theorem boxOf_subset_zoneRegion_R (hY : Y.OK) (hτ : TAdm hd Y a e τ) {st : RS d} (hI : TallInv hd Y hL hH a e τ st)
    {k : ℕ} (hk : k < st.sR.length) : boxOf Y.L Y.H (legOf st.sR k) ⊆ zoneRegion Y hd a e τ := by
  intro w hw
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := boxOf_R_facts Y hd hL hH a e τ hY hτ hI hk hw
  exact mem_zoneRegion_R Y hd a e τ h0 h1 h2 h3 h4 h5

/-- **The inequalities of the points of the boxes of the jog.** [cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
theorem boxOf_J_facts (hY : Y.OK) (hτ : TAdm hd Y a e τ) {st : RS d} (hI : TallInv hd Y hL hH a e τ st)
    {k : ℕ} (hk : k < st.sJ.length) {w : Site d} (hw : w ∈ boxOf Y.L Y.H (legOf st.sJ k)) :
    (∀ j, j ≠ axOf hd e → j ≠ latOf hd e → j ≠ ax0 hd → |w j| ≤ 2 * Y.Lp + Y.K0) ∧
      2 * Y.Pw * Y.ell - Y.K0 ≤ (sgOf e : ℤ) * (w (axOf hd e) - 2 * τ.pos (axOf hd e)) ∧
      (sgOf e : ℤ) * (w (axOf hd e) - 2 * τ.pos (axOf hd e)) ≤
        2 * Y.Pw * Y.ell + 2 * Y.H + 4 * Y.N₁ * Y.Lp + 2 * Y.ell + 2 * Y.Lp + Y.K0 ∧
      -(2 * Y.Lp + 2 * Y.Δw) ≤ (jogDir a e : ℤ) * (w (latOf hd e) - 2 * τ.pos (latOf hd e)) ∧
      (jogDir a e : ℤ) * (w (latOf hd e) - 2 * Y.lane (tgtCell a e) e) ≤ 2 * Y.m + 2 * Y.H + 6 ∧
      |w (ax0 hd) - 2 * Y.zOf e| ≤ 2 * Y.ρv + Y.K0 := by
  obtain ⟨hLp0, -, hLeq, hell, hmH, -⟩ := hY.facts
  have hK0 : Y.K0 = 2 * Y.L + 2 * Y.H + 2 := rfl
  have hs1 : (sgOf e : ℤ) = 1 ∨ (sgOf e : ℤ) = -1 := by rcases Int.units_eq_one_or (sgOf e) with h | h <;> simp [h]
  have hv1 : (jogDir a e : ℤ) = 1 ∨ (jogDir a e : ℤ) = -1 := by rcases Int.units_eq_one_or (jogDir a e) with h | h <;> simp [h]
  have hl0 : (0 : ℤ) ≤ Y.ell := by linarith
  obtain ⟨hNR, hNJ⟩ := sched_bounds Y hd hL hH a e τ hY hτ hI
  have hJne : st.sJ ≠ [] := List.ne_nil_of_length_pos (by omega)
  obtain ⟨hbf, hJ0, hfw0, hfw1, h0lo, h0hi, hht, hoth⟩ := boundsJ Y hd hL hH a e τ hY hI hNR hk
  obtain ⟨hax, hsx⟩ := hI.invJ.axis_sign Y hd hL hH a e τ hJne hk
  obtain ⟨-, -, hElat⟩ := bounds_entryLast Y hd hL hH a e τ hY hI hJne hNR
  have hkn := le_jogLen Y hd hL hH a e τ hI hk
  have hN := hNJ hJne
  have hkN : (k : ℤ) * Y.Lp ≤ Y.N₁ * Y.Lp := mul_le_mul_of_nonneg_right (by exact_mod_cast hkn.trans hN) hLp0
  refine ⟨oth_of_bound Y hd e hK0 hw hoth, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨h3, h2⟩ := box_trans hw (i := axOf hd e) (by rw [hax]; exact (latOf_ne_axOf hd e).symm)
    rw [hK0]
    rcases hs1 with h | h <;> rw [h] at hfw0 h0lo ⊢ <;> linarith only [hfw0, h0lo, h2, h3]
  · obtain ⟨h3, h2⟩ := box_trans hw (i := axOf hd e) (by rw [hax]; exact (latOf_ne_axOf hd e).symm)
    rw [hK0]
    have hN0 : (0 : ℤ) ≤ Y.N₁ * Y.Lp := by positivity
    rcases hs1 with h | h <;> rw [h] at hfw1 h0hi ⊢ <;> linarith only [hfw1, h0hi, h2, h3, hkN, hN0]
  · obtain ⟨h1, -⟩ := box_axis hw
    rw [hax, hsx, hbf, hJ0] at h1
    have hEl := abs_le.1 hElat
    have hk0 : (0 : ℤ) ≤ Y.ell * k := by positivity
    rcases hv1 with h | h <;> rw [h] at h1 ⊢ <;> linarith only [h1, hEl.1, hEl.2, hk0, hLeq, hLp0]
  · obtain ⟨-, h2⟩ := box_axis hw
    rw [hax, hsx, hbf] at h2
    have hdist := jogLen_le_dist Y hd hL hH a e τ hY hτ hI hJne
    have hkl : Y.ell * (k : ℤ) ≤ (jogLen Y a e ((legOf st.sJ 0).b (latOf hd e)) : ℤ) * Y.ell := by
      have : (k : ℤ) ≤ jogLen Y a e ((legOf st.sJ 0).b (latOf hd e)) := by exact_mod_cast hkn
      nlinarith
    rcases hv1 with h | h <;> rw [h] at h2 hdist ⊢ <;> linarith only [h2, hdist, hkl, hell]
  · have h := abs_le.1 hht
    obtain ⟨h3, h2⟩ := box_trans hw (i := ax0 hd) (by rw [hax]; exact (latOf_ne_ax0 hd e).symm)
    rw [hK0, abs_le]; constructor <;> linarith only [h.1, h.2, h2, h3]

/-- **Boxes of the jog lie in the region.** [cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
theorem boxOf_subset_zoneRegion_J (hY : Y.OK) (hτ : TAdm hd Y a e τ) {st : RS d} (hI : TallInv hd Y hL hH a e τ st)
    {k : ℕ} (hk : k < st.sJ.length) : boxOf Y.L Y.H (legOf st.sJ k) ⊆ zoneRegion Y hd a e τ := by
  intro w hw
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := boxOf_J_facts Y hd hL hH a e τ hY hτ hI hk hw
  exact mem_zoneRegion_J Y hd a e τ h0 h1 h2 h3 h4 h5

/-- The trunk stays in the cell: `s (T_k.b_e - X_e) ≤ D/2 - 1 - ℓ` for every recorded index. [folklore] -/
theorem trunk_in_cell (hY : Y.OK) (hτ : TAdm hd Y a e τ) {st : RS d} (hI : TallInv hd Y hL hH a e τ st) {k : ℕ}
    (hk : k < st.sT.length) :
    (sgOf e : ℤ) * ((legOf st.sT k).b (axOf hd e) - Y.ctr (tgtCell a e) e.1) ≤ Y.Dh - 1 - Y.ell := by
  obtain ⟨-, -, -, hell, hmH, -⟩ := hY.facts
  obtain ⟨hNR, hNJ⟩ := sched_bounds Y hd hL hH a e τ hY hτ hI
  have hTne : st.sT ≠ [] := List.ne_nil_of_length_pos (by omega)
  obtain ⟨hbe, -, -, -, -, -, -⟩ := boundsT Y hd hL hH a e τ hY hI hNR hNJ hk
  obtain ⟨h1len, -, -, -⟩ := trunk_feasible Y hd hL hH a e τ hY hτ hI hTne
  have hss : (sgOf e : ℤ) * (sgOf e : ℤ) = 1 := by rcases Int.units_eq_one_or (sgOf e) with h | h <;> simp [h]
  have hl0 : (0 : ℤ) ≤ Y.ell := by linarith
  set nE := legLen Y a e e ((legOf st.sT 0).b (axOf hd e)) with hnE
  have hkE : k ≤ nE := by
    have hs := hI.invT.sched
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · exact Nat.zero_le _
    · have := hs (k - 1) (by omega); omega
  have hroomE := not_of_lt_firstIdx (p := fun k => ¬roomT Y (tgtCell a e) e ((legOf st.sT 0).b (axOf hd e) + (sgOf e : ℤ) * (k * Y.ell)))
    (N := Y.Rmax) (k := nE - 1) (by show nE - 1 < legLen Y a e e _; omega)
  simp only [not_not] at hroomE
  unfold roomT at hroomE
  have hkE' : Y.ell * (k : ℤ) ≤ Y.ell * ((nE - 1 : ℕ) : ℤ) + Y.ell := by
    have : (k : ℤ) ≤ ((nE - 1 : ℕ) : ℤ) + 1 := by
      have h' : k ≤ nE - 1 + 1 := by omega
      exact_mod_cast h'
    nlinarith
  have e1 : (sgOf e : ℤ) * ((legOf st.sT 0).b (axOf hd e) + (sgOf e : ℤ) * (((nE - 1 : ℕ) : ℤ) * Y.ell) + (sgOf e : ℤ) * Y.ell -
      Y.ctr (tgtCell a e) e.1) = (sgOf e : ℤ) * ((legOf st.sT 0).b (axOf hd e) - Y.ctr (tgtCell a e) e.1) +
      ((sgOf e : ℤ) * (sgOf e : ℤ)) * (((nE - 1 : ℕ) : ℤ) * Y.ell + Y.ell) := by ring
  rw [e1, hss] at hroomE
  rw [hbe]
  have e2 : (sgOf e : ℤ) * ((legOf st.sT 0).b (axOf hd e) + (sgOf e : ℤ) * Y.ell * k - Y.ctr (tgtCell a e) e.1) =
      (sgOf e : ℤ) * ((legOf st.sT 0).b (axOf hd e) - Y.ctr (tgtCell a e) e.1) + ((sgOf e : ℤ) * (sgOf e : ℤ)) * (Y.ell * k) := by ring
  rw [e2, hss]
  linarith only [hroomE, hkE']

/-- **The inequalities of the points of the boxes of the trunk.** [cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
theorem boxOf_T_facts (hY : Y.OK) (hτ : TAdm hd Y a e τ) {st : RS d} (hI : TallInv hd Y hL hH a e τ st)
    {k : ℕ} (hk : k < st.sT.length) {w : Site d} (hw : w ∈ boxOf Y.L Y.H (legOf st.sT k)) :
    (∀ j, j ≠ axOf hd e → j ≠ latOf hd e → j ≠ ax0 hd → |w j| ≤ 2 * Y.Lp + Y.K0) ∧
      2 * Y.Pw * Y.ell + 2 * Y.L + 3 ≤ (sgOf e : ℤ) * (w (axOf hd e) - 2 * τ.pos (axOf hd e)) ∧
      (sgOf e : ℤ) * (w (axOf hd e) - 2 * Y.ctr (tgtCell a e) e.1) ≤ 2 * Y.Dh - 2 ∧
      |w (latOf hd e) - 2 * Y.lane (tgtCell a e) e| ≤ 2 * Y.ell + 2 * Y.Lp + 8 * Y.Δw + Y.K0 ∧
      |w (ax0 hd) - 2 * Y.zOf e| ≤ 2 * Y.ρv + Y.K0 := by
  obtain ⟨hLp0, -, hLeq, hell, hmH, -⟩ := hY.facts
  have hK0 : Y.K0 = 2 * Y.L + 2 * Y.H + 2 := rfl
  have hs1 : (sgOf e : ℤ) = 1 ∨ (sgOf e : ℤ) = -1 := by rcases Int.units_eq_one_or (sgOf e) with h | h <;> simp [h]
  have hl0 : (0 : ℤ) ≤ Y.ell := by linarith
  obtain ⟨hNR, hNJ⟩ := sched_bounds Y hd hL hH a e τ hY hτ hI
  have hTne : st.sT ≠ [] := List.ne_nil_of_length_pos (by omega)
  obtain ⟨hbe, hlo, -, -, hlat, hht, hoth⟩ := boundsT Y hd hL hH a e τ hY hI hNR hNJ hk
  obtain ⟨hax, hsx⟩ := hI.invT.axis_sign Y hd hL hH a e hTne hk
  have hcell := trunk_in_cell Y hd hL hH a e τ hY hτ hI hk
  refine ⟨oth_of_bound Y hd e hK0 hw hoth, ?_, ?_, ?_, ?_⟩
  · obtain ⟨h1, -⟩ := box_axis hw
    rw [hax, hsx, hbe] at h1
    have hk0 : (0 : ℤ) ≤ Y.ell * k := by positivity
    rcases hs1 with h | h <;> rw [h] at h1 hlo ⊢ <;> linarith only [h1, hlo, hk0]
  · obtain ⟨-, h2⟩ := box_axis hw
    rw [hax, hsx] at h2
    rcases hs1 with h | h <;> rw [h] at h2 hcell ⊢ <;> linarith only [h2, hcell, hell]
  · have h := abs_le.1 hlat
    obtain ⟨h3, h2⟩ := box_trans hw (i := latOf hd e) (by rw [hax]; exact latOf_ne_axOf hd e)
    rw [hK0, abs_le]; constructor <;> linarith only [h.1, h.2, h2, h3]
  · have h := abs_le.1 hht
    obtain ⟨h3, h2⟩ := box_trans hw (i := ax0 hd) (by rw [hax]; exact (axOf_ne_ax0 hd e).symm)
    rw [hK0, abs_le]; constructor <;> linarith only [h.1, h.2, h2, h3]

/-- **Boxes of the trunk lie in the region.** [cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
theorem boxOf_subset_zoneRegion_T (hY : Y.OK) (hτ : TAdm hd Y a e τ) {st : RS d} (hI : TallInv hd Y hL hH a e τ st)
    {k : ℕ} (hk : k < st.sT.length) : boxOf Y.L Y.H (legOf st.sT k) ⊆ zoneRegion Y hd a e τ := by
  intro w hw
  obtain ⟨h0, h1, h2, h3, h4⟩ := boxOf_T_facts Y hd hL hH a e τ hY hτ hI hk hw
  exact mem_zoneRegion_T Y hd a e τ h0 h1 h2 h3 h4

/-- **A branch leg stays in the cell** laterally: `w' (b_f - X_f) ≤ D/2 - 1 - ℓ` for the branch brick
and every recorded branch-leg brick. [folklore] -/
theorem branch_in_cell (hY : Y.OK) (hτ : TAdm hd Y a e τ) {st : RS d} (hI : TallInv hd Y hL hH a e τ st)
    {w' : ℤˣ} {g : BrickRec d} {sB : List (BrickRec d)} {D : Prop} (hB : InvB hd Y hL hH a e w' (some g) sB D)
    (hg : brIdx Y a e w' ((legOf st.sT 0).b (axOf hd e)) < st.sT.length ∧
      IsTurn Y.m Y.L Y.H (axOf hd e) (sgOf e) (latOf hd e) w' (legOf st.sT (brIdx Y a e w' ((legOf st.sT 0).b (axOf hd e)))) g.1 ∧
      |g.1.b (ax0 hd) - Y.zOf e| ≤ Y.ρv ∧ ∀ j, j ≠ axOf hd e → j ≠ latOf hd e → j ≠ ax0 hd → |g.1.b j| ≤ Y.Lp)
    {k : ℕ} (hk : k ≤ sB.length) :
    (w' : ℤ) * ((legOf (sB ++ [g]) k).b (latOf hd e) - Y.ctr (tgtCell a e) ⟨1 - e.1.val, by have := e.1.isLt; omega⟩) ≤
      Y.Dh - 1 - Y.ell := by
  obtain ⟨-, -, -, hell, hmH, -⟩ := hY.facts
  obtain ⟨-, -, -, -, -, -, hallR⟩ := all_length_lt Y hd hL hH a e τ hY hτ hI
  have hlenT : st.sT.length ≤ Y.Rmax := by
    have : st.sT.length ≤ st.all.length := by simp only [RS.all, List.length_append]; omega
    omega
  obtain ⟨h1len, -⟩ := branch_feasible Y hd hL hH a e τ hY hτ hI hlenT hg rfl
  obtain ⟨hbf, -, -, -⟩ := boundsB Y hd hL hH a e hB hg.2.1.axis hg.2.1.sign hk
  set nE := legLen Y a e (latDir e (decide ((w' : ℤ) = 1))) (g.1.b (latOf hd e)) with hnE
  have hsw : (sgOf (latDir e (decide ((w' : ℤ) = 1))) : ℤ) = w' := by
    rw [sgOf_latDir_val]; rcases Int.units_eq_one_or w' with h | h <;> simp [h]
  have hw2 : (w' : ℤ) * (w' : ℤ) = 1 := by rcases Int.units_eq_one_or w' with h | h <;> simp [h]
  have hl0 : (0 : ℤ) ≤ Y.ell := by linarith
  have hkE : k ≤ nE := by
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · exact Nat.zero_le _
    · have := hB.sched g rfl (k - 1) (by omega); omega
  have hroomE := not_of_lt_firstIdx
    (p := fun k => ¬roomT Y (tgtCell a e) (latDir e (decide ((w' : ℤ) = 1))) (g.1.b (latOf hd e) + (sgOf (latDir e (decide ((w' : ℤ) = 1))) : ℤ) * (k * Y.ell)))
    (N := Y.Rmax) (k := nE - 1) (by show nE - 1 < legLen Y a e _ (g.1.b (latOf hd e)); omega)
  simp only [not_not] at hroomE
  unfold roomT at hroomE
  rw [hsw] at hroomE
  have hctr : Y.ctr (tgtCell a e) (latDir e (decide ((w' : ℤ) = 1))).1 = Y.ctr (tgtCell a e) ⟨1 - e.1.val, by have := e.1.isLt; omega⟩ := rfl
  rw [hctr] at hroomE
  have hkE' : Y.ell * (k : ℤ) ≤ Y.ell * ((nE - 1 : ℕ) : ℤ) + Y.ell := by
    have : (k : ℤ) ≤ ((nE - 1 : ℕ) : ℤ) + 1 := by
      have h' : k ≤ nE - 1 + 1 := by omega
      exact_mod_cast h'
    nlinarith
  have e1 : (w' : ℤ) * (g.1.b (latOf hd e) + (w' : ℤ) * (((nE - 1 : ℕ) : ℤ) * Y.ell) + (w' : ℤ) * Y.ell - Y.ctr (tgtCell a e) ⟨1 - e.1.val, by have := e.1.isLt; omega⟩) =
      (w' : ℤ) * (g.1.b (latOf hd e) - Y.ctr (tgtCell a e) ⟨1 - e.1.val, by have := e.1.isLt; omega⟩) + ((w' : ℤ) * (w' : ℤ)) * (((nE - 1 : ℕ) : ℤ) * Y.ell + Y.ell) := by
    ring
  rw [e1, hw2] at hroomE
  rw [hbf]
  have e2 : (w' : ℤ) * (g.1.b (latOf hd e) + (w' : ℤ) * Y.ell * k - Y.ctr (tgtCell a e) ⟨1 - e.1.val, by have := e.1.isLt; omega⟩) =
      (w' : ℤ) * (g.1.b (latOf hd e) - Y.ctr (tgtCell a e) ⟨1 - e.1.val, by have := e.1.isLt; omega⟩) + ((w' : ℤ) * (w' : ℤ)) * (Y.ell * k) := by ring
  rw [e2, hw2]
  linarith only [hroomE, hkE']

/-- **The inequalities of the points of the boxes of a branch.** [cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
theorem boxOf_B_facts (hY : Y.OK) (hτ : TAdm hd Y a e τ) {st : RS d} (hI : TallInv hd Y hL hH a e τ st)
    {w' : ℤˣ} {g : BrickRec d} {sB : List (BrickRec d)} {D : Prop} (hB : InvB hd Y hL hH a e w' (some g) sB D)
    (hg : brIdx Y a e w' ((legOf st.sT 0).b (axOf hd e)) < st.sT.length ∧
      IsTurn Y.m Y.L Y.H (axOf hd e) (sgOf e) (latOf hd e) w' (legOf st.sT (brIdx Y a e w' ((legOf st.sT 0).b (axOf hd e)))) g.1 ∧
      |g.1.b (ax0 hd) - Y.zOf e| ≤ Y.ρv ∧ ∀ j, j ≠ axOf hd e → j ≠ latOf hd e → j ≠ ax0 hd → |g.1.b j| ≤ Y.Lp)
    {k : ℕ} (hk : k ≤ sB.length) {w : Site d} (hw : w ∈ boxOf Y.L Y.H (legOf (sB ++ [g]) k)) :
    (∀ j, j ≠ axOf hd e → j ≠ latOf hd e → j ≠ ax0 hd → |w j| ≤ 2 * Y.Lp + Y.K0) ∧
      -(2 * Y.Lp) - Y.K0 ≤ (sgOf e : ℤ) * (w (axOf hd e) - 2 * brLane Y a e w') ∧
      (sgOf e : ℤ) * (w (axOf hd e) - 2 * brLane Y a e w') ≤ 2 * Y.ell + 2 * Y.H + 2 * Y.Lp + Y.K0 ∧
      -(2 * Y.ell + 2 * Y.Lp + 8 * Y.Δw) ≤ (w' : ℤ) * (w (latOf hd e) - 2 * Y.lane (tgtCell a e) e) ∧
      (w' : ℤ) * (w (latOf hd e) - 2 * Y.ctr (tgtCell a e) ⟨1 - e.1.val, by have := e.1.isLt; omega⟩) ≤ 2 * Y.Dh - 2 ∧
      |w (ax0 hd) - 2 * Y.zOf e| ≤ 2 * Y.ρv + Y.K0 := by
  obtain ⟨hLp0, -, hLeq, hell, hmH, -⟩ := hY.facts
  have hK0 : Y.K0 = 2 * Y.L + 2 * Y.H + 2 := rfl
  have hs1 : (sgOf e : ℤ) = 1 ∨ (sgOf e : ℤ) = -1 := by rcases Int.units_eq_one_or (sgOf e) with h | h <;> simp [h]
  have hw1 : (w' : ℤ) = 1 ∨ (w' : ℤ) = -1 := by rcases Int.units_eq_one_or w' with h | h <;> simp [h]
  have hl0 : (0 : ℤ) ≤ Y.ell := by linarith
  obtain ⟨hNR, hNJ⟩ := sched_bounds Y hd hL hH a e τ hY hτ hI
  obtain ⟨-, -, -, -, -, -, hallR⟩ := all_length_lt Y hd hL hH a e τ hY hτ hI
  have hlenT : st.sT.length ≤ Y.Rmax := by
    have : st.sT.length ≤ st.all.length := by simp only [RS.all, List.length_append]; omega
    omega
  have hT : st.sT ≠ [] := List.ne_nil_of_length_pos (by omega)
  obtain ⟨-, -, hn1, -⟩ := trunk_feasible Y hd hL hH a e τ hY hτ hI hT
  have h12 := n1Of_le_n2Of Y hd a e st.sT
  have hn1' : 1 ≤ brIdx Y a e w' ((legOf st.sT 0).b (axOf hd e)) := by
    rcases Int.units_eq_one_or w' with rfl | rfl <;> rcases Int.units_eq_one_or (br1Sign e) with h | h
    · rw [← h]; exact hn1
    · have : -br1Sign e = 1 := by rw [h]; simp
      rw [← this]; exact hn1.trans h12
    · have : -br1Sign e = -1 := by rw [h]
      rw [← this]; exact hn1.trans h12
    · rw [← h]; exact hn1
  obtain ⟨hgax, hgs', hface, hTlat, hg0, hg1, -, -⟩ := boundsG Y hd hL hH a e τ hY hI hNR hNJ hlenT hg rfl hn1'
  obtain ⟨hbf, hlng, hht, hoth⟩ := boundsB Y hd hL hH a e hB hgax hgs' hk
  have hax : (legOf (sB ++ [g]) k).a = latOf hd e ∧ (legOf (sB ++ [g]) k).s = w' := by
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · rw [legOf_append_singleton_zero]; exact ⟨hgax, hgs'⟩
    · have hne : sB ≠ [] := List.ne_nil_of_length_pos (by omega)
      have := (hB.grown g rfl hne).axis_sign (k := k) (by simp; omega)
      rw [legOf_append_singleton_zero] at this; rw [this.1, this.2]; exact ⟨hgax, hgs'⟩
  have hcell := branch_in_cell Y hd hL hH a e τ hY hτ hI hB hg hk
  refine ⟨oth_of_bound Y hd e hK0 hw hoth, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨h3, h2⟩ := box_trans hw (i := axOf hd e) (by rw [hax.1]; exact (latOf_ne_axOf hd e).symm)
    have hl := abs_le.1 hlng
    rw [hK0]
    rcases hs1 with h | h <;> rw [h] at hg0 ⊢ <;> linarith only [hg0, hl.1, hl.2, h2, h3]
  · obtain ⟨h3, h2⟩ := box_trans hw (i := axOf hd e) (by rw [hax.1]; exact (latOf_ne_axOf hd e).symm)
    have hl := abs_le.1 hlng
    rw [hK0]
    rcases hs1 with h | h <;> rw [h] at hg1 ⊢ <;> linarith only [hg1, hl.1, hl.2, h2, h3]
  · obtain ⟨h1, -⟩ := box_axis hw
    rw [hax.1, hax.2, hbf, hface] at h1
    have hTl := abs_le.1 hTlat
    have hk0 : (0 : ℤ) ≤ Y.ell * k := by positivity
    rcases hw1 with h | h <;> rw [h] at h1 ⊢ <;> linarith only [h1, hTl.1, hTl.2, hk0, hLeq, hLp0]
  · obtain ⟨-, h2⟩ := box_axis hw
    rw [hax.1, hax.2] at h2
    rcases hw1 with h | h <;> rw [h] at h2 hcell ⊢ <;> linarith only [h2, hcell, hell]
  · have h := abs_le.1 hht
    obtain ⟨h3, h2⟩ := box_trans hw (i := ax0 hd) (by rw [hax.1]; exact (latOf_ne_ax0 hd e).symm)
    rw [hK0, abs_le]; constructor <;> linarith only [h.1, h.2, h2, h3]

/-- **Boxes of a branch brick and its leg lie in the region.** [cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
theorem boxOf_subset_zoneRegion_B (hY : Y.OK) (hτ : TAdm hd Y a e τ) {st : RS d} (hI : TallInv hd Y hL hH a e τ st)
    {w' : ℤˣ} {g : BrickRec d} {sB : List (BrickRec d)} {D : Prop} (hB : InvB hd Y hL hH a e w' (some g) sB D)
    (hg : brIdx Y a e w' ((legOf st.sT 0).b (axOf hd e)) < st.sT.length ∧
      IsTurn Y.m Y.L Y.H (axOf hd e) (sgOf e) (latOf hd e) w' (legOf st.sT (brIdx Y a e w' ((legOf st.sT 0).b (axOf hd e)))) g.1 ∧
      |g.1.b (ax0 hd) - Y.zOf e| ≤ Y.ρv ∧ ∀ j, j ≠ axOf hd e → j ≠ latOf hd e → j ≠ ax0 hd → |g.1.b j| ≤ Y.Lp)
    {k : ℕ} (hk : k ≤ sB.length) : boxOf Y.L Y.H (legOf (sB ++ [g]) k) ⊆ zoneRegion Y hd a e τ := by
  intro w hw
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := boxOf_B_facts Y hd hL hH a e τ hY hτ hI hB hg hk hw
  exact mem_zoneRegion_B Y hd a e τ h0 w' h1 h2 h3 h4 h5

/-- **The box of every recorded brick lies in the region.** [cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
theorem boxOf_subset_zoneRegion (hY : Y.OK) (hτ : TAdm hd Y a e τ) {st : RS d} (hI : TallInv hd Y hL hH a e τ st)
    {r : BrickRec d} (hr : r ∈ st.all) : boxOf Y.L Y.H r.1 ⊆ zoneRegion Y hd a e τ := by
  simp only [RS.all, List.mem_append] at hr
  -- branch records, by side
  have hside : ∀ (w' : ℤˣ) (go : Option (BrickRec d)) (sB : List (BrickRec d)) (D : Prop), InvB hd Y hL hH a e w' go sB D →
      (∀ g, go = some g → brIdx Y a e w' ((legOf st.sT 0).b (axOf hd e)) < st.sT.length ∧
        IsTurn Y.m Y.L Y.H (axOf hd e) (sgOf e) (latOf hd e) w' (legOf st.sT (brIdx Y a e w' ((legOf st.sT 0).b (axOf hd e)))) g.1 ∧
        |g.1.b (ax0 hd) - Y.zOf e| ≤ Y.ρv ∧ ∀ j, j ≠ axOf hd e → j ≠ latOf hd e → j ≠ ax0 hd → |g.1.b j| ≤ Y.Lp) →
      (r ∈ go.toList ∨ r ∈ sB) → boxOf Y.L Y.H r.1 ⊆ zoneRegion Y hd a e τ := by
    intro w' go sB D hB hgs hx
    obtain ⟨g, hgo⟩ : ∃ g, go = some g := by
      rcases hx with hx | hx
      · cases go with
        | none => exact absurd hx (by simp)
        | some g => exact ⟨g, rfl⟩
      · exact Option.ne_none_iff_exists'.1 (hB.prev (List.ne_nil_of_mem hx))
    subst hgo
    have hx' : r ∈ sB ++ [g] := by
      rcases hx with hx | hx
      · simp only [Option.toList_some, List.mem_singleton] at hx; subst hx; simp
      · exact List.mem_append_left _ hx
    obtain ⟨k, hk, rfl⟩ := exists_recOf_of_mem hx'
    exact boxOf_subset_zoneRegion_B Y hd hL hH a e τ hY hτ hI hB (hgs g rfl) (by simpa using hk)
  rcases hr with ((((((hr | hr) | hr) | hr) | hr) | hr) | hr) | hr
  · obtain ⟨k, hk, rfl⟩ := exists_recOf_of_mem hr; exact boxOf_subset_zoneRegion_A Y hd hL hH a e τ hY hτ hI hk
  · obtain ⟨k, hk, rfl⟩ := exists_recOf_of_mem hr; exact boxOf_subset_zoneRegion_R Y hd hL hH a e τ hY hτ hI hk
  · obtain ⟨k, hk, rfl⟩ := exists_recOf_of_mem hr; exact boxOf_subset_zoneRegion_J Y hd hL hH a e τ hY hτ hI hk
  · obtain ⟨k, hk, rfl⟩ := exists_recOf_of_mem hr; exact boxOf_subset_zoneRegion_T Y hd hL hH a e τ hY hτ hI hk
  · exact hside _ _ _ _ hI.invB1 (fun g hg => hI.invT.g1_some g hg) (Or.inl hr)
  · exact hside _ _ _ _ hI.invB2 (fun g hg => hI.invT.g2_some g hg) (Or.inl hr)
  · exact hside _ _ _ _ hI.invB1 (fun g hg => hI.invT.g1_some g hg) (Or.inr hr)
  · exact hside _ _ _ _ hI.invB2 (fun g hg => hI.invT.g2_some g hg) (Or.inr hr)

/-! ## The zone as a finite set of edges -/

/-- The reference point of the zone: the centre of the target cell in the plane, `0` elsewhere. [folklore] -/
def zoneCentre : Site d := fun i =>
  if i = axOf hd e then Y.ctr (tgtCell a e) e.1
  else if i = latOf hd e then Y.ctr (tgtCell a e) ⟨1 - e.1.val, by have := e.1.isLt; omega⟩ else 0

/-- The radius of the vertex box of the zone, `4 · D/2`. [folklore] -/
def zoneRad (Y : TallLayout) : ℕ := 2 ^ 12 * Y.P ^ 3 * Y.ell

omit [NeZero d] in
/-- The radius in `ℤ`. [folklore] -/
theorem zoneRad_eq (Y : TallLayout) : ((zoneRad Y : ℕ) : ℤ) = 4 * Y.Dh := by
  unfold zoneRad TallLayout.Dh; push_cast; ring

/-- The vertex box of the zone. [folklore] -/
def vbox : Finset (Site d) := (box d (zoneRad Y)).image fun x => x + zoneCentre Y hd a e

/-- **The zone**: the lattice edges with both endpoints in the vertex box and doubled midpoint in the
region. [cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
def zoneF : Finset (Sym2 (Site d)) := (edgesIn (zdGraph d) (vbox Y hd a e)).filter fun z => dmid z ∈ zoneRegion Y hd a e τ

omit [NeZero d] in
/-- Membership in the zone. [folklore] -/
theorem mem_zoneF {z : Sym2 (Site d)} :
    z ∈ zoneF Y hd a e τ ↔ z ∈ (zdGraph d).edgeSet ∧ (∀ x ∈ z, x ∈ vbox Y hd a e) ∧ dmid z ∈ zoneRegion Y hd a e τ := by
  unfold zoneF; rw [Finset.mem_filter, mem_edgesIn_iff, and_assoc]

omit [NeZero d] in
/-- The region is bounded along `e`. [folklore] -/
theorem zoneRegion_bound_e (hY : Y.OK) (hτ : TAdm hd Y a e τ) {w : Site d} (hw : w ∈ zoneRegion Y hd a e τ) :
    |w (axOf hd e) - 2 * Y.ctr (tgtCell a e) e.1| ≤ 2 * (4 * Y.Dh) - 2 := by
  obtain ⟨hLp0, hLpP, hLeq, hell, hmH, -, -, -, hΔ0, -, -, hlam, hlamJ, -, hDh, -, hPe, hP2, hP3, hNL, hP32, hP64, hPwe, -⟩ := hY.facts
  have hK0 : Y.K0 = 2 * Y.L + 2 * Y.H + 2 := rfl
  obtain ⟨-, hcases⟩ := hw
  have hτe := hτ.longit
  have hc := ctr_tgtCell_fst Y a e
  have hs1 : (sgOf e : ℤ) = 1 ∨ (sgOf e : ℤ) = -1 := by rcases Int.units_eq_one_or (sgOf e) with h | h <;> simp [h]
  have hDh0 : 0 ≤ Y.Dh := by rw [hDh]; positivity
  have hl0 : (0 : ℤ) ≤ Y.ell := by linarith only [hell, hmH]
  have hm0 : (0 : ℤ) ≤ Y.m := by positivity
  have hN0 : (0 : ℤ) ≤ Y.N₁ * Y.Lp := by positivity
  -- everything small is at most `D/2`
  have hsmall : 2 * Y.Pw * Y.ell + 2 * Y.H + 4 * Y.N₁ * Y.Lp + 2 * Y.ell + 2 * Y.Lp + Y.K0 + 2 * Y.L + Y.lam + Y.lamJ + 3 ≤ Y.Dh := by
    rw [hK0]; linarith only [hDh, hPwe, hNL, hlam, hlamJ, hLeq, hLpP, hP3, hP2, hPe, hP64, hP32, hell, hmH, hLp0]
  have hbig : 2 * Y.ell + 2 ≤ Y.Dh := by linarith only [hDh, hP3, hP2, hPe, hP64, hell, hmH]
  -- the token's plane relative to the target centre
  have hp : |τ.pos (axOf hd e) - Y.ctr (tgtCell a e) e.1| ≤ Y.Dh + Y.ell := by
    rw [hc, abs_le]
    rcases hs1 with h | h <;> rw [h] at hτe ⊢ <;> constructor <;> linarith only [hτe.1, hτe.2, hDh0]
  have hp' := abs_le.1 hp
  -- the lanes relative to the target centre
  have hlane : ∀ w' : ℤˣ, |brLane Y a e w' - Y.ctr (tgtCell a e) e.1| ≤ Y.lam + Y.lamJ := by
    intro w'
    rw [brLane_eq]
    have hlam0 : 0 ≤ Y.lam := by rw [hlam]; positivity
    have hlamJ0 : 0 ≤ Y.lamJ := by rw [hlamJ]; positivity
    have hpar : TallLayout.cpar (tgtCell a e) = 0 ∨ TallLayout.cpar (tgtCell a e) = 1 := by unfold TallLayout.cpar; omega
    rcases hpar with hq | hq <;> rw [hq] <;> split_ifs <;> rw [abs_le] <;> constructor <;> linarith only [hlam0, hlamJ0]
  -- reduce every case to `|s (w - 2 ref)| ≤ 3 D/2` with `|ref - X| ≤ D/2 + ℓ`
  have key : ∀ ref : ℤ, |τ.pos (axOf hd e) - ref| = 0 ∨ |brLane Y a e 1 - ref| = 0 ∨ |brLane Y a e (-1) - ref| = 0 →
      |ref - Y.ctr (tgtCell a e) e.1| ≤ Y.Dh + Y.ell := by
    intro ref href
    rcases href with h | h | h <;> rw [abs_eq_zero, sub_eq_zero] at h <;> rw [← h]
    · exact hp
    · have := abs_le.1 (hlane 1); rw [abs_le]; constructor <;> linarith only [this.1, this.2, hsmall, hK0, hl0, hm0, hN0, hLp0, hLeq, hPwe, hPe]
    · have := abs_le.1 (hlane (-1)); rw [abs_le]; constructor <;> linarith only [this.1, this.2, hsmall, hK0, hl0, hm0, hN0, hLp0, hLeq, hPwe, hPe]
  have finish : ∀ ref : ℤ, |ref - Y.ctr (tgtCell a e) e.1| ≤ Y.Dh + Y.ell →
      -(3 * Y.Dh) ≤ (sgOf e : ℤ) * (w (axOf hd e) - 2 * ref) → (sgOf e : ℤ) * (w (axOf hd e) - 2 * ref) ≤ 3 * Y.Dh →
      |w (axOf hd e) - 2 * Y.ctr (tgtCell a e) e.1| ≤ 2 * (4 * Y.Dh) - 2 := by
    intro ref href hlo hhi
    have hr := abs_le.1 href
    rw [abs_le]
    rcases hs1 with h | h <;> rw [h] at hlo hhi <;> constructor <;> linarith only [hlo, hhi, hr.1, hr.2, hbig, hDh0]
  have hlam0 : 0 ≤ Y.lam := by rw [hlam]; positivity
  have hlamJ0 : 0 ≤ Y.lamJ := by rw [hlamJ]; positivity
  rcases hcases with ⟨h1, h2, -, -⟩ | ⟨h1, h2, -, -, -⟩ | ⟨h1, h2, -, -, -⟩ | ⟨h1, h2, -, -⟩ | ⟨w', h1, h2, -, -, -⟩
  · exact finish (τ.pos (axOf hd e)) hp (by linarith only [h1, hDh0])
      (by linarith only [h2, hsmall, hK0, hl0, hm0, hN0, hLp0, hLeq, hlam0, hlamJ0, hPwe, hPe])
  · exact finish (τ.pos (axOf hd e)) hp
      (by linarith only [h1, hsmall, hK0, hl0, hm0, hN0, hLp0, hLeq, hPwe, hPe, hlam0, hlamJ0, hDh0])
      (by linarith only [h2, hsmall, hK0, hl0, hm0, hN0, hLp0, hLeq, hlam0, hlamJ0, hPwe, hPe])
  · exact finish (τ.pos (axOf hd e)) hp
      (by linarith only [h1, hsmall, hK0, hl0, hm0, hN0, hLp0, hLeq, hPwe, hPe, hlam0, hlamJ0, hDh0])
      (by linarith only [h2, hsmall, hK0, hl0, hm0, hN0, hLp0, hLeq, hlam0, hlamJ0, hPwe, hPe])
  · -- the trunk
    rw [abs_le]
    rcases hs1 with h | h <;> rw [h] at h1 h2 <;> constructor <;>
      linarith only [h1, h2, hp'.1, hp'.2, hDh0, hbig, hl0, hm0, hLeq, hLp0, hPwe, hPe]
  · have hw' : w' = 1 ∨ w' = -1 := Int.units_eq_one_or w'
    have hkey : |brLane Y a e w' - Y.ctr (tgtCell a e) e.1| ≤ Y.Dh + Y.ell := by
      rcases hw' with rfl | rfl
      · exact key _ (Or.inr (Or.inl (by simp)))
      · exact key _ (Or.inr (Or.inr (by simp)))
    exact finish (brLane Y a e w') hkey
      (by linarith only [h1, hsmall, hK0, hl0, hm0, hN0, hLp0, hLeq, hPwe, hPe, hlam0, hlamJ0, hDh0])
      (by linarith only [h2, hsmall, hK0, hl0, hm0, hN0, hLp0, hLeq, hlam0, hlamJ0, hPwe, hPe, hDh0])

omit [NeZero d] in
/-- The region is bounded laterally. [folklore] -/
theorem zoneRegion_bound_f (hY : Y.OK) (hτ : TAdm hd Y a e τ) {w : Site d} (hw : w ∈ zoneRegion Y hd a e τ) :
    |w (latOf hd e) - 2 * Y.ctr (tgtCell a e) ⟨1 - e.1.val, by have := e.1.isLt; omega⟩| ≤ 2 * (4 * Y.Dh) - 2 := by
  obtain ⟨hLp0, hLpP, hLeq, hell, hmH, -, -, hΔw, hΔ0, -, hρp, hlam, hlamJ, -, hDh, -, hPe, hP2, hP3, -, hP32, hP64, -, -⟩ := hY.facts
  have hK0 : Y.K0 = 2 * Y.L + 2 * Y.H + 2 := rfl
  obtain ⟨-, hcases⟩ := hw
  set Xf := Y.ctr (tgtCell a e) ⟨1 - e.1.val, by have := e.1.isLt; omega⟩ with hXf
  have hDh0 : 0 ≤ Y.Dh := by rw [hDh]; positivity
  have hl0 : (0 : ℤ) ≤ Y.ell := by linarith only [hell, hmH]
  have hm0 : (0 : ℤ) ≤ Y.m := by positivity
  have hlam0 : 0 ≤ Y.lam := by rw [hlam]; positivity
  have hlamJ0 : 0 ≤ Y.lamJ := by rw [hlamJ]; positivity
  have hτl := abs_le.1 hτ.lateral
  have hy : Y.lane (tgtCell a e) e = Y.lane a e + (jogDir a e : ℤ) * Y.lamJ := lane_tgtCell Y a e
  have hla : |Y.lane a e - Xf| ≤ Y.lam + Y.lamJ := by
    rw [hXf]; unfold TallLayout.lane
    rw [← ctr_tgtCell_snd Y a e]
    have hpar : TallLayout.cpar a = 0 ∨ TallLayout.cpar a = 1 := by unfold TallLayout.cpar; omega
    unfold TallLayout.nu
    rcases hpar with hq | hq <;> rw [hq] <;> split_ifs <;> rw [abs_le] <;> constructor <;> linarith only [hlam0, hlamJ0]
  have hla' := abs_le.1 hla
  have hv1 : (jogDir a e : ℤ) = 1 ∨ (jogDir a e : ℤ) = -1 := by rcases Int.units_eq_one_or (jogDir a e) with h | h <;> simp [h]
  have hp : |τ.pos (latOf hd e) - Xf| ≤ Y.ρp + Y.lam + Y.lamJ := by
    rw [abs_le]; constructor <;> linarith only [hτl.1, hτl.2, hla'.1, hla'.2]
  have hyb : |Y.lane (tgtCell a e) e - Xf| ≤ Y.lam + 2 * Y.lamJ := by
    rw [hy, abs_le]; rcases hv1 with h | h <;> rw [h] <;> constructor <;> linarith only [hla'.1, hla'.2, hlamJ0]
  have hp' := abs_le.1 hp
  have hyb' := abs_le.1 hyb
  -- everything small is at most `D/2`
  have hsmall : 2 * Y.ρp + 4 * Y.lam + 4 * Y.lamJ + 2 * Y.Lp + 10 * Y.Δw + Y.K0 + 2 * Y.ell + 2 * Y.m + 2 * Y.H + 8 ≤ Y.Dh := by
    rw [hK0]; linarith only [hDh, hρp, hΔw, hlam, hlamJ, hLeq, hLpP, hP3, hP2, hPe, hP64, hP32, hell, hmH, hLp0]
  rcases hcases with ⟨-, -, h3, -⟩ | ⟨-, -, h3, -, -⟩ | ⟨-, -, h3, h4, -⟩ | ⟨-, -, h3, -⟩ | ⟨w', -, -, h3, h4, -⟩
  · have h := abs_le.1 h3
    rw [abs_le]; constructor <;> linarith only [h.1, h.2, hp'.1, hp'.2, hsmall, hDh0, hlamJ0, hlam0, hΔ0, hl0, hm0, hLp0, hK0, hLeq, hρp]
  · have h := abs_le.1 h3
    rw [abs_le]; constructor <;> linarith only [h.1, h.2, hp'.1, hp'.2, hsmall, hDh0, hlamJ0, hlam0, hΔ0, hl0, hm0, hLp0, hK0, hLeq, hρp]
  · rcases hv1 with h | h <;> rw [h] at h3 h4 <;> rw [abs_le] <;> constructor <;>
      linarith only [h3, h4, hp'.1, hp'.2, hyb'.1, hyb'.2, hsmall, hDh0, hlamJ0, hlam0, hΔ0, hl0, hm0, hLp0, hK0, hLeq, hρp]
  · have h := abs_le.1 h3
    rw [abs_le]; constructor <;> linarith only [h.1, h.2, hyb'.1, hyb'.2, hsmall, hDh0, hlamJ0, hlam0, hΔ0, hl0, hm0, hLp0, hK0, hLeq, hρp]
  · have hw1 : (w' : ℤ) = 1 ∨ (w' : ℤ) = -1 := by rcases Int.units_eq_one_or w' with h | h <;> simp [h]
    rcases hw1 with h | h <;> rw [h] at h3 h4 <;> rw [abs_le] <;> constructor <;>
      linarith only [h3, h4, hyb'.1, hyb'.2, hsmall, hDh0, hlamJ0, hlam0, hΔ0, hl0, hm0, hLp0, hK0, hLeq, hρp]

omit [NeZero d] in
/-- The region is bounded vertically and in the remaining coordinates. [folklore] -/
theorem zoneRegion_bound_0 (hY : Y.OK) {w : Site d} (hw : w ∈ zoneRegion Y hd a e τ) {i : Fin d} (hie : i ≠ axOf hd e)
    (hif : i ≠ latOf hd e) : |w i| ≤ 2 * (4 * Y.Dh) - 2 := by
  obtain ⟨hLp0, hLpP, hLeq, hell, hmH, -, -, hΔw, hΔ0, hρv, -, -, -, hWl, hDh, -, hPe, hP2, hP3, -, hP32, hP64, -, -⟩ := hY.facts
  have hK0 : Y.K0 = 2 * Y.L + 2 * Y.H + 2 := rfl
  have hCv : Y.Cv = 2 * Y.ρv + 2 * Y.Δw + 2 * Y.m + 2 * Y.H + 4 := rfl
  obtain ⟨hoth, hcases⟩ := hw
  have hl0 : (0 : ℤ) ≤ Y.ell := by linarith only [hell, hmH]
  have hm0 : (0 : ℤ) ≤ Y.m := by positivity
  have hW0 : 0 ≤ Y.Wl := by rw [hWl]; positivity
  have hρv0 : 0 ≤ Y.ρv := by rw [hρv]; linarith only [hl0, hLp0]
  have hsmall : 6 * Y.Wl + Y.Cv + 2 * Y.ρv + 2 * Y.Δw + Y.K0 + 2 * Y.Lp + 2 ≤ 2 * (4 * Y.Dh) := by
    rw [hK0, hCv]; linarith only [hDh, hWl, hρv, hΔw, hLeq, hLpP, hP3, hP2, hPe, hP64, hP32, hell, hmH, hLp0]
  by_cases hi0 : i = ax0 hd
  · subst hi0
    have hz : ∀ e' : MDir, 0 ≤ Y.zOf e' ∧ Y.zOf e' ≤ 3 * Y.Wl := by
      intro e'
      have h3 : TallLayout.layerIdx e' ≤ 3 := by unfold TallLayout.layerIdx; have := e'.1.isLt; split_ifs <;> omega
      unfold TallLayout.zOf
      constructor
      · positivity
      · have : (TallLayout.layerIdx e' : ℤ) ≤ 3 := by exact_mod_cast h3
        nlinarith
    have hze := hz e
    have hzs := hz (τ.src.getD e)
    have hmin : 0 ≤ min (Y.zOf (τ.src.getD e)) (Y.zOf e) := le_min hzs.1 hze.1
    have hmax : max (Y.zOf (τ.src.getD e)) (Y.zOf e) ≤ 3 * Y.Wl := max_le hzs.2 hze.2
    rcases hcases with ⟨-, -, -, h4⟩ | ⟨-, -, -, h4, h5⟩ | ⟨-, -, -, -, h4⟩ | ⟨-, -, -, h4⟩ | ⟨w', -, -, -, -, h4⟩
    · have h := abs_le.1 h4
      rw [abs_le]; constructor <;> linarith only [h.1, h.2, hzs.1, hzs.2, hsmall, hCv, hρv0, hΔ0, hLp0, hm0, hl0, hell, hK0, hLeq]
    · rw [abs_le]; constructor <;> linarith only [h4, h5, hmin, hmax, hsmall, hρv0, hΔ0, hLp0, hK0, hLeq, hm0, hl0, hell, hW0]
    · have h := abs_le.1 h4
      rw [abs_le]; constructor <;> linarith only [h.1, h.2, hze.1, hze.2, hsmall, hCv, hρv0, hΔ0, hLp0, hm0, hl0, hell, hK0, hLeq]
    · have h := abs_le.1 h4
      rw [abs_le]; constructor <;> linarith only [h.1, h.2, hze.1, hze.2, hsmall, hCv, hρv0, hΔ0, hLp0, hm0, hl0, hell, hK0, hLeq]
    · have h := abs_le.1 h4
      rw [abs_le]; constructor <;> linarith only [h.1, h.2, hze.1, hze.2, hsmall, hCv, hρv0, hΔ0, hLp0, hm0, hl0, hell, hK0, hLeq]
  · have h := abs_le.1 (hoth i hie hif hi0)
    have hCv0 : 0 ≤ Y.Cv := by rw [hCv]; linarith only [hρv0, hΔ0, hm0, hl0, hell]
    rw [abs_le]; constructor <;> linarith only [h.1, h.2, hsmall, hW0, hCv0, hρv0, hΔ0]

omit [NeZero d] in
/-- **The region lies well inside the doubled vertex box**: every coordinate of a point of the region
is within `8 · D/2 - 2` of twice the reference point. [folklore] -/
theorem zoneRegion_bound (hY : Y.OK) (hτ : TAdm hd Y a e τ) {w : Site d} (hw : w ∈ zoneRegion Y hd a e τ) (i : Fin d) :
    |w i - 2 * zoneCentre Y hd a e i| ≤ 2 * (4 * Y.Dh) - 2 := by
  unfold zoneCentre
  by_cases hie : i = axOf hd e
  · subst hie; rw [if_pos rfl]; exact zoneRegion_bound_e Y hd a e τ hY hτ hw
  by_cases hif : i = latOf hd e
  · subst hif; rw [if_neg hie, if_pos rfl]; exact zoneRegion_bound_f Y hd a e τ hY hτ hw
  · rw [if_neg hie, if_neg hif, mul_zero, sub_zero]; exact zoneRegion_bound_0 Y hd a e τ hY hw hie hif

/-- **A placed brick whose box lies in the region has its support in the zone.**
[cite: GrimmettPercolation1999, §7.3 p. 173 (C)] -/
theorem suppP_subset_zoneF (hY : Y.OK) (hτ : TAdm hd Y a e τ) {β : BrickPos d} (hβ : boxOf Y.L Y.H β ⊆ zoneRegion Y hd a e τ) :
    suppP Y.m Y.L Y.H β ⊆ zoneF Y hd a e τ := by
  intro z hz
  have hL1 : 1 ≤ Y.L := by have := hY.hL; omega
  have hzE : z ∈ (zdGraph d).edgeSet := suppP_subset_edgeSet hL1 β hz
  have hdm : dmid z ∈ zoneRegion Y hd a e τ := hβ (dmid_mem_boxOf_of_mem_suppP hY.hL hY.hH β hz)
  rw [mem_zoneF]
  refine ⟨hzE, fun x hx => ?_, hdm⟩
  unfold vbox
  rw [Finset.mem_image]
  refine ⟨x - zoneCentre Y hd a e, ?_, sub_add_cancel _ _⟩
  rw [mem_box]
  intro i
  have h1 := abs_le.1 (abs_two_mul_sub_dmid_le hzE hx i)
  have h2 := abs_le.1 (zoneRegion_bound Y hd a e τ hY hτ hdm i)
  rw [Pi.sub_apply, zoneRad_eq]
  constructor <;> linarith

end Containment

end BGNd

end Percolation.Literature

end
