import Percolation.Literature.KozmaNitzanScheme
import Percolation.Util.Linter

/-!
# Kozma–Nitzan, Theorem 6 — the geometry of Steps II–IV: reaching `M_x`, crossing the faces, the target

Ninth proofs-only companion of
`KozmaNitzanReduction.lean` (G. Kozma, S. Nitzan, arXiv:2401.12397, §4), the three deterministic
ingredients of the supercriticality bound (33) for the examination of `v` from `w` along an onward
direction `x = v + du`, after a valid history (`KozmaNitzanScheme.lean`):

* `exists_face_prefix` — "to hit `M_x` via `H_{v,x}` you must pass through all the `F^j_{v,x}`"
  (p. 31): an open path inside `E_i ∪ E_{w,v} ∪ H_{v,x}` from `0` to a vertex of `E_{v,x}` beyond
  the level of `F^j` has an initial segment inside `E_i ∪ E_{w,v} ∪ H^j` ending ON `F^j` (the
  explored region is separated from `E_{v,x}`: `Cells.cover_sep_Efar`);
* `cond_of_face` — Step III (p. 30): if `F^{j+1}` is reached with probability `> 1 - δ₂` under the
  weighting of level `j` then the connection is good at level `j`, by the target lemma (fed as a
  hypothesis, with the elongated geometries of aspect `2K`) with `D = E_{v,x} \ E^j_{v,x}`,
  `B = F^{j+1}_{v,x}`, `T = M_x`, `ℓ(u) = ⌊(15r - 10r(j+1)/K)/2K⌋`.

## References

* G. Kozma, S. Nitzan, arXiv:2401.12397 (2024), §4 pp. 29–31 (Steps II–IV), Lemma 12 p. 23.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

namespace Percolation.Literature

open LatticeModels SimpleGraph GadgetSystem ProbeHistory Contour

namespace KozmaNitzan

variable {d : ℕ}

/-! ## More static geometry -/

/-- Two vertices differing in two distinct coordinates are neither equal nor adjacent. [folklore] -/
theorem sep_of_two_gaps {y z : Site d} {i i' : Fin d} (hii' : i ≠ i') (hi : y i ≠ z i) (hi' : y i' ≠ z i') :
    y ≠ z ∧ ¬(zdGraph d).Adj y z := by
  refine ⟨fun h => hi (by rw [h]), fun hadj => ?_⟩
  obtain ⟨k, τ, -, rfl⟩ := adj_iff_exists_sign.1 hadj
  by_cases hk : i = k
  · subst hk
    apply hi'; rw [add_smul_unitVec_apply, if_neg (Ne.symm hii')]; simp
  · apply hi; rw [add_smul_unitVec_apply, if_neg hk]; simp

/-- A two-sided bound on `σ z` is a two-sided bound on `z`. [folklore] -/
theorem abs_bounds_of_level {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) {z n : ℤ} (h1 : -n ≤ σ * z) (h2 : σ * z ≤ n) :
    -n ≤ z ∧ z ≤ n := by
  rcases hσ with rfl | rfl <;> constructor <;> linarith

namespace Cells

variable (C : Cells d)

/-- Membership in `Q_v` in terms of the level along `δ` and the transverse coordinates. [folklore] -/
theorem level_of_mem_Q {v : Site 2} {δ : MDir} {y : Site d} (hy : y ∈ C.Q v) :
    (-(5 * C.r : ℤ) ≤ sgOf δ * (y (C.axOf δ) - C.cen v (C.axOf δ)) ∧ sgOf δ * (y (C.axOf δ) - C.cen v (C.axOf δ)) ≤ 5 * C.r) ∧
      ∀ j, C.cen v j - 5 * C.r ≤ y j ∧ y j ≤ C.cen v j + 5 * C.r := by
  rw [Q, mem_cIcc_iff] at hy
  push_cast at hy
  refine ⟨?_, hy⟩
  have := hy (C.axOf δ)
  exact level_bounds_of_abs_le (sgOf_sign δ) (x := C.cen v (C.axOf δ)) (y := y (C.axOf δ)) (ℓ := 5 * C.r)
    (by linarith) (by linarith) |> fun h => by
      have e : sgOf δ * (y (C.axOf δ) - C.cen v (C.axOf δ)) = sgOf δ * y (C.axOf δ) - sgOf δ * C.cen v (C.axOf δ) := by ring
      rw [e]; constructor <;> linarith [h.1, h.2]

/-- `M_x ⊆ E_{v,x}` with levels in `[17r, 23r]`, `x = v + δ`. [folklore] -/
theorem level_of_mem_M_tgt {v : Site 2} {δ : MDir} {y : Site d} (hy : y ∈ C.M (v + stepVec δ)) :
    (17 * (C.r : ℤ) ≤ sgOf δ * (y (C.axOf δ) - C.cen v (C.axOf δ)) ∧ sgOf δ * (y (C.axOf δ) - C.cen v (C.axOf δ)) ≤ 23 * C.r) ∧
      ∀ j, j ≠ C.axOf δ → C.cen v j - 3 * C.r ≤ y j ∧ y j ≤ C.cen v j + 3 * C.r := by
  rw [M, mem_cIcc_iff] at hy
  push_cast at hy
  refine ⟨?_, fun j hj => ?_⟩
  · have := hy (C.axOf δ)
    rw [C.cen_add_stepVec, if_pos rfl] at this
    have hsq := sign_mul_self (sgOf_sign δ)
    rcases sgOf_sign δ with h | h <;> rw [h] at this ⊢ <;> constructor <;> linarith [this.1, this.2]
  · have := hy j
    rw [C.cen_add_stepVec, if_neg hj] at this
    exact this

/-- `M_x ⊆ E_{v,x}`. [folklore] -/
theorem M_tgt_subset_Efar (v : Site 2) (δ : MDir) : C.M (v + stepVec δ) ⊆ C.Efar v δ := by
  intro y hy
  have hr : (1 : ℤ) ≤ C.r := by exact_mod_cast C.r_pos
  obtain ⟨hl, ht⟩ := C.level_of_mem_M_tgt hy
  rw [Efar, mem_sBox_iff (sgOf_sign δ)]
  refine ⟨⟨by linarith [hl.1], by linarith [hl.2]⟩, fun j hj => ?_⟩
  have := ht j hj; constructor <;> linarith [this.1, this.2]

/-- The subbox `bigD` is `Q_v ∪ E_{v,x}` (as far as membership goes). [folklore] -/
theorem mem_Q_or_Efar_of_mem_bigD {v : Site 2} {δ : MDir} {y : Site d} (hy : y ∈ C.bigD v δ) :
    y ∈ C.Q v ∨ y ∈ C.Efar v δ := by
  rw [bigD, mem_sBox_iff (sgOf_sign δ)] at hy
  obtain ⟨hl, ht⟩ := hy
  by_cases hlev : sgOf δ * (y (C.axOf δ) - C.cen v (C.axOf δ)) ≤ 5 * C.r
  · left
    rw [Q, mem_cIcc_iff]
    push_cast
    intro i
    by_cases hi : i = C.axOf δ
    · subst hi
      have := abs_bounds_of_level (sgOf_sign δ) (z := y (C.axOf δ) - C.cen v (C.axOf δ)) (n := 5 * C.r) hl.1 hlev
      constructor <;> linarith [this.1, this.2]
    · exact ht i hi
  · right
    rw [Efar, mem_sBox_iff (sgOf_sign δ)]
    push Not at hlev
    exact ⟨⟨by linarith, hl.2⟩, ht⟩

/-- `Q_v` and `E_{v,x}` are disjoint (levels `≤ 5r` versus `> 5r`). [folklore] -/
theorem Q_disjoint_Efar {v : Site 2} {δ : MDir} {y : Site d} (hy : y ∈ C.Q v) : y ∉ C.Efar v δ := by
  intro hy'
  obtain ⟨hl, -⟩ := C.level_of_mem_Q (δ := δ) hy
  rw [Efar, mem_sBox_iff (sgOf_sign δ)] at hy'
  linarith [hy'.1.1, hl.2]

/-- The sign of the reversed direction. [folklore] -/
theorem sgOf_rev (δ : MDir) : sgOf (rev δ) = -sgOf δ := by
  unfold sgOf rev; cases δ.2 <;> simp

/-- The axis of the reversed direction. [folklore] -/
theorem axOf_rev (δ : MDir) : C.axOf (rev δ) = C.axOf δ := rfl

/-- **The between-box of a directed macro-edge equals that of the reversed edge.** [folklore] -/
theorem Btw_rev (v : Site 2) (δ : MDir) : C.Btw (v + stepVec δ) (rev δ) = C.Btw v δ := by
  ext y
  rw [Btw, Btw, C.axOf_rev δ, mem_sBox_iff (sgOf_sign (rev δ)), mem_sBox_iff (sgOf_sign δ), sgOf_rev]
  have hca : C.cen (v + stepVec δ) (C.axOf δ) = C.cen v (C.axOf δ) + 20 * C.r * sgOf δ := by
    rw [C.cen_add_stepVec, if_pos rfl]
  have hct : ∀ j, j ≠ C.axOf δ → C.cen (v + stepVec δ) j = C.cen v j := fun j hj => by
    rw [C.cen_add_stepVec, if_neg hj]
  have hsq := sign_mul_self (sgOf_sign δ)
  constructor
  · rintro ⟨hl, ht⟩
    rw [hca] at hl
    refine ⟨?_, fun j hj => by rw [← hct j hj]; exact ht j hj⟩
    constructor <;> nlinarith [hl.1, hl.2]
  · rintro ⟨hl, ht⟩
    rw [hca]
    refine ⟨?_, fun j hj => by rw [hct j hj]; exact ht j hj⟩
    constructor <;> nlinarith [hl.1, hl.2]

/-- **A between-box out of `v` is separated from `E_{v,x}` in another direction.** [folklore] -/
theorem Btw_sep_Efar {v : Site 2} {δ δ' : MDir} (hne : δ' ≠ δ) : Sep (↑(C.Btw v δ') : Set (Site d)) ↑(C.Efar v δ) := by
  intro y hy z hz
  have hr : (1 : ℤ) ≤ C.r := by exact_mod_cast C.r_pos
  rw [Finset.mem_coe, Btw, mem_sBox_iff (sgOf_sign δ')] at hy
  rw [Finset.mem_coe, Efar, mem_sBox_iff (sgOf_sign δ)] at hz
  obtain ⟨hyl, hyt⟩ := hy
  obtain ⟨hzl, hzt⟩ := hz
  by_cases hax : δ'.1 = δ.1
  · -- opposite directions along the same axis
    have haxOf : C.axOf δ' = C.axOf δ := by unfold axOf; rw [hax]
    have hsg : sgOf δ' = -sgOf δ := by
      have hne2 : δ'.2 ≠ δ.2 := fun h2 => hne (Prod.ext hax h2)
      unfold sgOf; cases h1 : δ'.2 <;> cases h2 : δ.2 <;> simp_all
    rw [haxOf, hsg] at hyl
    refine sep_of_gap (C.axOf δ) ?_
    rcases sgOf_sign δ with h | h <;> rw [h] at hyl hzl
    · left; linarith [hyl.1, hzl.1]
    · right; linarith [hyl.1, hzl.1]
  · -- perpendicular directions: two coordinates differ
    have hne' : C.axOf δ' ≠ C.axOf δ := fun h => hax (C.pax_injective h)
    have h1 := hyt (C.axOf δ) (Ne.symm hne')   -- `|y_a - c_a| ≤ 5r`
    have h2 := hzt (C.axOf δ') hne'             -- `|z_{a'} - c_{a'}| ≤ 5r`
    refine sep_of_two_gaps hne' (fun heq => ?_) (fun heq => ?_)
    · -- along `a'`: `y` has level `≥ 5r+1`, `z` is within `5r`
      rw [heq] at hyl
      rcases sgOf_sign δ' with h | h <;> rw [h] at hyl <;> linarith [hyl.1, h2.1, h2.2]
    · rw [← heq] at hzl
      rcases sgOf_sign δ with h | h <;> rw [h] at hzl <;> linarith [hzl.1, h1.1, h1.2]

/-- `E_{w,v} ∩ E_{v,x} = ∅` when `x ≠ w`: with `v = w + δw`, `x = v + du`, `du ≠ rev δw`. [folklore] -/
theorem Ewv_disjoint_Efar {w : Site 2} {δw du : MDir} (hne : du ≠ rev δw) {y : Site d}
    (hy : y ∈ C.Ewv w δw) : y ∉ C.Efar (w + stepVec δw) du := by
  rcases Finset.mem_union.1 hy with hy | hy
  · rw [← C.Btw_rev] at hy
    exact (C.Btw_sep_Efar (v := w + stepVec δw) (Ne.symm hne)).not_mem (Finset.mem_coe.2 hy) ∘ Finset.mem_coe.2
  · exact C.Q_disjoint_Efar hy

/-- Stubs, corridors and faces lie in `Q_v ∪ E_{v,x}` (levels `[5r, 15r]`, `[5r, 22r]`): a point of
level `≥ 5r + 1` of them is in `E_{v,x}`, a point of level `5r` in `Q_v`. Here for the corridor.
[folklore] -/
theorem mem_Q_or_Efar_of_mem_Hfull {v : Site 2} {δ : MDir} {y : Site d} (hy : y ∈ C.Hfull v δ) :
    y ∈ C.Q v ∨ y ∈ C.Efar v δ := by
  refine C.mem_Q_or_Efar_of_mem_bigD (sBox_mono (sgOf_sign δ) _ ?_ ?_ ?_ hy)
  · have : (0 : ℤ) ≤ C.r := by positivity
    linarith
  · linarith
  · linarith

/-- Stubs of level `≤ K` lie in the corridor. [folklore] -/
theorem Stub_subset_Hfull (v : Site 2) (δ : MDir) {j : ℕ} (hj : j ≤ C.K) : C.Stub v δ j ⊆ C.Hfull v δ := by
  refine sBox_mono (sgOf_sign δ) _ le_rfl ?_ le_rfl
  have h1 : 10 * (C.s : ℤ) * j ≤ 10 * C.s * C.K :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast hj) (by positivity)
  have h2 : (C.r : ℤ) = C.K * C.s := by unfold Cells.r; push_cast; ring
  nlinarith

end Cells

/-! ## The setting of one examination -/

namespace KSch

open Cells

variable (S : KSch d)

/-- The weighting pinned on `ω|_{E_i}` and restricted to `E_i ∪ E_{w,v} ∪ E_{v,x}` (the weighting
of KN's graph `Ω` restricted to `E_{w,v} ∪ E_{v,x}`, p. 28). [cite: KozmaNitzan2024, §4 p. 28 (Ω)] -/
def Wfull (h : ProbeHistory (Site d)) (e : Site 2 × MDir) (du : MDir) : Sym2 (Site d) → unitInterval :=
  restrW (↑(S.Sx h e du) : Set (Site d)) (pinW (lattW d S.p) ↑(S.F h) ↑(S.ξ h))

/-- The event `{0 ↔ M_x in E_i ∪ E_{w,v} ∪ H_{v,x}}` (KN: `o ↔^{E_{w,v} ∪ H_{v,x}} M_x` in `Ω`).
[cite: KozmaNitzan2024, §4 p. 30 (Step IV)] -/
def Reach (h : ProbeHistory (Site d)) (e : Site 2 × MDir) (du : MDir) : Set (BondConfig (Site d)) :=
  ⋃ t ∈ (↑(S.C.M (tgt e + stepVec du)) : Set (Site d)),
    openConnIn (↑(S.V h ∪ S.C.Ewv e.1 e.2 ∪ S.C.Hfull (tgt e) du) : Set (Site d)) (0 : Site d) t

/-- The event `A'_j = {0 ↔ F^{j+1}_{v,x} in E_i ∪ E_{w,v} ∪ H^{j+1}_{v,x}}`. [cite: KozmaNitzan2024, §4 p. 30 (B_j)] -/
def Aface (h : ProbeHistory (Site d)) (e : Site 2 × MDir) (du : MDir) (j : ℕ) : Set (BondConfig (Site d)) :=
  ⋃ t ∈ (↑(S.C.Face (tgt e) du (j + 1)) : Set (Site d)),
    openConnIn (↑(S.V h ∪ S.C.Ewv e.1 e.2 ∪ S.C.Stub (tgt e) du (j + 1)) : Set (Site d)) (0 : Site d) t

variable {S}

section Setting

variable {h : ProbeHistory (Site d)} {e : Site 2 × MDir} (hV : S.Valid h e) {du : MDir}
  (hdu : du ∈ S.onward h (tgt e))
include hV hdu

omit hdu in
/-- The explored region is separated from `Q_v`. [cite: KozmaNitzan2024, §4 p. 26 (29)] -/
theorem Valid.sep_Q : Sep (↑(S.V h) : Set (Site d)) ↑(S.C.Q (tgt e)) := by
  obtain ⟨det, hv, -, hsub⟩ := hV.cover
  exact (S.C.cover_sep_Q hv).mono hsub le_rfl

/-- The explored region is separated from `E_{v,x}`. [cite: KozmaNitzan2024, §4 p. 27 (31)] -/
theorem Valid.sep_Efar : Sep (↑(S.V h) : Set (Site d)) ↑(S.C.Efar (tgt e) du) := by
  obtain ⟨det, hv, hx, hsub⟩ := hV.cover
  exact (S.C.cover_sep_Efar hv (hx du hdu)).mono hsub le_rfl

/-- An onward direction does not point back at the source. [folklore] -/
theorem Valid.du_ne_rev : du ≠ rev e.2 := by
  intro h
  have h1 := (Finset.mem_filter.1 hdu).2
  rw [h] at h1
  apply h1
  have : tgt e + stepVec (rev e.2) = e.1 := tgt_tgt_rev e
  rw [this]
  exact hV.src_mem

/-- `E_{w,v}` misses `E_{v,x}`. [folklore] -/
theorem Valid.Ewv_not_mem_Efar {y : Site d} (hy : y ∈ S.C.Ewv e.1 e.2) : y ∉ S.C.Efar (tgt e) du := by
  have := S.C.Ewv_disjoint_Efar (w := e.1) (δw := e.2) (Valid.du_ne_rev hV hdu) hy
  exact this

/-- The origin is outside `Q_v ∪ E_{v,x}`. [folklore] -/
theorem Valid.zero_not_mem_bigD : (0 : Site d) ∉ S.C.bigD (tgt e) du := by
  intro h0
  rcases S.C.mem_Q_or_Efar_of_mem_bigD h0 with h0 | h0
  · exact (Valid.sep_Q hV).not_mem (Finset.mem_coe.2 hV.zero_mem) (Finset.mem_coe.2 h0)
  · exact (Valid.sep_Efar hV hdu).not_mem (Finset.mem_coe.2 hV.zero_mem) (Finset.mem_coe.2 h0)

/-- Explored vertices are outside `Q_v ∪ E_{v,x}`. [folklore] -/
theorem Valid.not_mem_bigD_of_mem_V {y : Site d} (hy : y ∈ S.V h) : y ∉ S.C.bigD (tgt e) du := by
  intro h0
  rcases S.C.mem_Q_or_Efar_of_mem_bigD h0 with h0 | h0
  · exact (Valid.sep_Q hV).not_mem (Finset.mem_coe.2 hy) (Finset.mem_coe.2 h0)
  · exact (Valid.sep_Efar hV hdu).not_mem (Finset.mem_coe.2 hy) (Finset.mem_coe.2 h0)

/-! ## Step IV, first claim: `M_x` is reached through the corridor (Lemma 12) -/

/-- The datum of Lemma 12 for the examination: direction `du`, centre `cen v`, the weighting `Wfull`
supported on `E_i ∪ E_{w,v} ∪ E_{v,x}`, source `0`. [cite: KozmaNitzan2024, §4 p. 31 (Lemma 12 with D = E_{v,x} ∪ Q_v)] -/
def cdOf (S : KSch d) (h : ProbeHistory (Site d)) (e : Site 2 × MDir) (du : MDir) : CData d :=
  ⟨S.C.axOf du, sgOf du, sgOf_sign du, S.C.cen (tgt e), S.C.r, S.Wfull h e du, S.Sx h e du, 0⟩

/-- **The hypotheses of Lemma 12 hold for the examination datum.** [cite: KozmaNitzan2024, §4 p. 31] -/
theorem Valid.cd_hyp : (cdOf S h e du).Hyp S.p := by
  have hbigD : (cdOf S h e du).bigD = S.C.bigD (tgt e) du := rfl
  have hsub : S.C.bigD (tgt e) du ⊆ S.Sx h e du := by
    intro y hy
    rcases S.C.mem_Q_or_Efar_of_mem_bigD hy with hy | hy
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_union_right _ hy))
    · exact Finset.mem_union_right _ hy
  refine ⟨finSupp_restrW _ _, ?_, ?_, ?_, ?_⟩
  · rw [hbigD]
    change IsSubbox (restrW _ _) S.p _
    refine ((isSubbox_lattW S.p (S.C.bigD (tgt e) du)).pinW _ fun x hx y hy => ?_).restrW (Finset.coe_subset.2 hsub)
    have hx' : x ∈ S.F h := hx
    rw [hV.F_eq, mem_edgesIn_iff] at hx'
    exact Valid.not_mem_bigD_of_mem_V hV hdu (hx'.2 y hy)
  · rw [hbigD]; exact hsub
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ hV.zero_mem)
  · rw [hbigD]; exact Valid.zero_not_mem_bigD hV hdu

/-- `A` of Lemma 12 is `E_i ∪ E_{w,v}`. [folklore] -/
theorem Valid.cd_Aset : (cdOf S h e du).Aset = S.V h ∪ S.C.Ewv e.1 e.2 := by
  change S.Sx h e du \ S.C.Efar (tgt e) du = _
  ext y
  simp only [Sx, Finset.mem_sdiff, Finset.mem_union]
  constructor
  · rintro ⟨(hy | hy) | hy, hn⟩
    · exact Or.inl hy
    · exact Or.inr hy
    · exact absurd hy hn
  · rintro (hy | hy)
    · exact ⟨Or.inl (Or.inl hy), (Valid.sep_Efar hV hdu).not_mem (Finset.mem_coe.2 hy) ∘ Finset.mem_coe.2⟩
    · exact ⟨Or.inl (Or.inr hy), Valid.Ewv_not_mem_Efar hV hdu hy⟩

omit hV hdu in
/-- The next centre of Lemma 12 is `cen x`. [folklore] -/
theorem cd_cnext : (cdOf S h e du).cnext = S.C.cen (tgt e + stepVec du) := by
  funext j
  change (if j = S.C.axOf du then S.C.cen (tgt e) (S.C.axOf du) + 20 * (S.C.r : ℤ) * sgOf du else S.C.cen (tgt e) j) = _
  rw [S.C.cen_add_stepVec]
  by_cases hj : j = S.C.axOf du
  · subst hj; simp
  · rw [if_neg hj, if_neg hj]

/-- **Step IV, first claim** (KN p. 30–31): `P(0 ↔ M_x in E_i ∪ E_{w,v} ∪ H_{v,x} | ω|_{E_i}) > 1 - ε'`,
from (32) by Lemma 12 — here Lemma 12 at scale `r` is the hypothesis `hcorr`.
[cite: KozmaNitzan2024, §4 pp. 30–31 (Step IV)] -/
theorem reach_bound {ε' : ℝ}
    (hcorr : ∀ T : CData d, T.Hyp S.p → T.r = S.C.r →
      1 - S.δc < (prodBernoulli T.W).real
          (⋃ b ∈ Finset.Icc (T.c - ((3 * T.r : ℕ) : Site d)) (T.c + ((3 * T.r : ℕ) : Site d)),
            openConnIn (↑T.Aset : Set (Site d)) T.o b) →
        1 - ε' < (prodBernoulli T.W).real (⋃ b ∈ T.Tn (3 * T.r), openConnIn (↑T.Uset : Set (Site d)) T.o b)) :
    1 - ε' < (prodBernoulli (S.Wfull h e du)).real (S.Reach h e du) := by
  set T := cdOf S h e du with hT
  have hA := Valid.cd_Aset hV hdu
  set A : Finset (Site d) := S.V h ∪ S.C.Ewv e.1 e.2 with hAdef
  have h0A : (0 : Site d) ∈ (↑A : Set (Site d)) := Finset.mem_coe.2 (Finset.mem_union_left _ hV.zero_mem)
  have hAS : (↑A : Set (Site d)) ⊆ ↑(S.Sx h e du) := Finset.coe_subset.2 Finset.subset_union_left
  -- the hypothesis of Lemma 12 from (32)
  have hreach := hV.reach
  have e1 : (prodBernoulli (S.W₀ h e)).real (⋃ t ∈ S.C.M (tgt e), openConn (0 : Site d) t) =
      (prodBernoulli (pinW (lattW d S.p) ↑(S.F h) ↑(S.ξ h))).real
        (⋃ t ∈ (↑(S.C.M (tgt e)) : Set (Site d)), openConnIn (↑A : Set (Site d)) 0 t) := by
    rw [W₀, ← Finset.set_biUnion_coe, prodBernoulli_restrW_real_biUnion_openConn _ _ h0A]
  have e2 : (prodBernoulli T.W).real (⋃ b ∈ Finset.Icc (T.c - ((3 * T.r : ℕ) : Site d)) (T.c + ((3 * T.r : ℕ) : Site d)),
      openConnIn (↑T.Aset : Set (Site d)) T.o b) =
      (prodBernoulli (pinW (lattW d S.p) ↑(S.F h) ↑(S.ξ h))).real
        (⋃ t ∈ (↑(S.C.M (tgt e)) : Set (Site d)), openConnIn (↑A : Set (Site d)) 0 t) := by
    rw [hA, ← Finset.set_biUnion_coe]
    change (prodBernoulli (restrW _ _)).real _ = _
    exact prodBernoulli_restrW_real_eq_of_determinedBy _ _
      (determinedBy_biUnion_openConnIn _ _ _ (KozmaNitzan.wireSet_mono hAS)) (measurableSet_biUnion_openConnIn _ _ _)
  have hyp : 1 - S.δc < (prodBernoulli T.W).real (⋃ b ∈ Finset.Icc (T.c - ((3 * T.r : ℕ) : Site d))
      (T.c + ((3 * T.r : ℕ) : Site d)), openConnIn (↑T.Aset : Set (Site d)) T.o b) := by
    rw [e2, ← e1]; exact hreach
  have concl := hcorr T (Valid.cd_hyp hV hdu) rfl hyp
  -- read the conclusion
  have hU : (↑T.Uset : Set (Site d)) = ↑(S.V h ∪ S.C.Ewv e.1 e.2 ∪ S.C.Hfull (tgt e) du) := by
    change (↑(T.Aset ∪ S.C.Hfull (tgt e) du) : Set (Site d)) = _
    rw [hA]
  have hTn : T.Tn (3 * T.r) = S.C.M (tgt e + stepVec du) := by
    change Finset.Icc (T.cnext - ((3 * S.C.r : ℕ) : Site d)) (T.cnext + ((3 * S.C.r : ℕ) : Site d)) = _
    rw [cd_cnext]; rfl
  rw [hTn, hU, ← Finset.set_biUnion_coe] at concl
  exact concl

/-! ## Crossing the faces -/

omit hV hdu in
/-- The level of a point along `du` from `cen v`. [folklore] -/
theorem level_le_of_mem_Hfull_of_not_past {y : Site d} (hy : y ∈ S.C.Hfull (tgt e) du) {L : ℤ} (hL : 5 * (S.C.r : ℤ) ≤ L)
    (hR : ¬(y ∈ S.C.Efar (tgt e) du ∧ L + 1 ≤ sgOf du * (y (S.C.axOf du) - S.C.cen (tgt e) (S.C.axOf du)))) :
    sgOf du * (y (S.C.axOf du) - S.C.cen (tgt e) (S.C.axOf du)) ≤ L := by
  by_contra hlt
  push Not at hlt
  apply hR
  refine ⟨?_, by omega⟩
  rw [Cells.Hfull, mem_sBox_iff (sgOf_sign du)] at hy
  rw [Cells.Efar, mem_sBox_iff (sgOf_sign du)]
  refine ⟨⟨by linarith, by linarith [hy.1.2]⟩, fun j hj => ?_⟩
  have := hy.2 j hj; constructor <;> linarith [this.1, this.2]

/-- **To reach beyond the level of `F^j` through the corridor one crosses `F^j`** (KN p. 31: "to hit
`M_x` via `H_{v,x}` you must pass through all the `F^j_{v,x}`"): an open path inside
`Rgn' ⊆ E_i ∪ E_{w,v} ∪ H_{v,x}`, using lattice edges, from `0` to a point of `E_{v,x}` of level
`> 5r + 10sj` (`1 ≤ j ≤ K`) has an initial segment inside `E_i ∪ E_{w,v} ∪ H^j_{v,x}` ending on
`F^j_{v,x}`. [cite: KozmaNitzan2024, §4 p. 31 (Step IV)] -/
theorem exists_face_prefix {G : SimpleGraph (Site d)} {Rgn' : Set (Site d)}
    (hRgn : Rgn' ⊆ ↑(S.V h ∪ S.C.Ewv e.1 e.2 ∪ S.C.Hfull (tgt e) du))
    (hG : ∀ y ∈ Rgn', ∀ z ∈ Rgn', G.Adj y z → (zdGraph d).Adj y z)
    {z : Site d} (hz : z ∈ S.C.Efar (tgt e) du) {j : ℕ} (hj1 : 1 ≤ j)
    (hlev : 5 * (S.C.r : ℤ) + 10 * S.C.s * j + 1 ≤ sgOf du * (z (S.C.axOf du) - S.C.cen (tgt e) (S.C.axOf du)))
    (hp : PathIn G Rgn' 0 z) :
    ∃ a ∈ S.C.Face (tgt e) du j, PathIn G (↑(S.V h ∪ S.C.Ewv e.1 e.2 ∪ S.C.Stub (tgt e) du j) : Set (Site d)) 0 a := by
  set v := tgt e with hv
  set ax := S.C.axOf du with hax
  set c := S.C.cen v ax with hc
  set L : ℤ := 5 * S.C.r + 10 * S.C.s * j with hLdef
  have hs1 : (1 : ℤ) ≤ S.C.s := by exact_mod_cast S.C.hs
  have hr1 : (1 : ℤ) ≤ S.C.r := by exact_mod_cast S.C.r_pos
  have hj1' : (1 : ℤ) ≤ j := by exact_mod_cast hj1
  have hL5 : 5 * (S.C.r : ℤ) + 10 ≤ L := by rw [hLdef]; nlinarith
  set Past : Set (Site d) := {y | y ∈ S.C.Efar v du ∧ L + 1 ≤ sgOf du * (y ax - c)} with hPast
  have h0 : (0 : Site d) ∈ Pastᶜ := fun h0 =>
    (Valid.sep_Efar hV hdu).not_mem (Finset.mem_coe.2 hV.zero_mem) (Finset.mem_coe.2 h0.1)
  have hzP : z ∉ Pastᶜ := fun h' => h' ⟨hz, hlev⟩
  obtain ⟨a, b, ha, hb, hbR, hab, hpa⟩ := hp.exit h0 hzP
  simp only [Set.mem_compl_iff, not_not] at hb
  obtain ⟨hbE, hbl⟩ := hb
  have haR : a ∈ Rgn' := hpa.right_mem.2
  have hadj : (zdGraph d).Adj a b := hG a haR b hbR hab
  -- `b` is in the corridor (not explored, not in `E_{w,v}`)
  have hbH : b ∈ S.C.Hfull v du := by
    rcases Finset.mem_union.1 (hRgn hbR) with hb' | hb'
    · rcases Finset.mem_union.1 hb' with hb'' | hb''
      · exact absurd hbE ((Valid.sep_Efar hV hdu).not_mem (Finset.mem_coe.2 hb'') ∘ Finset.mem_coe.2)
      · exact absurd hbE (Valid.Ewv_not_mem_Efar hV hdu hb'')
    · exact hb'
  have hbH' := hbH
  rw [Cells.Hfull, mem_sBox_iff (sgOf_sign du)] at hbH'
  obtain ⟨-, hbt⟩ := hbH'
  -- the level relation between `a` and `b`
  have hla := level_adj (a := ax) (sgOf_sign du) (S.C.cen v) hadj
  -- where is `a`?
  have haH : a ∈ S.C.Hfull v du ∧ sgOf du * (a ax - c) = L := by
    rcases Finset.mem_union.1 (hRgn haR) with ha' | ha'
    · rcases Finset.mem_union.1 ha' with ha'' | ha''
      · exact absurd hadj ((Valid.sep_Efar hV hdu) a (Finset.mem_coe.2 ha'') b (Finset.mem_coe.2 hbE)).2
      · rcases Finset.mem_union.1 ha'' with ha3 | ha3
        · -- `a ∈ Btw w δw = Btw v (rev δw)`: separated from `E_{v,x}`
          rw [← S.C.Btw_rev] at ha3
          exact absurd hadj ((S.C.Btw_sep_Efar (v := e.1 + stepVec e.2) (Ne.symm (Valid.du_ne_rev hV hdu)))
            a (Finset.mem_coe.2 ha3) b (Finset.mem_coe.2 hbE)).2
        · -- `a ∈ Q_v`: level `≤ 5r`, but `b` has level `≥ L + 1 ≥ 5r + 11`
          exfalso
          obtain ⟨hal, -⟩ := S.C.level_of_mem_Q (δ := du) ha3
          change -(5 * (S.C.r : ℤ)) ≤ sgOf du * (a ax - c) ∧ sgOf du * (a ax - c) ≤ 5 * S.C.r at hal
          rcases hla with ⟨hl, -⟩ | ⟨hl, -⟩
          · change sgOf du * (b ax - c) = sgOf du * (a ax - c) at hl; linarith [hal.2]
          · change sgOf du * (b ax - c) = sgOf du * (a ax - c) + 1 ∨ sgOf du * (b ax - c) = sgOf du * (a ax - c) - 1 at hl
            rcases hl with hl | hl <;> linarith [hal.2]
    · have hal : sgOf du * (a ax - c) ≤ L :=
        level_le_of_mem_Hfull_of_not_past ha' (by linarith) ha
      refine ⟨ha', le_antisymm hal ?_⟩
      rcases hla with ⟨hl, -⟩ | ⟨hl, -⟩
      · change sgOf du * (b ax - c) = sgOf du * (a ax - c) at hl; linarith
      · change sgOf du * (b ax - c) = sgOf du * (a ax - c) + 1 ∨ sgOf du * (b ax - c) = sgOf du * (a ax - c) - 1 at hl
        rcases hl with hl | hl <;> linarith
  obtain ⟨haHf, haL⟩ := haH
  refine ⟨a, ?_, hpa.mono ?_⟩
  · rw [Cells.Hfull, mem_sBox_iff (sgOf_sign du)] at haHf
    rw [Cells.Face, mem_sBox_iff (sgOf_sign du)]
    exact ⟨⟨haL.ge, haL.le⟩, haHf.2⟩
  · -- the complement of `Past` inside `Rgn'` lies in `E_i ∪ E_{w,v} ∪ H^j`
    rintro y ⟨hyP, hyR⟩
    rcases Finset.mem_union.1 (hRgn hyR) with hy' | hy'
    · exact Finset.mem_coe.2 (Finset.mem_union_left _ hy')
    · have hyl : sgOf du * (y ax - c) ≤ L :=
        level_le_of_mem_Hfull_of_not_past hy' (by linarith) hyP
      rw [Cells.Hfull, mem_sBox_iff (sgOf_sign du)] at hy'
      refine Finset.mem_coe.2 (Finset.mem_union_right _ ?_)
      rw [Cells.Stub, mem_sBox_iff (sgOf_sign du)]
      exact ⟨⟨hy'.1.1, hyl⟩, hy'.2⟩

/-- **`Reach ⊆ A'_{K-1}`** on configurations whose open pairs inside the region are lattice edges.
[cite: KozmaNitzan2024, §4 p. 31 (Step IV)] -/
theorem reach_subset_Aface {ω : BondConfig (Site d)} (hω : ω ∈ lattOnly (S.V h ∪ S.C.Ewv e.1 e.2 ∪ S.C.Hfull (tgt e) du))
    (hR : ω ∈ S.Reach h e du) : ω ∈ S.Aface h e du (S.C.K - 1) := by
  have hK1 : 1 ≤ S.C.K := by have := S.C.hK; omega
  have hKK : S.C.K - 1 + 1 = S.C.K := by omega
  simp only [Reach, Set.mem_iUnion, exists_prop, Finset.mem_coe] at hR
  obtain ⟨t, ht, hpath⟩ := hR
  rw [DCT16.mem_openConnIn_iff_pathIn] at hpath
  have hG : ∀ y ∈ (↑(S.V h ∪ S.C.Ewv e.1 e.2 ∪ S.C.Hfull (tgt e) du) : Set (Site d)),
      ∀ z ∈ (↑(S.V h ∪ S.C.Ewv e.1 e.2 ∪ S.C.Hfull (tgt e) du) : Set (Site d)),
      (openGraph ω).Adj y z → (zdGraph d).Adj y z := by
    intro y hy z hz hadj
    rw [openGraph_adj] at hadj
    have hmem : s(y, z) ∈ pairsF (S.V h ∪ S.C.Ewv e.1 e.2 ∪ S.C.Hfull (tgt e) du) := by
      rw [← Finset.mem_coe, coe_pairsF]
      exact mk_mem_wireSet_iff.2 ⟨hy, hz, hadj.2⟩
    exact (SimpleGraph.mem_edgeSet _).1 (hω s(y, z) hmem hadj.1)
  obtain ⟨hl, -⟩ := S.C.level_of_mem_M_tgt ht
  have hr1 : (1 : ℤ) ≤ S.C.r := by exact_mod_cast S.C.r_pos
  have hs20 : 20 * (S.C.s : ℤ) ≤ S.C.r := by exact_mod_cast S.C.twenty_s_le_r
  have hrK : (S.C.r : ℤ) = S.C.K * S.C.s := by unfold Cells.r; push_cast; ring
  obtain ⟨a, ha, hpa⟩ := exists_face_prefix hV hdu subset_rfl hG (S.C.M_tgt_subset_Efar _ _ ht) hK1
    (by
      have : 10 * (S.C.s : ℤ) * (S.C.K : ℕ) = 10 * S.C.r := by rw [hrK]; ring
      rw [this]; linarith [hl.1]) hpath
  simp only [Aface, Set.mem_iUnion, exists_prop, Finset.mem_coe, hKK]
  refine ⟨a, ha, ?_⟩
  rw [DCT16.mem_openConnIn_iff_pathIn]
  exact hpa

/-- **`A'_j ⊆ A'_{j-1}`** (`1 ≤ j < K`) on configurations whose open pairs inside the region are lattice
edges. [cite: KozmaNitzan2024, §4 p. 31 (Step IV)] -/
theorem Aface_subset_Aface {j : ℕ} (hj1 : 1 ≤ j) (hjK : j < S.C.K) {ω : BondConfig (Site d)}
    (hω : ω ∈ lattOnly (S.V h ∪ S.C.Ewv e.1 e.2 ∪ S.C.Stub (tgt e) du (j + 1)))
    (hR : ω ∈ S.Aface h e du j) : ω ∈ S.Aface h e du (j - 1) := by
  have hjj : j - 1 + 1 = j := by omega
  simp only [Aface, Set.mem_iUnion, exists_prop, Finset.mem_coe] at hR
  obtain ⟨t, ht, hpath⟩ := hR
  rw [DCT16.mem_openConnIn_iff_pathIn] at hpath
  set Rgn' : Set (Site d) := ↑(S.V h ∪ S.C.Ewv e.1 e.2 ∪ S.C.Stub (tgt e) du (j + 1)) with hRgn'
  have hsub : Rgn' ⊆ ↑(S.V h ∪ S.C.Ewv e.1 e.2 ∪ S.C.Hfull (tgt e) du) := by
    refine Finset.coe_subset.2 (Finset.union_subset_union le_rfl (S.C.Stub_subset_Hfull _ _ (by omega)))
  have hG : ∀ y ∈ Rgn', ∀ z ∈ Rgn', (openGraph ω).Adj y z → (zdGraph d).Adj y z := by
    intro y hy z hz hadj
    rw [openGraph_adj] at hadj
    have hmem : s(y, z) ∈ pairsF (S.V h ∪ S.C.Ewv e.1 e.2 ∪ S.C.Stub (tgt e) du (j + 1)) := by
      rw [← Finset.mem_coe, coe_pairsF]
      exact mk_mem_wireSet_iff.2 ⟨hy, hz, hadj.2⟩
    exact (SimpleGraph.mem_edgeSet _).1 (hω s(y, z) hmem hadj.1)
  have htE : t ∈ S.C.Efar (tgt e) du := by
    have hs1 : (1 : ℤ) ≤ S.C.s := by exact_mod_cast S.C.hs
    have hrK : (S.C.r : ℤ) = S.C.K * S.C.s := by unfold Cells.r; push_cast; ring
    have hjK' : (j : ℤ) + 1 ≤ S.C.K := by exact_mod_cast hjK
    rw [Cells.Face, mem_sBox_iff (sgOf_sign du)] at ht
    rw [Cells.Efar, mem_sBox_iff (sgOf_sign du)]
    push_cast at ht
    refine ⟨⟨by nlinarith [ht.1.1], ?_⟩, fun i hi => ?_⟩
    · have : 10 * (S.C.s : ℤ) * (j + 1) ≤ 10 * S.C.s * S.C.K :=
        mul_le_mul_of_nonneg_left hjK' (by positivity)
      nlinarith [ht.1.2]
    · have := ht.2 i hi; constructor <;> linarith [this.1, this.2]
  have hlev : 5 * (S.C.r : ℤ) + 10 * S.C.s * j + 1 ≤
      sgOf du * (t (S.C.axOf du) - S.C.cen (tgt e) (S.C.axOf du)) := by
    rw [Cells.Face, mem_sBox_iff (sgOf_sign du)] at ht
    push_cast at ht
    have hs1 : (1 : ℤ) ≤ S.C.s := by exact_mod_cast S.C.hs
    nlinarith [ht.1.1]
  obtain ⟨a, ha, hpa⟩ := exists_face_prefix hV hdu hsub hG htE hj1 hlev hpath
  simp only [Aface, Set.mem_iUnion, exists_prop, Finset.mem_coe, hjj]
  refine ⟨a, ha, ?_⟩
  rw [DCT16.mem_openConnIn_iff_pathIn]
  exact hpa

/-! ## Step III: the target lemma turns "`F^{j+1}` reached" into "good at level `j`" -/

/-- The subbox `E_{v,x} \ E^j_{v,x}` of Step III: levels `(5r + 10sj, 25r]`, width `5r`.
[cite: KozmaNitzan2024, §4 p. 30 (D = E_{v,x} \ E^j_{v,x})] -/
def Dpast (S : KSch d) (e : Site 2 × MDir) (du : MDir) (j : ℕ) : Finset (Site d) :=
  sBox (S.C.axOf du) (sgOf du) (S.C.cen (tgt e)) (5 * S.C.r + 10 * S.C.s * j + 1) (25 * S.C.r) (5 * S.C.r)

omit hV hdu in
/-- `Dpast ⊆ E_{v,x}`. [folklore] -/
theorem Dpast_subset_Efar (j : ℕ) : Dpast S e du j ⊆ S.C.Efar (tgt e) du :=
  sBox_mono (sgOf_sign du) _ (by have : (0 : ℤ) ≤ 10 * S.C.s * j := by positivity
                                 linarith) le_rfl le_rfl

omit hV hdu in
/-- **`M_x` is a target of `F^{j+1}` in `E_{v,x} \ E^j`** with respect to the elongated geometries of
aspect `2K`, via `ℓ(u) = ⌊(15r - 10s(j+1))/2K⌋` in direction `du` (KN p. 30). Requires `j < K`,
`2R ≤ s`. [cite: KozmaNitzan2024, §4 p. 30 (Step III)] -/
theorem isTarget_stepIII {R : ℕ} (hRs : 2 * R ≤ S.C.s) {j : ℕ} (hj : j < S.C.K) :
    IsTarget (S.C.M (tgt e + stepVec du))
      (sLo (S.C.axOf du) (sgOf du) (S.C.cen (tgt e)) (5 * S.C.r + 10 * S.C.s * (j + 1 : ℕ)) (5 * S.C.r + 10 * S.C.s * (j + 1 : ℕ)) (2 * S.C.r))
      (sHi (S.C.axOf du) (sgOf du) (S.C.cen (tgt e)) (5 * S.C.r + 10 * S.C.s * (j + 1 : ℕ)) (5 * S.C.r + 10 * S.C.s * (j + 1 : ℕ)) (2 * S.C.r))
      (Dpast S e du j) R (elongList d (2 * S.C.K) (by have := S.C.hK; omega)) := by
  refine ⟨fun u hu => ?_⟩
  set v := tgt e with hv
  set a := S.C.axOf du with ha
  set σ := sgOf du with hσdef
  have hσ : σ = 1 ∨ σ = -1 := sgOf_sign du
  set c := S.C.cen v with hc
  rw [sBox_enlarge a σ hσ, mem_sBox_iff hσ] at hu
  obtain ⟨⟨hu1, hu2⟩, hut⟩ := hu
  push_cast at hu1 hu2 hut
  -- constants
  have hK : (20 : ℤ) ≤ S.C.K := by exact_mod_cast S.C.hK
  have hs1 : (1 : ℤ) ≤ S.C.s := by exact_mod_cast S.C.hs
  have hrK : (S.C.r : ℤ) = S.C.K * S.C.s := by unfold Cells.r; push_cast; ring
  have hRs' : 2 * (R : ℤ) ≤ S.C.s := by exact_mod_cast hRs
  have hjK : (j : ℤ) + 1 ≤ S.C.K := by exact_mod_cast hj
  have hKs20 : 20 * (S.C.s : ℤ) ≤ S.C.K * S.C.s := mul_le_mul_of_nonneg_right hK (by linarith)
  have hjs : 10 * (S.C.s : ℤ) * (j + 1) ≤ 10 * S.C.s * S.C.K := mul_le_mul_of_nonneg_left hjK (by positivity)
  have hj0 : (0 : ℤ) ≤ 10 * S.C.s * j := by positivity
  -- the scale `ℓ = ⌊N / 2K⌋`, `N = 15r - 10s(j+1)`
  set N : ℤ := 15 * S.C.r - 10 * S.C.s * (j + 1) with hN
  have hN5 : 5 * ((S.C.K : ℤ) * S.C.s) ≤ N := by rw [hN, hrK]; nlinarith
  have hN15 : N ≤ 15 * ((S.C.K : ℤ) * S.C.s) := by rw [hN, hrK]; nlinarith
  have hN0 : 0 ≤ N := by nlinarith
  have h2K : (0 : ℤ) < 2 * S.C.K := by linarith
  have hx0 : 0 ≤ N / (2 * S.C.K) := Int.ediv_nonneg hN0 h2K.le
  set ℓ : ℕ := (N / (2 * S.C.K)).toNat with hℓdef
  have hℓ : (ℓ : ℤ) = N / (2 * S.C.K) := Int.toNat_of_nonneg hx0
  have hℓ1 : 2 * (S.C.K : ℤ) * ℓ ≤ N := by rw [hℓ]; exact Int.mul_ediv_self_le h2K.ne'
  have hℓ2 : N < 2 * (S.C.K : ℤ) * ℓ + 2 * S.C.K := by rw [hℓ]; exact Int.lt_mul_ediv_self_add h2K
  have hK0 : (0 : ℤ) < S.C.K := by linarith
  have hℓ15 : 2 * (ℓ : ℤ) ≤ 15 * S.C.s := by
    have : (S.C.K : ℤ) * (2 * ℓ) ≤ S.C.K * (15 * S.C.s) := by nlinarith
    exact le_of_mul_le_mul_left this hK0
  have hℓ5 : 5 * (S.C.s : ℤ) - 1 ≤ 2 * ℓ := by
    have : (S.C.K : ℤ) * (5 * S.C.s) < S.C.K * (2 * ℓ + 2) := by nlinarith
    have := lt_of_mul_lt_mul_left this hK0.le
    linarith
  -- the geometry
  set σu : ℤˣ := if σ = 1 then 1 else -1 with hσu
  have hσuval : (σu : ℤ) = σ := units_of_sign_val hσ
  have hK2 : 1 ≤ 2 * S.C.K := by have := S.C.hK; omega
  refine ⟨ℓ, ?_, elongGeom a σu (2 * S.C.K) hK2, elongGeom_mem_elongList _ _ _ _, ?_, ?_⟩
  · have : (R : ℤ) ≤ ℓ := by linarith
    exact_mod_cast this
  · -- `u + ℓQ ⊆ Dpast`
    intro y hy
    rw [elongGeom_Qset_eq, hσuval, mem_sBox_iff hσ] at hy
    obtain ⟨⟨hy1, hy2⟩, hyt⟩ := hy
    push_cast at hy2
    rw [Dpast, mem_sBox_iff hσ]
    have hsplit : σ * (y a - c a) = σ * (y a - u a) + σ * (u a - c a) := by ring
    refine ⟨⟨?_, ?_⟩, fun i hi => ?_⟩
    · rw [hsplit]; linarith
    · rw [hsplit]
      have : 2 * (S.C.K : ℤ) * ℓ = ℓ * (2 * S.C.K) := by ring
      linarith
    · have := hyt i hi; have := hut i hi
      constructor <;> linarith
  · -- `u + ℓF ⊆ M_x`
    intro y hy
    rw [elongGeom_Fset_eq, hσuval, mem_sBox_iff hσ] at hy
    obtain ⟨⟨hy1, hy2⟩, hyt⟩ := hy
    push_cast at hy1 hy2
    rw [Cells.M, mem_cIcc_iff]
    push_cast
    intro i
    rw [S.C.cen_add_stepVec]
    by_cases hi : i = a
    · subst hi
      rw [if_pos rfl]
      have hsq := sign_mul_self hσ
      have hyeq : σ * (y a - u a) = 2 * S.C.K * ℓ := by
        have := le_antisymm hy2 hy1
        linear_combination this
      have hlev : σ * (y a - (S.C.cen (tgt e) a + 20 * S.C.r * sgOf du)) =
          σ * (y a - u a) + σ * (u a - c a) - 20 * S.C.r := by
        have : sgOf du = σ := rfl
        rw [this]
        have e1 : σ * (y a - (S.C.cen (tgt e) a + 20 * S.C.r * σ)) = σ * (y a - u a) + σ * (u a - c a) - 20 * S.C.r * (σ * σ) := by
          rw [hc]; ring
        rw [e1, hsq, mul_one]
      have hKr : (S.C.K : ℤ) ≤ S.C.r := by
        have := mul_le_mul_of_nonneg_left hs1 (show (0 : ℤ) ≤ S.C.K by linarith)
        rw [hrK]; linarith
      have hb : -(3 * (S.C.r : ℤ)) ≤ σ * (y a - (S.C.cen (tgt e) a + 20 * S.C.r * sgOf du)) ∧
          σ * (y a - (S.C.cen (tgt e) a + 20 * S.C.r * sgOf du)) ≤ 3 * S.C.r := by
        rw [hlev, hyeq]
        constructor <;> linarith
      have := abs_bounds_of_level hσ hb.1 hb.2
      constructor <;> linarith [this.1, this.2]
    · rw [if_neg hi]
      have h20 : 20 * (S.C.s : ℤ) ≤ S.C.r := by exact_mod_cast S.C.twenty_s_le_r
      have := hyt i hi; have := hut i hi
      constructor <;> linarith

/-- **Step III** (KN p. 30: "if for some `j` the event `B_j` did not happen then the connection between
`v` and `x` is good"): if `F^{j+1}_{v,x}` is reached from `0` with probability `> 1 - δ₂` under the
weighting of level `j`, then the connection is good at level `j` — by the target lemma, here the
hypothesis `htgt` (with `δ_{L10} = δ₂`, its `R`, and the elongated geometries of aspect `2K`).
[cite: KozmaNitzan2024, §4 p. 30 (Step III)] -/
theorem cond_of_face {δ₂ : ℝ} {R : ℕ}
    (htgt : ∀ (W : Sym2 (Site d) → unitInterval) (Sfin D : Finset (Site d)) (lo hi : Site d)
      (T : Finset (Site d)) (o : Site d),
      FinSupp W Sfin → IsSubbox W S.p D → D ⊆ Sfin → o ∈ Sfin → o ∉ D →
      Finset.Icc (lo - (R : Site d)) (hi + (R : Site d)) ⊆ D →
      IsTarget T lo hi D R (elongList d (2 * S.C.K) (by have := S.C.hK; omega)) → T ⊆ D → T.Nonempty →
      1 - δ₂ < (prodBernoulli W).real (⋃ b ∈ Finset.Icc lo hi, openConn o b) →
      1 - S.δc < (prodBernoulli W).real (⋃ t ∈ T, openConn o t))
    (hRs : 2 * R ≤ S.C.s) {j : ℕ} (hj : j < S.C.K) (o : Finset (Sym2 (Site d)))
    (hface : 1 - δ₂ < (prodBernoulli (S.Wt h e du j o)).real
      (⋃ b ∈ S.C.Face (tgt e) du (j + 1), openConn (0 : Site d) b)) :
    S.cond h e du j o := by
  set D := Dpast S e du j with hD
  have hK : (20 : ℤ) ≤ S.C.K := by exact_mod_cast S.C.hK
  have hs1 : (1 : ℤ) ≤ S.C.s := by exact_mod_cast S.C.hs
  have hr1 : (1 : ℤ) ≤ S.C.r := by exact_mod_cast S.C.r_pos
  have hrK : (S.C.r : ℤ) = S.C.K * S.C.s := by unfold Cells.r; push_cast; ring
  have hRs' : 2 * (R : ℤ) ≤ S.C.s := by exact_mod_cast hRs
  have hjK : (j : ℤ) + 1 ≤ S.C.K := by exact_mod_cast hj
  have hjs : 10 * (S.C.s : ℤ) * (j + 1) ≤ 10 * S.C.s * S.C.K := mul_le_mul_of_nonneg_left hjK (by positivity)
  have hKs20 : 20 * (S.C.s : ℤ) ≤ S.C.K * S.C.s := mul_le_mul_of_nonneg_right hK (by linarith)
  have hj0 : (0 : ℤ) ≤ 10 * S.C.s * j := by positivity
  have hDE : D ⊆ S.C.Efar (tgt e) du := Dpast_subset_Efar j
  have hDS : D ⊆ S.Sx h e du := hDE.trans Finset.subset_union_right
  -- the subbox
  have hsub : IsSubbox (S.Wt h e du j o) S.p D := by
    refine ((isSubbox_lattW S.p D).pinW _ fun x hx y hy hyD => ?_).restrW (Finset.coe_subset.2 hDS)
    have hx' : x ∈ S.Fj h e du j := hx
    rw [Fj, mem_edgesIn_iff] at hx'
    rcases Finset.mem_union.1 (hx'.2 y hy) with hy' | hy'
    · rcases Finset.mem_union.1 hy' with hy'' | hy''
      · exact (Valid.sep_Efar hV hdu).not_mem (Finset.mem_coe.2 hy'') (Finset.mem_coe.2 (hDE hyD))
      · exact Valid.Ewv_not_mem_Efar hV hdu hy'' (hDE hyD)
    · rw [Cells.Stub, mem_sBox_iff (sgOf_sign du)] at hy'
      rw [hD, Dpast, mem_sBox_iff (sgOf_sign du)] at hyD
      linarith [hy'.1.2, hyD.1.1]
  have h0S : (0 : Site d) ∈ S.Sx h e du := Finset.mem_union_left _ (Finset.mem_union_left _ hV.zero_mem)
  have h0D : (0 : Site d) ∉ D := fun h0 =>
    (Valid.sep_Efar hV hdu).not_mem (Finset.mem_coe.2 hV.zero_mem) (Finset.mem_coe.2 (hDE h0))
  -- the enlarged face lies in `D`
  have hencl : Finset.Icc (sLo (S.C.axOf du) (sgOf du) (S.C.cen (tgt e)) (5 * S.C.r + 10 * S.C.s * (j + 1 : ℕ))
        (5 * S.C.r + 10 * S.C.s * (j + 1 : ℕ)) (2 * S.C.r) - (R : Site d))
      (sHi (S.C.axOf du) (sgOf du) (S.C.cen (tgt e)) (5 * S.C.r + 10 * S.C.s * (j + 1 : ℕ))
        (5 * S.C.r + 10 * S.C.s * (j + 1 : ℕ)) (2 * S.C.r) + (R : Site d)) ⊆ D := by
    rw [sBox_enlarge _ _ (sgOf_sign du)]
    refine sBox_mono (sgOf_sign du) _ ?_ ?_ ?_
    · push_cast; linarith
    · push_cast; nlinarith
    · linarith
  -- `M_x ⊆ D`
  have hMD : S.C.M (tgt e + stepVec du) ⊆ D := by
    intro y hy
    obtain ⟨hl, ht⟩ := S.C.level_of_mem_M_tgt hy
    rw [hD, Dpast, mem_sBox_iff (sgOf_sign du)]
    refine ⟨⟨by nlinarith [hl.1], by linarith [hl.2]⟩, fun i hi => ?_⟩
    have := ht i hi; constructor <;> linarith [this.1, this.2]
  have hMne : (S.C.M (tgt e + stepVec du)).Nonempty := ⟨_, center_mem_cIcc _ _⟩
  exact htgt (S.Wt h e du j o) (S.Sx h e du) D _ _ (S.C.M (tgt e + stepVec du)) 0 (finSupp_restrW _ _) hsub hDS h0S
    h0D hencl (isTarget_stepIII hRs hj) hMD hMne hface

end Setting

end KSch

end KozmaNitzan

end Percolation.Literature

end

/-!
# Kozma–Nitzan, Theorem 6 — the static geometry of the exploration ((29), (31))

Eleventh proofs-only companion of
`KozmaNitzanReduction.lean` (G. Kozma, S. Nitzan, arXiv:2401.12397, §4 pp. 26–29): the mutual position
of the boxes `Q_v`, `E_{v,x}`, `H^j_{v,x}` of the cells (`KozmaNitzanScheme.lean`), which is all that the
two facts KN leave to the reader rest on — (29) "`v ∈ X_i ⟺ Q_v ⊆ E_i ⟺ Q_v ∩ E_i ≠ ∅`" and (31)
"`E_{i₁+1} ∩ E_{w,v} = ⋯ = E_{i₂} ∩ E_{w,v}` … straightforward from the construction above and we omit
it":

* cubes of distinct macro-vertices are disjoint; a cube never meets a between-box (the between-boxes
  are open along their axis); two between-boxes meet only if they belong to the same macro-edge;
* `E_{v,x} ⊆ Btw ∪ Q_x`, `H^j ⊆ Q_v ∪ Btw` (`j < K`), `E_{w,v} ⊆ Cell_w ∪ Cell_v`, `H^j ⊆ Cell_v ∪ Zone`;
* a centre lies in the cover of a set of macro-vertices only if its vertex belongs to the set;
* every vertex of a box lies on a lattice edge inside it, so the vertex span of the lattice edges
  inside a union of boxes is the union.

## References

* G. Kozma, S. Nitzan, arXiv:2401.12397 (2024), §4 pp. 26–29 ((29), (31)).
-/

noncomputable section

open scoped Classical

namespace Percolation.Literature

open LatticeModels SimpleGraph GadgetSystem Contour

namespace KozmaNitzan

variable {d : ℕ}

/-! ## Boxes and lattice edges -/

/-- A vertex of a box with two distinct corners in some coordinate has a lattice neighbour in the box.
[folklore] -/
theorem exists_adj_of_mem_Icc {lo hi y : Site d} (hy : y ∈ Finset.Icc lo hi) {i : Fin d} (hio : lo i < hi i) :
    ∃ z ∈ Finset.Icc lo hi, (zdGraph d).Adj y z := by
  rw [mem_Icc_iff] at hy
  by_cases hlt : y i < hi i
  · refine ⟨y + (1 : ℤ) • unitVec i, ?_, adj_iff_exists_sign.2 ⟨i, 1, Or.inl rfl, rfl⟩⟩
    rw [mem_Icc_iff]
    intro j
    rw [add_smul_unitVec_apply]
    by_cases hj : j = i
    · subst hj; rw [if_pos rfl]; have := hy j; omega
    · rw [if_neg hj, add_zero]; exact hy j
  · refine ⟨y + (-1 : ℤ) • unitVec i, ?_, adj_iff_exists_sign.2 ⟨i, -1, Or.inr rfl, rfl⟩⟩
    rw [mem_Icc_iff]
    intro j
    rw [add_smul_unitVec_apply]
    by_cases hj : j = i
    · subst hj; rw [if_pos rfl]; have := hy j; omega
    · rw [if_neg hj, add_zero]; exact hy j

/-- **The vertex span of the lattice edges inside `X` is `X`** when every vertex of `X` has a lattice
neighbour in `X`. [folklore] -/
theorem span_edgesIn_eq {X : Finset (Site d)} (h : ∀ y ∈ X, ∃ z ∈ X, (zdGraph d).Adj y z) :
    span (edgesIn (zdGraph d) X) = X := by
  ext y
  rw [mem_span_iff]
  constructor
  · rintro ⟨e, he, hy⟩
    rw [mem_edgesIn_iff] at he
    exact he.2 y hy
  · intro hy
    obtain ⟨z, hz, hadj⟩ := h y hy
    refine ⟨s(y, z), ?_, Sym2.mem_mk_left _ _⟩
    rw [mem_edgesIn_iff]
    refine ⟨(SimpleGraph.mem_edgeSet _).2 hadj, fun x hx => ?_⟩
    rcases Sym2.mem_iff.1 hx with rfl | rfl
    · exact hy
    · exact hz

/-! ## Neighbours inside the boxes -/

/-- Every vertex of a symmetric cube of positive radius has a lattice neighbour inside (`d ≥ 1`). [folklore] -/
theorem exists_adj_of_mem_cIcc (hd : 0 < d) {c : Site d} {u : ℕ} (hu : 1 ≤ u) {y : Site d}
    (hy : y ∈ Finset.Icc (c - (u : Site d)) (c + (u : Site d))) :
    ∃ z ∈ Finset.Icc (c - (u : Site d)) (c + (u : Site d)), (zdGraph d).Adj y z := by
  refine exists_adj_of_mem_Icc hy (i := ⟨0, hd⟩) ?_
  simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply]
  omega

namespace Cells

variable (C : Cells d)

/-- Every vertex of a signed box of positive width along a macro-axis has a lattice neighbour inside.
[folklore] -/
theorem exists_adj_of_mem_sBox {δ : MDir} {c : Site d} {α β w : ℤ} (hw : 1 ≤ w) {y : Site d}
    (hy : y ∈ sBox (C.axOf δ) (sgOf δ) c α β w) :
    ∃ z ∈ sBox (C.axOf δ) (sgOf δ) c α β w, (zdGraph d).Adj y z := by
  have hne : C.pax (oth δ.1) ≠ C.axOf δ := fun h => oth_ne δ.1 (C.pax_injective h)
  refine exists_adj_of_mem_Icc hy (i := C.pax (oth δ.1)) ?_
  simp only [sLo, sHi, if_neg hne]
  omega

/-! ## Inclusions between the boxes -/

/-- `Q_v ⊆ Cell_v`. [folklore] -/
theorem Q_subset_Cell (v : Site 2) : C.Q v ⊆ C.Cell v := by
  intro y hy
  rw [Q, mem_cIcc_iff] at hy
  rw [Cell, mem_Icc_iff]
  intro j
  have := hy j
  have hw : 5 * (C.r : ℤ) ≤ C.wC j := by
    unfold wC; split_ifs <;> linarith
  simp only [Pi.sub_apply, Pi.add_apply]
  push_cast at this
  constructor <;> linarith [this.1, this.2]

/-- `E_{v,x} ⊆ Btw ∪ Q_x`. [folklore] -/
theorem Efar_subset_Btw_union_Q (v : Site 2) (δ : MDir) : C.Efar v δ ⊆ C.Btw v δ ∪ C.Q (v + stepVec δ) := by
  intro y hy
  have hσ := sgOf_sign δ
  rw [Efar, mem_sBox_iff hσ] at hy
  obtain ⟨⟨h1, h2⟩, ht⟩ := hy
  by_cases hl : sgOf δ * (y (C.axOf δ) - C.cen v (C.axOf δ)) ≤ 15 * C.r - 1
  · refine Finset.mem_union_left _ ?_
    rw [Btw, mem_sBox_iff hσ]
    exact ⟨⟨h1, hl⟩, ht⟩
  · refine Finset.mem_union_right _ ?_
    rw [Q, mem_cIcc_iff]
    intro i
    rw [C.cen_add_stepVec]
    push_cast
    by_cases hi : i = C.axOf δ
    · subst hi
      rw [if_pos rfl]
      have hsq := sign_mul_self hσ
      have hb : -(5 * (C.r : ℤ)) ≤ sgOf δ * (y (C.axOf δ) - (C.cen v (C.axOf δ) + 20 * C.r * sgOf δ)) ∧
          sgOf δ * (y (C.axOf δ) - (C.cen v (C.axOf δ) + 20 * C.r * sgOf δ)) ≤ 5 * C.r := by
        have e1 : sgOf δ * (y (C.axOf δ) - (C.cen v (C.axOf δ) + 20 * C.r * sgOf δ)) =
            sgOf δ * (y (C.axOf δ) - C.cen v (C.axOf δ)) - 20 * C.r * (sgOf δ * sgOf δ) := by ring
        rw [e1, hsq]
        constructor <;> linarith
      have := abs_bounds_of_level hσ hb.1 hb.2
      constructor <;> linarith [this.1, this.2]
    · rw [if_neg hi]
      exact ht i hi

/-- `E_{v,x} ⊆ E_{w,v}`-shaped: `Efar v δ ⊆ Ewv v δ`. [folklore] -/
theorem Efar_subset_Ewv (v : Site 2) (δ : MDir) : C.Efar v δ ⊆ C.Ewv v δ :=
  C.Efar_subset_Btw_union_Q v δ

/-- `H^j_{v,x} ⊆ Q_v ∪ Btw` for `j < K`. [folklore] -/
theorem Stub_subset_Q_union_Btw (v : Site 2) (δ : MDir) {j : ℕ} (hj : j + 1 ≤ C.K) :
    C.Stub v δ j ⊆ C.Q v ∪ C.Btw v δ := by
  intro y hy
  have hσ := sgOf_sign δ
  have hs1 : (1 : ℤ) ≤ C.s := by exact_mod_cast C.hs
  have hrK : (C.r : ℤ) = C.K * C.s := by unfold Cells.r; push_cast; ring
  have hjK : (j : ℤ) + 1 ≤ C.K := by exact_mod_cast hj
  have hjs : 10 * (C.s : ℤ) * (j + 1) ≤ 10 * C.s * C.K := mul_le_mul_of_nonneg_left hjK (by positivity)
  rw [Stub, mem_sBox_iff hσ] at hy
  obtain ⟨⟨h1, h2⟩, ht⟩ := hy
  by_cases hl : sgOf δ * (y (C.axOf δ) - C.cen v (C.axOf δ)) ≤ 5 * C.r
  · refine Finset.mem_union_left _ ?_
    rw [Q, mem_cIcc_iff]
    intro i
    push_cast
    by_cases hi : i = C.axOf δ
    · subst hi
      have := abs_bounds_of_level hσ (n := 5 * C.r) (by linarith) hl
      constructor <;> linarith [this.1, this.2]
    · have := ht i hi; constructor <;> linarith [this.1, this.2]
  · refine Finset.mem_union_right _ ?_
    rw [Btw, mem_sBox_iff hσ]
    refine ⟨⟨by linarith, ?_⟩, fun i hi => ?_⟩
    · have : 10 * (C.s : ℤ) * j + 10 * C.s ≤ 10 * C.r := by rw [hrK]; linarith
      linarith
    · have := ht i hi; constructor <;> linarith [this.1, this.2]

/-- `E_{w,v} ⊆ Cell_w ∪ Cell_v`. [folklore] -/
theorem Ewv_subset_Cells (v : Site 2) (δ : MDir) : C.Ewv v δ ⊆ C.Cell v ∪ C.Cell (v + stepVec δ) := by
  intro y hy
  have hσ := sgOf_sign δ
  have hr1 : (1 : ℤ) ≤ C.r := by exact_mod_cast C.r_pos
  rcases Finset.mem_union.1 hy with hy | hy
  · rw [Btw, mem_sBox_iff hσ] at hy
    obtain ⟨⟨h1, h2⟩, ht⟩ := hy
    have hwC : ∀ j, 5 * (C.r : ℤ) ≤ C.wC j ∧ (j = C.axOf δ → C.wC j = 10 * C.r) := by
      intro j
      unfold wC
      constructor
      · split_ifs <;> linarith
      · intro hj
        rw [if_pos]
        unfold axOf pax at hj
        split_ifs at hj
        · exact Or.inl hj
        · exact Or.inr hj
    by_cases hl : sgOf δ * (y (C.axOf δ) - C.cen v (C.axOf δ)) ≤ 10 * C.r
    · refine Finset.mem_union_left _ ?_
      rw [Cell, mem_Icc_iff]
      intro j
      simp only [Pi.sub_apply, Pi.add_apply]
      by_cases hj : j = C.axOf δ
      · subst hj
        rw [(hwC _).2 rfl]
        have := abs_bounds_of_level hσ (n := 10 * C.r) (by linarith) hl
        constructor <;> linarith [this.1, this.2]
      · have := ht j hj; have := (hwC j).1; constructor <;> linarith
    · refine Finset.mem_union_right _ ?_
      rw [Cell, mem_Icc_iff]
      intro j
      simp only [Pi.sub_apply, Pi.add_apply]
      rw [C.cen_add_stepVec]
      by_cases hj : j = C.axOf δ
      · subst hj
        rw [if_pos rfl, (hwC _).2 rfl]
        have hsq := sign_mul_self hσ
        have hb : -(10 * (C.r : ℤ)) ≤ sgOf δ * (y (C.axOf δ) - (C.cen v (C.axOf δ) + 20 * C.r * sgOf δ)) ∧
            sgOf δ * (y (C.axOf δ) - (C.cen v (C.axOf δ) + 20 * C.r * sgOf δ)) ≤ 10 * C.r := by
          have e1 : sgOf δ * (y (C.axOf δ) - (C.cen v (C.axOf δ) + 20 * C.r * sgOf δ)) =
              sgOf δ * (y (C.axOf δ) - C.cen v (C.axOf δ)) - 20 * C.r * (sgOf δ * sgOf δ) := by ring
          rw [e1, hsq]
          constructor <;> linarith
        have := abs_bounds_of_level hσ hb.1 hb.2
        constructor <;> linarith [this.1, this.2]
      · rw [if_neg hj]
        have := ht j hj; have := (hwC j).1; constructor <;> linarith
  · exact Finset.mem_union_right _ (C.Q_subset_Cell _ hy)

/-- `H^j_{v,x} ⊆ Cell_v ∪ Zone` for `j < K`. [folklore] -/
theorem Stub_subset_Cell_union_Zone (v : Site 2) (δ : MDir) {j : ℕ} (hj : j + 1 ≤ C.K) :
    C.Stub v δ j ⊆ C.Cell v ∪ C.Zone v δ := by
  intro y hy
  have hσ := sgOf_sign δ
  have hr1 : (1 : ℤ) ≤ C.r := by exact_mod_cast C.r_pos
  have hs1 : (1 : ℤ) ≤ C.s := by exact_mod_cast C.hs
  have hrK : (C.r : ℤ) = C.K * C.s := by unfold Cells.r; push_cast; ring
  have hjK : (j : ℤ) + 1 ≤ C.K := by exact_mod_cast hj
  have hjs : 10 * (C.s : ℤ) * (j + 1) ≤ 10 * C.s * C.K := mul_le_mul_of_nonneg_left hjK (by positivity)
  rw [Stub, mem_sBox_iff hσ] at hy
  obtain ⟨⟨h1, h2⟩, ht⟩ := hy
  by_cases hl : sgOf δ * (y (C.axOf δ) - C.cen v (C.axOf δ)) ≤ 10 * C.r
  · refine Finset.mem_union_left _ ?_
    rw [Cell, mem_Icc_iff]
    intro i
    simp only [Pi.sub_apply, Pi.add_apply]
    have hwC : 5 * (C.r : ℤ) ≤ C.wC i ∧ (i = C.axOf δ → C.wC i = 10 * C.r) := by
      unfold wC
      constructor
      · split_ifs <;> linarith
      · intro hi
        rw [if_pos]
        unfold axOf pax at hi
        split_ifs at hi
        · exact Or.inl hi
        · exact Or.inr hi
    by_cases hi : i = C.axOf δ
    · subst hi
      rw [hwC.2 rfl]
      have := abs_bounds_of_level hσ (n := 10 * C.r) (by linarith) hl
      constructor <;> linarith [this.1, this.2]
    · have := ht i hi; have := hwC.1; constructor <;> linarith
  · refine Finset.mem_union_right _ ?_
    rw [Zone, mem_sBox_iff hσ]
    refine ⟨⟨by linarith, ?_⟩, ht⟩
    have : 10 * (C.s : ℤ) * j + 10 * C.s ≤ 10 * C.r := by rw [hrK]; linarith
    linarith

/-! ## Disjointness -/

/-- **Cubes of distinct macro-vertices are disjoint.** [cite: KozmaNitzan2024, §4 p. 26 (Q_v)] -/
theorem Q_disjoint_Q {u x : Site 2} (hux : u ≠ x) : Disjoint (C.Q u) (C.Q x) := by
  rw [Finset.disjoint_left]
  intro y hy hy'
  exact (C.cell_sep_Q hux).not_mem (Finset.mem_coe.2 (C.Q_subset_Cell _ hy)) (Finset.mem_coe.2 hy')

/-- **A cube never meets a between-box** (the between-boxes are open along their axis).
[cite: KozmaNitzan2024, §4 p. 26 (E_{v,x})] -/
theorem Q_disjoint_Btw (x v : Site 2) (δ : MDir) : Disjoint (C.Q x) (C.Btw v δ) := by
  rw [Finset.disjoint_left]
  intro y hy hy'
  have hr : (0 : ℤ) ≤ 20 * C.r := by positivity
  have h1 := C.planar_of_mem_cIcc hy δ.1
  obtain ⟨⟨h2, h3⟩, -⟩ := C.planar_of_mem_sBox hy'
  push_cast at h1
  rcases le_or_gt (x δ.1) (v δ.1) with hle | hlt
  · have := mul_le_mul_of_nonneg_left hle hr
    rcases sgOf_sign δ with hs | hs <;> rw [hs] at h2 h3
    · linarith
    · rcases lt_or_eq_of_le hle with hlt | heq
      · have h4 : x δ.1 + 1 ≤ v δ.1 := hlt
        have := mul_le_mul_of_nonneg_left h4 hr
        linarith
      · rw [heq] at h1; linarith
  · have h4 : v δ.1 + 1 ≤ x δ.1 := hlt
    have := mul_le_mul_of_nonneg_left h4 hr
    rcases sgOf_sign δ with hs | hs <;> rw [hs] at h2 h3
    · rcases lt_or_eq_of_le h4 with h5 | h5
      · have h6 : v δ.1 + 2 ≤ x δ.1 := by omega
        have := mul_le_mul_of_nonneg_left h6 hr
        linarith
      · rw [← h5] at h1; linarith
    · linarith

/-- A macro-direction is determined by its axis and its sign. [folklore] -/
theorem MDir.eq_of_sgOf {δ δ' : MDir} (h1 : δ'.1 = δ.1) (h2 : sgOf δ' = sgOf δ) : δ' = δ := by
  obtain ⟨a, b⟩ := δ; obtain ⟨a', b'⟩ := δ'
  simp only at h1; subst h1
  unfold sgOf at h2
  cases b <;> cases b' <;> simp_all

/-- The direction with the same axis and the opposite sign is the reverse. [folklore] -/
theorem MDir.eq_rev_of_sgOf {δ δ' : MDir} (h1 : δ'.1 = δ.1) (h2 : sgOf δ' = -sgOf δ) : δ' = rev δ := by
  obtain ⟨a, b⟩ := δ; obtain ⟨a', b'⟩ := δ'
  simp only at h1; subst h1
  unfold sgOf at h2
  cases b <;> cases b' <;> simp_all [rev]

/-- **Two between-boxes meet only if they belong to the same macro-edge.**
[cite: KozmaNitzan2024, §4 p. 27 ((31))] -/
theorem Btw_disjoint_Btw {v v' : Site 2} {δ δ' : MDir} (h1 : (v', δ') ≠ (v, δ))
    (h2 : (v', δ') ≠ (v + stepVec δ, rev δ)) : Disjoint (C.Btw v δ) (C.Btw v' δ') := by
  rw [Finset.disjoint_left]
  intro y hy hy'
  have hr : (0 : ℤ) ≤ 20 * C.r := by positivity
  have hr1 : (1 : ℤ) ≤ C.r := by exact_mod_cast C.r_pos
  obtain ⟨⟨hl1, hl2⟩, ht1, ht2⟩ := C.planar_of_mem_sBox hy
  obtain ⟨⟨hl1', hl2'⟩, ht1', ht2'⟩ := C.planar_of_mem_sBox hy'
  by_cases hax : δ'.1 = δ.1
  · -- parallel
    rw [hax] at hl1' hl2' ht1' ht2'
    by_cases hut : v (oth δ.1) = v' (oth δ.1)
    · rw [hut] at ht1 ht2
      rcases sgOf_sign δ with hs | hs <;> rcases sgOf_sign δ' with hs' | hs'
      · -- same sign `+`
        by_cases hva : v δ.1 = v' δ.1
        · exact h1 (Prod.ext (eq_of_coords δ.1 hva.symm hut.symm) (MDir.eq_of_sgOf hax (by rw [hs, hs'])))
        · rw [hs] at hl1 hl2; rw [hs'] at hl1' hl2'
          rcases C.cen_gap hva with h | h <;> linarith
      · -- `σ = 1`, `σ' = -1`: then `v' = v + e` and `δ' = rev δ`
        rw [hs] at hl1 hl2; rw [hs'] at hl1' hl2'
        exfalso
        apply h2
        have ht : v' δ.1 - v δ.1 = 1 := by
          have k1 : 20 * (C.r : ℤ) * (v' δ.1 - v δ.1) ≥ 10 * C.r + 2 := by linarith
          have k2 : 20 * (C.r : ℤ) * (v' δ.1 - v δ.1) ≤ 30 * C.r - 2 := by linarith
          by_contra hne
          rcases lt_or_gt_of_ne hne with hlt | hlt
          · have : v' δ.1 - v δ.1 ≤ 0 := by omega
            have := mul_le_mul_of_nonneg_left this hr
            linarith
          · have : (2 : ℤ) ≤ v' δ.1 - v δ.1 := by omega
            have := mul_le_mul_of_nonneg_left this hr
            linarith
        refine Prod.ext (eq_of_coords (u := v') (v := v + stepVec δ) δ.1 ?_ ?_) (MDir.eq_rev_of_sgOf (δ := δ) (δ' := δ') hax (by omega))
        · rw [Pi.add_apply, stepVec_apply_fst, hs]; omega
        · rw [Pi.add_apply, stepVec_apply_oth, add_zero]; exact hut.symm
      · -- `σ = -1`, `σ' = 1`: then `v' = v - e = v + stepVec δ` and `δ' = rev δ`
        rw [hs] at hl1 hl2; rw [hs'] at hl1' hl2'
        exfalso
        apply h2
        have ht : v' δ.1 - v δ.1 = -1 := by
          have k1 : 20 * (C.r : ℤ) * (v δ.1 - v' δ.1) ≥ 10 * C.r + 2 := by linarith
          have k2 : 20 * (C.r : ℤ) * (v δ.1 - v' δ.1) ≤ 30 * C.r - 2 := by linarith
          by_contra hne
          rcases lt_or_gt_of_ne hne with hlt | hlt
          · have : (2 : ℤ) ≤ v δ.1 - v' δ.1 := by omega
            have := mul_le_mul_of_nonneg_left this hr
            linarith
          · have : v δ.1 - v' δ.1 ≤ 0 := by omega
            have := mul_le_mul_of_nonneg_left this hr
            linarith
        refine Prod.ext (eq_of_coords (u := v') (v := v + stepVec δ) δ.1 ?_ ?_) (MDir.eq_rev_of_sgOf (δ := δ) (δ' := δ') hax (by omega))
        · rw [Pi.add_apply, stepVec_apply_fst, hs]; omega
        · rw [Pi.add_apply, stepVec_apply_oth, add_zero]; exact hut.symm
      · -- same sign `-`
        by_cases hva : v δ.1 = v' δ.1
        · exact h1 (Prod.ext (eq_of_coords δ.1 hva.symm hut.symm) (MDir.eq_of_sgOf hax (by rw [hs, hs'])))
        · rw [hs] at hl1 hl2; rw [hs'] at hl1' hl2'
          rcases C.cen_gap hva with h | h <;> linarith
    · rcases C.cen_gap hut with h | h <;> linarith
  · -- perpendicular: `δ'.1 = oth δ.1`
    have hδ1 : δ'.1 = oth δ.1 := eq_oth_of_ne hax
    rw [hδ1] at hl1' hl2'
    by_cases hut : v (oth δ.1) = v' (oth δ.1)
    · rw [hut] at ht1 ht2
      rcases sgOf_sign δ' with hs' | hs' <;> rw [hs'] at hl1' hl2' <;> linarith
    · rcases C.cen_gap hut with h | h <;> rcases sgOf_sign δ' with hs' | hs' <;> rw [hs'] at hl1' hl2'
      · linarith
      · linarith
      · linarith
      · linarith

/-! ## Centres and the cover -/

/-- `cen 0 = 0`. [folklore] -/
theorem cen_zero : C.cen 0 = 0 := by
  funext j; simp [cen]

/-- A centre lies in a cell only if it is its centre. [folklore] -/
theorem eq_of_cen_mem_Cell {x u : Site 2} (h : C.cen x ∈ C.Cell u) : x = u := by
  by_contra hne
  obtain ⟨i, hi⟩ := exists_ne_of_ne hne
  have h1 := C.planar_of_mem_Cell h i
  rw [C.cen_pax] at h1
  have hr1 : (1 : ℤ) ≤ C.r := by exact_mod_cast C.r_pos
  rcases C.cen_gap hi with h2 | h2 <;> linarith

/-- A centre never lies in a stub zone. [folklore] -/
theorem cen_not_mem_Zone (x u : Site 2) (δ : MDir) : C.cen x ∉ C.Zone u δ := by
  intro h
  have hr : (0 : ℤ) ≤ 20 * C.r := by positivity
  have hr1 : (1 : ℤ) ≤ C.r := by exact_mod_cast C.r_pos
  have hs1 : (1 : ℤ) ≤ C.s := by exact_mod_cast C.hs
  obtain ⟨⟨h1, h2⟩, -⟩ := C.planar_of_mem_sBox h
  rw [C.cen_pax] at h1 h2
  rcases sgOf_sign δ with hs | hs <;> rw [hs] at h1 h2
  · rcases le_or_gt (x δ.1) (u δ.1) with hle | hlt
    · have := mul_le_mul_of_nonneg_left hle hr; linarith
    · have h4 : u δ.1 + 1 ≤ x δ.1 := hlt
      have := mul_le_mul_of_nonneg_left h4 hr; linarith
  · rcases le_or_gt (u δ.1) (x δ.1) with hle | hlt
    · have := mul_le_mul_of_nonneg_left hle hr; linarith
    · have h4 : x δ.1 + 1 ≤ u δ.1 := hlt
      have := mul_le_mul_of_nonneg_left h4 hr; linarith

/-- **A centre lies in the cover of a set of macro-vertices only if its vertex is in the set.**
[cite: KozmaNitzan2024, §4 p. 26 ((29))] -/
theorem mem_of_cen_mem_Cover {det : Set (Site 2)} {x : Site 2} (h : C.cen x ∈ C.Cover det) : x ∈ det := by
  simp only [Cover, Set.mem_iUnion, Set.mem_union, exists_prop, Finset.mem_coe] at h
  obtain ⟨u, hu, h | ⟨δ, h⟩⟩ := h
  · rwa [C.eq_of_cen_mem_Cell h]
  · exact absurd h (C.cen_not_mem_Zone x u δ)

end Cells

end KozmaNitzan

end Percolation.Literature

end

/-!
# Kozma–Nitzan, Theorem 6 — Step IV: the failure probability of one examination

Tenth proofs-only companion of
`KozmaNitzanReduction.lean` (G. Kozma, S. Nitzan, arXiv:2401.12397, §4 pp. 30–31), the probabilistic
half of the supercriticality bound (33): after a valid history, the examination of `v` from `w`
fails with probability at most `ε`.

For an onward direction `x = v + du` let `μ` be the weighting pinned on `ω|_{E_i}` and restricted to
`E_i ∪ E_{w,v} ∪ E_{v,x}` (`KSch.Wfull`), `A'_j = {0 ↔ F^{j+1} in E_i ∪ E_{w,v} ∪ H^{j+1}}` (`KSch.Aface`)
and `B_j = {P(0 ↔ F^{j+1} | ω|_{E_i ∪ E_{w,v} ∪ H^j}) ≤ 1 - δ₂}` (`KSch.Bev`). Then

* `real_Gev_le` — "for each `j`, if `B_j` happened then there is probability at least `δ₂` to not
  reach `F^{j+1}`, uniformly over the past" (p. 31): `μ(⋂_{i<j} (A'_i ∩ B_i)) ≤ (1 - δ₂)^j`, by the
  transfer of conditional bounds (`prodBernoulli_real_inter_le_of_pinW_le`) — under `μ` pinned on the
  pairs inside `E_i ∪ E_{w,v} ∪ H^j` along a pattern `T ∈ B_j` the weighting IS the weighting of (30);
* `real_bad_le` — (36)–(37): `μ(⋂_j B_j) ≤ (1 - δ₂)^K + ε/8`, since `{0 ↔ M_x}` forces all the `A'_j`
  (`reach_subset_Aface`, `Aface_subset_Aface`) and has probability `> 1 - ε/8` (`reach_bound`);
* `fail_bound` — (33): by Step III (`cond_of_face`) a bad direction lies in `⋂_j B_j`; the event is
  determined by fresh lattice edges, on which `μ` and `P_p` agree; summing over the `≤ 4` onward
  directions, `P_p(v is not declared open) ≤ ε`.

## References

* G. Kozma, S. Nitzan, arXiv:2401.12397 (2024), §4 pp. 30–31 (Steps III–IV, (33), (36), (37)).
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

namespace Percolation.Literature

open LatticeModels SimpleGraph GadgetSystem ProbeHistory Contour

namespace KozmaNitzan

variable {d : ℕ}

/-! ## Pairs and lattice-only configurations -/

/-- `pairsF` is monotone. [folklore] -/
theorem pairsF_mono {D D' : Finset (Site d)} (h : D ⊆ D') : pairsF D ⊆ pairsF D' := by
  intro e he
  rw [← Finset.mem_coe, coe_pairsF] at he ⊢
  exact wireSet_mono (Finset.coe_subset.2 h) he

/-- `lattOnly` is antitone. [folklore] -/
theorem lattOnly_anti {D D' : Finset (Site d)} (h : D ⊆ D') : lattOnly D' ⊆ lattOnly D :=
  fun _ hω e he heω => hω e (pairsF_mono h he) heω

/-- The lattice edges inside `D` are pairs inside `D`. [folklore] -/
theorem edgesIn_subset_pairsF (D : Finset (Site d)) : edgesIn (zdGraph d) D ⊆ pairsF D := by
  intro e he
  rw [mem_edgesIn_iff] at he
  rw [← Finset.mem_coe, coe_pairsF]
  exact ⟨fun x hx => Finset.mem_coe.2 (he.2 x hx), SimpleGraph.not_isDiag_of_mem_edgeSet _ he.1⟩

/-- `lattOnly D` is determined by the pairs inside `D`. [folklore] -/
theorem determinedBy_lattOnly (D : Finset (Site d)) : DeterminedBy (lattOnly D) (↑(pairsF D) : Set (Sym2 (Site d))) := by
  rw [determinedBy_iff]
  intro ω ω' hωω'
  simp only [lattOnly, Set.mem_setOf_eq]
  refine forall₂_congr fun e he => ?_
  have : e ∈ ω ↔ e ∈ ω' := by
    constructor
    · intro h1; exact ((Set.ext_iff.1 hωω' e).1 ⟨h1, Finset.mem_coe.2 he⟩).1
    · intro h1; exact ((Set.ext_iff.1 hωω' e).2 ⟨h1, Finset.mem_coe.2 he⟩).1
  rw [this]

namespace KSch

open Cells

variable (S : KSch d)

/-! ## The events of Step IV -/

/-- The pairs inside `E_i ∪ E_{w,v} ∪ H^j_{v,x}` (the coordinates conditioned on in `B_j`, p. 30).
[cite: KozmaNitzan2024, §4 p. 30 (B_j)] -/
def Fp (h : ProbeHistory (Site d)) (e : Site 2 × MDir) (du : MDir) (j : ℕ) : Finset (Sym2 (Site d)) :=
  pairsF (S.V h ∪ S.C.Ewv e.1 e.2 ∪ S.C.Stub (tgt e) du j)

/-- **The event `B_j`** `= {P(0 ↔ F^{j+1}_{v,x} | ω|_{E_i ∪ E_{w,v} ∪ H^j_{v,x}}) ≤ 1 - δ₂}`, the conditional
probability being that of (30) at level `j` for the observation `ω`. [cite: KozmaNitzan2024, §4 p. 30 (B_j)] -/
def Bev (h : ProbeHistory (Site d)) (e : Site 2 × MDir) (du : MDir) (j : ℕ) (δ₂ : ℝ) : Set (BondConfig (Site d)) :=
  {ω | (prodBernoulli (S.Wt h e du j (obs ω (S.env h e)))).real
      (⋃ b ∈ S.C.Face (tgt e) du (j + 1), openConn (0 : Site d) b) ≤ 1 - δ₂}

/-- `G_j = ⋂_{i<j} (A'_i ∩ B_i)`. [cite: KozmaNitzan2024, §4 p. 31 ((36))] -/
def Gev (h : ProbeHistory (Site d)) (e : Site 2 × MDir) (du : MDir) (δ₂ : ℝ) : ℕ → Set (BondConfig (Site d))
  | 0 => Set.univ
  | j + 1 => S.Aface h e du j ∩ (S.Bev h e du j δ₂ ∩ Gev h e du δ₂ j)

/-- **A bad direction**: the connection `v–x` is good at no level. [cite: KozmaNitzan2024, §4 p. 27 (j_x), p. 31] -/
def bad (h : ProbeHistory (Site d)) (e : Site 2 × MDir) (du : MDir) : Set (BondConfig (Site d)) :=
  {ω | ∀ j < S.C.K, ¬S.cond h e du j (obs ω (S.env h e))}

variable {S}

/-! ## Static inclusions -/

/-- `Q_v ⊆ E_{w,v}`. [folklore] -/
theorem Q_subset_Ewv (S : KSch d) (e : Site 2 × MDir) : S.C.Q (tgt e) ⊆ S.C.Ewv e.1 e.2 :=
  Finset.subset_union_right

/-- `E_i ∪ E_{w,v} ∪ H_{v,x} ⊆ E_i ∪ E_{w,v} ∪ E_{v,x}`. [folklore] -/
theorem regionH_subset_Sx (S : KSch d) (h : ProbeHistory (Site d)) (e : Site 2 × MDir) (du : MDir) :
    S.V h ∪ S.C.Ewv e.1 e.2 ∪ S.C.Hfull (tgt e) du ⊆ S.Sx h e du := by
  intro y hy
  rcases Finset.mem_union.1 hy with hy | hy
  · exact Finset.mem_union_left _ hy
  · rcases S.C.mem_Q_or_Efar_of_mem_Hfull hy with hy | hy
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Q_subset_Ewv S e hy))
    · exact Finset.mem_union_right _ hy

/-- `E_i ∪ E_{w,v} ∪ H^j_{v,x} ⊆ E_i ∪ E_{w,v} ∪ H_{v,x}` for `j ≤ K`. [folklore] -/
theorem region_subset_regionH (S : KSch d) (h : ProbeHistory (Site d)) (e : Site 2 × MDir) (du : MDir) {j : ℕ}
    (hj : j ≤ S.C.K) : S.V h ∪ S.C.Ewv e.1 e.2 ∪ S.C.Stub (tgt e) du j ⊆ S.V h ∪ S.C.Ewv e.1 e.2 ∪ S.C.Hfull (tgt e) du :=
  Finset.union_subset_union le_rfl (S.C.Stub_subset_Hfull _ _ hj)

/-- `E_i ∪ E_{w,v} ∪ H^j_{v,x} ⊆ E_i ∪ E_{w,v} ∪ E_{v,x}` for `j ≤ K`. [folklore] -/
theorem region_subset_Sx (S : KSch d) (h : ProbeHistory (Site d)) (e : Site 2 × MDir) (du : MDir) {j : ℕ}
    (hj : j ≤ S.C.K) : S.V h ∪ S.C.Ewv e.1 e.2 ∪ S.C.Stub (tgt e) du j ⊆ S.Sx h e du :=
  (region_subset_regionH S h e du hj).trans (regionH_subset_Sx S h e du)

/-- `Fj ⊆ Fp`. [folklore] -/
theorem Fj_subset_Fp (S : KSch d) (h : ProbeHistory (Site d)) (e : Site 2 × MDir) (du : MDir) (j : ℕ) :
    S.Fj h e du j ⊆ S.Fp h e du j :=
  edgesIn_subset_pairsF _

/-- `Fp` is monotone in the level. [folklore] -/
theorem Fp_mono (S : KSch d) (h : ProbeHistory (Site d)) (e : Site 2 × MDir) (du : MDir) {j j' : ℕ} (hjj' : j ≤ j') :
    S.Fp h e du j ⊆ S.Fp h e du j' :=
  pairsF_mono (Finset.union_subset_union le_rfl (S.C.stub_mono _ _ hjj'))

/-- The pairs of level `j ≤ K` lie inside `E_i ∪ E_{w,v} ∪ E_{v,x}`. [folklore] -/
theorem coe_Fp_subset_wireSet (S : KSch d) (h : ProbeHistory (Site d)) (e : Site 2 × MDir) (du : MDir) {j : ℕ}
    (hj : j ≤ S.C.K) : (↑(S.Fp h e du j) : Set (Sym2 (Site d))) ⊆ wireSet (↑(S.Sx h e du) : Set (Site d)) := by
  rw [Fp, coe_pairsF]
  exact wireSet_mono (Finset.coe_subset.2 (region_subset_Sx S h e du hj))

/-! ## Determination and measurability -/

/-- `B_j` is determined by the conditioned lattice edges of level `j`. [folklore] -/
theorem determinedBy_Bev (S : KSch d) (h : ProbeHistory (Site d)) (e : Site 2 × MDir) (du : MDir) (j : ℕ) (δ₂ : ℝ) :
    DeterminedBy (S.Bev h e du j δ₂) (↑(S.Fj h e du j) : Set (Sym2 (Site d))) := by
  rw [determinedBy_iff]
  intro ω ω' hωω'
  have key : S.pat h e du j (obs ω (S.env h e)) = S.pat h e du j (obs ω' (S.env h e)) := by
    refine S.pat_congr h e du j fun x hx => ?_
    have hxF : x ∈ S.Fj h e du j := (Finset.mem_sdiff.1 hx).1
    simp only [mem_obs_iff]
    refine and_congr_right fun _ => ⟨fun h1 => ?_, fun h1 => ?_⟩
    · exact ((Set.ext_iff.1 hωω' x).1 ⟨h1, Finset.mem_coe.2 hxF⟩).1
    · exact ((Set.ext_iff.1 hωω' x).2 ⟨h1, Finset.mem_coe.2 hxF⟩).1
  simp only [Bev, Set.mem_setOf_eq, Wt, key]

/-- A bad direction is determined by the fresh conditioned lattice edges of level `K - 1`. [folklore] -/
theorem determinedBy_bad (S : KSch d) (h : ProbeHistory (Site d)) (e : Site 2 × MDir) (du : MDir) :
    DeterminedBy (S.bad h e du) (↑(S.Fj h e du (S.C.K - 1) \ S.F h) : Set (Sym2 (Site d))) := by
  rw [determinedBy_iff]
  intro ω ω' hωω'
  simp only [bad, Set.mem_setOf_eq]
  refine forall₂_congr fun j hj => not_congr (S.cond_congr h e du j fun x hx => ?_)
  have hx' : x ∈ S.Fj h e du (S.C.K - 1) \ S.F h :=
    Finset.mem_sdiff.2 ⟨S.Fj_mono h e du (by omega) (Finset.mem_sdiff.1 hx).1, (Finset.mem_sdiff.1 hx).2⟩
  simp only [mem_obs_iff]
  refine and_congr_right fun _ => ⟨fun h1 => ?_, fun h1 => ?_⟩
  · exact ((Set.ext_iff.1 hωω' x).1 ⟨h1, Finset.mem_coe.2 hx'⟩).1
  · exact ((Set.ext_iff.1 hωω' x).2 ⟨h1, Finset.mem_coe.2 hx'⟩).1

/-- `A'_j` is determined by the pairs of level `j + 1`. [folklore] -/
theorem determinedBy_Aface (S : KSch d) (h : ProbeHistory (Site d)) (e : Site 2 × MDir) (du : MDir) (j : ℕ) :
    DeterminedBy (S.Aface h e du j) (↑(S.Fp h e du (j + 1)) : Set (Sym2 (Site d))) :=
  determinedBy_biUnion_openConnIn _ _ _ (by rw [Fp, coe_pairsF])

/-- `A'_j` is measurable. [folklore] -/
theorem measurableSet_Aface (S : KSch d) (h : ProbeHistory (Site d)) (e : Site 2 × MDir) (du : MDir) (j : ℕ) :
    MeasurableSet (S.Aface h e du j) :=
  measurableSet_biUnion_openConnIn _ _ _

/-- `G_j` is determined by the pairs of level `j`. [folklore] -/
theorem determinedBy_Gev (S : KSch d) (h : ProbeHistory (Site d)) (e : Site 2 × MDir) (du : MDir) (δ₂ : ℝ) :
    ∀ j, DeterminedBy (S.Gev h e du δ₂ j) (↑(S.Fp h e du j) : Set (Sym2 (Site d)))
  | 0 => determinedBy_univ _
  | j + 1 => by
    have hmono : (↑(S.Fp h e du j) : Set (Sym2 (Site d))) ⊆ ↑(S.Fp h e du (j + 1)) :=
      Finset.coe_subset.2 (Fp_mono S h e du (Nat.le_succ j))
    refine (determinedBy_Aface S h e du j).inter (DeterminedBy.inter ?_ ((determinedBy_Gev S h e du δ₂ j).mono hmono))
    exact (determinedBy_Bev S h e du j δ₂).mono ((Finset.coe_subset.2 (Fj_subset_Fp S h e du j)).trans hmono)

section Setting

variable {h : ProbeHistory (Site d)} {e : Site 2 × MDir} (hV : S.Valid h e) {du : MDir}
  (hdu : du ∈ S.onward h (tgt e))
include hV hdu

omit hdu in
/-- The explored edges are pairs of every level. [folklore] -/
theorem Valid.coe_F_subset_Fp (j : ℕ) : (↑(S.F h) : Set (Sym2 (Site d))) ⊆ ↑(S.Fp h e du j) :=
  Finset.coe_subset.2 ((S.F_subset_Fj hV.F_eq e du j).trans (Fj_subset_Fp S h e du j))

omit hdu in
/-- The explored edges are lattice edges. [folklore] -/
theorem Valid.mem_edgeSet_of_mem_F {x : Sym2 (Site d)} (hx : x ∈ S.F h) : x ∈ (zdGraph d).edgeSet := by
  rw [hV.F_eq, mem_edgesIn_iff] at hx
  exact hx.1

omit hdu in
/-- The explored edges lie inside `E_i ∪ E_{w,v} ∪ E_{v,x}`. [folklore] -/
theorem Valid.coe_F_subset_wireSet : (↑(S.F h) : Set (Sym2 (Site d))) ⊆ wireSet (↑(S.Sx h e du) : Set (Site d)) :=
  (Valid.coe_F_subset_Fp hV 0).trans (coe_Fp_subset_wireSet S h e du (Nat.zero_le _))

/-! ## Almost sure facts under `μ` -/

omit hdu in
/-- Under `μ` the pattern on the explored edges is the recorded one, almost surely. [folklore] -/
theorem Valid.ae_cyl : ∀ᵐ ω ∂prodBernoulli (S.Wfull h e du), ω ∈ localCylinder (↑(S.F h) : Set (Sym2 (Site d))) ↑(S.ξ h) := by
  have : S.Wfull h e du = pinW (restrW (↑(S.Sx h e du) : Set (Site d)) (lattW d S.p)) ↑(S.F h) ↑(S.ξ h) := by
    unfold Wfull
    exact restrW_pinW_comm _ _ (Valid.coe_F_subset_wireSet hV)
  rw [this]
  exact prodBernoulli_pinW_ae_localCylinder _ (S.F h).finite_toSet.countable _

omit hdu in
/-- Under `μ` no non-lattice pair is open, almost surely. [folklore] -/
theorem Valid.ae_forall_notMem : ∀ᵐ ω ∂prodBernoulli (S.Wfull h e du),
    ∀ x ∈ {x : Sym2 (Site d) | x ∉ (zdGraph d).edgeSet}, x ∉ ω := by
  refine prodBernoulli_ae_forall_notMem _ (Set.to_countable _) fun x hx => ?_
  unfold Wfull
  by_cases hxS : x ∈ wireSet (↑(S.Sx h e du) : Set (Site d))
  · rw [restrW_apply_of_mem _ hxS, pinW_apply_of_not_mem _ _ (fun hxF => hx (Valid.mem_edgeSet_of_mem_F hV hxF))]
    rw [lattW_apply, if_neg hx]
  · exact restrW_apply_of_not_mem _ hxS

omit hdu in
/-- Under `μ` every `lattOnly D` holds almost surely. [folklore] -/
theorem Valid.ae_lattOnly (D : Finset (Site d)) : ∀ᵐ ω ∂prodBernoulli (S.Wfull h e du), ω ∈ lattOnly D := by
  filter_upwards [Valid.ae_forall_notMem hV (du := du)] with ω hω
  intro x _ hxω
  by_contra hx
  exact hω x hx hxω

/-! ## The transfer: pinning `μ` on the pairs of level `j` gives the weighting of (30) -/

/-- **Under `μ` pinned on the pairs inside `E_i ∪ E_{w,v} ∪ H^j` along a lattice pattern `T` extending
`ω|_{E_i}`, the weighting is that of (30) at level `j` for the observation `T`.**
[cite: KozmaNitzan2024, §4 p. 30 (Step III: "usual percolation on this auxiliary graph is identical to conditioned percolation on Ω")] -/
theorem pinW_Wfull_eq_Wt {j : ℕ} (hj : j < S.C.K) {T : Finset (Sym2 (Site d))}
    (hTc : (↑T : Set (Sym2 (Site d))) ∈ localCylinder (↑(S.F h) : Set (Sym2 (Site d))) ↑(S.ξ h))
    (hTl : (↑T : Set (Sym2 (Site d))) ∈ lattOnly (S.V h ∪ S.C.Ewv e.1 e.2 ∪ S.C.Stub (tgt e) du j)) :
    pinW (S.Wfull h e du) ↑(S.Fp h e du j) ↑T = S.Wt h e du j (obs ↑T (S.env h e)) := by
  have hFpS := coe_Fp_subset_wireSet S h e du hj.le
  funext x
  unfold Wt Wfull
  by_cases hxP : x ∈ S.Fp h e du j
  · have hxS : x ∈ wireSet (↑(S.Sx h e du) : Set (Site d)) := hFpS (Finset.mem_coe.2 hxP)
    rw [restrW_apply_of_mem _ hxS]
    by_cases hxj : x ∈ S.Fj h e du j
    · -- a lattice edge of level `j`: both sides read the pattern
      have hiff : x ∈ (↑(S.pat h e du j (obs ↑T (S.env h e))) : Set (Sym2 (Site d))) ↔ x ∈ (↑T : Set (Sym2 (Site d))) := by
        rw [Finset.mem_coe, Finset.mem_coe, pat, Finset.mem_union, Finset.mem_inter, mem_obs_iff, Finset.mem_sdiff,
          Finset.mem_coe]
        by_cases hxF : x ∈ S.F h
        · have h1 := hTc x (Finset.mem_coe.2 hxF)
          rw [Finset.mem_coe, Finset.mem_coe] at h1
          constructor
          · rintro (h2 | ⟨-, -, h3⟩)
            · exact h1.2 h2
            · exact absurd hxF h3
          · intro h2; exact Or.inl (h1.1 h2)
        · have hxenv : x ∈ S.env h e := S.Fj_sdiff_subset_env h e hdu hj (Finset.mem_sdiff.2 ⟨hxj, hxF⟩)
          constructor
          · rintro (h2 | ⟨⟨-, h3⟩, -, -⟩)
            · exact absurd (hV.ξ_sub h2) hxF
            · exact h3
          · intro h2; exact Or.inr ⟨⟨hxenv, h2⟩, hxj, hxF⟩
      by_cases hxT : x ∈ (↑T : Set (Sym2 (Site d)))
      · rw [pinW_apply_of_mem_of_mem _ (Finset.mem_coe.2 hxP) hxT,
          pinW_apply_of_mem_of_mem _ (Finset.mem_coe.2 hxj) (hiff.2 hxT)]
      · rw [pinW_apply_of_mem_of_not_mem _ (Finset.mem_coe.2 hxP) hxT,
          pinW_apply_of_mem_of_not_mem _ (Finset.mem_coe.2 hxj) (fun h' => hxT (hiff.1 h'))]
    · -- a non-lattice pair of level `j`: closed on both sides
      have hxE : x ∉ (zdGraph d).edgeSet := by
        intro hxE
        apply hxj
        rw [Fj, mem_edgesIn_iff]
        refine ⟨hxE, fun y hy => ?_⟩
        have := (Finset.mem_coe.2 hxP : x ∈ (↑(S.Fp h e du j) : Set (Sym2 (Site d))))
        rw [Fp, coe_pairsF] at this
        exact Finset.mem_coe.1 (this.1 y hy)
      have hxT : x ∉ (↑T : Set (Sym2 (Site d))) := fun hxT => hxE (hTl x hxP hxT)
      rw [pinW_apply_of_mem_of_not_mem _ (Finset.mem_coe.2 hxP) hxT, pinW_apply_of_not_mem _ _ (fun h' => hxj (Finset.mem_coe.1 h')),
        lattW_apply, if_neg hxE]
  · have hxj : x ∉ (↑(S.Fj h e du j) : Set (Sym2 (Site d))) := fun h' => hxP (Fj_subset_Fp S h e du j (Finset.mem_coe.1 h'))
    have hxF : x ∉ (↑(S.F h) : Set (Sym2 (Site d))) := fun h' => hxP (Finset.mem_coe.1 (Valid.coe_F_subset_Fp hV j h'))
    rw [pinW_apply_of_not_mem _ _ (fun h' => hxP (Finset.mem_coe.1 h'))]
    by_cases hxS : x ∈ wireSet (↑(S.Sx h e du) : Set (Site d))
    · rw [restrW_apply_of_mem _ hxS, restrW_apply_of_mem _ hxS, pinW_apply_of_not_mem _ _ hxF, pinW_apply_of_not_mem _ _ hxj]
    · rw [restrW_apply_of_not_mem _ hxS, restrW_apply_of_not_mem _ hxS]

/-! ## The chain (36) -/

/-- **One step of the chain**: `μ(A'_j ∩ B_j ∩ G ∩ [ξ] ∩ L_j) ≤ (1 - δ₂) μ(B_j ∩ G ∩ [ξ] ∩ L_j)` for
`G` determined by the pairs of level `j` ("if `B_j` happened then there is probability at least `δ₂`
to not reach `F^{j+1}`, and this bound holds uniformly over … any `j' < j`", p. 31).
[cite: KozmaNitzan2024, §4 p. 31 ((36))] -/
theorem real_Aface_inter_le {δ₂ : ℝ} {j : ℕ} (hj : j < S.C.K) {G : Set (BondConfig (Site d))}
    (hG : DeterminedBy G (↑(S.Fp h e du j) : Set (Sym2 (Site d)))) :
    (prodBernoulli (S.Wfull h e du)).real (S.Aface h e du j ∩ (S.Bev h e du j δ₂ ∩ G ∩
        localCylinder (↑(S.F h) : Set (Sym2 (Site d))) ↑(S.ξ h) ∩ lattOnly (S.V h ∪ S.C.Ewv e.1 e.2 ∪ S.C.Stub (tgt e) du j))) ≤
      (1 - δ₂) * (prodBernoulli (S.Wfull h e du)).real (S.Bev h e du j δ₂ ∩ G ∩
        localCylinder (↑(S.F h) : Set (Sym2 (Site d))) ↑(S.ξ h) ∩ lattOnly (S.V h ∪ S.C.Ewv e.1 e.2 ∪ S.C.Stub (tgt e) du j)) := by
  have hB : DeterminedBy (S.Bev h e du j δ₂ ∩ G ∩ localCylinder (↑(S.F h) : Set (Sym2 (Site d))) ↑(S.ξ h) ∩
      lattOnly (S.V h ∪ S.C.Ewv e.1 e.2 ∪ S.C.Stub (tgt e) du j)) (↑(S.Fp h e du j) : Set (Sym2 (Site d))) := by
    refine (((determinedBy_Bev S h e du j δ₂).mono (Finset.coe_subset.2 (Fj_subset_Fp S h e du j))).inter hG).inter
      ((determinedBy_localCylinder _ _).mono (Valid.coe_F_subset_Fp hV j)) |>.inter ?_
    exact determinedBy_lattOnly _
  refine prodBernoulli_real_inter_le_of_pinW_le _ _ (measurableSet_Aface S h e du j) hB fun T _ hTB => ?_
  obtain ⟨⟨⟨hTB, -⟩, hTc⟩, hTl⟩ := hTB
  have hTB' : (prodBernoulli (S.Wt h e du j (obs ↑T (S.env h e)))).real
      (⋃ b ∈ S.C.Face (tgt e) du (j + 1), openConn (0 : Site d) b) ≤ 1 - δ₂ := hTB
  rw [pinW_Wfull_eq_Wt hV hdu hj hTc hTl]
  refine le_trans (measureReal_mono ?_ (measure_ne_top _ _)) hTB'
  rw [← Finset.set_biUnion_coe]
  exact biUnion_openConnIn_subset_biUnion_openConn _ _ _

/-- **The chain**: `μ(G_j ∩ [ξ]) ≤ (1 - δ₂)^j` for `j ≤ K`. [cite: KozmaNitzan2024, §4 p. 31 ((36))] -/
theorem real_Gev_le {δ₂ : ℝ} (hδ₂ : δ₂ ≤ 1) :
    ∀ j ≤ S.C.K, (prodBernoulli (S.Wfull h e du)).real (S.Gev h e du δ₂ j ∩ localCylinder (↑(S.F h) : Set (Sym2 (Site d))) ↑(S.ξ h)) ≤
      (1 - δ₂) ^ j
  | 0, _ => by rw [pow_zero]; exact measureReal_le_one
  | j + 1, hj => by
    set μ := prodBernoulli (S.Wfull h e du) with hμ
    set Cyl := localCylinder (↑(S.F h) : Set (Sym2 (Site d))) (↑(S.ξ h) : Set (Sym2 (Site d))) with hCyl
    set L := lattOnly (S.V h ∪ S.C.Ewv e.1 e.2 ∪ S.C.Stub (tgt e) du j) with hL
    have hj' : j < S.C.K := by omega
    have ih := real_Gev_le hδ₂ j hj'.le
    have e1 : μ.real (S.Gev h e du δ₂ (j + 1) ∩ Cyl) =
        μ.real (S.Aface h e du j ∩ (S.Bev h e du j δ₂ ∩ S.Gev h e du δ₂ j ∩ Cyl ∩ L)) := by
      refine measureReal_congr ?_
      filter_upwards [Valid.ae_lattOnly hV (du := du) (S.V h ∪ S.C.Ewv e.1 e.2 ∪ S.C.Stub (tgt e) du j)] with ω hωL
      refine propext ⟨?_, ?_⟩
      · rintro ⟨⟨hA, hB, hG⟩, hC⟩; exact ⟨hA, ⟨⟨hB, hG⟩, hC⟩, hωL⟩
      · rintro ⟨hA, ⟨⟨hB, hG⟩, hC⟩, -⟩; exact ⟨⟨hA, hB, hG⟩, hC⟩
    rw [e1]
    refine (real_Aface_inter_le hV hdu hj' (determinedBy_Gev S h e du δ₂ j)).trans ?_
    rw [pow_succ, mul_comm ((1 - δ₂) ^ j)]
    refine mul_le_mul_of_nonneg_left (le_trans (measureReal_mono ?_ (measure_ne_top _ _)) ih) (by linarith)
    rintro ω ⟨⟨⟨-, hG⟩, hC⟩, -⟩
    exact ⟨hG, hC⟩

/-! ## (36)–(37): a bad direction is unlikely under `μ` -/

/-- Reaching `M_x` through the corridor forces all the `A'_j`. [cite: KozmaNitzan2024, §4 p. 31 ("to hit M_x via H_{v,x} you must pass through all the F^j")] -/
theorem mem_Aface_of_reach {ω : BondConfig (Site d)} (hωL : ω ∈ lattOnly (S.V h ∪ S.C.Ewv e.1 e.2 ∪ S.C.Hfull (tgt e) du))
    (hR : ω ∈ S.Reach h e du) {j : ℕ} (hj : j < S.C.K) : ω ∈ S.Aface h e du j := by
  have main : ∀ m, m < S.C.K → ω ∈ S.Aface h e du (S.C.K - 1 - m) := by
    intro m
    induction m with
    | zero => intro _; exact reach_subset_Aface hV hdu hωL hR
    | succ m ih =>
      intro hm
      have h1 := ih (by omega)
      have h2 : S.C.K - 1 - (m + 1) = S.C.K - 1 - m - 1 := by omega
      rw [h2]
      refine Aface_subset_Aface hV hdu (by omega) (by omega) ?_ h1
      exact lattOnly_anti (region_subset_regionH S h e du (by omega)) hωL
  have := main (S.C.K - 1 - j) (by omega)
  have h3 : S.C.K - 1 - (S.C.K - 1 - j) = j := by omega
  rwa [h3] at this

omit hV hdu in
/-- All `B_j` and all `A'_j` give `G_K`. [folklore] -/
theorem mem_Gev_of_forall {δ₂ : ℝ} {ω : BondConfig (Site d)} (hB : ∀ j < S.C.K, ω ∈ S.Bev h e du j δ₂)
    (hA : ∀ j < S.C.K, ω ∈ S.Aface h e du j) : ∀ j ≤ S.C.K, ω ∈ S.Gev h e du δ₂ j
  | 0, _ => Set.mem_univ _
  | j + 1, hj => ⟨hA j (by omega), hB j (by omega), mem_Gev_of_forall hB hA j (by omega)⟩

/-- **Step III inside Step IV**: a bad direction lies in every `B_j`. [cite: KozmaNitzan2024, §4 p. 30 (Step III)] -/
theorem bad_subset_Bev {δ₂ : ℝ} {R : ℕ}
    (htgt : ∀ (W : Sym2 (Site d) → unitInterval) (Sfin D : Finset (Site d)) (lo hi : Site d)
      (T : Finset (Site d)) (o : Site d),
      FinSupp W Sfin → IsSubbox W S.p D → D ⊆ Sfin → o ∈ Sfin → o ∉ D →
      Finset.Icc (lo - (R : Site d)) (hi + (R : Site d)) ⊆ D →
      IsTarget T lo hi D R (elongList d (2 * S.C.K) (by have := S.C.hK; omega)) → T ⊆ D → T.Nonempty →
      1 - δ₂ < (prodBernoulli W).real (⋃ b ∈ Finset.Icc lo hi, openConn o b) →
      1 - S.δc < (prodBernoulli W).real (⋃ t ∈ T, openConn o t))
    (hRs : 2 * R ≤ S.C.s) {j : ℕ} (hj : j < S.C.K) : S.bad h e du ⊆ S.Bev h e du j δ₂ := by
  intro ω hω
  by_contra hB
  simp only [Bev, Set.mem_setOf_eq, not_le] at hB
  exact hω j hj (cond_of_face hV hdu htgt hRs hj _ hB)

/-- **(36)–(37) for one direction**: `μ(bad) ≤ (1 - δ₂)^K + ε'`, given Lemma 12 (`hcorr`, at `ε'`)
and the target lemma (`htgt`). [cite: KozmaNitzan2024, §4 p. 31 ((36), (37))] -/
theorem real_bad_le {ε' δ₂ : ℝ} (hδ₂ : δ₂ ≤ 1) {R : ℕ}
    (hcorr : ∀ T : CData d, T.Hyp S.p → T.r = S.C.r →
      1 - S.δc < (prodBernoulli T.W).real
          (⋃ b ∈ Finset.Icc (T.c - ((3 * T.r : ℕ) : Site d)) (T.c + ((3 * T.r : ℕ) : Site d)),
            openConnIn (↑T.Aset : Set (Site d)) T.o b) →
        1 - ε' < (prodBernoulli T.W).real (⋃ b ∈ T.Tn (3 * T.r), openConnIn (↑T.Uset : Set (Site d)) T.o b))
    (htgt : ∀ (W : Sym2 (Site d) → unitInterval) (Sfin D : Finset (Site d)) (lo hi : Site d)
      (T : Finset (Site d)) (o : Site d),
      FinSupp W Sfin → IsSubbox W S.p D → D ⊆ Sfin → o ∈ Sfin → o ∉ D →
      Finset.Icc (lo - (R : Site d)) (hi + (R : Site d)) ⊆ D →
      IsTarget T lo hi D R (elongList d (2 * S.C.K) (by have := S.C.hK; omega)) → T ⊆ D → T.Nonempty →
      1 - δ₂ < (prodBernoulli W).real (⋃ b ∈ Finset.Icc lo hi, openConn o b) →
      1 - S.δc < (prodBernoulli W).real (⋃ t ∈ T, openConn o t))
    (hRs : 2 * R ≤ S.C.s) :
    (prodBernoulli (S.Wfull h e du)).real (S.bad h e du) ≤ (1 - δ₂) ^ S.C.K + ε' := by
  set μ := prodBernoulli (S.Wfull h e du) with hμ
  set Cyl := localCylinder (↑(S.F h) : Set (Sym2 (Site d))) (↑(S.ξ h) : Set (Sym2 (Site d))) with hCyl
  set L := lattOnly (S.V h ∪ S.C.Ewv e.1 e.2 ∪ S.C.Hfull (tgt e) du) with hL
  have hreach : 1 - ε' < μ.real (S.Reach h e du) := reach_bound hV hdu hcorr
  have hRm : MeasurableSet (S.Reach h e du) := measurableSet_biUnion_openConnIn _ _ _
  have hae : ∀ᵐ ω ∂μ, ω ∈ Cyl ∩ L := by
    filter_upwards [Valid.ae_cyl hV (du := du),
      Valid.ae_lattOnly hV (du := du) (S.V h ∪ S.C.Ewv e.1 e.2 ∪ S.C.Hfull (tgt e) du)] with ω h1 h2
    exact ⟨h1, h2⟩
  have hnull : μ.real (Cyl ∩ L)ᶜ = 0 := by
    have : μ (Cyl ∩ L)ᶜ = 0 := mem_ae_iff.1 hae
    exact (measureReal_eq_zero_iff (measure_ne_top _ _)).2 this
  have h1 : μ.real (S.bad h e du) ≤ μ.real (S.bad h e du ∩ (Cyl ∩ L)) + μ.real (Cyl ∩ L)ᶜ := by
    refine le_trans (measureReal_mono ?_ (measure_ne_top _ _)) (measureReal_union_le _ _)
    intro ω hω
    by_cases h' : ω ∈ Cyl ∩ L
    · exact Or.inl ⟨hω, h'⟩
    · exact Or.inr h'
  have h2 : S.bad h e du ∩ (Cyl ∩ L) ⊆ (S.Gev h e du δ₂ S.C.K ∩ Cyl) ∪ (S.Reach h e du)ᶜ := by
    rintro ω ⟨hω, hC, hωL⟩
    by_cases hR : ω ∈ S.Reach h e du
    · refine Or.inl ⟨mem_Gev_of_forall (fun j hj => bad_subset_Bev hV hdu htgt hRs hj hω)
        (fun j hj => mem_Aface_of_reach hV hdu hωL hR hj) _ le_rfl, hC⟩
    · exact Or.inr hR
  have h3 : μ.real (S.Reach h e du)ᶜ < ε' := by
    rw [probReal_compl_eq_one_sub hRm]; linarith
  calc μ.real (S.bad h e du) ≤ μ.real (S.bad h e du ∩ (Cyl ∩ L)) + μ.real (Cyl ∩ L)ᶜ := h1
    _ ≤ μ.real ((S.Gev h e du δ₂ S.C.K ∩ Cyl) ∪ (S.Reach h e du)ᶜ) + 0 := by
        rw [hnull]; exact add_le_add (measureReal_mono h2 (measure_ne_top _ _)) le_rfl
    _ ≤ μ.real (S.Gev h e du δ₂ S.C.K ∩ Cyl) + μ.real (S.Reach h e du)ᶜ := by
        rw [add_zero]; exact measureReal_union_le _ _
    _ ≤ (1 - δ₂) ^ S.C.K + ε' := add_le_add (real_Gev_le hV hdu hδ₂ _ le_rfl) h3.le

/-! ## Back to `P_p`, and the sum over the onward directions: (33) -/

omit hV hdu in
/-- **`P_p(bad) = μ(bad)`**: a bad direction is determined by fresh conditioned lattice edges, on which
`μ` and the lattice weighting agree (Step II, p. 29: "the result we proved in `Ω` is equivalent to the
result in `ℤ^d`"). [cite: KozmaNitzan2024, §4 p. 29 (Step II), p. 31] -/
theorem real_bad_eq : (bondPercolation (zdGraph d) S.p).real (S.bad h e du) = (prodBernoulli (S.Wfull h e du)).real (S.bad h e du) := by
  have hK1 : S.C.K - 1 ≤ S.C.K := Nat.sub_le _ _
  have hdet := determinedBy_bad S h e du
  rw [← prodBernoulli_lattW]
  refine prodBernoulli_real_eq_of_determinedBy _ _ (fun x hx => ?_) hdet hdet.measurableSet_of_finset
  obtain ⟨hx1, hx2⟩ := Finset.mem_sdiff.1 (Finset.mem_coe.1 hx)
  have hxS : x ∈ wireSet (↑(S.Sx h e du) : Set (Site d)) :=
    coe_Fp_subset_wireSet S h e du hK1 (Finset.mem_coe.2 (Fj_subset_Fp S h e du _ hx1))
  unfold Wfull
  rw [restrW_apply_of_mem _ hxS, pinW_apply_of_not_mem _ _ (fun h' => hx2 (Finset.mem_coe.1 h'))]

omit hV hdu in
/-- A failed examination has a bad onward direction. [cite: KozmaNitzan2024, §4 p. 27 (j_x), p. 31] -/
theorem not_succ_subset (S : KSch d) (h : ProbeHistory (Site d)) (e : Site 2 × MDir) :
    {ω | ¬S.succ h e ((S.probe h e).read ω)} ⊆ ⋃ du ∈ S.onward h (tgt e), S.bad h e du := by
  intro ω hω
  simp only [Set.mem_setOf_eq, S.succ_read_iff] at hω
  simp only [succ] at hω
  push Not at hω
  obtain ⟨du, hdu, hc⟩ := hω
  simp only [Set.mem_iUnion, exists_prop]
  refine ⟨du, hdu, ?_⟩
  exact forall_not_of_not_jIdx (P := fun j => S.cond h e du j (obs ω (S.env h e))) (by have := S.C.hK; omega) hc

omit hdu in
/-- **(33): the examination fails with probability at most `ε`** — after a valid history, given
Lemma 12 at `ε/8` (`hcorr`), the target lemma with `δ_{L10} = δ₂ ≤ 1` and its `R ≤ s/2` (`htgt`), and
`(1 - δ₂)^K + ε/8 ≤ ε/4`. [cite: KozmaNitzan2024, §4 pp. 28–31 ((33), Steps I–IV)] -/
theorem fail_bound {ε δ₂ : ℝ} (hε : 0 ≤ ε) (hδ₂ : δ₂ ≤ 1) {R : ℕ}
    (hcorr : ∀ T : CData d, T.Hyp S.p → T.r = S.C.r →
      1 - S.δc < (prodBernoulli T.W).real
          (⋃ b ∈ Finset.Icc (T.c - ((3 * T.r : ℕ) : Site d)) (T.c + ((3 * T.r : ℕ) : Site d)),
            openConnIn (↑T.Aset : Set (Site d)) T.o b) →
        1 - ε / 8 < (prodBernoulli T.W).real (⋃ b ∈ T.Tn (3 * T.r), openConnIn (↑T.Uset : Set (Site d)) T.o b))
    (htgt : ∀ (W : Sym2 (Site d) → unitInterval) (Sfin D : Finset (Site d)) (lo hi : Site d)
      (T : Finset (Site d)) (o : Site d),
      FinSupp W Sfin → IsSubbox W S.p D → D ⊆ Sfin → o ∈ Sfin → o ∉ D →
      Finset.Icc (lo - (R : Site d)) (hi + (R : Site d)) ⊆ D →
      IsTarget T lo hi D R (elongList d (2 * S.C.K) (by have := S.C.hK; omega)) → T ⊆ D → T.Nonempty →
      1 - δ₂ < (prodBernoulli W).real (⋃ b ∈ Finset.Icc lo hi, openConn o b) →
      1 - S.δc < (prodBernoulli W).real (⋃ t ∈ T, openConn o t))
    (hRs : 2 * R ≤ S.C.s) (hKε : (1 - δ₂) ^ S.C.K + ε / 8 ≤ ε / 4) :
    (bondPercolation (zdGraph d) S.p).real {ω | ¬S.succ h e ((S.probe h e).read ω)} ≤ ε := by
  have hcard : ((S.onward h (tgt e)).card : ℝ) ≤ 4 := by
    have h1 : (S.onward h (tgt e)).card ≤ Fintype.card MDir := Finset.card_le_univ _
    have h2 : Fintype.card MDir = 4 := by simp [MDir, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
    have h3 : (S.onward h (tgt e)).card ≤ 4 := h2 ▸ h1
    exact_mod_cast h3
  calc (bondPercolation (zdGraph d) S.p).real {ω | ¬S.succ h e ((S.probe h e).read ω)}
      ≤ (bondPercolation (zdGraph d) S.p).real (⋃ du ∈ S.onward h (tgt e), S.bad h e du) :=
        measureReal_mono (not_succ_subset S h e) (measure_ne_top _ _)
    _ ≤ ∑ du ∈ S.onward h (tgt e), (bondPercolation (zdGraph d) S.p).real (S.bad h e du) :=
        measureReal_biUnion_finset_le _ _
    _ ≤ ∑ du ∈ S.onward h (tgt e), ε / 4 := by
        refine Finset.sum_le_sum fun du hdu' => ?_
        rw [real_bad_eq]
        exact (real_bad_le hV hdu' hδ₂ hcorr htgt hRs).trans hKε
    _ = (S.onward h (tgt e)).card * (ε / 4) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 4 * (ε / 4) := mul_le_mul_of_nonneg_right hcard (by linarith)
    _ = ε := by ring

end Setting

end KSch

end KozmaNitzan

end Percolation.Literature

end
