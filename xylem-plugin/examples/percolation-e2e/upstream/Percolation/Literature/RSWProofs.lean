import Percolation.Literature.HarrisLocal
import Percolation.Literature.LatticeSymmetry
import Percolation.Literature.PlanarDuality
import Percolation.Literature.RSW
import Percolation.Util.Linter

/-!
# Russo–Seymour–Welsh theory on `ℤ²`: proofs of the duality and gluing steps

Companion ("Proofs") file of `RSW.lean`, discharging three
of the named facts of the decomposition of `Percolation.Literature.rsw_half`:

* `Percolation.Literature.crossingProb_add_crossingProb_symm_holds` (Bollobás–Riordan, *Percolation*
  (2006), Ch. 3, Corollary 3(i); Grimmett, *Percolation* (1999), §11.2 and Lemma 11.21):
  `crossingProb p (m + 1) n + crossingProb (1 - p) (n + 1) m = 1`. From
  `crossingProb_add_real_dualTBCrossing_holds` (`P_p(LR) + P_p(TB*) = 1`, `PlanarDuality.lean`),
  the law `P_p ∘ dualConfig⁻¹ = P_{1-p}` of the dual configuration
  (`bondPercolation_map_dualConfig_holds`, `Crossings.lean`) and the identification of the dual
  rectangle of `[0, m + 1] × [0, n]` with the translate by `(0, -1)` of `[0, m] × [0, n + 1]`,
  whose vertical crossing probability is `crossingProb (1 - p) (n + 1) m` (`real_tbCrossing`,
  `real_openCrossing_shift`, `LatticeSymmetry.lean`).
* `Percolation.Literature.crossingProb_half_succ_self_holds` (Bollobás–Riordan Ch. 3, Corollary 3(ii);
  Grimmett 1999, Lemma 11.21): `crossingProb ½ (n + 1) n = 1/2`, the case `p = 1/2`, `m = n`.
* `Percolation.Literature.crossingProb_glue_holds` (Bollobás–Riordan Ch. 3, eq. (2) with Figure 7, and
  §3.4, eq. (12); Grimmett 1999, Lemma 11.75): for `n ≤ m₁, m₂`,
  `crossingProb p m₁ n * crossingProb p m₂ n * crossingProb p n n ≤ crossingProb p (m₁ + m₂ - n) n`.
  Put `R₁ = [0, m₁] × [0, n]`, `S = [m₁ - n, m₁] × [0, n]`, `R₂ = [m₁ - n, m₁ + m₂ - n] × [0, n]`,
  so that `R₁ ∩ R₂ = S` and `R₁ ∪ R₂ = [0, m₁ + m₂ - n] × [0, n]`.
  - Deterministic step (`lrCrossing_of_glue`): if `R₁` and `R₂` have open horizontal crossings
    `P₁`, `P₂` and `S` has an open vertical crossing `Q`, then the part of `P₁` after its last
    visit to the left side of `S` and the part of `P₂` before its first visit to the right side
    of `S` are horizontal crossings of `S` (`exists_openConnIn_column_ge`,
    `exists_openConnIn_column`), so both meet `Q` (`exists_mem_support_of_crossing`, the discrete
    Jordan-curve lemma of `PlanarDuality.lean`), and `P₁ ∪ Q ∪ P₂` contains an open horizontal
    crossing of `R₁ ∪ R₂` ("this path must meet both some horizontal crossing of `R₁` and some
    horizontal crossing of `R₂`", Bollobás–Riordan, proof of eq. (2)).
  - Probabilistic step: the three crossing events are increasing and local, so by Harris's lemma
    (`harris_fkg_local`, twice) the probability of their intersection is at least the product of
    their probabilities; the crossing probabilities of the translated rectangle `R₂` and of the
    square `S` (vertical) are `crossingProb p m₂ n` and `crossingProb p n n` by translation
    invariance and transposition symmetry of `P_p` (`real_openCrossing_shift`, `real_tbCrossing`).

Mathlib anchors: `SimpleGraph.Walk`, `Set.image_add_right`, `MeasureTheory.map_measureReal_apply`,
`MeasureTheory.measure_mono_ae`; tree anchors: `exists_mem_support_of_crossing`,
`exists_walk_of_mem_openConnIn`, `mem_openConnIn_of_mem_support`, `isLocalEvent_openCrossing`,
`measurable_dualConfig`, `crossingProb_add_real_dualTBCrossing_holds` (`PlanarDuality.lean`),
`bondPercolation_map_dualConfig_holds` (`Crossings.lean`), `exists_openConnIn_column`,
`openConnIn_mono`, `symm_half` (`RSW.lean`), `harris_fkg_local` (`HarrisLocal.lean`),
`real_openCrossing_shift`, `real_tbCrossing` (`LatticeSymmetry.lean`).

## References
* B. Bollobás, O. Riordan, *Percolation*, CUP (2006), Ch. 3, Lemma 1, Corollary 3, eq. (2),
  eq. (12) [BollobasRiordanPercolation2006].
* G. Grimmett, *Percolation*, 2nd ed., Springer (1999), §11.2, Lemma 11.21, Lemma 11.75
  [GrimmettPercolation1999].
-/

namespace Percolation.Literature

open MeasureTheory SimpleGraph

noncomputable section

/-! ### Last visit to a column -/

/-- Mirror image of `exists_openConnIn_column`: for a lattice configuration `ω`, an open path
inside `S` from `x` with `a ≤ x₀` to `y` with `y₀ ≤ a` contains an initial segment inside
`S ∩ {a ≤ z₀}` ending on the column `{z₀ = a}`. Applied to the reversed path this isolates the
part of a left-right crossing after its *last* visit to a column. (Kesten 1982, §2.2; used
implicitly in Bollobás–Riordan 2006, Ch. 3, proof of eq. (2).) [folklore] -/
theorem exists_openConnIn_column_ge {ω : BondConfig (LatticeModels.Site 2)} (hω : ω ⊆ (LatticeModels.zdGraph 2).edgeSet)
    {S : Set (LatticeModels.Site 2)} {x y : LatticeModels.Site 2} (a : ℤ) (hx : a ≤ x 0) (hy : y 0 ≤ a)
    (h : ω ∈ openConnIn S x y) :
    ∃ z, z 0 = a ∧ ω ∈ openConnIn (S ∩ {z | a ≤ z 0}) x z := by
  obtain ⟨hxS, hyS, ⟨p⟩⟩ := h
  suffices H : ∀ (u v : S) (p : ((openGraph ω).induce S).Walk u v), a ≤ (u : LatticeModels.Site 2) 0 →
      (v : LatticeModels.Site 2) 0 ≤ a → ∃ z, z 0 = a ∧ ω ∈ openConnIn (S ∩ {z | a ≤ z 0}) u z from
    H ⟨x, hxS⟩ ⟨y, hyS⟩ p hx hy
  intro u v p
  induction p with
  | nil =>
    intro hu hv
    rename_i u
    exact ⟨u, le_antisymm hv hu, ⟨u.2, hu⟩, ⟨u.2, hu⟩, SimpleGraph.Reachable.refl _⟩
  | cons hadj p ih =>
    intro hu hv
    rename_i u w v'
    rcases hu.eq_or_lt with hua | hua
    · exact ⟨u, hua.symm, ⟨u.2, hu⟩, ⟨u.2, hu⟩, SimpleGraph.Reachable.refl _⟩
    · have hadj' : (openGraph ω).Adj u w := hadj
      have hw : a ≤ (w : LatticeModels.Site 2) 0 := by
        have hzd : (LatticeModels.zdGraph 2).Adj (u : LatticeModels.Site 2) (w : LatticeModels.Site 2) :=
          hω ((openGraph_adj _ _ _).1 hadj').1
        have := (zdGraph_adj_apply_le hzd 0).2
        omega
      obtain ⟨z, hz, huS, hzS, hr⟩ := ih hw hv
      refine ⟨z, hz, ⟨u.2, hu⟩, hzS, ?_⟩
      refine SimpleGraph.Reachable.trans (SimpleGraph.Adj.reachable ?_) hr
      simpa [SimpleGraph.induce_adj] using hadj'

/-! ### Translated rectangles -/

/-- Membership in a translated rectangle `[0, m] × [0, n] + v`. [folklore] -/
theorem mem_image_add_rectangle {v z : LatticeModels.Site 2} {m n : ℕ} :
    z ∈ (· + v) '' (↑(rectangle m n) : Set (LatticeModels.Site 2)) ↔
      v 0 ≤ z 0 ∧ z 0 ≤ v 0 + m ∧ v 1 ≤ z 1 ∧ z 1 ≤ v 1 + n := by
  simp only [Set.image_add_right, Set.mem_preimage, Finset.mem_coe, mem_rectangle_iff,
    Pi.add_apply, Pi.neg_apply]
  omega

/-- Membership in the left side of a translated rectangle. [folklore] -/
theorem mem_image_add_leftSide {v z : LatticeModels.Site 2} {m n : ℕ} :
    z ∈ (· + v) '' (↑(leftSide m n) : Set (LatticeModels.Site 2)) ↔
      (v 0 ≤ z 0 ∧ z 0 ≤ v 0 + m ∧ v 1 ≤ z 1 ∧ z 1 ≤ v 1 + n) ∧ z 0 = v 0 := by
  simp only [Set.image_add_right, Set.mem_preimage, Finset.mem_coe, leftSide, Finset.mem_filter,
    mem_rectangle_iff, Pi.add_apply, Pi.neg_apply]
  omega

/-- Membership in the right side of a translated rectangle. [folklore] -/
theorem mem_image_add_rightSide {v z : LatticeModels.Site 2} {m n : ℕ} :
    z ∈ (· + v) '' (↑(rightSide m n) : Set (LatticeModels.Site 2)) ↔
      (v 0 ≤ z 0 ∧ z 0 ≤ v 0 + m ∧ v 1 ≤ z 1 ∧ z 1 ≤ v 1 + n) ∧ z 0 = v 0 + m := by
  simp only [Set.image_add_right, Set.mem_preimage, Finset.mem_coe, rightSide, Finset.mem_filter,
    mem_rectangle_iff, Pi.add_apply, Pi.neg_apply]
  omega

/-- Membership in the bottom side of a translated rectangle. [folklore] -/
theorem mem_image_add_bottomSide {v z : LatticeModels.Site 2} {m n : ℕ} :
    z ∈ (· + v) '' (↑(bottomSide m n) : Set (LatticeModels.Site 2)) ↔
      (v 0 ≤ z 0 ∧ z 0 ≤ v 0 + m ∧ v 1 ≤ z 1 ∧ z 1 ≤ v 1 + n) ∧ z 1 = v 1 := by
  simp only [Set.image_add_right, Set.mem_preimage, Finset.mem_coe, bottomSide, Finset.mem_filter,
    mem_rectangle_iff, Pi.add_apply, Pi.neg_apply]
  omega

/-- Membership in the top side of a translated rectangle. [folklore] -/
theorem mem_image_add_topSide {v z : LatticeModels.Site 2} {m n : ℕ} :
    z ∈ (· + v) '' (↑(topSide m n) : Set (LatticeModels.Site 2)) ↔
      (v 0 ≤ z 0 ∧ z 0 ≤ v 0 + m ∧ v 1 ≤ z 1 ∧ z 1 ≤ v 1 + n) ∧ z 1 = v 1 + n := by
  simp only [Set.image_add_right, Set.mem_preimage, Finset.mem_coe, topSide, Finset.mem_filter,
    mem_rectangle_iff, Pi.add_apply, Pi.neg_apply]
  omega

/-- The horizontal translation by `m₁ - n` placing the square `[0, n]²` and the rectangle
`[0, m₂] × [0, n]` at the right end of `[0, m₁] × [0, n]` (Bollobás–Riordan 2006, Ch. 3,
Figure 7). [folklore] -/
def glueShift (m₁ n : ℕ) : LatticeModels.Site 2 := ![(m₁ : ℤ) - n, 0]

/-- First coordinate of `glueShift`. [folklore] -/
@[simp] theorem glueShift_apply_zero (m₁ n : ℕ) : glueShift m₁ n 0 = (m₁ : ℤ) - n := rfl

/-- Second coordinate of `glueShift`. [folklore] -/
@[simp] theorem glueShift_apply_one (m₁ n : ℕ) : glueShift m₁ n 1 = 0 := rfl

/-! ### Duality of crossing probabilities -/

/-- Open crossing events are symmetric in the two target sets. [folklore] -/
theorem openCrossing_comm {V : Type*} (S A B : Set V) :
    (openCrossing S A B : Set (BondConfig V)) = openCrossing S B A := by
  ext ω
  simp only [mem_openCrossing_iff]
  constructor
  · rintro ⟨x, hx, y, hy, h⟩
    exact ⟨y, hy, x, hx, by rw [openConnIn_comm]; exact h⟩
  · rintro ⟨x, hx, y, hy, h⟩
    exact ⟨y, hy, x, hx, by rw [openConnIn_comm]; exact h⟩

/-- The vertical translation by `-1` carrying `[0, m] × [0, n + 1]` onto the dual rectangle
`[0, m] × [-1, n]` of `[0, m + 1] × [0, n]`. [folklore] -/
def dualShift : LatticeModels.Site 2 := ![0, -1]

/-- First coordinate of `dualShift`. [folklore] -/
@[simp] theorem dualShift_apply_zero : dualShift 0 = 0 := rfl

/-- Second coordinate of `dualShift`. [folklore] -/
@[simp] theorem dualShift_apply_one : dualShift 1 = -1 := rfl

/-- The dual rectangle of `[0, m + 1] × [0, n]` is the translate by `(0, -1)` of
`[0, m] × [0, n + 1]`. (Bollobás–Riordan 2006, Ch. 3, Lemma 1: "`R^h` is an `m - 1` by `n + 1`
rectangle".) [folklore] -/
theorem image_dualShift_rectangle (m n : ℕ) :
    (· + dualShift) '' (↑(rectangle m (n + 1)) : Set (LatticeModels.Site 2)) = ↑(dualRectangle (m + 1) n) := by
  ext z
  rw [mem_image_add_rectangle, Finset.mem_coe, mem_dualRectangle_iff, dualShift_apply_zero,
    dualShift_apply_one]
  push_cast
  constructor <;> intro h <;> omega

/-- The top side of the translate is the top side of the dual rectangle. [folklore] -/
theorem image_dualShift_topSide (m n : ℕ) :
    (· + dualShift) '' (↑(topSide m (n + 1)) : Set (LatticeModels.Site 2)) = ↑(dualTopSide (m + 1) n) := by
  ext z
  rw [mem_image_add_topSide, Finset.mem_coe, dualTopSide, Finset.mem_filter, mem_dualRectangle_iff,
    dualShift_apply_zero, dualShift_apply_one]
  push_cast
  constructor <;> intro h <;> omega

/-- The bottom side of the translate is the bottom side of the dual rectangle. [folklore] -/
theorem image_dualShift_bottomSide (m n : ℕ) :
    (· + dualShift) '' (↑(bottomSide m (n + 1)) : Set (LatticeModels.Site 2)) = ↑(dualBottomSide (m + 1) n) := by
  ext z
  rw [mem_image_add_bottomSide, Finset.mem_coe, dualBottomSide, Finset.mem_filter,
    mem_dualRectangle_iff, dualShift_apply_zero, dualShift_apply_one]
  push_cast
  constructor <;> intro h <;> omega

/-- The probability of the dual top-bottom crossing of `[0, m + 1] × [0, n]` under `P_p` is the
crossing probability `crossingProb (1 - p) (n + 1) m` of the transposed dual rectangle at the
dual parameter: `P_p(TB*(m + 1, n)) = P_{1-p}(TB([0, m] × [0, n + 1])) = h_{1-p}` of the `n + 2`
by `m + 1` rectangle. (Bollobás–Riordan 2006, Ch. 3, proof of Corollary 3(i); Grimmett 1999,
§11.2.) [cite: BollobasRiordanPercolation2006, Ch. 3, Corollary 3(i)] -/
theorem real_dualTBCrossing_succ (p : unitInterval) (m n : ℕ) :
    (bondPercolation (LatticeModels.zdGraph 2) p).real (dualTBCrossing (m + 1) n) =
      crossingProb (unitInterval.symm p) (n + 1) m := by
  have hE : MeasurableSet (openCrossing (↑(dualRectangle (m + 1) n) : Set (LatticeModels.Site 2))
      ↑(dualTopSide (m + 1) n) ↑(dualBottomSide (m + 1) n)) := measurableSet_openCrossing _ _ _
  rw [dualTBCrossing, ← map_measureReal_apply measurable_dualConfig hE,
    bondPercolation_map_dualConfig_holds p, ← image_dualShift_rectangle, ← image_dualShift_topSide,
    ← image_dualShift_bottomSide, real_openCrossing_shift, openCrossing_comm, ← tbCrossing,
    real_tbCrossing]

/-- **Discharge of `crossingProb_half_succ_self`** (Bollobás–Riordan 2006, Ch. 3, Corollary 3(ii);
Grimmett 1999, Lemma 11.21): at `p = 1/2` the rectangle `[0, n + 1] × [0, n]` is crossed
horizontally with probability exactly `1/2`, since `P_{1/2}(LR) + P_{1/2}(TB*) = 1` and the dual
crossing has the same probability by self-duality and symmetry. [cite: BollobasRiordanPercolation2006, Ch. 3, Corollary 3(ii)] [cite: GrimmettPercolation1999, Lemma 11.21] -/
theorem crossingProb_half_succ_self_holds : crossingProb_half_succ_self := by
  intro n
  have h := crossingProb_add_real_dualTBCrossing_holds half (n + 1) n
  rw [real_dualTBCrossing_succ, symm_half] at h
  linarith

/-! ### The deterministic gluing step -/

/-- **Gluing crossings** (Bollobás–Riordan 2006, Ch. 3, proof of eq. (2), Figure 7; Grimmett
1999, proof of Lemma 11.75, Fig. 11.11). Let `n ≤ m₁, m₂`, `R₁ = [0, m₁] × [0, n]`,
`S = [m₁ - n, m₁] × [0, n]`, `R₂ = [m₁ - n, m₁ + m₂ - n] × [0, n]`. For a lattice configuration,
if `R₁` and `R₂` have open left-right crossings and `S` has an open top-bottom crossing, then
`R₁ ∪ R₂ = [0, m₁ + m₂ - n] × [0, n]` has an open left-right crossing: the vertical crossing of
`S` meets both horizontal crossings. [cite: BollobasRiordanPercolation2006, Ch. 3, proof of eq. (2)] -/
theorem lrCrossing_of_glue {m₁ m₂ n : ℕ} (hn₁ : n ≤ m₁) (hn₂ : n ≤ m₂) {ω : BondConfig (LatticeModels.Site 2)}
    (hω : ω ⊆ (LatticeModels.zdGraph 2).edgeSet) (h₁ : ω ∈ lrCrossing m₁ n)
    (hV : ω ∈ openCrossing ((· + glueShift m₁ n) '' ↑(rectangle n n))
      ((· + glueShift m₁ n) '' ↑(bottomSide n n)) ((· + glueShift m₁ n) '' ↑(topSide n n)))
    (h₂ : ω ∈ openCrossing ((· + glueShift m₁ n) '' ↑(rectangle m₂ n))
      ((· + glueShift m₁ n) '' ↑(leftSide m₂ n)) ((· + glueShift m₁ n) '' ↑(rightSide m₂ n))) :
    ω ∈ lrCrossing (m₁ + m₂ - n) n := by
  classical
  set v := glueShift m₁ n with hv
  set S : Set (LatticeModels.Site 2) := (· + v) '' ↑(rectangle n n) with hS
  set Big : Set (LatticeModels.Site 2) := ↑(rectangle (m₁ + m₂ - n) n) with hBig
  have hcast : ((m₁ + m₂ - n : ℕ) : ℤ) = m₁ + m₂ - n := by push_cast [show n ≤ m₁ + m₂ by omega]; ring
  have hmemS : ∀ z : LatticeModels.Site 2, z ∈ S ↔ (m₁ : ℤ) - n ≤ z 0 ∧ z 0 ≤ m₁ ∧ 0 ≤ z 1 ∧ z 1 ≤ n := by
    intro z; rw [hS, mem_image_add_rectangle, hv, glueShift_apply_zero, glueShift_apply_one]
    constructor <;> intro h <;> omega
  have hmemBig : ∀ z : LatticeModels.Site 2, z ∈ Big ↔ 0 ≤ z 0 ∧ z 0 ≤ m₁ + m₂ - n ∧ 0 ≤ z 1 ∧ z 1 ≤ n := by
    intro z; rw [hBig, Finset.mem_coe, mem_rectangle_iff, hcast]
  have hR₁Big : (↑(rectangle m₁ n) : Set (LatticeModels.Site 2)) ⊆ Big := by
    intro z hz; rw [Finset.mem_coe, mem_rectangle_iff] at hz; rw [hmemBig]; omega
  have hSBig : S ⊆ Big := by
    intro z hz; rw [hmemS] at hz; rw [hmemBig]; omega
  have hR₂Big : (· + v) '' (↑(rectangle m₂ n) : Set (LatticeModels.Site 2)) ⊆ Big := by
    intro z hz; rw [mem_image_add_rectangle] at hz; simp only [hv, glueShift_apply_zero,
      glueShift_apply_one] at hz; rw [hmemBig]; omega
  -- the first horizontal crossing and its part after the last visit to the column `m₁ - n`
  obtain ⟨x, hx, y, hy, hxy⟩ := h₁
  simp only [Finset.mem_coe, leftSide, rightSide, Finset.mem_filter, mem_rectangle_iff] at hx hy
  have hyx : ω ∈ openConnIn ↑(rectangle m₁ n) y x := by rw [openConnIn_comm]; exact hxy
  obtain ⟨z, hz0, hyz⟩ := exists_openConnIn_column_ge hω ((m₁ : ℤ) - n) (by rw [hy.2]; omega)
    (by rw [hx.2]; omega) hyx
  have hsub₁ : (↑(rectangle m₁ n) ∩ {z : LatticeModels.Site 2 | (m₁ : ℤ) - n ≤ z 0}) ⊆ S := by
    intro w hw
    simp only [Set.mem_inter_iff, Finset.mem_coe, mem_rectangle_iff, Set.mem_setOf_eq] at hw
    rw [hmemS]; omega
  have hzy : ω ∈ openConnIn S z y := by rw [openConnIn_comm]; exact openConnIn_mono hsub₁ _ _ hyz
  obtain ⟨P, hPS, hPω⟩ := exists_walk_of_mem_openConnIn hω hzy
  -- the vertical crossing of the square
  obtain ⟨b, hb, t, ht, hbt⟩ := hV
  rw [mem_image_add_bottomSide] at hb
  rw [mem_image_add_topSide] at ht
  simp only [hv, glueShift_apply_zero, glueShift_apply_one, zero_add] at hb ht
  obtain ⟨Q, hQS, hQω⟩ := exists_walk_of_mem_openConnIn hω hbt
  have hQbox : ∀ w ∈ Q.support, (m₁ : ℤ) - n ≤ w 0 ∧ w 0 ≤ m₁ ∧ 0 ≤ w 1 ∧ w 1 ≤ n :=
    fun w hw => (hmemS w).1 (hQS w hw)
  -- they meet
  obtain ⟨w, hwP, hwQ⟩ := exists_mem_support_of_crossing (L := (m₁ : ℤ) - n) (R := m₁) (B := 0)
    (T := n) P Q (fun w hw => (hmemS w).1 (hPS w hw)) hQbox hz0 hy.2 hb.2 ht.2
  -- the second horizontal crossing and its part before the first visit to the column `m₁`
  obtain ⟨x₂, hx₂, y₂, hy₂, hxy₂⟩ := h₂
  rw [mem_image_add_leftSide] at hx₂
  rw [mem_image_add_rightSide] at hy₂
  simp only [hv, glueShift_apply_zero, glueShift_apply_one, zero_add] at hx₂ hy₂
  obtain ⟨z₂, hz₂0, hxz₂⟩ := exists_openConnIn_column hω (m₁ : ℤ) (by rw [hx₂.2]; omega)
    (by rw [hy₂.2]; omega) hxy₂
  have hsub₂ : ((· + v) '' (↑(rectangle m₂ n) : Set (LatticeModels.Site 2)) ∩ {z : LatticeModels.Site 2 | z 0 ≤ (m₁ : ℤ)}) ⊆ S := by
    intro w hw
    rw [Set.mem_inter_iff, mem_image_add_rectangle, Set.mem_setOf_eq] at hw
    simp only [hv, glueShift_apply_zero, glueShift_apply_one] at hw
    rw [hmemS]; omega
  have hxz₂' : ω ∈ openConnIn S x₂ z₂ := openConnIn_mono hsub₂ _ _ hxz₂
  obtain ⟨P₂, hP₂S, hP₂ω⟩ := exists_walk_of_mem_openConnIn hω hxz₂'
  obtain ⟨w', hw'P, hw'Q⟩ := exists_mem_support_of_crossing (L := (m₁ : ℤ) - n) (R := m₁) (B := 0)
    (T := n) P₂ Q (fun w hw => (hmemS w).1 (hP₂S w hw)) hQbox hx₂.2 hz₂0 hb.2 ht.2
  -- assemble the crossing `x ↔ y ↔ w ↔ w' ↔ x₂ ↔ y₂` inside the big rectangle
  have c₁ : ω ∈ openConnIn Big x y := openConnIn_mono hR₁Big _ _ hxy
  have c₂ : ω ∈ openConnIn Big y w := by
    refine openConnIn_mono hSBig _ _ ?_
    rw [openConnIn_comm]
    exact PlanarDuality.openConnIn_trans (by rw [openConnIn_comm]; exact mem_openConnIn_of_mem_support P hPS hPω hwP)
      hzy
  have c₃ : ω ∈ openConnIn Big w w' := by
    refine openConnIn_mono hSBig _ _ ?_
    exact PlanarDuality.openConnIn_trans (by rw [openConnIn_comm]; exact mem_openConnIn_of_mem_support Q hQS hQω hwQ)
      (mem_openConnIn_of_mem_support Q hQS hQω hw'Q)
  have c₄ : ω ∈ openConnIn Big w' x₂ := by
    refine openConnIn_mono hSBig _ _ ?_
    rw [openConnIn_comm]
    exact mem_openConnIn_of_mem_support P₂ hP₂S hP₂ω hw'P
  have c₅ : ω ∈ openConnIn Big x₂ y₂ := openConnIn_mono hR₂Big _ _ hxy₂
  refine ⟨x, ?_, y₂, ?_, PlanarDuality.openConnIn_trans (PlanarDuality.openConnIn_trans (PlanarDuality.openConnIn_trans
    (PlanarDuality.openConnIn_trans c₁ c₂) c₃) c₄) c₅⟩
  · simp only [Finset.mem_coe, leftSide, Finset.mem_filter, mem_rectangle_iff]
    exact ⟨by omega, hx.2⟩
  · simp only [Finset.mem_coe, rightSide, Finset.mem_filter, mem_rectangle_iff, hcast]
    exact ⟨by omega, by rw [hy₂.2]; ring⟩

/-! ### Locality of the translated crossing events -/

/-- Open crossing events of translated finite regions are local. [folklore] -/
theorem isLocalEvent_openCrossing_image (F : Finset (LatticeModels.Site 2)) (v : LatticeModels.Site 2) (A B : Set (LatticeModels.Site 2)) :
    IsLocalEvent (openCrossing ((· + v) '' (↑F : Set (LatticeModels.Site 2))) A B) := by
  rw [← Finset.coe_image]
  exact isLocalEvent_openCrossing _ _ _

/-- The intersection of two local events is local. (Grimmett 1999, §2.2.) [folklore] -/
theorem IsLocalEvent.inter {ι : Type*} [DecidableEq ι] {A B : Set (Set ι)} (hA : IsLocalEvent A)
    (hB : IsLocalEvent B) : IsLocalEvent (A ∩ B) := by
  obtain ⟨F, hF⟩ := hA
  obtain ⟨G, hG⟩ := hB
  refine ⟨F ∪ G, ?_⟩
  rw [Finset.coe_union]
  exact (hF.mono Set.subset_union_left).inter (hG.mono Set.subset_union_right)

end

end Percolation.Literature

/-! ### The probabilistic step -/

namespace Percolation.Literature

open MeasureTheory LatticeModels PlanarDuality

noncomputable section

/-- **Discharge of `crossingProb_add_crossingProb_symm`** (Bollobás–Riordan 2006, Ch. 3,
Corollary 3(i); Grimmett 1999, §11.2 and Lemma 11.21):
`crossingProb p (m + 1) n + crossingProb (1 - p) (n + 1) m = 1`, from `P_p(LR) + P_p(TB*) = 1`
(`crossingProb_add_real_dualTBCrossing_holds`) and `P_p(TB*(m + 1, n)) = crossingProb (1 - p) (n + 1) m`
(`real_dualTBCrossing_succ`). [cite: BollobasRiordanPercolation2006, Ch. 3, Corollary 3(i)] [cite: GrimmettPercolation1999, Lemma 11.21] -/
theorem crossingProb_add_crossingProb_symm_holds : crossingProb_add_crossingProb_symm := by
  intro p m n
  have h := crossingProb_add_real_dualTBCrossing_holds p (m + 1) n
  rwa [real_dualTBCrossing_succ] at h

/-- **Discharge of `crossingProb_glue`** (Bollobás–Riordan 2006, Ch. 3, eq. (2) and eq. (12);
Grimmett 1999, Lemma 11.75): for `n ≤ m₁, m₂`,
`crossingProb p m₁ n * crossingProb p m₂ n * crossingProb p n n ≤ crossingProb p (m₁ + m₂ - n) n`.
The three crossing events (`R₁` horizontal, `S` vertical, `R₂` horizontal, as in
`lrCrossing_of_glue`) are increasing and local, so Harris's lemma applies twice; their
intersection is contained (on lattice configurations, a `P_p`-sure set) in the horizontal crossing
event of `R₁ ∪ R₂`; and `P_p(V(S)) = crossingProb p n n`, `P_p(H(R₂)) = crossingProb p m₂ n` by
the symmetries of `P_p`. [cite: BollobasRiordanPercolation2006, Ch. 3, eq. (2) and eq. (12)] [cite: GrimmettPercolation1999, Lemma 11.75] -/
theorem crossingProb_glue_holds : crossingProb_glue := by
  classical
  intro p m₁ m₂ n hn₁ hn₂
  set μ := bondPercolation (zdGraph 2) p with hμ
  set v := glueShift m₁ n with hv
  set H₁ := lrCrossing m₁ n with hH₁
  set V := openCrossing ((· + v) '' (↑(rectangle n n) : Set (Site 2)))
    ((· + v) '' ↑(bottomSide n n)) ((· + v) '' ↑(topSide n n)) with hVdef
  set H₂ := openCrossing ((· + v) '' (↑(rectangle m₂ n) : Set (Site 2)))
    ((· + v) '' ↑(leftSide m₂ n)) ((· + v) '' ↑(rightSide m₂ n)) with hH₂def
  have hPV : μ.real V = crossingProb p n n := by
    rw [hVdef, real_openCrossing_shift]
    exact real_tbCrossing p n n
  have hPH₂ : μ.real H₂ = crossingProb p m₂ n := by
    rw [hH₂def, real_openCrossing_shift]
    rfl
  have hPH₁ : μ.real H₁ = crossingProb p m₁ n := rfl
  have hup₁ : IsUpperSet H₁ := isUpperSet_lrCrossing _ _
  have hupV : IsUpperSet V := isUpperSet_openCrossing _ _ _
  have hup₂ : IsUpperSet H₂ := isUpperSet_openCrossing _ _ _
  have hloc₁ : IsLocalEvent H₁ := isLocalEvent_lrCrossing _ _
  have hlocV : IsLocalEvent V := isLocalEvent_openCrossing_image _ _ _ _
  have hloc₂ : IsLocalEvent H₂ := isLocalEvent_openCrossing_image _ _ _ _
  have h12 : μ.real H₁ * μ.real V ≤ μ.real (H₁ ∩ V) :=
    harris_fkg_local (zdGraph 2) p hup₁ hupV hloc₁ hlocV
  have h123 : μ.real (H₁ ∩ V) * μ.real H₂ ≤ μ.real (H₁ ∩ V ∩ H₂) :=
    harris_fkg_local (zdGraph 2) p (hup₁.inter hupV) hup₂ (hloc₁.inter hlocV) hloc₂
  have hsub : μ.real (H₁ ∩ V ∩ H₂) ≤ crossingProb p (m₁ + m₂ - n) n := by
    rw [crossingProb]
    refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_)
    filter_upwards [ae_subset_edgeSet (zdGraph 2) p] with ω hω hmem
    exact lrCrossing_of_glue hn₁ hn₂ hω hmem.1.1 hmem.1.2 hmem.2
  calc crossingProb p m₁ n * crossingProb p m₂ n * crossingProb p n n
      = μ.real H₁ * μ.real V * μ.real H₂ := by rw [hPV, hPH₂, hPH₁]; ring
    _ ≤ μ.real (H₁ ∩ V) * μ.real H₂ := mul_le_mul_of_nonneg_right h12 measureReal_nonneg
    _ ≤ μ.real (H₁ ∩ V ∩ H₂) := h123
    _ ≤ crossingProb p (m₁ + m₂ - n) n := hsub

end

end Percolation.Literature
