import Mathlib.Algebra.BigOperators.Ring.Finset
import Percolation.Literature.DecisionTreeBK
import Percolation.Util.Linter

/-!
# Decision-tree HK, vdBK and Cauchy–Schwarz inequalities with inhomogeneous edge weights (Gladkov 2024, Lemma 3.1, Theorems 3.2, 4.3, 5.2)

Source: N. Gladkov, *Percolation Inequalities and
Decision Trees*, arXiv:2408.08457v2 (2024) [Gladkov2024], §2 (standing assumption: Bernoulli bond
percolation in which EACH edge `e` has its own probability `p_e`), Lemma 3.1 and Theorem 3.2 (p. 4–5),
Def. 4.2 and Theorem 4.3 (p. 5–6), Theorem 5.2 (p. 6–7).

Everything here is proved. `DecisionTreeBK.lean` proves the swap involution (Lemma 3.1), Theorem 4.3
and the Cauchy–Schwarz step of Theorem 5.2 for the HOMOGENEOUS weight `wt D p` (`p : ℝ`); this file
redoes them coordinate-wise for an arbitrary weight vector `p : ι → ℝ` with `p i ∈ [0, 1]` — the
generality in which the paper states them, and the one needed when glued or contracted instances
carry weight-one and weight-zero coordinates — and ADDS the decision-tree Harris–Kleitman inequality
(Theorem 3.2), absent from the homogeneous file.

* `sum_wtW` — total mass one (`∏ (p_i + (1 - p_i)) = 1`); `wtW_splice_mul_wtW_splice`,
  `wt2W_swapPair`, **`sum_pair_reindexW`**, `Pr2W_preimage_swapPair` — Lemma 3.1 (= [GZ24, Lemma 4.2])
  in finitary form: the swap `(C₁, C₂) ↦ (C₁ →_S C₂, C₂ →_S C₁)` along a self-determined `S(C₁)`
  preserves the product weight, so reindexing by it preserves every pair sum.
* `hkWith S A B = {(C₁, C₂) | C₁ ∈ A, C₁ →_S C₂ ∈ B}`, `treeHK`; `swapAt_mem_hkWith_of_mem_diff` (the
  combinatorial heart of inequality (5)), `Pr2W_hkWith_le_insert`, `Pr2W_treeHK_prune_le`,
  **`PrW_mul_PrW_le_Pr2W_treeHK`** — Theorem 3.2 (decision-tree HK):
  `P(C₁ ∈ A, C₁ →_S C₂ ∈ B) ≥ P(A) P(B)` for increasing `A, B` and `S = S(C₁)` built by a tree.

Trees here read `C₁` and send every queried coordinate to `S` (the class of Def. 2.4 / Algorithm 1
used in §§5–6; an `S̄`-decision below the last `S`-decision builds the same set). Not here: trees
reading both configurations, Main Lemma 8.1.

## References

* N. Gladkov, *Percolation Inequalities and Decision Trees*, arXiv:2408.08457v2 (2024), Lemma 3.1,
  Thm. 3.2, Def. 4.2, Thm. 4.3, Thm. 5.2. [Gladkov2024]
* N. Gladkov, A. Zimin, *Bond percolation does not simulate site percolation*, arXiv:2404.08873
  (2024), Lemma 4.2. [GladkovZimin2024]
-/

noncomputable section

namespace Percolation.Literature

namespace DecisionTree

open Finset

variable {ι : Type*} [DecidableEq ι]

/-! ### Bernoulli weights and finite probabilities -/

/-- The Bernoulli weight of the configuration `S` (open coordinates) among the coordinates `D`:
`∏_{i ∈ D} (p_i if i ∈ S else 1 - p_i)`, each coordinate `i` with its own probability `p_i`.
[cite: Gladkov2024, §2 (Bernoulli bond percolation with edge probabilities p_e)] -/
def wtW (D : Finset ι) (p : ι → ℝ) (S : Finset ι) : ℝ :=
  ∏ i ∈ D, if i ∈ S then p i else 1 - p i

/-- The probability of an event of one configuration: `Σ_{S ⊆ D} wtW S · 1[S ∈ X]`.
[cite: Gladkov2024, §2] -/
def PrW (D : Finset ι) (p : ι → ℝ) (X : Set (Finset ι)) : ℝ :=
  ∑ S ∈ D.powerset, X.indicator (wtW D p) S

/-- The weight of a pair of independent configurations. [cite: Gladkov2024, §2] -/
def wt2W (D : Finset ι) (p : ι → ℝ) (x : Finset ι × Finset ι) : ℝ := wtW D p x.1 * wtW D p x.2

/-- The probability of an event of a pair `(C₁, C₂)` of independent configurations:
`Σ_{S₁, S₂ ⊆ D} wtW S₁ wtW S₂ · 1[(S₁, S₂) ∈ Y]`. [cite: Gladkov2024, §2] -/
def Pr2W (D : Finset ι) (p : ι → ℝ) (Y : Set (Finset ι × Finset ι)) : ℝ :=
  ∑ x ∈ D.powerset ×ˢ D.powerset, Y.indicator (wt2W D p) x

section Weights

variable (D : Finset ι) {p : ι → ℝ}

/-- Weights are nonnegative for `p ∈ [0, 1]`. [folklore] -/
theorem wtW_nonneg (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (S : Finset ι) : 0 ≤ wtW D p S := by
  unfold wtW
  refine Finset.prod_nonneg fun i _ => ?_
  split_ifs with h
  · exact hp0 i
  · exact sub_nonneg.2 (hp1 i)

/-- Pair weights are nonnegative for `p ∈ [0, 1]`. [folklore] -/
theorem wt2W_nonneg (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (x : Finset ι × Finset ι) : 0 ≤ wt2W D p x :=
  mul_nonneg (wtW_nonneg D hp0 hp1 x.1) (wtW_nonneg D hp0 hp1 x.2)

/-- `Pr2W` is monotone (it suffices to compare the events on pairs of configurations `⊆ D`).
[folklore] -/
theorem Pr2W_mono (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) {X Y : Set (Finset ι × Finset ι)}
    (h : ∀ x : Finset ι × Finset ι, x.1 ⊆ D → x.2 ⊆ D → x ∈ X → x ∈ Y) :
    Pr2W D p X ≤ Pr2W D p Y := by
  unfold Pr2W
  refine Finset.sum_le_sum fun x hx => ?_
  rw [Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset] at hx
  by_cases hX : x ∈ X
  · rw [Set.indicator_of_mem hX, Set.indicator_of_mem (h x hx.1 hx.2 hX)]
  · rw [Set.indicator_of_notMem hX]
    exact Set.indicator_nonneg (fun y _ => wt2W_nonneg D hp0 hp1 y) x

/-- `Pr2W` is additive on disjoint events. [folklore] -/
theorem Pr2W_union (p : ι → ℝ) {X Y : Set (Finset ι × Finset ι)} (h : Disjoint X Y) :
    Pr2W D p (X ∪ Y) = Pr2W D p X + Pr2W D p Y := by
  unfold Pr2W
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Set.indicator_union_of_disjoint h]

/-- `Pr2W X = Pr2W (X ∩ Y) + Pr2W (X \ Y)`. [folklore] -/
theorem Pr2W_eq_inter_add_diff (p : ι → ℝ) (X Y : Set (Finset ι × Finset ι)) :
    Pr2W D p X = Pr2W D p (X ∩ Y) + Pr2W D p (X \ Y) := by
  rw [← Pr2W_union D p (Set.disjoint_sdiff_inter.symm), Set.inter_union_sdiff]

/-- `Pr2W (X × Y) = PrW X · PrW Y` (independence of the two configurations). [folklore] -/
theorem Pr2W_prod (p : ι → ℝ) (X Y : Set (Finset ι)) :
    Pr2W D p (X ×ˢ Y) = PrW D p X * PrW D p Y := by
  unfold Pr2W PrW
  rw [Finset.sum_product, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun T _ => ?_
  by_cases hS : S ∈ X
  · by_cases hT : T ∈ Y
    · rw [Set.indicator_of_mem (Set.mk_mem_prod hS hT), Set.indicator_of_mem hS,
        Set.indicator_of_mem hT]
      rfl
    · rw [Set.indicator_of_notMem (fun h : (S, T) ∈ X ×ˢ Y => hT h.2),
        Set.indicator_of_notMem hT, mul_zero]
  · rw [Set.indicator_of_notMem (fun h : (S, T) ∈ X ×ˢ Y => hS h.1),
      Set.indicator_of_notMem hS, zero_mul]

/-- The weight of `S ⊆ D` is `∏_{i ∈ S} p_i · ∏_{i ∈ D ∖ S} (1 - p_i)`. [folklore] -/
theorem wtW_eq_prod_mul_prod (p : ι → ℝ) {S : Finset ι} (hS : S ⊆ D) :
    wtW D p S = (∏ i ∈ S, p i) * ∏ i ∈ D \ S, (1 - p i) := by
  unfold wtW
  rw [Finset.prod_ite, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 hS,
    Finset.filter_notMem_eq_sdiff]

/-- **Total mass one**: `Σ_{S ⊆ D} wtW S = ∏_{i ∈ D} (p_i + (1 - p_i)) = 1`. [folklore] -/
theorem sum_wtW (p : ι → ℝ) : ∑ S ∈ D.powerset, wtW D p S = 1 := by
  rw [Finset.sum_congr rfl fun S hS => wtW_eq_prod_mul_prod D p (Finset.mem_powerset.1 hS),
    ← Finset.prod_add]
  exact Finset.prod_eq_one fun i _ => by ring

end Weights

/-! ### The homogeneous weight is the constant weight vector -/

/-- **Weight preservation of the swap** `(S₁, S₂) ↦ (S₁ →_F S₂, S₂ →_F S₁)`: the product of
the weights is unchanged (each coordinate's two values are merely exchanged).
[cite: Gladkov2024, Lemma 3.1 (= GZ24 Lemma 4.2)] -/
theorem wtW_splice_mul_wtW_splice (D : Finset ι) (p : ι → ℝ) (F S₁ S₂ : Finset ι) :
    wtW D p (splice F S₁ S₂) * wtW D p (splice F S₂ S₁) = wtW D p S₁ * wtW D p S₂ := by
  unfold wtW
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : i ∈ F
  · simp only [mem_splice_of_mem hi]
  · simp only [mem_splice_of_not_mem hi]
    ring
/-- The swap preserves pair weights. [cite: Gladkov2024, Lemma 3.1] -/
theorem wt2W_swapPair (D : Finset ι) (p : ι → ℝ) (Fm : Finset ι → Finset ι)
    (x : Finset ι × Finset ι) : wt2W D p (swapPair Fm x) = wt2W D p x := by
  unfold wt2W swapPair
  exact wtW_splice_mul_wtW_splice D p (Fm x.1) x.1 x.2

/-- **Reindexing by the swap** (finitary form of Gladkov's Lemma 3.1 / [GZ24, Lemma 4.2]: the
pair `(C₁ →_S C₂, C₂ →_S C₁)` is again an independent pair): for self-determined `Fm`,
`Σ_x wt2W x · f x = Σ_x wt2W x · f (swap x)`. [cite: Gladkov2024, Lemma 3.1] -/
theorem sum_pair_reindexW (D : Finset ι) (p : ι → ℝ) {Fm : Finset ι → Finset ι}
    (hF : SelfDetermined Fm) (f : Finset ι × Finset ι → ℝ) :
    ∑ x ∈ D.powerset ×ˢ D.powerset, wt2W D p x * f x =
      ∑ x ∈ D.powerset ×ˢ D.powerset, wt2W D p x * f (swapPair Fm x) := by
  refine Finset.sum_nbij' (swapPair Fm) (swapPair Fm) (fun x hx => swapPair_mem Fm hx)
    (fun x hx => swapPair_mem Fm hx) (fun x _ => swapPair_swapPair hF x)
    (fun x _ => swapPair_swapPair hF x) fun x _ => ?_
  rw [wt2W_swapPair, swapPair_swapPair hF]

/-- `Pr2W` is invariant under the swap: `Pr2W (swap ⁻¹' Y) = Pr2W Y`. [cite: Gladkov2024, Lemma 3.1] -/
theorem Pr2W_preimage_swapPair (D : Finset ι) (p : ι → ℝ) {Fm : Finset ι → Finset ι}
    (hF : SelfDetermined Fm) (Y : Set (Finset ι × Finset ι)) :
    Pr2W D p (swapPair Fm ⁻¹' Y) = Pr2W D p Y := by
  unfold Pr2W
  have h := sum_pair_reindexW D p hF (Y.indicator fun _ => (1 : ℝ))
  have key : ∀ (Z : Set (Finset ι × Finset ι)) (x : Finset ι × Finset ι),
      Z.indicator (wt2W D p) x = wt2W D p x * Z.indicator (fun _ => (1 : ℝ)) x := by
    intro Z x
    by_cases hx : x ∈ Z <;> simp [hx]
  simp_rw [key]
  rw [h]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : swapPair Fm x ∈ Y
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show x ∈ swapPair Fm ⁻¹' Y from hx)]
  · rw [Set.indicator_of_notMem hx,
      Set.indicator_of_notMem (show x ∉ swapPair Fm ⁻¹' Y from hx)]
/-! ### The Cauchy–Schwarz step (Theorem 5.2 for a tree that reveals everything it queries) -/

section CauchySchwarz

/-- `PrW` as a weighted sum of `ind`. [folklore] -/
theorem PrW_eq_sum_ind (D : Finset ι) (p : ι → ℝ) (X : Set (Finset ι)) :
    PrW D p X = ∑ S ∈ D.powerset, wtW D p S * ind X S := by
  unfold PrW
  exact Finset.sum_congr rfl fun S _ => indicator_eq_mul_ind X _ S

/-- `Pr2W` as a weighted sum of `ind`. [folklore] -/
theorem Pr2W_eq_sum_ind (D : Finset ι) (p : ι → ℝ) (Y : Set (Finset ι × Finset ι)) :
    Pr2W D p Y = ∑ x ∈ D.powerset ×ˢ D.powerset, wt2W D p x * ind Y x := by
  unfold Pr2W
  exact Finset.sum_congr rfl fun x _ => indicator_eq_mul_ind Y _ x

/-- The conditional probability of `B` given the revealed coordinates, times nothing: the inner
sum `h(K) = Σ_{K₂} wtW K₂ · 1[K →_{Fm K} K₂ ∈ B]`. [cite: Gladkov2024, proof of Thm. 5.2 ((9), P(B | T₂ goes through N))] -/
def condSumW (D : Finset ι) (p : ι → ℝ) (Fm : Finset ι → Finset ι) (B : Set (Finset ι))
    (K : Finset ι) : ℝ :=
  ∑ K₂ ∈ D.powerset, wtW D p K₂ * ind B (splice (Fm K) K K₂)

end CauchySchwarz

/-! ### Theorem 3.2: the decision-tree Harris–Kleitman inequality -/

section HK

/-- The event `{(C₁, C₂) | C₁ ∈ A, C₁ →_S C₂ ∈ B}` of Theorem 3.2, for a GIVEN set `S`.
[cite: Gladkov2024, Thm. 3.2] -/
def hkWith (S : Finset ι) (A B : Set (Finset ι)) : Set (Finset ι × Finset ι) :=
  {x | x.1 ∈ A ∧ splice S x.1 x.2 ∈ B}

/-- The event of Theorem 3.2 with `S = S₀ ∪ S(C₁)`, `S(C₁)` built by the tree `T`.
[cite: Gladkov2024, Thm. 3.2] -/
def treeHK (S₀ : Finset ι) (T : DTree ι) (A B : Set (Finset ι)) : Set (Finset ι × Finset ι) :=
  {x | x ∈ hkWith (S₀ ∪ revealed T x.1) A B}

/-- For `S = ∅`: `C₁ →_∅ C₂ = C₂`, so the event is `A × B`. [cite: Gladkov2024, proof of Thm. 3.2 (base case)] -/
theorem hkWith_empty (A B : Set (Finset ι)) : hkWith ∅ A B = A ×ˢ B := by
  ext x
  simp only [hkWith, Set.mem_setOf_eq, Set.mem_prod]
  have : splice ∅ x.1 x.2 = x.2 := by
    ext i
    rw [mem_splice_of_not_mem (Finset.notMem_empty i)]
  rw [this]

/-- Unfolding `treeHK` at a node: the root query splits the event according to `e ∈ C₁`.
[folklore] -/
theorem treeHK_node (S₀ : Finset ι) (e : ι) (yes no : DTree ι) (A B : Set (Finset ι)) :
    treeHK S₀ (.node e yes no) A B =
      (treeHK (insert e S₀) yes A B ∩ {x | e ∈ x.1}) ∪
        (treeHK (insert e S₀) no A B ∩ {x | e ∉ x.1}) := by
  ext x
  simp only [treeHK, Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff, revealed]
  by_cases he : e ∈ x.1
  · simp only [he, if_true, not_true_eq_false, and_false, or_false, and_true]
    rw [Finset.union_insert, Finset.insert_union]
  · simp only [he, if_false, and_false, false_or, not_false_eq_true, and_true]
    rw [Finset.union_insert, Finset.insert_union]

/-- `treeHK` at a leaf is `hkWith S₀`. [folklore] -/
theorem treeHK_leaf (S₀ : Finset ι) (A B : Set (Finset ι)) :
    treeHK S₀ (.leaf : DTree ι) A B = hkWith S₀ A B := by
  ext x
  simp only [treeHK, Set.mem_setOf_eq, revealed, Finset.union_empty]

/-- **The combinatorial heart of inequality (5)** (proof of Thm. 3.2, p. 5): if `e ∉ S`,
`(C₁, C₂) ∈ hkWith S A B` but `∉ hkWith (S ∪ {e}) A B` for increasing `A, B` (so `e` is closed in
`C₁` and open in `C₂`), then swapping the coordinate `e` between `C₁` and `C₂` gives a pair in
`hkWith (S ∪ {e}) A B` and not in `hkWith S A B`. [cite: Gladkov2024, proof of Thm. 3.2, (5)] -/
theorem swapAt_mem_hkWith_of_mem_diff {D S : Finset ι} {e : ι} (he : e ∉ S) {A B : Set (Finset ι)}
    (hA : IsUpperSet A) (hB : IsUpperSet B) {x : Finset ι × Finset ι} (hx1 : x.1 ⊆ D) (hx2 : x.2 ⊆ D)
    (hx : x ∈ hkWith S A B \ hkWith (insert e S) A B) :
    swapAt D e x ∈ hkWith (insert e S) A B \ hkWith S A B := by
  obtain ⟨⟨hxA, hxB⟩, hx0⟩ := hx
  have hx0' : splice (insert e S) x.1 x.2 ∉ B := fun h => hx0 ⟨hxA, h⟩
  -- `e ∈ C₂` and `e ∉ C₁`: otherwise the two splices coincide
  have hsame : (e ∈ x.1 ↔ e ∈ x.2) → splice (insert e S) x.1 x.2 = splice S x.1 x.2 := by
    intro hiff
    ext i
    rw [mem_splice_insert, mem_splice]
    by_cases hie : i = e
    · subst hie
      simp [he, hiff]
    · simp [hie]
  have he2 : e ∈ x.2 := by
    by_contra he2
    by_cases he1 : e ∈ x.1
    · -- `e ∈ C₁`, `e ∉ C₂`: the `S ∪ {e}`-splice is ABOVE the `S`-splice
      refine hx0' (hB (fun i hi => ?_) hxB)
      rw [mem_splice_insert]
      rcases mem_splice.1 hi with ⟨hiS, hiX⟩ | ⟨hiS, hiX⟩
      · exact Or.inr ⟨fun h => he (h ▸ hiS), Or.inl ⟨hiS, hiX⟩⟩
      · have hie : i ≠ e := fun h => he2 (h ▸ hiX)
        exact Or.inr ⟨hie, Or.inr ⟨hiS, hiX⟩⟩
    · exact hx0' ((hsame ⟨fun h => absurd h he1, fun h => absurd h he2⟩).symm ▸ hxB)
  have he1 : e ∉ x.1 := fun he1 => hx0' ((hsame ⟨fun _ => he2, fun _ => he1⟩).symm ▸ hxB)
  -- the swapped pair `y = (C₁ + e, C₂ - e)`
  have hy1 : ∀ i, i ∈ (swapAt D e x).1 ↔ (i ≠ e ∧ i ∈ x.1) ∨ i = e := fun i => by
    rw [mem_swapAt_fst hx1 hx2]
    constructor
    · rintro (h | ⟨h, -⟩)
      · exact Or.inl h
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr ⟨h, h ▸ he2⟩
  have hy2 : ∀ i, i ∈ (swapAt D e x).2 ↔ (i ≠ e ∧ i ∈ x.2) := fun i => by
    rw [mem_swapAt_snd hx1 hx2]
    constructor
    · rintro (h | ⟨rfl, h⟩)
      · exact h
      · exact absurd h he1
    · exact fun h => Or.inl h
  -- `y₁ ⊇ C₁ ∈ A`; `y₁ →_{S ∪ {e}} y₂ = C₁ →_S C₂ ∈ B`; `y₁ →_S y₂ = C₁ →_{S ∪ {e}} C₂ ∉ B`
  have hup : (swapAt D e x).1 ∈ A :=
    hA (fun i hi => (hy1 i).2 (by
      by_cases hie : i = e
      · exact Or.inr hie
      · exact Or.inl ⟨hie, hi⟩)) hxA
  have hspl1 : splice (insert e S) (swapAt D e x).1 (swapAt D e x).2 = splice S x.1 x.2 := by
    ext i
    rw [mem_splice_insert, hy1, hy2, mem_splice]
    by_cases hie : i = e
    · subst hie
      simp [he, he2]
    · simp [hie]
  have hspl2 : splice S (swapAt D e x).1 (swapAt D e x).2 = splice (insert e S) x.1 x.2 := by
    ext i
    rw [mem_splice_insert, mem_splice, hy1, hy2]
    by_cases hie : i = e
    · subst hie
      simp [he, he1]
    · simp [hie]
  exact ⟨⟨hup, hspl1.symm ▸ hxB⟩, fun h => hx0' (hspl2 ▸ h.2)⟩

/-- **Inequality (5) summed** (proof of Thm. 3.2): for `e ∉ S`, increasing `A, B` and an auxiliary
event `Z` determined by `C₁` on `S`, `P(Z ∩ hkWith S A B) ≤ P(Z ∩ hkWith (S ∪ {e}) A B)` — sending
one more queried coordinate to `S` can only increase the probability. [cite: Gladkov2024, proof of Thm. 3.2, (5)] -/
theorem Pr2W_hkWith_le_insert (D : Finset ι) {p : ι → ℝ} (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    {S : Finset ι} {e : ι} (he : e ∉ S) {A B : Set (Finset ι)} (hA : IsUpperSet A) (hB : IsUpperSet B)
    {Z : Set (Finset ι × Finset ι)} (hZ : FstLocal S Z) :
    Pr2W D p (Z ∩ hkWith S A B) ≤ Pr2W D p (Z ∩ hkWith (insert e S) A B) := by
  set H0 := hkWith S A B
  set Hp := hkWith (insert e S) A B
  rw [Pr2W_eq_inter_add_diff D p (Z ∩ H0) Hp, Pr2W_eq_inter_add_diff D p (Z ∩ Hp) H0]
  refine add_le_add (Pr2W_mono D hp0 hp1 fun x _ _ hx => ⟨⟨hx.1.1, hx.2⟩, hx.1.2⟩) ?_
  rw [← Pr2W_preimage_swapPair D p (selfDetermined_const (D.erase e)) ((Z ∩ Hp) \ H0)]
  refine Pr2W_mono D hp0 hp1 fun x hx1 hx2 hx => ?_
  have hsw := swapAt_mem_hkWith_of_mem_diff (D := D) he hA hB hx1 hx2 ⟨hx.1.2, hx.2⟩
  refine ⟨⟨hZ x _ (fun i hi => ?_) hx.1.1, hsw.1⟩, hsw.2⟩
  show i ∈ x.1 ↔ i ∈ (swapAt D e x).1
  rw [mem_swapAt_fst hx1 hx2]
  have hie : i ≠ e := fun h => he (h ▸ hi)
  simp [hie]

/-- **The induction step of Theorem 3.2**: pruning one deepest node does not increase the
probability of `{C₁ ∈ A, C₁ →_S C₂ ∈ B}` (with any pre-shared set `S₀` and any auxiliary event `Z`
determined by `C₁` on `S₀`). [cite: Gladkov2024, proof of Thm. 3.2] -/
theorem Pr2W_treeHK_prune_le (D : Finset ι) {p : ι → ℝ} (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    {A B : Set (Finset ι)} (hA : IsUpperSet A) (hB : IsUpperSet B) :
    ∀ (T : DTree ι) (S₀ : Finset ι) (Z : Set (Finset ι × Finset ι)), FstLocal S₀ Z →
      Pr2W D p (Z ∩ treeHK S₀ (prune T) A B) ≤ Pr2W D p (Z ∩ treeHK S₀ T A B)
  | .leaf, _, _, _ => le_rfl
  | .node e yes no, S₀, Z, hZ => by
      have hsplit : ∀ yes' no' : DTree ι, Pr2W D p (Z ∩ treeHK S₀ (.node e yes' no') A B) =
          Pr2W D p ((Z ∩ {x | e ∈ x.1}) ∩ treeHK (insert e S₀) yes' A B) +
            Pr2W D p ((Z ∩ {x | e ∉ x.1}) ∩ treeHK (insert e S₀) no' A B) := by
        intro yes' no'
        rw [treeHK_node, Set.inter_union_distrib_left, Pr2W_union]
        · congr 1
          · congr 1; ext x; simp only [Set.mem_inter_iff, Set.mem_setOf_eq]; tauto
          · congr 1; ext x; simp only [Set.mem_inter_iff, Set.mem_setOf_eq]; tauto
        · exact Set.disjoint_left.2 fun x hx hx' => hx'.2.2 hx.2.2
      simp only [prune]
      by_cases hy : size yes = 0
      · by_cases hn : size no = 0
        · -- both children are leaves: inequality (5)
          simp only [hy, hn, if_true]
          rw [eq_leaf_of_size_eq_zero hy, eq_leaf_of_size_eq_zero hn, treeHK_leaf]
          have hnode : treeHK S₀ (.node e .leaf .leaf) A B = hkWith (insert e S₀) A B := by
            ext x
            simp only [treeHK, Set.mem_setOf_eq, revealed, ite_self]
            rw [Finset.union_insert, Finset.union_empty]
          rw [hnode]
          by_cases he : e ∈ S₀
          · rw [Finset.insert_eq_of_mem he]
          · exact Pr2W_hkWith_le_insert D hp0 hp1 he hA hB hZ
        · simp only [hy, hn, if_true, if_false]
          rw [hsplit, hsplit]
          exact add_le_add le_rfl
            (Pr2W_treeHK_prune_le D hp0 hp1 hA hB no _ _ (hZ.inter_not_mem e))
      · simp only [hy, if_false]
        rw [hsplit, hsplit]
        exact add_le_add (Pr2W_treeHK_prune_le D hp0 hp1 hA hB yes _ _ (hZ.inter_mem e)) le_rfl

/-- Iterating the pruning down to the empty tree. [cite: Gladkov2024, proof of Thm. 3.2] -/
theorem Pr2W_hkWith_empty_le_treeHK (D : Finset ι) {p : ι → ℝ} (hp0 : ∀ i, 0 ≤ p i)
    (hp1 : ∀ i, p i ≤ 1) {A B : Set (Finset ι)} (hA : IsUpperSet A) (hB : IsUpperSet B) :
    ∀ (n : ℕ) (T : DTree ι), size T = n → Pr2W D p (hkWith ∅ A B) ≤ Pr2W D p (treeHK ∅ T A B)
  | 0, T, hT => by rw [eq_leaf_of_size_eq_zero hT, treeHK_leaf]
  | n + 1, T, hT => by
      have hne : size T ≠ 0 := by omega
      have hsz : size (prune T) = n := by have := size_prune T hne; omega
      calc Pr2W D p (hkWith ∅ A B) ≤ Pr2W D p (treeHK ∅ (prune T) A B) :=
            Pr2W_hkWith_empty_le_treeHK D hp0 hp1 hA hB n (prune T) hsz
        _ = Pr2W D p (Set.univ ∩ treeHK ∅ (prune T) A B) := by rw [Set.univ_inter]
        _ ≤ Pr2W D p (Set.univ ∩ treeHK ∅ T A B) :=
            Pr2W_treeHK_prune_le D hp0 hp1 hA hB T ∅ Set.univ (fstLocal_univ ∅)
        _ = Pr2W D p (treeHK ∅ T A B) := by rw [Set.univ_inter]

/-- **Gladkov 2024, Theorem 3.2 (decision-tree Harris–Kleitman inequality)**, finitary form with
inhomogeneous weights: for increasing events `A, B` of configurations and the set `S = S(C₁)` built
by any decision tree `T`, `P(C₁ ∈ A, C₁ →_S C₂ ∈ B) ≥ P(C₁ ∈ A) P(C₁ →_S C₂ ∈ B) = μ(A) μ(B)`.
For the tree querying everything this is the classical Harris–Kleitman (FKG) inequality; for the
empty tree it is the independence of `C₁` and `C₂`. [cite: Gladkov2024, Thm. 3.2] -/
theorem PrW_mul_PrW_le_Pr2W_treeHK (D : Finset ι) {p : ι → ℝ} (hp0 : ∀ i, 0 ≤ p i)
    (hp1 : ∀ i, p i ≤ 1) (T : DTree ι) {A B : Set (Finset ι)} (hA : IsUpperSet A)
    (hB : IsUpperSet B) : PrW D p A * PrW D p B ≤ Pr2W D p (treeHK ∅ T A B) := by
  rw [← Pr2W_prod, ← hkWith_empty]
  exact Pr2W_hkWith_empty_le_treeHK D hp0 hp1 hA hB (size T) T rfl

end HK

end DecisionTree

end Percolation.Literature
