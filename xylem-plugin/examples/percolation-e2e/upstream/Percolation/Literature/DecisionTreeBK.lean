import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Group.Indicator
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.Order.UpperLower.Basic
import Percolation.Util.Linter

/-!
# The van den Berg–Kesten inequality for decision trees (Gladkov 2024, Thm. 4.3)

Source: N. Gladkov, *Percolation Inequalities and
Decision Trees*, arXiv:2408.08457v2 (2024) [Gladkov2024], §2 (Def. 2.3, Def. 2.4, Algorithm 1),
§4 (Def. 4.1, Def. 4.2, **Theorem 4.3** and its proof, pp. 5–6).

Everything here is proved, in the finitary form in which it is used for Gladkov's three-point bound
(Thm. 6.2): a finite set `D` of coordinates ("edges"), configurations `S ⊆ D` (the set of open
coordinates) weighted by the Bernoulli weights `wt D p S = ∏_{i ∈ D} (p if i ∈ S, else 1 - p)`, and
probabilities of events of one configuration (`Pr`) and of an independent pair of configurations
(`Pr2`) as finite sums.

* `DTree ι` — binary decision trees querying coordinates of the FIRST configuration and sending
  every queried coordinate to `S` (the sub-class of Def. 2.4 / Algorithm 1 needed in §6; a
  general tree of Def. 2.4 with `S̄`-decisions below the last `S`-decision builds the same set);
  `revealed T S` — the set `S(C₁)` built by `T` on `C₁ = S`; `prune` — removal of one deepest
  node (the surgery `T ↦ T'` of the printed proof); `revealed_congr` — the set built is
  determined by the configuration on it.

Design: configurations are `Finset ι` with `S ⊆ D` enforced by summing over `D.powerset` (no measure
theory; the link with `bondPercolation` is `Russo.measureReal_eq_cylPoly`, made). Increasing events
are `IsUpperSet (A : Set (Finset ι))`. Not here: trees reading both configurations or with
`S̄`-decisions at inner nodes (Def. 2.4 in full), the decision-tree HK inequality (Thm. 3.2), Main
Lemma 8.1.
-/

noncomputable section

namespace Percolation.Literature

namespace DecisionTree

open Finset

variable {ι : Type*} [DecidableEq ι]

/-! ### Splicing two configurations (`C₁ →_F C₂`) -/

/-- `splice F S₁ S₂ = (S₁ ∩ F) ∪ (S₂ \ F)`: the configuration `C₁ →_F C₂` that coincides with
`S₁` on `F` and with `S₂` off `F`. [cite: Gladkov2024, Def. 2.3] -/
def splice (F S₁ S₂ : Finset ι) : Finset ι := (S₁ ∩ F) ∪ (S₂ \ F)

/-- Membership in a splice. [cite: Gladkov2024, Def. 2.3] -/
theorem mem_splice {F S₁ S₂ : Finset ι} {i : ι} :
    i ∈ splice F S₁ S₂ ↔ (i ∈ F ∧ i ∈ S₁) ∨ (i ∉ F ∧ i ∈ S₂) := by
  simp only [splice, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
  tauto

/-- On `F` the splice is the first configuration. [cite: Gladkov2024, Def. 2.3] -/
theorem mem_splice_of_mem {F S₁ S₂ : Finset ι} {i : ι} (hi : i ∈ F) :
    i ∈ splice F S₁ S₂ ↔ i ∈ S₁ := by
  rw [mem_splice]; tauto

/-- Off `F` the splice is the second configuration. [cite: Gladkov2024, Def. 2.3] -/
theorem mem_splice_of_not_mem {F S₁ S₂ : Finset ι} {i : ι} (hi : i ∉ F) :
    i ∈ splice F S₁ S₂ ↔ i ∈ S₂ := by
  rw [mem_splice]; tauto

/-- A splice of configurations `⊆ D` is `⊆ D`. [folklore] -/
theorem splice_subset {D F S₁ S₂ : Finset ι} (h₁ : S₁ ⊆ D) (h₂ : S₂ ⊆ D) :
    splice F S₁ S₂ ⊆ D := by
  intro i hi
  rcases mem_splice.1 hi with ⟨-, h⟩ | ⟨-, h⟩
  · exact h₁ h
  · exact h₂ h

/-- Splicing back: `(S₁ →_F S₂) →_F (S₂ →_F S₁) = S₁`. [folklore] -/
theorem splice_splice_left (F S₁ S₂ : Finset ι) :
    splice F (splice F S₁ S₂) (splice F S₂ S₁) = S₁ := by
  ext i
  by_cases hi : i ∈ F
  · rw [mem_splice_of_mem hi, mem_splice_of_mem hi]
  · rw [mem_splice_of_not_mem hi, mem_splice_of_not_mem hi]

/-- The splice agrees with the first configuration on `F`. [folklore] -/
theorem splice_agree (F S₁ S₂ : Finset ι) : ∀ i ∈ F, (i ∈ splice F S₁ S₂ ↔ i ∈ S₁) :=
  fun _ hi => mem_splice_of_mem hi

/-- If `S₁'` agrees with `S₁` on `F`, splicing gives the same result. [folklore] -/
theorem splice_congr_left {F S₁ S₁' : Finset ι} (h : ∀ i ∈ F, (i ∈ S₁ ↔ i ∈ S₁')) (S₂ : Finset ι) :
    splice F S₁ S₂ = splice F S₁' S₂ := by
  ext i
  by_cases hi : i ∈ F
  · rw [mem_splice_of_mem hi, mem_splice_of_mem hi, h i hi]
  · rw [mem_splice_of_not_mem hi, mem_splice_of_not_mem hi]

/-! ### The swap involution of the pair space -/

/-- A set-valued map on configurations is *self-determined* if its value is determined by the
configuration restricted to that value (the defining property of a set built by a decision
tree reading `C₁`). [cite: Gladkov2024, Def. 2.4] -/
def SelfDetermined (Fm : Finset ι → Finset ι) : Prop :=
  ∀ S S' : Finset ι, (∀ i ∈ Fm S, (i ∈ S ↔ i ∈ S')) → Fm S' = Fm S

/-- The swap of the pair space along a (configuration-dependent) set `Fm C₁`:
`(C₁, C₂) ↦ (C₁ →_F C₂, C₂ →_F C₁)`. [cite: Gladkov2024, Lemma 3.1] -/
def swapPair (Fm : Finset ι → Finset ι) (x : Finset ι × Finset ι) : Finset ι × Finset ι :=
  (splice (Fm x.1) x.1 x.2, splice (Fm x.1) x.2 x.1)

/-- The first component of the swap agrees with `C₁` on `Fm C₁`, so builds the same set.
[cite: Gladkov2024, Lemma 3.1] -/
theorem apply_swapPair_fst {Fm : Finset ι → Finset ι} (hF : SelfDetermined Fm)
    (x : Finset ι × Finset ι) : Fm (swapPair Fm x).1 = Fm x.1 :=
  hF x.1 _ fun _ hi => (mem_splice_of_mem hi).symm

/-- The swap is an involution. [cite: Gladkov2024, Lemma 3.1] -/
theorem swapPair_swapPair {Fm : Finset ι → Finset ι} (hF : SelfDetermined Fm)
    (x : Finset ι × Finset ι) : swapPair Fm (swapPair Fm x) = x := by
  have h1 := apply_swapPair_fst hF x
  unfold swapPair at h1 ⊢
  simp only at h1 ⊢
  rw [h1, splice_splice_left, splice_splice_left]

/-- The swap preserves the pair space of configurations `⊆ D`. [folklore] -/
theorem swapPair_mem {D : Finset ι} (Fm : Finset ι → Finset ι) {x : Finset ι × Finset ι}
    (hx : x ∈ D.powerset ×ˢ D.powerset) : swapPair Fm x ∈ D.powerset ×ˢ D.powerset := by
  rw [Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset] at hx ⊢
  exact ⟨splice_subset hx.1 hx.2, splice_subset hx.2 hx.1⟩

/-! ### The Cauchy–Schwarz step (Theorem 5.2 for a tree that reveals everything it queries) -/

section CauchySchwarz

open Classical in
/-- The `0/1`-indicator of an event, as a real number. [folklore] -/
def ind {α : Type*} (X : Set α) (x : α) : ℝ := if x ∈ X then 1 else 0

omit [DecidableEq ι] in
/-- `ind` of a member. [folklore] -/
theorem ind_of_mem {α : Type*} {X : Set α} {x : α} (h : x ∈ X) : ind X x = 1 := by
  unfold ind; rw [if_pos h]

omit [DecidableEq ι] in
/-- `ind` of a non-member. [folklore] -/
theorem ind_of_not_mem {α : Type*} {X : Set α} {x : α} (h : x ∉ X) : ind X x = 0 := by
  unfold ind; rw [if_neg h]

omit [DecidableEq ι] in
/-- `0 ≤ ind X x`. [folklore] -/
theorem ind_nonneg {α : Type*} (X : Set α) (x : α) : 0 ≤ ind X x := by
  by_cases h : x ∈ X
  · rw [ind_of_mem h]; exact zero_le_one
  · rw [ind_of_not_mem h]

omit [DecidableEq ι] in
/-- The indicator of a weight is the weight times `ind`. [folklore] -/
theorem indicator_eq_mul_ind {α : Type*} (X : Set α) (f : α → ℝ) (x : α) :
    X.indicator f x = f x * ind X x := by
  by_cases h : x ∈ X
  · rw [Set.indicator_of_mem h, ind_of_mem h, mul_one]
  · rw [Set.indicator_of_notMem h, ind_of_not_mem h, mul_zero]

end CauchySchwarz

/-! ### Decision trees reading the first configuration -/

/-- Binary decision trees over the coordinates `ι`: a `leaf` stops; `node e yes no` queries the
coordinate `e` of the first configuration, sends it to `S`, and continues with `yes` if `e` is
open and with `no` otherwise. [cite: Gladkov2024, Def. 2.4 and Algorithm 1] -/
inductive _root_.Percolation.Literature.DTree (ι : Type*) : Type _
  | leaf : DTree ι
  | node : ι → DTree ι → DTree ι → DTree ι

/-- The set `S(C₁)` built by the tree on the configuration `C₁ = S`: the coordinates queried
along the path followed by `S`. [cite: Gladkov2024, Def. 2.4 and Algorithm 1] -/
def revealed : DTree ι → Finset ι → Finset ι
  | .leaf, _ => ∅
  | .node e yes no, S => if e ∈ S then insert e (revealed yes S) else insert e (revealed no S)

/-- The number of (decision) nodes of a tree. [folklore] -/
def size : DTree ι → ℕ
  | .leaf => 0
  | .node _ yes no => size yes + size no + 1

/-- Removing one deepest node (a node both of whose children are leaves): the surgery
`T ↦ T'` of the printed proof, which stops querying one coordinate. [cite: Gladkov2024, proof of Thm. 4.3 (and of Thm. 3.2)] -/
def prune : DTree ι → DTree ι
  | .leaf => .leaf
  | .node e yes no =>
      if size yes = 0 then (if size no = 0 then .leaf else .node e yes (prune no))
      else .node e (prune yes) no

omit [DecidableEq ι] in
/-- A tree of size `0` is a leaf. [folklore] -/
theorem eq_leaf_of_size_eq_zero {T : DTree ι} (h : size T = 0) : T = .leaf := by
  cases T with
  | leaf => rfl
  | node e yes no => simp [size] at h

omit [DecidableEq ι] in
/-- Pruning removes exactly one node. [folklore] -/
theorem size_prune : ∀ T : DTree ι, size T ≠ 0 → size (prune T) + 1 = size T
  | .leaf, h => absurd rfl h
  | .node e yes no, _ => by
      simp only [prune]
      by_cases hy : size yes = 0
      · by_cases hn : size no = 0
        · simp [hy, hn, size]
        · simp only [hy, hn, if_true, if_false, size]
          have := size_prune no hn
          omega
      · simp only [hy, if_false, size]
        have := size_prune yes hy
        omega

/-- **The set built by a tree is determined by the configuration on it** (determinism of the
exploration): if `S'` agrees with `S` on `revealed T S` then `T` builds the same set on `S'`.
[cite: Gladkov2024, Def. 2.4] -/
theorem revealed_congr : ∀ (T : DTree ι) {S S' : Finset ι},
    (∀ i ∈ revealed T S, (i ∈ S ↔ i ∈ S')) → revealed T S' = revealed T S
  | .leaf, _, _, _ => rfl
  | .node e yes no, S, S', h => by
      have he : e ∈ revealed (.node e yes no) S := by
        unfold revealed; split_ifs <;> exact Finset.mem_insert_self _ _
      have hee := h e he
      by_cases hS : e ∈ S
      · have hS' : e ∈ S' := hee.1 hS
        have hsub : ∀ i ∈ revealed yes S, (i ∈ S ↔ i ∈ S') := fun i hi =>
          h i (by unfold revealed; rw [if_pos hS]; exact Finset.mem_insert_of_mem hi)
        show (if e ∈ S' then _ else _) = (if e ∈ S then _ else _)
        rw [if_pos hS', if_pos hS, revealed_congr yes hsub]
      · have hS' : e ∉ S' := fun h' => hS (hee.2 h')
        have hsub : ∀ i ∈ revealed no S, (i ∈ S ↔ i ∈ S') := fun i hi =>
          h i (by unfold revealed; rw [if_neg hS]; exact Finset.mem_insert_of_mem hi)
        show (if e ∈ S' then _ else _) = (if e ∈ S then _ else _)
        rw [if_neg hS', if_neg hS, revealed_congr no hsub]

/-- `revealed T` is self-determined. [cite: Gladkov2024, Def. 2.4] -/
theorem selfDetermined_revealed (T : DTree ι) : SelfDetermined (revealed T) :=
  fun _ _ h => revealed_congr T h

omit [DecidableEq ι] in
/-- A constant set is self-determined. [folklore] -/
theorem selfDetermined_const (F : Finset ι) : SelfDetermined fun _ : Finset ι => F :=
  fun _ _ _ => rfl

/-! ### Disjoint occurrence along a set `S` -/

/-- An event of the pair space is *determined by `C₁` on `S₀`* if membership only depends on
the first configuration restricted to `S₀`. [folklore] -/
def FstLocal (S₀ : Finset ι) (Z : Set (Finset ι × Finset ι)) : Prop :=
  ∀ x y : Finset ι × Finset ι, (∀ i ∈ S₀, (i ∈ x.1 ↔ i ∈ y.1)) → x ∈ Z → y ∈ Z

omit [DecidableEq ι] in
/-- `univ` is determined by nothing. [folklore] -/
theorem fstLocal_univ (S₀ : Finset ι) : FstLocal S₀ (Set.univ : Set (Finset ι × Finset ι)) :=
  fun _ _ _ _ => Set.mem_univ _

/-- Intersecting with the query `e ∈ C₁` keeps locality on `insert e S₀`. [folklore] -/
theorem FstLocal.inter_mem {S₀ : Finset ι} {Z : Set (Finset ι × Finset ι)} (hZ : FstLocal S₀ Z)
    (e : ι) : FstLocal (insert e S₀) (Z ∩ {x | e ∈ x.1}) := fun x y h hx =>
  ⟨hZ x y (fun i hi => h i (Finset.mem_insert_of_mem hi)) hx.1,
    (h e (Finset.mem_insert_self e S₀)).1 hx.2⟩

/-- Intersecting with the query `e ∉ C₁` keeps locality on `insert e S₀`. [folklore] -/
theorem FstLocal.inter_not_mem {S₀ : Finset ι} {Z : Set (Finset ι × Finset ι)}
    (hZ : FstLocal S₀ Z) (e : ι) : FstLocal (insert e S₀) (Z ∩ {x | e ∉ x.1}) := fun x y h hx =>
  ⟨hZ x y (fun i hi => h i (Finset.mem_insert_of_mem hi)) hx.1,
    fun hy => hx.2 ((h e (Finset.mem_insert_self e S₀)).2 hy)⟩

/-! ### The one-edge splitting step -/

/-- The swap of the single coordinate `e` between the two configurations (of coordinates
`⊆ D`): `(C₁, C₂) ↦ (C₁ →_{D ∖ e} C₂, C₂ →_{D ∖ e} C₁)`. [cite: Gladkov2024, proof of Thm. 4.3] -/
def swapAt (D : Finset ι) (e : ι) : Finset ι × Finset ι → Finset ι × Finset ι :=
  swapPair fun _ : Finset ι => D.erase e

/-- First component of the swap at `e`. [folklore] -/
theorem mem_swapAt_fst {D : Finset ι} {e : ι} {x : Finset ι × Finset ι} (hx1 : x.1 ⊆ D)
    (hx2 : x.2 ⊆ D) (i : ι) :
    i ∈ (swapAt D e x).1 ↔ (i ≠ e ∧ i ∈ x.1) ∨ (i = e ∧ i ∈ x.2) := by
  simp only [swapAt, swapPair]
  rw [mem_splice]
  simp only [Finset.mem_erase]
  constructor
  · rintro (⟨⟨hie, -⟩, hi⟩ | ⟨hne, hi⟩)
    · exact Or.inl ⟨hie, hi⟩
    · right
      refine ⟨?_, hi⟩
      by_contra hie
      exact hne ⟨hie, hx2 hi⟩
  · rintro (⟨hie, hi⟩ | ⟨hie, hi⟩)
    · exact Or.inl ⟨⟨hie, hx1 hi⟩, hi⟩
    · right
      exact ⟨fun h => h.1 hie, hi⟩

/-- Second component of the swap at `e`. [folklore] -/
theorem mem_swapAt_snd {D : Finset ι} {e : ι} {x : Finset ι × Finset ι} (hx1 : x.1 ⊆ D)
    (hx2 : x.2 ⊆ D) (i : ι) :
    i ∈ (swapAt D e x).2 ↔ (i ≠ e ∧ i ∈ x.2) ∨ (i = e ∧ i ∈ x.1) := by
  simp only [swapAt, swapPair]
  rw [mem_splice]
  simp only [Finset.mem_erase]
  constructor
  · rintro (⟨⟨hie, -⟩, hi⟩ | ⟨hne, hi⟩)
    · exact Or.inl ⟨hie, hi⟩
    · right
      refine ⟨?_, hi⟩
      by_contra hie
      exact hne ⟨hie, hx1 hi⟩
  · rintro (⟨hie, hi⟩ | ⟨hie, hi⟩)
    · exact Or.inl ⟨⟨hie, hx2 hi⟩, hi⟩
    · right
      exact ⟨fun h => h.1 hie, hi⟩

/-- Pointwise description of `C₁ →_{S ∪ {e}} C₂`. [folklore] -/
theorem mem_splice_insert {S X₁ X₂ : Finset ι} {e i : ι} :
    i ∈ splice (insert e S) X₁ X₂ ↔
      (i = e ∧ i ∈ X₁) ∨ (i ≠ e ∧ ((i ∈ S ∧ i ∈ X₁) ∨ (i ∉ S ∧ i ∈ X₂))) := by
  rw [mem_splice]
  simp only [Finset.mem_insert]
  by_cases hie : i = e
  · subst hie; simp
  · simp [hie]

end DecisionTree

end Percolation.Literature
