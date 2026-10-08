import Mathlib.Probability.ProductMeasure
import Percolation.Literature.Basic
import Percolation.Literature.PercolationEvents
import Percolation.Literature.SitePercolationMeasure
import Percolation.Util.Linter

/-!
# Site percolation: transport of connection events under the lattice symmetries of `ℤ^d`, exit lemma, boxes

Elementary facts about site percolation on `ℤ^d` used in Cerf's two-arms argument (Cerf 2015, §10, p. 15): the signed
coordinate permutations of `ℤ^d` as graph automorphisms of `zdGraph d` (`LatticeModels.Site.signedPerm`, `zdGraph_adj_signedPerm`,
`zdShiftIso`) and the transport of connection events and their probabilities under them, the FKG gluing of connections, and
the exit estimate `θ(p) ≤ Σ_{x ∈ ∂ⁱⁿΛ(n)} P(0 ⟷ x in Λ(n))` with `|∂ⁱⁿΛ(n)| ≤ 2d(2n+1)^{d−1}`. Everything is standard
(Grimmett, *Percolation* (1999), §§1.6, 2.2).

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §1.6 (site percolation), §2.2 ((2.7): the standard FKG gluing of
  connections).
* R. Cerf, Ann. Probab. 43 (2015) 2458–2480, arXiv:1306.3105, §10, p. 15 (where these facts are used).
-/

noncomputable section

noncomputable section

namespace Percolation.Literature

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal

variable {V W : Type*}

/-! ### Automorphisms of `ℤ^d` -/

section ZdAut

variable {d : ℕ}

/-- Translation by `v` is an automorphism of the nearest-neighbour graph `ℤ^d`. [folklore] -/
def zdShiftIso (v : LatticeModels.Site d) : LatticeModels.zdGraph d ≃g LatticeModels.zdGraph d where
  toEquiv := LatticeModels.Site.shift v
  map_rel_iff' := by
    intro a b
    exact LatticeModels.zdGraph_adj_shift_iff v a b

/-- `zdShiftIso v x = x + v`. [folklore] -/
@[simp] theorem zdShiftIso_apply (v x : LatticeModels.Site d) : zdShiftIso v x = x + v := rfl

/-- A signed coordinate permutation `x ↦ (i ↦ ε i * x (π⁻¹ i))` with signs `ε i = ±1`, as a
bijection of `ℤ^d` (the hyperoctahedral symmetries fixing the origin). [folklore] -/
def _root_.Percolation.Literature.LatticeModels.Site.signedPerm (π : Equiv.Perm (Fin d)) (ε : Fin d → ℤˣ) : LatticeModels.Site d ≃ LatticeModels.Site d where
  toFun x := fun i => (ε i : ℤ) * x (π.symm i)
  invFun y := fun j => (ε (π j) : ℤ) * y (π j)
  left_inv x := by
    funext j
    simp [← mul_assoc]
  right_inv y := by
    funext i
    simp [← mul_assoc]

/-- Coordinates of a signed permutation. [folklore] -/
@[simp] theorem _root_.Percolation.Literature.LatticeModels.Site.signedPerm_apply (π : Equiv.Perm (Fin d)) (ε : Fin d → ℤˣ) (x : LatticeModels.Site d)
    (i : Fin d) : LatticeModels.Site.signedPerm π ε x i = (ε i : ℤ) * x (π.symm i) := rfl

/-- Coordinates of the inverse signed permutation. [folklore] -/
@[simp] theorem _root_.Percolation.Literature.LatticeModels.Site.signedPerm_symm_apply (π : Equiv.Perm (Fin d)) (ε : Fin d → ℤˣ)
    (y : LatticeModels.Site d) (j : Fin d) : (LatticeModels.Site.signedPerm π ε).symm y j = (ε (π j) : ℤ) * y (π j) := rfl

/-- The inverse of a signed permutation is a signed permutation. [folklore] -/
theorem _root_.Percolation.Literature.LatticeModels.Site.signedPerm_symm (π : Equiv.Perm (Fin d)) (ε : Fin d → ℤˣ) :
    (LatticeModels.Site.signedPerm π ε).symm = LatticeModels.Site.signedPerm π.symm (ε ∘ π) :=
  Equiv.ext fun y => funext fun j => by simp

/-- Signed permutations fix the origin. [folklore] -/
@[simp] theorem _root_.Percolation.Literature.LatticeModels.Site.signedPerm_zero (π : Equiv.Perm (Fin d)) (ε : Fin d → ℤˣ) :
    LatticeModels.Site.signedPerm π ε 0 = 0 := by
  funext i; simp

/-- Signed permutations are additive. [folklore] -/
theorem _root_.Percolation.Literature.LatticeModels.Site.signedPerm_add (π : Equiv.Perm (Fin d)) (ε : Fin d → ℤˣ) (x y : LatticeModels.Site d) :
    LatticeModels.Site.signedPerm π ε (x + y) = LatticeModels.Site.signedPerm π ε x + LatticeModels.Site.signedPerm π ε y := by
  funext i; simp [mul_add]

/-- Signed permutations map unit vectors to signed unit vectors. [folklore] -/
theorem _root_.Percolation.Literature.LatticeModels.Site.signedPerm_single (π : Equiv.Perm (Fin d)) (ε : Fin d → ℤˣ) (i : Fin d) :
    LatticeModels.Site.signedPerm π ε (Pi.single i 1) = (ε (π i) : ℤ) • Pi.single (π i) (1 : ℤ) := by
  funext j
  simp only [LatticeModels.Site.signedPerm_apply, Pi.smul_apply, smul_eq_mul]
  rcases eq_or_ne j (π i) with rfl | hj
  · simp
  · have : π.symm j ≠ i := fun h => hj (by rw [← h, Equiv.apply_symm_apply])
    simp [Pi.single_eq_of_ne this, Pi.single_eq_of_ne hj]

/-- Signed coordinate permutations map neighbours to neighbours. [folklore] -/
theorem zdGraph_adj_signedPerm (π : Equiv.Perm (Fin d)) (ε : Fin d → ℤˣ) {x y : LatticeModels.Site d}
    (h : (LatticeModels.zdGraph d).Adj x y) :
    (LatticeModels.zdGraph d).Adj (LatticeModels.Site.signedPerm π ε x) (LatticeModels.Site.signedPerm π ε y) := by
  rw [LatticeModels.zdGraph_adj_iff] at h ⊢
  obtain ⟨i, h⟩ := h
  refine ⟨π i, ?_⟩
  rcases Int.units_eq_one_or (ε (π i)) with hε | hε
  · rcases h with rfl | rfl
    · left; rw [LatticeModels.Site.signedPerm_add, LatticeModels.Site.signedPerm_single, hε]; simp
    · right; rw [LatticeModels.Site.signedPerm_add, LatticeModels.Site.signedPerm_single, hε]; simp
  · rcases h with rfl | rfl
    · right
      rw [LatticeModels.Site.signedPerm_add, LatticeModels.Site.signedPerm_single, hε]
      simp [add_assoc]
    · left
      rw [LatticeModels.Site.signedPerm_add, LatticeModels.Site.signedPerm_single, hε]
      simp [add_assoc]

/-- Signed coordinate permutations are automorphisms of `ℤ^d`. [folklore] -/
def zdSignedPermIso (π : Equiv.Perm (Fin d)) (ε : Fin d → ℤˣ) : LatticeModels.zdGraph d ≃g LatticeModels.zdGraph d where
  toEquiv := LatticeModels.Site.signedPerm π ε
  map_rel_iff' := by
    intro a b
    refine ⟨fun h => ?_, zdGraph_adj_signedPerm π ε⟩
    have := zdGraph_adj_signedPerm π.symm (ε ∘ π) h
    rwa [← LatticeModels.Site.signedPerm_symm, Equiv.symm_apply_apply, Equiv.symm_apply_apply] at this

/-- `zdSignedPermIso` acts by `Site.signedPerm`. [folklore] -/
@[simp] theorem zdSignedPermIso_apply (π : Equiv.Perm (Fin d)) (ε : Fin d → ℤˣ) (x : LatticeModels.Site d) :
    zdSignedPermIso π ε x = LatticeModels.Site.signedPerm π ε x := rfl

/-- Signed coordinate permutations preserve the boxes `Λ(n)`. [folklore] -/
theorem signedPerm_mem_box_iff (π : Equiv.Perm (Fin d)) (ε : Fin d → ℤˣ) {n : ℕ} {x : LatticeModels.Site d} :
    LatticeModels.Site.signedPerm π ε x ∈ LatticeModels.box d n ↔ x ∈ LatticeModels.box d n := by
  simp only [LatticeModels.mem_box, LatticeModels.Site.signedPerm_apply]
  constructor
  · intro h j
    have := h (π j)
    rw [Equiv.symm_apply_apply] at this
    rcases Int.units_eq_one_or (ε (π j)) with hε | hε <;> rw [hε] at this <;> simp at this <;>
      omega
  · intro h i
    have := h (π.symm i)
    rcases Int.units_eq_one_or (ε i) with hε | hε <;> rw [hε] <;> simp <;> omega

end ZdAut

/-! ### Exit through the inner boundary; `θ ≤ P(x ⟷ ∂ⁱⁿΛ in Λ)` -/

section Exit

variable {G : SimpleGraph V} [DecidableEq V] [G.LocallyFinite]

/-- A walk in a subgraph `H ≤ G` from a vertex of `Λ` to a vertex outside `Λ` passes through the
inner vertex boundary of `Λ`, and its initial segment up to that point stays inside `Λ`.
[folklore] -/
theorem exists_innerBoundary_reachable_of_walk {H : SimpleGraph V} (hH : H ≤ G) (Λ : Finset V) :
    ∀ {u v : V} (_ : H.Walk u v), u ∈ Λ → v ∉ Λ →
      ∃ b ∈ LatticeModels.innerBoundary G Λ, ∃ (hu : u ∈ (↑Λ : Set V)) (hb : b ∈ (↑Λ : Set V)),
        (H.induce (↑Λ : Set V)).Reachable ⟨u, hu⟩ ⟨b, hb⟩ := by
  intro u v w
  induction w with
  | nil => intro hu hv; exact absurd hu hv
  | @cons a c _ hac w ih =>
    intro ha hv
    by_cases hc : c ∈ Λ
    · obtain ⟨b, hb, hcΛ, hbΛ, hr⟩ := ih hc hv
      refine ⟨b, hb, ha, hbΛ, SimpleGraph.Reachable.trans (SimpleGraph.Adj.reachable ?_) hr⟩
      simpa [SimpleGraph.comap_adj] using hac
    · refine ⟨a, ?_, ha, ha, SimpleGraph.Reachable.refl _⟩
      rw [LatticeModels.mem_innerBoundary_iff]
      exact ⟨ha, c, hc, hH hac⟩

end Exit

/-! ### Geometry of the boxes `Λ(n) ⊆ ℤ^d` -/

section ZdBox

variable {d : ℕ}

/-- Every site of `Λ(n)` is joined to the origin by a nearest-neighbour path inside `Λ(n)`
(move one coordinate towards `0` at a time). [folklore] -/
theorem box_induce_reachable_zero (n : ℕ) {x : LatticeModels.Site d} (hx : x ∈ LatticeModels.box d n) :
    ((LatticeModels.zdGraph d).induce (↑(LatticeModels.box d n) : Set (LatticeModels.Site d))).Reachable ⟨x, hx⟩ ⟨0, LatticeModels.zero_mem_box d n⟩ := by
  suffices H : ∀ m : ℕ, ∀ x : LatticeModels.Site d, ∀ hx : x ∈ LatticeModels.box d n, ∑ i, (x i).natAbs = m →
      ((LatticeModels.zdGraph d).induce (↑(LatticeModels.box d n) : Set (LatticeModels.Site d))).Reachable ⟨x, hx⟩ ⟨0, LatticeModels.zero_mem_box d n⟩ from
    H _ x hx rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro x hx hm
    by_cases h0 : x = 0
    · subst h0; rfl
    · obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
        by_contra h
        push Not at h
        exact h0 (funext h)
      have hxi := (LatticeModels.mem_box.1 hx) i
      set v : ℤ := if 0 < x i then x i - 1 else x i + 1 with hv
      set x' : LatticeModels.Site d := Function.update x i v with hx'
      have hx'j : ∀ j, j ≠ i → x' j = x j := fun j hj => by simp [hx', hj]
      have hx'i : x' i = v := by simp [hx']
      have hx'box : x' ∈ LatticeModels.box d n := by
        rw [LatticeModels.mem_box] at hx ⊢
        intro j
        rcases eq_or_ne j i with rfl | hj
        · rw [hx'i, hv]; split_ifs <;> omega
        · rw [hx'j j hj]; exact hx j
      have hadj : (LatticeModels.zdGraph d).Adj x x' := by
        rw [LatticeModels.zdGraph_adj_iff]
        refine ⟨i, ?_⟩
        by_cases hpos : 0 < x i
        · right
          funext j
          rcases eq_or_ne j i with rfl | hj
          · simp [hx'i, hv, hpos]
          · simp [hx'j j hj, hj]
        · left
          funext j
          rcases eq_or_ne j i with rfl | hj
          · simp [hx'i, hv, hpos]
          · simp [hx'j j hj, hj]
      have hlt : ∑ j, (x' j).natAbs < m := by
        rw [← hm]
        apply Finset.sum_lt_sum
        · intro j _
          rcases eq_or_ne j i with rfl | hj
          · rw [hx'i, hv]; split_ifs <;> omega
          · rw [hx'j j hj]
        · refine ⟨i, Finset.mem_univ _, ?_⟩
          rw [hx'i, hv]; split_ifs <;> omega
      have hadj' : ((LatticeModels.zdGraph d).induce (↑(LatticeModels.box d n) : Set (LatticeModels.Site d))).Adj ⟨x, hx⟩ ⟨x', hx'box⟩ := by
        simpa [SimpleGraph.comap_adj] using hadj
      exact hadj'.reachable.trans (ih _ hlt x' hx'box rfl)

/-- Any two sites of `Λ(n)` are joined by a nearest-neighbour path inside `Λ(n)`. [folklore] -/
theorem box_induce_reachable (n : ℕ) {x y : LatticeModels.Site d} (hx : x ∈ LatticeModels.box d n) (hy : y ∈ LatticeModels.box d n) :
    ((LatticeModels.zdGraph d).induce (↑(LatticeModels.box d n) : Set (LatticeModels.Site d))).Reachable ⟨x, hx⟩ ⟨y, hy⟩ :=
  (box_induce_reachable_zero n hx).trans (box_induce_reachable_zero n hy).symm

/-- A site of the inner boundary of `Λ(n)` lies on a face `{x_i = ±n}`. [folklore] -/
theorem exists_eq_of_mem_innerBoundary_box {n : ℕ} {x : LatticeModels.Site d}
    (hx : x ∈ LatticeModels.innerBoundary (LatticeModels.zdGraph d) (LatticeModels.box d n)) : ∃ i, x i = n ∨ x i = -n := by
  rw [LatticeModels.mem_innerBoundary_iff] at hx
  obtain ⟨hx, y, hy, hxy⟩ := hx
  rw [LatticeModels.mem_box] at hx hy
  push Not at hy
  obtain ⟨j, hj⟩ := hy
  rw [LatticeModels.zdGraph_adj_iff] at hxy
  obtain ⟨i, h | h⟩ := hxy
  · have hyj : y j = x j + (Pi.single i (1 : ℤ) : LatticeModels.Site d) j := by rw [h]; rfl
    refine ⟨j, ?_⟩
    rcases eq_or_ne j i with rfl | hji
    · simp at hyj; have := hx j; omega
    · simp [hji] at hyj; have := hx j; omega
  · have hxj : x j = y j + (Pi.single i (1 : ℤ) : LatticeModels.Site d) j := by rw [h]; rfl
    refine ⟨j, ?_⟩
    rcases eq_or_ne j i with rfl | hji
    · simp at hxj; have := hx j; omega
    · simp [hji] at hxj; have := hx j; omega

/-- The face `{x ∈ Λ(n) : x_i = c}` has at most `(2n+1)^{d-1}` sites. [folklore] -/
theorem card_filter_box_apply_eq_le (n : ℕ) (i : Fin d) (c : ℤ) :
    ((LatticeModels.box d n).filter fun x => x i = c).card ≤ (2 * n + 1) ^ (d - 1) := by
  classical
  calc ((LatticeModels.box d n).filter fun x => x i = c).card
      ≤ (Fintype.piFinset fun j => if j = i then ({c} : Finset ℤ) else Finset.Icc (-(n : ℤ)) n).card := by
        refine Finset.card_le_card fun x hx => ?_
        rw [Finset.mem_filter, LatticeModels.mem_box] at hx
        rw [Fintype.mem_piFinset]
        intro j
        split_ifs with hj
        · subst hj; simp [hx.2]
        · exact Finset.mem_Icc.2 (hx.1 j)
    _ = (2 * n + 1) ^ (d - 1) := by
        rw [Fintype.card_piFinset]
        simp only [apply_ite Finset.card, Finset.card_singleton, Int.card_Icc]
        rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const,
          Finset.filter_ne' Finset.univ i, Finset.card_erase_of_mem (Finset.mem_univ i),
          Finset.card_univ, Fintype.card_fin]
        congr 1; omega

/-- **`|∂ⁱⁿΛ(n)| ≤ 2d(2n+1)^{d-1}`** (Cerf 2015, §6/§10). [folklore] -/
theorem card_innerBoundary_box_le (n : ℕ) :
    (LatticeModels.innerBoundary (LatticeModels.zdGraph d) (LatticeModels.box d n)).card ≤ 2 * d * (2 * n + 1) ^ (d - 1) := by
  classical
  have hsub : LatticeModels.innerBoundary (LatticeModels.zdGraph d) (LatticeModels.box d n) ⊆ Finset.univ.biUnion fun i : Fin d =>
      ((LatticeModels.box d n).filter fun x => x i = (n : ℤ)) ∪ ((LatticeModels.box d n).filter fun x => x i = -(n : ℤ)) := by
    intro x hx
    have hxbox : x ∈ LatticeModels.box d n := (LatticeModels.mem_innerBoundary_iff.1 hx).1
    obtain ⟨i, hi⟩ := exists_eq_of_mem_innerBoundary_box hx
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_filter]
    exact ⟨i, hi.imp (fun h => ⟨hxbox, h⟩) (fun h => ⟨hxbox, h⟩)⟩
  calc (LatticeModels.innerBoundary (LatticeModels.zdGraph d) (LatticeModels.box d n)).card
      ≤ (Finset.univ.biUnion fun i : Fin d =>
          ((LatticeModels.box d n).filter fun x => x i = (n : ℤ)) ∪
            ((LatticeModels.box d n).filter fun x => x i = -(n : ℤ))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ i : Fin d, (((LatticeModels.box d n).filter fun x => x i = (n : ℤ)) ∪
          ((LatticeModels.box d n).filter fun x => x i = -(n : ℤ))).card := Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin d, 2 * (2 * n + 1) ^ (d - 1) := by
        refine Finset.sum_le_sum fun i _ => (Finset.card_union_le _ _).trans ?_
        have h1 := card_filter_box_apply_eq_le n i (n : ℤ)
        have h2 := card_filter_box_apply_eq_le n i (-(n : ℤ))
        omega
    _ = 2 * d * (2 * n + 1) ^ (d - 1) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]; ring

/-- A translate of `Λ(n)` by a vector of `Λ(k)` lies in `Λ(k + n)`. [folklore] -/
theorem image_add_box_subset {v : LatticeModels.Site d} {k n : ℕ} (hv : v ∈ LatticeModels.box d k) :
    (LatticeModels.box d n).image (· + v) ⊆ LatticeModels.box d (k + n) := by
  intro y hy
  rw [Finset.mem_image] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  rw [LatticeModels.mem_box] at hx hv ⊢
  intro i
  have h1 := hx i; have h2 := hv i
  simp only [Pi.add_apply, Nat.cast_add]
  omega

end ZdBox

end Percolation.Literature
