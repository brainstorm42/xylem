import Percolation.Continuity.CovTau.A2Defs
import Percolation.Util.Linter

/-!
# The law of BHK's neighbour set `S` is a product law

Companion of `Continuity/CovTau/A2Defs.lean` / `Continuity/CovTau/A2Star.lean` (the two-source inequality (A2)
in the finite-sum framework of `BHK2006.core`).

For `Z ⊆ U`, BHK's random set `S = rS U Z ω` of vertices of `U ∖ Z` joined to `Z` by an open edge
([VandenbergHaggstromKahn2005, §1 p. 4]: "the law of `S` is a product measure") — here as a push-forward identity
on the lattice `Set V`:
* `CovTau.sum_weight_rS` — `Σ_ω weight_w(ω) Γ(S(ω)) = Σ_η weight_p(η) Γ(η)` for every `Γ : Set V → ℝ`, with
  `p = CovTau.pZ w U Z` (`p_u = CovTau.piZ w Z u = μ(u has an open edge to Z)` for `u ∈ U ∖ Z`, `0` elsewhere;
  `CovTau.pZ_mem`: `p ∈ [0,1]`), proved by induction on the vertex set through `CovTau.sum_weight_rST`
  (block Fubini at the star of one vertex, `BHK2006.blockFubini`) and `CovTau.sum_weight_update`.
This is the form in which the Ahlswede–Daykin four functions theorem is applied in the proof of (A2): the functional
`X` is not monotone in the source set, so the configuration-level shortcut of `BHK2006.core`
(`rS(a ∩ b) ⊆ rS a ∩ rS b` absorbed by antitonicity) is not available and one needs `S ∩ T` exactly.
[cite: VandenbergHaggstromKahn2005, §1 p. 4] [cite: KozmaNitzan2024, Conj. 1 (p. 3)]
-/

noncomputable section

namespace Percolation.Continuity.CovTau

open Percolation.Literature
open Percolation.Literature.BHK2006
open Percolation.Literature.DecisionTree (ind ind_of_mem ind_of_not_mem ind_nonneg)
open scoped Classical

variable {V : Type*} [Fintype V]

/-! ### The law of the neighbour set `S` is a product law -/

/-- The probability that `u` has an open edge to `Z`. [folklore] -/
def piZ (w : Sym2 V → ℝ) (Z : Finset V) (u : V) : ℝ :=
  ∑ ω, weight w ω * ind {ω : Set (Sym2 V) | ∃ z ∈ Z, s(u, z) ∈ ω} ω

/-- The parameters of the product law of `S = rS U Z ·` on `Set V`: `p_u = piZ w Z u` for `u ∈ U ∖ Z`, else `0`.
[cite: VandenbergHaggstromKahn2005, §1 p. 4 ("the law of `S` is a product measure")] -/
def pZ (w : Sym2 V → ℝ) (U Z : Finset V) (u : V) : ℝ := if u ∈ U \ Z then piZ w Z u else 0

/-- The partial neighbour set `S_T = {n ∈ T | n has an open edge to Z}` (so `rS U Z = S_{U∖Z}`). [folklore] -/
def rST (T Z : Finset V) (ω : Set (Sym2 V)) : Set V := {n | n ∈ T ∧ ∃ z ∈ Z, s(n, z) ∈ ω}

/-- Its product parameters: `piZ` on `T`, `0` elsewhere. [folklore] -/
def pT (w : Sym2 V → ℝ) (T Z : Finset V) (u : V) : ℝ := if u ∈ T then piZ w Z u else 0

omit [Fintype V] in
/-- `rS U Z = S_{U ∖ Z}`. [folklore] -/
theorem rS_eq_rST (U Z : Finset V) (ω : Set (Sym2 V)) : rS U Z ω = rST (U \ Z) Z ω := rfl

/-- `0 ≤ piZ ≤ 1`. [folklore] -/
theorem piZ_mem {w : Sym2 V → ℝ} (hw0 : ∀ e, 0 ≤ w e) (hw1 : ∀ e, w e ≤ 1) (hm : ∑ ω, weight w ω = 1)
    (Z : Finset V) (u : V) : 0 ≤ piZ w Z u ∧ piZ w Z u ≤ 1 := by
  constructor
  · exact Finset.sum_nonneg fun ω _ => mul_nonneg (weight_nonneg hw0 hw1 ω) (ind_nonneg _ _)
  · calc piZ w Z u ≤ ∑ ω, weight w ω * 1 := Finset.sum_le_sum fun ω _ =>
          mul_le_mul_of_nonneg_left (ind_le_one _ _) (weight_nonneg hw0 hw1 ω)
      _ = 1 := by rw [← Finset.sum_mul, hm, one_mul]

/-- The weight with all parameters `0` is the point mass at `∅`. [folklore] -/
theorem weight_zero_param (η : Set V) : weight (fun _ : V => (0 : ℝ)) η = if η = ∅ then 1 else 0 := by
  unfold weight
  split_ifs with h
  · subst h; simp
  · obtain ⟨u, hu⟩ := Set.nonempty_iff_ne_empty.2 h
    exact Finset.prod_eq_zero (Finset.mem_univ u) (by simp [hu])

/-- Toggling the membership of `u`. [folklore] -/
def toggle (u : V) (η : Set V) : Set V := if u ∈ η then η \ {u} else insert u η

omit [Fintype V] in
/-- `toggle u` is an involution. [folklore] -/
theorem toggle_toggle (u : V) (η : Set V) : toggle u (toggle u η) = η := by
  unfold toggle
  by_cases hu : u ∈ η
  · rw [if_pos hu, if_neg (fun h : u ∈ η \ {u} => h.2 rfl)]
    ext v
    simp only [Set.mem_insert_iff, Set.mem_sdiff, Set.mem_singleton_iff]
    constructor
    · rintro (rfl | ⟨h, _⟩); exacts [hu, h]
    · intro hv; by_cases hvu : v = u; exacts [Or.inl hvu, Or.inr ⟨hv, hvu⟩]
  · rw [if_neg hu, if_pos (Set.mem_insert u η)]
    ext v
    simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨rfl | h, hne⟩; exacts [absurd rfl hne, h]
    · intro hv; exact ⟨Or.inr hv, fun h => hu (h ▸ hv)⟩

omit [Fintype V] in
/-- For `u ∉ η`, `toggle u η = insert u η`. [folklore] -/
theorem toggle_of_not_mem {u : V} {η : Set V} (hu : u ∉ η) : toggle u η = insert u η := if_neg hu

/-- The product weight factors through the coordinate `u`. [folklore] -/
theorem weight_eq_mul_erase (p : V → ℝ) (u : V) (η : Set V) :
    weight p η = (if u ∈ η then p u else 1 - p u) *
      ∏ v ∈ Finset.univ.erase u, (if v ∈ η then p v else 1 - p v) := by
  unfold weight
  rw [← Finset.mul_prod_erase Finset.univ (fun e => if e ∈ η then p e else 1 - p e) (Finset.mem_univ u)]

/-- **Updating one parameter**: if `p u = 0` then
`Σ_η weight_{p[u ↦ c]}(η) Γ(η) = c·Σ_η weight_p(η) Γ(η ∪ {u}) + (1 − c)·Σ_η weight_p(η) Γ(η)`. [folklore] -/
theorem sum_weight_update (p : V → ℝ) (u : V) (hu : p u = 0) (c : ℝ) (Γ : Set V → ℝ) :
    ∑ η, weight (Function.update p u c) η * Γ η =
      c * ∑ η, weight p η * Γ (insert u η) + (1 - c) * ∑ η, weight p η * Γ η := by
  set R : Set V → ℝ := fun η => ∏ v ∈ Finset.univ.erase u, (if v ∈ η then p v else 1 - p v) with hR
  have hRq : ∀ η, ∏ v ∈ Finset.univ.erase u, (if v ∈ η then Function.update p u c v else
      1 - Function.update p u c v) = R η := by
    intro η
    refine Finset.prod_congr rfl fun v hv => ?_
    have hvu : v ≠ u := Finset.ne_of_mem_erase hv
    simp [Function.update_of_ne hvu]
  have hq : ∀ η, weight (Function.update p u c) η = (if u ∈ η then c else 1 - c) * R η := by
    intro η
    rw [weight_eq_mul_erase _ u, hRq]
    simp [Function.update_self]
  have hp : ∀ η, weight p η = (if u ∈ η then 0 else 1) * R η := by
    intro η
    rw [weight_eq_mul_erase _ u, hu]; simp [hR]
  have hRins : ∀ η, R (insert u η) = R η := fun η => by
    simp only [hR]
    refine Finset.prod_congr rfl fun v hv => ?_
    have hvu : v ≠ u := Finset.ne_of_mem_erase hv
    simp [Set.mem_insert_iff, hvu]
  -- the `u ∈ η` part of the left sum, re-indexed by `toggle u`
  have hperm : ∑ η, (if u ∈ η then c * R η * Γ η else 0) =
      ∑ η, (if u ∈ η then 0 else c * R η * Γ (insert u η)) := by
    have hinv : Function.Involutive (toggle (V := V) u) := toggle_toggle u
    rw [← Equiv.sum_comp hinv.toPerm]
    refine Finset.sum_congr rfl fun η _ => ?_
    show (if u ∈ toggle u η then c * R (toggle u η) * Γ (toggle u η) else 0) = _
    by_cases hη : u ∈ η
    · have : u ∉ toggle u η := by rw [toggle, if_pos hη]; exact fun h => h.2 rfl
      rw [if_neg this, if_pos hη]
    · rw [toggle_of_not_mem hη, if_pos (Set.mem_insert u η), if_neg hη, hRins]
  calc ∑ η, weight (Function.update p u c) η * Γ η
      = ∑ η, ((if u ∈ η then c * R η * Γ η else 0) + (if u ∈ η then 0 else (1 - c) * R η * Γ η)) := by
        refine Finset.sum_congr rfl fun η _ => ?_
        rw [hq]; split_ifs <;> ring
    _ = ∑ η, (if u ∈ η then 0 else c * R η * Γ (insert u η)) +
        ∑ η, (if u ∈ η then 0 else (1 - c) * R η * Γ η) := by rw [Finset.sum_add_distrib, hperm]
    _ = c * ∑ η, weight p η * Γ (insert u η) + (1 - c) * ∑ η, weight p η * Γ η := by
        rw [Finset.mul_sum, Finset.mul_sum]
        congr 1 <;> refine Finset.sum_congr rfl fun η _ => ?_ <;> rw [hp] <;> split_ifs <;> ring

section Push

variable {w : Sym2 V → ℝ} (hm : ∑ ω, weight w ω = 1)
include hm

/-- **The law of `S_T` is the product law `pT`** (induction on `T ⊆ Zᶜ`): for every `Γ : Set V → ℝ`,
`Σ_ω weight_w(ω) Γ(S_T(ω)) = Σ_η weight_{pT}(η) Γ(η)`.
[cite: VandenbergHaggstromKahn2005, §1 p. 4 ("the law of `S` is a product measure")] -/
theorem sum_weight_rST (Z : Finset V) :
    ∀ T : Finset V, Disjoint T Z → ∀ Γ : Set V → ℝ,
      ∑ ω, weight w ω * Γ (rST T Z ω) = ∑ η : Set V, weight (pT w T Z) η * Γ η := by
  intro T
  induction T using Finset.induction_on with
  | empty =>
    intro _ Γ
    have h0 : ∀ ω : Set (Sym2 V), rST (∅ : Finset V) Z ω = ∅ := fun ω =>
      Set.eq_empty_of_forall_notMem fun n hn => Finset.notMem_empty n hn.1
    have hp : pT w (∅ : Finset V) Z = fun _ => (0 : ℝ) := funext fun u => if_neg (Finset.notMem_empty u)
    simp only [h0, hp, weight_zero_param, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
    rw [← Finset.sum_mul, hm, one_mul]
  | @insert u T huT ih =>
    intro hdisj Γ
    have huZ : u ∉ Z := Finset.disjoint_left.1 hdisj (Finset.mem_insert_self u T)
    have hTZ : Disjoint T Z := Finset.disjoint_of_subset_left (Finset.subset_insert u T) hdisj
    -- the star edges at `u`
    set A : Set (Sym2 V) := {e | ∃ z ∈ Z, e = s(u, z)} with hA
    set B : Set (Set (Sym2 V)) := {ω | ∃ z ∈ Z, s(u, z) ∈ ω} with hB
    have hmemA : ∀ {n z : V}, n ∈ T → z ∈ Z → s(n, z) ∉ A := by
      intro n z hn hz ⟨z', hz', he⟩
      rcases Sym2.eq_iff.1 he with ⟨rfl, -⟩ | ⟨rfl, rfl⟩
      · exact huT hn
      · exact Finset.disjoint_left.1 hTZ hn hz'
    have hT_diff : ∀ ω : Set (Sym2 V), rST T Z (ω \ A) = rST T Z ω := by
      intro ω; ext n
      simp only [rST, Set.mem_setOf_eq, Set.mem_sdiff]
      constructor
      · rintro ⟨hn, z, hz, hω, -⟩; exact ⟨hn, z, hz, hω⟩
      · rintro ⟨hn, z, hz, hω⟩; exact ⟨hn, z, hz, hω, hmemA hn hz⟩
    have hB_inter : ∀ ω : Set (Sym2 V), (ω ∩ A ∈ B ↔ ω ∈ B) := by
      intro ω
      simp only [hB, Set.mem_setOf_eq, Set.mem_inter_iff]
      constructor
      · rintro ⟨z, hz, hω, -⟩; exact ⟨z, hz, hω⟩
      · rintro ⟨z, hz, hω⟩; exact ⟨z, hz, hω, z, hz, rfl⟩
    have hsplit : ∀ ω : Set (Sym2 V), rST (insert u T) Z ω = rST T Z ω ∪ (if ω ∈ B then {u} else ∅) := by
      intro ω; ext n
      simp only [rST, Finset.mem_insert, Set.mem_setOf_eq, Set.mem_union]
      constructor
      · rintro ⟨rfl | hn, z, hz, hω⟩
        · right; rw [if_pos (show ω ∈ B from ⟨z, hz, hω⟩)]; exact Set.mem_singleton _
        · exact Or.inl ⟨hn, z, hz, hω⟩
      · rintro (⟨hn, z, hz, hω⟩ | h)
        · exact ⟨Or.inr hn, z, hz, hω⟩
        · by_cases hω : ω ∈ B
          · rw [if_pos hω, Set.mem_singleton_iff] at h; subst h
            obtain ⟨z, hz, hω⟩ := hω; exact ⟨Or.inl rfl, z, hz, hω⟩
          · rw [if_neg hω] at h; exact h.elim
    set Φ : Set (Sym2 V) → Set (Sym2 V) → ℝ := fun ζ η =>
      Γ (rST T Z η ∪ (if ζ ∈ B then {u} else ∅)) with hΦ
    have h1 : ∀ ω, Γ (rST (insert u T) Z ω) = Φ (ω ∩ A) (ω \ A) := by
      intro ω; simp only [hΦ, hsplit, hT_diff, hB_inter]
    have h2 : ∀ ω ω', Φ (ω ∩ A) (ω' \ A) = Γ (rST T Z ω' ∪ (if ω ∈ B then {u} else ∅)) := by
      intro ω ω'; simp only [hΦ, hT_diff, hB_inter]
    -- block Fubini at the star of `u`, then the induction hypothesis inside
    have hstep : ∑ ω, weight w ω * Γ (rST (insert u T) Z ω) =
        ∑ ω, weight w ω * ∑ η : Set V, weight (pT w T Z) η * Γ (η ∪ (if ω ∈ B then {u} else ∅)) := by
      calc ∑ ω, weight w ω * Γ (rST (insert u T) Z ω)
          = (∑ ω, weight w ω) * ∑ ω, weight w ω * Φ (ω ∩ A) (ω \ A) := by rw [hm, one_mul]; simp_rw [h1]
        _ = ∑ ω, weight w ω * ∑ ω', weight w ω' * Φ (ω ∩ A) (ω' \ A) := blockFubini w A Φ
        _ = _ := by
            refine Finset.sum_congr rfl fun ω _ => ?_
            simp_rw [h2]
            rw [ih hTZ (fun η => Γ (η ∪ (if ω ∈ B then {u} else ∅)))]
    -- the outer sum only sees the bit `1_B(ω)`
    have hbit : ∀ ω : Set (Sym2 V),
        (∑ η : Set V, weight (pT w T Z) η * Γ (η ∪ (if ω ∈ B then {u} else ∅))) =
        ind B ω * (∑ η : Set V, weight (pT w T Z) η * Γ (insert u η)) +
          (1 - ind B ω) * ∑ η : Set V, weight (pT w T Z) η * Γ η := by
      intro ω
      by_cases hω : ω ∈ B
      · rw [if_pos hω, ind_of_mem hω]
        simp only [Set.union_singleton, one_mul, sub_self, zero_mul, add_zero]
      · rw [if_neg hω, ind_of_not_mem hω]
        simp only [Set.union_empty, zero_mul, sub_zero, one_mul, zero_add]
    have hπ : ∑ ω, weight w ω * ind B ω = piZ w Z u := rfl
    have hπ' : ∑ ω, weight w ω * (1 - ind B ω) = 1 - piZ w Z u := by
      simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hm, hπ]
    rw [hstep]
    simp only [hbit, mul_add, Finset.sum_add_distrib]
    rw [show ∑ ω, weight w ω * (ind B ω * ∑ η : Set V, weight (pT w T Z) η * Γ (insert u η)) =
        (∑ ω, weight w ω * ind B ω) * ∑ η : Set V, weight (pT w T Z) η * Γ (insert u η) by
          rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun ω _ => by ring,
      show ∑ ω, weight w ω * ((1 - ind B ω) * ∑ η : Set V, weight (pT w T Z) η * Γ η) =
        (∑ ω, weight w ω * (1 - ind B ω)) * ∑ η : Set V, weight (pT w T Z) η * Γ η by
          rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun ω _ => by ring,
      hπ, hπ']
    -- the right-hand side: `pT (insert u T) = (pT T)[u ↦ piZ u]`
    have hupd : pT w (insert u T) Z = Function.update (pT w T Z) u (piZ w Z u) := by
      funext v
      by_cases hvu : v = u
      · subst hvu; simp [pT]
      · simp [pT, Finset.mem_insert, hvu]
    have hu0 : pT w T Z u = 0 := if_neg huT
    rw [hupd, sum_weight_update _ u hu0]

/-- **The law of the neighbour set `S = rS U Z ·` is the product law `pZ w U Z` on `Set V`**: for every
`Γ : Set V → ℝ`, `Σ_ω weight_w(ω) Γ(S(ω)) = Σ_η weight_{pZ}(η) Γ(η)`.
[cite: VandenbergHaggstromKahn2005, §1 p. 4 ("the law of `S` is a product measure")] -/
theorem sum_weight_rS (U Z : Finset V) (Γ : Set V → ℝ) :
    ∑ ω, weight w ω * Γ (rS U Z ω) = ∑ η : Set V, weight (pZ w U Z) η * Γ η := by
  have h := sum_weight_rST hm Z (U \ Z) Finset.sdiff_disjoint Γ
  have hp : pT w (U \ Z) Z = pZ w U Z := rfl
  simpa only [rS_eq_rST, hp] using h

omit hm in
/-- The parameters `pZ` lie in `[0, 1]`. [folklore] -/
theorem pZ_mem (hw0 : ∀ e, 0 ≤ w e) (hw1 : ∀ e, w e ≤ 1) (hm : ∑ ω, weight w ω = 1) (U Z : Finset V) (u : V) :
    0 ≤ pZ w U Z u ∧ pZ w U Z u ≤ 1 := by
  unfold pZ
  split_ifs
  · exact piZ_mem hw0 hw1 hm Z u
  · exact ⟨le_refl _, zero_le_one⟩

end Push

end Percolation.Continuity.CovTau
