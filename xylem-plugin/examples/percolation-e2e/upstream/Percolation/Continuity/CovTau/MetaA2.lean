import Mathlib.Combinatorics.SetFamily.FourFunctions
import Percolation.Continuity.CovTau.MetaA2Defs
import Percolation.Util.Linter

/-!
# META-A2 — the generic two-source induction (avoided SET, arbitrary pure world functional) modulo the one-source bounds

The inequality "META-A2" in the finite-sum framework of `BHK2006.core` (functionals of `Continuity/CovTau/MetaA2Defs.lean`).

THEOREM (`CovTau.metaA2_of_star`). Fix weights `w ∈ [0,1]` (normalised), an owner `x`, observers `o,
v`, an avoided set `A`, and a pure world functional `F : Finset V → ℝ` with `F ≥ 0` and `F(U') = 0`
whenever `v ∉ U'`. If in every sub-world `U' ⊆ U` (★^F) `Y_F(N)·M_A(∅) ≤ M_A(N)·F(U')` for all `N ⊆
U'` (one-source bound), and (anti) `N ↦ Y_F(N)` is antitone, then for all source sets `N, N' ⊆ U`:
(META-A2) `E_A(N)·Y_F(N') ≤ M_A(N ∪ N')·X_F(N ∩ N')`. Instances: `A = {x}`, `F = B` is (A2); `A = S
∋ x`, `F = Cov(g(C_x), 1{v ↔ S})` is A2^H (`Continuity/CovTau/A2H.lean`). [cite:
VandenbergHaggstromKahn2005, Thm. 1.1 (pp. 3–5), Thm. 1.3 (p. 6)] [cite: KozmaNitzan2024, Conj. 1
(p. 3)]
-/

noncomputable section

namespace Percolation.Continuity.CovTau

open Percolation.Literature
open Percolation.Literature.BHK2006
open Percolation.Literature.DecisionTree (ind ind_of_mem ind_of_not_mem ind_nonneg)
open scoped Classical

variable {V : Type*} [Fintype V]

/-- **META-A2 modulo the one-source bounds**: if in every sub-world `U' ⊆ U` the one-source bound
(★^F) `Y_F(N)·M_A(∅) ≤ M_A(N)·F(U')` holds for all `N ⊆ U'` and `N ↦ Y_F(N)` is antitone, then
`E_A(N)·Y_F(N') ≤ M_A(N ∪ N')·X_F(N ∩ N')` for all source sets `N, N' ⊆ U` (proof sketched in the module docstring).
[cite: VandenbergHaggstromKahn2005, Thm. 1.1 (pp. 3–5), Thm. 1.3 (p. 6)] -/
theorem metaA2_of_star (w : Sym2 V → ℝ) (hw0 : ∀ e, 0 ≤ w e) (hw1 : ∀ e, w e ≤ 1)
    (hm : ∑ ω, weight w ω = 1) (x o v : V) (A : Set V) {F : Finset V → ℝ}
    (hF0 : ∀ U' : Finset V, 0 ≤ F U') (hFv : ∀ U' : Finset V, v ∉ U' → F U' = 0) (U : Finset V)
    (hstar : ∀ U' ⊆ U, ∀ N : Set V, N ⊆ ↑U' →
      Yw w U' x F N * Mav w U' A v ∅ ≤ Mav w U' A v N * F U')
    (hanti : ∀ U' ⊆ U, ∀ N N' : Set V, N ⊆ N' → N' ⊆ ↑U' → Yw w U' x F N' ≤ Yw w U' x F N) :
    ∀ N N' : Set V, N ⊆ ↑U → N' ⊆ ↑U →
      Eav w U A o v N * Yw w U x F N' ≤ Mav w U A v (N ∪ N') * Xw w U x A o v F (N ∩ N') := by
  induction U using Finset.strongInduction with
  | H U ih =>
  intro N N' hNU hN'U
  have hRHS : 0 ≤ Mav w U A v (N ∪ N') * Xw w U x A o v F (N ∩ N') :=
    mul_nonneg (Mav_nonneg hw0 hw1 U A v _) (Xw_nonneg hw0 hw1 U x A o v hF0 _)
  -- trivial cases
  by_cases hvN : v ∈ A ∪ N
  · rw [Eav_eq_zero_of_mem w U A o v hvN, zero_mul]; exact hRHS
  have hvA : v ∉ A := fun h => hvN (Or.inl h)
  have hvN0 : v ∉ N := fun h => hvN (Or.inr h)
  by_cases hxN' : x ∈ N'
  · rw [Yw_eq_zero_of_mem w U x F hxN', mul_zero]; exact hRHS
  by_cases hvU : v ∈ U
  swap
  · rw [Yw_eq_zero_of_not_mem w x hFv hvU, mul_zero]; exact hRHS
  -- `Z := N ∩ N'`
  set Z : Finset V := U.filter fun u => u ∈ N ∧ u ∈ N' with hZ
  have hZU : Z ⊆ U := Finset.filter_subset _ _
  have hmemZ : ∀ u, u ∈ Z ↔ u ∈ N ∧ u ∈ N' := fun u => by
    simp only [hZ, Finset.mem_filter, and_iff_right_iff_imp]
    exact fun h => hNU h.1
  have hxZ : x ∉ Z := fun h => hxN' ((hmemZ x).1 h).2
  have hvZ : v ∉ Z := fun h => hvN0 ((hmemZ v).1 h).1
  have hZN : (↑Z : Set V) ⊆ N := fun u hu => ((hmemZ u).1 hu).1
  have hZN' : (↑Z : Set V) ⊆ N' := fun u hu => ((hmemZ u).1 hu).2
  have hNN'Z : N ∩ N' = ↑Z := Set.ext fun u => by
    rw [Finset.mem_coe, hmemZ]; rfl
  rcases Z.eq_empty_or_nonempty with hZe | hZne
  · /- `N ∩ N' = ∅`: (★^F) for `N'` and BHK Thm 1.3 (`BHK2006.core` with `s = v`, `F = 1`, `G = 1{o ∈ C_v}` on the
    avoided sets `(A ∪ N') ∩ U`, `(A ∪ N) ∩ U`). -/
    have hNN' : N ∩ N' = ∅ := by rw [hNN'Z, hZe, Finset.coe_empty]
    rw [hNN', Xw_empty w hm]
    have hst := hstar U le_rfl N' hN'U
    have hcore := core w hw0 hw1 hm U v hvU ((A ∪ N') ∩ ↑U) ((A ∪ N) ∩ ↑U)
      Set.inter_subset_right Set.inter_subset_right (fun _ => (1 : ℝ)) (oInd o v)
      monotone_const (oInd_mono o v) (fun _ => zero_le_one) (oInd_nonneg o v)
    have hi : (A ∪ N') ∩ ↑U ∩ ((A ∪ N) ∩ ↑U) = (A ∪ ∅) ∩ ↑U := by
      ext u
      simp only [Set.mem_inter_iff, Set.mem_union, Set.union_empty, Finset.mem_coe]
      constructor
      · rintro ⟨⟨ha | hn', hu⟩, ha' | hn, -⟩
        · exact ⟨ha, hu⟩
        · exact ⟨ha, hu⟩
        · exact ⟨ha', hu⟩
        · exact absurd hNN' (Set.nonempty_iff_ne_empty.1 ⟨u, hn, hn'⟩)
      · rintro ⟨ha, hu⟩; exact ⟨⟨Or.inl ha, hu⟩, Or.inl ha, hu⟩
    have hu : (A ∪ N') ∩ ↑U ∪ (A ∪ N) ∩ ↑U = (A ∪ (N ∪ N')) ∩ ↑U := by
      ext u
      simp only [Set.mem_inter_iff, Set.mem_union, Finset.mem_coe]
      tauto
    simp only [one_mul, hi, hu] at hcore
    rw [← Mav_eq_inter w U A hvU, ← Eav_eq_inter w U A o hvU, ← Eav_eq_inter w U A o hvU,
      ← Mav_eq_inter w U A hvU] at hcore
    -- hcore : Mav N' * Eav N ≤ Eav ∅ * Mav (N ∪ N')
    have hE := Eav_nonneg hw0 hw1 U A o v N
    have hB := hF0 U
    have hM := Mav_nonneg hw0 hw1 U A v (N ∪ N')
    have hM0 := Mav_nonneg hw0 hw1 U A v (∅ : Set V)
    have key : Eav w U A o v N * Yw w U x F N' * Mav w U A v ∅ ≤
        Mav w U A v (N ∪ N') * (Eav w U A o v ∅ * F U) :=
      calc Eav w U A o v N * Yw w U x F N' * Mav w U A v ∅
          = Eav w U A o v N * (Yw w U x F N' * Mav w U A v ∅) := by ring
        _ ≤ Eav w U A o v N * (Mav w U A v N' * F U) := mul_le_mul_of_nonneg_left hst hE
        _ = (Mav w U A v N' * Eav w U A o v N) * F U := by ring
        _ ≤ (Eav w U A o v ∅ * Mav w U A v (N ∪ N')) * F U := mul_le_mul_of_nonneg_right hcore hB
        _ = _ := by ring
    rcases hM0.eq_or_lt with hM0e | hM0p
    · -- `μ(v ↮ A) = 0`: then `E_A(N) = 0`
      have hE0 : Eav w U A o v N = 0 := le_antisymm
        ((Eav_le_Mav hw0 hw1 U A o v N).trans
          ((Mav_antitone hw0 hw1 U A v (Set.empty_subset N)).trans hM0e.symm.le)) hE
      rw [hE0, zero_mul]
      exact mul_nonneg hM (mul_nonneg (qav_nonneg hw0 hw1 U A o v) hB)
    · unfold qav
      calc Eav w U A o v N * Yw w U x F N'
          = Eav w U A o v N * Yw w U x F N' * Mav w U A v ∅ / Mav w U A v ∅ := by
            field_simp
        _ ≤ Mav w U A v (N ∪ N') * (Eav w U A o v ∅ * F U) / Mav w U A v ∅ :=
            div_le_div_of_nonneg_right key hM0p.le
        _ = Mav w U A v (N ∪ N') * (Eav w U A o v ∅ / Mav w U A v ∅ * F U) := by
            field_simp
  · /- `Z ≠ ∅`: condition on the neighbour set `S` of `Z`, push forward to its product law, and apply the
    four functions theorem with the induction hypothesis on `U ∖ Z`. -/
    have hss : U \ Z ⊂ U := Finset.sdiff_ssubset hZU hZne
    have hU'U : U \ Z ⊆ U := Finset.sdiff_subset
    have hZNN' : (↑Z : Set V) ⊆ N ∪ N' := hZN.trans Set.subset_union_left
    -- star decompositions
    have eE := Eav_step hZU hvU hvZ (A := A) hZN w hm o
    have eY := Yw_step hZU hxZ hZN' w hm F
    have eM := Mav_step hZU hvU hvZ (A := A) hZNN' w hm
    have eX : Xw w U x A o v F (N ∩ N') = ∑ ω, weight w ω * Xw w (U \ Z) x A o v F (rS U Z ω) := by
      rw [hNN'Z, Xw_step hZU hxZ (subset_refl _) w hm A o v F]
      simp only [Set.sdiff_self, Set.empty_union]
    -- the four functionals on the lattice `Set V`
    set e : Set V → ℝ := fun η => Eav w (U \ Z) A o v (N \ ↑Z ∪ (η ∩ ↑(U \ Z))) with he
    set y : Set V → ℝ := fun η => Yw w (U \ Z) x F (N' \ ↑Z ∪ (η ∩ ↑(U \ Z))) with hy
    set m : Set V → ℝ := fun η => Mav w (U \ Z) A v ((N ∪ N') \ ↑Z ∪ (η ∩ ↑(U \ Z))) with hm'
    set χ : Set V → ℝ := fun η => Xw w (U \ Z) x A o v F (η ∩ ↑(U \ Z)) with hχ
    set wp : Set V → ℝ := weight (pZ w U Z) with hwp
    have hrSU : ∀ ω : Set (Sym2 V), rS U Z ω ∩ ↑(U \ Z) = rS U Z ω := fun ω =>
      Set.inter_eq_left.2 (rS_subset U Z ω)
    have hE' : Eav w U A o v N = ∑ η, wp η * e η := by
      rw [eE, ← sum_weight_rS hm U Z e]
      refine Finset.sum_congr rfl fun ω _ => ?_
      simp only [he, hrSU]
    have hY' : Yw w U x F N' = ∑ η, wp η * y η := by
      rw [eY, ← sum_weight_rS hm U Z y]
      refine Finset.sum_congr rfl fun ω _ => ?_
      simp only [hy, hrSU]
    have hM' : Mav w U A v (N ∪ N') = ∑ η, wp η * m η := by
      rw [eM, ← sum_weight_rS hm U Z m]
      refine Finset.sum_congr rfl fun ω _ => ?_
      simp only [hm', hrSU]
    have hX' : Xw w U x A o v F (N ∩ N') = ∑ η, wp η * χ η := by
      rw [eX, ← sum_weight_rS hm U Z χ]
      refine Finset.sum_congr rfl fun ω _ => ?_
      simp only [hχ, hrSU]
    -- nonnegativity
    have hp0 : ∀ u, 0 ≤ pZ w U Z u := fun u => (pZ_mem hw0 hw1 hm U Z u).1
    have hp1 : ∀ u, pZ w U Z u ≤ 1 := fun u => (pZ_mem hw0 hw1 hm U Z u).2
    have hwp0 : ∀ η, 0 ≤ wp η := fun η => weight_nonneg hp0 hp1 η
    have he0 : ∀ η, 0 ≤ e η := fun η => Eav_nonneg hw0 hw1 _ A o v _
    have hy0 : ∀ η, 0 ≤ y η := fun η => Yw_nonneg hw0 hw1 _ x hF0 _
    have hm0 : ∀ η, 0 ≤ m η := fun η => Mav_nonneg hw0 hw1 _ A v _
    have hχ0 : ∀ η, 0 ≤ χ η := fun η => Xw_nonneg hw0 hw1 _ x A o v hF0 _
    -- hypotheses restricted to `(U \ Z)`
    have hstar' : ∀ U'' ⊆ (U \ Z), ∀ N : Set V, N ⊆ ↑U'' →
        Yw w U'' x F N * Mav w U'' A v ∅ ≤ Mav w U'' A v N * F U'' :=
      fun U'' hU'' => hstar U'' (hU''.trans hU'U)
    have hanti' : ∀ U'' ⊆ (U \ Z), ∀ N N' : Set V, N ⊆ N' → N' ⊆ ↑U'' → Yw w U'' x F N' ≤ Yw w U'' x F N :=
      fun U'' hU'' => hanti U'' (hU''.trans hU'U)
    have IH := ih (U \ Z) hss hstar' hanti'
    have keyZ : ∀ u, u ∈ N → u ∈ N' → u ∈ (↑Z : Set V) := fun u h1 h2 => (hmemZ u).2 ⟨h1, h2⟩
    rw [hE', hY', hM', hX', mul_comm (∑ η, wp η * m η)]
    refine four_functions_theorem_univ (fun η => wp η * e η) (fun η => wp η * y η)
      (fun η => wp η * χ η) (fun η => wp η * m η)
      (fun η => mul_nonneg (hwp0 η) (he0 η)) (fun η => mul_nonneg (hwp0 η) (hy0 η))
      (fun η => mul_nonneg (hwp0 η) (hχ0 η)) (fun η => mul_nonneg (hwp0 η) (hm0 η)) fun a b => ?_
    -- the Ahlswede–Daykin hypothesis from the induction hypothesis at the pair `(P̃, P̃')`
    set S' : Set V := a ∩ ↑(U \ Z) with hS'
    set T' : Set V := b ∩ ↑(U \ Z) with hT'
    set P : Set V := S' ∪ (N \ ↑Z) \ T' with hP
    set P' : Set V := T' ∪ (N' \ ↑Z) \ S' with hP'
    have hPU : P ⊆ ↑(U \ Z) := by
      rintro u (hu | ⟨⟨huN, huZ⟩, -⟩)
      · exact hu.2
      · rw [Finset.coe_sdiff]; exact ⟨hNU huN, huZ⟩
    have hP'U : P' ⊆ ↑(U \ Z) := by
      rintro u (hu | ⟨⟨huN, huZ⟩, -⟩)
      · exact hu.2
      · rw [Finset.coe_sdiff]; exact ⟨hN'U huN, huZ⟩
    have hIH := IH P P' hPU hP'U
    have h1 : e a ≤ Eav w (U \ Z) A o v P :=
      Eav_antitone hw0 hw1 (U \ Z) A o v (show P ⊆ N \ ↑Z ∪ S' from by
        rintro u (hu | ⟨hu, -⟩); exacts [Or.inr hu, Or.inl hu])
    have h2 : y b ≤ Yw w (U \ Z) x F P' :=
      hanti (U \ Z) hU'U P' (N' \ ↑Z ∪ T') (by rintro u (hu | ⟨hu, -⟩); exacts [Or.inr hu, Or.inl hu])
        (by
          rintro u (⟨huN, huZ⟩ | hu)
          · rw [Finset.coe_sdiff]; exact ⟨hN'U huN, huZ⟩
          · exact hu.2)
    have hunion : P ∪ P' = (N ∪ N') \ ↑Z ∪ ((a ∪ b) ∩ ↑(U \ Z)) := by
      ext u
      constructor
      · rintro ((hS | ⟨hA, -⟩) | (hT | ⟨hA', -⟩))
        · exact Or.inr ⟨Or.inl hS.1, hS.2⟩
        · exact Or.inl ⟨Or.inl hA.1, hA.2⟩
        · exact Or.inr ⟨Or.inr hT.1, hT.2⟩
        · exact Or.inl ⟨Or.inr hA'.1, hA'.2⟩
      · rintro (⟨hN | hN', hZ'⟩ | ⟨ha | hb, hU⟩)
        · by_cases hT : u ∈ T'
          · exact Or.inr (Or.inl hT)
          · exact Or.inl (Or.inr ⟨⟨hN, hZ'⟩, hT⟩)
        · by_cases hS : u ∈ S'
          · exact Or.inl (Or.inl hS)
          · exact Or.inr (Or.inr ⟨⟨hN', hZ'⟩, hS⟩)
        · exact Or.inl (Or.inl ⟨ha, hU⟩)
        · exact Or.inr (Or.inl ⟨hb, hU⟩)
    have hinter : P ∩ P' = (a ∩ b) ∩ ↑(U \ Z) := by
      ext u
      constructor
      · rintro ⟨hS | ⟨⟨hN, hZ'⟩, hT⟩, hT' | ⟨⟨hN', -⟩, hS'⟩⟩
        · exact ⟨⟨hS.1, hT'.1⟩, hS.2⟩
        · exact absurd hS hS'
        · exact absurd hT' hT
        · exact absurd (keyZ u hN hN') hZ'
      · rintro ⟨⟨ha, hb⟩, hU⟩
        exact ⟨Or.inl ⟨ha, hU⟩, Or.inl ⟨hb, hU⟩⟩
    have h3 : e a * y b ≤ m (a ∪ b) * χ (a ∩ b) :=
      calc e a * y b ≤ Eav w (U \ Z) A o v P * Yw w (U \ Z) x F P' :=
            mul_le_mul h1 h2 (hy0 b) (Eav_nonneg hw0 hw1 _ A o v _)
        _ ≤ Mav w (U \ Z) A v (P ∪ P') * Xw w (U \ Z) x A o v F (P ∩ P') := hIH
        _ = m (a ∪ b) * χ (a ∩ b) := by rw [hunion, hinter]
    have hwab := weight_inter_mul_union (pZ w U Z) a b
    show wp a * e a * (wp b * y b) ≤ wp (a ∩ b) * χ (a ∩ b) * (wp (a ∪ b) * m (a ∪ b))
    calc wp a * e a * (wp b * y b) = (wp a * wp b) * (e a * y b) := by ring
      _ ≤ (wp (a ∩ b) * wp (a ∪ b)) * (m (a ∪ b) * χ (a ∩ b)) := by
          rw [hwp, hwab]
          exact mul_le_mul_of_nonneg_left h3 (mul_nonneg (hwp0 _) (hwp0 _))
      _ = _ := by ring

end Percolation.Continuity.CovTau
