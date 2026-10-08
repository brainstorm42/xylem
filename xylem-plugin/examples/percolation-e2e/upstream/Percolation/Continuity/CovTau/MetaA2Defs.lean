import Percolation.Continuity.CovTau.A2EdgeDefs
import Percolation.Util.Linter

/-!
# The functionals of the GENERIC two-source inequality (META-A2) — avoided SET and an arbitrary pure world functional

* an avoided SET `A` in the observer functionals: `E_A(N) = μ(o ↔ v, v ↮ A ∪ N)`, `M_A(N) = μ(v ↮ A ∪ N)`,
  `q_A = E_A(∅)/M_A(∅) = μ(o ↔ v | v ↮ A)`;
* an ARBITRARY nonnegative "pure world functional" `F`: a number `F(U')` attached to every vertex set `U'`
  (the world `G[U']`), entering through `Y_F(N) = E[F(U ∖ C_N); x ∉ C_N]` and `X_F(N) = E[q_A(U ∖ C_N)·F(U ∖ C_N); x ∉ C_N]`.
THIS FILE sets up these functionals in the finite-sum framework of `BHK2006.core` (percolation restricted to
`U : Finset V` through `ω ∩ edgesIn U`, product weight `BHK2006.weight w`) and records their elementary properties and
star decompositions:
* `CovTau.Eav`, `CovTau.Mav`, `CovTau.qav`, `CovTau.Yw`, `CovTau.Xw` (definitions above);
* nonnegativity, `Eav ≤ Mav`, antitonicity in the source set, the vanishing cases, `Yw ∅ = F U`, `Xw ∅ = q_A·F U`;
* `CovTau.rD_eq_of_agree` (avoidance events only see the part of the avoided set inside `U`) and the star
  decompositions `CovTau.Eav_step`, `CovTau.Mav_step`, `CovTau.Yw_step`, `CovTau.Xw_step` (BHK's identity (6));
The induction (`CovTau.metaA2_of_star`) and the antitonicity of `Y_F` are in the companion files
`Continuity/CovTau/MetaA2.lean`, `Continuity/CovTau/MetaA2Anti.lean`; the instance A2^H (`F = Cov(g(C_x), 1{v ↔ S})`) in `Continuity/CovTau/A2H.lean`.
[cite: VandenbergHaggstromKahn2005, Thm. 1.1 (pp. 3–5), §1 p. 4 identity (6)] [cite: KozmaNitzan2024, Conj. 1 (p. 3)]
-/

noncomputable section

namespace Percolation.Continuity.CovTau

open Percolation.Literature
open Percolation.Literature.BHK2006
open Percolation.Literature.DecisionTree (ind ind_of_mem ind_of_not_mem ind_nonneg)
open scoped Classical

variable {V : Type*}

/-! ### Avoidance events only see the avoided vertices inside `U` -/

/-- In `G[U]` a vertex `v ∈ U` can only reach vertices of `U`; hence two avoided sets that agree on `U` define the
same avoidance event `{v ↮ ·}`. [cite: VandenbergHaggstromKahn2005, §1 p. 3 (definition of `R_X`)] -/
theorem rD_eq_of_agree (U : Finset V) {v : V} (hv : v ∈ U) {X Y : Set V}
    (h : ∀ a ∈ U, a ∈ X ↔ a ∈ Y) : rD U v X = rD U v Y := by
  ext ω
  simp only [rD, Set.mem_setOf_eq]
  constructor
  · intro hX a haY hr
    have haU : a ∈ U := by
      by_cases hva : v = a
      · exact hva ▸ hv
      · exact SandwichBHK.mem_of_reachable hr hva
    exact hX a ((h a haU).2 haY) hr
  · intro hY a haX hr
    have haU : a ∈ U := by
      by_cases hva : v = a
      · exact hva ▸ hv
      · exact SandwichBHK.mem_of_reachable hr hva
    exact hY a ((h a haU).1 haX) hr

/-- In particular `{v ↮ X} = {v ↮ X ∩ U}` in `G[U]` for `v ∈ U`. [cite: VandenbergHaggstromKahn2005, §1 p. 3] -/
theorem rD_inter_coe (U : Finset V) {v : V} (hv : v ∈ U) (X : Set V) : rD U v (X ∩ ↑U) = rD U v X :=
  rD_eq_of_agree U hv fun _ haU => ⟨fun h => h.1, fun h => ⟨h, haU⟩⟩

variable [Fintype V]

/-! ### The functionals -/

/-- `E_A(N) = μ_{G[U]}(o ↔ v, v ↮ A ∪ N)` — the observer functional with an avoided SET `A`.
[cite: VandenbergHaggstromKahn2005, §1 p. 3] -/
def Eav (w : Sym2 V → ℝ) (U : Finset V) (A : Set V) (o v : V) (N : Set V) : ℝ :=
  ∑ ω, weight w ω * (oInd o v (rC U v ω) * ind (rD U v (A ∪ N)) ω)

/-- `M_A(N) = μ_{G[U]}(v ↮ A ∪ N)`. [cite: VandenbergHaggstromKahn2005, §1 p. 3] -/
def Mav (w : Sym2 V → ℝ) (U : Finset V) (A : Set V) (v : V) (N : Set V) : ℝ :=
  ∑ ω, weight w ω * ind (rD U v (A ∪ N)) ω

/-- `q_A = μ_{G[U]}(o ↔ v | v ↮ A) = E_A(∅)/M_A(∅)` (`0` if `M_A(∅) = 0`). [folklore] -/
def qav (w : Sym2 V → ℝ) (U : Finset V) (A : Set V) (o v : V) : ℝ := Eav w U A o v ∅ / Mav w U A v ∅

/-- `Y_F(N) = E[ F(U ∖ C_N) ; x ∉ C_N ]` for a pure world functional `F : Finset V → ℝ`
(with the owner indicator). [cite: VandenbergHaggstromKahn2005, §1 p. 4] -/
def Yw (w : Sym2 V → ℝ) (U : Finset V) (x : V) (F : Finset V → ℝ) (N : Set V) : ℝ :=
  ∑ ω, weight w ω * (F (rest U N ω) * ind (rD U x N) ω)

/-- `X_F(N) = E[ q_A(U ∖ C_N)·F(U ∖ C_N) ; x ∉ C_N ]`.
[cite: VandenbergHaggstromKahn2005, §1 p. 4] -/
def Xw (w : Sym2 V → ℝ) (U : Finset V) (x : V) (A : Set V) (o v : V) (F : Finset V → ℝ) (N : Set V) : ℝ :=
  ∑ ω, weight w ω * (qav w (rest U N ω) A o v * F (rest U N ω) * ind (rD U x N) ω)

/-! ### Elementary properties -/

section Props

variable {w : Sym2 V → ℝ} (hw0 : ∀ e, 0 ≤ w e) (hw1 : ∀ e, w e ≤ 1)
include hw0 hw1

/-- `E_A(N) ≥ 0`. [folklore] -/
theorem Eav_nonneg (U : Finset V) (A : Set V) (o v : V) (N : Set V) : 0 ≤ Eav w U A o v N :=
  sum_ind_nonneg hw0 hw1 (fun _ => oInd_nonneg _ _ _) _

/-- `M_A(N) ≥ 0`. [folklore] -/
theorem Mav_nonneg (U : Finset V) (A : Set V) (v : V) (N : Set V) : 0 ≤ Mav w U A v N :=
  Finset.sum_nonneg fun ω _ => mul_nonneg (weight_nonneg hw0 hw1 ω) (ind_nonneg _ _)

/-- `E_A(N) ≤ M_A(N)`. [folklore] -/
theorem Eav_le_Mav (U : Finset V) (A : Set V) (o v : V) (N : Set V) : Eav w U A o v N ≤ Mav w U A v N :=
  Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left
    (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (oInd_le_one o v (rC U v ω)) (ind_nonneg (rD U v (A ∪ N)) ω))
    (weight_nonneg hw0 hw1 ω)

/-- `E_A` is antitone in the source set. [cite: VandenbergHaggstromKahn2005, §1 p. 3] -/
theorem Eav_antitone (U : Finset V) (A : Set V) (o v : V) {N N' : Set V} (h : N ⊆ N') :
    Eav w U A o v N' ≤ Eav w U A o v N :=
  sum_ind_mono hw0 hw1 (fun _ => oInd_nonneg _ _ _) (rD_antitone (Set.union_subset_union_right A h))

/-- `M_A` is antitone in the source set. [cite: VandenbergHaggstromKahn2005, §1 p. 3] -/
theorem Mav_antitone (U : Finset V) (A : Set V) (v : V) {N N' : Set V} (h : N ⊆ N') :
    Mav w U A v N' ≤ Mav w U A v N := by
  have := sum_ind_mono hw0 hw1 (h := fun _ => (1 : ℝ)) (fun _ => zero_le_one)
    (rD_antitone (U := U) (s := v) (Set.union_subset_union_right A h)) (w := w)
  simpa only [Mav, one_mul] using this

/-- `q_A ≥ 0`. [folklore] -/
theorem qav_nonneg (U : Finset V) (A : Set V) (o v : V) : 0 ≤ qav w U A o v :=
  div_nonneg (Eav_nonneg hw0 hw1 U A o v ∅) (Mav_nonneg hw0 hw1 U A v ∅)

/-- `Y_F(N) ≥ 0` for a nonnegative world functional. [folklore] -/
theorem Yw_nonneg (U : Finset V) (x : V) {F : Finset V → ℝ} (hF0 : ∀ U', 0 ≤ F U') (N : Set V) :
    0 ≤ Yw w U x F N :=
  sum_ind_nonneg hw0 hw1 (fun _ => hF0 _) _

/-- `X_F(N) ≥ 0` for a nonnegative world functional. [folklore] -/
theorem Xw_nonneg (U : Finset V) (x : V) (A : Set V) (o v : V) {F : Finset V → ℝ} (hF0 : ∀ U', 0 ≤ F U')
    (N : Set V) : 0 ≤ Xw w U x A o v F N :=
  sum_ind_nonneg hw0 hw1 (fun _ => mul_nonneg (qav_nonneg hw0 hw1 _ A o v) (hF0 _)) _

end Props

/-! ### Vanishing cases and the empty source set -/

/-- `E_A(N) = 0` when `v ∈ A ∪ N` (`v ↮ v` is impossible). [folklore] -/
theorem Eav_eq_zero_of_mem (w : Sym2 V → ℝ) (U : Finset V) (A : Set V) (o v : V) {N : Set V}
    (hv : v ∈ A ∪ N) : Eav w U A o v N = 0 :=
  Finset.sum_eq_zero fun ω _ => by
    rw [rD_eq_empty hv, ind_of_not_mem (Set.notMem_empty ω)]; ring

/-- `Y_F(N) = 0` when `x ∈ N` (`x ∈ C_N` always). [folklore] -/
theorem Yw_eq_zero_of_mem (w : Sym2 V → ℝ) (U : Finset V) (x : V) (F : Finset V → ℝ) {N : Set V}
    (hx : x ∈ N) : Yw w U x F N = 0 :=
  Finset.sum_eq_zero fun ω _ => by
    rw [rD_eq_empty hx, ind_of_not_mem (Set.notMem_empty ω)]; ring

/-- `Y_F(N) = 0` in `G[U]` when the functional vanishes on every world not containing `v` and `v ∉ U`. [folklore] -/
theorem Yw_eq_zero_of_not_mem (w : Sym2 V → ℝ) {U : Finset V} (x : V) {v : V} {F : Finset V → ℝ}
    (hFv : ∀ U' : Finset V, v ∉ U' → F U' = 0) (hv : v ∉ U) (N : Set V) : Yw w U x F N = 0 :=
  Finset.sum_eq_zero fun ω _ => by
    rw [hFv _ (fun h' => hv (rest_subset U N ω h'))]; ring

/-- `X_F(∅) = q_A·F(U)` (the cluster of the empty source set is empty). [folklore] -/
theorem Xw_empty (w : Sym2 V → ℝ) (hm : ∑ ω, weight w ω = 1) (U : Finset V) (x : V) (A : Set V) (o v : V)
    (F : Finset V → ℝ) : Xw w U x A o v F ∅ = qav w U A o v * F U := by
  unfold Xw
  have h : ∀ ω : Set (Sym2 V), ind (rD U x (∅ : Set V)) ω = 1 := fun ω => ind_of_mem fun _ h => h.elim
  simp only [rest_empty, h, mul_one]
  rw [← Finset.sum_mul, hm, one_mul]

/-! ### Star decompositions (BHK's (6)) -/

/-- Star decomposition of `Y_F`: `Y_U(N) = Σ_ω weight(ω) · Y_{U∖Z}((N ∖ Z) ∪ S(ω))` for `Z ⊆ N`, `x ∉ Z`.
[cite: VandenbergHaggstromKahn2005, §1 p. 4, identity (6)] -/
theorem Yw_step {U Z : Finset V} (hZU : Z ⊆ U) {x : V} (hx : x ∉ Z) {N : Set V} (hZN : (↑Z : Set V) ⊆ N)
    (w : Sym2 V → ℝ) (hm : ∑ ω, weight w ω = 1) (F : Finset V → ℝ) :
    Yw w U x F N = ∑ ω, weight w ω * Yw w (U \ Z) x F ((N \ ↑Z) ∪ rS U Z ω) :=
  setStep_sum hZU hx hZN w hm F

/-- Star decomposition of `X_F`: `X_U(N) = Σ_ω weight(ω) · X_{U∖Z}((N ∖ Z) ∪ S(ω))` for `Z ⊆ N`, `x ∉ Z`.
[cite: VandenbergHaggstromKahn2005, §1 p. 4, identity (6)] -/
theorem Xw_step {U Z : Finset V} (hZU : Z ⊆ U) {x : V} (hx : x ∉ Z) {N : Set V} (hZN : (↑Z : Set V) ⊆ N)
    (w : Sym2 V → ℝ) (hm : ∑ ω, weight w ω = 1) (A : Set V) (o v : V) (F : Finset V → ℝ) :
    Xw w U x A o v F N = ∑ ω, weight w ω * Xw w (U \ Z) x A o v F ((N \ ↑Z) ∪ rS U Z ω) :=
  setStep_sum hZU hx hZN w hm fun U' => qav w U' A o v * F U'

omit [Fintype V] in
/-- The avoided sets `((A ∪ N) ∖ Z) ∪ R` and `A ∪ ((N ∖ Z) ∪ R)` agree on `U ∖ Z`. [folklore] -/
theorem union_diff_agree (U Z : Finset V) (A N R : Set V) :
    ∀ a ∈ U \ Z, a ∈ (A ∪ N) \ ↑Z ∪ R ↔ a ∈ A ∪ ((N \ ↑Z) ∪ R) := by
  intro a ha
  have haZ : a ∉ Z := (Finset.mem_sdiff.1 ha).2
  simp only [Set.mem_union, Set.mem_sdiff, Finset.mem_coe]
  tauto

/-- Star decomposition of `E_A`: `E_U(N) = Σ_ω weight(ω) · E_{U∖Z}((N ∖ Z) ∪ S(ω))` for `Z ⊆ N`, `v ∈ U ∖ Z`
(`BHK2006.step_sum`; the members of `A ∩ Z` are invisible in `G[U ∖ Z]`).
[cite: VandenbergHaggstromKahn2005, §1 p. 4, identity (6)] -/
theorem Eav_step {U Z : Finset V} (hZU : Z ⊆ U) {v : V} (hvU : v ∈ U) (hv : v ∉ Z) {A N : Set V}
    (hZN : (↑Z : Set V) ⊆ N) (w : Sym2 V → ℝ) (hm : ∑ ω, weight w ω = 1) (o : V) :
    Eav w U A o v N = ∑ ω, weight w ω * Eav w (U \ Z) A o v ((N \ ↑Z) ∪ rS U Z ω) := by
  have hZW : (↑Z : Set V) ⊆ A ∪ N := hZN.trans Set.subset_union_right
  have hvUZ : v ∈ U \ Z := Finset.mem_sdiff.2 ⟨hvU, hv⟩
  unfold Eav
  rw [step_sum hZU hv hZW w hm (oInd o v)]
  refine Finset.sum_congr rfl fun ω _ => ?_
  simp only [blockE, rD_eq_of_agree (U \ Z) hvUZ (union_diff_agree U Z A N (rS U Z ω))]

/-- Star decomposition of `M_A`: `M_U(N) = Σ_ω weight(ω) · M_{U∖Z}((N ∖ Z) ∪ S(ω))` for `Z ⊆ N`, `v ∈ U ∖ Z`
(`BHK2006.step_sum` with `H = 1`). [cite: VandenbergHaggstromKahn2005, §1 p. 4, identity (6)] -/
theorem Mav_step {U Z : Finset V} (hZU : Z ⊆ U) {v : V} (hvU : v ∈ U) (hv : v ∉ Z) {A N : Set V}
    (hZN : (↑Z : Set V) ⊆ N) (w : Sym2 V → ℝ) (hm : ∑ ω, weight w ω = 1) :
    Mav w U A v N = ∑ ω, weight w ω * Mav w (U \ Z) A v ((N \ ↑Z) ∪ rS U Z ω) := by
  have hZW : (↑Z : Set V) ⊆ A ∪ N := hZN.trans Set.subset_union_right
  have hvUZ : v ∈ U \ Z := Finset.mem_sdiff.2 ⟨hvU, hv⟩
  have h := step_sum hZU hv hZW w hm (fun _ => (1 : ℝ))
  simp only [one_mul, blockE] at h
  unfold Mav
  rw [h]
  refine Finset.sum_congr rfl fun ω _ => ?_
  simp only [rD_eq_of_agree (U \ Z) hvUZ (union_diff_agree U Z A N (rS U Z ω))]

/-- `E_A` only sees `A ∩ U`: `E_{A}(N) = Σ weight·(1{o ∈ C_v}·1{v ↮ (A ∪ N) ∩ U})` for `v ∈ U`. [folklore] -/
theorem Eav_eq_inter (w : Sym2 V → ℝ) (U : Finset V) (A : Set V) (o : V) {v : V} (hv : v ∈ U) (N : Set V) :
    Eav w U A o v N = ∑ ω, weight w ω * (oInd o v (rC U v ω) * ind (rD U v ((A ∪ N) ∩ ↑U)) ω) := by
  unfold Eav; rw [rD_inter_coe U hv]

/-- `M_A` only sees `A ∩ U`. [folklore] -/
theorem Mav_eq_inter (w : Sym2 V → ℝ) (U : Finset V) (A : Set V) {v : V} (hv : v ∈ U) (N : Set V) :
    Mav w U A v N = ∑ ω, weight w ω * ind (rD U v ((A ∪ N) ∩ ↑U)) ω := by
  unfold Mav; rw [rD_inter_coe U hv]

end Percolation.Continuity.CovTau
