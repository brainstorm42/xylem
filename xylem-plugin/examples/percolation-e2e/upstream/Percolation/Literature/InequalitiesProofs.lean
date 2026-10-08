import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Percolation.Literature.HarrisInequality
import Percolation.Literature.HarrisLocal
import Percolation.Literature.Inequalities
import Percolation.Util.Linter

/-!
# Proofs of correlation inequalities for Bernoulli bond percolation

Proofs of the statements of `Percolation.Literature.Inequalities`.

* `harris_fkg_holds : harris_fkg` — the Harris–FKG inequality `P_p(A) P_p(B) ≤ P_p(A ∩ B)` for
  increasing measurable events under Bernoulli bond percolation `bondPercolation G p =
  setBer(G.edgeSet, p)` on an arbitrary simple graph (Grimmett, *Percolation* (1999), Thm. (2.4)(b);
  Harris (1960), Lemma 4.1). It is the general product-space Harris inequality
  `Percolation.Literature.infinitePi_harris` (file `HarrisInequality.lean`, following Grimmett's proof)
  transported along the measurable order-embedding `q ↦ {e | q e} : (Sym2 V → Prop) → Set (Sym2 V)`
  through which Mathlib defines `setBer` (`ProbabilityTheory.setBernoulli_apply'`).
* `harris_fkg_lower` — the same inequality for decreasing (`IsLowerSet`) events, by passing to
  complements (Grimmett (1999), remark after Thm. (2.4)).
* `sqrt_trick_holds : sqrt_trick` — the square-root trick
  `maxᵢ P_p(Aᵢ) ≥ 1 - (1 - P_p(⋃ᵢ Aᵢ))^{1/n}` for increasing events `A₁, …, Aₙ`
  (Grimmett (1999), (11.14), pp. 288–289; Cox–Durrett (1988)): Harris–FKG for the decreasing
  complements gives `1 - P_p(⋃ Aᵢ) = P_p(⋂ Aᵢᶜ) ≥ ∏ (1 - P_p(Aᵢ)) ≥ (1 - maxᵢ P_p(Aᵢ))ⁿ`.
-/

namespace Percolation.Literature

open MeasureTheory LatticeModels ProbabilityTheory unitInterval
open scoped LatticeModels

variable {V : Type*}

/-- **Harris–FKG inequality for events** (Harris, *Proc. Camb. Phil.
Soc.* 56 (1960), Lemma 4.1; Grimmett, *Percolation* (2nd ed., 1999), Thm. (2.4)(b), pp. 34–36).
Under Bernoulli bond percolation `P_p` on any simple graph `G` (any vertex type `V`), increasing
measurable events are positively correlated: `P_p(A) P_p(B) ≤ P_p(A ∩ B)`. Proof: `setBer(E, p)` is
the image of the product measure `⨂_e (p δ_{e ∈ E} + (1 - p) δ_False)` on `Sym2 V → Prop` under the
monotone measurable map `q ↦ {e | q e}`, so this is `infinitePi_harris` applied to the preimages.
[cite: GrimmettPercolation1999, Thm. 2.4] [cite: HarrisPCPS1960, Lemma 4.1] -/
theorem harris_fkg_holds : harris_fkg (V := V) := by
  intro G p A B hA hB hAm hBm
  have hφ : Monotone (fun q : Sym2 V → Prop => {i | q i}) := fun q q' h i hi => h i hi
  have hφm : Measurable (fun q : Sym2 V → Prop => {i | q i}) := MeasurableEquiv.setOf.measurable
  have key : ∀ S : Set (BondConfig V), (bondPercolation G p).real S =
      (Measure.infinitePi fun i : Sym2 V =>
        toNNReal p • Measure.dirac (i ∈ G.edgeSet) + toNNReal (σ p) • Measure.dirac False).real
        ((fun q : Sym2 V → Prop => {i | q i}) ⁻¹' S) := fun S => by
    simp only [measureReal_def, bondPercolation, setBernoulli_apply']
  rw [key, key, key, Set.preimage_inter]
  exact infinitePi_harris _ (hA.preimage hφ) (hB.preimage hφ) (hφm hAm) (hφm hBm)

/-- **Harris–FKG for decreasing events** (Grimmett, *Percolation* (2nd ed., 1999), Thm. (2.4) and
the remark following it, p. 34: the inequality for decreasing events follows from the increasing
case since complements of decreasing events are increasing). Under Bernoulli bond percolation
`P_p` on any simple graph, decreasing measurable events are positively correlated:
`P_p(A) P_p(B) ≤ P_p(A ∩ B)`. Proof: apply `harris_fkg_holds` to `Aᶜ, Bᶜ` and use
`P(Aᶜ ∩ Bᶜ) = 1 - P(A) - P(B) + P(A ∩ B)`. [cite: GrimmettPercolation1999, Thm. 2.4] -/
theorem harris_fkg_lower (G : SimpleGraph V) (p : unitInterval) {A B : Set (BondConfig V)}
    (hA : IsLowerSet A) (hB : IsLowerSet B) (hAm : MeasurableSet A) (hBm : MeasurableSet B) :
    (bondPercolation G p).real A * (bondPercolation G p).real B ≤
      (bondPercolation G p).real (A ∩ B) := by
  have h := harris_fkg_holds G p hA.compl hB.compl hAm.compl hBm.compl
  rw [← Set.compl_union, probReal_compl_eq_one_sub hAm, probReal_compl_eq_one_sub hBm,
    probReal_compl_eq_one_sub (hAm.union hBm)] at h
  have hu := measureReal_union_add_inter hBm (μ := bondPercolation G p) (s := A)
  nlinarith [hu, h]

/-- **Square-root trick** (Grimmett, *Percolation* (2nd ed., 1999),
(11.14), pp. 288–289, following Cox–Durrett (1988)). If `A₁, …, Aₙ` (`n ≥ 1`) are increasing
measurable events under Bernoulli bond percolation `P_p` on any simple graph, then
`maxᵢ P_p(Aᵢ) ≥ 1 - (1 - P_p(⋃ᵢ Aᵢ))^{1/n}`. Grimmett states it for events of equal probability
(`P_p(A₁) ≥ …`); the vendored `∃ i` (maximum) form has the same proof:
`1 - P_p(⋃ Aᵢ) = P_p(⋂ Aᵢᶜ) ≥ ∏ P_p(Aᵢᶜ)` by Harris–FKG for the decreasing events `Aᵢᶜ`
(`harris_fkg_lower`, iterated over the finite index set as in Grimmett's (2.7), p. 34), and
`∏ (1 - P_p(Aᵢ)) ≥ (1 - maxᵢ P_p(Aᵢ))ⁿ`; take `n`-th roots. [cite: GrimmettPercolation1999, (11.14)] -/
theorem sqrt_trick_holds : sqrt_trick (V := V) := by
  classical
  intro G p ι _ _ A hA hAm
  obtain ⟨i, hi⟩ := Finite.exists_max fun i => (bondPercolation G p).real (A i)
  refine ⟨i, ?_⟩
  set μ := bondPercolation G p with hμ
  set m : ℝ := μ.real (A i) with hm
  have hm1 : m ≤ 1 := measureReal_le_one
  have hn : Fintype.card ι ≠ 0 := Fintype.card_ne_zero
  -- Harris–FKG for the decreasing events `(A j)ᶜ`, by induction on a finite index set.
  have hprod : ∀ s : Finset ι, ∏ j ∈ s, μ.real (A j)ᶜ ≤ μ.real (⋂ j ∈ s, (A j)ᶜ) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [μ]
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.set_biInter_insert]
      calc μ.real (A a)ᶜ * ∏ j ∈ s, μ.real (A j)ᶜ
          ≤ μ.real (A a)ᶜ * μ.real (⋂ j ∈ s, (A j)ᶜ) :=
            mul_le_mul_of_nonneg_left ih measureReal_nonneg
        _ ≤ μ.real ((A a)ᶜ ∩ ⋂ j ∈ s, (A j)ᶜ) :=
            harris_fkg_lower G p (hA a).compl (isLowerSet_iInter₂ fun j _ => (hA j).compl)
              (hAm a).compl (s.measurableSet_biInter fun j _ => (hAm j).compl)
  -- `(1 - m)^n ≤ ∏ⱼ (1 - P(A j)) ≤ P(⋂ⱼ (A j)ᶜ) = 1 - P(⋃ⱼ A j)`.
  have key : (1 - m) ^ Fintype.card ι ≤ 1 - μ.real (⋃ j, A j) := by
    have h1 : 1 - μ.real (⋃ j, A j) = μ.real (⋂ j ∈ (Finset.univ : Finset ι), (A j)ᶜ) := by
      rw [← probReal_compl_eq_one_sub (MeasurableSet.iUnion hAm), Set.compl_iUnion]
      simp
    have h2 : (1 - m) ^ Fintype.card ι ≤ ∏ j ∈ (Finset.univ : Finset ι), μ.real (A j)ᶜ := by
      rw [← Finset.card_univ, ← Finset.prod_const]
      refine Finset.prod_le_prod (fun j _ => sub_nonneg.2 hm1) fun j _ => ?_
      rw [probReal_compl_eq_one_sub (hAm j)]
      linarith [hi j]
    exact h1 ▸ h2.trans (hprod _)
  -- Take `n`-th roots.
  have hroot : 1 - m ≤ (1 - μ.real (⋃ j, A j)) ^ ((Fintype.card ι : ℝ)⁻¹) := by
    calc 1 - m = ((1 - m) ^ Fintype.card ι) ^ ((Fintype.card ι : ℝ)⁻¹) :=
          (Real.pow_rpow_inv_natCast (sub_nonneg.2 hm1) hn).symm
      _ ≤ (1 - μ.real (⋃ j, A j)) ^ ((Fintype.card ι : ℝ)⁻¹) :=
          Real.rpow_le_rpow (pow_nonneg (sub_nonneg.2 hm1) _) key (by positivity)
  linarith

open Finset Function

/-! ### The BK inequality on the weighted discrete cube -/

section Cube

variable {α : Type*} [Fintype α] [DecidableEq α]

section Coupling

/-! The coupled events `E_S` of the BK coupling proof on two copies `(x, y)` of the cube `α → Bool`
 (Grimmett, *Probability on Graphs* (2018), proof of Thm. 4.17, events `Â_j ∘ B̂`; Grimmett,
 *Percolation* (1999), proof of Thm. (2.12), events `A' ∘ B'_k`): `A` is witnessed by `K` inside
 `x`, `B` is witnessed by `L`, read in `y` on the coordinates of `S` and in `x` off `S`, and the two
 witnesses are disjoint off `S`.
-/

variable {A B : Set (α → Bool)} {E : Finset α → Set ((α → Bool) × (α → Bool))}
  (hE : ∀ (S : Finset α) (xy : (α → Bool) × (α → Bool)), xy ∈ E S ↔
    ∃ K L : α → Bool, K ≤ xy.1 ∧ (∀ i ∈ S, L i ≤ xy.2 i) ∧ (∀ i ∉ S, L i ≤ xy.1 i) ∧
      (∀ i, K i = true → L i = true → i ∈ S) ∧ K ∈ A ∧ L ∈ B)
  {S : Finset α} {k : α}

include hE

end Coupling

end Cube

/-! ### The BK inequality for Bernoulli bond percolation -/

/-! ### Reimer's inequality — butterfly lemma, flip lemma, folding, proof

This section is definition-free: the auxiliary vectors of the linear-algebra proof of Reimer's
butterfly lemma and the maps of the folding argument are section variables constrained by
defining equations (hypotheses `hfV`, `hgV`, …), instantiated by `rfl` in the final theorems, in
the manner of the coupled events `E S` of the BK proof above. -/

section ReimerButterflyLA

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! #### The linear algebra of butterflies

For a butterfly `(x, S)` on the cube `α → Bool` (Reimer 2000; Borgs–Chayes–Randall 1999, §4):
red wing `[x]_S = {z | z = x on S}`, flipped yellow wing `{z | z = x̄ off S}`. Vectors over `ℤ`:
`f_{x,S}(z) = [z ∈ [x]_S] 2^{d(z,x)}` (`fV S x z`), `g_{x,S}(z) = [z = x̄ off S] 2^{#{i∈S | zᵢ=xᵢ}}
(-1)^{#{i∈S | zᵢ≠xᵢ}}` (`gV S x z`), the kernel `K = [[2,-1],[-1,2]]^{⊗α}` (`kK`), the constant
`c_S = 3^{|α|-|S|}` (`cC S`) and the Walsh characters `χ_C` (`ch C`), all given by one-coordinate
product formulas. -/

variable {fV gV : Finset α → (α → Bool) → (α → Bool) → ℤ} {kK : (α → Bool) → (α → Bool) → ℤ}
  {cC : Finset α → ℤ} {ch : Finset α → (α → Bool) → ℤ}
  (hfV : ∀ S x z, fV S x z = ∏ i, (if z i = x i then (1 : ℤ) else if i ∈ S then 0 else 2))
  (hgV : ∀ S x z, gV S x z =
    ∏ i, (if i ∈ S then (if z i = x i then (2 : ℤ) else -1) else (if z i = x i then 0 else 1)))
  (hkK : ∀ z w, kK z w = ∏ i, (if z i = w i then (2 : ℤ) else -1))
  (hcC : ∀ S, cC S = ∏ i, (if i ∈ S then (1 : ℤ) else 3))
  (hch : ∀ C z, ch C z = ∏ i ∈ C, (if z i then (-1 : ℤ) else 1))

end ReimerButterflyLA

section ReimerFolding

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! #### Folding: from the flip lemma to the weighted cube

`flp Δ y = y^Δ` is `y` flipped on `Δ`; `rp Δ y` resets the coordinates in `Δ` to `false` (a fibre
representative); for fixed `Δ, u`, `ext v` extends a pattern `v : Δ → Bool` by `u` off `Δ`. -/

variable {flp : Finset α → (α → Bool) → α → Bool}
  (hflp : ∀ Δ y i, flp Δ y i = if i ∈ Δ then !y i else y i)
  {rp : Finset α → (α → Bool) → α → Bool}
  (hrp : ∀ Δ y i, rp Δ y i = if i ∈ Δ then false else y i)

section Fibre

variable (Δ : Finset α) (u : α → Bool) {ext : (Δ → Bool) → α → Bool}
  (hext : ∀ v i, ext v i = if h : i ∈ Δ then v ⟨i, h⟩ else u i)

end Fibre

end ReimerFolding

end Percolation.Literature
