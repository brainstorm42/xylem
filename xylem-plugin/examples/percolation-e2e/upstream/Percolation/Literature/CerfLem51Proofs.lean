import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Percolation.Literature.CerfTwoArms
import Percolation.Literature.SiteMonotonicity
import Percolation.Util.Linter

/-!
# Cerf 2015, Lemma 5.1 (the central inequality): proof from Proposition 4.1

## The argument, as formalised

For `ω` fixed write `𝒞 = reachingClusters G L Λ(n+1) ω`, and for `C ∈ 𝒞` let
`K_C = |C̄ ∩ Λ(n)|`, `O_C = |C ∩ Λ(n)|`, `h_C = h(C̄ ∩ Λ(n))`; for `x ∈ Λ(n)` let
`m_x = #{C ∈ 𝒞 : x ∈ C̄}`. Cerf's sets are `F = {x open, C(x) ∈ 𝒞}`,
`G = {x closed, m_x ≥ 1}`, `H = {x closed, m_x ≥ 2}` (p. 6).

## Main result

* `Cerf2015_lem_5_1_of_prop_4_1 : Cerf2015_prop_4_1 → Cerf2015_lem_5_1`.
-/

noncomputable section

open MeasureTheory Filter Topology Percolation.Literature.LatticeModels Percolation.Literature

namespace Percolation.Literature

section CriticalPercolation

variable {V : Type*} {d : ℕ}

/-! ### The lattice `ℤ^d`: degrees, the two-arms events -/

section Lattice

/-- Every site of `ℤ^d` has at most `2d` neighbours (they are among the `x ± eᵢ`). [folklore] -/
theorem card_neighborFinset_zdGraph_le (x : Site d) :
    ((zdGraph d).neighborFinset x).card ≤ 2 * d := by
  classical
  have hsub : (zdGraph d).neighborFinset x ⊆ (Finset.univ : Finset (Fin d × Bool)).image
      fun q => if q.2 then x + Pi.single q.1 1 else x - Pi.single q.1 1 := by
    intro y hy
    rw [SimpleGraph.mem_neighborFinset, zdGraph_adj_iff] at hy
    obtain ⟨i, h | h⟩ := hy
    · exact Finset.mem_image.2 ⟨(i, true), Finset.mem_univ _, by simp [h]⟩
    · exact Finset.mem_image.2 ⟨(i, false), Finset.mem_univ _, by simp [h]⟩
  calc ((zdGraph d).neighborFinset x).card
      ≤ ((Finset.univ : Finset (Fin d × Bool)).image
          fun q => if q.2 then x + Pi.single q.1 1 else x - Pi.single q.1 1).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin d × Bool)).card := Finset.card_image_le
    _ = 2 * d := by simp [Finset.card_univ, mul_comm]

end Lattice

end CriticalPercolation

end Percolation.Literature
