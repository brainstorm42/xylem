import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Percolation.Literature.Basic
import Percolation.Util.Linter

/-!
# Shifted boxes `x + Λ(n)` in `ℤ^d`, and Cerf's limiting two-arms exponent

`shiftedBox x n` is the translate `x + Λ(n)` of the box `Λ(n) = [-n, n]^d` (`mem_shiftedBox_iff`, `shiftedBox_zero`), the
neighbourhoods used in the uniqueness-of-the-infinite-cluster argument (`UniquenessInfiniteCluster.lean`) and in Cerf's
two-arms estimates. The file also records Cerf's limiting exponent `γ_∞(d) = (2d² + 3d − 3)/(4d² + 5d − 5)` and its fixed-point
identity `γ_∞ = 1/2 + (d−1) γ_∞ /(4d² + 6d − 6)` (`cerfTwoArmsExponent_fixedPoint`); the two-arms estimate itself is not part of
this library. [cite: Cerf2015, §9]
-/

noncomputable section

open MeasureTheory Filter Topology Percolation.Literature.LatticeModels Percolation.Literature

namespace Percolation.Literature

section CriticalPercolation

variable {V : Type*} {d : ℕ}

/-! ### Restricted clusters and shifted boxes -/

/-- The shifted box `x + Λ(n) = {y | ‖y − x‖_∞ ≤ n}`. (Cerf 2015, p. 9, `x + Λ(n)`.) [cite: Cerf2015, §5] -/
def shiftedBox (x : Site d) (n : ℕ) : Finset (Site d) := (box d n).image fun y => x + y

/-- Membership in the shifted box. [cite: Cerf2015, §5] -/
theorem mem_shiftedBox_iff {x z : Site d} {n : ℕ} : z ∈ shiftedBox x n ↔ z - x ∈ box d n := by
  simp only [shiftedBox, Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨z - x, h, by abel⟩

/-- `0 + Λ(n) = Λ(n)`. [cite: Cerf2015, §5] -/
@[simp] theorem shiftedBox_zero (n : ℕ) : shiftedBox (0 : Site d) n = box d n := by
  ext z; simp [mem_shiftedBox_iff]

/-! ### Cerf's two-arms events -/

/-- Cerf's limiting two-arms exponent `γ_∞(d) = (2d² + 3d − 3)/(4d² + 5d − 5)`, the limit of
`γ_0 = 1/2`, `γ_{i+1} = 1/2 + (d−1) γ_i/(4d² + 6d − 6)` (Cerf 2015, §9, p. 14). [cite: Cerf2015, §9] -/
def cerfTwoArmsExponent (d : ℕ) : ℝ :=
  (2 * (d : ℝ) ^ 2 + 3 * d - 3) / (4 * (d : ℝ) ^ 2 + 5 * d - 5)

/-- `γ_∞` is the fixed point of the iteration `γ ↦ 1/2 + (d−1)γ/(4d²+6d−6)` (Cerf 2015, §9). [cite: Cerf2015, §9] -/
theorem cerfTwoArmsExponent_fixedPoint (hd : 1 ≤ d) :
    (1 : ℝ) / 2 + ((d : ℝ) - 1) * cerfTwoArmsExponent d / (4 * (d : ℝ) ^ 2 + 6 * d - 6) =
      cerfTwoArmsExponent d := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 : (4 * (d : ℝ) ^ 2 + 5 * d - 5) ≠ 0 := by nlinarith
  have h2 : (4 * (d : ℝ) ^ 2 + 6 * d - 6) ≠ 0 := by nlinarith
  unfold cerfTwoArmsExponent
  rw [mul_div_assoc', div_div, div_add_div _ _ two_ne_zero (mul_ne_zero h1 h2),
    div_eq_div_iff (mul_ne_zero two_ne_zero (mul_ne_zero h1 h2)) h1]
  ring

end CriticalPercolation

end Percolation.Literature
