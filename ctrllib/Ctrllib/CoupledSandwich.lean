/-
Coupled-block class-𝒦∞ sandwich — the cheap discharge of the cascade `hsand`
interface (scope dossier the corresponding local note card 86baw867b).

`Cascade.lean` carries `hsand : ∀ t ∈ Ici 0, α₁ ‖x₁ t‖ ≤ V (x₁ t)` (α₁ ∈ 𝒦∞) as a
named modelling input — the reshaped-Lyapunov lower sandwich (panteley2001growth
eq 10/13). For the *concrete SPD coupled block* it is not a modelling input at all:
the block already owns a machine-checked quadratic lower bound,

    `blockLyap_coercive` :  c₁ (v ⬝ᵥ v + x ⬝ᵥ x) ≤ blockLyap M K v x ,  0 < c₁

(BlockLyapunov.lean, Rayleigh–Ritz on the two SPD blocks). This file converts that
into the exact `hsand` shape by supplying the concrete class-𝒦∞ lower comparison
function `α₁(s) = c₁ s²` (built through the sealed `ComparisonFunctions` algebra,
mirroring `isClassKInfinity_id` / `IsClassKInfinity.const_mul`) and wiring the
Euclidean norm identity `‖x‖² = x ⬝ᵥ x` (EuclideanSpace).

State space. The stacked state is the product `EuclideanSpace ℝ n × EuclideanSpace ℝ m`
so `y.1`, `y.2` are the base/arm blocks that `blockLyap` consumes. Mathlib gives this
product the sup norm `‖y‖ = max ‖y.1‖ ‖y.2‖` (`Prod.norm_def`); a *lower* sandwich
`α₁(‖y‖) ≤ V` only needs `‖y‖² ≤ ‖y.1‖² + ‖y.2‖²`, which the max satisfies — so the
𝒦∞ lower bound holds with room to spare and `hsand` is discharged for the block.

Scope note (dossier §3–4). This is `hsand` ONLY. Its companion `hdi` (the strict
`v' ≤ -a V + c‖x₂‖` decrease, eq 35) stays a WALL by design: the block's natural
energy decreases only semidefinitely (the `hzero` counterexample subspace), so no
sealed object yields a strict `-a·V` — that needs a converse-Lyapunov theorem
absent from Mathlib v4.31.0. Nothing here touches `hdi`.

Imports the sealed `BlockLyapunov` and `ComparisonFunctions`; edits neither.
-/
import Ctrllib.BlockLyapunov
import Ctrllib.ComparisonFunctions

open Set Filter Topology Matrix

namespace Ctrllib

/-! ### The class-𝒦∞ square -/

/-- The squaring map `s ↦ s²` is class 𝒦∞: continuous, strictly increasing on the ray,
zero at the origin, and unbounded. The building block for the quadratic lower comparison
function `α₁(s) = c₁ s²`; constructed directly, in the same spirit as `isClassKInfinity_id`. -/
theorem isClassKInfinity_sq : IsClassKInfinity (fun s : ℝ => s ^ 2) where
  continuousOn := (continuous_pow 2).continuousOn
  strictMonoOn := fun _ ha _ _ hab => pow_lt_pow_left₀ hab (mem_Ici.mp ha) (by norm_num)
  map_zero := by norm_num
  tendsto_atTop := tendsto_pow_atTop (by norm_num)

/-! ### The Euclidean norm ↔ dot-product bridge -/

variable {n m : Type*} [Fintype n] [Fintype m]

/-- On `EuclideanSpace ℝ n` the squared norm is the self dot product `‖x‖² = x ⬝ᵥ x`:
the `L²` norm's defining sum `∑ (x i)²` is literally `∑ x i * x i`. This is the bridge
from `blockLyap_coercive`'s `v ⬝ᵥ v` to the comparison function's `‖·‖`. -/
private lemma norm_sq_eq_dotProduct (x : EuclideanSpace ℝ n) : ‖x‖ ^ 2 = x ⬝ᵥ x := by
  rw [EuclideanSpace.real_norm_sq_eq, dotProduct]
  simp only [pow_two]

/-! ### The cascade `hsand` discharge for the concrete coupled block -/

/-- **The coupled-block class-𝒦∞ sandwich (pointwise).** For positive-definite blocks
`M, K` the block Lyapunov value dominates a concrete class-𝒦∞ function of the stacked-state
norm: there is `α₁ ∈ 𝒦∞` with `α₁(‖y‖) ≤ blockLyap M K y.1 y.2` for every stacked state
`y = (v, x)`. The witness is `α₁(s) = c₁ s²` with `c₁ = ½ min(λ_min M, λ_min K)` from
`blockLyap_coercive`. This is exactly the lower half of Panteley's eq 10/13 sandwich,
delivered as a theorem (not a modelling input) for the concrete SPD block. -/
theorem blockLyap_classKInfinity_sandwich [Nonempty n] [Nonempty m]
    {M : Matrix n n ℝ} {K : Matrix m m ℝ} (hM : M.PosDef) (hK : K.PosDef) :
    ∃ α₁ : ℝ → ℝ, IsClassKInfinity α₁ ∧
      ∀ y : EuclideanSpace ℝ n × EuclideanSpace ℝ m, α₁ ‖y‖ ≤ blockLyap M K y.1 y.2 := by
  classical
  obtain ⟨c₁, hc₁, hbound⟩ := blockLyap_coercive hM hK
  refine ⟨fun s => c₁ * s ^ 2, isClassKInfinity_sq.const_mul hc₁, ?_⟩
  intro y
  -- sup-product norm: `‖y‖² ≤ ‖y.1‖² + ‖y.2‖²`
  have hmax : ‖y‖ ^ 2 ≤ ‖y.1‖ ^ 2 + ‖y.2‖ ^ 2 := by
    rw [Prod.norm_def]
    rcases le_total ‖y.1‖ ‖y.2‖ with h | h
    · rw [max_eq_right h]; nlinarith [sq_nonneg ‖y.1‖]
    · rw [max_eq_left h]; nlinarith [sq_nonneg ‖y.2‖]
  -- the sealed quadratic lower bound, in norm form
  have hb : c₁ * (‖y.1‖ ^ 2 + ‖y.2‖ ^ 2) ≤ blockLyap M K y.1 y.2 := by
    have := hbound y.1 y.2
    rwa [← norm_sq_eq_dotProduct y.1, ← norm_sq_eq_dotProduct y.2] at this
  calc c₁ * ‖y‖ ^ 2
      ≤ c₁ * (‖y.1‖ ^ 2 + ‖y.2‖ ^ 2) := mul_le_mul_of_nonneg_left hmax hc₁.le
    _ ≤ blockLyap M K y.1 y.2 := hb

/-- **The `hsand` interface, discharged along any trajectory.** Specialises the pointwise
sandwich to the exact hypothesis shape `cascade_attractive` / `propIV1_cascade_attractive` consume
(`∀ t ∈ Ici 0, α₁ ‖x₁ t‖ ≤ V (x₁ t)` with `V = fun y => blockLyap M K y.1 y.2`). For the
concrete SPD coupled block this converts the `hsand` modelling input into a theorem: any
trajectory `x₁` in the stacked state space satisfies the reshaped-Lyapunov lower sandwich
with a concrete class-𝒦∞ `α₁`. -/
theorem blockLyap_hsand [Nonempty n] [Nonempty m]
    {M : Matrix n n ℝ} {K : Matrix m m ℝ} (hM : M.PosDef) (hK : K.PosDef)
    (x₁ : ℝ → EuclideanSpace ℝ n × EuclideanSpace ℝ m) :
    ∃ α₁ : ℝ → ℝ, IsClassKInfinity α₁ ∧
      ∀ t ∈ Ici (0 : ℝ), α₁ ‖x₁ t‖ ≤ blockLyap M K (x₁ t).1 (x₁ t).2 := by
  obtain ⟨α₁, hα₁, hsand⟩ := blockLyap_classKInfinity_sandwich hM hK
  exact ⟨α₁, hα₁, fun t _ => hsand (x₁ t)⟩

end Ctrllib

#print axioms Ctrllib.isClassKInfinity_sq
#print axioms Ctrllib.blockLyap_classKInfinity_sandwich
#print axioms Ctrllib.blockLyap_hsand
