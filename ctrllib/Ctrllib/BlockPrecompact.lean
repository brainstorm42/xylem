/-
Forward precompactness for the circumcentroidal block.

`forwardPrecompact_of_coercive` (`LaSalle.lean:87`) discharges the `hcpt` interface from a
norm-coercive Lyapunov function, and `blockLyap_coercive` (`BlockLyapunov.lean:87`) supplies
coercivity for the concrete SPD block — but the two do not meet. The bridge consumes a
squared-norm bound on a single point of a normed space, `c₁ ‖y‖² ≤ V y`; the block lemma
produces a dot-product bound on a PAIR, `c₁ (v ⬝ᵥ v + x ⬝ᵥ x) ≤ V v x`. This module closes
that shape gap and composes them, so that for the circumcentroidal block coercivity is a
THEOREM rather than a modelling input.

After this module exactly two things remain applier-side:

* the `Flow ℝ` itself — the `IsSolutionTo` interface, still open. Mathlib v4.31.0 has no
  ODE→Flow bridge, so the flow cannot be built inside the library; see the WALL note on
  the corresponding local note.
  Note this is a missing-capability wall, NOT a proof that no such flow exists;
* the forward decrease of `blockLyap` along the orbit, which the Lyapunov argument
  integrates.

The norm bookkeeping is the one `CoupledSandwich` already uses for Panteley's 𝒦∞ sandwich:
on `EuclideanSpace` the squared norm is the self dot product, and Mathlib's product norm is
the SUP norm, so `‖y‖² ≤ ‖y.1‖² + ‖y.2‖²` — with room to spare, which is why no constant is
lost in the composition.
-/
import Ctrllib.LaSalle
import Ctrllib.CoupledSandwich

open Matrix

namespace Ctrllib

variable {n m : Type*} [Fintype n] [Fintype m]

/-- On `EuclideanSpace ℝ n` the squared norm is the self dot product: the `L²` norm's
defining sum `∑ (x i)²` is literally `∑ x i * x i`. Re-derived here rather than imported —
`CoupledSandwich`'s copy is `private`, and duplicating two lines is cheaper than widening a
sealed module's public surface. -/
private lemma norm_sq_eq_dotProduct (x : EuclideanSpace ℝ n) : ‖x‖ ^ 2 = x ⬝ᵥ x := by
  rw [EuclideanSpace.real_norm_sq_eq, dotProduct]
  simp only [pow_two]

/-- **Norm-coercivity of the block Lyapunov function**, in the exact shape
`forwardPrecompact_of_coercive` consumes. For positive-definite `M, K` there is `c₁ > 0`
with `c₁ ‖y‖² ≤ V(y)` for every stacked state `y = (v, x)`, where `c₁ = ½ min(λ_min M,
λ_min K)` comes from `blockLyap_coercive`.

This is the same quadratic lower bound `blockLyap_classKInfinity_sandwich` establishes en
route to its 𝒦∞ witness, stated on its own instead of inside an existential over class-𝒦∞
functions — the precompactness bridge needs the concrete `c₁ s²`, which the 𝒦∞ packaging
discards. -/
theorem blockLyap_norm_coercive [Nonempty n] [Nonempty m]
    {M : Matrix n n ℝ} {K : Matrix m m ℝ} (hM : M.PosDef) (hK : K.PosDef) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ y : EuclideanSpace ℝ n × EuclideanSpace ℝ m,
      c₁ * ‖y‖ ^ 2 ≤ blockLyap M K y.1 y.2 := by
  classical
  obtain ⟨c₁, hc₁, hbound⟩ := blockLyap_coercive hM hK
  refine ⟨c₁, hc₁, fun y => ?_⟩
  -- Mathlib's product norm is the sup norm, so the stacked squared norm is dominated by
  -- the sum of the block squared norms.
  have hmax : ‖y‖ ^ 2 ≤ ‖y.1‖ ^ 2 + ‖y.2‖ ^ 2 := by
    rw [Prod.norm_def]
    rcases le_total ‖y.1‖ ‖y.2‖ with h | h
    · rw [max_eq_right h]; nlinarith [sq_nonneg ‖y.1‖]
    · rw [max_eq_left h]; nlinarith [sq_nonneg ‖y.2‖]
  have hb : c₁ * (‖y.1‖ ^ 2 + ‖y.2‖ ^ 2) ≤ blockLyap M K y.1 y.2 := by
    have := hbound y.1 y.2
    rwa [← norm_sq_eq_dotProduct y.1, ← norm_sq_eq_dotProduct y.2] at this
  calc c₁ * ‖y‖ ^ 2
      ≤ c₁ * (‖y.1‖ ^ 2 + ‖y.2‖ ^ 2) := mul_le_mul_of_nonneg_left hmax hc₁.le
    _ ≤ blockLyap M K y.1 y.2 := hb

/-- **Forward precompactness for the circumcentroidal block.** Given a flow on the stacked
state space along which the block Lyapunov function does not increase forward in time,
positive-definiteness of `M` and `K` alone yields `ForwardPrecompact`.

This is the `hcpt` interface discharged *at the concrete block* rather than as an
implication: the coercivity hypothesis of `forwardPrecompact_of_coercive` is supplied here
by `blockLyap_norm_coercive`, so an applier no longer has to produce it. The two remaining
inputs are the flow `ϕ` and the forward decrease `hdec`, and only the first of those is
blocked by a Mathlib gap. -/
theorem forwardPrecompact_blockLyap [Nonempty n] [Nonempty m]
    {M : Matrix n n ℝ} {K : Matrix m m ℝ} (hM : M.PosDef) (hK : K.PosDef)
    (ϕ : Flow ℝ (EuclideanSpace ℝ n × EuclideanSpace ℝ m))
    (y₀ : EuclideanSpace ℝ n × EuclideanSpace ℝ m)
    (hdec : ∀ t : ℝ, 0 ≤ t →
      blockLyap M K (ϕ t y₀).1 (ϕ t y₀).2 ≤ blockLyap M K y₀.1 y₀.2) :
    ForwardPrecompact ϕ y₀ := by
  obtain ⟨c₁, hc₁, hcoer⟩ := blockLyap_norm_coercive hM hK
  exact forwardPrecompact_of_coercive (V := fun y => blockLyap M K y.1 y.2) ϕ y₀ hc₁
    hcoer hdec

end Ctrllib

#print axioms Ctrllib.blockLyap_norm_coercive
#print axioms Ctrllib.forwardPrecompact_blockLyap
