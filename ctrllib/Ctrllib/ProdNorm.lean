/-
Copyright (c) 2026 Antonia Hoffman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antonia Hoffman
-/
/-
Neutral norm bookkeeping for ordinary product spaces.

Mathlib's `Prod` norm is the sup norm. This helper records the lower squared
bound needed by the first consumers without importing any physical model,
quadratic form, flow, or trajectory assumptions.
-/
import Mathlib.Analysis.Normed.Group.Constructions

namespace Ctrllib

/-- The squared norm of a product is bounded by the sum of the squared component
norms for the ordinary sup product norm. -/
theorem prod_norm_sq_le_sum_sq {E F : Type*} [Norm E] [Norm F] (z : E × F) :
    ‖z‖ ^ 2 ≤ ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 := by
  rw [Prod.norm_def]
  rcases le_total ‖z.1‖ ‖z.2‖ with h | h
  · rw [max_eq_right h]
    nlinarith [sq_nonneg ‖z.1‖]
  · rw [max_eq_left h]
    nlinarith [sq_nonneg ‖z.2‖]

end Ctrllib

#print axioms Ctrllib.prod_norm_sq_le_sum_sq
