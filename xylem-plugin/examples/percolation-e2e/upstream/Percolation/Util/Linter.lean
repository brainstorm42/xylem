import Lean

/-!
# Unused-variables linter: named binders of `∀` telescopes

Named propositions in this library spell their hypotheses as named binders of a `∀` telescope,
`def X : Prop := ∀ {ε : ℝ} (hε : 0 < ε), …`, exactly as a theorem signature would. Core's
`linter.unusedVariables` reports such binders although it exempts the arrow spelling
`(hε : 0 < ε) → …` (its builtin `depArrow` ignore function). This file extends that exemption to
bracketed binders sitting directly under `∀`; nothing else is affected.
-/

namespace Percolation.Util

/-- Ignore unused *named* binders `(h : P)`, `{x : α}`, `⦃x : α⦄` of a `∀` telescope, like core's
`depArrow` exemption of `(h : P) → Q`. -/
@[unused_variables_ignore_fn]
def ignoreForallBinder : Lean.Linter.IgnoreFunction := fun _ stack _ =>
  stack.matches [`null, ``Lean.Parser.Term.explicitBinder, `null, ``Lean.Parser.Term.forall] ||
  stack.matches [`null, ``Lean.Parser.Term.implicitBinder, `null, ``Lean.Parser.Term.forall] ||
  stack.matches [`null, ``Lean.Parser.Term.strictImplicitBinder, `null, ``Lean.Parser.Term.forall]

end Percolation.Util
