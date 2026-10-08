import Init

/-!
# Cross-task proof-search fixture

An elementary helper for testing persistent lemma reuse. Its conventional
derivation and the two-task experiment are in the corresponding local note.
This is a tool integration fixture, not a new research result or a complete Brick.
-/

namespace Ctrllib.ProofSearchReuse

/-- Retain a premise while adjoining a trivial conjunct. -/
theorem keep (P : Prop) (h : P) : P ∧ True := ⟨h, True.intro⟩

end Ctrllib.ProofSearchReuse
