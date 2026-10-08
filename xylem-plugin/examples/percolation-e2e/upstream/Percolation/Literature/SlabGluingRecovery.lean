import Percolation.Literature.SlabGluingFact1
import Percolation.Util.Linter

/-!
# DST 2016, §2.3 — towards Fact 2: the structure is invisible from the old world

A small generic **propagation lemma** for the local
surgeries of Duminil-Copin–Sidoravicius–Tassion 2016, §2.3 (proof of Fact 2): if `ω' ⊆ ω ∪ Enew`
where every new edge joins two structure vertices (`Sw`), protected structure vertices (`Wv ⊆ Sw`)
can be entered by an `ω'`-open edge only from structure vertices or when they belong to a set
`Keep` (the kept part of the minimal path, entered through its own stubs), and unprotected
structure vertices are not `ω`-joined inside `Reg` to a base point `x₀`, then along any
`ω'`-open path inside a set `A ⊆ Reg` with `A ∩ Keep ∩ Sw = ∅`, the property "off the structure
and `ω`-joined to `x₀` inside `Reg`" propagates from the start to the end
(`not_mem_structure_of_pathIn`). In DST's recovery step ("`z` is the only vertex in
`γ_min(ω^{(z)})` which is connected to `S'_n` in `B'_n ∖ γ_min(ω^{(z)})`", p. 7) this is used
twice: for the unknown continuation of `γ_min(ω^{(z)})` after the rerouted piece (it never meets
the structure), and for a putative attachment path from a non-structure vertex of
`γ_min(ω^{(z)})` to `S̄'_n` (it would be `ω`-open, giving `C_n(ω)`).

## Sources

* H. Duminil-Copin, V. Sidoravicius, V. Tassion, *Absence of infinite cluster for critical
  Bernoulli percolation on slabs*, CPAM 69 (2016), arXiv:1401.7130, §2.3, proof of Fact 2 (p. 7).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace Percolation.Literature

open LatticeModels

variable {k : ℕ}

/-- **propagation off the structure** (DST 2016, §2.3, proof of Fact 2, recovery step).
Along an `ω'`-open path inside `A ⊆ Reg`, if the start is off the structure `Sw` and `ω`-joined
to `x₀` inside `Reg`, so is the end — provided new edges join structure vertices (`hEnew`),
protected vertices are entered only from the structure or lie in `Keep` (`h2`), `A` contains no
structure vertex of `Keep` (`hA`), and unprotected structure vertices are not `ω`-joined to `x₀`
inside `Reg` (`h4`). [cite: DuminilCopinSidoraviciusTassion2016, §2.3, proof of Fact 2 (p. 7)] -/
theorem not_mem_structure_of_pathIn {ω ω' : BondConfig (slab 3 k)} {Reg A : Set (slab 3 k)}
    (hAReg : A ⊆ Reg) (Enew : Set (Sym2 (slab 3 k))) (Wv Sw Keep : Set (slab 3 k))
    (hWv : Wv ⊆ Sw) (x₀ : slab 3 k)
    (h3 : ω' ⊆ ω ∪ Enew) (hEnew : ∀ a b, s(a, b) ∈ Enew → a ∈ Sw ∧ b ∈ Sw)
    (h2 : ∀ t x, s(t, x) ∈ ω' → x ∈ Wv → t ∈ Sw ∨ x ∈ Keep)
    (hA : ∀ x ∈ A, x ∈ Keep → x ∉ Sw)
    (h4 : ∀ x ∈ Sw, x ∉ Wv → ω ∉ openConnIn Reg x₀ x)
    {q s : slab 3 k} (hpath : PathIn (openGraph ω') A q s)
    (hq : q ∉ Sw) (hq' : ω ∈ openConnIn Reg x₀ q) :
    s ∉ Sw ∧ ω ∈ openConnIn Reg x₀ s := by
  obtain ⟨-, h⟩ := hpath
  induction h with
  | refl => exact ⟨hq, hq'⟩
  | @tail y y' _ hyy' ih =>
    obtain ⟨hy, hy'⟩ := ih
    obtain ⟨hadj, hy'A⟩ := hyy'
    have he : s(y, y') ∈ ω' ∧ y ≠ y' := (openGraph_adj ω' y y').1 hadj
    have hω : s(y, y') ∈ ω := by
      rcases h3 he.1 with h | h
      · exact h
      · exact absurd (hEnew _ _ h).1 hy
    have hyReg : y ∈ Reg := hy'.2.1
    have hy'Reg : y' ∈ Reg := hAReg hy'A
    have hconn : ω ∈ openConnIn Reg x₀ y' := by
      refine SlabCriticality.openConnIn_trans hy' ?_
      exact openConnIn_head_of_mem y [y']
        (List.isChain_cons_cons.2 ⟨⟨hω, he.2⟩, List.isChain_singleton _⟩)
        (fun v hv => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl
          · exact hyReg
          · exact hy'Reg) y' (by simp)
    have hy'W : y' ∉ Wv := fun hW => by
      rcases h2 y y' he.1 hW with h | h
      · exact hy h
      · exact hA y' hy'A h (hWv hW)
    exact ⟨fun hS => h4 y' hS hy'W hconn, hconn⟩

/-- Corollary in `openConnIn` form. [cite: DuminilCopinSidoraviciusTassion2016, §2.3, proof of
Fact 2 (p. 7)] -/
theorem not_mem_structure_of_openConnIn {ω ω' : BondConfig (slab 3 k)} {Reg A : Set (slab 3 k)}
    (hAReg : A ⊆ Reg) (Enew : Set (Sym2 (slab 3 k))) (Wv Sw Keep : Set (slab 3 k))
    (hWv : Wv ⊆ Sw) (x₀ : slab 3 k)
    (h3 : ω' ⊆ ω ∪ Enew) (hEnew : ∀ a b, s(a, b) ∈ Enew → a ∈ Sw ∧ b ∈ Sw)
    (h2 : ∀ t x, s(t, x) ∈ ω' → x ∈ Wv → t ∈ Sw ∨ x ∈ Keep)
    (hA : ∀ x ∈ A, x ∈ Keep → x ∉ Sw)
    (h4 : ∀ x ∈ Sw, x ∉ Wv → ω ∉ openConnIn Reg x₀ x)
    {q s : slab 3 k} (hqs : ω' ∈ openConnIn A q s)
    (hq : q ∉ Sw) (hq' : ω ∈ openConnIn Reg x₀ q) :
    s ∉ Sw ∧ ω ∈ openConnIn Reg x₀ s :=
  not_mem_structure_of_pathIn hAReg Enew Wv Sw Keep hWv x₀ h3 hEnew h2 hA h4
    (mem_openConnIn_iff_pathIn.1 hqs) hq hq'

end Percolation.Literature
