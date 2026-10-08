import Percolation.Literature.CriticalContinuity
import Percolation.Util.Linter

/-!
# Percolation in half-spaces and slabs of `ℤ³`

Published theorems of Barsky–Grimmett–Newman, Grimmett–Marstrand and
Duminil-Copin–Sidoravicius–Tassion on percolation in half-spaces and slabs, recorded as
statements `def … : Prop`, on the way to `θ_{ℤ³}(p_c) = 0` (`PercolationContinuityZ3`).

## Content

* `halfSpaceGraph d`, `slabGraph d k` — the subgraphs of `zdGraph d` induced on
  `ℍ = {x | 0 ≤ x₀}` and `S_k = {x | 0 ≤ x₀ ≤ k}` (first coordinate; Grimmett 1999, §7.3 uses the
  last coordinate, `ℍ = ℤ^{d-1} × ℤ₊`, and DST 2016 the slab `ℤ² × {0,…,k}` — the same graphs up
  to the coordinate permutation symmetry of `zdGraph d`), with their origin `halfSpaceOrigin`,
  `slabOrigin`.
* `BarskyGrimmettNewman1991` — Grimmett 1999, Thm. (7.35) (Barsky–Grimmett–Newman
  1991): for `d ≥ 2`, `θ_ℍ(p_c) = 0`, where `p_c = p_c(ℤ^d)` (Grimmett 1999, §7.2, p. 148:
  "`p_c = p_c(ℤ^d)`"; and `p_c(ℍ) = p_c`, p. 162).
* `BarskyGrimmettNewman1991_Z3` — its case `d = 3`, written in the form used downstream
  (`(zdGraph 3).induce {x | 0 ≤ x 0}` rooted at `0`).
* `DuminilCopinSidoraviciusTassion2016` — DST 2016 (arXiv:1401.7130), Thm. 1: for
  every `k > 0`, bond percolation on the slab `S_k` of `ℤ³` has no infinite cluster at its own
  critical point, `θ_{S_k}(p_c(S_k)) = 0`.

## Sources

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999: §7.2 Thm. (7.2) (p. 148), §7.3 p. 162
  (`p_c(ℍ) = p_c`) and Thm. (7.35) (p. 163, `θ_ℍ(p_c) = 0`).
* D. J. Barsky, G. R. Grimmett, C. M. Newman, *Percolation in half-spaces: equality of critical
  densities and continuity of the percolation probability*, PTRF 90 (1991) 111–148.
* H. Duminil-Copin, V. Sidoravicius, V. Tassion, *Absence of infinite cluster for critical
  Bernoulli percolation on slabs*, CPAM 69 (2016), arXiv:1401.7130, Thm. 1 (p. 2).

## Design choices

* Percolation "in `ℍ`" / "in `S_k`" is bond percolation on the INDUCED subgraph
  (`SimpleGraph.induce`), with `theta` and `criticalProb` of `Literature/Basic.lean` applied to that
  graph at the origin — exactly Grimmett's `p_c(A)` convention (§7.2, p. 148: "the critical value
  of bond percolation on the subgraph of `ℤ^d` induced by the vertex set `A`") and DST's `P_p` on
  `S_k` (p. 2). The equivalent formulation by `ℍ`-restricted open paths of the full configuration
  (`openConnIn`) is not used here.
* Critical points are fed to `theta` as points of `unitInterval` via `criticalProb_mem_Icc`, as
  in `criticalProbI`.
-/

noncomputable section

namespace Percolation.Literature

open MeasureTheory LatticeModels

/-! ## Half-spaces and slabs as induced subgraphs -/

/-- The half-space `ℍ = {x ∈ ℤ^d | 0 ≤ x₀}` (Grimmett 1999, §7.3, up to permuting coordinates).
[cite: GrimmettPercolation1999, §7.3 (p. 162)] -/
def halfSpace (d : ℕ) [NeZero d] : Set (Site d) := {x | 0 ≤ x 0}

/-- The slab `S_k = {x ∈ ℤ^d | 0 ≤ x₀ ≤ k}` (Grimmett 1999, §7.1–7.2 `S_k`; DST 2016 `ℤ² × {0,…,k}`
for `d = 3`, up to permuting coordinates). [cite: DuminilCopinSidoraviciusTassion2016, p. 2 (S_k)] -/
def slab (d : ℕ) [NeZero d] (k : ℕ) : Set (Site d) := {x | 0 ≤ x 0 ∧ x 0 ≤ (k : ℤ)}

/-- The origin lies in the half-space. [folklore] -/
theorem zero_mem_halfSpace (d : ℕ) [NeZero d] : (0 : Site d) ∈ halfSpace d :=
  Set.mem_setOf.mpr le_rfl

/-- The origin lies in every slab. [folklore] -/
theorem zero_mem_slab (d : ℕ) [NeZero d] (k : ℕ) : (0 : Site d) ∈ slab d k :=
  ⟨le_rfl, Int.natCast_nonneg k⟩

/-- Bond percolation "in `ℍ`": the subgraph of `zdGraph d` induced on the half-space (Grimmett
1999, §7.2 p. 148 convention for `p_c(A)`). [cite: GrimmettPercolation1999, §7.2 (p. 148, p_c(A))] -/
abbrev halfSpaceGraph (d : ℕ) [NeZero d] : SimpleGraph (halfSpace d) :=
  (zdGraph d).induce (halfSpace d)

/-- Bond percolation "in `S_k`": the subgraph of `zdGraph d` induced on the slab.
[cite: DuminilCopinSidoraviciusTassion2016, p. 2] -/
abbrev slabGraph (d : ℕ) [NeZero d] (k : ℕ) : SimpleGraph (slab d k) :=
  (zdGraph d).induce (slab d k)

/-- The origin of `ℍ`. [folklore] -/
def halfSpaceOrigin (d : ℕ) [NeZero d] : halfSpace d := ⟨0, zero_mem_halfSpace d⟩

/-- The origin of `S_k`. [folklore] -/
def slabOrigin (d : ℕ) [NeZero d] (k : ℕ) : slab d k := ⟨0, zero_mem_slab d k⟩

/-- The critical probability of a rooted graph as a point of `[0,1]`. [folklore] -/
def criticalProbIOf {V : Type} (G : SimpleGraph V) (x : V) : unitInterval :=
  ⟨criticalProb G x, criticalProb_mem_Icc _ _⟩

/-! ## Statements -/

/-- **Barsky–Grimmett–Newman: no percolation in the half-space at `p_c`**
(Grimmett 1999, Thm. (7.35), p. 163: "Let `d ≥ 2`. We have that `θ_ℍ(p_c) = 0`", with
`p_c = p_c(ℤ^d)` by the convention of §7.2, p. 148, and `p_c(ℍ) = p_c`, p. 162;
Barsky–Grimmett–Newman 1991). Here `ℍ = {0 ≤ x₀}` (coordinate symmetry of `ℤ^d`).
[cite: GrimmettPercolation1999, Thm. (7.35)] -/
def BarskyGrimmettNewman1991 : Prop :=
  ∀ (d : ℕ) [NeZero d], 2 ≤ d →
    theta (halfSpaceGraph d) (halfSpaceOrigin d) (criticalProbI d) = 0

/-- The case `d = 3` of `BarskyGrimmettNewman1991`, in the form used downstream:
`θ_ℍ(p_c(ℤ³)) = 0` for `ℍ = {x ∈ ℤ³ | 0 ≤ x₀}` (Grimmett 1999, Thm. (7.35) with p. 162).
[cite: GrimmettPercolation1999, Thm. (7.35)] -/
def BarskyGrimmettNewman1991_Z3 : Prop :=
  theta ((zdGraph 3).induce {x | 0 ≤ x 0}) ⟨0, Set.mem_setOf.mpr le_rfl⟩ (criticalProbI 3) = 0

/-- **Duminil-Copin–Sidoravicius–Tassion: no infinite cluster at criticality on slabs** (DST 2016, arXiv:1401.7130, Thm. 1: "For any `k > 0`, `P_{p_c(k)}[0 ↔ ∞ in S_k] = 0`",
`S_k = ℤ² × {0,…,k}` with nearest-neighbour edges, `p_c(k)` its critical parameter). Here
`S_k = {x ∈ ℤ³ | 0 ≤ x₀ ≤ k}` (coordinate symmetry).
[cite: DuminilCopinSidoraviciusTassion2016, Thm. 1] -/
def DuminilCopinSidoraviciusTassion2016 : Prop :=
  ∀ k : ℕ, 0 < k →
    theta (slabGraph 3 k) (slabOrigin 3 k) (criticalProbIOf (slabGraph 3 k) (slabOrigin 3 k)) = 0

end Percolation.Literature

end
