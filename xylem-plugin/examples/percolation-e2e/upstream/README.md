# θ(p_c) = 0 for Bernoulli bond percolation on ℤ^d in all dimensions d ≥ 2, in Lean 4 / Mathlib

The percolation probability θ(p) of nearest-neighbour Bernoulli bond percolation on ℤ^d vanishes at the critical point,
θ(p_c) = 0, for every d ≥ 2 — in particular on ℤ³, the classical open case (3 ≤ d ≤ 10 were open). The formal statement is
the vanishing at p_c; continuity of p ↦ θ(p) on [0,1] follows classically and is not part of the formal statement.

This project lives in the `percolation/` subdirectory of [anthropics/formal-math](https://github.com/anthropics/formal-math). All build
commands below are run from this directory (`cd percolation`).

> Research artifact. Not maintained; issues are welcome, pull requests are not accepted.
> A Lean 4 / Mathlib formalization released as a static research artifact; correctness rests on the mechanical checks recorded in AUDIT.md.

Repository: <https://github.com/anthropics/formal-math/tree/main/percolation>.

## Abstract

We prove θ(p_c) = 0 for nearest-neighbour Bernoulli bond percolation on ℤ^d for every dimension d ≥ 2: at the critical parameter the open cluster of the origin is almost surely finite (`Percolation.Continuity.CSH.percolationContinuity_allDimensions : ∀ d, 2 ≤ d → PercolationContinuity d`, in Lean 4 / Mathlib; comparator-checked over Mathlib-only definitions as `BondPercolation.percolation_continuity` and, for d = 3, `BondPercolation.percolation_continuity_Z3`). In particular this covers ℤ³, where it yields the classical corollary that p ↦ θ(p) is continuous on [0,1]; the formal statement is the vanishing of θ at p_c, and the classical equivalence with continuity on [0,1] is not itself part of the formal statement. The result was previously known for d = 2 (Harris, Kesten) and for d ≥ 11 (lace expansion); the cases 3 ≤ d ≤ 10 were open.

The route is Kozma–Nitzan's reduction (arXiv:2401.12397): they conjectured gluing inequalities for percolation on arbitrary finite weighted graphs and proved (their Theorem 6) that the weakest of them, Conjecture 3, implies θ(p_c) = 0 on ℤ^d for all d ≥ 2. This development proves Conjecture 3 (`Percolation.Continuity.CSH.kozmaNitzan_conjecture3_holds`) through a stronger additive gluing inequality (`Percolation.Continuity.CSH.additiveGluing_holds`): if P(a ↔ b) ≥ 1 − t for every a ∈ A, then P(o ↔ b) ≥ P(o ↔ A) − t. Additive gluing is derived from a new conditioned slack hierarchy (`Percolation.Continuity.CSH.cshHolds`): conditioned covariance inequalities for increasing functions of a single open cluster, indexed by finite lists of auxiliary vertices and proved by induction on the list, whose level-zero unconditioned case is the Harris inequality. Kozma–Nitzan's Theorem 6 and every classical input (Harris, van den Berg–Häggström–Kahn, the four functions theorem, Gladkov's decision-tree Harris–Kleitman inequality, the Barsky–Grimmett–Newman half-space theorem, Kesten's p_c(ℤ²) = 1/2) are re-proved in the library from Mathlib, so the statement has no hypothesis other than 2 ≤ d. Kozma–Nitzan's Conjectures 1, 2 and 4 are neither proved nor stated; nothing new is claimed about slabs, site percolation or other lattices. All main theorems depend only on propext, Classical.choice and Quot.sound; there is no sorry outside the two deliberate placeholders of the statement file Challenge.lean and no added axiom. The work has not yet been refereed by anyone independent of the author; correctness rests on the mechanical checks recorded in AUDIT.md, and readers should check that Challenge.lean states the intended theorem.

**Proof sketch:** a 15-page guide to the proof is in [`summary.pdf`](summary.pdf) (source [`summary.tex`](summary.tex); build with `tectonic summary.tex` or `latexmk -pdf summary.tex`, either of which uses `references.bib` and the bibliography style `amsplain-norepeat.bst` in this directory). The guide is an aid to reading, not the warrant: correctness rests on the Lean development and the comparator check recorded in AUDIT.md, and readers should still check that `Challenge.lean` states the intended theorem.

## Proof outline

1. **Model and statement** (`Percolation/Literature/Basic.lean`, `CriticalContinuity.lean`). Sites of ℤ^d are `Fin d → ℤ`, the nearest-neighbour graph is `zdGraph d`, a configuration is a set of open edges under Mathlib's product Bernoulli measure `setBernoulli` with parameter p; θ(p) is the probability that the open cluster of the origin is infinite, p_c := inf ({p ∈ [0,1] : θ(p) > 0} ∪ {1}), and `PercolationContinuity d := θ(p_c(ℤ^d)) = 0`.
2. **The conditioned slack hierarchy** (`Percolation/Continuity/CSH/`, theorem `cshHolds`). On a finite vertex set with pair weights in (0,1), fix an owner x, an avoided set Y, a list of distinct decoy vertices and two observers o ≠ v. For every increasing real function f of the open edge cluster 𝒞_x of x, the level form of the conditioned covariance u ↦ Cov(f(𝒞_x), 1{u ∈ C_x} | x ↮ Y) is nonnegative; at level zero this reads Cov(f(𝒞_x), 1{o ∈ C_x} | x ↮ Y) ≥ P(o ↔ v | v ↮ {x} ∪ Y) · Cov(f(𝒞_x), 1{v ∈ C_x} | x ↮ Y), and for Y = ∅, f = 1{v ∈ ·} it is the Harris inequality. Proof by strong induction on the number of decoys: conditionally on the open cluster of Y, the cluster of x is a percolation cluster in the graph with that cluster deleted; the induction step rewrites the averaged margin as a sum of margins of lower level, one per decoy and nonnegative by the induction hypothesis, plus a horizontal term that is bounded below by zero using a two-source covariance inequality. Inputs (all re-proved, `Percolation/Continuity/CovTau/`, `HullPort/`, `LowerTail/` and `Percolation/Literature/`): the Harris inequality, the conditional association inequalities of van den Berg–Häggström–Kahn (2006), the four functions theorem (via Mathlib), and Gladkov's decision-tree Harris–Kleitman inequality (2024, Thm 3.2).
3. **Hierarchy ⇒ additive gluing** (`CSH/AdditiveGluingOfCSH.lean`, `Percolation/Continuity/AdditiveGluing/`). The hierarchy gives a surplus-transfer inequality with decoys discounted, hence the plain surplus-transfer inequality, hence a first-relay lower bound for E[F(C_o); o ↔ A], hence the union bound localised on the first relay, P(o ↔ A, o ↮ b) ≤ Σ_a P(a is the first relay of o) · P(a ↮ b), hence additive gluing; the restriction to weights in (0,1) is removed at the end by continuity in the weights. Result: `additiveGluing_holds` on every finite graph with weights in [0,1].
4. **Additive gluing ⇒ Kozma–Nitzan Conjecture 3** (`MainTheorem.lean`, `OfGluing.lean`, `Statements.lean`): take t = δ = ε/2. The library's `NearOneGluing` is Kozma–Nitzan's Conjecture 3 verbatim (`nearOneGluing_iff_conjecture3`, by `Iff.rfl`).
5. **Conjecture 3 ⇒ θ(p_c) = 0 for d ≥ 3** — Kozma–Nitzan's Theorem 6, re-proved (`Percolation/Literature/KozmaNitzan*.lean`, following §§2–4 of their paper, including their Theorems 1, 3, 4, 7, 8). If θ(p) > 0, Conjecture 3 applied to finite auxiliary graphs built from boxes of ℤ^d yields percolation in a two-dimensional slab of ℤ^d at the same p (the one-step renormalisation / exploration scheme of §4). But no slab percolates at p_c(ℤ^d): a slab lies inside a half-space, and θ_ℍ(p_c) = 0 by the Barsky–Grimmett–Newman half-space theorem, re-proved here by the block construction of Grimmett, *Percolation* §7.3, together with slab technology. (The printed proof invokes the Aizenman–Grimmett strict inequality p_c(slab) > p_c; the formal proof does not need it. The Duminil-Copin–Sidoravicius–Tassion slab theorem is formalised as a literature input.)
6. **d = 2**: Harris' θ(1/2) = 0 and Kesten's p_c(ℤ²) = 1/2 (with Russo–Seymour–Welsh estimates), re-proved in `Percolation/Literature/Harris*`, `Kesten*`, `RSW*`.
7. **Assembly** (`MainTheorem.lean`, `Solution.lean`): `percolationContinuity_allDimensions` and `percolationContinuity_three`; `Solution.lean` transports them along `Iff.rfl` to the Mathlib-only definitions of `Challenge.lean` (`BondPercolation.percolation_continuity`, `BondPercolation.percolation_continuity_Z3`), and the comparator checks that the proved statements match the trusted statement file.

Not claimed: Kozma–Nitzan's Conjectures 1 (multiplicative gluing), 2 and 4; anything new about slabs, site percolation, other lattices, or quantitative behaviour of θ near p_c; continuity of θ as a function on [0,1] as a formal statement (classically equivalent, not formalised).

## Overview

This repository is a formal proof, in Lean 4 with Mathlib, that the percolation probability of
nearest-neighbour Bernoulli **bond** percolation on the hypercubic lattice ℤ^d vanishes at the
critical point in **every dimension d ≥ 2**:

> For every integer d ≥ 2, with p_c := inf ({p ∈ [0,1] : P_p(the open cluster of the origin is infinite) > 0} ∪ {1}),
> one has P_{p_c}(the open cluster of the origin is infinite) = 0.

(The `∪ {1}` only fixes the degenerate case in which θ vanishes identically; by monotonicity of θ this p_c is the
textbook sup {p : θ(p) = 0}.) The result was known for d = 2 (Harris 1960, Kesten 1980) and for d ≥ 11 (lace
expansion: Hara–Slade 1990, Fitzner–van der Hofstad 2017). The cases 3 ≤ d ≤ 10 were open
(Grimmett, *Percolation*, 2nd ed., pp. 14 and 202–203; Duminil-Copin, ICM 2018, Conjecture 1).

How it is proved. Kozma and Nitzan (arXiv:2401.12397, 2024) conjectured a family of *gluing inequalities* for
Bernoulli percolation on an arbitrary finite weighted graph and proved (their Theorem 6) that the weakest of them,
their Conjecture 3 ("near-one gluing"), implies θ(p_c) = 0 on ℤ^d for every d ≥ 2. This library proves
Kozma–Nitzan's **Conjecture 3** (`kozmaNitzan_conjecture3_holds`) — via a new **additive gluing inequality**
(`additiveGluing_holds`: if P(a ↔ b) ≥ 1 − t for every a ∈ A then P(o ↔ b) ≥ P(o ↔ A) − t; this is the additive
form implied by their Conjecture 1, and it implies Conjecture 3), which in turn is derived from a
**conditioned slack hierarchy** (`cshHolds`): a family of conditioned covariance inequalities for monotone functions
of a single open cluster, indexed by finite lists of auxiliary vertices and proved by induction on the list — and
hence, by Kozma–Nitzan's Theorem 6 (also formalised here, following §4 of their paper), θ(p_c) = 0 on ℤ^d for
every d ≥ 2 (the case d = 2 via Harris' θ(1/2) = 0 and Kesten's p_c(ℤ²) = 1/2, both formalised here).
Kozma–Nitzan's Conjectures 1 (multiplicative form), 2 and 4 are not proved or stated here.
The inputs of the hierarchy — the Harris inequality, the conditional association inequalities of
van den Berg–Häggström–Kahn (2006), the four functions (Ahlswede–Daykin) theorem, a decision-tree
Harris–Kleitman inequality (Gladkov 2024, Thm 3.2) — and everything Theorem 6 invokes (the Barsky–Grimmett–Newman
(1991) half-space theorem by the block construction of Grimmett's book, §7.3, and slab technology) are proved in the
library from Mathlib, so the final statement is unconditional and has no hypothesis other than `2 ≤ d`. Nothing new is
claimed about site percolation, other lattices or slabs (the Duminil-Copin–Sidoravicius–Tassion slab theorem is
formalised, as a literature input), or about continuity of θ as a function on [0,1] (the latter is equivalent by
standard facts that are not part of the formal statement).

**Author.** Justin Leder ([@jleder3](https://github.com/jleder3)).

Toolchain: Lean `leanprover/lean4:v4.32.0`; Mathlib commit `81a5d257c8e410db227a6665ed08f64fea08e997` (Mathlib's tag `v4.32.0`; pinned in
`lakefile.toml` and `lake-manifest.json`, every dependency there is a github.com URL at a full commit SHA; do not run `lake update`).

## Main formal statements

| Lean declaration | file | statement |
|---|---|---|
| `Percolation.Continuity.CSH.percolationContinuity_allDimensions` | `Percolation/Continuity/MainTheorem.lean` | θ_0(p_c(ℤ^d)) = 0 for every d ≥ 2 (`∀ d, 2 ≤ d → PercolationContinuity d`) |
| `Percolation.Continuity.CSH.percolationContinuity_three` | `Percolation/Continuity/MainTheorem.lean` | the case d = 3 (`PercolationContinuity 3`) |
| `Percolation.Continuity.CSH.kozmaNitzan_conjecture3_holds` | `Percolation/Continuity/MainTheorem.lean` | Kozma–Nitzan's Conjecture 3 (near-one gluing, uniformly in |A|) on every finite weighted graph |
| `Percolation.Continuity.CSH.additiveGluing_holds` | `Percolation/Continuity/MainTheorem.lean` | additive gluing on every finite weighted graph: if P(a ↔ b) ≥ 1 − t for all a ∈ A then P(o ↔ b) ≥ P(o ↔ A) − t (the additive form implied by Kozma–Nitzan's Conjecture 1; implies their Conjecture 3) |
| `Percolation.Continuity.CSH.cshHolds` | `Percolation/Continuity/MainTheorem.lean` | the conditioned slack hierarchy: nonnegativity of the conditioned covariance margin `cshMargin` for every monotone cluster functional, every decoy list and every pair of observers |
| `BondPercolation.percolation_continuity` | `Solution.lean` | comparator-checked form: `∀ d, 2 ≤ d → BondPercolation.PercolationContinuity d` (Mathlib-only definitions of `Challenge.lean`) |
| `BondPercolation.percolation_continuity_Z3` | `Solution.lean` | comparator-checked form, d = 3 |

Here `Percolation.Literature.PercolationContinuity d := theta (zdGraph d) 0 (criticalProbI d) = 0`
(`Percolation/Literature/CriticalContinuity.lean`) unfolds to Mathlib primitives as follows: sites of ℤ^d are
`Fin d → ℤ`; the nearest-neighbour graph `zdGraph d` is `SimpleGraph.hasse (Fin d → ℤ)` (adjacent iff the sites differ
by ±1 in exactly one coordinate); a configuration is a set ω ⊆ Sym2 (Fin d → ℤ) of open edges, distributed according to
Mathlib's product Bernoulli measure `ProbabilityTheory.setBernoulli (zdGraph d).edgeSet p`; the open cluster of x is
`{y | (SimpleGraph.fromEdgeSet ω).Reachable x y}`; `theta G x p` is the measure (as a real number) of the event that
this cluster is infinite; `criticalProb G x := sInf ({p | ∃ h : p ∈ [0,1], 0 < theta G x ⟨p,h⟩} ∪ {1})`; and
`criticalProbI d` is `criticalProb (zdGraph d) 0` regarded as a point of `[0,1]`.
`Percolation.Continuity.Statements.AdditiveGluing` and
`Percolation.Literature.KozmaNitzan2024_conjecture3` (=
`Percolation.Continuity.Statements.NearOneGluing`, by `Iff.rfl`) are the
two gluing statements over all finite weighted graphs (`Percolation/Continuity/Statements.lean`,
`Percolation/Literature/KozmaNitzanReduction.lean`); `Percolation.Continuity.CSH.CSHHolds`
(`Percolation/Continuity/CSH/Defs.lean`) is the conditioned slack hierarchy.

The repository is also laid out as a [Palomar](https://palomar-registry.org) submission: the short Mathlib-only
statement file `Challenge.lean` (namespace `BondPercolation`, every definition with a docstring giving its ordinary
meaning), its proved twin `Solution.lean` (same declarations, the two theorems
`BondPercolation.percolation_continuity (d : ℕ) (hd : 2 ≤ d)` and `BondPercolation.percolation_continuity_Z3` proved
by importing the library and transporting along `Iff.rfl`), the comparator configuration `comparator.json`, and the
metadata file `formalization.yaml`.

## Conventions

* `[cite: Key, locator]` at the end of a docstring marks a definition or statement taken from the literature; `Key`
  resolves in `references.bib`, `locator` is the theorem / page / equation there. A result from the literature is
  recorded as a named proposition `def AuthorYear_result : Prop := …` next to its citation and proved as
  `theorem AuthorYear_result_holds : AuthorYear_result` (docstrings call this "proof of" or "discharge of" the named
  statement); nothing from the literature is assumed.
* A bare bracketed label such as `[KestenPTM1982]` in a module's reference list is also a key of `references.bib`.
* `[folklore]` marks standard auxiliary facts (measurability bookkeeping, finite-graph lemmas) stated in the form needed here.
* Everything under `Percolation/Continuity/` is this work: declarations there without a `[cite:]` tag are new, and a
  `[cite:]` tag there points to the published statement a lemma re-proves or specialises, not to a source of its proof.
* `Percolation/Literature/` re-proves the results the argument imports from the literature (Harris, Kesten,
  Russo–Seymour–Welsh, Barsky–Grimmett–Newman, Grimmett–Marstrand slab technology, van den Berg–Häggström–Kahn,
  Gladkov, Kozma–Nitzan §§2–4), with Mathlib-style module docstrings; file and declaration names follow the source
  (`KozmaNitzanTheorem6…`, `HalfSpaceBGN…`, `BHK2006.…`).

## Building and checking

Install [elan](https://github.com/leanprover/elan); the pinned Lean toolchain is selected automatically from `lean-toolchain`.
About 13 GB of disk for Mathlib; 32 GB RAM recommended (cap parallelism with `LEAN_NUM_THREADS`).

```sh
lake exe cache get && lake build   # prebuilt Mathlib for the pinned commit, then the default targets: Percolation, Solution
lake env lean scripts/Axioms.lean  # prints the statement and the axioms of each main theorem
lake build Challenge               # optional, not a default target: the Palomar statement file (Mathlib-only; its two theorems have placeholder proofs by design, proved in Solution.lean)
```

Expected: no errors; the `sorry` token occurs 2 times in the repository (`Challenge.lean`: 2) — the deliberate placeholders of the Palomar statement file, which is checked against `Solution.lean` by the comparator;
no `axiom` declarations (0); every `#print axioms` line reads `[propext, Classical.choice, Quot.sound]`.
Recorded at this release: `lake build` from an empty `.lake/build` completed with exit code 0 in 6 min 6 s on a 128-core x86-64 Linux node, 0 errors, no `sorry` warning outside `Challenge.lean`; the full record (axiom listing verbatim, comparator run) is in [`AUDIT.md`](AUDIT.md).

CI: [`../.github/workflows/lean-projects.yml`](../.github/workflows/lean-projects.yml) builds this project on its pinned toolchain and runs the
Palomar acceptance check — [leanprover/comparator](https://github.com/leanprover/comparator) with a toolchain-matched `lean4export`, the
independent `nanoda` kernel and the `landrun` sandbox, at the registry's tool pins — on `comparator.json`; run it locally with
`bash ../.github/scripts/comparator-check.sh` from this directory (needs `git`, `go`, `cargo`, `jq`; Linux).

## Layout

```
Percolation/                   the formalisation: 247 Lean files (86892 non-blank lines together with the root module Percolation.lean, which imports the main-theorem module)
Percolation/Continuity/           this work: MainTheorem.lean (the 5 theorems of the table above and `cshAll`, the `Fin n` repackaging of `cshHolds`), Statements.lean (the gluing statements), OfGluing.lean
                                  (continuity from gluing via Kozma–Nitzan's Theorem 6), CSH/ (the conditioned slack hierarchy: Defs, the induction,
                                  AdditiveGluingOfCSH), AdditiveGluing/ (additive gluing from the surplus-transfer margin), CovTau/, HullPort/ and
                                  LowerTail/ (the conditioned covariance-transfer, marker-dominance and tree-Harris lemmas the induction step uses)
Percolation/Literature/           re-proved literature: Basic.lean (the model), CriticalContinuity.lean (θ, p_c, the statement), KozmaNitzan*.lean
                                  (§§2–4 of Kozma–Nitzan incl. Theorem 6), HalfSpace*/Flat*/Tall*/…(Barsky–Grimmett–Newman via Grimmett §7.3),
                                  Harris*/Kesten*/RSW* (d = 2), LatticeModels/ (product Bernoulli measures, boxes in ℤ^d)
Percolation/Util/Linter.lean      a linter option (unused-variable exemption for named ∀-binders) imported by the library files; no mathematics
Challenge.lean                    Palomar statement file (imports Mathlib only; namespace BondPercolation; its two theorems carry placeholder proofs by design)
Solution.lean                     the same declarations proved from the library
comparator.json, formalization.yaml   comparator configuration and Palomar registry metadata
summary.pdf, summary.tex        a 15-page guide to the proof (compiled PDF and LaTeX source; bibliography style amsplain-norepeat.bst): a reader's guide, not part of the checked artifact
scripts/Axioms.lean             statement / axiom listing for the main theorems
references.bib                  bibliography entries for the `[cite: Key, locator]` markers in the docstrings and for summary.tex (45 entries)
AUDIT.md                        what was checked on exactly these sources, and how to reproduce it
lakefile.toml, lean-toolchain, lake-manifest.json   build configuration and pins (package `PercolationContinuity`)
LICENSE, NOTICE
```

## Provenance and review status

The Lean sources in this repository — definitions, statements and proofs, together with `Challenge.lean`,
`Solution.lean` and the metadata — were written by an AI system (Anthropic's Claude models) working autonomously
under the direction of Justin Leder; no human wrote or edited the Lean code. Correctness rests on mechanical
checking: the Lean 4 kernel accepts every file under the pinned toolchain and Mathlib commit with no `sorry`
(outside the two deliberate placeholders of `Challenge.lean`), no added axioms and no unsafe code, and the main
theorems depend only on the standard axioms `propext`, `Classical.choice`, `Quot.sound` (see `AUDIT.md`; the
comparator additionally replays the compared proofs in the independent nanoda kernel). The work has not
yet been refereed by human mathematicians or by anyone independent of the author; the only review so far was
carried out by AI systems (adversarial reads of the formal statements and of the proof chain against the cited
literature). Mechanical checking does not cover whether the formal statements express the intended mathematics:
readers should satisfy themselves that the definitions in `Challenge.lean` (`zdGraph`, `bondPercolation`,
`openCluster`, `theta`, `criticalProb`, `PercolationContinuity`) state "θ(p_c) = 0 for nearest-neighbour Bernoulli
bond percolation on ℤ^d, d ≥ 2". The docstrings in the library were machine-written as working notes and only
mechanically filtered for release; they are not an exposition: the guide to the proof is [`summary.pdf`](summary.pdf), which was
drafted in the same way (by the AI system, under the author's direction) and has likewise not been independently refereed. This release fixes the exact machine-checked claim
publicly while independent examination is sought.

## Licence

Apache License 2.0 (`LICENSE`, SPDX `Apache-2.0`); copyright and attribution notice in `NOTICE`. The licence covers this repository, not the cited works; Lean 4, Mathlib and the other pinned dependencies are separate works under their own licences.
