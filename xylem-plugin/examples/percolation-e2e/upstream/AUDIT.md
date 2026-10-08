# Audit record

This file records the checks that were run on exactly the sources in this repository and how to reproduce them. Nothing here is part of
the trusted base: a reader can re-run everything below, and can run the [comparator](https://github.com/leanprover/comparator) against the
trusted statement file `Challenge.lean` (configuration `comparator.json`).

Toolchain: Lean `leanprover/lean4:v4.32.0`; Mathlib commit `81a5d257c8e410db227a6665ed08f64fea08e997` (the commit Mathlib's tag `v4.32.0` points to; pinned in
`lakefile.toml` and `lake-manifest.json`). Library name: `Percolation` (Lake package `PercolationContinuity`). Repository: <https://github.com/anthropics/formal-math/tree/main/percolation>.

Size: 251 Lean files, 97574 lines (87136 non-blank) — of which the library `Percolation/` + `Percolation.lean`: 248 files,
86892 non-blank lines; the rest is `Challenge.lean`, `Solution.lean`, `scripts/Axioms.lean`.

## How to reproduce

```sh
lake exe cache get                     # optional: prebuilt Mathlib for the pinned commit; otherwise Mathlib builds from source
lake build                             # default targets: Percolation Solution
lake env lean scripts/Axioms.lean      # statement + `#print axioms` of the 7 theorems listed below
lake build Challenge                 # the trusted statement file; expect only its deliberate sorry placeholders
bash ../.github/scripts/comparator-check.sh   # Palomar acceptance: comparator + lean4export + nanoda + landrun at the registry pins, on comparator.json
```

## Recorded results at this release

* `lake build` (Percolation, Solution, Challenge) from an empty `.lake/build`: exit code 0, 6 min 6 s on a 128-core x86-64 Linux node; 0 errors, 2 warnings; `declaration uses 'sorry'` warnings only in `Challenge.lean` (2 — the placeholder proofs of the statement file, by design) and none in `Percolation/` or `Solution.lean`.
* Occurrences of the `sorry` token outside comments: **2** (`Challenge.lean`: 2). Declarations of new axioms (`axiom …`) anywhere, counted on the sources with comments stripped: **0**.
* Axiom audit: every one of the 7 `#print axioms` lines below is exactly `[propext, Classical.choice, Quot.sound]` (checked by the release tool; a non-standard axiom or `sorryAx` fails the release).
* post-check `comparator`: OK in 256 s — Lean default kernel accepts the solution; Your solution is okay!; comparator rc=0; real	4m16.617s

### `#print axioms` for the 7 main / compared theorems (`lake env lean scripts/Axioms.lean`), verbatim

```
'Percolation.Continuity.CSH.percolationContinuity_allDimensions' depends on axioms: [propext, Classical.choice, Quot.sound]
'Percolation.Continuity.CSH.percolationContinuity_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'Percolation.Continuity.CSH.kozmaNitzan_conjecture3_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'Percolation.Continuity.CSH.additiveGluing_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'Percolation.Continuity.CSH.cshHolds' depends on axioms: [propext, Classical.choice, Quot.sound]
'BondPercolation.percolation_continuity' depends on axioms: [propext, Classical.choice, Quot.sound]
'BondPercolation.percolation_continuity_Z3' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Comparator

`comparator.json` compares `Solution` against the Mathlib-only statement file `Challenge` for the theorems
`BondPercolation.percolation_continuity`, `BondPercolation.percolation_continuity_Z3`, with permitted axioms `propext`, `Quot.sound`, `Classical.choice` and the
`nanoda` replay enabled. The formal-math CI script `../.github/scripts/comparator-check.sh` pins comparator
`575674928e239f5bc452aab72d1dd7b0f1326494`, nanoda `68d5ca9db226849b41a6fff59d796ff19d0a8840`, landrun `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4`
(the Palomar registry's verifier pins) and takes `lean4export` at the release tag matching `lean-toolchain`; it must print `Your solution is okay!`.
