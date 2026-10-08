<!-- SPDX-License-Identifier: Apache-2.0 -->
# Compact coordinate-value bounds

## Mathematical result

Let `ι` be a finite index type and `K : Set (ι → ℝ)` be compact. Assume

```text
hpos : ∀ x ∈ K, ∀ i : ι, 0 < x i.
```

The parent goal is one common `ε` with `0 < ε < 1` and `ε ≤ x i ≤ ε⁻¹` for every `x ∈ K` and every coordinate `i`. Neither nonempty `K` nor a nonempty coordinate type is required.

The proof collects every coordinate value in

```text
S = ⋃ i : ι, (fun x : ι → ℝ => x i) '' K.
```

For each fixed `i`, coordinate evaluation `x ↦ x i` is continuous, so its image of `K` is compact. Because `ι` is finite, the union `S` is compact:

```text
hS : IsCompact S
```

If `y ∈ S`, then `y = x i` for some `x ∈ K` and `i ∈ ι`. The premise `hpos` therefore gives `0 < y`:

```text
hSpos : ∀ y ∈ S, 0 < y
```

Both recorded helper interfaces retain the parent context: finiteness of `ι`, compactness of `K`, and coordinatewise positivity, together with the definition of `S`. Their visible source arguments use different parts of that context: `hS` uses compactness and finiteness; `hSpos` uses coordinatewise positivity and membership in the coordinate-image union. An unused hypothesis can still be retained in an extracted callable interface. Neither interface was minimized. Neither argument needs `ι` or `K` to be nonempty.

The later bound uses positive lower bounds for values in `S` and for their reciprocals. The later witnesses `a`, `b`, and `ε` remain outside this page's extracted boundary; the account does not rely on a claim about attained extrema.

One illustration shows why `S` can be infinite even when the coordinate family is finite. With `K = [1,2] × [3,4]` and two coordinates, `S = [1,2] ∪ [3,4]`. This illustration explains the set construction; the quantified Lean argument supplies the proof.

## Recorded formal interfaces

The parent declaration is `OAI.Problem326.compact_positive_uniform_bounds`. Its exact signature and five binders are retained in [`../../capture/declarations.json`](../../capture/declarations.json). The recorded helper interfaces, attributed to historical checking summaries, are:

```text
hS:
∀ {ι : Type uIota} [Finite ι] {K : Set (ι → ℝ)},
  IsCompact K → (∀ x ∈ K, ∀ (i : ι), 0 < x i) →
  IsCompact (⋃ i, (fun x : ι → ℝ => x i) '' K)

hSpos:
∀ {ι : Type uIota} [Finite ι] {K : Set (ι → ℝ)},
  IsCompact K → (∀ x ∈ K, ∀ (i : ι), 0 < x i) →
  let S := ⋃ i, (fun x : ι → ℝ => x i) '' K;
  ∀ y ∈ S, 0 < y
```

Generated helper proof terms and printed-signature output are not bundled. These recorded strings and the parent source are inspectable, but their exact identity with historically generated helpers is not independently replayable from this package.

The source span and helper names are recorded in [`component-record.json`](component-record.json). The checked evidence is [`extraction-summary.json`](evidence/extraction-summary.json) and [`reproduction-receipt.json`](evidence/reproduction-receipt.json). The [explanation verification](evidence/review-corrected-explanations.json) passed source, mathematics, and interface checks. Generated Lean helper replay was not performed.

## Converter and evidence boundary

The included declaration projection has no expression trees. The current canonical converter therefore uses an **exact Lean-text fallback** for the affected fragments. This page is separately authored prose; it is not a converter rendering and does not establish semantic equivalence.

The graph input contains one module and one declaration with containment only. `premises_included: false` means dependency records were not supplied. The empty `premises` list and zero `USES_*` edge counts must not be read as a claim that the theorem has no dependencies. Source/dependency, containment, import, and conceptual/provenance links remain separate.

This example explains the coordinate-image union and its two leading boundaries: compactness of the union and positivity of every value in it.
