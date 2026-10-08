<!-- SPDX-License-Identifier: Apache-2.0 -->
# Xylem v0.1.0 — ProofBricks technical report

Xylem provides bounded statement inspection, graph navigation, and MCP. ProofBricks supplies statement rendering, component checking summaries, and mathematical explanations.

## 1. Purpose and scope

This package lets a reader inspect a captured Lean declaration, its source location, and labelled graph records. It also carries an experimental decomposition record and an authored explanation of two leading proof boundaries. The navigator and decomposition evidence remain separate surfaces.

The supplied example is `OAI.Problem326.compact_positive_uniform_bounds`. The bundled projection keeps the exact theorem signature, all five binders, conclusion text, source range, and recorded axioms. It does not include proof terms, expression trees, or premise records. The CompactBounds graph therefore contains setup evidence only: one module, one declaration, and a `DECLARED_IN` containment edge.

| Surface | What this package demonstrates | What it does not establish |
| --- | --- | --- |
| Navigator | repository-relative build, search, context, and optional MCP over the supplied graph | proof-dependency navigation for this projection |
| BrickConverter | exact statement retention and exact Lean-text fallback for tree-free fragments | semantic conversion or source equivalence |
| Decomposition | checked `hS` and `hSpos` leading boundaries from the supplied receipts | automatic helper-to-graph integration or full theorem decomposition |
| Explanation | a mathematical account of the shared coordinate-value set | a new theorem, reuse benefit, or application result |

## 2. CompactBounds mathematics

Let `ι` be a finite index type and let `K : Set (ι → ℝ)` be compact. Assume

```text
hpos : ∀ x ∈ K, ∀ i : ι, 0 < x i.
```

Define the set of all coordinate values by

```text
S = {x i | x ∈ K, i ∈ ι}
  = ⋃ i : ι, (fun x : ι → ℝ => x i) '' K.
```

For a fixed `i`, the coordinate map `x ↦ x i` is continuous. Its image of `K` is therefore compact. Finiteness of `ι` makes the union of those coordinate images compact, which is the recorded fact `hS : IsCompact S`.

If `y ∈ S`, then `y = x i` for some `x ∈ K` and `i ∈ ι`. The hypothesis `hpos` gives `0 < x i`, and hence `0 < y`. This is the recorded fact `hSpos : ∀ y ∈ S, 0 < y`.

Both recorded helper interfaces retain the full parent context: finite index type, compactness, positivity, and the definition of S. The visible `hS` argument uses finiteness and compactness; the visible `hSpos` argument unpacks membership in S and uses positivity. These are different argument roles, not minimized helper signatures. Neither argument requires nonemptiness.

The later bound uses positive lower bounds for values in `S` and for their reciprocals, then chooses `ε` below those bounds and below `1`. This report does not describe those quantities as attained extrema, and the later `a`, `b`, `ε`, and final-bound steps remain outside the extracted component scope.

One illustration is enough to show the shape of `S`. Take `K = [1,2] × [3,4]` with two coordinates. Then `S = [1,2] ∪ [3,4]`: the set of values in either coordinate is infinite, while the coordinate family is finite. The illustration supports the notation; the Lean statement supplies the quantified proof.

The source fixture is [`examples/compact-bounds/proof/CompactBoundsExplicitResolved.lean`](examples/compact-bounds/proof/CompactBoundsExplicitResolved.lean), adapted from the attributed `openai/math` revision recorded in [`examples/compact-bounds/third_party/openai-math/NOTICE.md`](examples/compact-bounds/third_party/openai-math/NOTICE.md).

## 3. Extracted components and interfaces

The parent statement is retained exactly in [`capture/declarations.json`](capture/declarations.json). Its five binders are `ι`, `[Finite ι]`, `K`, `hK`, and `hpos`, followed by the uniform positive-box conclusion. The capture's `premises` field is empty because dependency records were not supplied; it is not evidence that the theorem has no dependencies.

The historically recorded helper interfaces are:

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

These signatures preserve the full context, including parameters that may not be minimal for an isolated mathematical lemma. They are recorded extraction summaries, not an automatic minimization result. Generated helper proof terms and printed signatures are not bundled, so this package does not provide a self-contained fresh replay of those helper interfaces. The exact source span, helper names, and checked receipts are linked from [`examples/compact-bounds/component-record.json`](examples/compact-bounds/component-record.json), [`examples/compact-bounds/evidence/extraction-summary.json`](examples/compact-bounds/evidence/extraction-summary.json), and [`examples/compact-bounds/evidence/reproduction-receipt.json`](examples/compact-bounds/evidence/reproduction-receipt.json).

The current converter receives a tree-free declaration projection. Its output therefore retains exact Lean text as an **exact Lean-text fallback**. The prose above is separately authored and is not converter output or source-equivalence evidence.

## 4. Navigation relationships

The package keeps four relationship kinds distinct:

| Relationship | Meaning | Present in the bundled graph? |
| --- | --- | --- |
| Dependency | `USES_IN_TYPE` or `USES_IN_PROOF` records a named formal occurrence in supplied capture data | no; premise records were unavailable |
| Containment | `DECLARED_IN` places a declaration in its captured module | yes; one edge |
| Import | `IMPORTS` records a module-import relation from the supplied DOT input | no asserted import edge |
| Conceptual/provenance | authored explanation, source locator, review receipt, or package membership | yes in records; never treated as a proof edge |

The canonical CLI and MCP expose `status`, `search`, `context`, bounded dependency traversals, and report-only `similar` among the existing operations. In this example the status output says that dependency data is `unavailable`; the zero `USES_*` edge counts describe only the indexed graph. The `context` result carries the same declaration-level availability state. The `dependencies` and `dependents` results carry a structured `dependency_data` object next to their `items` list, so an empty list is never the only signal. The review JSON and generated HTML carry the same state for direct proof/type dependency sections and bounded impact. `similar` remains experimental and is not part of the first-use claim.

The bundled `mcp/bundled_server.py` and `runtime/bundled_converter.py` are older example-scoped regression surfaces. The plugin-linked provider is the canonical runtime under `canonical/`, and its MCP is started by [`canonical/mcp.sh`](canonical/mcp.sh) for CompactBounds. The separate [Ctrllib example](examples/ctrllib-e2e/README.md) supplies genuine captured dependency navigation and an explicitly configured MCP runner.

## 5. Reproduction and verification

Run every command from the package root. The checked first-use environment is macOS with Python 3.12.14, PyYAML 6.0.3, and MCP 2.2.0 already available. The package declares `PyYAML==6.0.3` and `mcp==2.2.0` in [`canonical/requirements.txt`](canonical/requirements.txt). The commands below do not install packages.

```sh
PYTHON=/path/to/python3.12
"$PYTHON" canonical/run.py build
"$PYTHON" canonical/run.py query status --json
"$PYTHON" canonical/run.py query search compact --json
"$PYTHON" canonical/run.py query dependencies OAI.Problem326.compact_positive_uniform_bounds --json
"$PYTHON" canonical/run.py query dependents OAI.Problem326.compact_positive_uniform_bounds --json
"$PYTHON" canonical/run.py query review OAI.Problem326.compact_positive_uniform_bounds --json
"$PYTHON" canonical/run.py convert render-statement \
  --declaration OAI.Problem326.compact_positive_uniform_bounds --json
```

The expected status includes one declaration, one `DECLARED_IN` edge, no asserted `USES_IN_TYPE`/`USES_IN_PROOF` edges, and:

```json
"declaration_dependency_data": {
  "status": "unavailable",
  "counts": {"unavailable": 1}
}
```

The search returns the named CompactBounds declaration. The converter retains all five binders and reports exact-text fallback for the tree-free fragments; it does not claim formal checking or semantic equivalence.

For the dependency-facing commands, inspect `dependency_data.status` and `dependency_data.note` before interpreting `items`. The bundled projection reports `unavailable`; a supplied empty capture would report `empty`, a partial capture `partial`, and a complete capture `captured`.

MCP is optional after the CLI result is useful. From the same package-root working directory, run:

```sh
XYLEM_PYTHON="$PYTHON" canonical/mcp.sh
```

This is a foreground stdio server for the plugin-linked `xylem_query` tool. The supplied [`.mcp.json`](.mcp.json) points to the same relative launcher for a host that supports MCP configuration. `canonical/mcp.sh` prefers `.venv/bin/python`, accepts `XYLEM_PYTHON` or `PROOFBRICKS_PYTHON`, checks the two direct pins, and never installs packages.

The Air check covers an isolated Python installation, CLI/MCP/converter workflow, and full 123-module public source-first regeneration; see [Air verification](../provenance/AIR-CONSUMER-CHECK.md). Targeted current runtime-label and explanation checks are in [Correction check](../provenance/CORRECTION-CHECK.md). Windows remains untested.

## 6. Limitations and open work

- The projection omits proof terms, expression trees, and dependency records.
  `premises_included: false` is surfaced as unavailable data, not as a claim of
  no dependencies.
- The CompactBounds graph is setup/statement-inspection evidence only. Automatic mapping from
  extracted helpers to the canonical graph remains future work.
- The decomposition receipts cover only the native `hS` and `hSpos` leading
  boundaries. General decomposition, helper minimization, and proof completion
  remain deferred.
- The canonical converter's exact-text fallback retains source text; it does
  not prove a mathematical translation or source equivalence.
- Fresh replay of the historical CompactBounds helper extraction requires its
  separate Lean 4.34.1 environment and generated-helper evidence, which is not
  bundled. Public Ctrllib source-first regeneration instead uses the shipped
  extractor and pinned Lean 4.34.0 dependency procedure.
- The adapted OpenAI Math fixture keeps its Apache-2.0 attribution and license
  beside the source.
- Windows execution is untested.

Current verification is recorded in the linked Air and correction checks. Source notices and exact fixture attribution remain beside the relevant files.
