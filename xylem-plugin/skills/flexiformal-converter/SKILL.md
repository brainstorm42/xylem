---
name: flexiformal-converter
description: Render complete captured Lean statements while separating notation and formal-check scope.
---
<!-- SPDX-License-Identifier: Apache-2.0 -->
# Flexiformal converter v0.1.0

Run the packaged canonical converter from `xylem-plugin`:

```sh
"$PYTHON" canonical/run.py convert render-statement \
  --declaration OAI.Problem326.compact_positive_uniform_bounds --json
```

For Ctrllib supply `--config examples/ctrllib-e2e/xylem-e2e-config.json` before `convert` and select `Ctrllib.pointMass_tendsto_zero`. Retain all binders and exact signatures. Tree-free fragments use exact Lean-text fallback. Statement rendering keeps `acceptance_status: not_assessed`; it does not check rendered output formally or establish source equivalence.

`round-trip` schema 2 reports `ir_round_trip` and `check_scope: normalized_ir_equality`: parser/render/parser IR equality only. The former `semantic_round_trip` field is removed. `check` schema 2 reports `check_scope: existing_declaration_check` and `checks_passed`; its Lean gate checks the named existing declaration, while the rendered output is hashed but is not submitted to that gate. Both keep acceptance unassessed and report `generated_output_formally_checked: false` and `source_equivalence_checked: false`. Use the exit code and scoped check status, not a semantic acceptance label. The older `runtime/bundled_converter.py` is an example regression adapter.
