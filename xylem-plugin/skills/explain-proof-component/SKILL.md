---
name: explain-proof-component
description: Explain one supplied Lean component from exact source and retained evidence, with separate formal, notation, source, review, and engineering statuses.
---

<!-- SPDX-License-Identifier: Apache-2.0 -->

# Explain one proof component v0.1.0

Read the component record, exact source, declaration capture, request, and receipts before writing. Choose one named component. Preserve its exact type, parent declaration, binders, assumptions, source revision, and evidence paths. Translate notation gradually; define technical words at first use; include a short derivation and a small valid illustration. Keep formal checking, source correspondence, notation conversion, explanation, independent review, and engineering applicability in separate fields.

The bundled example's completed page is `examples/compact-bounds/explanation-hS.md` and its packet is `examples/compact-bounds/explanation-hS.json`. It explains the leading boundaries `hS : IsCompact S` and `hSpos : ∀ y ∈ S, 0 < y`. Distinguish their full retained parent contexts from the assumptions used in each visible source argument. Recorded helper interfaces have historical summaries; generated helper proof terms and printed signatures are not bundled. Keep the explanation within these leading boundaries.

Before calling prose reviewed, send the packet and evidence to a separate review pass. If no independent pass is available, leave review as `pending_independent_review`.
