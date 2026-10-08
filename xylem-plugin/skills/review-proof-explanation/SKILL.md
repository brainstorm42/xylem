---
name: review-proof-explanation
description: Independently compare one explanation against its exact Lean statement and evidence; return pass, revise, or blocked without editing the proof.
---

<!-- SPDX-License-Identifier: Apache-2.0 -->

# Review one proof explanation v0.1.0

Read the packet, exact source, source hash, declaration capture, definitions, and completed receipts directly. Check the full name and revision; every binder and assumption; quantifiers, domains, strictness, and inequality directions; local definitions; and the distinction between a universal theorem and an illustration. Check that conventional display did not silently change the claim. Do not treat a notation conversion, dependency edge, or learner response as proof of semantic equivalence or applicability.

Return exactly one verdict: `pass`, `revise`, or `blocked`, with the field or sentence, evidence, smallest correction, and limits. `pass` means no discrepancy was found in the reviewed scope, not that the prose is formally certified. Never label a self-review independent.
