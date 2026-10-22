<!-- SPDX-License-Identifier: Apache-2.0 -->
# Evaluation status

This page records the checked status of selected proof-reading and technique-selection work. It is a concise guide to the public release, not a benchmark score or a replacement for the formal statements and retained records.

## Checked tracks

| Track | Current status | Public interpretation |
| --- | --- | --- |
| Reuse and bound checks (RC/BC) | The selected `ProdNorm` replay and two startup-ramp adapters were accepted at the reviewed source boundary; a fixed-parameter interval certificate was also accepted. | Bounded source-preserving reuse and a fixed certificate, not generalized automated bound inference or an application result. |
| Proof Generalizer (PG) | Three repaired candidate/client demonstrations passed positive, specialization, negative, and standard-axiom checks; a separate-import case passed. The selected source pairs are included with provenance in the [public examples](xylem-plugin/examples/proof-generalizer/README.md). Raw generation remained nonpass, and original cases 10–15 remain incomplete. | Bounded evidence that proposed generalizations can be tested against a starting result, not a completed study or a generalization claim. |
| Technique Finder (TF) | Two bounded Sol-selector cases were accepted: storage-decay-to-norm transfer and rejection when qualitative assumptions were insufficient. | Bounded evidence about matching a move to its hypotheses, not a held-out capability score, library gain, or original Pro-completion claim. |

The BC certificate fixes the scalar parameters `m = k = 1`. For every real `β` in `[1/5, 1/4]`, it proves the storage-side condition `0 < β < min 1 1` and feeds that same arbitrary `β` into the unchanged strict-decay theorem. The caller still supplies `τ`, `d`, `T`, `κ`, `μ`, the ramp inequalities, the tail condition, and the state. The certificate rejects `β = 1` and a falsely widened interval; it does not prove the ramp inequalities, trajectory existence, stability beyond the existing theorem, or hardware behavior.

The selected startup-ramp roots are included with their 37-module Ctrllib import closure, together with the fixed-parameter BC pilot. The two RC roots and the BC pilot were checked against the public Lean 4.34.0 and pinned Mathlib revision. The [BC pilot](ctrllib/Ctrllib/ControllerScalarPilotV2.lean) is a fixed-parameter interval certificate, not generalized automated bound inference or a physical-control result.

## Public source

The directly inspectable formal slice in this release includes the [standalone `ProdNorm` helper](ctrllib/Ctrllib/ProdNorm.lean), the [planar module documentation and closure](ctrllib/HANDBOOK-PLANAR.md), the [startup-ramp supplied-tail root](ctrllib/Ctrllib/ComStartupRampSuppliedTailNorm.lean), the [endpoint adapter root](ctrllib/Ctrllib/ComStartupRampEndpointAdapter.lean), the [BC pilot](ctrllib/Ctrllib/ControllerScalarPilotV2.lean), and the [selected Proof Generalizer examples](xylem-plugin/examples/proof-generalizer/README.md), alongside the [Ctrllib source guide](ctrllib/README.md) and the repository's [release scope](RELEASE-SCOPE.md). Those files link the source, assumptions, and provenance for the material that is actually included.

The RC, BC, PG, and TF entries above summarize selected checks whose private prompts, evaluator records, source packets, and receipts are not included in this public package. A result not linked from the public source and provenance pages remains outside the publication scope.

## Scholarly context

The Proof Generalizer track is influenced by [Automatically Generalizing Proofs and Statements](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2025.12), and the Technique Finder track by Gowers's [Motivated proofs](https://wtgowers.github.io/human-style-atp/motivatedproofs.html). These are source influences only. Xylem does not claim affiliation, reproduce either study's evaluation protocol, or implement the paper's algorithm.
