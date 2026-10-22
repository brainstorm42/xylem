# Xylem and ProofBricks

A short reader guide · 22 October 2026

## Small useful steps

At its heart, a ProofBrick packages a formal proof and its supporting declarations[^1] with an informal, people-centred explanation. It lists the assumptions needed and resultant guarantees. Bricks formalized from pre-existing literature list the bibliographic source from which the analysis was derived. The goal is to preserve reasoning for reuse through consistency, linking and searchability.

Theorems thusly linked form nodes in a graph I call the **xylem**. This searchable graph allows researchers, human or agent, to trace dependencies and compare the structure of formal expressions independently of local variable names.

## Three connected views

A **formal dependency graph** records links between declarations. A **conceptual view** connects mathematical ideas and explanations. An **assurance view** connects claims to evidence and outstanding obligations.

Lean checks a formal proof against its statement and dependencies. Further review examines the faithfulness of that statement to the intended claim and the applicability of its assumptions. It also examines admitted claims and unproved steps in the proof and its dependencies. Independent checking should support that review without assuming it is infallible.

Recent research into modularization has decomposed selected proofs into named helpers and reconnected them. These interfaces let a reader inspect a supporting step separately and identify the assumptions required to reuse it.

A small worked example, *From strict comparisons to equality*, extracts two one-sided boundary inequalities from a continuous-function argument and recombines them into equality.

## Connections to proof motivation and reuse

**Proof Generalizer** explores the assumptions under which a proof remains valid, inspired by Gandhi, Tadipatri and Gowers’s *Automatically Generalizing Proofs and Statements*. In checked examples, specialization recovers the original theorem from the generalized statement. Researchers can inspect the assumptions relaxed or retained and recover the starting theorem as a special case.

**Technique Finder** draws on Gowers’s discussion of motivated proofs and move types. Its checked examples recognized a common storage-decay argument under changed notation and used retrieved declarations to obtain a norm-decay bound. When storage is bounded above and below by positive multiples of the squared norm, an exponential storage-decay estimate yields a norm estimate with half the decay rate. The contrast with qualitative convergence makes the quantitative assumptions needed for transfer explicit.

**Reuse Check** examines the replacement of duplicated reasoning with existing mathematical results. Selected square-root and product-norm examples preserved the original assumptions and conclusions while replacing duplicate arguments with shared lemmas. The resulting interfaces expose the conditions that must remain valid when a proof is reorganized.

## Research use

Researchers can use the linked record to inspect a candidate lemma’s assumptions before adapting it, trace its supporting arguments, and locate the source of an unresolved obligation. The experiments provide worked cases for comparing alternative decompositions and studying the cues that make a technique useful on a new problem.

## Further reading

- Anshula Gandhi, Anand Rao Tadipatri and Timothy Gowers, [Automatically Generalizing Proofs and Statements](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2025.12), ITP 2025.
- Timothy Gowers, [Finding a formal notion of a motivated proof](https://wtgowers.github.io/human-style-atp/motivatedproofs.html).

Companion note: *From strict comparisons to equality*.

[^1]: Usually written in Lean 4, also PVS (Prototype Verification System).
