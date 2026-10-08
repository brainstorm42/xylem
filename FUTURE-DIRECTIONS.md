# Future directions

Xylem's next steps build on the focus of v0.1.0: helping people understand formal mathematics, follow the evidence behind a claim, and find a useful next step in a proof or explanation.

This document distinguishes v0.1.1 work in progress, planned improvements, requested integrations, and longer-term research. Release notes remain the record of what a published version provides. Teaching resources are curated separately so readers can choose material that fits their background and goals.

## v0.1.1 work in progress: freshness and reusable contracts

Work toward v0.1.1 uses a checked timestamp-freshness example, including a theorem, counterexample, and repair, to develop reusable contract review. Integration into Xylem is in progress. The next goal is to make that work useful in a repeatable review: a reader should be able to inspect a contract, see what changed, and understand which conclusions need attention.

### Contract snapshots and change review

Planned reusable snapshots will preserve the information needed to interpret and compare a mathematical interface:

- **Exact statements and ordered binders.** Retain the formal statement, assumptions, and binder order, including dependencies between parameters.
- **Definition meaning.** Retain the defining terms and referenced definitions that give the statement its meaning. A familiar name should lead back to the definition used in that snapshot.
- **Proof changes.** Show changes to the proof separately from changes to the statement it establishes.
- **Dependency changes.** Show added, removed, or changed dependencies with evidence for each relation.
- **Explanatory changes.** Track prose and presentation separately so readers can identify a revised explanation alongside the formal result it describes.

The intended comparison should let a reader answer: What is the claim now? Which assumptions changed? Which definitions changed? What was rechecked? Which explanation should I revisit?

### Reverse impact with evidence

Planned reverse-impact views will follow recorded dependencies from a changed item to the contracts and explanations that use it. Each reported impact should include its path and supporting evidence, with direct and transitive relationships clearly identified. Missing source, incomplete extraction, or an unavailable check should produce an explicit **unknown** result.

### Small control-theory and robotics examples

Timestamp freshness and bounded command age provide a focused starting point for interface contracts. Small examples should make the clock assumptions, timestamp relationships, age bound, and conclusion easy to inspect together.

A useful example should include:

1. A readable contract and its exact formal statement.
2. A counterexample showing why an assumption matters.
3. The repaired statement and its replayable check.
4. A snapshot comparison showing what the repair changed.
5. An evidence-linked account of the downstream claims that need review.

These examples will help readers connect the mathematical guarantee to the assumptions a control or robotics system must satisfy.

## Planned improvements to mathematical navigation

### Formal, conceptual, and explanatory graphs

Readers need several views of the same mathematics:

- A **formal graph** records dependencies supported by formal artifacts and their checks.
- A **conceptual graph** connects mathematical ideas, reusable constructions, and interfaces.
- An **explanatory graph** organizes a route through the material for a particular reader or question.

Xylem should keep these relations distinct while linking them through stable source references. Each edge should say what relationship it represents and show the evidence or interpretation behind it.

### Useful boundaries with evidence

A useful mathematical boundary packages enough assumptions and conclusions for a reader to reason about a component and reuse it. Planned views should expose those assumptions, the guarantee, the supporting proof, and the surrounding dependencies. Readers should be able to open the source at each step and judge whether the boundary fits their task.

### Converters and notation continuity

Future converter work should preserve identifiers, ordered binders, mathematical notation, references, and source locations across supported representations. A reader moving between a source, graph, contract, and explanation should be able to recognize the same mathematical object. Conversion reports should make preserved information and unresolved interpretation visible.

## Requested addition: Google Gemini integration

**Status: requested.** Gemini support would give readers another provider choice, including people whose institutions already offer access to Google AI tools.

The proposed design starts with a provider-neutral interface for Xylem's supported workflows. A Gemini adapter should use the same evidence and output contracts as other providers, with provider-specific capabilities recorded explicitly.

Before implementation, resolve four practical questions:

1. **Access and audience.** Identify the supported Google service, account type, regions, age requirements, and institutional permissions for a third-party Xylem integration.
2. **Data and privacy.** Show which provider receives the selected source material, which data leaves the user's environment, and which retention and training terms apply to that service and tier.
3. **Quota and cost.** Show the selected model, applicable limits, billing route, and expected cost before a paid workflow begins. Keep provider changes explicit.
4. **Workflow parity.** Test the same representative tasks across supported providers: source-grounded explanation, contract inspection, evidence links, structured outputs, and handling of incomplete input. Report the tested capability and any remaining gaps.

### Educational access and API access

Institution-provided Gemini app access, a personal Google AI subscription, and Gemini API access have separate eligibility, administration, quotas, and terms. Google documents [Gemini access through school accounts](https://support.google.com/gemini/answer/14620100?co=DASHER._Family%3DEducation&hl=en) separately from [Gemini API billing](https://ai.google.dev/gemini-api/docs/billing). A proposed Xylem connection should verify the entitlement for the service it actually uses.

Review the [Gemini API terms](https://ai.google.dev/gemini-api/terms) against the intended audience before choosing this route. As checked on 2026-10-08, the terms effective 2026-03-23 require API users to be 18 or older and restrict API clients directed toward or likely to be accessed by under-18s. This makes audience and service selection an early design decision for educational use.

## Longer-term research: choosing mathematical box size

Finding a good size for a reusable mathematical component remains an open research direction. Future work can examine how authors split proofs, package assumptions, choose interfaces, and reuse constructions across projects. Comparing those choices may help explain when a small lemma, a larger theorem, or an intermediate contract makes the mathematics easier to understand and maintain.

This mathematical box-size archaeology is deferred research. It can draw on evidence from practical contract examples once those examples are available.

## Limitations

- v0.1.1 integration is still in progress. The checked freshness example covers a specific theorem, counterexample, and repair; release-level capability depends on completed integration, testing, and publication.
- Dependency and change reports are bounded by the available artifacts and checks. A definition change may require mathematical review, and incomplete evidence remains unknown.
- Gemini integration is a requested addition and has not been implemented. A campus account or app subscription alone does not establish free API quota, third-party integration rights, or availability at a particular institution.
- Provider access, prices, quotas, and terms can change. Check the official documentation and the actual account before enabling an integration.
