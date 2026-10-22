# Proof Generalizer provenance notice

The six Lean files in this directory were generated or assembled for the project's NEW-PG study. The candidate files retain extracted solver responses; the client files are evaluator artifacts, not solver responses. No direct third-party code copying was identified, and this release does not assert a human author, model identity, or independent mathematical originality for the generated material.

Each candidate imports only Mathlib. Each client imports its local `Candidate` file and Mathlib. Mathlib's own Apache-2.0 terms apply to the imported library. The donor statements were drawn from the project's `Ctrllib.EstimationError` material for NPG-01 and NPG-02, and from `Ctrllib.IntegratedEnergy` material for NPG-03; the public files do not copy those donor modules or import Ctrllib.

NPG-01 and NPG-03 each received one proof/API repair. NPG-02 received a transport-capture correction followed by one proof repair. The retained checks support the bounded demonstrations described in the public [evaluation status](../../../RESULTS-STATUS.md); they do not turn the raw generation into a pass or establish a broader theorem-discovery claim.
