<!-- SPDX-License-Identifier: Apache-2.0 -->
# Selected Proof Generalizer examples

This directory contains three selected candidate/client pairs from the NEW-PG study. The candidates are small Lean proof components; each client applies the candidate to a downstream example and retains positive, specialization, negative, and standard-axiom checks. The exact source provenance and dependency boundary are recorded in [`NOTICE.md`](NOTICE.md).

The files are source snapshots for inspection and comparison. They are not a claim that the original generation was successful, that an agent independently discovered the mathematics, or that the examples establish a general capability. The broader study remains incomplete, including the original cases 10–15.

The pairings are:

| Pair | Candidate | Client |
| --- | --- | --- |
| NPG-01 | affine error norm bound | observer-style downstream client |
| NPG-02 | scalar recurrence bound | norm-sequence downstream client |
| NPG-03 | shifted endpoint integral bound | concrete interval-integral client |
