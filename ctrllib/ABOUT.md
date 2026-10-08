<!-- SPDX-License-Identifier: Apache-2.0 -->
# Ctrllib source organization

The umbrella imports 122 modules; `AllocationSignConvention` is separately importable. The extractor includes that standalone module so full extraction covers all 123 source modules. Dependency revisions and Lean 4.34.0 are pinned in the package configuration.

Use [subject navigation](SUBJECT-INDEX.md) to find mathematical topics, [rover theorem navigation](ROVER-PROVISIONAL.md) for geometry/timing/clearance, and [public regeneration](../xylem-plugin/examples/ctrllib-e2e/REGENERATE-FULL.md) to build and extract into an external output directory.
