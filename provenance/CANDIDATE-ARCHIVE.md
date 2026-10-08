<!-- SPDX-License-Identifier: Apache-2.0 -->
# Private candidate archive

The corrected release manifest is the exact inventory for the private
candidate. It hashes every tracked regular file except itself; the archive
includes the manifest as an unhashed self-describing sidecar. Ignored files,
generated working databases, Python caches, and the old dirty Xylem checkout
are not package inputs.

First regenerate the manifest after the last code/data/receipt change, review the
diff, and commit it:

```sh
python3 provenance/build_candidate_manifest.py
```

Only after that commit, run the aggregate finalization command from the
repository root:

```sh
python3 provenance/build_candidate_manifest.py \
  --finalize-archive /tmp/xylem-private-candidate.tar.gz
```

The aggregate command requires a clean working tree, recomputes the manifest
from the exact tracked payload, creates the archive from `HEAD`, and invokes
the validator before it reports `PASS`. If the tree uses Git LFS, the command
replaces the archive's LFS pointer members with the materialized worktree
payloads; run `git lfs checkout` first. A stale manifest, unmaterialized LFS
payload, stale archive, hash mismatch, membership drift, or broken link
therefore cannot be reported as a successful final package. To inspect an
already-created archive without regenerating it, run:

```sh
python3 provenance/validate_candidate_archive.py \
  --archive /tmp/xylem-private-candidate.tar.gz \
  --manifest provenance/corrected-release-manifest.json
```

The validator checks exact archive membership, every listed byte count and
SHA-256, the archived manifest, and all relative Markdown links. The candidate
remains private; the `release` remote has a `no_push://` URL and is not a
publication target.
