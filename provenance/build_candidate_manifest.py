#!/usr/bin/env python3
"""Generate the exact tracked-file inventory for the private candidate archive."""

from __future__ import annotations

import argparse
import copy
import gzip
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import tarfile


ROOT = Path(__file__).resolve().parents[1]
MANIFEST_REL = "provenance/corrected-release-manifest.json"


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def tracked_payload(root: Path) -> list[str]:
    raw = subprocess.check_output(
        ["git", "ls-files", "--cached", "--stage", "-z"], cwd=root
    ).decode("utf-8")
    paths = []
    for record in raw.split("\0"):
        if not record:
            continue
        metadata, path = record.split("\t", 1)
        mode = metadata.split(" ", 1)[0]
        if path == MANIFEST_REL:
            continue
        if mode not in {"100644", "100755"}:
            raise SystemExit(f"tracked payload is not a regular file: {path} (mode {mode})")
        paths.append(path)
    missing = [path for path in paths if not (root / path).is_file()]
    if missing:
        raise SystemExit("tracked payload files missing from checkout: " + ", ".join(missing[:5]))
    return sorted(paths)


def build_manifest(root: Path) -> dict:
    payload = tracked_payload(root)
    return {
        "schema": "xylem-ctrllib-release-inventory/v1",
        "version": "0.1.0",
        "inventory_scope": (
            "all tracked regular files in the final Git tree except this manifest"
        ),
        "candidate_archive": {
            "format": "tar.gz",
            "source_selection": (
                "git archive of the final tracked tree with materialized Git LFS payloads"
            ),
            "includes_manifest": True,
            "manifest_path": MANIFEST_REL,
            "payload_member_rule": (
                "archive regular-file members equal this manifest's files plus "
                "the manifest itself; ignored and untracked files are excluded"
            ),
        },
        "file_count": len(payload),
        "files": [
            {
                "path": path,
                "bytes": (root / path).stat().st_size,
                "sha256": sha256(root / path),
            }
            for path in payload
        ],
    }


def manifest_bytes(root: Path) -> bytes:
    return (json.dumps(build_manifest(root), indent=2, ensure_ascii=False) + "\n").encode(
        "utf-8"
    )


def write_manifest(root: Path, output: Path) -> int:
    output.parent.mkdir(parents=True, exist_ok=True)
    manifest = build_manifest(root)
    output.write_bytes((json.dumps(manifest, indent=2, ensure_ascii=False) + "\n").encode("utf-8"))
    print(json.dumps({"manifest": str(output), "file_count": manifest["file_count"]}))
    return 0


def require_clean_tree(root: Path) -> None:
    status = subprocess.check_output(
        ["git", "status", "--porcelain", "--untracked-files=all"], cwd=root
    ).decode("utf-8")
    if status:
        raise SystemExit(
            "final packaging requires a clean working tree; regenerate, commit, "
            "and rerun after reviewing:\n" + status
        )


def lfs_paths(root: Path) -> set[str]:
    """Return LFS paths in HEAD, if this checkout uses Git LFS."""
    tracked_attributes = []
    tracked = subprocess.check_output(["git", "ls-files", "-z"], cwd=root)
    for raw_path in tracked.split(b"\0"):
        if not raw_path:
            continue
        path = raw_path.decode("utf-8")
        if Path(path).name == ".gitattributes":
            tracked_attributes.append(root / path)
    if not any(
        "filter=lfs" in path.read_text(encoding="utf-8") for path in tracked_attributes
    ):
        return set()
    try:
        output = subprocess.check_output(
            ["git", "lfs", "ls-files", "--name-only"], cwd=root, text=True
        )
    except FileNotFoundError as exc:
        raise SystemExit(
            "this candidate contains Git LFS rules, but the git-lfs executable is unavailable"
        ) from exc
    return {line for line in output.splitlines() if line}


def require_materialized(path: Path) -> None:
    with path.open("rb") as stream:
        prefix = stream.read(128)
    if prefix.startswith(b"version https://git-lfs.github.com/spec/v1"):
        raise SystemExit(
            f"Git LFS payload is not materialized in the worktree: {path}; "
            "run `git lfs checkout` and rerun"
        )


def create_archive(root: Path, output: Path) -> None:
    output.parent.mkdir(parents=True, exist_ok=True)
    lfs = lfs_paths(root)
    for path in lfs:
        require_materialized(root / path)
    temporary = tempfile.NamedTemporaryFile(
        prefix=f".{output.name}.", suffix=".tmp", dir=output.parent, delete=False
    )
    temporary_path = Path(temporary.name)
    try:
        with temporary:
            archive = subprocess.Popen(
                [
                    "git",
                    "archive",
                    "--format=tar",
                    "--prefix=xylem-private-candidate/",
                    "HEAD",
                ],
                cwd=root,
                stdout=subprocess.PIPE,
            )
            try:
                if archive.stdout is None:
                    raise SystemExit("git archive did not provide a readable stream")
                with tarfile.open(fileobj=archive.stdout, mode="r|") as source:
                    with gzip.GzipFile(
                        fileobj=temporary, mode="wb", compresslevel=9, mtime=0
                    ) as compressed:
                        with tarfile.open(fileobj=compressed, mode="w|") as destination:
                            for member in source:
                                relative = member.name.removeprefix(
                                    "xylem-private-candidate/"
                                )
                                if member.isfile() and relative in lfs:
                                    materialized = copy.copy(member)
                                    path = root / relative
                                    materialized.size = path.stat().st_size
                                    with path.open("rb") as stream:
                                        destination.addfile(materialized, stream)
                                    continue
                                stream = source.extractfile(member) if member.isfile() else None
                                try:
                                    destination.addfile(member, stream)
                                finally:
                                    if stream is not None:
                                        stream.close()
            finally:
                archive.stdout.close()
            return_code = archive.wait()
            if return_code:
                raise SystemExit(f"git archive failed with exit code {return_code}")
        os.replace(temporary_path, output)
    except BaseException:
        temporary_path.unlink(missing_ok=True)
        raise


def finalize(root: Path, manifest: Path, archive: Path) -> int:
    require_clean_tree(root)
    expected = manifest_bytes(root)
    actual = manifest.read_bytes()
    if actual != expected:
        raise SystemExit(
            "candidate manifest is stale for the current tracked tree; run "
            "build_candidate_manifest.py, review the diff, commit it, and rerun"
        )

    create_archive(root, archive)
    validator = root / "provenance" / "validate_candidate_archive.py"
    result = subprocess.run(
        [
            sys.executable,
            str(validator),
            "--archive",
            str(archive),
            "--manifest",
            str(manifest),
            "--root",
            str(root),
        ],
        cwd=root,
        check=False,
    )
    if result.returncode:
        raise SystemExit("candidate archive validation failed")
    print(
        json.dumps(
            {
                "status": "PASS",
                "manifest": str(manifest),
                "archive": str(archive),
                "final_head": subprocess.check_output(
                    ["git", "rev-parse", "HEAD"], cwd=root, text=True
                ).strip(),
                "validator": "PASS",
            },
            indent=2,
        )
    )
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--output", type=Path, default=ROOT / MANIFEST_REL)
    parser.add_argument(
        "--finalize-archive",
        type=Path,
        help=(
            "require a clean committed tree, regenerate the archive from HEAD, "
            "and run the exact-membership/hash validator before reporting PASS"
        ),
    )
    args = parser.parse_args()
    root = args.root.resolve()
    output = args.output.resolve()
    if args.finalize_archive:
        return finalize(root, output, args.finalize_archive.resolve())
    return write_manifest(root, output)


if __name__ == "__main__":
    raise SystemExit(main())
