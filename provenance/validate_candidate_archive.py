#!/usr/bin/env python3
"""Validate a private candidate archive against the tracked-file inventory."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import posixpath
import re
import subprocess
import tarfile
from urllib.parse import unquote


MANIFEST_REL = "provenance/corrected-release-manifest.json"
LINK_RE = re.compile(r"\[[^\]]*\]\(([^)]+)\)")
SCHEME_RE = re.compile(r"^[A-Za-z][A-Za-z0-9+.-]*:")


def digest_stream(stream) -> tuple[int, str]:
    digest = hashlib.sha256()
    size = 0
    while block := stream.read(1024 * 1024):
        size += len(block)
        digest.update(block)
    return size, digest.hexdigest()


def tracked_payload(root: Path) -> set[str]:
    raw = subprocess.check_output(
        ["git", "ls-files", "--cached", "-z"], cwd=root
    ).decode("utf-8")
    return {path for path in raw.split("\0") if path and path != MANIFEST_REL}


def link_target(raw: str) -> str | None:
    target = raw.strip()
    if target.startswith("<") and ">" in target:
        target = target[1:target.index(">")]
    else:
        target = target.split()[0] if target else ""
    if not target or target.startswith("#") or target.startswith("/"):
        return None
    if SCHEME_RE.match(target):
        return None
    target = target.split("#", 1)[0].split("?", 1)[0]
    return unquote(target) or None


def validate_links(files: dict[str, tarfile.TarInfo], archive: tarfile.TarFile) -> list[str]:
    errors: list[str] = []
    names = set(files)
    for path, member in files.items():
        if not path.endswith(".md"):
            continue
        stream = archive.extractfile(member)
        if stream is None:
            errors.append(f"{path}: cannot read Markdown member")
            continue
        text = stream.read().decode("utf-8")
        for raw in LINK_RE.findall(text):
            target = link_target(raw)
            if target is None:
                continue
            resolved = posixpath.normpath(posixpath.join(posixpath.dirname(path), target))
            if resolved in names:
                continue
            if any(name.startswith(resolved.rstrip("/") + "/") for name in names):
                continue
            errors.append(f"{path}: broken relative link {raw!r} -> {resolved!r}")
    return errors


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--archive", type=Path, required=True)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--root", type=Path, default=Path.cwd())
    args = parser.parse_args()

    manifest = json.loads(args.manifest.read_text(encoding="utf-8"))
    expected = {entry["path"]: entry for entry in manifest["files"]}
    if manifest.get("file_count") != len(expected):
        raise SystemExit("manifest file_count does not match its file list")
    if set(expected) != tracked_payload(args.root.resolve()):
        raise SystemExit("manifest inventory differs from the staged tracked payload")

    with tarfile.open(args.archive, mode="r:gz") as archive:
        regular = {
            member.name: member
            for member in archive.getmembers()
            if member.isfile()
        }
        manifest_members = [
            name for name in regular if name.endswith("/" + MANIFEST_REL) or name == MANIFEST_REL
        ]
        if len(manifest_members) != 1:
            raise SystemExit(f"expected one archived manifest, found {manifest_members}")
        manifest_member = manifest_members[0]
        prefix = manifest_member[: -len(MANIFEST_REL)]
        normalized = {
            name[len(prefix):]: member
            for name, member in regular.items()
            if name.startswith(prefix)
        }
        if len(normalized) != len(regular):
            raise SystemExit("archive contains members outside the manifest prefix")
        expected_members = set(expected) | {MANIFEST_REL}
        if set(normalized) != expected_members:
            missing = sorted(expected_members - set(normalized))
            extra = sorted(set(normalized) - expected_members)
            raise SystemExit(f"archive membership mismatch; missing={missing[:5]} extra={extra[:5]}")

        manifest_stream = archive.extractfile(normalized[MANIFEST_REL])
        if manifest_stream is None:
            raise SystemExit("archived manifest cannot be read")
        if manifest_stream.read() != args.manifest.read_bytes():
            raise SystemExit("archived manifest differs from the validated manifest")

        for path, entry in expected.items():
            stream = archive.extractfile(normalized[path])
            if stream is None:
                raise SystemExit(f"cannot read archived payload member {path}")
            size, digest = digest_stream(stream)
            if size != entry["bytes"] or digest != entry["sha256"]:
                raise SystemExit(f"hash mismatch for archived payload member {path}")

        link_errors = validate_links(normalized, archive)
        if link_errors:
            raise SystemExit("broken Markdown links:\n" + "\n".join(link_errors[:20]))

    print(json.dumps({
        "status": "PASS",
        "archive": str(args.archive.resolve()),
        "payload_files": len(expected),
        "archive_regular_files": len(normalized),
        "manifest_included_as_sidecar": True,
        "relative_markdown_links": "PASS",
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
