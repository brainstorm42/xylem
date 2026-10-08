"""Read collection manifests without adding formal composition claims."""

from pathlib import Path
from typing import Any

from .catalogue import _cell, _parse_frontmatter, _relative_link, load_bricks


def read_sets(root: Path) -> tuple[list[dict[str, Any]], list[str]]:
    known = {b.brick_id: b for b in load_bricks(root)}
    records, issues = [], []
    for path in sorted((root / "40_sets").glob("*/README.md")):
        metadata, _, errors = _parse_frontmatter(path)
        issues.extend(f"{path.parent.name}: {error}" for error in errors)
        if metadata.get("type") != "brick_set" or metadata.get("set_id") != path.parent.name:
            issues.append(f"{path.parent.name}: invalid set identity")
        for field in ("title", "summary"):
            if not isinstance(metadata.get(field), str) or not metadata[field].strip():
                issues.append(f"{path.parent.name}: missing {field}")
        members = metadata.get("bricks")
        if not isinstance(members, list) or not members or any(not isinstance(x, str) for x in members):
            issues.append(f"{path.parent.name}: bricks must be a nonempty list of identities")
            members = []
        elif len(set(members)) != len(members):
            issues.append(f"{path.parent.name}: duplicate Brick membership")
        for member in members:
            if member not in known:
                issues.append(f"{path.parent.name}: unknown member Brick {member}")
        records.append({"id": path.parent.name, "title": metadata.get("title", path.parent.name),
                        "summary": metadata.get("summary", ""), "path": path,
                        "bricks": members})
    return records, issues


def sets_markdown(root: Path, destination: Path) -> tuple[str, list[str]]:
    sets, issues = read_sets(root)
    if not sets:
        return "", issues
    lines = ["## Reader sets", "", "Sets provide reading paths through related Bricks. Membership does not prove",
             "a composition or combine the assumptions of the component results.", "",
             "| Set | Purpose | Bricks |", "| --- | --- | ---: |"]
    lines += [f"| [{_cell(s['title'])}]({_relative_link(s['path'], destination)}) | {_cell(s['summary'])} | {len(s['bricks'])} |" for s in sets]
    return "\n".join(lines) + "\n", issues
