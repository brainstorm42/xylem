"""Whole-library navigation derived from the capture and canonical Brick manifests.

This inventory never promotes a supporting declaration to a public guarantee.
Module membership, explicit inventory membership, and public outputs stay separate.
"""

from __future__ import annotations

from collections import Counter
from pathlib import Path
from typing import Any

from .catalogue import _cell, _heading_anchor, _relative_link, _strings, load_bricks
from .extractor import load_capture
from .statement import DEFAULT_CAPTURE


def library_payload(repo_root: str | Path, *, capture: str | Path | None = None,
                    query: str | None = None, module: str | None = None) -> dict[str, Any]:
    root = Path(repo_root).resolve()
    capture_path = Path(capture) if capture else root / DEFAULT_CAPTURE.relative_to(Path(__file__).parents[2])
    data = load_capture(capture_path)
    for declaration in data["declarations"]:
        if any(not isinstance(declaration.get(field), str) or not declaration[field].strip()
               for field in ("module", "kind", "signature")):
            raise ValueError(f"incomplete captured declaration: {declaration['name']}")
    bricks = load_bricks(root)
    inventory: dict[str, list[str]] = {}
    public: dict[str, list[str]] = {}
    contexts: dict[str, list[str]] = {}
    titles = {b.brick_id: b.title for b in bricks}
    issues = [f"{b.brick_id}: {issue}" for b in bricks for issue in b.issues]
    for brick in bricks:
        for name in brick.declarations:
            inventory.setdefault(name, []).append(brick.brick_id)
        outputs = brick.interface.get("outputs")
        for output in outputs if isinstance(outputs, list) else []:
            if isinstance(output, dict):
                for name in _strings(output.get("declarations")):
                    public.setdefault(name, []).append(brick.brick_id)
        for name in _strings(brick.metadata.get("lean_modules")):
            full_name = name if name.startswith("Ctrllib.") else f"Ctrllib.{name}"
            contexts.setdefault(full_name, []).append(brick.brick_id)

    sources = {
        ".".join(path.relative_to(root / "ctrllib").with_suffix("").parts): path
        for path in sorted((root / "ctrllib" / "Ctrllib").rglob("*.lean"))
    }
    captured_modules = {d["module"] for d in data["declarations"]}
    for name in sorted(set(sources) - captured_modules):
        issues.append(f"source module absent from selected capture: {name}")
    for name in sorted(captured_modules - set(sources)):
        issues.append(f"captured module missing from source tree: {name}")
    names = {d["name"] for d in data["declarations"]}
    for name in sorted((set(inventory) | set(public)) - names):
        issues.append(f"manifest declaration absent from selected capture: {name}")
    for name in sorted(set(contexts) - set(sources)):
        issues.append(f"manifest module missing from source tree: {name}")

    records = []
    for declaration in sorted(data["declarations"], key=lambda d: (d["module"], d["name"])):
        name, module_name = declaration["name"], declaration["module"]
        exported = sorted(set(public.get(name, [])))
        included = sorted(set(inventory.get(name, [])))
        module_bricks = sorted(set(contexts.get(module_name, [])))
        role = ("public_output" if exported else "explicit_inventory" if included
                else "module_context" if module_bricks else "unpackaged")
        source = sources.get(module_name)
        records.append({
            "name": name, "kind": declaration["kind"], "module": module_name,
            "signature": declaration.get("signature", ""),
            "doc": declaration.get("doc") or "",
            "source": source.relative_to(root).as_posix() if source else None,
            "line": (declaration.get("range") or {}).get("start", [None])[0],
            "role": role, "public_in": exported, "inventory_in": included,
            "module_context": module_bricks,
        })
    counts = Counter(record["role"] for record in records)
    all_modules = sorted(set(sources) | captured_modules)
    modules = [{"name": name, "source": sources[name].relative_to(root).as_posix() if name in sources else None,
                "declarations": sum(r["module"] == name for r in records),
                "bricks": sorted(set(contexts.get(name, [])))} for name in all_modules]
    terms = (query or "").casefold().split()
    selected = [r for r in records if
                (not module or r["module"] in {module, f"Ctrllib.{module}"}) and
                all(term in "\n".join([r["name"], r["module"], r["signature"], r["doc"],
                    *[titles.get(b, b) for b in r["module_context"]]]).casefold() for term in terms)]
    if query or module:
        selected_modules = {r["module"] for r in selected}
        modules = [m for m in modules if m["name"] in selected_modules]
    return {
        "schema_version": 1, "toolchain": data.get("toolchain"),
        "query": query, "module": module, "issues": issues,
        "total_declarations": len(records), "total_source_modules": len(sources),
        "kind_counts": dict(sorted(Counter(r["kind"] for r in records).items())),
        "role_counts": dict(sorted(counts.items())),
        "brick_count": len(bricks), "brick_titles": titles,
        "unpackaged_modules": [name for name in all_modules if not contexts.get(name)],
        "modules": modules, "records": selected, "result_count": len(selected),
        "scope": "selected local declaration capture; not a fresh build or semantic review",
    }


def library_markdown(payload: dict[str, Any], *, repo_root: str | Path,
                     output: str | Path | None = None) -> str:
    root = Path(repo_root).resolve()
    destination = Path(output).resolve() if output else root / "LIBRARY.md"
    link = lambda path: _relative_link(root / path, destination)

    def brick_links(ids: list[str]) -> str:
        return ", ".join(f"[{_cell(payload['brick_titles'][b])}]({link(f'30_bricks/{b}/interface.md')})" for b in ids) or "—"

    lines = ["# Complete library map", "",
             f"[Browse mathematical Bricks]({link('INDEX.md')}). This map includes every declaration",
             "in the selected local capture, including definitions and internal support.",
             "A Lean declaration is not automatically a separate Brick.", "",
             f"**{payload['total_source_modules']} source modules · {payload['total_declarations']} captured declarations · {payload['brick_count']} Brick records.**", "",
             "| Captured kind | Count |", "| --- | ---: |"]
    kind_labels = {"theorem": "Theorems", "def": "Definitions (including generated support)",
                   "ctor": "Constructors", "rec": "Recursors", "inductive": "Inductive types and structures"}
    lines += [f"| {kind_labels.get(kind, kind)} | {count} |" for kind, count in payload["kind_counts"].items()]
    infrastructure = [("package import root", "ctrllib/Ctrllib.lean"),
                      ("declaration extractor", "ctrllib/Extract.lean")]
    present = [f"[{label}]({link(path)})" for label, path in infrastructure if (root / path).is_file()]
    if present:
        lines += ["", "Package infrastructure: " + " · ".join(present) + ".",
                  "These entry points are separate from the mathematical source-module count."]
    lines += ["", "## How to read coverage", "",
              "- **Public output:** explicitly named in a Brick's interface; follow its conventional proof.",
              "- **Explicit inventory:** named in a Brick record, but not exposed as a public output.",
              "- **Module context:** belongs to a listed module; its presence does not claim individual exposition or review.",
              "- **Unpackaged:** no current Brick names the declaration or its module.", "",
              "The counts below describe navigation coverage, not mathematical acceptance.", "",
              "| Role | Declarations |", "| --- | ---: |"]
    labels = {"public_output": "Public output", "explicit_inventory": "Explicit inventory",
              "module_context": "Module context", "unpackaged": "Unpackaged"}
    lines += [f"| {labels[role]} | {payload['role_counts'].get(role, 0)} |" for role in labels]
    if payload["query"] or payload["module"]:
        lines += ["", f"Search results: **{payload['result_count']}**. Global counts above remain unfiltered."]
    if payload["issues"]:
        lines += ["", "## Input issues", "", *[f"- {issue}" for issue in payload["issues"]]]
    if payload["unpackaged_modules"]:
        lines += ["", "Modules without a Brick context: " + ", ".join(f"`{m}`" for m in payload["unpackaged_modules"]) + "."]
    lines += ["", "## Module directory", "", "| Module | Declarations | Reader interfaces |", "| --- | ---: | --- |"]
    for module in payload["modules"]:
        short = module["name"].removeprefix("Ctrllib.")
        lines.append(f"| [{short}](#{_heading_anchor(short)}) | {module['declarations']} | {brick_links(module['bricks'])} |")
    for module in payload["modules"]:
        short = module["name"].removeprefix("Ctrllib.")
        lines += ["", f"## {short}", ""]
        if module["source"]:
            lines.append(f"[Canonical Lean source]({link(module['source'])}).")
        lines += ["", "| Exact declaration | Kind | Role | Explicit Brick records |",
                  "| --- | --- | --- | --- |"]
        for record in payload["records"]:
            if record["module"] == module["name"]:
                lines.append(f"| `{record['name']}` | {record['kind']} | {labels[record['role']]} | {brick_links(record['inventory_in'])} |")
    lines += ["", "## Search and evidence", "",
              "Use Find for a declaration, module, or Brick name. Agent search also includes",
              "captured signatures and documentation:", "", "```sh",
              "./20_tools/brickconverter.sh library --query 'barbalat'",
              "./20_tools/brickconverter.sh library --module Lyapunov --json", "```", "",
              f"Capture toolchain: {_cell(payload['toolchain'])}. Source and capture identities are",
              "checked for navigation; this inventory does not rerun Lean or establish source",
              "fidelity, conventional proof completeness, or physical applicability.", ""]
    return "\n".join(lines)
