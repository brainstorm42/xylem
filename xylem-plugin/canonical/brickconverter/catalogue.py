"""Searchable Brick catalogue and deterministic reader generation.

This module is deliberately a reader aid.  It reads Brick frontmatter and the
root bibliography, then delegates exact statement rendering to
``statement.render_brick``.  It does not rebuild the declaration capture, run
Lean, or infer source equivalence.
"""

from __future__ import annotations

from dataclasses import dataclass
import json
import os
from pathlib import Path
import re
from typing import Any, Iterable

import yaml

from .profiles import load_profile
from .extractor import load_capture
from .statement import DEFAULT_CAPTURE, DEFAULT_PROFILE, render_brick


LEVELS = ("atomic", "composite", "review_pending")
FRONTMATTER_RE = re.compile(r"\A---\s*\n(.*?)\n---(?:\n|\Z)", re.DOTALL)
ENTRY_RE = re.compile(
    r"(?ms)^\s*@(?P<kind>[^\s{]+)\s*\{\s*(?P<key>[^,\s]+)\s*,(?P<body>.*?)(?=^\s*@[^\s{]+\s*\{|\Z)"
)
FIELD_RE = re.compile(r"(?m)^\s*([A-Za-z][A-Za-z0-9_-]*)\s*=\s*(.*?)(?:,\s*)?$")


class _StrictLoader(yaml.SafeLoader):
    """Safe YAML loader that rejects duplicate manifest keys."""


def _strict_mapping(loader: _StrictLoader, node: yaml.MappingNode, deep: bool = False):
    mapping = {}
    for key_node, value_node in node.value:
        key = loader.construct_object(key_node, deep=deep)
        if key in mapping:
            raise yaml.constructor.ConstructorError(
                "while constructing a mapping", node.start_mark,
                f"found duplicate key {key!r}", key_node.start_mark,
            )
        mapping[key] = loader.construct_object(value_node, deep=deep)
    return mapping


_StrictLoader.add_constructor(yaml.resolver.BaseResolver.DEFAULT_MAPPING_TAG, _strict_mapping)


@dataclass(frozen=True)
class Brick:
    """A parsed Brick record and its repository-relative reader paths."""

    root: Path
    path: Path
    metadata: dict[str, Any]
    title: str
    summary: str
    issues: tuple[str, ...]

    @property
    def brick_id(self) -> str:
        return str(self.metadata.get("brick_id") or self.path.name)

    @property
    def level(self) -> str:
        value = self.metadata.get("brick_level")
        return value if value in LEVELS else "review_pending"

    @property
    def declarations(self) -> list[str]:
        return _strings(self.metadata.get("lean_declarations"))

    @property
    def source_keys(self) -> list[str]:
        return _strings(self.metadata.get("source_keys"))

    @property
    def keywords(self) -> list[str]:
        return _strings(self.metadata.get("keywords"))

    @property
    def interface(self) -> dict[str, Any]:
        value = self.metadata.get("interface")
        return value if isinstance(value, dict) else {}

    @property
    def search_terms(self) -> list[str]:
        """Return literal searchable values in stable, duplicate-free order."""

        values: list[str] = [self.title, self.summary]
        values.extend(self.keywords)
        values.extend(_flatten_strings(self.interface))
        values.extend(self.declarations)
        values.extend(self.source_keys)
        source_record = self.path.parent / "provenance" / "source.md"
        if source_record.is_file():
            # Source identity names and locators are useful search vocabulary;
            # this remains a literal reader index, not a citation inference.
            values.append(source_record.read_text(encoding="utf-8"))
        if self.metadata.get("level_reason"):
            values.append(str(self.metadata["level_reason"]))
        # File and module names are useful when looking up a source record.
        values.extend(_strings(self.metadata.get("lean_modules")))
        values.extend(("proof.md", "provenance/source.md", "correspondence/statements.md"))
        seen: set[str] = set()
        return [value for value in values if value and not (value in seen or seen.add(value))]

    def search_text(self) -> str:
        return "\n".join(self.search_terms)

    def readers(self) -> dict[str, str]:
        brick_root = self.path.parent
        return {
            "reader": _relative_link(brick_root / "reader.md", self.root / "INDEX.md"),
            "manifest": _relative_link(self.path, self.root / "INDEX.md"),
            "interface": _relative_link(brick_root / "interface.md", self.root / "INDEX.md"),
            "references": _relative_link(
                brick_root / "correspondence" / "references.md", self.root / "INDEX.md"
            ),
            "statements": _relative_link(
                brick_root / "correspondence" / "statements.md", self.root / "INDEX.md"
            ),
            "proof": _relative_link(brick_root / "proof.md", self.root / "INDEX.md"),
            "source": _relative_link(
                brick_root / "provenance" / "source.md", self.root / "INDEX.md"
            ),
        }


def _strings(value: Any) -> list[str]:
    return [item for item in value or [] if isinstance(item, str)] if isinstance(value, list) else []


def _flatten_strings(value: Any) -> list[str]:
    if isinstance(value, str):
        return [value]
    if isinstance(value, dict):
        values: list[str] = []
        for key, item in value.items():
            # Field names themselves are literal interface vocabulary too.
            values.append(str(key))
            values.extend(_flatten_strings(item))
        return values
    if isinstance(value, list):
        values: list[str] = []
        for item in value:
            values.extend(_flatten_strings(item))
        return values
    return []


def _relative_link(target: Path, source: Path) -> str:
    return Path(os.path.relpath(target, source.parent)).as_posix()


def _parse_frontmatter(path: Path) -> tuple[dict[str, Any], str, list[str]]:
    text = path.read_text(encoding="utf-8")
    match = FRONTMATTER_RE.match(text)
    if not match:
        return {}, text, ["README.md is missing YAML frontmatter"]
    try:
        metadata = yaml.load(match.group(1), Loader=_StrictLoader)
    except yaml.YAMLError as error:
        return {}, text[match.end():], [f"invalid YAML frontmatter: {error}"]
    if not isinstance(metadata, dict):
        return {}, text[match.end():], ["frontmatter is not a mapping"]
    return metadata, text[match.end():], []


def _first_paragraph(body: str) -> str:
    lines = []
    for line in body.splitlines():
        if line.startswith("#"):
            if lines:
                break
            continue
        if line.strip():
            lines.append(line.strip())
        elif lines:
            break
    return " ".join(lines)


def load_bricks(repo_root: str | Path) -> list[Brick]:
    """Load all current ``30_bricks/*/README.md`` records in path order."""

    root = Path(repo_root).resolve()
    records_root = root / "30_bricks"
    if not records_root.is_dir():
        raise ValueError(f"canonical Brick directory missing: {records_root}")
    bricks: list[Brick] = []
    for readme in sorted(records_root.glob("*/README.md")):
        metadata, body, issues = _parse_frontmatter(readme)
        if metadata.get("kind") != "brick":
            issues.append("frontmatter kind is not 'brick'")
        if metadata.get("brick_id") != readme.parent.name:
            issues.append("brick_id does not match the Brick directory")
        if not isinstance(metadata.get("brick_level"), str):
            issues.append("missing brick_level; indexed as review_pending")
        elif metadata["brick_level"] not in LEVELS:
            issues.append(f"unsupported brick_level {metadata['brick_level']!r}")
        if not isinstance(metadata.get("level_reason"), str) or not metadata.get("level_reason", "").strip():
            issues.append("missing level_reason")
        if not isinstance(metadata.get("summary"), str) or not metadata.get("summary", "").strip():
            issues.append("missing summary; using the first README paragraph")
        title = next((line[2:].strip() for line in body.splitlines() if line.startswith("# ")), readme.parent.name)
        summary = metadata.get("summary") if isinstance(metadata.get("summary"), str) else _first_paragraph(body)
        bricks.append(Brick(root, readme, metadata, title, summary, tuple(issues)))
    return bricks


def filter_bricks(bricks: Iterable[Brick], *, query: str | None = None, level: str | None = None) -> list[Brick]:
    """Filter by literal, case-insensitive substring and exact catalogue level."""

    if level is not None and level not in LEVELS:
        raise ValueError(f"unsupported catalogue level {level!r}")
    terms = query.casefold().split() if query else []
    return [
        brick for brick in bricks
        if (level is None or brick.level == level)
        and (not terms or all(term in brick.search_text().casefold() for term in terms))
    ]


def _capture_info(repo_root: Path, capture: str | Path | None = None) -> dict[str, Any]:
    path = Path(capture) if capture is not None else repo_root / DEFAULT_CAPTURE.relative_to(Path(__file__).parents[2])
    info: dict[str, Any] = {
        "path": _relative_link(path, repo_root / "INDEX.md"),
        "exists": path.is_file(),
        "freshness": "reported artifact; freshness is not independently established",
        "limitations": [
            "Catalogue and reader generation do not rebuild or recheck the declaration capture.",
            "Generated summaries and interface text are authored metadata, not automatic semantic translations.",
        ],
    }
    if not path.is_file():
        info["status"] = "missing"
        return info
    try:
        data = load_capture(path)
        info.update({
            "status": "available",
            "schema_version": data.get("schema_version"),
            "toolchain": data.get("toolchain"),
            "generated_from": data.get("generated_from"),
            "declaration_count": len(data.get("declarations", [])) if isinstance(data.get("declarations"), list) else None,
        })
    except (OSError, ValueError) as error:
        info.update({"status": "unreadable", "error": str(error)})
    return info


def catalogue_payload(bricks: Iterable[Brick], *, repo_root: str | Path,
                      query: str | None = None, level: str | None = None,
                      capture: str | Path | None = None) -> dict[str, Any]:
    root = Path(repo_root).resolve()
    records = []
    for brick in filter_bricks(bricks, query=query, level=level):
        records.append({
            "brick_id": brick.brick_id,
            "title": brick.title,
            "path": brick.path.relative_to(root).as_posix(),
            "level": brick.level,
            "level_reason": brick.metadata.get("level_reason"),
            "summary": brick.summary,
            "keywords": brick.keywords,
            "interface": brick.interface,
            "declarations": brick.declarations,
            "source_keys": brick.source_keys,
            "readers": brick.readers(),
            "issues": list(brick.issues),
        })
    return {
        "schema_version": 1,
        "operation": "catalogue",
        "query": query,
        "level": level,
        "record_count": len(records),
        "records": records,
        "declaration_capture": _capture_info(root, capture),
    }


def _cell(value: Any) -> str:
    text = ", ".join(value) if isinstance(value, list) else str(value or "")
    return text.replace("|", r"\|").replace("\n", " ").strip()


def catalogue_markdown(payload: dict[str, Any], *, output: str | Path,
                       repo_root: str | Path | None = None) -> str:
    """Render a catalogue with links resolved relative to its output file."""

    output_path = Path(output).resolve()
    root = Path(repo_root).resolve() if repo_root is not None else output_path.parents[0]
    # Payload paths are repository-relative.  Derive repository root from the
    # current checkout by walking until 30_bricks exists; callers normally use
    # the checkout root and this keeps temporary fixture use straightforward.
    while root != root.parent and not (root / "30_bricks").is_dir():
        root = root.parent
    lines = [
        "# Brick catalogue", "",
        "Each Brick title opens one reading page with its assumptions, guarantees,",
        "notation, full authored proof, sources, and evidence. The catalogue lists",
        "the available records; it does not grant mathematical or scientific acceptance.", "",
        f"Records: **{payload['record_count']}**.", "",
        f"[Complete library map]({_relative_link(root / 'LIBRARY.md', output_path)}) includes every captured local declaration,",
        "with definitions, supporting results, and public outputs distinguished.", "",
        "**Atomic:** one reusable mathematical interface. **Composite:** a result",
        "assembled through stated proof connections. **Boundary under review:** a",
        "legacy bundle whose separate results remain available while its packaging is reviewed.", "",
        "| Brick | Level | Mathematical purpose | Read |",
        "| --- | --- | --- | --- |",
    ]
    rationales: list[str] = []
    for record in sorted(payload["records"], key=lambda r: (LEVELS.index(r["level"]), r["title"])):
        brick_path = root / record["path"]
        brick_link = _relative_link(brick_path.parent / "reader.md", output_path)
        reader_links = []
        for label in ("reader", "manifest", "proof"):
            # Readers in payload are rooted at INDEX.md; recompute from the
            # actual output so --output elsewhere still yields working links.
            target = brick_path.parent / {
                "reader": "reader.md",
                "manifest": "README.md",
                "proof": "proof.md",
                "interface": "interface.md",
                "references": "correspondence/references.md",
                "statements": "correspondence/statements.md",
            }[label]
            reader_links.append(f"[{label}]({_relative_link(target, output_path)})")
        lines.append(
            f"| [{_cell(record['title'])}]({brick_link}) | "
            f"{_level_label(record['level'])} | {_cell(record['summary'])} | "
            f"{' · '.join(reader_links)} |"
        )
        if record.get("level_reason"):
            rationales.append(f"- **{_cell(record['brick_id'])}:** {_cell(record['level_reason'])}")
    from .sets import sets_markdown
    sets_text, _set_issues = sets_markdown(root, output_path)
    if sets_text:
        lines += ["", sets_text]
    if rationales:
        lines += ["", "## Level rationale", "", *rationales, ""]
    issues = [f"{r['brick_id']}: {issue}" for r in payload["records"] for issue in r.get("issues", [])]
    issues.extend(_set_issues)
    if issues:
        lines += ["", "## Reader metadata issues", "", *[f"- {issue}" for issue in issues], ""]
    lines += ["", "## Search and evidence", "",
              "Use Find in this page, or ask an agent to search the catalogue by mathematical",
              "terms, assumptions, source, or exact declaration name. The catalogue search",
              "also reads the complete structured interfaces and source records.", "",
              "These summaries are authored descriptions rendered by BrickConverter. Exact",
              "captured statements are linked from each interface; unsupported notation",
              "remains explicitly marked in that appendix.", "",
              "Capture toolchain: " + _cell(payload["declaration_capture"].get("toolchain")) + ". "
              + _cell(payload["declaration_capture"].get("freshness")) + ".", ""]
    return "\n".join(lines).rstrip() + "\n"


def _level_label(level: str) -> str:
    return {"atomic": "Atomic", "composite": "Composite",
            "review_pending": "Boundary under review"}[level]


def _interface_markdown(brick: Brick) -> str:
    interface = brick.interface
    outputs = interface.get("outputs") if isinstance(interface.get("outputs"), list) else []
    composition = interface.get("composition") if isinstance(interface.get("composition"), list) else []
    lines = [
        f"# Interface — {brick.title}", "",
        "This reader page summarizes the authored interface metadata for this Brick.",
        "Authored summaries are not automatic semantic translations. The exact",
        "captured statement is the authority for Lean binders and assumptions; see",
        f"[the statement appendix](correspondence/statements.md) and [the conventional proof](proof.md).", "",
        f"**Level:** {_level_label(brick.level)}.",
    ]
    if interface.get("level_reason") or brick.metadata.get("level_reason"):
        lines.append(f"**Level rationale:** {interface.get('level_reason') or brick.metadata.get('level_reason')}")
    evidence = brick.path.parent / "provenance" / "acceptance.md"
    dependencies = brick.path.parent / "provenance" / "dependencies.md"
    lines += ["", "## Evidence and dependencies", ""]
    if evidence.is_file():
        lines.append(f"[Acceptance and evidence record]({_relative_link(evidence, brick.path.parent / 'interface.md')}).")
    else:
        lines.append("No acceptance record is present.")
    if dependencies.is_file():
        lines.append(f"[Dependency record]({_relative_link(dependencies, brick.path.parent / 'interface.md')}).")
    if brick.issues:
        lines += ["", "Reader metadata notes:", "", *[f"- {issue}" for issue in brick.issues]]
    lines += ["", "## Inputs", ""]
    lines += [f"- {value}" for value in _strings(interface.get("inputs"))] or ["- No authored inputs are recorded."]
    lines += ["", "## Assumptions", ""]
    lines += [f"- {value}" for value in _strings(interface.get("assumptions"))] or ["- No authored assumptions are recorded."]
    lines += ["", "## Outputs", ""]
    if outputs:
        for item in outputs:
            if not isinstance(item, dict):
                lines.append(f"- {item}")
                continue
            statement = item.get("statement", "")
            declarations = _strings(item.get("declarations"))
            proof_section = item.get("proof_section", "")
            title = str(item.get('id', 'Unnamed output')).replace('_', ' ').capitalize()
            lines += [f"### {title}", "", str(statement)]
            if declarations:
                lines.append("",)  # Keep exact declaration names visibly separate.
                lines.append("Exact declarations: " + ", ".join(f"`{name}`" for name in declarations) + ".")
            if proof_section:
                lines.append(f"Proof section: [{proof_section}](proof.md#{_heading_anchor(str(proof_section))}).")
            lines.append("")
    else:
        lines.append("- No authored outputs are recorded.")
    lines += ["## Composition", ""]
    if composition:
        for item in composition:
            if not isinstance(item, dict):
                lines.append(f"- {item}")
                continue
            uses = ", ".join(f"`{x}`" for x in _strings(item.get("uses"))) or "(none recorded)"
            lines += [f"- Uses {uses}; establishes `{item.get('establishes', '')}`. {item.get('explanation', '')}"]
    else:
        lines.append("- No authored composition is recorded.")
    lines += ["", "## Exact correspondence", "", "The statement appendix retains every captured binder and endpoint. Unsupported", "notation remains in exact Lean text with its reason; generation does not run", "Lean or certify source equivalence.", ""]
    return "\n".join(lines).rstrip() + "\n"


def _heading_anchor(title: str) -> str:
    """Approximate the stable GitHub Markdown anchor for a proof heading."""

    value = re.sub(r"[^\w\s-]", "", title.casefold(), flags=re.UNICODE)
    return re.sub(r"[\s-]+", "-", value).strip("-")


def _bib_value(value: str) -> str:
    """Unwrap a simple BibTeX value for a truthful display/link."""

    value = value.strip().rstrip(",").strip()
    if len(value) >= 2 and value[0] == "{" and value[-1] == "}":
        return value[1:-1].strip()
    if len(value) >= 2 and value[0] == '"' and value[-1] == '"':
        return value[1:-1].strip()
    return value


def _bib_entries(path: Path) -> dict[str, dict[str, Any]]:
    if not path.is_file():
        return {}
    text = path.read_text(encoding="utf-8")
    result: dict[str, dict[str, Any]] = {}
    for match in ENTRY_RE.finditer(text):
        if match.group("key") in result:
            raise ValueError(f"duplicate bibliography key: {match.group('key')}")
        raw = text[match.start():match.end()].strip()
        fields: dict[str, str] = {}
        for field in FIELD_RE.finditer(match.group("body")):
            value = field.group(2).strip().rstrip(",").strip()
            fields[field.group(1).lower()] = value
        result[match.group("key")] = {"kind": match.group("kind"), "raw": raw, "fields": fields}
    return result


def _source_locators(path: Path) -> list[str]:
    if not path.is_file():
        return []
    lines = path.read_text(encoding="utf-8").splitlines()
    locators: list[str] = []
    in_locator_section = False
    for line in lines:
        if re.match(r"^##+\s+", line):
            in_locator_section = bool(re.search(r"locator|source statement|retained source", line, re.I))
        if in_locator_section and line.startswith("-"):
            locators.append(line[1:].strip())
    return locators


def _references_markdown(brick: Brick, bibliography: Path) -> tuple[str, list[str]]:
    try:
        entries = _bib_entries(bibliography)
    except (OSError, ValueError) as error:
        return "", [f"invalid bibliography: {error}"]
    source_path = brick.path.parent / "provenance" / "source.md"
    locators = _source_locators(source_path)
    issues: list[str] = []
    lines = [
        f"# References — {brick.title}", "",
        "This page joins the Brick's declared bibliography keys with the exact",
        "root bibliography entries and locators retained in `provenance/source.md`.",
        "It records provenance for reading; it does not claim source equivalence", "or acceptance.", "",
        f"Canonical bibliography: `{_relative_link(bibliography, brick.path.parent / 'correspondence' / 'references.md')}`.", "",
    ]
    if not brick.source_keys:
        lines += ["No scholarly bibliography keys are declared. The source record describes the in-house derivation.", ""]
    for key in brick.source_keys:
        entry = entries.get(key)
        lines += [f"## `{key}`", ""]
        if entry is None:
            issue = f"missing bibliography entry for source key {key!r}"
            issues.append(issue)
            lines += [f"**Missing bibliography entry:** `{key}` is retained from frontmatter but has no exact entry in the root bibliography.", ""]
            continue
        fields = entry.get("fields", {})
        lines += [f"BibTeX entry type: `{entry['kind']}`.", ""]
        if fields.get("author"):
            lines.append(f"Authors: {_bib_value(fields['author'])}")
        if fields.get("title"):
            lines.append(f"Title: {_bib_value(fields['title'])}")
        if fields.get("year"):
            lines.append(f"Year: {_bib_value(fields['year'])}")
        if fields.get("doi"):
            doi = _bib_value(fields["doi"])
            lines.append(f"DOI: [{doi}](https://doi.org/{doi})")
        if fields.get("url"):
            url = _bib_value(fields["url"])
            lines.append(f"URL: [{url}]({url})")
        lines += ["", "<details>", "<summary>Exact BibTeX entry excerpt</summary>", "", "```bibtex", entry["raw"], "```", "", "</details>", ""]
    if not source_path.is_file():
        issues.append("missing provenance/source.md")
        lines += ["## Source record", "", "**Missing source record:** `provenance/source.md` is not present.", ""]
    else:
        lines += ["## Source record locators", "", f"[Open provenance/source.md]({_relative_link(source_path, brick.path.parent / 'correspondence' / 'references.md')}).", ""]
        lines += [f"- {locator}" for locator in locators] or ["No dedicated locator bullets were found; consult the source record for its bounded context."]
        lines.append("")
    lines += ["The source record and exact bibliography entries remain separate from the", "captured Lean statements and conventional proof.", ""]
    return "\n".join(lines).rstrip() + "\n", issues


def _expected_readers(brick: Brick, bibliography: Path, capture_data: dict[str, Any], profile: Any) -> tuple[dict[Path, str], list[str]]:
    outputs: dict[Path, str] = {
        brick.path.parent / "interface.md": _interface_markdown(brick),
    }
    references, issues = _references_markdown(brick, bibliography)
    outputs[brick.path.parent / "correspondence" / "references.md"] = references
    try:
        statements, _records = render_brick(brick.path, capture_data, profile=profile)
        outputs[brick.path.parent / "correspondence" / "statements.md"] = statements
    except (OSError, ValueError, KeyError, json.JSONDecodeError) as error:
        issues.append(f"statement rendering failed: {error}")
    return outputs, issues


def _validator_issues(brick: Brick, capture_data: dict[str, Any] | None) -> list[str]:
    """Reuse the repository validator for interface and composition preflight."""

    try:
        import validate_bricks
    except ImportError:
        return ["repository validator is unavailable"]
    records = {
        item.get("name"): item for item in (capture_data or {}).get("declarations", [])
        if isinstance(item, dict) and isinstance(item.get("name"), str)
    }
    return [f"{finding.code}: {finding.message}"
            for finding in validate_bricks.validate_interface(brick.metadata, brick.path.parent, records)]


def refresh_readers(repo_root: str | Path, *, check: bool = False,
                    capture: str | Path | None = None,
                    bibliography: str | Path | None = None,
                    profile: str | Path | None = None) -> dict[str, Any]:
    """Generate reader files or report missing/stale files without writing."""

    root = Path(repo_root).resolve()
    capture_path = Path(capture).resolve() if capture is not None else (root / DEFAULT_CAPTURE.relative_to(Path(__file__).parents[2])).resolve()
    bibliography_path = Path(bibliography).resolve() if bibliography is not None else root / "bibliography.bib"
    profile_path = Path(profile).resolve() if profile is not None else DEFAULT_PROFILE
    bricks = load_bricks(root)
    report: dict[str, Any] = {"schema_version": 1, "operation": "refresh-readers", "check": check, "updated": [], "stale": [], "issues": [], "declaration_capture": _capture_info(root, capture_path)}
    report["reader_findings"] = []
    for directory in sorted((root / "30_bricks").iterdir()):
        if directory.is_dir() and not (directory / "README.md").is_file():
            report["issues"].append(f"missing authored manifest: 30_bricks/{directory.name}/README.md")
    payload = catalogue_payload(bricks, repo_root=root, capture=capture_path)
    index = root / "INDEX.md"
    expected_index = catalogue_markdown(payload, output=index, repo_root=root)
    expected: dict[Path, str] = {index: expected_index}
    from .sets import read_sets
    _, set_issues = read_sets(root)
    report["issues"].extend(set_issues)
    capture_data: dict[str, Any] | None = None
    profile_data: Any | None = None
    if report["declaration_capture"].get("status") != "available":
        report["issues"].append(f"missing or invalid declaration capture: {capture_path}")
    else:
        try:
            # All Brick statement renders reuse this parsed declaration universe.
            capture_data = load_capture(capture_path)
        except (OSError, ValueError, json.JSONDecodeError) as error:
            report["issues"].append(f"invalid declaration capture: {error}")
    try:
        profile_data = load_profile(profile_path)
    except (OSError, ValueError, yaml.YAMLError) as error:
        report["issues"].append(f"invalid notation profile: {error}")
    if bricks and not bibliography_path.is_file():
        report["issues"].append(f"missing canonical bibliography: {bibliography_path}")
    for brick in bricks:
        if brick.issues:
            report["issues"].extend(f"{brick.brick_id}: {issue}" for issue in brick.issues)
        report["issues"].extend(f"{brick.brick_id}: {issue}" for issue in _validator_issues(brick, capture_data))
        if not (brick.path.parent / "provenance" / "source.md").is_file():
            report["issues"].append(f"{brick.brick_id}: missing provenance/source.md")
        if capture_data is None or profile_data is None:
            generated, issues = ({brick.path.parent / "interface.md": _interface_markdown(brick)}, [])
            references, ref_issues = _references_markdown(brick, bibliography_path)
            generated[brick.path.parent / "correspondence" / "references.md"] = references
            issues.extend(ref_issues)
        else:
            generated, issues = _expected_readers(brick, bibliography_path, capture_data, profile_data)
        from .reader import render_reader
        reader_findings: list[str] = []
        reader, reader_issues = render_reader(brick, generated, findings=reader_findings)
        report.setdefault("reader_findings", []).extend(f"{brick.brick_id}: {finding}" for finding in reader_findings)
        generated[brick.path.parent / "reader.md"] = reader
        issues.extend(reader_issues)
        expected.update(generated)
        report["issues"].extend(f"{brick.brick_id}: {issue}" for issue in issues)
    if capture_data is not None:
        from .library import library_markdown, library_payload
        try:
            library = library_payload(root, capture=capture_path)
            report["issues"].extend(library["issues"])
            expected[root / "LIBRARY.md"] = library_markdown(library, repo_root=root)
        except (OSError, ValueError) as error:
            report["issues"].append(f"library inventory failed: {error}")
    for path, content in expected.items():
        if not path.is_file():
            report["stale"].append({"path": str(path.relative_to(root)), "reason": "missing"})
        elif path.read_text(encoding="utf-8") != content:
            report["stale"].append({"path": str(path.relative_to(root)), "reason": "content differs"})
    # Input failures must not leave a partially refreshed reader set. Build all
    # expected content first, then write only after validation is clean.
    if not check and not report["issues"]:
        written: list[str] = []
        for path, content in expected.items():
            if path.parent != root and not path.parent.exists():
                path.parent.mkdir(parents=True, exist_ok=True)
            if not path.is_file() or path.read_text(encoding="utf-8") != content:
                path.write_text(content, encoding="utf-8")
                written.append(str(path.relative_to(root)))
        report["updated"] = written
        report["stale_before_refresh"] = report["stale"]
        report["stale"] = []
    report["status"] = (
        "ok" if not report["issues"] and (not check or not report["stale"])
        else "needs_attention"
    )
    report["generated_files"] = len(expected)
    report["limitations"] = [
        "Reader generation does not rebuild or recheck Lean declarations.",
        "Authored summaries and interface metadata are not semantic translations.",
        "Missing declarations, source records, and bibliography keys stay visible as issues.",
    ]
    return report
