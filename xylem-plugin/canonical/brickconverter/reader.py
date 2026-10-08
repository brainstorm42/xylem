"""Assemble authored Brick records without reconstructing their mathematics.

Only navigation is generated. Authored prose, equations, evidence claims and
captured declarations keep their separate authorities in the resulting page.
The upfront table contains inline-safe accounts or links to full block copies
directly below it; code/math blocks are never flattened into table cells. The
source records are still included in full. Preflight uses reader_markdown's
bounded protected recognition, not an independent heading/link-stripping regex.
Nonempty records and unique supported explicit IDs are structural checks only.
"""

from __future__ import annotations

import re
from pathlib import Path
from typing import TYPE_CHECKING

from .reader_markdown import (
    Document,
    Embedding,
    authored_content,
    duplicate_anchors,
    source_anchor,
)

if TYPE_CHECKING:
    from .catalogue import Brick


AUTHORED_RECORDS = (
    ("README.md", "Manifest and reader orientation"),
    ("proof.md", "Conventional proof"),
    ("correspondence/notation.md", "Authored notation correspondence"),
    ("correspondence/source_to_lean.md", "Authored source-to-Lean correspondence"),
    ("provenance/source.md", "Source identity and locators"),
    ("provenance/dependencies.md", "Dependency record"),
    ("provenance/acceptance.md", "Recorded evidence and acceptance"),
    ("correspondence/discrepancies.md", "Discrepancies and open items"),
)
GENERATED_RECORDS = (
    ("interface.md", "Generated interface record"),
    ("correspondence/references.md", "Bibliography and source references"),
    ("correspondence/statements.md", "Exact captured statement appendix"),
)


def _cell(text: str) -> str:
    return re.sub(r"(?<!\\)\|", r"\\|", text.strip()).replace("\n", "<br>")


def _terminology(embedding: Embedding) -> tuple[list[str], list[str]]:
    """Copy explicitly named authored accounts; do not infer symbol meanings."""
    accounts = []
    for name in ("README.md", "proof.md", "correspondence/notation.md"):
        doc = embedding.documents.get(name)
        if doc is None:
            continue
        if name == "correspondence/notation.md":
            # Include unheaded introductory text as well as every authored section.
            body, requires_block = embedding.excerpt(name, 0, len(doc.text))
            accounts.append((name, "Notation correspondence", doc.anchor, body, requires_block))
        else:
            selected_end = -1
            for h in doc.headings:
                if h.start < selected_end or not re.search(r"\b(definitions?|notation|terminology|nomenclature|conventions?)\b", h.title, re.IGNORECASE):
                    continue
                start, selected_end = doc.section_bounds(h)
                body, requires_block = embedding.excerpt(name, start, selected_end)
                accounts.append((name, h.title, doc.fragments[h.fragment], body, requires_block))
    lines = ["## Terminology and notation", "",
             "The table copies available authored definitions and notation accounts. Definition coverage is not assessed: missing meanings, types, units, frames, or conventions require author review; the converter supplies none. Source accounts remain in full below.", "",
             "| Term or notation account | Authored definition or account | Same-page source |",
             "| --- | --- | --- |"]
    has_table = False
    block_copies = []
    for index, (name, title, anchor, body, requires_block) in enumerate(accounts):
        link = f"[{_cell(title)}](#{anchor})"
        if requires_block:
            copy_anchor = f"terminology-account-{index}"
            lines.append(f"| {_cell(title)} | [Full authored account below](#{copy_anchor}) | {link} |")
            block_copies += ["", f'<a id="{copy_anchor}"></a>', "", f"### Copied account: {title}", "", body]
            continue
        # Tables retain the author's column meanings, rather than turning an
        # arbitrary Lean name or endpoint into a purported definition.
        for block in re.split(r"\n\s*\n", body):
            rows = block.splitlines()
            if len(rows) > 2 and re.fullmatch(r"\s*\|?\s*:?-{3,}.*", rows[1]):
                split = lambda row: [c.strip() for c in re.split(r"(?<!\\)\|", row.strip().strip("|"))]
                headers = split(rows[0])
                separators = split(rows[1])
                if len(headers) > 1 and all(re.fullmatch(r":?-{3,}:?", c) for c in separators):
                    has_table = True
                    for row in rows[2:]:
                        cells = split(row)
                        if len(cells) != len(headers):
                            continue
                        meaning = "<br>".join(f"{header}: {value}" for header, value in zip(headers[1:], cells[1:]))
                        lines.append(f"| {_cell(cells[0])} | {_cell(meaning)} | {link} |")
                    continue
            if block.strip():
                lines.append(f"| {_cell(title)} | {_cell(block)} | {link} |")
    findings = []
    if not accounts or not any(body.strip() for _, _, _, body, _ in accounts):
        findings.append("No authored definitions or notation accounts are available; missing definitions require author review.")
    if not has_table:
        findings.append("No authored term-by-term definition table was found in the selected accounts; prose accounts are retained, and missing definitions require author review.")
    if findings:
        lines += ["", "**Definition findings:**", "", *[f"- {finding}" for finding in findings]]
    return lines + block_copies, findings


def render_reader(brick: Brick, generated: dict[Path, str], *, findings: list[str] | None = None) -> tuple[str, list[str]]:
    """Return a single reading page and blocking source-input issues.

    Generated records must come from this render pass, not possibly stale disk
    copies. Authored records are read from their canonical paths.
    """
    from .catalogue import FRONTMATTER_RE

    base = brick.path.parent
    sources: dict[str, str] = {}
    issues: list[str] = []
    for name, _title in AUTHORED_RECORDS:
        path = base / name
        if path.is_file():
            try:
                sources[name] = path.read_text(encoding="utf-8")
            except (OSError, UnicodeError) as error:
                issues.append(f"unreadable {name}: {error}")
                continue
            # This is a structural check, never a claim of semantic completeness.
            body = FRONTMATTER_RE.sub("", sources[name])
            body, navigation_issues = authored_content(Document(name, body))
            issues.extend(f"{name}: {issue}" for issue in navigation_issues)
            if not body.strip():
                issues.append(f"empty or link-only authored record: {name}")
        else:
            issues.append(f"missing authored record: {name}")
    for name, _title in GENERATED_RECORDS:
        if base / name in generated:
            sources[name] = generated[base / name]
        else:
            issues.append(f"missing current generated record: {name}")
    metadata = ""
    if "README.md" in sources:
        match = FRONTMATTER_RE.match(sources["README.md"])
        if match:
            metadata = match.group(1)
            sources["README.md"] = sources["README.md"][match.end():]
    embedding = Embedding(base, sources)
    lines = [f"# {brick.title}", "", brick.summary, "",
             "## Assumptions and guarantees", "",
             "The following contract is authored manifest metadata, not an inferred formal specification.", "",
             "### Inputs", ""]
    for field in ("inputs", "assumptions"):
        if field == "assumptions":
            lines += ["", "### Assumptions", ""]
        values = brick.interface.get(field)
        values = values if isinstance(values, list) else []
        lines += [f"- {item}" for item in values] or [f"No authored {field} are recorded."]
    lines += ["", "### Guarantees", ""]
    outputs = brick.interface.get("outputs")
    for output in outputs if isinstance(outputs, list) else []:
        if isinstance(output, dict):
            lines += [f"- **{output.get('id', 'Unnamed output')}:** {output.get('statement', '')}"]
    terminology, definition_findings = _terminology(embedding)
    lines += ["", *terminology]
    if findings is not None:
        findings.extend(definition_findings)
    lines += ["", "## Source and evidence boundaries", "",
              "This generated reading page includes the authored records below in full. README.md remains the manifest authority; proof.md remains the conventional-derivation authority. The captured statements retain the exact formal premises. Assembly does not check proof completeness, semantic equivalence, source fidelity, physical applicability, or acceptance.", "",
              "## Contents", ""]
    for name, title in (*AUTHORED_RECORDS, *GENERATED_RECORDS):
        if name in sources:
            lines += [f"- [{title}](#{source_anchor(name)})"]
    for name, title in (*AUTHORED_RECORDS, *GENERATED_RECORDS):
        if name not in sources:
            continue
        lines += ["", f'<a id="{source_anchor(name)}"></a>', "", f"## {title}", "",
                  f"Source: [{name}]({name}). " + ("Authored record." if (name, title) in AUTHORED_RECORDS else "Generated correspondence; not an authored proof."), ""]
        lines += [embedding.render(name)]
        if name == "README.md" and metadata:
            lines += ["", "### Exact authored manifest metadata", "", "```yaml", metadata, "```"]
    issues.extend(embedding.issues)
    text = "\n".join(lines).rstrip() + "\n"
    issues.extend(f"assembled reader: {issue}" for issue in duplicate_anchors(text))
    return text, list(dict.fromkeys(issues))
