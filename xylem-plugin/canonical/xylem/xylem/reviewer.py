"""Bounded, publication-oriented review reports over the Xylem store.

This module deliberately reports recorded graph facts and their limits.  It
does not run Lean, infer proof validity, or treat the derived index as a
checker.
"""

from __future__ import annotations

import html
import json
from pathlib import Path
from typing import Any
from urllib.parse import quote, urlsplit

from . import navigation

AXIOM_BASELINE = ["propext", "Classical.choice", "Quot.sound"]
MAX_GRAPH_LIMIT = 100
MAX_GRAPH_DEPTH = 3


def _json(value: str | None, default: Any = None) -> Any:
    if not value:
        return default
    try:
        return json.loads(value)
    except (TypeError, json.JSONDecodeError):
        return default


def _exact_target(conn, declaration: str) -> tuple[str, dict[str, Any], Any]:
    """Resolve only an exact local declaration name; reject modules and stubs."""
    row = conn.execute("SELECT * FROM node WHERE name = ?", (declaration,)).fetchone()
    if row is None:
        raise ValueError(f"no exact declaration matches '{declaration}'")
    if row["kind"] != "declaration":
        raise ValueError(f"review target must be a declaration, not {row['kind']}: {declaration}")
    if row["is_external"]:
        raise ValueError(f"review target must be a local declaration, not an external stub: {declaration}")
    return row["id"], navigation.node(conn, row["id"], True), row


def _dependency_section(context: dict[str, Any], edge_type: str) -> dict[str, Any]:
    """Return one bounded direct dependency section from indexed nodes."""
    raw = context["dependencies"]
    dependency_data = context.get("dependency_data") or {
        "status": "unavailable",
        "counts": {},
        "note": "dependency-data coverage was not reported",
    }
    return {
        "count": raw["total"],
        "shown": len(raw["items"]),
        "truncated": raw["truncated"],
        "items": raw["items"],
        "edge_type": edge_type,
        "status": dependency_data["status"],
        "dependency_data": dependency_data,
        "note": dependency_data["note"],
        "external_stubs_not_expanded": True,
    }


def _impact_section(impact: dict[str, Any], dependency_data: dict[str, Any]) -> dict[str, Any]:
    items = []
    filtered_external = 0
    for item in impact["items"]:
        if item["node"].get("external_stub"):
            filtered_external += 1
            continue
        items.append(item)
    return {
        "count_within_depth": impact["total_within_depth"],
        "shown": len(items),
        "truncated": impact["truncated"],
        "depth_limited": impact["depth_limited"],
        "max_depth": impact["max_depth"],
        "filtered_external_stub": filtered_external,
        "items": items,
        "status": dependency_data["status"],
        "dependency_data": dependency_data,
        "note": dependency_data["note"],
        "paths_are_extracted_dependency_witnesses": True,
    }


def _axiom_assessment(row: Any) -> dict[str, Any]:
    """Assess the extractor's target-level transitive axiom record."""
    props = _json(row["props"], None)
    recorded = None if props is None or "axioms" not in props else props["axioms"]
    if recorded is not None:
        recorded = sorted(set(recorded))
    extra = [] if recorded is None else sorted(set(recorded) - set(AXIOM_BASELINE))
    if recorded is None:
        assessment = "recorded_axioms_unknown"
    elif extra:
        assessment = "extra_recorded_axioms"
    else:
        assessment = "within_recorded_baseline"
    return {
        "baseline": list(AXIOM_BASELINE),
        "recorded_transitive": recorded,
        "extra_recorded": extra,
        "recorded_axioms_unknown": recorded is None,
        "assessment": assessment,
        "follow_up": bool(extra or recorded is None),
        "needs_review": bool(extra or recorded is None),
        "proof_validity_verdict": None,
        "note": "Recorded axioms are an audit input; this report does not establish proof validity.",
    }


def _external_coverage(conn, target_id: str) -> dict[str, Any]:
    rows = conn.execute(
        """SELECT n.id, n.kind, n.name, n.module, n.is_external,
                  GROUP_CONCAT(e.type) AS edge_types
           FROM edge e JOIN node n ON n.id = e.dst
           WHERE e.src = ? AND e.type IN ('USES_IN_TYPE','USES_IN_PROOF')
             AND n.is_external = 1
           GROUP BY n.id, n.kind, n.name, n.module, n.is_external
           ORDER BY n.name""",
        (target_id,),
    ).fetchall()
    items = [
        {"id": row["id"], "kind": row["kind"], "name": row["name"],
         "module": row["module"], "edge_types": sorted(set(row["edge_types"].split(",")))}
        for row in rows[:MAX_GRAPH_LIMIT]
    ]
    return {
        "external_reference_count": len(rows),
        "shown": len(items),
        "truncated": len(rows) > MAX_GRAPH_LIMIT,
        "items": items,
        "axioms_available": False,
        "note": "External declarations are recorded references; their bodies and axioms are not expanded in this store.",
    }


def load_evidence(path: str | Path, declaration: str) -> dict[str, Any]:
    """Load supplied evidence and require the exact declaration identity."""
    evidence_path = Path(path)
    try:
        payload = json.loads(evidence_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise ValueError(f"could not read evidence JSON {evidence_path}: {exc}") from exc
    if not isinstance(payload, dict):
        raise TypeError("evidence JSON must be an object")
    if payload.get("declaration") != declaration:
        raise ValueError(
            "evidence declaration does not match the exact review target "
            f"({payload.get('declaration')!r} != {declaration!r})"
        )
    return payload


def _validate_evidence(evidence: dict[str, Any], declaration: str) -> None:
    if not isinstance(evidence, dict):
        raise TypeError("evidence must be an object")
    if evidence.get("declaration") != declaration:
        raise ValueError(
            "evidence declaration does not match the exact review target "
            f"({evidence.get('declaration')!r} != {declaration!r})"
        )


def _source_view(row: Any, source_root: str | Path | None) -> dict[str, Any]:
    source = {"file": row["src_file"], "start_line": row["src_start"], "end_line": row["src_end"]}
    if source_root is None:
        source.update(available=False, note="source reading disabled; pass --source-root to opt in")
        return source
    if not row["src_file"]:
        source.update(available=False, note="declaration has no recorded source file")
        return source
    root = Path(source_root).expanduser().resolve()
    candidate = (root / row["src_file"]).resolve()
    try:
        candidate.relative_to(root)
    except ValueError:
        source.update(available=False, note="recorded source path is outside --source-root")
        return source
    if not candidate.is_file():
        source.update(available=False, note="recorded source file is not present below --source-root")
        return source
    try:
        lines = candidate.read_text(encoding="utf-8").splitlines()
    except (OSError, UnicodeError) as exc:
        source.update(available=False, note=f"source could not be read: {exc}")
        return source
    start = max(1, int(row["src_start"] or 1))
    end = min(len(lines), int(row["src_end"] or start))
    source.update(available=True, root=str(root), path=str(candidate), text="\n".join(lines[start - 1 : end]))
    return source


def build_report(
    conn,
    declaration: str,
    *,
    freshness_warning: str | None = None,
    freshness_inputs: list[dict[str, str]] | None = None,
    evidence: dict[str, Any] | None = None,
    source_root: str | Path | None = None,
) -> dict[str, Any]:
    """Build the bounded reviewer JSON payload from an open Xylem connection."""
    target_id, target, row = _exact_target(conn, declaration)
    if evidence is not None:
        _validate_evidence(evidence, declaration)
    contexts = {
        "proof": navigation.context(conn, declaration, MAX_GRAPH_LIMIT, "proof"),
        "type": navigation.context(conn, declaration, MAX_GRAPH_LIMIT, "type"),
    }
    impact = navigation.impact(conn, declaration, MAX_GRAPH_DEPTH, MAX_GRAPH_LIMIT, "all")
    all_context = navigation.context(conn, declaration, MAX_GRAPH_LIMIT, "all")
    payload = {
        "schema_version": 1,
        "declaration": {
            "name": target["name"],
            "full_name": target["name"],
            "type": target.get("signature"),
            "binders": target.get("binders", []),
            "conclusion": target.get("conclusion"),
            "kind": target.get("decl_kind"),
        },
        "source": _source_view(row, source_root),
        "axioms": _axiom_assessment(row),
        "coverage": _external_coverage(conn, target_id),
        "dependency_data": all_context["dependency_data"],
        "dependencies": {
            "proof": _dependency_section(contexts["proof"], "USES_IN_PROOF"),
            "type": _dependency_section(contexts["type"], "USES_IN_TYPE"),
        },
        "affected_local_results": _impact_section(impact, all_context["dependency_data"]),
        "provenance": all_context["provenance"],
        "freshness": (
            {
                "status": "checked",
                "warning": freshness_warning,
                "inputs": freshness_inputs,
                "summary": "No recorded input changes detected" if freshness_warning is None
                else "Selected-input or extraction-coverage warning; see details",
            }
            if freshness_inputs is not None
            else {
                "status": "unknown",
                "warning": "freshness was not checked by the caller",
                "inputs": [],
                "summary": "Freshness was not checked",
            }
        ),
        "limitations": [
            "The extractor's internal-detail policy determines which declarations enter the indexed graph; indexed local declarations remain visible.",
            "External references are counted from recorded direct edges, but their bodies and axioms are not expanded.",
            "The derived Xylem index records extraction facts; it is not a proof checker and this report gives no proof-validity verdict.",
            "Dependency paths are bounded to depth 3 and displayed neighborhoods to 100 items.",
            "Provenance links are displayed separately and are excluded from proof dependency impact.",
        ],
    }
    if evidence is not None:
        payload["evidence"] = evidence
    return payload


def _cell(value: Any) -> str:
    return html.escape("" if value is None else str(value), quote=True)



def _safe_evidence_href(value: Any) -> str | None:
    if not isinstance(value, str):
        return None
    parsed = urlsplit(value)
    if (
        not value
        or "\\" in value
        or any(ord(char) < 32 for char in value)
        or parsed.scheme
        or parsed.netloc
        or parsed.query
        or parsed.fragment
        or value.startswith("//")
    ):
        return None
    path = Path(value)
    if path.is_absolute() or ".." in path.parts:
        return None
    return quote(path.as_posix(), safe="/")


def _binder_table(binders: list[dict[str, Any]]) -> str:
    rows = []
    for binder in binders:
        info = binder.get("binderInfo") or "default"
        visibility = "implicit" if info in {"implicit", "strictImplicit", "instImplicit"} else "explicit"
        rows.append(
            "<tr><td>{}</td><td>{}</td><td>{}</td></tr>".format(
                _cell(binder.get("name")), _cell(binder.get("type")), _cell(visibility)
            )
        )
    if not rows:
        rows.append('<tr><td colspan="3" class="muted">No binders recorded.</td></tr>')
    return "<table><thead><tr><th>Name</th><th>Type</th><th>Visibility</th></tr></thead><tbody>{}</tbody></table>".format("".join(rows))


def _evidence_table(evidence: dict[str, Any]) -> str:
    rows = []
    for check in evidence.get("checks") or []:
        if not isinstance(check, dict):
            continue
        file_value = check.get("evidence_file")
        href = _safe_evidence_href(file_value)
        evidence_file = (
            f'<a href="{_cell(href)}">Read evidence log</a>' if href
            else _cell(file_value)
        )
        rows.append(
            '<tr><td style="width:24%">{}</td><td style="white-space:nowrap">{}</td>'
            '<td><div>{}</div><div>{}</div><details><summary>Command and limits</summary>'
            '<pre>{}</pre><p>{}</p></details></td></tr>'.format(
                _cell(str(check.get("name") or "Unnamed check").replace("_", " ")),
                _cell(check.get("status")), _cell(check.get("scope")), evidence_file,
                _cell(check.get("command")), _cell(check.get("limitations")),
            )
        )
    if not rows:
        rows.append('<tr><td colspan="3" class="muted">No checks supplied.</td></tr>')
    return '<table><thead><tr><th>Check</th><th style="white-space:nowrap">Result</th><th>Scope and record</th></tr></thead><tbody>{}</tbody></table>'.format("".join(rows))


def _provenance_table(provenance: dict[str, Any]) -> str:
    rows = []
    for item in provenance.get("items", []):
        node = item.get("node", {})
        rows.append(
            "<tr><td>{}</td><td>{}</td><td>{}</td></tr>".format(
                _cell(node.get("kind")), _cell(node.get("name")), _cell(item.get("type"))
            )
        )
    if not rows:
        rows.append('<tr><td colspan="3" class="muted">No provenance links recorded.</td></tr>')
    summary = (
        f"total {provenance.get('total', 0)}; shown {len(provenance.get('items', []))}; "
        f"truncated={provenance.get('truncated', False)}"
    )
    return f'<p class="muted">{_cell(summary)}</p><table><thead><tr><th>Kind</th><th>Name</th><th>Link type</th></tr></thead><tbody>{"".join(rows)}</tbody></table>'


def _dependency_details(section: dict[str, Any], label: str) -> str:
    dependency_data = section.get("dependency_data") or {
        "status": section.get("status", "unavailable"),
        "note": section.get("note", "dependency-data coverage was not reported"),
    }
    state = dependency_data.get("status", "unavailable")
    note = dependency_data.get("note", "dependency-data coverage was not reported")
    rows = []
    for item in section.get("items", []):
        node = item["node"]
        rows.append(
            '<li data-search="{search}"><code>{name}</code> '
            '<span class="muted">{module} · {stub}</span></li>'.format(
                search=_cell((node.get("name") or "") + " " + (node.get("module") or "")),
                name=_cell(node.get("name")), module=_cell(node.get("module")),
                stub="external stub" if node.get("external_stub") else "local",
            )
        )
    if not rows:
        rows.append(
            '<li class="muted">No dependency rows indexed; '
            f'dependency data state: {_cell(state)}. {_cell(note)}</li>'
        )
    summary = (
        f"{label}: data state {state}; count {section.get('count', 0)}; "
        f"shown {section.get('shown', 0)}; truncated={section.get('truncated', False)}; {note}"
    )
    return f'<details><summary>{_cell(summary)}</summary><ul class="deps">{"".join(rows)}</ul></details>'


def _coverage_details(coverage: dict[str, Any]) -> str:
    rows = []
    for item in coverage.get("items", []):
        rows.append(
            '<li><code>{}</code> <span class="muted">{} · {}</span></li>'.format(
                _cell(item.get("name")), _cell(item.get("module")),
                _cell(", ".join(item.get("edge_types", []))),
            )
        )
    if not rows:
        rows.append('<li class="muted">No external references recorded.</li>')
    summary = (
        f"External references: {coverage.get('external_reference_count', 0)} recorded; "
        f"shown {coverage.get('shown', 0)}; truncated={coverage.get('truncated', False)}"
    )
    return f'<details><summary>{_cell(summary)}</summary><ul>{"".join(rows)}</ul></details>'


def render_html(report: dict[str, Any]) -> str:
    decl = report["declaration"]
    source = report["source"]
    ax = report["axioms"]
    coverage = report.get("coverage", {
        "external_reference_count": 0, "shown": 0, "truncated": False,
    })
    affected = report["affected_local_results"]
    impact_dependency_data = affected.get("dependency_data") or {
        "status": affected.get("status", "unavailable"),
        "note": affected.get("note", "dependency-data coverage was not reported"),
    }
    impact_rows = []
    for item in affected["items"]:
        impact_rows.append(
            '<li><code>{}</code> <span class="muted">distance {} · path {}</span></li>'.format(
                _cell(item["node"].get("name")), _cell(item["distance"]),
                _cell(" → ".join(node_id for node_id in item["path"])),
            )
        )
    if not impact_rows:
        impact_rows.append(
            '<li class="muted">No affected local results indexed; '
            f'dependency data state: {_cell(impact_dependency_data.get("status", "unavailable"))}. '
            f'{_cell(impact_dependency_data.get("note", "dependency-data coverage was not reported"))}</li>'
        )
    source_block = (
        f'<details><summary>Read recorded source range</summary><pre>{_cell(source.get("text"))}</pre></details>'
        if source.get("available") else f'<p class="muted">{_cell(source.get("note"))}</p>'
    )
    evidence = report.get("evidence")
    if evidence is None:
        evidence_block = '<p class="muted">No supplied evidence JSON.</p>'
    else:
        evidence_block = (
            _evidence_table(evidence)
            + '<details><summary>Raw supplied evidence</summary><pre>'
            + _cell(json.dumps(evidence, indent=2, ensure_ascii=False))
            + '</pre></details><p class="muted">Supplied evidence is displayed as provided; it was not executed or independently authenticated by this report.</p>'
        )
    binder_table = _binder_table(decl.get("binders", []))
    provenance_block = _provenance_table(report["provenance"])
    deps = (
        _dependency_details(report["dependencies"]["proof"], "Direct proof dependencies")
        + _dependency_details(report["dependencies"]["type"], "Direct type dependencies")
    )
    axiom_message = (
        "Recorded axioms are within the displayed baseline."
        if ax["assessment"] == "within_recorded_baseline"
        else "Recorded axioms require follow-up because an extra axiom was recorded."
        if ax["assessment"] == "extra_recorded_axioms"
        else "The target's recorded axiom list is unavailable."
    )
    recorded_text = (
        ", ".join(ax["recorded_transitive"])
        if ax["recorded_transitive"]
        else "none (recorded empty list)"
        if ax["recorded_transitive"] == []
        else "unknown"
    )
    freshness = report.get("freshness", {
        "status": "unknown", "summary": "Freshness was not checked",
        "warning": "freshness was not checked by the caller",
    })
    template = """<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Proof dependency review: {title}</title><style>
body{{margin:0;background:#f6f7f9;color:#1f2933;font:16px/1.5 system-ui,-apple-system,BlinkMacSystemFont,"Segoe UI",sans-serif}}
main{{max-width:1100px;margin:0 auto;padding:2rem 1.25rem 4rem}} section,article{{background:#fff;border:1px solid #d8dee6;border-radius:10px;padding:1rem 1.15rem;margin:1rem 0;box-shadow:0 1px 2px #0000000b}}
h1{{font-size:1.65rem;margin:.2rem 0 .4rem}} h2{{font-size:1.2rem;margin:.2rem 0 .5rem}} code,pre{{font-family:ui-monospace,SFMono-Regular,Menlo,monospace}} code{{overflow-wrap:anywhere}} pre{{white-space:pre-wrap;overflow-wrap:anywhere;background:#f3f5f7;padding:.8rem;border-radius:6px;max-height:28rem;overflow:auto}} .muted{{color:#596675;font-size:.9rem}} ul{{padding-left:1.4rem}} li{{margin:.25rem 0}} input{{width:100%;box-sizing:border-box;padding:.55rem;border:1px solid #aeb8c4;border-radius:6px;font:inherit}} table{{border-collapse:collapse;width:100%;font-size:.93rem}} th,td{{border-bottom:1px solid #e0e5ea;text-align:left;padding:.45rem;vertical-align:top;overflow-wrap:anywhere}} th{{background:#f3f5f7}} details{{margin:.55rem 0}} summary{{cursor:pointer;font-weight:600}} a{{color:#175ca8}} @media print{{body{{background:#fff}} section,article{{box-shadow:none;break-inside:avoid}} .filter{{display:none}}}}
</style></head><body><main>
<h1>Proof dependency review</h1><p><code>{name}</code></p><nav><a href="#declaration">Declaration</a> · <a href="#axioms">Axioms</a> · <a href="#dependencies">Dependencies</a> · <a href="#impact">Impact</a> · <a href="#provenance">Provenance</a> · <a href="#evidence">Evidence</a></nav>
<article id="declaration"><h2>Declaration</h2><p><strong>{kind}</strong></p><p><code>{name}</code></p><h3>Type</h3><pre>{signature}</pre><h3>Binders</h3>{binder_table}<h3>Conclusion</h3><pre>{conclusion}</pre></article>
<section id="axioms"><h2>Recorded axiom assessment</h2><p>{axiom_message}</p><p>Baseline: <code>{baseline}</code></p><p>Recorded transitive axioms: <code>{recorded}</code></p><p>Extra recorded axioms: <code>{extra}</code></p><p class="muted">The report records an audit input and gives no proof-validity verdict.</p></section>
<section id="source"><h2>Source range</h2><p><code>{source_file}</code>, lines {start}–{end}</p>{source_block}</section>
<section class="filter"><h2>Dependency filter</h2><label for="dep-filter">Filter the displayed dependency rows</label><input id="dep-filter" oninput="filterDeps()" placeholder="type to filter"></section>
<section id="dependencies"><h2>Direct dependencies</h2>{deps}</section>
<section id="coverage"><h2>External graph coverage</h2><p class="muted">Their bodies and axioms were not expanded.</p>{coverage_details}</section>
<section id="impact"><h2>Affected local results</h2><p class="muted">dependency data state={impact_dependency_state}; count within depth {impact_count}; shown {impact_shown}; truncated={impact_truncated}; depth_limited={depth_limited}</p><ul>{impact_rows}</ul></section>
<section id="provenance"><h2>Provenance</h2><p class="muted">Provenance is separate from proof dependency impact.</p>{provenance}</section>
<section id="freshness"><h2>Freshness</h2><p>{freshness_summary}</p><p class="muted">status={freshness_status}; {freshness_warning}</p></section>
<section id="evidence"><h2>Supplied evidence</h2>{evidence_block}</section>
<section id="limitations"><h2>Limitations</h2><ul>{limitations}</ul></section>
<script>function filterDeps(){{const q=document.getElementById('dep-filter').value.toLowerCase();document.querySelectorAll('.deps li[data-search]').forEach(x=>x.hidden=!x.dataset.search.toLowerCase().includes(q));}}</script>
</main></body></html>"""
    return template.format(
        title=_cell(decl["name"]), name=_cell(decl["name"]), kind=_cell(decl.get("kind")),
        signature=_cell(decl.get("type")),
        binder_table=binder_table, conclusion=_cell(decl.get("conclusion") or "Not recorded"),
        baseline=_cell(", ".join(ax["baseline"])),
        recorded=_cell(recorded_text),
        extra=_cell(", ".join(ax["extra_recorded"]) or "none"), axiom_message=_cell(axiom_message),
        source_file=_cell(source.get("file")), start=_cell(source.get("start_line")),
        end=_cell(source.get("end_line")), source_block=source_block, deps=deps,
        coverage_details=_coverage_details(coverage), impact_count=_cell(affected["count_within_depth"]),
        impact_shown=_cell(affected["shown"]), impact_truncated=_cell(affected["truncated"]),
        depth_limited=_cell(affected["depth_limited"]), impact_rows="".join(impact_rows),
        impact_dependency_state=_cell(impact_dependency_data.get("status", "unavailable")),
        provenance=provenance_block, freshness_summary=_cell(freshness.get("summary", "Freshness was not checked")),
        freshness_status=_cell(freshness.get("status", "unknown")),
        freshness_warning=_cell(freshness.get("warning") or "none"),
        evidence_block=evidence_block,
        limitations="".join(f"<li>{_cell(item)}</li>" for item in report["limitations"]),
    )
def write_html(report: dict[str, Any], path: str | Path) -> Path:
    """Write one self-contained report."""
    output = Path(path)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(render_html(report), encoding="utf-8")
    return output
