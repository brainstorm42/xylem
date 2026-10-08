#!/usr/bin/env python
"""Graph-native query CLI over the xylem store. Subcommands:
dependents (alias statement_dependents), dependencies (alias
statement_dependencies), hubs, impact, path, orphans, search, unresolved,
bricks, similar, overview, components. status. --json on each. dependents/dependencies/impact/path print a stderr
caveat: extraction covers the selected local graph as of the last rebuild;
the extractor's internal-detail policy determines indexed coverage and external
stubs are not expanded.
Every subcommand also prints a stderr staleness warning when
xylem.db predates its own build inputs."""
import argparse
import json
import sys
from pathlib import Path

from . import navigation, reviewer, similarity, store
from .build import DATA_DIR, VAULT_LEAN

DEP = store.DEPENDENCY_EDGE_TYPES

# The extractor traverses opaque proof bodies, so dependency edges include
# proof uses as well as declaration types.
DEP_CAVEAT = (
    "note: dependency edges cover the selected local extraction as of the last "
    "extract; the extractor's capture policy determines indexed coverage and "
    "external stubs are not expanded. Edges reflect the last capture, so rebuild "
    "after changing the source or capture artifact."
)


def _caveat():
    # Loud, unconditional stderr note for every dependency-edge traversal.
    print(DEP_CAVEAT, file=sys.stderr)


def _emit(rows, as_json, header=None, empty_note="(none)"):
    # Print rows as JSON or a fixed-width table. empty_note overrides the
    # bare "(none)" (a dependency traversal must not print a bare
    # "(none)" a caller could read as "confirmed no callers exist").
    if as_json:
        print(json.dumps(rows, indent=2))
        return
    if not rows:
        print(empty_note)
        return
    if isinstance(rows[0], dict):
        if header:
            print(header)
        for r in rows:
            print("  ".join(str(v) for v in r.values()))
    else:
        for r in rows:
            print(r)


def _emit_dependency(result, as_json, empty_note):
    """Emit dependency rows without hiding the capture-data availability state."""
    if as_json:
        print(json.dumps(result, indent=2, ensure_ascii=False))
        return
    state = result["dependency_data"]
    print(f"dependency data: {state['status']} — {state['note']}")
    _emit(result["items"], False, "kind  name", empty_note=empty_note)


def _need(conn, token):
    # Resolve or exit with a named error.
    try:
        nid = store.resolve(conn, token)
    except ValueError as error:
        print(f"error: {error}", file=sys.stderr)
        sys.exit(3)
    if nid is None:
        print(f"error: no node matches '{token}'", file=sys.stderr)
        sys.exit(3)
    return nid


def _labels(conn, ids):
    # Map node ids to {id, kind, name} rows preserving order.
    if not ids:
        return []
    marks = ",".join("?" for _ in ids)
    got = {r["id"]: r for r in conn.execute(
        f"SELECT id, kind, name FROM node WHERE id IN ({marks})", tuple(ids))}
    return [{"id": i, "kind": got[i]["kind"], "name": got[i]["name"]} for i in ids if i in got]


def cmd_dependents(conn, args):
    # Reverse BFS over dependency edges: who depends on the target.
    # See DEP_CAVEAT for selected-extract and external-stub limits.
    _caveat()
    try:
        result = navigation.dependency_traversal(conn, args.name, "dependents", args.depth)
    except ValueError as error:
        print(f"error: {error}", file=sys.stderr)
        sys.exit(3)
    _emit_dependency(result, args.json,
                     "(no dependents indexed for this target; see dependency data above)")


def cmd_dependencies(conn, args):
    # Forward BFS over dependency edges: what the target depends on.
    # See DEP_CAVEAT for selected-extract and external-stub limits.
    _caveat()
    try:
        result = navigation.dependency_traversal(conn, args.name, "dependencies", args.depth)
    except ValueError as error:
        print(f"error: {error}", file=sys.stderr)
        sys.exit(3)
    _emit_dependency(result, args.json,
                     "(no dependencies indexed for this target; see dependency data above)")


def cmd_hubs(conn, args):
    # Rank nodes by degree (dependency edges) or PageRank.
    if args.by == "pagerank":
        rows = conn.execute(
            "SELECT id, kind, name, rank FROM node ORDER BY rank DESC LIMIT ?", (args.n,)
        ).fetchall()
        out = [{"id": r["id"], "kind": r["kind"], "name": r["name"],
                "rank": round(r["rank"], 6)} for r in rows]
    else:
        deg = {}
        for src, dst, _t in store.load_edges(conn, DEP):
            deg[src] = deg.get(src, 0) + 1
            deg[dst] = deg.get(dst, 0) + 1
        top = sorted(deg.items(), key=lambda kv: kv[1], reverse=True)[: args.n]
        labels = {r["id"]: r for r in _labels(conn, [i for i, _ in top])}
        by_id = {r["id"]: r for r in labels.values()}
        out = [{"id": i, "kind": by_id[i]["kind"], "name": by_id[i]["name"], "degree": d}
               for i, d in top if i in by_id]
    _emit(out, args.json, "hub")


def cmd_impact(conn, args):
    # Reverse-BFS blast radius of a module node.
    # See DEP_CAVEAT for selected-extract and external-stub limits.
    _caveat()
    _, rev = store.adjacency(store.load_edges(conn, DEP))
    nid = _need(conn, args.module)
    items = _labels(conn, store.bfs(rev, nid, None))
    result = {
        "direction": "impact",
        "target": navigation.node(conn, nid),
        "depth": None,
        "count": len(items),
        "items": items,
        "dependency_data": navigation.dependency_capture_summary(conn),
        "scope_note": navigation.SCOPE_NOTE,
    }
    if args.json:
        print(json.dumps(result, indent=2, ensure_ascii=False))
        return
    state = result["dependency_data"]
    print(f"dependency data: {state['status']} — {state['note']}")
    _emit(items, False, "kind  name",
          empty_note="(no impact indexed for this target; see dependency data above)")


def cmd_path(conn, args):
    # BFS shortest dependency path a->b.
    # See DEP_CAVEAT for selected-extract and external-stub limits.
    _caveat()
    fwd, _ = store.adjacency(store.load_edges(conn, DEP))
    a, b = _need(conn, args.a), _need(conn, args.b)
    chain = store.shortest_path(fwd, a, b)
    if chain is None:
        print("error: no dependency path", file=sys.stderr)
        sys.exit(4)
    _emit(chain, args.json)


def cmd_orphans(conn, args):
    # Nodes with no incident dependency edges (containment edges excluded).
    incident = set()
    for src, dst, _t in store.load_edges(conn, DEP):
        incident.add(src)
        incident.add(dst)
    rows = conn.execute("SELECT id FROM node").fetchall()
    orphan_ids = [r["id"] for r in rows if r["id"] not in incident]
    _emit(_labels(conn, orphan_ids), args.json, "kind  name")


def cmd_unresolved(conn, args):
    """List premises Extract.lean recorded as used but never resolved a full
    declaration for — external stub nodes (is_external=1) still cited by a
    USES_IN_TYPE/USES_IN_PROOF edge. Scope to one declaration's own premises
    with `name`; omit it for the corpus-wide list, ranked by how many
    declarations cite each unresolved premise."""
    where = "n.is_external = 1"
    params = ()
    if args.name:
        nid = _need(conn, args.name)
        where += " AND e.src = ?"
        params = (nid,)
    rows = conn.execute(
        f"""SELECT n.id, n.kind, n.name, n.module, COUNT(*) AS used_by
            FROM edge e JOIN node n ON n.id = e.dst
            WHERE e.type IN ('USES_IN_TYPE', 'USES_IN_PROOF') AND {where}
            GROUP BY n.id ORDER BY used_by DESC, n.name""",
        params,
    ).fetchall()
    out = [{"id": r["id"], "kind": r["kind"], "name": r["name"],
            "module": r["module"], "used_by": r["used_by"]} for r in rows]
    _emit(out, args.json, "kind  name  module  used_by")


def cmd_bricks(conn, args):
    """List Brick-identity nodes: module, cited source, resolved flag, declaration
    count. Optional `name` scopes to one declaration's own bricks, one module's
    bricks, or one source's bricks (resolves against decl/module/source names)."""
    scope_decl_ids, scope_module, scope_bibkey = None, None, None
    if args.name:
        nid = _need(conn, args.name)
        row = conn.execute("SELECT kind, module, name FROM node WHERE id=?", (nid,)).fetchone()
        if row["kind"] == "declaration":
            scope_decl_ids = {r["dst"] for r in conn.execute(
                "SELECT dst FROM edge WHERE src=? AND type='BRICK_OF'", (nid,))}
        elif row["kind"] == "source":
            scope_bibkey = row["name"]
        else:
            scope_module = row["module"] or row["name"]

    out = []
    for b in conn.execute("SELECT id, module, props FROM node WHERE kind='brick'").fetchall():
        if scope_decl_ids is not None and b["id"] not in scope_decl_ids:
            continue
        props = json.loads(b["props"] or "{}")
        modules = {m if m.startswith('Ctrllib.') else 'Ctrllib.' + m
                   for m in props.get('lean_modules', [])}
        if scope_module is not None and b["module"] != scope_module and scope_module not in modules:
            continue
        if scope_bibkey is not None and props.get("bibkey") != scope_bibkey and scope_bibkey not in props.get('source_keys', []):
            continue
        n = conn.execute(
            "SELECT COUNT(*) c FROM edge WHERE dst=? AND type='BRICK_OF'", (b["id"],)
        ).fetchone()["c"]
        out.append({"id": b["id"], "module": b["module"], "bibkey": props.get("bibkey"),
                    "resolved": props.get("resolved"), "n_declarations": n,
                    "status": props.get('status'), "canonical": props.get('canonical', False),
                    "issues": props.get('issues', [])})
    out.sort(key=lambda r: (r["module"] or "", r["id"]))
    _emit(out, args.json, "id  module  bibkey  resolved  n_declarations")


def cmd_search(conn, args):
    # Substring match on node name.
    rows = conn.execute(
        "SELECT id, kind, name FROM node WHERE name LIKE ? ORDER BY name",
        (f"%{args.substr}%",),
    ).fetchall()
    _emit([{"id": r["id"], "kind": r["kind"], "name": r["name"]} for r in rows],
          args.json, "kind  name")


def cmd_similar(conn, args):
    """Print a report-only structural shortlist for one exact declaration."""
    try:
        result = similarity.query_similar(
            conn, args.name, limit=args.limit, all_kinds=args.all_kinds,
            cross_module_only=args.cross_module_only,
        )
    except similarity.SimilarityError as error:
        print(f"error: {error}", file=sys.stderr)
        return 2
    if args.json:
        print(json.dumps(result, indent=2))
        return 0
    print("rank  name  module  kind  shape  heads  type-premises  proof-premises")
    for candidate in result["candidates"]:
        scores = candidate["scores"]
        print(f"{candidate['rank']}  {candidate['name']}  {candidate['module']}  "
              f"{candidate['kind']}  {scores['shape']:.6f}  {scores['semantic_heads']:.6f}  "
              f"{scores['type_premises']:.6f}  {scores['proof_premises']:.6f}")
    if not result["candidates"]:
        print("(no structurally usable candidates)")
    print("report-only: inspect premises, domains, frames, and the exact theorem type before reuse")
    return 0


def cmd_components(conn, args):
    try:
        if args.name:
            result = navigation.component_zoom(conn, args.name, args.limit)
        else:
            result = navigation.overview(conn, args.surface, args.limit)
    except ValueError as error:
        print(f"error: {error}", file=sys.stderr)
        return 2
    print(json.dumps(result, indent=2, ensure_ascii=False) if args.json else json.dumps(result, ensure_ascii=False))
    return 0


def cmd_overview(conn, args):
    try:
        result = navigation.overview(conn, args.surface, args.limit)
    except ValueError as error:
        print(f"error: {error}", file=sys.stderr)
        return 2
    if args.json:
        print(json.dumps(result, indent=2, ensure_ascii=False))
    else:
        print(f"surface: {result['surface'] or 'all'}")
        print(f"components: {result['total_components']}")
        for item in result["items"]:
            print("  ".join(str(item.get(key) or "") for key in
                              ("id", "role", "formal_status", "interpretation_status", "summary")))
        print(result["status_note"])
    return 0


def cmd_navigation(conn, args):
    """Use the same structured result on CLI and MCP."""
    if args.cmd == "impact" and not args.details:
        args.module = args.name
        return cmd_impact(conn, args)
    try:
        if args.cmd == "discover":
            result = navigation.discover(conn, args.name, args.limit)
        elif args.cmd == "context":
            result = navigation.context(conn, args.name, args.limit, args.edge_scope)
        elif args.cmd == "explain":
            result = navigation.explain(conn, args.name, args.target, args.depth, args.edge_scope)
        else:
            result = navigation.impact(conn, args.name, args.depth, args.limit, args.edge_scope)
    except ValueError as error:
        print(f"error: {error}", file=sys.stderr)
        return 2
    print(json.dumps(result, indent=2, ensure_ascii=False))
    return 0


def _build_inputs():
    # Build-input paths at the default locations build.py itself reads: the
    # two derived Lean files (DATA_DIR, via refresh_inputs.sh) plus the
    # newest reader page -- a stand-in for the frontmatter
    # parse_pages scans, since no per-page build stamp exists to compare against.
    inputs = [
        ("module_graph.dot", DATA_DIR / "module_graph.dot"),
        ("declarations.json", DATA_DIR / "declarations.json"),
    ]
    pages = [p for p in VAULT_LEAN.glob("*.md") if p.is_file()]
    if pages:
        newest = max(pages, key=lambda p: p.stat().st_mtime)
        inputs.append((f"wiki frontmatter ({newest.name})", newest))
    return inputs


def cmd_status(conn, args):
    """Print database counts and whether the default inputs are newer."""
    warning = store.freshness_warning(args.db, _build_inputs())
    rows = {
        "database": str(args.db),
        "fresh": warning is None,
        "warning": warning,
        "nodes": {r["kind"]: r["count"] for r in conn.execute(
            "SELECT kind, COUNT(*) AS count FROM node GROUP BY kind")},
        "edges": {r["type"]: r["count"] for r in conn.execute(
            "SELECT type, COUNT(*) AS count FROM edge GROUP BY type")},
        "declaration_dependency_data": navigation.dependency_capture_summary(conn),
    }
    if args.json:
        print(json.dumps(rows, indent=2))
    else:
        print(f"database: {rows['database']}")
        print(f"fresh: {rows['fresh']}")
        if warning:
            print(warning)
        print("nodes: " + " / ".join(f"{k} {v}" for k, v in rows["nodes"].items()))
        print("edges: " + " / ".join(f"{k} {v}" for k, v in rows["edges"].items()))


def cmd_review(conn, args):
    """Write a bounded, publication-oriented review and optionally emit JSON."""
    try:
        evidence = reviewer.load_evidence(args.evidence, args.name) if args.evidence else None
        inputs = [
            {"label": label, "path": str(path)}
            for label, path in getattr(args, "_freshness_inputs", [])
        ]
        report = reviewer.build_report(
            conn,
            args.name,
            freshness_warning=getattr(args, "_freshness_warning", None),
            freshness_inputs=inputs,
            evidence=evidence,
            source_root=args.source_root,
        )
        if args.output:
            reviewer.write_html(report, args.output)
        if args.json:
            print(json.dumps(report, indent=2, ensure_ascii=False))
        elif args.output:
            print(f"wrote {args.output}")
        else:
            print("review built (use --json or --output PATH.html to retain it)")
    except (OSError, TypeError, ValueError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 2


def build_parser():
    ap = argparse.ArgumentParser(description="Query the xylem property-graph store.")
    ap.add_argument("--db", default=str(store.db_path_default()))
    sub = ap.add_subparsers(dest="cmd", required=True)

    p = sub.add_parser("status", help="show graph counts and input freshness")
    p.add_argument("--json", action="store_true")
    p.add_argument("--db", dest="db", default=argparse.SUPPRESS)
    p.set_defaults(func=cmd_status)

    # statement_dependents/statement_dependencies are non-breaking aliases;
    # dependents/dependencies keep working
    # identically; kept as aliases (harmless, may already be referenced
    # elsewhere) but the help text no longer claims "statement-level only" --
    # that would be inaccurate now, not just outdated.
    dep_help = "selected extract as of the last rebuild -- see stderr note"
    for cmd_name in ("dependents", "statement_dependents"):
        p = sub.add_parser(cmd_name, help=f"who depends on NAME ({dep_help})")
        p.add_argument("name")
        p.add_argument("--depth", type=int, default=None); p.add_argument("--json", action="store_true")
        p.set_defaults(func=cmd_dependents)

    for cmd_name in ("dependencies", "statement_dependencies"):
        p = sub.add_parser(cmd_name, help=f"what NAME depends on ({dep_help})")
        p.add_argument("name")
        p.add_argument("--depth", type=int, default=None); p.add_argument("--json", action="store_true")
        p.set_defaults(func=cmd_dependencies)

    p = sub.add_parser("hubs"); p.add_argument("--by", choices=("degree", "pagerank"), default="degree")
    p.add_argument("-n", type=int, default=10); p.add_argument("--json", action="store_true")
    p.set_defaults(func=cmd_hubs)

    for name in ("context", "explain", "impact", "discover"):
        p = sub.add_parser(name, help="bounded, explained graph result (JSON)")
        p.add_argument("name")
        p.add_argument("--json", action="store_true")
        p.add_argument("--limit", type=int, default=10)
        p.add_argument("--edge-scope", choices=tuple(navigation.EDGE_SCOPES), default="all")
        if name in ("explain", "impact"):
            p.add_argument("--depth", type=int, default=8 if name == "explain" else 3)
        if name == "impact":
            p.add_argument("--details", action="store_true",
                           help="bounded impact with edge reasons; otherwise retain legacy list")
        if name == "explain":
            p.add_argument("target")
        p.set_defaults(func=cmd_navigation)

    p = sub.add_parser("overview", help="list the indexed source-backed proof components")
    p.add_argument("--surface", choices=("solution", "challenge", "shared"), default=None)
    p.add_argument("--limit", type=int, default=100)
    p.add_argument("--json", action="store_true")
    p.set_defaults(func=cmd_overview)

    p = sub.add_parser("components", help="list components or zoom into one exact component")
    p.add_argument("name", nargs="?", default=None)
    p.add_argument("--surface", choices=("solution", "challenge", "shared"), default=None)
    p.add_argument("--limit", type=int, default=100)
    p.add_argument("--json", action="store_true")
    p.set_defaults(func=cmd_components)

    p = sub.add_parser("path", help=f"shortest A->B ({dep_help})")
    p.add_argument("a"); p.add_argument("b")
    p.add_argument("--json", action="store_true"); p.set_defaults(func=cmd_path)

    p = sub.add_parser("orphans"); p.add_argument("--json", action="store_true")
    p.set_defaults(func=cmd_orphans)

    p = sub.add_parser("search"); p.add_argument("substr")
    p.add_argument("--json", action="store_true"); p.set_defaults(func=cmd_search)

    p = sub.add_parser("similar", help="report-only structural shortlist for NAME")
    p.add_argument("name"); p.add_argument("--top", dest="limit", type=int, default=10)
    p.add_argument("--all-kinds", action="store_true")
    p.add_argument("--cross-module", dest="cross_module_only", action="store_true")
    p.add_argument("--json", action="store_true"); p.set_defaults(func=cmd_similar)

    p = sub.add_parser("unresolved"); p.add_argument("name", nargs="?", default=None)
    p.add_argument("--json", action="store_true"); p.set_defaults(func=cmd_unresolved)

    p = sub.add_parser("bricks"); p.add_argument("name", nargs="?", default=None)
    p.add_argument("--json", action="store_true"); p.set_defaults(func=cmd_bricks)

    p = sub.add_parser("review", help="bounded publication-oriented review of one exact local declaration")
    p.add_argument("name")
    p.add_argument("--output", help="write a self-contained HTML report")
    p.add_argument("--evidence", help="display supplied evidence JSON after exact declaration matching")
    p.add_argument("--source-root", help="optional root below which the recorded source range may be read")
    p.add_argument("--json", action="store_true", help="emit the reviewer payload on stdout")
    p.set_defaults(func=cmd_review)
    return ap


def main(argv=None):
    args = build_parser().parse_args(argv)
    if args.cmd == "status" and not Path(args.db).is_file():
        payload = {"database": str(args.db), "fresh": False,
                   "warning": f"database not found: {args.db}",
                   "nodes": {}, "edges": {}}
        if args.json:
            print(json.dumps(payload, indent=2))
        else:
            print(f"database: {args.db}")
            print("fresh: False")
            print(payload["warning"])
        return 1
    conn = store.open_db(args.db)
    freshness_inputs = _build_inputs()
    warning = store.freshness_warning(args.db, freshness_inputs)
    if warning:
        print(warning, file=sys.stderr)
    args._freshness_warning = warning
    args._freshness_inputs = freshness_inputs
    try:
        result = args.func(conn, args)
    finally:
        conn.close()
    return 0 if result is None else result


if __name__ == "__main__":
    sys.exit(main())
