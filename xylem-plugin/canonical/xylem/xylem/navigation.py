"""Explainable, bounded navigation over extracted facts; no inferred proof edges."""
import json
from collections import defaultdict, deque

from . import store

EDGE_SCOPES = {
    "all": store.DEPENDENCY_EDGE_TYPES,
    "type": ("USES_IN_TYPE",),
    "proof": ("USES_IN_PROOF",),
    "imports": ("IMPORTS",),
}
MEANINGS = {
    "USES_IN_TYPE": "the source declaration's type uses the target constant",
    "USES_IN_PROOF": "the source declaration's proof uses the target constant",
    "IMPORTS": "the source module imports the target module",
    "COMPONENT_OF": "the declaration is explicitly listed as evidence for the component",
    "COMPONENT_RELATION": "the component relation is recorded by the component manifest",
}
SCOPE_NOTE = (
    "Indexed dependencies describe the last extraction, not a new proof or a "
    "prediction that changing a dependency will break its users. External stubs "
    "have no extracted body here. Reader/source links are provenance, not proof edges."
)

CAPTURE_STATUS_NOTES = {
    "captured": "dependency records were supplied by the declaration capture",
    "empty": "the capture supplied an empty dependency list; this is not an unavailable field",
    "partial": "the capture supplied only partial dependency data",
    "unavailable": "dependency records were not supplied; zero indexed edges do not mean no dependencies",
}


def _validate(limit=10, depth=None, edge_scope="all"):
    if not 1 <= limit <= 100:
        raise ValueError("limit must be between 1 and 100")
    if depth is not None and not 0 <= depth <= 100:
        raise ValueError("depth must be between 0 and 100")
    if edge_scope not in EDGE_SCOPES:
        raise ValueError("edge_scope must be all, type, proof, or imports")


def _resolve(conn, token):
    nid = store.resolve(conn, token)
    if nid is None:
        raise ValueError(f"no node matches '{token}'")
    return nid


def dependency_capture_summary(conn):
    """Summarize premise-data availability separately from graph edge counts."""
    counts = {}
    for row in conn.execute("SELECT kind, props FROM node WHERE kind='declaration'"):
        props = json.loads(row["props"] or "{}")
        state = props.get("dependency_capture") or {"status": "unavailable"}
        status = state.get("status", "unavailable")
        counts[status] = counts.get(status, 0) + 1
    if not counts:
        status = "unavailable"
    elif set(counts) == {"captured"}:
        status = "captured"
    elif set(counts) == {"empty"}:
        status = "empty"
    elif set(counts) == {"unavailable"}:
        status = "unavailable"
    else:
        status = "partial"
    return {
        "status": status,
        "counts": counts,
        "note": CAPTURE_STATUS_NOTES.get(status, "dependency-data coverage is mixed"),
    }


def _labels(conn, ids):
    """Return the compact node labels used by the legacy dependency API."""
    return [
        {key: value for key, value in node(conn, nid).items()
         if key in {"id", "kind", "name"}}
        for nid in ids
    ]


def dependency_traversal(conn, name, direction, depth=None):
    """Return a dependency traversal together with its capture-data state.

    An empty ``items`` list is meaningful only together with ``dependency_data``:
    ``unavailable`` means no dependency records were supplied, while ``empty``
    means the capture supplied an empty list.  ``partial`` and ``captured`` are
    retained even when the selected node has no indexed edges.
    """
    if direction not in {"dependencies", "dependents"}:
        raise ValueError("direction must be dependencies or dependents")
    _validate(depth=depth)
    nid = _resolve(conn, name)
    fwd, rev, _types = _graph(conn, "all")
    adjacency = fwd if direction == "dependencies" else rev
    ids = store.bfs(adjacency, nid, depth)
    return {
        "direction": direction,
        "target": node(conn, nid),
        "depth": depth,
        "count": len(ids),
        "items": _labels(conn, ids),
        "dependency_data": dependency_capture_summary(conn),
        "scope_note": SCOPE_NOTE,
    }


def node(conn, nid, detail=False):
    r = conn.execute("SELECT * FROM node WHERE id=?", (nid,)).fetchone()
    out = {key: r[key] for key in ("id", "kind", "name", "module", "decl_kind")}
    out["external_stub"] = bool(r["is_external"])
    out["source"] = {"file": r["src_file"], "start_line": r["src_start"],
                     "end_line": r["src_end"]}
    props = json.loads(r["props"] or "{}")
    out["dependency_capture"] = (
        props.get("dependency_capture")
        if r["kind"] == "declaration"
        else {"status": "not_applicable", "reason": "node is not a declaration"}
    )
    if detail:
        sig = json.loads(r["signature"] or "{}")
        out.update(docstring=r["docstring"], signature=sig.get("signature"),
                   binders=[{k: b.get(k) for k in ("name", "binderInfo", "type")}
                            for b in sig.get("binders", [])],
                   conclusion=sig.get("conclusion"),
                   axioms=props.get("axioms"),
                   metadata={k: v for k, v in props.items()
                             if k not in {"premises", "dependency_capture"}})
        if r["kind"] == "component":
            out["component"] = props
    return out


def _graph(conn, edge_scope):
    fwd, rev = defaultdict(set), defaultdict(set)
    types = defaultdict(set)
    for src, dst, typ in store.load_edges(conn, EDGE_SCOPES[edge_scope]):
        fwd[src].add(dst)
        rev[dst].add(src)
        types[src, dst].add(typ)
    return fwd, rev, types


def _edge(src, dst, types):
    ts = sorted(types[src, dst])
    return {"source": src, "target": dst, "types": ts,
            "evidence": "extracted",
            "origins": {
                t: ("module_graph.dot" if t == "IMPORTS"
                    else "components.json" if t in {"COMPONENT_OF", "COMPONENT_RELATION"}
                    else "declarations.json")
                for t in ts
            },
            "explanations": [MEANINGS[t] for t in ts]}


def _chain(prev, end):
    chain = []
    while end is not None:
        chain.append(end)
        end = prev[end]
    return chain[::-1]


def context(conn, name, limit=10, edge_scope="all"):
    """One declaration/module, direct neighbors, and separately labeled provenance."""
    _validate(limit, edge_scope=edge_scope)
    nid = _resolve(conn, name)
    fwd, rev, types = _graph(conn, edge_scope)
    result = {"node": node(conn, nid, True), "edge_scope": edge_scope,
              "scope_note": SCOPE_NOTE,
              "dependency_data": dependency_capture_summary(conn)}
    for label, adj in (("dependencies", fwd), ("dependents", rev)):
        ids = sorted(adj.get(nid, ()))
        result[label] = {
            "total": len(ids), "truncated": len(ids) > limit,
            "items": [{"node": node(conn, other),
                       "edge": _edge(nid, other, types) if label == "dependencies"
                       else _edge(other, nid, types)} for other in ids[:limit]],
        }
    # Walk only two provenance hops: declaration -> module -> reader page,
    # or declaration -> Brick -> source. Never mix these into proof paths.
    links, seen, queue = {}, {nid}, deque([(nid, 0)])
    while queue:
        cur, distance = queue.popleft()
        if distance == 2:
            continue
        rows = conn.execute(
            "SELECT src,dst,type FROM edge WHERE (src=? OR dst=?) "
            "AND type IN ('DECLARED_IN','PAIRED_WITH','BRICK_OF','CITES','BRICK_DEPENDS_ON',"
            "'COMPONENT_OF','COMPONENT_RELATION') "
            "ORDER BY src,dst,type", (cur, cur))
        for r in rows:
            other = r["dst"] if r["src"] == cur else r["src"]
            # A module's other declarations are neighbors, not provenance.
            if r["type"] == "DECLARED_IN" and r["src"] != nid:
                continue
            if r["type"] == "BRICK_OF" and r["src"] != nid:
                continue
            key = (r["src"], r["dst"], r["type"])
            if key in links:
                continue
            links[key] = {"source": r["src"], "target": r["dst"],
                          "type": r["type"], "node": node(conn, other, True)}
            if other not in seen:
                seen.add(other)
                queue.append((other, distance + 1))
    ordered = [links[k] for k in sorted(links)]
    result["provenance"] = {"total": len(ordered), "truncated": len(ordered) > limit,
                            "items": ordered[:limit]}
    return result


def explain(conn, name, target, depth=8, edge_scope="all"):
    """A shortest directed path with the actual extracted type/proof/import reasons."""
    _validate(depth=depth, edge_scope=edge_scope)
    a, b = _resolve(conn, name), _resolve(conn, target)
    fwd, _, types = _graph(conn, edge_scope)
    prev, queue = {a: None}, deque([(a, 0)])
    cutoff = False
    while queue and b not in prev:
        cur, d = queue.popleft()
        if d >= depth:
            cutoff |= any(n not in prev for n in fwd.get(cur, ()))
            continue
        for nxt in sorted(fwd.get(cur, ())):
            if nxt not in prev:
                prev[nxt] = cur
                queue.append((nxt, d + 1))
    chain = _chain(prev, b) if b in prev else []
    return {"found": bool(chain), "source": node(conn, a), "target": node(conn, b),
            "edge_scope": edge_scope, "max_depth": depth,
            "depth_limited": cutoff if not chain else False,
            "nodes": [node(conn, i) for i in chain],
            "steps": [_edge(s, t, types) for s, t in zip(chain, chain[1:])],
            "dependency_data": dependency_capture_summary(conn),
            "scope_note": SCOPE_NOTE}


def impact(conn, name, depth=3, limit=10, edge_scope="all"):
    """Bounded reverse dependency report with a witness chain for each affected node."""
    _validate(limit, depth, edge_scope)
    nid = _resolve(conn, name)
    _, rev, types = _graph(conn, edge_scope)
    prev, distance, queue = {nid: None}, {nid: 0}, deque([nid])
    found, cutoff = [], False
    while queue:
        cur = queue.popleft()
        if distance[cur] >= depth:
            cutoff |= any(n not in prev for n in rev.get(cur, ()))
            continue
        for nxt in sorted(rev.get(cur, ())):
            if nxt not in prev:
                prev[nxt] = cur
                distance[nxt] = distance[cur] + 1
                found.append(nxt)
                queue.append(nxt)
    items = []
    for other in found[:limit]:
        # Reverse the traversal chain so every witness follows depends-on edges.
        chain = _chain(prev, other)[::-1]
        items.append({"node": node(conn, other), "distance": distance[other],
                      "path": chain,
                      "steps": [_edge(s, t, types) for s, t in zip(chain, chain[1:])]})
    return {"direction": "impact", "target": node(conn, nid), "edge_scope": edge_scope, "max_depth": depth,
            "total_within_depth": len(found), "truncated": len(found) > limit,
            "depth_limited": cutoff, "items": items,
            "dependency_data": dependency_capture_summary(conn),
            "scope_note": SCOPE_NOTE}


def discover(conn, text, limit=10):
    """Literal all-term lookup across names, documentation, and rendered signatures."""
    _validate(limit)
    terms = text.casefold().split()
    if not terms:
        raise ValueError("query_text must contain a search term")
    matches = []
    for r in conn.execute("SELECT id,name,docstring,signature FROM node ORDER BY name,id"):
        sig = json.loads(r["signature"] or "{}")
        fields = {"name": r["name"], "docstring": r["docstring"] or "",
                  "signature": sig.get("signature") or ""}
        hits = {term: [key for key, value in fields.items() if term in value.casefold()]
                for term in terms}
        if all(hits.values()):
            score = sum(max({"name": 3, "docstring": 2, "signature": 1}[key]
                            for key in keys) for keys in hits.values())
            matches.append((score, r["name"], r["id"], hits))
    matches.sort(key=lambda x: (-x[0], x[1], x[2]))
    return {"query": text, "total": len(matches), "truncated": len(matches) > limit,
            "ranking": "all terms required; name=3, documentation=2, signature=1 per term",
            "items": [{"node": node(conn, nid), "score": score, "matched_fields": hits}
                      for score, _, nid, hits in matches[:limit]]}


def component_zoom(conn, name, limit=100):
    """Return one component with exact declaration evidence and typed relations."""
    _validate(limit)
    nid = _resolve(conn, name)
    row = conn.execute("SELECT kind FROM node WHERE id=?", (nid,)).fetchone()
    if row["kind"] != "component":
        raise ValueError(f"'{name}' is not a component node")
    declarations = [
        node(conn, r["src"], True)
        for r in conn.execute(
            "SELECT src FROM edge WHERE dst=? AND type='COMPONENT_OF' ORDER BY src LIMIT ?",
            (nid, limit),
        )
    ]
    relations = []
    for r in conn.execute(
        "SELECT src,dst,type,props FROM edge WHERE (src=? OR dst=?) "
        "AND type='COMPONENT_RELATION' ORDER BY src,dst",
        (nid, nid),
    ):
        other = r["dst"] if r["src"] == nid else r["src"]
        relations.append({
            "source": r["src"], "target": r["dst"], "type": r["type"],
            "direction": "out" if r["src"] == nid else "in",
            "node": node(conn, other, True),
            "props": json.loads(r["props"] or "{}"),
        })
    return {
        "component": node(conn, nid, True),
        "declarations": declarations,
        "declarations_truncated": len(declarations) >= limit,
        "relations": relations,
        "interpretation_note": (
            "Component membership and relations are manifest evidence; they do not add "
            "synthetic Lean proof edges or certify explanation quality."
        ),
    }


def overview(conn, surface=None, limit=100):
    """Return a readable component overview with formal/interpretive status labels."""
    _validate(limit)
    rows = conn.execute(
        "SELECT id,name,docstring,props FROM node WHERE kind='component' ORDER BY id"
    ).fetchall()
    items = []
    for row in rows:
        props = json.loads(row["props"] or "{}")
        if surface and props.get("surface") not in {surface, "shared", None}:
            continue
        count = conn.execute(
            "SELECT COUNT(*) AS c FROM edge WHERE dst=? AND type='COMPONENT_OF'", (row["id"],)
        ).fetchone()["c"]
        items.append({
            "id": row["id"], "name": row["name"], "title": row["docstring"],
            "surface": props.get("surface"), "role": props.get("role"),
            "formal_status": props.get("formal_status"),
            "interpretation_status": props.get("interpretation_status"),
            "evidence_status": props.get("evidence_status"),
            "declaration_count": count,
            "summary": props.get("summary"),
        })
    return {
        "surface": surface,
        "total_components": len(items),
        "truncated": len(items) > limit,
        "items": items[:limit],
        "status_note": (
            "formal_status is a source/index classification, not a claim that Lean "
            "establishes the component's human-readable explanation."
        ),
    }
