#!/usr/bin/env python
"""Minimal read-only MCP surface for the Xylem property graph.

The CLI remains the complete operator interface. MCP clients receive one
project-scoped tool for lookup, similarity, and explained dependency navigation.
The DB path resolves once at import time from XYLEM_DB or store.db_path_default().

Run: python -m xylem.server   (stdio transport for an MCP client config), or
`xylem-mcp` once this package is installed
(console script, see pyproject.toml).

Uses mcp.server.MCPServer (the SDK's ergonomic decorator-based server class,
mcp>=2.0.0) -- this replaced the older mcp.server.fastmcp.FastMCP name; verified
against the actual installed package (2026-07-29), not assumed from training.
"""
import os
from pathlib import Path
from typing import Literal

from mcp.server import MCPServer

from . import discovery, navigation, query, similarity, store

DB_PATH = os.environ.get("XYLEM_DB", str(store.db_path_default()))

mcp = MCPServer(name="xylem")


def _conn():
    """Open the graph in SQLite read-only mode."""
    return store.open_db(DB_PATH)


def _resolve_or_error(conn, token):
    try:
        nid = store.resolve(conn, token)
    except ValueError as error:
        return None, {"error": str(error)}
    if nid is None:
        return None, {"error": f"no node matches '{token}'"}
    return nid, None


def _labels(conn, ids):
    return query._labels(conn, ids)


def dependents(name: str, depth: int | None = None) -> dict:
    """Return dependents together with the capture-data availability state."""
    conn = _conn()
    try:
        try:
            return navigation.dependency_traversal(conn, name, "dependents", depth)
        except ValueError as error:
            return {"error": str(error)}
    finally:
        conn.close()


def dependencies(name: str, depth: int | None = None) -> dict:
    """Return dependencies together with the capture-data availability state."""
    conn = _conn()
    try:
        try:
            return navigation.dependency_traversal(conn, name, "dependencies", depth)
        except ValueError as error:
            return {"error": str(error)}
    finally:
        conn.close()


def hubs(by: str = "degree", n: int = 10) -> list[dict]:
    """Top-n most-connected nodes. by: 'degree' (dependency edge count) or 'pagerank'."""
    if by not in ("degree", "pagerank"):
        return [{"error": "by must be 'degree' or 'pagerank'"}]
    conn = _conn()
    try:
        if by == "pagerank":
            rows = conn.execute(
                "SELECT id, kind, name, rank FROM node ORDER BY rank DESC, id LIMIT ?", (n,)
            ).fetchall()
            return [{"id": r["id"], "kind": r["kind"], "name": r["name"],
                     "rank": round(r["rank"], 6)} for r in rows]
        deg = {}
        for src, dst, _t in store.load_edges(conn, query.DEP):
            deg[src] = deg.get(src, 0) + 1
            deg[dst] = deg.get(dst, 0) + 1
        top = sorted(deg.items(), key=lambda kv: (-kv[1], kv[0]))[:n]
        by_id = {r["id"]: r for r in _labels(conn, [i for i, _ in top])}
        return [{"id": i, "kind": by_id[i]["kind"], "name": by_id[i]["name"], "degree": d}
                for i, d in top if i in by_id]
    finally:
        conn.close()


def impact(module: str) -> list[dict] | dict:
    """Blast radius of a module: every node that transitively depends on it."""
    conn = _conn()
    try:
        nid, err = _resolve_or_error(conn, module)
        if err:
            return err
        _, rev = store.adjacency(store.load_edges(conn, query.DEP))
        return _labels(conn, store.bfs(rev, nid, None))
    finally:
        conn.close()


def path(a: str, b: str) -> list[str] | dict:
    """Shortest dependency path from node a to node b (list of node ids), if one exists."""
    conn = _conn()
    try:
        na, erra = _resolve_or_error(conn, a)
        if erra:
            return erra
        nb, errb = _resolve_or_error(conn, b)
        if errb:
            return errb
        fwd, _ = store.adjacency(store.load_edges(conn, query.DEP))
        chain = store.shortest_path(fwd, na, nb)
        if chain is None:
            return {"error": "no dependency path"}
        return chain
    finally:
        conn.close()


def orphans() -> list[dict]:
    """Nodes with no incident dependency edges (containment edges excluded)."""
    conn = _conn()
    try:
        incident = set()
        for src, dst, _t in store.load_edges(conn, query.DEP):
            incident.add(src)
            incident.add(dst)
        rows = conn.execute("SELECT id FROM node").fetchall()
        orphan_ids = [r["id"] for r in rows if r["id"] not in incident]
        return _labels(conn, orphan_ids)
    finally:
        conn.close()


def search(substr: str) -> list[dict]:
    """Substring match on node name (declaration, module, or wiki page)."""
    conn = _conn()
    try:
        rows = conn.execute(
            "SELECT id, kind, name FROM node WHERE name LIKE ? ORDER BY name",
            (f"%{substr}%",),
        ).fetchall()
        return [{"id": r["id"], "kind": r["kind"], "name": r["name"]} for r in rows]
    finally:
        conn.close()


def similar(name: str, limit: int = 10, all_kinds: bool = False,
            cross_module_only: bool = False) -> dict:
    """Return the report-only structural shortlist for an exact declaration."""
    conn = _conn()
    try:
        try:
            return similarity.query_similar(
                conn, name, limit=limit, all_kinds=all_kinds,
                cross_module_only=cross_module_only,
            )
        except similarity.SimilarityError as error:
            return {"error": str(error)}
    finally:
        conn.close()


def techniques(manifest_path: str) -> dict:
    """Run the fixed-manifest structural overlay without writing any artifact."""
    roots = _authorized_roots()
    try:
        manifest = _authorized_discovery_manifest(manifest_path, roots)
        result = discovery.discover(manifest)
        return {"ok": True, "operation": "techniques", "data": result}
    except (OSError, discovery.DiscoveryError, ValueError) as error:
        return _error("techniques", str(error))


def _error(operation, message):
    return {"ok": False, "operation": operation, "error": message}


def _authorized_roots() -> list[Path]:
    """Return roots permitted for MCP discovery-manifest inputs."""
    raw = os.environ.get("XYLEM_AUTHORIZED_ROOTS", "")
    values = [Path(item).expanduser().resolve() for item in raw.split(os.pathsep) if item]
    if not values:
        values = [Path(DB_PATH).expanduser().resolve().parent]
        data_root = os.environ.get("DATA")
        if data_root:
            values.append(Path(data_root).expanduser().resolve())
    return list(dict.fromkeys(values))


def _authorized_file(raw_path: str, roots: list[Path] | None = None) -> Path:
    candidate = Path(raw_path).expanduser().resolve()
    if not candidate.is_file():
        raise ValueError(f"MCP file is not a regular file: {candidate}")
    roots = roots or _authorized_roots()
    for root in roots:
        try:
            candidate.relative_to(root)
            return candidate
        except ValueError:
            continue
    rendered = ", ".join(str(root) for root in roots)
    raise ValueError(f"MCP file access denied outside configured authorized roots: {rendered}")


def _authorized_directory(raw_path: str, roots: list[Path] | None = None) -> Path:
    candidate = Path(raw_path).expanduser().resolve()
    if not candidate.is_dir():
        raise ValueError(f"MCP directory is not a directory: {candidate}")
    roots = roots or _authorized_roots()
    for root in roots:
        try:
            candidate.relative_to(root)
            return candidate
        except ValueError:
            continue
    rendered = ", ".join(str(root) for root in roots)
    raise ValueError(f"MCP directory access denied outside configured authorized roots: {rendered}")


def _authorized_discovery_manifest(raw_path: str, roots: list[Path] | None = None) -> Path:
    """Authorize a manifest and every resolved input path it names."""
    roots = roots or _authorized_roots()
    manifest = _authorized_file(raw_path, roots)
    parsed = discovery.load_manifest(manifest)
    for immediate in (
        parsed.capture_path,
        parsed.trace_path,
        parsed.type_evidence_path,
        parsed.source_manifest_path,
    ):
        if immediate is not None:
            _authorized_file(str(immediate), roots)
    for path in discovery.referenced_paths(manifest):
        if path.is_dir():
            _authorized_directory(str(path), roots)
        else:
            _authorized_file(str(path), roots)
    return manifest


def _status():
    db = Path(DB_PATH)
    if not db.is_file():
        return _error("status", f"database not found: {db}")
    conn = _conn()
    try:
        nodes = {
            row["kind"]: row["count"]
            for row in conn.execute(
                "SELECT kind, COUNT(*) AS count FROM node GROUP BY kind"
            )
        }
        edges = {
            row["type"]: row["count"]
            for row in conn.execute(
                "SELECT type, COUNT(*) AS count FROM edge GROUP BY type"
            )
        }
        dependency_data = navigation.dependency_capture_summary(conn)
    finally:
        conn.close()
    warning = store.freshness_warning(db, query._build_inputs())
    return {
        "ok": warning is None,
        "operation": "status",
        "data": {
            "database": str(db),
            "fresh": warning is None,
            "warning": warning,
            "nodes": nodes,
            "edges": edges,
            "declaration_dependency_data": dependency_data,
        },
    }


@mcp.tool()
def xylem_query(
    operation: Literal["status", "search", "dependencies", "dependents", "path", "similar", "techniques",
                       "context", "explain", "impact", "discover", "overview", "components"],
    query_text: str | None = None,
    target: str | None = None,
    depth: int | None = None,
    limit: int = 10,
    all_kinds: bool = False,
    cross_module_only: bool = False,
    manifest_path: str | None = None,
    edge_scope: Literal["all", "type", "proof", "imports"] = "all",
    surface: Literal["solution", "challenge", "shared"] | None = None,
) -> dict:
    """Query Xylem without writes.

    Use query_text for search, dependencies, dependents, similar, and the source
    of a path. Use target only for the path destination. Depth optionally bounds
    dependency traversals. Similar is report-only and accepts limit, all_kinds,
    and cross_module_only. Context returns the statement, source, direct users
    and premises, and separate provenance. Discover searches names, docs, and
    signatures with matched-field reasons. Explain returns a directed path with
    edge reasons (target required, default depth 8). Impact returns reverse users
    and witness paths (default depth 3). These new reports use limit (1..100) and
    edge_scope to bound/select results; they do not certify theorem reuse.
    Techniques takes manifest_path and runs the separate read-only structural
    overlay; it does not write the report or certify mathematical meaning.
    """
    if operation == "status":
        return _status()
    if operation == "techniques":
        if not manifest_path:
            return _error(operation, "manifest_path is required")
        return techniques(manifest_path)
    if operation in ("overview", "components"):
        conn = _conn()
        try:
            if operation == "overview":
                data = navigation.overview(conn, surface, limit)
            elif query_text:
                data = navigation.component_zoom(conn, query_text, limit)
            else:
                data = navigation.overview(conn, surface, limit)
        except ValueError as error:
            return _error(operation, str(error))
        finally:
            conn.close()
        return {"ok": True, "operation": operation, "data": data,
                "index_warning": store.freshness_warning(DB_PATH, query._build_inputs())}
    if not query_text:
        return _error(operation, "query_text is required")
    if depth is not None and depth < 0:
        return _error(operation, "depth must be nonnegative")

    if operation in ("context", "explain", "impact", "discover"):
        if operation == "explain" and not target:
            return _error(operation, "target is required for explain")
        conn = _conn()
        try:
            if operation == "context":
                data = navigation.context(conn, query_text, limit, edge_scope)
            elif operation == "discover":
                data = navigation.discover(conn, query_text, limit)
            elif operation == "explain":
                data = navigation.explain(conn, query_text, target,
                                          8 if depth is None else depth, edge_scope)
            else:
                data = navigation.impact(conn, query_text, 3 if depth is None else depth,
                                         limit, edge_scope)
        except ValueError as error:
            return _error(operation, str(error))
        finally:
            conn.close()
    elif operation == "search":
        data = search(query_text)
    elif operation == "dependencies":
        data = dependencies(query_text, depth)
    elif operation == "dependents":
        data = dependents(query_text, depth)
    elif operation == "similar":
        data = similar(query_text, limit, all_kinds, cross_module_only)
    elif operation == "path":
        if not target:
            return _error(operation, "target is required for path")
        data = path(query_text, target)
    else:
        return _error(operation, f"unknown operation '{operation}'")

    if isinstance(data, dict) and "error" in data:
        return _error(operation, data["error"])
    return {"ok": True, "operation": operation, "data": data,
            "index_warning": store.freshness_warning(DB_PATH, query._build_inputs())}


def main():
    mcp.run()


if __name__ == "__main__":
    main()
