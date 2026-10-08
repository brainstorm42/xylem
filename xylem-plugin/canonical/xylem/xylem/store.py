#!/usr/bin/env python
"""Shared xylem store layer: DB open, adjacency, node resolution, BFS, PageRank."""
import os
import sqlite3
from collections import defaultdict, deque
from pathlib import Path

# Edge direction convention (load-bearing): src depends-on / uses dst.
DEPENDENCY_EDGE_TYPES = ("IMPORTS", "USES_IN_TYPE", "USES_IN_PROOF")
# BRICK_OF/CITES are provenance, not proof dependency: a
# declaration isn't "dependent on" its Brick the way it depends on a premise.
CONTAINMENT_EDGE_TYPES = ("DECLARED_IN", "PAIRED_WITH", "BRICK_OF", "CITES", "BRICK_DEPENDS_ON")


def open_db(path):
    """Open an existing xylem DB read-only, preserving normal WAL visibility."""
    uri = Path(path).resolve().as_uri() + "?mode=ro"
    conn = sqlite3.connect(uri, uri=True)
    conn.row_factory = sqlite3.Row
    return conn


def load_edges(conn, types=None):
    """Return edge rows (src, dst, type), optionally filtered to a type set."""
    if types is None:
        rows = conn.execute("SELECT src, dst, type FROM edge").fetchall()
    else:
        marks = ",".join("?" for _ in types)
        rows = conn.execute(
            f"SELECT src, dst, type FROM edge WHERE type IN ({marks})", tuple(types)
        ).fetchall()
    return [(r["src"], r["dst"], r["type"]) for r in rows]


def adjacency(edges):
    """Build forward (src->dsts) and reverse (dst->srcs) adjacency dicts."""
    fwd, rev = defaultdict(list), defaultdict(list)
    for src, dst, _type in edges:
        fwd[src].append(dst)
        rev[dst].append(src)
    return fwd, rev


def resolve(conn, token):
    """Resolve an exact id/name or a unique literal substring; reject ambiguity."""
    row = conn.execute("SELECT id FROM node WHERE id = ?", (token,)).fetchone()
    if row:
        return row["id"]
    rows = conn.execute("SELECT id FROM node WHERE name = ? ORDER BY id", (token,)).fetchall()
    if not rows:
        rows = conn.execute(
            "SELECT id FROM node WHERE instr(lower(name), lower(?)) > 0 ORDER BY id",
            (token,),
        ).fetchall()
    if len(rows) > 1:
        choices = ", ".join(r["id"] for r in rows[:8])
        suffix = f" (and {len(rows) - 8} more)" if len(rows) > 8 else ""
        raise ValueError(f"ambiguous node '{token}'; use an exact id: {choices}{suffix}")
    return rows[0]["id"] if rows else None


def bfs(adj, start, depth=None):
    """BFS from start over adjacency; return set of reachable ids (excluding start)."""
    seen, out = {start}, []
    q = deque([(start, 0)])
    while q:
        node, d = q.popleft()
        if depth is not None and d >= depth:
            continue
        for nxt in adj.get(node, ()):
            if nxt not in seen:
                seen.add(nxt)
                out.append(nxt)
                q.append((nxt, d + 1))
    return out


def shortest_path(adj, a, b):
    """BFS shortest path a->b over adjacency; return id chain or None."""
    if a == b:
        return [a]
    prev, q = {a: None}, deque([a])
    while q:
        node = q.popleft()
        for nxt in adj.get(node, ()):
            if nxt not in prev:
                prev[nxt] = node
                if nxt == b:
                    chain, cur = [], b
                    while cur is not None:
                        chain.append(cur)
                        cur = prev[cur]
                    return list(reversed(chain))
                q.append(nxt)
    return None


def pagerank(node_ids, edges, damping=0.85, max_iter=100, tol=1e-8):
    """Power-iteration PageRank over dependency edges. rank accumulates at pointed-to
    (dst) nodes, so a foundational lemma many decls depend on outranks a leaf."""
    ids = list(node_ids)
    n = len(ids)
    if n == 0:
        return {}
    out_links = defaultdict(list)
    for src, dst, _type in edges:
        if src in node_ids and dst in node_ids:
            out_links[src].append(dst)
    rank = {i: 1.0 / n for i in ids}
    teleport = (1.0 - damping) / n
    for _ in range(max_iter):
        nxt = {i: teleport for i in ids}
        dangling = 0.0
        for i in ids:
            outs = out_links.get(i)
            if not outs:
                dangling += rank[i]
                continue
            share = damping * rank[i] / len(outs)
            for dst in outs:
                nxt[dst] += share
        # redistribute dangling mass uniformly (damped)
        dshare = damping * dangling / n
        for i in ids:
            nxt[i] += dshare
        delta = sum(abs(nxt[i] - rank[i]) for i in ids)
        rank = nxt
        if delta < tol:
            break
    return rank


def db_path_default():
    """Return XYLEM_DB or the repository-relative generated database path."""
    package_root = Path(__file__).resolve().parent.parent
    generated = package_root.parent / "generated" / "xylem" / "xylem.db"
    return Path(os.environ.get("XYLEM_DB", str(generated)))


def freshness_warning(db_path, inputs):
    """Return a staleness warning if db_path predates any file in `inputs`
    (mtime comparison), else None. `inputs` is an iterable of (label, path)
    pairs; missing paths are skipped, not errors. Falls back to mtimes
    because schema.sql carries no build-stamp column yet."""
    db_path = Path(db_path)
    if not db_path.is_file():
        return None
    from . import input_state
    conn = sqlite3.connect(db_path.resolve().as_uri() + '?mode=ro', uri=True)
    conn.row_factory = sqlite3.Row
    try:
        warning = input_state.current_warning(conn)
        tracked = conn.execute("SELECT 1 FROM sqlite_master WHERE name='input_state'").fetchone()
    finally:
        conn.close()
    if warning or tracked:
        return warning
    db_mtime = db_path.stat().st_mtime
    stale = [label for label, path in inputs
             if Path(path).is_file() and Path(path).stat().st_mtime > db_mtime]
    if not stale:
        return None
    return (
        "warning: xylem.db is stale -- rebuilt input(s) postdate the last "
        "build (" + ", ".join(stale) + "). Rebuild with build.py before "
        "trusting these results."
    )
