"""xylem — typed property-graph memory layer over the ctrllib Lean corpus.

store.py   shared graph primitives (adjacency, BFS, PageRank)
build.py   idempotent SQLite build from DOT + extractor JSON + wiki frontmatter
query.py   graph-native query CLI (dependents/dependencies/hubs/impact/path/orphans/search)
server.py  MCP server exposing query.py's operations as tools

The package is importable directly from this repository with ``PYTHONPATH``;
installation metadata is not required. The indexed reader pages default to a
ClearFocus sibling of the Lean repository; use ``XYLEM_VAULT_LEAN`` or
``--vault`` for another input tree.
"""

__version__ = "0.1.0"
