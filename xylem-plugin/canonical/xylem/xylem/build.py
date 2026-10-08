#!/usr/bin/env python
"""Build the xylem typed-property-graph SQLite store from four derived inputs:
importGraph DOT, the Lean extractor JSON (contract v1), vault/lean/*.md frontmatter
(wiki pages + Brick source locators), and the corpus BibTeX (source bibliographic
data). Idempotent: drops and recreates every table on each run. Prints node/edge counts."""
import argparse
import json
import os
import re
import sqlite3
import sys
import tempfile
from pathlib import Path

from . import catalogue, config, input_state, similarity, store

PKG = Path(__file__).resolve().parent
VAULT_LEAN = config.vault_lean_default()
DATA_DIR = config.data_default()

DOT_EDGE = re.compile(r'"?([\w.]+)"?\s*->\s*"?([\w.]+)"?')
CTRLLIB_MODULE = re.compile(
    r"Ctrllib\.[A-Za-z_][A-Za-z0-9_]*"
)
LEAN_FILE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*\.lean")


def _is_ctrllib(module):
    # True when a module name lives under the Ctrllib root.
    return module == "Ctrllib" or module.startswith("Ctrllib.")


def _mod_node(module):
    # A module node row; is_external flags non-Ctrllib modules.
    return {
        "id": f"mod:{module}", "kind": "module", "name": module, "module": module,
        "decl_kind": None, "docstring": None, "src_file": None, "src_start": None,
        "src_end": None, "signature": None, "is_external": 0 if _is_ctrllib(module) else 1,
        "props": None, "rank": None,
    }


def _put(nodes, row, force):
    # Insert a node unless a fuller one already sits at that id (force overwrites).
    if force or row["id"] not in nodes:
        nodes[row["id"]] = row


def parse_dot(path, nodes, edges):
    """Add module nodes and IMPORTS edges from an importGraph DOT file.

    importGraph's DOT arrow `A -> B` means B imports A (verified against the real
    graph: GammaInvertible imports DetGamma, yet the DOT draws DetGamma -> Gamma-
    Invertible). Under the store's src-depends-on-dst convention the IMPORTS edge is
    therefore dst-depends-on-src: the DOT destination depends on the DOT source."""
    text = Path(path).read_text(encoding="utf-8")
    for src, dst in DOT_EDGE.findall(text):
        _put(nodes, _mod_node(src), force=False)
        _put(nodes, _mod_node(dst), force=False)
        edges.append((f"mod:{dst}", f"mod:{src}", "IMPORTS", None))


def _stub(nodes, name, module, external):
    # Mint an external premise stub if absent (a real Ctrllib decl wins via force=True).
    _put(nodes, {
        "id": f"decl:{name}", "kind": "declaration", "name": name, "module": module,
        "decl_kind": None, "docstring": None, "src_file": None, "src_start": None,
        "src_end": None, "signature": None, "is_external": 1 if external else 0,
        "props": None, "rank": None,
    }, force=False)


def _dependency_capture_status(capture, declaration):
    """Describe premise-data availability without inferring dependencies."""
    projection = capture.get("capture_projection")
    premises = declaration.get("premises")
    if not isinstance(projection, dict) or "premises_included" not in projection:
        return {
            "status": "unavailable",
            "reason": "the capture does not declare premise-data coverage",
        }
    if projection.get("premises_included") is False:
        return {
            "status": "unavailable",
            "reason": "premises_included=false; dependency records were not supplied",
        }
    if projection.get("premises_included") is not True:
        return {
            "status": "unavailable",
            "reason": "premises_included is not a supported boolean value",
        }
    if projection.get("premises_complete") is False:
        return {
            "status": "partial",
            "reason": "the capture marks premise data as partial",
        }
    if not isinstance(premises, list):
        return {
            "status": "partial",
            "reason": "the declaration premise field is not a list",
        }
    if not premises:
        return {
            "status": "empty",
            "reason": "the capture supplied an empty dependency list",
        }
    return {
        "status": "captured",
        "record_count": len(premises),
        "reason": "dependency records were supplied by the declaration capture",
    }


def parse_declarations(path, nodes, edges):
    """Add declaration nodes, DECLARED_IN, and USES_IN_TYPE/PROOF edges from the extractor JSON.

    Contract v1 (RULED-FINAL 2026-07-18): FLAT premises = [{name, module, in_type,
    in_proof, external}], one row per constant with independent booleans, no
    premise_nodes — this builder derives the node/edge split on insert. Raises
    ValueError on malformed/empty JSON (the caller maps it to a named nonzero exit)."""
    raw = Path(path).read_text(encoding="utf-8")
    try:
        data = json.loads(raw)
    except json.JSONDecodeError as e:
        raise ValueError(f"malformed extractor JSON {path}: {e}") from e
    if data.get('errors'):
        raise ValueError(f"extractor reported errors in {path}: {data['errors']}")
    for d in data.get("declarations", []):
        module = d["module"]
        rng = d.get("range") or {}
        start = (rng.get("start") or [None])[0]
        end = (rng.get("end") or [None])[0]
        sig = {
            "binders": d.get("binders", []),
            "conclusion": d.get("conclusion"),
            "conclusion_tree": d.get("conclusion_tree"),
            "signature": d.get("signature"),
        }
        _put(nodes, {
            "id": f"decl:{d['name']}", "kind": "declaration", "name": d["name"],
            "module": module, "decl_kind": d.get("kind"), "docstring": d.get("doc"),
            "src_file": module.replace(".", "/") + ".lean", "src_start": start,
            "src_end": end, "signature": json.dumps(sig), "is_external": 0,
            "props": json.dumps({
                "premises": d.get("premises", []),
                "axioms": d.get("axioms", []),
                "dependency_capture": _dependency_capture_status(data, d),
            }),
            "rank": None,
        }, force=True)
        _put(nodes, _mod_node(module), force=False)
        edges.append((f"decl:{d['name']}", f"mod:{module}", "DECLARED_IN", None))
    # premise nodes + edges: in_type->USES_IN_TYPE, in_proof->USES_IN_PROOF. Mint external
    # stubs on first sight; a constant used in both type and proof yields both edges.
    for d in data.get("declarations", []):
        for p in (d.get("premises") or []):
            name = p["name"]
            tid = f"decl:{name}"
            if tid not in nodes:
                _stub(nodes, name, p.get("module"), bool(p.get("external")))
            if p.get("in_type"):
                edges.append((f"decl:{d['name']}", tid, "USES_IN_TYPE", None))
            if p.get("in_proof"):
                edges.append((f"decl:{d['name']}", tid, "USES_IN_PROOF", None))


def _read_frontmatter(path):
    # Parse the leading YAML block of a wiki page; {} when absent or malformed.
    import yaml
    text = path.read_text(encoding="utf-8")
    if not text.startswith("---"):
        return {}
    end = text.find("\n---", 3)
    if end == -1:
        return {}
    return yaml.safe_load(text[3:end]) or {}


def _page_module(fm):
    """Resolve a lean-module page to one exact Ctrllib module name.

    Older pages identify the source with ``lean_file: X.lean`` while newer
    pages use ``module: Ctrllib.X``.  A supplied lean_file is authoritative;
    malformed paths are not interpreted by Path.stem, and module-only pages
    must name a real Ctrllib namespace rather than merely containing the
    string ``Ctrllib``.
    """
    if "lean_file" in fm:
        lean_file = fm.get("lean_file")
        if not isinstance(lean_file, str) or not LEAN_FILE.fullmatch(lean_file):
            return None
        return "Ctrllib." + Path(lean_file).stem
    module = fm.get("module")
    if isinstance(module, str) and CTRLLIB_MODULE.fullmatch(module):
        return module
    return None


def parse_pages(lean_dir, nodes, edges):
    """Add wiki_page nodes and PAIRED_WITH edges from lean-module frontmatter."""
    lean_dir = Path(lean_dir)
    if not lean_dir.is_dir():
        return
    for page in sorted(lean_dir.glob("*.md")):
        fm = _read_frontmatter(page)
        if fm.get("type") != "lean-module":
            continue
        slug = page.stem
        _put(nodes, {
            "id": f"wiki:{slug}", "kind": "wiki_page", "name": slug, "module": None,
            "decl_kind": None, "docstring": fm.get("title"), "src_file": None,
            "src_start": None, "src_end": None, "signature": None, "is_external": 0,
            "props": json.dumps({
                "abbr": fm.get("abbr"), "branch": fm.get("branch"),
                "status": fm.get("status"), "sources": fm.get("sources", []),
            }), "rank": None,
        }, force=True)
        module = _page_module(fm)
        if module:
            _put(nodes, _mod_node(module), force=False)
            edges.append((f"wiki:{slug}", f"mod:{module}", "PAIRED_WITH", None))


def _bib_entries(bib_path):
    # Bibliography is an optional explicit input; missing or malformed data
    # leaves source nodes thin rather than blocking the graph build.
    if not bib_path:
        return {}
    path = Path(bib_path)
    if not path.is_file():
        return {}
    helper_candidates = (
        path.resolve().parent.parent / "vault" / "research" / "build_bibliography.py",
        path.resolve().parent / "build_bibliography.py",
    )
    helper = next((candidate for candidate in helper_candidates if candidate.is_file()), None)
    if helper is None:
        return {}
    import importlib.util
    spec = importlib.util.spec_from_file_location("build_bibliography", helper)
    bb = importlib.util.module_from_spec(spec)
    try:
        spec.loader.exec_module(bb)
        entries = bb.parse_bib(path.read_text(encoding="utf-8"))
    except (ValueError, OSError):
        return {}
    return {e["bibkey"]: e for e in entries}


def _source_node(bibkey, bib_entries):
    # A source node row for bibkey; thin (null bibliographic fields) if bib_entries lacks it.
    entry = bib_entries.get(bibkey, {})
    title = (entry.get("title") or "").strip("{}") or None
    return {
        "id": f"src:{bibkey}", "kind": "source", "name": bibkey, "module": None,
        "decl_kind": None, "docstring": title, "src_file": None,
        "src_start": None, "src_end": None, "signature": None, "is_external": 0,
        "props": json.dumps({
            "author": entry.get("author"), "year": entry.get("year"),
            "wiki_page": f"vault/research/sources/{bibkey}.md",
        }), "rank": None,
    }


def _theorem_bricks(module, theorem_provenance, sources, bib_entries, nodes, edges):
    """Per-theorem bricks from `theorem_provenance:`. Finer than the (module,
    bibkey) candidates below: each entry names exactly one declaration, so its
    brick is always `resolved` regardless of how many sources the module cites
    overall. Returns the set of declaration ids claimed here, so the coarse
    pass can exclude them (a declaration is either precisely attributed or an
    ambiguous candidate — never counted as both)."""
    claimed = set()
    for theorem, entry in (theorem_provenance or {}).items():
        did = f"decl:Ctrllib.{theorem}"
        if did not in nodes or nodes[did]["kind"] != "declaration":
            continue  # theorem_provenance names a decl the extractor didn't emit; skip, don't guess
        kind = (entry or {}).get("kind")
        if kind == "paper":
            bibkey = entry.get("bibkey")
            if not bibkey or bibkey not in sources:
                continue  # lint's job to flag this; build.py never trusts an unvalidated entry
            _put(nodes, _source_node(bibkey, bib_entries), force=False)
            brick_id = f"brick:{module}.{theorem}:{bibkey}"
            props = {"bibkey": bibkey, "kind": "paper", "resolved": True, "per_theorem": True}
            edges.append((brick_id, f"src:{bibkey}", "CITES", None))
        elif kind == "mathlib":
            path = entry.get("mathlib")
            if not path:
                continue
            brick_id = f"brick:{module}.{theorem}:mathlib"
            props = {"kind": "mathlib_derived", "mathlib_path": path,
                      "resolved": True, "per_theorem": True}
        elif kind == "new_result":
            brick_id = f"brick:{module}.{theorem}:new_result"
            props = {"kind": "new_result", "resolved": True, "per_theorem": True}
        else:
            continue  # unknown kind; lint's job, not build.py's, to flag it
        _put(nodes, {
            "id": brick_id, "kind": "brick", "name": f"{module}.{theorem}", "module": module,
            "decl_kind": None, "docstring": None, "src_file": None, "src_start": None,
            "src_end": None, "signature": None, "is_external": 0,
            "props": json.dumps(props), "rank": None,
        }, force=True)
        edges.append((did, brick_id, "BRICK_OF", None))
        claimed.add(did)
    return claimed


def parse_bricks(lean_dir, bib_entries, nodes, edges):
    """Add Brick-identity + source nodes from lean-module frontmatter.

    Brick identity rides the source locator, not the Lean declaration name
    (report.md:112, appendix.md:68 — RULED-FINAL). Two grains, finest first:

    Per-theorem `theorem_provenance:` entries route their
    named declaration to its own resolved brick — see _theorem_bricks.

    Per-module (the fallback floor): one brick node per
    (module, cited bibkey) for every declaration NOT claimed by a per-theorem
    entry. A module citing exactly one source is `resolved` — an unambiguous
    declaration-to-source attribution (GiordanoErrata's worked example: one
    source, several declarations). A module citing several sources is NOT
    auto-split per theorem beyond what theorem_provenance: already resolved —
    frontmatter carries no per-theorem locator for the rest, and inventing one
    would be a silent, unreviewed attribution — so every STILL-unclaimed
    declaration in that module links to every remaining brick candidate, each
    flagged unresolved. A (module, bibkey) pair with zero unclaimed
    declarations left (theorem_provenance: covered the whole module) mints no
    brick at all — nothing to flag as ambiguous once nothing is left ambiguous."""
    lean_dir = Path(lean_dir)
    if not lean_dir.is_dir():
        return
    for page in sorted(lean_dir.glob("*.md")):
        fm = _read_frontmatter(page)
        if fm.get("type") != "lean-module":
            continue
        lean_file = fm.get("lean_file")
        sources = fm.get("sources") or []
        if not lean_file:
            continue
        module = "Ctrllib." + Path(lean_file).stem
        claimed = _theorem_bricks(module, fm.get("theorem_provenance"), sources, bib_entries, nodes, edges)
        if not sources:
            continue
        decl_ids = [nid for nid, row in nodes.items()
                    if row["kind"] == "declaration" and row["module"] == module
                    and not row["is_external"] and nid not in claimed]
        if not decl_ids:
            continue
        resolved = len(sources) == 1
        for bibkey in sources:
            _put(nodes, _source_node(bibkey, bib_entries), force=False)
            brick_id = f"brick:{module}:{bibkey}"
            _put(nodes, {
                "id": brick_id, "kind": "brick", "name": f"{module}:{bibkey}", "module": module,
                "decl_kind": None, "docstring": None, "src_file": None, "src_start": None,
                "src_end": None, "signature": None, "is_external": 0,
                "props": json.dumps({
                    "bibkey": bibkey, "resolved": resolved, "n_sources": len(sources),
                }), "rank": None,
            }, force=True)
            edges.append((brick_id, f"src:{bibkey}", "CITES", None))
            for did in decl_ids:
                edges.append((did, brick_id, "BRICK_OF", None))


def rank(nodes, edges):
    """Fill node['rank'] with PageRank over dependency edges only."""
    dep = [(s, d, t) for (s, d, t, _p) in edges if t in store.DEPENDENCY_EDGE_TYPES]
    scores = store.pagerank(set(nodes.keys()), dep)
    for nid, row in nodes.items():
        row["rank"] = scores.get(nid, 0.0)


def write_db(db_path, nodes, edges, input_payload=None):
    """Build a complete replacement before publishing it to concurrent readers."""
    Path(db_path).parent.mkdir(parents=True, exist_ok=True)
    fd, temporary = tempfile.mkstemp(prefix='.xylem-', suffix='.db', dir=Path(db_path).parent)
    os.close(fd)
    conn = sqlite3.connect(temporary)
    try:
        conn.executescript(
            "DROP TABLE IF EXISTS similarity_feature; "
            "DROP TABLE IF EXISTS edge; DROP TABLE IF EXISTS node;"
        )
        conn.executescript((PKG / "schema.sql").read_text(encoding="utf-8"))
        cols = ("id", "kind", "name", "module", "decl_kind", "docstring", "src_file",
                "src_start", "src_end", "signature", "is_external", "props", "rank")
        conn.executemany(
            f"INSERT INTO node ({','.join(cols)}) VALUES ({','.join('?' for _ in cols)})",
            [tuple(row[c] for c in cols) for row in nodes.values()],
        )
        # dedupe edges on (src,dst,type) — the PK forbids repeats
        seen, rows = set(), []
        for src, dst, etype, props in edges:
            key = (src, dst, etype)
            if key not in seen:
                seen.add(key)
                rows.append((src, dst, etype, props))
        conn.executemany("INSERT INTO edge (src, dst, type, props) VALUES (?, ?, ?, ?)", rows)
        conn.executemany(
            """INSERT INTO similarity_feature
               (decl_id, schema_version, signature_sha256, status, reason, tree_size, features)
               VALUES (?, ?, ?, ?, ?, ?, ?)""",
            similarity.build_feature_rows(nodes),
        )
        if input_payload is not None:
            conn.execute('CREATE TABLE input_state (id INTEGER PRIMARY KEY, payload TEXT NOT NULL)')
            conn.execute('INSERT INTO input_state VALUES (1, ?)', (json.dumps(input_payload),))
        conn.commit()
        conn.close()
        os.replace(temporary, db_path)
    finally:
        conn.close()
        if Path(temporary).exists():
            Path(temporary).unlink()


def _counts(nodes, edges):
    # (node-kind counts incl external decls, edge-type counts) for the build summary.
    nk, ek = {}, {}
    ext = 0
    for row in nodes.values():
        nk[row["kind"]] = nk.get(row["kind"], 0) + 1
        if row["kind"] == "declaration" and row["is_external"]:
            ext += 1
    seen = set()
    for src, dst, etype, _p in edges:
        if (src, dst, etype) in seen:
            continue
        seen.add((src, dst, etype))
        ek[etype] = ek.get(etype, 0) + 1
    return nk, ext, ek


def main(argv=None):
    ap = argparse.ArgumentParser(description="Build the xylem property-graph store.")
    ap.add_argument("--dot", default=str(DATA_DIR / "module_graph.dot"))
    ap.add_argument("--extractor", default=str(DATA_DIR / "declarations.json"))
    ap.add_argument("--vault", default=str(VAULT_LEAN))
    ap.add_argument("--bib", default=None)
    ap.add_argument("--bricks", default=None, help="canonical Brick directory; empty disables")
    ap.add_argument("--ctrllib", default=None, help="Lean source root for freshness/coverage")
    ap.add_argument("--db", default=str(store.db_path_default()))
    args = ap.parse_args(argv)
    default_capture = Path(args.extractor).resolve() == (DATA_DIR / 'declarations.json').resolve()
    if args.bricks is None:
        args.bricks = str(config.LEAN_ROOT / '30_bricks') if default_capture else ''
    if args.bib is None:
        args.bib = str(config.LEAN_ROOT / 'bibliography.bib') if args.bricks else ''
    if args.ctrllib is None:
        args.ctrllib = str(config.ctrllib_default()) if default_capture else ''

    for label, path in (("--dot", args.dot), ("--extractor", args.extractor)):
        if not Path(path).is_file():
            print(f"error: missing input {label}: {path}", file=sys.stderr)
            return 2

    nodes, edges = {}, []
    parse_dot(args.dot, nodes, edges)
    try:
        parse_declarations(args.extractor, nodes, edges)
    except ValueError as e:
        print(f"error: {e}", file=sys.stderr)
        return 2
    parse_pages(args.vault, nodes, edges)
    parse_bricks(args.vault, _bib_entries(args.bib), nodes, edges)
    catalogue_report = {'bricks': 0, 'issues': []}
    if args.bricks:
        catalogue_report = catalogue.parse_catalogue(args.bricks, args.bib, nodes, edges)
    spec = dict(dot=args.dot, extractor=args.extractor, vault=args.vault,
                bibliography=args.bib, bricks=args.bricks, ctrllib=args.ctrllib)
    spec = {key: str(Path(value).resolve()) if value else '' for key, value in spec.items()}
    # Compare Lean sources to extraction even if someone rebuilds SQLite alone.
    payload = {'spec': spec, 'files': input_state.snapshot(spec),
               'issues': input_state.extraction_issues(spec, nodes) + catalogue_report['issues'],
               'catalogue': catalogue_report}
    rank(nodes, edges)
    write_db(args.db, nodes, edges, payload)

    nk, ext, ek = _counts(nodes, edges)
    print(
        f"nodes: {nk.get('module', 0)} module / "
        f"{nk.get('declaration', 0)} decl ({ext} external) / "
        f"{nk.get('wiki_page', 0)} wiki / "
        f"{nk.get('brick', 0)} brick / {nk.get('source', 0)} source  -> {args.db}"
    )
    print("edges: " + " / ".join(f"{ek.get(t, 0)} {t}" for t in
          ("IMPORTS", "USES_IN_TYPE", "USES_IN_PROOF", "DECLARED_IN", "PAIRED_WITH",
           "BRICK_OF", "CITES")))
    return 0


if __name__ == "__main__":
    sys.exit(main())
