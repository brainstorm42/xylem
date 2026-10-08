#!/usr/bin/env python
"""Build the xylem typed-property-graph SQLite store from four derived inputs:
importGraph DOT, the Lean extractor JSON (contract v1), vault/lean/*.md frontmatter
(wiki pages + Brick source locators), and the corpus BibTeX (source bibliographic
data). Idempotent: drops and recreates every table on each run. Prints node/edge counts."""
import argparse
import gzip
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
    # Do not let explanatory comments containing the arrow token become graph
    # edges.  The percolation source graph records its direction convention in
    # a comment immediately above the edge list.
    graph_lines = "\n".join(
        line for line in text.splitlines()
        if not line.lstrip().startswith(("//", "#"))
    )
    for src, dst in DOT_EDGE.findall(graph_lines):
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


def parse_declarations(path, nodes, edges, compact=False):
    """Add declaration nodes, DECLARED_IN, and USES_IN_TYPE/PROOF edges from the extractor JSON.

    Contract v1 (RULED-FINAL 2026-07-18): FLAT premises = [{name, module, in_type,
    in_proof, external}], one row per constant with independent booleans, no
    premise_nodes — this builder derives the node/edge split on insert. Raises
    ValueError on malformed/empty JSON (the caller maps it to a named nonzero exit)."""
    input_path = Path(path)
    opener = gzip.open if input_path.suffix == ".gz" else open
    with opener(input_path, "rt", encoding="utf-8") as handle:
        raw = handle.read()
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
        binders = d.get("binders", [])
        if compact:
            binders = [{key: binder.get(key) for key in ("idx", "name", "binderInfo", "type")}
                       for binder in binders]
        sig = {
            "binders": binders,
            "conclusion": d.get("conclusion"),
            "conclusion_tree": None if compact else d.get("conclusion_tree"),
            "signature": d.get("signature"),
        }
        source_file = d.get("src_file") or module.replace(".", "/") + ".lean"
        capture_surface = d.get("capture_surface")
        _put(nodes, {
            "id": f"decl:{d['name']}", "kind": "declaration", "name": d["name"],
            "module": module, "decl_kind": d.get("kind"), "docstring": d.get("doc"),
            "src_file": source_file, "src_start": start,
            "src_end": end, "signature": json.dumps(sig), "is_external": 0,
            "props": json.dumps({
                "axioms": d.get("axioms", []),
                "premise_count": len(d.get("premises", [])),
                "type_premise_count": sum(bool(p.get("in_type")) for p in d.get("premises", [])),
                "proof_premise_count": sum(bool(p.get("in_proof")) for p in d.get("premises", [])),
                "capture_storage": "compact_index_projection" if compact else "full_node_projection",
                # Keep the index portable across checkouts; the exact absolute
                # input and its content hash live in input_state/receipts.
                "capture_artifact": Path(path).name,
                **({"premises": d.get("premises", [])} if not compact else {}),
                "capture_surface": capture_surface,
                "source_name": d.get("source_name", d["name"]),
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


def parse_components(path, nodes, edges):
    """Add source-backed component nodes and typed, non-proof relations.

    Component edges deliberately stay outside ``DEPENDENCY_EDGE_TYPES``.  A
    component record may summarize a formal chain or carry an authored
    interpretation, but it never becomes a synthetic Lean proof dependency.
    Every declaration reference is checked against the elaborated declaration
    set so stale or misspelled component claims fail the build.
    """
    if not path:
        return {"components": 0, "relations": 0, "issues": []}
    data = json.loads(Path(path).read_text(encoding="utf-8"))
    if data.get("schema_version") not in {1, 2}:
        raise ValueError(f"unsupported component schema in {path}")
    declarations = {nid[5:] for nid, row in nodes.items()
                    if row["kind"] == "declaration" and nid.startswith("decl:")}
    components = data.get("components")
    relations = data.get("relations", [])
    if not isinstance(components, list) or not isinstance(relations, list):
        raise ValueError(f"components and relations must be arrays in {path}")
    captured_edge_keys = {(src, dst, edge_type) for src, dst, edge_type, _props in edges}
    ids = set()
    for component in components:
        cid = component.get("id")
        if not isinstance(cid, str) or not cid or cid in ids:
            raise ValueError(f"component ids must be unique nonempty strings in {path}")
        ids.add(cid)
        referenced = component.get("declarations", [])
        if not isinstance(referenced, list) or any(name not in declarations for name in referenced):
            missing = [name for name in referenced if name not in declarations]
            raise ValueError(f"component {cid} references missing declarations: {missing[:5]}")
        component_id = f"component:{cid}"
        props = dict(component)
        props.pop("id", None)
        _put(nodes, {
            "id": component_id, "kind": "component", "name": cid,
            "module": component.get("module"), "decl_kind": component.get("kind"),
            "docstring": component.get("title") or component.get("summary"),
            "src_file": (component.get("source") or {}).get("file"),
            "src_start": (component.get("source") or {}).get("start_line"),
            "src_end": (component.get("source") or {}).get("end_line"),
            "signature": None, "is_external": 0, "props": json.dumps(props), "rank": None,
        }, force=True)
        for decl_name in referenced:
            edges.append((f"decl:{decl_name}", component_id, "COMPONENT_OF", json.dumps({
                "evidence": "component declaration membership",
                "source_declaration": decl_name,
            })))
    for relation in relations:
        source = relation.get("source")
        target = relation.get("target")
        relation_type = relation.get("type")
        if source not in ids or target not in ids:
            raise ValueError(f"component relation has unknown endpoint: {source} -> {target}")
        if not isinstance(relation_type, str) or not relation_type:
            raise ValueError("component relation type must be a nonempty string")
        evidence_kind = relation.get("evidence_kind")
        if evidence_kind not in {"compiler", "capture_metadata", "authored"}:
            raise ValueError(f"component relation {source}->{target} has unknown evidence_kind")
        evidence = relation.get("evidence")
        if not isinstance(evidence, dict):
            raise ValueError(f"component relation {source}->{target} lacks evidence metadata")
        if evidence_kind == "compiler":
            source_decl = evidence.get("source_declaration")
            target_decl = evidence.get("target_declaration")
            edge_type = evidence.get("edge_type")
            if not isinstance(source_decl, str) or not isinstance(target_decl, str):
                raise ValueError(f"compiler component relation {source}->{target} lacks declaration endpoints")
            if edge_type not in {"USES_IN_TYPE", "USES_IN_PROOF", "IMPORTS"}:
                raise ValueError(f"compiler component relation {source}->{target} has invalid edge type")
            if (f"decl:{source_decl}", f"decl:{target_decl}", edge_type) not in captured_edge_keys:
                raise ValueError(
                    f"compiler component relation {source}->{target} does not match captured "
                    f"{edge_type}: {source_decl} -> {target_decl}"
                )
        props = dict(relation)
        props.pop("source", None)
        props.pop("target", None)
        edges.append((f"component:{source}", f"component:{target}",
                      "COMPONENT_RELATION", json.dumps(props)))
    return {"components": len(components), "relations": len(relations), "issues": []}


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
    ap.add_argument("--source-root", default=None, help="immutable source snapshot for freshness/coverage")
    ap.add_argument("--components", default=None, help="source-backed component hierarchy JSON")
    ap.add_argument("--compact-index", action="store_true",
                    help="omit repeated premise/tree payloads from nodes; edges and source capture remain complete")
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
    if args.components and not Path(args.components).is_file():
        print(f"error: missing input --components: {args.components}", file=sys.stderr)
        return 2
    if args.source_root and not Path(args.source_root).is_dir():
        print(f"error: missing input --source-root: {args.source_root}", file=sys.stderr)
        return 2

    nodes, edges = {}, []
    parse_dot(args.dot, nodes, edges)
    try:
        parse_declarations(args.extractor, nodes, edges, compact=args.compact_index)
        component_report = parse_components(args.components, nodes, edges)
    except ValueError as e:
        print(f"error: {e}", file=sys.stderr)
        return 2
    if not args.components:
        component_report = {'components': 0, 'relations': 0, 'issues': []}
    parse_pages(args.vault, nodes, edges)
    parse_bricks(args.vault, _bib_entries(args.bib), nodes, edges)
    catalogue_report = {'bricks': 0, 'issues': []}
    if args.bricks:
        catalogue_report = catalogue.parse_catalogue(args.bricks, args.bib, nodes, edges)
    spec = dict(dot=args.dot, extractor=args.extractor, vault=args.vault,
                bibliography=args.bib, bricks=args.bricks, ctrllib=args.ctrllib,
                source_root=args.source_root, components=args.components)
    spec = {key: str(Path(value).resolve()) if value else '' for key, value in spec.items()}
    # Compare Lean sources to extraction even if someone rebuilds SQLite alone.
    payload = {'spec': spec, 'files': input_state.snapshot(spec),
               'issues': input_state.extraction_issues(spec, nodes) + catalogue_report['issues'],
               'catalogue': catalogue_report, 'components': component_report}
    rank(nodes, edges)
    write_db(args.db, nodes, edges, payload)

    nk, ext, ek = _counts(nodes, edges)
    print(
        f"nodes: {nk.get('module', 0)} module / "
        f"{nk.get('declaration', 0)} decl ({ext} external) / "
        f"{nk.get('component', 0)} component / "
        f"{nk.get('wiki_page', 0)} wiki / "
        f"{nk.get('brick', 0)} brick / {nk.get('source', 0)} source  -> {args.db}"
    )
    print("edges: " + " / ".join(f"{ek.get(t, 0)} {t}" for t in
          ("IMPORTS", "USES_IN_TYPE", "USES_IN_PROOF", "DECLARED_IN", "PAIRED_WITH",
          "BRICK_OF", "CITES", "COMPONENT_OF", "COMPONENT_RELATION")))
    return 0


if __name__ == "__main__":
    sys.exit(main())
