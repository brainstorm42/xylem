"""Deterministic, report-only structural ranking for local Lean declarations."""

from __future__ import annotations

from collections import Counter
import hashlib
import json
import math
from typing import Any

FEATURE_SCHEMA_VERSION = 1
MIN_SUBTREE_NODES = 3
MAX_SHARED_FEATURES = 5
REPORT_WARNING = (
    "report-only structural shortlist; inspect premises, domains, frames, and "
    "the exact theorem type, then replay the selected declaration in Lean"
)


class SimilarityError(ValueError):
    """A named failure at the structural-retrieval trust boundary."""


def _canonical_json(value: Any) -> str:
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"))


def _literal_kind(node: dict[str, Any]) -> str:
    kind = node.get("kind")
    if isinstance(kind, str) and kind:
        return kind
    value = node.get("value")
    if value is None:
        return "none"
    if isinstance(value, bool):
        return "bool"
    if isinstance(value, (int, float)):
        return "num"
    return "text"


def _normal_node(node: Any, heads: Counter[str]) -> tuple[str, list[Any]]:
    """Normalize one extractor node while collecting visible constant names."""
    if not isinstance(node, dict):
        raise SimilarityError("malformed_tree_node")
    kind = node.get("node")
    if kind == "const":
        name = node.get("name")
        if not isinstance(name, str) or not name:
            raise SimilarityError("malformed_const")
        heads[name] += 1
        return "const", []
    if kind == "fvar":
        idx = node.get("binderIdx")
        return (f"fvar:{idx}" if isinstance(idx, int) else "fvar"), []
    if kind == "lit":
        return f"lit:{_literal_kind(node)}", []
    if kind == "sort":
        return "sort", []
    if kind == "app":
        args = node.get("args")
        if not isinstance(args, list):
            raise SimilarityError("malformed_app")
        explicit = []
        for arg in args:
            if not isinstance(arg, dict) or "value" not in arg:
                raise SimilarityError("malformed_app_argument")
            if arg.get("explicit"):
                explicit.append(_normal_node(arg["value"], heads))
        return f"app:{len(explicit)}", [_normal_node(node.get("fn"), heads), *explicit]
    if kind == "forall":
        return f"forall:{node.get('binderInfo') or 'default'}", [
            _normal_node(node.get("binderType"), heads),
            _normal_node(node.get("body"), heads),
        ]
    if kind == "lam":
        return "lam", [
            _normal_node(node.get("binderType"), heads),
            _normal_node(node.get("body"), heads),
        ]
    if kind == "proj":
        idx = node.get("idx")
        if not isinstance(idx, int):
            raise SimilarityError("malformed_projection")
        return f"proj:{idx}", [_normal_node(node.get("struct"), heads)]
    raise SimilarityError(f"unsupported_node:{kind or 'missing'}")


def _signature_tree(signature: dict[str, Any], heads: Counter[str]) -> tuple[str, list[Any]]:
    conclusion = signature.get("conclusion_tree")
    if conclusion is None:
        raise SimilarityError("missing_conclusion_tree")
    binders = signature.get("binders")
    if not isinstance(binders, list):
        raise SimilarityError("malformed_binders")
    children = []
    for binder in binders:
        if not isinstance(binder, dict) or not isinstance(binder.get("tree"), dict):
            raise SimilarityError("malformed_binder_tree")
        info = binder.get("binderInfo") or "default"
        children.append((f"binder:{info}", [_normal_node(binder["tree"], heads)]))
    children.append(("conclusion", [_normal_node(conclusion, heads)]))
    return "signature", children


def _fingerprint_features(root: tuple[str, list[Any]]) -> tuple[int, dict[str, list[Any]]]:
    features: dict[str, list[Any]] = {}

    def visit(node: tuple[str, list[Any]]) -> tuple[bytes, int]:
        token, children = node
        child_rows = [visit(child) for child in children]
        size = 1 + sum(row[1] for row in child_rows)
        digest = hashlib.sha256()
        digest.update(token.encode("utf-8"))
        digest.update(b"\0")
        for child_digest, _child_size in child_rows:
            digest.update(child_digest)
        raw = digest.digest()
        key = raw.hex()
        if size >= MIN_SUBTREE_NODES:
            if key not in features:
                features[key] = [0, size, token]
            features[key][0] += 1
        return raw, size

    _digest, tree_size = visit(root)
    return tree_size, features


def feature_payload(signature: dict[str, Any]) -> dict[str, Any]:
    """Return the version-1 normalized features for one extractor signature."""
    heads: Counter[str] = Counter()
    tree = _signature_tree(signature, heads)
    tree_size, shape = _fingerprint_features(tree)
    return {
        "tree_size": tree_size,
        "shape": {key: shape[key] for key in sorted(shape)},
        "semantic_heads": {key: heads[key] for key in sorted(heads)},
    }


def build_feature_rows(nodes: dict[str, dict[str, Any]]) -> list[tuple[Any, ...]]:
    """Build one deterministic row for every local declaration."""
    rows = []
    declarations = sorted(
        (row for row in nodes.values()
         if row["kind"] == "declaration" and not row["is_external"]),
        key=lambda row: row["id"],
    )
    for declaration in declarations:
        raw_signature = declaration.get("signature")
        signature_hash = hashlib.sha256((raw_signature or "").encode()).hexdigest()
        status, reason, tree_size, payload = "usable", None, None, None
        try:
            signature = json.loads(raw_signature or "null")
            if not isinstance(signature, dict):
                raise SimilarityError("malformed_signature")
            payload = feature_payload(signature)
            tree_size = payload["tree_size"]
        except (json.JSONDecodeError, SimilarityError) as error:
            status, reason = "skipped", str(error)
        rows.append((
            declaration["id"], FEATURE_SCHEMA_VERSION, signature_hash,
            status, reason, tree_size,
            _canonical_json(payload) if payload is not None else None,
        ))
    return rows


def _shape_counter(payload: dict[str, Any]) -> Counter[str]:
    return Counter({key: int(value[0]) for key, value in payload["shape"].items()})


def _multiset_jaccard(a: Counter[str], b: Counter[str]) -> tuple[float, int]:
    keys = set(a) | set(b)
    if not keys:
        return 0.0, 0
    shared = sum(min(a[key], b[key]) for key in keys)
    union = sum(max(a[key], b[key]) for key in keys)
    return (shared / union if union else 0.0), shared


def _idf_weights(documents: list[set[str]]) -> dict[str, float]:
    df: Counter[str] = Counter()
    for document in documents:
        df.update(document)
    n = len(documents)
    return {term: math.log((n + 1) / (count + 1)) + 1.0 for term, count in df.items()}


def _weighted_jaccard(a: set[str], b: set[str], weights: dict[str, float]) -> float:
    union = a | b
    if not union:
        return 0.0
    return sum(weights.get(term, 1.0) for term in a & b) / sum(
        weights.get(term, 1.0) for term in union
    )


def _premises(conn, edge_type: str) -> dict[str, set[str]]:
    out: dict[str, set[str]] = {}
    for row in conn.execute(
        """SELECT e.src, n.name FROM edge e JOIN node n ON n.id=e.dst
           WHERE e.type=? ORDER BY e.src, n.name""",
        (edge_type,),
    ):
        out.setdefault(row["src"], set()).add(row["name"])
    return out


def _feature_rows(conn) -> list[dict[str, Any]]:
    rows = conn.execute(
        """SELECT n.id, n.name, n.module, n.decl_kind, n.signature, n.src_file,
                  n.src_start, n.src_end, f.schema_version, f.signature_sha256,
                  f.status, f.reason, f.tree_size, f.features
           FROM node n JOIN similarity_feature f ON f.decl_id=n.id
           WHERE n.kind='declaration' AND n.is_external=0 ORDER BY n.name"""
    ).fetchall()
    out = []
    for row in rows:
        item = dict(row)
        raw_features = item.pop("features")
        item["feature_payload"] = json.loads(raw_features) if raw_features else None
        item["signature_payload"] = json.loads(item["signature"] or "null")
        out.append(item)
    return out


def _corpus_hash(rows: list[dict[str, Any]]) -> str:
    digest = hashlib.sha256()
    for row in rows:
        digest.update(row["id"].encode())
        digest.update(b"\0")
        digest.update(row["signature_sha256"].encode())
        digest.update(b"\n")
    return digest.hexdigest()


def query_similar(
    conn,
    exact_name: str,
    *,
    limit: int = 10,
    all_kinds: bool = False,
    cross_module_only: bool = False,
) -> dict[str, Any]:
    """Rank local candidates for one exact local declaration name."""
    if not isinstance(limit, int) or not 1 <= limit <= 100:
        raise SimilarityError("top/limit must be between 1 and 100")
    rows = _feature_rows(conn)
    matches = [row for row in rows if row["name"] == exact_name]
    if len(matches) != 1:
        raise SimilarityError(f"exact local declaration {exact_name!r} matched {len(matches)} records")
    query = matches[0]
    if query["status"] != "usable":
        raise SimilarityError(
            f"declaration {exact_name!r} is not structurally indexable: {query['reason']}"
        )

    usable = [row for row in rows if row["status"] == "usable"]
    type_premises = _premises(conn, "USES_IN_TYPE")
    proof_premises = _premises(conn, "USES_IN_PROOF")
    head_weights = _idf_weights([set(r["feature_payload"]["semantic_heads"]) for r in usable])
    type_weights = _idf_weights([type_premises.get(r["id"], set()) for r in usable])
    proof_weights = _idf_weights([proof_premises.get(r["id"], set()) for r in usable])

    qp = query["feature_payload"]
    q_shape = _shape_counter(qp)
    q_heads = set(qp["semantic_heads"])
    q_type = type_premises.get(query["id"], set())
    q_proof = proof_premises.get(query["id"], set())
    ranked = []
    for candidate in usable:
        if candidate["id"] == query["id"]:
            continue
        if not all_kinds and candidate["decl_kind"] != query["decl_kind"]:
            continue
        if cross_module_only and candidate["module"] == query["module"]:
            continue
        cp = candidate["feature_payload"]
        c_shape = _shape_counter(cp)
        c_heads = set(cp["semantic_heads"])
        c_type = type_premises.get(candidate["id"], set())
        c_proof = proof_premises.get(candidate["id"], set())
        shape_score, shared_count = _multiset_jaccard(q_shape, c_shape)
        common = q_shape & c_shape
        shared_keys = sorted(
            common,
            key=lambda key: (-min(q_shape[key], c_shape[key]) * int(qp["shape"][key][1]), key),
        )[:MAX_SHARED_FEATURES]
        signature = candidate["signature_payload"] or {}
        ranked.append({
            "name": candidate["name"],
            "module": candidate["module"],
            "kind": candidate["decl_kind"],
            "signature": signature.get("signature"),
            "source": {"file": candidate["src_file"], "start": candidate["src_start"], "end": candidate["src_end"]},
            "same_module": candidate["module"] == query["module"],
            "scores": {
                "shape": round(shape_score, 12),
                "semantic_heads": round(_weighted_jaccard(q_heads, c_heads, head_weights), 12),
                "type_premises": round(_weighted_jaccard(q_type, c_type, type_weights), 12),
                "proof_premises": round(_weighted_jaccard(q_proof, c_proof, proof_weights), 12),
            },
            "tree_sizes": {"query": qp["tree_size"], "candidate": cp["tree_size"]},
            "shared_fingerprint_count": shared_count,
            "shared_shape": [
                {"sha256": key, "root": qp["shape"][key][2], "nodes": qp["shape"][key][1], "multiplicity": min(q_shape[key], c_shape[key])}
                for key in shared_keys
            ],
            "shared_semantic_heads": sorted(q_heads & c_heads),
            "shared_type_premises": sorted(q_type & c_type),
            "shared_proof_premises": sorted(q_proof & c_proof),
        })

    ranked.sort(key=lambda item: (
        -item["scores"]["shape"], -item["scores"]["semantic_heads"],
        -item["scores"]["type_premises"], -item["scores"]["proof_premises"], item["name"],
    ))
    selected = ranked[:limit]
    for rank, item in enumerate(selected, 1):
        item["rank"] = rank
    skipped = [
        {"name": row["name"], "module": row["module"], "reason": row["reason"]}
        for row in rows if row["status"] != "usable"
    ]
    q_signature = query["signature_payload"] or {}
    return {
        "schema_version": 1,
        "operation": "similar",
        "report_only": True,
        "warning": REPORT_WARNING,
        "query": {
            "name": query["name"], "module": query["module"], "kind": query["decl_kind"],
            "signature": q_signature.get("signature"),
            "source": {"file": query["src_file"], "start": query["src_start"], "end": query["src_end"]},
            "signature_sha256": query["signature_sha256"],
        },
        "parameters": {
            "limit": limit, "all_kinds": all_kinds, "cross_module_only": cross_module_only,
            "ranking": ["shape", "semantic_heads", "type_premises", "proof_premises", "name"],
        },
        "corpus": {
            "feature_schema_version": FEATURE_SCHEMA_VERSION,
            "corpus_sha256": _corpus_hash(rows),
            "local_declarations": len(rows), "usable": len(usable), "skipped": len(skipped),
        },
        "candidates": selected,
        "skipped": skipped,
    }
