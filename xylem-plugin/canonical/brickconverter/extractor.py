"""Exact declaration selection and Xylem extractor adapters."""

from __future__ import annotations
import json
from pathlib import Path
from typing import Any
from .ir import App, Forall, Ident, Lam, Lit, Proj, Sort, Unknown

class ExtractorError(ValueError):
    pass

def _uncurry(node: dict[str, Any]) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    args: list[dict[str, Any]] = []
    while isinstance(node, dict) and node.get("node") == "app":
        args = list(node.get("args") or []) + args
        node = node["fn"]
    return node, args

def expression_from_xylem(node: Any):
    if node is None:
        return Unknown("null", "")
    kind = node.get("node")
    if kind == "const":
        name = node.get("name") or "?"
        return Ident(name, is_const=True, semantic_id=name)
    if kind == "fvar":
        return Ident(node.get("name") or "_", scope="binder")
    if kind == "lit":
        return Lit(str(node.get("value")))
    if kind == "sort":
        return Sort(node.get("level") or "Type")
    if kind == "app":
        head, args = _uncurry(node)
        return App(expression_from_xylem(head), [expression_from_xylem(a["value"]) for a in args if a.get("explicit")])
    if kind == "forall":
        return Forall(node.get("binderName") or "", node.get("binderInfo") or "default", expression_from_xylem(node.get("binderType")), expression_from_xylem(node.get("body")))
    if kind == "lam":
        return Lam(node.get("binderName") or "", expression_from_xylem(node.get("binderType")), expression_from_xylem(node.get("body")))
    if kind == "proj":
        return Proj(expression_from_xylem(node.get("struct")), str(node.get("idx")))
    return Unknown(kind or "?", json.dumps(node, ensure_ascii=False, sort_keys=True)[:160])

def load_capture(path: str | Path) -> dict[str, Any]:
    data = json.loads(Path(path).read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise ExtractorError("extractor capture must be a mapping")
    if data.get("schema_version") != 1:
        raise ExtractorError(f"unsupported extractor schema_version {data.get('schema_version')!r}")
    if not isinstance(data.get("errors", []), list):
        raise ExtractorError("extractor errors must be a list")
    if data.get("errors"):
        raise ExtractorError(f"extractor reported {len(data['errors'])} error(s)")
    declarations = data.get("declarations")
    if not isinstance(declarations, list) or not declarations:
        raise ExtractorError("extractor declarations must be a nonempty list")
    names: set[str] = set()
    for declaration in declarations:
        name = declaration.get("name") if isinstance(declaration, dict) else None
        if not isinstance(name, str) or not name.strip() or name in names:
            raise ExtractorError("extractor declarations have a missing or duplicate identity")
        names.add(name)
    return data

def select_declaration(data: dict[str, Any], exact_name: str) -> dict[str, Any]:
    matches = [d for d in data.get("declarations", []) if d.get("name") == exact_name]
    if len(matches) != 1:
        raise ExtractorError(f"exact declaration {exact_name!r} matched {len(matches)} records")
    return matches[0]

def declaration_ir(declaration: dict[str, Any]):
    return expression_from_xylem(declaration.get("conclusion_tree"))
