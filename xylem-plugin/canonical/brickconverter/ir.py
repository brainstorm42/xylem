"""Versioned neutral expression IR shared by every BrickConverter front end."""

from __future__ import annotations
from dataclasses import dataclass, fields, is_dataclass
import json
from typing import Any

SCHEMA_VERSION = 1

@dataclass(frozen=True)
class Ident:
    name: str
    is_const: bool = False
    semantic_id: str | None = None
    scope: str | None = None
    frame: str | None = None

@dataclass(frozen=True)
class Lit:
    text: str

@dataclass(frozen=True)
class Sort:
    level: str = "Type"

@dataclass(frozen=True)
class Paren:
    items: list[Any]

@dataclass(frozen=True)
class Proj:
    base: Any
    field: str

@dataclass(frozen=True)
class BinOp:
    op: str
    lhs: Any
    rhs: Any

@dataclass(frozen=True)
class App:
    head: Any
    args: list[Any]

@dataclass(frozen=True)
class Forall:
    binder_name: str
    binder_info: str
    binder_type: Any
    body: Any

@dataclass(frozen=True)
class Lam:
    binder_name: str
    binder_type: Any
    body: Any

@dataclass(frozen=True)
class DerivativeAt:
    """A declared derivative convention, never inferred from glyphs alone."""
    expression: Any
    variable: Any
    order: int = 1
    evaluation: Any | None = None

@dataclass(frozen=True)
class Unknown:
    node_type: str
    text: str

NODE_TYPES = {c.__name__: c for c in (Ident, Lit, Sort, Paren, Proj, BinOp, App, Forall, Lam, DerivativeAt, Unknown)}

def _encode(value: Any) -> Any:
    if is_dataclass(value):
        return {"node": type(value).__name__, **{f.name: _encode(getattr(value, f.name)) for f in fields(value)}}
    if isinstance(value, list):
        return [_encode(v) for v in value]
    if isinstance(value, dict):
        return {str(k): _encode(v) for k, v in sorted(value.items())}
    return value

def to_json(value: Any) -> dict[str, Any]:
    return {"schema_version": SCHEMA_VERSION, "expression": _encode(value)}

def _decode(value: Any) -> Any:
    if isinstance(value, list):
        return [_decode(v) for v in value]
    if not isinstance(value, dict):
        return value
    kind = value.get("node")
    if not kind:
        return {k: _decode(v) for k, v in value.items()}
    cls = NODE_TYPES.get(kind)
    if cls is None:
        raise ValueError(f"unsupported IR node {kind!r}")
    return cls(**{k: _decode(v) for k, v in value.items() if k != "node"})

def from_json(payload: dict[str, Any]) -> Any:
    if payload.get("schema_version") != SCHEMA_VERSION:
        raise ValueError(f"unsupported IR schema_version {payload.get('schema_version')!r}")
    return _decode(payload["expression"])

def canonical_json(value: Any) -> str:
    return json.dumps(to_json(value), ensure_ascii=False, sort_keys=True, separators=(",", ":"))

def normalize(value: Any) -> Any:
    if isinstance(value, Ident) and value.semantic_id:
        return Ident(value.semantic_id, value.is_const, value.semantic_id, value.scope, value.frame)
    if isinstance(value, Paren) and len(value.items) == 1:
        return normalize(value.items[0])
    if is_dataclass(value):
        return type(value)(**{f.name: normalize(getattr(value, f.name)) for f in fields(value)})
    if isinstance(value, list):
        return [normalize(v) for v in value]
    return value
