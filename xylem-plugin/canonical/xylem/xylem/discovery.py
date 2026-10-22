#!/usr/bin/env python3
"""Bounded, CPU-only structural technique discovery over Xylem captures.

This module deliberately sits beside the canonical property graph.  It reads
the existing declaration capture and an optional bounded proof-trace artifact,
then writes a source-anchored discovery report.  It never edits Lean source,
proof terms, dependency edges, or the baseline similarity index.

The report has three explicitly different layers:

* ``baseline`` reuses the current declaration-tree/Jaccard feature family;
* ``one_pass`` proposes typed, binding-aware anti-unifications from a fixed
  training split;
* ``two_pass`` feeds only structurally accepted proposal IDs back as exact
  vocabulary tokens.

No layer asserts mathematical meaning, theorem equivalence, or proof
reusability.  Missing trees, unavailable trace evidence, and exhausted fixed
budgets remain visible as ``unknown``/``truncated`` statuses.
"""

from __future__ import annotations

from collections import Counter, defaultdict
from dataclasses import dataclass, field
import gzip
import hashlib
from itertools import combinations, product
import json
from pathlib import Path
from typing import Any, Iterable, Iterator

from . import similarity


SCHEMA_VERSION = 1
ALGORITHM_VERSION = "structural-discovery-v1"
BASELINE_FEATURE_SCHEMA_VERSION = similarity.FEATURE_SCHEMA_VERSION
DEFAULT_LIMITS = {
    "max_declarations": 32,
    "max_candidates_per_query": 8,
    "max_pairs": 160,
    "max_pattern_nodes": 256,
    "max_metavariables": 64,
    "min_metavariables": 1,
    "min_support": 2,
    "min_families": 2,
    "min_anchors": 1,
    "max_trace_bytes": 64 * 1024 * 1024,
    "max_trace_records": 256,
    "max_type_evidence_bytes": 4 * 1024 * 1024,
    "max_type_evidence_records": 64,
    "max_fragment_candidates": 48,
    "max_fragment_pairs": 96,
    "max_component_occurrences": 32,
    "max_component_combinations": 64,
    "max_rounds": 2,
}

# Verification is intentionally limited to the application-owned percolation
# fixture.  A manifest is input data, not an authority for executable paths or
# evidence trust.  These pins are updated only with the private fixture's
# checked-in artifact freeze; they are not read from the manifest or receipt.
APPLICATION_ROOT = Path(__file__).resolve().parents[3]
TRUSTED_DISCOVERY_RELATIVE_ROOT = Path("examples/percolation-e2e/data")
TRUSTED_DISCOVERY_MANIFEST_SHA256 = (
    "640e641f6c0f1992a3f38745ef244b4501c6baf8a72ce4a9ad4e908a7698f050"
)
TRUSTED_DISCOVERY_RECEIPT_SHA256 = (
    "4da4fbefc068572b5df8d80577cf35c22760897109788f376d3de7c6fcd0b3a5"
)
TRUSTED_DISCOVERY_ARTIFACT_HASHES = {
    "capture": "e18f05f7609f26aeb2de67da9f91013e6b04c8cf96afdd86723f203cb63a0345",
    "source_manifest": "59b9281bbc1999114080241b6532038a82629f273ea0b60d1758ea529ce9b7cc",
    "trace": "a6df73214ce40dea78dc0f6841d6f6f85a2a686e819c526426eab6d80aa7f038",
    "type_evidence": "b642098e958efd6e9b65a536208d4dc3a0e0a7e8a523a3e05f530b06d2915b5c",
}
TRUSTED_DISCOVERY_EXTRACTOR_HASHES = {
    "trace": "90d60db470098aef94fd9e90ee084102640d37a46f2649abde70e6bbc0947ad4",
    "type_evidence": "6ffa03d2715c3974c21ecd4cf9f6a31385121bbbd89232aec57aea803b8b1678",
}


class DiscoveryError(ValueError):
    """A named failure at the discovery artifact trust boundary."""


class UnsupportedTree(DiscoveryError):
    """A declaration tree cannot be represented by this versioned IR."""


def _canonical_json(value: Any) -> str:
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"))


def _sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def _sha256_json(value: Any) -> str:
    return _sha256_bytes(_canonical_json(value).encode("utf-8"))


def _read_json(path: Path) -> tuple[Any, str]:
    """Read JSON or JSON.GZ and return its parsed value plus content hash."""
    raw = path.read_bytes()
    try:
        payload = gzip.decompress(raw) if path.name.endswith(".gz") else raw
        value = json.loads(payload.decode("utf-8"))
        # Hash logical JSON content, not gzip headers or filesystem metadata.
        return value, _sha256_json(value)
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise DiscoveryError(f"cannot read JSON artifact {path}: {error}") from error


def _read_json_bounded(path: Path, max_bytes: int, *, label: str = "artifact") -> tuple[Any, str]:
    """Read a bounded logical JSON stream, including compressed traces.

    ``Path.stat().st_size`` is not a sufficient guard for ``.gz`` artifacts:
    a small compressed file can expand dramatically before ``json.loads`` sees
    it.  Read at most ``max_bytes + 1`` decompressed bytes so the trace trust
    boundary remains bounded even for a decompression bomb.
    """
    opener = gzip.open if path.name.endswith(".gz") else Path.open
    try:
        with opener(path, "rb") as stream:  # type: ignore[operator]
            chunks: list[bytes] = []
            remaining = max_bytes + 1
            while remaining > 0:
                chunk = stream.read(min(1024 * 1024, remaining))
                if not chunk:
                    break
                chunks.append(chunk)
                remaining -= len(chunk)
            payload = b"".join(chunks)
        if len(payload) > max_bytes:
            raise DiscoveryError(f"{label}_decompressed_size_limit")
        value = json.loads(payload.decode("utf-8"))
        return value, _sha256_json(value)
    except DiscoveryError:
        raise
    except (OSError, EOFError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise DiscoveryError(f"cannot read bounded JSON artifact {path}: {error}") from error


def _normal_name(name: str, prefix: str) -> str:
    if not isinstance(name, str) or not name:
        raise DiscoveryError("manifest declaration names must be nonempty strings")
    return name if "::" in name or not prefix else f"{prefix}{name}"


def _relative_path(raw: Any, *, base: Path, label: str) -> Path:
    if not isinstance(raw, str) or not raw:
        raise DiscoveryError(f"manifest {label} path must be a nonempty string")
    value = Path(raw).expanduser()
    return value if value.is_absolute() else (base / value).resolve()


@dataclass(frozen=True)
class FamilySpec:
    name: str
    partition: str
    declarations: tuple[str, ...]


@dataclass(frozen=True)
class Manifest:
    path: Path
    capture_path: Path
    capture_sha256: str | None
    trace_path: Path | None
    trace_capture_sha256: str | None
    trace_extractor_path: Path | None
    trace_extractor_sha256: str | None
    type_evidence_path: Path | None
    type_evidence_sha256: str | None
    type_evidence_capture_sha256: str | None
    type_evidence_extractor_path: Path | None
    type_evidence_extractor_sha256: str | None
    type_evidence_generated_from: str | None
    source_manifest_path: Path | None
    trace_generated_from: str | None
    source_revision: str | None
    surface_prefix: str
    families: tuple[FamilySpec, ...]
    limits: dict[str, int]
    content_hash: str

    @property
    def declaration_names(self) -> tuple[str, ...]:
        return tuple(name for family in self.families for name in family.declarations)

    def family_by_declaration(self) -> dict[str, FamilySpec]:
        return {
            declaration: family
            for family in self.families
            for declaration in family.declarations
        }


def load_manifest(path: str | Path) -> Manifest:
    manifest_path = Path(path).expanduser().resolve()
    raw, raw_hash = _read_json(manifest_path)
    if not isinstance(raw, dict) or raw.get("schema_version") != SCHEMA_VERSION:
        raise DiscoveryError(f"manifest {manifest_path} must use schema_version {SCHEMA_VERSION}")
    capture_path = _relative_path(raw.get("capture"), base=manifest_path.parent, label="capture")
    capture_sha256 = raw.get("capture_sha256")
    if capture_sha256 is not None and (
        not isinstance(capture_sha256, str) or len(capture_sha256) != 64
        or any(character not in "0123456789abcdef" for character in capture_sha256)
    ):
        raise DiscoveryError("manifest capture_sha256 must be a lowercase SHA-256 or null")
    trace_raw = raw.get("trace")
    trace_path = None if trace_raw in (None, "") else _relative_path(
        trace_raw, base=manifest_path.parent, label="trace"
    )
    trace_capture_sha256 = raw.get("trace_capture_sha256")
    if trace_capture_sha256 is not None and (
        not isinstance(trace_capture_sha256, str) or len(trace_capture_sha256) != 64
        or any(character not in "0123456789abcdef" for character in trace_capture_sha256)
    ):
        raise DiscoveryError("manifest trace_capture_sha256 must be a lowercase SHA-256 or null")
    trace_extractor_raw = raw.get("trace_extractor")
    trace_extractor_path = None if trace_extractor_raw in (None, "") else _relative_path(
        trace_extractor_raw, base=manifest_path.parent, label="trace_extractor"
    )
    trace_extractor_sha256 = raw.get("trace_extractor_sha256")
    if trace_extractor_sha256 is not None and (
        not isinstance(trace_extractor_sha256, str) or len(trace_extractor_sha256) != 64
        or any(character not in "0123456789abcdef" for character in trace_extractor_sha256)
    ):
        raise DiscoveryError("manifest trace_extractor_sha256 must be a lowercase SHA-256 or null")
    type_evidence_raw = raw.get("type_evidence")
    type_evidence_path = None if type_evidence_raw in (None, "") else _relative_path(
        type_evidence_raw, base=manifest_path.parent, label="type_evidence"
    )
    type_evidence_sha256 = raw.get("type_evidence_sha256")
    if type_evidence_sha256 is not None and (
        not isinstance(type_evidence_sha256, str) or len(type_evidence_sha256) != 64
        or any(character not in "0123456789abcdef" for character in type_evidence_sha256)
    ):
        raise DiscoveryError("manifest type_evidence_sha256 must be a lowercase SHA-256 or null")
    type_evidence_capture_sha256 = raw.get("type_evidence_capture_sha256")
    if type_evidence_capture_sha256 is not None and (
        not isinstance(type_evidence_capture_sha256, str) or len(type_evidence_capture_sha256) != 64
        or any(character not in "0123456789abcdef" for character in type_evidence_capture_sha256)
    ):
        raise DiscoveryError(
            "manifest type_evidence_capture_sha256 must be a lowercase SHA-256 or null"
        )
    type_evidence_extractor_raw = raw.get("type_evidence_extractor")
    type_evidence_extractor_path = (
        None if type_evidence_extractor_raw in (None, "") else _relative_path(
            type_evidence_extractor_raw,
            base=manifest_path.parent,
            label="type_evidence_extractor",
        )
    )
    type_evidence_extractor_sha256 = raw.get("type_evidence_extractor_sha256")
    if type_evidence_extractor_sha256 is not None and (
        not isinstance(type_evidence_extractor_sha256, str)
        or len(type_evidence_extractor_sha256) != 64
        or any(character not in "0123456789abcdef" for character in type_evidence_extractor_sha256)
    ):
        raise DiscoveryError(
            "manifest type_evidence_extractor_sha256 must be a lowercase SHA-256 or null"
        )
    type_evidence_generated_from = raw.get("type_evidence_generated_from")
    if type_evidence_generated_from is not None and (
        not isinstance(type_evidence_generated_from, str) or not type_evidence_generated_from
    ):
        raise DiscoveryError("manifest type_evidence_generated_from must be a string or null")
    source_manifest_raw = raw.get("source_manifest")
    source_manifest_path = None if source_manifest_raw in (None, "") else _relative_path(
        source_manifest_raw, base=manifest_path.parent, label="source_manifest"
    )
    trace_generated_from = raw.get("trace_generated_from")
    if trace_generated_from is not None and (
        not isinstance(trace_generated_from, str) or not trace_generated_from
    ):
        raise DiscoveryError("manifest trace_generated_from must be a string or null")
    source_revision = raw.get("source_revision")
    if source_revision is not None and (
        not isinstance(source_revision, str) or not source_revision
    ):
        raise DiscoveryError("manifest source_revision must be a string or null")
    prefix = raw.get("surface_prefix", "")
    if not isinstance(prefix, str):
        raise DiscoveryError("manifest surface_prefix must be a string")
    family_raw = raw.get("families")
    if not isinstance(family_raw, dict) or not family_raw:
        raise DiscoveryError("manifest families must be a nonempty object")
    families: list[FamilySpec] = []
    seen: set[str] = set()
    for family_name in sorted(family_raw):
        value = family_raw[family_name]
        if not isinstance(value, dict):
            raise DiscoveryError(f"family {family_name!r} must be an object")
        partition = value.get("partition")
        if partition not in {"train", "held_out"}:
            raise DiscoveryError(f"family {family_name!r} partition must be train or held_out")
        names = value.get("declarations")
        if not isinstance(names, list) or not names:
            raise DiscoveryError(f"family {family_name!r} declarations must be nonempty")
        normalized = tuple(sorted(_normal_name(name, prefix) for name in names))
        if len(set(normalized)) != len(normalized):
            raise DiscoveryError(f"family {family_name!r} contains duplicate declarations")
        overlap = seen.intersection(normalized)
        if overlap:
            raise DiscoveryError("declarations occur in more than one family: " + ", ".join(sorted(overlap)))
        seen.update(normalized)
        families.append(FamilySpec(family_name, partition, normalized))
    limits = dict(DEFAULT_LIMITS)
    raw_limits = raw.get("limits", {})
    if not isinstance(raw_limits, dict):
        raise DiscoveryError("manifest limits must be an object")
    for key, value in raw_limits.items():
        if key not in limits or not isinstance(value, int) or value <= 0:
            raise DiscoveryError(f"invalid positive integer discovery limit {key!r}")
        limits[key] = value
    if not any(f.partition == "train" for f in families):
        raise DiscoveryError("manifest requires at least one training family")
    if not any(f.partition == "held_out" for f in families):
        raise DiscoveryError("manifest requires at least one held-out family")
    return Manifest(
        path=manifest_path,
        capture_path=capture_path,
        capture_sha256=capture_sha256,
        trace_path=trace_path,
        trace_capture_sha256=trace_capture_sha256,
        trace_extractor_path=trace_extractor_path,
        trace_extractor_sha256=trace_extractor_sha256,
        type_evidence_path=type_evidence_path,
        type_evidence_sha256=type_evidence_sha256,
        type_evidence_capture_sha256=type_evidence_capture_sha256,
        type_evidence_extractor_path=type_evidence_extractor_path,
        type_evidence_extractor_sha256=type_evidence_extractor_sha256,
        type_evidence_generated_from=type_evidence_generated_from,
        source_manifest_path=source_manifest_path,
        trace_generated_from=trace_generated_from,
        source_revision=source_revision,
        surface_prefix=prefix,
        families=tuple(families),
        limits=limits,
        content_hash=raw_hash,
    )


# Internal canonical IR.  A node is a tuple whose first item is a stable tag.
# Keeping it immutable makes anti-unification and matching independent of dict
# insertion order and Python hash randomization.
Node = tuple[Any, ...]


def _parse_node(raw: Any, *, path: str, env: dict[str, str] | None = None,
                scope_path: tuple[int, ...] = (), top_count: int | None = None) -> Node:
    env = env or {}
    if not isinstance(raw, dict):
        raise UnsupportedTree(f"{path}:node_not_object")
    kind = raw.get("node")
    if kind == "const":
        name = raw.get("name")
        if not isinstance(name, str) or not name:
            raise UnsupportedTree(f"{path}:malformed_const")
        return ("const", name)
    if kind == "fvar":
        index = raw.get("binderIdx")
        if index is not None and (type(index) is not int or index < 0):
            raise UnsupportedTree(f"{path}:malformed_binder_index")
        if isinstance(index, int):
            if top_count is not None and index >= top_count:
                raise UnsupportedTree(f"{path}:binder_index_out_of_scope")
            return ("fvar", f"top:{index}")
        name = raw.get("name")
        if isinstance(name, str) and name in env:
            return ("fvar", env[name])
        raise UnsupportedTree(f"{path}:missing_binder_index")
    if kind == "lit":
        literal_kind = raw.get("kind")
        if not isinstance(literal_kind, str) or not literal_kind:
            value = raw.get("value")
            literal_kind = (
                "bool" if isinstance(value, bool) else
                "num" if isinstance(value, (int, float)) else
                "text" if isinstance(value, str) else "unknown"
            )
        return ("lit", literal_kind, str(raw.get("value")))
    if kind == "sort":
        return ("sort", str(raw.get("level", "unknown")))
    if kind == "app":
        args = raw.get("args")
        if not isinstance(args, list):
            raise UnsupportedTree(f"{path}:malformed_app")
        normalized_args = []
        for index, argument in enumerate(args):
            if not isinstance(argument, dict) or not isinstance(argument.get("value"), dict):
                raise UnsupportedTree(f"{path}/args/{index}:malformed_argument")
            normalized_args.append((bool(argument.get("explicit", True)), _parse_node(
                argument["value"], path=f"{path}/args/{index}/value", env=env,
                scope_path=scope_path + (index,), top_count=top_count
            )))
        return ("app", _parse_node(raw.get("fn"), path=f"{path}/fn", env=env,
                                    scope_path=scope_path + (-1,), top_count=top_count), tuple(normalized_args))
    if kind in {"forall", "lam"}:
        binder_type_key = "binderType"
        if not isinstance(raw.get(binder_type_key), dict) or not isinstance(raw.get("body"), dict):
            raise UnsupportedTree(f"{path}:malformed_{kind}")
        binder_name = raw.get("binderName")
        nested_token = f"local:{'.'.join(str(part) for part in scope_path) or 'root'}"
        nested_env = dict(env)
        if isinstance(binder_name, str) and binder_name:
            nested_env[binder_name] = nested_token
        return (
            kind,
            str(raw.get("binderInfo") or "default"),
            _parse_node(raw[binder_type_key], path=f"{path}/binderType", env=env,
                        scope_path=scope_path + (0,), top_count=top_count),
            _parse_node(raw["body"], path=f"{path}/body", env=nested_env,
                        scope_path=scope_path + (1,), top_count=top_count),
        )
    if kind == "proj":
        index = raw.get("idx")
        if not isinstance(index, int) or not isinstance(raw.get("struct"), dict):
            raise UnsupportedTree(f"{path}:malformed_projection")
        return ("proj", index, _parse_node(raw["struct"], path=f"{path}/struct", env=env,
                                            scope_path=scope_path + (0,), top_count=top_count))
    if kind == "let":
        keys = ("binderType", "value", "body")
        if not all(isinstance(raw.get(key), dict) for key in keys):
            raise UnsupportedTree(f"{path}:malformed_let")
        return (
            "let",
            _parse_node(raw["binderType"], path=f"{path}/binderType", env=env,
                        scope_path=scope_path + (0,), top_count=top_count),
            _parse_node(raw["value"], path=f"{path}/value", env=env,
                        scope_path=scope_path + (1,), top_count=top_count),
            _parse_node(raw["body"], path=f"{path}/body", env=env,
                        scope_path=scope_path + (2,), top_count=top_count),
        )
    # The capture currently diagnoses unsupported mvars/mdata/bvars rather
    # than serializing them.  Refusing them is safer than silently widening a
    # pattern whose binding scope cannot be checked.
    raise UnsupportedTree(f"{path}:unsupported_node:{kind or 'missing'}")


def _node_json(node: Node) -> dict[str, Any]:
    tag = node[0]
    if tag == "const":
        return {"node": "const", "name": node[1]}
    if tag == "fvar":
        return {"node": "binder", "index": node[1]}
    if tag == "lit":
        return {"node": "lit", "kind": node[1], "value": node[2]}
    if tag == "sort":
        return {"node": "sort", "level": node[1]}
    if tag == "app":
        return {"node": "app", "fn": _node_json(node[1]), "args": [
            {"explicit": explicit, "value": _node_json(value)}
            for explicit, value in node[2]
        ]}
    if tag in {"forall", "lam"}:
        return {"node": tag, "binderInfo": node[1], "binderType": _node_json(node[2]),
                "body": _node_json(node[3])}
    if tag == "proj":
        return {"node": "proj", "idx": node[1], "struct": _node_json(node[2])}
    if tag == "let":
        return {"node": "let", "binderType": _node_json(node[1]),
                "value": _node_json(node[2]), "body": _node_json(node[3])}
    if tag == "meta":
        return {"node": "meta", "id": node[1], "role": node[2]}
    if tag == "technique_ref":
        return {"node": "technique_ref", "id": node[1]}
    raise DiscoveryError(f"unknown internal IR node {tag!r}")


def _node_size(node: Node) -> int:
    tag = node[0]
    if tag in {"const", "fvar", "lit", "sort", "meta", "technique_ref"}:
        return 1
    if tag == "app":
        return 1 + _node_size(node[1]) + sum(_node_size(value) for _explicit, value in node[2])
    if tag in {"forall", "lam"}:
        return 1 + _node_size(node[2]) + _node_size(node[3])
    if tag == "proj":
        return 1 + _node_size(node[2])
    if tag == "let":
        return 1 + sum(_node_size(part) for part in node[1:])
    raise DiscoveryError(f"cannot size internal IR node {tag!r}")


def _node_key(node: Node) -> str:
    return _canonical_json(_node_json(node))


def _type_skeleton(node: Node) -> Any:
    """Preserve type constructors while alpha-normalizing local variables."""
    tag = node[0]
    if tag == "fvar":
        return ("binder", node[1])
    if tag == "const":
        return node
    if tag in {"lit", "sort", "meta", "technique_ref"}:
        return node
    if tag == "app":
        return ("app", _type_skeleton(node[1]), tuple(
            (explicit, _type_skeleton(value)) for explicit, value in node[2]
        ))
    if tag in {"forall", "lam"}:
        return (tag, node[1], _type_skeleton(node[2]), _type_skeleton(node[3]))
    if tag == "proj":
        return ("proj", node[1], _type_skeleton(node[2]))
    if tag == "let":
        return ("let", *(_type_skeleton(part) for part in node[1:]))
    raise DiscoveryError(f"cannot skeletonize internal IR node {tag!r}")


@dataclass(frozen=True, eq=False)
class SignatureIR:
    binders: tuple[tuple[str, Node, Any], ...]
    conclusion: Node
    type_evidence: tuple[dict[str, Any] | None, ...] = ()

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, SignatureIR):
            return NotImplemented
        # Raw binder dicts retain source names for evidence classification, but
        # names are not part of the canonical structural identity.
        return (
            tuple((info, tree) for info, tree, _raw in self.binders)
            == tuple((info, tree) for info, tree, _raw in other.binders)
            and self.conclusion == other.conclusion
        )

    def binder_type_evidence(self, index: int) -> dict[str, Any] | None:
        if 0 <= index < len(self.type_evidence):
            return self.type_evidence[index]
        return None

    def as_json(self) -> dict[str, Any]:
        return {
            "binders": [
                {"binderInfo": info, "type": _node_json(tree),
                 "type_skeleton": _canonical_json(_type_skeleton(tree))}
                for info, tree, _raw in self.binders
            ],
            "conclusion": _node_json(self.conclusion),
        }

    def fvar_contracts(self) -> dict[str, dict[str, Any]]:
        contracts: dict[str, dict[str, Any]] = {}
        for index, (_info, tree, raw) in enumerate(self.binders):
            evidence = self.binder_type_evidence(index)
            if _binder_role(raw, tree, evidence).startswith("hypothesis_"):
                contracts[f"top:{index}"] = {
                    "kind": "hypothesis_role",
                    "role": "hypothesis",
                    "classification": "trusted_lean_type_evidence",
                }
            else:
                contracts[f"top:{index}"] = {
                    "kind": "exact",
                    "skeleton": _canonical_json(_type_skeleton(tree)),
                }
        return contracts


def _binder_role(
    raw: Any,
    tree: Node,
    type_evidence: dict[str, Any] | None = None,
) -> str:
    """Classify only the safe structural distinction needed for domains.

    Pretty-printed text and binder names are never evidence.  The role is
    trusted only when the bounded Lean-elaborated sidecar says the domain is
    proposition-valued and has ``Prop`` as its type sort.  Ordinary
    data/type domains still require exact normalized type skeletons.
    """
    if (
        isinstance(type_evidence, dict)
        and type_evidence.get("is_proposition") is True
        and type_evidence.get("type_sort") == "Prop"
    ):
        return "hypothesis_lean_type_evidence"
    return "unknown"


def _binder_type_match(
    left_raw: Any,
    left_type: Node,
    right_raw: Any,
    right_type: Node,
    left_evidence: dict[str, Any] | None = None,
    right_evidence: dict[str, Any] | None = None,
) -> dict[str, Any] | None:
    left_skeleton = _canonical_json(_type_skeleton(left_type))
    right_skeleton = _canonical_json(_type_skeleton(right_type))
    if left_skeleton == right_skeleton:
        return {"kind": "exact", "skeleton": left_skeleton}
    left_role = _binder_role(left_raw, left_type, left_evidence)
    right_role = _binder_role(right_raw, right_type, right_evidence)
    if left_role.startswith("hypothesis_") and right_role.startswith("hypothesis_"):
        return {
            "kind": "hypothesis_role",
            "role": "hypothesis",
            "classification": "trusted_lean_type_evidence",
            "left_role": left_role,
            "right_role": right_role,
            "left_skeleton": left_skeleton,
            "right_skeleton": right_skeleton,
        }
    return None


def _signature_ir(
    record: dict[str, Any],
    *,
    type_evidence: list[dict[str, Any]] | None = None,
) -> SignatureIR:
    binders_raw = record.get("binders")
    conclusion_raw = record.get("conclusion_tree")
    if not isinstance(binders_raw, list) or not isinstance(conclusion_raw, dict):
        raise UnsupportedTree("missing_binders_or_conclusion_tree")
    if type_evidence is not None and len(type_evidence) != len(binders_raw):
        raise UnsupportedTree("type_evidence_binder_count_mismatch")
    binders: list[tuple[str, Node, Any]] = []
    # Lean telescopes permit a binder type to depend on earlier binders, never
    # on a later binder.  Build the name environment progressively and pass
    # the same prefix bound to binderIdx validation; constructing ``top_env``
    # from the whole list would silently accept forward references.
    top_env: dict[str, str] = {}
    for index, binder in enumerate(binders_raw):
        if not isinstance(binder, dict) or not isinstance(binder.get("tree"), dict):
            raise UnsupportedTree(f"binder_{index}:missing_tree")
        if binder.get("idx") != index:
            raise UnsupportedTree(f"binder_{index}:malformed_or_noncanonical_index")
        if not isinstance(binder.get("binderInfo"), str) or not binder.get("binderInfo"):
            raise UnsupportedTree(f"binder_{index}:malformed_binder_info")
        binder_info = str(binder.get("binderInfo") or "default")
        tree = _parse_node(binder["tree"], path=f"binders/{index}/tree", env=top_env,
                           scope_path=(index,), top_count=index)
        binders.append((binder_info, tree, binder))
        binder_name = binder.get("name")
        if isinstance(binder_name, str) and binder_name:
            top_env[binder_name] = f"top:{index}"
    conclusion = _parse_node(conclusion_raw, path="conclusion_tree", env=top_env,
                             scope_path=(len(binders_raw),), top_count=len(binders_raw))
    return SignatureIR(
        tuple(binders), conclusion,
        tuple(type_evidence) if type_evidence is not None else tuple(None for _ in binders),
    )


@dataclass
class LoadedDeclaration:
    name: str
    record: dict[str, Any]
    family: str
    partition: str
    ir: SignatureIR | None
    status: str
    reason: str | None
    signature_sha256: str
    source: dict[str, Any]
    evidence: dict[str, Any]

    @property
    def usable(self) -> bool:
        return self.status == "usable" and self.ir is not None


def _record_source(record: dict[str, Any], source_hashes: dict[str, str]) -> dict[str, Any]:
    raw_range = record.get("range") or {}
    start = raw_range.get("start") if isinstance(raw_range, dict) else None
    end = raw_range.get("end") if isinstance(raw_range, dict) else None
    src_file = record.get("src_file")
    source_hash = source_hashes.get(src_file) if isinstance(src_file, str) else None
    return {
        "file": src_file,
        "sha256": source_hash,
        "hash_status": "captured_source_manifest" if source_hash else "not_available",
        "start": start[0] + 1 if isinstance(start, list) and start and isinstance(start[0], int) else None,
        "end": end[0] + 1 if isinstance(end, list) and end and isinstance(end[0], int) else None,
        "module": record.get("module"),
        "source_name": record.get("source_name"),
        "surface": record.get("capture_surface"),
    }


def _signature_hash(record: dict[str, Any]) -> str:
    return _sha256_json({
        "name": record.get("name"),
        "binders": record.get("binders"),
        "conclusion_tree": record.get("conclusion_tree"),
        "signature": record.get("signature"),
    })


def _capture_binder_sha256(binder: dict[str, Any]) -> str:
    """Hash the exact captured binder row used by the Lean sidecar binding."""
    return _sha256_json(binder)


def _type_evidence_capture_binding(
    record: dict[str, Any], type_record: dict[str, Any] | None,
) -> tuple[list[dict[str, Any]] | None, dict[str, Any]]:
    """Bind every sidecar row to the capture, not only to its source range."""
    if type_record is None:
        return None, {"status": "unknown", "reason": "type_evidence_record_unavailable"}
    if type_record.get("capture_signature_sha256") != _signature_hash(record):
        return None, {
            "status": "unknown", "reason": "type_evidence_capture_signature_mismatch"
        }
    capture_binders = record.get("binders")
    sidecar_binders = type_record.get("binders")
    if not isinstance(capture_binders, list) or not isinstance(sidecar_binders, list):
        return None, {"status": "unknown", "reason": "type_evidence_capture_binders_malformed"}
    if len(capture_binders) != len(sidecar_binders):
        return None, {"status": "unknown", "reason": "type_evidence_capture_binder_count_mismatch"}
    for capture_binder, sidecar_binder in zip(capture_binders, sidecar_binders):
        if not isinstance(capture_binder, dict) or not isinstance(sidecar_binder, dict):
            return None, {"status": "unknown", "reason": "type_evidence_capture_binder_malformed"}
        if (
            sidecar_binder.get("idx") != capture_binder.get("idx")
            or sidecar_binder.get("binderInfo") != capture_binder.get("binderInfo")
            or sidecar_binder.get("type") != capture_binder.get("type")
            or sidecar_binder.get("capture_binder_sha256") != _capture_binder_sha256(capture_binder)
            or (
                capture_binder.get("name") is not None
                and sidecar_binder.get("name") != capture_binder.get("name")
            )
        ):
            return None, {
                "status": "unknown", "reason": "type_evidence_capture_binder_mismatch"
            }
    return sidecar_binders, {"status": "captured"}


def _capture_evidence(
    record: dict[str, Any],
    capture: dict[str, Any],
    *,
    type_evidence: dict[str, Any] | None = None,
) -> dict[str, Any]:
    projection = capture.get("capture_projection") if isinstance(capture, dict) else None
    projection_status = "captured" if isinstance(projection, dict) else "unknown"
    projection = projection if isinstance(projection, dict) else {}
    raw_binders = record.get("binders")
    binder_rows = raw_binders if isinstance(raw_binders, list) else []
    premises = record.get("premises")
    premise_rows = premises if isinstance(premises, list) else []
    return {
        "capture_status": projection_status,
        **({"reason": "capture_projection_malformed"} if projection_status == "unknown" else {}),
        "expression_trees_included": projection.get("expression_trees_included"),
        "expression_trees_complete": projection.get("expression_trees_complete"),
        "proof_terms_included": projection.get("proof_terms_included"),
        "premises_included": projection.get("premises_included"),
        "premises_complete": projection.get("premises_complete"),
        "tree_diagnostics": {
            "binder_errors": sum(bool(b.get("tree_error")) for b in binder_rows if isinstance(b, dict)),
            "conclusion_error": record.get("conclusion_tree_error"),
        },
        "premise_counts": {
            "total": len(premise_rows),
            "type": sum(bool(row.get("in_type")) for row in premise_rows if isinstance(row, dict)),
            "proof": sum(bool(row.get("in_proof")) for row in premise_rows if isinstance(row, dict)),
        },
        "type_evidence": type_evidence or {
            "status": "unknown", "reason": "type_evidence_record_unavailable"
        },
    }


def _trace_evidence(
    trace_index: dict[str, dict[str, Any]],
    name: str,
    prefix: str,
    trace_summary: dict[str, Any],
) -> dict[str, Any]:
    if trace_summary.get("status") != "captured":
        return {
            "trace_status": trace_summary.get("status", "unknown"),
            "reason": trace_summary.get("reason", "trace_not_verified"),
        }
    candidates = [name]
    if prefix and name.startswith(prefix):
        candidates.append(name[len(prefix):])
    record = next((trace_index.get(candidate) for candidate in candidates if trace_index.get(candidate)), None)
    if record is None:
        return {"trace_status": "unavailable", "reason": "no_matching_trace_record"}
    applications = record.get("application_records")
    references = record.get("reference_records")
    return {
        "trace_status": record.get("status", "captured"),
        "declaration": record.get("declaration"),
        "application_record_count": len(applications) if isinstance(applications, list) else None,
        "reference_record_count": len(references) if isinstance(references, list) else None,
        "proof_constants_count": len(record.get("proof_constants", [])) if isinstance(record.get("proof_constants"), list) else None,
        "tree_present": isinstance(record.get("tree"), dict),
    }


def _load_trace(
    path: Path | None,
    *,
    limits: dict[str, int],
    expected_toolchain: str | None,
    expected_generated_from: str | None,
    expected_source_revision: str | None = None,
    expected_declarations: tuple[str, ...] | None = None,
    expected_manifest_sha256: str | None = None,
    expected_capture_sha256: str | None = None,
    expected_extractor_path: Path | None = None,
    expected_extractor_sha256: str | None = None,
) -> tuple[dict[str, dict[str, Any]], str | None, dict[str, Any]]:
    if path is None:
        return {}, None, {"status": "unavailable", "reason": "manifest_has_no_trace"}
    if not path.is_file():
        return {}, None, {"status": "unknown", "reason": f"trace_not_found:{path.name}"}
    if path.stat().st_size > limits["max_trace_bytes"]:
        return {}, None, {
            "status": "unknown",
            "reason": "trace_compressed_size_limit",
            "compressed_bytes": path.stat().st_size,
            "max_bytes": limits["max_trace_bytes"],
            "hash_status": "not_verified_budget",
        }
    try:
        raw, digest = _read_json_bounded(path, limits["max_trace_bytes"], label="trace")
    except DiscoveryError as error:
        return {}, None, {
            "status": "unknown", "reason": str(error), "hash_status": "not_verified"
        }
    if not isinstance(raw, dict) or not isinstance(raw.get("records"), list):
        return {}, digest, {"status": "unknown", "reason": "trace_missing_records_list"}
    if raw.get("schema_version") != 1:
        return {}, digest, {"status": "unknown", "reason": "trace_schema_mismatch"}
    if not isinstance(raw.get("toolchain"), str) or not raw.get("toolchain"):
        return {}, digest, {"status": "unknown", "reason": "trace_toolchain_missing"}
    if expected_toolchain is not None and raw.get("toolchain") != expected_toolchain:
        return {}, digest, {
            "status": "unknown", "reason": "trace_toolchain_mismatch",
            "expected_toolchain": expected_toolchain, "actual_toolchain": raw.get("toolchain"),
        }
    if not isinstance(raw.get("generated_from"), str) or not raw.get("generated_from"):
        return {}, digest, {"status": "unknown", "reason": "trace_generated_from_missing"}
    if expected_generated_from is not None and raw.get("generated_from") != expected_generated_from:
        return {}, digest, {
            "status": "unknown", "reason": "trace_generated_from_mismatch",
            "expected_generated_from": expected_generated_from,
            "actual_generated_from": raw.get("generated_from"),
        }
    trace_revision = raw.get("source_revision")
    if not isinstance(trace_revision, str) or not trace_revision:
        return {}, digest, {"status": "unknown", "reason": "trace_source_revision_missing"}
    if expected_source_revision is not None and trace_revision != expected_source_revision:
        return {}, digest, {
            "status": "unknown", "reason": "trace_source_revision_mismatch",
            "expected_source_revision": expected_source_revision,
            "actual_source_revision": trace_revision,
        }
    if expected_manifest_sha256 is not None:
        manifest_sha256 = raw.get("manifest_sha256")
        if not isinstance(manifest_sha256, str) or manifest_sha256 != expected_manifest_sha256:
            return {}, digest, {
                "status": "unknown", "reason": "trace_manifest_identity_mismatch",
                "expected_manifest_sha256": expected_manifest_sha256,
                "actual_manifest_sha256": manifest_sha256,
            }
    if expected_capture_sha256 is not None:
        capture_sha256 = raw.get("capture_sha256")
        if not isinstance(capture_sha256, str) or capture_sha256 != expected_capture_sha256:
            return {}, digest, {
                "status": "unknown", "reason": "trace_capture_identity_mismatch",
                "expected_capture_sha256": expected_capture_sha256,
                "actual_capture_sha256": capture_sha256,
            }
    if expected_extractor_sha256 is not None:
        extractor_sha256 = raw.get("extractor_sha256")
        if not isinstance(extractor_sha256, str) or extractor_sha256 != expected_extractor_sha256:
            return {}, digest, {
                "status": "unknown", "reason": "trace_extractor_identity_mismatch",
                "expected_extractor_sha256": expected_extractor_sha256,
                "actual_extractor_sha256": extractor_sha256,
            }
        if expected_extractor_path is None or not expected_extractor_path.is_file():
            return {}, digest, {"status": "unknown", "reason": "trace_extractor_not_found"}
        if _sha256_file(expected_extractor_path) != expected_extractor_sha256:
            return {}, digest, {"status": "unknown", "reason": "trace_extractor_file_tampered"}
    if len(raw["records"]) > limits["max_trace_records"]:
        return {}, digest, {
            "status": "unknown", "reason": "trace_record_limit",
            "records": len(raw["records"]), "max_records": limits["max_trace_records"],
        }
    selected = raw.get("selected_declarations")
    if selected is None and expected_declarations is not None:
        return {}, digest, {"status": "unknown", "reason": "trace_selected_declarations_missing"}
    if selected is not None and (
        not isinstance(selected, list)
        or not all(isinstance(item, str) for item in selected)
    ):
        return {}, digest, {"status": "unknown", "reason": "trace_selected_declarations_malformed"}
    if expected_declarations is not None and set(selected or ()) != set(expected_declarations):
        return {}, digest, {
            "status": "unknown", "reason": "trace_selected_declarations_mismatch",
            "expected_count": len(set(expected_declarations)),
            "actual_count": len(set(selected or ())),
        }
    index = {}
    for record in raw["records"]:
        if not isinstance(record, dict) or not isinstance(record.get("declaration"), str):
            return {}, digest, {"status": "unknown", "reason": "trace_record_malformed"}
        if selected is not None and record["declaration"] not in selected:
            return {}, digest, {"status": "unknown", "reason": "trace_record_not_selected"}
        if record["declaration"] in index:
            return {}, digest, {"status": "unknown", "reason": "trace_duplicate_declaration"}
        index[record["declaration"]] = record
    if selected is not None and set(index) != set(selected):
        return {}, digest, {"status": "unknown", "reason": "trace_selected_declarations_mismatch"}
    return index, digest, {
        "status": "captured",
        "schema_version": raw.get("schema_version"),
        "toolchain": raw.get("toolchain"),
        "generated_from": raw.get("generated_from"),
        **({"manifest_sha256": raw.get("manifest_sha256")} if expected_manifest_sha256 is not None else {}),
        **({"capture_sha256": raw.get("capture_sha256")} if expected_capture_sha256 is not None else {}),
        **({"extractor_sha256": raw.get("extractor_sha256")} if expected_extractor_sha256 is not None else {}),
        "record_count": len(index),
    }


def _load_type_evidence(
    path: Path | None,
    *,
    limits: dict[str, int],
    expected_declarations: tuple[str, ...],
    expected_toolchain: str | None,
    expected_generated_from: str | None,
    expected_source_revision: str | None,
    expected_surface_prefix: str,
    expected_capture_sha256: str | None = None,
    expected_artifact_sha256: str | None = None,
    expected_extractor_path: Path | None = None,
    expected_extractor_sha256: str | None = None,
) -> tuple[dict[str, dict[str, Any]], str | None, dict[str, Any]]:
    """Load the selected Lean ``isProp``/type-sort sidecar conservatively."""
    if path is None:
        return {}, None, {"status": "unavailable", "reason": "manifest_has_no_type_evidence"}
    if not path.is_file():
        return {}, None, {"status": "unknown", "reason": f"type_evidence_not_found:{path.name}"}
    if path.stat().st_size > limits["max_type_evidence_bytes"]:
        return {}, None, {
            "status": "unknown",
            "reason": "type_evidence_size_limit",
            "compressed_bytes": path.stat().st_size,
            "max_bytes": limits["max_type_evidence_bytes"],
            "hash_status": "not_verified_budget",
        }
    try:
        raw, digest = _read_json_bounded(
            path, limits["max_type_evidence_bytes"], label="type_evidence"
        )
    except DiscoveryError as error:
        return {}, None, {
            "status": "unknown", "reason": str(error), "hash_status": "not_verified"
        }
    if expected_artifact_sha256 is not None and digest != expected_artifact_sha256:
        return {}, digest, {
            "status": "unknown", "reason": "type_evidence_artifact_hash_mismatch",
            "expected_sha256": expected_artifact_sha256, "actual_sha256": digest,
        }
    if not isinstance(raw, dict) or not isinstance(raw.get("declarations"), list):
        return {}, digest, {"status": "unknown", "reason": "type_evidence_missing_declarations_list"}
    if raw.get("schema_version") != 1:
        return {}, digest, {"status": "unknown", "reason": "type_evidence_schema_mismatch"}
    toolchain = raw.get("toolchain")
    if not isinstance(toolchain, str) or not toolchain:
        return {}, digest, {"status": "unknown", "reason": "type_evidence_toolchain_missing"}
    if expected_toolchain is not None and toolchain != expected_toolchain:
        return {}, digest, {
            "status": "unknown", "reason": "type_evidence_toolchain_mismatch",
            "expected_toolchain": expected_toolchain, "actual_toolchain": toolchain,
        }
    generated_from = raw.get("generated_from")
    if not isinstance(generated_from, str) or not generated_from:
        return {}, digest, {"status": "unknown", "reason": "type_evidence_generated_from_missing"}
    if expected_generated_from is not None and generated_from != expected_generated_from:
        return {}, digest, {
            "status": "unknown", "reason": "type_evidence_generated_from_mismatch",
            "expected_generated_from": expected_generated_from,
            "actual_generated_from": generated_from,
        }
    revision = raw.get("source_revision")
    if not isinstance(revision, str) or not revision:
        return {}, digest, {"status": "unknown", "reason": "type_evidence_source_revision_missing"}
    if expected_source_revision is not None and revision != expected_source_revision:
        return {}, digest, {
            "status": "unknown", "reason": "type_evidence_source_revision_mismatch",
            "expected_source_revision": expected_source_revision,
            "actual_source_revision": revision,
        }
    if expected_capture_sha256 is not None:
        capture_sha256 = raw.get("capture_sha256")
        if not isinstance(capture_sha256, str) or capture_sha256 != expected_capture_sha256:
            return {}, digest, {
                "status": "unknown", "reason": "type_evidence_capture_identity_mismatch",
                "expected_capture_sha256": expected_capture_sha256,
                "actual_capture_sha256": capture_sha256,
            }
    if expected_extractor_sha256 is not None:
        extractor_sha256 = raw.get("extractor_sha256")
        if not isinstance(extractor_sha256, str) or extractor_sha256 != expected_extractor_sha256:
            return {}, digest, {
                "status": "unknown", "reason": "type_evidence_extractor_identity_mismatch",
                "expected_extractor_sha256": expected_extractor_sha256,
                "actual_extractor_sha256": extractor_sha256,
            }
        if expected_extractor_path is None or not expected_extractor_path.is_file():
            return {}, digest, {"status": "unknown", "reason": "type_evidence_extractor_not_found"}
        if _sha256_file(expected_extractor_path) != expected_extractor_sha256:
            return {}, digest, {
                "status": "unknown", "reason": "type_evidence_extractor_file_tampered"
            }
    scope = raw.get("scope")
    if scope != "bounded_selected_declaration_binder_type_evidence":
        return {}, digest, {"status": "unknown", "reason": "type_evidence_scope_mismatch"}
    if raw.get("extraction_mode") != "lean_meta_replay":
        return {}, digest, {
            "status": "unknown", "reason": "type_evidence_extraction_mode_untrusted"
        }
    provenance = raw.get("extraction_provenance")
    replay_command = provenance.get("replay_command") if isinstance(provenance, dict) else None
    replay_prefix_ok = (
        isinstance(replay_command, list)
        and len(replay_command) == 5
        and replay_command[:4] == ["lake", "env", "lean", "--run"]
    )
    replay_absolute_prefix_ok = (
        isinstance(replay_command, list)
        and len(replay_command) == 5
        and Path(str(replay_command[0])).name == "lake"
        and Path(str(replay_command[0])).is_absolute()
        and replay_command[1] == "env"
        and replay_command[3] == "--run"
        and Path(str(replay_command[2])).name == "lean"
        and Path(str(replay_command[2])).is_absolute()
    )
    if (
        not isinstance(provenance, dict)
        or not isinstance(provenance.get("extractor"), str)
        or not isinstance(provenance.get("capture"), str)
        or not isinstance(provenance.get("manifest"), str)
        or not isinstance(provenance.get("selected_declaration_count"), int)
        or not (replay_prefix_ok or replay_absolute_prefix_ok)
        or expected_extractor_path is None
        or not str(replay_command[4]).endswith(expected_extractor_path.name)
        or provenance["selected_declaration_count"] != len(expected_declarations)
    ):
        return {}, digest, {
            "status": "unknown", "reason": "type_evidence_replay_provenance_malformed"
        }
    if raw.get("surface_prefix") != expected_surface_prefix:
        return {}, digest, {
            "status": "unknown", "reason": "type_evidence_surface_prefix_mismatch",
            "expected_surface_prefix": expected_surface_prefix,
            "actual_surface_prefix": raw.get("surface_prefix"),
        }
    if len(raw["declarations"]) > limits["max_type_evidence_records"]:
        return {}, digest, {
            "status": "unknown", "reason": "type_evidence_record_limit",
            "records": len(raw["declarations"]),
            "max_records": limits["max_type_evidence_records"],
        }
    expected = set(expected_declarations)
    index: dict[str, dict[str, Any]] = {}
    for record in raw["declarations"]:
        if not isinstance(record, dict) or not isinstance(record.get("declaration"), str):
            return {}, digest, {"status": "unknown", "reason": "type_evidence_record_malformed"}
        name = record["declaration"]
        if name in index:
            return {}, digest, {"status": "unknown", "reason": "type_evidence_duplicate_declaration"}
        if not isinstance(record.get("binders"), list):
            return {}, digest, {"status": "unknown", "reason": "type_evidence_binders_malformed"}
        if (
            not isinstance(record.get("source_file"), str)
            or not isinstance(record.get("range"), (dict, type(None)))
            or not isinstance(record.get("source_name"), str)
            or not isinstance(record.get("capture_signature_sha256"), str)
        ):
            return {}, digest, {"status": "unknown", "reason": "type_evidence_source_provenance_malformed"}
        rows: list[dict[str, Any]] = []
        for index_value, binder in enumerate(record["binders"]):
            if not isinstance(binder, dict) or binder.get("idx") != index_value:
                return {}, digest, {"status": "unknown", "reason": "type_evidence_binder_index_malformed"}
            if not isinstance(binder.get("is_proposition"), bool):
                return {}, digest, {"status": "unknown", "reason": "type_evidence_is_prop_malformed"}
            if not isinstance(binder.get("type_sort"), str) or not binder["type_sort"]:
                return {}, digest, {"status": "unknown", "reason": "type_evidence_type_sort_malformed"}
            if (
                not isinstance(binder.get("name"), str)
                or not isinstance(binder.get("binderInfo"), str)
                or not isinstance(binder.get("type"), str)
                or not isinstance(binder.get("capture_binder_sha256"), str)
            ):
                return {}, digest, {
                    "status": "unknown", "reason": "type_evidence_capture_binding_malformed"
                }
            if binder.get("is_proposition") != (binder.get("type_sort") == "Prop"):
                return {}, digest, {
                    "status": "unknown", "reason": "type_evidence_prop_sort_inconsistent"
                }
            rows.append(binder)
        index[name] = {**record, "binders": rows}
    if set(index) != expected:
        return {}, digest, {
            "status": "unknown", "reason": "type_evidence_selected_declarations_mismatch",
            "expected_count": len(expected), "actual_count": len(index),
        }
    return index, digest, {
        "status": "captured",
        "schema_version": raw["schema_version"],
        "toolchain": toolchain,
        "generated_from": generated_from,
        "source_revision": revision,
        "extraction_mode": raw.get("extraction_mode"),
        "extraction_provenance": provenance,
        **({"capture_sha256": raw.get("capture_sha256")} if expected_capture_sha256 is not None else {}),
        **({"extractor_sha256": raw.get("extractor_sha256")} if expected_extractor_sha256 is not None else {}),
        "scope": scope,
        "record_count": len(index),
    }


def load_corpus(manifest: Manifest) -> tuple[list[LoadedDeclaration], dict[str, Any]]:
    if not manifest.capture_path.is_file():
        raise DiscoveryError(f"capture artifact not found: {manifest.capture_path}")
    capture, capture_hash = _read_json(manifest.capture_path)
    if not isinstance(capture, dict) or not isinstance(capture.get("declarations"), list):
        raise DiscoveryError("capture artifact must contain a declarations list")
    if capture.get("schema_version") != SCHEMA_VERSION:
        raise DiscoveryError(f"capture artifact must use schema_version {SCHEMA_VERSION}")
    capture_identity_status = {"status": "captured"}
    if manifest.capture_sha256 is not None and capture_hash != manifest.capture_sha256:
        capture_identity_status = {
            "status": "unknown",
            "reason": "capture_artifact_hash_mismatch",
            "expected_sha256": manifest.capture_sha256,
            "actual_sha256": capture_hash,
        }
    capture_metadata = {
        "generated_from": capture.get("generated_from"),
        "toolchain": capture.get("toolchain"),
        "source_revision": capture.get("source_revision"),
    }
    capture_metadata_status = "captured"
    capture_metadata_reason = None
    for field_name, value in capture_metadata.items():
        if not isinstance(value, str) or not value:
            capture_metadata_status = "unknown"
            capture_metadata_reason = f"capture_{field_name}_missing"
            break
    projection = capture.get("capture_projection")
    if not isinstance(projection, dict):
        capture_metadata_status = "unknown"
        capture_metadata_reason = "capture_projection_malformed"
    trace_names = tuple(
        name[len(manifest.surface_prefix):]
        if manifest.surface_prefix and name.startswith(manifest.surface_prefix)
        else name
        for name in manifest.declaration_names
    )
    trace_capture_identity = None
    trace_capture_pin_error: dict[str, Any] | None = None
    if manifest.trace_capture_sha256 is not None:
        if manifest.trace_capture_sha256 != capture_hash:
            trace_capture_pin_error = {
                "status": "unknown",
                "reason": "trace_manifest_capture_pin_mismatch",
                "expected_capture_sha256": capture_hash,
                "manifest_capture_sha256": manifest.trace_capture_sha256,
            }
        else:
            trace_capture_identity = capture_hash
    trace_index, trace_hash, trace_summary = _load_trace(
        manifest.trace_path,
        limits=manifest.limits,
        expected_toolchain=capture.get("toolchain"),
        expected_generated_from=manifest.trace_generated_from,
        expected_source_revision=capture.get("source_revision"),
        expected_declarations=trace_names,
        expected_manifest_sha256=(
            manifest.content_hash
            if manifest.trace_capture_sha256 is not None
            or manifest.trace_extractor_sha256 is not None
            else None
        ),
        expected_capture_sha256=trace_capture_identity,
        expected_extractor_path=manifest.trace_extractor_path,
        expected_extractor_sha256=manifest.trace_extractor_sha256,
    )
    if trace_capture_pin_error is not None:
        trace_index, trace_summary = {}, trace_capture_pin_error
    type_capture_identity = None
    type_capture_pin_error: dict[str, Any] | None = None
    if manifest.type_evidence_capture_sha256 is not None:
        if manifest.type_evidence_capture_sha256 != capture_hash:
            type_capture_pin_error = {
                "status": "unknown",
                "reason": "type_evidence_manifest_capture_pin_mismatch",
                "expected_capture_sha256": capture_hash,
                "manifest_capture_sha256": manifest.type_evidence_capture_sha256,
            }
        else:
            type_capture_identity = capture_hash
    type_evidence_by_name, type_evidence_hash, type_evidence_summary = _load_type_evidence(
        manifest.type_evidence_path,
        limits=manifest.limits,
        expected_declarations=manifest.declaration_names,
        expected_toolchain=capture.get("toolchain"),
        expected_generated_from=manifest.type_evidence_generated_from,
        expected_source_revision=capture.get("source_revision"),
        expected_surface_prefix=manifest.surface_prefix,
        expected_capture_sha256=type_capture_identity,
        expected_artifact_sha256=manifest.type_evidence_sha256,
        expected_extractor_path=manifest.type_evidence_extractor_path,
        expected_extractor_sha256=manifest.type_evidence_extractor_sha256,
    )
    if type_capture_pin_error is not None:
        type_evidence_by_name, type_evidence_summary = {}, type_capture_pin_error
    source_hashes: dict[str, str] = {}
    source_manifest_hash = None
    source_manifest_summary = {"status": "unavailable", "reason": "manifest_has_no_source_manifest"}
    if manifest.source_manifest_path is not None:
        if not manifest.source_manifest_path.is_file():
            raise DiscoveryError(f"source manifest not found: {manifest.source_manifest_path}")
        source_manifest, source_manifest_hash = _read_json(manifest.source_manifest_path)
        if not isinstance(source_manifest, dict) or not isinstance(source_manifest.get("files"), list):
            raise DiscoveryError("source manifest must contain a files list")
        source_root_raw = source_manifest.get("source_root")
        source_root = Path(source_root_raw).expanduser().resolve() if isinstance(source_root_raw, str) else None
        if source_root is not None:
            for row in source_manifest["files"]:
                if not isinstance(row, dict) or not isinstance(row.get("path"), str):
                    continue
                relative = Path(row["path"])
                if relative.is_absolute():
                    raise DiscoveryError("source_manifest_path_traversal")
                candidate = (source_root / relative).resolve()
                try:
                    candidate.relative_to(source_root)
                except ValueError as error:
                    raise DiscoveryError("source_manifest_path_traversal") from error
        source_hashes = {
            row["path"]: row["sha256"]
            for row in source_manifest["files"]
            if isinstance(row, dict) and isinstance(row.get("path"), str)
            and isinstance(row.get("sha256"), str)
        }
        source_manifest_revision = source_manifest.get("source_revision")
        if manifest.source_revision is not None and source_manifest_revision != manifest.source_revision:
            raise DiscoveryError(
                f"source manifest revision mismatch: manifest={manifest.source_revision!r} "
                f"source_manifest={source_manifest_revision!r}"
            )
        source_manifest_summary = {
            "status": "captured",
            "file_count": source_manifest.get("file_count"),
            "lean_file_count": source_manifest.get("lean_file_count"),
        }
    family_map = manifest.family_by_declaration()
    by_name = {
        record.get("name"): record for record in capture["declarations"]
        if isinstance(record, dict) and isinstance(record.get("name"), str)
    }
    declarations: list[LoadedDeclaration] = []
    type_evidence_link_status = {"status": "captured"}
    for name in manifest.declaration_names:
        family = family_map[name]
        record = by_name.get(name)
        if record is None:
            declarations.append(LoadedDeclaration(
                name=name, record={}, family=family.name, partition=family.partition,
                ir=None, status="unknown", reason="declaration_not_in_capture",
                signature_sha256="", source={}, evidence={"capture_status": "unknown"},
            ))
            continue
        signature_hash = _signature_hash(record)
        type_record = type_evidence_by_name.get(name)
        type_rows, type_binding_status = _type_evidence_capture_binding(
            record, type_record if isinstance(type_record, dict) else None
        )
        if type_record is not None and (
            type_record.get("source_file") != record.get("src_file")
            or type_record.get("range") != record.get("range")
            or type_record.get("source_name") != record.get("source_name")
        ):
            type_rows = None
            type_binding_status = {
                "status": "unknown",
                "reason": "type_evidence_source_provenance_mismatch",
                "declaration": name,
            }
        if type_binding_status["status"] != "captured":
            if type_evidence_link_status["status"] == "captured":
                type_evidence_link_status = {**type_binding_status, "declaration": name}
        try:
            ir = _signature_ir(record, type_evidence=type_rows)
            status, reason = "usable", None
        except UnsupportedTree as error:
            ir, status, reason = None, "unknown", str(error)
        declarations.append(LoadedDeclaration(
            name=name, record=record, family=family.name, partition=family.partition,
            ir=ir, status=status, reason=reason, signature_sha256=signature_hash,
            source=_record_source(record, source_hashes),
            evidence={**_capture_evidence(
                          record, capture,
                          type_evidence=(
                              {"status": "captured", "binders": type_rows}
                              if type_rows is not None and type_binding_status["status"] == "captured"
                              else type_binding_status
                          ),
                      ),
                      "trace": _trace_evidence(
                          trace_index, name, manifest.surface_prefix, trace_summary
                      )},
        ))
    if len(declarations) > manifest.limits["max_declarations"]:
        raise DiscoveryError(
            f"manifest selects {len(declarations)} declarations, over max_declarations="
            f"{manifest.limits['max_declarations']}"
        )
    source_revision = capture.get("source_revision")
    if manifest.source_revision is not None and source_revision != manifest.source_revision:
        raise DiscoveryError(
            f"source revision mismatch: manifest={manifest.source_revision!r} capture={source_revision!r}"
        )
    input_info = {
        "capture_sha256": capture_hash,
        "trace_sha256": trace_hash,
        "source_revision": source_revision,
        "source_repository": capture.get("source_repository"),
        "toolchain": capture.get("toolchain"),
        "capture": {
            "status": (
                capture_metadata_status
                if capture_identity_status["status"] == "captured"
                else "unknown"
            ),
            **({"reason": capture_metadata_reason} if capture_metadata_reason else {}),
            **({"identity": capture_identity_status}
               if capture_identity_status["status"] != "captured" else {}),
            "schema_version": capture.get("schema_version"),
            **capture_metadata,
        },
        "capture_projection": projection,
        "source_manifest_sha256": source_manifest_hash,
        "source_manifest": source_manifest_summary,
        "trace": trace_summary,
        "type_evidence_sha256": type_evidence_hash,
        "type_evidence": {
            **type_evidence_summary,
            **({"link_status": type_evidence_link_status}
               if type_evidence_link_status["status"] != "captured" else {}),
        },
    }
    evidence_parts = {
        "capture": (
            capture_metadata_status
            if capture_identity_status["status"] == "captured"
            else "unknown"
        ),
        "source_manifest": source_manifest_summary["status"],
        "trace": trace_summary["status"] if manifest.trace_path is not None else "not_required",
        "type_evidence": (
            type_evidence_link_status["status"]
            if manifest.type_evidence_path is not None
            and type_evidence_summary["status"] == "captured"
            else (
                type_evidence_summary["status"]
                if manifest.type_evidence_path is not None
                else "not_required"
            )
        ),
    }
    input_info["evidence_status"] = {
        "status": "captured" if all(
            status in {"captured", "not_required"} for status in evidence_parts.values()
        ) else "unknown",
        "components": evidence_parts,
    }
    return declarations, input_info


def referenced_paths(manifest_path: str | Path) -> tuple[Path, ...]:
    """Return every transitive file/directory named by a discovery manifest.

    The MCP layer validates these resolved paths against its authorized roots
    before calling :func:`discover`.  Source manifest entries are included so
    a manifest cannot authorize only its immediate JSON files while reading a
    symlink or traversal path elsewhere.
    """
    manifest = load_manifest(manifest_path)
    paths: list[Path] = [manifest.path, manifest.capture_path]
    if manifest.trace_path is not None:
        paths.append(manifest.trace_path)
    if manifest.trace_extractor_path is not None:
        paths.append(manifest.trace_extractor_path)
    if manifest.type_evidence_path is not None:
        paths.append(manifest.type_evidence_path)
    if manifest.type_evidence_extractor_path is not None:
        paths.append(manifest.type_evidence_extractor_path)
    if manifest.source_manifest_path is not None:
        paths.append(manifest.source_manifest_path)
        source_manifest, _digest = _read_json(manifest.source_manifest_path)
        if not isinstance(source_manifest, dict) or not isinstance(source_manifest.get("files"), list):
            raise DiscoveryError("source manifest must contain a files list")
        source_root_raw = source_manifest.get("source_root")
        if isinstance(source_root_raw, str):
            source_root = Path(source_root_raw).expanduser().resolve()
            paths.append(source_root)
            for row in source_manifest["files"]:
                if isinstance(row, dict) and isinstance(row.get("path"), str):
                    if Path(row["path"]).is_absolute():
                        raise DiscoveryError("source_manifest_path_traversal")
                    candidate = (source_root / row["path"]).resolve()
                    try:
                        candidate.relative_to(source_root)
                    except ValueError as error:
                        raise DiscoveryError("source_manifest_path_traversal") from error
                    paths.append(candidate)
    return tuple(dict.fromkeys(paths))


def _premise_sets(declarations: Iterable[LoadedDeclaration], key: str) -> dict[str, set[str]]:
    result: dict[str, set[str]] = {}
    for declaration in declarations:
        rows = declaration.record.get("premises", []) if declaration.record else []
        if not isinstance(rows, list):
            rows = []
        result[declaration.name] = {
            row.get("name") for row in rows
            if isinstance(row, dict) and row.get(key) and isinstance(row.get("name"), str)
        }
    return result


def _baseline_payload(declaration: LoadedDeclaration) -> dict[str, Any] | None:
    if not declaration.usable:
        return None
    raw_signature = {
        "binders": [binder for _info, _tree, binder in declaration.ir.binders],
        "conclusion_tree": declaration.record.get("conclusion_tree"),
    }
    try:
        return similarity.feature_payload(raw_signature)
    except similarity.SimilarityError:
        return None


def _baseline_pairs(
    declarations: list[LoadedDeclaration],
    *,
    max_candidates_per_query: int,
    max_pairs: int,
    query_partition: str,
    candidate_partition: str,
) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    payloads = {declaration.name: _baseline_payload(declaration) for declaration in declarations}
    queries = [
        declaration for declaration in declarations
        if declaration.partition == query_partition and payloads.get(declaration.name) is not None
    ]
    candidates = [
        declaration for declaration in declarations
        if declaration.partition == candidate_partition and payloads.get(declaration.name) is not None
    ]
    type_premises = _premise_sets(declarations, "in_type")
    proof_premises = _premise_sets(declarations, "in_proof")
    head_weights = similarity._idf_weights([
        set(payloads[d.name]["semantic_heads"]) for d in candidates  # type: ignore[index]
    ])
    type_weights = similarity._idf_weights([type_premises[d.name] for d in candidates])
    proof_weights = similarity._idf_weights([proof_premises[d.name] for d in candidates])
    pairs: dict[tuple[str, str], dict[str, Any]] = {}
    query_count = 0
    for query in sorted(queries, key=lambda item: item.name):
        ranked: list[dict[str, Any]] = []
        qp = payloads[query.name]
        for candidate in sorted(candidates, key=lambda item: item.name):
            if candidate.name == query.name or candidate.record.get("kind") != query.record.get("kind"):
                continue
            cp = payloads[candidate.name]
            shape_score, shared_count = similarity._multiset_jaccard(
                similarity._shape_counter(qp), similarity._shape_counter(cp)
            )
            q_heads = set(qp["semantic_heads"])
            c_heads = set(cp["semantic_heads"])
            scores = {
                "shape": round(shape_score, 12),
                "semantic_heads": round(similarity._weighted_jaccard(q_heads, c_heads, head_weights), 12),
                "type_premises": round(similarity._weighted_jaccard(
                    type_premises[query.name], type_premises[candidate.name], type_weights
                ), 12),
                "proof_premises": round(similarity._weighted_jaccard(
                    proof_premises[query.name], proof_premises[candidate.name], proof_weights
                ), 12),
            }
            ranked.append({
                "query": query.name,
                "candidate": candidate.name,
                "scores": scores,
                "shared_fingerprint_count": shared_count,
            })
        ranked.sort(key=lambda item: (
            -item["scores"]["shape"], -item["scores"]["semantic_heads"],
            -item["scores"]["type_premises"], -item["scores"]["proof_premises"],
            item["candidate"],
        ))
        query_count += 1
        for rank, item in enumerate(ranked[:max_candidates_per_query], 1):
            item = dict(item)
            item["rank"] = rank
            left, right = sorted((item["query"], item["candidate"]))
            key = (left, right)
            # Keep the stronger directed score if both query directions select
            # the same unordered pair; ties resolve by query name.
            old = pairs.get(key)
            if old is None or (
                tuple(-item["scores"][field] for field in ("shape", "semantic_heads", "type_premises", "proof_premises")),
                item["query"],
            ) < (
                tuple(-old["scores"][field] for field in ("shape", "semantic_heads", "type_premises", "proof_premises")),
                old["query"],
            ):
                item["left"], item["right"] = left, right
                pairs[key] = item
    selected = sorted(pairs.values(), key=lambda item: (item["left"], item["right"]))
    truncated = len(selected) > max_pairs
    selected = selected[:max_pairs]
    return selected, {
        "feature_schema_version": BASELINE_FEATURE_SCHEMA_VERSION,
        "query_partition": query_partition,
        "candidate_partition": candidate_partition,
        "usable_queries": len(queries),
        "usable_candidates": len(candidates),
        "unknown_queries": sum(
            item.partition == query_partition and payloads.get(item.name) is None
            for item in declarations
        ),
        "unknown_candidates": sum(
            item.partition == candidate_partition and payloads.get(item.name) is None
            for item in declarations
        ),
        "query_count": query_count,
        "candidate_pairs": len(selected),
        "status": "truncated" if truncated else "complete",
    }


@dataclass
class AntiUnifyState:
    next_meta: int = 0
    pair_metas: dict[tuple[str, str, str], str] = field(default_factory=dict)
    left_to_right: dict[tuple[str, str], str] = field(default_factory=dict)
    right_to_left: dict[tuple[str, str], str] = field(default_factory=dict)
    metas: dict[str, dict[str, Any]] = field(default_factory=dict)
    left_fvar_contracts: dict[str, dict[str, Any]] = field(default_factory=dict)
    right_fvar_contracts: dict[str, dict[str, Any]] = field(default_factory=dict)

    def meta(
        self,
        left: Node,
        right: Node,
        role: str,
        *,
        type_status: str = "unknown",
        type_contract: dict[str, Any] | None = None,
    ) -> Node:
        left_key, right_key = _node_key(left), _node_key(right)
        # A free variable is one logical parameter even when it appears in
        # different syntactic positions.  In particular, the same fvar can
        # be the function of an inner application and an argument of its
        # parent.  Including ``role`` in that key would split one repeated
        # variable into two metas and let K(x x) / K(u u) match K(x u).
        # Constants and other atoms retain their role-sensitive keys.
        pair_role = "fvar" if left[0] == right[0] == "fvar" else role
        pair_key = (left_key, right_key, pair_role)
        existing = self.pair_metas.get(pair_key)
        if existing is not None:
            prior_role = self.metas.get(existing, {}).get("role", role)
            return ("meta", existing, prior_role)
        if left[0] in {"fvar", "const", "lit", "sort"} and right[0] == left[0]:
            atom_role = "fvar" if left[0] == "fvar" else role
            left_atom = (atom_role, left_key)
            right_atom = (atom_role, _node_key(right))
            prior_right = self.left_to_right.get(left_atom)
            prior_left = self.right_to_left.get(right_atom)
            if prior_right is not None and prior_right != right_atom[1]:
                raise DiscoveryError("repeated_variable_constraint_conflict")
            if prior_left is not None and prior_left != left_atom[1]:
                raise DiscoveryError("repeated_variable_constraint_conflict")
            self.left_to_right[left_atom] = right_atom[1]
            self.right_to_left[right_atom] = left_atom[1]
        meta_id = f"m{self.next_meta}"
        self.next_meta += 1
        self.pair_metas[pair_key] = meta_id
        self.metas[meta_id] = {
            "id": meta_id,
            "role": role,
            "left": _node_json(left),
            "right": _node_json(right),
            "type_status": type_status,
            "type_contract": type_contract,
        }
        return ("meta", meta_id, role)


def _anti_node(
    left: Node,
    right: Node,
    state: AntiUnifyState,
    role: str,
    *,
    generalize_fvars: bool = False,
) -> Node:
    if left[0] != right[0]:
        raise DiscoveryError("incompatible_node_kinds")
    tag = left[0]
    if tag in {"const", "fvar", "lit", "sort"}:
        if left == right and not (tag == "fvar" and generalize_fvars):
            return left
        if tag == "fvar":
            left_contract = state.left_fvar_contracts.get(left[1])
            right_contract = state.right_fvar_contracts.get(right[1])
            if left_contract is not None and left_contract == right_contract:
                return state.meta(
                    left, right, role, type_status="checked", type_contract=left_contract
                )
        return state.meta(left, right, role)
    if tag == "app":
        if len(left[2]) != len(right[2]):
            raise DiscoveryError("application_arity_mismatch")
        fn = _anti_node(
            left[1], right[1], state, "function",
            generalize_fvars=generalize_fvars,
        )
        args = []
        for (left_explicit, left_arg), (right_explicit, right_arg) in zip(left[2], right[2]):
            if left_explicit != right_explicit:
                raise DiscoveryError("explicit_argument_mismatch")
            args.append((left_explicit, _anti_node(
                left_arg, right_arg, state, role,
                generalize_fvars=generalize_fvars,
            )))
        return ("app", fn, tuple(args))
    if tag in {"forall", "lam"}:
        if left[1] != right[1]:
            raise DiscoveryError("binder_info_mismatch")
        # Binder types are checked exactly up to alpha-normalized local refs;
        # widening a domain type would make the occurrence evidence unsafe.
        if _type_skeleton(left[2]) != _type_skeleton(right[2]):
            raise DiscoveryError("binder_type_mismatch")
        body = _anti_node(
            left[3], right[3], state, role,
            generalize_fvars=generalize_fvars,
        )
        return (tag, left[1], left[2], body)
    if tag == "proj":
        if left[1] != right[1]:
            raise DiscoveryError("projection_index_mismatch")
        return ("proj", left[1], _anti_node(
            left[2], right[2], state, role,
            generalize_fvars=generalize_fvars,
        ))
    if tag == "let":
        if _type_skeleton(left[1]) != _type_skeleton(right[1]):
            raise DiscoveryError("let_type_mismatch")
        return (
            "let", left[1], _anti_node(
                left[2], right[2], state, role,
                generalize_fvars=generalize_fvars,
            ),
            _anti_node(
                left[3], right[3], state, role,
                generalize_fvars=generalize_fvars,
            ),
        )
    raise DiscoveryError(f"unsupported_anti_unification_node:{tag}")


def _pattern_anchors(node: Node) -> int:
    tag = node[0]
    if tag == "const":
        return 1
    if tag in {"fvar", "lit", "sort", "meta"}:
        return 0
    if tag == "app":
        return _pattern_anchors(node[1]) + sum(_pattern_anchors(value) for _e, value in node[2])
    if tag in {"forall", "lam"}:
        return _pattern_anchors(node[2]) + _pattern_anchors(node[3])
    if tag == "proj":
        return _pattern_anchors(node[2])
    if tag == "let":
        return sum(_pattern_anchors(value) for value in node[1:])
    return 0


def _anti_signature(left: SignatureIR, right: SignatureIR, limits: dict[str, int]) -> tuple[dict[str, Any], AntiUnifyState]:
    if len(left.binders) != len(right.binders):
        raise DiscoveryError("binder_count_mismatch")
    state = AntiUnifyState()
    state.left_fvar_contracts.update(left.fvar_contracts())
    state.right_fvar_contracts.update(right.fvar_contracts())
    binders = []
    for index, ((left_info, left_type, left_raw), (right_info, right_type, right_raw)) in enumerate(
        zip(left.binders, right.binders)
    ):
        if left_info != right_info:
            raise DiscoveryError("binder_info_mismatch")
        type_match = _binder_type_match(
            left_raw, left_type, right_raw, right_type,
            left.binder_type_evidence(index), right.binder_type_evidence(index),
        )
        if type_match is None:
            raise DiscoveryError("binder_type_mismatch")
        binders.append({
            "binderInfo": left_info,
            "type": _node_json(left_type),
            "type_match": type_match,
        })
    conclusion = _anti_node(left.conclusion, right.conclusion, state, "conclusion")
    if _node_size(conclusion) + sum(_node_size(left_type) for _info, left_type, _ in left.binders) > limits["max_pattern_nodes"]:
        raise DiscoveryError("pattern_budget_exhausted")
    if len(state.metas) > limits["max_metavariables"]:
        raise DiscoveryError("metavariable_budget_exhausted")
    type_status = "checked" if all(
        meta.get("type_status") == "checked" for meta in state.metas.values()
    ) else "unknown"
    pattern = {
        "binders": binders,
        "conclusion": _node_json(conclusion),
        "metavariables": [state.metas[key] for key in sorted(state.metas)],
        "node_count": _node_size(conclusion) + sum(_node_size(left_type) for _info, left_type, _ in left.binders),
        "anchor_count": _pattern_anchors(conclusion),
        "metavariable_count": len(state.metas),
        "typed_metavariable_count": sum(
            meta.get("type_status") == "checked" for meta in state.metas.values()
        ),
        "type_status": type_status,
    }
    return pattern, state


def _anti_fragment(
    left: Node,
    right: Node,
    left_contracts: dict[str, dict[str, Any]],
    right_contracts: dict[str, dict[str, Any]],
    limits: dict[str, int],
) -> tuple[dict[str, Any], AntiUnifyState]:
    """Anti-unify conclusion subtrees with every free variable parameterized.

    Whole-declaration binder lists are intentionally not required here.  The
    selected subtree carries exact top-binder type contracts in each source
    declaration; every referenced top fvar becomes a checked metavariable
    only when those contracts agree.  Local binders and unknown domains remain
    untyped and cannot pass acceptance.
    """
    state = AntiUnifyState(
        left_fvar_contracts=left_contracts,
        right_fvar_contracts=right_contracts,
    )
    pattern_node = _anti_node(
        left, right, state, "fragment",
        generalize_fvars=True,
    )
    if _node_size(pattern_node) > limits["max_pattern_nodes"]:
        raise DiscoveryError("pattern_budget_exhausted")
    if len(state.metas) > limits["max_metavariables"]:
        raise DiscoveryError("metavariable_budget_exhausted")
    type_status = "checked" if all(
        meta.get("type_status") == "checked" for meta in state.metas.values()
    ) else "unknown"
    return {
        "scope": "conclusion_fragment",
        "root": "conclusion",
        "binders": [],
        "conclusion": _node_json(pattern_node),
        "metavariables": [state.metas[key] for key in sorted(state.metas)],
        "node_count": _node_size(pattern_node),
        "anchor_count": _pattern_anchors(pattern_node),
        "metavariable_count": len(state.metas),
        "typed_metavariable_count": sum(
            meta.get("type_status") == "checked" for meta in state.metas.values()
        ),
        "type_status": type_status,
    }, state


def _fragment_candidates(
    signature: SignatureIR,
    limits: dict[str, int],
) -> list[tuple[tuple[str, ...], Node]]:
    candidates = [
        (path, node)
        for path, node in _iter_subnodes(signature.conclusion)
        if node[0] == "app"
        and _pattern_anchors(node) >= 1
        and _node_size(node) <= limits["max_pattern_nodes"]
    ]
    candidates.sort(key=lambda item: (_node_size(item[1]), item[0], _node_key(item[1])))
    return candidates[:limits["max_fragment_candidates"]]


def _node_from_json(raw: Any) -> Node:
    """Parse the module's own pattern JSON for second-pass matching."""
    if not isinstance(raw, dict) or not isinstance(raw.get("node"), str):
        raise DiscoveryError("malformed_pattern_node")
    tag = raw["node"]
    if tag == "const":
        return ("const", raw.get("name"))
    if tag == "binder":
        return ("fvar", raw.get("index"))
    if tag == "lit":
        return ("lit", raw.get("kind"), raw.get("value"))
    if tag == "sort":
        return ("sort", raw.get("level"))
    if tag == "meta":
        return ("meta", raw.get("id"), raw.get("role", "term"))
    if tag == "technique_ref":
        return ("technique_ref", raw.get("id"))
    if tag == "app":
        args = raw.get("args")
        if not isinstance(args, list):
            raise DiscoveryError("malformed_pattern_app")
        return ("app", _node_from_json(raw.get("fn")), tuple(
            (bool(arg.get("explicit", True)), _node_from_json(arg.get("value")))
            for arg in args if isinstance(arg, dict)
        ))
    if tag in {"forall", "lam"}:
        return (tag, raw.get("binderInfo", "default"),
                _node_from_json(raw.get("binderType")), _node_from_json(raw.get("body")))
    if tag == "proj":
        return ("proj", raw.get("idx"), _node_from_json(raw.get("struct")))
    if tag == "let":
        return ("let", _node_from_json(raw.get("binderType")),
                _node_from_json(raw.get("value")), _node_from_json(raw.get("body")))
    raise DiscoveryError(f"unsupported_pattern_node:{tag}")


def _match_node(
    pattern: Node,
    target: Node,
    substitutions: dict[str, Node],
    *,
    target_contracts: dict[str, dict[str, Any]] | None = None,
    meta_contracts: dict[str, dict[str, Any]] | None = None,
) -> bool:
    target_contracts = target_contracts or {}
    meta_contracts = meta_contracts or {}
    if pattern[0] == "meta":
        key = pattern[1]
        contract = meta_contracts.get(key, {})
        if contract.get("type_status") == "checked":
            if target[0] != "fvar" or target_contracts.get(target[1]) != contract.get("type_contract"):
                return False
        prior = substitutions.get(key)
        if prior is None:
            substitutions[key] = target
            return True
        return prior == target
    if pattern[0] != target[0]:
        return False
    tag = pattern[0]
    if tag in {"const", "fvar", "lit", "sort"}:
        return pattern == target
    if tag == "app":
        if len(pattern[2]) != len(target[2]) or not _match_node(
            pattern[1], target[1], substitutions,
            target_contracts=target_contracts, meta_contracts=meta_contracts,
        ):
            return False
        return all(
            pattern_arg[0] == target_arg[0] and _match_node(
                pattern_arg[1], target_arg[1], substitutions,
                target_contracts=target_contracts, meta_contracts=meta_contracts,
            )
            for pattern_arg, target_arg in zip(pattern[2], target[2])
        )
    if tag in {"forall", "lam"}:
        return (
            pattern[1] == target[1]
            and _type_skeleton(pattern[2]) == _type_skeleton(target[2])
            and _match_node(pattern[3], target[3], substitutions,
                            target_contracts=target_contracts, meta_contracts=meta_contracts)
        )
    if tag == "proj":
        return pattern[1] == target[1] and _match_node(
            pattern[2], target[2], substitutions,
            target_contracts=target_contracts, meta_contracts=meta_contracts,
        )
    if tag == "let":
        return (
            _type_skeleton(pattern[1]) == _type_skeleton(target[1])
            and _match_node(pattern[2], target[2], substitutions,
                            target_contracts=target_contracts, meta_contracts=meta_contracts)
            and _match_node(pattern[3], target[3], substitutions,
                            target_contracts=target_contracts, meta_contracts=meta_contracts)
        )
    return False


def _match_pattern_occurrences(
    pattern: dict[str, Any],
    target: SignatureIR,
) -> tuple[list[tuple[dict[str, Any], tuple[str, ...] | None]], str | None]:
    """Return all deterministic target locations for a pattern."""
    binders = pattern.get("binders")
    is_fragment = pattern.get("scope") == "conclusion_fragment"
    if not is_fragment and (not isinstance(binders, list) or len(binders) != len(target.binders)):
        return [], "binder_count_mismatch"
    target_contracts = target.fvar_contracts()
    meta_contracts = {
        item["id"]: item for item in pattern.get("metavariables", [])
        if isinstance(item, dict) and isinstance(item.get("id"), str)
    }
    if not is_fragment:
        for index, (pattern_binder, (target_info, target_type, target_raw)) in enumerate(
            zip(binders, target.binders)
        ):
            if pattern_binder.get("binderInfo") != target_info:
                return [], "binder_info_mismatch"
            type_match = pattern_binder.get("type_match")
            if not isinstance(type_match, dict):
                return [], "missing_binder_type_contract"
            if type_match.get("kind") == "exact":
                if type_match.get("skeleton") != _canonical_json(_type_skeleton(target_type)):
                    return [], "binder_type_mismatch"
            elif type_match.get("kind") == "hypothesis_role":
                if not _binder_role(
                    target_raw, target_type, target.binder_type_evidence(index)
                ).startswith("hypothesis_"):
                    return [], "hypothesis_role_mismatch"
            else:
                return [], "unknown_binder_type_contract"
    try:
        conclusion = _node_from_json(pattern["conclusion"])
        target_nodes = (
            _iter_subnodes(target.conclusion) if is_fragment
            else iter((((), target.conclusion),))
        )
        matches = []
        for path, target_node in target_nodes:
            substitutions: dict[str, Node] = {}
            if _match_node(
                conclusion, target_node, substitutions,
                target_contracts=target_contracts, meta_contracts=meta_contracts,
            ):
                matches.append(({
                    key: {"node": _node_json(value), "size": _node_size(value)}
                    for key, value in sorted(substitutions.items())
                }, path if is_fragment else None))
        if not matches:
            return [], "pattern_shape_mismatch"
        return matches, None
    except DiscoveryError as error:
        return [], str(error)


def match_pattern(pattern: dict[str, Any], target: SignatureIR) -> tuple[bool, dict[str, Any], str | None]:
    """Match one accepted pattern against one signature with typed scope checks."""
    matches, reason = _match_pattern_occurrences(pattern, target)
    if not matches:
        return False, {}, reason
    bindings, path = matches[0]
    if path is not None:
        bindings = {"target_path": list(path), "bindings": bindings}
    return True, bindings, None


def _source_occurrence(
    declaration: LoadedDeclaration,
    *,
    match: dict[str, Any] | None = None,
    target_path: tuple[str, ...] | None = None,
) -> dict[str, Any]:
    return {
        "declaration": declaration.name,
        "family": declaration.family,
        "partition": declaration.partition,
        "signature_sha256": declaration.signature_sha256,
        "source": declaration.source,
        "evidence": declaration.evidence,
        "target_evidence": {
            "status": "exact_capture_fields",
            "capture_declaration": declaration.name,
            "signature": declaration.record.get("signature"),
            "binders": declaration.record.get("binders"),
            "conclusion": declaration.record.get("conclusion"),
            "conclusion_tree": declaration.record.get("conclusion_tree"),
            "signature_sha256": declaration.signature_sha256,
        },
        **({"bindings": match} if match is not None else {}),
        **({"target_path": list(target_path)} if target_path is not None else {}),
    }


def _proposal_id(pattern: dict[str, Any]) -> str:
    return "technique:" + _sha256_json(pattern)[:24]


def _build_proposals(
    declarations: list[LoadedDeclaration],
    pairs: list[dict[str, Any]],
    limits: dict[str, int],
) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    by_name = {declaration.name: declaration for declaration in declarations}
    grouped: dict[str, dict[str, Any]] = {}
    rejected: Counter[str] = Counter()
    for pair in pairs:
        left, right = by_name[pair["left"]], by_name[pair["right"]]
        if left.partition != "train" or right.partition != "train":
            continue
        try:
            pattern, _state = _anti_signature(left.ir, right.ir, limits)  # type: ignore[arg-type]
            if pattern["anchor_count"] < limits["min_anchors"]:
                raise DiscoveryError("insufficient_exact_anchors")
        except DiscoveryError as error:
            rejected[str(error)] += 1
            continue
        key = _sha256_json(pattern)
        item = grouped.setdefault(key, {
            "id": _proposal_id(pattern),
            "pattern": pattern,
            "training_pairs": [],
            "candidate_scores": [],
        })
        item["training_pairs"].append([left.name, right.name])
        item["candidate_scores"].append({
            "left": left.name, "right": right.name,
            "rank": pair["rank"], "scores": pair["scores"],
        })
    proposals = []
    for key in sorted(grouped):
        item = grouped[key]
        support_names = sorted({name for pair in item["training_pairs"] for name in pair})
        support_families = sorted({by_name[name].family for name in support_names})
        pattern = item["pattern"]
        accepted = (
            len(support_names) >= limits["min_support"]
            and len(support_families) >= limits["min_families"]
            and pattern["anchor_count"] >= limits["min_anchors"]
            and pattern["node_count"] <= limits["max_pattern_nodes"]
            and pattern["metavariable_count"] >= limits["min_metavariables"]
            and pattern["type_status"] == "checked"
        )
        status = "accepted_by_structural_rule" if accepted else "proposed_structural_only"
        item["training_support"] = support_names
        item["training_families"] = support_families
        item["support_count"] = len(support_names)
        item["family_count"] = len(support_families)
        item["acceptance_status"] = status
        item["acceptance_reasons"] = [] if accepted else [
            reason for reason, condition in (
                ("insufficient_support", len(support_names) < limits["min_support"]),
                ("insufficient_families", len(support_families) < limits["min_families"]),
                ("insufficient_anchors", pattern["anchor_count"] < limits["min_anchors"]),
                ("insufficient_metavariables", pattern["metavariable_count"] < limits["min_metavariables"]),
                ("untyped_metavariable", pattern["type_status"] != "checked"),
                ("pattern_budget", pattern["node_count"] > limits["max_pattern_nodes"]),
            ) if condition
        ]
        item["evidence_status"] = "capture_tree_backed"
        item["interpretation_status"] = "not_reviewed"
        item["warning"] = (
            "repeated structure only; no mathematical meaning, theorem equivalence, "
            "or proof-reuse claim has been verified"
        )
        proposals.append(item)
    fragment_proposals, fragment_summary = _build_fragment_proposals(
        declarations, pairs, limits
    )
    proposals.extend(fragment_proposals)
    proposals.sort(key=lambda item: item["id"])
    accepted = [item for item in proposals if item["acceptance_status"] == "accepted_by_structural_rule"]
    combined_rejected = Counter(rejected)
    combined_rejected.update(fragment_summary["rejected_pair_reasons"])
    return proposals, {
        "proposal_count": len(proposals),
        "accepted_count": len(accepted),
        "full_signature_proposal_count": len(proposals) - len(fragment_proposals),
        "fragment_proposal_count": len(fragment_proposals),
        "rejected_pair_reasons": dict(sorted(combined_rejected.items())),
        "fragment_rejected_pair_reasons": fragment_summary["rejected_pair_reasons"],
        "status": "complete",
    }


def _build_fragment_proposals(
    declarations: list[LoadedDeclaration],
    pairs: list[dict[str, Any]],
    limits: dict[str, int],
) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    """Mine bounded conclusion fragments when declarations have unlike wrappers."""
    by_name = {declaration.name: declaration for declaration in declarations}
    grouped: dict[str, dict[str, Any]] = {}
    rejected: Counter[str] = Counter()
    for pair in pairs:
        left, right = by_name[pair["left"]], by_name[pair["right"]]
        if not left.usable or not right.usable:
            continue
        left_nodes = _fragment_candidates(left.ir, limits)  # type: ignore[arg-type]
        right_nodes = _fragment_candidates(right.ir, limits)  # type: ignore[arg-type]
        attempts = 0
        for left_path, left_node in left_nodes:
            for right_path, right_node in right_nodes:
                if left_node[0] != right_node[0]:
                    continue
                if left_node[0] == "app" and len(left_node[2]) != len(right_node[2]):
                    continue
                attempts += 1
                if attempts > limits["max_fragment_pairs"]:
                    break
                try:
                    pattern, _state = _anti_fragment(
                        left_node, right_node,
                        left.ir.fvar_contracts(), right.ir.fvar_contracts(), limits,  # type: ignore[union-attr]
                    )
                    if pattern["anchor_count"] < limits["min_anchors"]:
                        raise DiscoveryError("insufficient_exact_anchors")
                except DiscoveryError as error:
                    rejected["fragment_" + str(error)] += 1
                    continue
                key = _sha256_json(pattern)
                item = grouped.setdefault(key, {
                    "id": _proposal_id(pattern),
                    "kind": "fragment_structural_candidate",
                    "pattern": pattern,
                    "training_pairs": [],
                    "training_fragments": [],
                    "candidate_scores": [],
                })
                item["training_pairs"].append([left.name, right.name])
                item["training_fragments"].append({
                    "left": {"declaration": left.name, "path": list(left_path)},
                    "right": {"declaration": right.name, "path": list(right_path)},
                })
                item["candidate_scores"].append({
                    "left": left.name, "right": right.name,
                    "left_path": list(left_path), "right_path": list(right_path),
                    "rank": pair["rank"], "scores": pair["scores"],
                })
            if attempts > limits["max_fragment_pairs"]:
                break
    proposals: list[dict[str, Any]] = []
    for key in sorted(grouped):
        item = grouped[key]
        support_names = sorted({name for pair in item["training_pairs"] for name in pair})
        support_families = sorted({by_name[name].family for name in support_names})
        pattern = item["pattern"]
        accepted = (
            len(support_names) >= limits["min_support"]
            and len(support_families) >= limits["min_families"]
            and pattern["anchor_count"] >= limits["min_anchors"]
            and pattern["node_count"] <= limits["max_pattern_nodes"]
            and pattern["metavariable_count"] >= limits["min_metavariables"]
            and pattern["type_status"] == "checked"
        )
        item["training_support"] = support_names
        item["training_families"] = support_families
        item["support_count"] = len(support_names)
        item["family_count"] = len(support_families)
        item["acceptance_status"] = (
            "accepted_by_structural_rule" if accepted else "proposed_structural_only"
        )
        item["acceptance_reasons"] = [] if accepted else [
            reason for reason, condition in (
                ("insufficient_support", len(support_names) < limits["min_support"]),
                ("insufficient_families", len(support_families) < limits["min_families"]),
                ("insufficient_anchors", pattern["anchor_count"] < limits["min_anchors"]),
                ("insufficient_metavariables", pattern["metavariable_count"] < limits["min_metavariables"]),
                ("untyped_metavariable", pattern["type_status"] != "checked"),
                ("pattern_budget", pattern["node_count"] > limits["max_pattern_nodes"]),
            ) if condition
        ]
        item["evidence_status"] = "capture_tree_backed"
        item["interpretation_status"] = "not_reviewed"
        item["warning"] = (
            "repeated conclusion fragment only; no mathematical meaning, theorem equivalence, "
            "or proof-reuse claim has been verified"
        )
        proposals.append(item)
    return proposals, {
        "rejected_pair_reasons": dict(sorted(rejected.items())),
        "status": "complete",
    }


def _occurrences(
    declarations: list[LoadedDeclaration], accepted: list[dict[str, Any]]
) -> tuple[list[dict[str, Any]], dict[str, list[str]]]:
    occurrences = []
    vocabulary_by_declaration: dict[str, list[str]] = defaultdict(list)
    for proposal in sorted(accepted, key=lambda item: item["id"]):
        for declaration in sorted(declarations, key=lambda item: item.name):
            if not declaration.usable:
                continue
            matches, _reason = _match_pattern_occurrences(proposal["pattern"], declaration.ir)
            if not matches:
                continue
            for bindings, path in matches:
                occurrence = {
                    "abstraction_id": proposal["id"],
                    "match_status": "structural_match",
                    "occurrence": _source_occurrence(
                        declaration, match=bindings, target_path=path
                    ),
                }
                occurrences.append(occurrence)
                # Held-out matches are reported for evaluation but never become
                # vocabulary tokens.  This is the central no-leakage boundary
                # between pass one fitting and pass two retrieval.
                if declaration.partition == "train":
                    vocabulary_by_declaration[declaration.name].append(proposal["id"])
    occurrences.sort(key=lambda item: (item["abstraction_id"], item["occurrence"]["declaration"]))
    for name in vocabulary_by_declaration:
        vocabulary_by_declaration[name].sort()
    return occurrences, dict(sorted(vocabulary_by_declaration.items()))


def _node_children(node: Node) -> list[tuple[tuple[str, ...], Node]]:
    tag = node[0]
    if tag == "app":
        return [(('fn',), node[1])] + [
            (("arg", str(index)), value) for index, (_explicit, value) in enumerate(node[2])
        ]
    if tag in {"forall", "lam"}:
        return [(('binderType',), node[2]), (('body',), node[3])]
    if tag == "proj":
        return [(('struct',), node[2])]
    if tag == "let":
        return [
            (('binderType',), node[1]),
            (('value',), node[2]),
            (('body',), node[3]),
        ]
    return []


def _iter_subnodes(node: Node, path: tuple[str, ...] = ()) -> Iterator[tuple[tuple[str, ...], Node]]:
    yield path, node
    for child_path, child in _node_children(node):
        yield from _iter_subnodes(child, path + child_path)


def _contains_meta(node: Node) -> bool:
    if node[0] == "meta":
        return True
    return any(_contains_meta(child) for _path, child in _node_children(node))


def _meta_ids(node: Node) -> set[str]:
    if node[0] == "meta":
        return {node[1]}
    return {item for _path, child in _node_children(node) for item in _meta_ids(child)}


def _component_node(node: Node) -> Node:
    """Normalize proposal-local metavariable roles for component deduplication."""
    if node[0] == "meta":
        return ("meta", node[1], "component")
    if node[0] == "app":
        return (
            "app", _component_node(node[1]),
            tuple((explicit, _component_node(value)) for explicit, value in node[2]),
        )
    if node[0] in {"forall", "lam"}:
        return (node[0], node[1], _component_node(node[2]), _component_node(node[3]))
    if node[0] == "proj":
        return ("proj", node[1], _component_node(node[2]))
    if node[0] == "let":
        return ("let", *(_component_node(value) for value in node[1:]))
    return node


def _component_candidates(accepted: list[dict[str, Any]]) -> list[dict[str, Any]]:
    """Turn accepted parameterized patterns into structured second-pass nodes."""
    grouped: dict[str, dict[str, Any]] = {}
    for proposal in sorted(accepted, key=lambda item: item["id"]):
        root = _node_from_json(proposal["pattern"]["conclusion"])
        meta_defs = {
            item["id"]: item for item in proposal["pattern"].get("metavariables", [])
            if isinstance(item, dict) and isinstance(item.get("id"), str)
        }
        for _path, node in _iter_subnodes(root):
            if node[0] != "app" or not _contains_meta(node) or _pattern_anchors(node) < 1:
                continue
            # Keep the smallest anchored parameterized subtrees.  A parent
            # subtree containing another parameterized child is the composed
            # view, not a first-pass component.
            if any(
                child[0] != "meta" and _contains_meta(child)
                for _child_path, child in _node_children(node)
            ):
                continue
            component_node = _component_node(node)
            node_json = _node_json(component_node)
            key = _sha256_json(node_json)
            item = grouped.setdefault(key, {
                "id": "component:" + key[:24],
                "kind": "accepted_structural_component",
                "pattern": node_json,
                "metavariables": [
                    {
                        **meta_defs[meta_id],
                        "role": "component",
                    }
                    for meta_id in sorted(_meta_ids(component_node))
                    if meta_id in meta_defs
                ],
                "parent_proposal_ids": [],
                "evidence_status": "derived_from_accepted_occurrences",
                "interpretation_status": "not_reviewed",
            })
            if proposal["id"] not in item["parent_proposal_ids"]:
                item["parent_proposal_ids"].append(proposal["id"])
    for item in grouped.values():
        item["parent_proposal_ids"].sort()
        item["meta_aliases"] = {
            meta["id"]: meta["id"] for meta in item["metavariables"]
        }
    return [grouped[key] for key in sorted(grouped)]


def _component_occurrences(
    declarations: list[LoadedDeclaration],
    components: list[dict[str, Any]],
    limits: dict[str, int],
    *,
    partitions: set[str] | None = None,
) -> tuple[list[dict[str, Any]], dict[tuple[str, str], list[dict[str, Any]]]]:
    """Match components in a bounded, explicitly selected partition set."""
    all_occurrences: list[dict[str, Any]] = []
    by_declaration_component: dict[tuple[str, str], list[dict[str, Any]]] = defaultdict(list)
    for component in sorted(components, key=lambda item: item["id"]):
        pattern = _node_from_json(component["pattern"])
        meta_contracts = {
            item["id"]: item for item in component.get("metavariables", [])
            if isinstance(item, dict) and isinstance(item.get("id"), str)
        }
        for declaration in sorted(declarations, key=lambda item: item.name):
            if partitions is not None and declaration.partition not in partitions:
                continue
            if not declaration.usable:
                continue
            count = 0
            for path, target in _iter_subnodes(declaration.ir.conclusion):
                bindings: dict[str, Node] = {}
                if not _match_node(
                    pattern, target, bindings,
                    target_contracts=declaration.ir.fvar_contracts(),
                    meta_contracts=meta_contracts,
                ):
                    continue
                occurrence = {
                    "component_id": component["id"],
                    "declaration": declaration.name,
                    "family": declaration.family,
                    "partition": declaration.partition,
                    "path": list(path),
                    "bindings": {
                        key: {"node": _node_json(value), "size": _node_size(value)}
                        for key, value in sorted(bindings.items())
                    },
                    "source": declaration.source,
                    "signature_sha256": declaration.signature_sha256,
                    "target_evidence": {
                        "status": "exact_capture_fields",
                        "capture_declaration": declaration.name,
                        "signature": declaration.record.get("signature"),
                        "binders": declaration.record.get("binders"),
                        "conclusion": declaration.record.get("conclusion"),
                        "conclusion_tree": declaration.record.get("conclusion_tree"),
                        "signature_sha256": declaration.signature_sha256,
                    },
                }
                by_declaration_component[(declaration.name, component["id"])].append(occurrence)
                all_occurrences.append(occurrence)
                count += 1
                if count >= limits["max_component_occurrences"]:
                    break
    all_occurrences.sort(key=lambda item: (
        item["component_id"], item["declaration"], item["path"]
    ))
    return all_occurrences, by_declaration_component


def _replace_paths(node: Node, replacements: dict[tuple[str, ...], Node], path: tuple[str, ...] = ()) -> Node:
    replacement = replacements.get(path)
    if replacement is not None:
        return replacement
    tag = node[0]
    if tag == "app":
        return (
            "app",
            _replace_paths(node[1], replacements, path + ("fn",)),
            tuple(
                (explicit, _replace_paths(value, replacements, path + ("arg", str(index))))
                for index, (explicit, value) in enumerate(node[2])
            ),
        )
    if tag in {"forall", "lam"}:
        return (
            tag, node[1],
            _replace_paths(node[2], replacements, path + ("binderType",)),
            _replace_paths(node[3], replacements, path + ("body",)),
        )
    if tag == "proj":
        return ("proj", node[1], _replace_paths(node[2], replacements, path + ("struct",)))
    if tag == "let":
        return (
            "let",
            _replace_paths(node[1], replacements, path + ("binderType",)),
            _replace_paths(node[2], replacements, path + ("value",)),
            _replace_paths(node[3], replacements, path + ("body",)),
        )
    return node


def _path_overlap(left: tuple[str, ...], right: tuple[str, ...]) -> bool:
    return left == right or left[:len(right)] == right or right[:len(left)] == left


def _composition_roots(
    declaration: LoadedDeclaration,
    limits: dict[str, int],
) -> list[tuple[tuple[str, ...], Node]]:
    roots = [
        (path, node)
        for path, node in _iter_subnodes(declaration.ir.conclusion)
        if node[0] == "app"
        and _pattern_anchors(node) >= 1
        and _node_size(node) <= limits["max_pattern_nodes"]
    ]
    roots.sort(key=lambda item: (-_node_size(item[1]), item[0], _node_key(item[1])))
    return roots[:limits["max_fragment_candidates"]]


def _composition_rows_for_declaration(
    declaration: LoadedDeclaration,
    components: list[dict[str, Any]],
    by_declaration_component: dict[tuple[str, str], list[dict[str, Any]]],
    limits: dict[str, int],
    *,
    required_component_prefix: str | None = None,
) -> list[dict[str, Any]]:
    ordered_components = sorted(components, key=lambda item: item["id"])
    if len(ordered_components) < 2:
        return []
    rows = []
    count = 0
    for root_path, root_node in _composition_roots(declaration, limits):
        choices = []
        for component in ordered_components:
            scoped = []
            for occurrence in by_declaration_component.get((declaration.name, component["id"]), []):
                occurrence_path = tuple(occurrence["path"])
                if occurrence_path[:len(root_path)] != root_path:
                    continue
                item = dict(occurrence)
                item["relative_path"] = list(occurrence_path[len(root_path):])
                scoped.append(item)
            choices.append(scoped)
        if any(not choice for choice in choices):
            continue
        for selected in product(*choices):
            if required_component_prefix is not None and not any(
                item["component_id"].startswith(required_component_prefix)
                for item in selected
            ):
                continue
            paths = [tuple(item["relative_path"]) for item in selected]
            if any(_path_overlap(left, right) for index, left in enumerate(paths)
                   for right in paths[index + 1:]):
                continue
            parent_bindings: dict[str, str] = {}
            relation_slots: dict[str, str] = {}
            next_slot = 0
            consistent = True
            for component, occurrence in zip(ordered_components, selected):
                for local_id, binding in occurrence.get("bindings", {}).items():
                    parent_id = component.get("meta_aliases", {}).get(local_id, local_id)
                    binding_key = _canonical_json(binding["node"])
                    prior = parent_bindings.get(parent_id)
                    if prior is not None and prior != binding_key:
                        consistent = False
                        break
                    parent_bindings[parent_id] = binding_key
                    if binding_key not in relation_slots:
                        relation_slots[binding_key] = f"b{next_slot}"
                        next_slot += 1
                if not consistent:
                    break
            if not consistent:
                continue
            replacements = {
                tuple(item["relative_path"]): ("technique_ref", component["id"])
                for component, item in zip(ordered_components, selected)
            }
            skeleton = _node_json(_replace_paths(root_node, replacements))
            relation = [
                [parent_id, relation_slots[binding_key]]
                for parent_id, binding_key in sorted(parent_bindings.items())
            ]
            key_payload = {
                "components": [component["id"] for component in ordered_components],
                "skeleton": skeleton,
                "binding_relation": relation,
            }
            rows.append({
                "key": _sha256_json(key_payload),
                "declaration": declaration.name,
                "family": declaration.family,
                "partition": declaration.partition,
                "root_path": list(root_path),
                "components": [component["id"] for component in ordered_components],
                "skeleton": skeleton,
                "binding_relation": relation,
                "source": declaration.source,
                "signature_sha256": declaration.signature_sha256,
                "target_evidence": {
                    "status": "exact_capture_fields",
                    "capture_declaration": declaration.name,
                    "signature": declaration.record.get("signature"),
                    "binders": declaration.record.get("binders"),
                    "conclusion": declaration.record.get("conclusion"),
                    "conclusion_tree": declaration.record.get("conclusion_tree"),
                    "signature_sha256": declaration.signature_sha256,
                },
                "expansion_links": [
                    {
                        "component_id": component["id"],
                        "path": item["path"],
                        "relative_path": item["relative_path"],
                        "bindings": item.get("bindings", {}),
                        "source": item["source"],
                        "signature_sha256": item["signature_sha256"],
                        "target_evidence": item["target_evidence"],
                        **({"nested_expansion_links": item["nested_expansion_links"]}
                           if "nested_expansion_links" in item else {}),
                    }
                    for component, item in zip(ordered_components, selected)
                ],
            })
            count += 1
            if count >= limits["max_component_combinations"]:
                return rows
    return rows


def _expansion_reference_ids(links: Any) -> set[str]:
    """Collect composition IDs referenced by a finite expansion tree."""
    if not isinstance(links, list):
        return set()
    references: set[str] = set()
    for link in links:
        if not isinstance(link, dict):
            continue
        component_id = link.get("component_id")
        if isinstance(component_id, str) and component_id.startswith("feedback:"):
            references.add(component_id[len("feedback:"):])
        references.update(_expansion_reference_ids(link.get("nested_expansion_links")))
    return references


def _expansion_provenance_complete(links: Any) -> bool:
    """Require exact capture/source fields at every expansion leaf."""
    if not isinstance(links, list) or not links:
        return False
    for link in links:
        if not isinstance(link, dict):
            return False
        if not isinstance(link.get("component_id"), str):
            return False
        if not isinstance(link.get("source"), dict):
            return False
        target_evidence = link.get("target_evidence")
        if not isinstance(target_evidence, dict) or target_evidence.get("status") != "exact_capture_fields":
            return False
        if not isinstance(link.get("signature_sha256"), str) or not link["signature_sha256"]:
            return False
        nested = link.get("nested_expansion_links")
        if nested is not None and not _expansion_provenance_complete(nested):
            return False
    return True


def _feedback_components(
    compositions: list[dict[str, Any]],
    occurrences: list[dict[str, Any]],
    declarations: list[LoadedDeclaration],
    round_number: int,
) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    """Expose only the prior round's accepted compositions as new components.

    Feedback occurrences are carried from accepted, source-anchored rows rather
    than rematched against raw trees.  That keeps the overlay expandable while
    preventing an accepted composition from becoming an ungrounded synthetic
    theorem node.  Since this function receives only the immediately preceding
    round, the resulting expansion graph is acyclic by construction.
    """
    declaration_by_name = {item.name: item for item in declarations}
    by_composition: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for occurrence in occurrences:
        composition_id = occurrence.get("composition_id")
        if isinstance(composition_id, str):
            by_composition[composition_id].append(occurrence)
    components: list[dict[str, Any]] = []
    component_occurrences: list[dict[str, Any]] = []
    for composition in sorted(compositions, key=lambda item: item["id"]):
        composition_id = composition["id"]
        feedback_id = "feedback:" + composition_id
        nested_ids = set(composition.get("input_composition_ids", []))
        nested_ids.add(composition_id)
        components.append({
            "id": feedback_id,
            "kind": "accepted_composition_feedback",
            "pattern": composition["skeleton"],
            "metavariables": [],
            "meta_aliases": {},
            "parent_composition_ids": sorted(nested_ids),
            "parent_components": list(composition.get("components", [])),
            "round": round_number,
            "evidence_status": "carried_from_accepted_composition_occurrences",
            "interpretation_status": "not_reviewed",
        })
        for occurrence in sorted(
            by_composition.get(composition_id, []),
            key=lambda item: (item.get("declaration", ""), item.get("root_path", [])),
        ):
            declaration = declaration_by_name.get(occurrence.get("declaration"))
            if declaration is None:
                continue
            links = occurrence.get("expansion_links")
            if not _expansion_provenance_complete(links):
                continue
            component_occurrences.append({
                "component_id": feedback_id,
                "declaration": declaration.name,
                "family": declaration.family,
                "partition": declaration.partition,
                "path": list(occurrence.get("root_path", [])),
                "bindings": {},
                "source": occurrence.get("source") or declaration.source,
                "signature_sha256": occurrence.get("signature_sha256") or declaration.signature_sha256,
                "target_evidence": occurrence.get("target_evidence") or {
                    "status": "exact_capture_fields",
                    "capture_declaration": declaration.name,
                    "signature": declaration.record.get("signature"),
                    "binders": declaration.record.get("binders"),
                    "conclusion": declaration.record.get("conclusion"),
                    "conclusion_tree": declaration.record.get("conclusion_tree"),
                    "signature_sha256": declaration.signature_sha256,
                },
                "nested_expansion_links": links,
                "expanded_from_composition_id": composition_id,
                "expansion_status": "complete",
            })
    components.sort(key=lambda item: item["id"])
    component_occurrences.sort(key=lambda item: (
        item["component_id"], item["declaration"], item["path"]
    ))
    return components, component_occurrences


def _composition_candidate_sets(
    atomic_components: list[dict[str, Any]],
    feedback_components: list[dict[str, Any]],
    limits: dict[str, int],
) -> list[list[dict[str, Any]]]:
    """Bound the component sets tried in one feedback round."""
    if not feedback_components:
        if len(atomic_components) < 2:
            return []
        # Enumerating bounded pairs is what makes a genuine second level
        # possible: round one can accept A+B while leaving C available for a
        # later frozen-feedback composition (A+B)+C.  This remains explicit
        # structural composition, never baseline-pair reranking.
        return [
            sorted(pair, key=lambda item: item["id"])
            for pair in list(combinations(
                sorted(atomic_components, key=lambda item: item["id"]), 2
            ))[:limits["max_component_combinations"]]
        ]
    candidates: list[list[dict[str, Any]]] = []
    for feedback in feedback_components:
        for atomic in atomic_components:
            if feedback["id"] == atomic["id"]:
                continue
            candidates.append(sorted([feedback, atomic], key=lambda item: item["id"]))
    for left, right in combinations(feedback_components, 2):
        candidates.append(sorted([left, right], key=lambda item: item["id"]))
    deduped: dict[tuple[str, ...], list[dict[str, Any]]] = {}
    for candidate in candidates:
        key = tuple(item["id"] for item in candidate)
        deduped.setdefault(key, candidate)
    return [deduped[key] for key in sorted(deduped)[:limits["max_component_combinations"]]]


def _group_composition_rows(
    rows: list[dict[str, Any]],
    limits: dict[str, int],
    *,
    round_number: int,
    allowed_composition_ids: set[str],
) -> tuple[list[dict[str, Any]], set[str], list[dict[str, Any]]]:
    grouped: dict[str, dict[str, Any]] = {}
    for row in rows:
        if row.get("partition") != "train":
            continue
        references = _expansion_reference_ids(row.get("expansion_links"))
        if not references.issubset(allowed_composition_ids):
            continue
        if not _expansion_provenance_complete(row.get("expansion_links")):
            continue
        item = grouped.setdefault(row["key"], {
            "id": "composition:" + row["key"][:24],
            "composition_key": row["key"],
            "kind": "composed_structural_candidate",
            "round": round_number,
            "components": row["components"],
            "input_component_ids": row["components"],
            "input_composition_ids": sorted(references),
            "skeleton": row["skeleton"],
            "binding_relation": row["binding_relation"],
            "training_support": [],
            "training_families": [],
            "expansion_links": [],
            "evidence_status": "expanded_from_source_anchored_occurrences",
            "expansion_status": "complete",
            "acyclic": True,
            "interpretation_status": "not_reviewed",
            "warning": "composed structural recurrence only; no mathematical meaning or theorem equivalence verified",
        })
        item["training_support"].append(row["declaration"])
        item["training_families"].append(row["family"])
        item["expansion_links"].append({
            "declaration": row["declaration"],
            "links": row["expansion_links"],
        })
    compositions: list[dict[str, Any]] = []
    accepted_ids: set[str] = set()
    for key in sorted(grouped):
        item = grouped[key]
        item["training_support"] = sorted(set(item["training_support"]))
        item["training_families"] = sorted(set(item["training_families"]))
        item["expansion_links"].sort(key=lambda value: value["declaration"])
        item["support_count"] = len(item["training_support"])
        item["family_count"] = len(item["training_families"])
        item["acceptance_status"] = (
            "accepted_by_structural_rule"
            if len(item["components"]) >= 2
            and item["support_count"] >= limits["min_support"]
            and item["family_count"] >= limits["min_families"]
            and item["acyclic"]
            else "proposed_structural_only"
        )
        if item["acceptance_status"] == "accepted_by_structural_rule":
            accepted_ids.add(item["id"])
        compositions.append(item)
    accepted_occurrences = [
        {
            "composition_id": item["id"],
            "round": item["round"],
            "declaration": row["declaration"],
            "family": row["family"],
            "partition": row["partition"],
            "root_path": row["root_path"],
            "source": row["source"],
            "signature_sha256": row["signature_sha256"],
            "target_evidence": row["target_evidence"],
            "expansion_links": row["expansion_links"],
            "expansion_status": "complete",
        }
        for item in compositions if item["id"] in accepted_ids
        for row in rows if row["key"] == item["composition_key"]
    ]
    accepted_occurrences.sort(key=lambda item: (
        item["composition_id"], item["declaration"], item["root_path"]
    ))
    return compositions, accepted_ids, accepted_occurrences


def _mine_compositions(
    declarations: list[LoadedDeclaration],
    accepted: list[dict[str, Any]],
    limits: dict[str, int],
) -> dict[str, Any]:
    # Composition fitting and feedback are deliberately train-only.  In
    # particular, do not even materialize held-out component occurrences here:
    # the group/acceptance filter below is too late to be a safe no-leakage
    # boundary for intermediate artifacts.
    train_declarations = [
        declaration for declaration in declarations if declaration.partition == "train"
    ]
    atomic_components = _component_candidates(accepted)
    atomic_occurrences, atomic_by_declaration_component = _component_occurrences(
        train_declarations, atomic_components, limits, partitions={"train"}
    )
    all_components = list(atomic_components)
    all_component_occurrences = list(atomic_occurrences)
    all_compositions: list[dict[str, Any]] = []
    all_accepted_ids: set[str] = set()
    all_accepted_occurrences: list[dict[str, Any]] = []
    round_reports: list[dict[str, Any]] = []
    prior_compositions: list[dict[str, Any]] = []
    prior_occurrences: list[dict[str, Any]] = []
    termination_reason = "max_rounds_reached"
    max_rounds = limits["max_rounds"]
    for round_number in range(1, max_rounds + 1):
        feedback_components: list[dict[str, Any]] = []
        feedback_occurrences: list[dict[str, Any]] = []
        if round_number > 1:
            feedback_components, feedback_occurrences = _feedback_components(
                prior_compositions, prior_occurrences, train_declarations, round_number
            )
            if not feedback_components:
                round_reports.append({
                    "round": round_number,
                    "input_composition_ids": sorted(item["id"] for item in prior_compositions),
                    "feedback_component_count": 0,
                    "candidate_count": 0,
                    "accepted_count": 0,
                    "status": "no_feedback_components",
                })
                termination_reason = "no_feedback_components"
                break
        round_component_occurrences = atomic_occurrences if round_number == 1 else []
        round_by_declaration_component = (
            atomic_by_declaration_component if round_number == 1 else {}
        )
        if round_number > 1:
            round_component_occurrences = feedback_occurrences + atomic_occurrences
            round_by_declaration_component = defaultdict(list)
            for occurrence in round_component_occurrences:
                round_by_declaration_component[
                    (occurrence["declaration"], occurrence["component_id"])
                ].append(occurrence)
        candidate_sets = _composition_candidate_sets(
            atomic_components, feedback_components, limits
        )
        rows: list[dict[str, Any]] = []
        for component_set in candidate_sets:
            for declaration in sorted(train_declarations, key=lambda item: item.name):
                if declaration.usable:
                    rows.extend(_composition_rows_for_declaration(
                        declaration,
                        component_set,
                        round_by_declaration_component,
                        limits,
                        required_component_prefix="feedback:" if round_number > 1 else None,
                    ))
        deduped_rows = {(
            row["key"], row["declaration"], tuple(row["root_path"])
        ): row for row in rows}
        rows = [deduped_rows[key] for key in sorted(deduped_rows)]
        compositions, accepted_ids, accepted_occurrences = _group_composition_rows(
            rows,
            limits,
            round_number=round_number,
            allowed_composition_ids=set(all_accepted_ids),
        )
        all_components.extend(feedback_components)
        all_component_occurrences.extend(feedback_occurrences)
        all_compositions.extend(compositions)
        all_accepted_ids.update(accepted_ids)
        all_accepted_occurrences.extend(accepted_occurrences)
        round_reports.append({
            "round": round_number,
            "input_composition_ids": sorted(item["id"] for item in prior_compositions),
            "feedback_component_count": len(feedback_components),
            "candidate_set_count": len(candidate_sets),
            "candidate_count": len(compositions),
            "accepted_count": len(accepted_ids),
            "status": "complete" if compositions else "no_candidate_rows",
        })
        if not accepted_ids:
            termination_reason = "no_new_accepted_compositions"
            break
        prior_compositions = [item for item in compositions if item["id"] in accepted_ids]
        prior_occurrences = [
            item for item in accepted_occurrences if item["composition_id"] in accepted_ids
        ]
    all_components.sort(key=lambda item: item["id"])
    all_component_occurrences.sort(key=lambda item: (
        item["component_id"], item["declaration"], item["path"]
    ))
    all_compositions.sort(key=lambda item: (item["round"], item["id"]))
    all_accepted_occurrences.sort(key=lambda item: (
        item["composition_id"], item["declaration"], item["root_path"]
    ))
    return {
        "components": all_components,
        "component_occurrences": all_component_occurrences,
        "compositions": all_compositions,
        "accepted_ids": sorted(all_accepted_ids),
        "accepted_occurrences": all_accepted_occurrences,
        "rounds": round_reports,
        "summary": {
            "component_count": len(all_components),
            "component_occurrence_count": len(all_component_occurrences),
            "composition_candidate_count": len(all_compositions),
            "accepted_composition_count": len(all_accepted_ids),
            "held_out_composition_occurrence_count": sum(
                item["partition"] == "held_out" for item in all_accepted_occurrences
            ),
            "round_count": len(round_reports),
            "max_rounds": max_rounds,
            "feedback_component_count": sum(
                report["feedback_component_count"] for report in round_reports
            ),
            "termination_reason": termination_reason,
            "status": "complete",
            "fit_partitions": ["train"],
            "evaluation_partitions": [],
        },
    }


def _evaluate_held_out_compositions(
    declarations: list[LoadedDeclaration],
    composition_result: dict[str, Any],
    limits: dict[str, int],
) -> dict[str, Any]:
    """Evaluate frozen compositions on held-out declarations after fitting.

    Round fitting never sees these occurrences.  A composition containing a
    feedback component is reported as not evaluable in this pass because the
    current matcher has no raw-tree reifier for a carried synthetic node; it
    is not silently rematched or fed back into the vocabulary.
    """
    held_out_declarations = [
        declaration for declaration in declarations if declaration.partition == "held_out"
    ]
    atomic_components = [
        component for component in composition_result.get("components", [])
        if isinstance(component, dict)
        and isinstance(component.get("id"), str)
        and not component["id"].startswith("feedback:")
    ]
    atomic_by_id = {component["id"]: component for component in atomic_components}
    held_out_component_occurrences, held_out_by_declaration_component = _component_occurrences(
        held_out_declarations,
        atomic_components,
        limits,
        partitions={"held_out"},
    )
    accepted_compositions = [
        composition for composition in composition_result.get("compositions", [])
        if isinstance(composition, dict)
        and composition.get("acceptance_status") == "accepted_by_structural_rule"
    ]
    occurrences: list[dict[str, Any]] = []
    evaluated_ids: set[str] = set()
    skipped: list[dict[str, str]] = []
    for composition in sorted(accepted_compositions, key=lambda item: item["id"]):
        component_ids = composition.get("components", [])
        if (
            not isinstance(component_ids, list)
            or any(component_id not in atomic_by_id for component_id in component_ids)
        ):
            skipped.append({
                "composition_id": composition["id"],
                "reason": "feedback_component_evaluation_not_supported",
            })
            continue
        component_set = [atomic_by_id[component_id] for component_id in component_ids]
        matched = False
        for declaration in sorted(held_out_declarations, key=lambda item: item.name):
            if not declaration.usable:
                continue
            rows = _composition_rows_for_declaration(
                declaration,
                component_set,
                held_out_by_declaration_component,
                limits,
            )
            for row in rows:
                if row.get("key") != composition.get("composition_key"):
                    continue
                occurrences.append({
                    "composition_id": composition["id"],
                    "declaration": row["declaration"],
                    "family": row["family"],
                    "partition": "held_out",
                    "root_path": row["root_path"],
                    "source": row["source"],
                    "signature_sha256": row["signature_sha256"],
                    "target_evidence": row["target_evidence"],
                    "expansion_links": row["expansion_links"],
                    "evaluation_status": "post_freeze_structural_match",
                })
                evaluated_ids.add(composition["id"])
                matched = True
                if len(occurrences) >= limits["max_component_occurrences"]:
                    break
            if len(occurrences) >= limits["max_component_occurrences"]:
                break
        if not matched and composition["id"] not in evaluated_ids:
            # Absence is a measured zero, not an unreported attempt.
            evaluated_ids.add(composition["id"])
    occurrences.sort(key=lambda item: (
        item["composition_id"], item["declaration"], item["root_path"]
    ))
    return {
        "status": "complete",
        "phase": "post_freeze_evaluation",
        "fit_partitions": ["train"],
        "evaluation_partitions": ["held_out"],
        "accepted_composition_ids": sorted(
            composition["id"] for composition in accepted_compositions
        ),
        "evaluated_composition_ids": sorted(evaluated_ids),
        "skipped_compositions": skipped,
        "held_out_component_occurrence_count": len(held_out_component_occurrences),
        "held_out_occurrence_count": len(occurrences),
        "occurrences": occurrences,
    }


def _expanded_pairs(
    declarations: list[LoadedDeclaration],
    baseline_pairs: list[dict[str, Any]],
    vocabulary_by_declaration: dict[str, list[str]],
    max_pairs: int,
) -> list[dict[str, Any]]:
    expanded = []
    for pair in baseline_pairs:
        left_tokens = set(vocabulary_by_declaration.get(pair["left"], []))
        right_tokens = set(vocabulary_by_declaration.get(pair["right"], []))
        overlap = sorted(left_tokens & right_tokens)
        item = dict(pair)
        item["vocabulary_overlap"] = overlap
        item["expanded_score"] = round(
            pair["scores"]["shape"]
            + (0.25 * (len(overlap) / max(1, len(left_tokens | right_tokens)))), 12
        )
        expanded.append(item)
    expanded.sort(key=lambda item: (-item["expanded_score"], item["left"], item["right"]))
    return expanded[:max_pairs]


def _declaration_json(declaration: LoadedDeclaration) -> dict[str, Any]:
    return {
        "name": declaration.name,
        "family": declaration.family,
        "partition": declaration.partition,
        "status": declaration.status,
        "reason": declaration.reason,
        "signature_sha256": declaration.signature_sha256,
        "source": declaration.source,
        "evidence": declaration.evidence,
    }


def discover(manifest_path: str | Path) -> dict[str, Any]:
    """Run baseline, one-pass, and two-pass discovery from a fixed manifest."""
    manifest = load_manifest(manifest_path)
    declarations, input_info = load_corpus(manifest)
    limits = dict(manifest.limits)
    # Fitting retrieval, IDF statistics, candidate budgets, anti-unification,
    # and vocabulary construction are strictly training-only.  Held-out
    # queries are evaluated in a separate bounded report below and can never
    # change the fitted proposal set.
    baseline_pairs, baseline_summary = _baseline_pairs(
        declarations,
        max_candidates_per_query=limits["max_candidates_per_query"],
        max_pairs=limits["max_pairs"],
        query_partition="train",
        candidate_partition="train",
    )
    held_out_pairs, held_out_baseline_summary = _baseline_pairs(
        declarations,
        max_candidates_per_query=limits["max_candidates_per_query"],
        max_pairs=limits["max_pairs"],
        query_partition="held_out",
        candidate_partition="train",
    )
    proposals, proposal_summary = _build_proposals(declarations, baseline_pairs, limits)
    accepted = [proposal for proposal in proposals if proposal["acceptance_status"] == "accepted_by_structural_rule"]
    occurrences, vocabulary = _occurrences(declarations, accepted)
    composition_result = _mine_compositions(declarations, accepted, limits)
    # This call is intentionally after all training proposal/composition
    # fitting.  It consumes the frozen accepted composition set and writes only
    # a held-out evaluation report; no result from it is fed back into either
    # vocabulary or composition rounds.
    held_out_composition_evaluation = _evaluate_held_out_compositions(
        declarations, composition_result, limits
    )
    expanded = _expanded_pairs(declarations, baseline_pairs, vocabulary, limits["max_pairs"])
    held_out_expanded = _expanded_pairs(
        declarations, held_out_pairs, vocabulary, limits["max_pairs"]
    )
    train_occurrences = [
        item for item in occurrences if item["occurrence"]["partition"] == "train"
    ]
    held_out_occurrences = [
        item for item in occurrences if item["occurrence"]["partition"] == "held_out"
    ]
    core = {
        "schema_version": SCHEMA_VERSION,
        "algorithm_version": ALGORITHM_VERSION,
        "manifest_sha256": manifest.content_hash,
        "input": input_info,
        "limits": limits,
        "declarations": [_declaration_json(item) for item in declarations],
        "baseline": {
            "algorithm": "existing similarity feature family: shape/semantic-head/type-premise/proof-premise Jaccard",
            "summary": baseline_summary,
            "pairs": baseline_pairs,
        },
        "held_out_evaluation": {
            "baseline": {
                "summary": held_out_baseline_summary,
                "pairs": held_out_pairs,
            },
            "two_pass": {
                "summary": {
                    "candidate_pairs": len(held_out_expanded),
                    "status": "complete",
                },
                "pairs": held_out_expanded,
            },
            "composition": held_out_composition_evaluation,
        },
        "one_pass": {
            "summary": proposal_summary,
            "proposals": proposals,
            "occurrences": occurrences,
        },
        "two_pass": {
            "vocabulary": {
                "schema_version": 1,
                "accepted_ids": sorted(item["id"] for item in accepted),
                "accepted_composition_ids": composition_result["accepted_ids"],
                "accepted_occurrence_count": len(train_occurrences),
                "held_out_occurrence_count": len(held_out_occurrences),
                "by_declaration": vocabulary,
            },
            "expanded_pairs": expanded,
            "components": composition_result["components"],
            "component_occurrences": composition_result["component_occurrences"],
            "compositions": composition_result["compositions"],
            "composition_occurrences": composition_result["accepted_occurrences"],
            "composition_rounds": composition_result["rounds"],
            "composition_summary": composition_result["summary"],
            "summary": {
                "accepted_vocabulary": len(accepted),
                "accepted_compositions": len(composition_result["accepted_ids"]),
                "matched_occurrences": len(occurrences),
                "training_occurrences": len(train_occurrences),
                "held_out_occurrences": len(held_out_occurrences),
                "composition_round_count": len(composition_result["rounds"]),
                "status": "complete",
            },
        },
        "status_vocabulary": {
            "usable": "signature tree represented by the versioned IR",
            "unknown": "required capture tree or evidence is unavailable/unsupported",
            "truncated": "a fixed non-wall-clock budget was exhausted",
            "accepted_by_structural_rule": "deterministic recurrence rule passed; not mathematical validation",
            "accepted_composition": "deterministic multi-component expansion passed; not mathematical validation",
            "not_reviewed": "no independent mathematical interpretation review has been performed",
        },
        "limits_and_scope": [
            "declaration signature trees only; no tactic-state representation",
            "proof terms are not reconstructed and opaque theorem bodies are not inlined",
            "binder types and binderInfo must align exactly; local names are ignored",
            "all accepted occurrences are source/capture anchored, but structural recurrence is not theorem equivalence",
            "second pass consumes only first-pass accepted occurrences from the training split; bounded feedback rounds may carry accepted composed technique_ref nodes forward",
            "feedback rounds are capped by max_rounds, use only the immediately preceding accepted round, and retain source/capture expansion links",
        ],
    }
    core["canonical_result_sha256"] = _sha256_json(core)
    return core


def write_result(result: dict[str, Any], path: str | Path) -> Path:
    """Write a canonical report; volatile paths and times are never inserted."""
    output = Path(path).expanduser()
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(_canonical_json(result) + "\n", encoding="utf-8")
    return output


def _result_payload(result: dict[str, Any]) -> dict[str, Any]:
    """Return the canonical report payload without its self-referential hash."""
    return {
        key: value for key, value in result.items()
        if key != "canonical_result_sha256"
    }


def _result_payload_sha256(result: dict[str, Any]) -> str:
    return _sha256_json(_result_payload(result))


def verify_result(result: dict[str, Any], manifest_path: str | Path) -> dict[str, Any]:
    """Recompute a report and validate only application-owned evidence pins.

    Verification is deliberately read-only: it never executes Lean, Lake,
    Python, or any path named by a manifest.  A separate developer command
    regenerates evidence from the fixed private fixture; this function checks
    the resulting frozen artifact/receipt profile and does not reproduce that
    execution.  It does not prove a theorem or validate a mathematical
    interpretation.
    """
    if not isinstance(result, dict):
        return {"status": "FAIL", "reason": "result_payload_malformed"}
    expected = result.get("canonical_result_sha256")
    supplied_payload_hash = _result_payload_sha256(result)
    if not isinstance(expected, str) or expected != supplied_payload_hash:
        return {
            "status": "FAIL",
            "reason": "result_payload_tampered",
            "expected": expected,
            "actual": supplied_payload_hash,
        }
    current = discover(manifest_path)
    actual = current.get("canonical_result_sha256")
    if expected != actual:
        return {
            "status": "FAIL",
            "reason": "manifest_or_capture_changed",
            "expected": expected,
            "actual": actual,
        }
    manifest = load_manifest(manifest_path)
    source_check = _verify_source_manifest(manifest.source_manifest_path)
    if source_check["status"] == "FAIL":
        return {
            "status": "FAIL",
            "reason": "source_file_tampered",
            "source_check": source_check,
            "canonical_result_sha256": actual,
        }
    if source_check["status"] == "UNKNOWN":
        return {
            "status": "UNKNOWN",
            "reason": "source_verification_unknown",
            "source_check": source_check,
            "canonical_result_sha256": actual,
        }
    evidence_status = current.get("input", {}).get("evidence_status", {})
    if evidence_status.get("status") != "captured":
        return {
            "status": "UNKNOWN",
            "reason": "required_evidence_unknown",
            "evidence_status": evidence_status,
            "canonical_result_sha256": actual,
        }
    if manifest.trace_path is not None or manifest.type_evidence_path is not None:
        trusted_evidence = _verify_trusted_evidence_profile(manifest, current)
        if trusted_evidence.get("status") != "PASS":
            return {
                "status": "UNKNOWN",
                "reason": trusted_evidence.get("reason", "trusted_evidence_unknown"),
                "trusted_evidence": trusted_evidence,
                "canonical_result_sha256": actual,
            }
    return {
        "status": "PASS",
        "canonical_result_sha256": actual,
        "source_revision": current["input"].get("source_revision"),
        "source_check": source_check,
        "warning": "replay identity is not theorem validation",
    }


def _verify_source_manifest(path: Path | None) -> dict[str, Any]:
    """Check available source files against the pinned source manifest."""
    if path is None:
        return {"status": "UNKNOWN", "reason": "manifest_has_no_source_manifest"}
    if not path.is_file():
        return {"status": "UNKNOWN", "reason": "source_manifest_not_found"}
    raw, _digest = _read_json(path)
    if not isinstance(raw, dict) or not isinstance(raw.get("files"), list):
        return {"status": "UNKNOWN", "reason": "malformed_source_manifest"}
    root_raw = raw.get("source_root")
    root = Path(root_raw).expanduser().resolve() if isinstance(root_raw, str) else None
    if root is not None and not root.is_dir():
        root = None
    if root is None and root_raw is not None:
        return {"status": "UNKNOWN", "reason": "source_root_unavailable"}
    if root is None:
        fallback = path.parent.parent / "upstream"
        root = fallback.resolve() if fallback.is_dir() else None
    if root is None:
        return {"status": "UNKNOWN", "reason": "source_root_unavailable"}
    checked = 0
    missing = []
    mismatched = []
    for row in raw["files"]:
        if not isinstance(row, dict) or not isinstance(row.get("path"), str):
            continue
        if Path(row["path"]).is_absolute():
            return {"status": "UNKNOWN", "reason": "source_manifest_path_traversal"}
        candidate = (root / row["path"]).resolve()
        try:
            candidate.relative_to(root)
        except ValueError:
            return {"status": "UNKNOWN", "reason": "source_manifest_path_traversal"}
        if not candidate.is_file():
            missing.append(row["path"])
            continue
        checked += 1
        actual = _sha256_file(candidate)
        if actual != row.get("sha256"):
            mismatched.append(row["path"])
    if mismatched:
        return {"status": "FAIL", "checked": checked, "mismatched": sorted(mismatched)}
    if missing:
        return {"status": "UNKNOWN", "checked": checked, "missing": sorted(missing)}
    return {"status": "PASS", "checked": checked}


def _trusted_fixture_path(name: str) -> Path:
    """Resolve a path from the application-owned fixture root only."""
    return (APPLICATION_ROOT / TRUSTED_DISCOVERY_RELATIVE_ROOT / name).resolve()


def _path_is(path: Path | None, expected: Path) -> bool:
    return path is not None and path.resolve() == expected.resolve()


def _verify_trusted_evidence_profile(
    manifest: Manifest, current: dict[str, Any]
) -> dict[str, Any]:
    """Validate frozen evidence against code-owned paths and hashes.

    This function is deliberately read-only.  It never invokes Lean, ``lake``,
    a manifest-supplied script, or any executable found through ``PATH``.  A
    caller can provide a different manifest for exploratory discovery, but a
    verified result with executable-backed evidence requires this application-
    owned allowlist and frozen receipt.
    """
    trusted_manifest = _trusted_fixture_path("discovery-manifest.json")
    if not _path_is(manifest.path, trusted_manifest):
        return {"status": "UNKNOWN", "reason": "trusted_manifest_not_allowlisted"}
    if manifest.content_hash != TRUSTED_DISCOVERY_MANIFEST_SHA256:
        return {"status": "UNKNOWN", "reason": "trusted_manifest_hash_mismatch"}

    expected_paths = {
        "capture": _trusted_fixture_path("declarations.json.gz"),
        "source_manifest": _trusted_fixture_path("source-manifest.json"),
        "trace": _trusted_fixture_path("discovery-trace-boundaries.json.gz"),
        "type_evidence": _trusted_fixture_path("discovery-type-evidence.json"),
        "receipt": _trusted_fixture_path("discovery-receipt.json"),
        "trace_extractor": APPLICATION_ROOT / "capture/percolation/ExtractProofTrace.lean",
        "type_evidence_extractor": APPLICATION_ROOT / "capture/percolation/ExtractDiscoveryEvidence.lean",
    }
    if not _path_is(manifest.capture_path, expected_paths["capture"]):
        return {"status": "UNKNOWN", "reason": "trusted_capture_path_mismatch"}
    if not _path_is(manifest.source_manifest_path, expected_paths["source_manifest"]):
        return {"status": "UNKNOWN", "reason": "trusted_source_manifest_path_mismatch"}
    if not _path_is(manifest.trace_path, expected_paths["trace"]):
        return {"status": "UNKNOWN", "reason": "trusted_trace_path_mismatch"}
    if not _path_is(manifest.type_evidence_path, expected_paths["type_evidence"]):
        return {"status": "UNKNOWN", "reason": "trusted_type_evidence_path_mismatch"}
    if not _path_is(manifest.trace_extractor_path, expected_paths["trace_extractor"]):
        return {"status": "UNKNOWN", "reason": "trusted_trace_extractor_path_mismatch"}
    if not _path_is(
        manifest.type_evidence_extractor_path, expected_paths["type_evidence_extractor"]
    ):
        return {"status": "UNKNOWN", "reason": "trusted_type_evidence_extractor_path_mismatch"}

    artifact_hashes: dict[str, str] = {}
    for label in ("capture", "source_manifest", "trace", "type_evidence"):
        path = expected_paths[label]
        if not path.is_file():
            return {"status": "UNKNOWN", "reason": f"trusted_{label}_not_found"}
        try:
            _value, digest = _read_json(path)
        except DiscoveryError as error:
            return {"status": "UNKNOWN", "reason": f"trusted_{label}_malformed:{error}"}
        artifact_hashes[label] = digest
        if digest != TRUSTED_DISCOVERY_ARTIFACT_HASHES[label]:
            return {
                "status": "UNKNOWN",
                "reason": f"trusted_{label}_hash_mismatch",
                "actual_sha256": digest,
            }
    for label in ("trace", "type_evidence"):
        extractor = expected_paths[f"{label}_extractor"]
        if not extractor.is_file():
            return {"status": "UNKNOWN", "reason": f"trusted_{label}_extractor_not_found"}
        digest = _sha256_file(extractor)
        if digest != TRUSTED_DISCOVERY_EXTRACTOR_HASHES[label]:
            return {
                "status": "UNKNOWN",
                "reason": f"trusted_{label}_extractor_hash_mismatch",
                "actual_sha256": digest,
            }

    receipt = expected_paths["receipt"]
    if not receipt.is_file():
        return {"status": "UNKNOWN", "reason": "trusted_receipt_not_found"}
    try:
        receipt_value, receipt_hash = _read_json(receipt)
    except DiscoveryError as error:
        return {"status": "UNKNOWN", "reason": f"trusted_receipt_malformed:{error}"}
    if receipt_hash != TRUSTED_DISCOVERY_RECEIPT_SHA256:
        return {"status": "UNKNOWN", "reason": "trusted_receipt_hash_mismatch"}
    if not isinstance(receipt_value, dict):
        return {"status": "UNKNOWN", "reason": "trusted_receipt_malformed"}
    if receipt_value.get("canonical_result_sha256") != current.get("canonical_result_sha256"):
        return {"status": "UNKNOWN", "reason": "trusted_receipt_result_mismatch"}
    receipt_artifacts = receipt_value.get("evidence_artifacts")
    if not isinstance(receipt_artifacts, dict):
        return {"status": "UNKNOWN", "reason": "trusted_receipt_artifacts_missing"}
    for label, digest in artifact_hashes.items():
        receipt_key = "trace_logical_sha256" if label == "trace" else f"{label}_sha256"
        if receipt_artifacts.get(receipt_key) != digest:
            return {"status": "UNKNOWN", "reason": f"trusted_receipt_{label}_mismatch"}
    return {
        "status": "PASS",
        "manifest_sha256": manifest.content_hash,
        "receipt_sha256": receipt_hash,
        "artifact_hashes": artifact_hashes,
        "execution": "none",
    }


def main(argv: list[str] | None = None) -> int:
    import argparse

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", required=True, type=Path)
    parser.add_argument("--output", type=Path, help="optional canonical JSON report path")
    parser.add_argument("--json", action="store_true", help="emit JSON to stdout")
    args = parser.parse_args(argv)
    try:
        result = discover(args.manifest)
        if args.output:
            write_result(result, args.output)
        if args.json or not args.output:
            print(json.dumps(result, indent=2, ensure_ascii=False))
        else:
            print(f"wrote {args.output.expanduser().resolve()}")
        return 0
    except (OSError, DiscoveryError, json.JSONDecodeError) as error:
        print(f"error: {error}")
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
