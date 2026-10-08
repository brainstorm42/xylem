"""Strict, versioned notation-profile loader and compiler."""

from __future__ import annotations
from dataclasses import dataclass
import hashlib
from pathlib import Path
from typing import Any
import yaml

class ProfileError(ValueError):
    pass

PROFILE_KEYS = {"schema_version", "profile_id", "profile_version", "symbols", "structures", "notes"}
SYMBOL_KEYS = {"aliases", "output", "kind", "arity", "precedence", "associativity", "frame_required", "provenance"}
STRUCTURE_KEYS = {"head", "arity", "input", "output", "precedence", "associativity", "provenance"}
ASSOCIATIVITY = {"left", "right", "none"}

@dataclass(frozen=True)
class SymbolRule:
    semantic_id: str
    aliases: tuple[str, ...]
    output: str
    kind: str
    arity: int
    precedence: int | None = None
    associativity: str = "none"
    frame_required: bool = False
    provenance: str = ""

@dataclass(frozen=True)
class StructureRule:
    semantic_id: str
    head: str
    arity: int
    input: tuple[str, ...]
    output: str
    precedence: int | None = None
    associativity: str = "none"
    provenance: str = ""

@dataclass(frozen=True)
class NotationProfile:
    profile_id: str
    profile_version: int
    symbols: dict[str, SymbolRule]
    structures: dict[str, StructureRule]
    source_hash: str
    source: str

    @property
    def alias_index(self) -> dict[str, str]:
        return {alias: sid for sid, rule in self.symbols.items() for alias in rule.aliases}

    def output_for(self, semantic_id: str, *, frame: str | None = None) -> str:
        rule = self.symbols.get(semantic_id)
        if rule is None:
            raise ProfileError(f"{self.profile_id}: unknown semantic ID {semantic_id!r}")
        if rule.frame_required and not frame:
            raise ProfileError(f"{self.profile_id}: {semantic_id!r} requires frame metadata")
        return rule.output.replace("{frame}", frame or "")

def _mapping(value: Any, where: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise ProfileError(f"{where} must be a mapping")
    return value

def _reject_unknown(mapping: dict[str, Any], allowed: set[str], where: str) -> None:
    unknown = sorted(set(mapping) - allowed)
    if unknown:
        raise ProfileError(f"{where}: unknown keys: {', '.join(unknown)}")

def _text(value: Any, where: str) -> str:
    if isinstance(value, bool) or not isinstance(value, str):
        raise ProfileError(f"{where} must be a quoted string")
    return value

def _compile(raw: dict[str, Any], source: Path, digest: str) -> NotationProfile:
    _reject_unknown(raw, PROFILE_KEYS, str(source))
    if raw.get("schema_version") != 1:
        raise ProfileError(f"{source}: unsupported schema_version {raw.get('schema_version')!r}")
    profile_id = _text(raw.get("profile_id"), f"{source}: profile_id")
    version = raw.get("profile_version")
    if isinstance(version, bool) or not isinstance(version, int) or version < 1:
        raise ProfileError(f"{source}: profile_version must be a positive integer")
    symbols: dict[str, SymbolRule] = {}
    seen_aliases: dict[str, str] = {}
    for sid, entry in sorted(_mapping(raw.get("symbols", {}), f"{source}: symbols").items()):
        sid = _text(sid, f"{source}: symbol key")
        entry = _mapping(entry, f"{source}: symbols.{sid}")
        _reject_unknown(entry, SYMBOL_KEYS, f"{source}: symbols.{sid}")
        aliases_raw = entry.get("aliases", [])
        if not isinstance(aliases_raw, list):
            raise ProfileError(f"{source}: symbols.{sid}.aliases must be a list")
        aliases = tuple(_text(a, f"{source}: symbols.{sid}.aliases") for a in aliases_raw)
        output = _text(entry.get("output"), f"{source}: symbols.{sid}.output")
        kind = _text(entry.get("kind"), f"{source}: symbols.{sid}.kind")
        arity = entry.get("arity")
        if isinstance(arity, bool) or not isinstance(arity, int) or arity < 0:
            raise ProfileError(f"{source}: symbols.{sid}.arity must be a nonnegative integer")
        assoc = entry.get("associativity", "none")
        if assoc not in ASSOCIATIVITY:
            raise ProfileError(f"{source}: symbols.{sid}.associativity is invalid")
        for alias in aliases:
            other = seen_aliases.get(alias)
            if other is not None and other != sid:
                raise ProfileError(f"{source}: alias {alias!r} maps to both {other!r} and {sid!r}")
            seen_aliases[alias] = sid
        symbols[sid] = SymbolRule(sid, aliases, output, kind, arity, entry.get("precedence"), assoc, bool(entry.get("frame_required", False)), str(entry.get("provenance", "")))
    structures: dict[str, StructureRule] = {}
    for sid, entry in sorted(_mapping(raw.get("structures", {}), f"{source}: structures").items()):
        entry = _mapping(entry, f"{source}: structures.{sid}")
        _reject_unknown(entry, STRUCTURE_KEYS, f"{source}: structures.{sid}")
        arity, inputs = entry.get("arity"), entry.get("input", [])
        if isinstance(arity, bool) or not isinstance(arity, int) or arity < 0:
            raise ProfileError(f"{source}: structures.{sid}.arity must be a nonnegative integer")
        if not isinstance(inputs, list) or len(inputs) != arity:
            raise ProfileError(f"{source}: structures.{sid}.input must contain exactly {arity} arguments")
        assoc = entry.get("associativity", "none")
        if assoc not in ASSOCIATIVITY:
            raise ProfileError(f"{source}: structures.{sid}.associativity is invalid")
        structures[sid] = StructureRule(sid, _text(entry.get("head"), f"{source}: structures.{sid}.head"), arity, tuple(_text(x, f"{source}: structures.{sid}.input") for x in inputs), _text(entry.get("output"), f"{source}: structures.{sid}.output"), entry.get("precedence"), assoc, str(entry.get("provenance", "")))
    return NotationProfile(profile_id, version, symbols, structures, digest, str(source))

def load_profile(path: str | Path, overlay: str | Path | None = None) -> NotationProfile:
    path = Path(path)
    source = path.read_bytes()
    raw = yaml.safe_load(source) or {}
    if overlay is not None:
        overlay_path = Path(overlay)
        extra = yaml.safe_load(overlay_path.read_bytes()) or {}
        _reject_unknown(extra, PROFILE_KEYS, str(overlay_path))
        if extra.get("schema_version", 1) != 1:
            raise ProfileError(f"{overlay_path}: unsupported schema_version")
        raw = dict(raw)
        for section in ("symbols", "structures"):
            merged = dict(raw.get(section, {})); merged.update(extra.get(section, {})); raw[section] = merged
        source += b"\n--- overlay ---\n" + overlay_path.read_bytes()
    return _compile(_mapping(raw, str(path)), path, hashlib.sha256(source).hexdigest())

def profile_summary(profile: NotationProfile) -> dict[str, Any]:
    return {"schema_version": 1, "profile_id": profile.profile_id, "profile_version": profile.profile_version, "profile_hash": profile.source_hash, "symbols": len(profile.symbols), "structures": len(profile.structures)}
