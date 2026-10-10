#!/usr/bin/env python3
"""Memory-bounded companion for ``derive_proof_components.py``.

The historical derivation command loads both the complete capture and the
complete compact trace with ``json.load``.  The compact trace is intentionally
large after decompression, so this module keeps the same component contract
while streaming declarations and trace records one application/reference at a
time.  It is invoked by the parent command's explicit ``--bounded`` flag.
"""

from __future__ import annotations

import gzip
import json
import tempfile
from collections import defaultdict
from pathlib import Path
from typing import Any, Iterator

from derive_proof_components import (
    LEGITIMATE_NO_VALUE_KINDS,
    ROOT_DECL,
    _application_shape_errors,
    _app_head_name,
    _is_data_application,
    _is_proof_application,
    _local_name,
    _trace_component_id,
    _trace_record_id,
    _trace_target_component_id,
    generated_components,
    interface,
    load_json,
    record_map,
    validate_roles,
)


class TextReader:
    """Small incremental JSON reader for one top-level object/array stream.

    ``json.JSONDecoder.raw_decode`` is used for bounded values such as one
    declaration or one application record.  Large unknown values (notably the
    optional expression tree) are skipped with a delimiter scanner instead of
    being materialized.
    """

    def __init__(self, stream, *, chunk_size: int = 4 * 1024 * 1024) -> None:
        self.stream = stream
        self.chunk_size = chunk_size
        self.buffer = ""
        self.pos = 0
        self.eof = False
        self.decoder = json.JSONDecoder()

    def _fill(self) -> bool:
        if self.pos < len(self.buffer):
            return True
        if self.eof:
            return False
        more = self.stream.read(self.chunk_size)
        if not more:
            self.eof = True
            return False
        self.buffer = more
        self.pos = 0
        return True

    def _compact(self) -> None:
        if self.pos > self.chunk_size and self.pos > len(self.buffer) // 2:
            self.buffer = self.buffer[self.pos :]
            self.pos = 0

    def skip_ws(self) -> None:
        while True:
            while self.pos < len(self.buffer) and self.buffer[self.pos].isspace():
                self.pos += 1
            if self.pos < len(self.buffer):
                return
            if not self._fill():
                return

    def peek(self) -> str | None:
        self.skip_ws()
        if self.pos >= len(self.buffer):
            return None
        return self.buffer[self.pos]

    def expect(self, expected: str) -> None:
        self.skip_ws()
        if not self._fill() or self.buffer[self.pos] != expected:
            actual = None if self.pos >= len(self.buffer) else self.buffer[self.pos]
            raise ValueError(f"expected {expected!r}, got {actual!r}")
        self.pos += 1

    def value(self) -> Any:
        self.skip_ws()
        while True:
            try:
                result, end = self.decoder.raw_decode(self.buffer, self.pos)
                self.pos = end
                self._compact()
                return result
            except json.JSONDecodeError:
                if self.eof:
                    raise
                if self.pos:
                    self.buffer = self.buffer[self.pos :]
                    self.pos = 0
                more = self.stream.read(self.chunk_size)
                if not more:
                    self.eof = True
                else:
                    self.buffer += more

    def skip_value(self) -> None:
        self.skip_ws()
        first = self.peek()
        if first not in "[{":
            self.value()
            return
        stack: list[str] = []
        in_string = False
        escaped = False
        while True:
            if self.pos >= len(self.buffer):
                if not self._fill():
                    raise ValueError("truncated JSON value while skipping")
            char = self.buffer[self.pos]
            self.pos += 1
            if in_string:
                if escaped:
                    escaped = False
                elif char == "\\":
                    escaped = True
                elif char == '"':
                    in_string = False
                continue
            if char == '"':
                in_string = True
            elif char in "[{":
                stack.append(char)
            elif char == "]":
                if not stack or stack.pop() != "[":
                    raise ValueError("mismatched JSON array while skipping")
            elif char == "}":
                if not stack or stack.pop() != "{":
                    raise ValueError("mismatched JSON object while skipping")
            if not stack:
                self._compact()
                return

    def array_values(self) -> Iterator[Any]:
        self.expect("[")
        while True:
            self.skip_ws()
            if self.peek() == "]":
                self.pos += 1
                return
            yield self.value()
            self.skip_ws()
            delimiter = self.peek()
            if delimiter == ",":
                self.pos += 1
                continue
            if delimiter == "]":
                self.pos += 1
                return
            raise ValueError(f"expected array delimiter, got {delimiter!r}")


def _open_text(path: Path):
    if path.suffix == ".gz":
        return gzip.open(path, "rt", encoding="utf-8")
    return path.open("r", encoding="utf-8")


def _slim_capture_record(record: dict[str, Any]) -> dict[str, Any]:
    """Discard expression trees and retain the fields used by derivation."""
    premises = []
    for premise in record.get("premises", []):
        if isinstance(premise, dict):
            premises.append({
                "name": premise.get("name"),
                "in_proof": premise.get("in_proof"),
            })
    binders = []
    for binder in record.get("binders", []):
        if isinstance(binder, dict):
            binders.append({
                "idx": binder.get("idx"),
                "name": binder.get("name"),
                "binderInfo": binder.get("binderInfo"),
                "type": binder.get("type"),
            })
    return {
        "name": record.get("name"),
        "module": record.get("module"),
        "premises": premises,
        "binders": binders,
        "signature": record.get("signature"),
        "conclusion": record.get("conclusion"),
        "src_file": record.get("src_file"),
        "range": record.get("range"),
        "kind": record.get("kind"),
        "axioms": record.get("axioms", []),
    }


def load_capture_bounded(path: Path) -> dict[str, Any]:
    metadata: dict[str, Any] = {}
    declarations: list[dict[str, Any]] = []
    with _open_text(path) as stream:
        reader = TextReader(stream)
        reader.expect("{")
        while True:
            reader.skip_ws()
            if reader.peek() == "}":
                reader.pos += 1
                break
            key = reader.value()
            reader.expect(":")
            if key == "declarations":
                for record in reader.array_values():
                    if not isinstance(record, dict):
                        raise ValueError("capture declaration is not an object")
                    declarations.append(_slim_capture_record(record))
            elif key in {"schema_version", "generated_from", "source_repository", "source_revision", "capture_projection", "errors"}:
                metadata[key] = reader.value()
            else:
                reader.skip_value()
            reader.skip_ws()
            delimiter = reader.peek()
            if delimiter == ",":
                reader.pos += 1
                continue
            if delimiter == "}":
                reader.pos += 1
                break
            raise ValueError(f"expected capture object delimiter, got {delimiter!r}")
    if metadata.get("errors"):
        raise SystemExit(f"capture reports extraction errors: {metadata['errors'][:3]}")
    if metadata.get("capture_projection", {}).get("premises_complete") is not True:
        raise SystemExit("capture does not declare complete premise coverage")
    metadata["declarations"] = declarations
    return metadata


def _stream_array(reader: TextReader, callback) -> None:
    reader.expect("[")
    while True:
        reader.skip_ws()
        delimiter = reader.peek()
        if delimiter == "]":
            reader.pos += 1
            return
        callback(reader.value())
        reader.skip_ws()
        delimiter = reader.peek()
        if delimiter == ",":
            reader.pos += 1
            continue
        if delimiter == "]":
            reader.pos += 1
            return
        raise ValueError(f"expected streamed array delimiter, got {delimiter!r}")


def _read_trace_record(reader: TextReader, local_records: set[str]) -> dict[str, Any]:
    """Read one record while discarding its unneeded tree and large arrays."""
    summary: dict[str, Any] = {
        "application_records": [],
        "reference_records": [],
        "application_count": 0,
        "reference_count": 0,
        "structural_only_application_count": 0,
        "exact_context_application_count": 0,
        "proof_application_count": 0,
        "data_application_count": 0,
        "proof_application_samples": [],
        "data_application_samples": [],
        "type_only_reference_count": 0,
        "type_only_reference_samples": [],
        "proof_reference_count": 0,
        "proof_reference_samples": [],
        "type_only_names": set(),
        "proof_statement_heads": set(),
        "local_assumption_head_counts": defaultdict(int),
        "data_head_promoted": set(),
        "swapped_candidate": None,
        "local_application_targets": defaultdict(list),
        "local_reference_targets": defaultdict(list),
        "local_assumption_application_count": 0,
        "local_data_application_count": 0,
        "shape_errors": [],
    }

    def on_application(application: Any) -> None:
        source_name = summary.get("declaration")
        if not isinstance(application, dict):
            summary["shape_errors"].append(f"{source_name}: application is not an object")
            return
        summary["application_count"] += 1
        if application.get("detail_status") == "structural_only_external":
            summary["structural_only_application_count"] += 1
        if application.get("detail_status") == "exact_context":
            summary["exact_context_application_count"] += 1
        summary["shape_errors"].extend(
            f"{source_name} {application.get('path')}: {message}"
            for message in _application_shape_errors(application)
        )
        if _is_proof_application(application):
            summary["proof_application_count"] += 1
            if len(summary["proof_application_samples"]) < 16:
                summary["proof_application_samples"].append(application)
            if summary["swapped_candidate"] is None and len(application.get("arguments", [])) >= 2:
                summary["swapped_candidate"] = application
            if application.get("application_role") == "local_assumption_application":
                summary["local_assumption_application_count"] += 1
            head_name = _app_head_name(application)
            if isinstance(head_name, str) and ".Statements." in head_name:
                summary["proof_statement_heads"].add(head_name)
            target_local = _local_name(head_name) if head_name else None
            if target_local in local_records:
                # The extractor serializes application_records before the
                # declaration field.  Store paths first and qualify them once
                # the record object has been completely read.
                summary["local_application_targets"][target_local].append(
                    application.get("path", "")
                )
        if _is_data_application(application):
            summary["data_application_count"] += 1
            if len(summary["data_application_samples"]) < 16:
                summary["data_application_samples"].append(application)
            if application.get("application_role") == "local_assumption_application":
                summary["local_data_application_count"] += 1
        if application.get("application_role") == "local_assumption_application":
            head_name = _app_head_name(application)
            if isinstance(head_name, str):
                summary["local_assumption_head_counts"][head_name] += 1
                if head_name in {"w", "g"} and application.get("proof_relevance") == "proof_term":
                    summary["data_head_promoted"].add(head_name)

    def on_reference(reference: Any) -> None:
        source_name = summary.get("declaration")
        if not isinstance(reference, dict):
            return
        summary["reference_count"] += 1
        role = reference.get("role")
        if role == "type_only_reference":
            summary["type_only_reference_count"] += 1
            name = reference.get("name")
            if isinstance(name, str) and ".Statements." in name:
                summary["type_only_names"].add(name)
            if len(summary["type_only_reference_samples"]) < 16:
                summary["type_only_reference_samples"].append(reference)
        if role == "proof_constant_reference":
            summary["proof_reference_count"] += 1
            if len(summary["proof_reference_samples"]) < 16:
                summary["proof_reference_samples"].append(reference)
        if reference.get("context") != "proof":
            return
        if reference.get("declaration_role") not in {"theorem", "constructor", "opaque", "axiom"}:
            return
        name = reference.get("name")
        target_local = _local_name(name) if isinstance(name, str) else None
        if target_local in local_records:
            summary["local_reference_targets"][target_local].append(
                reference.get("path", "")
            )

    reader.expect("{")
    while True:
        reader.skip_ws()
        delimiter = reader.peek()
        if delimiter == "}":
            reader.pos += 1
            break
        key = reader.value()
        reader.expect(":")
        if key == "application_records":
            _stream_array(reader, on_application)
        elif key == "reference_records":
            _stream_array(reader, on_reference)
        elif key in {"declaration", "status", "kind", "fuel", "tree_status", "omitted_external_reference_count", "omitted_structural_application_count"}:
            summary[key] = reader.value()
        else:
            # The compact full-cone trace has no tree payload, but this also
            # handles a non-null tree without retaining it.
            reader.skip_value()
        reader.skip_ws()
        delimiter = reader.peek()
        if delimiter == ",":
            reader.pos += 1
            continue
        if delimiter == "}":
            reader.pos += 1
            break
        raise ValueError(f"expected trace record delimiter, got {delimiter!r}")

    source_name = summary.get("declaration")
    if not isinstance(source_name, str):
        source_name = "<unknown>"
    summary["local_application_targets"] = {
        key: [_trace_record_id(source_name, path) for path in value]
        for key, value in summary["local_application_targets"].items()
    }
    summary["local_reference_targets"] = {
        key: [_trace_record_id(source_name, path) for path in value]
        for key, value in summary["local_reference_targets"].items()
    }
    summary["type_only_names"] = sorted(summary["type_only_names"])
    summary["proof_statement_heads"] = sorted(summary["proof_statement_heads"])
    summary["local_assumption_head_counts"] = dict(summary["local_assumption_head_counts"])
    summary["data_head_promoted"] = sorted(summary["data_head_promoted"])
    summary["application_samples"] = summary["proof_application_samples"][:8]
    summary["data_application_sample"] = summary["data_application_samples"][:8]
    return summary


def _iter_trace_summaries(path: Path, local_records: set[str]) -> tuple[dict[str, Any], Iterator[dict[str, Any]]]:
    """Stream the trace envelope and one processed record at a time."""
    stream = _open_text(path)
    reader = TextReader(stream)
    reader.expect("{")
    header: dict[str, Any] = {}
    while True:
        reader.skip_ws()
        delimiter = reader.peek()
        if delimiter == "}":
            reader.pos += 1
            stream.close()
            raise ValueError("trace does not contain a records array")
        key = reader.value()
        reader.expect(":")
        if key == "records":
            break
        if key in {"schema_version", "generated_from", "toolchain", "selected_declarations", "capture_policy"}:
            header[key] = reader.value()
        else:
            reader.skip_value()
        reader.skip_ws()
        delimiter = reader.peek()
        if delimiter == ",":
            reader.pos += 1
            continue
        if delimiter == "}":
            reader.pos += 1
            stream.close()
            raise ValueError("trace does not contain a records array")
        raise ValueError(f"expected trace header delimiter, got {delimiter!r}")

    def summaries() -> Iterator[dict[str, Any]]:
        try:
            reader.expect("[")
            while True:
                reader.skip_ws()
                delimiter = reader.peek()
                if delimiter == "]":
                    reader.pos += 1
                    _finish_trace_document(reader)
                    return
                yield _read_trace_record(reader, local_records)
                reader.skip_ws()
                delimiter = reader.peek()
                if delimiter == ",":
                    reader.pos += 1
                    continue
                if delimiter == "]":
                    reader.pos += 1
                    _finish_trace_document(reader)
                    return
                raise ValueError(f"expected records array delimiter, got {delimiter!r}")
        finally:
            stream.close()

    return header, summaries()


def _finish_trace_document(reader: TextReader) -> None:
    """Require the records array to close its object and reach EOF."""
    reader.skip_ws()
    if reader.peek() != "}":
        raise ValueError("trace records array is not followed by its enclosing object close")
    reader.pos += 1
    reader.skip_ws()
    if reader.peek() is not None:
        raise ValueError("trace contains trailing data after its enclosing object")


def _summarize_trace(
    path: Path,
    records: dict[str, dict[str, Any]],
    edge_rows: dict[str, list[dict[str, Any]]],
    spool: Path,
) -> dict[str, Any]:
    local_records = set(records)
    local_edge_keys = {
        (source, row["target"], row["edge_type"])
        for source, rows in edge_rows.items()
        for row in rows
    }
    header, record_iter = _iter_trace_summaries(path, local_records)
    selected_names: list[str] = []
    errors: list[str] = []
    source_to_component: dict[str, str] = {}
    target_sources: dict[str, list[dict[str, Any]]] = defaultdict(list)
    contracts: list[dict[str, Any]] = []
    trace_coverage: list[dict[str, Any]] = []

    with spool.open("w", encoding="utf-8") as stream:
        for raw in record_iter:
            source_name = raw.get("declaration")
            if not isinstance(source_name, str):
                errors.append("selected trace record has no declaration name")
                continue
            selected_names.append(source_name)
            source_local = _local_name(source_name)
            source_record = records.get(source_local)
            if source_record is None:
                errors.append(f"missing captured source declaration for {source_local}")
                continue
            component_id = _trace_component_id(source_name)
            source_to_component[source_local] = component_id
            local_target_names = sorted(
                set(raw["local_application_targets"]) | set(raw["local_reference_targets"])
            )
            for target_local in local_target_names:
                target_sources[target_local].append({
                    "source": source_local,
                    "application_record_ids": raw["local_application_targets"].get(target_local, []),
                    "proof_reference_record_ids": raw["local_reference_targets"].get(target_local, []),
                })
            compact = {
                "source_name": source_name,
                "source_local": source_local,
                "component_id": component_id,
                "status": raw.get("status"),
                "kind": raw.get("kind"),
                "fuel": raw.get("fuel"),
                "tree_status": raw.get("tree_status"),
                "omitted_external_reference_count": raw.get("omitted_external_reference_count", 0),
                "omitted_structural_application_count": raw.get("omitted_structural_application_count", 0),
                "application_count": raw["application_count"],
                "structural_only_application_count": raw["structural_only_application_count"],
                "exact_context_application_count": raw["exact_context_application_count"],
                "proof_application_count": raw["proof_application_count"],
                "data_application_count": raw["data_application_count"],
                "proof_application_samples": raw["proof_application_samples"],
                "data_application_samples": raw["data_application_samples"],
                "local_assumption_application_count": raw["local_assumption_application_count"],
                "local_data_application_count": raw["local_data_application_count"],
                "type_only_reference_count": raw["type_only_reference_count"],
                "type_only_reference_samples": raw["type_only_reference_samples"],
                "proof_reference_count": raw["proof_reference_count"],
                "proof_reference_samples": raw["proof_reference_samples"],
                "local_target_names": local_target_names,
                "local_application_targets": raw["local_application_targets"],
                "local_reference_targets": raw["local_reference_targets"],
                "shape_errors": raw["shape_errors"],
            }
            json.dump(compact, stream, ensure_ascii=False, separators=(",", ":"))
            stream.write("\n")
            contracts.append({
                "trace_declaration": source_name,
                "component": component_id,
                "application_count": raw["application_count"],
                "exact_context_application_count": raw["exact_context_application_count"],
                "relevant_application_count": raw["proof_application_count"],
                "proof_application_count": raw["proof_application_count"],
                "data_application_count": raw["data_application_count"],
                "proof_application_sample_count": min(raw["proof_application_count"], 16),
                "data_application_sample_count": min(raw["data_application_count"], 16),
                "type_only_reference_count": raw["type_only_reference_count"],
                "local_target_declarations": local_target_names,
                "shape_error_count": len(raw["shape_errors"]),
            })
            trace_coverage.append({
                "declaration": source_name,
                "status": raw.get("status"),
                "kind": raw.get("kind"),
                "fuel": raw.get("fuel"),
                "component_ids": [component_id],
                "application_count": raw["application_count"],
                "structural_only_application_count": raw["structural_only_application_count"],
                "exact_context_application_count": raw["exact_context_application_count"],
                "relevant_application_count": raw["proof_application_count"],
                "proof_application_count": raw["proof_application_count"],
                "data_application_count": raw["data_application_count"],
                "proof_application_sample_count": min(raw["proof_application_count"], 16),
                "data_application_sample_count": min(raw["data_application_count"], 16),
                "type_only_reference_count": raw["type_only_reference_count"],
                "proof_constant_reference_count": raw["proof_reference_count"],
                "local_target_declarations": local_target_names,
                "truncated_node_present": False,
                "tree_status": raw.get("tree_status"),
                "omitted_structural_application_count": raw.get("omitted_structural_application_count", 0),
                "omitted_external_reference_count": raw.get("omitted_external_reference_count", 0),
            })

    return {
        "header": header,
        "selected_names": selected_names,
        "errors": errors,
        "source_to_component": source_to_component,
        "target_sources": target_sources,
        "contracts": contracts,
        "trace_coverage": trace_coverage,
    }


def _read_spool(spool: Path) -> Iterator[dict[str, Any]]:
    with spool.open("r", encoding="utf-8") as stream:
        for line in stream:
            if line.strip():
                yield json.loads(line)


def _source_component(summary: dict[str, Any], records: dict[str, dict[str, Any]]) -> dict[str, Any]:
    source_name = summary["source_name"]
    source_local = summary["source_local"]
    source_record = records[source_local]
    local_target_names = summary["local_target_names"]
    proof_samples = summary["proof_application_samples"]
    data_samples = summary["data_application_samples"]
    return {
        "id": summary["component_id"],
        "title": f"Structural application spine: {source_name}",
        "kind": "trace_backed_subargument",
        "surface": "solution",
        "role": "trace_backed_subargument",
        "formal_status": "trace_backed_structural_application_records",
        "evidence_status": "selected_elaborated_application_records_and_capture_metadata",
        "interpretation_status": "authored_pending_review",
        "declarations": [source_local],
        "summary": (
            "Algorithmically derived from every retained application spine in the selected "
            "elaborated declaration. Exact argument/type/context records are retained for "
            "local proof applications and assumptions; external applications remain explicitly "
            "structural-only rather than being silently dropped."
        ),
        "generated_from": {
            "algorithm": "complete reachable Lean trace records -> proof/data application records and references -> local target boundaries",
            "trace_declaration": source_name,
            "trace_artifact": "data/proof-trace.json.gz",
            "source_selection": "complete reachable local proof-cone declarations emitted by ExtractProofTrace.lean",
        },
        "interface": {
            "source_declaration": source_local,
            "target_declarations": local_target_names,
            "source_interface": interface(source_record),
            "target_interfaces": [interface(records[name]) for name in local_target_names],
        },
        "formal_interfaces": [interface(source_record)],
        "formal_interface_status": "checked_against_elaborated_capture",
        "proof_trace_evidence": {
            "trace_status": summary.get("status"),
            "fuel": summary.get("fuel"),
            "application_count": summary["application_count"],
            "structural_only_application_count": summary["structural_only_application_count"],
            "exact_context_application_count": summary["exact_context_application_count"],
            "proof_application_count": summary["proof_application_count"],
            "data_application_count": summary["data_application_count"],
            "proof_application_sample_count": min(summary["proof_application_count"], 16),
            "data_application_sample_count": min(summary["data_application_count"], 16),
            "subterm_record_ids": [
                _trace_record_id(source_name, application.get("path", ""))
                for application in proof_samples[:16]
            ],
            "application_records": proof_samples[:16],
            "application_samples": proof_samples[:8],
            "data_application_records": data_samples[:16],
            "data_application_samples": data_samples[:8],
            "local_assumption_application_count": summary["local_assumption_application_count"],
            "local_data_application_count": summary["local_data_application_count"],
            "type_only_reference_count": summary["type_only_reference_count"],
            "type_only_reference_records": summary["type_only_reference_samples"][:16],
            "type_only_reference_sample": summary["type_only_reference_samples"][:16],
            "proof_constant_reference_count": summary["proof_reference_count"],
            "proof_constant_reference_sample": summary["proof_reference_samples"][:16],
            "local_target_application_counts": {
                target: len(summary["local_application_targets"].get(target, []))
                for target in local_target_names
            },
            "local_target_proof_reference_counts": {
                target: len(summary["local_reference_targets"].get(target, []))
                for target in local_target_names
            },
        },
        "validation": {
            "source_trace_present": True,
            "all_application_records_structurally_valid": not summary["shape_errors"],
            "ordered_argument_mappings_checked": summary["exact_context_application_count"],
            "proof_classification_checked": all(
                _is_proof_application(application) for application in proof_samples
            ),
            "data_applications_retained_separately": all(
                not _is_proof_application(application) for application in data_samples
            ),
            "type_only_references_are_not_application_targets": True,
            "local_target_components_deferred_until_target_pass": True,
        },
        "limits": [
            "Structural application records are compiler evidence, not a claim that an opaque theorem body has been inlined.",
            "The full trace retains exact proof/data applications and local references; the component stores bounded samples and exact counts.",
            "External application records intentionally carry a structural-only status; exact type/context detail is retained for local proof applications and data applications omit local contexts by policy.",
            "The short mathematical reading remains authored and requires human review.",
        ],
    }


def _target_components(
    target_sources: dict[str, list[dict[str, Any]]],
    source_to_component: dict[str, str],
    records: dict[str, dict[str, Any]],
    errors: list[str],
) -> tuple[dict[str, str], list[dict[str, Any]]]:
    target_component_ids: dict[str, str] = {}
    components: list[dict[str, Any]] = []
    for target_local in sorted(target_sources):
        if target_local in source_to_component:
            target_component_ids[target_local] = source_to_component[target_local]
            continue
        target_record = records.get(target_local)
        if target_record is None:
            errors.append(f"missing discovered target declaration {target_local}")
            continue
        target_id = _trace_target_component_id(target_local.removeprefix("solution::"))
        target_component_ids[target_local] = target_id
        source_evidence = target_sources[target_local]
        components.append({
            "id": target_id,
            "title": f"Trace target interface: {target_local.removeprefix('solution::')}",
            "kind": "trace_application_target",
            "surface": "solution",
            "role": "trace_application_target",
            "formal_status": "compiler_linked_target_interface",
            "evidence_status": "discovered_from_exact_application_heads_or_proof_references",
            "interpretation_status": "compiler_derived_interface_pending_mathematical_review",
            "declarations": [target_local],
            "summary": (
                "A local declaration discovered as the head of a retained proof application "
                "or as a proof-context constant reference. It is a target interface, not a "
                "new authored subargument claim."
            ),
            "generated_from": {
                "algorithm": "union of local theorem/opaque application heads and local proof references",
                "source_trace_declarations": [item["source"] for item in source_evidence],
            },
            "formal_interfaces": [interface(target_record)],
            "formal_interface_status": "checked_against_elaborated_capture",
            "evidence": source_evidence,
            "limits": [
                "This target node records a compiler-visible interface boundary; it does not assert a human mathematical grouping.",
            ],
        })
    return target_component_ids, components


def _bounded_relations(
    spool: Path,
    source_to_component: dict[str, str],
    target_component_ids: dict[str, str],
    local_edge_keys: set[tuple[str, str, str]],
) -> list[dict[str, Any]]:
    relation_buckets: dict[tuple[str, str], dict[str, Any]] = {}
    for summary in _read_spool(spool):
        source_component = source_to_component[summary["source_local"]]
        for target_local in summary["local_target_names"]:
            target_component = target_component_ids.get(target_local)
            if target_component is None or target_component == source_component:
                continue
            key = (source_component, target_component)
            bucket = relation_buckets.setdefault(key, {
                "source": source_component,
                "target": target_component,
                "source_declaration": summary["source_local"],
                "target_declaration": target_local,
                "application_record_ids": [],
                "proof_reference_record_ids": [],
                "capture_edge_present": (
                    summary["source_local"], target_local, "USES_IN_PROOF"
                ) in local_edge_keys,
            })
            bucket["application_record_ids"].extend(
                summary["local_application_targets"].get(target_local, [])
            )
            bucket["proof_reference_record_ids"].extend(
                summary["local_reference_targets"].get(target_local, [])
            )
    relations: list[dict[str, Any]] = []
    for bucket in sorted(relation_buckets.values(), key=lambda item: (item["source"], item["target"])):
        edge_present = bucket["capture_edge_present"]
        relation_type = (
            "trace_application_boundary" if bucket["application_record_ids"]
            else "trace_proof_reference_boundary"
        )
        relations.append({
            "source": bucket["source"],
            "target": bucket["target"],
            "type": relation_type,
            "evidence_kind": "compiler" if edge_present else "trace",
            "evidence": {
                "source_declaration": bucket["source_declaration"],
                "target_declaration": bucket["target_declaration"],
                "edge_type": "USES_IN_PROOF",
                "capture_edge_present": edge_present,
                "application_record_ids": sorted(set(bucket["application_record_ids"])),
                "proof_reference_record_ids": sorted(set(bucket["proof_reference_record_ids"])),
                "derivation": (
                    "exact-context application head cross-checked against captured USES_IN_PROOF"
                    if edge_present else
                    "exact trace application/reference retained without upgrading an absent capture row"
                ),
            },
            "note": (
                "Compiler edge and trace edge are kept separate."
                if edge_present else
                "Trace evidence is retained without upgrading an absent capture row to a compiler edge."
            ),
        })
    return relations


def _write_array(stream, values: Iterator[dict[str, Any]]) -> None:
    stream.write("[")
    first = True
    for value in values:
        if not first:
            stream.write(",")
        json.dump(value, stream, ensure_ascii=False, indent=2)
        first = False
    stream.write("]")


def _write_bounded_output(
    path: Path,
    *,
    capture: dict[str, Any],
    roles: dict[str, Any],
    source_revision: str,
    proof_trace_path: Path,
    trace_result: dict[str, Any],
    generated: list[dict[str, Any]],
    generated_relations: list[dict[str, Any]],
    role_audit: dict[str, Any],
    proof_audit: dict[str, Any],
    spool: Path,
    target_nodes: list[dict[str, Any]],
    relations: list[dict[str, Any]],
    audit: dict[str, Any],
) -> None:
    header = trace_result["header"]
    prefix = {
        "schema_version": 2,
        "source_repository": capture.get("source_repository"),
        "source_revision": source_revision,
        "capture_manifest": "capture-manifest.json",
        "status_vocabulary": {
            **roles.get("status_vocabulary", {}),
            "compiler_generated_proof_region": (
                "membership and boundary relations are derived from captured elaborated proof edges; "
                "they are source-module regions, not authored mathematical subarguments."
            ),
            "trace_backed_subargument": (
                "the selected declaration's application-spine records are checked against exact captured "
                "interfaces; local target links and type-only references remain separately labelled, and "
                "opaque theorem bodies remain opaque."
            ),
        },
        "generation": {
            "script": "xylem-plugin/capture/percolation/derive_proof_components.py",
            "mode": "bounded_two_pass",
            "role_labels_input": "data/components.json",
            "proof_trace_input": "data/proof-trace.json.gz",
            "root": ROOT_DECL,
            "proof_trace_selected_declarations": len(trace_result["selected_names"]),
        },
        "interface_audit": role_audit,
        "proof_decomposition": proof_audit,
        "subargument_decomposition": audit,
        "proof_trace_summary": {
            "status": "captured",
            "selected": header.get("selected_declarations", trace_result["selected_names"]),
            "artifact_schema": header.get("schema_version"),
            "capture_policy": header.get("capture_policy", {}),
            "note": (
                "The compact full-cone artifact is the complete evidence source for retained "
                "proof/data applications and references; component nodes store bounded samples. "
                "Full Expr trees for reviewed boundary declarations are retained in the separate "
                "proof-trace-boundaries artifact."
            ),
        },
    }
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as stream:
        stream.write("{\n")
        first_member = True
        for key, value in prefix.items():
            if not first_member:
                stream.write(",\n")
            stream.write(f"  {json.dumps(key)}: ")
            json.dump(value, stream, ensure_ascii=False, indent=2)
            first_member = False
        stream.write(",\n  \"components\": [")
        first_component = True
        component_iter = (
            iter(roles.get("components", [])),
            iter(generated),
            (value for value in (_source_component(item, capture["_record_map"]) for item in _read_spool(spool))),
            iter(target_nodes),
        )
        for group in component_iter:
            for component in group:
                if not first_component:
                    stream.write(",")
                json.dump(component, stream, ensure_ascii=False, indent=2)
                first_component = False
        stream.write("],\n  \"relations\": [")
        first_relation = True
        for group in (roles.get("relations", []), generated_relations, relations):
            for relation in group:
                if not first_relation:
                    stream.write(",")
                json.dump(relation, stream, ensure_ascii=False, indent=2)
                first_relation = False
        stream.write("]\n}\n")


def run_bounded(args) -> int:
    capture = load_capture_bounded(args.capture)
    capture["_record_map"] = record_map(capture)
    records = capture["_record_map"]
    roles = load_json(args.roles)
    role_audit = validate_roles(roles, records)
    graph, edge_rows = __import__("derive_proof_components").proof_graph(records)
    generated, generated_relations, proof_audit = generated_components(records, graph, edge_rows)
    local_edge_keys = {
        (source, row["target"], row["edge_type"])
        for source, rows in edge_rows.items()
        for row in rows
    }

    with tempfile.TemporaryDirectory(prefix="xylem-bounded-components-") as temporary:
        spool = Path(temporary) / "trace-summaries.jsonl"
        trace_result = _summarize_trace(args.proof_trace, records, edge_rows, spool)
        errors = trace_result["errors"]
        target_component_ids, target_nodes = _target_components(
            trace_result["target_sources"], trace_result["source_to_component"], records, errors
        )
        relations = _bounded_relations(
            spool,
            trace_result["source_to_component"],
            target_component_ids,
            local_edge_keys,
        )
        selected_header = trace_result["header"].get("selected_declarations")
        if selected_header is not None and selected_header != trace_result["selected_names"]:
            errors.append("trace selected declaration order differs from streamed record order")
        accounted_sources = [item["trace_declaration"] for item in trace_result["contracts"]]
        if sorted(trace_result["selected_names"]) != sorted(accounted_sources):
            errors.append("not every selected trace declaration has an algorithmic component")
        unexpected_no_value = [
            item for item in trace_result["trace_coverage"]
            if item.get("status") == "no_value" and item.get("kind") not in LEGITIMATE_NO_VALUE_KINDS
        ]
        unavailable = [
            item for item in trace_result["trace_coverage"]
            if item.get("status") not in {"captured", "no_value"} or item in unexpected_no_value
        ]
        all_structural_traces_captured = all(
            item.get("status") in {"captured", "no_value"}
            and not item.get("truncated_node_present")
            and (
                item.get("status") == "no_value"
                or item.get("tree_status") == "omitted_compact_full_cone"
            )
            for item in trace_result["trace_coverage"]
        ) and len(trace_result["trace_coverage"]) == len(trace_result["selected_names"]) and not unavailable
        audit = {
            "status": "PASS" if not errors and all_structural_traces_captured else "FAIL",
            "algorithm": (
                "complete reachable Lean Expr records -> exact proof/data application mappings and "
                "explicit structural-only accounting -> discovered target interfaces"
            ),
            "selected_trace_count": len(trace_result["selected_names"]),
            "catalog_component_count": len(trace_result["source_to_component"]) + len(target_nodes),
            "source_component_count": len(trace_result["source_to_component"]),
            "target_component_count": len(target_nodes),
            "relation_count": len(relations),
            "compiler_relation_count": sum(item["evidence_kind"] == "compiler" for item in relations),
            "trace_only_relation_count": sum(item["evidence_kind"] == "trace" for item in relations),
            "selected_traces_accounted": sorted(trace_result["selected_names"]) == sorted(accounted_sources),
            "all_target_application_records_structurally_valid": not errors,
            "all_structural_traces_captured": all_structural_traces_captured,
            "explicit_no_value_count": sum(item.get("status") == "no_value" for item in trace_result["trace_coverage"]),
            "legitimate_no_value_kinds": sorted(LEGITIMATE_NO_VALUE_KINDS),
            "unexpected_no_value_records": unexpected_no_value,
            "unavailable_trace_records": unavailable,
            "type_only_references_are_not_proof_applications": True,
            "trace_coverage": trace_result["trace_coverage"],
            "contracts": trace_result["contracts"],
            "opaque_boundaries": [
                "The compact full-cone trace preserves exact retained proof/data application records and local references, but omits repeated external structural applications and external references with per-record counts.",
                "The separate boundary artifact retains full Expr trees for the reviewed boundary declarations; opaque theorem bodies are not recursively serialized.",
                "Exact types and local contexts are checked for local proof applications; data applications are retained as data evidence with local contexts explicitly omitted.",
                "A trace-only local boundary is never promoted to a compiler relation when the merged capture has no corresponding USES_IN_PROOF row.",
            ],
            "errors": errors,
        }
        if audit["status"] != "PASS":
            raise SystemExit("bounded trace-backed subargument audit failed:\n" + "\n".join(errors))
        _write_bounded_output(
            args.output,
            capture=capture,
            roles=roles,
            source_revision=args.source_revision,
            proof_trace_path=args.proof_trace,
            trace_result=trace_result,
            generated=generated,
            generated_relations=generated_relations,
            role_audit=role_audit,
            proof_audit=proof_audit,
            spool=spool,
            target_nodes=target_nodes,
            relations=relations,
            audit=audit,
        )
        args.audit_output.parent.mkdir(parents=True, exist_ok=True)
        args.audit_output.write_text(
            json.dumps({
                "schema_version": 1,
                "source_revision": args.source_revision,
                "component_manifest": "data/components-generated.json",
                "role_interface_audit": role_audit,
                "proof_decomposition": proof_audit,
                "subargument_decomposition": audit,
                "empty_dependency_classification": {
                    "status": "valid_zero_dependency_shapes_checked_separately",
                    "note": "See the capture audit for the complete 32-record list and source ranges.",
                },
            }, indent=2, ensure_ascii=False) + "\n",
            encoding="utf-8",
        )
    print(json.dumps({
        "status": "PASS",
        "components": audit["catalog_component_count"] + len(roles.get("components", [])) + len(generated),
        "relations": audit["relation_count"] + len(roles.get("relations", [])) + len(generated_relations),
        "proof_decomposition": proof_audit,
        "subargument_decomposition": audit,
        "role_interface_audit": role_audit,
    }, indent=2, ensure_ascii=False))
    return 0
