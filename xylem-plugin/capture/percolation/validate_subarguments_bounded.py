#!/usr/bin/env python3
"""Memory-bounded validator for the streamed component derivation."""

from __future__ import annotations

import copy
import json
from collections import Counter
from pathlib import Path
from typing import Any

from derive_proof_components_bounded import TextReader, _iter_trace_summaries, _stream_array
from validate_subarguments import (
    LEGITIMATE_NO_VALUE_KINDS,
    _is_proof_record,
    application_shape_errors,
    record_id,
)


def _stream_component_document(path: Path, on_component, on_relation) -> dict[str, Any]:
    metadata: dict[str, Any] = {}
    with path.open("r", encoding="utf-8") as stream:
        reader = TextReader(stream, chunk_size=4 * 1024 * 1024)
        reader.expect("{")
        while True:
            reader.skip_ws()
            delimiter = reader.peek()
            if delimiter == "}":
                reader.pos += 1
                return metadata
            key = reader.value()
            reader.expect(":")
            if key == "components":
                _stream_array(reader, on_component)
            elif key == "relations":
                _stream_array(reader, on_relation)
            elif key == "subargument_decomposition":
                value = reader.value()
                if isinstance(value, dict):
                    metadata["subargument_decomposition_status"] = value.get("status")
            else:
                reader.skip_value()
            reader.skip_ws()
            delimiter = reader.peek()
            if delimiter == ",":
                reader.pos += 1
                continue
            if delimiter == "}":
                reader.pos += 1
                return metadata
            raise ValueError(f"invalid component document delimiter {delimiter!r}")


def run_bounded(args) -> int:
    trace_header, trace_iter = _iter_trace_summaries(args.proof_trace, set())
    # The trace iterator's local-target classification only needs the set of
    # captured names for the derivation.  The validator itself can still run
    # with an empty set because it validates application/reference evidence.
    errors: list[str] = []
    source_count = 0
    target_count = 0
    trace_seen = 0
    trace_application_count = 0
    trace_reference_count = 0
    exact_context_count = 0
    structural_only_count = 0
    proof_count = 0
    data_count = 0
    omitted_structural_count = 0
    omitted_external_count = 0
    referenced_exact_subterm_count = 0
    compiler_relation_count = 0
    trace_only_relation_count = 0
    swapped_candidate: dict[str, Any] | None = None
    type_only_names: set[str] = set()
    proof_statement_heads: set[str] = set()
    data_head_counts: Counter[str] = Counter()
    data_head_promoted: set[str] = set()
    local_proof_count = 0

    def validate_component(component: Any) -> None:
        nonlocal source_count, trace_seen, trace_application_count, trace_reference_count
        nonlocal exact_context_count, structural_only_count, proof_count, data_count
        nonlocal omitted_structural_count, omitted_external_count, referenced_exact_subterm_count
        nonlocal swapped_candidate, local_proof_count
        nonlocal type_only_names, proof_statement_heads, data_head_counts, data_head_promoted
        if not isinstance(component, dict):
            errors.append("component is not an object")
            return
        kind = component.get("kind")
        if kind == "trace_application_target":
            target_count += 1
            return
        if kind != "trace_backed_subargument":
            return
        source_count += 1
        generated = component.get("generated_from") or {}
        source = generated.get("trace_declaration")
        if not isinstance(source, str):
            errors.append(f"source component {component.get('id')}: missing trace declaration")
            return
        try:
            summary = next(trace_iter)
        except StopIteration:
            errors.append(f"component {component.get('id')}: trace ended before {source}")
            return
        trace_seen += 1
        if summary.get("declaration") != source:
            errors.append(
                f"component {component.get('id')}: trace order mismatch, expected {source!r}, "
                f"got {summary.get('declaration')!r}"
            )
        if summary.get("status") not in {"captured", "no_value"}:
            errors.append(f"{component.get('id')}: trace unavailable")
        if summary.get("status") == "no_value" and summary.get("kind") not in LEGITIMATE_NO_VALUE_KINDS:
            errors.append(f"{component.get('id')}: unexpected no_value kind {summary.get('kind')!r}")
        if summary.get("status") == "captured" and summary.get("tree_status") != "omitted_compact_full_cone":
            errors.append(f"{component.get('id')}: compact tree policy is not recorded")
        evidence = component.get("proof_trace_evidence") or {}
        for key in (
            "application_count",
            "exact_context_application_count",
            "proof_application_count",
            "data_application_count",
            "structural_only_application_count",
        ):
            summary_key = key
            if evidence.get(key) != summary.get(summary_key):
                errors.append(
                    f"{component.get('id')}: {key} mismatch ({evidence.get(key)!r} != {summary.get(summary_key)!r})"
                )
        proof_samples = summary.get("proof_application_samples", [])
        data_samples = summary.get("data_application_samples", [])
        if evidence.get("application_records", []) != proof_samples[:16]:
            errors.append(f"{component.get('id')}: proof sample differs from trace")
        if evidence.get("data_application_records", []) != data_samples[:16]:
            errors.append(f"{component.get('id')}: data sample differs from trace")
        expected_ids = [record_id(source, app.get("path", "")) for app in proof_samples[:16]]
        if evidence.get("subterm_record_ids", []) != expected_ids:
            errors.append(f"{component.get('id')}: subterm IDs differ from trace")
        referenced_exact_subterm_count += len(evidence.get("subterm_record_ids", []))
        if evidence.get("proof_application_sample_count") != min(summary.get("proof_application_count", 0), 16):
            errors.append(f"{component.get('id')}: proof sample count mismatch")
        if evidence.get("data_application_sample_count") != min(summary.get("data_application_count", 0), 16):
            errors.append(f"{component.get('id')}: data sample count mismatch")
        for message in summary.get("shape_errors", []):
            errors.append(message)
        for application in proof_samples:
            if not _is_proof_record(application):
                errors.append(f"{component.get('id')}: non-proof sample promoted as proof")
        for application in data_samples:
            if _is_proof_record(application):
                errors.append(f"{component.get('id')}: proof sample duplicated as data")
        type_samples = summary.get("type_only_reference_samples", [])
        component_type_samples = evidence.get("type_only_reference_sample", [])
        if component_type_samples != type_samples[:16]:
            errors.append(f"{component.get('id')}: type-only reference sample differs from trace")
        for reference in component_type_samples:
            if reference.get("role") != "type_only_reference" or reference.get("context") != "type":
                errors.append(f"{component.get('id')}: misclassified type-only reference")
        trace_application_count += summary.get("application_count", 0)
        trace_reference_count += summary.get("reference_count", 0)
        exact_context_count += summary.get("exact_context_application_count", 0)
        structural_only_count += summary.get("structural_only_application_count", 0)
        proof_count += summary.get("proof_application_count", 0)
        data_count += summary.get("data_application_count", 0)
        omitted_structural_count += summary.get("omitted_structural_application_count", 0)
        omitted_external_count += summary.get("omitted_external_reference_count", 0)
        if swapped_candidate is None and summary.get("swapped_candidate") is not None:
            swapped_candidate = summary["swapped_candidate"]
        type_only_names.update(summary.get("type_only_names", []))
        proof_statement_heads.update(summary.get("proof_statement_heads", []))
        data_head_counts.update(summary.get("local_assumption_head_counts", {}))
        data_head_promoted.update(summary.get("data_head_promoted", []))
        local_proof_count += summary.get("local_assumption_application_count", 0)

    def validate_relation(relation: Any) -> None:
        nonlocal compiler_relation_count, trace_only_relation_count
        if not isinstance(relation, dict):
            errors.append("relation is not an object")
            return
        if relation.get("type") not in {"trace_application_boundary", "trace_proof_reference_boundary"}:
            return
        if relation.get("evidence_kind") == "compiler":
            compiler_relation_count += 1
        elif relation.get("evidence_kind") == "trace":
            trace_only_relation_count += 1

    metadata = _stream_component_document(args.components, validate_component, validate_relation)
    try:
        next(trace_iter)
        errors.append("trace has records without structural source components")
    except StopIteration:
        pass

    if metadata.get("subargument_decomposition_status") != "PASS":
        errors.append("generated subargument decomposition audit is not PASS")
    if trace_header.get("selected_declarations") is not None and trace_seen != len(trace_header["selected_declarations"]):
        errors.append("trace record count does not match selected declaration list")

    swapped_test = {"status": "FAIL", "reason": "no checked application with two arguments"}
    if isinstance(swapped_candidate, dict):
        mutated = copy.deepcopy(swapped_candidate)
        mutated["arguments"][0], mutated["arguments"][1] = mutated["arguments"][1], mutated["arguments"][0]
        swapped_errors = application_shape_errors(mutated)
        swapped_test = {
            "status": "PASS" if swapped_errors else "FAIL",
            "candidate": swapped_candidate.get("path"),
            "mutated_error_sample": swapped_errors[:2],
            "reason": "swapping ordered argument records must be rejected",
        }
    expected_type_names = {
        name for name in type_only_names
        if name.endswith("AdditiveGluing") or name.endswith("NearOneGluing")
    }
    type_only_test = {
        "status": "PASS" if expected_type_names and not expected_type_names.intersection(proof_statement_heads) else "FAIL",
        "type_only_statement_constants": sorted(expected_type_names),
        "proof_application_statement_heads": sorted(proof_statement_heads),
        "false_positive_overlap": sorted(expected_type_names.intersection(proof_statement_heads)),
        "reason": "statement constants used only in types must not be treated as proof applications",
    }
    observed_data_heads = sorted(name for name in ("w", "g") if data_head_counts[name])
    classification_test = {
        "status": "PASS" if observed_data_heads == ["g", "w"] and local_proof_count and not data_head_promoted else "FAIL",
        "data_heads_observed": observed_data_heads,
        "data_head_application_counts": {name: data_head_counts[name] for name in ("w", "g")},
        "data_heads_promoted_as_proof": sorted(data_head_promoted),
        "local_proof_application_count": local_proof_count,
        "reason": "w/e and g/e applications must remain data evidence; local proposition applications remain proof evidence",
    }
    for name, test in {
        "swapped arguments": swapped_test,
        "type-only false positive": type_only_test,
        "proof/data classification": classification_test,
    }.items():
        if test["status"] != "PASS":
            errors.append(f"negative {name} test did not pass")

    client_text = args.client.read_text(encoding="utf-8")
    for marker in (
        "CSHInterface",
        "additiveGluingStep",
        "theorem6FromSlabCritical",
        "reassembledPublicEndpoint",
        "cshAssumptionApplication",
        "reassembledNamedChain",
        "cshHolds_of_unfold",
    ):
        if marker not in client_text:
            errors.append(f"Lean client is missing marker {marker}")

    result = {
        "schema_version": 2,
        "status": "PASS" if not errors else "FAIL",
        "components_manifest": "data/components-generated.json",
        "proof_trace": "data/proof-trace.json.gz",
        "client": "reconstruction/SubargumentSpine.lean",
        "selected_trace_count": trace_seen,
        "trace_backed_component_count": source_count,
        "trace_application_target_component_count": target_count,
        "trace_application_record_count": trace_application_count,
        "trace_reference_record_count": trace_reference_count,
        "exact_context_application_count": exact_context_count,
        "structural_only_application_count": structural_only_count,
        "proof_application_count": proof_count,
        "data_application_count": data_count,
        "omitted_structural_application_count": omitted_structural_count,
        "omitted_external_reference_count": omitted_external_count,
        "referenced_exact_subterm_count": referenced_exact_subterm_count,
        "compiler_relation_count": compiler_relation_count,
        "trace_only_relation_count": trace_only_relation_count,
        "negative_tests": {
            "swapped_arguments": swapped_test,
            "type_only_false_positive": type_only_test,
            "proof_data_classification": classification_test,
        },
        "opaque_body_policy": (
            "Structural proof traces and named declaration interfaces are retained; "
            "opaque theorem bodies are not claimed to be inlined."
        ),
        "errors": errors,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))
    return 0 if not errors else 1
