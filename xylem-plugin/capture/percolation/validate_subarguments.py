#!/usr/bin/env python3
"""Independently validate structural percolation application records."""

from __future__ import annotations

import argparse
import copy
import gzip
import json
from pathlib import Path
from typing import Any


LEGITIMATE_NO_VALUE_KINDS = {"axiom", "inductive", "ctor", "rec", "quot"}


def load_json(path: Path) -> dict[str, Any]:
    opener = gzip.open if path.suffix == ".gz" else open
    with opener(path, "rt", encoding="utf-8") as stream:
        return json.load(stream)


def has_truncated(value: Any) -> bool:
    if isinstance(value, dict):
        return value.get("node") == "truncated" or any(
            has_truncated(child) for child in value.values()
        )
    if isinstance(value, list):
        return any(has_truncated(child) for child in value)
    return False


def record_id(declaration: str, path: str) -> str:
    return f"{declaration}::{path or '<root>'}"


def application_shape_errors(application: dict[str, Any]) -> list[str]:
    """Reject missing, reordered, or weakly typed application mappings."""
    errors: list[str] = []
    detail_status = application.get("detail_status")
    status = application.get("status")
    arity = application.get("arity")
    arguments = application.get("arguments")
    if not isinstance(application.get("path"), str):
        errors.append("missing path")
    if not isinstance(arity, int) or arity < 0:
        return [*errors, "invalid arity"]
    if not isinstance(arguments, list):
        return [*errors, "arguments is not a list"]
    if detail_status == "structural_only_external":
        if arguments:
            errors.append("structural-only application has argument mappings")
        if status != "structural_only":
            errors.append(f"structural-only status is {status!r}")
        return errors
    if detail_status != "exact_context":
        errors.append(f"unknown detail_status {detail_status!r}")
    if len(arguments) != arity:
        errors.append(f"argument count {len(arguments)} != arity {arity}")
    indices = [item.get("index") for item in arguments if isinstance(item, dict)]
    if indices != list(range(arity)):
        errors.append(f"argument order/index mismatch: {indices!r}")
    for item in arguments:
        if not isinstance(item, dict):
            errors.append("non-object argument mapping")
            continue
        if item.get("mapping_status") is not None:
            errors.append(f"unsupported mapping at index {item.get('index')}")
            continue
        for field in ("expected_type", "actual_type", "binderName", "binderInfo"):
            if not isinstance(item.get(field), str):
                errors.append(f"argument {item.get('index')} missing {field}")
        if item.get("definitional_type_match") is not True:
            errors.append(f"argument {item.get('index')} is not definitionally type-correct")
        if not isinstance(item.get("argument"), dict):
            errors.append(f"argument {item.get('index')} missing expression summary")
    if not isinstance(application.get("head_type"), str):
        errors.append("missing head_type")
    if not isinstance(application.get("output_type"), str):
        errors.append("missing output_type")
    if not isinstance(application.get("output_is_proposition"), bool):
        errors.append("missing output proposition classification")
    result_class = application.get("result_class")
    context_status = application.get("context_status")
    if result_class == "proof_term":
        if context_status != "exact_proof_context":
            errors.append("proof application missing exact_proof_context status")
        if not isinstance(application.get("local_context"), list):
            errors.append("proof application missing local_context")
    elif result_class in {"data_value", "proposition_value"}:
        if context_status != "omitted_data_context":
            errors.append("data application missing omitted_data_context status")
        if application.get("local_context") is not None:
            errors.append("data application unexpectedly carries local_context")
    else:
        errors.append("exact application has no supported context policy")
    return errors


def _is_proof_record(application: dict[str, Any]) -> bool:
    return (
        application.get("detail_status") == "exact_context"
        and application.get("proof_relevance") == "proof_term"
        and application.get("result_class") == "proof_term"
        and application.get("output_is_proposition") is True
    )


def trace_application_index(trace_records: dict[str, dict[str, Any]]) -> dict[str, dict[str, Any]]:
    result: dict[str, dict[str, Any]] = {}
    for declaration, record in trace_records.items():
        for application in record.get("application_records", []):
            if not isinstance(application, dict):
                continue
            key = record_id(declaration, application.get("path", ""))
            if key in result:
                raise ValueError(f"duplicate application record id {key}")
            result[key] = application
    return result


def trace_reference_index(trace_records: dict[str, dict[str, Any]]) -> dict[str, dict[str, Any]]:
    result: dict[str, dict[str, Any]] = {}
    for declaration, record in trace_records.items():
        for reference in record.get("reference_records", []):
            if not isinstance(reference, dict):
                continue
            key = record_id(declaration, reference.get("path", ""))
            if key in result:
                raise ValueError(f"duplicate reference record id {key}")
            result[key] = reference
    return result


def negative_swapped_argument_test(application_index: dict[str, dict[str, Any]]) -> dict[str, Any]:
    candidate_id = next(
        (
            key for key, application in application_index.items()
            if application.get("detail_status") == "exact_context"
            and application.get("status") == "checked"
            and isinstance(application.get("arguments"), list)
            and len(application["arguments"]) >= 2
        ),
        None,
    )
    if candidate_id is None:
        return {"status": "FAIL", "reason": "no checked application with two arguments"}
    mutated = copy.deepcopy(application_index[candidate_id])
    mutated["arguments"][0], mutated["arguments"][1] = (
        mutated["arguments"][1], mutated["arguments"][0]
    )
    errors = application_shape_errors(mutated)
    return {
        "status": "PASS" if errors else "FAIL",
        "candidate": candidate_id,
        "mutated_error_sample": errors[:2],
        "reason": "swapping ordered argument records must be rejected",
    }


def negative_type_only_false_positive_test(
    trace_records: dict[str, dict[str, Any]],
) -> dict[str, Any]:
    type_names: set[str] = set()
    proof_heads: set[str] = set()
    for record in trace_records.values():
        for reference in record.get("reference_records", []):
            if isinstance(reference, dict) and reference.get("role") == "type_only_reference":
                name = reference.get("name")
                if isinstance(name, str) and ".Statements." in name:
                    type_names.add(name)
        for application in record.get("application_records", []):
            if not isinstance(application, dict):
                continue
            if application.get("proof_relevance") != "proof_term":
                continue
            head = application.get("head")
            name = head.get("name") if isinstance(head, dict) else None
            if isinstance(name, str) and ".Statements." in name:
                proof_heads.add(name)
    expected = {
        name for name in type_names
        if name.endswith("AdditiveGluing") or name.endswith("NearOneGluing")
    }
    overlap = sorted(expected & proof_heads)
    return {
        "status": "PASS" if expected and not overlap else "FAIL",
        "type_only_statement_constants": sorted(expected),
        "proof_application_statement_heads": sorted(proof_heads),
        "false_positive_overlap": overlap,
        "reason": "statement constants used only in types must not be treated as proof applications",
    }


def classification_regression_test(
    trace_records: dict[str, dict[str, Any]],
) -> dict[str, Any]:
    """Check that common data locals stay evidence, not proof steps."""
    data_heads: dict[str, int] = {"w": 0, "g": 0}
    data_head_promoted: list[str] = []
    local_proof_count = 0
    for record in trace_records.values():
        for application in record.get("application_records", []):
            if not isinstance(application, dict):
                continue
            head = application.get("head")
            name = head.get("name") if isinstance(head, dict) else None
            if application.get("application_role") == "local_assumption_application":
                if application.get("proof_relevance") == "proof_term":
                    local_proof_count += 1
                if name in data_heads:
                    data_heads[name] += 1
                    if application.get("proof_relevance") == "proof_term":
                        data_head_promoted.append(name)
    observed_data_heads = sorted(name for name, count in data_heads.items() if count)
    return {
        "status": "PASS" if observed_data_heads == ["g", "w"] and local_proof_count and not data_head_promoted else "FAIL",
        "data_heads_observed": observed_data_heads,
        "data_head_application_counts": data_heads,
        "data_heads_promoted_as_proof": sorted(set(data_head_promoted)),
        "local_proof_application_count": local_proof_count,
        "reason": "w/e and g/e applications must remain data evidence; local proposition applications remain proof evidence",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--components", type=Path, required=True)
    parser.add_argument("--proof-trace", type=Path, required=True)
    parser.add_argument("--client", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    components = load_json(args.components)
    trace = load_json(args.proof_trace)
    trace_records = {record["declaration"]: record for record in trace.get("records", [])}
    source_components = [
        component for component in components.get("components", [])
        if component.get("kind") == "trace_backed_subargument"
    ]
    target_components = [
        component for component in components.get("components", [])
        if component.get("kind") == "trace_application_target"
    ]
    errors: list[str] = []
    if len(trace_records) != len(trace.get("selected_declarations", [])):
        errors.append("trace record count does not match selected declaration list")
    if len(source_components) != len(trace_records):
        errors.append(
            f"expected one structural source component per selected trace, got {len(source_components)}"
        )

    try:
        application_index = trace_application_index(trace_records)
        reference_index = trace_reference_index(trace_records)
    except ValueError as error:
        errors.append(str(error))
        application_index = {}
        reference_index = {}

    accounted: set[str] = set()
    referenced_application_ids: set[str] = set()
    for component in source_components:
        evidence = component.get("proof_trace_evidence") or {}
        generated = component.get("generated_from") or {}
        source = generated.get("trace_declaration")
        if not isinstance(source, str):
            errors.append(f"{component.get('id')}: missing generated trace declaration")
            continue
        accounted.add(source)
        record = trace_records.get(source)
        if record is None:
            errors.append(f"{component.get('id')}: no matching selected trace for {source}")
            continue
        if record.get("status") not in {"captured", "no_value"} or has_truncated(record.get("tree")):
            errors.append(f"{component.get('id')}: trace is unavailable or truncated")
        if (
            record.get("status") == "no_value"
            and record.get("kind") not in LEGITIMATE_NO_VALUE_KINDS
        ):
            errors.append(
                f"{component.get('id')}: unexpected no_value status for kind {record.get('kind')!r}"
            )
        if record.get("status") == "captured" and record.get("tree_status") != (
            "omitted_compact_full_cone"
        ):
            errors.append(f"{component.get('id')}: compact tree policy is not recorded")
        if record.get("status") == "captured":
            for count_field in (
                "omitted_structural_application_count",
                "omitted_external_reference_count",
            ):
                if not isinstance(record.get(count_field), int) or record.get(count_field) < 0:
                    errors.append(f"{component.get('id')}: invalid {count_field}")
        if component.get("formal_interface_status") != "checked_against_elaborated_capture":
            errors.append(f"{component.get('id')}: formal interface was not marked checked")
        if component.get("formal_status") != "trace_backed_structural_application_records":
            errors.append(f"{component.get('id')}: incorrect formal status")
        trace_apps = record.get("application_records") or []
        if evidence.get("application_count") != len(trace_apps):
            errors.append(f"{component.get('id')}: application count mismatch")
        proof_count = sum(
            isinstance(application, dict) and _is_proof_record(application)
            for application in trace_apps
        )
        data_count = sum(
            isinstance(application, dict)
            and application.get("proof_relevance") == "data_term"
            for application in trace_apps
        )
        if evidence.get("proof_application_count") != proof_count:
            errors.append(f"{component.get('id')}: proof application count mismatch")
        if evidence.get("data_application_count") != data_count:
            errors.append(f"{component.get('id')}: data application count mismatch")
        for application in trace_apps:
            if not isinstance(application, dict):
                errors.append(f"{component.get('id')}: non-object full application record")
                continue
            for message in application_shape_errors(application):
                errors.append(f"{component.get('id')} full {application.get('path')}: {message}")
        proof_apps = evidence.get("application_records") or []
        data_apps = evidence.get("data_application_records") or []
        if evidence.get("proof_application_sample_count") != len(proof_apps):
            errors.append(f"{component.get('id')}: proof application sample count mismatch")
        if evidence.get("data_application_sample_count") != len(data_apps):
            errors.append(f"{component.get('id')}: data application sample count mismatch")
        for application in proof_apps:
            if not isinstance(application, dict):
                errors.append(f"{component.get('id')}: non-object application record")
                continue
            for message in application_shape_errors(application):
                errors.append(f"{component.get('id')} {application.get('path')}: {message}")
            if not _is_proof_record(application):
                errors.append(f"{component.get('id')}: non-proof application promoted as proof evidence")
        for application in data_apps:
            if not isinstance(application, dict):
                errors.append(f"{component.get('id')}: non-object data application record")
                continue
            for message in application_shape_errors(application):
                errors.append(f"{component.get('id')} data {application.get('path')}: {message}")
            if _is_proof_record(application):
                errors.append(f"{component.get('id')}: proof application duplicated as data evidence")
        ids = evidence.get("subterm_record_ids") or []
        for application_id in ids:
            referenced_application_ids.add(application_id)
            application = application_index.get(application_id)
            if application is None:
                errors.append(f"{component.get('id')}: missing subterm record {application_id}")
                continue
            if application.get("detail_status") != "exact_context":
                errors.append(f"{component.get('id')}: subterm is not exact-context {application_id}")
        for reference in evidence.get("type_only_reference_sample") or evidence.get("type_only_reference_records") or []:
            if reference.get("role") != "type_only_reference" or reference.get("context") != "type":
                errors.append(f"{component.get('id')}: misclassified type-only reference")
            ref_id = record_id(source, reference.get("path", ""))
            if ref_id not in reference_index:
                errors.append(f"{component.get('id')}: type-only reference is not trace-indexed {ref_id}")

    if accounted != set(trace_records):
        errors.append("structural source components do not account for exactly the selected trace records")
    if (components.get("subargument_decomposition") or {}).get("status") != "PASS":
        errors.append("generated subargument decomposition audit is not PASS")

    swapped_test = negative_swapped_argument_test(application_index)
    if swapped_test["status"] != "PASS":
        errors.append("negative swapped-argument test did not reject the mutation")
    type_only_test = negative_type_only_false_positive_test(trace_records)
    if type_only_test["status"] != "PASS":
        errors.append("negative type-only false-positive test did not pass")
    classification_test = classification_regression_test(trace_records)
    if classification_test["status"] != "PASS":
        errors.append("proof/data application classification regression did not pass")

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
        "selected_trace_count": len(trace_records),
        "trace_backed_component_count": len(source_components),
        "trace_application_target_component_count": len(target_components),
        "trace_application_record_count": len(application_index),
        "trace_reference_record_count": len(reference_index),
        "exact_context_application_count": sum(
            application.get("detail_status") == "exact_context"
            for application in application_index.values()
        ),
        "structural_only_application_count": sum(
            application.get("detail_status") == "structural_only_external"
            for application in application_index.values()
        ),
        "proof_application_count": sum(
            application.get("proof_relevance") == "proof_term"
            for application in application_index.values()
        ),
        "data_application_count": sum(
            application.get("proof_relevance") == "data_term"
            for application in application_index.values()
        ),
        "omitted_structural_application_count": sum(
            record.get("omitted_structural_application_count", 0)
            for record in trace_records.values()
        ),
        "omitted_external_reference_count": sum(
            record.get("omitted_external_reference_count", 0)
            for record in trace_records.values()
        ),
        "referenced_exact_subterm_count": len(referenced_application_ids),
        "compiler_relation_count": sum(
            relation.get("evidence_kind") == "compiler"
            for relation in components.get("relations", [])
            if relation.get("type") in {
                "trace_application_boundary", "trace_proof_reference_boundary"
            }
        ),
        "trace_only_relation_count": sum(
            relation.get("evidence_kind") == "trace"
            for relation in components.get("relations", [])
            if relation.get("type") in {
                "trace_application_boundary", "trace_proof_reference_boundary"
            }
        ),
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


if __name__ == "__main__":
    raise SystemExit(main())
