#!/usr/bin/env python3
"""Derive a proof-structure component layer from an elaborated capture.

The small role labels in ``components.json`` remain authored interpretation.
This command is the compiler-derived layer: it walks the captured Solution
``USES_IN_PROOF`` graph from the public theorem, partitions the reachable proof
cone by its owning Lean module, computes boundary interfaces, validates the
authored role labels against literal captured signatures and binder order, and
derives application-spine components from the complete reachable elaborated
``Expr`` record set.
Source-module regions are deliberately labelled as regions, not mathematical
subarguments.  The structural application layer does not claim to inline
opaque theorem bodies or replace human mathematical exposition.
"""

from __future__ import annotations

import argparse
import gzip
import hashlib
import json
from collections import Counter, defaultdict, deque
from pathlib import Path
from typing import Any


ROOT_DECL = "solution::BondPercolation.percolation_continuity"
LEGITIMATE_NO_VALUE_KINDS = {"axiom", "inductive", "ctor", "rec", "quot"}


def sha256_text(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


def load_json(path: Path) -> dict[str, Any]:
    opener = gzip.open if path.suffix == ".gz" else open
    with opener(path, "rt", encoding="utf-8") as stream:
        return json.load(stream)


def load_capture(path: Path) -> dict[str, Any]:
    opener = gzip.open if path.suffix == ".gz" else open
    with opener(path, "rt", encoding="utf-8") as stream:
        data = json.load(stream)
    if data.get("errors"):
        raise SystemExit(f"capture reports extraction errors: {data['errors'][:3]}")
    if data.get("capture_projection", {}).get("premises_complete") is not True:
        raise SystemExit("capture does not declare complete premise coverage")
    return data


def record_map(capture: dict[str, Any]) -> dict[str, dict[str, Any]]:
    result = {record["name"]: record for record in capture.get("declarations", [])}
    if len(result) != len(capture.get("declarations", [])):
        raise SystemExit("capture contains duplicate declaration names")
    return result


def interface(record: dict[str, Any]) -> dict[str, Any]:
    signature = record.get("signature") or ""
    return {
        "declaration": record["name"],
        "signature": signature,
        "signature_sha256": sha256_text(signature),
        "binders": [
            {
                "idx": binder.get("idx"),
                "name": binder.get("name"),
                "binderInfo": binder.get("binderInfo"),
                "type": binder.get("type"),
            }
            for binder in record.get("binders", [])
        ],
        "conclusion": record.get("conclusion"),
        "source": {
            "file": record.get("src_file"),
            "range": record.get("range"),
        },
        "kind": record.get("kind"),
        "axioms": record.get("axioms", []),
    }


def binder_names(record: dict[str, Any]) -> list[str | None]:
    return [binder.get("name") for binder in record.get("binders", [])]


# These are the expected literal binder orders for the twelve authored role
# labels.  The validator compares them to the captured Lean records; it does
# not infer order from prose or from declaration names.
EXPECTED_BINDERS: dict[str, list[str | None]] = {
    "solution::Percolation.Continuity.CSH.cshHolds": [
        "V", None, "w", "hw", "x", "Y", "D", "o", "v", "hxY", "ho", "hv", "hov", "hnd", "hdis"
    ],
    "solution::Percolation.Continuity.CSH.cshAll": [
        "n", "w", None, "o", "v", "x", "Y", "D", None, None, None, None, None, None, None, None
    ],
    "solution::Percolation.Continuity.CSH.additiveGluing_of_csh": ["hCSH"],
    "solution::Percolation.Continuity.CSH.percolationContinuity_of_csh": ["hCSH", "d", "hd"],
    "solution::Percolation.Continuity.percolationContinuity_of_additiveGluing": ["h", "d", "hd"],
    "solution::Percolation.Continuity.nearOneGluing_iff_conjecture3": [],
    "solution::Percolation.Continuity.percolationContinuity_of_nearOneGluing": ["hX", "d", "hd"],
    "solution::Percolation.Continuity.CSH.kozmaNitzan_conjecture3_holds": [],
    "solution::Percolation.Literature.KozmaNitzan2024_thm6_holds": [],
    "solution::Percolation.Literature.KozmaNitzan2024_thm6_holds_of": ["hslab", "hAG"],
    "solution::Percolation.Continuity.CSH.percolationContinuity_allDimensions": ["d", "hd"],
    "solution::BondPercolation.percolation_continuity": ["d", "hd"],
    "solution::BondPercolation.percolation_continuity_Z3": [],
}


def validate_roles(roles: dict[str, Any], records: dict[str, dict[str, Any]]) -> dict[str, Any]:
    errors: list[str] = []
    checked: list[dict[str, Any]] = []
    for component in roles.get("components", []):
        declarations = component.get("declarations", [])
        formal = []
        for name in declarations:
            record = records.get(name)
            if record is None:
                errors.append(f"{component.get('id')}: missing declaration {name}")
                continue
            actual = binder_names(record)
            expected = EXPECTED_BINDERS.get(name)
            if expected is not None and actual != expected:
                errors.append(
                    f"{component.get('id')}: binder order mismatch for {name}: "
                    f"expected {expected!r}, got {actual!r}"
                )
            formal.append(interface(record))
        component["formal_interfaces"] = formal
        component["formal_interface_status"] = "checked_against_elaborated_capture"
        checked.append({
            "component": component.get("id"),
            "declarations": declarations,
            "binder_orders": {name: binder_names(records[name]) for name in declarations if name in records},
            "signature_sha256": {name: sha256_text(records[name].get("signature") or "")
                                  for name in declarations if name in records},
        })
    if errors:
        raise SystemExit("component interface audit failed:\n" + "\n".join(errors))
    return {"status": "PASS", "components": checked, "error_count": 0}


def proof_graph(records: dict[str, dict[str, Any]]) -> tuple[dict[str, set[str]], dict[str, list[dict[str, Any]]]]:
    graph: dict[str, set[str]] = defaultdict(set)
    edge_rows: dict[str, list[dict[str, Any]]] = defaultdict(list)
    local = set(records)
    for source, record in records.items():
        if not source.startswith("solution::"):
            continue
        for premise in record.get("premises", []):
            if not premise.get("in_proof"):
                continue
            target = premise.get("name")
            if not isinstance(target, str):
                continue
            row = {
                "source": source,
                "target": target,
                "edge_type": "USES_IN_PROOF",
                "target_local": target in local,
                "target_surface": "solution" if target.startswith("solution::") else None,
            }
            edge_rows[source].append(row)
            if target in local and target.startswith("solution::"):
                graph[source].add(target)
    return graph, edge_rows


def reachable(graph: dict[str, set[str]], root: str) -> tuple[set[str], dict[str, int]]:
    seen = {root}
    distance = {root: 0}
    queue: deque[str] = deque([root])
    while queue:
        source = queue.popleft()
        for target in sorted(graph.get(source, ())):
            if target not in seen:
                seen.add(target)
                distance[target] = distance[source] + 1
                queue.append(target)
    return seen, distance


def component_id(module: str) -> str:
    slug = "-".join(part for part in module.split(".") if part)
    return f"proof-module-{slug}-{sha256_text(module)[:8]}"


def generated_components(
    records: dict[str, dict[str, Any]],
    graph: dict[str, set[str]],
    edge_rows: dict[str, list[dict[str, Any]]],
) -> tuple[list[dict[str, Any]], list[dict[str, Any]], dict[str, Any]]:
    reached, distances = reachable(graph, ROOT_DECL)
    by_module: dict[str, list[str]] = defaultdict(list)
    for name in sorted(reached):
        by_module[records[name]["module"]].append(name)
    module_ids = {module: component_id(module) for module in by_module}
    parents: dict[str, set[str]] = defaultdict(set)
    for parent, children in graph.items():
        for child in children:
            parents[child].add(parent)
    generated: list[dict[str, Any]] = []
    for module in sorted(by_module):
        members = by_module[module]
        member_set = set(members)
        incoming = set()
        outgoing = set()
        relation_edges: list[dict[str, Any]] = []
        external_edges: list[dict[str, Any]] = []
        for source in members:
            for row in edge_rows.get(source, []):
                target = row["target"]
                if target in reached:
                    target_module = records[target]["module"]
                    if target_module != module:
                        outgoing.add(target)
                        relation_edges.append(row)
                else:
                    external_edges.append(row)
            for parent in parents.get(source, set()):
                if parent in reached and records[parent]["module"] != module:
                    incoming.add(parent)
        entry_names = sorted(incoming)
        exit_names = sorted(outgoing)
        entry_interfaces = [interface(records[name]) for name in entry_names]
        exit_interfaces = [interface(records[name]) for name in exit_names]
        external_counts = Counter(row["target"] for row in external_edges)
        generated.append({
            "id": module_ids[module],
            "title": f"Compiler source-module region: {module}",
            "kind": "compiler_source_module_region",
            "surface": "solution",
            "module": module,
            "role": "compiler_source_module_region",
            "formal_status": "compiler_derived_source_partition",
            "evidence_status": "captured_proof_edges_and_literal_interfaces",
            "interpretation_status": "compiler_partition_not_a_mathematical_subargument",
            "declarations": members,
            "summary": (
                "Compiler-derived source-module region partitioned by the owning Lean module; "
                "membership is the reachable local proof cone from the public Solution theorem. "
                "This is a source partition, not a mathematical subargument boundary."
            ),
            "generated_from": {
                "root": ROOT_DECL,
                "algorithm": (
                    "BFS over captured USES_IN_PROOF, then exact source-module partition; "
                    "not a mathematical subargument boundary"
                ),
                "proof_distance_min": min(distances[name] for name in members),
                "proof_distance_max": max(distances[name] for name in members),
            },
            "interface": {
                "entry_declarations": entry_names,
                "exit_declarations": exit_names,
                "entry_interfaces": entry_interfaces,
                "exit_interfaces": exit_interfaces,
                "external_exit_counts": dict(sorted(external_counts.items())),
            },
            "coverage": {
                "declaration_count": len(members),
                "proof_edge_count": sum(len(edge_rows.get(name, [])) for name in members),
                "cross_region_edge_count": len(relation_edges),
                "external_edge_count": len(external_edges),
            },
        })

    relation_buckets: dict[tuple[str, str], list[dict[str, Any]]] = defaultdict(list)
    for source in sorted(reached):
        source_module = records[source]["module"]
        for row in edge_rows.get(source, []):
            target = row["target"]
            if target not in reached:
                continue
            target_module = records[target]["module"]
            if source_module != target_module:
                relation_buckets[(module_ids[source_module], module_ids[target_module])].append(row)
    relations: list[dict[str, Any]] = []
    for (source_id, target_id), rows in sorted(relation_buckets.items()):
        sample = rows[0]
        relations.append({
            "source": source_id,
            "target": target_id,
            "type": "compiler_proof_boundary",
            "evidence_kind": "compiler",
            "evidence": {
                "source_declaration": sample["source"],
                "target_declaration": sample["target"],
                "edge_type": sample["edge_type"],
                "edge_count": len(rows),
                "derivation": "aggregated crossing edge in the captured elaborated proof graph",
            },
        })
    audit = {
        "status": "PASS",
        "root": ROOT_DECL,
        "algorithm": "reachable proof cone over USES_IN_PROOF, partitioned by exact source module",
        "solution_declarations_in_capture": sum(name.startswith("solution::") for name in records),
        "reachable_solution_declarations": len(reached),
        "reachable_module_components": len(generated),
        "unreached_solution_declarations": sum(
            name.startswith("solution::") and name not in reached for name in records
        ),
        "cross_region_relations": len(relations),
        "proof_edges_from_reachable_sources": sum(len(edge_rows.get(name, [])) for name in reached),
        "external_proof_edges_from_reachable_sources": sum(
            1 for name in reached for row in edge_rows.get(name, []) if not row["target_local"]
        ),
        "component_membership_accounted": sum(len(c["declarations"]) for c in generated) == len(reached),
    }
    return generated, relations, audit


def _trace_children(value: Any):
    """Yield ``(path, node, fn_arity)`` for nodes in a proof trace.

    ``fn_arity`` is the number of consecutive application nodes for which the
    current node is on the function spine.  It is useful evidence that a
    named constant is being applied rather than merely mentioned as an
    argument.  Paths are structural renderer paths, not source locations.
    """
    def walk(node: Any, path: str, fn_ancestors: int = 0):
        if isinstance(node, dict):
            yield path, node, fn_ancestors
            if node.get("node") == "app":
                if "fn" in node:
                    yield from walk(node["fn"], f"{path}/fn", fn_ancestors + 1)
                if "arg" in node:
                    yield from walk(node["arg"], f"{path}/arg", 0)
                return
            for key, child in node.items():
                if key in {"node", "name", "levels", "index", "binderInfo"}:
                    continue
                if isinstance(child, (dict, list)):
                    yield from walk(child, f"{path}/{key}", 0)
        elif isinstance(node, list):
            for idx, child in enumerate(node):
                yield from walk(child, f"{path}[{idx}]", 0)

    yield from walk(value, "", 0)


def trace_occurrences(record: dict[str, Any]) -> dict[str, list[dict[str, Any]]]:
    """Return every structural constant occurrence in one retained trace."""
    occurrences: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for path, node, fn_arity in _trace_children(record.get("tree")):
        if node.get("node") != "const" or not isinstance(node.get("name"), str):
            continue
        occurrences[node["name"]].append({
            "path": path,
            "application_arity": fn_arity,
        })
    return dict(occurrences)


def _local_name(name: str) -> str:
    return f"solution::{name}"


def generated_subarguments_legacy(
    records: dict[str, dict[str, Any]],
    edge_rows: dict[str, list[dict[str, Any]]],
    proof_trace: dict[str, Any],
) -> tuple[list[dict[str, Any]], list[dict[str, Any]], dict[str, Any]]:
    """Compatibility shim for callers of the pre-structural helper."""
    # Kept as a compatibility name for callers of the earlier helper.  The
    # implementation below is intentionally unreachable; all current callers
    # use the traversal-derived implementation defined later in this file.
    return generated_subarguments(records, edge_rows, proof_trace)

    trace_records = {record["declaration"]: record for record in proof_trace.get("records", [])}
    local_records = set(records)
    local_edge_keys = {
        (source, row["target"], row["edge_type"])
        for source, rows in edge_rows.items()
        for row in rows
    }
    trace_apps = {
        name: trace_occurrences(record)
        for name, record in trace_records.items()
    }
    errors: list[str] = []
    components: list[dict[str, Any]] = []
    source_to_component: dict[str, str] = {}
    contracts: list[dict[str, Any]] = []

    for spec in ():
        source_name = spec["source"]
        source_local = _local_name(source_name)
        trace_record = trace_records.get(source_name)
        if trace_record is None:
            errors.append(f"missing selected trace record for {source_name}")
            continue
        source_record = records.get(source_local)
        if source_record is None:
            errors.append(f"missing captured source declaration for {source_local}")
            continue
        occurrences = trace_apps.get(source_name, {})
        target_evidence: list[dict[str, Any]] = []
        local_target_names: list[str] = []
        for target in spec["targets"]:
            matches = occurrences.get(target, [])
            if not matches:
                errors.append(
                    f"{source_name}: trace does not contain required constant {target}"
                )
            target_local = _local_name(target)
            is_local = target_local in local_records
            if is_local:
                local_target_names.append(target_local)
            capture_edge = (source_local, target_local, "USES_IN_PROOF") in local_edge_keys
            if is_local and not capture_edge:
                edge_status = "trace_only_inlined_or_normalized"
            elif is_local:
                edge_status = "captured_uses_in_proof"
            else:
                edge_status = "external_or_nonlocal_trace_constant"
            target_evidence.append({
                "constant": target,
                "local_declaration": target_local if is_local else None,
                "trace_occurrence_count": len(matches),
                "trace_occurrences": matches[:8],
                "capture_edge_status": edge_status,
                "capture_edge": {
                    "source": source_local,
                    "target": target_local,
                    "edge_type": "USES_IN_PROOF",
                    "present": capture_edge,
                } if is_local else None,
            })
        declarations = [source_local] + [name for name in local_target_names if name != source_local]
        # Preserve first occurrence if the catalog ever lists a duplicate target.
        declarations = list(dict.fromkeys(declarations))
        formal_interfaces = [interface(records[name]) for name in declarations]
        component = {
            "id": spec["id"],
            "title": spec["title"],
            "kind": "trace_backed_subargument",
            "surface": "solution",
            "role": "trace_backed_subargument",
            "formal_status": "trace_backed_interface",
            "evidence_status": "selected_elaborated_proof_application_and_capture_metadata",
            "interpretation_status": "authored_pending_review",
            "declarations": declarations,
            "summary": spec["summary"],
            "generated_from": {
                "algorithm": "explicit contract checked against retained structural Expr trace and merged capture",
                "trace_declaration": source_name,
                "trace_artifact": "data/proof-trace.json.gz",
            },
            "interface": {
                "source_declaration": source_local,
                "target_declarations": local_target_names,
                "source_interface": interface(source_record),
                "target_interfaces": [interface(records[name]) for name in local_target_names],
            },
            "formal_interfaces": formal_interfaces,
            "formal_interface_status": "checked_against_elaborated_capture",
            "proof_trace_evidence": {
                "trace_status": trace_record.get("status"),
                "fuel": trace_record.get("fuel"),
                "source_proof_constants": trace_record.get("proof_constants", []),
                "targets": target_evidence,
            },
            "validation": {
                "source_trace_present": True,
                "all_target_constants_present": all(item["trace_occurrence_count"] > 0 for item in target_evidence),
                "local_capture_edges": sum(
                    item["capture_edge_status"] == "captured_uses_in_proof" for item in target_evidence
                ),
                "trace_only_inlined_or_normalized": sum(
                    item["capture_edge_status"] == "trace_only_inlined_or_normalized" for item in target_evidence
                ),
            },
            "limits": [
                "This record is a trace-backed interface step, not a claim that the opaque target theorem body has been inlined.",
                "The short mathematical reading remains authored and requires human review.",
            ],
        }
        components.append(component)
        source_to_component[source_local] = spec["id"]
        contracts.append({
            "component": spec["id"],
            "trace_declaration": source_name,
            "required_constants": spec["targets"],
            "required_constant_status": {
                item["constant"]: item["trace_occurrence_count"] > 0
                for item in target_evidence
            },
        })

    relations: list[dict[str, Any]] = []
    relation_keys: set[tuple[str, str, str]] = set()
    for component, spec in zip(components, ()):
        source_local = _local_name(spec["source"])
        for evidence in component["proof_trace_evidence"]["targets"]:
            target_local = evidence.get("local_declaration")
            if not target_local or target_local not in source_to_component:
                continue
            target_component = source_to_component[target_local]
            if target_component == component["id"]:
                continue
            key = (component["id"], target_component, target_local)
            if key in relation_keys:
                continue
            relation_keys.add(key)
            if evidence["capture_edge_status"] == "captured_uses_in_proof":
                evidence_kind = "compiler"
                relation_evidence = {
                    "source_declaration": source_local,
                    "target_declaration": target_local,
                    "edge_type": "USES_IN_PROOF",
                    "trace_declaration": spec["source"],
                    "trace_constant": evidence["constant"],
                    "trace_occurrences": evidence["trace_occurrences"],
                    "derivation": "selected structural Expr application cross-checked against captured USES_IN_PROOF",
                }
            else:
                evidence_kind = "capture_metadata"
                relation_evidence = {
                    "source_declaration": source_local,
                    "target_declaration": target_local,
                    "edge_type": "USES_IN_PROOF",
                    "trace_declaration": spec["source"],
                    "trace_constant": evidence["constant"],
                    "trace_occurrences": evidence["trace_occurrences"],
                    "derivation": "selected structural Expr application; capture row was inlined or normalized",
                }
            relations.append({
                "source": component["id"],
                "target": target_component,
                "type": "trace_subargument_boundary",
                "evidence_kind": evidence_kind,
                "evidence": relation_evidence,
                "note": (
                    "Compiler evidence and trace evidence are kept separate."
                    if evidence_kind == "compiler" else
                    "Trace evidence is retained without upgrading an absent capture row to a compiler edge."
                ),
            })

    selected_names = [record.get("declaration") for record in proof_trace.get("records", [])]
    accounted_sources = [contract["trace_declaration"] for contract in contracts]
    trace_coverage = []
    for trace_name in selected_names:
        occurrences = trace_apps.get(trace_name, {})
        trace_coverage.append({
            "declaration": trace_name,
            "status": trace_records[trace_name].get("status"),
            "fuel": trace_records[trace_name].get("fuel"),
            "component_ids": [
                component["id"] for component, spec in zip(components, ())
                if spec["source"] == trace_name
            ],
            "structural_constant_count": sum(len(values) for values in occurrences.values()),
            "truncated_node_present": any(
                node.get("node") == "truncated"
                for _path, node, _arity in _trace_children(trace_records[trace_name].get("tree"))
            ),
        })
    audit = {
        "status": "PASS" if not errors else "FAIL",
        "algorithm": "explicit trace contracts over retained structural Expr trees plus capture interfaces",
        "selected_trace_count": len(selected_names),
        "catalog_component_count": len(components),
        "relation_count": len(relations),
        "compiler_relation_count": sum(r["evidence_kind"] == "compiler" for r in relations),
        "trace_only_relation_count": sum(r["evidence_kind"] != "compiler" for r in relations),
        "selected_traces_accounted": sorted(selected_names) == sorted(accounted_sources),
        "all_target_constants_present": all(
            all(contract["required_constant_status"].values()) for contract in contracts
        ),
        "all_structural_traces_captured": all(
            item["status"] == "captured" and not item["truncated_node_present"]
            for item in trace_coverage
        ),
        "trace_coverage": trace_coverage,
        "contracts": contracts,
        "opaque_boundaries": [
            "Selected proof traces preserve elaborated Expr structure, but opaque theorem bodies are not recursively serialized.",
            "The cshHolds trace contains the named local helper applications; the helper theorem bodies remain separate captured declarations.",
            "A trace-only local boundary is never promoted to a compiler relation when the merged capture has no corresponding USES_IN_PROOF row.",
        ],
        "errors": errors,
    }
    if not audit["selected_traces_accounted"]:
        audit["errors"].append("not every selected trace declaration has an explicit catalog contract")
        audit["status"] = "FAIL"
    return components, relations, audit


def _trace_record_id(source: str, path: str) -> str:
    return f"{source}::{path or '<root>'}"


def _trace_component_id(source: str) -> str:
    slug = "-".join(part for part in source.split(".") if part)
    return f"trace-subarg-{slug}-{sha256_text(source)[:8]}"


def _trace_target_component_id(target: str) -> str:
    slug = "-".join(part for part in target.split(".") if part)
    return f"trace-target-{slug}-{sha256_text(target)[:8]}"


def _app_head_name(application: dict[str, Any]) -> str | None:
    head = application.get("head")
    if not isinstance(head, dict):
        return None
    name = head.get("name")
    return name if isinstance(name, str) else None


def _is_proof_application(application: dict[str, Any]) -> bool:
    return (
        application.get("detail_status") == "exact_context"
        and application.get("proof_relevance") == "proof_term"
        and application.get("result_class") == "proof_term"
        and application.get("output_is_proposition") is True
    )


def _is_data_application(application: dict[str, Any]) -> bool:
    return (
        application.get("detail_status") == "exact_context"
        and application.get("proof_relevance") == "data_term"
        and application.get("result_class") in {"data_value", "proposition_value"}
    )


def _application_shape_errors(application: dict[str, Any]) -> list[str]:
    """Check the invariant emitted by ExtractProofTrace for one application."""
    errors: list[str] = []
    path = application.get("path")
    status = application.get("status")
    detail_status = application.get("detail_status")
    arity = application.get("arity")
    arguments = application.get("arguments")
    if not isinstance(path, str):
        errors.append("missing path")
    if not isinstance(arity, int) or arity < 0:
        errors.append("invalid arity")
        return errors
    if not isinstance(arguments, list):
        errors.append("arguments is not a list")
        return errors
    if detail_status == "structural_only_external":
        if arguments:
            errors.append("structural-only application unexpectedly has argument mappings")
        if status != "structural_only":
            errors.append(f"structural-only application has status {status!r}")
        if application.get("proof_relevance") != "structural_only":
            errors.append("structural-only application has proof relevance")
        if application.get("result_class") != "unknown":
            errors.append("structural-only application has a result class")
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
            errors.append(f"unsupported argument mapping at index {item.get('index')}")
            continue
        for field in ("expected_type", "actual_type", "binderName", "binderInfo"):
            if not isinstance(item.get(field), str):
                errors.append(f"argument {item.get('index')} missing {field}")
        if item.get("definitional_type_match") is not True:
            errors.append(f"argument {item.get('index')} is not definitionally type-correct")
        if not isinstance(item.get("argument"), dict):
            errors.append(f"argument {item.get('index')} missing expression summary")
    if not isinstance(application.get("head_type"), str):
        errors.append("exact-context application missing head_type")
    if not isinstance(application.get("output_type"), str):
        errors.append("exact-context application missing output_type")
    if not isinstance(application.get("output_is_proposition"), bool):
        errors.append("exact-context application missing proposition classification")
    if application.get("proof_relevance") not in {"proof_term", "data_term"}:
        errors.append("exact-context application has an unknown proof relevance")
    if application.get("result_class") not in {"proof_term", "data_value", "proposition_value"}:
        errors.append("exact-context application has an unknown result class")
    if application.get("proof_relevance") == "proof_term":
        if application.get("result_class") != "proof_term":
            errors.append("proof application is not result-classified as a proof term")
        if application.get("output_is_proposition") is not True:
            errors.append("proof application does not return a proposition-typed term")
    elif application.get("output_is_proposition") is True:
        errors.append("non-proof application is marked proposition-typed")
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
        errors.append("exact-context application has no supported context policy")
    return errors


def generated_subarguments(
    records: dict[str, dict[str, Any]],
    edge_rows: dict[str, list[dict[str, Any]]],
    proof_trace: dict[str, Any],
) -> tuple[list[dict[str, Any]], list[dict[str, Any]], dict[str, Any]]:
    """Derive application-spine components from retained elaborated records.

    The reachable declarations emitted by the deterministic proof-cone
    traversal are the input. Heads, argument order, exact input/output types,
    contexts, and type-only references are read from ``ExtractProofTrace.lean``
    output. Local proof targets are materialized as separate interface nodes;
    data-valued applications remain attached as data evidence, and external
    applications remain in the proof trace with an explicit structural-only
    status. The full trace is the evidence source; component JSON stores
    bounded proof/data samples plus exact per-declaration counts so the
    navigable index does not duplicate the entire capture.
    """
    trace_records = {record["declaration"]: record for record in proof_trace.get("records", [])}
    local_records = set(records)
    local_edge_keys = {
        (source, row["target"], row["edge_type"])
        for source, rows in edge_rows.items()
        for row in rows
    }
    errors: list[str] = []
    components: list[dict[str, Any]] = []
    source_to_component: dict[str, str] = {}
    source_data: dict[str, dict[str, Any]] = {}
    target_sources: dict[str, list[dict[str, Any]]] = defaultdict(list)
    contracts: list[dict[str, Any]] = []
    selected_names = [record.get("declaration") for record in proof_trace.get("records", [])]

    for source_name in selected_names:
        if not isinstance(source_name, str):
            errors.append("selected trace record has no declaration name")
            continue
        source_local = _local_name(source_name)
        trace_record = trace_records.get(source_name)
        source_record = records.get(source_local)
        if trace_record is None:
            errors.append(f"missing selected trace record for {source_name}")
            continue
        if source_record is None:
            errors.append(f"missing captured source declaration for {source_local}")
            continue
        applications = trace_record.get("application_records", [])
        references = trace_record.get("reference_records", [])
        if not isinstance(applications, list):
            errors.append(f"{source_name}: application_records is not a list")
            applications = []
        if not isinstance(references, list):
            errors.append(f"{source_name}: reference_records is not a list")
            references = []
        shape_errors = [
            f"{source_name} {application.get('path')}: {message}"
            for application in applications
            if isinstance(application, dict)
            for message in _application_shape_errors(application)
        ]
        errors.extend(shape_errors)
        detailed_apps = [
            application for application in applications
            if isinstance(application, dict) and application.get("detail_status") == "exact_context"
        ]
        relevant_apps = [
            application for application in detailed_apps
            if _is_proof_application(application)
        ]
        data_apps = [application for application in detailed_apps if _is_data_application(application)]
        local_application_targets: dict[str, list[dict[str, Any]]] = defaultdict(list)
        for application in relevant_apps:
            head_name = _app_head_name(application)
            target_local = _local_name(head_name) if head_name else None
            if target_local in local_records:
                local_application_targets[target_local].append(application)
        local_reference_targets: dict[str, list[dict[str, Any]]] = defaultdict(list)
        for reference in references:
            if not isinstance(reference, dict) or reference.get("context") != "proof":
                continue
            if reference.get("declaration_role") not in {
                "theorem", "constructor", "opaque", "axiom"
            }:
                continue
            name = reference.get("name")
            target_local = _local_name(name) if isinstance(name, str) else None
            if target_local in local_records:
                local_reference_targets[target_local].append(reference)
        local_target_names = sorted(set(local_application_targets) | set(local_reference_targets))
        for target_local in local_target_names:
            target_sources[target_local].append({
                "source": source_local,
                "application_record_ids": [
                    _trace_record_id(source_name, application.get("path", ""))
                    for application in local_application_targets[target_local]
                ],
                "proof_reference_record_ids": [
                    _trace_record_id(source_name, reference.get("path", ""))
                    for reference in local_reference_targets[target_local]
                ],
            })
        type_only_references = [
            reference for reference in references
            if isinstance(reference, dict) and reference.get("role") == "type_only_reference"
        ]
        proof_references = [
            reference for reference in references
            if isinstance(reference, dict) and reference.get("role") == "proof_constant_reference"
        ]
        component_id = _trace_component_id(source_name)
        source_to_component[source_local] = component_id
        source_data[source_name] = {
            "source_local": source_local,
            "trace_record": trace_record,
            "source_record": source_record,
            "applications": applications,
            "references": references,
            "detailed_apps": detailed_apps,
            "relevant_apps": relevant_apps,
            "data_apps": data_apps,
            "local_application_targets": local_application_targets,
            "local_reference_targets": local_reference_targets,
            "local_target_names": local_target_names,
            "type_only_references": type_only_references,
            "proof_references": proof_references,
            "shape_errors": shape_errors,
        }
        components.append({
            "id": component_id,
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
                "trace_status": trace_record.get("status"),
                "fuel": trace_record.get("fuel"),
                "application_count": len(applications),
                "structural_only_application_count": sum(
                    application.get("detail_status") == "structural_only_external"
                    for application in applications if isinstance(application, dict)
                ),
                "exact_context_application_count": len(detailed_apps),
                "proof_application_count": len(relevant_apps),
                "data_application_count": len(data_apps),
                "proof_application_sample_count": min(len(relevant_apps), 16),
                "data_application_sample_count": min(len(data_apps), 16),
                "subterm_record_ids": [
                    _trace_record_id(source_name, application.get("path", ""))
                    for application in relevant_apps[:16]
                ],
                "application_records": relevant_apps[:16],
                "application_samples": relevant_apps[:8],
                "data_application_records": data_apps[:16],
                "data_application_samples": data_apps[:8],
                "local_assumption_application_count": sum(
                    application.get("application_role") == "local_assumption_application"
                    for application in relevant_apps
                ),
                "local_data_application_count": sum(
                    application.get("application_role") == "local_assumption_application"
                    for application in data_apps
                ),
                "type_only_reference_count": len(type_only_references),
                "type_only_reference_records": type_only_references[:16],
                "type_only_reference_sample": type_only_references[:16],
                "proof_constant_reference_count": len(proof_references),
                "proof_constant_reference_sample": proof_references[:16],
                "local_target_application_counts": {
                    target: len(rows) for target, rows in sorted(local_application_targets.items())
                },
                "local_target_proof_reference_counts": {
                    target: len(rows) for target, rows in sorted(local_reference_targets.items())
                },
            },
            "validation": {
                "source_trace_present": True,
                "all_application_records_structurally_valid": not shape_errors,
                "ordered_argument_mappings_checked": len(detailed_apps),
                "proof_classification_checked": all(
                    _is_proof_application(application) for application in relevant_apps
                ),
                "data_applications_retained_separately": all(
                    not _is_proof_application(application) for application in data_apps
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
        })
        contracts.append({
            "trace_declaration": source_name,
            "component": component_id,
            "application_count": len(applications),
            "exact_context_application_count": len(detailed_apps),
            "relevant_application_count": len(relevant_apps),
            "proof_application_count": len(relevant_apps),
            "data_application_count": len(data_apps),
            "proof_application_sample_count": min(len(relevant_apps), 16),
            "data_application_sample_count": min(len(data_apps), 16),
            "type_only_reference_count": len(type_only_references),
            "local_target_declarations": local_target_names,
            "shape_error_count": len(shape_errors),
        })

    # Materialize one navigable target interface for each discovered local
    # theorem/opaque application head or proof-context reference.
    target_component_ids: dict[str, str] = {}
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

    relation_buckets: dict[tuple[str, str], dict[str, Any]] = {}
    for source_name, info in source_data.items():
        source_local = info["source_local"]
        source_component = source_to_component[source_local]
        for target_local in info["local_target_names"]:
            target_component = target_component_ids.get(target_local)
            if target_component is None or target_component == source_component:
                continue
            app_rows = info["local_application_targets"].get(target_local, [])
            ref_rows = info["local_reference_targets"].get(target_local, [])
            key = (source_component, target_component)
            bucket = relation_buckets.setdefault(key, {
                "source": source_component,
                "target": target_component,
                "source_declaration": source_local,
                "target_declaration": target_local,
                "application_record_ids": [],
                "proof_reference_record_ids": [],
                "capture_edge_present": (source_local, target_local, "USES_IN_PROOF") in local_edge_keys,
            })
            bucket["application_record_ids"].extend(
                _trace_record_id(source_name, row.get("path", "")) for row in app_rows
            )
            bucket["proof_reference_record_ids"].extend(
                _trace_record_id(source_name, row.get("path", "")) for row in ref_rows
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

    trace_coverage: list[dict[str, Any]] = []
    for source_name in selected_names:
        info = source_data.get(source_name)
        trace_record = trace_records.get(source_name, {})
        if info is None:
            continue
        applications = info["applications"]
        trace_coverage.append({
            "declaration": source_name,
            "status": trace_record.get("status"),
            "kind": trace_record.get("kind"),
            "fuel": trace_record.get("fuel"),
            "component_ids": [source_to_component[info["source_local"]]],
            "application_count": len(applications),
            "structural_only_application_count": sum(
                application.get("detail_status") == "structural_only_external"
                for application in applications if isinstance(application, dict)
            ),
            "exact_context_application_count": len(info["detailed_apps"]),
            "relevant_application_count": len(info["relevant_apps"]),
            "proof_application_count": len(info["relevant_apps"]),
            "data_application_count": len(info["data_apps"]),
            "proof_application_sample_count": min(len(info["relevant_apps"]), 16),
            "data_application_sample_count": min(len(info["data_apps"]), 16),
            "type_only_reference_count": len(info["type_only_references"]),
            "proof_constant_reference_count": len(info["proof_references"]),
            "local_target_declarations": info["local_target_names"],
            "truncated_node_present": any(
                node.get("node") == "truncated"
                for _path, node, _arity in _trace_children(trace_record.get("tree"))
            ),
            "tree_status": trace_record.get("tree_status"),
            "omitted_structural_application_count": trace_record.get(
                "omitted_structural_application_count", 0
            ),
            "omitted_external_reference_count": trace_record.get(
                "omitted_external_reference_count", 0
            ),
        })
    accounted_sources = [item["trace_declaration"] for item in contracts]
    unexpected_no_value = [
        item for item in trace_coverage
        if item.get("status") == "no_value"
        and item.get("kind") not in LEGITIMATE_NO_VALUE_KINDS
    ]
    unavailable = [
        item for item in trace_coverage
        if item.get("status") not in {"captured", "no_value"}
        or item in unexpected_no_value
    ]
    all_structural_traces_captured = all(
        item.get("status") in {"captured", "no_value"}
        and not item.get("truncated_node_present")
        and (
            item.get("status") == "no_value"
            or item.get("tree_status") == "omitted_compact_full_cone"
        )
        for item in trace_coverage
    ) and len(trace_coverage) == len(selected_names) and not unavailable
    audit = {
        "status": "PASS" if not errors else "FAIL",
        "algorithm": (
            "complete reachable Lean Expr records -> exact proof/data application mappings and "
            "explicit structural-only accounting -> discovered target interfaces"
        ),
        "selected_trace_count": len(selected_names),
        "catalog_component_count": len(components),
        "source_component_count": len(source_data),
        "target_component_count": sum(component.get("kind") == "trace_application_target" for component in components),
        "relation_count": len(relations),
        "compiler_relation_count": sum(item["evidence_kind"] == "compiler" for item in relations),
        "trace_only_relation_count": sum(item["evidence_kind"] == "trace" for item in relations),
        "selected_traces_accounted": sorted(selected_names) == sorted(accounted_sources),
        "all_target_application_records_structurally_valid": not errors,
        "all_structural_traces_captured": all_structural_traces_captured,
        "explicit_no_value_count": sum(
            item.get("status") == "no_value" for item in trace_coverage
        ),
        "legitimate_no_value_kinds": sorted(LEGITIMATE_NO_VALUE_KINDS),
        "unexpected_no_value_records": unexpected_no_value,
        "unavailable_trace_records": unavailable,
        "type_only_references_are_not_proof_applications": True,
        "trace_coverage": trace_coverage,
        "contracts": contracts,
        "opaque_boundaries": [
            "The compact full-cone trace preserves exact retained proof/data application records and local references, but omits repeated external structural applications and external references with per-record counts.",
            "The separate boundary artifact retains full Expr trees for the reviewed boundary declarations; opaque theorem bodies are not recursively serialized.",
            "Exact types and local contexts are checked for local proof applications; data applications are retained as data evidence with local contexts explicitly omitted.",
            "A trace-only local boundary is never promoted to a compiler relation when the merged capture has no corresponding USES_IN_PROOF row.",
        ],
        "errors": errors,
    }
    if not audit["selected_traces_accounted"]:
        audit["errors"].append("not every selected trace declaration has an algorithmic component")
        audit["status"] = "FAIL"
    if not audit["all_structural_traces_captured"]:
        audit["errors"].append(
            "one or more selected structural traces are missing, unavailable, or truncated"
        )
        audit["status"] = "FAIL"
    return components, relations, audit


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--capture", type=Path, required=True)
    parser.add_argument("--roles", type=Path, required=True)
    parser.add_argument("--proof-trace", type=Path, required=True)
    parser.add_argument("--source-revision", required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--audit-output", type=Path, required=True)
    args = parser.parse_args()

    capture = load_capture(args.capture)
    records = record_map(capture)
    roles = load_json(args.roles)
    role_audit = validate_roles(roles, records)
    proof_trace = load_json(args.proof_trace)
    if proof_trace.get("generated_from") != "Solution":
        raise SystemExit("proof trace is not the Solution surface")
    graph, edge_rows = proof_graph(records)
    generated, generated_relations, proof_audit = generated_components(records, graph, edge_rows)
    subarguments, subargument_relations, subargument_audit = generated_subarguments(
        records, edge_rows, proof_trace
    )
    if subargument_audit["status"] != "PASS":
        raise SystemExit(
            "trace-backed subargument audit failed:\n" +
            "\n".join(subargument_audit.get("errors", []))
        )

    output = {
        "schema_version": 2,
        "source_repository": capture.get("source_repository"),
        "source_revision": args.source_revision,
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
            "role_labels_input": "data/components.json",
            "proof_trace_input": "data/proof-trace.json.gz",
            "root": ROOT_DECL,
            "proof_trace_selected_declarations": len(proof_trace.get("records", [])),
        },
        "interface_audit": role_audit,
        "proof_decomposition": proof_audit,
        "subargument_decomposition": subargument_audit,
        "proof_trace_summary": {
            "status": "captured",
            "selected": proof_trace.get("selected_declarations", []),
            "artifact_schema": proof_trace.get("schema_version"),
            "capture_policy": proof_trace.get("capture_policy", {}),
            "note": (
                "The compact full-cone artifact is the complete evidence source for retained "
                "proof/data applications and references; component nodes store bounded samples. "
                "Full Expr trees for reviewed boundary declarations are retained in the separate "
                "proof-trace-boundaries artifact."
            ),
        },
        "components": roles.get("components", []) + generated + subarguments,
        "relations": roles.get("relations", []) + generated_relations + subargument_relations,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(output, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    audit = {
        "schema_version": 1,
        "source_revision": args.source_revision,
        "component_manifest": "data/components-generated.json",
        "role_interface_audit": role_audit,
        "proof_decomposition": proof_audit,
        "subargument_decomposition": subargument_audit,
        "empty_dependency_classification": {
            "status": "valid_zero_dependency_shapes_checked_separately",
            "note": "See the capture audit for the complete 32-record list and source ranges.",
        },
    }
    args.audit_output.parent.mkdir(parents=True, exist_ok=True)
    args.audit_output.write_text(json.dumps(audit, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps({"components": len(output["components"]), "relations": len(output["relations"]),
                      "proof_decomposition": proof_audit,
                      "subargument_decomposition": subargument_audit,
                      "role_interface_audit": role_audit}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
