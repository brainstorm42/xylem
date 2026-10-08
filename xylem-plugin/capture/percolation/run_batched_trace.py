#!/usr/bin/env python3
"""Capture the complete local proof cone in bounded, validated Lean batches.

The Lean extractor intentionally keeps the traversal algorithm in one place.
This runner only supplies deterministic batch ranges, checks that every batch
matches the emitted manifest, and merges records without loading the complete
trace into memory.  It is therefore a reproducibility adapter, not a second
source of declaration selection.
"""

from __future__ import annotations

import argparse
import gzip
import io
import json
import os
import subprocess
import tempfile
from pathlib import Path
from typing import Any, Iterator


LEGITIMATE_NO_VALUE_KINDS = {"axiom", "inductive", "ctor", "rec", "quot"}


def load_json(path: Path) -> dict[str, Any]:
    with path.open("r", encoding="utf-8") as stream:
        value = json.load(stream)
    if not isinstance(value, dict):
        raise ValueError(f"expected object in {path}")
    return value


def manifest_items(manifest: dict[str, Any]) -> list[dict[str, Any]]:
    items = manifest.get("items")
    if not isinstance(items, list) or not all(isinstance(item, dict) for item in items):
        raise ValueError("manifest items must be a list of objects")
    names = [item.get("declaration") for item in items]
    if not all(isinstance(name, str) for name in names):
        raise ValueError("manifest item declarations must be strings")
    if len(names) != len(set(names)):
        raise ValueError("manifest contains duplicate declarations")
    if manifest.get("record_count") != len(items):
        raise ValueError("manifest record_count does not match items")
    return items


def batch_command(
    *,
    upstream: Path,
    extractor: Path,
    start: int,
    size: int,
    raw_output: Path,
) -> None:
    environment = os.environ.copy()
    environment.update(
        {
            "XYLEM_TRACE_MODE": "batch",
            "XYLEM_TRACE_BATCH_START": str(start),
            "XYLEM_TRACE_BATCH_SIZE": str(size),
            "XYLEM_TRACE_INCLUDE_TREES": "0",
            "XYLEM_TRACE_COMPACT": "1",
        }
    )
    with raw_output.open("wb") as stream:
        subprocess.run(
            ["lake", "env", "lean", "--run", str(extractor)],
            cwd=upstream,
            env=environment,
            stdout=stream,
            check=True,
        )


def validate_batch(
    batch_path: Path,
    *,
    items: list[dict[str, Any]],
    start: int,
    size: int,
) -> dict[str, Any]:
    batch = load_json(batch_path)
    records = batch.get("records")
    batch_items = batch.get("items")
    expected_items = items[start : start + size]
    if not isinstance(records, list) or not isinstance(batch_items, list):
        raise ValueError(f"batch {start}: records/items must be lists")
    if batch.get("mode") != "batch":
        raise ValueError(f"batch {start}: wrong mode {batch.get('mode')!r}")
    if batch.get("batch_start") != start or batch.get("batch_size") != size:
        raise ValueError(f"batch {start}: range metadata mismatch")
    if batch.get("global_record_count") != len(items):
        raise ValueError(f"batch {start}: global record count mismatch")
    expected_names = [item["declaration"] for item in expected_items]
    actual_item_names = [item.get("declaration") for item in batch_items]
    actual_record_names = [record.get("declaration") for record in records]
    if actual_item_names != expected_names or actual_record_names != expected_names:
        raise ValueError(f"batch {start}: declaration order does not match manifest")
    for record in records:
        if record.get("status") not in {"captured", "no_value"}:
            raise ValueError(f"batch {start}: unavailable declaration record {record.get('declaration')}")
        if (
            record.get("status") == "no_value"
            and record.get("kind") not in LEGITIMATE_NO_VALUE_KINDS
        ):
            raise ValueError(
                f"batch {start}: unexpected no_value kind {record.get('kind')!r} "
                f"for {record.get('declaration')}"
            )
        if record.get("status") == "captured" and record.get("tree_status") != "omitted_compact_full_cone":
            raise ValueError(f"batch {start}: compact tree policy was not recorded")
    return {
        "start": start,
        "record_count": len(records),
        "application_count": sum(len(record.get("application_records", [])) for record in records),
        "reference_count": sum(len(record.get("reference_records", [])) for record in records),
        "proof_application_count": sum(
            application.get("proof_relevance") == "proof_term"
            for record in records
            for application in record.get("application_records", [])
        ),
        "data_application_count": sum(
            application.get("proof_relevance") == "data_term"
            for record in records
            for application in record.get("application_records", [])
        ),
        "statuses": sorted({record.get("status") for record in records}),
        "omitted_structural_application_count": sum(
            record.get("omitted_structural_application_count", 0) for record in records
        ),
        "omitted_external_reference_count": sum(
            record.get("omitted_external_reference_count", 0) for record in records
        ),
    }


def write_trace(
    output: Path,
    *,
    manifest: dict[str, Any],
    items: list[dict[str, Any]],
    batch_summaries: list[dict[str, Any]],
    batch_paths: Iterator[Path],
) -> dict[str, Any]:
    output.parent.mkdir(parents=True, exist_ok=True)
    total_apps = sum(item["application_count"] for item in batch_summaries)
    total_refs = sum(item["reference_count"] for item in batch_summaries)
    total_proof_apps = sum(item["proof_application_count"] for item in batch_summaries)
    total_data_apps = sum(item["data_application_count"] for item in batch_summaries)
    total_omitted_apps = sum(item["omitted_structural_application_count"] for item in batch_summaries)
    total_omitted_refs = sum(item["omitted_external_reference_count"] for item in batch_summaries)
    statuses = sorted({status for item in batch_summaries for status in item["statuses"]})
    header = {
        "schema_version": 1,
        "generated_from": "Solution",
        "toolchain": "leanprover/lean4:v4.32.0",
        "root_declarations": manifest.get("root_declarations", []),
        "selected_declarations": [item["declaration"] for item in items],
        "traversal": {
            "algorithm": manifest.get("algorithm"),
            "root_count": len(manifest.get("root_declarations", [])),
            "record_count": len(items),
            "visited_count": len(items),
            "max_depth": max(item.get("traversal_depth", 0) for item in items),
            "local_namespace_policy": "Percolation, BondPercolation, and Solution names",
            "capture_mode": "validated_bounded_batches",
            "batch_size": batch_summaries[0].get("batch_size", None),
            "batch_count": len(batch_summaries),
        },
        "capture_policy": {
            "exact_records": "local proof/data application spines and retained local references",
            "proof_context": "exact local_context retained for proof-valued applications; data contexts explicitly omitted",
            "expr_tree": "omitted_compact_full_cone; prior validated boundary trees are stored separately",
            "omitted_structural_application_count": total_omitted_apps,
            "omitted_external_reference_count": total_omitted_refs,
            "exact_application_count": total_apps,
            "proof_application_count": total_proof_apps,
            "data_application_count": total_data_apps,
            "retained_reference_count": total_refs,
            "statuses": statuses,
        },
        "batch_summaries": batch_summaries,
    }
    with output.open("wb") as raw:
        with gzip.GzipFile(fileobj=raw, mode="wb", mtime=0) as compressed:
            with io.TextIOWrapper(compressed, encoding="utf-8", newline="") as stream:
                # Keep the opening array in exactly one place.  Appending an
                # opening bracket to the serialization of an empty records
                # array would produce `"records":[[` and a deceptively large
                # but invalid merged trace.
                encoded_header = json.dumps(header, ensure_ascii=False, separators=(",", ":"))
                if not encoded_header.endswith("}"):
                    raise ValueError("trace header did not serialize as an object")
                stream.write(encoded_header[:-1])
                stream.write(',"records":[')
                first = True
                for batch_path in batch_paths:
                    batch = load_json(batch_path)
                    for record in batch["records"]:
                        if not first:
                            stream.write(",")
                        json.dump(record, stream, ensure_ascii=False, separators=(",", ":"))
                        first = False
                stream.write("]}")
    validate_merged_trace(output, items=items)
    return {
        "record_count": len(items),
        "application_count": total_apps,
        "reference_count": total_refs,
        "proof_application_count": total_proof_apps,
        "data_application_count": total_data_apps,
        "omitted_structural_application_count": total_omitted_apps,
        "omitted_external_reference_count": total_omitted_refs,
    }


def validate_merged_trace(output: Path, *, items: list[dict[str, Any]]) -> dict[str, Any]:
    """Validate the merged gzip JSON without materializing the full trace.

    Batch JSON is already parsed and validated before merging.  This check
    validates the serialized header, the gzip CRC, and the top-level envelope
    boundaries while the batch summaries supply the record and evidence
    counts. It deliberately avoids decoding the potentially multi-gigabyte
    nested application arrays a second time.
    """
    marker = b',"records":['
    expected_names = [item["declaration"] for item in items]
    buffer = b""
    with output.open("rb") as raw:
        with gzip.GzipFile(fileobj=raw, mode="rb") as compressed:
            while marker not in buffer:
                chunk = compressed.read(1024 * 1024)
                if not chunk:
                    raise ValueError("merged trace is missing its records array")
                buffer += chunk
            marker_offset = buffer.find(marker)
            encoded_header = buffer[:marker_offset] + b',"records":[]}'
            try:
                header = json.loads(encoded_header)
            except json.JSONDecodeError as error:
                raise ValueError(f"merged trace header is invalid: {error}") from error
            if not isinstance(header, dict):
                raise ValueError("merged trace header is not an object")
            after_marker = buffer[marker_offset + len(marker) :]
            first_nonspace = next((byte for byte in after_marker if byte not in b" \t\r\n"), None)
            if first_nonspace != ord("{"):
                raise ValueError("merged trace records array does not begin with an object")
            tail = after_marker
            while True:
                chunk = compressed.read(1024 * 1024)
                if not chunk:
                    break
                tail = (tail + chunk)[-16:]
            if not tail.rstrip().endswith(b"]}"):
                raise ValueError(f"merged trace has invalid top-level closing bytes: {tail!r}")

    capture_policy = header.get("capture_policy")
    batch_summaries = header.get("batch_summaries")
    if not isinstance(capture_policy, dict) or not isinstance(batch_summaries, list):
        raise ValueError("merged trace is missing capture policy or batch summaries")
    record_count = len(expected_names)
    if header.get("selected_declarations") != expected_names:
        raise ValueError("merged trace selected declaration order differs from manifest")
    if sum(item.get("record_count", 0) for item in batch_summaries) != record_count:
        raise ValueError("merged trace batch summaries do not cover the manifest")
    return {
        "schema_version": header.get("schema_version"),
        "toolchain": header.get("toolchain"),
        "generated_from": header.get("generated_from"),
        "selected_declarations": expected_names,
        "record_count": record_count,
        "application_record_count": capture_policy.get("exact_application_count", 0),
        "reference_record_count": capture_policy.get("retained_reference_count", 0),
        "proof_application_count": capture_policy.get("proof_application_count", 0),
        "data_application_count": capture_policy.get("data_application_count", 0),
        "omitted_structural_application_count": capture_policy.get(
            "omitted_structural_application_count", 0
        ),
        "omitted_external_reference_count": capture_policy.get(
            "omitted_external_reference_count", 0
        ),
        "statuses": capture_policy.get("statuses", ["captured"]),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream", type=Path, required=True)
    parser.add_argument("--extractor", type=Path, required=True)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--batch-size", type=int, default=500)
    args = parser.parse_args()
    if args.batch_size <= 0:
        raise SystemExit("--batch-size must be positive")
    manifest = load_json(args.manifest)
    items = manifest_items(manifest)
    summaries: list[dict[str, Any]] = []
    with tempfile.TemporaryDirectory(prefix="xylem-proof-trace-") as temporary:
        temporary_path = Path(temporary)
        batch_paths: list[Path] = []
        for start in range(0, len(items), args.batch_size):
            size = min(args.batch_size, len(items) - start)
            batch_path = temporary_path / f"batch-{start:06d}.json"
            batch_command(
                upstream=args.upstream,
                extractor=args.extractor,
                start=start,
                size=size,
                raw_output=batch_path,
            )
            summary = validate_batch(batch_path, items=items, start=start, size=size)
            summary["batch_size"] = size
            summaries.append(summary)
            batch_paths.append(batch_path)
            print(json.dumps(summary, sort_keys=True), flush=True)
        result = write_trace(
            args.output,
            manifest=manifest,
            items=items,
            batch_summaries=summaries,
            batch_paths=iter(batch_paths),
        )
    print(json.dumps({"status": "PASS", **result}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
