#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Bounded source-first Ctrllib build, extraction, and import-graph runner.

This runner is intentionally independent of ``lake build`` and ``lake exe``.
It uses a user-supplied existing Lake environment only for ``lake env
printenv``/version discovery, invokes the user-supplied Lean executable
directly, puts the candidate source first, and excludes the canonical Ctrllib
source/object paths from child environments. All generated objects, logs, and
captures must live in an external output directory.
"""

from __future__ import annotations

import argparse
from collections.abc import Iterable
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time


RUNNER_VERSION = "ctrllib-source-first-e2e-v1"
PACKAGE_CTRLLIB = Path(__file__).resolve().parents[1]
SOURCE_ROOT = PACKAGE_CTRLLIB / "Ctrllib"
UMBRELLA = PACKAGE_CTRLLIB / "Ctrllib.lean"
EXTRACTOR = PACKAGE_CTRLLIB / "Extract.lean"
LEAN_OPTIONS = (
    "-D", "pp.unicode.fun=true",
    "-D", "relaxedAutoImplicit=false",
    "-D", "weak.linter.mathlibStandardSet=true",
    "-D", "maxSynthPendingDepth=3",
)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def json_write(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def existing_file(value: str, label: str, executable: bool = False) -> Path:
    path = Path(value).expanduser().resolve()
    if not path.is_file():
        raise ValueError(f"{label} does not exist as a file: {value}")
    if executable and not os.access(path, os.X_OK):
        raise ValueError(f"{label} is not executable: {value}")
    return path


def existing_dir(value: str, label: str) -> Path:
    path = Path(value).expanduser().resolve()
    if not path.is_dir():
        raise ValueError(f"{label} does not exist as a directory: {value}")
    return path


def inside(path: Path, root: Path) -> bool:
    return path == root or root in path.parents


def fresh_output(path: Path, label: str) -> Path:
    path = path.expanduser().resolve()
    if inside(path, PACKAGE_CTRLLIB.parent):
        raise ValueError(f"{label} must be outside the candidate package: {path}")
    if path.exists() and any(path.iterdir()):
        raise ValueError(f"{label} must be new or empty: {path}")
    path.mkdir(parents=True, exist_ok=True)
    return path


def candidate_modules() -> tuple[dict[str, Path], dict[str, set[str]]]:
    modules: dict[str, Path] = {}
    imports: dict[str, set[str]] = {}
    for path in sorted(SOURCE_ROOT.rglob("*.lean")):
        name = path.relative_to(PACKAGE_CTRLLIB).with_suffix("").as_posix().replace("/", ".")
        modules[name] = path
        imports[name] = set()
    for name, path in modules.items():
        for line in path.read_text(encoding="utf-8").splitlines():
            words = line.strip().split()
            if len(words) == 2 and words[0] == "import" and words[1] in modules:
                imports[name].add(words[1])
    return modules, imports


def topo_order(modules: dict[str, Path], imports: dict[str, set[str]]) -> list[str]:
    indegree = {name: len(deps) for name, deps in imports.items()}
    dependents: dict[str, set[str]] = {name: set() for name in modules}
    for name, deps in imports.items():
        for dep in deps:
            dependents[dep].add(name)
    ready = sorted(name for name, degree in indegree.items() if degree == 0)
    order: list[str] = []
    while ready:
        name = ready.pop(0)
        order.append(name)
        for child in sorted(dependents[name]):
            indegree[child] -= 1
            if indegree[child] == 0:
                ready.append(child)
                ready.sort()
    if len(order) != len(modules):
        raise ValueError("candidate import graph contains a cycle or unresolved internal import")
    return order


def lake_environment(canonical: Path | None, lake: Path | None) -> dict[str, str]:
    """Read an existing dependency environment without building or installing."""
    if canonical is None and lake is None:
        return {}
    if canonical is None or lake is None:
        raise ValueError("--canonical-ctrllib and --lake must be supplied together")
    result = subprocess.run(
        [str(lake), "env", "printenv"], cwd=canonical, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False,
    )
    if result.returncode != 0:
        raise RuntimeError(
            "lake env printenv failed; supply an existing compatible Lake checkout "
            f"and executable (status {result.returncode})"
        )
    environment: dict[str, str] = {}
    for line in result.stdout.splitlines():
        if "=" in line:
            key, value = line.split("=", 1)
            environment[key] = value
    return environment


def filtered_paths(
    values: Iterable[str], canonical: Path | None, candidate: Path, canonical_build: Path | None,
) -> list[str]:
    result: list[str] = []
    candidate_package = candidate.parent
    canonical_source = (canonical / "Ctrllib").resolve() if canonical is not None else None
    for raw in values:
        if not raw:
            continue
        path = Path(raw).expanduser().resolve()
        if inside(path, candidate_package):
            continue
        if canonical is not None and (path == canonical or (canonical_source is not None and inside(path, canonical_source))):
            continue
        if canonical_build is not None and inside(path, canonical_build):
            continue
        if str(path) not in result:
            result.append(str(path))
    return result


def child_environment(
    *, canonical: Path | None, lake: Path | None, lean: Path, output: Path,
    explicit_lean_paths: list[str] | None, explicit_source_paths: list[str] | None,
) -> tuple[dict[str, str], dict[str, object]]:
    # In explicit-path mode retain ordinary process settings such as HOME,
    # PATH, and Lean's runtime variables, but replace the dependency search
    # paths below.  The canonical/Lake mode instead derives its environment
    # only from the supplied existing checkout.
    base = dict(os.environ) if canonical is None and lake is None else lake_environment(canonical, lake)
    canonical_build = ((canonical / ".lake" / "build" / "lib" / "lean").resolve()
                       if canonical is not None else None)
    lean_paths = explicit_lean_paths if explicit_lean_paths is not None else base.get("LEAN_PATH", "").split(os.pathsep)
    source_paths = explicit_source_paths if explicit_source_paths is not None else base.get("LEAN_SRC_PATH", "").split(os.pathsep)
    filtered_lean = filtered_paths(lean_paths, canonical, PACKAGE_CTRLLIB, canonical_build)
    filtered_source = filtered_paths(source_paths, canonical, PACKAGE_CTRLLIB, canonical_build)
    child = dict(base)
    child["LEAN"] = str(lean)
    child["LEAN_PATH"] = os.pathsep.join([str(output), *filtered_lean])
    child["LEAN_SRC_PATH"] = os.pathsep.join([str(PACKAGE_CTRLLIB), *filtered_source])
    details = {
        "candidate_source_first": True,
        "canonical_ctrllib_source_excluded": True,
        "canonical_ctrllib_build_excluded": True,
        "dependency_lean_path_entry_count": len(filtered_lean),
        "dependency_source_path_entry_count": len(filtered_source),
        "environment_source": "both explicit path lists when supplied; otherwise lake env printenv from the optional user-supplied checkout",
    }
    return child, details


def run_process(
    command: list[str], environment: dict[str, str], cwd: Path,
    stdout_path: Path, stderr_path: Path, timeout: float,
) -> tuple[int | None, float, bool]:
    started = time.monotonic()
    with stdout_path.open("wb") as stdout, stderr_path.open("wb") as stderr:
        process = subprocess.Popen(
            command, cwd=cwd, env=environment, stdout=stdout, stderr=stderr,
            start_new_session=True,
        )
        timed_out = False
        try:
            returncode = process.wait(timeout=max(timeout, 0.1))
        except subprocess.TimeoutExpired:
            timed_out = True
            try:
                os.killpg(os.getpgid(process.pid), signal.SIGTERM)
            except ProcessLookupError:
                pass
            try:
                returncode = process.wait(timeout=10)
            except subprocess.TimeoutExpired:
                try:
                    os.killpg(os.getpgid(process.pid), signal.SIGKILL)
                except ProcessLookupError:
                    pass
                returncode = process.wait()
    return returncode, time.monotonic() - started, timed_out


def tool_versions(lean: Path, lake: Path | None, canonical: Path | None) -> dict[str, str]:
    lean_result = subprocess.run([str(lean), "--version"], cwd=canonical, text=True,
                                 stdout=subprocess.PIPE, check=True)
    versions = {"lean_version": lean_result.stdout.strip()}
    if lake is not None and canonical is not None:
        lake_result = subprocess.run([str(lake), "--version"], cwd=canonical, text=True,
                                     stdout=subprocess.PIPE, check=True)
        versions["lake_version"] = lake_result.stdout.strip()
    return versions


def build(args: argparse.Namespace, output: Path) -> int:
    canonical = existing_dir(args.canonical_ctrllib, "canonical Ctrllib checkout") if args.canonical_ctrllib else None
    lake = existing_file(args.lake, "Lake executable", executable=True) if args.lake else None
    lean = existing_file(args.lean, "Lean executable", executable=True)
    if canonical is None and (not args.lean_path or not args.lean_src_path):
        raise ValueError("without --canonical-ctrllib, supply both --lean-path and --lean-src-path dependency entries")
    if canonical is not None and not (canonical / "lakefile.toml").is_file():
        raise ValueError("canonical Ctrllib checkout must contain lakefile.toml")
    modules, imports = candidate_modules()
    order = topo_order(modules, imports)
    if len(order) != 123:
        raise ValueError(f"expected 123 included Ctrllib modules, found {len(order)}")
    output = fresh_output(output, "build output")
    logs = output / "logs"
    logs.mkdir()
    environment, path_details = child_environment(
        canonical=canonical, lake=lake, lean=lean, output=output,
        explicit_lean_paths=args.lean_path, explicit_source_paths=args.lean_src_path,
    )
    metadata = {
        "schema": RUNNER_VERSION,
        "phase": "build",
        "candidate_source": "ctrllib",
        "candidate_module_count": len(order),
        "candidate_module_order_sha256": hashlib.sha256("\n".join(order).encode()).hexdigest(),
        "toolchain": tool_versions(lean, lake, canonical),
        "lean_options": list(LEAN_OPTIONS),
        "memory_mb": args.memory_mb,
        "per_module_timeout_seconds": args.per_module_timeout,
        "total_timeout_seconds": args.total_timeout,
        "path_policy": path_details,
        "lake_operations": ["env printenv", "--version"] if canonical is not None else [],
        "build_operations": ["direct lean module compilation", "direct lean umbrella compilation", "direct lean extractor compilation"],
    }
    json_write(output / "build-metadata.json", metadata)
    progress: list[dict[str, object]] = []
    failures: list[dict[str, object]] = []
    started = time.monotonic()
    for index, name in enumerate(order, start=1):
        remaining = args.total_timeout - (time.monotonic() - started)
        if remaining <= 0:
            failures.append({"phase": "module", "status": "total_timeout", "completed": index - 1})
            break
        source = modules[name]
        rel = source.relative_to(PACKAGE_CTRLLIB).with_suffix("")
        olean = output / (rel.as_posix() + ".olean")
        ilean = output / (rel.as_posix() + ".ilean")
        olean.parent.mkdir(parents=True, exist_ok=True)
        stdout_path = logs / f"{name.replace('.', '_')}.stdout"
        stderr_path = logs / f"{name.replace('.', '_')}.stderr"
        command = [str(lean), *LEAN_OPTIONS, "-R", str(PACKAGE_CTRLLIB), "-M", str(args.memory_mb),
                   "-j", "1", "-o", str(olean), "-i", str(ilean), str(source)]
        returncode, seconds, timed_out = run_process(
            command, environment, canonical, stdout_path, stderr_path,
            min(args.per_module_timeout, remaining),
        )
        event = {
            "phase": "module", "index": index, "total": len(order), "module": name,
            "source": str(source.relative_to(PACKAGE_CTRLLIB.parent)),
            "returncode": returncode, "seconds": round(seconds, 3),
            "timed_out": timed_out, "olean_exists": olean.is_file(), "ilean_exists": ilean.is_file(),
        }
        progress.append(event)
        print(json.dumps(event), flush=True)
        if timed_out or returncode != 0 or not olean.is_file():
            failures.append(event)
            break
    if not failures and len(progress) == len(order):
        for phase, source, name in (("umbrella", UMBRELLA, "Ctrllib"), ("extractor", EXTRACTOR, "Extract")):
            remaining = args.total_timeout - (time.monotonic() - started)
            if remaining <= 0:
                failures.append({"phase": phase, "status": "total_timeout"})
                break
            olean = output / f"{name}.olean"
            ilean = output / f"{name}.ilean"
            command = [str(lean), *LEAN_OPTIONS, "-R", str(PACKAGE_CTRLLIB), "-M", str(args.memory_mb),
                       "-j", "1", "-o", str(olean), "-i", str(ilean), str(source)]
            stdout_path = logs / f"{phase}.stdout"
            stderr_path = logs / f"{phase}.stderr"
            returncode, seconds, timed_out = run_process(
                command, environment, canonical, stdout_path, stderr_path,
                min(args.per_module_timeout, remaining),
            )
            event = {"phase": phase, "returncode": returncode, "seconds": round(seconds, 3),
                     "timed_out": timed_out, "olean_exists": olean.is_file(), "ilean_exists": ilean.is_file()}
            progress.append(event)
            print(json.dumps(event), flush=True)
            if timed_out or returncode != 0 or not olean.is_file():
                failures.append(event)
                break
    result = {
        "schema": RUNNER_VERSION,
        "phase": "build",
        "candidate_module_count": len(order),
        "completed_module_count": sum(event.get("phase") == "module" and event.get("returncode") == 0 for event in progress),
        "progress": progress,
        "failures": failures,
        "overall_pass": not failures and len(progress) == len(order) + 2,
        "elapsed_seconds": round(time.monotonic() - started, 3),
        "outputs_are_external": True,
    }
    json_write(output / "build-receipt.json", result)
    print(json.dumps({"overall_pass": result["overall_pass"], "completed_module_count": result["completed_module_count"],
                      "candidate_module_count": len(order), "receipt": "build-receipt.json"}, indent=2), flush=True)
    return 0 if result["overall_pass"] else 1


def extract(args: argparse.Namespace, output: Path) -> int:
    canonical = existing_dir(args.canonical_ctrllib, "canonical Ctrllib checkout") if args.canonical_ctrllib else None
    lake = existing_file(args.lake, "Lake executable", executable=True) if args.lake else None
    lean = existing_file(args.lean, "Lean executable", executable=True)
    if canonical is None and (not args.lean_path or not args.lean_src_path):
        raise ValueError("without --canonical-ctrllib, supply both --lean-path and --lean-src-path dependency entries")
    build_output = existing_dir(args.build_output, "source-first build output")
    build_receipt_path = build_output / "build-receipt.json"
    if not build_receipt_path.is_file():
        raise ValueError("build output does not contain build-receipt.json")
    build_receipt = json.loads(build_receipt_path.read_text(encoding="utf-8"))
    if not build_receipt.get("overall_pass") or build_receipt.get("completed_module_count") != 123:
        raise ValueError("the supplied build receipt is not a passing 123-module run")
    output = fresh_output(output, "extraction output")
    environment, path_details = child_environment(
        canonical=canonical, lake=lake, lean=lean, output=build_output,
        explicit_lean_paths=args.lean_path, explicit_source_paths=args.lean_src_path,
    )
    partial = output / "declarations.json.partial"
    stderr_path = output / "extractor.stderr"
    progress_path = output / "extractor-progress.jsonl"
    metadata = {
        "schema": RUNNER_VERSION,
        "phase": "extract",
        "candidate_source": "ctrllib",
        "build_receipt_overall_pass": True,
        "build_completed_module_count": 123,
        "toolchain": tool_versions(lean, lake, canonical),
        "lean_options": list(LEAN_OPTIONS),
        "memory_mb": args.memory_mb,
        "wall_timeout_seconds": args.wall_timeout,
        "sample_seconds": args.sample_seconds,
        "path_policy": path_details,
        "lake_operations": ["env printenv", "--version"] if canonical is not None else [],
        "extract_operations": ["direct lean --run Extract.lean", "JSON schema/count/coverage validation"],
    }
    json_write(output / "extractor-metadata.json", metadata)
    command = [str(lean), *LEAN_OPTIONS, "-R", str(PACKAGE_CTRLLIB), "-M", str(args.memory_mb), "--run", str(EXTRACTOR)]
    started = time.monotonic()
    with partial.open("wb") as stdout, stderr_path.open("wb") as stderr:
        process = subprocess.Popen(command, cwd=canonical, env=environment, stdout=stdout, stderr=stderr,
                                   start_new_session=True)
        timed_out = False
        samples: list[dict[str, object]] = []
        while True:
            returncode = process.poll()
            elapsed = time.monotonic() - started
            event = {"elapsed_seconds": round(elapsed, 3), "returncode": returncode,
                     "stdout_bytes": partial.stat().st_size if partial.exists() else 0,
                     "stderr_bytes": stderr_path.stat().st_size if stderr_path.exists() else 0}
            if not samples or elapsed - float(samples[-1]["elapsed_seconds"]) >= args.sample_seconds or returncode is not None:
                samples.append(event)
                with progress_path.open("a", encoding="utf-8") as stream:
                    stream.write(json.dumps(event) + "\n")
                print(json.dumps(event), flush=True)
            if returncode is not None:
                break
            if elapsed >= args.wall_timeout:
                timed_out = True
                try:
                    os.killpg(os.getpgid(process.pid), signal.SIGTERM)
                except ProcessLookupError:
                    pass
                try:
                    process.wait(timeout=10)
                except subprocess.TimeoutExpired:
                    try:
                        os.killpg(os.getpgid(process.pid), signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                    process.wait()
                break
            time.sleep(min(max(args.sample_seconds, 1.0), 5.0))
    result: dict[str, object] = {
        "schema": RUNNER_VERSION, "phase": "extract", "returncode": process.returncode,
        "timed_out": timed_out, "elapsed_seconds": round(time.monotonic() - started, 3),
        "progress_samples": samples, "declaration_count": 0, "source_module_count": 0,
        "error_count": None, "overall_pass": False, "outputs_are_external": True,
    }
    if not timed_out and process.returncode == 0:
        try:
            data = json.loads(partial.read_text(encoding="utf-8"))
            declarations = data.get("declarations", [])
            modules = {item.get("module") for item in declarations}
            expected_modules = set(candidate_modules()[0])
            projection = data.get("capture_projection")
            result.update({
                "declaration_count": len(declarations), "source_module_count": len(modules),
                "error_count": len(data.get("errors", [])),
                "premise_record_count": sum(len(item.get("premises") or []) for item in declarations),
                "type_premise_edge_count": sum(sum(bool(p.get("in_type")) for p in (item.get("premises") or [])) for item in declarations),
                "proof_premise_edge_count": sum(sum(bool(p.get("in_proof")) for p in (item.get("premises") or [])) for item in declarations),
                "external_premise_record_count": sum(sum(bool(p.get("external")) for p in (item.get("premises") or [])) for item in declarations),
                "source_module_coverage_exact": modules == expected_modules,
                "source_modules_missing": sorted(expected_modules - modules),
                "unexpected_modules": sorted(modules - expected_modules),
                "capture_projection_present": isinstance(projection, dict),
                "capture_projection": projection,
            })
            if not data.get("errors") and modules == expected_modules and declarations and isinstance(projection, dict):
                final = output / "declarations.json"
                final.write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
                result["declarations_sha256"] = sha256(final)
                result["formatted_capture_bytes"] = final.stat().st_size
                result["overall_pass"] = True
        except (OSError, json.JSONDecodeError) as error:
            result["parse_error"] = str(error)
    json_write(output / "extractor-receipt.json", result)
    print(json.dumps({"overall_pass": result["overall_pass"], "returncode": result["returncode"],
                      "timed_out": result["timed_out"], "declaration_count": result["declaration_count"],
                      "source_module_count": result["source_module_count"], "receipt": "extractor-receipt.json"}, indent=2), flush=True)
    return 0 if result["overall_pass"] else 1


def graph(output: Path) -> int:
    output = output.expanduser().resolve()
    if inside(output, PACKAGE_CTRLLIB.parent):
        raise ValueError("graph output must be outside the candidate package")
    if output.exists():
        raise ValueError(f"graph output already exists: {output}")
    modules, imports = candidate_modules()
    edges = sorted((dep, name) for name, deps in imports.items() for dep in deps)
    output.parent.mkdir(parents=True, exist_ok=True)
    lines = ["digraph Ctrllib {"]
    lines.extend(f'  "{dep}" -> "{name}";' for dep, name in edges)
    lines.append("}")
    output.write_text("\n".join(lines) + "\n", encoding="utf-8")
    result = {"schema": RUNNER_VERSION, "phase": "graph", "module_count": len(modules),
              "internal_import_edge_count": len(edges), "output": "external module_graph.dot",
              "sha256": sha256(output), "overall_pass": len(modules) == 123}
    json_write(output.with_name("module-graph-receipt.json"), result)
    print(json.dumps(result, indent=2))
    return 0 if result["overall_pass"] else 1


def add_common(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--canonical-ctrllib",
                        help="optional existing checkout used only for lake env/version discovery; never a source/object input")
    parser.add_argument("--lake", help="optional existing pinned Lake executable used with --canonical-ctrllib")
    parser.add_argument("--lean", required=True, help="existing pinned Lean executable")
    parser.add_argument("--lean-path", action="append", default=None,
                        help="explicit dependency LEAN_PATH entry; in no-checkout mode repeat with --lean-src-path")
    parser.add_argument("--lean-src-path", action="append", default=None,
                        help="explicit dependency LEAN_SRC_PATH entry; in no-checkout mode repeat with --lean-path")
    parser.add_argument("--memory-mb", type=int, default=8192)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="phase", required=True)
    build_parser = sub.add_parser("build", help="compile all candidate modules, umbrella, and extractor")
    add_common(build_parser)
    build_parser.add_argument("--output", required=True, type=Path)
    build_parser.add_argument("--per-module-timeout", type=float, default=600.0)
    build_parser.add_argument("--total-timeout", type=float, default=3600.0)
    extract_parser = sub.add_parser("extract", help="run the compiled candidate extractor once")
    add_common(extract_parser)
    extract_parser.add_argument("--build-output", required=True, type=Path)
    extract_parser.add_argument("--output", required=True, type=Path)
    extract_parser.add_argument("--wall-timeout", type=float, default=1800.0)
    extract_parser.add_argument("--sample-seconds", type=float, default=30.0)
    graph_parser = sub.add_parser("graph", help="write the candidate internal import graph")
    graph_parser.add_argument("--output", required=True, type=Path)
    all_parser = sub.add_parser("all", help="run build, extraction, and import-graph generation")
    add_common(all_parser)
    all_parser.add_argument("--output-root", required=True, type=Path)
    all_parser.add_argument("--per-module-timeout", type=float, default=600.0)
    all_parser.add_argument("--total-timeout", type=float, default=3600.0)
    all_parser.add_argument("--wall-timeout", type=float, default=1800.0)
    all_parser.add_argument("--sample-seconds", type=float, default=30.0)
    args = parser.parse_args(argv)
    try:
        if args.phase == "build":
            return build(args, args.output)
        if args.phase == "extract":
            return extract(args, args.output)
        if args.phase == "graph":
            return graph(args.output)
        root = fresh_output(args.output_root, "E2E output root")
        build_args = argparse.Namespace(**vars(args), output=root / "build")
        code = build(build_args, build_args.output)
        if code:
            return code
        extract_args = argparse.Namespace(**vars(args), build_output=root / "build", output=root / "extract")
        code = extract(extract_args, extract_args.output)
        if code:
            return code
        return graph(root / "graph" / "module_graph.dot")
    except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as error:
        print(f"source-first-e2e: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
