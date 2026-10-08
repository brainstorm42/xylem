#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Run the copied canonical Xylem and BrickConverter packages from a moved checkout.

All paths in the selected JSON config are package-root relative unless they are
absolute.  The runner only sets process-local environment variables and imports
the existing canonical modules; it does not edit host configuration or install
dependencies.
"""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import sys
from typing import Any


PACKAGE_ROOT = Path(__file__).resolve().parents[1]
XYLEM_ROOT = PACKAGE_ROOT / "canonical" / "xylem"
CONVERTER_ROOT = PACKAGE_ROOT / "canonical" / "brickconverter"


def _path(value: Any, *, key: str, base: Path) -> Path | None:
    if value in (None, ""):
        return None
    if not isinstance(value, str):
        raise ValueError(f"config path {key!r} must be a string or empty")
    candidate = Path(value).expanduser()
    return candidate if candidate.is_absolute() else base / candidate


def load_config(path: Path) -> tuple[dict[str, Path | None], Path]:
    raw = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(raw, dict) or not isinstance(raw.get("paths"), dict):
        raise ValueError("config must contain a paths object")
    relative_to = raw.get("relative_to", "package_root")
    if relative_to == "package_root":
        base = PACKAGE_ROOT
    elif relative_to == "config":
        base = path.parent
    else:
        raise ValueError("relative_to must be 'package_root' or 'config'")
    values = {key: _path(value, key=key, base=base)
              for key, value in raw["paths"].items()}
    options = raw.get("options", {})
    if not isinstance(options, dict):
        raise ValueError("config options must be an object")
    values["compact_index"] = bool(options.get("compact_index", False))
    required = ("dot", "extractor", "vault", "db")
    missing = [key for key in required if values.get(key) is None]
    if missing:
        raise ValueError("config is missing required paths: " + ", ".join(missing))
    return values, path


def _set_xylem_environment(paths: dict[str, Path | None]) -> None:
    """Make canonical status/freshness paths agree with the selected dataset."""
    env = {
        "XYLEM_DB": paths["db"],
        "DATA": paths.get("data") or paths["dot"].parent,
        "XYLEM_VAULT_LEAN": paths["vault"],
    }
    for key, value in env.items():
        if value is not None:
            os.environ[key] = str(value)
    ctrllib = paths.get("ctrllib")
    if ctrllib is None:
        os.environ.pop("CTRLLIB", None)
    else:
        os.environ["CTRLLIB"] = str(ctrllib)


def _check_input_paths(paths: dict[str, Path | None]) -> None:
    for key in ("dot", "extractor", "vault"):
        value = paths.get(key)
        if value is None:
            continue
        if key == "vault":
            if not value.is_dir():
                raise ValueError(f"configured vault directory does not exist: {value}")
        elif not value.is_file():
            raise ValueError(f"configured input file does not exist: {value}")
    for key in ("components",):
        value = paths.get(key)
        if value is not None and not value.is_file():
            raise ValueError(f"configured input file does not exist: {value}")
    value = paths.get("source_root")
    if value is not None and not value.is_dir():
        raise ValueError(f"configured source root does not exist: {value}")


def _import_xylem():
    sys.path.insert(0, str(XYLEM_ROOT))
    from xylem import build, query, server  # type: ignore[import-not-found]
    return build, query, server


def _import_converter():
    # The package directory is canonical/brickconverter; its import parent is
    # canonical. Keep this explicit so invocation from any working directory
    # cannot accidentally resolve an unrelated installed package.
    sys.path.insert(0, str(CONVERTER_ROOT.parent))
    from brickconverter import cli  # type: ignore[import-not-found]
    return cli


def _build(paths: dict[str, Path | None]) -> int:
    _check_input_paths(paths)
    build, _query, _server = _import_xylem()
    argv = [
        "--dot", str(paths["dot"]),
        "--extractor", str(paths["extractor"]),
        "--vault", str(paths["vault"]),
        "--bricks", str(paths.get("bricks") or ""),
        "--bib", str(paths.get("bib") or ""),
        "--ctrllib", str(paths.get("ctrllib") or ""),
        "--source-root", str(paths.get("source_root") or ""),
        "--components", str(paths.get("components") or ""),
        "--db", str(paths["db"]),
    ]
    if paths.get("compact_index"):
        argv.append("--compact-index")
    return build.main(argv)


def _query(paths: dict[str, Path | None], argv: list[str]) -> int:
    _set_xylem_environment(paths)
    _build_module, query, _server = _import_xylem()
    return query.main(["--db", str(paths["db"]), *argv])


def _mcp(paths: dict[str, Path | None]) -> int:
    _set_xylem_environment(paths)
    _build_module, _query, server = _import_xylem()
    server.main()
    return 0


def _converter(paths: dict[str, Path | None], argv: list[str]) -> int:
    cli = _import_converter()
    args = list(argv)
    operation = args[0] if args else ""
    capture = paths.get("converter_capture") or paths["extractor"]
    profile = paths.get("converter_profile") or CONVERTER_ROOT / "profiles" / "engineering.yaml"
    if operation in {"render-statement", "render-brick"}:
        if "--extractor" not in args:
            args[1:1] = ["--extractor", str(capture)]
        if "--profile" not in args:
            args[1:1] = ["--profile", str(profile)]
    elif operation == "render-declaration":
        if "--extractor" not in args:
            args[1:1] = ["--extractor", str(capture)]
        if "--profile" not in args:
            args[1:1] = ["--profile", str(profile)]
    return cli.main(args)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--config", type=Path, default=PACKAGE_ROOT / "canonical" / "example-config.json")
    sub = parser.add_subparsers(dest="command", required=True)
    sub.add_parser("build", help="build the canonical Xylem SQLite graph from configured inputs")
    query = sub.add_parser("query", help="run the canonical Xylem query CLI")
    query.add_argument("args", nargs=argparse.REMAINDER)
    sub.add_parser("mcp", help="run the canonical Xylem MCP stdio server")
    converter = sub.add_parser("convert", help="run the canonical BrickConverter CLI")
    converter.add_argument("args", nargs=argparse.REMAINDER)
    args = parser.parse_args(argv)
    try:
        config_path = args.config.expanduser().resolve()
        paths, _ = load_config(config_path)
        if args.command == "build":
            return _build(paths)
        if args.command == "query":
            return _query(paths, args.args)
        if args.command == "mcp":
            return _mcp(paths)
        if not args.args:
            raise ValueError("convert requires a BrickConverter operation and its arguments")
        return _converter(paths, args.args)
    except ModuleNotFoundError as error:
        missing = error.name or "a runtime dependency"
        print(
            "canonical-runner: missing dependency "
            f"{missing!r}; install the pinned packages from canonical/requirements.txt "
            "in an isolated environment or set XYLEM_PYTHON to one that has them",
            file=sys.stderr,
        )
        return 2
    except (OSError, ValueError, json.JSONDecodeError) as error:
        print(f"canonical-runner: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
