"""Pinned Lean acceptance gate for generated types and expressions.

The gate deliberately distinguishes three different claims:

* Lean can resolve the exact, fully qualified declaration name;
* an explicitly supplied generated type is definitionally accepted for that
  declaration; and
* an explicitly supplied generated expression elaborates at its declared type.

Resolving a name is not reported as expression elaboration. Likewise, an
elaborated expression is not reported as a proof unless the supplied proof term
is the named, already accepted declaration.
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile
from typing import Any, Iterable


class LeanGateError(ValueError):
    """Raised when the requested gate cannot be formed deterministically."""


_QUALIFIED_NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)+")
_AXIOM_LINE = re.compile(r"'([^']+)' depends on axioms: \[([^\]]*)\]")
_TEMP_PATH = re.compile(r"(?:/private)?/var/folders/[^\s:]+/T/brickconverter-[^\s:]+")


@dataclass(frozen=True)
class LeanCheckSpec:
    """One exact declaration and its optional generated Lean syntax.

    ``binder_context`` contains only the ``variable`` declarations required by
    ``expected_type`` or ``generated_expression``. ``expected_type`` is checked
    by constructing ``example : expected_type := by exact declaration``. This
    is stronger than ``#check declaration``: Lean must accept the generated type
    as the type of the named theorem, up to definitional equality.
    """

    declaration: str
    module: str
    binder_context: str = ""
    expected_type: str | None = None
    generated_expression: str | None = None
    generated_expression_type: str | None = None

    def __post_init__(self) -> None:
        if not _QUALIFIED_NAME.fullmatch(self.declaration):
            raise LeanGateError(
                f"declaration must be an exact qualified Lean name: {self.declaration!r}"
            )
        if not _QUALIFIED_NAME.fullmatch(self.module):
            raise LeanGateError(f"module must be an exact Lean module name: {self.module!r}")
        if (self.generated_expression is None) != (self.generated_expression_type is None):
            raise LeanGateError(
                "generated_expression and generated_expression_type must be supplied together"
            )


def _sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _run(args: list[str], cwd: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(args, cwd=cwd, text=True, capture_output=True, check=False)


def _lake_command(root: Path) -> list[str]:
    """Use the checkout wrapper when this is a repository checkout.

    The wrapper resolves the pinned compiler without requiring callers to
    export ``ELAN_HOME``.  Keeping a ``lake`` fallback preserves the gate's
    use with an independently supplied Ctrllib directory.
    """

    wrapper = root.parent / "20_tools" / "lake.sh"
    return [str(wrapper)] if wrapper.is_file() else ["lake"]


def _lake_env_lean(root: Path, *arguments: str) -> list[str]:
    return [*_lake_command(root), "--dir", str(root), "env", "lean", *arguments]


def _git_metadata(root: Path) -> dict[str, Any]:
    revision = _run(["git", "rev-parse", "HEAD"], root)
    status = _run(["git", "status", "--porcelain=v1", "--untracked-files=normal"], root)
    if revision.returncode != 0 or status.returncode != 0:
        raise LeanGateError(f"Ctrllib path is not a readable Git worktree: {root}")
    dirty_paths = sorted(line.rstrip() for line in status.stdout.splitlines() if line.strip())
    return {
        "commit": revision.stdout.strip(),
        "dirty": bool(dirty_paths),
        "dirty_paths": dirty_paths,
    }


def _project_metadata(root: Path) -> dict[str, Any]:
    toolchain_path = root / "lean-toolchain"
    manifest_path = root / "lake-manifest.json"
    if not toolchain_path.is_file() or not manifest_path.is_file():
        raise LeanGateError(f"Ctrllib pin files are missing under {root}")

    toolchain_bytes = toolchain_path.read_bytes()
    manifest_bytes = manifest_path.read_bytes()
    manifest = json.loads(manifest_bytes)
    mathlib_revision = next(
        (
            package.get("rev")
            for package in manifest.get("packages", [])
            if package.get("name") == "mathlib"
        ),
        None,
    )
    if not mathlib_revision:
        raise LeanGateError("lake-manifest.json does not pin a Mathlib revision")

    version = _run(_lake_env_lean(root, "--version"), root)
    if version.returncode != 0:
        raise LeanGateError("the pinned `lake env lean --version` command failed")

    return {
        "lean_toolchain": toolchain_bytes.decode("utf-8").strip(),
        "lean_toolchain_sha256": _sha256(toolchain_bytes),
        "lean_version": version.stdout.strip(),
        "mathlib_revision": mathlib_revision,
        "lake_manifest_sha256": _sha256(manifest_bytes),
        "ctrllib_git": _git_metadata(root),
    }


def _render_check_file(specs: tuple[LeanCheckSpec, ...]) -> str:
    imports = "\n".join(f"import {module}" for module in sorted({s.module for s in specs}))
    checks: list[str] = [imports, "", "set_option autoImplicit false", ""]

    for index, spec in enumerate(specs):
        checks.extend(
            [
                f"namespace BrickConverterGate{index}",
                spec.binder_context.strip(),
                f"#check {spec.declaration}",
            ]
        )
        if spec.expected_type is not None:
            checks.extend(
                [
                    "/-- The generated type must match the named accepted declaration. -/",
                    f"example : {spec.expected_type.strip()} := by",
                    f"  exact {spec.declaration}",
                ]
            )
        if spec.generated_expression is not None:
            checks.extend(
                [
                    "/-- The generated expression must elaborate at its declared type. -/",
                    f"example : {spec.generated_expression_type.strip()} := by",
                    f"  exact {spec.generated_expression.strip()}",
                ]
            )
        checks.extend([f"#print axioms {spec.declaration}", f"end BrickConverterGate{index}", ""])

    return "\n".join(checks).rstrip() + "\n"


def _normalize_output(output: str, temporary_root: Path) -> str:
    normalized = output.replace(str(temporary_root), "<temporary>")
    return _TEMP_PATH.sub("<temporary>", normalized)


def _parse_axioms(output: str) -> dict[str, list[str]]:
    parsed: dict[str, list[str]] = {}
    for name, contents in _AXIOM_LINE.findall(output):
        parsed[name] = sorted(item.strip() for item in contents.split(",") if item.strip())
    return parsed


def check_declarations(
    ctrllib: str | Path, specs: Iterable[LeanCheckSpec]
) -> dict[str, Any]:
    """Run one pinned, deterministic Lean gate over one or more declarations.

    A batch shares imports and therefore gives the moving-reference pilot one
    reproducible acceptance command. A failing batch is rejected as a whole;
    diagnostics retain Lean's exact line and column information.
    """

    root = Path(ctrllib).resolve()
    normalized_specs = tuple(specs)
    if not normalized_specs:
        raise LeanGateError("at least one LeanCheckSpec is required")

    metadata = _project_metadata(root)
    body = _render_check_file(normalized_specs)
    with tempfile.TemporaryDirectory(prefix="brickconverter-") as temporary:
        temporary_root = Path(temporary)
        check_file = temporary_root / "BrickConverterCheck.lean"
        check_file.write_text(body, encoding="utf-8")
        actual_command = _lake_env_lean(root, str(check_file))
        process = _run(actual_command, root)
        output = _normalize_output(
            (process.stdout or "") + (process.stderr or ""), temporary_root
        )

    parsed_axioms = _parse_axioms(output)
    batch_passed = process.returncode == 0
    results: list[dict[str, Any]] = []
    for spec in normalized_specs:
        axioms = parsed_axioms.get(spec.declaration)
        axiom_audit_passed = batch_passed and axioms is not None and "sorryAx" not in axioms
        generated_type_elaborated = batch_passed and spec.expected_type is not None
        generated_expression_elaborated = (
            batch_passed and spec.generated_expression is not None
        )
        results.append(
            {
                "declaration": spec.declaration,
                "module": spec.module,
                "declaration_resolved": batch_passed,
                "generated_type_requested": spec.expected_type is not None,
                "generated_type_elaborated": generated_type_elaborated,
                "declaration_type_equivalent": generated_type_elaborated,
                "generated_expression_requested": spec.generated_expression is not None,
                "generated_expression_elaborated": generated_expression_elaborated,
                "axiom_audit_passed": axiom_audit_passed,
                "axioms": axioms or [],
                "contains_sorry_ax": bool(axioms and "sorryAx" in axioms),
            }
        )

    requested_checks_passed = batch_passed and all(
        result["axiom_audit_passed"]
        and (
            not result["generated_type_requested"]
            or result["declaration_type_equivalent"]
        )
        and (
            not result["generated_expression_requested"]
            or result["generated_expression_elaborated"]
        )
        for result in results
    )
    return {
        "schema_version": 1,
        "parsed_successfully": batch_passed,
        "requested_checks_passed": requested_checks_passed,
        "returncode": process.returncode,
        "command": ["lake", "env", "lean", "<temporary>/BrickConverterCheck.lean"],
        "source_hash": _sha256(body.encode("utf-8")),
        "output_hash": _sha256(output.encode("utf-8")),
        "diagnostics": output,
        "results": results,
        **metadata,
    }


def check_declaration(
    ctrllib: str | Path,
    declaration: str,
    module: str,
    *,
    binder_context: str = "",
    expected_type: str | None = None,
    generated_expression: str | None = None,
    generated_expression_type: str | None = None,
) -> dict[str, Any]:
    """Compatibility wrapper for one exact declaration.

    The legacy fields remain available to ``brickconverter check``. Their
    meanings are intentionally narrow: ``matched_existing_declaration`` means
    exact name resolution unless an expected type was supplied, in which case
    it means definitional type equivalence. ``lean_syntax_elaborated`` is true
    only when caller-supplied Lean syntax was actually checked.
    """

    batch = check_declarations(
        ctrllib,
        [
            LeanCheckSpec(
                declaration=declaration,
                module=module,
                binder_context=binder_context,
                expected_type=expected_type,
                generated_expression=generated_expression,
                generated_expression_type=generated_expression_type,
            )
        ],
    )
    result = batch["results"][0]
    syntax_requested = result["generated_type_requested"] or result[
        "generated_expression_requested"
    ]
    syntax_elaborated = (
        (not result["generated_type_requested"] or result["generated_type_elaborated"])
        and (
            not result["generated_expression_requested"]
            or result["generated_expression_elaborated"]
        )
    ) if syntax_requested else False
    matched = (
        result["declaration_type_equivalent"]
        if result["generated_type_requested"]
        else result["declaration_resolved"]
    )
    return {
        **batch,
        "matched_existing_declaration": matched,
        "reused_kernel_checked_theorem": matched and result["axiom_audit_passed"],
        "lean_syntax_elaborated": syntax_elaborated,
        "declaration_resolved": result["declaration_resolved"],
        "declaration_type_equivalent": result["declaration_type_equivalent"],
        "generated_type_elaborated": result["generated_type_elaborated"],
        "generated_expression_elaborated": result["generated_expression_elaborated"],
        "axiom_audit_passed": result["axiom_audit_passed"],
        "axioms": result["axioms"],
    }
