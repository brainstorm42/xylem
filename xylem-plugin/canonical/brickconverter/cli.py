"""BrickConverter v1 command-line interface."""

from __future__ import annotations
import argparse
import json
from pathlib import Path
import sys
from .document import translate_manifest
from .extractor import declaration_ir, load_capture, select_declaration
from .ir import canonical_json, normalize
from .lean_gate import check_declaration
from .parser import parse_math
from .profiles import ProfileError, load_profile, profile_summary
from .receipts import build_receipt, sha256_bytes, sha256_file, write_receipt
from .render import render
from .statement import DEFAULT_CAPTURE, DEFAULT_PROFILE, render_brick, render_statement
from .catalogue import LEVELS, catalogue_markdown, catalogue_payload, load_bricks, refresh_readers
from .library import library_markdown, library_payload

REPO_ROOT = Path(__file__).parents[2]

def _json(data) -> None:
    print(json.dumps(data, ensure_ascii=False, indent=2, sort_keys=True))

def _profiles(args):
    profile = load_profile(args.profile, args.overlay)
    _json(profile_summary(profile)); return 0

def _render_declaration(args):
    profile = load_profile(args.profile); capture = load_capture(args.extractor)
    decl = select_declaration(capture, args.declaration); ir = declaration_ir(decl)
    output = render(ir, profile, target=args.target, strict=args.strict)
    result = {"schema_version": 1, "declaration": decl["name"], "module": decl["module"], "normalized_ir": json.loads(canonical_json(normalize(ir))), "rendered_output": output, "profile": profile_summary(profile), "warnings": ["Conclusion only; use render-statement for parameters and assumptions."], "errors": [], "acceptance_status": "notation_only", "scope": "conclusion_only", "formal_check_performed": False}
    if args.output: Path(args.output).write_text(output + "\n", encoding="utf-8")
    _json(result); return 0

def _round_trip(args):
    source, target = load_profile(args.source_profile), load_profile(args.target_profile)
    ir = parse_math(args.expression, source)
    latex = render(ir, source, target="latex", strict=args.strict)
    reparsed = parse_math(latex, source)
    lean = render(ir, target, target="lean", strict=args.strict)
    passed = normalize(ir) == normalize(reparsed)
    result = {"schema_version": 2, "ir_round_trip": passed,
              "check_scope": "normalized_ir_equality",
              "check_status": "passed" if passed else "failed",
              "normalized_ir": json.loads(canonical_json(normalize(ir))),
              "conventional": latex, "lean_facing": lean,
              "acceptance_status": "not_assessed", "formal_check_performed": False,
              "generated_output_formally_checked": False,
              "source_equivalence_checked": False, "proof_translated": False}
    _json(result); return 0 if passed else 1

def _translate(args):
    output, results = translate_manifest(args.manifest, args.extractor, args.source_profile, args.target_profile, strict=args.strict)
    Path(args.output).write_text(output, encoding="utf-8")
    complete = all(r.status != "unconverted" for r in results)
    result = {"schema_version": 1, "output": str(Path(args.output)), "output_hash": sha256_bytes(output.encode()), "blocks": [r.__dict__ for r in results], "processing_status": "complete" if complete else "partial", "acceptance_status": "not_assessed", "formal_check_performed": False, "source_equivalence_checked": False, "coverage": {kind: sum(r.formal_coverage == kind for r in results) for kind in ("linked", "conventional-only", "unconverted")}}
    _json(result); return 0 if complete or not args.strict else 1


def _statement(args):
    capture = load_capture(args.extractor)
    profile = load_profile(args.profile)
    if args.operation == "render-brick":
        output, records = render_brick(args.brick, capture, profile=profile)
    else:
        output, record = render_statement(select_declaration(capture, args.declaration), profile=profile)
        records = [record]
    if args.output:
        Path(args.output).write_text(output, encoding="utf-8")
    if args.json:
        _json({"operation": args.operation, "output": args.output,
               "capture_toolchain": capture.get("toolchain"), "statements": records,
               "acceptance_status": "not_assessed"})
    elif not args.output:
        print(output)
    else:
        _json({"output": args.output, "declarations": len(records),
               "all_binders_retained": True, "proof_translated": False,
               "exact_text_fragments": sum(r["coverage"]["exact_text_fragments"] for r in records)})
    return 0

def _check(args):
    profile = load_profile(args.profile); capture = load_capture(args.extractor); decl = select_declaration(capture, args.declaration)
    ir = declaration_ir(decl); output = render(ir, profile, target="lean", strict=True)
    lean = check_declaration(args.ctrllib, decl["name"], decl["module"])
    checks = {"extractor_valid": True, "profile_valid": True, "normalized_ir": True, "matched_existing_declaration": lean["matched_existing_declaration"], "kernel_declaration_check": lean["reused_kernel_checked_theorem"]}
    receipt = build_receipt(operation="check", inputs={"extractor_sha256": sha256_file(args.extractor), "profile_sha256": sha256_file(args.profile)}, outputs={"lean_facing_sha256": sha256_bytes(output.encode())}, profile=profile_summary(profile), declaration={"name": decl["name"], "module": decl["module"], "source": decl.get("source")}, checks=checks, warnings=[], errors=[] if all(checks.values()) else ["Lean declaration gate failed"], metadata={"lean": lean}, check_scope="existing_declaration_check", formal_check_performed=True)
    if args.receipt: write_receipt(args.receipt, receipt)
    _json(receipt); return 0 if receipt["checks_passed"] else 1

def _check_statement(args):
    """Check a reviewer-specified Lean statement against an exact declaration."""
    capture = load_capture(args.extractor)
    decl = select_declaration(capture, args.declaration)
    expected = Path(args.expected_type_file).read_text(encoding="utf-8")
    if not expected.strip():
        raise ValueError("expected type file is empty")
    context = Path(args.context_file).read_text(encoding="utf-8") if args.context_file else ""
    result = check_declaration(args.ctrllib, decl["name"], decl["module"],
                               binder_context=context, expected_type=expected)
    payload = {"operation": "check-statement", "declaration": decl["name"],
               "expected_type_file": str(Path(args.expected_type_file).resolve()),
               "formal_type_check_passed": result['declaration_type_equivalent'],
               "axiom_audit_passed": result['axiom_audit_passed'],
               "source_correspondence": "requires source-to-statement review",
               "lean": result}
    if args.output:
        Path(args.output).write_text(json.dumps(payload, indent=2, ensure_ascii=False)+'\n')
    _json(payload)
    return 0 if result['requested_checks_passed'] else 1


def _library(args):
    payload = library_payload(REPO_ROOT, capture=args.extractor, query=args.query, module=args.module)
    output = (json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True) + "\n" if args.json
              else library_markdown(payload, repo_root=REPO_ROOT, output=args.output))
    if args.output:
        Path(args.output).write_text(output, encoding="utf-8")
    else:
        print(output, end="")
    return 1 if payload["issues"] else 0


def _catalogue(args):
    bricks = load_bricks(REPO_ROOT)
    payload = catalogue_payload(bricks, repo_root=REPO_ROOT,
                                query=args.query, level=args.level,
                                capture=args.extractor)
    if args.json:
        output = json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True) + "\n"
    else:
        destination = Path(args.output) if args.output else REPO_ROOT / "INDEX.md"
        output = catalogue_markdown(payload, output=destination, repo_root=REPO_ROOT)
    if args.output:
        Path(args.output).write_text(output, encoding="utf-8")
    else:
        print(output, end="")
    return 0


def _refresh_readers(args):
    report = refresh_readers(REPO_ROOT, check=args.check,
                             capture=args.extractor, bibliography=args.bibliography,
                             profile=args.profile)
    if args.json:
        _json(report)
    else:
        print(f"refresh-readers: {report['status']}")
        if report.get("updated"):
            print("Updated: " + ", ".join(report["updated"]))
        if report.get("stale"):
            print("Missing or stale: " + ", ".join(item["path"] for item in report["stale"]))
        for issue in report.get("issues", []):
            print("Issue: " + issue)
    return 0 if report["status"] == "ok" else 1

def parser() -> argparse.ArgumentParser:
    ap = argparse.ArgumentParser(prog="python -m brickconverter", description=__doc__)
    sub = ap.add_subparsers(dest="operation", required=True)
    for command in ("render-statement", "render-brick"):
        p = sub.add_parser(command, help="export complete captured statements with all assumptions; does not translate proofs")
        p.add_argument("--extractor", default=str(DEFAULT_CAPTURE))
        p.add_argument("--profile", default=str(DEFAULT_PROFILE))
        p.add_argument("--brick" if command == "render-brick" else "--declaration", required=True)
        p.add_argument("--output")
        p.add_argument("--json", action="store_true", help="include exact statement and translation coverage as JSON")
        p.set_defaults(run=_statement)
    p = sub.add_parser("profile-check"); p.add_argument("profile"); p.add_argument("--overlay"); p.set_defaults(run=_profiles)
    p = sub.add_parser("render-declaration"); p.add_argument("--extractor", required=True); p.add_argument("--profile", required=True); p.add_argument("--declaration", required=True); p.add_argument("--target", choices=("latex", "lean"), default="latex"); p.add_argument("--output"); p.add_argument("--strict", action="store_true"); p.add_argument("--preview", action="store_true"); p.set_defaults(run=_render_declaration)
    p = sub.add_parser("round-trip"); p.add_argument("--source-profile", required=True); p.add_argument("--target-profile", required=True); p.add_argument("--expression", required=True); p.add_argument("--strict", action="store_true"); p.add_argument("--preview", action="store_true"); p.set_defaults(run=_round_trip)
    p = sub.add_parser("translate-document"); p.add_argument("--manifest", required=True); p.add_argument("--extractor", required=True); p.add_argument("--source-profile", required=True); p.add_argument("--target-profile", required=True); p.add_argument("--output", required=True); p.add_argument("--strict", action="store_true"); p.add_argument("--preview", action="store_true"); p.set_defaults(run=_translate)
    p = sub.add_parser("check"); p.add_argument("--extractor", required=True); p.add_argument("--profile", required=True); p.add_argument("--declaration", required=True); p.add_argument("--ctrllib", required=True); p.add_argument("--receipt"); p.set_defaults(run=_check)
    p = sub.add_parser("check-statement", help="check an explicit Lean type; does not translate prose")
    p.add_argument("--extractor", required=True)
    p.add_argument("--declaration", required=True)
    p.add_argument("--expected-type-file", required=True)
    p.add_argument("--context-file")
    p.add_argument("--ctrllib", required=True)
    p.add_argument("--output")
    p.set_defaults(run=_check_statement)
    p = sub.add_parser("library", help="search every captured local declaration and its Brick coverage")
    p.add_argument("--query", help="require all search terms in names, signatures, documentation or Brick titles")
    p.add_argument("--module", help="exact module name, with or without Ctrllib prefix")
    p.add_argument("--output")
    p.add_argument("--json", action="store_true")
    p.add_argument("--extractor", default=str(DEFAULT_CAPTURE))
    p.set_defaults(run=_library)
    p = sub.add_parser("catalogue", help="search and render the current Brick catalogue")
    p.add_argument("--query", help="case-insensitive literal substring")
    p.add_argument("--level", choices=LEVELS)
    p.add_argument("--output", help="write Markdown or JSON to this path")
    p.add_argument("--json", action="store_true", help="emit the searchable catalogue as JSON")
    p.add_argument("--extractor", default=str(DEFAULT_CAPTURE), help="declaration capture to report")
    p.set_defaults(run=_catalogue)
    p = sub.add_parser("refresh-readers", help="regenerate INDEX and Brick reader pages")
    p.add_argument("--check", action="store_true", help="report missing or stale output without writing")
    p.add_argument("--json", action="store_true", help="emit the refresh report as JSON")
    p.add_argument("--extractor", default=str(DEFAULT_CAPTURE))
    p.add_argument("--profile", default=str(DEFAULT_PROFILE))
    p.add_argument("--bibliography", default=str(REPO_ROOT / "bibliography.bib"))
    p.set_defaults(run=_refresh_readers)
    return ap

def main(argv: list[str] | None = None) -> int:
    args = parser().parse_args(argv)
    if getattr(args, "strict", False) and getattr(args, "preview", False):
        raise SystemExit("--strict and --preview are mutually exclusive")
    try: return args.run(args)
    except (ProfileError, ValueError, OSError) as error:
        print(f"brickconverter: {error}", file=sys.stderr); return 2
