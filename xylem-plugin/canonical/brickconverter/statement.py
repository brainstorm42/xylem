"""Complete captured statements, with explicit conventional-notation coverage.

Capture text is always retained. Unsupported mathematics falls back to that
text, never to an inferred translation. Proof terms are not translated.
"""

from __future__ import annotations

from pathlib import Path
import re

import yaml

from .extractor import _uncurry, expression_from_xylem, select_declaration
from .ir import App, BinOp, Forall, Ident, Lam, Lit
from .profiles import load_profile
from .render import render

DEFAULT_PROFILE = Path(__file__).parent / "profiles" / "engineering.yaml"
DEFAULT_CAPTURE = Path(__file__).parents[1] / "generated" / "xylem" / "declarations.json"

# These are exact Lean operator identities, not a spelling-based inference.
OPERATORS = {
    "Eq": "=", "Ne": "≠", "LE.le": "≤", "LT.lt": "<", "GE.ge": "≥",
    "GT.gt": ">", "HAdd.hAdd": "+", "HSub.hSub": "-", "HMul.hMul": "*",
    "HDiv.hDiv": "/", "HPow.hPow": "^", "And": "∧", "Iff": "↔",
}


def notation_ir(node):
    """Use mathematical operators only for known heads with matching arity."""
    if isinstance(node, App):
        args = [notation_ir(a) for a in node.args]
        head = node.head.semantic_id if isinstance(node.head, Ident) else None
        if head in OPERATORS and len(args) == 2:
            return BinOp(OPERATORS[head], *args)
        if head == "OfNat.ofNat" and len(args) == 1 and isinstance(args[0], Lit):
            return args[0]
        if head == "Matrix.mulVec" and len(args) == 1:
            return App(Ident("Matrix.mulVec.function", True, "Matrix.mulVec.function"), args)
        return App(notation_ir(node.head), args)
    if isinstance(node, Forall):
        # Anonymous, nondependent Pi binders are function/implication arrows.
        # Named/dependent Pi binders remain explicit quantifiers in the renderer.
        if not node.binder_name:
            return BinOp("→", notation_ir(node.binder_type), notation_ir(node.body))
        return Forall(node.binder_name, node.binder_info,
                      notation_ir(node.binder_type), notation_ir(node.body))
    if isinstance(node, Lam):
        return Lam(node.binder_name, notation_ir(node.binder_type), notation_ir(node.body))
    return node


def _application(tree, name, arity):
    """Match an exact captured constant application, never a printed spelling."""
    if not isinstance(tree, dict) or tree.get("node") != "app":
        return None
    head, args = _uncurry(tree)
    explicit = [a["value"] for a in args if a.get("explicit")]
    if head == {"node": "const", "name": name} and len(explicit) == arity:
        return explicit
    return None


def _statement_ir(tree):
    # Mathlib/MeasureTheory/OuterMeasure/AE.lean defines precisely this notation:
    # Filter.Eventually (fun omega => predicate) (MeasureTheory.ae mu).
    # Do not turn an arbitrary filter into a.e., or enable general dependent binders.
    eventual = _application(tree, "Filter.Eventually", 2)
    if eventual:
        predicate, filter_tree = eventual
        measure = _application(filter_tree, "MeasureTheory.ae", 1)
        if (measure and isinstance(predicate, dict) and predicate.get("node") == "lam"
                and predicate.get("binderName")):
            domain, body = predicate.get("binderType"), predicate.get("body")
            for part in (domain, measure[0]):
                _check_tree(part)
            _check_tree(body, bound_name=predicate["binderName"])
            sid = "Filter.Eventually.ae"
            return App(Ident(sid, True, sid), [
                Ident(predicate["binderName"], scope="binder"),
                notation_ir(expression_from_xylem(domain)),
                notation_ir(expression_from_xylem(measure[0])),
                notation_ir(expression_from_xylem(body)),
            ])
    _check_tree(tree)
    return notation_ir(expression_from_xylem(tree))


def _fragment(tree, exact_text, profile):
    if not isinstance(exact_text, str) or not exact_text.strip():
        raise ValueError("capture is missing the exact statement/type text")
    try:
        ir = _statement_ir(tree)
        conventional = render(ir, profile, target="latex", strict=True)
        return {"exact": exact_text, "conventional": conventional, "reason": ""}
    except (ValueError, KeyError, TypeError) as error:
        return {"exact": exact_text, "conventional": None, "reason": str(error)}


def _check_tree(tree, *, bound_name=None):
    """Reject capture forms whose identity or dependent meaning is unavailable."""
    if not isinstance(tree, dict):
        raise ValueError("No expression tree; exact text retained.")
    if tree.get("node") == "fvar" and not tree.get("name"):
        raise ValueError("Unnamed internal variable; exact text retained.")
    if tree.get("node") == "fvar" and bound_name is not None:
        # Xylem records top-level variables by binderIdx, but lambda-local
        # variables by name with a null index. Do not merge those identities.
        local = tree.get("binderIdx") is None
        if local != (tree.get("name") == bound_name):
            raise ValueError("Ambiguous or unresolved a.e. binder scope; exact text retained.")
    if tree.get("node") == "sort":
        raise ValueError("Type/universe declaration retained verbatim.")
    if tree.get("node") == "lam" or (
            tree.get("node") == "forall" and tree.get("binderName")):
        raise ValueError("Named/dependent binder requires a richer notation map; exact text retained.")
    for value in tree.values():
        if isinstance(value, dict) and "node" in value:
            _check_tree(value, bound_name=bound_name)
        elif isinstance(value, list):
            for item in value:
                # Implicit application arguments are retained in the exact
                # signature; ordinary notation does not print typeclass terms.
                if isinstance(item, dict) and item.get("explicit"):
                    _check_tree(item["value"], bound_name=bound_name)


def statement_record(declaration, profile=None):
    """Retain every binder in order, including anonymous and instance binders."""
    profile = profile or load_profile(DEFAULT_PROFILE)
    if not isinstance(declaration.get("binders"), list):
        raise ValueError("capture has no binder list; cannot claim a complete statement")
    if not declaration.get("signature"):
        raise ValueError("capture has no full signature; cannot claim a complete statement")
    binders = []
    for i, binder in enumerate(declaration["binders"]):
        if binder.get("idx") != i:
            raise ValueError("capture binder indices are missing or out of order")
        binders.append({"index": i, "name": binder.get("name"),
                        "binder_info": binder.get("binderInfo"),
                        **_fragment(binder.get("tree"), binder.get("type"), profile)})
    conclusion = _fragment(declaration.get("conclusion_tree"),
                           declaration.get("conclusion"), profile)
    fragments = [*binders, conclusion]
    unsupported = sum(f["conventional"] is None for f in fragments)
    return {
        "declaration": declaration["name"], "module": declaration["module"],
        "kind": declaration.get("kind"), "signature": declaration["signature"],
        "source_file": declaration.get("src_file"), "source_range": declaration.get("range"),
        "binders": binders, "conclusion": conclusion,
        "coverage": {"all_binders_retained": True, "binder_count": len(binders),
                     "conventional_fragments": len(fragments) - unsupported,
                     "exact_text_fragments": unsupported,
                     "proof_translated": False, "formal_check_performed": False,
                     "source_equivalence_checked": False},
    }


def _inline(text):
    return "`" + text.replace("`", "&#96;").replace("|", "&#124;").replace("\n", " ") + "`"


def statement_markdown(record, *, heading=1):
    rows = ["#" * heading + " " + record["declaration"], "",
            "### Parameters and assumptions", "",
            "All entries occur in the captured statement, in the order shown. "
            "An implicit argument is still part of the theorem. Instance arguments "
            "record mathematical structure or Lean representation requirements.", "",
            "| Name | Argument | Conventional notation or retained exact text |",
            "| --- | --- | --- |"]
    if not record["binders"]:
        rows.append("| — | — | No parameters or assumptions in the capture. |")
    for b in record["binders"]:
        value = ("$" + b["conventional"].replace("|", r"\vert ") + "$") if b["conventional"] else _inline(b["exact"])
        name = b["name"] or "(anonymous " + str(b["index"] + 1) + ")"
        rows.append(f"| {_inline(name)} | {b['binder_info']} | {value} |")
    c = record["conclusion"]
    rows += ["", "### Conclusion", ""]
    rows += ["$$", c["conventional"], "$$"] if c["conventional"] else ["```lean", c["exact"], "```"]
    fallback = [b for b in [*record["binders"], c] if b["conventional"] is None]
    if fallback:
        rows += ["", "Some fragments remain in exact Lean notation:", ""]
        rows += [f"- {_inline(b['exact'])}: {b['reason']}" for b in fallback]
    rows += ["", "<details>", "<summary>Exact captured Lean statement</summary>", "",
             "```lean", record["signature"], "```", "", "</details>", ""]
    return "\n".join(rows)


def render_statement(declaration, *, profile=None):
    record = statement_record(declaration, profile)
    notice = ("> Statement correspondence from the selected declaration capture. "
              "This operation does not translate the proof, run Lean, or certify "
              "source equivalence. Unsupported fragments retain their exact text.\n\n")
    return notice + statement_markdown(record), record


def render_brick(brick, capture, *, profile=None):
    """Export only the exact declarations selected by a Brick's existing manifest."""
    brick = Path(brick)
    readme = brick / "README.md" if brick.is_dir() else brick
    match = re.match(r"\A---\s*\n(.*?)\n---(?:\n|$)", readme.read_text(), re.DOTALL)
    if not match:
        raise ValueError(f"{readme}: missing Brick frontmatter")
    metadata = yaml.safe_load(match.group(1))
    names = metadata.get("lean_declarations")
    if not isinstance(names, list) or not names or not all(isinstance(n, str) for n in names):
        raise ValueError(f"{readme}: no exact Lean declaration list")
    if len(names) != len(set(names)):
        raise ValueError(f"{readme}: duplicate declaration names")
    records = [statement_record(select_declaration(capture, name), profile) for name in names]
    lines = [f"# Captured statements — {metadata['brick_id']}", "",
             "Generated by BrickConverter from the Brick's exact declaration list. "
             "Read the Brick's conventional proof first. This appendix retains all "
             "captured parameters and assumptions; unsupported notation remains "
             "explicit. It is not an automatically reconstructed proof.", "",
             "Capture toolchain: " + _inline(str(capture.get("toolchain", "not recorded"))) + ". "
             "No new Lean check or source-equivalence check is performed by this export.", ""]
    lines += [statement_markdown(r, heading=2) for r in records]
    return "\n".join(lines), records
