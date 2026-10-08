"""Deterministic conventional and Lean-facing IR renderers."""

from __future__ import annotations
from .ir import App, BinOp, DerivativeAt, Forall, Ident, Lam, Lit, Paren, Proj, Sort, Unknown
from .profiles import NotationProfile, ProfileError

LATEX_OPS = {"=": "=", "≠": r"\ne", "∈": r"\in", "<": "<", ">": ">", "≤": r"\le", "≥": r"\ge", "+": "+", "-": "-", "*": r"\cdot", "/": "/", "^": "^", "→": r"\to", "↔": r"\leftrightarrow", "∧": r"\land"}
LEAN_OPS = {"=": "=", "≠": "≠", "∈": "∈", "<": "<", ">": ">", "≤": "≤", "≥": "≥", "+": "+", "-": "-", "*": "*", "/": "/", "^": "^", "→": "→", "↔": "↔", "∧": "∧"}
PRECEDENCE = {"↔": 5, "→": 6, "∧": 8, "=": 10, "≠": 10, "∈": 10, "<": 10, ">": 10, "≤": 10, "≥": 10, "+": 20, "-": 20, "*": 30, "/": 30, "^": 40}
# This matches the parser's grammar: powers and implication are right-associative;
# the other binary operators are rendered left-associatively.  Parentheses
# are emitted at the boundary where regrouping would change the expression.
ASSOCIATIVITY = {op: "right" if op in {"^", "→"} else "left" for op in PRECEDENCE}
UNARY_PRECEDENCE = 35

class RenderError(ValueError):
    pass

def _ident(node: Ident, profile: NotationProfile, strict: bool) -> str:
    binder_rule = profile.symbols.get(node.name)
    sid = node.semantic_id or (node.name if node.is_const or (
        binder_rule is not None and binder_rule.kind == "binder") else None)
    if sid and sid in profile.symbols:
        return profile.output_for(sid, frame=node.frame)
    if profile.profile_id == "lean" and node.is_const:
        return node.name
    if strict and node.is_const:
        raise RenderError(f"unmapped semantic ID {sid or node.name!r}")
    return node.name

def render(node, profile: NotationProfile, *, target: str, strict: bool = True, parent: int = 0) -> str:
    ops = LATEX_OPS if target == "latex" else LEAN_OPS if target == "lean" else None
    if ops is None: raise RenderError(f"unknown target {target!r}")
    if isinstance(node, Ident): return _ident(node, profile, strict)
    if isinstance(node, Lit): return node.text
    if isinstance(node, Sort): return "Prop" if node.level == "Prop" else "Type"
    if isinstance(node, Paren): return "(" + " ".join(render(x, profile, target=target, strict=strict) for x in node.items) + ")"
    if isinstance(node, BinOp):
        if node.op not in ops: raise RenderError(f"unsupported operator {node.op!r}")
        p = PRECEDENCE[node.op]
        if ASSOCIATIVITY[node.op] == "right":
            lhs_parent, rhs_parent = p + 1, p
        else:
            lhs_parent, rhs_parent = p, p + 1
        lhs = render(node.lhs, profile, target=target, strict=strict, parent=lhs_parent)
        rhs = render(node.rhs, profile, target=target, strict=strict, parent=rhs_parent)
        if target == "latex" and node.op == "^": out = f"{lhs}^{{{rhs}}}"
        else: out = f"{lhs} {ops[node.op]} {rhs}"
        return f"({out})" if p < parent else out
    if isinstance(node, App):
        head_sid = node.head.semantic_id if isinstance(node.head, Ident) else None
        structural = profile.structures.get(head_sid or "")
        if isinstance(node.head, Ident) and node.head.semantic_id == "Neg.neg" and len(node.args) == 1:
            # A unary minus binds less tightly than powers but more tightly
            # than multiplication and addition.  Passing its precedence down
            # is essential when the IR contains -(a + b) without an explicit
            # Paren node.
            argument = render(
                node.args[0], profile, target=target, strict=strict,
                parent=UNARY_PRECEDENCE,
            )
            out = "-" + argument
            return f"({out})" if UNARY_PRECEDENCE < parent else out
        args = [render(a, profile, target=target, strict=strict) for a in node.args]
        if structural:
            if len(args) != structural.arity: raise RenderError(f"{head_sid} expects {structural.arity} arguments")
            return structural.output.format(**dict(zip(structural.input, args)))
        head = render(node.head, profile, target=target, strict=strict)
        return f"{head}({', '.join(args)})" if target == "latex" else f"{head} " + " ".join(f"({a})" for a in args)
    if isinstance(node, Proj): return f"{render(node.base, profile, target=target, strict=strict)}.{node.field}"
    if isinstance(node, Forall):
        binder_type = render(node.binder_type, profile, target=target, strict=strict)
        body = render(node.body, profile, target=target, strict=strict)
        return (rf"\forall {node.binder_name} : {binder_type},\ {body}" if target == "latex" else f"∀ ({node.binder_name} : {binder_type}), {body}")
    if isinstance(node, Lam):
        binder_type = render(node.binder_type, profile, target=target, strict=strict)
        body = render(node.body, profile, target=target, strict=strict)
        return (rf"\lambda {node.binder_name} : {binder_type},\ {body}" if target == "latex" else f"fun ({node.binder_name} : {binder_type}) => {body}")
    if isinstance(node, DerivativeAt):
        expr = render(node.expression, profile, target=target, strict=strict); var = render(node.variable, profile, target=target, strict=strict)
        if target == "latex": return rf"\frac{{d^{node.order}}}{{d {var}^{node.order}}}{expr}"
        return f"iteratedDeriv {node.order} (fun {var} => {expr}) {render(node.evaluation, profile, target=target, strict=strict) if node.evaluation else var}"
    if isinstance(node, Unknown): raise RenderError(f"unresolved node {node.node_type!r}: {node.text}")
    raise RenderError(f"unsupported IR node {type(node).__name__}")
