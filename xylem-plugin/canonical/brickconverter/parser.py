"""Restricted, deterministic parser for declared conventional-math expressions."""

from __future__ import annotations
from dataclasses import dataclass
import re
from .ir import App, BinOp, Ident, Lit, Paren, Unknown
from .profiles import NotationProfile

class ParseError(ValueError):
    pass

TOKEN_RE = re.compile(r"\s*(?:(\\dot\{[A-Za-z][A-Za-z0-9_]*\}|\\[A-Za-z]+)|([A-Za-z][A-Za-z0-9_.]*)|(\d+(?:\.\d+)?)|(<=|>=|!=|->|<->|[=+\-*/^(),<>{}]))")
COMMAND_OPS = {"\\ne": "≠", "\\le": "≤", "\\ge": "≥", "\\in": "∈", "\\to": "→", "\\implies": "→", "\\iff": "↔", "\\land": "∧", "\\cdot": "*"}
PLAIN_OPS = {"=": "=", "+": "+", "-": "-", "*": "*", "/": "/", "^": "^", "<": "<", ">": ">", "<=": "≤", ">=": "≥", "!=": "≠", "->": "→", "<->": "↔"}
PRECEDENCE = {"↔": 5, "→": 6, "∧": 8, "=": 10, "≠": 10, "∈": 10, "<": 10, ">": 10, "≤": 10, "≥": 10, "+": 20, "-": 20, "*": 30, "/": 30, "^": 40}

@dataclass(frozen=True)
class Token:
    kind: str
    text: str

def tokenize(text: str) -> list[Token]:
    text = text.strip()
    if text.startswith("$") and text.endswith("$"):
        text = text.strip("$").strip()
    pos, out = 0, []
    while pos < len(text):
        m = TOKEN_RE.match(text, pos)
        if not m:
            raise ParseError(f"unsupported token at byte {pos}: {text[pos:pos + 20]!r}")
        command, name, number, punctuation = m.groups()
        raw = command or name or number or punctuation
        kind = "number" if number else "name" if name or (command and command not in COMMAND_OPS) else "op" if raw in COMMAND_OPS or raw in PLAIN_OPS else raw
        out.append(Token(kind, raw)); pos = m.end()
    out.append(Token("eof", ""))
    return out

class Parser:
    def __init__(self, text: str, profile: NotationProfile):
        self.tokens, self.pos, self.profile = tokenize(text), 0, profile

    def peek(self) -> Token:
        return self.tokens[self.pos]

    def take(self) -> Token:
        tok = self.peek(); self.pos += 1; return tok

    def expression(self, minimum: int = 0):
        tok = self.take()
        if tok.kind == "number":
            left = Lit(tok.text)
        elif tok.text == "-":
            left = App(Ident("Neg.neg", is_const=True, semantic_id="Neg.neg"), [self.expression(35)])
        elif tok.text == "(":
            left = Paren([self.expression()])
            if self.take().text != ")":
                raise ParseError("missing closing parenthesis")
        elif tok.text == "{":
            left = Paren([self.expression()])
            if self.take().text != "}":
                raise ParseError("missing closing brace")
        elif tok.kind == "name":
            sid = self.profile.alias_index.get(tok.text)
            if sid is None:
                raise ParseError(f"undeclared symbol {tok.text!r}")
            rule = self.profile.symbols[sid]
            left = Ident(tok.text, is_const=rule.kind == "constant", semantic_id=sid)
            if self.peek().text == "(":
                self.take(); args = []
                if self.peek().text != ")":
                    while True:
                        args.append(self.expression())
                        if self.peek().text != ",": break
                        self.take()
                if self.take().text != ")": raise ParseError("missing function-call parenthesis")
                if len(args) != rule.arity: raise ParseError(f"{tok.text!r} expects {rule.arity} arguments, got {len(args)}")
                left = App(left, args)
        else:
            raise ParseError(f"expected expression, found {tok.text!r}")
        while True:
            raw = self.peek().text
            op = COMMAND_OPS.get(raw, PLAIN_OPS.get(raw))
            precedence = PRECEDENCE.get(op or "", -1)
            if precedence < minimum:
                break
            self.take()
            rhs = self.expression(precedence + (0 if op in {"^", "→"} else 1))
            left = BinOp(op, left, rhs)
        return left

def parse_math(text: str, profile: NotationProfile):
    parser = Parser(text, profile)
    result = parser.expression()
    if parser.peek().kind != "eof":
        raise ParseError(f"unconverted suffix begins with {parser.peek().text!r}")
    return result

def parse_math_block(text: str, profile: NotationProfile) -> list:
    """Parse one expression or the rows of a restricted ``aligned`` block.

    Alignment markers and equation tags are presentation metadata. Empty rows
    are ignored; every nonempty row must independently satisfy the grammar.
    """
    body = text.strip().replace(r"\begin{aligned}", "").replace(r"\end{aligned}", "")
    rows = body.split(r"\\")
    parsed = []
    for row in rows:
        row = re.sub(r"\\tag\{[^{}]+\}", "", row).replace("&", "").strip()
        if row:
            parsed.append(parse_math(row, profile))
    if not parsed:
        raise ParseError("mathematical block contains no expressions")
    return parsed
