"""Typed, restricted reconstruction/change-of-coordinates pilot for AER506.

Frames, vector identities and source locators come from an explicit context.
This module does not infer them from textbook LaTeX. Basis properties are
declared premises, not checked physical facts or a proof of equivalence.
"""

from __future__ import annotations

from dataclasses import dataclass, fields, is_dataclass
import re
from typing import Literal


class FrameNotationError(ValueError):
    """Unsupported syntax, missing declarations or incompatible semantic roles."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise FrameNotationError(message)


def label(value: str, pattern: str, role: str) -> None:
    require(isinstance(value, str) and re.fullmatch(pattern, value) is not None,
            f"{role}: unsupported or missing label {value!r}")


@dataclass(frozen=True)
class VectorSpace:
    identity: str
    dimension: int
    scalar_field: str

    def __post_init__(self):
        require(isinstance(self.identity, str) and bool(self.identity), "missing vector-space identity")
        require(type(self.dimension) is int and self.dimension == 3, "pilot requires dimension 3")
        require(self.scalar_field == "real", "pilot requires real scalar coordinates")


@dataclass(frozen=True)
class GeometricVector:
    identity: str
    space: VectorSpace
    unit: str

    def __post_init__(self):
        label(self.identity, r"[a-z]", "vector")
        require(isinstance(self.space, VectorSpace), "geometric vector requires a vector space")
        require(isinstance(self.unit, str) and bool(self.unit), "vector requires an explicit unit (or '1')")


@dataclass(frozen=True)
class FrameBasis:
    """Ordered geometric basis; source layout is a 3x1 vectrix, not scalar data."""
    frame: str
    space: VectorSpace
    axes: tuple[str, ...]
    handedness: str
    orthonormal: bool
    vectrix_layout: str

    def __post_init__(self):
        label(self.frame, r"[A-Z]", "frame")
        require(isinstance(self.space, VectorSpace), "frame requires a vector space")
        require(type(self.axes) is tuple and len(self.axes) == self.space.dimension,
                "basis axis count must match dimension")
        for axis in self.axes:
            label(axis, r"[a-z][1-3]", "basis axis")
        require(len(set(self.axes)) == len(self.axes), "basis axes must be distinct and ordered")
        require(self.handedness == "right", "source pilot requires explicit right handedness")
        require(self.orthonormal is True, "source pilot requires declared orthonormal basis")
        require(self.vectrix_layout == "column", "source pilot requires resolved column-vectrix convention")


@dataclass(frozen=True)
class Coordinates:
    """Scalar column for one geometric vector in one ordered frame basis."""
    vector: GeometricVector
    basis: FrameBasis

    def __post_init__(self):
        require(isinstance(self.vector, GeometricVector) and isinstance(self.basis, FrameBasis),
                "coordinates require a geometric vector and a frame basis")
        require(self.vector.space == self.basis.space, "coordinate vector-space mismatch")

    @property
    def shape(self):
        return (self.basis.space.dimension, 1)


@dataclass(frozen=True)
class ChangeOfBasis:
    """Passive dimensionless map from source scalar coordinates to target ones."""
    target: FrameBasis
    source: FrameBasis
    interpretation: str
    matrix_kind: str = "proper-rotation"

    def __post_init__(self):
        require(isinstance(self.target, FrameBasis) and isinstance(self.source, FrameBasis),
                "change of basis requires directed frame endpoints")
        require(self.target.space == self.source.space, "matrix vector-space mismatch")
        require(self.interpretation == "passive", "active rotation requires a separate operation")
        require(self.matrix_kind == "proper-rotation", "source pilot supports proper rotations only")
        require(self.target.frame != self.source.frame or self.target == self.source,
                "same frame label has conflicting basis definitions")

    @property
    def shape(self):
        return (self.target.space.dimension, self.source.space.dimension)


@dataclass(frozen=True)
class Reconstruct:
    basis: FrameBasis
    coordinates: Coordinates

    def __post_init__(self):
        require(isinstance(self.basis, FrameBasis) and isinstance(self.coordinates, Coordinates),
                "reconstruction requires a basis and scalar coordinates")
        require(self.basis == self.coordinates.basis, "reconstruction basis/order mismatch")


@dataclass(frozen=True)
class ApplyBasisChange:
    """Ordered left-to-right matrix factors; the rightmost factor acts first."""
    factors: tuple[ChangeOfBasis, ...]
    coordinates: Coordinates

    def __post_init__(self):
        require(type(self.factors) is tuple and bool(self.factors), "missing directed matrix factors")
        require(isinstance(self.coordinates, Coordinates), "matrix application requires scalar coordinates")
        require(all(isinstance(f, ChangeOfBasis) for f in self.factors), "invalid matrix factor")
        for left, right in zip(self.factors, self.factors[1:]):
            require(left.source == right.target, "matrix composition frame/order mismatch")
        require(self.factors[-1].source == self.coordinates.basis,
                "matrix source does not match input coordinates")
        definitions = {}
        for factor in self.factors:
            for basis in (factor.target, factor.source):
                require(basis.frame not in definitions or definitions[basis.frame] == basis,
                        "same frame label has conflicting basis definitions")
                definitions[basis.frame] = basis


@dataclass(frozen=True)
class SourceLocator:
    url: str
    author: str
    year: int
    printed_page: int
    equation: str
    relation: str
    source_id: str

    def __post_init__(self):
        require(all(isinstance(s, str) and bool(s) for s in (self.url, self.author, self.equation)),
                "source locator requires URL, author and equation")
        require(type(self.year) is int and type(self.printed_page) is int,
                "source locator requires integer year and printed page")
        require(self.relation in {"transcribed", "derived-example"}, "missing source/example distinction")
        label(self.source_id, r"[a-z0-9.-]+", "source/version identity")


@dataclass(frozen=True)
class FrameEquation:
    lhs: GeometricVector | Coordinates
    rhs: Reconstruct | ApplyBasisChange
    provenance: SourceLocator

    def __post_init__(self):
        require(isinstance(self.provenance, SourceLocator), "equation requires source provenance")
        if isinstance(self.rhs, Reconstruct):
            require(isinstance(self.lhs, GeometricVector) and self.lhs == self.rhs.coordinates.vector,
                    "reconstruction must preserve geometric vector identity/unit")
        elif isinstance(self.rhs, ApplyBasisChange):
            require(isinstance(self.lhs, Coordinates), "coordinate change requires scalar-coordinate lhs")
            require(self.lhs.vector == self.rhs.coordinates.vector, "coordinate change changed vector identity/unit")
            require(self.lhs.basis == self.rhs.factors[0].target, "matrix target does not match lhs coordinates")
        else:
            raise FrameNotationError("unsupported equation operation")


@dataclass(frozen=True)
class Context:
    frames: tuple[FrameBasis, ...]
    vectors: tuple[GeometricVector, ...]
    provenance: SourceLocator

    def __post_init__(self):
        require(type(self.frames) is tuple and all(isinstance(f, FrameBasis) for f in self.frames),
                "context requires explicitly declared frames")
        require(type(self.vectors) is tuple and all(isinstance(v, GeometricVector) for v in self.vectors),
                "context requires explicitly declared vectors")
        require(len({f.frame for f in self.frames}) == len(self.frames), "ambiguous frame declarations")
        require(len({v.identity for v in self.vectors}) == len(self.vectors), "ambiguous vector declarations")
        require(isinstance(self.provenance, SourceLocator), "context requires source provenance")

    def frame(self, name: str) -> FrameBasis:
        for basis in self.frames:
            if basis.frame == name:
                return basis
        raise FrameNotationError(f"undeclared frame {name!r}; no inferred default")

    def vector(self, name: str) -> GeometricVector:
        for vector in self.vectors:
            if vector.identity == name:
                return vector
        raise FrameNotationError(f"undeclared geometric vector {name!r}")


Dialect = Literal["vatankhahghadim-2019", "frame-matrix"]


def _glyph(value, dialect: Dialect) -> str:
    source = dialect == "vatankhahghadim-2019"
    if isinstance(value, GeometricVector):
        command = "underrightarrow" if source else "vec"
        return rf"\{command}{{{value.identity}}}"
    if isinstance(value, FrameBasis):
        if source:
            return rf"\underrightarrow{{\mathcal{{F}}}}_{{{value.frame}}}^{{\top}}"
        return rf"\mathcal{{B}}_{{{value.frame}}}"
    if isinstance(value, Coordinates):
        if source:
            return rf"\boldsymbol{{{value.vector.identity}}}_{{{value.basis.frame}}}"
        return rf"[{value.vector.identity}]_{{{value.basis.frame}}}"
    if isinstance(value, ChangeOfBasis):
        if source:
            return rf"C_{{{value.target.frame}{value.source.frame}}}"
        return rf"{{}}^{{{value.target.frame}}}R_{{{value.source.frame}}}"
    raise FrameNotationError("unsupported rendered object")


def render_equation(equation: FrameEquation, dialect: Dialect) -> str:
    require(dialect in {"vatankhahghadim-2019", "frame-matrix"}, "unsupported dialect")
    require(isinstance(equation, FrameEquation), "rendering requires a typed frame equation")
    if isinstance(equation.rhs, Reconstruct):
        factors = [equation.rhs.basis]
    else:
        factors = list(equation.rhs.factors)
    factors.append(equation.rhs.coordinates)
    return _glyph(equation.lhs, dialect) + " = " + " ".join(_glyph(f, dialect) for f in factors)


# Only these two deliberately restricted grammars are supported. In particular,
# an untransposed source vectrix, an unlabeled vector, C_AB^T, generic products,
# active rotations and arbitrary LaTeX are not interpreted by this parser.
_TOKENS = {
    "vatankhahghadim-2019": (
        ("basis", r"\\underrightarrow\{\\mathcal\{F\}\}_\{([A-Z])\}\^\{\\top\}"),
        ("vector", r"\\underrightarrow\{([a-z])\}"),
        ("coordinates", r"\\boldsymbol\{([a-z])\}_\{([A-Z])\}"),
        ("matrix", r"C_\{([A-Z])([A-Z])\}"),
    ),
    "frame-matrix": (
        ("basis", r"\\mathcal\{B\}_\{([A-Z])\}"),
        ("vector", r"\\vec\{([a-z])\}"),
        ("coordinates", r"\[([a-z])\]_\{([A-Z])\}"),
        ("matrix", r"\{\}\^\{([A-Z])\}R_\{([A-Z])\}"),
    ),
}


def _terms(text: str, dialect: Dialect, context: Context) -> list:
    terms = []
    rest = text.strip()
    while rest:
        for kind, pattern in _TOKENS[dialect]:
            match = re.match(pattern, rest)
            if match:
                names = match.groups()
                if kind == "vector":
                    value = context.vector(names[0])
                elif kind == "basis":
                    value = context.frame(names[0])
                elif kind == "coordinates":
                    value = Coordinates(context.vector(names[0]), context.frame(names[1]))
                else:
                    value = ChangeOfBasis(context.frame(names[0]), context.frame(names[1]), "passive")
                terms.append(value)
                rest = rest[match.end():].lstrip()
                break
        else:
            raise FrameNotationError(f"unsupported or ambiguous syntax near {rest[:50]!r}")
    return terms


def parse_equation(text: str, dialect: Dialect, context: Context) -> FrameEquation:
    require(dialect in _TOKENS, "unsupported dialect")
    require(isinstance(context, Context), "explicit typed context is required")
    require(isinstance(text, str) and text.count("=") == 1, "expected one supported equality")
    left_text, right_text = text.split("=")
    left, right = _terms(left_text, dialect, context), _terms(right_text, dialect, context)
    require(len(left) == 1 and len(right) >= 2, "expected one lhs and a basis/matrix application")
    require(isinstance(right[-1], Coordinates), "application must end with scalar coordinates")
    if len(right) == 2 and isinstance(right[0], FrameBasis):
        rhs = Reconstruct(right[0], right[1])
    else:
        rhs = ApplyBasisChange(tuple(right[:-1]), right[-1])
    return FrameEquation(left[0], rhs, context.provenance)


# An explicit extension envelope keeps production's untyped schema v1 intact.
# The node-tag convention follows BrickConverter.ir; it is not wire-compatible
# with production from_json until that decoder explicitly adopts the extension.
_NODE_TYPES = {cls.__name__: cls for cls in (
    VectorSpace, GeometricVector, FrameBasis, Coordinates, ChangeOfBasis,
    Reconstruct, ApplyBasisChange, SourceLocator, FrameEquation,
)}
_ENVELOPE = "brickconverter.frame_notation.v1"


def _encode(value):
    if is_dataclass(value):
        return {"node": type(value).__name__, **{f.name: _encode(getattr(value, f.name)) for f in fields(value)}}
    if isinstance(value, tuple):
        return [_encode(item) for item in value]
    return value


def to_json(equation: FrameEquation) -> dict:
    require(isinstance(equation, FrameEquation), "serialization requires a typed frame equation")
    return {"schema_version": 1, "ir_extension": _ENVELOPE, "expression": _encode(equation)}


def _decode(value):
    if isinstance(value, list):
        return tuple(_decode(item) for item in value)
    if not isinstance(value, dict):
        return value
    kind = value.get("node")
    require(isinstance(kind, str), "invalid frame IR node tag")
    cls = _NODE_TYPES.get(kind)
    require(cls is not None, "unknown frame IR node")
    expected = {f.name for f in fields(cls)} | {"node"}
    require(set(value) == expected, f"missing or unknown fields for {cls.__name__}")
    return cls(**{k: _decode(v) for k, v in value.items() if k != "node"})


def from_json(payload: dict) -> FrameEquation:
    require(type(payload) is dict and set(payload) == {"schema_version", "ir_extension", "expression"},
            "invalid frame IR envelope")
    require(type(payload["schema_version"]) is int and payload["schema_version"] == 1
            and payload["ir_extension"] == _ENVELOPE, "unsupported frame IR extension/version")
    equation = _decode(payload["expression"])
    require(isinstance(equation, FrameEquation), "frame IR root must be an equation")
    return equation
