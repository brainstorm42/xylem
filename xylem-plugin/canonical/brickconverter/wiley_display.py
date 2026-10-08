"""Named Wiley-2013 display style for the reviewed typed frame-equation IR.

Display only: no Wiley text/PDF parser. Frame labels are explicit injective
aliases, not new basis identities. Original equation provenance is retained.
"""

from dataclasses import dataclass
from typing import ClassVar

from .frame_notation import (
    ChangeOfBasis, Coordinates, FrameBasis, FrameEquation, GeometricVector,
    Reconstruct, label, require, to_json,
)


@dataclass(frozen=True)
class WileyDisplayProfile:
    frame_labels: tuple[tuple[str, str], ...]
    profile_id: ClassVar[str] = "deruiter-damaren-forbes-2013"

    def __post_init__(self):
        require(type(self.frame_labels) is tuple, "Wiley frame aliases must be an immutable tuple")
        for pair in self.frame_labels:
            require(type(pair) is tuple and len(pair) == 2, "Wiley aliases require frame/label pairs")
            label(pair[0], r"[A-Z]", "semantic frame")
            # Single-digit labels keep C_ij unambiguous in this narrow style.
            label(pair[1], r"[1-9]", "Wiley display frame")
        require(len({pair[0] for pair in self.frame_labels}) == len(self.frame_labels),
                "duplicate semantic frames in Wiley aliases")
        require(len({pair[1] for pair in self.frame_labels}) == len(self.frame_labels),
                "Wiley frame aliases must be injective")

    def frame_label(self, basis: FrameBasis) -> str:
        for frame, display in self.frame_labels:
            if frame == basis.frame:
                return display
        from .frame_notation import FrameNotationError
        raise FrameNotationError(f"missing explicit Wiley alias for frame {basis.frame!r}")


def _glyph(value, profile: WileyDisplayProfile) -> str:
    if isinstance(value, GeometricVector):
        return rf"\vec{{\mathbf{{{value.identity}}}}}"
    if isinstance(value, FrameBasis):
        return rf"\vec{{\mathcal{{F}}}}_{{{profile.frame_label(value)}}}^{{\top}}"
    if isinstance(value, Coordinates):
        return rf"\mathbf{{{value.vector.identity}}}_{{{profile.frame_label(value.basis)}}}"
    if isinstance(value, ChangeOfBasis):
        return rf"\mathbf{{C}}_{{{profile.frame_label(value.target)}{profile.frame_label(value.source)}}}"
    from .frame_notation import FrameNotationError
    raise FrameNotationError("unsupported Wiley display object")


def render_wiley(equation: FrameEquation, profile: WileyDisplayProfile) -> str:
    require(isinstance(equation, FrameEquation), "Wiley display requires a typed frame equation")
    require(isinstance(profile, WileyDisplayProfile), "Wiley display requires explicit frame aliases")
    factors = ([equation.rhs.basis] if isinstance(equation.rhs, Reconstruct)
               else list(equation.rhs.factors))
    factors.append(equation.rhs.coordinates)
    return _glyph(equation.lhs, profile) + " = " + " ".join(_glyph(factor, profile) for factor in factors)


def display_payload(equation: FrameEquation, profile: WileyDisplayProfile) -> dict:
    """Keep the source equation/metadata alongside the book's display convention."""
    return {
        "profile_id": profile.profile_id,
        "profile_version": 1,
        "profile_origin": {
            "source_id": "deruiter-damaren-forbes.2013.ed1.chapter1",
            "url": "https://catalogimages.wiley.com/images/db/pdf/9781118342367.excerpt.pdf",
            "reconstruction_locator": "printed p. 7, Eqs. 1.11-1.13",
        },
        "frame_aliases": dict(profile.frame_labels),
        "rendered": render_wiley(equation, profile),
        "ir": to_json(equation),
        "acceptance_status": "not_assessed",
        "wiley_text_parsing": "unsupported",
    }
