"""Repository-derived Xylem paths and environment overrides."""

import os
from pathlib import Path


PACKAGE_ROOT = Path(__file__).resolve().parent.parent
TOOLS_ROOT = PACKAGE_ROOT.parent
LEAN_ROOT = TOOLS_ROOT.parent
GENERATED_ROOT = TOOLS_ROOT / "generated" / "xylem"


def clearfocus_root() -> Path:
    return Path(os.environ.get("CLEARFOCUS_ROOT", str(LEAN_ROOT.parent / "20_Focus")))


def vault_lean_default() -> Path:
    return Path(os.environ.get(
        "XYLEM_VAULT_LEAN",
        str(clearfocus_root() / "99_archive" / "20_migration" / "historical_focus_proof_reference"),
    ))


def data_default() -> Path:
    return Path(os.environ.get("DATA", str(GENERATED_ROOT)))


def ctrllib_default() -> Path:
    return Path(os.environ.get("CTRLLIB", str(LEAN_ROOT / "ctrllib")))
