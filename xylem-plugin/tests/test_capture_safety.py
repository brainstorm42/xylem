#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Check manifest-root enumeration and no-clobber capture behavior."""

from __future__ import annotations

import json
from pathlib import Path
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from capture.capture_declaration import manifest_library_roots  # noqa: E402


def main() -> int:
    with tempfile.TemporaryDirectory(prefix="proofbricks-capture-safety-") as scratch:
        root = Path(scratch)
        sentinel = root / "existing.json"
        sentinel.write_text("sentinel\n", encoding="utf-8")
        result = subprocess.run(
            [
                sys.executable,
                "-S",
                str(ROOT / "capture" / "capture_declaration.py"),
                "--lean",
                str(root / "missing-lean"),
                "--library-root",
                str(root / "missing-library"),
                "--capture-source",
                str(root / "missing-capture-source.lean"),
                "--output",
                str(sentinel),
            ],
            capture_output=True,
            text=True,
            check=False,
        )
        assert result.returncode == 2
        assert sentinel.read_text(encoding="utf-8") == "sentinel\n"
        assert "refusing to overwrite" in result.stderr

        manifest_root = root / "lake-manifest.json"
        names = ["mathlib", "importGraph", "batteries"]
        for name in names:
            (root / ".lake" / "packages" / name / ".lake" / "build" / "lib" / "lean").mkdir(parents=True)
        manifest_root.write_text(
            json.dumps({"packagesDir": ".lake/packages", "packages": [{"name": name} for name in names]}),
            encoding="utf-8",
        )
        roots = manifest_library_roots(manifest_root)
        assert [path.parent.parent.parent.parent.name for path in roots] == names
    print("capture_output_no_clobber: PASS")
    print("manifest_library_roots: PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
