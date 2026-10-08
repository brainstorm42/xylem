#!/bin/sh
# SPDX-License-Identifier: Apache-2.0
set -eu

HERE=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
PACKAGE_ROOT=$(CDPATH= cd -- "$HERE/.." && pwd)
LOCAL_PYTHON="$PACKAGE_ROOT/.venv/bin/python"

if [ -n "${XYLEM_PYTHON:-}" ]; then
  PYTHON_BIN=$XYLEM_PYTHON
elif [ -n "${PROOFBRICKS_PYTHON:-}" ]; then
  PYTHON_BIN=$PROOFBRICKS_PYTHON
elif [ -x "$LOCAL_PYTHON" ]; then
  PYTHON_BIN=$LOCAL_PYTHON
else
  PYTHON_BIN=$(command -v python3 2>/dev/null || true)
fi

if [ -z "$PYTHON_BIN" ]; then
  echo "proofbricks-xylem: no Python interpreter found" >&2
  echo "Create .venv with Python 3.10+ or set XYLEM_PYTHON explicitly." >&2
  exit 2
fi

if ! "$PYTHON_BIN" -c 'import importlib.metadata as m; import yaml, mcp; assert m.version("PyYAML") == "6.0.3"; assert m.version("mcp") == "2.2.0"' >/dev/null 2>&1; then
  echo "proofbricks-xylem: selected Python is missing the pinned runtime dependencies" >&2
  echo "  selected interpreter: $PYTHON_BIN" >&2
  echo "  required: PyYAML==6.0.3 and mcp==2.2.0" >&2
  echo "Create an isolated environment with:" >&2
  echo "  python3.12 -m venv .venv" >&2
  echo "  .venv/bin/python -m pip install -r canonical/requirements.txt" >&2
  echo "Or set XYLEM_PYTHON to an existing dependency-bearing interpreter." >&2
  echo "The launcher does not install packages." >&2
  exit 2
fi

exec "$PYTHON_BIN" "$HERE/run.py" --config "$HERE/example-config.json" mcp
