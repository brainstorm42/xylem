<!-- SPDX-License-Identifier: Apache-2.0 -->
# Public dependency bootstrap tested on macOS arm64

This is a portable transcription of the successful Air consumer test, with caller-selected paths replacing test-machine paths. It provisions dependencies separately from the shipped direct-Lean runner. These commands do download public packages; the runner in [REGENERATE-FULL.md](REGENERATE-FULL.md) does not.

The test used an existing Python 3.12.13 interpreter and existing Git, curl, tar, and zstd executables. It did not test installation of those prerequisites onto a blank macOS system. The earlier Python baseline was 3.12.14. The direct Python pins are PyYAML 6.0.3 and MCP 2.2.0. This procedure is macOS arm64 only; Windows and other platforms remain unverified.

## Select new isolated paths

Use bash or zsh. Set `PACKAGE` to the combined release root, `WORK` to a new external directory, and `PYTHON_BASE` to the existing Python 3.12 interpreter. Use a new directory for the pinned public dependency checkouts.

```sh
set -eu
set -o pipefail
PACKAGE=/path/to/combined-release
WORK=/path/to/new-air-consumer-test
PYTHON_BASE=/path/to/python3.12
mkdir "$WORK"
"$PYTHON_BASE" -m venv "$WORK/venv"
PYTHON="$WORK/venv/bin/python"
"$PYTHON" -m pip install --no-cache-dir \
  -r "$PACKAGE/xylem-plugin/canonical/requirements.txt"
```

The test installed into an external venv and recorded the resolved transitive versions. The release pins direct dependencies; it does not supply a complete transitive Python lockfile. PyYAML and MCP reported MIT licenses.

## Fetch the exact public source closure

The shipped [Lake manifest](../../../ctrllib/lake-manifest.json) pins all nine repositories, including Mathlib at `5ed2965256430c3649e86755f9576b54eca72435` (`v4.34.0`). Fetch the exact commits; do not resolve their branch names to newer revisions.

```sh
"$PYTHON" - "$PACKAGE" "$WORK" <<'PY'
from pathlib import Path
import json, subprocess, sys
package, work = map(Path, sys.argv[1:])
deps = work / "public-dependencies"
deps.mkdir()
manifest = json.loads((package / "ctrllib/lake-manifest.json").read_text())
for item in manifest["packages"]:
    root = deps / item["name"]
    root.mkdir()
    commands = [
        ["git", "init", str(root)],
        ["git", "-C", str(root), "remote", "add", "origin", item["url"]],
        ["git", "-C", str(root), "-c", "credential.helper=",
         "fetch", "--depth=1", "origin", item["rev"]],
        ["git", "-C", str(root), "checkout", "--detach", "FETCH_HEAD"],
    ]
    for command in commands:
        subprocess.run(command, check=True)
    actual = subprocess.check_output(
        ["git", "-C", str(root), "rev-parse", "HEAD"], text=True).strip()
    assert actual == item["rev"]
    print(item["name"], actual)
PY
```

Before any Lake execution, inspect the fetched licenses and all `lakefile*` files. The Air check found Apache-2.0 licenses except `Cli` (MIT). The pinned Mathlib file has a `post_update` cache-fetch hook, and ProofWidgets defines npm build targets. No top-level `run_cmd` or patch operation was found in these pinned configurations. The successful route used Mathlib's cache command; it did not run Ctrllib's ordinary `lake build`/`lake exe extract`, a Lake update, or an npm install. No NASALib runtime was needed.

## Download and verify the official Lean toolchain

The test obtained release metadata from the official [Lean v4.34.0 release](https://github.com/leanprover/lean4/releases/tag/v4.34.0) and verified the selected asset before extraction or execution.

```sh
"$PYTHON" - "$WORK" <<'PY'
from pathlib import Path
import hashlib, json, sys, urllib.request
work = Path(sys.argv[1])
downloads = work / "downloads"
downloads.mkdir()
url = "https://api.github.com/repos/leanprover/lean4/releases/tags/v4.34.0"
with urllib.request.urlopen(url) as response:
    release = json.load(response)
asset = next(a for a in release["assets"]
             if a["name"] == "lean-4.34.0-darwin_aarch64.tar.zst")
archive = downloads / asset["name"]
with urllib.request.urlopen(asset["browser_download_url"], timeout=300) as src:
    with archive.open("wb") as dst:
        while block := src.read(1024 * 1024):
            dst.write(block)
digest = hashlib.sha256(archive.read_bytes()).hexdigest()
assert archive.stat().st_size == asset["size"] == 561666156
assert digest == "69f263fa6e21bbc2466bbfb1affcd92479ee2714c883a07de548e099a5922932"
assert asset["digest"] == "sha256:" + digest
print("verified", archive.name, archive.stat().st_size, digest)
PY

mkdir "$WORK/lean-toolchain"
zstd -dc "$WORK/downloads/lean-4.34.0-darwin_aarch64.tar.zst" | \
  tar -xf - -C "$WORK/lean-toolchain"
LEAN_ROOT="$WORK/lean-toolchain/lean-4.34.0-darwin_aarch64"
LEAN="$LEAN_ROOT/bin/lean"
LAKE="$LEAN_ROOT/bin/lake"
```

On the Air, `tar --use-compress-program=zstd` failed with a broken pipe. Explicit `zstd -dc ... | tar -xf - ...` above recovered successfully. The existing zstd executable was used; no replacement was installed. Lean's distribution reports Apache-2.0. The new toolchain reported Lean 4.34.0 and Lake 5.0.0-src+293d5d0. The pre-existing Lean toolchain was unchanged.

## Link the pinned closure and retrieve official cached objects

Create links only inside the new public Mathlib checkout. Run the inspected cache command with a new external cache directory and the downloaded Lean toolchain first on the child process PATH. This does not change shell profiles, system settings, or the existing toolchain.

```sh
"$PYTHON" - "$WORK" <<'PY'
from pathlib import Path
import os, subprocess, sys
work = Path(sys.argv[1]).resolve()
deps = work / "public-dependencies"
lean = work / "lean-toolchain/lean-4.34.0-darwin_aarch64"
links = deps / "mathlib/.lake/packages"
links.mkdir(parents=True)
for root in deps.iterdir():
    if root.is_dir() and root.name != "mathlib":
        (links / root.name).symlink_to(root, target_is_directory=True)
env = {k: os.environ[k] for k in ("HOME", "TMPDIR", "LANG", "LC_ALL")
       if k in os.environ}
env["PATH"] = str(lean / "bin") + ":/opt/homebrew/bin:/usr/bin:/bin"
env["MATHLIB_CACHE_DIR"] = str(work / "mathlib-cache")
env["MATHLIB_NO_CACHE_ON_UPDATE"] = "1"
for command in ([str(lean / "bin/lean"), "--version"],
                [str(lean / "bin/lake"), "--version"],
                [str(lean / "bin/lake"), "exe", "cache", "get"]):
    subprocess.run(command, cwd=deps / "mathlib", env=env, check=True)
PY
```

The observed cache run compiled the public cache utility and downloaded and decompressed 8,908 official cache files. It used no upload command, account, credential entry, background service, or security-setting change.

## Run the shipped source-first pipeline with explicit paths

This is the explicit public mode tested on Air. The output directory must be new and outside the release. Supply source roots for every pinned repository and object roots only where the cache created them. `Cli` did not require a compiled object root in this closure. Include Lean's own source/object roots.

```sh
"$PYTHON" - "$PACKAGE" "$WORK" <<'PY'
from pathlib import Path
import os, subprocess, sys
package, work = (Path(p).resolve() for p in sys.argv[1:])
deps = work / "public-dependencies"
lean = work / "lean-toolchain/lean-4.34.0-darwin_aarch64"
env = {k: os.environ[k] for k in ("HOME", "TMPDIR", "LANG", "LC_ALL")
       if k in os.environ}
env["PATH"] = str(lean / "bin") + ":/opt/homebrew/bin:/usr/bin:/bin"
command = [
    sys.executable, str(package / "ctrllib/tools/source_first_e2e.py"),
    "all", "--lean", str(lean / "bin/lean"),
    "--output-root", str(work / "full-source-e2e"),
]
for root in sorted(deps.iterdir()):
    if root.is_dir():
        objects = root / ".lake/build/lib/lean"
        if objects.is_dir():
            command += ["--lean-path", str(objects)]
        command += ["--lean-src-path", str(root)]
command += ["--lean-path", str(lean / "lib/lean"),
            "--lean-src-path", str(lean / "src/lean")]
subprocess.run(command, cwd=work, env=env, check=True)
PY
```

No ambient `LEAN_PATH` or `LEAN_SRC_PATH`, existing Ctrllib checkout, or previous Ctrllib objects are supplied. The runner compiles the release source first and writes all objects, extraction, and graph outputs externally.

Set `OUT="$WORK/full-source-e2e"` and use steps 2–3 in [REGENERATE-FULL.md](REGENERATE-FULL.md) for the external Xylem config/database, CLI queries, converter, and foreground MCP server. The [Air evidence and limits](../../../provenance/AIR-CONSUMER-CHECK.md) record the successful results; a navigation response is not a proof-acceptance claim.

