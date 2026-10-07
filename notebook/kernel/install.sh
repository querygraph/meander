#!/bin/sh
# Install the Lean notebook kernel: build the Lean REPL for this project's toolchain, create a
# Python environment with ipykernel, and register the kernel `lean4-arnold` with Jupyter.
# Run from anywhere; Lean (elan) and the project's build (`lake build`) must already exist.
set -eu
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
NB="$ROOT/notebook"
PATH="$HOME/.elan/bin:$PATH"
TOOLCHAIN=$(cat "$ROOT/lean-toolchain")
# The REPL tag for this Lean minor version (4.34.x -> v4.34.0).
REPL_TAG=${REPL_TAG:-$(echo "$TOOLCHAIN" | sed -E 's/.*:v([0-9]+\.[0-9]+)\..*/v\1.0/')}

if [ ! -x "$NB/.repl/.lake/build/bin/repl" ]; then
  rm -rf "$NB/.repl"
  git clone -q --depth 1 --branch "$REPL_TAG" https://github.com/leanprover-community/repl "$NB/.repl"
  cp "$ROOT/lean-toolchain" "$NB/.repl/lean-toolchain"
  (cd "$NB/.repl" && lake build)
fi

if [ ! -x "$NB/.venv/bin/python" ]; then
  if command -v uv >/dev/null 2>&1; then
    uv venv -q "$NB/.venv"
    uv pip install -q --python "$NB/.venv/bin/python" ipykernel
  else
    python3 -m venv "$NB/.venv"
    "$NB/.venv/bin/pip" install -q ipykernel
  fi
fi

SPEC=$(mktemp -d)
cat > "$SPEC/kernel.json" <<JSON
{
  "argv": ["$NB/.venv/bin/python", "$NB/kernel/lean_kernel.py", "-f", "{connection_file}"],
  "display_name": "Lean 4 (Arnold)",
  "language": "lean4",
  "env": {"ARNOLD_ROOT": "$ROOT"}
}
JSON
jupyter kernelspec install --user --name lean4-arnold "$SPEC"
rm -rf "$SPEC"
echo "Installed kernel lean4-arnold (REPL $REPL_TAG, $TOOLCHAIN)"
