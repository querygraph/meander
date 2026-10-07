#!/usr/bin/env bash
# FirstPair `prepare` hook: build the LaTeX PDF and the Markdown manuscript from paper/meanders.tex.
#   paper/firstpair/prepare.sh <buildDir>
# Writes <buildDir>/latex/meanders.pdf (copied to the dist by the PDF hook) and
# <buildDir>/manuscript.md (rendered to EPUB and HTML by the shared builder).
set -euo pipefail

repo="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
build="$1"
export PATH="/Library/TeX/texbin:$PATH"

node "$repo/paper/figures.mjs"

latex="$build/latex"
rm -rf "$latex"
mkdir -p "$latex"
cp "$repo/paper/meanders.tex" "$latex/"
cp -R "$repo/paper/figs" "$latex/figs"
(
  cd "$latex"
  for pass in 1 2; do
    pdflatex -interaction=nonstopmode -halt-on-error meanders.tex > "pdflatex-$pass.log"
  done
  if grep -E "^!|LaTeX Warning: (Reference|Citation)" pdflatex-2.log; then
    echo "prepare: LaTeX reported errors or unresolved references" >&2
    exit 1
  fi
)

python3 "$repo/paper/firstpair/tex2md.py" "$latex/meanders.tex" "$latex/meanders.aux" "$latex/paper-pandoc.tex"
(cd "$latex" && pandoc paper-pandoc.tex --from latex --to markdown --wrap=preserve --output "$build/manuscript.md")
echo "prepare: built $latex/meanders.pdf and $build/manuscript.md"
