# FirstPair Library Contract

slug: arnold-meanders
shelf: math
default_edition: full

This file is the library deployment contract read by the centralized FirstPair
publisher (`~/src/firstpair`). Keep the key-value header simple and unbulleted.

## Ownership

This repository owns the paper *Counting Arnold's Meanders with Verified
Algorithms* (`paper/meanders.tex`), its figure generator (`paper/figures.mjs`),
the LaTeX-to-Markdown bridge (`paper/firstpair/`), the visualization
(`viz/index.html` and its self-contained copy `viz/arnold-meanders-visualization.html`), the
cover art (`cover/meanders.png`), `book.build.json`, and the built package under
`paper/dist`. The Lean formalization it describes lives in `Arnold/`. FirstPair
owns the unified builder, catalog, readers, Blob uploads and deployment.

The LaTeX source is the single source of the text. The `prepare` hook builds the
PDF with `pdflatex` and converts the same source to the Markdown manuscript that
the shared builder renders to EPUB and HTML, with section, theorem, figure and
reference numbers taken from the LaTeX build.

## Build

Requires MacTeX (`pdflatex`), pandoc, node and python3.

```sh
python3 viz/inline_fonts.py viz/index.html viz/arnold-meanders-visualization.html   # when viz/index.html changes
"$HOME/src/firstpair/publishing/scripts/build-library-book.sh" --repo-root "$(git rev-parse --show-toplevel)"
```

## Publish

The visualization is published as the title's tutorial at `/learn/arnold-meanders/`.

```sh
cd "$HOME/src/firstpair"
npm run library:publish -- "$HOME/src/arnold" --dry-run --no-build --no-smoke --no-deploy --no-icloud
npm run library:publish -- "$HOME/src/arnold"
```

## Film

The film of the visualization is not part of the library package. It is
published as release assets of `querygraph/meander` (tag `v1.0.0`).
