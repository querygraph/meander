"""Build the companion notebooks from their Markdown sources.

    notebook/.venv/bin/python notebook/build.py [lean|python|ocaml ...] [--no-execute]

Each notebook is written as Markdown chapters in `notebook/<lang>/NN-*.md`. A fenced block in
the notebook's language becomes a code cell; everything else becomes text cells (one per
chapter section). In Lean cells, a line `@include <file> <head>` is replaced by the declaration
of `<file>` whose first line starts with `<head>`, together with its docstring and attributes,
so the notebook shows the library's code exactly. A declaration may be included only once.

The notebook is then executed in a fresh kernel in an empty working directory, and the build
fails if any cell reports an error. The executed notebook, with its outputs, is written to
`notebook/arnold-meanders-<lang>.ipynb`.
"""

import argparse
import glob
import os
import re
import sys
import tempfile
import time

import nbformat
from nbclient import NotebookClient

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)

LANGS = {
    "lean": {
        "fence": "lean",
        "kernel": {"name": "lean4-arnold", "display_name": "Lean 4 (Arnold)", "language": "lean4"},
        "language_info": {"name": "lean4", "file_extension": ".lean",
                          "mimetype": "text/x-lean4", "pygments_lexer": "lean4"},
    },
    "python": {
        "fence": "python",
        "kernel": {"name": "python3", "display_name": "Python 3", "language": "python"},
        # Executed with the math-companion environment (Python 3.12, NumPy, Matplotlib).
        "exec_kernel": os.environ.get("PYTHON_KERNEL", "math-companion-python"),
        "language_info": {"name": "python", "file_extension": ".py"},
    },
    "ocaml": {
        "fence": "ocaml",
        "kernel": {"name": "ocaml-jupyter-5.5.1", "display_name": "OCaml 5.5.1",
                   "language": "OCaml"},
        "language_info": {"name": "OCaml", "file_extension": ".ml"},
    },
}

DECL_START = re.compile(
    r"^(/--|/-!|@\[|theorem |lemma |def |abbrev |instance|inductive |structure |class |"
    r"namespace |end\b|section\b|open |variable |set_option |omit |include |noncomputable |"
    r"private |protected |-- )"
)


class Includer:
    """Cuts declarations out of Lean source files, each at most once."""

    def __init__(self):
        self.files = {}
        self.used = set()

    def lines(self, path):
        if path not in self.files:
            with open(os.path.join(ROOT, path), encoding="utf-8") as f:
                self.files[path] = f.read().split("\n")
        return self.files[path]

    def decl(self, path, head):
        lines = self.lines(path)
        def heads(l):
            rest = l[len(head):]
            return l.startswith(head) and not (rest[:1].isalnum() or rest[:1] in ("_", "'", "."))
        starts = [i for i, l in enumerate(lines) if heads(l)]
        if len(starts) != 1:
            raise SystemExit(f"@include {path} {head!r}: {len(starts)} matches")
        i = starts[0]
        key = (path, i)
        if key in self.used:
            raise SystemExit(f"@include {path} {head!r}: included twice")
        self.used.add(key)
        # Back up over the docstring and attribute or `set_option ... in` lines.
        j = i
        while j > 0 and (lines[j - 1].startswith("@[") or lines[j - 1].startswith("set_option")):
            j -= 1
        if j > 0 and lines[j - 1].rstrip().endswith("-/"):
            k = j - 1
            while not lines[k].startswith("/--"):
                k -= 1
            j = k
        while j > 0 and lines[j - 1].startswith("set_option") and lines[j - 1].endswith(" in"):
            j -= 1
        # Run forward to the next top-level item after a blank line, or to the end.
        e = i + 1
        while e < len(lines):
            if DECL_START.match(lines[e]):
                break
            if lines[e].strip() == "" and (e + 1 >= len(lines) or DECL_START.match(lines[e + 1])
                                           or lines[e + 1].strip() == ""):
                break
            e += 1
        return "\n".join(lines[j:e]).rstrip()


def expand_lean(src, inc):
    out = []
    for line in src.split("\n"):
        m = re.match(r"^@include\s+(\S+)\s+(.+)$", line)
        out.append(inc.decl(m.group(1), m.group(2)) if m else line)
    return "\n".join(out)


def cells_of(text, fence, inc):
    cells = []
    md = []
    pat = re.compile(r"^```" + re.escape(fence) + r"\s*$")

    def flush_md():
        body = "\n".join(md).strip()
        if body:
            for part in re.split(r"\n(?=## )", body):
                if part.strip():
                    cells.append(nbformat.v4.new_markdown_cell(part.strip()))
        md.clear()

    lines = text.split("\n")
    i = 0
    while i < len(lines):
        if pat.match(lines[i]):
            j = i + 1
            while not lines[j].startswith("```"):
                j += 1
            code = "\n".join(lines[i + 1:j]).strip("\n")
            if fence == "lean":
                code = expand_lean(code, inc)
            flush_md()
            cells.append(nbformat.v4.new_code_cell(code))
            i = j + 1
        else:
            md.append(lines[i])
            i += 1
    flush_md()
    return cells


def build(lang, execute):
    cfg = LANGS[lang]
    parts = sorted(glob.glob(os.path.join(HERE, lang, "*.md")))
    if not parts:
        raise SystemExit(f"no sources in notebook/{lang}/")
    text = "\n\n".join(open(p, encoding="utf-8").read() for p in parts)
    inc = Includer()
    nb = nbformat.v4.new_notebook()
    nb.cells = cells_of(text, cfg["fence"], inc)
    nb.metadata["kernelspec"] = cfg["kernel"]
    nb.metadata["language_info"] = cfg["language_info"]
    code = sum(c.cell_type == "code" for c in nb.cells)
    print(f"{lang}: {len(nb.cells)} cells ({code} code, {len(inc.used)} included declarations)")
    out = os.path.join(HERE, f"arnold-meanders-{lang}.ipynb")
    if execute:
        t = time.time()
        with tempfile.TemporaryDirectory() as wd:
            client = NotebookClient(nb, timeout=3600, kernel_name=cfg.get("exec_kernel", cfg["kernel"]["name"]),
                                    allow_errors=True, resources={"metadata": {"path": wd}})
            client.execute()
        bad = []
        for n, c in enumerate(nb.cells):
            if c.cell_type != "code":
                continue
            for o in c.outputs:
                if o.output_type == "error":
                    bad.append((n, c.source.split("\n")[0], o.get("evalue", "")))
        print(f"{lang}: executed in {time.time() - t:.0f}s")
        if bad:
            for n, head, ev in bad:
                print(f"--- cell {n}: {head}\n{ev}\n", file=sys.stderr)
            nbformat.write(nb, out + ".failed")
            raise SystemExit(f"{lang}: {len(bad)} cell(s) failed; see {out}.failed")
    nbformat.write(nb, out)
    print(f"wrote {os.path.relpath(out, ROOT)}")
    return inc


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("langs", nargs="*", default=list(LANGS))
    ap.add_argument("--no-execute", action="store_true")
    args = ap.parse_args()
    for lang in args.langs:
        build(lang, not args.no_execute)


if __name__ == "__main__":
    main()
