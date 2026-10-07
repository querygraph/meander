#!/usr/bin/env python3
"""Prepare paper/meanders.tex for pandoc, which writes the Markdown manuscript that the
FirstPair builder turns into EPUB and HTML. The LaTeX file stays the single source.

  tex2md.py <meanders.tex> <meanders.aux> <out.tex>

- TikZ figures (\\input{figs/NAME}) become \\includegraphics{figs/NAME.svg}.
- The Lean listings (alltt with math-mode symbols) become verbatim Unicode code.
- Sections, theorems, figures, tables, \\ref and \\cite carry the numbers LaTeX printed,
  read from the .aux file, so the EPUB and HTML match the PDF.
"""
import re
import sys

tex_path, aux_path, out_path = sys.argv[1:4]
s = open(tex_path, encoding="utf-8").read()
aux = open(aux_path, encoding="utf-8").read()

# label -> number, from \newlabel{name}{{number}{page}...}
labels = {m.group(1): m.group(2) for m in re.finditer(r"\\newlabel\{([^}]*)\}\{\{([^}]*)\}", aux)}

# Lean listings: undo the alltt encoding back to plain Unicode source.
SYMBOLS = {
    r"\(\forall\)": "∀", r"\(\to\)": "→", r"\(\neg\)": "¬", r"\(\wedge\)": "∧",
    r"\(\leftrightarrow\)": "↔", r"\(\mathbb{N}\)": "ℕ", r"\(\sigma\)": "σ", r"\(\times\)": "×",
}


def lean_block(m):
    body = m.group(1)
    for k, v in SYMBOLS.items():
        body = body.replace(k, v)
    body = re.sub(r"\\kw\{([^}]*)\}", r"\1", body)
    body = re.sub(r"\\textit\{([^}]*)\}", r"\1", body)
    body = body.replace("\\{", "{").replace("\\}", "}").replace("\\_", "_")
    return "\\begin{verbatim}\n" + body.strip("\n") + "\n\\end{verbatim}"


s = re.sub(r"\\begin\{leancode\}\n(.*?)\\end\{leancode\}", lean_block, s, flags=re.S)

# Figures: SVG images instead of TikZ; drop layout-only wrappers.
s = re.sub(r"\\scalebox\{[^}]*\}\{\\input\{figs/([^}]*)\}\}", r"\\includegraphics{figs/\1.svg}", s)
s = re.sub(r"\\input\{figs/([^}]*)\}", r"\\includegraphics{figs/\1.svg}", s)
s = re.sub(r"\\hspace\{[^}]*\}", " ", s)
s = s.replace("\\clearpage\n", "")

# The n = 5 gallery: a plain two-column table of images over their crossing orders.
def gallery(m):
    cells = re.findall(r"\\includegraphics\{(figs/[^}]*)\}\\\\\[4pt\] \\small \$(\d+)\$", m.group(0))
    rows = []
    for i in range(0, len(cells), 2):
        pair = cells[i:i + 2]
        rows.append(" & ".join(f"\\includegraphics{{{c[0]}}}" for c in pair) + " \\\\")
        rows.append(" & ".join(f"${c[1]}$" for c in pair) + " \\\\")
    return "\\begin{tabular}{cc}\n" + "\n".join(rows) + "\n\\end{tabular}"


s = re.sub(r"\\begin\{tabular\}\{cc\}.*?\\end\{tabular\}(?=\n\\caption\{All eight)", gallery, s, flags=re.S)

# Numbered sections, theorems, captions and citations, as in the PDF.
section = 0
subsection = 0
counter = 0
out = []
ENVS = {"theorem": "Theorem", "proposition": "Proposition", "lemma": "Lemma",
        "definition": "Definition", "remark": "Remark"}
for line in s.split("\n"):
    m = re.match(r"\\section\{(.*)\}(.*)$", line)
    if m:
        section += 1; subsection = 0; counter = 0
        line = f"\\section*{{{section}. {m.group(1)}}}{m.group(2)}"
    m = re.match(r"\\subsection\{(.*)\}(.*)$", line)
    if m:
        subsection += 1
        line = f"\\subsection*{{{section}.{subsection}. {m.group(1)}}}{m.group(2)}"
    m = re.match(r"\\begin\{(theorem|proposition|lemma|definition|remark)\}(\[[^\]]*\])?(.*)$", line)
    if m:
        counter += 1
        name = ENVS[m.group(1)]
        note = f" ({m.group(2)[1:-1]})" if m.group(2) else ""
        line = f"\\par\\noindent\\textbf{{{name} {section}.{counter}{note}.}} {m.group(3)}"
        out.append(line)
        continue
    if re.match(r"\\end\{(theorem|proposition|lemma|definition|remark)\}", line):
        out.append("")
        continue
    out.append(line)
s = "\n".join(out)

def number_captions(s, env):
    def repl(m):
        body = m.group(0)
        lab = re.search(r"\\label\{([^}]*)\}", body)
        if not lab: return body
        n = labels[lab.group(1)]
        word = "Figure" if env == "figure" else "Table"
        return body.replace("\\caption{", f"\\caption{{{word} {n}. ", 1)
    return re.sub(r"\\begin\{" + env + r"\}.*?\\end\{" + env + r"\}", repl, s, flags=re.S)

s = number_captions(s, "figure")
s = number_captions(s, "table")

bib = {m.group(1): m.group(2) for m in re.finditer(r"\\bibcite\{([^}]*)\}\{([^}]*)\}", aux)}
s = re.sub(r"\\cite\{([^}]*)\}", lambda m: "[" + ", ".join(bib[k.strip()] for k in m.group(1).split(",")) + "]", s)
s = re.sub(r"\\bibitem\{([^}]*)\}", lambda m: f"\\par [{bib[m.group(1)]}] ", s)
s = s.replace("\\begin{thebibliography}{99}", "\\section*{References}").replace("\\end{thebibliography}", "")

# The abstract becomes the opening section.
s = s.replace("\\begin{abstract}", "\\section*{Abstract}").replace("\\end{abstract}", "")

# References: the numbers LaTeX printed.
def ref(m):
    key = m.group(1)
    if key not in labels:
        raise SystemExit(f"tex2md: unresolved reference {key}")
    return labels[key]


s = re.sub(r"\\ref\{([^}]*)\}", ref, s)

open(out_path, "w", encoding="utf-8").write(s)
