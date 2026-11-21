# Building the preprints locally

The English and Russian PDFs are built from their matching Markdown files:

```bash
python3 build_preprints.py
```

The documentation build requires **Pandoc** and the Python packages
**reportlab**, **matplotlib**, and **Pillow**. These are optional documentation
dependencies; the research experiments and their audit use the Python standard
library. Pandoc must already be installed and available on `PATH`.

```bash
python3 -m pip install reportlab matplotlib Pillow
```

Dependency installation may require network access. The build itself performs
no network requests and invokes no TeX compiler or browser. It uses Pandoc only
to parse Markdown into a local JSON syntax tree, ReportLab to lay out the pages,
and Matplotlib's built-in MathText renderer for equations. DejaVu fonts are
resolved from Matplotlib's local font installation and embedded in the PDFs.

Use `--language en`, `--language ru`, or `--output-dir PATH` to limit the build or
write its output elsewhere. Unsupported Markdown constructs or equations stop
the build with an error rather than being silently dropped.

## Formula representation

The Markdown files retain the authoritative TeX formula source. The PDFs contain
selectable text and high-resolution embedded formula images. Local rendering
normalizes equivalent TeX spellings (`\le` to `\leq`, for example), supplies braces
around single-character font commands, and uses an outlined square for the end
of a proof. Formula images are not separately selectable as equation text; use
the Markdown sources for copying or editing mathematical notation.

After changes, render both final PDFs and inspect every page for clipped text,
formula legibility, table layout, and complete references before publication.
