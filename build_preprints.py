#!/usr/bin/env python3
"""Build both preprint PDFs locally, without TeX, a browser, or network access.

Optional documentation dependencies: Pandoc, reportlab, matplotlib, Pillow.
The research experiments and their tests do not depend on these packages.
Markdown is parsed through Pandoc's JSON AST. Matplotlib's local MathText
renderer typesets formulas; their authoritative TeX remains in the Markdown.
"""

from __future__ import annotations

import argparse
import hashlib
import html
import json
from pathlib import Path
import re
import subprocess
import tempfile

import matplotlib

matplotlib.use("Agg")
from matplotlib.font_manager import FontProperties, findfont
from matplotlib.mathtext import MathTextParser
import numpy as np
from PIL import Image as PILImage
from reportlab.lib import colors
from reportlab.lib.pagesizes import A4
from reportlab.lib.styles import ParagraphStyle
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.pdfgen.canvas import Canvas
from reportlab.platypus import (
    HRFlowable,
    Image,
    KeepTogether,
    Paragraph,
    SimpleDocTemplate,
    Spacer,
    Table,
    TableStyle,
)

ROOT = Path(__file__).resolve().parent
PAGE_W, PAGE_H = A4
MARGIN = 51
TEXT_W = PAGE_W - 2 * MARGIN
INK = colors.HexColor("#18222d")
BLUE = colors.HexColor("#244d69")
GRAY = colors.HexColor("#5a6671")


def register_fonts():
    for family, source in (
        ("PaperSerif", "DejaVu Serif"),
        ("PaperSans", "DejaVu Sans"),
        ("PaperMono", "DejaVu Sans Mono"),
    ):
        for suffix, weight, style in (
            ("", "normal", "normal"),
            ("-Bold", "bold", "normal"),
            ("-Italic", "normal", "italic"),
            ("-BoldItalic", "bold", "italic"),
        ):
            path = findfont(FontProperties(family=source, weight=weight, style=style))
            pdfmetrics.registerFont(TTFont(family + suffix, path))
        pdfmetrics.registerFontFamily(
            family,
            normal=family,
            bold=family + "-Bold",
            italic=family + "-Italic",
            boldItalic=family + "-BoldItalic",
        )


def styles():
    result = {}
    result["body"] = ParagraphStyle(
        "PaperBody", fontName="PaperSerif", fontSize=10.1,
        leading=14.8, textColor=INK, spaceAfter=7, splitLongWords=True,
        allowWidows=0, allowOrphans=0, autoLeading="max",
    )
    result["title"] = ParagraphStyle(
        "PaperTitle", parent=result["body"], fontName="PaperSans-Bold",
        fontSize=17, leading=22, textColor=BLUE, spaceAfter=13,
        keepWithNext=True,
    )
    result["h2"] = ParagraphStyle(
        "PaperH2", parent=result["body"], fontName="PaperSans-Bold",
        fontSize=12.1, leading=16.1, textColor=BLUE,
        spaceBefore=12, spaceAfter=7, keepWithNext=True,
    )
    result["h3"] = ParagraphStyle(
        "PaperH3", parent=result["h2"], fontSize=10.5, leading=14,
        spaceBefore=9,
    )
    result["table"] = ParagraphStyle(
        "PaperTable", parent=result["body"], fontName="PaperSans",
        fontSize=8.5, leading=11.5, spaceAfter=0, allowWidows=1,
        allowOrphans=1,
    )
    result["tableheader"] = ParagraphStyle(
        "PaperTableHeader", parent=result["table"], fontName="PaperSans-Bold",
        textColor=colors.white,
    )
    result["reference"] = ParagraphStyle(
        "PaperReference", parent=result["body"], fontSize=8.4,
        leading=12.4, leftIndent=13, firstLineIndent=-13,
        spaceAfter=6,
    )
    result["code"] = ParagraphStyle(
        "PaperCode", parent=result["body"], fontName="PaperMono",
        fontSize=9.2, leading=13.2, backColor=colors.HexColor("#edf2f6"),
        borderPadding=8, spaceBefore=4, spaceAfter=11,
    )
    return result


def mathtext_source(source):
    """Map equivalent TeX spellings to MathText's supported local subset."""
    source = " ".join(source.strip().split())
    source = re.sub(r"\\(mathcal|mathbb|mathbf)\s*([A-Za-z0-9])", r"\\\1{\2}", source)
    source = source.replace(r"\text{", r"\mathrm{")
    for old, new in (("ne", "neq"), ("ge", "geq"), ("le", "leq")):
        source = re.sub(r"\\" + old + r"(?![A-Za-z])", lambda m, n=new: "\\" + n, source)
    source = source.replace(r"\iff", r"\Longleftrightarrow")
    source = source.replace(r"\square", "□")
    return source


class Builder:
    def __init__(self, language, cache_dir):
        self.language = language
        self.cache = Path(cache_dir)
        self.parser = MathTextParser("agg")
        self.styles = styles()
        self.math_files = {}
        self.references = False
        self.stats = {"math_occurrences": 0, "display_equations": 0, "tables": 0}

    def math_image(self, source, fontsize=10.1):
        key = (source, fontsize)
        if key in self.math_files:
            return self.math_files[key]
        normalized = mathtext_source(source)
        dpi = 288
        scale = dpi / 72
        parsed = self.parser.parse(
            "$" + normalized + "$", dpi=dpi,
            prop=FontProperties(size=fontsize, math_fontfamily="dejavuserif"),
        )
        mask = np.asarray(parsed.image)
        rgba = np.empty((*mask.shape, 4), dtype=np.uint8)
        rgba[:, :, :3] = [24, 34, 45]
        rgba[:, :, 3] = mask
        name = hashlib.sha256((str(fontsize) + "\0" + source).encode()).hexdigest() + ".png"
        path = self.cache / name
        PILImage.fromarray(rgba).save(path)
        values = (path, mask.shape[1] / scale, mask.shape[0] / scale, parsed.depth / scale)
        self.math_files[key] = values
        return values

    def inlines(self, nodes, fontsize=10.1):
        output = []
        consumed = {}
        for index, node in enumerate(nodes):
            kind, content = node["t"], node.get("c")
            if kind == "Str":
                text = content[consumed.get(index, 0):]
                escaped = html.escape(text)
                if text.startswith(("https://", "http://")):
                    output.append(f'<link href="{html.escape(text, quote=True)}" color="#244d69">{escaped}</link>')
                else:
                    output.append(escaped)
            elif kind in ("Space", "SoftBreak"):
                output.append(" ")
            elif kind == "LineBreak":
                output.append("<br/>")
            elif kind in ("Strong", "Emph", "Underline", "Strikeout"):
                tag = {"Strong": "b", "Emph": "i", "Underline": "u", "Strikeout": "strike"}[kind]
                output.append(f"<{tag}>" + self.inlines(content, fontsize) + f"</{tag}>")
            elif kind == "Code":
                output.append('<font name="PaperMono" size="' + str(fontsize * .92) + '">' + html.escape(content[1]) + "</font>")
            elif kind == "Math":
                self.stats["math_occurrences"] += 1
                source = content[1]
                if index + 1 < len(nodes) and nodes[index + 1]["t"] == "Str":
                    punctuation = re.match(r"^[,.;:!?)]*", nodes[index + 1]["c"]).group()
                    if punctuation:
                        consumed[index + 1] = len(punctuation)
                        source += punctuation
                path, width, height, depth = self.math_image(source, fontsize)
                output.append(f'<img src="{path}" width="{width:.3f}" height="{height:.3f}" valign="{-depth:.3f}"/>')
            elif kind == "Link":
                url = html.escape(content[2][0], quote=True)
                output.append(f'<link href="{url}" color="#244d69">' + self.inlines(content[1], fontsize) + "</link>")
            elif kind == "Quoted":
                output.append("“" + self.inlines(content[1], fontsize) + "”")
            elif kind == "Span":
                output.append(self.inlines(content[1], fontsize))
            elif kind == "RawInline" and content[0] == "html":
                if content[1] not in ("<br>", "<br/>", "<br />"):
                    raise ValueError(f"Unsupported raw inline: {content}")
                output.append("<br/>")
            else:
                raise ValueError(f"Unsupported inline: {node}")
        return "".join(output)

    def display(self, source):
        self.stats["math_occurrences"] += 1
        self.stats["display_equations"] += 1
        path, width, height, depth = self.math_image(source, 11.2)
        ratio = min(1, TEXT_W / width)
        if ratio < .78:
            raise ValueError(f"Equation would be too small: {source}")
        image = Image(str(path), width=width * ratio, height=height * ratio)
        image.hAlign = "CENTER"
        return KeepTogether([Spacer(1, 5), image, Spacer(1, 10)])

    def table(self, content):
        self.stats["tables"] += 1
        head_rows = content[3][1]
        body_rows = [row for body in content[4] for row in body[3]]
        foot_rows = content[5][1]
        output = []
        for idx, row in enumerate(head_rows + body_rows + foot_rows):
            cells = []
            for cell in row[1]:
                if cell[2:4] != [1, 1]:
                    raise ValueError("Merged table cells require explicit handling")
                style = self.styles["tableheader" if idx < len(head_rows) else "table"]
                parts = []
                for block in cell[4]:
                    if block["t"] not in ("Plain", "Para"):
                        raise ValueError(f"Unsupported table cell block: {block}")
                    parts.append(self.inlines(block["c"], style.fontSize))
                cells.append(Paragraph("<br/>".join(parts), style))
            output.append(cells)
        table = Table(output, colWidths=[TEXT_W * .34] + [TEXT_W * .165] * 4, repeatRows=len(head_rows), hAlign="LEFT")
        table.setStyle(TableStyle([
            ("BACKGROUND", (0, 0), (-1, len(head_rows) - 1), BLUE),
            ("ROWBACKGROUNDS", (0, len(head_rows)), (-1, -1), [colors.white, colors.HexColor("#f0f4f7")]),
            ("VALIGN", (0, 0), (-1, -1), "TOP"),
            ("LEFTPADDING", (0, 0), (-1, -1), 6),
            ("RIGHTPADDING", (0, 0), (-1, -1), 6),
            ("TOPPADDING", (0, 0), (-1, -1), 7),
            ("BOTTOMPADDING", (0, 0), (-1, -1), 7),
            ("LINEBELOW", (0, -1), (-1, -1), .6, BLUE),
        ]))
        return table

    def blocks(self, blocks):
        result = []
        for block in blocks:
            kind, content = block["t"], block.get("c")
            if kind == "Header":
                level, _, inlines = content
                plain = " ".join(x.get("c", "") for x in inlines if x["t"] == "Str")
                if plain in ("References", "Ссылки"):
                    self.references = True
                style = self.styles["title" if level == 1 else "h2" if level == 2 else "h3"]
                result.append(Paragraph(self.inlines(inlines, style.fontSize), style))
                if level == 1:
                    result.extend([HRFlowable(width="100%", thickness=1.1, color=BLUE), Spacer(1, 12)])
            elif kind in ("Para", "Plain"):
                if len(content) == 1 and content[0]["t"] == "Math" and content[0]["c"][0]["t"] == "DisplayMath":
                    result.append(self.display(content[0]["c"][1]))
                else:
                    result.append(Paragraph(self.inlines(content), self.styles["body"]))
            elif kind == "Table":
                result.extend([Spacer(1, 5), self.table(content), Spacer(1, 12)])
            elif kind == "CodeBlock":
                result.append(Paragraph(html.escape(content[1]).replace("\n", "<br/>"), self.styles["code"]))
            elif kind == "OrderedList":
                start = content[0][0]
                entries = []
                for number, items in enumerate(content[1], start):
                    for index, item in enumerate(items):
                        if item["t"] not in ("Para", "Plain"):
                            raise ValueError("Unexpected nested reference/list block")
                        style = self.styles["reference" if self.references else "body"]
                        prefix = f"{number}. " if index == 0 else ""
                        entries.append(Paragraph(prefix + self.inlines(item["c"], style.fontSize), style))
                if self.references:
                    heading = result.pop()
                    result.append(KeepTogether([heading, *entries]))
                else:
                    result.extend(entries)
            elif kind == "BulletList":
                for items in content:
                    for item in items:
                        if item["t"] not in ("Para", "Plain"):
                            raise ValueError("Unexpected nested bullet block")
                        result.append(Paragraph("• " + self.inlines(item["c"]), self.styles["body"]))
            elif kind == "HorizontalRule":
                result.append(HRFlowable(width="100%", thickness=.6, color=GRAY))
            else:
                raise ValueError(f"Unsupported block: {block}")
        return result

    def footer(self, canvas, doc):
        canvas.saveState()
        canvas.setStrokeColor(colors.HexColor("#c9d3dc"))
        canvas.setLineWidth(.5)
        canvas.line(MARGIN, 39, PAGE_W - MARGIN, 39)
        canvas.setFillColor(GRAY)
        canvas.setFont("PaperSans", 7.6)
        label = "Proof-Carrying Discovery · Preprint v1.1 · " + self.language.upper()
        canvas.drawString(MARGIN, 27, label)
        canvas.drawRightString(PAGE_W - MARGIN, 27, str(doc.page))
        canvas.restoreState()

    def build(self, source, output):
        parsed = json.loads(subprocess.check_output([
            "pandoc", str(source), "--from", "markdown+tex_math_dollars", "--to", "json",
        ], text=True))
        story = self.blocks(parsed["blocks"])
        title = source.read_text(encoding="utf-8").splitlines()[0].removeprefix("# ")
        doc = SimpleDocTemplate(
            str(output), pagesize=A4, leftMargin=MARGIN, rightMargin=MARGIN,
            topMargin=44, bottomMargin=53, title=title,
            author="Aleksandr Strand", subject="Cumulative search, explicit invariants, and historical event replay",
        )
        def invariant_canvas(*args, **kwargs):
            kwargs["invariant"] = 1
            canvas = Canvas(*args, **kwargs)
            canvas.setCreator("build_preprints.py: local Pandoc JSON, ReportLab, and MathText")
            return canvas

        doc.build(story, onFirstPage=self.footer, onLaterPages=self.footer, canvasmaker=invariant_canvas)
        return {"file": output.name, "bytes": output.stat().st_size, **self.stats}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--language", choices=("en", "ru", "both"), default="both")
    parser.add_argument("--output-dir", type=Path, default=ROOT)
    args = parser.parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    register_fonts()
    reports = []
    with tempfile.TemporaryDirectory(prefix="preprint-local-math-") as cache:
        for language in (("en", "ru") if args.language == "both" else (args.language,)):
            source = ROOT / f"PREPRINT_v1.1.{language}.md"
            output = args.output_dir / f"PREPRINT_v1.1.{language}.pdf"
            reports.append(Builder(language, cache).build(source, output))
    print(json.dumps(reports, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
