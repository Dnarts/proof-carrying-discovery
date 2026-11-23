#!/usr/bin/env python3
"""Check the multilingual sources and PDF outputs; package only translated artifacts.

Mathematical identifiers/structure and PDF text are checked. Natural-language
translation equivalence is NOT certified by this script.
"""
from __future__ import annotations
from pathlib import Path
from hashlib import sha256
import json, os, re, subprocess, zipfile
ROOT = Path(__file__).resolve().parent.parent
LANG = ROOT / 'papers/hypothesis-language/translations/gate11-gate12-v12.3'
BASE = ROOT / 'papers/hypothesis-language'
CUM = ROOT / 'papers/cumulative-search'
REF = Path(os.environ.get('PCD_RU_TEX', str(ROOT/'papers/hypothesis-language/gate11-gate12-v12.3/src/hypothesis_language_gate12_ru.tex')))
DEST = ROOT/'docs/PREPRINT_TRANSLATIONS_SHA256.json'
ARCH = ROOT/'docs/preprint_translations_bundle.zip'
SOURCE = [
 LANG/'hypothesis_language_gate12_en.tex',
 LANG/'hypothesis_language_gate12_zh.tex',
 BASE/'HYPOTHESIS_LANGUAGE.zh.md',
 CUM/'CUMULATIVE_SEARCH.zh.md',
]
PDFS = [
 LANG/'hypothesis_language_gate12_en.pdf',
 LANG/'hypothesis_language_gate12_zh.pdf',
 BASE/'HYPOTHESIS_LANGUAGE.zh.pdf',
 CUM/'CUMULATIVE_SEARCH.zh.pdf',
]
EXTRAS = [LANG/'README.md',ROOT/'docs/PREPRINT_LANGUAGES.md',ROOT/'docs/zh_pdf_header.tex',ROOT/'docs/translation_release.py']


def digest(path):
    d=path.read_bytes()
    return {'bytes':len(d),'sha256':sha256(d).hexdigest()}

def labels(content):
    return re.findall(r'\\label\{([^}]+)\}', content)

def cites(content):
    return re.findall(r'\\cite\{([^}]+)\}', content)


def validate():
    assert REF.is_file(), f'Missing original Russian TeX: {REF}'
    for path in SOURCE+PDFS+EXTRAS:
        assert path.is_file() and path.stat().st_size > 10, path
    orig = REF.read_text(encoding='utf-8')
    checks = []
    for fn in SOURCE[:2]:
        text=fn.read_text(encoding='utf-8')
        assert labels(text) == labels(orig), f'Changed math labels: {fn}'
        assert cites(text) == cites(orig), f'Changed citations: {fn}'
        assert len(labels(text)) == 27, fn
        checks.append({'file':str(fn.relative_to(ROOT)),'label_count':27,'cite_count':len(cites(text)),'structure':'MATCH'})
    for f in SOURCE[2:]:
        s=f.read_text(encoding='utf-8')
        assert s.count('$$') % 2 == 0, f'Unmatched display math delimiter: {f}'
        assert s.count('```') % 2 == 0, f'Unmatched code fence: {f}'
    for idx,f in enumerate(PDFS):
        info=subprocess.run(['pdfinfo',str(f)],capture_output=True,text=True,check=True)
        assert 'Pages:' in info.stdout, f
        text=subprocess.run(['pdftotext','-layout',str(f),'-'],capture_output=True,text=True,check=True).stdout
        assert '\ufffd' not in text, f'Unicode replacement in {f}'
        assert len(text)>2500, f'Unexpectedly short PDF: {f}'
        if idx in (1,2,3):
            han=sum('\u4e00'<=c<='\u9fff' for c in text)
            assert han>500, f'Chinese text missing from {f}: {han}'
        checks.append({'file':str(f.relative_to(ROOT)),'pdf_text_chars':len(text),'check':'PASS'})
    files=SOURCE+PDFS+EXTRAS
    payload={
        'abi':'proof-carrying-discovery/preprint-translations/1',
        'edition':'2026-11-23',
        'source_russian_gate11_12_sha256':sha256(REF.read_bytes()).hexdigest(),
        'status':'translation-typesetting-checked; natural-language equivalence not formally proved',
        'sources':{str(f.relative_to(ROOT)):digest(f) for f in files},
        'checks':checks,
        'notes':{
            'main':'Gate 11-12 (RU original, EN and ZH translations)',
            'earlier':'Historical EN and RU versions already existed; only missing ZH translations were added',
            'proof':'Formal Lean evidence remains unchanged in its original versioned package',
        },
    }
    DEST.write_text(json.dumps(payload,ensure_ascii=False,indent=2,sort_keys=True)+'\n',encoding='utf-8')
    ordered=sorted(files+[DEST],key=lambda f:f.relative_to(ROOT).as_posix())
    with zipfile.ZipFile(ARCH,'w',zipfile.ZIP_DEFLATED,compresslevel=8) as z:
        for f in ordered:
            entry=zipfile.ZipInfo(str(f.relative_to(ROOT)),(2026,11,23,0,0,0))
            entry.compress_type=zipfile.ZIP_DEFLATED
            entry.external_attr=0o644<<16
            z.writestr(entry,f.read_bytes(),compress_type=zipfile.ZIP_DEFLATED,compresslevel=8)
    with zipfile.ZipFile(ARCH) as z:
        assert z.testzip() is None
        for f in ordered:
            assert z.read(str(f.relative_to(ROOT)))==f.read_bytes(),f
    return {'status':'PASS','num_translation_artifacts':len(files),'archive_bytes':ARCH.stat().st_size,
            'archive_sha256':digest(ARCH)['sha256'],'files':len(ordered),'source_labels_matched':27,'proof_updated':False}

if __name__=='__main__':
    print(json.dumps(validate(),ensure_ascii=False,indent=2))
