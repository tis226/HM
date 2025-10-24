# ================================================================
# COMMENT
# 파싱까지는 잘되지만 4지선 다형에서 만약에 심볼로 되어있는 선택지가 나왔을 시에는 처리 오류 존재_해결 완
# 뛰어쓰기 안되는 문항 존재_해결 완
# 빈칸 채우기 부분에서 순서 부분 파싱 문항으로 됨(빈칸 가,나,다,라 있으면 해당 부분을 문제로 판단)
# 다툼이 있는 경우 판례에 의함 부분 아직 처리 안됨.
# 헤더가 오른쪽에 있어서 헤더가 있는 페이지의 경우 option에 헤더 들어가는것 확인
#pg number omit needed_해결 완
# ================================================================


from __future__ import annotations
from dataclasses import dataclass
from typing import List, Tuple, Optional, Iterable, Union, Dict, Any
from statistics import mean
import json, re, unicodedata, os, csv
from pdfminer.high_level import extract_pages
from pdfminer.layout import LAParams, LTTextContainer, LTTextLine, LTChar, LTLine

# ================================================================
# CONFIG RESTRAINTS
# ================================================================
TARGET_SUBJECTS = ["경찰학개론"]#"헌법", "형사법", "경찰학", "형법", "형사소송법", "경찰학개론"]
CIRCLED_CHOICE_CHARS = "①②③④⑤⑥⑦⑧⑨⑩⑪⑫⑬⑭⑮⑯⑰⑱⑲⑳"
CIRCLED_CHOICE_RE = re.compile(rf'^[{CIRCLED_CHOICE_CHARS}]')
PLAIN_CHOICE_RE = re.compile(r'^\s*(\(?[1-9]\d?\)|[1-9]\d?\.)\s*')
QNUM_RE = re.compile(r'^\s*(\d{1,3})\.\s*(.*)')
HANGUL_RUN_RE = re.compile(r"[가-힣]{2,}(?:\s*[가-힣]{2,})*")
PAGE_NO_RE = re.compile(r"^\s*-\s*\d+\s*-\s*$")
DISPUTE_RE = re.compile(
    r"다툼이\s*있는\s*경우\s*(?P<site>.*?)\s*판례에\s*의함",
    re.IGNORECASE,
)

MATRIX_LABEL_RE = re.compile(r'^[㉠-㉷]$')
PAREN_MATRIX_LABEL_RE = re.compile(r'^\(?[가-힣]\)?$')

# Exact boilerplate line (no middle text)
DISPUTE_LINE_RE = re.compile(
    r"^\s*다툼이\s*있는\s*경우\s*판례에\s*의함\s*$",
    re.IGNORECASE,
)
ORDER_MODE = "smart"

# ================================================================
# DATA STRUCTURES
# ================================================================
@dataclass
class Line:
    text: str
    x0: float
    y0: float
    x1: float
    y1: float
    size: float
    font: str
    column: str  # "left" or "right"

# ================================================================
# UTILITIES
# ================================================================
def _normalize_header_text(s: str) -> str:
    s = unicodedata.normalize("NFC", s)
    s = re.sub(r"[\u00A0\u2000-\u200B]", " ", s)
    s = re.sub(r"[【】()\[\]{}·･•※〈〉《》『』—–\-:·•\s]+", "", s)
    return s.strip()

def _extract_subject_and_target(raw: str) -> Tuple[Optional[str], Optional[str]]:
    """
    Extracts both subject and target from headers like:
    【헌 법】(일 반 공 채･101경 비 단)
    """
    if not raw:
        return None, None
    subj, target = None, None
    m1 = re.search(r"[【\[]\s*([^】\]]+?)\s*[】\]]", raw)
    if m1:
        subj = _normalize_header_text(m1.group(1))
    m2 = re.search(r"\(([^)]+)\)", raw)
    if m2:
        target = _normalize_header_text(m2.group(1))
    return subj, target

def _line_font_stats(ln: LTTextLine) -> Tuple[float, str]:
    sizes, fonts = [], []
    for obj in ln:
        if isinstance(obj, LTChar):
            sizes.append(obj.size)
            fonts.append(obj.fontname)
    if not sizes:
        return (10.0, "UNKNOWN")
    return (mean(sizes), max(set(fonts), key=fonts.count))

def _is_choice_anchor(text: str, allow_plain: bool = True) -> bool:
    t = text.strip()
    if CIRCLED_CHOICE_RE.match(t): return True
    if allow_plain and PLAIN_CHOICE_RE.match(t): return True
    return False

def _auto_x_threshold(x_centers: List[float]) -> Optional[float]:
    if not x_centers: return None
    c1, c2 = min(x_centers), max(x_centers)
    for _ in range(15):
        left = [x for x in x_centers if abs(x - c1) <= abs(x - c2)]
        right = [x for x in x_centers if abs(x - c2) < abs(x - c1)]
        if left: c1 = sum(left) / len(left)
        if right: c2 = sum(right) / len(right)
    return (c1 + c2) / 2.0

# ================================================================
# FOOTER REMOVAL
# ================================================================
def _get_bbox_and_text(line):
    # Works with your Line dataclass OR (x0,y0,x1,y1,text) tuples
    if hasattr(line, "x0") and hasattr(line, "text"):
        x0, y0, x1, y1, txt = line.x0, line.y0, line.x1, line.y1, line.text
    else:
        x0, y0, x1, y1, txt = line
    return x0, y0, x1, y1, txt


def filter_page_numbers(lines, page_w: float, page_h: float):
    """
    Drop lines that look like centered page numbers ('- 5 -') that appear near the bottom.
    """
    out = []
    page_center_x = page_w * 0.5
    for line in lines:
        x0, y0, x1, y1, txt = _get_bbox_and_text(line)
        t = (txt or "").replace("\u00A0", " ").strip()

        # only consider lower 25% of the page as "footer zone"
        in_footer_zone = y1 < page_h * 0.04
        looks_like_page_no = bool(PAGE_NO_RE.match(t))
        roughly_centered = abs(((x0 + x1) * 0.5) - page_center_x) < page_w * 0.25

        if in_footer_zone and looks_like_page_no and roughly_centered:
            continue  # drop it

        out.append(line)
    return out

# ================================================================
# DISPUTE TRIGGER
# ================================================================

def _norm_space(s: str) -> str:
    return (s or "").replace("\u00A0", " ").strip()

def _clean_dispute_site(s: str) -> str:
    s = _norm_space(s)
    # strip most common surrounding brackets/punct
    s = s.strip("()[]{}〈〉《》『』“”\"' ")
    return s


# ================================================================
# SUBJECT DETECTION
# ================================================================
def _detect_subject_for_page(all_elements: List[Any], page_width: float, page_height: float):
    """Detect subject & target if wide horizontal line (>=70% width) exists near top."""
    candidate_lines = []
    for el in all_elements:
        if isinstance(el, LTLine):
            width, height = abs(el.x1 - el.x0), abs(el.y1 - el.y0)
            if width >= page_width * 0.7 and height < 5:
                candidate_lines.append(el.y1)
    if not candidate_lines:
        return None, None
    top_line_y = max(candidate_lines)
    text_lines = [el for el in all_elements if isinstance(el, Line) and el.y0 > top_line_y]
    if not text_lines:
        return None, None
    merged = " ".join(l.text for l in sorted(text_lines, key=lambda L: (-L.y1, L.x0)))
    subj, target = _extract_subject_and_target(merged)
    return subj, target

# ================================================================
# PAGE SPLITTING
# ================================================================
def _split_block_on_gaps(block: Dict[str, Any], keep_first_qnum: Optional[str]) -> List[Dict[str, Any]]:
    """Split a block whenever vertical gaps suggest a new section."""
    lines: List[Line] = block["lines"]
    if len(lines) <= 1:
        clone = dict(block)
        clone["qnum"] = keep_first_qnum
        return [clone]

    # Questions with an explicit number can legitimately span columns, so allow
    # tighter splitting to peel off follow-up fragments (e.g., next question's
    # options) while keeping unnumbered continuations intact.
    threshold = 45.0 if keep_first_qnum else 80.0

    chunks: List[List[Line]] = []
    current: List[Line] = [lines[0]]
    for prev, cur in zip(lines, lines[1:]):
        if abs(prev.y1 - cur.y1) > threshold:
            chunks.append(current[:])
            current = [cur]
        else:
            current.append(cur)
    chunks.append(current[:])

    out: List[Dict[str, Any]] = []
    for idx, chunk in enumerate(chunks):
        q = keep_first_qnum if idx == 0 else None
        out.append(
            {
                "lines": chunk,
                "top": max(ln.y1 for ln in chunk),
                "qnum": q,
                "column": block["column"],
            }
        )
    return out


def _group_column_blocks(lines: List[Line], column: str) -> List[Dict[str, Any]]:
    blocks: List[Dict[str, Any]] = []
    current: List[Line] = []
    current_q: Optional[str] = None

    for ln in lines:
        text = ln.text.strip()
        m = QNUM_RE.match(text)
        if m and current:
            blocks.extend(
                _split_block_on_gaps(
                    {"lines": current, "top": max(l.y1 for l in current), "qnum": current_q, "column": column},
                    current_q,
                )
            )
            current = [ln]
            current_q = m.group(1)
        else:
            if not current:
                current = [ln]
                current_q = m.group(1) if m else None
            else:
                current.append(ln)
    if current:
        blocks.extend(
            _split_block_on_gaps(
                {"lines": current, "top": max(l.y1 for l in current), "qnum": current_q, "column": column},
                current_q,
            )
        )
    return blocks


def _first_qnum(blocks: List[Dict[str, Any]]) -> Optional[int]:
    for blk in blocks:
        q = blk.get("qnum")
        if q is None:
            continue
        try:
            return int(q)
        except ValueError:
            continue
    return None


def _merge_column_blocks(left_blocks: List[Dict[str, Any]], right_blocks: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    left_fixed = [b for b in left_blocks if b.get("qnum")]
    left_float = [b for b in left_blocks if not b.get("qnum")]
    right_fixed = [b for b in right_blocks if b.get("qnum")]
    right_float = [b for b in right_blocks if not b.get("qnum")]

    lf_q, rf_q = _first_qnum(left_blocks), _first_qnum(right_blocks)
    if lf_q is None and rf_q is None:
        left_first = True
    elif lf_q is None:
        left_first = False
    elif rf_q is None:
        left_first = True
    else:
        left_first = lf_q <= rf_q

    def _attach(source: List[Dict[str, Any]], anchors: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
        leftovers: List[Dict[str, Any]] = []
        for blk in source:
            if not anchors:
                leftovers.append(blk)
                continue
            anchor = min(anchors, key=lambda b: abs(b["top"] - blk["top"]))
            if abs(anchor["top"] - blk["top"]) > 220.0:
                leftovers.append(blk)
                continue
            merged = anchor["lines"] + blk["lines"]
            anchor["lines"] = sorted(merged, key=lambda ln: (-ln.y1, ln.x0))
            anchor["top"] = max(ln.y1 for ln in anchor["lines"])
        return leftovers

    loose_left = _attach(left_float, right_fixed)
    loose_right = _attach(right_float, left_fixed)

    ordered: List[Dict[str, Any]] = []

    def _append(block: Dict[str, Any]) -> None:
        ordered.append(block)

    if left_first:
        for blk in left_fixed:
            _append(blk)
        for blk in right_fixed:
            _append(blk)
    else:
        for blk in right_fixed:
            _append(blk)
        for blk in left_fixed:
            _append(blk)

    if left_first:
        ordered.extend(loose_left)
        ordered.extend(loose_right)
    else:
        ordered.extend(loose_right)
        ordered.extend(loose_left)

    return ordered


def _stitch_smart(left: List[Line], right: List[Line]) -> List[Line]:
    left_blocks = _group_column_blocks(left, "left")
    right_blocks = _group_column_blocks(right, "right")
    merged_blocks = _merge_column_blocks(left_blocks, right_blocks)
    ordered: List[Line] = []
    for blk in merged_blocks:
        ordered.extend(blk["lines"])
    return ordered


def extract_lines_by_side(pdf_path: str) -> List[Dict[str, Any]]:
    laparams = LAParams(char_margin=3.0, word_margin=0.2, line_margin=0.3)
    out = []
    for idx, layout in enumerate(extract_pages(pdf_path, laparams=laparams)):
        W, H = layout.bbox[2], layout.bbox[3]
        raw_lines, all_elements = [], []
        for el in layout:
            all_elements.append(el)
            if isinstance(el, LTTextContainer):
                for ln in el:
                    if isinstance(ln, LTTextLine):
                        t = ln.get_text().strip()
                        if not t: continue
                        size, font = _line_font_stats(ln)
                        raw_lines.append(Line(t, ln.x0, ln.y0, ln.x1, ln.y1, size, font, "?"))
        raw_lines = filter_page_numbers(raw_lines, W, H)
        subj, target = _detect_subject_for_page(raw_lines + all_elements, W, H)
        centers = [(l.x0 + l.x1) / 2 for l in raw_lines]
        x_thr = _auto_x_threshold(centers) or (W / 2)
        for L in raw_lines:
            L.column = "left" if ((L.x0 + L.x1) / 2) < x_thr else "right"
        left = sorted([l for l in raw_lines if l.column == "left"], key=lambda L: (-L.y1, L.x0))
        right = sorted([l for l in raw_lines if l.column == "right"], key=lambda L: (-L.y1, L.x0))
        if ORDER_MODE == "pdfminer":
            ordered = raw_lines[:]
        elif ORDER_MODE == "natural":
            ordered = sorted(raw_lines, key=lambda L: (-L.y1, L.x0))
        elif ORDER_MODE == "column_first":
            ordered = left + right
        else:  # smart column stitching with floating block support
            ordered = _stitch_smart(left, right)
        out.append(
            {
                "page_index": idx,
                "subject": subj,
                "target": target,
                "left": left,
                "right": right,
                "ordered": ordered,
            }
        )
    return out

# ================================================================
# QA PARSER
# ================================================================
OPT_RE_CIRCLED = re.compile(r'^\s*([①②③④⑤⑥⑦⑧⑨⑩])\s*(.*)')
OPT_RE_PLAIN = re.compile(r'^\s*(\(?[1-5]\)|[1-5]\.)\s*(.*)')

# --- Added: unified anchor regex + inline splitter (supports multiple anchors per line) ---
OPT_SPLIT_RE = re.compile(
    r'''
    (?:
        (?P<circ>[①②③④⑤⑥⑦⑧⑨⑩⑪⑫⑬⑭⑮⑯⑰⑱⑲⑳])
      |
        (?P<plain>
            \(?(?P<num>([1-9]|1[0-9]|20))\) #| (?P<numdot>([1-9]|1[0-9]|20)\.) 날짜가 본문이나 문항에 있을 때 삐꾸됨
        )
    )
    ''',
    re.VERBOSE,
)

def split_inline_options(line_text: str):
    s = (line_text or '').replace('\u00A0', ' ').strip()
    matches = list(OPT_SPLIT_RE.finditer(s))
    if not matches:
        return []
    parts = []
    for i, m in enumerate(matches):
        idx = m.group('circ') if m.group('circ') else m.group(0).strip()
        start = m.end()
        end = matches[i+1].start() if i+1 < len(matches) else len(s)
        body = s[start:end].strip()
        parts.append((idx, body))
    return parts
# --- end added ---


def _reshape_matrix_options(opts: List[Dict[str, str]]) -> List[Dict[str, str]]:
    """Detects simple row/column matrices flattened into a single option and spreads values across options."""
    if not opts:
        return opts
    nonempty = [opt for opt in opts if (opt.get("text") or "").strip()]
    empty = [opt for opt in opts if not (opt.get("text") or "").strip()]
    if len(nonempty) != 1 or not empty:
        return opts
    combined = nonempty[0]["text"].strip()
    tokens = combined.split()
    if not tokens:
        return opts
    rows: List[Tuple[str, List[str]]] = []
    current_label = None
    current_values: List[str] = []
    for token in tokens:
        if token.startswith("(") and token.endswith(")"):
            if current_label is not None:
                rows.append((current_label, current_values))
                current_values = []
            current_label = token
        else:
            current_values.append(token)
    if current_label is not None:
        rows.append((current_label, current_values))
    option_count = len(opts)
    if not rows or any(len(values) != option_count for _, values in rows):
        return opts
    rebuilt: Dict[str, List[str]] = {opt["index"]: [] for opt in opts}
    order = [opt["index"] for opt in opts]
    for label, values in rows:
        for idx, value in enumerate(values):
            rebuilt[order[idx]].append(f"{label} {value}".strip())
    out = []
    for opt in opts:
        pieces = rebuilt.get(opt["index"], [])
        text = " ".join(pieces).strip()
        out.append({"index": opt["index"], "text": text})
    return out


def _collect_matrix_block(lines: List[Line], start: int) -> Tuple[List[Line], int]:
    block: List[Line] = []
    j = start
    while j < len(lines):
        text = (lines[j].text or '').strip()
        if j > start and QNUM_RE.match(text):
            break
        block.append(lines[j])
        j += 1
    return block, j


def _parse_matrix_block(block: List[Line]) -> Optional[List[Dict[str, str]]]:
    if not block:
        return None

    paren_columns: List[Tuple[str, float]] = []
    circ_columns: List[Tuple[str, float]] = []
    for ln in block:
        label = (ln.text or '').strip()
        if PAREN_MATRIX_LABEL_RE.match(label):
            center = (ln.x0 + ln.x1) / 2.0
            paren_columns.append((label, center))
        elif MATRIX_LABEL_RE.match(label):
            center = (ln.x0 + ln.x1) / 2.0
            circ_columns.append((label, center))
    columns = paren_columns if len(paren_columns) >= 2 else circ_columns
    use_paren_labels = len(paren_columns) >= 2
    if len(columns) < 2:
        return None
    columns.sort(key=lambda item: item[1])
    column_labels = [label for label, _ in columns]
    column_centers = [center for _, center in columns]

    rows: List[Dict[str, Any]] = []
    anchor_lines: set[int] = set()
    for ln in block:
        text = (ln.text or '').strip()
        if not text:
            continue
        m_circ = CIRCLED_CHOICE_RE.match(text)
        m_plain = PLAIN_CHOICE_RE.match(text)
        anchor = None
        remainder = ''
        if m_circ:
            anchor = m_circ.group(0)
            remainder = text[m_circ.end():].strip()
        elif m_plain:
            anchor = m_plain.group(1)
            remainder = text[m_plain.end():].strip()
        if anchor:
            row = {
                'index': anchor,
                'y': ln.y1,
                'cols': [[] for _ in column_labels],
            }
            if remainder:
                row['cols'][0].append(remainder)
            rows.append(row)
            anchor_lines.add(id(ln))
    if len(rows) < 2:
        return None

    rows.sort(key=lambda r: -r['y'])

    for ln in block:
        if id(ln) in anchor_lines:
            continue
        text = (ln.text or '').strip()
        if not text:
            continue
        if use_paren_labels and PAREN_MATRIX_LABEL_RE.match(text):
            continue
        if not use_paren_labels and MATRIX_LABEL_RE.match(text):
            continue
        if CIRCLED_CHOICE_RE.match(text) or PLAIN_CHOICE_RE.match(text):
            continue
        center = (ln.x0 + ln.x1) / 2.0
        col_idx = min(range(len(column_centers)), key=lambda idx: abs(column_centers[idx] - center))
        row = min(rows, key=lambda r: abs(r['y'] - ln.y1))
        row['cols'][col_idx].append(text)

    options: List[Dict[str, str]] = []
    for row in rows:
        pieces = []
        for label, texts in zip(column_labels, row['cols']):
            cell = ' '.join(txt for txt in texts if txt).strip()
            if not cell:
                continue
            pieces.append(f"{label} {cell}")
        options.append({'index': row['index'], 'text': ' / '.join(pieces)})
    return options


def _parse_qas_from_lines(lines: List[Line], subject: str, year: Optional[int], target: Optional[str]) -> List[Dict[str, Any]]:
    qas: List[Dict[str, Any]] = []
    qnum, qtxt, opts, cur_opt, cur_txt = None, [], [], None, []

    def flush_opt():
        nonlocal cur_opt, cur_txt, opts
        if cur_opt:
            opts.append({"index": cur_opt, "text": " ".join(cur_txt).strip()})
        cur_opt, cur_txt = None, []

    def flush_q():
        nonlocal qnum, qtxt, opts, qas
        if qnum:
            normalized_opts = _reshape_matrix_options(opts[:])
            qas.append({
                "subject": subject,
                "year": year,
                "target": target,
                "content": {
                    "question_number": qnum,
                    "question_text": " ".join(qtxt).strip(),
                    "options": normalized_opts,
                },
            })
        qnum, qtxt, opts = None, [], []

    i = 0
    while i < len(lines):
        raw = lines[i]
        text = (raw.text if isinstance(raw, Line) else str(raw)) or ''
        stripped = text.strip()
        # 1) Detect start of a new question
        m_q = QNUM_RE.match(stripped)
        if m_q:
            flush_opt(); flush_q()
            qnum = int(m_q.group(1)); qtxt = [m_q.group(2).strip()]
            i += 1
            continue

        if qnum and (MATRIX_LABEL_RE.match(stripped) or PAREN_MATRIX_LABEL_RE.match(stripped)):
            block, next_idx = _collect_matrix_block(lines, i)
            matrix_opts = _parse_matrix_block(block)
            if matrix_opts:
                flush_opt()
                opts.extend(matrix_opts)
                i = next_idx
                continue

        # 2) Split inline options: a physical line may have multiple anchors (e.g., "② ... ③ ... ④ ...")
        parts = split_inline_options(text)
        if parts and qnum:
            # Close previous option (if any) before starting anchors
            flush_opt()
            # Emit all but the last option immediately (these won't have continuation lines)
            if len(parts) > 1:
                for idx_label, body in parts[:-1]:
                    opts.append({"index": idx_label, "text": body.strip()})
            # Keep the last option open to allow the next lines to continue its body
            last_idx, last_body = parts[-1]
            cur_opt = last_idx
            cur_txt = [last_body.strip()] if last_body else []
            i += 1
            continue

        # 3) Continuations
        if cur_opt:
            cur_txt.append(stripped)
        elif qnum:
            qtxt.append(stripped)
        i += 1

    flush_opt(); flush_q()
    return qas

# ================================================================
# MAIN EXTRACTION
# ================================================================
def extract_all_subjects_qa(
    pdf_path: str,
    json_out_combined: Optional[str] = None,
    json_out_per_subject_dir: Optional[str] = None,
    audit: bool = True,
    audit_csv_out: Optional[str] = None,
    audit_json_out: Optional[str] = None,
):
    year = infer_year_from_filename(pdf_path)
    pages = extract_lines_by_side(pdf_path)
    current_subj, current_target, skip = None, None, False
    per_subject = {s: [] for s in TARGET_SUBJECTS}
    audit_rows = []

    for p in pages:
        pg = p["page_index"] + 1
        subj, target = p["subject"], p["target"]
        is_target = subj in TARGET_SUBJECTS
        if is_target:
            current_subj, current_target, skip = subj, target, False
            action = f"ENTER {subj}"
        elif subj is None:
            if skip or not current_subj:
                action = "SKIP"
                audit_rows.append((pg, subj, current_subj, skip, action))
                continue
            action = f"INHERIT {current_subj}"
        else:
            current_subj, current_target, skip = None, None, True
            action = f"RESET (non-target)"
            audit_rows.append((pg, subj, current_subj, skip, action))
            continue
        if audit: print(f"[page {pg}] header={subj} target={target} -> {action}")
        audit_rows.append((pg, subj, current_subj, skip, action))
        if current_subj not in TARGET_SUBJECTS:
            continue
        ordered_lines = list(p.get("ordered") or [])
        if not ordered_lines:
            left_blocks = list(p.get("left") or [])
            right_blocks = list(p.get("right") or [])
            ordered_lines = left_blocks + right_blocks
        per_subject[current_subj].append((current_target or "default", ordered_lines))

    combined = []
    for subj in TARGET_SUBJECTS:
        groups = {}
        for targ, lines in per_subject[subj]:
            groups.setdefault(targ, []).extend(lines)
        for targ, lines in groups.items():
            qas = _parse_qas_from_lines(lines, subj, year, targ)
            combined.extend(qas)
            if json_out_per_subject_dir:
                os.makedirs(json_out_per_subject_dir, exist_ok=True)
                fname = f"{subj}_{targ}_QA.json".replace("/", "_")
                with open(os.path.join(json_out_per_subject_dir, fname), "w", encoding="utf-8") as f:
                    json.dump(qas, f, ensure_ascii=False, indent=2)

    if json_out_combined:
        with open(json_out_combined, "w", encoding="utf-8") as f:
            json.dump(combined, f, ensure_ascii=False, indent=2)

    if audit_csv_out:
        with open(audit_csv_out, "w", newline="", encoding="utf-8") as f:
            w = csv.writer(f)
            w.writerow(["page", "detected_subject", "current_subject", "skip", "action"])
            for r in audit_rows: w.writerow(r)

    if audit_json_out:
        with open(audit_json_out, "w", encoding="utf-8") as f:
            json.dump(
                [{"page": r[0], "detected_subject": r[1], "current_subject": r[2], "skip": r[3], "action": r[4]}
                 for r in audit_rows],
                f, ensure_ascii=False, indent=2)

    return combined

# ================================================================
# YEAR INFERENCE
# ================================================================
def infer_year_from_filename(path: str) -> Optional[int]:
    fname = os.path.basename(path)
    m = re.search(r"(\d{2})년", fname)
    if m:
        yy = int(m.group(1))
        return 2000 + yy
    m = re.search(r"(20\d{2}|19\d{2})", fname)
    if m:
        return int(m.group(1))
    return None

# ================================================================
# RUN
# ================================================================
if __name__ == "__main__":
    pdf_path = r"C:\Users\Jae\Desktop\HM\docs\exam\pdf\20년 1차.pdf"
    combined_out = r"C:\Users\Jae\Desktop\HM\23년_1차_ALL_QA.json"
    per_subject_dir = r"C:\Users\Jae\Desktop\HM\23년_1차_per_subject"
    audit_csv = r"C:\Users\Jae\Desktop\HM\audit_pages.csv"
    audit_json = r"C:\Users\Jae\Desktop\HM\audit_pages.json"

    results = extract_all_subjects_qa(
        pdf_path=pdf_path,
        json_out_combined=combined_out,
        json_out_per_subject_dir=per_subject_dir,
        audit=True,
        audit_csv_out=audit_csv,
        audit_json_out=audit_json,
    )
    print(f"✅ Extracted {len(results)} total")
    print(f"✅ Combined JSON: {combined_out}")
    print(f"✅ Audit CSV: {audit_csv}")
    print(f"✅ Audit JSON: {audit_json}")
