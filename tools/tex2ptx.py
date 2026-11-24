#!/usr/bin/env python3
"""Багшийн LaTeX лекцийг PreTeXt рүү хөрвүүлэх туслах скрипт.

Энэ нь зөвхөн эхний хувилбар гаргана; гаралтыг гараар шалгаж засна.
Хэрэглээ: python3 tools/tex2ptx.py config.json
"""
import json
import re
import sys
from pathlib import Path

THM_ENVS = {
    "dfn": "definition", "thm": "theorem", "lem": "lemma", "cor": "corollary",
    "prp": "proposition", "axm": "axiom", "exm": "example", "hnt": "remark",
    "sen": "remark", "exe": "exercise", "exerciseT": "exercise",
}
PROOFABLE = {"theorem", "lemma", "corollary", "proposition"}
DISPLAY_ENVS = {"equation", "equation*", "align", "align*", "gather", "gather*",
                "eqnarray", "eqnarray*", "multline", "multline*"}
EXERCISE_SECTION = re.compile(r"Бодлого|Семинар", re.I)

# Нэр томъёо нэгтгэх (нэр томъёоны жагсаалтаар батлагдсан)
TERMS = [
    (r"Борелын", "Борелийн"), (r"Борелиор", "Борелээр"),
    (r"Каратеодорын", "Каратеодорийн"), (r"Каратеодоры", "Каратеодорийн"),
    (r"эзэлхүүн", "эзлэхүүн"), (r"төгсгөлөг өөрчлөлттэй", "зааглагдсан өөрчлөлттэй"),
    (r"бараг хаа сайгүй", "бараг бүх цэгт"),
    (r"интегралчлагддаг", "интегралчлагдах"),
    (r"неотрицатель", "сөрөг бус"), (r"хэмжүүр", "хэмжээ"),
]


def strip_comments(s):
    out = []
    for line in s.split("\n"):
        m = re.search(r"(?<!\\)%", line)
        if m:
            line = line[: m.start()]
            if not line.strip():
                continue
        out.append(line)
    return "\n".join(out)


def match_brace(s, i):
    """s[i] == '{' ; return index of matching '}'"""
    depth = 0
    j = i
    while j < len(s):
        c = s[j]
        if c == "\\":
            j += 2
            continue
        if c == "{":
            depth += 1
        elif c == "}":
            depth -= 1
            if depth == 0:
                return j
        j += 1
    raise ValueError("unbalanced brace at %d: %r" % (i, s[i:i + 60]))


def match_bracket(s, i):
    depth = 0
    j = i
    while j < len(s):
        c = s[j]
        if c == "{":
            j = match_brace(s, j) + 1
            continue
        if c == "[":
            depth += 1
        elif c == "]":
            depth -= 1
            if depth == 0:
                return j
        j += 1
    raise ValueError("unbalanced bracket")


def expand_macro(s, name, nargs, template):
    pat = re.compile(r"\\" + name + r"(?![a-zA-Z])")
    while True:
        m = pat.search(s)
        if not m:
            return s
        j = m.end()
        args = []
        for _ in range(nargs):
            while j < len(s) and s[j] in " \n\t":
                j += 1
            if s[j] != "{":
                raise ValueError(name)
            k = match_brace(s, j)
            args.append(s[j + 1:k])
            j = k + 1
        rep = template
        for n, a in enumerate(args, 1):
            rep = rep.replace("#%d" % n, a)
        s = s[: m.start()] + rep + s[j:]


MATH_SPAN = re.compile(r"\$\$.*?\$\$|(?<!\\)\$.*?(?<!\\)\$|\\\[.*?\\\]|\\\(.*?\\\)", re.S)


def protect_math(s):
    def rep(m):
        x = re.sub(r"\n\s*\n", "\n", m.group(0))
        return x.replace("\\begin{", "\\bEgIn{").replace("\\end{", "\\eNd{")
    return MATH_SPAN.sub(rep, s)


def preprocess(s):
    s = strip_comments(s)
    s = re.sub(r"\\\\\[[^\]]*\]", r"\\\\", s)  # \\[2mm] -> \\
    s = s.replace("\\siga", "$\\sigma$-алгебр ")
    s = expand_macro(s, "enum", 1, "\\begin{enumerate}[a)]#1\\end{enumerate}")
    s = expand_macro(s, "enumn", 1, "\\begin{enumerate}#1\\end{enumerate}")
    s = expand_macro(s, "eqn", 2, "\\begin{equation}\\label{#1}#2\\end{equation}")
    s = expand_macro(s, "proof", 1, "\\begin{proof}#1\\end{proof}")
    s = re.sub(r"\\(begin|end)\{2col\}", "\n\n", s)
    s = re.sub(r"\\begin\{exerciseT\}", r"\\begin{exe}", s)
    s = re.sub(r"\\end\{exerciseT\}", r"\\end{exe}", s)
    s = re.sub(r"\\(newpage|noindent|hfill|medskip|bigskip|smallskip|centering)\b", "", s)
    s = re.sub(r"\\vspace\*?\{[^}]*\}", "", s)
    s = s.replace("\\qedhere", "")
    s = re.sub(r"\\(begin|end)\{(multicols|center)\}(\{\d\})?", "\n\n", s)
    for a, b in TERMS:
        s = re.sub(a, b, s)
    s = s.replace("\\\\", "\\\\ ")
    s = protect_math(s)
    return s


# ---------------------------------------------------------------- labels
GLOBAL_LABELS = {
    # 1-р бүлгийг гараар хөрвүүлсэн
    "saeq": "prop-generated-compare", "intsigalg1": "prop-intersection-sigma",
    "torogdson": "prop-generated", "algebra": "ex-finite-cofinite",
}


class Ctx:
    def __init__(self, prefix):
        self.prefix = prefix
        self.labels = {}
        self.figs = []
        self.solutions = []

    def ref(self, label):
        lab = label.strip()
        if lab in self.labels or GLOBAL_LABELS.get(lab, (None,))[0] == self.prefix:
            return '<xref ref="%s"/>' % self.lid(lab)
        if lab in GLOBAL_LABELS:
            g = GLOBAL_LABELS[lab]
            return '<xref ref="%s"/>' % (g if isinstance(g, str) else self._mk(g[0], lab))
        return '<!-- TODO: ref %s олдсонгүй -->(?)' % lab

    @staticmethod
    def _mk(prefix, lab):
        safe = re.sub(r"[^A-Za-z0-9_-]", "-", lab)
        if not re.match(r"[A-Za-z]", safe):
            safe = "x" + safe
        return "%s-%s" % (prefix, safe)

    def lid(self, label):
        lab = label.strip()
        if lab not in self.labels:
            safe = re.sub(r"[^A-Za-z0-9_-]", "-", lab)
            if not re.match(r"[A-Za-z]", safe):
                safe = "x" + safe
            self.labels[lab] = "%s-%s" % (self.prefix, safe)
        return self.labels[lab]


# ---------------------------------------------------------------- math
REF_ONLY = re.compile(r"^(?:[\s(),]|\\ref\{[^}]*\})*\\ref\{[^}]*\}(?:[\s(),]|\\ref\{[^}]*\})*$")

def xml_math(s):
    s = s.replace("\\bEgIn{", "\\begin{").replace("\\eNd{", "\\end{")
    s = s.replace("&", "&amp;").replace("<", "\\lt ").replace(">", "\\gt ")
    return s


def conv_display(body, ctx, env="equation"):
    multirow = env.startswith(("align", "eqnarray", "gather", "multline")) and "\\\\" in body
    if multirow and not env.startswith("multline") and len(re.findall(r"\\label\{", body)) > 0:
        return conv_rows_labeled(body, ctx, env)
    labels = re.findall(r"\\label\{([^}]*)\}", body)
    body = re.sub(r"\\label\{[^}]*\}", "", body)
    body = re.sub(r"\\eqno\s*\(([^)]*)\)", r"\\tag{\1}", body)
    body = re.sub(r"\\eqno\s*\{?([^}\n]*)\}?", r"\\tag{\1}", body)
    body = body.replace("\\notag", "").replace("\\nonumber", "")
    body = body.strip()
    attrs = ""
    if labels:
        attrs = ' number="yes" xml:id="%s"' % ctx.lid(labels[0])
    if env.startswith(("align", "eqnarray", "gather", "multline")) and "\\\\" in body:
        rows = [r.strip() for r in re.split(r"\\\\(?:\[[^\]]*\])?", body) if r.strip()]
        if env.startswith("eqnarray"):
            rows = [re.sub(r"&\s*([^&]*?)\s*&", r"\1 &", r, count=1) for r in rows]
        if env.startswith(("gather", "multline")):
            rows = [r.replace("&", "") for r in rows]
        inner = "".join("<mrow%s>%s</mrow>" % (attrs if k == len(rows) - 1 else "", xml_math(r))
                        for k, r in enumerate(rows))
        return "<md>%s</md>" % inner
    if env.startswith(("align", "eqnarray")):
        body = body.replace("&", "")
    return "<md%s>%s</md>" % (attrs, xml_math(body))


def conv_rows_labeled(body, ctx, env):
    body = re.sub(r"\\eqno\s*\(([^)]*)\)", r"\\tag{\1}", body).replace("\\notag", "").replace("\\nonumber", "")
    rows = [r.strip() for r in re.split(r"\\\\(?:\[[^\]]*\])?", body) if r.strip()]
    out = []
    for r in rows:
        lab = re.search(r"\\label\{([^}]*)\}", r)
        r = re.sub(r"\\label\{[^}]*\}", "", r)
        if env.startswith("eqnarray"):
            r = re.sub(r"&\s*([^&]*?)\s*&", r"\1 &", r, count=1)
        if env.startswith("gather"):
            r = r.replace("&", "")
        a = ' number="yes" xml:id="%s"' % ctx.lid(lab.group(1)) if lab else ""
        out.append("<mrow%s>%s</mrow>" % (a, xml_math(r)))
    return "<md>%s</md>" % "".join(out)


# ---------------------------------------------------------------- inline
def conv_inline(t, ctx):
    """Convert a run of text (no environments) to PreTeXt inline markup."""
    out = []
    i = 0
    buf = []

    def flush():
        if buf:
            out.append(text_xml("".join(buf), ctx))
            buf.clear()

    while i < len(t):
        if t.startswith("$$", i):
            j = t.index("$$", i + 2)
            flush()
            out.append(conv_display(t[i + 2:j], ctx))
            i = j + 2
        elif t.startswith("\\[", i):
            j = t.index("\\]", i + 2)
            flush()
            out.append(conv_display(t[i + 2:j], ctx))
            i = j + 2
        elif t[i] == "$" and (i == 0 or t[i - 1] != "\\"):
            j = i + 1
            while True:
                j = t.index("$", j)
                if t[j - 1] != "\\":
                    break
                j += 1
            flush()
            inner = t[i + 1:j].strip()
            if REF_ONLY.match(inner):
                # math that holds only references, e.g. $(\ref{a}) , (\ref{b})$: emit as text with xrefs
                out.append(re.sub(r"\\ref\{([^}]*)\}", lambda mm: ctx.ref(mm.group(1)), re.sub(r"\s+", " ", inner)))
            else:
                out.append("<m>%s</m>" % xml_math(inner))
            i = j + 1
        elif t.startswith("\\(", i):
            j = t.index("\\)", i)
            flush()
            out.append("<m>%s</m>" % xml_math(t[i + 2:j].strip()))
            i = j + 2
        else:
            buf.append(t[i])
            i += 1
    flush()
    return "".join(out)


def text_xml(s, ctx):
    s = s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")
    s = s.replace("~", " ").replace("\\\\", " ").replace("\\,", " ")
    s = re.sub(r"\\(quad|qquad)\b", " ", s)
    s = s.replace("``", "“").replace("''", "”").replace("--", "–")
    s = re.sub(r"\\(eq)?ref\{([^}]*)\}", lambda m: ctx.ref(m.group(2)), s)
    s = re.sub(r"\\label\{[^}]*\}", "", s)
    s = re.sub(r"\\(?:ldots|dots)\b", "…", s)
    # simple formatting groups
    for _ in range(3):
        s = re.sub(r"\{\\bf\s+([^{}]*)\}", r"<term>\1</term>", s)
        s = re.sub(r"\{\\(?:em|it)\s+([^{}]*)\}", r"<em>\1</em>", s)
        s = re.sub(r"\\textbf\{([^{}]*)\}", r"<term>\1</term>", s)
        s = re.sub(r"\\(?:emph|textit)\{([^{}]*)\}", r"<em>\1</em>", s)
        s = re.sub(r"\\(?:textrm|text|mbox)\{([^{}]*)\}", r"\1", s)
        s = re.sub(r"\\underline\{([^{}]*)\}", r"<em>\1</em>", s)
    s = re.sub(r"\{\\(?:em|it|bf)\s*", "", s)
    s = s.replace("\\ ", " ")
    s = re.sub(r"\\R\b", "ℝ", s)
    return s


def fix_inline_groups(x):
    """\\textbf{..$..$..} etc. after math conversion"""
    for _ in range(3):
        x = re.sub(r"\\textbf\{((?:[^{}]|<m>[^<]*</m>)*)\}", r"<term>\1</term>", x)
        x = re.sub(r"\{\\bf\s+((?:[^{}]|<m>[^<]*</m>)*)\}", r"<term>\1</term>", x)
        x = re.sub(r"\{\\(?:em|it)\s+((?:[^{}]|<m>[^<]*</m>)*)\}", r"<em>\1</em>", x)
        x = re.sub(r"\\(?:emph|textit)\{((?:[^{}]|<m>[^<]*</m>)*)\}", r"<em>\1</em>", x)
        x = re.sub(r"\\index\{((?:[^{}]|<m>[^<]*</m>)*)\}", r"<idx>\1</idx>", x)
        x = re.sub(r"\{\\(?:it|em)\{((?:[^{}]|<m>[^<]*</m>)*)\}\}", r"<em>\1</em>", x)
    # stray braces / font switches outside math
    parts = re.split(r"(<m>.*?</m>|<md.*?</md>)", x, flags=re.S)
    for k in range(0, len(parts), 2):
        parts[k] = re.sub(r"\\(?:it|em|bf|rm)\b\s*", "", parts[k]).replace("{", "").replace("}", "")
    return "".join(parts)


# ---------------------------------------------------------------- blocks
ENV_RE = re.compile(r"\\begin\{([a-zA-Z*]+)\}")


def find_env_end(s, start, name):
    pat = re.compile(r"\\(begin|end)\{" + re.escape(name) + r"\}")
    depth = 1
    for m in pat.finditer(s, start):
        depth += 1 if m.group(1) == "begin" else -1
        if depth == 0:
            return m.start(), m.end()
    raise ValueError("no end for %s near: %r" % (name, s[max(0,start-80):start+80]))


def parse_opt(s, j):
    while j < len(s) and s[j] in " \t":
        j += 1
    if j < len(s) and s[j] == "[":
        k = match_bracket(s, j)
        return s[j + 1:k], k + 1
    return None, j


def split_items(body):
    """split list body at top-level \\item"""
    items = []
    depth = 0
    i = 0
    cur_start = None
    cur_label = None
    pat = re.compile(r"\\(begin|end)\{(?:enumerate|itemize|description)\}|\\item\b")
    for m in pat.finditer(body):
        if m.group(0).startswith("\\item"):
            if depth == 0:
                if cur_start is not None:
                    items.append((cur_label, body[cur_start:m.start()]))
                lab, j = parse_opt(body, m.end())
                cur_label, cur_start = lab, j
        elif m.group(1) == "begin":
            depth += 1
        else:
            depth -= 1
    if cur_start is not None:
        items.append((cur_label, body[cur_start:]))
    return items


def marker_of(opt):
    if not opt:
        return None
    o = opt.replace("$", "").strip()
    o = re.sub(r"label=", "", o)
    o = o.replace("\\alph*", "a").replace("\\arabic*", "1").replace("\\roman*", "i")
    if re.fullmatch(r"\(?[aA1iI]\)?\.?", o):
        return o
    return None


def conv_list(env, opt, body, ctx):
    items = split_items(body)
    tag = "ol" if env == "enumerate" else "ul"
    mk = marker_of(opt) if env == "enumerate" else None
    custom = env != "enumerate" or (opt and not mk)
    lis = []
    for lab, content in items:
        inner = conv_flow(content, ctx)
        if lab and (custom or env == "itemize" or env == "description"):
            labx = conv_inline(lab, ctx)
            if env == "description":
                labx = "<term>%s</term>" % labx
            inner = add_label(inner, labx)
        lis.append("<li>%s</li>" % inner)
    attr = ' marker="%s"' % mk if mk else ""
    if tag == "ol" and custom:
        tag = "ul"
        attr = ' marker=""'
    if tag == "ul" and any(lab for lab, _ in items) and not attr:
        attr = ' marker=""'
    return "<%s%s>%s</%s>" % (tag, attr, "".join(lis), tag)


def add_label(inner, labx):
    if inner.startswith("<p>"):
        return "<p>%s %s" % (labx, inner[3:])
    return "<p>%s</p>%s" % (labx, inner)


def conv_flow(s, ctx):
    """Convert flowing content (paragraph level) into a sequence of <p> blocks.
    Lists and display math stay inside <p>."""
    paras = []
    cur = []

    def close():
        x = "".join(cur).strip()
        cur.clear()
        if x:
            paras.append("<p>%s</p>" % fix_inline_groups(x))

    i = 0
    while i < len(s):
        m = ENV_RE.search(s, i)
        nb = re.search(r"\n\s*\n", s[i:])
        nb_pos = i + nb.start() if nb else None
        env_pos = m.start() if m else None
        if nb_pos is not None and (env_pos is None or nb_pos < env_pos):
            cur.append(conv_inline(s[i:nb_pos], ctx))
            close()
            i = i + nb.end()
            continue
        if m is None:
            cur.append(conv_inline(s[i:], ctx))
            break
        cur.append(conv_inline(s[i:m.start()], ctx))
        name = m.group(1)
        bstart, bend = find_env_end(s, m.end(), name)
        body = s[m.end():bstart]
        if name in DISPLAY_ENVS:
            cur.append(conv_display(body, ctx, name))
        elif name in ("enumerate", "itemize", "description"):
            opt, j = parse_opt(body, 0)
            cur.append(conv_list(name, opt, body[j:], ctx))
        elif name in ("minipage",):
            _, j = parse_opt(body, 0)
            if body[j:j + 1] == "{":
                j = match_brace(body, j) + 1
            close()
            paras.append(conv_flow(body[j:], ctx))
        elif name == "figure":
            close()
            paras.append(conv_flow(body, ctx))
        elif name in ("cases", "array", "tabular"):
            cur.append("<!-- TODO: %s -->" % name)
            cur.append(conv_inline("$\\begin{%s}%s\\end{%s}$" % (name, body, name), ctx))
        else:
            close()
            paras.append("<!-- TODO env %s -->%s" % (name, conv_flow(body, ctx)))
        i = bend
    close()
    out = "\n".join(paras)
    out = images(out, ctx)
    return out


def images(x, ctx):
    def rep(m):
        opts, path = m.group(1) or "", m.group(2)
        w = re.search(r"width=([0-9.]+)\\textwidth", opts)
        width = "%d%%" % round(float(w.group(1)) * 100) if w else "50%"
        name = Path(path).stem.lower() + ".png"
        ctx.figs.append((path, name))
        return '</p><image source="images/%s" width="%s"/><p>' % (name, width)
    x = re.sub(r"\\includegraphics(?:\[([^\]]*)\])?\{?([^\s{}<]+)\}?", rep, x)
    x = re.sub(r"<p>\s*</p>", "", x)
    return x


def conv_blocks(s, ctx):
    """Top level of a section: theorem-like environments + flow."""
    out = []
    i = 0
    pending_flow = []
    last_thm = None
    pat = re.compile(r"\\begin\{(" + "|".join(list(THM_ENVS) + ["proof"]) + r")\}")
    while True:
        m = pat.search(s, i)
        if not m:
            pending_flow.append(s[i:])
            break
        pending_flow.append(s[i:m.start()])
        flow = "".join(pending_flow).strip()
        pending_flow = []
        if flow:
            out.append(conv_flow(flow, ctx))
            last_thm = None
        name = m.group(1)
        bstart, bend = find_env_end(s, m.end(), name)
        body = s[m.end():bstart]
        title, j = parse_opt(body, 0)
        body = body[j:]
        labels = re.findall(r"^\s*\\label\{([^}]*)\}", body)
        lab = None
        mm = re.match(r"\s*\\label\{([^}]*)\}", body)
        if mm:
            lab = mm.group(1)
            body = body[mm.end():]
        else:
            mm = re.search(r"\\label\{([^}]*)\}", body[:200])
            if mm and not re.search(r"\\begin\{|\$\$|\\\[", body[:mm.start()]):
                lab = mm.group(1)
                body = body[:mm.start()] + body[mm.end():]
        content = conv_flow(body, ctx)
        if name == "proof":
            blk = "<proof>%s</proof>" % content
            if last_thm is not None and out and out[-1].endswith("</%s>" % last_thm):
                out[-1] = out[-1][: -len("</%s>" % last_thm)] + blk + "</%s>" % last_thm
            else:
                out.append(blk)
            last_thm = None
        else:
            tag = THM_ENVS[name]
            idattr = ' xml:id="%s"' % ctx.lid(lab) if lab else ""
            title = re.sub(r"^\s*\\bf\s*", "", title) if title else title
            tt = "<title>%s</title>" % fix_inline_groups(conv_inline(title, ctx)) if title else ""
            if tag in ("example", "remark", "exercise"):
                inner = tt + content if tag != "exercise" else tt + "<statement>%s</statement>" % content
            else:
                inner = tt + "<statement>%s</statement>" % content
            out.append("<%s%s>%s</%s>" % (tag, idattr, inner, tag))
            last_thm = tag if tag in PROOFABLE else None
        i = bend
    flow = "".join(pending_flow).strip()
    if flow:
        out.append(conv_flow(flow, ctx))
    return "\n".join(x for x in out if x.strip())


SOL_RE = re.compile(r"\\begin\{(hnt|proof|sen)\}")


def take_solutions(item, ctx):
    """Remove hint/solution environments from a problem; keep them for the teacher only."""
    sols = []
    while True:
        m = SOL_RE.search(item)
        if not m:
            break
        b, e = find_env_end(item, m.end(), m.group(1))
        sols.append(item[m.end():b].strip())
        item = item[:m.start()] + item[e:]
    return item, sols


def conv_exercises(s, ctx, xid, title="Семинарын бодлогууд", skip=()):
    """A problem section: enumerate items or exe environments become exercises.
    Hints/solutions are removed (stored in ctx.solutions, never published)."""
    probs = []   # raw tex of each problem
    pre_text = ""
    m = re.search(r"\\begin\{enumerate\}", s)
    m2 = re.search(r"\\begin\{exe\}", s)
    if m and (not m2 or m.start() < m2.start()):
        bstart, bend = find_env_end(s, m.end(), "enumerate")
        body = s[m.end():bstart]
        _, j = parse_opt(body, 0)
        probs = [it for _, it in split_items(body[j:])]
        pre_text = s[:m.start()].strip()
        rest = s[bend:]
        extra = re.split(r"\\noindent\\textbf\{[0-9.]+\}|\\textbf\{[0-9.]+\.?\}", rest)
        probs += extra[1:]
        rest_exe = extra[0]
    else:
        rest_exe = s
        parts = re.split(r"\\noindent\s*\\textbf\{[0-9.]+\}|\\textbf\{[0-9]+\.[0-9]+\.?\}", s)
        if len(parts) > 1:
            pre_text = parts[0].strip()
            probs = parts[1:]
            rest_exe = ""
    # exe environments (each possibly followed by a hint = solution)
    pos = 0
    first = True
    for mm in re.finditer(r"\\begin\{exe\}", rest_exe):
        if first and not probs:
            pre_text = rest_exe[:mm.start()].strip()
        first = False
        b, e = find_env_end(rest_exe, mm.end(), "exe")
        nxt = re.search(r"\\begin\{exe\}", rest_exe[e:])
        tail = rest_exe[e: e + nxt.start()] if nxt else rest_exe[e:]
        probs.append(rest_exe[mm.end():b] + "\n" + tail)
    body = []
    if pre_text:
        _, presol = take_solutions(pre_text, ctx)
        pre_text = _
        if pre_text.strip():
            body.append("<introduction>%s</introduction>" % conv_flow(pre_text, ctx))
    for n, e in enumerate(probs, 1):
        if n in skip:
            continue
        e, sols = take_solutions(e.strip(), ctx)
        if not e.strip():
            continue
        if sols:
            ctx.solutions.append((xid, n, e.strip(), sols))
        body.append("<exercise><statement>%s</statement></exercise>" % conv_blocks(e, ctx))
    return '<exercises xml:id="%s"><title>%s</title>\n%s\n</exercises>' % (xid, title, "\n".join(body))


def split_sections(s):
    parts = re.split(r"\\(?:chapter|section|subsection)\*?\{", s)
    out = [(None, parts[0])]
    for p in parts[1:]:
        k = match_brace("{" + p, 0) - 1
        out.append((p[:k], p[k + 1:]))
    return out


# ---------------------------------------------------------------- driver
def read_piece(src_dir, spec):
    f, a, b = spec["file"], spec.get("from", 1), spec.get("to")
    lines = (src_dir / f).read_text(encoding="utf-8").split("\n")
    if "ranges" in spec:
        return "\n".join("\n".join(lines[x - 1:y]) for x, y in spec["ranges"]) + spec.get("append", "")
    return "\n".join(lines[a - 1:b]) + spec.get("append", "")


def build_chapter(ch, src_dir, ctx):
    sections = []      # (title, xml)
    exgroups = []      # (title, raw tex)
    for spec in ch["pieces"]:
        raw = read_piece(src_dir, spec)
        for old, new in ch.get("fix", []):
            if new.startswith("@add:"):
                # new text kept in tools/additions/<name>.tex; "@@" in it stands for old
                add = (Path(__file__).resolve().parent / "additions" / (new[5:] + ".tex")).read_text(encoding="utf-8")
                new = add.replace("@@", old)
            raw = raw.replace(old, new)
        raw = preprocess(raw)
        if spec.get("kind") == "exercises":
            exgroups.append((spec.get("title"), raw, tuple(spec.get("skip", []))))
            continue
        for title, body in split_sections(raw):
            if title is None:
                if body.strip():
                    t = spec.get("title") or (sections[-1][0] if sections else ch["title"])
                    if sections and not spec.get("title"):
                        sections[-1] = (sections[-1][0], sections[-1][1] + "\n" + body)
                    else:
                        sections.append((t, body))
                continue
            if EXERCISE_SECTION.search(title):
                exgroups.append((title, body, ()))
            else:
                sections.append((title, body))
    parts = []
    for n, (title, body) in enumerate(sections, 1):
        tt = title if "<m>" in title else fix_inline_groups(conv_inline(preprocess(title).strip().rstrip("."), ctx))
        tt = re.sub(r"^\\bf\s*", "", tt)
        parts.append('<section xml:id="sec-%s-%d">\n<title>%s</title>\n%s\n</section>' %
                     (ch["slug"], n, tt, conv_blocks(body, ctx)))
    more = Path(__file__).resolve().parent.parent / "source" / "exercises" / ("sem-%s-more.ptx" % ch["slug"])
    if exgroups:
        if len(exgroups) == 1 and not more.exists():
            parts.append(conv_exercises(exgroups[0][1], ctx, "sem-" + ch["slug"], skip=exgroups[0][2]))
        else:
            subs = []
            for k, (t, raw, sk) in enumerate(exgroups, 1):
                x = conv_exercises(raw, ctx, "sem-%s-%d" % (ch["slug"], k), "", skip=sk)
                x = x.replace("<exercises", "<subexercises", 1).rsplit("</exercises>", 1)[0] + "</subexercises>"
                tt = (t if "<m>" in t else fix_inline_groups(conv_inline(t, ctx))) if t else ""
                x = x.replace("<title></title>", "<title>%s</title>" % tt if tt else "")
                subs.append(x)
            if more.exists():
                subs.append('<xi:include href="./exercises/sem-%s-more.ptx"/>' % ch["slug"])
            parts.append('<exercises xml:id="sem-%s"><title>Семинарын бодлогууд</title>\n%s\n</exercises>' %
                         (ch["slug"], "\n".join(subs)))
    extra = Path(__file__).resolve().parent.parent / "source" / "exercises" / ("sem-%s.ptx" % ch["slug"])
    if not exgroups and extra.exists():
        parts.append('<xi:include href="./exercises/sem-%s.ptx"/>' % ch["slug"])
    hw = Path(__file__).resolve().parent.parent / "source" / "exercises" / ("hw-%s.ptx" % ch["slug"])
    if hw.exists():
        parts.append('<xi:include href="./exercises/hw-%s.ptx"/>' % ch["slug"])
    tag = ch.get("tag", "chapter")
    src = "; ".join("%s:%s-%s" % (p["file"], p.get("from", 1), p.get("to", "")) for p in ch["pieces"])
    return ('<?xml version="1.0" encoding="UTF-8"?>\n<!-- Эх файл: %s -->\n'
            '<%s xml:id="%s" xmlns:xi="http://www.w3.org/2001/XInclude">\n<title>%s</title>\n%s\n</%s>\n'
            % (src, tag, ch["id"], ch["title"], "\n".join(parts), tag))


def main():
    cfg = json.loads(Path(sys.argv[1]).read_text(encoding="utf-8"))
    src_dir = Path(cfg["src"])
    out_dir = Path(cfg["out"])
    only = sys.argv[2:]
    figs = []
    for ch in cfg["chapters"]:
        for spec in ch["pieces"]:
            for lab in re.findall(r"\\label\{([^}]*)\}", preprocess(read_piece(src_dir, spec))):
                GLOBAL_LABELS.setdefault(lab.strip(), (ch["slug"],))
    for ch in cfg["chapters"]:
        if only and ch["slug"] not in only:
            continue
        ctx = Ctx(ch["slug"])
        try:
            xml = build_chapter(ch, src_dir, ctx)
        except Exception as ex:
            print("FAILED", ch["slug"], ex)
            continue
        (out_dir / ch["file"]).write_text(xml, encoding="utf-8")
        figs += ctx.figs
        print("wrote", ch["file"])
        if ctx.solutions and cfg.get("solutions"):
            sd = Path(cfg["solutions"]); sd.mkdir(parents=True, exist_ok=True)
            with open(sd / (ch["file"].replace(".ptx", ".tex")), "w", encoding="utf-8") as fh:
                fh.write("%% Семинарын бодлогын бодолт/заавар: %s (зөвхөн багшид)\n" % ch["title"])
                for xid, n, prob, sols in ctx.solutions:
                    fh.write("\n%% ---- %s, бодлого %d\n\\begin{exe}\n%s\n\\end{exe}\n" % (xid, n, prob))
                    for so in sols:
                        fh.write("\\begin{proof}[Бодолт]\n%s\n\\end{proof}\n" % so)
    for path, name in figs:
        print("FIG", path, name)


if __name__ == "__main__":
    main()
