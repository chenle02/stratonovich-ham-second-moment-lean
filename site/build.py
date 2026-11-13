#!/usr/bin/env python3
"""Build the static documentation site of this repository.

Usage: python3 site/build.py OUTDIR

Every page is rendered from the repository's own files (README.md, COMPLETION.md,
FORMALIZATION.md, docs/statement-ledger.md) plus the few hand-written pages in site/.
Those files are the authority; the site repeats them and adds navigation. The output
is plain static HTML (served with .nojekyll from the gh-pages branch): no Jekyll, no
GitHub Actions build, no external script or font. Requires Python-Markdown (3.x).

Links: a link to a file that has a page here goes to that page; any other relative
link goes to the file on GitHub (blob/main or tree/main); README anchors go to the
page that carries that section.
"""
import html
import os
import re
import shutil
import sys

import markdown

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
GH = "https://github.com/chenle02/stratonovich-ham-second-moment-lean"
SITE_URL = "https://chenle02.github.io/stratonovich-ham-second-moment-lean/"
SITE_TITLE = "Stratonovich HAM Second Moment: Lean Companion"
TAGLINE = "Lean 4 paper companion · partial formalization · Apache-2.0"
DESCRIPTION = ("Lean 4 companion (partial formalization) to the second moment of the "
               "Stratonovich hyperbolic Anderson model: finite, algebraic and scalar steps "
               "checked by Lean, analytic inputs as explicit hypotheses; correspondence "
               "reviewed by AI, not by a human.")

# page file -> (title, list of sources). A source is ("file", path), ("readme", [sections])
# or ("hand", path under site/).
PAGES = [
    ("index.html", "Home", [("hand", "index.md")]),
    ("what-is-checked.html", "What is checked",
     [("readme", ["What is checked", "What is not checked"])]),
    ("completion.html", "Completion record", [("file", "COMPLETION.md")]),
    ("statement-ledger.html", "Statement ledger", [("file", "docs/statement-ledger.md")]),
    ("formalization.html", "Formalization scope", [("file", "FORMALIZATION.md")]),
    ("trust.html", "Trust and verification",
     [("hand", "coverage-note.md"), ("readme", ["Trust", "Verification record"])]),
    ("getting-started.html", "Build and verify", [("readme", ["Build", "Architecture"])]),
    ("cite.html", "Cite",
     [("readme", ["Citation", "License", "Attribution and acknowledgments"])]),
]

MENU = [
    ("Start", [("index.html", "Home"), ("getting-started.html", "Build and verify")]),
    ("Results", [("what-is-checked.html", "What is checked"),
                 ("completion.html", "Completion record"),
                 ("statement-ledger.html", "Statement ledger"),
                 ("formalization.html", "Formalization scope")]),
    ("Evidence", [("trust.html", "Trust and verification"), ("cite.html", "Cite")]),
]

# repository files that have a page on this site
FILE_PAGES = {
    "README.md": "index.html",
    "COMPLETION.md": "completion.html",
    "FORMALIZATION.md": "formalization.html",
    "docs/statement-ledger.md": "statement-ledger.html",
}


def slug(text):
    """GitHub-style heading anchor."""
    s = re.sub(r"<[^>]+>", "", text).strip().lower()
    s = re.sub(r"[^\w\- ]", "", s)
    return s.replace(" ", "-")


def readme_sections():
    """README.md split into its level-2 sections, plus the header parts."""
    text = open(os.path.join(REPO, "README.md"), encoding="utf-8").read()
    parts = re.split(r"(?m)^## (.+)$", text)
    head, sections = parts[0], {}
    for i in range(1, len(parts), 2):
        sections[parts[i].strip()] = "## " + parts[i] + parts[i + 1]
    badges = "\n".join(l for l in head.splitlines() if l.startswith("[!["))
    intro = head.split("</div>", 1)[1] if "</div>" in head else ""
    return sections, badges, intro


SECTIONS, BADGES, INTRO = readme_sections()

# README anchor -> page carrying that section
ANCHOR_PAGE = {}
for page, _title, sources in PAGES:
    for kind, arg in sources:
        if kind == "readme":
            for name in arg:
                ANCHOR_PAGE[slug(name)] = page
for name in ("At a glance", "This release"):
    ANCHOR_PAGE[slug(name)] = "index.html"
ANCHOR_PAGE["theorem-to-paper-map"] = "completion.html"
ANCHOR_PAGE["milestones"] = "completion.html#milestones"


def alerts(md):
    """GitHub alert blocks (> [!IMPORTANT] ...) -> a boundary box."""
    out, lines, i = [], md.splitlines(), 0
    while i < len(lines):
        m = re.match(r"^> \[!(IMPORTANT|NOTE|WARNING|CAUTION|TIP)\]\s*$", lines[i])
        if not m:
            out.append(lines[i])
            i += 1
            continue
        i += 1
        body = []
        while i < len(lines) and lines[i].startswith(">"):
            body.append(lines[i][1:].lstrip(" ") if lines[i] != ">" else "")
            i += 1
        out += ['<div class="boundary" markdown="1">', ""] + body + ["", "</div>"]
    return "\n".join(out)


def mark_html_blocks(md):
    """Let Markdown inside <details>/<div> blocks render (md_in_html)."""
    md = re.sub(r"<details>", '<details markdown="1">', md)
    md = re.sub(r"<div align=\"center\">", '<div markdown="1">', md)
    return md


def expand_includes(md):
    def repl(m):
        src, what = m.group(1), m.group(2).strip()
        if src == "README.md":
            if what == "badges":
                return BADGES
            if what == "intro":
                # on the home page the checked steps are on another page, not "below"
                old = "Lean checks the steps listed below."
                if old not in " ".join(INTRO.replace(">", " ").split()):
                    raise SystemExit("README intro changed: review site/build.py")
                return re.sub(r"listed\s+below\.",
                              "listed on the [What is checked](what-is-checked.html) page.",
                              INTRO, count=1)
            if what.startswith("section:"):
                return SECTIONS[what.split(":", 1)[1].strip()]
        else:
            return open(os.path.join(REPO, src), encoding="utf-8").read()
        raise SystemExit("unknown include: " + m.group(0))
    return re.sub(r"<!-- include (\S+)\s*([^>]*?)-->", repl, md)


def rewrite_link(target, from_path):
    """A relative link of a Markdown file at from_path (repository-relative)."""
    if re.match(r"^[a-z]+:", target) or target.startswith("//"):
        return target
    if target.startswith("#"):
        if from_path == "README.md":
            page = ANCHOR_PAGE.get(target[1:])
            if page:
                return page if "#" in page else page + target
        return target
    path, _, frag = target.partition("#")
    if path in {p for p, _t, _s in PAGES}:
        return target
    full =os.path.normpath(os.path.join(os.path.dirname(from_path), path))
    if full in FILE_PAGES:
        return FILE_PAGES[full] + ("#" + frag if frag else "")
    kind = "tree" if os.path.isdir(os.path.join(REPO, full)) else "blob"
    if not os.path.exists(os.path.join(REPO, full)):
        raise SystemExit("link to a missing file: %s (in %s)" % (target, from_path))
    return "%s/%s/main/%s%s" % (GH, kind, full, "#" + frag if frag else "")


def rewrite_links(md, from_path):
    # inline Markdown links and images outside code; code spans are protected first
    stash = []

    def keep(m):
        stash.append(m.group(0))
        return "\x00%d\x00" % (len(stash) - 1)
    md = re.sub(r"(?s)```.*?```", keep, md)
    md = re.sub(r"`[^`\n]*`", keep, md)
    md = re.sub(r"(\]\()([^)\s]+)(\))",
                lambda m: m.group(1) + rewrite_link(m.group(2), from_path) + m.group(3), md)
    # href="..." in raw HTML (for example inside a <summary>)
    md = re.sub(r'(href=")([^"]+)(")',
                lambda m: m.group(1) + rewrite_link(m.group(2), from_path) + m.group(3), md)
    return re.sub(r"\x00(\d+)\x00", lambda m: stash[int(m.group(1))], md)


def render(md):
    conv = markdown.Markdown(extensions=["tables", "fenced_code", "md_in_html", "toc", "sane_lists"],
                             extension_configs={"toc": {"slugify": lambda v, sep: slug(v)}})
    return conv.convert(md)


def page_markdown(sources):
    chunks = []
    for kind, arg in sources:
        if kind == "hand":
            md = open(os.path.join(REPO, "site", arg), encoding="utf-8").read()
            md = expand_includes(md)
            md = rewrite_links(alerts(mark_html_blocks(md)), "README.md")
        elif kind == "readme":
            md = "\n\n".join(SECTIONS[name] for name in arg)
            md = rewrite_links(alerts(mark_html_blocks(md)), "README.md")
        else:
            md = open(os.path.join(REPO, arg), encoding="utf-8").read()
            md = rewrite_links(alerts(mark_html_blocks(md)), arg)
        chunks.append(md)
    return "\n\n".join(chunks)


def menu_html(current):
    out = []
    for group, items in MENU:
        out.append('<p class="group">%s</p>\n<ul>' % html.escape(group))
        for href, label in items:
            cur = ' aria-current="page"' if href == current else ""
            out.append('<li><a href="%s"%s>%s</a></li>' % (href, cur, html.escape(label)))
        out.append("</ul>")
    out.append('<p class="group">Elsewhere</p>\n<ul>')
    out.append('<li><a href="%s">Source on GitHub</a></li>' % GH)
    out.append('<li><a href="https://doi.org/10.5281/zenodo.24199104">Zenodo (all versions)</a></li>')
    out.append('<li><a href="llms.txt">llms.txt</a></li>')
    out.append("</ul>")
    return "\n".join(out)


FOOTER = ('stratonovich-ham-second-moment-lean · Le Chen · developed with '
          '<a href="https://github.com/lean-pkg/lean-pkg">lean-pkg</a> · '
          '<a href="%s/blob/main/CITATION.cff">CITATION.cff</a> · '
          '<a href="%s/blob/main/LICENSE">Apache-2.0</a>' % (GH, GH))


def main():
    if len(sys.argv) != 2:
        raise SystemExit(__doc__)
    out = os.path.abspath(sys.argv[1])
    if os.path.exists(out):
        raise SystemExit("refusing to overwrite an existing directory: " + out)
    os.makedirs(out)
    layout = open(os.path.join(REPO, "site", "layout.html"), encoding="utf-8").read()
    for page, title, sources in PAGES:
        body = render(page_markdown(sources))
        if page != "index.html":
            body = "<h1>%s</h1>\n%s" % (html.escape(title), body)
        full_title = SITE_TITLE if page == "index.html" else "%s · %s" % (title, SITE_TITLE)
        doc = layout
        for key, val in (("{title}", html.escape(full_title)),
                         ("{description}", html.escape(DESCRIPTION)),
                         ("{canonical}", SITE_URL + ("" if page == "index.html" else page)),
                         ("{site_title}", html.escape(SITE_TITLE)),
                         ("{tagline}", html.escape(TAGLINE)),
                         ("{menu}", menu_html(page)),
                         ("{footer}", FOOTER)):
            doc = doc.replace(key, val)
        doc = doc.replace("{content}", body)
        with open(os.path.join(out, page), "w", encoding="utf-8") as fh:
            fh.write(doc)
    shutil.copytree(os.path.join(REPO, "site", "assets"), os.path.join(out, "assets"))
    shutil.copy(os.path.join(REPO, "site", "llms.txt"), os.path.join(out, "llms.txt"))
    open(os.path.join(out, ".nojekyll"), "w").close()
    print("built %d pages in %s" % (len(PAGES), out))


if __name__ == "__main__":
    main()
