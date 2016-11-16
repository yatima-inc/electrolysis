#! /bin/python3

import os
import re
import subprocess

import markdown
from pygments import highlight
from pygments.lexers import RustLexer, LeanLexer
from pygments.formatters import HtmlFormatter
from pygments_markdown import CodeBlockExtension

def success(path):
    ok = False
    fail = False
    rec = False
    for f in os.listdir(path):
        p = os.path.join(path, f)
        #if f == 'lib.rs':
        #    lib = open(p).read()
        #    if 'FIXME' in lib:
        #        return False  # wrong if there are passing sub items
        if f == 'generated.lean':
            gen = open(p).read()
            if ('unimplemented' in gen or 'compiler error' in gen) and not path.endswith('-'):
                fail = True
            else:
                ok = True
        if f == 'broken.lean':
            fail = True
        if os.path.isdir(p):
            rec = True
            s = success(p)
            if s != True:
                fail = True
            if s != False:
                ok = True
    if not fail and not rec:
        ok = True
    if ok and fail or not ok and not fail:
        return None
    return ok

def success_class(path):
    s = success(path)
    return "success" if s else "fail" if s == False else ""

def chapter_key(s):
    if s[0].isdigit():
        return ([int(s.split('-')[0]) for s in s.split(' ')[0].split('.')], s.split(' ')[1:])
    else:
        return ([], [s])

def toc(path):
    entries = sorted(os.listdir(path), key=chapter_key)

    yield "<ul>"
    for f in entries:
        p = os.path.join(path, f)
        if os.path.isdir(p) and f[0].isdigit():
            if ' ' in f:
                anchor = '-'.join(f.split(' ')[1:]).lower()
                name = f
                if f.endswith('.'):
                    name = ' '.join(name.split(' ')[1:])[:-1]
                yield """<li><a class="{}" href="#{}">{}</a>""".format(
                    success_class(p), anchor, name)
                yield from toc(p)
                yield "</li>"
    yield "</ul>"
    return success

def rec(path, depth):
    entries = sorted(os.listdir(path), key=chapter_key)
    if 'pre.md' in entries:
        yield markdown.markdown(open(os.path.join(path, 'pre.md')).read(), extensions=[CodeBlockExtension()])
    if 'lib.rs' in entries:
        rust = os.path.join(path, 'lib.rs')
        mir = open(os.path.join(path, 'mir')).read()
        generated = open(os.path.join(path, 'broken.lean' if '!' in path else 'generated.lean')).read()
        if '5 Crates' not in path:
            generated = re.search('(open [^\n]*\n)+\n(.*)', generated, flags=re.DOTALL).group(2)
        yield """<div>
  <label><input type="checkbox" onchange="toggle_mir(this)">Show MIR</label>
  <div class="code-pair">{}{}{}</div>
</div>""".format(
    highlight(open(rust).read(), RustLexer(), HtmlFormatter(cssclass="rust")),
    highlight(mir, RustLexer(), HtmlFormatter(cssclass="mir")),
    highlight(generated, LeanLexer(), HtmlFormatter(cssclass="lean")))
        if 'broken.lean' in entries:
            errors = subprocess.run(['lean', 'broken.lean'],
                                    cwd=path,
                                    stdout=subprocess.PIPE).stdout.decode('utf8')
            yield """<div class="broken"><pre>{}</pre></div>""".format(errors)
        if 'thy.lean' in entries:
            thy = open(os.path.join(path, 'thy.lean')).read()
            # trim import and open
            thy = re.search('((|(open|import) .*)\n)*((.|\n)*)', thy, flags=re.MULTILINE).group(4)
            yield highlight(thy, LeanLexer(), HtmlFormatter(cssclass="lean"))

    for f in entries:
        p = os.path.join(path, f)
        if os.path.isdir(p) and f[0].isdigit():
            if ' ' in f:
                id = '-'.join(f.split(' ')[1:]).lower()
                name = f
                if f.endswith('.'):
                    name = ' '.join(name.split(' ')[1:])[:-1]
                yield """<h{} id="{id}"><a href="#{id}" class="{}">{}</a>""".format(depth, success_class(p), name, id=id)
                if not f.endswith('.'):
                    yield """<a class="ref" href="https://doc.rust-lang.org/reference.html#{}">[ref]</a>""".format(id)
                yield """</h{}>""".format(depth)
            yield from rec(p, depth + 1)


open('index.html', 'w').write("""<html>
<head>
  <meta charset="utf-8">
  <link href="rust.css" rel="stylesheet">
  <link href="ref.css" rel="stylesheet">
  <link href="highlight.css" rel="stylesheet">
  <script src="ref.js"></script>
</head>
<body class="rustdoc">
  <h1 class="title">Electrolysis Reference</h1>
  <p>This document shows <a href="https://github.com/Kha/electrolysis">electrolysis</a>'s current coverage of the <a href="https://doc.rust-lang.org/reference.html">Rust Reference</a> by testing the translation of code examples (taken from the Reference or made up on the spot). Some sections have been added on top of the Reference to display details and edge cases.</p>

<p>A ✔ means the translated Lean code type checks, whereas a ✗ marks unimplemented language features or (very rarely) inputs crashing the transpiler or creating invalid output. A few examples also come with example Lean proofs that are also checked automatically and give greater assurance of semantics preservation.</p>

  <nav id="TOC">{}</nav>
  {}
</body>
</html>""".format(
    "\n".join(toc('.')),
    "\n".join(rec('.', 1))))
