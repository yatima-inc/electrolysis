#! /bin/python3

import os
import re
import subprocess

import markdown
from pygments import highlight
from pygments.lexers import RustLexer, LeanLexer
from pygments.formatters import HtmlFormatter

def success(path):
    ok = False
    fail = False
    for f in os.listdir(path):
        p = os.path.join(path, f)
        if f == 'lib.rs':
            lib = open(p).read()
            if 'FIXME' in lib:
                return False  # wrong if there are passing sub items
        if f == 'generated.lean':
            gen = open(p).read()
            if ('unimplemented' in gen or 'compiler error' in gen)\
               and not path.endswith('-'):
                fail = True
            else:
                ok = True
        if os.path.isdir(p):
            s = success(p)
            if s != True:
                fail = True
            if s != False:
                ok = True
    if ok and fail or not ok and not fail:
        return None
    return ok

def toc(path):
    entries = sorted(os.listdir(path))

    yield "<ul>"
    for f in entries:
        p = os.path.join(path, f)
        if os.path.isdir(p) and f[0].isdigit():
            if ' ' in f:
                anchor = '-'.join(f.split(' ')[1:]).lower()
                s = success(p)
                name = f
                if f.endswith('.'):
                    name = ' '.join(name.split(' ')[1:])[:-1]
                yield """<li><a class="{}" href="#{}">{}</a>""".format(
                    "success" if s else "fail" if s == False else "",
                    anchor, name)
                yield from toc(p)
                yield "</li>"
    yield "</ul>"
    return success

def rec(path, depth):
    entries = sorted(os.listdir(path))
    if 'pre.md' in entries:
        yield markdown.markdown(open(os.path.join(path, 'pre.md')).read())
    if 'lib.rs' in entries:
        rust = os.path.join(path, 'lib.rs')
        mir = subprocess.run(['rustc', '--crate-type', 'lib', '-Z', 'unstable-options', '--unpretty', 'mir', rust],
                             stdout=subprocess.PIPE, check=True).stdout.decode('utf8')
        lean = open(os.path.join(path, 'generated.lean')).read()
        if '5 Crates' not in path:
            lean = re.search('namespace test(.*)end test', lean, flags=re.DOTALL).group(1)
        yield """<div>
  <label><input type="checkbox" onchange="toggle_mir(this)">Show MIR</label>
  <div class="code-pair">{}{}{}</div>
</div>""".format(
    highlight(open(rust).read(), RustLexer(), HtmlFormatter(cssclass="rust")),
    highlight(mir, RustLexer(), HtmlFormatter(cssclass="mir")),
    highlight(lean, LeanLexer(), HtmlFormatter(cssclass="lean")))

    for f in entries:
        p = os.path.join(path, f)
        if os.path.isdir(p) and f[0].isdigit():
            if ' ' in f:
                id = '-'.join(f.split(' ')[1:]).lower()
                name = f
                if f.endswith('.'):
                    name = ' '.join(name.split(' ')[1:])[:-1]
                yield """<h{} id={id}><a href="#{id}">{}</a>""".format(depth, name, id=id)
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
  <nav id="TOC">{}</nav>
  {}
</body>
</html>""".format(
    "\n".join(toc('.')),
    "\n".join(rec('.', 1))))
