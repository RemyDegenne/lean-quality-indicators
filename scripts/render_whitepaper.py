"""Render the whitepaper Markdown to a two-page PDF using XeLaTeX."""
import argparse
import subprocess
import tempfile

from pathlib import Path
from markdown_it import MarkdownIt

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('source', type=Path)
parser.add_argument('output', type=Path)
args = parser.parse_args()
source = args.source
tokens=MarkdownIt('commonmark').enable('table').parse(source.read_text())
escapes={'\\':r'\textbackslash{}','&':r'\&','%':r'\%','$':r'\$','#':r'\#','_':r'\_','{':r'\{','}':r'\}','~':r'\textasciitilde{}','^':r'\textasciicircum{}'}
def escape(text):
    return ''.join(escapes.get(c,c) for c in text)
def inline(token):
    result=[]
    for t in token.children or []:
        if t.type=='text': result.append(escape(t.content))
        elif t.type=='strong_open': result.append(r'\textbf{')
        elif t.type=='strong_close': result.append('}')
        elif t.type=='em_open': result.append(r'\emph{')
        elif t.type=='em_close': result.append('}')
        elif t.type=='link_open': result.append(r'\href{'+t.attrGet('href')+'}{')
        elif t.type=='link_close': result.append('}')
        elif t.type=='code_inline': result.append(r'\texttt{'+escape(t.content)+'}')
        elif t.type in ('softbreak','hardbreak'): result.append(' ')
        else: raise ValueError(t.type)
    return ''.join(result)
body=[]
i=0
while i<len(tokens):
    t=tokens[i]
    if t.type=='heading_open':
        heading=tokens[i+1]
        if t.tag=='h1':
            body.append(r'{\fontsize{19}{22}\selectfont\bfseries\color{ink} '+inline(heading)+r'\par}\vspace{4pt}')
        else:
            if heading.content.startswith('2.'):
                body.append(r'\newpage')
            body.append(r'\subsection*{'+inline(heading)+'}')
        i+=3
    elif t.type=='paragraph_open':
        body.append(inline(tokens[i+1])+r'\par')
        i+=3
    elif t.type=='table_open':
        j=i+1; rows=[]; current=[]; header=False
        while tokens[j].type!='table_close':
            z=tokens[j]
            if z.type=='tr_open': current=[]
            elif z.type in ('th_open','td_open'):
                value=inline(tokens[j+1])
                current.append(r'\textbf{'+value+'}' if z.type=='th_open' else value)
            elif z.type=='tr_close': rows.append(' & '.join(current)+r' \\')
            j+=1
        columns = len(rows[0].split(' & '))
        alignment = 'l' + 'r' * (columns - 1)
        body.append(r'\begin{center}\small\renewcommand{\arraystretch}{1.12}\begin{tabular*}{\textwidth}{@{\extracolsep{\fill}}' + alignment + r'@{}}\toprule')
        body.append(rows[0]+r' \midrule')
        body.extend(rows[1:])
        body.append(r'\bottomrule\end{tabular*}\end{center}')
        i=j+1
    else: raise ValueError(t.type)

preamble=r'''\documentclass[11pt,a4paper]{article}
\usepackage[margin=18mm,top=17mm,bottom=18mm]{geometry}
\usepackage{fontspec}
\setmainfont{texgyrepagella-regular.otf}[BoldFont=texgyrepagella-bold.otf,ItalicFont=texgyrepagella-italic.otf,BoldItalicFont=texgyrepagella-bolditalic.otf]
\usepackage{microtype,booktabs,xcolor,fancyhdr}
\definecolor{ink}{HTML}{20364D}
\usepackage[unicode,colorlinks=true,urlcolor=ink,linkcolor=ink]{hyperref}
\hypersetup{pdftitle={Auditing formalization quality in Lean libraries},pdfsubject={Draft; results snapshot 27 October 2026}}
\setlength{\parindent}{0pt}
\setlength{\parskip}{5pt}
\setlength{\emergencystretch}{1em}
\pagestyle{fancy}
\fancyhf{}
\renewcommand{\headrulewidth}{0pt}
\fancyfoot[L]{\footnotesize\color{gray}Draft · 27 October 2026}
\fancyfoot[R]{\footnotesize\color{gray}\thepage}
\makeatletter
\renewcommand\subsection{\@startsection{subsection}{2}{0pt}{9pt}{4pt}{\normalfont\fontsize{12}{15}\selectfont\bfseries\color{ink}}}
\makeatother
\widowpenalty=10000
\clubpenalty=10000
\raggedbottom
\begin{document}
\fontsize{10.5}{13.1}\selectfont
'''
with tempfile.TemporaryDirectory(prefix='lean-quality-whitepaper-') as temporary:
    directory = Path(temporary)
    tex = directory / 'whitepaper.tex'
    tex.write_text(preamble+'\n'.join(body)+'\n\\end{document}\n')
    for _ in range(2):
        result = subprocess.run(['xelatex', '-interaction=nonstopmode', '-halt-on-error',
                                 '-output-directory='+str(directory), str(tex)], capture_output=True, text=True)
        if result.returncode:
            raise RuntimeError(result.stdout[-4000:])
    pdf = directory / 'whitepaper.pdf'
    info = subprocess.check_output(['pdfinfo', str(pdf)], text=True)
    pages = next(int(line.split(':', 1)[1]) for line in info.splitlines() if line.startswith('Pages:'))
    if pages != 2:
        raise ValueError(f'Expected two pages; got {pages}')
    args.output.write_bytes(pdf.read_bytes())
    print(f'Rendered {pages} pages to {args.output}')
