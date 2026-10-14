"""Small shared TeX scanners: balanced arguments, comments, and local inputs."""
from pathlib import Path
import re


def control_words(text):
    """Match TeX control words, consuming control symbols such as \\\\ first."""
    return (m for m in re.finditer(r'\\(?:([A-Za-z@]+)|.)', text, re.S) if m[1])


def blank(text):
    return ''.join('\n' if c == '\n' else ' ' for c in text)


def strip_comments(text):
    out = list(text)
    for match in re.finditer('%', text):
        i = match.start(); back = i - 1
        while back >= 0 and text[back] == '\\': back -= 1
        if (i - back - 1) % 2: continue
        end = text.find('\n', i)
        end = len(text) if end < 0 else end
        out[i:end] = ' ' * (end - i)
    return ''.join(out)


def balanced(text, start, opening='{', closing='}'):
    if start >= len(text) or text[start] != opening: return None
    depth = 1; i = start + 1
    while i < len(text):
        if text[i] == '\\':
            i += 2; continue
        if text[i] == opening: depth += 1
        elif text[i] == closing:
            depth -= 1
            if not depth: return start + 1, i, i + 1
        i += 1
    return None


def commands(text, names=None):
    """Return one required argument and any optional args, preserving offsets."""
    found = []
    for match in re.finditer(r'\\([A-Za-z@]+)\*?', text):
        name = match[1]
        if names is not None and name not in names: continue
        pos = match.end(); optional = []
        while pos < len(text):
            while pos < len(text) and text[pos].isspace(): pos += 1
            if pos >= len(text) or text[pos] != '[': break
            group = balanced(text, pos, '[', ']')
            if not group: break
            optional.append(text[group[0]:group[1]]); pos = group[2]
        group = balanced(text, pos)
        if group:
            found.append(dict(name=name, start=match.start(), end=group[2],
                              arg_start=group[0], arg_end=group[1],
                              argument=text[group[0]:group[1]], optional=optional))
    return found


def mask_spans(text, spans):
    out = list(text)
    for start, end in spans: out[start:end] = blank(text[start:end])
    return ''.join(out)


def source_files(paper):
    """Include draft sections/captions and resolve nested inputs; never build/."""
    paper = Path(paper).resolve()
    paths = {(paper / 'main.tex').resolve()}
    for directory in ['sections', 'appendices', 'figures', 'tables']:
        paths.update(p.resolve() for p in (paper / directory).rglob('*.tex')
                     if 'generated' not in p.relative_to(paper).parts)
    pending = list(paths)
    while pending:
        path = pending.pop()
        if not path.is_file(): raise FileNotFoundError(path)
        text = strip_comments(path.read_text())
        for command in commands(text, {'input', 'include'}):
            name = Path(command['argument'])
            if not name.suffix: name = name.with_suffix('.tex')
            candidates = [paper / name, path.parent / name]
            target = next((p.resolve() for p in candidates if p.is_file()), None)
            if target is None: raise FileNotFoundError(candidates[0])
            if not target.is_relative_to(paper): raise ValueError(f'Input outside paper: {target}')
            if target not in paths:
                paths.add(target); pending.append(target)
    return sorted(paths)


NATBIB_KEYS = {'cite', 'citet', 'citep', 'citealt', 'citealp', 'citeauthor',
               'citefullauthor', 'citeyear', 'citeyearpar', 'citenum',
               'citetalias', 'citepalias', 'Citet', 'Citep', 'Citealt',
               'Citealp', 'Citeauthor', 'nocite'}


def escaped(text, pos):
    """An odd number of preceding backslashes escapes this character."""
    start = pos - 1
    while start >= 0 and text[start] == '\\': start -= 1
    return (pos - start - 1) % 2 == 1


def mask_math(text):
    """Balanced math scanner; retain text groups and mask their nested math.

    Keep offsets/newlines. Delimiters inside balanced text groups belong to
    those groups, not the enclosing math. Malformed math is an explicit error.
    """
    out = list(text)
    env = re.compile(r'\\begin\{(equation\*?|align\*?|gather\*?|multline\*?|math|displaymath)\}')
    def erase(a,b): out[a:b] = blank(text[a:b])
    def math(start, stop, opening, closing):
        i = start + len(opening); erase(start,i); depth = 0
        while i < stop:
            if not depth and text.startswith(closing,i) and not escaped(text,i):
                erase(i,i+len(closing)); return i+len(closing)
            if text.startswith(r'\text',i) and not escaped(text,i):
                command = re.match(r'\\text\b\s*',text[i:stop])
                if command:
                    pos = i + command.end(); group = balanced(text,pos)
                    if not group or group[2] > stop: raise ValueError('Unbalanced text group in math')
                    erase(i,group[0]); erase(group[1],group[2])
                    prose_region(group[0],group[1]); i=group[2]; continue
            if not escaped(text,i):
                if text[i]=='{': depth += 1
                elif text[i]=='}': depth -= 1
            erase(i,i+1); i += 1
        raise ValueError(f'Unclosed math delimiter {opening!r}')
    def prose_region(start,stop):
        i = start
        while i < stop:
            if escaped(text,i): i += 1; continue
            if text[i]=='$':
                delimiter = '$$' if text.startswith('$$',i) else '$'
                i=math(i,stop,delimiter,delimiter); continue
            if text.startswith(r'\(',i) or text.startswith(r'\[',i):
                opening=text[i:i+2]; closing=r'\)' if opening==r'\(' else r'\]'
                i=math(i,stop,opening,closing); continue
            match=env.match(text,i)
            if match:
                i=math(i,stop,match[0],r'\end{'+match[1]+'}'); continue
            i += 1
    prose_region(0,len(text))
    return ''.join(out)


def top_level_split(text, separator=','):
    """Split TikZ options without splitting commas inside groups/brackets."""
    pieces=[]; start=0; stack=[]
    pairs={'{':'}','[':']','(':')'}
    for i,char in enumerate(text):
        if escaped(text,i): continue
        if char in pairs: stack.append(pairs[char])
        elif stack and char==stack[-1]: stack.pop()
        elif char==separator and not stack:
            pieces.append(text[start:i]); start=i+1
    if stack: raise ValueError('Unbalanced TikZ option group')
    pieces.append(text[start:]); return pieces


def macro_declarations(text):
    """Braced/unbraced command declarations; simple undelimited def arguments.

    Return source spans, bodies and argument counts. Unsupported declaration
    syntax is rejected, so it cannot bypass snapshot protection or node checks.
    """
    text=strip_comments(text); records=[]
    pattern=re.compile(r'\\(newcommand|renewcommand|providecommand|DeclareRobustCommand|def|gdef|edef|xdef)\*?\s*')
    for match in pattern.finditer(text):
        pos=match.end(); name_match=None
        if pos<len(text) and text[pos]=='{':
            group=balanced(text,pos)
            if not group: raise ValueError('Unbalanced macro name')
            name_match=re.fullmatch(r'\s*\\([A-Za-z@]+)\s*',text[group[0]:group[1]])
            pos=group[2]
        else:
            name_match=re.match(r'\\([A-Za-z@]+)',text[pos:])
            if name_match: pos += name_match.end()
        if not name_match: raise ValueError('Unsupported macro declaration name')
        name=name_match[1]; args=0; default=None
        while pos<len(text) and text[pos].isspace(): pos+=1
        if match[1] in {'def','gdef','edef','xdef'}:
            begin=pos
            while pos<len(text) and text[pos]!='{': pos+=1
            parameters=text[begin:pos].strip()
            if not re.fullmatch(r'(?:#[1-9])*',parameters): raise ValueError('Unsupported delimited macro parameters: '+name)
            args=len(parameters)//2
            if parameters!=''.join('#'+str(i) for i in range(1,args+1)):
                raise ValueError('Unsupported macro parameter order: '+name)
        elif pos<len(text) and text[pos]=='[':
            group=balanced(text,pos,'[',']')
            if not group: raise ValueError('Unbalanced argument count: '+name)
            count=text[group[0]:group[1]]
            if not re.fullmatch(r'[0-9]',count): raise ValueError('Unsupported macro argument count: '+name)
            args=int(count); pos=group[2]
            while pos<len(text) and text[pos].isspace():pos+=1
            if pos<len(text) and text[pos]=='[':
                group=balanced(text,pos,'[',']')
                if not group or not args: raise ValueError('Invalid default macro argument: '+name)
                default=text[group[0]:group[1]];pos=group[2]
        while pos<len(text) and text[pos].isspace():pos+=1
        group=balanced(text,pos)
        if not group: raise ValueError('Unsupported or unbalanced macro body: '+name)
        records.append(dict(name=name,body=text[group[0]:group[1]],args=args,default=default,
                            start=match.start(),end=group[2]))
    return records


def resolve_input(paper, source, name):
    path=Path(name)
    if not path.suffix:path=path.with_suffix('.tex')
    target=next((p.resolve() for p in [paper/path,source.parent/path] if p.is_file()),None)
    if target is None:raise FileNotFoundError(paper/path)
    if not target.is_relative_to(paper):raise ValueError('Input outside paper: '+str(target))
    return target
