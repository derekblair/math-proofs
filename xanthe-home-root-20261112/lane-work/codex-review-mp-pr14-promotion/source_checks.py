#!/usr/bin/env python3
import collections
import hashlib
import json
from pathlib import Path
import re
import subprocess

BASE = '0b17820a79f969c883b363de670402512b47341d'
AUDIT = 'c9d3c0ebb6474c5b134b2c85cae36ff84cd2af43'
HEAD = '344e3352e2f1106846e1ec3cbef0b04bff99e187'
MODULE = 'Mathproofs/ESSubfamilyExtended.lean'
TOKENS = ['sorry', 'admit', 'sorryAx', 'axiom', 'native_decide', 'ofReduceBool', 'implemented_by', 'unsafe']

def git(*args):
    command = ['git', *args]
    run = subprocess.run(command, capture_output=True)
    print('COMMAND:', json.dumps(command), 'EXIT:', run.returncode)
    if run.stderr:
        print('STDERR:', run.stderr.decode())
    run.check_returncode()
    return run.stdout

def strip(text):
    """Blank nested Lean block/line comments and escaped strings, retaining positions."""
    out = list(text)
    index, depth, string, line = 0, 0, False, False
    def blank(pos):
        if out[pos] != '\n':
            out[pos] = ' '
    while index < len(text):
        pair = text[index:index+2]
        if depth:
            if pair == '/-':
                blank(index); blank(index+1); depth += 1; index += 2
            elif pair == '-/':
                blank(index); blank(index+1); depth -= 1; index += 2
            else:
                blank(index); index += 1
        elif line:
            if text[index] == '\n':
                line = False
            blank(index); index += 1
        elif string:
            if text[index] == '\\' and index + 1 < len(text):
                blank(index); blank(index+1); index += 2
            else:
                if text[index] == '"':
                    string = False
                blank(index); index += 1
        elif pair == '/-':
            blank(index); blank(index+1); depth = 1; index += 2
        elif pair == '--':
            blank(index); blank(index+1); line = True; index += 2
        elif text[index] == '"':
            blank(index); string = True; index += 1
        else:
            index += 1
    result = ''.join(out)
    assert len(text) == len(result)
    assert [i for i,c in enumerate(text) if c == '\n'] == [i for i,c in enumerate(result) if c == '\n']
    return result

def scan(label, text):
    stripped = strip(text)
    found = {token: [] for token in TOKENS}
    for line_no, line in enumerate(stripped.splitlines(), 1):
        for token in TOKENS:
            if re.search(r'\b' + re.escape(token) + r'\b', line):
                found[token].append({'line':line_no, 'text':line.strip(), 'count':len(re.findall(r'\b' + re.escape(token) + r'\b', line))})
    print(json.dumps({'file':label, 'counts':{t:sum(item['count'] for item in found[t]) for t in TOKENS}, 'matches':{t:m for t,m in found.items() if m}}, ensure_ascii=False))

sources = {}
for revision in [AUDIT, BASE, HEAD]:
    source = git('show', revision + ':' + MODULE)
    sources[revision] = source
    print(json.dumps({'revision':revision, 'file':MODULE, 'bytes':len(source), 'sha256':hashlib.sha256(source).hexdigest()}))
print('BYTE_IDENTICAL_ALL_THREE:', len(set(sources.values())) == 1)

# Blank context and removed lines; retain the added lines at their actual HEAD line positions.
diff = git('diff', '--no-ext-diff', '--unified=0', BASE, HEAD).decode()
additions = {}
current = None
line_no = 0
for line in diff.splitlines():
    if line.startswith('+++ b/'):
        current = line[6:]
        additions[current] = {}
    elif line.startswith('@@'):
        line_no = int(re.search(r'\+(\d+)', line).group(1))
    elif line.startswith('+') and current:
        additions[current][line_no] = line[1:]
        line_no += 1
    elif line.startswith(' '):
        line_no += 1
for filename, lines in additions.items():
    reconstructed = '\n'.join(lines.get(n, '') for n in range(1, max(lines) + 1))
    scan(filename + ' (added diff lines only)', reconstructed)
for revision, source in sources.items():
    scan(revision + ':' + MODULE, source.decode())
