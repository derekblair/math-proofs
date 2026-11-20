#!/usr/bin/env python3
"""Extract relevant lines from preserved GitHub evidence, never from prose reports."""
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent
E = ROOT / 'evidence'

def record(name):
    return json.loads((E / (name + '.json')).read_text())

for run in ['40426034024', '40426098547', '40431654876', '40431659272']:
    r = record('gh_log' + run)
    raw = r['stdout']
    (E / ('ci-' + run + '.log')).write_text(raw)
    print(f'RUN {run}: gh exit={r["exit_status"]}, bytes={len(raw.encode())}, sha256={r["stdout_sha256"]}')
    lines = raw.splitlines()
    selected = set()
    pat = r'Build completed successfully|[0-9]+/[0-9]+.*Mathproofs|lean-toolchain|Lean \(version|lake --version|lake build|git log -1|check environment with leanchecker|audit axioms|run tests|run lint|outcome=skipped|cbf4c3d4b3ed545daf22b1e00a28a68b48e8867a|344e3352e2f1106846e1ec3cbef0b04bff99e187'
    for i, line in enumerate(lines):
        if re.search(pat, line):
            selected.add(i)
            if 'git log -1' in line or 'start-action display=' in line:
                selected.update(range(i + 1, min(i + 3, len(lines))))
    for i in sorted(selected):
        print(f'{i+1}: {lines[i]}')

for number in [14, 15]:
    r = record('gh_pr' + str(number))
    data = json.loads(r['stdout'])
    text = data['body']
    for c in data['comments']:
        text += '\n\nCOMMENT ' + c['url'] + '\n' + c['body']
    (E / ('pr' + str(number) + '-readable.txt')).write_text(text + '\n')
    print(f'PR{number} body/comments:')
    for i, line in enumerate(text.splitlines(), 1):
        print(f'{i}: {line}')

r = record('gh_pr14_timeline')
timeline = json.loads(r['stdout'])
print('PR14 timeline events:')
for e in timeline:
    print(json.dumps({k:e.get(k) for k in ['event','created_at','sha','commit_id']}, sort_keys=True))
print('head_ref_force_pushed count:', sum(e.get('event') == 'head_ref_force_pushed' for e in timeline))

for name in ['gh_head_runs', 'gh_head_checks', 'gh_head_status']:
    d = json.loads(record(name)['stdout'])
    print(name + ' total_count=' + str(d['total_count']))
    for field in ['workflow_runs', 'check_runs', 'statuses']:
        for x in d.get(field, []):
            print(json.dumps({k:x.get(k) for k in ['id','head_sha','event','status','conclusion','created_at','started_at','completed_at','html_url']}, sort_keys=True))
for name in ['gh_artifacts15_push', 'gh_artifacts15_pr', 'gh_artifacts14_push', 'gh_artifacts14_pr', 'gh_pr14_reviews', 'gh_pr15_reviews']:
    r = record(name)
    print(name + ' exit=' + str(r['exit_status']) + ' output=' + r['stdout'].strip())
