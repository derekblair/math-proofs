#!/usr/bin/env python3
"""Recover raw non-UTF8 search output and verify its originally recorded digest."""
import hashlib
import json
from pathlib import Path
import subprocess
from collections import defaultdict, deque

root = Path(__file__).resolve().parent
path = root / 'evidence' / 'src_paper_search.json'
entry = json.loads(path.read_text())
run = subprocess.run(entry['argv'], cwd=entry['cwd'], capture_output=True)
digest = hashlib.sha256(run.stdout).hexdigest()
print(json.dumps({'command': entry['command'], 'exit_status': run.returncode,
                  'stdout_sha256': digest, 'original_stdout_sha256': entry['stdout_sha256'],
                  'matches_original': digest == entry['stdout_sha256']}))
assert run.returncode == entry['exit_status']
if digest != entry['stdout_sha256']:
    # rg may emit independently searched files in a different order. Reconstruct
    # the recorded line order using newly captured raw lines, then require the
    # original cryptographic digest. No guessed byte is accepted.
    lines = defaultdict(deque)
    for raw_line in run.stdout.split(b'\n'):
        lines[raw_line.decode(errors='replace')].append(raw_line)
    recovered = []
    for displayed_line in entry['stdout'].split('\n'):
        assert lines[displayed_line], 'Original displayed line not recaptured'
        recovered.append(lines[displayed_line].popleft())
    assert all(not q for q in lines.values()), 'Unexpected additional raw lines'
    raw_stdout = b'\n'.join(recovered)
else:
    raw_stdout = run.stdout
digest = hashlib.sha256(raw_stdout).hexdigest()
print(json.dumps({'reconstructed_in_recorded_line_order_sha256': digest,
                  'matches_original': digest == entry['stdout_sha256']}))
assert digest == entry['stdout_sha256'], 'Do not substitute changed bytes for original evidence'
assert raw_stdout.decode(errors='replace') == entry['stdout']
target = root / 'evidence' / 'src_paper_search.stdout.raw'
assert not target.exists()
target.write_bytes(raw_stdout)
print('Preserved raw bytes:', str(target))
