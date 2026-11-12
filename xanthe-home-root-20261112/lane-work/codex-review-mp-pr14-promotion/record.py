#!/usr/bin/env python3
"""Record review commands and their complete outputs without changing the repo."""
import datetime
import hashlib
import json
from pathlib import Path
import shlex
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
label, *argv = sys.argv[1:]
outdir = ROOT / 'evidence'
outdir.mkdir(exist_ok=True)
target = outdir / (label + '.json')
if target.exists():
    raise SystemExit('Refusing to overwrite evidence: ' + str(target))
started = datetime.datetime.now(datetime.timezone.utc).isoformat()
try:
    result = subprocess.run(argv, cwd=ROOT / 'repo', stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    code, stdout, stderr = result.returncode, result.stdout, result.stderr
except OSError as exc:
    code, stdout, stderr = 127, b'', str(exc).encode()
entry = dict(command=shlex.join(argv), argv=argv, cwd=str(ROOT / 'repo'),
             started_utc=started, finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
             exit_status=code, stdout=stdout.decode(errors='replace'), stderr=stderr.decode(errors='replace'),
             stdout_sha256=hashlib.sha256(stdout).hexdigest(), stderr_sha256=hashlib.sha256(stderr).hexdigest())
target.write_text(json.dumps(entry, indent=2) + '\n')
print(json.dumps(entry, indent=2))
sys.exit(code if 0 <= code < 256 else 1)
