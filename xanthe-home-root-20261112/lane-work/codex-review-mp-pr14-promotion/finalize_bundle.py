#!/usr/bin/env python3
"""Index and validate the preserved review evidence; no repository mutations."""
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent
records = []
for path in sorted((ROOT / 'evidence').glob('*.json')):
    entry = json.loads(path.read_text())
    if 'command' not in entry:
        continue
    for stream in ('stdout', 'stderr'):
        actual = hashlib.sha256(entry[stream].encode()).hexdigest()
        if actual != entry[stream + '_sha256']:
            raw = path.with_suffix('.' + stream + '.raw').read_bytes()
            assert raw.decode(errors='replace') == entry[stream]
            actual = hashlib.sha256(raw).hexdigest()
        assert actual == entry[stream + '_sha256'], (path, stream, actual)
    records.append((path, entry))

for run in ('40426034024', '40426098547', '40431654876', '40431659272'):
    entry = json.loads((ROOT / 'evidence' / ('gh_log' + run + '.json')).read_text())
    log = ROOT / 'evidence' / ('ci-' + run + '.log')
    assert log.read_bytes() == entry['stdout'].encode(), log

review = (ROOT / 'REVIEW.md').read_text()
assert review.rstrip().endswith('VERDICT: FAIL')
for claim in range(1, 9):
    assert re.search(r'^### ' + str(claim) + r'\..*(CONFIRMED|REFUTED|UNVERIFIED)', review, re.M), claim
for annex in 'ABCDE':
    assert re.search(r'^## Annex ' + annex + r' — (CLEAR|FOUND)', review, re.M), annex

index = [
    '# Recorded evidence command index', '',
    'All paths below are relative to this review workdir. The linked JSON records contain complete outputs, argv, cwd, UTC times, exit statuses, and output hashes.', '',
    'The recorder invokes each command from `repo/`. An exit status of 127 in the four root tool-launch attempts represents an OSError before process launch, not a Lean result.', '',
    'One broad paper search produced non-UTF8 bytes. Its JSON stdout is a replacement-decoded display; `evidence/src_paper_search.stdout.raw` preserves the raw bytes. The exact read-only command was repeated, raw lines reordered to their recorded display order (rg search order varied), and the reconstructed bytes matched the originally recorded SHA256. See `root_search_raw_recovery_ordered.json` and `recover_search_bytes.py`; the first recovery attempt is preserved as failed. All output hashes validate against UTF-8 text or that verified raw sidecar.', '',
    'The exploratory `root_repo_pins` command exited 2 because a searched `scripts/` directory does not exist. Dedicated successful pin reads supersede that search. `root_lean_source` also records that incidental directory-search stderr; no proof conclusion relies on the missing directory.', '',
    'Clone/checkout/head verification is in [setup.log](setup.log), with all three commands exit 0.', '',
]
for path, entry in records:
    rel = path.relative_to(ROOT)
    index.extend([
        '## ' + path.stem, '',
        f'Record: [{rel}]({rel}). Exit: **{entry["exit_status"]}**. UTC: `{entry["started_utc"]}`.', '',
        '```bash', entry['command'], '```', '',
        'Stdout SHA256: `' + entry['stdout_sha256'] + '`.', '',
        'Stderr SHA256: `' + entry['stderr_sha256'] + '`.', '',
    ])
(ROOT / 'EVIDENCE-INDEX.md').write_text('\n'.join(index))

result = {
    'record_count': len(records),
    'recorded_stream_hashes_valid': True,
    'four_full_ci_logs_match_recorded_stdout': True,
    'all_eight_claims_and_five_annexes_present': True,
    'report_sha256': hashlib.sha256((ROOT / 'REVIEW.md').read_bytes()).hexdigest(),
    'nonzero_command_statuses': {p.name: e['exit_status'] for p,e in records if e['exit_status']},
}
(ROOT / 'BUNDLE-CHECK.json').write_text(json.dumps(result, indent=2) + '\n')
stable_artifacts = [
    'BRIEF.md', 'REVIEW.md', 'EVIDENCE-INDEX.md', 'BUNDLE-CHECK.json',
    'setup.log', 'source-findings.md', 'github-findings.md',
    'record.py', 'source_checks.py', 'github-extract.py',
    'github-ci-summary.py', 'ss004-audit.lean',
    'recover_search_bytes.py', 'finalize_bundle.py',
]
# Harness runtime logs can continue changing while this command executes and
# are not part of the immutable evidence bundle.
paths = sorted([p for p in (ROOT / 'evidence').iterdir() if p.is_file()] +
               [ROOT / name for name in stable_artifacts])
manifest = ''.join(hashlib.sha256(p.read_bytes()).hexdigest() + '  ' + str(p.relative_to(ROOT)) + '\n' for p in paths)
(ROOT / 'EVIDENCE-SHA256SUMS').write_text(manifest)
print(json.dumps(result, indent=2))
print('Manifest file count:', len(paths))
