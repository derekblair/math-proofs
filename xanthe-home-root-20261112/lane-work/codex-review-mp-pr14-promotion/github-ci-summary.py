#!/usr/bin/env python3
import json
from pathlib import Path
E = Path(__file__).resolve().parent / 'evidence'
names = ['admission_criterion', 'a0_constancy', 'u_eq_Aqe_div_f', 'excess_prime_dvd_u', 'M_const', 'split_layered_repaired']
for run in ['40426034024', '40426098547', '40431654876', '40431659272']:
    r = json.loads((E / ('gh_log' + run + '.json')).read_text())
    data = json.loads(json.loads((E / ('gh_run' + run + '.json')).read_text())['stdout'])
    lines = r['stdout'].splitlines()
    extracted = []
    for i, line in enumerate(lines):
        if ('git log -1 --format=%H' in line or 'display=check environment with leanchecker' in line):
            extracted.extend([{'line':i+1,'text':line}, {'line':i+2,'text':lines[i+1]}])
        elif any(s in line for s in ['Lean (version', 'Build completed successfully', 'id=__leanprover_lean-action.build;outcome=', 'id=__leanprover_lean-action.axiom-audit;outcome=', 'id=__leanprover_lean-action.test;outcome=', 'id=__leanprover_lean-action.lint;outcome=']):
            extracted.append({'line':i+1,'text':line})
    print(json.dumps(dict(run=run, event=data['event'], associated_head=data['headSha'],
        status=data['status'], conclusion=data['conclusion'], github_jobs=len(data['jobs']),
        completed_at=data['jobs'][0]['completedAt'], download_exit=r['exit_status'],
        full_log='evidence/ci-'+run+'.log', full_log_bytes=len(r['stdout'].encode()), full_log_sha256=r['stdout_sha256'],
        named_ss004_output_matches={n:sum(n in l for l in lines) for n in names}, evidence=extracted), indent=2))
