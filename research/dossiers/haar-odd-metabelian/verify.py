#!/usr/bin/env python3
"""Clean replay of the final theorem against a pinned, cache-populated Mathlib checkout."""
import argparse, concurrent.futures as cf, hashlib, os, re, subprocess, tempfile
from pathlib import Path
here = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('mathlib', type=Path)
parser.add_argument('-j', '--jobs', type=int, default=2)
args = parser.parse_args()
mathlib = args.mathlib.resolve()
def shell(*a, **kw):
    return subprocess.check_output(a, cwd=mathlib, text=True, **kw).strip()
assert shell('git','rev-parse','HEAD') == 'd13f23b723b8a846827a245b89c10fc7d3f11612'
v = shell('lake', 'env', 'lean', '--version')
print(v, flush=True)
assert 'version 4.34.1' in v
src = {}
for line in (here/'sha256-lean.txt').read_text().splitlines():
    h,n = line.split()
    f = here/n
    b = f.read_bytes()
    if hashlib.sha256(b).hexdigest() != h:
        raise RuntimeError(f'source hash mismatch: {n}')
    src[f.stem] = (f,b.decode())
deps = {k:{x for line in data.splitlines() if line.startswith(('import ','public import '))
               for x in line.split('import ',1)[1].split('--',1)[0].split() if x in src}
        for k,(_,data) in src.items()}
targets = {'HaarMetaFullOddEnd': 2, 'HaarSharpOptimal': 3, 'HaarSharpAffine': 3}
with tempfile.TemporaryDirectory(prefix='haar-meta-verify-') as tmp:
    dest = Path(tmp)
    env = dict(os.environ, LEAN_PATH=tmp)
    def check(k):
        f, _ = src[k]
        p = subprocess.run(('lake','env','lean',f'--root={here}','-o',str(dest/f'{k}.olean'),str(f)),
                           cwd=mathlib, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        if p.returncode or re.search(r'sorryAx|uses .sorry.', p.stdout):
            raise RuntimeError(f'{k}\n{p.stdout}')
        return p.stdout
    pending = set(deps)
    ready = set()
    running = {}
    with cf.ThreadPoolExecutor(max_workers=max(1,args.jobs)) as pool:
        while pending or running:
            for k in sorted(pending):
                if len(running) >= args.jobs: break
                if deps[k] <= ready:
                    pending.remove(k)
                    running[pool.submit(check,k)] = k
            if not running:
                raise RuntimeError(f'dependency cycle: {sorted(pending)}')
            done,_ = cf.wait(running,return_when=cf.FIRST_COMPLETED)
            for f in done:
                k = running.pop(f)
                log = f.result()
                print(f'checked {k}', flush=True)
                if k in targets:
                    axioms = re.findall(r'depends on axioms: \[([^\]]+)\]',log)
                    if len(axioms) != targets[k] or any(set(x.split(', ')) - {'propext','Classical.choice','Quot.sound'} for x in axioms):
                        raise RuntimeError(log)
                    print(log, flush=True)
                ready.add(k)
    assert targets.keys() <= ready
    print(f'cleanly checked {len(ready)} modules', flush=True)
