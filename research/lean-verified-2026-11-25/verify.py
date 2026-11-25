#!/usr/bin/env python3
"""Clean independent verifier for the proof drops in this directory."""
import argparse
import os
from pathlib import Path
import re
import subprocess
import tempfile

PIN = 'd13f23b723b8a846827a245b89c10fc7d3f11612'
ROOT = Path(__file__).resolve().parent
NEGATIVE = {'cubic-zero-forcing-chain': ('NegativeDom.lean', 'NegativeZF.lean')}
IMPORTS = re.compile(r'^\s*(?:public\s+)?import\s+([^\n]+)', re.M)
FORBIDDEN = re.compile(r'\b(sorry|admit|sorryAx|native_decide|ofReduceBool)\b')
AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def modules(src):
    files = {f.stem: f for f in src.glob('*.lean')
             if f.name not in NEGATIVE.get(src.name, ())}
    done = set()
    running = set()

    def order(k):
        if k in running:
            raise ValueError(f'cyclic dependency in {src.name}: {k}')
        if k not in done:
            running.add(k)
            text = files[k].read_text()
            if FORBIDDEN.search(text):
                raise ValueError(f'forbidden proof token in {files[k].name}')
            for line in IMPORTS.findall(text):
                for imp in line.split('--', 1)[0].split():
                    if imp in files:
                        yield from order(imp)
            yield files[k]
            done.add(k)
            running.remove(k)

    for name in sorted(files):
        yield from order(name)


def run(command, d, env):
    proc = subprocess.run(command, cwd=d, env=env, check=False,
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    if proc.stdout:
        print(proc.stdout, end='', flush=True)
    proc.check_returncode()
    if 'uses `sorry`' in proc.stdout:
        raise ValueError('verification reported an admitted proof')
    for values in re.findall(r'depends on axioms: \[([^\]]*)\]', proc.stdout):
        extra = set(values.split(', ')) - AXIOMS - {''}
        if extra:
            raise ValueError(f'nonstandard theorem axioms: {extra}')


def main():
    p = argparse.ArgumentParser(__doc__)
    p.add_argument('mathlib', type=Path, help='built Mathlib checkout at the pinned commit')
    p.add_argument('bundle', nargs='*', help='optional bundle directories; default: all')
    a = p.parse_args()
    math = a.mathlib.resolve()
    commit = subprocess.check_output(['git', '-C', math, 'rev-parse', 'HEAD'], text=True).strip()
    if commit != PIN:
        p.error(f'expected Mathlib {PIN}, got {commit}')
    v = subprocess.check_output(['lean', '--version'], text=True)
    if 'version 4.34.1,' not in v:
        p.error('Lean 4.34.1 is required')
    bundles = a.bundle or sorted(d.name for d in ROOT.iterdir() if d.is_dir())
    num = negatives = 0
    for b in bundles:
        src = ROOT / b
        fs = list(modules(src))
        if not fs:
            p.error(f'no Lean modules at {b}')
        with tempfile.TemporaryDirectory(prefix='mathproofs-') as tmp:
            d = Path(tmp)
            env = dict(os.environ)
            deps = [math / '.lake/build/lib/lean',
                    *sorted((math / '.lake/packages').glob('*/.lake/build/lib/lean'))]
            env['LEAN_PATH'] = os.pathsep.join(map(str, [d, *deps]))
            for f in fs:
                (d / f.name).write_bytes(f.read_bytes())
                print(f'Compile {b}/{f.name}', flush=True)
                run(['lean', f'--root={d}', '-j1', '-o', f'{f.stem}.olean', f.name], d, env)
            for f in fs:
                print(f'Kernel replay {b}/{f.stem}', flush=True)
                run(['leanchecker', '-v', f.stem], d, env)
                num += 1
            for name in NEGATIVE.get(b, ()):
                (d / name).write_bytes((src / name).read_bytes())
                proc = subprocess.run(['lean', f'--root={d}', '-j1', name], cwd=d, env=env,
                                      text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
                if proc.returncode == 0 or 'error:' not in proc.stdout or 'is false' not in proc.stdout:
                    raise RuntimeError(f'unexpected negative control result for {b}/{name}: {proc.stdout}')
                print(f'Expected rejection {b}/{name}', flush=True)
                negatives += 1
    print(f'PASS: {num} source modules rebuilt and kernel-replayed in {len(bundles)} proof bundles; {negatives} negative controls rejected as expected.')


if __name__ == '__main__':
    main()
