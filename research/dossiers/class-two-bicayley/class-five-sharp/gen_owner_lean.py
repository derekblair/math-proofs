from pathlib import Path
import json
records=json.loads(Path('packed-owners.json').read_text())
parts=['''import Mathlib.Tactic

namespace Ribbon5Owner

private def mix (k salt : ℕ) : ℕ :=
  let h := (k+salt) &&& 18446744073709551615
  let h := ((h ^^^ (h >>> 30))*13787848793156543929) &&& 18446744073709551615
  let h := ((h ^^^ (h >>> 27))*10723151780598845931) &&& 18446744073709551615
  h ^^^ (h >>> 31)
''']
for j,d in enumerate(records):
    for key in ('offset','owners'):
        parts += [f'private def {key}{j} : ℕ → ℕ', *[f'  | {i} => {v}' for i,v in enumerate(d[key])], '  | _ => 0\n']
    parts.append(f'''private def lookup{j} (k : ℕ) : ℕ :=
  let h := mix k {d['salt']}
  let b := h &&& 32767
  let off := (offset{j} (b/{d['dbatch']}) >>> ({d['dbits']}*(b%{d['dbatch']}))) &&& {(1<<d['dbits'])-1}
  let j := ((h >>> 15)+off) &&& 131071
  (owners{j} (j/{d['tbatch']}) >>> (2*(j%{d['tbatch']}))) &&& 3
''')
parts.append('''/-- Candidate port owner. Soundness never assumes this hash
is injective: the designated owner of every endpoint is checked. -/
def owner (rootSide : Bool) (key : ℕ) : ℕ :=
  if rootSide then lookup1 key else lookup0 key
''')
for j in (0,1):
    data=Path(f'owner-keys{j}').read_text().splitlines()
    for i in (0,32768,65536):
        k,g=map(int,data[i].split())
        parts.append(f'example : owner {str(bool(j)).lower()} {k} = {g} := by decide +kernel')
parts += ['\nend Ribbon5Owner\n']
Path('Ribbon5OwnerData.lean').write_text('\n'.join(parts))
