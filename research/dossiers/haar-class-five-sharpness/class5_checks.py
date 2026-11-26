"""Generate small independent Lean kernel proof obligations from the certificate dimensions."""
from pathlib import Path
import sys
import os
s,t=map(int,sys.argv[1:3])
q=3*2**(s-1)
p=int(os.environ.get("HAAR_CERT_FIELD","17"))
tag=f'S{s}T{t}' if p==17 else f'F{p}S{s}T{t}'
stem='HaarOwner'+tag
mat='HaarMatrix' if p==17 else f'HaarMatrix{p}'
def pred():
    core = f'HaarOwnerCertificate.checkShard owner{tag}' if p==17 else f'HaarOwnerEncoded.check rawOwner{tag} {2**t}'
    return f'{core} s 0 (shards {s} {t})[s]! = true'
def body(l,r,ind,small=False):
    if r==l+1:
        return [f'{ind}have hs : s = {l} := by omega', f'{ind}subst s',f'{ind}exact checked_{l}']
    m=(l+r)//2 if small else (((l+r)//16)*8)
    if m%8 or m<=l or m>=r:m=((l+r)//2//8)*8
    if small:m=(l+r)//2
    if not small and (r-l<=8 or not l<m<r):
        return [f'{ind}exact group_{tag}_{l} s (by omega) (by omega)']
    return [f'{ind}by_cases h{l}_{r} : s < {m}',ind+'· '+body(l,m,ind+'  ',small)[0].lstrip(),
            *body(l,m,ind+'  ',small)[1:], ind+'· '+body(m,r,ind+'  ',small)[0].lstrip(),*body(m,r,ind+'  ',small)[1:]]
def pre(imports):
    return imports + ['namespace HaarOwnerPayload',
                      f'open {mat}Shards',
                      'set_option maxRecDepth 40000', 'set_option maxHeartbeats 0']
base = [f'import {stem}Eval', 'import HaarOwnerBind', f'import {mat}Shards']
if p!=17:
    raw = f'{stem}Raw'
    Path(raw+'.lean').write_text(f'import {stem}Eval\nnamespace HaarOwnerPayload\ndef rawOwner{tag} (k : Nat) : Nat := slots{tag} (slot{tag} k)\nend HaarOwnerPayload\n')
    base += [f'import {raw}', 'import HaarOwnerEncoded']
if 'probe' in sys.argv:
    st=pre(base)
    for j in [0,q//2,q-1]:
        st += [f'theorem probe{j} : '+pred().replace(' s ',f' {j} ').replace('[s]',f'[{j}]')+' := by decide +kernel',
               f'#print axioms probe{j}']
    Path(stem+'Probe.lean').write_text('\n'.join(st+['end HaarOwnerPayload'])+'\n')
    sys.exit()
parts=[]
for a in range(0,q,8):
    r=min(a+8,q)
    st=pre(base)
    for j in range(a,r):
        st += [f'private theorem checked_{j} : '+pred().replace(' s ',f' {j} ').replace('[s]',f'[{j}]')+' := by decide +kernel']
    st += [f'theorem group_{tag}_{a} (s : Nat) (_lo : {a} ≤ s) (_hi : s < {r}) : '+pred()+' := by',
           *body(a,r,'  ',True),'end HaarOwnerPayload']
    name=f'{stem}Part{a:03}'
    Path(name+'.lean').write_text('\n'.join(st)+'\n')
    parts.append(name)
st=pre([f'import {b}' for b in parts]+[f'import {mat}NoShort'])
tailProof = f'HaarOwnerBind.certify _ owner{tag}' if p==17 else f'HaarOwnerEncoded.certify _ rawOwner{tag} {2**t}'
st += [f'private theorem all_checked (s : Nat) (h : s < {q}) : '+pred()+' := by',
    *body(0,q,'  '),
    f'private theorem count : (shards {s} {t}).length = {q} := by decide +kernel',
    f'theorem exact_nodup_{tag} : ({mat}Packed.words {mat}Packed.zero true 3 {s+t}).Nodup := by',
    f'  rw [← {mat}Shards.exact_shards {s} {t}]',
    f'  exact {tailProof} (fun s hs => all_checked s (by simpa only [count] using hs))',
    'end HaarOwnerPayload',
    f'#print axioms HaarOwnerPayload.exact_nodup_{tag}']
Path(stem+'Complete.lean').write_text('\n'.join(st)+'\n')
print(' '.join(parts),stem+'Complete')
