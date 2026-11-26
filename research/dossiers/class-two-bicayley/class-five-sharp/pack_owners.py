#!/usr/bin/env python3
"""Exact two-level packed owner certificates; no hash assumption in Lean soundness."""
from pathlib import Path
import json
M=(1<<64)-1
B=1<<15
S=1<<17
N=B-1
Q=S-1
CC=8192
def mix(k,s):
    h=(k+s)&M
    h=((h^(h>>30))*13787848793156543929)&M
    h=((h^(h>>27))*10723151780598845931)&M
    return h^(h>>31)
def build(src,salt):
    buckets=[{} for _ in range(B)]
    for k,g in src:
        h=mix(k,salt)
        i,j=h&N,(h>>15)&Q
        cand=buckets[i].setdefault(j,g)
        if cand!=g:return
    d=[0]*B; owner=[3]*S
    tasks=sorted(range(B),key=lambda i:len(buckets[i]),reverse=True)
    for i in tasks:
        if not buckets[i]:break
        for off in range(S):
            if all(owner[(j+off)&Q] in (g,3) for j,g in buckets[i].items()):break
        else:return
        d[i]=off
        for j,g in buckets[i].items():owner[(j+off)&Q]=g
    return d,owner
def packs(seq,bits):
    # little endian element order; output bounded chunks for kernel arithmetic.
    k=CC//bits
    return k,[hex(sum(x<<(bits*j) for j,x in enumerate(seq[i:i+k]))) for i in range(0,len(seq),k)]
def main():
    record=[]
    for s in (0,1):
        data=[tuple(map(int,l.split())) for l in Path(f'owner-keys{s}').read_text().splitlines()]
        assert len(data)==98304 and len({k for k,g in data})==98304
        for salt in range(1,1024):
            model=build(data,salt)
            if model:break
        else:raise RuntimeError('no placement')
        d,tab=model
        for k,g in data:
            h=mix(k,salt);assert tab[((h>>15)+d[h&N])&Q]==g
        bits=max(d).bit_length()
        # take byte-length divisible chunks: choose power-of-two element count.
        dbits=max(4,((bits+3)//4)*4)
        dd,dp=packs(d,dbits); td,tp=packs(tab,2)
        record.append(dict(salt=salt,dbits=dbits,dbatch=dd,tbatch=td,offset=dp,owners=tp))
        print(s,'salt',salt,'max offset',max(d),'offset chunks',len(dp),'owner chunks',len(tp))
    Path('packed-owners.json').write_text(json.dumps(record,separators=(',',':')))
if __name__=='__main__':main()
