from math import comb
from pathlib import Path
ns={}
exec((Path(__file__).resolve().parent.parent / "lean-verified-2026-11-25" / "bks-packing-cutoff" / "independent.py").read_text().split("C=lambda",1)[0],ns)
literal,alt = ns['literal'],ns['pattern']
def peer(h):
    return [k for i in range(h) for k in (2*h+i,h-1-i,h+i)]+[3*h]
def C(j):
    return comb(2*j,j)//(j+1)
n=0
for h in range(2,13):
    p=peer(h)
    m=len(p)-3
    assert sorted(range(m),key=p.__getitem__)==sorted(range(m),key=lambda i:p[i+3])
    for j in range(1,h+5):
        assert literal(p,3,j)==C(j)
        n+=1
    assert literal(alt(h),3,h+1)==C(h+1)+C(h)
print(n, "exact original physical-window counts matched Catalan, and all difference checks passed.")
print("For h=5, partner:",[x+1 for x in peer(5)])
