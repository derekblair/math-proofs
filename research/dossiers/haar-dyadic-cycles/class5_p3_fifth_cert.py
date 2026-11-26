"""Generate finite Lean grid certificates; Lean verifies all generated rows."""
from pathlib import Path
from itertools import product
from functools import lru_cache

here=Path(__file__).resolve().parent
words = ['0102102120121021021201012012102121021201201012012102101021201201', '0102102120121201021021012012102121021201201012012102101201201021', '0120102102121021012012120102102121201201021012012010212102101201', '0120120210212012021021210201201212012021021021021020121201202102']

Z=(0,0,0,0)
C=(1,0,0,0)

def model(params):
    p,q,t0,t1,t2=params
    d=(-p-q)%3
    def norm(k,u,a,z):
        carry,u=divmod(u,3)
        return k,u,a%3,(z+carry*t1)%3
    def mul(x,y):
        k,u,a,z=x;l,v,b,w=y
        return norm(k+l,u+v,a+b,z+w-d*l*u)
    def inv(x):
        k,u,a,z=x
        return norm(-k,-u,-a,-z-d*k*u)
    def power(x,n):
        if n<0:return power(inv(x),-n)
        k,u,a,z=x
        return norm(n*k,n*u,n*a,n*z-d*k*u*(n*(n-1)//2))
    generators = (((1,-1,0,d),(0,1,-1,0),(0,0,1,-p)),
                  ((1,1,1,-t0-d),(0,1,1,-t2),(0,0,1,-q)))
    @lru_cache(None)
    def action(axis,x):
        k,u,a,z=x
        c1,u1,a1=generators[axis]
        return mul(mul(power(c1,k),power(u1,u)),mul(power(a1,a),norm(0,0,0,z)))
    @lru_cache(None)
    def inverse_table(axis,k):
        table={action(axis,n):n for u,a,z in product(range(3),repeat=3) if (n:=(k,u,a,z))}
        assert len(table)==27, (params,axis,k)
        return table
    def invert(axis,x):
        return inverse_table(axis,x[0])[x]
    @lru_cache(None)
    def fx(i):
        if i==0:return Z
        if i>0:return mul(invert(0,fx(i-1)),C)
        return action(0,mul(fx(i+1),inv(C)))
    def test(w):
        i=j=0;m=Z
        rows=[(0,0,*m)]
        for k,s in enumerate(w):
            if s=='1':
                if k%2:
                    i-=1;m=action(0,m)
                else:
                    i+=1;m=invert(0,m)
            if s=='2':
                if k%2:
                    j-=1;m=action(1,mul(inv(fx(i)),m))
                else:
                    j+=1;m=mul(fx(i),invert(1,m))
            rows.append((i,j,*m))
        return rows
    return test

def rep(x):
    return f'({x})' if x<0 else str(x)
def make_grid(row):
    i,j,k,u,a,z=row
    return '⟨'+','.join(map(rep,(i,j)))+',⟨'+','.join(map(rep,(k,u,a,z)))+'⟩⟩'
def controls(rows):
    if rows[0] != rows[-1] or rows[0] != (0,)*6:
        raise ValueError('bad closing endpoints')
    lows=[(0,0)]*18
    mids=[0]*54
    ls={}
    ms={}
    keys=set()
    for pos,(i,j,k,u,a,z) in enumerate(rows[:-1]):
        lo=(i%3)*3+j%3
        mi=lo*3+k%3
        if ls.setdefault((pos%2,lo),(i,j))!=(i,j) or ms.setdefault((pos%2,mi),k)!=k:
            return
        key=(pos%2,mi,u,a,z)
        if key in keys:
            return
        keys.add(key)
        lows[(pos%2)*9+lo]=(i,j)
        mids[(pos%2)*27+mi]=k
    return lows,mids
exceptions={(1,2,2,2,2),(2,1,1,1,1)}
pair_names=[]
for p,q in product(range(3),repeat=2):
    if (p,q)==(0,0): continue
    name=f'{p}{q}'
    pair_names.append(name)
    out=[]
    names=[]
    for t0,t1,t2 in product(range(3),repeat=3):
        param=(p,q,t0,t1,t2)
        ix=f'{t0}{t1}{t2}'
        st=model(param)
        result=next(((j,r,d) for j,w in enumerate(words) if (d:=controls(r:=st(w))) is not None),None)
        if result is None:
            assert param in exceptions,param
            names.append('default')
            continue
        j,r,(lows,mids)=result
        assert param not in exceptions
        names.append(f'c{name}{ix}')
        rows=',\n  '.join(', '.join(make_grid(t) for t in r[i:i+5]) for i in range(0,65,5))
        low=','.join(f'({rep(i)},{rep(j)})' for i,j in lows)
        mid=','.join(map(rep,mids))
        ptxt=','.join(map(str,param))
        out.append(f'''def c{name}{ix} : Cert := ⟨{j},#[\n  {rows}],#[{low}],#[{mid}]⟩
private theorem ok{name}{ix} : Valid ⟨{ptxt}⟩ c{name}{ix} := by decide +kernel
''')
    matrix=', '.join(names)
    ex=[e for e in exceptions if e[:2]==(p,q)]
    req=''.join(f'\n    (he : ¬ (a.val={t0} ∧ b.val={t1} ∧ c.val={t2}))' for _,_,t0,t1,t2 in ex)
    cases='\n'.join(f'  · exact ok{name}{a}{b}{c}' if (p,q,a,b,c) not in exceptions else '  · exact False.elim (he (by decide))' for a,b,c in product(range(3),repeat=3))
    (here/f'HaarP3FifthCert{name}.lean').write_text(f'''import HaarP3FifthCertCore
namespace HaarP3FifthCert
set_option maxHeartbeats 0
set_option maxRecDepth 14000
'''+''.join(out)+f'''
def data{name} (a b c : Fin 3) : Cert :=
  (#[{matrix}] : Array Cert)[a.val*9+b.val*3+c.val]!
theorem correct{name} (a b c : Fin 3){req} :
    Valid ⟨{p},{q},a.val,b.val,c.val⟩ (data{name} a b c) := by
  fin_cases a <;> fin_cases b <;> fin_cases c
{cases}
end HaarP3FifthCert
''')
imports=''.join(f'import HaarP3FifthCert{j}\n' for j in pair_names)
cs=[]
for p,q in product(range(3),repeat=2):
    if (p,q)==(0,0): cs.append('  · exact False.elim (he rfl rfl)')
    elif (p,q)==(1,2):cs.append('  · exact ⟨_,correct12 a b c (fun h => h12 ⟨rfl,rfl,h⟩)⟩')
    elif (p,q)==(2,1):cs.append('  · exact ⟨_,correct21 a b c (fun h => h21 ⟨rfl,rfl,h⟩)⟩')
    else:cs.append(f'  · exact ⟨_,correct{p}{q} a b c⟩')
(here/'HaarP3FifthCertData.lean').write_text(imports+'''namespace HaarP3FifthCert
theorem coverage (p q a b c : Fin 3) (he : ¬ (p.val=0 ∧ q.val=0))
    (h12 : ¬ (p.val=1 ∧ q.val=2 ∧ a.val=2 ∧ b.val=2 ∧ c.val=2))
    (h21 : ¬ (p.val=2 ∧ q.val=1 ∧ a.val=1 ∧ b.val=1 ∧ c.val=1)) :
    ∃ C, Valid ⟨p.val,q.val,a.val,b.val,c.val⟩ C := by
  fin_cases p <;> fin_cases q
'''+ '\n'.join(cs).replace('(he rfl rfl)','(he ⟨rfl,rfl⟩)')+'\nend HaarP3FifthCert\n#print axioms HaarP3FifthCert.coverage\n')
