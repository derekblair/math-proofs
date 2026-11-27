"""Reproducibly emit Lean data and separated kernel proof obligations."""
import json
from pathlib import Path
from check_cover_certificate import trace
nodes=json.loads(Path("cover_certificate.json").read_text())
def ls(L,f): return "["+",".join(f(a) for a in L)+"]"
def vec(L): return "!"+ls(L,str)
def expr(e): return "⟨"+str(e[0].bit_length()-1)+","+ls(e[1],str)+"⟩"
def branch(b): return "⟨"+vec(b[0])+","+str(b[1])+","+ls(b[2],expr)+"⟩"
def node(n):
    close,_=trace(n[1])
    e=n[2]
    if close>tuple(-c for c in close): e=[e[0],[-c for c in e[1]]]
    return "⟨"+ls(n[0],vec)+","+ls(n[1],str)+","+expr(e)+","+ls(n[3],branch)+"⟩"
Path("HaarK33Data.lean").write_text("""import HaarK33DAG
namespace HaarK33Data
open HaarK33DAG
set_option maxRecDepth 9000
def payload : Array Node := #[
""" + ",\n".join(map(node,nodes)) + "\n]\ndef D (i : Nat) : Node := payload[i]!\nend HaarK33Data\n")
prefix=["import HaarK33Data","namespace HaarK33Data","open HaarK33DAG HaarK33Voltage","set_option maxRecDepth 24000","set_option maxHeartbeats 0"]
def chain(top,l,r,indent):
    sp=' ' * indent
    if l+1==r:
        return [f'{sp}have e : i = {l} := by omega',f'{sp}subst i',f'{sp}exact {top}{l}']
    m=(l+r)//2
    left=chain(top,l,m,indent+2);right=chain(top,m,r,indent+2)
    return [f'{sp}by_cases h{l}_{r} : i < {m}',
        sp+'· '+left[0].lstrip(),*left[1:],
        sp+'· '+right[0].lstrip(),*right[1:]]
def chunks_chain(names,l,r,indent):
    sp=' ' * indent
    if l+1==r:return [f'{sp}exact {names[l][0]}valid i (by omega) (by omega)']
    m=(l+r)//2
    left=chunks_chain(names,l,m,indent+2);right=chunks_chain(names,m,r,indent+2)
    return [f'{sp}by_cases h{l}_{r} : i < {names[m][1]}',
        sp+'· '+left[0].lstrip(),*left[1:],
        sp+'· '+right[0].lstrip(),*right[1:]]
names=[]
for l in range(0,len(nodes),16):
    nm=f"C{l:03}"
    r=min(l+16,len(nodes)); names.append((nm,l))
    src=prefix + [f"private theorem ok{i} : valid D {i} := by decide +kernel" for i in range(l,r)]
    src += [f"theorem {nm}valid (i : Nat) (_lo : {l} ≤ i) (_hi : i < {r}) : valid D i := by"]
    src+=chain('ok',l,r,2)+["end HaarK33Data"]
    Path(f"HaarK33{nm}.lean").write_text("\n".join(src)+"\n")
s=[f"import HaarK33{n}" for n,_ in names]+prefix[1:]
s+=[f"theorem complete (i : Nat) (_hi : i ≤ {len(nodes)-1}) : valid D i := by"]
s+=chunks_chain(names,0,len(names),2)
s += [f"theorem root_empty : (D {len(nodes)-1}).rels = [] := by decide +kernel",
"variable {A : Type*} [AddCommGroup A]",
"theorem any_voltage (φ : V →+ A) (noTwo : ∀ a : A, a+a=0 → a=0) :",
"    ∃ n, n ∈ [4,8,16,32] ∧ HasCycle φ n :=",
f"  dag_sound φ noTwo D {len(nodes)-1} complete root_empty",
"end HaarK33Data","#print axioms HaarK33Data.any_voltage"]
Path("HaarK33Complete.lean").write_text("\n".join(s)+"\n")
print(*(f"HaarK33{n}" for n,_ in names))
