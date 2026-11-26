from pathlib import Path
A='21200212120212020021212120200211'
B='00212121202002112120021212021202'
def rw(x):return ''.join('102'[int(j)] for j in x[::-1])
C=A+rw(B)
def fw(w,r=0):
 a=[]
 for j in w:
  if j=='2':r^=1
  else:a.append((r+1)*(1 if j=='0' else -1))
 return tuple(a)
def red(w):
 a=[]
 for v in w:
  if a and a[-1]==-v:a.pop()
  else:a.append(v)
 return tuple(a)
def inv(w):return tuple(-z for z in w[::-1])
def expr(w):return '*'.join({1:'x',-1:'x⁻¹',2:'y',-2:'y⁻¹'}[v] for v in w) or '1'
def arr(w):return '#['+','.join(w)+']'
def chart(w):
 r=x=y=z=0; out=[(r,x,y,z)]
 for j in w:
  if j=='2':r^=1
  elif r:
   d=1 if j=='0' else -1;y+=d;z+=x*d
  else:x+=1 if j=='0' else -1
  out.append((r,x,y,z))
 return out
def ct(w):
 return '#['+','.join(f'({str(bool(r)).lower()},{x},{y},{z})' for r,x,y,z in chart(w))+']'
M=[]
p=chart(C)[:-1]
for i,(r,x,y,z) in enumerate(p):
 for j,(s,u,v,t) in enumerate(p[i+1:],i+1):
  if r!=s or 0<abs(x-u)<=4 or 0<abs(y-v)<=4 or (x==u and y==v and 0<abs(z-t)<=4):continue
  M.append((i,j))
a=fw(A);p0=fw(A[:16]);p1=fw(A[16:])
assert len(a)==18
for i,j in M:
 target=red(inv(fw(C[:i]))+fw(C[:j]))
 v=target;p=()
 while v and v[0]==-v[-1]:
  p+=v[:1];v=v[1:-1]
 found=None
 for j0 in (1,-1):
  s=a if j0==1 else inv(a)
  for k in range(len(s)):
   if s[k:]+s[:k]==v:found=(red(p+inv(s[:k])),j0);break
  if found:break
 assert found,(i,j,v)
 print(i,j,found)
code='''import Ribbon5Family

namespace Ribbon6
open Ribbon5Bridge HaarUniversal36 HaarClass5Commute HaarClass4Structure HaarClass4Ports
open scoped commutatorElement
variable {G : Type*} [Group G]
'''
for name,w in [('wa',A),('wb',B),('wc',C)]:
 code+=f'def {name} : Array P := {arr(w)}\n'
for name,w in [('ta',A),('tc',C)]:
 code+=f'def {name} : Array Q := {ct(w)}\n'
code+='\nset_option maxRecDepth 16000\nset_option maxHeartbeats 1600000\n'
code+=f'''def same (i j : Nat) : Prop := {" ∨ ".join(f"(i={i} ∧ j={j})" for i,j in M)}
instance (i j : Nat) : Decidable (same i j) := by unfold same; infer_instance
theorem astep : ∀ i : Fin 32, push ta[i.val]! wa[i.val]! = ta[i.val+1]! := by decide +kernel
theorem cstep : ∀ i : Fin 64, push tc[i.val]! wc[i.val]! = tc[i.val+1]! := by decide +kernel
theorem achart : ∀ i j : Fin 32, i.val<j.val → separated ta[i.val]! ta[j.val]! := by decide +kernel
theorem cchart : ∀ i j : Fin 64, i.val<j.val → separated tc[i.val]! tc[j.val]! ∨ same i.val j.val := by decide +kernel

def U (x y : G) : G := {expr(p0)}
def V (x y : G) : G := {expr(p1)}
def residue (x y : G) : G := U x y * V x y

theorem a_end (x y : G) : pathAt x y wa 32 = (false,residue x y) := by
  norm_num [pathAt,run,start,action,wa,residue,U,V]
  group

theorem b_end (x y : G) : pathAt x y wb 32 = (false,V x y*U x y) := by
  norm_num [pathAt,run,start,action,wb,U,V]
  group

theorem c_end (x y : G) : pathAt x y wc 64 = (false,(U x y*V x y)*(V x y*U x y)⁻¹) := by
  norm_num [pathAt,run,start,action,wc,U,V]
  group

theorem explicit (x y : G) :
    residue x y = (y⁻¹ * x) * ⁅⁅x,y⁻¹⁆,x⁻¹*⁅y,x^2⁆*x⁆ * (y⁻¹*x)⁻¹ := by
  unfold residue U V commutatorElement
  rw [pow_two]
  group

end Ribbon6
'''
Path('Ribbon6Chart.lean').write_text(code)
mcode='''import Ribbon6Chart

namespace Ribbon6
open Ribbon5Bridge
variable {G : Type*} [Group G]
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000
'''
for i,j in M:
 target=red(inv(fw(C[:i]))+fw(C[:j]));v=target;p=()
 while v and v[0]==-v[-1]:
  p+=v[:1];v=v[1:-1]
 found=next((red(p+inv(s[:k])),sg) for sg in (1,-1) for s in (a if sg==1 else inv(a),) for k in range(len(s)) if s[k:]+s[:k]==v)
 con,sg=found; r='residue x y' if sg==1 else '(residue x y)⁻¹'
 invend='  apply inv_eq_one.mp\n' if sg==-1 else ''
 mcode+=f'''
theorem mate_{i} (x y : G) (nz : residue x y ≠ 1) :
    pathAt x y wc {i} ≠ pathAt x y wc {j} := by
  let k : G := {expr(con)}
  have e : (pathAt x y wc {i}).2⁻¹ * (pathAt x y wc {j}).2 = k*({r})*k⁻¹ := by
    norm_num [pathAt,run,start,action,wc,residue,U,V,k] <;> group
  intro h
  have e' : k*({r})*k⁻¹=1 := by
    rw [← e, congrArg Prod.snd h, inv_mul_cancel]
  apply nz
{invend}  have h' := congrArg (fun g => k⁻¹*g*k) e'
  simp only [← mul_assoc, inv_mul_cancel, one_mul, mul_inv_cancel, mul_one] at h' ⊢
  simpa only [mul_assoc, inv_mul_cancel, mul_inv_cancel, mul_one, one_mul] using h'
'''
mcode+='''theorem mate_sep (x y : G) (nz : residue x y ≠ 1) (i j : Nat) (m : same i j) :
    pathAt x y wc i ≠ pathAt x y wc j := by
  rcases m with '''+' | '.join('⟨rfl,rfl⟩' for _ in M)+'\n'+''.join(f'  · exact mate_{i} x y nz\n' for i,j in M)+'\nend Ribbon6\n'
Path('Ribbon6Mates.lean').write_text(mcode)
