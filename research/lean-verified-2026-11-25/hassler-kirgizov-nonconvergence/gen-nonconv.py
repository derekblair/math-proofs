from itertools import product
def p(x):
  return [1+sum(y<z for y in x) for z in x]
rows=[]
for lane,S in enumerate((((2,3,1),(3,1,2)),((2,3,1),(3,2,1)))):
    for lead in range(3):
        rem=(9-lead)%3
        L=sorted({tuple(p(m[-lead:])) for m in S}) if lead else [()]
        R=sorted({tuple(p(m[:rem])) for m in S}) if rem else [()]
        for a in product(L,*([S]*((9-lead)//3)),R):
            w=[]
            for block in a:w.extend([len(w)+v for v in block])
            if lane:w=[10-v for v in w]
            def key(a):return sum(1<<j for j,(x,y) in enumerate((i,j) for i in range(8) for j in range(i+1,8)) if a[x]>a[y])
            rows.append((w,lane,(-lead)%3,key(w[:8]),key(w[1:])))
assert len(rows)==44 and len({tuple(w) for w,*_ in rows})==44
with open('NonconvData.lean','w') as f:
 f.write('''import Mathlib.Tactic

namespace Nonconv

structure Row where
  word : List Nat
  lane : Nat
  phase : Nat
  prefixKey : Nat
  suffixKey : Nat
  deriving Inhabited

def tbl : Array Row := #[
''')
 f.write(',\n'.join(f'  ⟨{w}, {L}, {o}, {pre}, {suf}⟩' for w,L,o,pre,suf in rows))
 f.write(''']
def row (k : Fin 44) : Row := tbl[k.val]!
def word (k : Fin 44) (i : Nat) : Nat := (row k).word[i]!

def invKey (w : Nat → Nat) (d : Nat) : Nat :=
  (((List.range 8).flatMap fun i => ((List.range 8).filter (i < ·)).map fun j =>
      decide (w (d+i) > w (d+j))).zipIdx).foldl (fun a (v,k) => a + (if v then 2^k else 0)) 0

set_option maxHeartbeats 8000000 in
theorem exactKeys : ∀ k : Fin 44,
  invKey (word k) 0 = (row k).prefixKey ∧ invKey (word k) 1 = (row k).suffixKey := by decide

set_option maxHeartbeats 8000000 in
theorem overlapTags : ∀ u v : Fin 44,
  (row u).suffixKey = (row v).prefixKey →
  (row u).lane = (row v).lane ∧ ((row u).phase + 1) % 3 = (row v).phase := by decide

theorem labelBounds : ∀ u : Fin 44, (row u).lane < 2 ∧ (row u).phase < 3 := by decide
#print axioms overlapTags
end Nonconv
''')
