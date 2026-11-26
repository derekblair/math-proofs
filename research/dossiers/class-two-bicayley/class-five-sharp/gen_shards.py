from pathlib import Path
base=Path('.')
dst=base/'owner-shards';dst.mkdir(exist_ok=True)
N=16
outer=5
leaf=8
back=[1,0,2]
def word(w):return '['+','.join(map(str,w))+']'
def rootname(s,p):return 'R'+str(int(s))+''.join(map(str,p))
def nexts(w):return [i for i in range(3) if not w or i!=back[w[-1]]]
def classify(seq,k):
    if len(seq)==k:yield seq
    else:
        for j in nexts(seq): yield from classify(seq+(j,),k)
def lean_file(module,imports,body):
    dst.joinpath(module+'.lean').write_text('\n'.join([
        *('import '+i for i in imports),'','namespace Ribbon5Owner',
        'open Ribbon5Packed','set_option maxRecDepth 50000','set_option maxHeartbeats 0',
        *body,'end Ribbon5Owner','']))
def mkth(s,seq,sz):
    q=seq[0];j=seq[-1];nm=rootname(s,seq); ls=word(seq); side=str(s).lower()
    ty=f'good {side} {q} (pref {side} {ls}) {j} {N-sz} = true'
    yield f'theorem {nm} : {ty} := by'
    if sz==leaf:
        yield '  decide +kernel'
        return
    yield '  apply join'
    yield "  intro k hk"
    yield "  fin_cases k"
    for i in range(3):
       if i==back[j]:
           yield "  · exact (hk (by decide)).elim"
       else:
           nxt=rootname(s,seq+(i,))
           yield f"  · change good {side} {q} (step (pref {side} {ls}) {i}) {i} {N-sz-1} = true"
           yield f"    rw [← pref_snoc]"
           yield f"    exact {nxt}"
mods=[]
for s in (False,True):
 for seq in classify((),outer):
    mod='Ribbon5OwnerShard'+rootname(s,seq)
    body=[]
    for sz in range(leaf,outer-1,-1):
        for ss in classify(seq,sz):body+=list(mkth(s,ss,sz))
    mods.append(mod)
    lean_file(mod,['Ribbon5OwnerBase'],body)
body=[]
for s in (False,True):
    for sz in range(outer-1,0,-1):
        for ss in classify((),sz):body+=list(mkth(s,ss,sz))
body+=['theorem allgood (s : Bool) (p : P) : good s p (step (zero s) p) p 15 = true := by',
         '  cases s <;> fin_cases p',
         *('  · exact '+rootname(s,(i,)) for s in (False,True) for i in range(3))]
lean_file('Ribbon5OwnerFinished',mods,body)
Path('owner-shard-order.txt').write_text('\n'.join(mods)+'\n')
print(len(mods), 'shards')
