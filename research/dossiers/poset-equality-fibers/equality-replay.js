
function pop(x){let n=0;while(x){x&=x-1;n++;}return n;}
function choose(n,k){let x=1n;for(let i=1;i<=k;i++)x=x*BigInt(n+1-i)/BigInt(i);return x;}
function relations(up){
  const n=up.length,down=Array(n).fill(0);
  for(let i=0;i<n;i++)for(let j=0;j<n;j++)if(up[i]&(1<<j))down[j]|=1<<i;
  return down;
}
function extensions(down){
  const n=down.length,res=[],ord=[];
  function rec(used){
    if(ord.length===n){res.push(ord.slice());return;}
    for(let j=0;j<n;j++)if(!(used&(1<<j))&&(down[j]&~used)===0){
      ord.push(j);rec(used|(1<<j));ord.pop();
    }
  }
  rec(0);return res;
}
function moduleCondition(A,B,up,down){
  const K=A|B;
  for(let i=0;i<up.length;i++){
    if((B&(1<<i))&&(up[i]&A))return false;
    if(K&(1<<i))continue;
    const above=up[i]&K,below=down[i]&K;
    if(above!==0&&above!==K)return false;
    if(below!==0&&below!==K)return false;
  }
  return true;
}
function corridor(A,B,up,down,more=false){
  const p=pop(A),q=pop(B),min=Array(p+q+1).fill(0);
  for(let b=0;b<up.length;b++)if(B&(1<<b)){
    for(let a=0;a<up.length;a++)if((A&(1<<a))&&(up[b]&(1<<a))){
      const l=1+pop(down[b]&B),h=p-pop(up[a]&A),k=l+h-1;
      min[k]=Math.max(min[k],l);
    }
  }
  const da=[],db=[];
  for(let i=0;i<up.length;i++){
    if(A&(1<<i))da.push(pop(down[i]&B));
    if(B&(1<<i))db.push(pop(up[i]&A));
  }
  da.sort((a,b)=>a-b);db.sort((a,b)=>b-a);
  const pref=[0];for(const a of da)pref.push(pref.at(-1)+a);
  const cap=Array.from({length:p+1},(_,i)=>{const v=[0];for(const b of db)v.push(v.at(-1)+Math.min(b,i));return v;});
  const ways=Array.from({length:p+1},()=>Array(q+1).fill(0n));
  for(let i=0;i<=p;i++)for(let j=0;j<=q;j++)if(j>=min[i+j]&&(!more||((i===0||j>=da[i-1])&&(j===q||i<=p-db[j])&&cap[i][j]>=pref[i]))){
    ways[i][j]=i+j===0?1n:(i?ways[i-1][j]:0n)+(j?ways[i][j-1]:0n);
  }
  return ways[p][q];
}
let posets=0,orderedPairs=0,equalities=0,improved=0,further=0,extensionIncidences=0;
for(let n=2;n<=6;n++){
  const edges=[];for(let i=0;i<n;i++)for(let j=i+1;j<n;j++)edges.push([i,j]);
  for(let m=0;m<2**edges.length;m++){
    const up=Array(n).fill(0);
    for(let e=0;e<edges.length;e++)if(m&(1<<e)){const [i,j]=edges[e];up[i]|=1<<j;}
    let okay=true;
    for(const [i,j] of edges)if((up[i]&(1<<j))&&(up[j]&~up[i])){okay=false;break;}
    if(!okay)continue;
    const down=relations(up), ex=extensions(down), total=BigInt(ex.length), f=Array.from({length:n},()=>Array(n).fill(0n));
    for(const L of ex)for(let i=0;i<n;i++)for(let j=i+1;j<n;j++)f[L[i]][L[j]]++;
    posets++;
    for(let x=0;x<n;x++)for(let y=0;y<n;y++)if(x!==y&&!((up[x]|down[x])&(1<<y))){
      const A=(1<<x)|(up[x]&~up[y]),B=(1<<y)|(down[y]&~down[x]);
      const c=choose(pop(A)+pop(B),pop(B)), d=corridor(A,B,up,down),e=corridor(A,B,up,down,true);
      if((f[y][x]*c===total)!==moduleCondition(A,B,up,down))throw Error("equality criterion");
      if(f[y][x]*d<total || e>d || f[y][x]*e<total)throw Error('corridor');
      if(e<d)further++;
      orderedPairs++;extensionIncidences+=ex.length;
      if(f[y][x]*c===total)equalities++;
      if(d<c)improved++;
    }
  }
}
function bound(xs,up,down){
  const m=xs.length,b=Array.from({length:m},()=>Array(m).fill(1n));
  for(let len=2;len<=m;len++)for(let i=0;i+len<=m;i++){
    const j=i+len-1;let l=0, best;
    for(let t=i;t<j;t++){
      l|=down[xs[t]];let r=0;
      for(let q=t+1;q<=j;q++)r|=up[xs[q]];
      const p=(t-i+1)+pop(l&~down[xs[t+1]]),q=(j-t)+pop(r&~up[xs[t]]);
      const value=b[i][t]*b[t+1][j]*choose(p+q,p);
      if(best===undefined||value<best)best=value;
    }
    b[i][j]=best;
  }
  return b[0][m-1];
}
function perm(a){
  if(!a.length)return [[]];
  return a.flatMap((x,i)=>perm(a.filter((_,j)=>i!==j)).map(t=>[x,...t]));
}
let seed=113353,orders=0;
for(let test=0;test<180;test++){
  const n=7,up=Array(n).fill(0);
  for(let i=n-1;i>=0;i--)for(let j=i+1;j<n;j++){
    seed=(Math.imul(seed,1664525)+1013904223)>>>0;
    if((seed>>>10)%5<2)up[i]|=(1<<j)|up[j];
  }
  const down=relations(up), ex=extensions(down);
  for(let mask=0;mask<(1<<n);mask++){
    const xs=Array.from({length:n},(_,i)=>i).filter(i=>mask&(1<<i));
    if(xs.length<3||xs.length>5||xs.some(i=>up[i]&mask))continue;
    const freq=new Map();
    for(const L of ex){
      const k=L.filter(i=>mask&(1<<i)).join("");
      freq.set(k,(freq.get(k)||0)+1);
    }
    for(const ys of perm(xs)){
      const c=freq.get(ys.join(""))||0;
      if(bound(ys,up,down)*BigInt(c)<BigInt(ex.length))throw Error("chain bound");
      orders++;
    }
  }
}
console.log({posets,orderedPairs,equalities,improved,further,extensionIncidences,orders});
{
 const down=[0,0,0,6,15,15,0,4,223], up=relations(down), x=0,y=7;
 const A=(1<<x)|(up[x]&~up[y]), B=(1<<y)|(down[y]&~down[x]);
 const w=new Map();
 for(const L of extensions(down)){
   let b=0; const a=[];
   for(const u of L){
     if(B&(1<<u))b++;
     if(A&(1<<u))a.push(b);
   }
   const k=a.join(",");w.set(k,(w.get(k)||0)+1);
 }
 const stats=["1,1,2","0,2,2","0,1,2","1,2,2"].map(k=>w.get(k));
 if(stats.join(",")!=="115,161,69,207" || stats[2]*stats[3]>=stats[0]*stats[1]) throw Error("mixed word obstruction");
 console.log("mixed unlabeled log-supermodularity obstruction",stats);
}
{
 const down=[0,1,0,0,3,11,12,111], L=extensions(down);
 let a=0,b=0,c=0;
 for(const e of L){const u=e.indexOf(3)<e.indexOf(4), v=e.indexOf(2)<e.indexOf(5); a+=u;b+=v;c+=u&&v;}
 if([L.length,a,b,c].join(",")!=="152,141,136,126" || c*L.length>=a*b)throw Error("mixed labeled association obstruction");
 console.log("mixed fixed-label association obstruction",L.length,a,b,c);
}
