"use strict";
let seed=0x691372ad;
function pick(n) {
  seed=(Math.imul(seed,1664525)+1013904223)>>>0;
  return (seed>>>12)%n;
}
function randomMatrix(n,m,g) {
  return Array.from({length:n},(_,i)=>Array.from({length:m},(_,j)=>g(i,j)));
}
const F=[1n];
for(let i=1;i<=30;i++)F[i]=F[i-1]*BigInt(i);
function vfac(n,p) {
  let v=0;
  for(let q=Math.floor(n/p);q;q=Math.floor(q/p))v+=q;
  return v;
}
function mod(x,m) {return (x%m+m)%m;}
function permanent(A) {
  const n=A.length,last=(1<<n)-1,dp=Array(last+1).fill(0n),pop=Array(last+1).fill(0);
  dp[0]=1n;
  for(let mask=0;mask<last;mask++) {
    if(mask)pop[mask]=pop[mask>>1]+(mask&1);
    if(dp[mask])for(let j=0;j<n;j++)if(!(mask&(1<<j))) {
      dp[mask|(1<<j)]+=dp[mask]*BigInt(A[pop[mask]][j]);
    }
  }
  return dp[last];
}
function matchingCounts(M) {
  const n=M.length,values=Array(n+1).fill(0n);
  function walk(i,used,q,w) {
    if(i===n){values[q]+=w;return;}
    walk(i+1,used,q,w);
    for(let j=0;j<n;j++)if(M[i][j]&&!(used&(1<<j))) {
      walk(i+1,used|(1<<j),q+1,w*BigInt(M[i][j]));
    }
  }
  walk(0,0,0,1n);
  return values;
}
function binaryBound(n,r) {
  if(!r)return n;
  let budget=n,weight=1,bits=0;
  while(budget>=r*weight){budget-=r*weight;bits+=r;weight*=2;}
  return n-bits-Math.floor(budget/weight);
}
function zeroP(dim) {return Array(dim).fill(0);}
function add(poly,e,c) {
  if(!c)return;
  const key=e.join(","),old=poly.get(key)?.c??0n;
  if(old+c)poly.set(key,{e,c:old+c});else poly.delete(key);
}
function partial(U,V,B) {
  const n=B.length,r=U[0].length,poly=new Map(),dim=1+2*r;
  function colorRight(j,used,e,w) {
    if(j===n){add(poly,e,w);return;}
    if(used&(1<<j)){colorRight(j+1,used,e,w);return;}
    for(let a=0;a<r;a++)if(V[j][a]){
      const next=[...e];next[1+r+a]++;
      colorRight(j+1,used,next,w*BigInt(V[j][a]));
    }
  }
  function colorOrMatch(i,used,e,w) {
    if(i===n){colorRight(0,used,e,w);return;}
    for(let j=0;j<n;j++)if(B[i][j]&&!(used&(1<<j))){
      const next=[...e];next[0]++;
      colorOrMatch(i+1,used|(1<<j),next,w*BigInt(B[i][j]));
    }
    for(let a=0;a<r;a++)if(U[i][a]){
      const next=[...e];next[1+a]++;
      colorOrMatch(i+1,used,next,w*BigInt(U[i][a]));
    }
  }
  colorOrMatch(0,0,zeroP(dim),1n);
  return poly;
}
function gadgetHafnian(U,V,B) {
  const n=B.length,r=U[0].length,m=2*n,dim=1+2*r,total=3*m;
  const graph=Array.from({length:total},()=>[]);
  function link(u,v,c,x=-1) {
    if(c){graph[u].push({v,c:BigInt(c),x});graph[v].push({v:u,c:BigInt(c),x});}
  }
  for(let i=0;i<n;i++)for(let j=0;j<n;j++)link(i,n+j,B[i][j],0);
  for(let i=0;i<m;i++) {
    const port=m+i,right=2*m+i,left=right-1,row=i<n;
    const v=row?U[i]:V[i-n];
    for(let a=0;a<r;a++)link(i,port,v[a],1+(row?0:r)+a);
    link(port,right,1);
    if(i){link(port,left,1);link(left,right,1);}
  }
  const cache=new Map([[0,new Map([[zeroP(dim).join(","),{e:zeroP(dim),c:1n}]])]]);
  function walk(mask) {
    if(cache.has(mask))return cache.get(mask);
    let u=0;
    while(!(mask&(1<<u)))u++;
    const out=new Map();
    for(const {v,c,x} of graph[u])if(mask&(1<<v)){
      for(const term of walk(mask^(1<<u)^(1<<v)).values()){
        const powers=[...term.e];
        if(x>=0)powers[x]++;
        add(out,powers,c*term.c);
      }
    }
    cache.set(mask,out);
    return out;
  }
  return walk((1<<total)-1);
}
function equalPolynomials(a,b) {
  return a.size===b.size&&[...a].every(([key,t])=>b.get(key)?.c===t.c);
}
const checks={binary:0,gadgets:0,binaryNonzero:0,odd:0,oddNonzero:0,maxOrder:0};
for(let trial=0;trial<96;trial++) {
  const n=1+trial%7,r=Math.min(n,1+Math.floor(trial/7)%3),excess=1+trial%5;
  const U=randomMatrix(n,r,(i,j)=>i<r?Number(i===j):pick(2));
  const V=randomMatrix(n,r,(i,j)=>i<r?Number(i===j):pick(2));
  const B=randomMatrix(n,n,()=>pick(5)-2);
  const A=randomMatrix(n,n,(i,j)=>2*B[i][j]+U[i].reduce((s,x,a)=>s+x*V[j][a],0));
  const poly=partial(U,V,B);
  if(n<=4) {
    if(!equalPolynomials(poly,gadgetHafnian(U,V,B)))throw Error("gadget matching polynomial");
    checks.gadgets++;
  }
  const b=binaryBound(n,r),divisor=2n**BigInt(b),modulus=2n**BigInt(excess);
  let out=0n;
  for(const {e,c} of poly.values()){
    const left=e.slice(1,1+r),right=e.slice(1+r);
    if(left.some((x,a)=>x!==right[a]))continue;
    const factor=left.reduce((s,x)=>s*F[x],2n**BigInt(e[0]));
    if(factor%divisor)throw Error("binary term valuation");
    out+=mod(c,modulus)*(factor/divisor);
  }
  const exact=permanent(A);
  if(exact%divisor||mod(exact/divisor,modulus)!==mod(out,modulus))throw Error("binary quotient");
  checks.binary++;
  if(mod(out,modulus))checks.binaryNonzero++;
}
for(const [p,maxN] of [[2,7],[3,8],[5,4],[7,6],[11,5]]){
  for(let trial=0;trial<20;trial++){
    const original=1+trial%maxN,k=1+Math.floor(trial/maxN)%Math.min(original,4);
    let power=p;
    while(power<=k||power-1+k<original)power*=p;
    const n=power-1+k,bigP=BigInt(p),v=k+vfac(k,p)+vfac(n-k,p);
    const divisor=bigP**BigInt(v),modulus=divisor*bigP;
    const M=randomMatrix(original,original,()=>pick(2));
    const coeff=matchingCounts(M)[k];
    const input=t=>randomMatrix(n,n,(i,j)=>1+p*t*(M[i]?.[j]??0));
    const row=Array.from({length:k+1},(_,t)=>mod(permanent(input(t)),modulus));
    for(let a=k;a;a--)for(let t=0;t<a;t++)row[t]=mod(row[t+1]-row[t],modulus);
    const unit=F[k]*F[n-k]*bigP**BigInt(k)/divisor;
    if(unit%bigP===0n||row[0]%divisor||row[0]/divisor!==mod(unit*coeff,bigP))
      throw Error("digit isolation "+[p,n,k]);
    const baseline=Math.min(...Array.from({length:n},(_,j)=>n-(j+1)+vfac(j+1,p)));
    if(v+1-baseline<1||v+1-baseline>k+vfac(k,p)+1)throw Error("excess bound");
    if(p===2&&v+1-baseline!==vfac(k,p)+1)throw Error("binary excess equality");
    if(p!==2){checks.odd++;if(mod(coeff,bigP))checks.oddNonzero++;}
    checks.maxOrder=Math.max(checks.maxOrder,n);
  }
}

function paddedPermanent(M,n,p,modulus) {
  const original=M.length,last=(1<<original)-1;
  let dp=Array(last+1).fill(0n);
  dp[0]=1n;
  const pop=dp.map((_,i)=>i.toString(2).replaceAll("0","").length);
  for(let row=0;row<original;row++){
    const next=dp.map(()=>0n);
    for(let mask=0;mask<=last;mask++)if(dp[mask]){
      const fresh=n-original-row+pop[mask];
      if(fresh>0)next[mask]=mod(next[mask]+BigInt(fresh)*dp[mask],modulus);
      for(let j=0;j<original;j++)if(!(mask&(1<<j))){
        const dest=mask|(1<<j);
        next[dest]=mod(next[dest]+BigInt(1+p*M[row][j])*dp[mask],modulus);
      }
    }
    dp=next;
  }
  let remaining=1n;
  for(let k=1;k<=n-original;k++)remaining=mod(remaining*BigInt(k),modulus);
  return mod(remaining*dp.reduce((s,x)=>s+x,0n),modulus);
}
checks.singleQuery=0;
checks.singleQueryNonzero=0;
checks.maxPaddedOrder=0;
for(const [p,cap] of [[2,5],[3,4],[5,3],[7,2],[11,2]])for(let sample=0;sample<30;sample++){
  const k=1+sample%cap, original=k+Math.floor(sample/cap)%5;
  let L=k+1,power=p**L;
  while(power-1+k<original){power*=p;L++;}
  const t0=power-1,n=t0+k,v=vfac(t0,p),b=k+v;
  const bigP=BigInt(p),divisor=bigP**BigInt(b),modulus=divisor*bigP;
  for(let q=0;q<=n;q++)if((q+vfac(n-q,p)===b)!==(q===k)||q+vfac(n-q,p)<b)
    throw Error("unique minimizing correction size");
  const M=randomMatrix(original,original,()=>pick(2));
  const coeff=matchingCounts(M)[k];
  const value=paddedPermanent(M,n,p,modulus);
  if(n<=12&&value!==mod(permanent(randomMatrix(n,n,(i,j)=>1+p*(M[i]?.[j]??0))),modulus))
    throw Error("independent padded permanent");
  let unit=1n;
  for(let a=1;a<=t0;a++){
    let f=a;
    while(f%p===0)f/=p;
    unit=mod(unit*BigInt(f),bigP);
  }
  if(value%divisor||value/divisor!==mod(unit*coeff,bigP))
    throw Error("single-query normalized digit "+[p,n,k]);
  checks.singleQuery++;
  if(coeff%bigP)checks.singleQueryNonzero++;
  checks.maxPaddedOrder=Math.max(checks.maxPaddedOrder,n);
}

console.log(JSON.stringify(checks));
