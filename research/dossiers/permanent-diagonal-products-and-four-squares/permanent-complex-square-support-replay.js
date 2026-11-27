"use strict";
let seed=0x8dd25b30;
function random(n){seed=(Math.imul(seed,1664525)+1013904223)>>>0;return (seed>>>9)%n;}
const ints=n=>Array.from({length:n},(_,i)=>i);
function permutations(n){
  const out=[];
  function visit(p){
    if(p.length===n){out.push(p);return;}
    for(const i of ints(n))if(!p.includes(i))visit([...p,i]);
  }
  visit([]);return out;
}
const perms=Array.from({length:9},(_,n)=>permutations(n));
function matchingMask(p){return p.reduce((mask,j,i)=>mask|(1<<(i*p.length+j)),0);}
function oneCycle(p,q){
  const rel=p.map((_,i)=>p.indexOf(q[i]));
  const start=rel.findIndex((x,i)=>x!==i);
  if(start<0)return false;
  const seen=new Set();
  let current=start;
  do{seen.add(current);current=rel[current];}while(current!==start);
  return seen.size===rel.filter((x,i)=>x!==i).length;
}
function shortest(arcs,start,goal){
  const queue=[[start]],seen=new Set([start]);
  for(const path of queue){
    const v=path.at(-1);
    if(goal(v))return path;
    for(const w of arcs[v])if(!seen.has(w)){seen.add(w);queue.push([...path,w]);}
  }
  throw Error("allowable edges must return to their component");
}
function switchAlong(cycle,fixed){
  const q=[...fixed];
  for(let j=0;j<cycle.length;j++)q[cycle[j]]=fixed[cycle[(j+1)%cycle.length]];
  return q;
}
function witness(arcs,u,fixed){
  const v=arcs[u][0],w=arcs[u][1];
  const cycle=[u,...shortest(arcs,v,x=>x===u).slice(0,-1)];
  const ear=[u,...shortest(arcs,w,x=>cycle.includes(x))];
  const end=ear.at(-1),suffix=end===u?[]:cycle.slice(cycle.indexOf(end)+1);
  const alternate=[...ear.slice(0,end===u?-1:undefined),...suffix];
  return [fixed,switchAlong(cycle,fixed),switchAlong(alternate,fixed)];
}
const count={graphsWithMatchings:0,noncycleWitnesses:0,cycleSupports:0};
function audit(n,mask,raw){
  const matchings=raw.filter(x=>(mask&x.mask)===x.mask);
  if(!matchings.length)return;
  count.graphsWithMatchings++;
  const allowed=matchings.reduce((bits,x)=>bits|x.mask,0);
  const fixed=matchings[0].p;
  const arcs=ints(n).map(i=>ints(n).filter(j=>i!==j&&(allowed&(1<<(i*n+fixed[j])))));
  const branch=arcs.findIndex(a=>a.length>=2);
  if(branch>=0){
    const P=witness(arcs,branch,fixed);
    if(P.some(p=>new Set(p).size!==n||(matchingMask(p)&allowed)!==matchingMask(p))
      ||!oneCycle(P[0],P[1])||!oneCycle(P[0],P[2])||!oneCycle(P[1],P[2]))
        throw Error("constructive matching triangle "+[n,mask,branch]);
    count.noncycleWitnesses++;
    return;
  }
  const switched=new Set(),cycleComponents=[];
  for(let i=0;i<n;i++)if(arcs[i].length&&!switched.has(i)){
    const members=[];
    let current=i;
    do{
      if(switched.has(current)||arcs[current].length!==1)throw Error("component is not a cycle");
      switched.add(current);members.push(current);current=arcs[current][0];
    }while(current!==i);
    cycleComponents.push(members);
  }
  const dim=cycleComponents.length;
  if(dim>Math.floor(n/2)||matchings.length!==2**dim)throw Error("matching count for cycle blocks");
  for(let i=0;i<matchings.length;i++)for(let j=i+1;j<matchings.length;j++){
    if(oneCycle(matchings[i].p,matchings[j].p)){
      const first=cycleComponents.filter(c=>matchings[i].p[c[0]]!==fixed[c[0]]).length;
      const last=cycleComponents.filter(c=>matchings[j].p[c[0]]!==fixed[c[0]]).length;
      if((first-last)%2===0)throw Error("cycle cube edge parity");
    }
  }
  count.cycleSupports++;
}
for(const n of [1,2,3,4,5]){
  const raw=perms[n].map(p=>({p,mask:matchingMask(p)}));
  if(n<5){for(let mask=0;mask<1<<(n*n);mask++)audit(n,mask,raw);}
  else for(let j=0;j<4000;j++)audit(n,random(2**(n*n)),raw);
}
function key(p){
  const blocks=[];
  for(let i=0;i<p.length;i+=2)blocks.push(p.slice(i,i+2).sort((x,y)=>x-y).join(","));
  return blocks.join("|");
}
function factorial(n){let z=1;for(let t=2;t<=n;t++)z*=t;return z;}
function squaredPermanent(A){
  const n=A.length;
  let dp=new Map([[0,1n]]);
  for(const row of A){
    const out=new Map();
    for(const [mask,total] of dp)for(let j=0;j<n;j++)if(!(mask&(1<<j))){
      const k=mask|(1<<j);
      out.set(k,(out.get(k)??0n)+total*row[j]**2n);
    }
    dp=out;
  }
  return dp.get((1<<n)-1);
}
function absSquareForBlockMask(A,p){
  let result=1n;
  for(let i=0;i<p.length;i+=2){
    if(i+1===p.length){result*=A[i][p[i]]**2n;continue;}
    const [a,b]=p.slice(i,i+2).sort((x,y)=>x-y);
    // The block is [i*A[i,a], A[i,b]; A[i+1,a], A[i+1,b]].
    const imaginary=A[i][a]*A[i+1][b],real=-A[i][b]*A[i+1][a];
    result*=real**2n+imaginary**2n;
  }
  return result;
}
function directDetNorm(A,p){
  const n=A.length;
  let real=0n,imaginary=0n;
  for(const q of perms[n]){
    let coeff=1n,imag=0;
    for(let i=0;i<n;i++){
      const first=i-i%2, cols=p.slice(first,first+2).sort((x,y)=>x-y);
      if(!cols.includes(q[i])){coeff=0n;break;}
      if(cols.length===2&&i===first&&q[i]===cols[0])imag++;
      coeff*=A[i][q[i]];
      for(let j=0;j<i;j++)if(q[j]>q[i])coeff=-coeff;
    }
    if(imag%4===0)real+=coeff;
    else if(imag%4===1)imaginary+=coeff;
    else if(imag%4===2)real-=coeff;
    else imaginary-=coeff;
  }
  return real**2n+imaginary**2n;
}
count.denseIdentities=0;
count.directGaussianNorms=0;
for(let n=0;n<=8;n++){
  const classes=new Map(perms[n].map(p=>[key(p),p]));
  if(classes.size!==factorial(n)/2**Math.floor(n/2))throw Error("number of orbit classes");
  for(let j=0;j<12;j++){
    const A=ints(n).map(()=>ints(n).map(()=>BigInt(random(11)-5)));
    let result=0n;
    for(const p of classes.values())result+=absSquareForBlockMask(A,p);
    if(result!==squaredPermanent(A))throw Error("exact block expression");
    if(n<=5){
      const p=[...classes.values()][random(classes.size)];
      if(directDetNorm(A,p)!==absSquareForBlockMask(A,p))throw Error("Gaussian determinant");
      count.directGaussianNorms++;
    }
    count.denseIdentities++;
  }
}

function cyclotomic(q) {
  const f=({2:[1,0,1],3:[1,-1,1],4:[1,0,0,0,1],5:[1,-1,1,-1,1],6:[1,0,-1,0,1]})[q].map(BigInt);
  const d=f.length-1;
  const zero=Array(d).fill(0n), one=[1n,...zero.slice(1)], zeta=[0n,1n,...zero.slice(2)];
  function add(a,b){return a.map((v,i)=>v+b[i]);}
  function neg(a){return a.map(v=>-v);}
  function mul(a,b){
    const c=Array(2*d-1).fill(0n);
    for(let i=0;i<d;i++)for(let j=0;j<d;j++)c[i+j]+=a[i]*b[j];
    for(let i=c.length-1;i>=d;i--)for(let j=0;j<d;j++)c[i-d+j]-=c[i]*f[j];
    return c.slice(0,d);
  }
  let powers=[one];
  for(let j=1;j<2*q;j++)powers.push(mul(powers.at(-1),zeta));
  const lambdas=ints(q).map(j=>neg(powers[2*j+1]));
  const equals=(a,b)=>a.every((v,i)=>v===b[i]);
  let poly=[one];
  for(const lambda of lambdas){
    const next=Array(poly.length+1).fill(zero);
    for(let i=0;i<poly.length;i++){
      next[i]=add(next[i],poly[i]);
      next[i+1]=add(next[i+1],mul(lambda,poly[i]));
    }
    poly=next;
  }
  if(poly.some((a,i)=>!equals(a,i&&i<q?zero:one)))throw Error("all mixed binomial coefficients vanish");
  return {zero,one,add,neg,mul,lambdas,equals,integer:k=>[k,...zero.slice(1)]};
}
function generalPermanent(A,q) {
  return perms[A.length].reduce((sum,p)=>sum+p.reduce((w,j,i)=>w*(A[i][j]**BigInt(q)),1n),0n);
}
function factorizedClass(A,p,q) {
  let value=1n;
  for(let i=0;i<p.length;i+=2){
    if(i+1===p.length){value*=A[i][p[i]]**BigInt(q);continue;}
    const [a,b]=p.slice(i,i+2).sort((x,y)=>x-y);
    const first=A[i][a]*A[i+1][b],second=A[i][b]*A[i+1][a];
    value*=first**BigInt(q)+second**BigInt(q);
  }
  return value;
}
function directRootProduct(R,A,p,q) {
  let product=R.one;
  const ordered=p.flatMap((_,i)=>i%2?[]:p.slice(i,i+2).sort((x,y)=>x-y));
  let orderSign=1n;
  for(let i=0;i<ordered.length;i++)for(let j=i+1;j<ordered.length;j++)if(ordered[i]>ordered[j])orderSign=-orderSign;
  for(const lambda of R.lambdas){
    let determinant=R.zero;
    for(const perm of perms[p.length]){
      let value=R.one;
      for(let i=0;i<p.length;i++){
        const first=i-i%2,cols=ordered.slice(first,first+2);
        if(!cols.includes(perm[i])){value=R.zero;break;}
        let w=R.integer(A[i][perm[i]]);
        if(i===first&&cols.length===2)w=perm[i]===cols[0]?R.mul(lambda,w):R.neg(w);
        for(let j=0;j<i;j++)if(perm[j]>perm[i])w=R.neg(w);
        value=R.mul(value,w);
      }
      determinant=R.add(determinant,value);
    }
    product=R.mul(product,determinant);
  }
  return R.mul(product,R.integer(orderSign**BigInt(q)));
}
count.cyclotomicIdentities=0;
count.directRootProducts=0;
count.generalPowerIdentities=0;
for(let q=2;q<=6;q++){
  const R=cyclotomic(q);
  count.cyclotomicIdentities++;
  for(let n=1;n<=6;n++)for(let trial=0;trial<6;trial++){
    const A=ints(n).map(()=>ints(n).map(()=>BigInt(random(7)-3)));
    const classes=new Map(perms[n].map(p=>[key(p),p]));
    const value=[...classes.values()].reduce((s,p)=>s+factorizedClass(A,p,q),0n);
    if(value!==generalPermanent(A,q))throw Error("general q class identity");
    if(n<=5){
      const p=[...classes.values()][random(classes.size)];
      if(!R.equals(R.integer(factorizedClass(A,p,q)),directRootProduct(R,A,p,q)))
        throw Error("direct cyclotomic determinant product");
      count.directRootProducts++;
    }
    count.generalPowerIdentities++;
  }
}

console.log(JSON.stringify(count));
