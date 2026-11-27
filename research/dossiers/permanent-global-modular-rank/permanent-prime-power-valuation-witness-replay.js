"use strict";
function vFactorial(n, p) {
  let result = 0;
  for (let q = Math.floor(n/p); q; q = Math.floor(q/p)) result += q;
  return result;
}
function predicted(n,r,p) {
  if(!r) return n;
  let result = n;
  for (let t=r;t<=n;t++) {
    let value=n-t;
    for(let q=p;q<=n;q*=p) value+=Math.max(0, Math.ceil((t+r)/q)-r);
    result=Math.min(result,value);
  }
  return result;
}
function witness(n,r,p) {
  const cost=Array.from({length:r+1},()=>Array(n+1).fill(Infinity));
  const sizes=Array.from({length:r+1},()=>Array(n+1).fill(0));
  cost[0][0]=0;
  for(let b=1;b<=r;b++) for(let t=b;t<=n;t++) for(let m=1;m<=t-b+1;m++) {
    const value=cost[b-1][t-m]+vFactorial(m,p);
    if(value<cost[b][t]) {cost[b][t]=value;sizes[b][t]=m;}
  }
  let t=0, best=Infinity;
  for(let j=r;j<=n;j++) if(n-j+cost[r][j]<best) {t=j;best=n-j+cost[r][j];}
  const out=[];
  let kept=t;
  for(let b=r;b>0;b--) {out.push(sizes[b][kept]);kept-=sizes[b][kept];}
  return {best,out,extra:n-t};
}
function denseMatrix(n, out, extra, p, bound) {
  const high=BigInt(p)**BigInt(bound+1);
  const groups=out.flatMap((size,group)=>Array(size).fill(group));
  return Array.from({length:n},(_,i)=>Array.from({length:n},(_,j)=>{
    if(i<groups.length&&j<groups.length&&groups[i]===groups[j])return 1n;
    if(i===j&&i>=groups.length&&extra)return BigInt(p);
    return high;
  }));
}
function permanent(A) {
  let dp=new Map([[0,1n]]);
  for(const row of A) {
    const next=new Map();
    for(const [mask,value] of dp) for(let j=0;j<row.length;j++) if(!(mask&(1<<j))) {
      const dest=mask|(1<<j);
      next.set(dest,(next.get(dest)??0n)+value*row[j]);
    }
    dp=next;
  }
  return dp.get((1<<A.length)-1);
}
function v(value,p) {
  let c=0;
  for(;value%BigInt(p)===0n;value/=BigInt(p))c++;
  return c;
}
let exactly=0;
for(const p of [2,3,5,7,11])for(let n=1;n<=12;n++)for(let r=0;r<=n;r++) {
  const {best,out,extra}=witness(n,r,p);
  const B=predicted(n,r,p);
  if(best!==B||v(permanent(denseMatrix(n,out,extra,p,B)),p)!==B)throw Error([n,r,p,B]);
  exactly++;
}
console.log(JSON.stringify({denseSharpWitnesses:exactly,binary15:predicted(15,1,2),ternary9:predicted(9,1,3)}));
