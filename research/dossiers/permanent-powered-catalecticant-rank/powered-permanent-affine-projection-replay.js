"use strict";
const assert=require("node:assert/strict");
const range=n=>Array.from({length:n},(_,i)=>i),bit=i=>1n<<BigInt(i);
let seed=1221;
function rnd(n){seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed%n;}
function sparsePermanent(A){
 const n=A.length, rows=A.map(r=>r.map((v,j)=>[j,v]).filter(([,v])=>v!==0n));
 const cols=range(n).map(j=>A.map((r,i)=>[i,r[j]]).filter(([,v])=>v!==0n));
 const memo=new Map;
 let work=0;
 function rec(rr,cc){
  if(rr===0n)return 1n;
  const code=(rr<<BigInt(n))|cc;
  if(memo.has(code))return memo.get(code);
  work++;
  let best=null, fixed=-1, left=true;
  function inspect(list,other,idx,fromleft){
   const viable=list.filter(([j])=>(other&bit(j))!==0n);
   if(best===null||viable.length<best.length){best=viable;fixed=idx;left=fromleft;}
  }
  for(let i=0;i<n&&(best===null||best.length>1);++i)if(rr&bit(i))inspect(rows[i],cc,i,true);
  for(let j=0;j<n&&(best===null||best.length>1);++j)if(cc&bit(j))inspect(cols[j],rr,j,false);
  let answer=0n;
  for(const [i,w] of best)answer+=w*(left?rec(rr^bit(fixed),cc^bit(i)):rec(rr^bit(i),cc^bit(fixed)));
  memo.set(code,answer);
  return answer;
 }
 const all=(1n<<BigInt(n))-1n;
 return [rec(all,all),work];
}
function build(X,q){
 const n=X.length,N=n+(q-1)*n*n;
 const A=range(N).map(()=>Array(N).fill(0n));
 for(let i=0;i<n;++i)for(let j=0;j<n;++j){
  if(q===1){A[i][j]=X[i][j];continue;}
  const off=n+(q-1)*(i*n+j);
  A[i][off]=X[i][j];
  for(let t=0;t<q-1;++t){
    A[off+t][off+t]=1n;
    A[off+t][t+1===q-1?j:off+t+1]=X[i][j];
  }
 }
 return A;
}
let checks=0,visited=0,largest=0;
for(let n=1;n<=4;++n)for(let q=1;q<=5;++q)for(let r=0;r<12;++r){
 const X=range(n).map(()=>range(n).map(()=>BigInt(rnd(9)-4)));
 const A=build(X,q), [p,w]=sparsePermanent(A);
 assert.equal(p,sparsePermanent(X.map(row=>row.map(x=>x**BigInt(q))))[0]);
 largest=Math.max(largest,A.length);visited+=w;checks++;
}
console.log({affinePermanentProjectionGadgetChecks:checks,largestOrder:largest,visited});
