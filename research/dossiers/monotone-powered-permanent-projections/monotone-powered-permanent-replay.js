"use strict";
const assert=require("node:assert/strict");
const seq=n=>Array.from({length:n},(_,i)=>i);
const bit=i=>1n<<BigInt(i);
let seed=27183;
function rng(n){seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed%n;}
function sparsePermanent(A){
 const n=A.length, rows=A.map(r=>r.map((x,j)=>[j,x]).filter(x=>x[1]));
 const cols=seq(n).map(j=>A.map((r,i)=>[i,r[j]]).filter(x=>x[1]));
 const memo=new Map;
 function solve(R,C){
  if(!R)return 1n;
  const key=(R<<BigInt(n))|C;if(memo.has(key))return memo.get(key);
  let best=null,I=-1,left=true;
  const check=(i,adj,M,l)=>{const b=adj.filter(([j])=>M&bit(j));if(!best||b.length<best.length){best=b;I=i;left=l;}};
  for(let i=0;i<n&&(!best||best.length>1);i++)if(R&bit(i))check(i,rows[i],C,true);
  for(let i=0;i<n&&(!best||best.length>1);i++)if(C&bit(i))check(i,cols[i],R,false);
  let v=0n;for(const [j,x] of best)v+=x*(left?solve(R^bit(I),C^bit(j)):solve(R^bit(j),C^bit(I)));
  memo.set(key,v);return v;
 }
 const all=(1n<<BigInt(n))-1n;return solve(all,all);
}
function purePowerProjection(x,q){
 const d=x.length;
 if(q===1)return [[x.reduce((a,b)=>a+b,0n)]];
 const N=d<=2?q:q+(d-1)*(q-1),A=seq(N).map(()=>Array(N).fill(0n));
 for(let i=0;i<N;i++)A[i][i]=i<q?x[0]:1n;
 if(d===2){for(let i=0;i<q;i++)A[i][(i+1)%q]=x[1];}
 if(d>=3){
  for(let i=1;i<q;i++)A[i][(i+1)%q]=1n;
  for(let j=1;j<d;j++){
   const p=q+(j-1)*(q-1);A[0][p]=x[j];
   for(let i=0;i<q-1;i++)A[p+i][i+1===q-1?1:p+i+1]=x[j];
  }
 }
 return A;
}
let scalar=0,hall=0,largest=0;
for(let q=1;q<=9;q++)for(let d=1;d<=9;d++)for(let t=0;t<3;t++){
 const x=seq(d).map(()=>t===0?1n:BigInt(rng(11)-5)),A=purePowerProjection(x,q);
 assert.equal(sparsePermanent(A),x.reduce((v,a)=>v+a**BigInt(q),0n));scalar++;largest=Math.max(largest,A.length);
}
const fac=n=>n<=1?1n:BigInt(n)*fac(n-1);
for(let n=1;n<=7;n++)for(let a=1;a<=n;a++)for(let q=2;q<=5;q++){
 const X=seq(n).map((i)=>seq(n).map(j=>i<a&&j>=a-1?BigInt(rng(11)-5):i>=a&&j<a-1?0n:1n));
 const v=X.slice(0,a).flatMap(row=>row.slice(a-1)).reduce((acc,x)=>acc+x**BigInt(q),0n)*fac(a-1)*fac(n-a);
 assert.equal(sparsePermanent(X.map(row=>row.map(x=>x**BigInt(q)))),v);hall++;
}
const matchingSlots=[[0,4,8],[0,5,7],[1,3,8],[1,5,6],[2,3,7],[2,4,6]];
let exhaustive=0,pureAll=0;
for(let code=0;code<5**9;code++){
 const A=[];let x=code;for(let i=0;i<9;i++){A[i]=x%5;x=Math.floor(x/5);}
 let labels=0,good=true;
 for(const S of matchingSlots){
  const t=S.map(e=>A[e]); if(t.includes(0))continue;
  const j=t.filter(x=>x>=2);
  if(j.length!==2||j[0]!==j[1]){good=false;break;}
  labels|=1<<(j[0]-2);
 }
 if(good&&labels===7)pureAll++;
 exhaustive++;
}
assert.equal(pureAll,0);
console.log({scalarConstructions:scalar,largestOrder:largest,hallBoxChecks:hall,exhaustive3x3Graphs:exhaustive,forbiddenRepresentations:pureAll});


const gcd=(a,b)=>b?gcd(b,a%b):a>=0n?a:-a;
const rat=(a,b=1n)=>{const g=gcd(a,b);return [a/g,b/g];};
const mul=(a,b)=>rat(a[0]*b[0],a[1]*b[1]),div=(a,b)=>rat(a[0]*b[1],a[1]*b[0]);
const le=(a,b)=>a[0]*b[1]<=b[0]*a[1];
function perms(a){return a.length?a.flatMap((v,i)=>perms(a.filter((_,j)=>i!==j)).map(t=>[v,...t])):[[]];}
let scaling=0;
for(let n=2;n<=6;n++){
 const pp=perms(seq(n));
 for(let trial=0;trial<25;trial++){
  const A=seq(n).map(()=>seq(n).map(()=>BigInt(rng(23))));
  let M=0n,best;
  for(const P of pp){const w=P.reduce((v,j,i)=>v*A[i][j],1n);if(w>M){M=w;best=P;}}
  if(!M)continue;
  const B=A.map((row,i)=>best.map(j=>rat(row[j],row[best[i]])));
  const potential=i=>{
   let best=[1n,1n];
   function dfs(j,mask,value){
    if(le(best,value))best=value;
    for(let k=0;k<n;k++)if(!(mask&(1<<k))&&B[j][k][0])dfs(k,mask|(1<<k),mul(value,B[j][k]));
   }
   dfs(i,1<<i,[1n,1n]);return best;
  };
  const P=seq(n).map(potential);
  const C=B.map((row,i)=>row.map((x,j)=>div(mul(x,P[j]),P[i])));
  for(const row of C)for(const x of row)assert(le(x,[1n,1n]));
  for(const sigma of pp){
   const old=sigma.reduce((v,j,i)=>v*A[i][best[j]],1n);
   const prod=sigma.reduce((v,j,i)=>mul(v,C[i][j]),[1n,1n]);
   assert.equal(prod[0]*M,old*prod[1]);
  }
  scaling++;
 }
}
console.log({exactMatchingNormalizations:scaling});
