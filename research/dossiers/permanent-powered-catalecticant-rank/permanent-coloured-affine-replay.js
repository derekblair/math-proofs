"use strict";
const assert=require("node:assert/strict");
function perms(a){return a.length?a.flatMap((x,i)=>perms(a.filter((_,j)=>i!==j)).map(t=>[x,...t])):[[]];}
function sign(a){let s=1n;for(let i=0;i<a.length;++i)for(let j=i+1;j<a.length;++j)if(a[i]>a[j])s=-s;return s;}
function choose(a,k){if(!k)return [[]];if(a.length<k)return [];return choose(a.slice(1),k-1).map(t=>[a[0],...t]).concat(choose(a.slice(1),k));}
const range=n=>Array.from({length:n},(_,i)=>i);
const comp=(a,t)=>a.filter(i=>!t.includes(i));
let state=314159265;
function random(n){state=(Math.imul(state,1664525)+1013904223)>>>0;return state%n;}
let Pcounter=Object.create(null);
function ring(bounds){
  const strides=[];let full=1;for(const b of bounds){strides.push(full);full*=b+1;}
  const valid=Array.from({length:full},(_,x)=>bounds.map((b,i)=>Math.floor(x/strides[i])%(b+1)));
  const one=()=>new Map([[0,1n]]);
  const mul=(x,y)=>{const z=new Map;for(const [i,a] of x)for(const [j,b] of y){if(!a||!b||valid[i].some((t,k)=>t+valid[j][k]>bounds[k]))continue;
    const k=i+j;z.set(k,(z.get(k)||0n)+a*b);}return z;};
  const det=M=>{
    let acc=new Map;
    const ps=Pcounter[M.length]||=perms(range(M.length));
    for(const p of ps){let v=one();for(let i=0;i<p.length;++i)v=mul(v,M[i][p[i]]);
     const s=sign(p);for(const [k,c] of v)acc.set(k,(acc.get(k)||0n)+s*c);}
    return acc;
  };
  const aff=(src,vs,constant)=>{const r=new Map([[0,constant?src[0]:0n]]);
    for(let i=0;i<vs.length;++i)r.set(strides[i],src[1+vs[i]]);
    return r;
  };
  return {mul,det,aff,one,top:full-1};
}
function test(n,N,q,a,σ,τ,A){
 const s=σ.map((v,i)=>i*n+v),t=τ.map((v,i)=>i*n+v),xs=[...new Set([...s,...t])];
 const mult=xs.map(i=>(s.includes(i)?q-a:0)+(t.includes(i)?a:0));
 const X=ring(mult),U=ring(Array(n).fill(q-a)),V=ring(Array(n).fill(a));
 const exact=X.det(A.map(row=>row.map(f=>X.aff(f,xs,true)))).get(X.top)||0n;
 const all=range(N),marks=choose(all,a*n);let Y=0n;
 for(const I of marks)for(const J of marks){
   const fu=U.det(comp(all,I).map(i=>comp(all,J).map(j=>U.aff(A[i][j],s,true)))).get(U.top)||0n;
   const fv=V.det(I.map(i=>J.map(j=>V.aff(A[i][j],t,false)))).get(V.top)||0n;
   const odd=(I.reduce((x,y)=>x+y,0)+J.reduce((x,y)=>x+y,0))&1;
   Y+=(odd?-1n:1n)*fu*fv;
 }
 const agree=s.filter(i=>t.includes(i)).length;
 const B=BigInt(choose(range(q),a).length);
 assert.equal(Y,exact*B**BigInt(agree));return Y!==0n;
}
let checks=0,nonzero=0;
for(const [n,N,q,a,reps] of [[2,4,2,1,80],[2,5,2,1,65],[2,6,3,1,30],[2,6,3,2,30],[3,6,2,1,26]]){
 const pp=perms(range(n));
 for(let i=0;i<reps;++i){
  const A=range(N).map(()=>range(N).map(()=>range(n*n+1).map(()=>BigInt(random(5)-2))));
  const σ=pp[random(pp.length)],τ=i%3===0?σ:pp[random(pp.length)];
  nonzero+=test(n,N,q,a,σ,τ,A);checks++;
 }
}
console.log({globalAffineChecks:checks,nonzero});
