'use strict';
const assert=require('node:assert/strict');
const fac=[1n]; for(let i=1;i<=14;++i)fac.push(fac.at(-1)*BigInt(i));
const ch=(n,k)=>fac[n]/fac[k]/fac[n-k];
const mod=(x,m)=>(x%m+m)%m;
function vFact(m,p){let a=0;while(m){m=Math.floor(m/p);a+=m;}return a;}
function lower(t,r,p){let a=0;for(let z=p;z<t+r;z*=p)a+=Math.max(0,Math.ceil((t+r)/z)-r);return a;}
function* compositions(t,r){if(r===1){if(t>=1)yield [t];return;}for(let i=1;i<=t-r+1;i++)for(let v of compositions(t-i,r-1))yield [i,...v];}
function finiteDiff(order,f,m){
 const u=Array(order.length).fill(0n);
 function go(i,k){
  if(i===order.length){const w=k*f(u);return m?mod(w,m):w;}
  let out=0n;for(let j=0;j<=order[i];j++){
   u[i]=BigInt(j);
   out+=go(i+1,((order[i]-j)&1?-1n:1n)*ch(order[i],j)*k);
  }
  return m?mod(out,m):out;
 }
 return go(0,1n);
}
const product=(rows,u,m)=>rows.reduce((a,row)=>{
 const z=a*row.reduce((b,c,i)=>b+c*u[i],0n);
 return m?mod(z,m):z;
},1n);
function calc(B,U,C,p,h){
 const r=B.length,n=r+C.length,P=BigInt(p),ph=P**BigInt(h);let result=0n,skips=0,qSeen=0,states=0;
 for(let mask=0;mask<1<<C.length;mask++){
  const corr=[], uRows=[];
  C.forEach((c,i)=>((mask>>i)&1?corr:uRows).push((mask>>i)&1?c:U[i]));
  const q=corr.length,t=n-q;
  if(q+lower(t,r,p)>=h){skips++;continue;}
  qSeen++;
  const m=P**BigInt(h-q);
  const rows=Array.from({length:n},(_,i)=>[...B.map(b=>b[i]),...corr.map(c=>c[i])]);
  for(const a of compositions(t,r)){
   if(q+a.reduce((s,i)=>s+vFact(i,p),0)>=h)continue;
   states++;
   const scale=a.reduce((v,i)=>v*fac[i],1n);
   const g=finiteDiff(a,x=>product(uRows,x)*x.reduce((v,i)=>v*i,1n),null);
   assert.equal(g%scale,0n);
   const w=finiteDiff([...a,...Array(q).fill(1)],y=>product(rows,y,m),m);
   result=mod(result+(P**BigInt(q))*(g/scale)*w,ph);
  }
 }
 return {result,skips,qSeen,states};
}
function per(A){
 const n=A.length,T=Array(1<<n).fill(0n);T[0]=1n;
 for(let s=0;s<T.length-1;s++){
   let bits=s,k=0;while(bits){k+=bits&1;bits>>=1;}
   A[k].forEach((a,j)=>{if(!(s>>j&1))T[s|1<<j]+=a*T[s];});
 }return T.at(-1);
}
let seed=0x3523da15;
function rnd(n){seed=(Math.imul(seed,1664525)+1013904223)>>>0;return (seed>>>4)%n;}
const seq=(n,f)=>Array.from({length:n},(_,i)=>f(i));
let tests=0,nonzero=0,skips=0,states=0,corrCases=0;
for(const p of [2,3,5,7])for(let u=0;u<25;u++){
 const n=3+rnd(6),r=1+rnd(Math.min(n,3)),h=1+rnd(7),P=BigInt(p);
 const B=seq(r,i=>seq(n,j=>j<r?(i===j?1n:0n)+P*BigInt(rnd(7)-3):BigInt(rnd(13)-6)));
 const U=seq(n-r,()=>seq(r,()=>BigInt(rnd(p))));
 const C=seq(n-r,()=>seq(n,()=>BigInt(rnd(9)-4)));
 const A=[...B,...U.map((u,i)=>C[i].map((c,j)=>P*c+u.reduce((s,b,k)=>s+b*B[k][j],0n)))];
 const z=calc(B,U,C,p,h);
 assert.equal(z.result,mod(per(A),P**BigInt(h)));
 tests++;nonzero+=Number(z.result!==0n);skips+=z.skips;states+=z.states;corrCases+=Number(z.qSeen>1);
}
console.log({tests,nonzero,skips,states,corrCases});
