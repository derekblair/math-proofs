'use strict';
const assert=require('node:assert/strict');
let seed=0x03195783;
const rnd=(n)=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return (seed>>>9)%n;};
const fac=[1n];for(let i=1;i<=10;i++)fac.push(fac.at(-1)*BigInt(i));
const ch=(n,k)=>fac[n]/fac[k]/fac[n-k];
const mod=(x,m)=>(x%m+m)%m;
const ref=(M,k)=>{let z=0n; function go(i,r,s){
 if(r===k){z++;return;}
 if(i===M.length)return;
 go(i+1,r,s);for(let j=0;j<M.length;j++)if(M[i][j]&&!(s>>j&1))go(i+1,r+1,s|(1<<j));
 }go(0,0,0);return z;};
const per=A=>{const T=Array(1<<A.length).fill(0n);T[0]=1n;
 for(let s=0;s<T.length-1;s++){let i=0,t=s;while(t){i+=t&1;t>>=1;}
 for(let j=0;j<A.length;j++)if(!(s>>j&1))T[s|(1<<j)]+=A[i][j]*T[s];}return T.at(-1);};
let tests=0, nonzero=0;
for(let j=0;j<80;j++){
 const n=2+rnd(7), k=rnd(n+1),p=BigInt([11,13,17,19,23][rnd(5)]),m=p**BigInt(k+1),scale=p**BigInt(k);
 const M=Array.from({length:n},()=>Array.from({length:n},()=>rnd(2)));
 let v=0n;for(let t=0;t<=k;t++){
   const z=per(M.map(r=>r.map(a=>1n+BigInt(a*t)*p)));
   v+=((k-t)&1?-1n:1n)*ch(k,t)*z;
 }
 v=mod(v,m);
 assert.equal(v%scale,0n);
 const target=mod(ref(M,k)*fac[k]*fac[n-k],p);
 assert.equal(v/scale,target);
 tests++;nonzero+=Number(target!==0n);
}
console.log({tests,nonzero});
