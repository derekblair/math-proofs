'use strict';
const I=n=>Array.from({length:n},(_,i)=>i), sum=x=>x.reduce((a,b)=>a+b,0n), prod=x=>x.reduce((a,b)=>a*b,1n);
let seed=949207;function r(n){seed^=seed<<13;seed^=seed>>>17;seed^=seed<<5;return (seed>>>0)%n;}
function simplex(d,D){
 let states=[],x=Array(d).fill(0);
 function rec(k,b){if(k===d){states.push(x.slice());return;}
  for(let i=0;i<=b;i++){x[k]=i;rec(k+1,b-i);}
 }
 rec(0,D);return states;
}
function compute(t,D,F){
 const f=[1n];for(let i=1;i<=D+2*t;i++)f.push(f.at(-1)*BigInt(i));
 const C=(n,m)=>f[n]/f[m]/f[n-m],sg=i=>i%2?-1n:1n;
 const N=I(D+1).map(a=>{
  let p=[1n];
  for(let j=0;j<a;j++){const q=Array(p.length+1).fill(0n);p.forEach((z,i)=>{q[i]-=BigInt(j)*z;q[i+1]+=z;});p=q;}
  return p.map(x=>x*f[D]/f[a]);
 });
 const L=I(D+1).map(a=>I(D+1).map(b=>sum(I(Math.min(a,b)+1).map(k=>f[k]*N[a][k]*N[b][k]))));
 let total=0n,evaluations=0;
 for(const x of simplex(2*t,D)){
  let q=[1n];
  for(let i=0;i<t;i++){
   const u=x[i],v=x[i+t],arr=Array(D+1).fill(0n);
   for(let a=u;a<=D;a++)for(let b=v;a+b<=D;b++)arr[a+b]+=sg(a+b-u-v)*C(a,u)*C(b,v)*L[a][b];
   const p=Array(D+1).fill(0n);
   q.forEach((w,k)=>{for(let j=0;k+j<=D;j++)p[k+j]+=w*arr[j];});
   q=p;
  }
  total+=sum(q)*F(x);evaluations++;
 }
 const den=f[D]**BigInt(2*t);
 if(total%den||BigInt(evaluations)!==C(D+2*t,2*t))throw Error('inexact count');
 return total/den;
}
let checked=0;
for(let t=1;t<=3;t++)for(let D=0;D<=6;D++)for(let rep=0;rep<5;rep++){
 const terms=I(14).map(()=>{let x=Array(2*t).fill(0),k=r(D+1);
   for(let j=0;j<k;j++)x[r(2*t)]++;
   return [BigInt(r(13)-6),x];});
 const F=x=>sum(terms.map(([a,e])=>a*prod(e.map((u,j)=>BigInt(x[j])**BigInt(u)))));
 const f=[1n];for(let i=1;i<=D;i++)f.push(f.at(-1)*BigInt(i));
 const known=sum(terms.map(([a,e])=>e.slice(0,t).every((u,j)=>u===e[j+t])?a*prod(e.slice(0,t).map(i=>f[i])):0n));
 if(compute(t,D,F)!==known)throw Error('weighted simplex quadrature');checked++;
}
console.log(JSON.stringify({checked}));
