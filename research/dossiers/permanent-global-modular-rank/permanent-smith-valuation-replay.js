'use strict';
const assert=require('node:assert/strict');
const aN=(n,f)=>Array.from({length:n},(_,i)=>f(i));
const zop=(x,n)=>((x%n)+n)%n;
const val=(x,p)=>{if(!x)return Infinity;let y=0;while(x%p===0n){x/=p;y++;}return y};
const fac=[1n];for(let i=1;i<=10;++i)fac.push(fac.at(-1)*BigInt(i));
function* comps(n,r){if(r===1){yield[n];return;}for(let x=0;x<=n;x++)for(let a of comps(n-x,r-1))yield[x,...a];}
function per(A){
 const T=Array(1<<A.length).fill(0n);T[0]=1n;
 for(let s=0;s<T.length-1;s++){let k=0,t=s;while(t){k+=(t&1);t>>=1;}
 for(let j=0;j<A.length;j++)if(!(s>>j&1))T[s|1<<j]+=A[k][j]*T[s];}
 return T.at(-1);
}
function eqSmith(A,D,block){
 const n=A.length,T=A.map(r=>[...r]);let a=0;
 for(let E of block){
  for(let i=a+1;i<a+E.length;i++)for(let j=0;j<n;j++)T[i][j]-=T[a][j];
  for(let j=a+1;j<a+E.length;j++)for(let i=0;i<n;i++)T[i][j]-=T[i][a];
  a+=E.length;
 }
 return T.every((r,i)=>r.every((x,j)=>x===(i===j?D[i]:0n)));
}
const witness=(D,p)=>{
 let n=D.length,opt=null,best=Infinity,used=0;
 for(const a of comps(n,n)){
  let loss=0,sz=0;
  for(let j=0;j<n;j++)if(a[j]){
   if(!D[j]){loss=Infinity;break;}
   sz++;loss+=val(D[j],p)*a[j]+val(fac[a[j]],p);
  }
  if(loss<best||(loss===best&&sz>used)){opt=a;best=loss;used=sz;}
 }
 if(!opt)return{best};
 const rest=opt.flatMap((a,j)=>a===0?[j]:[]),g=[];
 opt.forEach((a,j)=>{if(a)g.push([j,...rest.splice(0,a-1)]);});
 const bb=[],reorder=[];let i=0;
 for(const G of g){
  reorder.push(...G.map(t=>D[t]));
  bb.push(...aN(G.length,(a)=>aN(n,(k)=>k>=i&&k<i+G.length?(D[G[0]]+(a>0&&k===i+a?D[G[a]]:0n)):0n)));
  i+=G.length;
 }
 assert(eqSmith(bb,reorder,g));
 assert.equal(val(per(bb),p),best);
 return {best,bb};
};
let seed=0x3d2871f1;
const r=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return (seed>>>6)%n;};
const gcd=(x,y)=>{x=x<0n?-x:x;y=y<0n?-y:y;while(y){const z=x%y;x=y;y=z;}return x;};
const fixedGcd=D=>{
 let n=D.length,T=aN(n+1,k=>k?0n:1n);
 for(const d of D){
  const W=aN(n+1,a=>d**BigInt(a)*fac[a]);
  T=aN(n+1,t=>{let g=0n;for(let a=0;a<=t;a++)g=gcd(g,T[t-a]*W[a]);return g;});
 }
 return T[n];
};
let tests=0,singular=0,zero=0,lowerTests=0,strict=0, gcdTests=0;
for(let p of [2n,3n,5n,7n])for(let j=0;j<90;j++){
 const n=1+r(7),N=r(n+1);let d=1n;
 const D=aN(n,i=>i<N?(d*=p**BigInt(r(3))*BigInt([1,11,13][r(3)])):0n);
 const {best}=witness(D,p);
 const g=fixedGcd(D);
 assert.equal(val(g,p),best);
 let next=0n;for(const a of comps(n,n))next=gcd(next,a.reduce((x,m,i)=>x*D[i]**BigInt(m)*fac[m],1n));
 assert.equal(next,g);
 gcdTests++;
 if(N<n)singular++;
 if(!N)zero++;
 for(let i=0;i<4;i++){
  const T=aN(n,a=>aN(n,b=>a===b?D[a]:0n));
  if(n>1)for(let h=0;h<15;h++){
   let a=r(n),b=(a+r(n-1)+1)%n,u=BigInt(r(7)-3);
   if(h&1){for(let k=0;k<n;k++)T[a][k]+=u*T[b][k];}
   else{for(let k=0;k<n;k++)T[k][a]+=u*T[k][b];}
  }
  const v=val(per(T),p);assert(v>=best);if(g)assert.equal(per(T)%g,0n);lowerTests++;strict+=Number(v>best);
 }
 tests++;
}
console.log({tests,singular,zero,lowerTests,strict,gcdTests});
