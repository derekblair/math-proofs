"use strict";
const assert=require("node:assert/strict");
function perms(a){if(!a.length)return [[]];return a.flatMap((v,i)=>perms(a.filter((_,j)=>j!==i)).map(b=>[v,...b]));}
function sign(a){let s=1n;for(let i=0;i<a.length;++i)for(let j=i+1;j<a.length;++j)if(a[i]>a[j])s=-s;return s;}
function cycles(a,b){const ai=[];a.forEach((x,i)=>ai[x]=i);const p=b.map(x=>ai[x]),seen=new Set;let n=0;for(let i=0;i<a.length;i++)if(!seen.has(i)){if(p[i]!==i)n++;let j=i;do{seen.add(j);j=p[j]}while(!seen.has(j));}return n;}
let seed=77119;
function rng(n){seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed%n;}
function product(a,W){return a.reduce((acc,x,i)=>acc*W[i][x],1n);}
function check(n,P,a,b,q,W){
 const base=BigInt(q+1);
 const monom=x=>x.reduce((acc,v,i)=>acc+base**BigInt(i*n+v),0n);
 const det=new Map(P.filter(x=>x.every((v,i)=>v===a[i]||v===b[i])).map(x=>[monom(x),sign(x)*product(x,W)]));
 let D=new Map([[0n,1n]]);
 for(let j=0;j<q;++j){const nxt=new Map;for(const [s,c] of D)for(const [t,d] of det){const k=s+t;nxt.set(k,(nxt.get(k)||0n)+c*d);}D=nxt;}
 const target=BigInt(q-1)*monom(a)+monom(b);
 const expected=BigInt(q)**BigInt(cycles(a,b))*
   (sign(a)*product(a,W))**BigInt(q-1)*sign(b)*product(b,W);
 assert.equal(D.get(target)||0n,expected);
 if(q===2){
  // Multilinearization is determined by which edges occur at least once.
  const support=M=>{let out=0n,i=0n;while(M){if(M%base)out|=1n<<i;M/=base;i++;} return out;};
  const T=support(target);
  let boolCoef=0n;
  for(const [k,v] of D)if(support(k)===T)boolCoef+=v;
  assert.equal(boolCoef,expected);
 }
}
let count=0,boolean=0;
for(let n=2;n<=7;++n){const P=perms([...Array(n).keys()]);
 for(let j=0;j<28;++j){
  const a=P[rng(P.length)],b=j%5===0?a:P[rng(P.length)];
  const W=Array.from({length:n},()=>Array.from({length:n},()=>BigInt(rng(11)-5)));
  for(const q of [2,3,4,5,6]) {check(n,P,a,b,q,W);count++;if(q===2)boolean++;}
 }}
console.log({exactCoefficientChecks:count,booleanSquareChecks:boolean});

// Exact complex arithmetic as pairs of BigInts.
const plus=(a,b)=>[a[0]+b[0],a[1]+b[1]];
const times=(a,b)=>[a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0]];
const scale=(a,x)=>[a[0]*x,a[1]*x];
const conj=a=>[a[0],-a[1]];
const norm2=a=>a[0]*a[0]+a[1]*a[1];
const valG=(perm,W)=>perm.reduce((v,x,i)=>times(v,W[i][x]),[sign(perm),0n]);
function checkGaussian(n, P, a,b,q,mask){
 const Q=Number(q),base=BigInt(Q+1);
 const monom=x=>x.reduce((acc,v,i)=>acc+base**BigInt(i*n+v),0n);
 const allowed=P.filter(x=>x.every((v,i)=>v===a[i]||v===b[i]));
 const keys=allowed.map(monom);
 let dict=new Map([[0n,[1n,0n]]]);
 for(const W of mask){
   const coeffs=allowed.map(x=>valG(x,W)),next=new Map;
   for(const [k,c] of dict)for(let j=0;j<keys.length;++j){
    const z=k+keys[j];next.set(z,plus(next.get(z)||[0n,0n],times(c,coeffs[j])));
   }
   dict=next;
 }
 return k=>dict.get(BigInt(Q-k)*monom(a)+BigInt(k)*monom(b))||[0n,0n];
}
let mixed=0,modulus=0,middle=0;
for(let n=2;n<=7;++n){
 const P=perms([...Array(n).keys()]);
 const make=()=>Array.from({length:n},()=>Array.from({length:n},()=>[BigInt(rng(7)-3),BigInt(rng(7)-3)]));
 for(let j=0;j<45;j++){
  const a=P[rng(P.length)],b=P[rng(P.length)],c=cycles(a,b);
  if(c===0)continue;
  for(let q=2;q<=4;++q){
   if(c===1){
    const Ms=Array.from({length:q},make);
    const values=Ms.map(M=>[valG(a,M),valG(b,M)]);
    for(let k=1;k<q;++k){
     let exp=[0n,0n];
     for(let s=0;s<1<<q;++s){
      let cnt=0,t=s;while(t){cnt+=t&1;t>>=1;}if(cnt!==k)continue;
      exp=plus(exp,values.reduce((v,row,h)=>times(v,row[(s>>h)&1]),[1n,0n]));
     }
     assert.deepEqual(checkGaussian(n,P,a,b,q,Ms)(k),exp);mixed++;
    }
   }
   const M=make(),Mc=M.map(row=>row.map(conj)),masks=[...Array(q).fill(M),...Array(q).fill(Mc)];
   const ga=valG(a,M),gb=valG(b,M);
   const coef=checkGaussian(n,P,a,b,2*q,masks);
   if(c===1){
    assert.deepEqual(coef(1), [2n*BigInt(q)*norm2(ga)**BigInt(q-1)*times(conj(ga),gb)[0],0n]);modulus++;
   }
   const [g,h]=coef(2);
   assert.equal(h,0n);
   assert.equal(g>0n,norm2(ga)>0n&&norm2(gb)>0n);
   if(!norm2(ga)||!norm2(gb)) assert.equal(g,0n);
   middle++;
  }
 }
}
console.log({mixedOneCycleCoefficients:mixed,modulusOneCycleCoefficients:modulus,positiveMiddleCoefficients:middle});
