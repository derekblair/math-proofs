#!/usr/bin/env node
'use strict';
const assert=require('node:assert/strict');
const lib=new Map();
const choose=(a,b)=>{let r=1n;for(let i=1;i<=b;i++)r=r*BigInt(a-i+1)/BigInt(i);return r;};
function setup(n) {
  const p=[];
  function dfs(a,m) {
    if(a.length===n){p.push(a);return;}
    for(let j=0;j<n;j++)if(!(m>>j&1))dfs([...a,j],m|1<<j);
  }
  dfs([],0);
  const cycle=Array.from(p,()=>[]);
  for(let i=0;i<p.length;i++) {
    const inv=[];p[i].forEach((x,r)=>inv[x]=r);
    for(let j=0;j<=i;j++){
      let vis=0,c=0,t=0,mask=0;
      for(let v=0;v<n;v++)if(!(vis>>v&1)){
        let u=v,l=0,sub=0;
        do{vis|=1<<u;sub|=1<<u;u=inv[p[j][u]];l++;}while(u!==v);
        if(l>=2)c++;
        if(l===2){t++;mask|=sub;}
      }
      cycle[i].push([c,t,mask]);
    }
  }
  lib.set(n,[p,cycle]);return [p,cycle];
}
let seed=0x91e8502f,cases=0,pairs=0,positive=0,equalities=0,rootAboveHalf=0;
const random=()=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed;};
function check(A) {
  const n=A.length,[p,cycles]=lib.get(n)||setup(n);
  const w=p.map(q=>q.reduce((a,j,i)=>a*BigInt(A[i][j]),1n));
  const total=w.reduce((a,b)=>a+b,0n); cases++;if(!total)return;positive++;
  const hist=Array((n>>1)+1).fill(0n),point=Array(n).fill(0n);
  let z2=0n,z3=0n;
  for(let i=0;i<w.length;i++)if(w[i])for(let j=0;j<=i;j++)if(w[j]){
    const [c,t,M]=cycles[i][j],u=w[i]*w[j]*(i===j?1n:2n);pairs++;
    hist[t]+=u;z2+=u*(2n**BigInt(c));z3+=u*(3n**BigInt(c));
    for(let v=0;v<n;v++)if(M>>v&1)point[v]+=u;
  }
  const den=total*total;
  assert.equal(hist.reduce((a,b)=>a+b,0n),den);
  for(let k=1;k<hist.length;k++){
    const left=hist.slice(k).reduce((a,h,j)=>a+h*choose(j+k,k),0n)*2n**BigInt(k);
    const right=choose(n,2*k)*den;
    assert(left<=right);
    if(left===right)equalities++;
  }
  if(point.some(x=>2n*x>den))rootAboveHalf++;
  const e=BigInt(n);
  assert(z2*250n**e <= den*349n**e);
  assert(z3*1000n**e <= den*1699n**e);
}
for(let n=1;n<=4;n++)for(let b=0;b<2**(n*n);b++)
  check(Array.from({length:n},(_,i)=>Array.from({length:n},(_,j)=>(b>>(i*n+j))&1)));
for(const [n,repeats] of [[2,500],[3,1000],[4,1000],[5,500],[6,80]])for(let k=0;k<repeats;k++)
  check(Array.from({length:n},()=>Array.from({length:n},()=>((random()>>>16)&7)%5)));
for(let n=2;n<=6;n+=2)check(Array.from({length:n},(_,i)=>Array.from({length:n},(_,j)=>Number((i>>1)===(j>>1)))));
console.log({cases,positive,pairs,equalities,rootAboveHalf});
