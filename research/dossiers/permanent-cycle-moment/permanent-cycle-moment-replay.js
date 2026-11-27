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
      let vis=0,c=0,t=0,mask=0,fixed=0,three=0;
      for(let v=0;v<n;v++)if(!(vis>>v&1)){
        let u=v,l=0,sub=0;
        do{vis|=1<<u;sub|=1<<u;u=inv[p[j][u]];l++;}while(u!==v);
        if(l>=2)c++;
        if(l===1)fixed|=sub;
        if(l===2){t++;mask|=sub;}
        if(l===3)three|=sub;
      }
      cycle[i].push([c,t,mask,fixed,three]);
    }
  }
  lib.set(n,[p,cycle]);return [p,cycle];
}
let seed=0x91e8502f,cases=0,pairs=0,positive=0,equalities=0,pivotEqualities=0;
const random=()=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed;};
function check(A) {
  const n=A.length,[p,cycles]=lib.get(n)||setup(n);
  const w=p.map(q=>q.reduce((a,j,i)=>a*BigInt(A[i][j]),1n));
  const total=w.reduce((a,b)=>a+b,0n); cases++;if(!total)return;positive++;
  const hist=Array((n>>1)+1).fill(0n),point=Array(n).fill(0n),one=Array(n).fill(0n),three=Array(n).fill(0n);
  let z2=0n,z3=0n;
  for(let i=0;i<w.length;i++)if(w[i])for(let j=0;j<=i;j++)if(w[j]){
    const [c,t,M,F,U]=cycles[i][j],u=w[i]*w[j]*(i===j?1n:2n);pairs++;
    hist[t]+=u;z2+=u*(2n**BigInt(c));z3+=u*(3n**BigInt(c));
    for(let v=0;v<n;v++){
      if(M>>v&1)point[v]+=u;
      if(F>>v&1)one[v]+=u;
      if(U>>v&1)three[v]+=u;
    }
  }
  const den=total*total;
  assert.equal(hist.reduce((a,b)=>a+b,0n),den);
  for(let k=1;k<hist.length;k++){
    const left=hist.slice(k).reduce((a,h,j)=>a+h*choose(j+k,k),0n)*2n**BigInt(k);
    const right=choose(n,2*k)*den;
    assert(left<=right);
    if(left===right)equalities++;
  }
  for(let i=0;i<n;i++){
    const x=point[i];
    assert(2n*x<=den);
    if(2n*x===den)pivotEqualities++;
    for(const [t,s] of [[6889n,10000n],[14549n,20000n]])
      assert(x*t*s<=one[i]*s*s+three[i]*t*t);
  }
  const e=BigInt(n);
  assert(z2*10000n**e <= den*13112n**e);
  assert(z3*10000n**e <= den*15451n**e);
}
for(let n=1;n<=4;n++)for(let b=0;b<2**(n*n);b++)
  check(Array.from({length:n},(_,i)=>Array.from({length:n},(_,j)=>(b>>(i*n+j))&1)));
for(const [n,repeats] of [[2,500],[3,1000],[4,1000],[5,500],[6,80]])for(let k=0;k<repeats;k++)
  check(Array.from({length:n},()=>Array.from({length:n},()=>((random()>>>16)&7)%5)));
for(let n=2;n<=6;n+=2)check(Array.from({length:n},(_,i)=>Array.from({length:n},(_,j)=>Number((i>>1)===(j>>1)))));
let thinningChecks=0;
for(let m=1;m<=5;m++) {
  const [perms]=lib.get(m)||setup(m);
  for(const perm of perms) {
    let l=1,seen=1;
    for(let v=perm[0];v!==0;v=perm[v]){l++;seen|=1<<v;}
    if(perm.some((v,i)=>!(seen>>i&1)&&v!==i))continue;
    let numerator=0n;
    for(let h=0;h<1<<(2*m-1);h++){
      const row=i=>i===0?0:(h>>(i-1))&1;
      const col=i=>(h>>(m-1+i))&1;
      if(!perm.every((v,i)=>row(i)===col(i)&&row(i)===col(v)))continue;
      let ones=0;
      for(let jj=0;jj<2*m-1;jj++)ones+=(h>>jj)&1;
      numerator+=2n**BigInt(ones)*3n**BigInt(2*m-1-ones);
    }
    assert.equal(numerator,3n**BigInt(2*l-1)*13n**BigInt(m-l));
    thinningChecks++;
  }
}
assert.equal(thinningChecks,89);
console.log({cases,positive,pairs,equalities,pivotEqualities,thinningChecks});
