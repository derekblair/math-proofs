#!/usr/bin/env node
'use strict';
const assert=require('node:assert/strict');
let exact=0;
for(let j=0n;j<=2048n;j++){
  const D=2048n,J=j;
  const lhs=27n*D**4n-16n*(D+J)**2n*(D**2n-J**2n);
  const rhs=(2n*J-D)**2n*(4n*J**2n+12n*D*J+11n*D**2n);
  assert.equal(lhs,rhs);assert(lhs>=0n);exact++;
}
function choose(n,k){if(k>n)return 0;let z=1;for(let i=1;i<=k;i++)z=z*(n-i+1)/i;return z;}
for(let n=1;n<=9;n++){
  let total=0;function visit(i,q){if(i===n){total++;return;}
    for(let z=-2;z<=2;z++)if(q+z*z<=4)visit(i+1,q+z*z);}
  visit(0,0);let f=2*n;for(let k=0;k<=4;k++)f+=2**k*choose(n,k);
  assert.equal(f,total);exact++;
}
function midpoint(f,l,r,n){let s=0;for(let i=0;i<n;i++)s+=f(l+(r-l)*(i+0.5)/n);
  return s*(r-l)/n;}
function angularNormal(d){let a=d%2?0.5:1/Math.PI;for(let k=d%2?3:2;k<d;k+=2)a*=k/(k-1);return a;}
function saddle(e,r){const A=1+e,B=2*r;
  const t=B===0?0:2*B/(A+Math.sqrt(A*A+8*B*B));
  return (A+B*t)*Math.sqrt(1-t*t);}
function ratioF(d,e,r){
  const g=saddle(e,r),A=1+e,B=2*r;
  return angularNormal(d)*midpoint(t=>{
    const cut=A+B*t,z=cut*Math.sqrt(1-t*t)/g;
    return (cut/g)**3*z**(d-3);
  },-1,1,20000);
}
const limit=4/(3*Math.sqrt(2)), rows=[];
for(const d of [64,128,256,512,1024,2048]){
  const e=1/Math.sqrt(d),R=(1-e)/2,G=saddle(e,R);
  const laplace=ratioF(d,e,R), x=0.3,r=R*Math.exp(Math.log(x)/d);
  const radial=ratioF(d,e,r)/laplace*Math.exp(d*(Math.log(saddle(e,r))-Math.log(G)));
  rows.push({dimension:d,laplace,radial,target:Math.cbrt(x)});
}
assert(Math.abs(rows.at(-1).laplace-limit)<0.02);
assert(Math.abs(rows.at(-1).radial-Math.cbrt(0.3))<0.025);
const deriv=t=>t**3+2*t*t+4*t+4-4*Math.exp(t);
let lo=1,hi=2;for(let j=0;j<70;j++){const t=(lo+hi)/2;if(deriv(t)>0)lo=t;else hi=t;}
const λ=(lo+hi)/2;
const prefactor=3*λ*midpoint(t=>t*t*Math.exp(-λ*t),0,1,20000)/limit;
assert(λ>1.45&&λ<1.46&&prefactor>0.54&&prefactor<0.542);
console.log({exactIdentities:exact, numericalRows:rows, λ, prefactor});
