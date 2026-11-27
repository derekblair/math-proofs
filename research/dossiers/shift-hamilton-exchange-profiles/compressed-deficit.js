#!/usr/bin/env node
'use strict';
const assert=require('node:assert/strict');
const gcd=(a,b)=>b?gcd(b,a%b):a;

function enumerateProfiles(m,D,T,report,rooted=false){
  const s=D-1,g=gcd(m,s),a=m/g;
  const mod=i=>((i%m)+m)%m;
  const pos=Array(m);
  for(let o=0;o<g;o++)for(let p=0,j=o;p<a;p++,j=mod(j+s))pos[j]=p;
  const B=Math.min(T,s-2),bits=[];
  for(let i=0;i<m;i++)for(let j=0;j<=B;j++)bits.push([i,j]);
  let low=0;
  const events=new Map();
  function change(i,d,p){
    const [x,y]=events.get(i)||[0,0],u=x+d,v=y+p;
    if(u||v)events.set(i,[u,v]);else events.delete(i);
  }
  function emit(t,depth){
    let fixed=low,free=g;
    const orbitEvents=new Map();
    for(const [j,[d,p]] of events){
      const id=j%g;if(!orbitEvents.has(id))orbitEvents.set(id,[]);
      orbitEvents.get(id).push([pos[j],d,p]);
    }
    for(const e of orbitEvents.values()){
      e.sort((x,y)=>x[0]-y[0]);
      const valid=[];
      for(let start=0;start<=1;start++){
        let H=start,prev=0,count=0,ok=true;
        for(const [u,delta,p] of e){
          count+=H*(u-prev);H+=delta;prev=u;
          if(H<0||H>1||H+p<0||H+p>1){ok=false;break;}
        }
        if(ok&&H===start)valid.push(count+H*(a-prev));
      }
      if(!valid.length)return;
      if(valid.length===1){free--;fixed+=valid[0];}
      else assert.deepEqual(valid,[0,a]);
    }
    report(t,fixed,free,a,depth);
  }
  function toggle(i,b,d){
    const jmp=mod(i+(b||s-1)),sg=(b?1:-1)*d;
    change(i,sg,-sg);change(jmp,-sg,0);if(!b)low+=d;
  }
  function visit(begin,t,depth,skip){
    if(!rooted||t===T)emit(t,depth);
    if(t===T)return;
    for(let j=begin;j<bits.length;j++){
      if(j===skip)continue;
      const [i,b]=bits[j],cost=b||1;
      if(t+cost>T)continue;
      toggle(i,b,1);visit(j+1,t+cost,depth+1,skip);toggle(i,b,-1);
    }
  }
  if(!rooted)visit(0,0,0,-1);
  else if(T>0)for(let b=0;b<=B;b++){
    const cost=b||1;if(cost>T)continue;
    toggle(0,b,1);visit(0,cost,1,b);toggle(0,b,-1);
  }
}
function choices(n,j){
  if(j<0||j>n||!Number.isInteger(j))return 0n;
  let z=1n;
  for(let i=1;i<=Math.min(j,n-j);i++)z=z*BigInt(n-i+1)/BigInt(i);
  return z;
}
// Counts one distance/winding bucket, without listing edge sets.
function countExchange(m,D,k,w){
  const t=k*(D-1)-w*m;
  if(t<0||k<=0)return 0n;
  if(t===0){const g=gcd(m,D-1);return choices(g,k/(m/g));}
  let total=0n;
  const rootedTotals=new Map();
  const rows=new Map();
  function chooseCached(n,j){
    if(j<0||j>n||!Number.isInteger(j))return 0n;
    if(!rows.has(n)){
      const row=[1n];for(let i=1;i<=n;i++)row.push(row[i-1]*BigInt(n-i+1)/BigInt(i));
      rows.set(n,row);
    }
    return rows.get(n)[j];
  }
  enumerateProfiles(m,D,t,(z,fixed,free,a,depth)=>{
    const cnt=chooseCached(free,(k-fixed)/a);
    rootedTotals.set(depth,(rootedTotals.get(depth)??0n)+cnt);
  },true);
  for(const [depth,value] of rootedTotals){
    const totalRooted=BigInt(m)*value;
    assert.equal(totalRooted%BigInt(depth),0n);
    total+=totalRooted/BigInt(depth);
  }
  return total;
}
function replay(m,D,T){
  const s=D-1, actual=new Map(),want=new Map();
  const bump=(map,key,v)=>map.set(key,(map.get(key)??0n)+v);
  let compressedProfiles=0;
  enumerateProfiles(m,D,T,(t,h,g,a)=>{
    compressedProfiles++;
    for(let j=0;j<=g;j++){
      const k=h+j*a;if(!k)continue;
      assert.equal((k*s-t)%m,0);
      bump(actual,[k,(k*s-t)/m].join(':'),choices(g,j));
    }
  });
  const deg=Array(m).fill(0);
  function visit(i,k,t){
    if(i===m){if(k){assert.equal((k*s-t)%m,0);bump(want,[k,(k*s-t)/m].join(':'),1n);}return;}
    for(let a=0;a<D;a++)for(let b=a+1;b<D;b++){
      const v=(i+a)%m,z=(i+b)%m;
      const defect=Number(a!==s-1&&b!==s-1)+(a<s-1?a:0)+(b<s-1?b:0);
      if(t+defect>T||deg[v]===2||deg[z]===2)continue;
      deg[v]++;deg[z]++;visit(i+1,k+Number(a<s-1)+Number(b<s-1),t+defect);deg[v]--;deg[z]--;
    }
  }
  visit(0,0,0);
  assert.equal(actual.size,want.size);
  for(const [key,n] of want){
    assert.equal(actual.get(key),n);
    const [k,w]=key.split(':').map(Number);
    assert.equal(countExchange(m,D,k,w),n);
  }
  return {compressedProfiles, factors:[...actual.values()].reduce((a,b)=>a+b,0n),buckets:actual.size};
}
if(require.main===module){
  let cases=0,profiles=0,factors=0n,buckets=0;
  for(let D=3;D<=8;D++)for(let m=D;m<=11;m++){
    const r=replay(m,D,3);cases++;profiles+=r.compressedProfiles;factors+=r.factors;buckets+=r.buckets;
  }
  assert.equal(countExchange(5,4,4,2),25n);
  console.log({cases,profiles,factors:factors.toString(),buckets});
}
module.exports={countExchange,enumerateProfiles};
