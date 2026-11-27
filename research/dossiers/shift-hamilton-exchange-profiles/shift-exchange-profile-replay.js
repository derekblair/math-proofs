#!/usr/bin/env node
'use strict';
const assert=require('node:assert/strict');
const gcd=(a,b)=>b?gcd(b,a%b):Math.abs(a);
function binom(a,b){if(b<0||b>a)return 0;let x=1;for(let i=1;i<=b;i++)x=x*(a-i+1)/i;return x;}
function literalEven(m,D,limit){
  const d=D-2,deg=Array(m).fill(0),rows=[],hist=new Map();
  function visit(i,k,h){
    if(k>limit)return;
    if(i===m){
      if(!k||deg.some(x=>x!==2))return;
      const adj=Array.from({length:2*m},()=>[]);
      for(let j=0;j<m;j++)for(const b of rows[j]){adj[j].push(m+b);adj[m+b].push(j);}
      let c=0;const seen=new Set();
      for(let j=0;j<2*m;j++)if(!seen.has(j)){
        c++;const todo=[j];seen.add(j);
        while(todo.length)for(const w of adj[todo.pop()])if(!seen.has(w)){seen.add(w);todo.push(w);}
      }
      const key=[k,h,c].join(',');hist.set(key,1+(hist.get(key)??0));return;
    }
    for(let s=0;s<D;s++)for(let t=s+1;t<D;t++){
      const a=(i+s)%m,b=(i+t)%m;
      if(deg[a]===2||deg[b]===2)continue;
      deg[a]++;deg[b]++;rows.push([a,b]);
      visit(i+1,k+Number(s<d)+Number(t<d),h+Number(t<D-1));
      rows.pop();deg[a]--;deg[b]--;
    }
  }
  visit(0,0,0);return hist;
}
function predictedEven(m,D,limit){
  const d=D-2,s=D-1,hist=new Map();
  const add=(k,h,c,z)=>{if(z){const key=[k,h,c].join(',');hist.set(key,(hist.get(key)??0)+z);}};
  for(let k=1;k<=limit;k++){
    for(let h=0;h<=k;h++){
      let p=Array(m+1).fill(0);p[0]=1;
      for(let i=0;i<k;i++){
        const next=Array(m+1).fill(0);
        for(let j=0;j<=m;j++)
          for(let v=i<h?2:1;v<=(i<h?d+1:d)&&j+v<=m;v++)next[j+v]+=p[j];
        p=next;
      }
      const n=m*binom(k,h)*p[m];assert.equal(n%k,0);
      add(k,h,h||(k%2?1:2),n/k);
    }
    if(k*s===2*m){
      const g=gcd(m,s),w=s/g;
      assert.equal(2%w,0);
      add(k,k,1,binom(g,2/w));
    } else if(k*s===2*m+1){add(k,k,1,m);add(k,k-1,1,m);}
  }
  return hist;
}
function literalOdd(m){
  const n=2*m+1,V=n-1,adj=Array.from({length:n},()=>new Map());
  const add=(x,y,red)=>{adj[x].set(y,red);adj[y].set(x,red);};
  for(let i=0;i<m;i++)for(let j=0;j<4;j++){
    const b=m+(i+j)%m,red=Number(j>=2);
    if((i===0&&j===2)||(i===1&&j===0)){add(i,V,red);add(b,V,red);}
    else add(i,b,red);
  }
  const best=[n+1,n+1],ways=[0,0];let all=0;
  function visit(x,mask,blue,length,first){
    if(length===n){
      if(!adj[x].has(0)||first>x)return;
      blue+=1-adj[x].get(0);all++;
      for(const [p,k] of [[0,blue],[1,n-blue]])if(k){
        if(k<best[p]){best[p]=k;ways[p]=1;}
        else if(k===best[p])ways[p]++;
      }
      return;
    }
    for(const [y,red] of adj[x])if(!(mask>>y&1))
      visit(y,mask|(1<<y),blue+1-red,length+1,first<0?y:first);
  }
  visit(0,1,0,1,-1);return {best,ways,all};
}
let evenGraphs=0,evenFactors=0,buckets=0,boundary=0,oneSlack=0,oddGraphs=0,oddHamiltonians=0;
for(let D=3;D<=7;D++)for(let m=D;m<=13;m++){
  const limit=Math.floor((2*m+1)/(D-1));
  const a=literalEven(m,D,limit),b=predictedEven(m,D,limit);
  assert.equal(a.size,b.size);
  for(const [k,v] of a){assert.equal(v,b.get(k),JSON.stringify({D,m,k}));evenFactors+=v;}
  evenGraphs++;buckets+=a.size;
  if(limit*(D-1)===2*m)boundary++;
  if(limit*(D-1)===2*m+1)oneSlack++;
}
for(let m=4;m<=12;m++){
  const {best,ways,all}=literalOdd(m),k=Math.floor(m/2);
  assert.deepEqual(best,[k,k]);
  assert.deepEqual(ways,m%2?[2,m-1]:[2*m-2,k*(m-2)+2*(k%2)]);
  oddGraphs++;oddHamiltonians+=all;
}
console.log({evenGraphs,evenFactors,buckets,boundary,oneSlack,oddGraphs,oddHamiltonians});
