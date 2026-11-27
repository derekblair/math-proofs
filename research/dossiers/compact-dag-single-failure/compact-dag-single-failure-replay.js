'use strict';
let seed=785933;const rng=m=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return (seed>>>11)%m;};
const inf=Infinity, ord=(a,b)=>a[0]-b[0]||a[1]-b[1]||a[2]-b[2];
const check=(a,b,tag)=>{if(a!==b)throw Error(tag+':'+a+':'+b);};
let tested=0,vertexQueries=0,edgeQueries=0,changes=0,candidateCopies=0,arcCopies=0;
for(let n=3;n<=22;n++)for(let z=0;z<70;z++){
 const ids=Array.from({length:n},(_,i)=>i), W=ids.map(()=>ids.map(()=>inf)), blocks=[];
 const blockBudget=1+rng(3*n);
 for(let b=0;b<blockBudget;b++){
   const cut=1+rng(n-1), A=ids.filter(i=>i<cut&&rng(3)===0), B=ids.filter(i=>i>=cut&&rng(3)===0);
   if(!A.length||!B.length)continue;
   const p=A.map(()=>[rng(11)-5,rng(9)-4,rng(7)-3]), x=B.map(()=>rng(9)-4), y=B.map(()=>rng(21)-10);
   const C=A.map((i,j)=>B.map((k,l)=>{
     const w=p[j][0]+p[j][1]*x[l]+p[j][2]*x[l]*x[l]+y[l];
     W[i][k]=Math.min(W[i][k],w);arcCopies++;return [i,k,w];
   }));
   blocks.push(C);
 }
 if(z%2===0){for(let i=0;i+1<n;i++){const w=rng(21)-10;W[i][i+1]=Math.min(W[i][i+1],w);blocks.push([[[i,i+1,w]]]);arcCopies++;}}
 const s=z%2===0?0:rng(n-1),t=z%2===0?n-1:s+1+rng(n-s-1);
 const run=(del=-1,a=-1,b=-1,newValue=inf)=>{
    if(s===del||t===del)return inf;
    const d=ids.map(()=>inf);d[s]=0;
    for(let i=s;i<t;i++)if(i!==del&&d[i]!==inf)for(let j=i+1;j<=t;j++)if(j!==del){
       const w=i===a&&j===b?newValue:W[i][j]; d[j]=Math.min(d[j],d[i]+w);
    }
    return d[t];
 };
 const alpha=ids.map(()=>inf),beta=ids.map(()=>inf);alpha[s]=0;beta[t]=0;
 for(let i=s;i<n;i++)for(let j=i+1;j<n;j++)alpha[j]=Math.min(alpha[j],alpha[i]+W[i][j]);
 for(let j=t;j>=0;j--)for(let i=j-1;i>=0;i--)beta[i]=Math.min(beta[i],W[i][j]+beta[j]);
 const kept=new Map();
 const add=(row)=>{for(const [c,i,j] of row.filter(v=>v[0]!==inf).sort(ord).slice(0,2)){
     const k=i*n+j;const old=kept.get(k);if(!old||c<old[0])kept.set(k,[c,i,j]);candidateCopies++;
 }};
 for(const C of blocks){
   const H=C.map(row=>row.map(([i,j,w])=>[alpha[i]+w+beta[j],i,j]));
   H.forEach(add);for(let j=0;j<H[0].length;j++)add(H.map(q=>q[j]));
 }
 const arr=[...kept.values()];
 const cut=(r,strict)=>arr.filter(([,i,j])=>i<r&&(strict?j>r:j>=r)).sort(ord).slice(0,2);
 const V=ids.map(r=>cut(r,true)),E=ids.map(r=>cut(r,false));
 for(const r of ids){
  const ans=r===s||r===t?inf:r<s||r>t?alpha[t]:V[r][0]?.[0]??inf;
  check(ans,run(r),"vertex failure");vertexQueries++;
 }
 for(let a=0;a<n;a++)for(let b=a+1;b<n;b++){
  const avoid=b<=s||b>t?alpha[t]:E[b].find(([,i,j])=>i!==a||j!==b)?.[0]??inf;
  check(avoid,run(-1,a,b),"edge failure");edgeQueries++;
  const nw=rng(103)-51, updated=Math.min(avoid,alpha[a]+nw+beta[b]);
  check(updated,run(-1,a,b,nw),"edge replacement or insertion");changes++;
 }
 tested++;
}
console.log(JSON.stringify({tested,vertexQueries,edgeQueries,changes,candidateCopies,arcCopies}));