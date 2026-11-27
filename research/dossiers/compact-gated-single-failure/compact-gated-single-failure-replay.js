'use strict';
let seed=391;const rnd=m=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return (seed>>>9)%m;};
let instances=0,negativeChecks=0,edgeChecks=0,vertexChecks=0,loops=0;
const inf=Infinity, ck=(p,s)=>{if(!p)throw Error(s);};
for(let n=3;n<=13;n++)for(let z=0;z<42;z++){
 const V=Array.from({length:n},(_,i)=>i), F=V.filter(()=>rnd(4)===0), gs=new Set(F);
 const h=V.map(()=>rnd(29)-14), A=[];
 for(const i of V)for(const j of V)
  if((i<j||gs.has(i)||gs.has(j))&&rnd(5)===0){A.push([i,j,rnd(14)-h[i]+h[j]]);if(i===j)loops++;}
 const ns=n+F.length, In=u=>gs.has(u)?n+F.indexOf(u):u;
 const order=[...F,...V.filter(v=>!gs.has(v)),...F.map(In)], pos=new Map(order.map((a,i)=>[a,i]));
 const D=A.map(([u,v,w])=>[u,In(v),w]);ck(D.every(([a,b])=>pos.get(a)<pos.get(b)),"split topology");
 function dag(seed, E=D, bad=-1, ea=-1, eb=-1){
  const d=seed.slice();
  for(const a of order)if(a!==bad)for(const [u,v,w]of E)if(u===a&&v!==bad&&!(u===ea&&v===eb))d[v]=Math.min(d[v],d[u]+w);
  return d;
 }
 function bf(N,E,seed,bad=-1){
  const d=seed.slice();for(let i=0;i<N;i++){let changed=false;for(const [a,b,w] of E)if(a!==bad&&b!==bad&&d[a]+w<d[b]){d[b]=d[a]+w;changed=true;}
   if(!changed)return {d,negative:false}; if(i===N-1)return {d,negative:true};
  }return {d,negative:false};
 }
 const init=(N,v)=>Array(N).fill(v), at=(N,s)=>{const d=init(N,inf);d[s]=0;return d;};
 const seedMacro=dag(init(ns,0)), all=F.map(g=>dag(at(ns,g))), gateEdges=F.flatMap((_,i)=>F.map((g,j)=>[i,j,all[i][In(g)]]));
 const gsol=bf(F.length,gateEdges,F.map(g=>seedMacro[In(g)]));ck(!gsol.negative,"original feasible");
 const starts=init(ns,0);F.forEach((g,i)=>starts[g]=gsol.d[i]);const vsol=dag(starts);
 const explicit=bf(n,A,init(n,0));ck(!explicit.negative&&V.every(i=>(gs.has(i)?gsol.d[F.indexOf(i)]:vsol[i])===explicit.d[i]),"potential exact");
 if(F.length){
  const g=F[rnd(F.length)], ix=F.indexOf(g), ga=[...gateEdges,[ix,ix,-1]];
  ck(bf(F.length,ga,F.map(x=>seedMacro[In(x)])).negative&&bf(n,[...A,[g,g,-1]],init(n,0)).negative,"gate loop detection");negativeChecks++;
 }
 const s=rnd(n),t=rnd(n), U=[...new Set([s,t,...F])];
 function macro(bad=-1,ea=-1,eb=-1){
  if(bad===s||bad===t)return inf;
  const ae=ea,be=eb<0?-1:In(eb), dv=gs.has(bad)?-1:bad;
  const E=[];
  for(let i=0;i<U.length;i++)if(U[i]!==bad){
   const ds=dag(at(ns,U[i]),D,dv,ae,be);
   for(let j=0;j<U.length;j++)if(U[j]!==bad)E.push([i,j,ds[In(U[j])]]);
  }
  return bf(U.length,E,at(U.length,U.indexOf(s))).d[U.indexOf(t)];
 }
 for(const bad of V){
  const direct=bad===s||bad===t?inf:bf(n,A,at(n,s),bad).d[t];
  ck(macro(bad)===direct,"vertex removal");vertexChecks++;
 }
 for(const [a,b] of A){
  const direct=bf(n,A.filter(([i,j])=>i!==a||j!==b),at(n,s)).d[t];
  ck(macro(-1,a,b)===direct,"edge removal");edgeChecks++;
 }
 instances++;
}
console.log(JSON.stringify({instances,negativeChecks,edgeChecks,vertexChecks,loops}));